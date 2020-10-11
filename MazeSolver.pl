%these predicates(solve_maze) solves the maze:
%they read the maze input file(given as a parameter)
%finds the origin of the maze
%uses the chosen algorithm to reach the target and getting the moves
%then writes the solution to a file called "solvedMaze"
%
% I generilized the solution so that the code stays the same and i just
% plug the algorithm i want to search the maze with.
:- dynamic square/2.
:- dynamic origin/1.
:- dynamic target/1.
:- dynamic door/2.

%this is the dfs
solve_maze_dfs(FileName):-
    read_maze(FileName),origin(square(Ro,Co)),!,dfs(square(Ro,Co),Solution),
    write_solution(Solution,FileName),!.

%this is the best first
solve_maze_best_first(FileName):-
    read_maze(FileName),origin(square(Ro,Co)),!,bestfirst(square(Ro,Co),Solution),
    write_solution(Solution,FileName),!.

read_maze(FileName):-
    see(FileName),!,
    read_maze(1,1),!.

% read_maze(Row,Col) to keep track of which column and row we are
% currently at to map the maze
read_maze(R,C):-
    get0(Ch),!,
    (
        (Ch is -1,seen,!);%eof is -1 - close the file

        (Ch is 115,assert(square(R,C)),
         assert(origin(square(R,C))),C1 is C+1,read_maze(R,C1));%s is 115 - its the origin

        (Ch is 116,assert(square(R,C)),
         assert(target(square(R,C))),C1 is C+1,read_maze(R,C1));%t is 116 - its the target

        (Ch is 32,1 is mod(R,2),0 is mod(C,2),%space is 32 - square
         assert(square(R,C)),C1 is C+1,read_maze(R,C1));%it can only be in odd row and even col

        (Ch is 32,assert(door(R,C)),%space - door (not in odd row and even col - it's a door)
        C1 is C+1,read_maze(R,C1));

        (Ch is 10,R1 is R+1,read_maze(R1,1));%10 is a new line
        (C1 is C+1,read_maze(R,C1))).%everything else is a wall

% now we read the file again and writing to the solution file
% simultaneously - the walls and doors will be written the same but if
% its a space we walked on in the solution we write it as *
% after we finished we use clean_up - to retract everything.
write_solution(Solution,FileName):-
    see(FileName),!,tell(solved_maze),!,
    write_solution(1,1,Solution),!,clean_up.

write_solution(R,C,Solution):-
    get0(Ch),!,
    (
        (Ch is -1,seen,told,!);%eof - we are done with the files - close them all

        (origin(square(R,C)),write("s"),C1 is C+1,write_solution(R,C1,Solution));%s - write s

        (target(square(R,C)),write("t"),C1 is C+1,write_solution(R,C1,Solution));%t - write t

        (square(R,C),member(square(R,C),Solution),!,write("*"),
         C1 is C+1,write_solution(R,C1,Solution));%part of the solution - write *

        (square(R,C),write(" "),C1 is C+1,write_solution(R,C1,Solution));%not part of the solution - write a space

        (door(R,C),write(" "),C1 is C+1,write_solution(R,C1,Solution));%door - write a space

        (Ch is 124,write("|"),C1 is C+1,write_solution(R,C1,Solution));%wall | - write |

        (Ch is 45,write("-"),C1 is C+1,write_solution(R,C1,Solution));%wall - write -

        (Ch is 10,write("\n"),R1 is R+1,write_solution(R1,1,Solution))%new line - write a \n
    ).

%retract all after we finished
clean_up:-
    retractall(origin(_)),
    retractall(target(_)),
    retractall(square(_,_)),
    retractall(door(_,_)).

%move predicate is true when we can move from square coordinates to other square(there is a door between them)
%
%this case handels two squares in the same row and 2 columns away from each other - between them there is a door
move(Rs,Cs,Rs,Cs1):-
	square(Rs,Cs),square(Rs,Cs1),
	Cs1 is Cs+2,
	C is Cs+1,
	door(Rs,C).

%this case handels two squares in the same column and 2 rows away from each other - between them there is a door
move(Rs,Cs,Rs1,Cs):-
	square(Rs,Cs),square(Rs1,Cs),
	Rs1 is Rs+2,
	R is Rs+1,
	door(R,Cs).

%this is move that gets square(R,C) as parameters
move(square(Rs,Cs),square(Rs,Cs1)):-
	move(Rs,Cs,Rs,Cs1);
	move(Rs,Cs1,Rs,Cs).
move(square(Rs,Cs),square(Rs1,Cs)):-
	move(Rs,Cs,Rs1,Cs);
	move(Rs1,Cs,Rs,Cs).

%passage means - we can go directly from square1 to square2
passage(square(R,C),square(R1,C1)):-
	move(square(R,C),square(R1,C1)).

%simple dfs that prevents cycles
dfs(Start,Sol):-
	dfs(Start,[],Sol).
dfs(Goal,_,[Goal]):-
	target(Goal).
dfs(Node,Visited,[Node|Path]):-
	passage(Node,Node1),
	not(member(Node1,Visited)),
	dfs(Node1,[Node|Visited],Path).

%the huristic function's value is the distance from the target
findHuristic(square(R,C),Res):-
    target(square(X,Y)),
    Res is sqrt((R-X)*(R-X)+(C-Y)*(C-Y)).

s(N,M,1):- %the weight of "edges" between neighbors is 1 (for the best first predicate from page 285)
	passage(N,M).
min1(X,Y,Y):-
	Y=<X,!.
min1(X,_,X).

%this is the best first search algorithm from page 285
%just using my huristic function
bestfirst(Start,Solution):-
	expand([],l(Start,0/0),9999,_,yes,Solution).

expand(P,l(N,_),_,_,yes,[N|P]):-
	target(N).

expand(P,l(N,F/G),Bound,Tree1,Solved,Sol):-
	F=<Bound,
	(bagof(M/C,(s(N,M,C),\+member(M,P)),Succ),
		!,
		succlist(G,Succ,Ts),
		bestf(Ts,F1),
		expand(P,t(N,F1/G,Ts),Bound,Tree1,Solved,Sol)
		;
		Solved=never
	).

expand(P,t(N,F/G,[T|Ts]),Bound,Tree1,Solved,Sol):-
	F=<Bound,
	bestf(Ts,BF),min1(Bound,BF,Bound1),
	expand([N|P],T,Bound1,T1,Solved1,Sol),
	continue(P,t(N,F/G,[T1|Ts]),Bound,Tree1,Solved1,Solved,Sol).

expand(_,t(_,_,[]),_,_,never,_):-!.
expand(_,Tree,Bound,Tree,no,_):-
	f(Tree,F),F>Bound.

continue(_,_,_,_,yes,yes,_).
continue(P,t(N,_/G,[T1|Ts]),Bound,Tree1,no,Solved,Sol):-
	insert1(T1,Ts,NTs),
	bestf(NTs,F1),
	expand(P,t(N,F1/G,NTs),Bound,Tree1,Solved,Sol).

continue(P,t(N,_/G,[_|Ts]),Bound,Tree1,never,Solved,Sol):-
	bestf(Ts,F1),
	expand(P,t(N,F1/G,Ts),Bound,Tree1,Solved,Sol).

succlist(_,[],[]).
succlist(G0,[N/C|NCs],Ts):-
	G is G0+C,
	findHuristic(N,H),
	F is G+H,
	succlist(G0,NCs,Ts1),
	insert1(l(N,F/G),Ts1,Ts).

insert1(T,Ts,[T|Ts]):-
	f(T,F),bestf(Ts,F1),
	F=<F1,!.

insert1(T,[T1|Ts],[T1|Ts1]):-
	insert1(T,Ts,Ts1).

f(l(_,F/_),F).
f(t(_,F/_,_),F).

bestf([T|_],F):-
	f(T,F).
bestf([],9999).
