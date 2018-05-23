% expr(var(X)).
% expr(app(S,T)) :- expr(S), expr(T).
% expr(abs(X,T)) :- expr(T).
% expr(let(X,S,T)) :- expr(S), expr(T).

% find(X,[Y-S|_],S) :- X==Y, !.

% Find the type of a variable in the given context.
find(X, [Y:A|_], A) :- X == Y, !.
find(X, [_  |G], A) :- find(X, G, A).

:- op(140, xfx, :).
:- op(100, xfy, ->).
:- op(100, yfx, $).

% mono(D, X) :- var(X), !, member(X, D).
% mono(_, int).
% mono(D, A -> B) :- mono(D, A), mono(D, B).

% poly(D, A) :- mono(D, A).
% poly(D, all(X, A)) :- poly([X | D], A).

mono(X) :- var(X), !.
mono(int).
mono(A -> B) :- mono(A), mono(B).

% var_list([]).
% var_list([X | L ]) :- var(X), !, var_list(L).

poly(all(_, A)) :- mono(A).

lt(X,Y):-var(X);var(Y).
lt(X,Y):-nonvar(X),nonvar(Y),X<Y.

union([],S,S).
union(S,[],S):-S\=[].
union([X|TX],[Y|TY],[X|TZ]):-
        X == Y, !, union(TX,TY,TZ).
union([X|TX],[Y|TY],[X|TZ]):-
   lt(X,Y),
   union(TX,[Y|TY],TZ).
union([X|TX],[Y|TY],[Y|TZ]):-
   lt(Y,X),
   union([X|TX],TY,TZ).

from_list([], []).
from_list([X|TX], U) :- from_list(TX, V), union([X], V, U).

difference([],_,[]).
difference(S,[],S):-S\=[].
difference([X|TX],[Y|TY],TZ):-
        X == Y, !, difference(TX,TY,TZ).
difference([X|TX],[Y|TY],[X|TZ]):-
   lt(X,Y),
   difference(TX,[Y|TY],TZ).
difference([X|TX],[Y|TY],TZ):-
   lt(Y,X),
   difference([X|TX],TY,TZ).

intersection([],_,[]).
intersection(S,[],[]):-S\=[].
intersection([X|TX],[Y|TY],[X|TZ]):-
        X == Y, !, intersection(TX,TY,TZ).
intersection([X|TX],[Y|TY],TZ):-
   lt(X,Y),
   intersection(TX,[Y|TY],TZ).
intersection([X|TX],[Y|TY],TZ):-
   lt(Y,X),
   intersection([X|TX],TY,TZ).

subset([],_).
subset([H|T1],[H|T2]):-subset(T1,T2).
subset([H1|T1],[H2|T2]):- lt(H2,H1),subset([H1|T1],T2).

in(X,[X|_]).
in(X,[Y|T]):-lt(Y,X),in(X,T).

disjoint(X, Y) :- intersection(X, Y, []).

free(X, [X]) :- var(X).
free(int, []).
free(A -> B, U) :- free(A, V), free(B, W), union(V, W, U).
free(all(L, A), U) :- free(A, V), from_list(L, W), difference(V, W, U).

freeC([], []).
freeC([_:A | G], U) :-
        free(A, V),
        freeC(G, W),
        union(V, W, U).

spec(all([], A), B) :- unify_with_occurs_check(A, B).

% spec(all(L, A), B) :-
%         free(all(L, A), V),
%         disjoint
%         \+ in(Y, V),
%         spec(A, B).

% spec(A, B) :-
%         mono(A), mono(B),
%         unify_with_occurs_check(A, B).

% typed(Γ,M,A) means that the term M is of type A in context Γ.
% Γ |- X : A, if X : A in Γ
typed(G, X, A) :- var(X), !, find(X, G, B),
        unify_with_occurs_check(B, A).
% Γ |- λx.M : A -> B if Γ,x:A |- M : B
typed(G, λ(X, M), A -> B) :-
        mono(A),
        mono(B),
        typed([X : A | G], M, B).
% Γ |- M N : B if M : A -> B and N : A
typed(G, M $ N, B) :-
        mono(B),
        typed(G, M, A -> B),
        typed(G, N, C),
        mono(C),
        unify_with_occurs_check(A, C).
typed(G, let(X, M, N), B) :-
        poly(A),
        typed(G, M, A),
        mono(B),
        typed([X : A | G], N, B).
% Generalisation: if Γ |- M : A and L ∩ fv(Γ) = ∅, then Γ |- M : ∀L. A
typed(G, M, all(L, A)) :-
        mono(A),
        free(A, VA),
        freeC(G, VG),
        difference(VA, VG, L),
        typed(G, M, A).
typed(G, M, B) :-
        poly(A),
        typed(G, M, A),
        spec(A, B).

% ?- typed([X:A, Y:B], X $ Y, C).
% A = B->C.
                                % ?- typed([], λ(X,X), A -> A).
                                % ?- typed([Y:A], λ(X,X) $ Y, A).
                                % ?- mono(X -> X).
                                % ?- poly(all([X], X -> X)).
                                % ?- typed([Y:int], let(I, λ(X,X), I $ Y), int).
% ?- free(X -> Y, U).
% U = [X, Y]
% ?- free(all([X], X -> Y), U).
% U = [Y]
% ?- free(all([X, Y], X -> Y), U).
% U = []
% ?- typed([], λ(X,X), all([S], S -> S)).
% U = []
% ?- free(int -> Y, U).
% U = [Y]
% typed([Y:A], let(I, λ(X,X), (I $ I) $ Y), A).