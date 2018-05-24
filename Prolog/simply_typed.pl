%% Type inference for The Simply Typed Lambda Calculus

:- op(150, xfx, ⊢).
:- op(140, xfx, :).
:- op(100, xfy, ->).
:- op(100, yfx, $).

% Γ ⊢    Term : Type          :- atom(Term), member(Term : Type, Γ).
% Γ ⊢ λ(A, B) : Alpha -> Beta :- [A : Alpha|Γ] ⊢ B : Beta.
% Γ ⊢   A $ B : Beta          :- Γ ⊢ A : Alpha -> Beta, Γ ⊢ B : Alpha.

%% This version can find a context, in which the given term lives, but
%% relies on variables being given as atoms. That can lead to strange
%% inferences.

/*
typed(Γ, X      , A     ) :- atom(X), !, member(X : A, Γ).
typed(Γ, λ(X, M), A -> B) :- typed([X : A | Γ], M, B).
typed(Γ, M $ N  , B     ) :-
        typed(Γ, M, A -> B),
        typed(Γ, N, A_),
        unify_with_occurs_check(A, A_).

Γ ⊢ M : A :- typed(Γ, M, A).
*/

/** Examples:

% Typing fix
?- Γ ⊢ y $ f : A, Γ ⊢ f $ (y $ f) : A.
Γ = [y: (A->A)->A, f:A->A|_G330]

% Typing the Y combinator
?- Γ ⊢ λ(f, (λ(f, f $ f)) $ (λ(g, f $ (g $ g)))) : Y.
Γ = [g:_7148|_7250],
Y =  (_7148->_7148)->_7148

% Typing flip id
?- Id = λ(x, x), Flip = λ(f, λ(y, λ(x, f $ x $ y))),
   Γ ⊢ Flip $ Id : A.
A = _2720->(_2720->_2740)->_2740

**/

%% The following version relies on being given the correct context.
%% Otherwise the search just loops in some cases...

% Find the type of a variable in the given context.
find([Y:A | _], X, A) :- X == Y, !.
find([_   | Γ], X, A) :- find(Γ, X, A).

typed(Γ, X      , A     ) :-
        var(X), !, find(Γ, X, A_), unify_with_occurs_check(A_, A).
typed(Γ, λ(X, M), A -> B) :- typed([X : A | Γ], M, B).
typed(Γ, M $ N  , B     ) :-
        typed(Γ, M, A -> B),
        typed(Γ, N, A_),
        unify_with_occurs_check(A, A_).

Γ ⊢ M : A :- typed(Γ, M, A).

/** Examples:

% Typing fix
?- Γ = [Y: (A->A)->A, F:A->A],
  Γ ⊢ Y $ F : A, Γ ⊢ F $ (Y $ F) : A.

% Trying to type the Y combinator
?- [] ⊢ λ(F, (λ(F, F $ F)) $ (λ(G, F $ (G $ G)))) : Y.
  false.

% Typing flip id
?- Id = λ(X, X), Flip = λ(F, λ(Y, λ(X, F $ X $ Y))),
   Γ ⊢ Flip $ Id : A.
A = _6998->(_6998->_7018)->_7018

**/

%% The following version does not use the occurs check.
%% This allows the Y-combinator to be typed.

typed_bad(Γ, X      , A     ) :-
        var(X), !, find(Γ, X, A).
typed_bad(Γ, λ(X, M), A -> B) :- typed_bad([X : A | Γ], M, B).
typed_bad(Γ, M $ N  , B     ) :-
        typed_bad(Γ, M, A -> B),
        typed_bad(Γ, N, A).

/** Examples:

% Typing fix
?- Γ = [Y: (A->A)->A, F:A->A],
  Γ ⊢ Y $ F : A, Γ ⊢ F $ (Y $ F) : A.

% Typing self application
?- typed_bad([], λ(F, F $ F), A).
A = _S1->_1994, % where
    _S1 = _S1->_1994

% Typing the Y combinator
?- Y = λ(F, (λ(F, F $ F)) $ (λ(G, F $ (G $ G)))),
  typed_bad([], Y, A).
A =  (_592->_592)->_592

% Typing flip id
?- Id = λ(X, X), Flip = λ(F, λ(Y, λ(X, F $ X $ Y))),
   Γ ⊢ Flip $ Id : A.
A = _6998->(_6998->_7018)->_7018

**/

is_type(X) :- var(X), !.
is_type(A -> B) :-  acyclic_term(A -> B), is_type(A), is_type(B).

typed_alt(Γ, X      , A     ) :-
        var(X), !, find(Γ, X, A), is_type(A).
typed_alt(Γ, λ(X, M), A -> B) :- typed_alt([X : A | Γ], M, B).
typed_alt(Γ, M $ N  , B     ) :-
        typed_alt(Γ, M, A -> B),
        typed_alt(Γ, N, A).
