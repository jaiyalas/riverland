module Types where
-- .
-- I got normal type constructors
data IType : Set where
    Num : IType
    _⊃_ : IType → IType → IType
    _∧_ : IType → IType → IType
    _∨_ : IType → IType → IType
-- .
-- I also got linear type constructors
data LType : Set where
    Num : LType
    ‼_  : LType → LType
    _⊸_ : LType → LType → LType
    _⊗_  : LType → LType → LType -- ∧
    _⊕_  : LType → LType → LType -- ∨
    _&_  : LType → LType → LType -- or-liked disjunction
-- .
