module Types where
-- .
data IType : Set where
    Num : IType
    _⊃_ : IType → IType → IType
    _∧_ : IType → IType → IType
    _∨_ : IType → IType → IType
-- .
data LType : Set where
    Num : LType
    ‼_  : LType → LType
    _⊸_ : LType → LType → LType
    _⊗_  : LType → LType → LType -- ∧
    _&_  : LType → LType → LType -- ...
    _⊕_  : LType → LType → LType -- ∨
-- .
