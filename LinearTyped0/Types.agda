data IType : Set where
   numᵗ : IType
   _⊃_ : IType → IType → IType
   _∧_ : IType → IType → IType
   _∨_ : IType → IType → IType

data LType : Set where
   numᵗ : LType
   _⊸_  : LType → LType → LType
   _⊕_ : LType → LType → LType
   _⊗_ : LType → LType → LType
   _&_ : LType → LType → LType
   ⟪_⟫ : LType → LType
