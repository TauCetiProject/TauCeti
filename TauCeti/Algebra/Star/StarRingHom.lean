/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Projections and inclusions of a product as star ring homomorphisms

For star rings `R` and `S`, the projections `R × S → R`, `R × S → S` and the inclusions
`R → R × S`, `S → R × S` are nonunital star ring homomorphisms. Mathlib has them as nonunital
⋆-algebra homomorphisms over a scalar ring (`NonUnitalStarAlgHom.fst` and its siblings); these are
the underlying star ring homomorphisms, the form taken by functors such as the projection
`K₀`-group.

## Main definitions

* `TauCeti.NonUnitalStarRingHom.fst`, `TauCeti.NonUnitalStarRingHom.snd`: the projections.
* `TauCeti.NonUnitalStarRingHom.inl`, `TauCeti.NonUnitalStarRingHom.inr`: the inclusions.

## Main statements

* `TauCeti.NonUnitalStarRingHom.fst_comp_inl` and `TauCeti.NonUnitalStarRingHom.snd_comp_inr`:
  a projection after the matching inclusion is the identity.
* `TauCeti.NonUnitalStarRingHom.fst_comp_inr` and `TauCeti.NonUnitalStarRingHom.snd_comp_inl`:
  a projection after the other inclusion is zero.
-/

public section

namespace TauCeti.NonUnitalStarRingHom

section Prod

variable (R S : Type*) [NonUnitalNonAssocSemiring R] [Star R] [NonUnitalNonAssocSemiring S] [Star S]

/-- The first projection `R × S → R` as a star ring homomorphism. -/
def fst : R × S →⋆ₙ+* R :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.fst ℕ R S)

/-- The second projection `R × S → S` as a star ring homomorphism. -/
def snd : R × S →⋆ₙ+* S :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.snd ℕ R S)

variable {R S}

/-- The first projection sends `x` to `x.1`. -/
@[simp]
theorem fst_apply (x : R × S) : fst R S x = x.1 :=
  (rfl)

/-- The second projection sends `x` to `x.2`. -/
@[simp]
theorem snd_apply (x : R × S) : snd R S x = x.2 :=
  (rfl)

end Prod

section InlInr

variable (R S : Type*) [NonUnitalNonAssocSemiring R] [StarAddMonoid R]
  [NonUnitalNonAssocSemiring S] [StarAddMonoid S]

/-- The first inclusion `R → R × S` as a star ring homomorphism. -/
def inl : R →⋆ₙ+* R × S :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.inl ℕ R S)

/-- The second inclusion `S → R × S` as a star ring homomorphism. -/
def inr : S →⋆ₙ+* R × S :=
  NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.inr ℕ R S)

variable {R S}

/-- The first inclusion sends `r` to `(r, 0)`. -/
@[simp]
theorem inl_apply (r : R) : inl R S r = (r, 0) :=
  (rfl)

/-- The second inclusion sends `s` to `(0, s)`. -/
@[simp]
theorem inr_apply (s : S) : inr R S s = (0, s) :=
  (rfl)

variable (R S)

/-- The first projection after the first inclusion is the identity. -/
@[simp]
theorem fst_comp_inl : (fst R S).comp (inl R S) = NonUnitalStarRingHom.id R :=
  NonUnitalStarRingHom.ext fun _ ↦ rfl

/-- The second projection after the second inclusion is the identity. -/
@[simp]
theorem snd_comp_inr : (snd R S).comp (inr R S) = NonUnitalStarRingHom.id S :=
  NonUnitalStarRingHom.ext fun _ ↦ rfl

/-- The first projection after the second inclusion is zero. -/
@[simp]
theorem fst_comp_inr : (fst R S).comp (inr R S) = 0 :=
  NonUnitalStarRingHom.ext fun _ ↦ rfl

/-- The second projection after the first inclusion is zero. -/
@[simp]
theorem snd_comp_inl : (snd R S).comp (inl R S) = 0 :=
  NonUnitalStarRingHom.ext fun _ ↦ rfl

end InlInr

end TauCeti.NonUnitalStarRingHom
