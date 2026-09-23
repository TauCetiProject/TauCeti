/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Basis
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap

/-!
# Torus pinning for the modular F4 quotient

The special character-lattice map sends a torus point `s` to
`(s₃², s₂², s₁, s₀)`.  This file proves the corresponding character identity
and specializes it to the quotient basis: its long-root weight has the same
character as the associated short-root weight after applying the special torus
map.  The two Cartan coordinates have weight zero on both sides.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11, for the
  special isogeny of type `F₄` and its effect on the character lattice.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII, for the root
  coordinates and the simple-root numbering.
-/

public section

namespace TauCeti.DynkinType

open scoped _root_.Matrix

noncomputable section

/-- The quotient-basis weight: the long root paired with a nonzero short-root
weight, and zero on the two Cartan coordinates. -/
def f4ShortRootQuotientWeight (a : Fin 26) : Fin 4 → ℤ :=
  match f4ShortRootWeightIndexEquiv a with
  | Sum.inl i => f4Root (f4SpecialIsogenyIndexEquiv i)
  | Sum.inr _ => 0

@[simp] theorem f4ShortRootQuotientWeight_symm_inl (i : F4ShortRootIndex) :
    f4ShortRootQuotientWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
      f4Root (f4SpecialIsogenyIndexEquiv i) := by
  simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply]

@[simp] theorem f4ShortRootQuotientWeight_symm_inr (j : Fin 2) :
    f4ShortRootQuotientWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inr j)) = 0 := by
  simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply]

/-- The quotient-basis character equals the target short-root character after
the special torus map. -/
theorem torusCharacter_f4ShortRootQuotientWeight
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) (a : Fin 26) :
    TauCeti.torusCharacter s (f4ShortRootQuotientWeight a) =
      TauCeti.torusCharacter (f4SpecialIsogenyTorusMap s) (f4ShortRootWeight a) := by
  rcases h : f4ShortRootWeightIndexEquiv a with i | j
  · have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inl i) := by
      apply f4ShortRootWeightIndexEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    subst a
    rw [torusCharacter_f4SpecialIsogenyTorusMap]
    simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply,
      f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl]
    rw [← f4SimplyConnectedRootDatum_root,
      f4SpecialIsogenyMatrix_mulVec_root]
    simp only [i.property, one_smul]
  · have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inr j) := by
      apply f4ShortRootWeightIndexEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    subst a
    simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply,
      f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inr, TauCeti.torusCharacter_zero]

/-- The quotient-basis character identity after coercing units to the scalar ring. -/
theorem coe_torusCharacter_f4ShortRootQuotientWeight
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) (a : Fin 26) :
    ((TauCeti.torusCharacter s (f4ShortRootQuotientWeight a) : Aˣ) : A) =
      ((TauCeti.torusCharacter (f4SpecialIsogenyTorusMap s)
        (f4ShortRootWeight a) : Aˣ) : A) :=
  congrArg Units.val (torusCharacter_f4ShortRootQuotientWeight s a)

end

end TauCeti.DynkinType
