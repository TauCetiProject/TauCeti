/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus.Normalizer
public import TauCeti.NumberTheory.ModularForms.ArithmeticSubgroups
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Non-split Cartan levels: examples

For `ℓ = 13` and `𝔽_{13²} = GaloisField 13 2`, the non-split Cartan subgroup `C_ns(13)` of
`GL₂(𝔽₁₃)` has order `168` and projective index `156`, and its normalizer `C_ns⁺(13)` has order
`336`, contains `C_ns(13)` with index `2`, and has projective index `78`. The determinant maps
both onto `𝔽₁₃ˣ`.

For `ℓ = 2` and `𝔽₄ = GaloisField 2 2`, the non-split Cartan subgroup `C_ns(2)` is cyclic of order
`3`, and its normalizer is all of `GL₂(𝔽₂)`, of order `6`.
-/

public section

open TauCeti

namespace TauCeti.NonSplitTorusNormalizerExamples

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

instance : Algebra.IsQuadraticExtension (ZMod 13) (GaloisField 13 2) :=
  ⟨GaloisField.finrank 13 two_ne_zero⟩

/-- `|C_ns(13)| = 13² - 1 = 168`. -/
example : Nat.card (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2)) = 168 := by
  rw [GL2NonSplitTorus.natCard_eq, Nat.card_zmod]
  rfl

/-- `[GL₂(𝔽₁₃) : ±C_ns(13)] = 156`. -/
example : (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2)).projectiveIndex = 156 := by
  rw [Subgroup.projectiveIndex_eq_index GL2NonSplitTorus.neg_one_mem, GL2NonSplitTorus.index_eq,
    Nat.card_zmod]

/-- `|C_ns⁺(13)| = 336`. -/
example : Nat.card (Subgroup.normalizer
    (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2) : Set (GL (Fin 2) (ZMod 13)))) = 336 := by
  rw [GL2NonSplitTorus.natCard_normalizer, Nat.card_zmod]
  rfl

/-- `[GL₂(𝔽₁₃) : ±C_ns⁺(13)] = 78`. -/
example : (Subgroup.normalizer
    (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2) : Set (GL (Fin 2) (ZMod 13)))).projectiveIndex =
      78 := by
  rw [Subgroup.projectiveIndex_eq_index GL2NonSplitTorus.neg_one_mem_normalizer]
  have h := GL2NonSplitTorus.two_mul_index_normalizer (F := ZMod 13) (E := GaloisField 13 2)
  rw [Nat.card_zmod] at h
  omega

/-- `C_ns(13)` has index `2` in `C_ns⁺(13)`. -/
example : (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2)).relIndex (Subgroup.normalizer
    (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2) : Set (GL (Fin 2) (ZMod 13)))) = 2 :=
  GL2NonSplitTorus.relIndex_normalizer

/-- The determinant is surjective on `C_ns(13)` and on `C_ns⁺(13)`. -/
example : (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2)).map Matrix.GeneralLinearGroup.det = ⊤ ∧
    (Subgroup.normalizer (GL2NonSplitTorus (ZMod 13) (GaloisField 13 2) :
      Set (GL (Fin 2) (ZMod 13)))).map Matrix.GeneralLinearGroup.det = ⊤ :=
  ⟨GL2NonSplitTorus.map_det, GL2NonSplitTorus.map_det_normalizer⟩

instance instIsQuadraticExtensionGaloisFieldTwo :
    Algebra.IsQuadraticExtension (ZMod 2) (GaloisField 2 2) :=
  ⟨GaloisField.finrank 2 two_ne_zero⟩

/-- `|C_ns(2)| = 2² - 1 = 3`. -/
theorem natCard_gl2NonSplitTorus_two :
    Nat.card (GL2NonSplitTorus (ZMod 2) (GaloisField 2 2)) = 3 := by
  rw [GL2NonSplitTorus.natCard_eq, Nat.card_zmod]
  rfl

/-- `C_ns(2)` is cyclic (of order `3`). -/
example : IsCyclic (GL2NonSplitTorus (ZMod 2) (GaloisField 2 2)) :=
  have : Fact (Nat.card (GL2NonSplitTorus (ZMod 2) (GaloisField 2 2))).Prime :=
    ⟨natCard_gl2NonSplitTorus_two ▸ Nat.prime_three⟩
  isCyclic_of_prime_card rfl

/-- The normalizer `C_ns⁺(2)` of `C_ns(2)` is all of `GL₂(𝔽₂)`, of order `6`. -/
example : Subgroup.normalizer
      (GL2NonSplitTorus (ZMod 2) (GaloisField 2 2) : Set (GL (Fin 2) (ZMod 2))) = ⊤ ∧
    Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  have hGL : Nat.card (GL (Fin 2) (ZMod 2)) = 6 :=
    natCard_GL_fin_two_of_card_eq_two (Nat.card_zmod 2)
  refine ⟨Subgroup.eq_top_of_card_eq _ ?_, hGL⟩
  rw [GL2NonSplitTorus.natCard_normalizer, Nat.card_zmod, hGL]
  rfl

end TauCeti.NonSplitTorusNormalizerExamples
