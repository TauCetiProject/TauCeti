/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PreservesBracket
import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Generators
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Diagonal points of the short-root F₄ carrier

The diagonal points of the short-root carrier over characteristic two are precisely its
rank-four weight torus, over arbitrary commutative coefficient algebras. Bracket preservation
forces the diagonal entries to multiply along sums of short roots. Four of the short roots
form an integral basis of the character lattice; their values determine every other root
value. The two zero-weight diagonal entries are forced to be one by their brackets with
root vectors.

`exists_weightTorusPoints_eq_iff_isDiag` gives the pointwise characterization, and
`range_weightTorusPoints_eq_comap_diagonalTorus` gives the subgroup equality.
`exists_torusCharacter_eq_of_preservesBracket_diagonal` applies even to diagonal bracket
automorphisms not initially assumed to lie in the carrier.

This identifies diagonal carrier points, not the entire scheme-theoretic torus centralizer.
No identification with an independently pinned group is asserted.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
* The organization follows `TauCeti.Algebra.Lie.D4.Tripled.MaximalTorus`.

The proof uses the bracket invariance and integral weight table of the short-root module,
and the diagonal constant-multiplication criterion in
`TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Generators`.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

private theorem bracket_coefficient_of_weight_add (a b c : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) (hb : f4ShortRootWeight b ≠ 0)
    (hc : f4ShortRootWeight c ≠ 0)
    (hadd : f4ShortRootWeight c = f4ShortRootWeight a + f4ShortRootWeight b) :
    f4ShortRootBracketMatrix a c b = 1 := by
  obtain ⟨α, hα, hwα⟩ := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha
  obtain ⟨β, hβ, hwβ⟩ := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot b).mp hb
  obtain ⟨γ, hγ, hwγ⟩ := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot c).mp hc
  have heq : ⁅(f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra),
      (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra)⁆ =
      (f4ShortRootLieIdealBasis c : f4ModularChevalleyLieAlgebra) := by
    simp only [coe_f4ShortRootLieIdealBasis_of_weight_eq_root a α hα hwα.symm,
      coe_f4ShortRootLieIdealBasis_of_weight_eq_root b β hβ hwβ.symm,
      coe_f4ShortRootLieIdealBasis_of_weight_eq_root c γ hγ hwγ.symm]
    apply f4Modular_lie_rootVector_of_add_of_length_eq α β γ (hβ.trans hγ.symm)
    simpa only [f4SimplyConnectedRootDatum_root, ← hwα, ← hwβ, ← hwγ, add_comm] using hadd
  simp only [f4ShortRootBracketMatrix_apply, heq, ← f4ShortRootLieIdealBasis_repr_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem bracket_toral_coefficient (k : Fin 2) (a : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) :
    f4ShortRootBracketMatrix (f4ShortRootWeightIndexEquiv.symm (.inr k)) a a =
      (f4ShortRootWeight a (Fin.cast rank_F4 (f4ShortSimpleIndex k)) : ZMod 2) := by
  obtain ⟨α, hα, hwα⟩ := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha
  have heq : ⁅(f4ShortRootLieIdealBasis (f4ShortRootWeightIndexEquiv.symm (.inr k)) :
        f4ModularChevalleyLieAlgebra),
      (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)⁆ =
      (f4ShortRootWeight a (Fin.cast rank_F4 (f4ShortSimpleIndex k)) : ZMod 2) •
        (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) := by
    simp only [coe_f4ShortRootLieIdealBasis_symm_inr,
      coe_f4ShortRootLieIdealBasis_of_weight_eq_root a α hα hwα.symm,
      f4Modular_lie_simpleCoroot_rootVector, f4SimplyConnectedRootDatum_pairing,
      f4Coroot_castAdd, dotProduct_single_one, hwα]
  simp only [f4ShortRootBracketMatrix_apply, heq, map_smul,
    Finsupp.smul_apply, ← f4ShortRootLieIdealBasis_repr_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

-- This finite collection is a spanning set of the root-addition equations for the
-- twenty-four short roots. The first four weights are an integral lattice basis.
private theorem eq_one_of_root_relations {U : Type*} [MulOneClass U] (d : Fin 26 → U)
    (h : ∀ a b c, f4ShortRootWeight a ≠ 0 ∧ f4ShortRootWeight b ≠ 0 ∧
      f4ShortRootWeight c ≠ 0 ∧
      f4ShortRootWeight c = f4ShortRootWeight a + f4ShortRootWeight b →
        d c = d a * d b)
    (h0 : d 0 = 1) (h1 : d 1 = 1) (h2 : d 2 = 1) (h3 : d 3 = 1)
    (h12 : d 12 = 1) (h13 : d 13 = 1) (a : Fin 26) : d a = 1 := by
  have h15 : d 15 = 1 := by simpa only [h0, h1, one_mul] using (h 0 15 1 (by decide)).symm
  have h17 : d 17 = 1 := by simpa only [h0, h2, one_mul] using (h 0 17 2 (by decide)).symm
  have h19 : d 19 = 1 := by simpa only [h0, h3, one_mul] using (h 0 19 3 (by decide)).symm
  have h10 : d 10 = 1 := by simpa only [h1, h0, one_mul] using (h 1 10 0 (by decide)).symm
  have h24 : d 24 = 1 := by simpa only [h0, h10, one_mul] using (h 0 24 10 (by decide)).symm
  have h14 : d 14 = 1 := by simpa only [h1, h2, one_mul] using (h 1 14 2 (by decide)).symm
  have h16 : d 16 = 1 := by simpa only [h1, h3, one_mul] using (h 1 16 3 (by decide)).symm
  have h25 : d 25 = 1 := by simpa only [h1, h15, one_mul] using (h 1 25 15 (by decide)).symm
  have h8 : d 8 = 1 := by simpa only [h2, h0, one_mul] using (h 2 8 0 (by decide)).symm
  have h23 : d 23 = 1 := by simpa only [h0, h8, one_mul] using (h 0 23 8 (by decide)).symm
  have h11 : d 11 = 1 := by simpa only [h1, h23, one_mul] using h 1 23 11 (by decide)
  have h5 : d 5 = 1 := by simpa only [h2, h16, one_mul] using h 2 16 5 (by decide)
  have h21 : d 21 = 1 := by simpa only [h0, h5, one_mul] using (h 0 21 5 (by decide)).symm
  have h7 : d 7 = 1 := by simpa only [h1, h21, one_mul] using h 1 21 7 (by decide)
  have h6 : d 6 = 1 := by simpa only [h3, h0, one_mul] using (h 3 6 0 (by decide)).symm
  have h22 : d 22 = 1 := by simpa only [h0, h6, one_mul] using (h 0 22 6 (by decide)).symm
  have h9 : d 9 = 1 := by simpa only [h1, h22, one_mul] using h 1 22 9 (by decide)
  have h18 : d 18 = 1 := by simpa only [h2, h6, one_mul] using (h 2 18 6 (by decide)).symm
  have h4 : d 4 = 1 := by simpa only [h1, h18, one_mul] using h 1 18 4 (by decide)
  have h20 : d 20 = 1 := by simpa only [h0, h4, one_mul] using (h 0 20 4 (by decide)).symm
  fin_cases a <;> assumption

private theorem exists_character_of_root_relations {A : Type*} [CommRing A]
    (d : Fin 26 → Aˣ)
    (h : ∀ a b c, f4ShortRootWeight a ≠ 0 ∧ f4ShortRootWeight b ≠ 0 ∧
      f4ShortRootWeight c ≠ 0 ∧
      f4ShortRootWeight c = f4ShortRootWeight a + f4ShortRootWeight b →
        d c = d a * d b)
    (h12 : d 12 = 1) (h13 : d 13 = 1) :
    ∃ s : Fin 4 → Aˣ, ∀ a, d a = torusCharacter s (f4ShortRootWeight a) := by
  -- Write wₐ = f4ShortRootWeight a. Inverting the first four weights gives
  -- ϖ₄ = w₀, ϖ₃ = w₀ + w₁, ϖ₂ = w₀ + w₁ + w₂, ϖ₁ = w₂ + w₃.
  -- Thus s i is the prescribed character value at the fundamental weight ϖᵢ₊₁.
  let s : Fin 4 → Aˣ := ![d 2 * d 3, d 0 * d 1 * d 2, d 0 * d 1, d 0]
  let r (a : Fin 26) := d a / torusCharacter s (f4ShortRootWeight a)
  have hr (a b c : Fin 26) (hw : f4ShortRootWeight a ≠ 0 ∧
      f4ShortRootWeight b ≠ 0 ∧ f4ShortRootWeight c ≠ 0 ∧
      f4ShortRootWeight c = f4ShortRootWeight a + f4ShortRootWeight b) :
      r c = r a * r b := by
    simp only [r, h a b c hw, hw.2.2.2, torusCharacter_add, div_mul_div_comm]
  -- Only the four basis weights enter the character calculation below.
  have hw : ∀ i : Fin 4, f4ShortRootWeight (Fin.castAdd 22 i) =
      ![Pi.single 3 1, Pi.single 2 1 - Pi.single 3 1,
        Pi.single 1 1 - Pi.single 2 1,
        Pi.single 0 1 - Pi.single 1 1 + Pi.single 2 1] i := by decide
  have hbase (i : Fin 4) : r (Fin.castAdd 22 i) = 1 := by
    simp only [r, hw]
    fin_cases i <;>
      simp [s, torusCharacter_add, torusCharacter_sub, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm]
  refine ⟨s, fun a ↦ div_eq_one.mp ?_⟩
  exact eq_one_of_root_relations r hr (hbase 0) (hbase 1) (hbase 2) (hbase 3)
    (by simp [r, h12, (by decide : f4ShortRootWeight 12 = 0)])
    (by simp [r, h13, (by decide : f4ShortRootWeight 13 = 0)]) a

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- A diagonal automorphism preserving the short-root bracket is a weight-torus character
on the distinguished weight basis. This holds over nonreduced coefficient algebras as well. -/
theorem exists_torusCharacter_eq_of_preservesBracket_diagonal (d : Fin 26 → Aˣ)
    (hd : ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      (Matrix.diagonal fun a ↦ (d a : A))) :
    ∃ s : Fin 4 → Aˣ, ∀ a, d a = torusCharacter s (f4ShortRootWeight a) := by
  have hmul {a b c : Fin 26} (hc : f4ShortRootBracketMatrix a c b = 1) :
      d c = d a * d b := by
    apply Units.ext
    exact _root_.TauCeti.ConstantMultiplication.eq_mul_of_preserves_diagonal
      f4ShortRootBracketMatrix hd
      (by rw [hc, map_one]; exact isUnit_one)
  have h12 : d 1 = d 12 * d 1 := by
    apply hmul
    simpa only [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero,
      f4ShortSimpleIndex_zero, Fin.cast_cast, Fin.cast_refl, id_eq,
      (by decide : (f4ShortRootWeight 1 2 : ZMod 2) = 1)] using
      bracket_toral_coefficient 0 1 (by decide)
  have h13 : d 0 = d 13 * d 0 := by
    apply hmul
    simpa only [f4ShortRootWeightIndexEquiv_symm_apply_inr_one,
      f4ShortSimpleIndex_one, Fin.cast_cast, Fin.cast_refl, id_eq,
      (by decide : (f4ShortRootWeight 0 3 : ZMod 2) = 1)] using
      bracket_toral_coefficient 1 0 (by decide)
  exact exists_character_of_root_relations d
    (fun _ _ _ hw ↦ hmul (bracket_coefficient_of_weight_add _ _ _
      hw.1 hw.2.1 hw.2.2.1 hw.2.2.2))
    (mul_right_cancel (by simpa only [one_mul] using h12.symm))
    (mul_right_cancel (by simpa only [one_mul] using h13.symm))

/-- A point of the characteristic-two short-root F₄ carrier belongs to the weight torus
exactly when its matrix is diagonal. No field or reducedness assumption is needed. -/
@[simp]
theorem exists_weightTorusPoints_eq_iff_isDiag (g : points A) :
    (∃ s, weightTorusPoints A s = g) ↔
      ((g : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A).IsDiag := by
  constructor
  · rintro ⟨s, rfl⟩
    simp only [coe_weightTorusPoints, F4ShortRoot.coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · intro hg
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp (mem_diagonalTorus_iff.mpr hg)
    have hbracket := preservesBracket_of_mem_points g.property
    rw [← hd, diagGL_coe] at hbracket
    obtain ⟨s, hs⟩ := exists_torusCharacter_eq_of_preservesBracket_diagonal d hbracket
    refine ⟨s, Subtype.ext (Units.ext ?_)⟩
    simp only [coe_weightTorusPoints, F4ShortRoot.coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, ← hd, diagGL_coe]
    exact congrArg Matrix.diagonal (funext fun a ↦ congrArg Units.val (hs a).symm)

/-- Over every commutative 𝔽₂-algebra, the weight torus consists of all diagonal
points of the short-root F₄ carrier. -/
theorem range_weightTorusPoints_eq_comap_diagonalTorus :
    (weightTorusPoints A).range = (diagonalTorus A 26).comap (points A).subtype := by
  ext g
  rw [MonoidHom.mem_range, exists_weightTorusPoints_eq_iff_isDiag, Subgroup.mem_comap,
    Subgroup.subtype_apply, mem_diagonalTorus_iff]

end TauCeti.F4ShortRoot.PrimeField
