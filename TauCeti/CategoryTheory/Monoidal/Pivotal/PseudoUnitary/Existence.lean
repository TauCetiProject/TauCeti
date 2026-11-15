/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.PseudoUnitary.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Torsor
import TauCeti.Analysis.RCLike.Sum
import TauCeti.CategoryTheory.Monoidal.Grading.MonoidalAut

/-!
# The positive pivotal structure of a pseudo-unitary category

A pseudo-unitary complex pivotal fusion category has a unique pivotal structure whose left
dimensions are the Frobenius–Perron dimensions, and this structure is spherical.

The phase of the original dimension of each simple object defines a character of the universal
grading group. Indeed, pseudo-unitarity gives equality in the triangle inequality for every
product of simple classes, so all its simple constituents have the same phase. Twisting the
original pivotal structure by this character removes these phases from the left dimensions.
`TauCeti.IsPseudoUnitary.existsUnique_pivotalCategory` packages existence, uniqueness and
sphericity, with the dimension identity for all objects, including nonsimple and zero objects.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Proposition 8.23.
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §9.4.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C] [Linear ℂ C] [MonoidalLinear ℂ C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)] [EssentiallySmall.{w} C]
  [Fintype (SimpleClasses C)] [original : PivotalCategory C] [IsPseudoUnitary.{w} C]

private theorem norm_dimension (S : SimpleClasses C) :
    ‖SplitK0.leftDimChar.{w} ℂ C (SplitK0.simpleBasis C S)‖ =
      frobeniusPerronDim.{w} ℂ S.repr := by
  simpa only [SplitK0.simpleBasis_apply, SplitK0.leftDimChar_of] using
    (isPseudoUnitary_iff_norm_leftDim_eq.1 ‹IsPseudoUnitary.{w} C›) S.repr

private theorem dimension_ne_zero (S : SimpleClasses C) :
    SplitK0.leftDimChar.{w} ℂ C (SplitK0.simpleBasis C S) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_dimension]
  exact (frobeniusPerronDim_pos_of_simple ℂ S.repr).ne'

/-- The dimension phase of a simple class, as a nonzero complex scalar. -/
private def dimensionPhase (S : SimpleClasses C) : ℂˣ :=
  Units.mk0 (SplitK0.leftDimChar.{w} ℂ C (SplitK0.simpleBasis C S) /
    (frobeniusPerronDim.{w} ℂ S.repr : ℂ))
    (div_ne_zero (dimension_ne_zero S)
      (Complex.ofReal_ne_zero.2 (frobeniusPerronDim_pos_of_simple ℂ S.repr).ne'))

private theorem dimensionPhase_val (S : SimpleClasses C) :
    (dimensionPhase S : ℂ) = SplitK0.leftDimChar.{w} ℂ C (SplitK0.simpleBasis C S) /
      (frobeniusPerronDim.{w} ℂ S.repr : ℂ) := (rfl)

/-- Equality in the dimension bound forces the phase of a constituent to be the product of the
phases of the factors. -/
private theorem dimensionPhase_tensor (S T U : SimpleClasses C)
    (f : U.repr ⟶ S.repr ⊗ T.repr) (hf : f ≠ 0) :
    dimensionPhase U = dimensionPhase S * dimensionPhase T := by
  classical
  let χ := SplitK0.leftDimChar.{w} ℂ C
  let d (V : SimpleClasses C) := frobeniusPerronDim.{w} ℂ V.repr
  let a := χ (SplitK0.simpleBasis C S) * χ (SplitK0.simpleBasis C T)
  have ha : a ≠ 0 := mul_ne_zero (dimension_ne_zero S) (dimension_ne_zero T)
  have hna : ‖a‖ = d S * d T := by
    dsimp only [a, χ]
    rw [norm_mul, norm_dimension, norm_dimension]
  have hsum : ∑ V, (fusionCoeff ℂ S T V : ℂ) * χ (SplitK0.simpleBasis C V) = a := by
    have h := congrArg χ (SplitK0.simpleBasis_mul_simpleBasis_eq_sum_fusionCoeff ℂ S T)
    simpa only [map_mul, map_sum, map_zsmul, zsmul_eq_mul, Int.cast_natCast,
      map_natCast] using h.symm
  have hnorm : ∑ V, (fusionCoeff ℂ S T V : ℝ) * d V = d S * d T := by
    have h := congrArg (SplitK0.frobeniusPerronChar.{w} ℂ C)
      (SplitK0.simpleBasis_mul_simpleBasis_eq_sum_fusionCoeff ℂ S T)
    simpa [SplitK0.simpleBasis_apply, map_sum] using h.symm
  -- Rotate the tensor-product dimension to the positive real axis. Both the sum of the
  -- normalized constituents and the sum of their norms are one.
  let z (V : SimpleClasses C) := (fusionCoeff ℂ S T V : ℂ) *
    χ (SplitK0.simpleBasis C V) / a
  have hn (V : SimpleClasses C) : ‖z V‖ = (fusionCoeff ℂ S T V : ℝ) * d V / (d S * d T) := by
    simp only [z, norm_div, norm_mul, Complex.norm_natCast, hna]
    rw [norm_dimension]
  have hz : ∑ V, z V = ((∑ V, ‖z V‖ : ℝ) : ℂ) := by
    have hleft : ∑ V, z V = 1 := by simp only [z, ← Finset.sum_div, hsum, div_self ha]
    have hright : ∑ V, ‖z V‖ = 1 := by
      simp_rw [hn, ← Finset.sum_div, hnorm]
      exact div_self (mul_ne_zero (frobeniusPerronDim_pos_of_simple ℂ S.repr).ne'
        (frobeniusPerronDim_pos_of_simple ℂ T.repr).ne')
    rw [hleft, hright, Complex.ofReal_one]
  have hU := RCLike.eq_norm_of_sum_eq_sum_norm hz (Finset.mem_univ U)
  -- A genuine constituent has nonzero multiplicity, so its coefficient can be cancelled.
  have hN : (fusionCoeff ℂ S T U : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, fusionCoeff_eq_finrank_hom ℂ]
    exact (Module.finrank_pos_iff_exists_ne_zero.2 ⟨f, hf⟩).ne'
  have hd (V : SimpleClasses C) : (d V : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (frobeniusPerronDim_pos_of_simple ℂ V.repr).ne'
  rw [hn] at hU
  push_cast at hU
  apply Units.ext
  simp only [Units.val_mul, dimensionPhase_val]
  dsimp only [χ, d, z, a] at *
  field_simp [ha, hd S, hd T, hd U, hN] at hU ⊢
  linear_combination (div_eq_iff ha).1 hU

private def phaseCharacter : universalGradingGroup C →* ℂˣ :=
  universalGradingGroup.lift dimensionPhase dimensionPhase_tensor

private theorem phaseCharacter_degree (S : SimpleClasses C) :
    phaseCharacter (universalGradingGroup.degree S) = dimensionPhase S :=
  universalGradingGroup.lift_degree _ _ _

/-- Twist the original pivotal structure by its dimension phases. -/
@[instance_reducible]
private def positivePivotalCategory : PivotalCategory C :=
  characterMonoidalAut ℂ (phaseCharacter (C := C)) • (inferInstance : PivotalCategory C)

private theorem positivePivotalCategory_leftDim_simple (X : C) [Simple X] :
    @leftDim C _ _ _ positivePivotalCategory X =
      (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C) := by
  let S := SimpleClasses.classOf X
  let c : ℂ := dimensionPhase S
  have hc : c ≠ 0 := Units.ne_zero (dimensionPhase S)
  let Q : PivotalCategory C := positivePivotalCategory
  -- Retain the original ambient structure; all uses of the new one are explicit.
  let _ := original
  have hcomp : (@pivotalIsoApp C _ _ _ Q X).hom ≫ (pivotalIsoApp X).inv = c • 𝟙 X := by
    rw [PivotalCategory.smul_pivotalIsoApp, Iso.trans_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    exact (characterMonoidalAut_app_of_simple _ X).trans
      (congrArg (fun z : ℂˣ ↦ (z : ℂ) • 𝟙 X) (phaseCharacter_degree S))
  have hdim := leftDim_eq_leftTrace original Q X
  rw [hcomp, @leftTrace_smul C _ _ _ Q, @leftTrace_id C _ _ _ Q] at hdim
  apply smul_right_injective _ hc
  simp only []
  rw [← hdim, smul_smul]
  dsimp only [c]
  rw [dimensionPhase_val]
  rw [SplitK0.simpleBasis_apply, SplitK0.leftDimChar_of,
    ← leftDim_congr (SimpleClasses.classOfReprIso X),
    ← frobeniusPerronDim_eq_of_iso ℂ (SimpleClasses.classOfReprIso X)]
  rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2
    (frobeniusPerronDim_pos_of_simple ℂ S.repr).ne'), endAlgEquivOfSimple_smul_id]

/-- A pseudo-unitary complex pivotal fusion category has a unique pivotal structure whose left
dimensions are the Frobenius–Perron dimensions of all objects. This structure is spherical. -/
theorem IsPseudoUnitary.existsUnique_pivotalCategory :
    ∃! P : PivotalCategory C,
      (∀ X : C, @leftDim C _ _ _ P X = (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C)) ∧
        (letI := P; SphericalCategory C) := by
  have hsimple := positivePivotalCategory_leftDim_simple (C := C)
  let P : PivotalCategory C := positivePivotalCategory
  have hall (X : C) : @leftDim C _ _ _ P X =
      (frobeniusPerronDim.{w} ℂ X : ℂ) • 𝟙 (𝟙_ C) := by
    let _ := P
    have hscalar (S : SimpleClasses C) : SplitK0.leftDimChar.{w} ℂ C (SplitK0.of S.repr) =
        (frobeniusPerronDim.{w} ℂ S.repr : ℂ) := by
      rw [SplitK0.leftDimChar_of, endAlgEquivOfSimple_apply_eq_iff]
      exact hsimple S.repr
    rw [← SplitK0.leftDimChar_of_smul_id.{w} ℂ X, frobeniusPerronDim_eq_sum,
      SplitK0.of_eq_sum, map_finsuppSum, Finsupp.sum_fintype _ _ (by simp)]
    simp [hscalar, Finset.sum_smul]
  refine ⟨P, ⟨hall, ?_⟩, fun Q hQ ↦ ?_⟩
  · let _ := P
    exact sphericalCategory_of_leftDim_eq_frobeniusPerronDim fun X _ ↦ hall X
  · exact PivotalCategory.eq_of_leftDim_eq_frobeniusPerronDim
      (fun X _ ↦ hQ.1 X) (fun X _ ↦ hall X)

end TauCeti
