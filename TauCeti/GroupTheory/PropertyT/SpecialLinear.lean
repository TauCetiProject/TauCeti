/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Instances.Int
public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Action

import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.SpecialLinear
import TauCeti.GroupTheory.PropertyT.Foelner
import TauCeti.MeasureTheory.Constructions.BorelSpace.OnePoint
import TauCeti.RepresentationTheory.Continuous.Unitary.SpectralMeasure
import TauCeti.Topology.Algebra.PontryaginDual
import TauCeti.Topology.Compactification.OnePoint.InvariantMeasure

/-!
# Relative property (T) for `ℤ² ⋊ G` and Burger's theorem

Let `G` act on `ℤ²` through a homomorphism `ψ : G →* SL(2, ℤ)` and `TauCeti.slTwoAction`, forming
the semidirect product `ℤ² ⋊ G`. This file proves **Burger's characterization** of relative property
(T) for the normal subgroup `ℤ²` and deduces the **Kazhdan–Margulis theorem** for
`(ℤ² ⋊ SL(2, ℤ), ℤ²)`.

Pairs `(ℤ² ⋊ G, ℤ²)` with `G ≤ SL(2, ℤ)` nonamenable provide the fundamental linear examples of
relative property (T) without ambient property (T) (for instance when `G` is a nonabelian free
subgroup of `SL(2, ℤ)`), underpinning rigidity phenomena in ergodic theory and in the deformation–
rigidity theory of group von Neumann algebras.

## Main results

* `Subgroup.not_relativePropertyT_range_inl_of_amenable`: if `N` and `G` are discrete amenable
  groups with `N` infinite, `N` does not have relative property (T) in `N ⋊ G`.
* `Subgroup.relativePropertyT_range_inl_of_not_amenable`: if `ψ : G →* SL(2, ℤ)` is injective and
  `G` is not amenable, `(ℤ² ⋊ G, ℤ²)` has relative property (T) in every Hilbert-space universe.
* `Subgroup.relativePropertyT_range_inl_iff_not_amenable`: for a discrete group `G` embedding in
  `SL(2, ℤ)`, `(ℤ² ⋊ G, ℤ²)` has relative property (T) if and only if `G` is not amenable.
* `Subgroup.relativePropertyT_inl_of_not_amenable`,
  `Subgroup.relativePropertyT_inl_iff_not_amenable`: Burger's theorem and characterization for
  subgroups `G ≤ SL(2, ℤ)`.
* `Subgroup.relativePropertyT_inl_slTwo`: the Kazhdan–Margulis theorem that
  `(ℤ² ⋊ SL(2, ℤ), ℤ²)` has relative property (T).

## References

* M. Burger, *Kazhdan constants for `SL(3, ℤ)`*, J. Reine Angew. Math. 413 (1991), 36–67,
  Proposition 3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Example 1.7.4 and Proposition 4.2.2.
* C. Anantharaman, S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

open Filter Matrix MeasureTheory Multiplicative OnePoint SemidirectProduct Set Topology
open scoped BoundedContinuousFunction InnerProductSpace MatrixGroups OnePoint

namespace Subgroup

universe u v w

/-! ### Torus model of the Pontryagin dual of `ℤ²` -/

-- Under `TauCeti.piCircleEquivPontryaginDualPiInt` and `AddCircle.homeomorphCircle`, the dual of
-- `ℤ²` identifies with `(ℝ / ℤ)²`, transporting dual pullback along `slTwoAction g` to the
-- transpose linear action `transposeAct g`.

private noncomputable instance :
    MeasurableSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
  borel _

private instance : BorelSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ))) := ⟨rfl⟩

section DualTorus

private abbrev Torus2 : Type := Fin 2 → AddCircle (1 : ℝ)

private instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private noncomputable def torusHomeomorphDual :
    Torus2 ≃ₜ PontryaginDual (Multiplicative (Fin 2 → ℤ)) :=
  (Homeomorph.piCongrRight fun _ ↦ AddCircle.homeomorphCircle one_ne_zero).trans
    (Homeomorph.ofClass (TauCeti.piCircleEquivPontryaginDualPiInt (ι := Fin 2)))

private theorem torusHomeomorphDual_apply (u : Torus2) (v : Fin 2 → ℤ) :
    torusHomeomorphDual u (ofAdd v) = AddCircle.toCircle (∑ i : Fin 2, v i • u i) := by
  simp only [torusHomeomorphDual, Homeomorph.trans_apply, Homeomorph.coe_ofClass,
    TauCeti.piCircleEquivPontryaginDualPiInt_apply_apply, toAdd_ofAdd,
    Homeomorph.piCongrRight_apply, AddCircle.homeomorphCircle_apply,
    Fin.prod_univ_two, Fin.sum_univ_two, ← AddCircle.toCircle_zsmul, ← AddCircle.toCircle_add]

private theorem torusHomeomorphDual_zero : torusHomeomorphDual 0 = 1 :=
  PontryaginDual.ext fun x ↦ by
    rw [← ofAdd_toAdd x, torusHomeomorphDual_apply]
    simp

private def transposeAct (g : SL(2, ℤ)) (u : Torus2) : Torus2 :=
  fun i ↦ ∑ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℤ) j i • u j

private theorem continuous_transposeAct (g : SL(2, ℤ)) : Continuous (transposeAct g) := by
  refine continuous_pi fun i ↦ ?_
  dsimp only [transposeAct]
  simp_rw [Fin.sum_univ_two]
  exact ((continuous_apply 0).zsmul _).add ((continuous_apply 1).zsmul _)

private theorem symm_map_slTwoAction_eq_transposeAct (g : SL(2, ℤ))
    (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) :
    torusHomeomorphDual.symm
        (PontryaginDual.map
          ⟨(TauCeti.slTwoAction g).toMonoidHom, continuous_of_discreteTopology⟩ χ) =
      transposeAct g (torusHomeomorphDual.symm χ) := by
  apply torusHomeomorphDual.injective
  rw [torusHomeomorphDual.apply_symm_apply]
  apply PontryaginDual.ext
  intro x
  set u := torusHomeomorphDual.symm χ
  have hχ : χ = torusHomeomorphDual u := (torusHomeomorphDual.apply_symm_apply χ).symm
  have hsl : TauCeti.slTwoAction g (ofAdd (toAdd x)) =
      ofAdd ((g : Matrix (Fin 2) (Fin 2) ℤ).mulVec (toAdd x)) := by
    rw [← ofAdd_toAdd (TauCeti.slTwoAction g _), TauCeti.slTwoAction_apply_eq_mulVec, toAdd_ofAdd]
  have hlhs :
      (PontryaginDual.map ⟨(TauCeti.slTwoAction g).toMonoidHom, continuous_of_discreteTopology⟩ χ)
          x = torusHomeomorphDual u (TauCeti.slTwoAction g (ofAdd (toAdd x))) := by
    conv_lhs => rw [hχ, ← ofAdd_toAdd x]
    rfl
  rw [hlhs, hsl, torusHomeomorphDual_apply]
  conv_rhs => rw [← ofAdd_toAdd x, torusHomeomorphDual_apply]
  congr 1
  simp only [transposeAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    add_zsmul, zsmul_add, ← mul_zsmul, mul_comm (toAdd x _)]
  abel

end DualTorus

/-! ### Fundamental-domain lift and local equivariance into `OnePoint ℝ` -/

-- Lifting `AddCircle 1` to `[-1/2, 1/2)` and projecting `(x₀, x₁) ∈ ℝ² \ {0}` to `-x₁ / x₀` in
-- `OnePoint ℝ` intertwines the contragredient action `(A⁻¹)ᵀ` near `0 ∈ (ℝ / ℤ)²` with the
-- standard Möbius action of `A` on `OnePoint ℝ`.

section ProjectiveProjection

private noncomputable def torusRep (z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-1 / 2) z : ℝ)

private theorem measurable_torusRep : Measurable torusRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) (-1 / 2)).measurable

private theorem coe_torusRep (z : AddCircle (1 : ℝ)) : (torusRep z : AddCircle (1 : ℝ)) = z :=
  AddCircle.coe_equivIco

private theorem torusRep_coe_of_abs_lt {t : ℝ} (ht : |t| < 1 / 2) :
    torusRep (t : AddCircle (1 : ℝ)) = t := by
  have hmem : t ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) :=
    ⟨by linarith [(abs_lt.mp ht).1], by linarith [(abs_lt.mp ht).2]⟩
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem)

private theorem torusRep_eq_zero_iff {z : AddCircle (1 : ℝ)} : torusRep z = 0 ↔ z = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← coe_torusRep z, h, QuotientAddGroup.mk_zero]
  · rw [h, ← QuotientAddGroup.mk_zero]
    exact torusRep_coe_of_abs_lt (by norm_num)

private noncomputable def projLine (x : Fin 2 → ℝ) : OnePoint ℝ :=
  if x 0 = 0 then ∞ else ((-x 1 / x 0 : ℝ) : OnePoint ℝ)

private theorem measurable_projLine : Measurable projLine :=
  Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
    measurable_const
    (OnePoint.measurable_coe.comp ((measurable_pi_apply 1).neg.div (measurable_pi_apply 0)))

private theorem projLine_transpose_inv (A : SL(2, ℝ)) {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    projLine (fun i ↦ ∑ j : Fin 2, ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) j i * x j) =
      (A : GL (Fin 2) ℝ) • projLine x := by
  have hinv : ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  set y : Fin 2 → ℝ :=
    fun i ↦ ∑ j : Fin 2, ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) j i * x j
  have hy0 : y 0 = A 1 1 * x 0 - A 1 0 * x 1 := by
    simp only [y, Fin.sum_univ_two, hinv]; simp; ring
  have hy1 : y 1 = -A 0 1 * x 0 + A 0 0 * x 1 := by
    simp only [y, Fin.sum_univ_two, hinv]; simp
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := fun h1 ↦ hx (funext fun i ↦ by fin_cases i <;> assumption)
    have hpx : projLine x = ∞ := by simp [projLine, hx0]
    rw [hpx, smul_infty_eq_ite]
    split_ifs with hc
    · have hy0' : y 0 = 0 := by
        have hc' : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := hc
        rw [hy0, hx0, hc']; ring
      simp [projLine, hy0']
    · have hc' : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0 := hc
      have hy0' : y 0 ≠ 0 := by
        rw [hy0, hx0, mul_zero, zero_sub, neg_ne_zero]
        exact mul_ne_zero hc' hx1
      have hpy : projLine y = ((-y 1 / y 0 : ℝ) : OnePoint ℝ) := by simp [projLine, hy0']
      rw [hpy, OnePoint.coe_eq_coe, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hy0, hy1, hx0]
      field_simp [hc', hx1]
      ring
  · let t : ℝ := -x 1 / x 0
    have hx1 : x 1 = -x 0 * t := by dsimp [t]; field_simp [hx0]
    have hy0_eq : y 0 = x 0 * (A 1 0 * t + A 1 1) := by rw [hy0, hx1]; ring
    have hy1_eq : -y 1 = x 0 * (A 0 0 * t + A 0 1) := by rw [hy1, hx1]; ring
    have hpx : projLine x = (t : OnePoint ℝ) := by simp [projLine, hx0, t]
    rw [hpx, smul_some_eq_ite]
    split_ifs with hden
    · have hy0' : y 0 = 0 := by
        have hden' : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * t + A 1 1 = 0 := hden
        rw [hy0_eq, hden', mul_zero]
      simp [projLine, hy0']
    · have hden' : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * t + A 1 1 ≠ 0 := hden
      have hy0' : y 0 ≠ 0 := by rw [hy0_eq]; exact mul_ne_zero hx0 hden'
      have hpy : projLine y = ((-y 1 / y 0 : ℝ) : OnePoint ℝ) := by simp [projLine, hy0']
      rw [hpy, OnePoint.coe_eq_coe, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        hy1_eq, hy0_eq, mul_div_mul_left _ _ hx0]

private noncomputable def torusProj (u : Torus2) : OnePoint ℝ :=
  projLine fun i ↦ torusRep (u i)

private theorem measurable_torusProj : Measurable torusProj :=
  measurable_projLine.comp
    (measurable_pi_iff.mpr fun i ↦ measurable_torusRep.comp (measurable_pi_apply i))

private theorem exists_delta_torusProj_transposeAct_inv (g : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ u : Torus2, u ≠ 0 → (∀ i, |torusRep (u i)| < δ) →
      torusProj (transposeAct g⁻¹ u) = SpecialLinearGroup.mapGL ℝ g • torusProj u := by
  let h : SL(2, ℤ) := g⁻¹
  let M : ℝ := |(h 0 0 : ℝ)| + |(h 0 1 : ℝ)| + |(h 1 0 : ℝ)| + |(h 1 1 : ℝ)| + 1
  have hM1 : 1 ≤ M := by
    dsimp [M]
    linarith [abs_nonneg (h 0 0 : ℝ), abs_nonneg (h 0 1 : ℝ),
      abs_nonneg (h 1 0 : ℝ), abs_nonneg (h 1 1 : ℝ)]
  refine ⟨1 / (4 * M), by positivity, ?_, fun u hu hδ ↦ ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hrep_ne : (fun i ↦ torusRep (u i)) ≠ 0 := fun h0 ↦
    hu (funext fun i ↦ torusRep_eq_zero_iff.mp (congrFun h0 i))
  have hrep_act (i : Fin 2) :
      torusRep (transposeAct h u i) = ∑ j : Fin 2, (h j i : ℝ) * torusRep (u j) := by
    let s : ℝ := ∑ j : Fin 2, (h j i : ℝ) * torusRep (u j)
    have hcoe : (s : AddCircle (1 : ℝ)) = transposeAct h u i := by
      dsimp [s, transposeAct]
      rw [Fin.sum_univ_two, Fin.sum_univ_two, QuotientAddGroup.mk_add]
      rw [← zsmul_eq_mul, QuotientAddGroup.mk_zsmul, coe_torusRep]
      rw [← zsmul_eq_mul, QuotientAddGroup.mk_zsmul, coe_torusRep]
    have hs_lt : |s| < 1 / 2 := by
      have hsum_coef : |(h 0 i : ℝ)| + |(h 1 i : ℝ)| ≤ M := by
        fin_cases i <;> dsimp [M] <;>
          linarith [abs_nonneg (h 0 0 : ℝ), abs_nonneg (h 0 1 : ℝ),
            abs_nonneg (h 1 0 : ℝ), abs_nonneg (h 1 1 : ℝ)]
      have htri : |s| ≤ |(h 0 i : ℝ)| * |torusRep (u 0)| +
          |(h 1 i : ℝ)| * |torusRep (u 1)| := by
        dsimp [s]
        rw [Fin.sum_univ_two, ← abs_mul, ← abs_mul]
        exact abs_add_le _ _
      have hstep : |(h 0 i : ℝ)| * |torusRep (u 0)| + |(h 1 i : ℝ)| * |torusRep (u 1)| ≤
          (|(h 0 i : ℝ)| + |(h 1 i : ℝ)|) * (1 / (4 * M)) := by
        calc |(h 0 i : ℝ)| * |torusRep (u 0)| + |(h 1 i : ℝ)| * |torusRep (u 1)|
            ≤ |(h 0 i : ℝ)| * (1 / (4 * M)) + |(h 1 i : ℝ)| * (1 / (4 * M)) :=
              add_le_add (mul_le_mul_of_nonneg_left (hδ 0).le (abs_nonneg _))
                (mul_le_mul_of_nonneg_left (hδ 1).le (abs_nonneg _))
          _ = (|(h 0 i : ℝ)| + |(h 1 i : ℝ)|) * (1 / (4 * M)) := by ring
      have hbound : |s| ≤ M * (1 / (4 * M)) :=
        htri.trans (hstep.trans (mul_le_mul_of_nonneg_right hsum_coef (by positivity)))
      have hquarter : M * (1 / (4 * M)) = 1 / 4 := by
        field_simp [(by positivity : 0 < M).ne']
      linarith
    rw [← hcoe]
    exact torusRep_coe_of_abs_lt hs_lt
  let A : SL(2, ℝ) := SpecialLinearGroup.map (algebraMap ℤ ℝ) g
  have hAinv : (A⁻¹ : SL(2, ℝ)) = SpecialLinearGroup.map (algebraMap ℤ ℝ) h :=
    (map_inv (SpecialLinearGroup.map (algebraMap ℤ ℝ)) g).symm
  calc torusProj (transposeAct g⁻¹ u)
      = projLine (fun i ↦ torusRep (transposeAct h u i)) := rfl
    _ = projLine
          (fun i ↦ ∑ j : Fin 2,
            ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) j i * torusRep (u j)) := by
        congr 1
        ext i
        rw [hrep_act i, hAinv]
        rfl
    _ = SpecialLinearGroup.mapGL ℝ g • torusProj u := projLine_transpose_inv A hrep_ne

end ProjectiveProjection

/-! ### Spectral concentration and pushforward almost-invariance -/

-- Small displacement under the standard generators of `ℤ²` concentrates the torus spectral
-- measure near `0 ∈ (ℝ / ℤ)²`, while small displacement under `inr g⁻¹` makes the spectral
-- measure almost invariant under `transposeAct (ψ g⁻¹)`.

section SpectralEstimates

private theorem exists_pos_le_norm_toCircle_sub_one_sq {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : AddCircle (1 : ℝ), δ ≤ |torusRep z| →
      c ≤ ‖(AddCircle.toCircle z : ℂ) - 1‖ ^ 2 := by
  let U : Set (AddCircle (1 : ℝ)) := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo (-δ) δ
  have hU_open : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hK_compact : IsCompact Uᶜ := hU_open.isClosed_compl.isCompact
  have hsub : {z : AddCircle (1 : ℝ) | δ ≤ |torusRep z|} ⊆ Uᶜ := by
    rintro _ hmem ⟨t, ht, rfl⟩
    have ht_half : |t| < 1 / 2 := (abs_lt.mpr ht).trans_le hδ1
    rw [mem_ofPred_eq, torusRep_coe_of_abs_lt ht_half] at hmem
    exact not_lt_of_ge hmem (abs_lt.mpr ht)
  have hne : Uᶜ.Nonempty := by
    refine ⟨(-1 / 2 : ℝ), hsub ?_⟩
    have hmem : (-1 / 2 : ℝ) ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) := ⟨le_rfl, by norm_num⟩
    have hrep_half : torusRep ((-1 / 2 : ℝ) : AddCircle (1 : ℝ)) = -1 / 2 :=
      congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem)
    rw [mem_ofPred_eq, hrep_half]
    have habs : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rwa [habs]
  let hfun : AddCircle (1 : ℝ) → ℝ := fun z ↦ ‖(AddCircle.toCircle z : ℂ) - 1‖ ^ 2
  have hcont : Continuous hfun :=
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).sub continuous_const).norm.pow 2
  obtain ⟨z₀, hz₀, hmin⟩ := hK_compact.exists_isMinOn hne hcont.continuousOn
  have hz₀_ne : z₀ ≠ 0 := fun h0 ↦
    hz₀ ⟨0, ⟨by linarith, hδ0⟩, by rw [h0, QuotientAddGroup.mk_zero]⟩
  have hc_pos : 0 < hfun z₀ := by
    refine sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr fun h1 ↦ hz₀_ne ?_))
    exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext (by simpa using h1))
  exact ⟨hfun z₀, hc_pos, fun z hz ↦ hmin (hsub hz)⟩

private theorem torus_diag_tail_toReal_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ)) H} (hπ : π.IsUnitary)
    {δ c : ℝ} (hc : 0 < c)
    (hchord : ∀ z : AddCircle (1 : ℝ), δ ≤ |torusRep z| →
      c ≤ ‖(AddCircle.toCircle z : ℂ) - 1‖ ^ 2)
    (ζ : H) (i : Fin 2) :
    ((Measure.map torusHomeomorphDual.symm ((π.spectralPVM hπ).diag ζ))
        {u : Torus2 | δ ≤ |torusRep (u i)|}).toReal ≤
      ‖π (ofAdd (Pi.single i 1)) ζ - ζ‖ ^ 2 / c := by
  let P := π.spectralPVM hπ
  let μ : Measure Torus2 := Measure.map torusHomeomorphDual.symm (P.diag ζ)
  let S : Set Torus2 := {u : Torus2 | δ ≤ |torusRep (u i)|}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_torusRep.comp (measurable_pi_apply i)))
  let q : Torus2 → ℝ := fun u ↦ ‖(AddCircle.toCircle (u i) : ℂ) - 1‖ ^ 2
  have hq_cont : Continuous q :=
    (((continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
      (continuous_apply i)).sub continuous_const).norm.pow 2
  have hq_int : Integrable q μ := hq_cont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace q)
  have hdisp : ‖π (ofAdd (Pi.single i 1)) ζ - ζ‖ ^ 2 = ∫ u, q u ∂μ := by
    set ei : Fin 2 → ℤ := Pi.single i 1
    let symb : TauCeti.BoundedBorelFunction (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
      TauCeti.BoundedBorelFunction.ofContinuousMap
        (PontryaginDual.evalBoundedContinuous ei).toContinuousMap - 1
    have happly : P.integral symb ζ = π (ofAdd ei) ζ - ζ := by simp [P, symb]
    rw [← happly, P.norm_sq_integral_apply]
    rw [integral_map torusHomeomorphDual.symm.measurable.aemeasurable hq_cont.aestronglyMeasurable]
    refine integral_congr_ae (.of_forall fun χ ↦ ?_)
    have hχ : χ (ofAdd ei) = AddCircle.toCircle (torusHomeomorphDual.symm χ i) := by
      conv_lhs => rw [← torusHomeomorphDual.apply_symm_apply χ]
      rw [torusHomeomorphDual_apply]
      congr 1
      fin_cases i <;> simp [ei]
    simp [symb, q, hχ]
  have hind_le : S.indicator (fun _ ↦ c) ≤ q := fun u ↦ by
    by_cases hu : u ∈ S
    · simpa [hu] using hchord (u i) hu
    · simp [hu, q]
  have hc_mul : c * (μ S).toReal ≤ ∫ u, q u ∂μ := by
    calc c * (μ S).toReal
        = ∫ u, S.indicator (fun _ : Torus2 ↦ c) u ∂μ := by
          rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm, Measure.real]
      _ ≤ ∫ u, q u ∂μ :=
          integral_mono ((integrable_const c).indicator hS) hq_int hind_le
  exact (le_div_iff₀ hc).mpr (by rw [mul_comm, hdisp]; exact hc_mul)

private theorem map_transposeAct_torus_spectralDiag {G : Type v} [Group G] (ψ : G →* SL(2, ℤ))
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) H}
    (hρ : ρ.IsUnitary) (g : G) (ζ : H) :
    Measure.map (transposeAct (ψ g⁻¹))
        (Measure.map torusHomeomorphDual.symm
          (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ρ (inr g⁻¹) ζ))) =
      Measure.map torusHomeomorphDual.symm
        (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ζ) := by
  rw [Measure.map_map (continuous_transposeAct _).measurable torusHomeomorphDual.symm.measurable]
  have hcomp : transposeAct (ψ g⁻¹) ∘ torusHomeomorphDual.symm =
      torusHomeomorphDual.symm ∘
        PontryaginDual.map ⟨(TauCeti.slTwoAction (ψ g⁻¹)).toMonoidHom,
          continuous_of_discreteTopology⟩ :=
    funext fun χ ↦ (symm_map_slTwoAction_eq_transposeAct (ψ g⁻¹) χ).symm
  rw [hcomp, ← Measure.map_map torusHomeomorphDual.symm.measurable
    (map_continuous (PontryaginDual.map _)).measurable]
  congr 1
  exact ρ.map_diag_spectralPVM_restrict_inl_apply_inr hρ g⁻¹ ζ

private theorem torus_spectralDiag_singleton_zero {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ)) H} (hπ : π.IsUnitary)
    (hinv : π.invariants = ⊥) (ζ : H) :
    (Measure.map torusHomeomorphDual.symm ((π.spectralPVM hπ).diag ζ)) {0} = 0 := by
  let P := π.spectralPVM hπ
  rw [Measure.map_apply torusHomeomorphDual.symm.measurable (measurableSet_singleton 0)]
  have hpre : torusHomeomorphDual.symm ⁻¹' ({0} : Set Torus2) = {1} := by
    ext χ
    simp [Homeomorph.symm_apply_eq, torusHomeomorphDual_zero]
  rw [hpre]
  have hproj0 : P.proj {1} (measurableSet_singleton 1) = 0 :=
    (π.spectralPVM_proj_singleton_one_eq_zero_iff hπ).mpr hinv
  have hreal0 : ((P.diag ζ) {1}).toReal = 0 := by
    rw [← P.norm_sq_proj_apply {1} (measurableSet_singleton 1) ζ, hproj0]
    simp
  exact (ENNReal.toReal_eq_zero_iff _).mp hreal0 |>.resolve_right (measure_ne_top _ _)

private theorem abs_integral_torusProj_sub_transposeAct_le
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ)) H} (hπ : π.IsUnitary)
    (hinv : π.invariants = ⊥) (h : SL(2, ℤ)) (f : OnePoint ℝ →ᵇ ℝ) {δ c : ℝ} (hc : 0 < c)
    (hloc : ∀ w : Torus2, w ≠ 0 → (∀ i, |torusRep (w i)| < δ) →
      torusProj (transposeAct h⁻¹ w) = SpecialLinearGroup.mapGL ℝ h • torusProj w)
    (hchord : ∀ z : AddCircle (1 : ℝ), δ ≤ |torusRep z| →
      c ≤ ‖(AddCircle.toCircle z : ℂ) - 1‖ ^ 2)
    (ζ : H) {r : ℝ}
    (he0 : ‖π (ofAdd (Pi.single 0 1)) ζ - ζ‖ ≤ r)
    (he1 : ‖π (ofAdd (Pi.single 1 1)) ζ - ζ‖ ≤ r) :
    |(∫ w, f (SpecialLinearGroup.mapGL ℝ h • torusProj w)
          ∂(Measure.map torusHomeomorphDual.symm ((π.spectralPVM hπ).diag ζ))) -
        ∫ w, f (torusProj (transposeAct h⁻¹ w))
          ∂(Measure.map torusHomeomorphDual.symm ((π.spectralPVM hπ).diag ζ))| ≤
      4 * ‖f‖ / c * r ^ 2 := by
  set μζ : Measure Torus2 := Measure.map torusHomeomorphDual.symm ((π.spectralPVM hπ).diag ζ)
  have : IsFiniteMeasure μζ := Measure.isFiniteMeasure_map _ _
  let F1 : Torus2 → ℝ := fun w ↦ f (SpecialLinearGroup.mapGL ℝ h • torusProj w)
  let F2 : Torus2 → ℝ := fun w ↦ f (torusProj (transposeAct h⁻¹ w))
  have hF1_meas : Measurable F1 := f.continuous.measurable.comp
    ((continuous_const_smul _).measurable.comp measurable_torusProj)
  have hF2_meas : Measurable F2 := f.continuous.measurable.comp
    (measurable_torusProj.comp (continuous_transposeAct _).measurable)
  let S0 : Set Torus2 := {w | δ ≤ |torusRep (w 0)|}
  let S1 : Set Torus2 := {w | δ ≤ |torusRep (w 1)|}
  let Bset : Set Torus2 := ({0} : Set Torus2) ∪ S0 ∪ S1
  have hS0 : MeasurableSet S0 := measurableSet_le measurable_const
    (continuous_abs.measurable.comp (measurable_torusRep.comp (measurable_pi_apply 0)))
  have hS1 : MeasurableSet S1 := measurableSet_le measurable_const
    (continuous_abs.measurable.comp (measurable_torusRep.comp (measurable_pi_apply 1)))
  have hBset : MeasurableSet Bset := ((measurableSet_singleton 0).union hS0).union hS1
  have hF1_int : Integrable F1 μζ := .of_bound hF1_meas.aestronglyMeasurable ‖f‖
    (.of_forall fun _ ↦ f.norm_coe_le_norm _)
  have hF2_int : Integrable F2 μζ := .of_bound hF2_meas.aestronglyMeasurable ‖f‖
    (.of_forall fun _ ↦ f.norm_coe_le_norm _)
  have hdom : ∀ w, ‖F1 w - F2 w‖ ≤ Bset.indicator (fun _ ↦ 2 * ‖f‖) w := fun w ↦ by
    by_cases hw : w ∈ Bset
    · simp only [hw, indicator_of_mem]
      calc ‖F1 w - F2 w‖ ≤ ‖F1 w‖ + ‖F2 w‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
    · have hw0 : w ≠ 0 := fun h0 ↦ hw (Or.inl (Or.inl h0))
      have hw_δ (i : Fin 2) : |torusRep (w i)| < δ := by
        fin_cases i
        · exact lt_of_not_ge fun hge ↦ hw (Or.inl (Or.inr hge))
        · exact lt_of_not_ge fun hge ↦ hw (Or.inr hge)
      have heq : F1 w = F2 w := by dsimp [F1, F2]; rw [hloc w hw0 hw_δ]
      simp [hw, heq]
  have hμB_le : (μζ Bset).toReal ≤ 2 * (r ^ 2 / c) := by
    have hle_enn : μζ Bset ≤ μζ S0 + μζ S1 := by
      calc μζ Bset ≤ μζ ({0} ∪ S0) + μζ S1 := measure_union_le _ _
        _ ≤ (μζ {0} + μζ S0) + μζ S1 := add_le_add (measure_union_le _ _) le_rfl
        _ = μζ S0 + μζ S1 := by rw [torus_spectralDiag_singleton_zero hπ hinv ζ, zero_add]
    have hle_real : (μζ Bset).toReal ≤ (μζ S0).toReal + (μζ S1).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)).mpr hle_enn
    have ht0 : (μζ S0).toReal ≤ r ^ 2 / c :=
      (torus_diag_tail_toReal_le hπ hc hchord ζ 0).trans
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) he0 2) hc.le)
    have ht1 : (μζ S1).toReal ≤ r ^ 2 / c :=
      (torus_diag_tail_toReal_le hπ hc hchord ζ 1).trans
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) he1 2) hc.le)
    linarith
  rw [← integral_sub hF1_int hF2_int, ← Real.norm_eq_abs]
  calc ‖∫ w, (F1 w - F2 w) ∂μζ‖
      ≤ ∫ w, ‖F1 w - F2 w‖ ∂μζ := norm_integral_le_integral_norm _
    _ ≤ ∫ w, Bset.indicator (fun _ ↦ 2 * ‖f‖) w ∂μζ :=
        integral_mono (hF1_int.sub hF2_int).norm ((integrable_const _).indicator hBset) hdom
    _ = 2 * ‖f‖ * (μζ Bset).toReal := by
        rw [integral_indicator_const _ hBset, smul_eq_mul, mul_comm, Measure.real]
    _ ≤ 2 * ‖f‖ * (2 * (r ^ 2 / c)) := mul_le_mul_of_nonneg_left hμB_le (by positivity)
    _ = 4 * ‖f‖ / c * r ^ 2 := by ring

private theorem abs_integral_torusProj_smul_sub_le {G : Type v} [Group G] (ψ : G →* SL(2, ℤ))
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) H}
    (hρ : ρ.IsUnitary) (hinv : (ρ.restrict inl).invariants = ⊥)
    (g : G) (f : OnePoint ℝ →ᵇ ℝ) {δ c : ℝ} (hc : 0 < c)
    (hloc : ∀ w : Torus2, w ≠ 0 → (∀ i, |torusRep (w i)| < δ) →
      torusProj (transposeAct (ψ g)⁻¹ w) = SpecialLinearGroup.mapGL ℝ (ψ g) • torusProj w)
    (hchord : ∀ z : AddCircle (1 : ℝ), δ ≤ |torusRep z| →
      c ≤ ‖(AddCircle.toCircle z : ℂ) - 1‖ ^ 2)
    {ζ : H} (hζ : ‖ζ‖ = 1) {r : ℝ}
    (hg : ‖ρ (inr g⁻¹) ζ - ζ‖ ≤ r)
    (he0 : ‖ρ (inl (ofAdd (Pi.single 0 1))) ζ - ζ‖ ≤ r)
    (he1 : ‖ρ (inl (ofAdd (Pi.single 1 1))) ζ - ζ‖ ≤ r) :
    |(∫ y, f (SpecialLinearGroup.mapGL ℝ (ψ g) • y)
          ∂(Measure.map torusProj
            (Measure.map torusHomeomorphDual.symm
              (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ζ)))) -
        ∫ y, f y
          ∂(Measure.map torusProj
            (Measure.map torusHomeomorphDual.symm
              (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ζ)))| ≤
      2 * ‖f‖ * r + 4 * ‖f‖ / c * r ^ 2 := by
  set P := (ρ.restrict inl).spectralPVM (hρ.restrict _)
  let η : H := ρ (inr g⁻¹) ζ
  have hη : ‖η‖ = 1 := by simp [η, hρ.norm_map, hζ]
  set μζ : Measure Torus2 := Measure.map torusHomeomorphDual.symm (P.diag ζ)
  set μη : Measure Torus2 := Measure.map torusHomeomorphDual.symm (P.diag η)
  let F1 : Torus2 → ℝ := fun w ↦ f (SpecialLinearGroup.mapGL ℝ (ψ g) • torusProj w)
  let F2 : Torus2 → ℝ := fun w ↦ f (torusProj (transposeAct (ψ g)⁻¹ w))
  have hF2_meas : Measurable F2 := f.continuous.measurable.comp
    (measurable_torusProj.comp (continuous_transposeAct _).measurable)
  have hint_lhs : ∫ y, f (SpecialLinearGroup.mapGL ℝ (ψ g) • y) ∂(Measure.map torusProj μζ) =
      ∫ w, F1 w ∂μζ :=
    integral_map measurable_torusProj.aemeasurable
      (f.continuous.comp (continuous_const_smul _)).aestronglyMeasurable
  have hint_rhs : ∫ y, f y ∂(Measure.map torusProj μζ) = ∫ w, F2 w ∂μη := by
    have hequiv : Measure.map (transposeAct (ψ g⁻¹)) μη = μζ :=
      map_transposeAct_torus_spectralDiag ψ hρ g ζ
    rw [integral_map measurable_torusProj.aemeasurable f.continuous.aestronglyMeasurable, ← hequiv]
    have hf_aesm : AEStronglyMeasurable (fun x ↦ f (torusProj x))
        (Measure.map (transposeAct (ψ g⁻¹)) μη) :=
      (f.continuous.measurable.comp measurable_torusProj).aestronglyMeasurable
    rw [integral_map (continuous_transposeAct (ψ g⁻¹)).measurable.aemeasurable hf_aesm, map_inv]
  have hstep1 : |∫ w, F2 w ∂μζ - ∫ w, F2 w ∂μη| ≤ 2 * ‖f‖ * r := by
    rw [integral_map torusHomeomorphDual.symm.measurable.aemeasurable hF2_meas.aestronglyMeasurable,
      integral_map torusHomeomorphDual.symm.measurable.aemeasurable hF2_meas.aestronglyMeasurable]
    let symb : TauCeti.BoundedBorelFunction (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
      TauCeti.BoundedBorelFunction.ofFunction (fun χ ↦ (F2 (torusHomeomorphDual.symm χ) : ℂ))
        (Complex.continuous_ofReal.measurable.comp
          (hF2_meas.comp torusHomeomorphDual.symm.measurable))
        ⟨‖f‖, norm_nonneg f, fun _ ↦ by simpa [F2, Real.norm_eq_abs] using f.norm_coe_le_norm _⟩
    have hsymb (ξ : H) : ((∫ χ, F2 (torusHomeomorphDual.symm χ) ∂(P.diag ξ) : ℝ) : ℂ) =
        ∫ χ, symb χ ∂(P.diag ξ) := by
      rw [← integral_complex_ofReal]
      simp [symb]
    calc |∫ χ, F2 (torusHomeomorphDual.symm χ) ∂(P.diag ζ) -
            ∫ χ, F2 (torusHomeomorphDual.symm χ) ∂(P.diag η)|
        = ‖∫ χ, symb χ ∂(P.diag ζ) - ∫ χ, symb χ ∂(P.diag η)‖ := by
            rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, hsymb, hsymb]
      _ ≤ ‖f‖ * (‖ζ‖ + ‖η‖) * ‖ζ - η‖ := P.norm_integral_diag_sub_le (norm_nonneg f)
            (fun _ ↦ by simpa [symb, F2, Real.norm_eq_abs] using f.norm_coe_le_norm _) ζ η
      _ ≤ 2 * ‖f‖ * r := by
          rw [hζ, hη, norm_sub_rev]
          have : ‖f‖ * (1 + 1) * ‖η - ζ‖ = 2 * ‖f‖ * ‖η - ζ‖ := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hg (by positivity)
  have hstep2 : |∫ w, F1 w ∂μζ - ∫ w, F2 w ∂μζ| ≤ 4 * ‖f‖ / c * r ^ 2 :=
    abs_integral_torusProj_sub_transposeAct_le (hρ.restrict _) hinv (ψ g) f hc hloc hchord ζ he0 he1
  rw [hint_lhs, hint_rhs]
  calc |∫ w, F1 w ∂μζ - ∫ w, F2 w ∂μη|
      = |(∫ w, F1 w ∂μζ - ∫ w, F2 w ∂μζ) + (∫ w, F2 w ∂μζ - ∫ w, F2 w ∂μη)| := by ring_nf
    _ ≤ |∫ w, F1 w ∂μζ - ∫ w, F2 w ∂μζ| + |∫ w, F2 w ∂μζ - ∫ w, F2 w ∂μη| := abs_add_le _ _
    _ ≤ 4 * ‖f‖ / c * r ^ 2 + 2 * ‖f‖ * r := add_le_add hstep2 hstep1
    _ = 2 * ‖f‖ * r + 4 * ‖f‖ / c * r ^ 2 := add_comm _ _

end SpectralEstimates

/-! ### Burger's theorem and Kazhdan–Margulis -/

/-- When both `N` and `G` are discrete amenable groups in universe-small form and `N` is infinite,
the normal subgroup `N` in `N ⋊ G` does not have relative property (T). -/
theorem not_relativePropertyT_range_inl_of_amenable {N : Type w} {G : Type v}
    [Group N] [Infinite N] [TopologicalSpace N] [DiscreteTopology N] [TauCeti.Amenable N]
    [Small.{u} N]
    [Group G] [TopologicalSpace G] [DiscreteTopology G] [TauCeti.Amenable G] [Small.{u} G]
    (φ : G →* MulAut N) :
    ¬ (inl (N := N) (G := G) (φ := φ)).range.RelativePropertyT.{u} := by
  let : TopologicalSpace (N ⋊[φ] G) := ⊥
  have : DiscreteTopology (N ⋊[φ] G) := ⟨rfl⟩
  have : TauCeti.Amenable (N ⋊[φ] G) :=
    TauCeti.Amenable.of_ker_le_range inl rightHom fun x hx ↦ by
      rw [MonoidHom.mem_ker] at hx
      exact ⟨x.left, SemidirectProduct.ext (by simp) (by simpa using hx.symm)⟩
  have : Small.{u} (N ⋊[φ] G) :=
    small_of_injective (f := fun x : N ⋊[φ] G ↦ (x.left, x.right)) fun x y h ↦
      SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have : Infinite (inl (N := N) (G := G) (φ := φ)).range :=
    Infinite.of_injective (fun n : N ↦ ⟨inl n, n, rfl⟩) fun a b h ↦
      SemidirectProduct.inl_injective (congrArg Subtype.val h)
  exact not_relativePropertyT_of_amenable _

private theorem tendsto_integral_torusProj_smul_sub {G : Type v} [Group G] (ψ : G →* SL(2, ℤ))
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) H}
    (hρ : ρ.IsUnitary) (hinv : (ρ.restrict inl).invariants = ⊥)
    {ξ : Finset (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) × ℕ → H}
    (hξ_norm : ∀ p, ‖ξ p‖ = 1)
    (hξ_move : ∀ p, ∀ x ∈ p.1, ‖ρ x (ξ p) - ξ p‖ < 1 / ((p.2 : ℝ) + 1))
    (g : G) (f : OnePoint ℝ →ᵇ ℝ) :
    Tendsto (fun p ↦
      (∫ y, f (SpecialLinearGroup.mapGL ℝ (ψ g) • y)
          ∂(Measure.map torusProj
            (Measure.map torusHomeomorphDual.symm
              (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ξ p))))) -
        ∫ y, f y
          ∂(Measure.map torusProj
            (Measure.map torusHomeomorphDual.symm
              (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ξ p)))))
      atTop (𝓝 0) := by
  classical
  obtain ⟨δ, hδ0, hδ1, hloc⟩ := exists_delta_torusProj_transposeAct_inv (ψ g)
  obtain ⟨c, hc, hchord⟩ := exists_pos_le_norm_toCircle_sub_one_sq hδ0 hδ1
  let F₀ : Finset (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) :=
    {inr g⁻¹, inl (ofAdd (Pi.single 0 1)), inl (ofAdd (Pi.single 1 1))}
  let r : Finset (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) × ℕ → ℝ :=
    fun p ↦ 1 / ((p.2 : ℝ) + 1)
  have hr_lim : Tendsto r atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp
      (tendsto_atTop_atTop.mpr fun n ↦ ⟨(∅, n), fun _ hp ↦ hp.2⟩)
  have hupper : Tendsto (fun p ↦ 2 * ‖f‖ * r p + 4 * ‖f‖ / c * r p ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun p ↦ 2 * ‖f‖ * r p) atTop (𝓝 0) := by
      simpa using hr_lim.const_mul (2 * ‖f‖)
    have h2 : Tendsto (fun p ↦ 4 * ‖f‖ / c * r p ^ 2) atTop (𝓝 0) := by
      simpa using (hr_lim.pow 2).const_mul (4 * ‖f‖ / c)
    simpa using h1.add h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hupper
  refine eventually_atTop.mpr ⟨(F₀, 0), fun p hp ↦ ?_⟩
  rw [Real.norm_eq_abs]
  exact abs_integral_torusProj_smul_sub_le ψ hρ hinv g f hc hloc hchord (hξ_norm p)
    (hξ_move p _ (hp.1 (by simp [F₀]))).le
    (hξ_move p _ (hp.1 (by simp [F₀]))).le
    (hξ_move p _ (hp.1 (by simp [F₀]))).le

/-- **Burger's theorem (general injective form).** If `ψ : G →* SL(2, ℤ)` is injective and `G` is
not amenable, then the normal subgroup `ℤ²` in `ℤ² ⋊ G` has relative property (T) in every
Hilbert-space universe. -/
theorem relativePropertyT_range_inl_of_not_amenable {G : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ψ : G →* SL(2, ℤ)) (hψ : Function.Injective ψ)
    (hG : ¬ TauCeti.Amenable G) :
    (inl (G := G) (φ := TauCeti.slTwoAction.comp ψ)).range.RelativePropertyT.{u} := by
  classical
  rw [relativePropertyT_def]
  intro H _ _ _ ρ hρ hAI
  by_contra hno
  have hinv : (ρ.restrict inl).invariants = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    exact hno ⟨v, hv0, fun ⟨_, a, rfl⟩ ↦ hv a⟩
  let P := (ρ.restrict inl).spectralPVM (hρ.restrict _)
  let ι := Finset (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp ψ] G) × ℕ
  choose ξ hξ_norm hξ_move using fun p : ι ↦
    (ρ.hasAlmostInvariantVectors_def.mp hAI) p.1 (1 / ((p.2 : ℝ) + 1)) (by positivity)
  have hprob (p : ι) :
      IsProbabilityMeasure
        (Measure.map torusProj (Measure.map torusHomeomorphDual.symm (P.diag (ξ p)))) := by
    have : IsProbabilityMeasure (P.diag (ξ p)) :=
      isProbabilityMeasure_iff_real.mpr (by simp [P, hξ_norm p])
    infer_instance
  let u : ι → ProbabilityMeasure (OnePoint ℝ) :=
    fun p ↦ ⟨Measure.map torusProj (Measure.map torusHomeomorphDual.symm (P.diag (ξ p))), hprob p⟩
  obtain ⟨μ, -, hμ⟩ := isCompact_univ.exists_mapClusterPt (u := u) (f := atTop) (by simp)
  -- Regularize the weak-* cluster point `μ` to obtain a genuine `G`-invariant Borel probability
  -- measure `ν` on `OnePoint ℝ`, contradicting nonamenability of `G` via Furstenberg's lemma.
  obtain ⟨ν, _, _, hμν⟩ := (μ : Measure (OnePoint ℝ)).exists_regular_eq_of_compactSpace
  have : IsProbabilityMeasure ν :=
    isProbabilityMeasure_iff_real.mpr
      (by simpa using (hμν (BoundedContinuousFunction.const (OnePoint ℝ) 1)).symm)
  have hν_inv (g : G) : Measure.map (SpecialLinearGroup.mapGL ℝ (ψ g) • ·) ν = ν := by
    set act : OnePoint ℝ → OnePoint ℝ := (SpecialLinearGroup.mapGL ℝ (ψ g) • ·)
    have hact : Continuous act := continuous_const_smul _
    have : (Measure.map act ν).Regular := by
      have := Measure.InnerRegularCompactLTTop.map_of_continuous hact (μ := ν)
      infer_instance
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    have hf_cont : Continuous (fun y ↦ f y) := f.continuous
    rw [integral_map hact.aemeasurable hf_cont.aestronglyMeasurable]
    simp_rw [← f.toBoundedContinuousFunction_apply]
    rw [← ContinuousMap.coe_mk act hact]
    simp_rw [← f.toBoundedContinuousFunction.compContinuous_apply ⟨act, hact⟩, ← hμν]
    exact ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hact hμ
      (tendsto_integral_torusProj_smul_sub ψ hρ hinv hξ_norm hξ_move g
        f.toBoundedContinuousFunction)
  exact hG (ψ.amenable_of_injective_slTwo_of_map_onePoint_measure_eq hψ hν_inv)

/-- **Burger's characterization (injective homomorphism form).** For a discrete group `G`
embedding in `SL(2, ℤ)` via `ψ`, the normal subgroup `ℤ²` in `ℤ² ⋊ G` has relative property (T)
if and only if `G` is not amenable. -/
theorem relativePropertyT_range_inl_iff_not_amenable {G : Type v} [Group G]
    [TopologicalSpace G] [DiscreteTopology G] (ψ : G →* SL(2, ℤ)) (hψ : Function.Injective ψ) :
    (inl (G := G) (φ := TauCeti.slTwoAction.comp ψ)).range.RelativePropertyT.{u} ↔
      ¬ TauCeti.Amenable G := by
  refine ⟨fun hT hAmen ↦ ?_, relativePropertyT_range_inl_of_not_amenable ψ hψ⟩
  have : Small.{u} G :=
    small_of_injective (f := fun g : G ↦ ULift.up.{u} (ψ g)) fun a b h ↦
      hψ (ULift.up_injective h)
  have : Small.{u} (Multiplicative (Fin 2 → ℤ)) :=
    small_of_injective (f := ULift.up.{u}) ULift.up_injective
  have : Infinite (Multiplicative (Fin 2 → ℤ)) :=
    Infinite.of_injective (fun n : ℤ ↦ ofAdd ![n, 0]) fun a b h ↦ by
      simpa using congrFun (ofAdd.injective h) 0
  exact not_relativePropertyT_range_inl_of_amenable (TauCeti.slTwoAction.comp ψ) hT

/-- **Burger's theorem for subgroups of `SL(2, ℤ)`.** If `G ≤ SL(2, ℤ)` is not amenable, then
the pair `(ℤ² ⋊ G, ℤ²)` has relative property (T). -/
theorem relativePropertyT_inl_of_not_amenable (G : Subgroup SL(2, ℤ))
    (hG : ¬ TauCeti.Amenable G) :
    (inl (G := G) (φ := TauCeti.slTwoAction.comp G.subtype)).range.RelativePropertyT.{u} :=
  relativePropertyT_range_inl_of_not_amenable G.subtype G.subtype_injective hG

/-- **Burger's characterization for subgroups of `SL(2, ℤ)`.** For any subgroup `G ≤ SL(2, ℤ)`,
the pair `(ℤ² ⋊ G, ℤ²)` has relative property (T) if and only if `G` is not amenable. -/
theorem relativePropertyT_inl_iff_not_amenable (G : Subgroup SL(2, ℤ)) :
    (inl (G := G) (φ := TauCeti.slTwoAction.comp G.subtype)).range.RelativePropertyT.{u} ↔
      ¬ TauCeti.Amenable G :=
  relativePropertyT_range_inl_iff_not_amenable G.subtype G.subtype_injective

/-- **Kazhdan–Margulis theorem.** The pair `(ℤ² ⋊ SL(2, ℤ), ℤ²)` has relative property (T). -/
theorem relativePropertyT_inl_slTwo :
    (inl (G := SL(2, ℤ)) (φ := TauCeti.slTwoAction)).range.RelativePropertyT.{u} :=
  relativePropertyT_range_inl_of_not_amenable (MonoidHom.id SL(2, ℤ)) Function.injective_id
    TauCeti.not_amenable_specialLinearGroup_fin_two

end Subgroup
