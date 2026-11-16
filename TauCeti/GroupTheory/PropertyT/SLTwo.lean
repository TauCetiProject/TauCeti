/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.FreeGroup
import TauCeti.GroupTheory.FreeGroup.Linear
import TauCeti.GroupTheory.HaagerupProperty.Amenable
import TauCeti.GroupTheory.HaagerupProperty.PropertyT
import TauCeti.RepresentationTheory.Continuous.Unitary.SpectralMeasure
import TauCeti.Topology.Compactification.OnePoint.InvariantMeasure

/-!
# Relative property (T) for `(ℤ² ⋊ G, ℤ²)`

For any group `G` and any homomorphism `φ : G →* SL(2, ℤ)` acting on `ℤ²` via
`TauCeti.slTwoAction.comp φ`, the pair `(ℤ² ⋊ G, ℤ²)` has relative property (T) if and only if
the image `φ.range ≤ SL(2, ℤ)` is nonamenable as a discrete group. In particular, this yields
Burger's theorem for nonamenable subgroups `G ≤ SL(2, ℤ)` and the Kazhdan–Margulis theorem that
`(ℤ² ⋊ SL(2, ℤ), ℤ²)` has relative property (T), while showing that the nonamenability hypothesis
cannot be dropped (for instance, relative property (T) fails for the unipotent transvection
subgroups of `SL(2, ℤ)`).

## Proof overview

For the forward direction (Burger's theorem), suppose a unitary representation `ρ` of
`ℤ² ⋊[slTwoAction.comp φ] G` has almost invariant unit vectors `ξ_p` and no nonzero `ℤ²`-invariant
vector. Let `P` be the spectral projection-valued measure of `ρ` restricted to `ℤ²` on the dual
torus `PontryaginDual (Multiplicative (Fin 2 → ℤ))`. Because there are no nonzero `ℤ²`-invariant
vectors, the diagonal spectral measures `P.diag ξ_p` give mass zero to the trivial character `1`.
Near `1`, the principal-argument coordinates `dualCoord : χ ↦ (arg (χ e₀), arg (χ e₁))` intertwine
the dual action of `g` with the contragredient linear action `(φ g)⁻¹ᵀ` on `ℝ²`, so composing with
`OnePoint.ofVec` intertwines the dual action with the Möbius action of `(φ g)⁻¹ᵀ` on the real
projective line `OnePoint ℝ` outside an arbitrarily small box around `1`. Almost invariance of `ξ_p`
under the generators of `ℤ²` concentrates `P.diag ξ_p` inside this box, while almost invariance
under `g` controls the pushforward perturbation. By compactness of
`ProbabilityMeasure (OnePoint ℝ)`, a weak-* cluster point of the pushed-forward probability
measures is a Borel probability measure on `OnePoint ℝ` invariant under `(φ g)⁻¹ᵀ` for every
`g : G`. By Furstenberg's lemma and amenability of projective-line stabilizers
(`MonoidHom.amenable_of_map_smul_onePoint_eq`), `φ.range` is amenable for every group topology.

For the converse, if `φ.range` is discrete amenable, then `ℤ² ⋊ φ.range` is a discrete amenable
extension of `ℤ²` by `φ.range`, so its lift to any universe `u` has the Haagerup property
(`TauCeti.hasHaagerupProperty_of_amenable`), whence every subgroup with relative property (T) in
universe `u` is finite (`TauCeti.HasHaagerupProperty.finite_of_relativePropertyT`), contradicting
the infinitude of `ℤ²`.

## Main results

* `Subgroup.relativePropertyT_inl_comp_of_not_amenable_range`: if `φ : G →* SL(2, ℤ)` has
  nonamenable image, then `(ℤ² ⋊ G, ℤ²)` has relative property (T).
* `Subgroup.not_relativePropertyT_inl_comp_of_amenable_range`: if `φ : G →* SL(2, ℤ)` has discrete
  amenable image, then `(ℤ² ⋊ G, ℤ²)` does not have relative property (T).
* `Subgroup.relativePropertyT_inl_comp_iff_not_amenable_range`: complete characterization for every
  homomorphism `φ : G →* SL(2, ℤ)`.
* `Subgroup.relativePropertyT_inl_comp_of_not_amenable`: Burger's theorem for an injective
  homomorphism `φ : G →* SL(2, ℤ)` from a nonamenable group.
* `Subgroup.relativePropertyT_inl_of_not_amenable` and
  `Subgroup.relativePropertyT_inl_iff_not_amenable`: Burger's theorem and its converse for
  subgroups `G : Subgroup SL(2, ℤ)`.
* `Subgroup.relativePropertyT_inl_slTwo`: the Kazhdan–Margulis theorem for `(ℤ² ⋊ SL(2, ℤ), ℤ²)`.
* `Subgroup.not_relativePropertyT_inl_range_transvectionHom`: failure of relative property (T) for
  the unipotent transvection subgroups of `SL(2, ℤ)`.

## References

* M. Burger, *Kazhdan constants for `SL(3, ℤ)`*, J. Reine Angew. Math. 413 (1991), 36–67.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), §1.4.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

noncomputable section

open BoundedContinuousFunction Filter Matrix MeasureTheory MulAction SemidirectProduct Set
  TauCeti Topology
open scoped InnerProductSpace MatrixGroups OnePoint

namespace Subgroup

universe u v

/-! ### Contragredient action and dual-torus coordinates -/

section SpectralProof

private local instance : MeasurableSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
  borel _

private local instance : BorelSpace (PontryaginDual (Multiplicative (Fin 2 → ℤ))) := ⟨rfl⟩

private local instance : MeasurableSpace (OnePoint ℝ) := borel _

private local instance : BorelSpace (OnePoint ℝ) := ⟨rfl⟩

/-- The contragredient automorphism `g ↦ (g⁻¹)ᵀ` on `SL(2, ℤ)`. -/
private def contragredient : SL(2, ℤ) →* SL(2, ℤ) where
  toFun g := g⁻¹.transpose
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_transpose, _root_.mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

private theorem contragredient_involutive : Function.Involutive contragredient := by
  intro g
  have hinv : g⁻¹.transpose⁻¹ = g.transpose := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    simp
  have happly (x : SL(2, ℤ)) : contragredient x = x⁻¹.transpose := rfl
  rw [happly, happly, hinv]
  ext i j
  rfl

private theorem contragredient_injective : Function.Injective contragredient :=
  contragredient_involutive.injective

/-- The standard basis vectors of `ℤ²`, viewed in `Multiplicative (Fin 2 → ℤ)`. -/
private def stdGen (i : Fin 2) : Multiplicative (Fin 2 → ℤ) :=
  Multiplicative.ofAdd (Pi.single i 1)

private theorem eq_prod_stdGen_zpow (v : Multiplicative (Fin 2 → ℤ)) :
    v = ∏ i : Fin 2, stdGen i ^ Multiplicative.toAdd v i := by
  apply Multiplicative.toAdd.injective
  ext k
  rw [toAdd_prod, Fin.sum_univ_two]
  fin_cases k <;> simp [stdGen]

/-- Principal-argument coordinates on the dual torus `PontryaginDual (Multiplicative (Fin 2 → ℤ))`,
taking values in `(-π, π]²`. -/
private def dualCoord (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (i : Fin 2) : ℝ :=
  Complex.arg (χ (stdGen i) : ℂ)

private theorem measurable_dualCoord : Measurable dualCoord := by
  rw [measurable_pi_iff]
  intro i
  exact Complex.measurable_arg.comp
    (TauCeti.PontryaginDual.continuous_coe_eval_const (stdGen i)).measurable

private theorem dualCoord_eq_zero_iff (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) :
    dualCoord χ = 0 ↔ χ = 1 := by
  constructor
  · intro h
    ext v
    have hgen (i : Fin 2) : χ (stdGen i) = 1 :=
      Circle.arg_eq_zero.1 (congrFun h i)
    rw [eq_prod_stdGen_zpow v, map_prod]
    simp [map_zpow, hgen]
  · rintro rfl
    ext i
    simp [dualCoord]

/-- Lower bound `(2 / π * t) ^ 2 ≤ ‖e^{it} - 1‖ ^ 2` for `|t| ≤ π`. -/
private theorem sq_mul_le_norm_sq_circle_exp_sub_one {t : ℝ} (ht : |t| ≤ Real.pi) :
    (2 / Real.pi * t) ^ 2 ≤ ‖(Circle.exp t : ℂ) - 1‖ ^ 2 := by
  have hcos := Real.cos_le_one_sub_mul_cos_sq ht
  have hnorm : ‖(Circle.exp t : ℂ) - 1‖ ^ 2 = 2 - 2 * Real.cos t := by
    rw [Circle.coe_exp, Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
      Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.cos_ofReal_im, Complex.mul_im, zero_add, Complex.one_im, sub_zero]
    have hcs := Real.cos_sq_add_sin_sq t
    nlinarith
  rw [hnorm]
  have hsq : (2 / Real.pi * t) ^ 2 = 2 * (2 / Real.pi ^ 2 * t ^ 2) := by ring
  linarith

private theorem sq_mul_dualCoord_le_norm_sq
    (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (i : Fin 2) :
    (2 / Real.pi * dualCoord χ i) ^ 2 ≤ ‖(χ (stdGen i) : ℂ) - 1‖ ^ 2 := by
  have hle : |dualCoord χ i| ≤ Real.pi :=
    abs_le.2 ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hexp := sq_mul_le_norm_sq_circle_exp_sub_one hle
  rwa [dualCoord, Circle.exp_arg] at hexp

/-- The dual action on characters induced by `slTwoAction g⁻¹`. -/
private def dualAction (g : SL(2, ℤ)) :
    PontryaginDual (Multiplicative (Fin 2 → ℤ)) →ₜ*
      PontryaginDual (Multiplicative (Fin 2 → ℤ)) :=
  PontryaginDual.map ⟨(slTwoAction g⁻¹).toMonoidHom, continuous_of_discreteTopology⟩

private theorem dualAction_apply_stdGen (g : SL(2, ℤ))
    (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) (j : Fin 2) :
    dualAction g χ (stdGen j) =
      Circle.exp (((Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) :
        Matrix (Fin 2) (Fin 2) ℝ) *ᵥ dualCoord χ) j) := by
  have hval : slTwoAction g⁻¹ (stdGen j) =
      ∏ i : Fin 2, stdGen i ^ ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [eq_prod_stdGen_zpow (slTwoAction g⁻¹ (stdGen j))]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    rw [slTwoAction_apply_eq_mulVec]
    simp [stdGen]
  have hterm (i : Fin 2) :
      χ (stdGen i) ^ ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j =
        Circle.exp (((Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) :
          Matrix (Fin 2) (Fin 2) ℝ) j i) * dualCoord χ i) := by
    rw [← Circle.exp_arg (χ (stdGen i)), ← Circle.exp_intCast_mul]
    congr 1
  dsimp only [dualAction, PontryaginDual.map_apply, ContinuousMonoidHom.coe_mk,
    MonoidHom.coe_mk, MulEquiv.coe_toMonoidHom]
  rw [hval, map_prod, Fin.prod_univ_two, map_zpow, map_zpow, hterm 0, hterm 1, ← Circle.exp_add]
  congr 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Entrywise `ℓ¹` bound for `contragredient g`, padded by `1` to stay strictly positive. -/
private def entryBound (g : SL(2, ℤ)) : ℝ :=
  1 + ∑ j : Fin 2, ∑ i : Fin 2,
    |((Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) :
      Matrix (Fin 2) (Fin 2) ℝ) j i)|

private theorem one_le_entryBound (g : SL(2, ℤ)) : 1 ≤ entryBound g := by
  unfold entryBound
  have h0 : 0 ≤ ∑ j : Fin 2, ∑ i : Fin 2,
      |((Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) :
        Matrix (Fin 2) (Fin 2) ℝ) j i)| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- Half-width of the coordinate box around `1` where `dualAction g` does not wrap mod `2π`. -/
private def boxRadius (g : SL(2, ℤ)) : ℝ :=
  Real.pi / (2 * entryBound g)

private theorem boxRadius_pos (g : SL(2, ℤ)) : 0 < boxRadius g := by
  unfold boxRadius
  have h1 : 0 < entryBound g := lt_of_lt_of_le zero_lt_one (one_le_entryBound g)
  positivity

/-- Open coordinate box `{χ | ∀ i, |dualCoord χ i| < r}` around `1` on the dual torus. -/
private def dualBox (r : ℝ) : Set (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
  {χ | ∀ i : Fin 2, |dualCoord χ i| < r}

private theorem measurableSet_dualBox (r : ℝ) : MeasurableSet (dualBox r) := by
  have heq : dualBox r = ⋂ i : Fin 2, (fun χ => |dualCoord χ i|) ⁻¹' Set.Iio r := by
    ext χ; simp [dualBox]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (continuous_abs.measurable.comp ((measurable_pi_apply i).comp measurable_dualCoord))
      measurableSet_Iio

/-- On `dualBox (boxRadius g)`, the dual action is linear in the `dualCoord` coordinates. -/
private theorem dualCoord_dualAction (g : SL(2, ℤ))
    {χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))} (hχ : χ ∈ dualBox (boxRadius g)) :
    dualCoord (dualAction g χ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) :
        Matrix (Fin 2) (Fin 2) ℝ) *ᵥ dualCoord χ := by
  ext j
  set A : Matrix (Fin 2) (Fin 2) ℝ :=
    (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) : Matrix (Fin 2) (Fin 2) ℝ)
  have hbound : |(A *ᵥ dualCoord χ) j| < Real.pi := by
    have hrow : ∑ i : Fin 2, |A j i| < entryBound g := by
      have hle : ∑ i : Fin 2, |A j i| ≤ ∑ k : Fin 2, ∑ i : Fin 2, |A k i| :=
        Finset.single_le_sum (f := fun k => ∑ i : Fin 2, |A k i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      unfold entryBound
      linarith
    have h1 : |(A *ᵥ dualCoord χ) j| ≤ ∑ i : Fin 2, |A j i| * |dualCoord χ i| := by
      simpa [Matrix.mulVec, dotProduct, abs_mul] using
        Finset.abs_sum_le_sum_abs (fun i : Fin 2 => A j i * dualCoord χ i) Finset.univ
    have h2 : ∑ i : Fin 2, |A j i| * |dualCoord χ i| ≤ (∑ i : Fin 2, |A j i|) * boxRadius g := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hχ i).le (abs_nonneg _)
    have h3 : (∑ i : Fin 2, |A j i|) * boxRadius g < entryBound g * boxRadius g :=
      mul_lt_mul_of_pos_right hrow (boxRadius_pos g)
    have h4 : entryBound g * boxRadius g = Real.pi / 2 := by
      unfold boxRadius
      have hne : entryBound g ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_entryBound g)).ne'
      field_simp
    linarith [Real.pi_pos]
  rw [dualCoord, dualAction_apply_stdGen]
  exact Circle.arg_exp (abs_lt.1 hbound).1 (abs_lt.1 hbound).2.le

/-- Projection from the dual torus to `OnePoint ℝ` via `dualCoord` and `OnePoint.ofVec`. -/
private def projMap (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) : OnePoint ℝ :=
  OnePoint.ofVec (dualCoord χ)

private theorem measurable_projMap : Measurable projMap :=
  OnePoint.measurable_ofVec.comp measurable_dualCoord

private theorem projMap_dualAction (g : SL(2, ℤ))
    {χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))}
    (hχ : χ ∈ dualBox (boxRadius g)) (hχ1 : χ ≠ 1) :
    projMap (dualAction g χ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (contragredient g) • projMap χ := by
  have hv : dualCoord χ ≠ 0 := fun h => hχ1 ((dualCoord_eq_zero_iff χ).1 h)
  rw [projMap, dualCoord_dualAction g hχ, OnePoint.ofVec_mulVec _ hv, projMap]

/-! ### Spectral-measure estimates for `ℤ² ⋊ G` -/

section SpectralEstimates

variable {G : Type v} [Group G] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {φ : G →* SL(2, ℤ)}
  {ρ : ContRepresentation ℂ (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp φ] G) H}

/-- `∫ |χ(eᵢ) - 1|² d(P.diag ξ) = ‖ρ(inl eᵢ) ξ - ξ‖²`. -/
private theorem integral_norm_sq_eval_sub_one (hρ : ρ.IsUnitary) (ξ : H) (i : Fin 2) :
    ∫ χ, ‖(χ (stdGen i) : ℂ) - 1‖ ^ 2
        ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ) =
      ‖ρ (inl (stdGen i)) ξ - ξ‖ ^ 2 := by
  set P := (ρ.restrict inl).spectralPVM (hρ.restrict inl)
  let s : BoundedBorelFunction (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
    BoundedBorelFunction.ofContinuousMap
      (PontryaginDual.evalBoundedContinuous (Pi.single i (1 : ℤ))).toContinuousMap - 1
  have hs_int : P.integral s = ρ (inl (stdGen i)) - 1 := by
    have heval : P.integral (BoundedBorelFunction.ofContinuousMap
        (PontryaginDual.evalBoundedContinuous (Pi.single i (1 : ℤ))).toContinuousMap) =
        ρ (inl (stdGen i)) :=
      ContRepresentation.integral_spectralPVM_evalBoundedContinuous (hρ.restrict inl)
        (Pi.single i (1 : ℤ))
    simp only [s, map_sub, map_one, heval]
  have hnorm := P.norm_sq_integral_apply s ξ
  rw [hs_int] at hnorm
  simpa [s, stdGen] using hnorm.symm

/-- Concentration of `P.diag ξ` inside `dualBox r` controlled by `ρ (inl (stdGen i)) ξ - ξ`. -/
private theorem diag_real_compl_dualBox_le (hρ : ρ.IsUnitary) (ξ : H) {r : ℝ} (hr : 0 < r) :
    (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ).real (dualBox r)ᶜ ≤
      (∑ j : Fin 2, ‖ρ (inl (stdGen j)) ξ - ξ‖ ^ 2) / (2 / Real.pi * r) ^ 2 := by
  set μ := ((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ
  set c : ℝ := (2 / Real.pi * r) ^ 2
  have hc : 0 < c := by positivity
  have hint_j (j : Fin 2) : Integrable (fun χ => ‖(χ (stdGen j) : ℂ) - 1‖ ^ 2) μ := by
    have hcont : Continuous fun χ : PontryaginDual (Multiplicative (Fin 2 → ℤ)) =>
        ‖(χ (stdGen j) : ℂ) - 1‖ ^ 2 :=
      ((TauCeti.PontryaginDual.continuous_coe_eval_const (stdGen j)).sub
        continuous_const).norm.pow 2
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt (χ : PontryaginDual (Multiplicative (Fin 2 → ℤ))) :
      (dualBox r)ᶜ.indicator (fun _ => c) χ ≤
        ‖(χ (stdGen 0) : ℂ) - 1‖ ^ 2 + ‖(χ (stdGen 1) : ℂ) - 1‖ ^ 2 := by
    by_cases hχ : χ ∈ (dualBox r)ᶜ
    · rw [Set.indicator_of_mem hχ]
      simp only [Set.mem_compl_iff, dualBox, Set.mem_ofPred_eq, not_forall, not_lt] at hχ
      obtain ⟨j, hj⟩ := hχ
      have h1 : c ≤ (2 / Real.pi * dualCoord χ j) ^ 2 := by
        have habs : 2 / Real.pi * r ≤ |2 / Real.pi * dualCoord χ j| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
          exact mul_le_mul_of_nonneg_left hj (by positivity)
        have hnn : (0 : ℝ) ≤ 2 / Real.pi * r := by positivity
        simpa [c] using sq_le_sq.2 (by rwa [abs_of_nonneg hnn])
      have h2 := h1.trans (sq_mul_dualCoord_le_norm_sq χ j)
      fin_cases j
      · exact h2.trans (le_add_of_nonneg_right (sq_nonneg _))
      · exact h2.trans (le_add_of_nonneg_left (sq_nonneg _))
    · rw [Set.indicator_of_notMem hχ]
      positivity
  have hint_sum :
      Integrable (fun χ => ‖(χ (stdGen 0) : ℂ) - 1‖ ^ 2 + ‖(χ (stdGen 1) : ℂ) - 1‖ ^ 2) μ :=
    (hint_j 0).add (hint_j 1)
  have hmono := integral_mono ((integrable_const c).indicator (measurableSet_dualBox r).compl)
    hint_sum hpt
  rw [integral_indicator_const _ (measurableSet_dualBox r).compl, smul_eq_mul,
    integral_add (hint_j 0) (hint_j 1), integral_norm_sq_eval_sub_one hρ ξ 0,
    integral_norm_sq_eval_sub_one hρ ξ 1] at hmono
  rw [Fin.sum_univ_two]
  exact (le_div_iff₀ hc).2 hmono

/-- Perturbing the unit vector `ξ` by `η` changes the integral of `f ∘ projMap` against `P.diag`
by at most `2 * ‖f‖ * ‖η - ξ‖`. -/
private theorem abs_integral_diag_sub_le (hρ : ρ.IsUnitary) {ξ η : H} (hξ : ‖ξ‖ = 1)
    (hη : ‖η‖ = 1) (f : OnePoint ℝ →ᵇ ℝ) :
    |(∫ χ, f (projMap χ) ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag η)) -
        (∫ χ, f (projMap χ) ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ))| ≤
      2 * ‖f‖ * ‖η - ξ‖ := by
  set P := (ρ.restrict inl).spectralPVM (hρ.restrict _)
  have hmeas : Measurable fun χ => ((f (projMap χ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (f.continuous.measurable.comp measurable_projMap)
  let h : BoundedBorelFunction (PontryaginDual (Multiplicative (Fin 2 → ℤ))) :=
    BoundedBorelFunction.ofFunction (fun χ => ((f (projMap χ) : ℝ) : ℂ)) hmeas
      ⟨‖f‖, norm_nonneg f, fun χ => by
        rw [Complex.norm_real]
        exact f.norm_coe_le_norm (projMap χ)⟩
  have hOp : ‖P.integral h‖ ≤ ‖f‖ :=
    P.norm_integral_le (norm_nonneg f) fun χ => by
      simp only [h, BoundedBorelFunction.ofFunction_apply, Complex.norm_real]
      exact f.norm_coe_le_norm (projMap χ)
  have hInt (v : H) : ((∫ χ, f (projMap χ) ∂(P.diag v) : ℝ) : ℂ) = ⟪v, P.integral h v⟫_ℂ := by
    rw [← integral_complex_ofReal]
    simpa [h] using P.integral_diag_eq_inner_integral h v
  have hdiff : ((∫ χ, f (projMap χ) ∂(P.diag η) - ∫ χ, f (projMap χ) ∂(P.diag ξ) : ℝ) : ℂ) =
      ⟪η - ξ, P.integral h η⟫_ℂ + ⟪ξ, P.integral h (η - ξ)⟫_ℂ := by
    rw [Complex.ofReal_sub, hInt η, hInt ξ, inner_sub_left, map_sub, inner_sub_right]
    ring
  calc |(∫ χ, f (projMap χ) ∂(P.diag η)) - (∫ χ, f (projMap χ) ∂(P.diag ξ))|
      = ‖((∫ χ, f (projMap χ) ∂(P.diag η) - ∫ χ, f (projMap χ) ∂(P.diag ξ) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖⟪η - ξ, P.integral h η⟫_ℂ + ⟪ξ, P.integral h (η - ξ)⟫_ℂ‖ := by rw [hdiff]
    _ ≤ ‖⟪η - ξ, P.integral h η⟫_ℂ‖ + ‖⟪ξ, P.integral h (η - ξ)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖η - ξ‖ * ‖P.integral h η‖ + ‖ξ‖ * ‖P.integral h (η - ξ)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖η - ξ‖ * (‖f‖ * ‖η‖) + ‖ξ‖ * (‖f‖ * ‖η - ξ‖) := by
        gcongr
        · exact ((P.integral h).le_opNorm η).trans
            (mul_le_mul_of_nonneg_right hOp (norm_nonneg η))
        · exact ((P.integral h).le_opNorm (η - ξ)).trans
            (mul_le_mul_of_nonneg_right hOp (norm_nonneg _))
    _ = 2 * ‖f‖ * ‖η - ξ‖ := by rw [hξ, hη]; ring

/-- Without nonzero `ℤ²`-invariant vectors, the trivial character `1` has spectral mass zero. -/
private theorem diag_singleton_one_eq_zero (hρ : ρ.IsUnitary)
    (hinv0 : (ρ.restrict inl).invariants = ⊥) (ξ : H) :
    (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ) {1} = 0 := by
  set P := (ρ.restrict inl).spectralPVM (hρ.restrict _)
  have hP1 : P.proj {1} (measurableSet_singleton 1) = 0 :=
    (ContRepresentation.spectralPVM_proj_singleton_one_eq_zero_iff (hρ.restrict _)).2 hinv0
  have hr : (P.diag ξ).real {1} = 0 := by
    rw [Measure.real, ← P.norm_sq_proj_apply {1} (measurableSet_singleton 1) ξ, hP1]
    simp
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hr

/-- Equivariance of the diagonal spectral measure under `dualAction (φ g)`. -/
private theorem map_dualAction_diag (hρ : ρ.IsUnitary) (g : G) (ξ : H) :
    Measure.map (dualAction (φ g)) (((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ) =
      ((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ρ (inr g) ξ) := by
  have h := ContRepresentation.map_diag_spectralPVM_restrict_inl_apply_inr hρ g⁻¹ (ρ (inr g) ξ)
  have hcancel : ρ (inr g⁻¹) (ρ (inr g) ξ) = ξ := by
    rw [← mul_apply_eq_comp, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
      one_apply_eq_self]
  rw [hcancel] at h
  have hmap : PontryaginDual.map
      ⟨((slTwoAction.comp φ) g⁻¹).toMonoidHom, continuous_of_discreteTopology⟩ =
      dualAction (φ g) := by
    ext χ v
    simp [dualAction, map_inv]
  rwa [hmap] at h

/-- Error between `f (Φ • projMap χ)` and `f (projMap (dualAction (φ g) χ))` integrated against
`P.diag ξ` is supported outside `dualBox (boxRadius (φ g))`. -/
private theorem abs_integral_smul_sub_dualAction_le (hρ : ρ.IsUnitary)
    (hinv0 : (ρ.restrict inl).invariants = ⊥) (ξ : H) (g : G) (f : OnePoint ℝ →ᵇ ℝ) :
    |∫ χ, (f (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g)) • projMap χ) -
          f (projMap (dualAction (φ g) χ)))
        ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ)| ≤
      2 * ‖f‖ * ((∑ j : Fin 2, ‖ρ (inl (stdGen j)) ξ - ξ‖ ^ 2) /
        (2 / Real.pi * boxRadius (φ g)) ^ 2) := by
  set μ := ((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ
  set Φ := Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g))
  have hae : ∀ᵐ χ ∂μ, ‖f (Φ • projMap χ) - f (projMap (dualAction (φ g) χ))‖ ≤
      (dualBox (boxRadius (φ g)))ᶜ.indicator (fun _ => 2 * ‖f‖) χ := by
    have hne1 : ∀ᵐ χ ∂μ, χ ≠ 1 := by
      rw [ae_iff]
      simpa using diag_singleton_one_eq_zero hρ hinv0 ξ
    filter_upwards [hne1] with χ hχ1
    by_cases hB : χ ∈ dualBox (boxRadius (φ g))
    · rw [Set.indicator_of_notMem (not_not.2 hB), projMap_dualAction (φ g) hB hχ1, sub_self,
        norm_zero]
    · rw [Set.indicator_of_mem hB]
      calc ‖f (Φ • projMap χ) - f (projMap (dualAction (φ g) χ))‖
          ≤ ‖f (Φ • projMap χ)‖ + ‖f (projMap (dualAction (φ g) χ))‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
  have hle := norm_integral_le_of_norm_le
    ((integrable_const (2 * ‖f‖)).indicator (measurableSet_dualBox _).compl) hae
  rw [integral_indicator_const _ (measurableSet_dualBox _).compl, smul_eq_mul, mul_comm,
    Real.norm_eq_abs] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left
    (diag_real_compl_dualBox_le hρ ξ (boxRadius_pos (φ g))) (by positivity))

/-- Quantitative almost-invariance of the pushed-forward spectral measure on `OnePoint ℝ`. -/
private theorem abs_integral_map_projMap_sub_le (hρ : ρ.IsUnitary)
    (hinv0 : (ρ.restrict inl).invariants = ⊥) {ξ : H} (hξ : ‖ξ‖ = 1) (g : G)
    (f : OnePoint ℝ →ᵇ ℝ) :
    |(∫ x, f (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g)) • x)
          ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ).map projMap) -
        (∫ x, f x
          ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag ξ).map projMap)| ≤
      2 * ‖f‖ * ((∑ j : Fin 2, ‖ρ (inl (stdGen j)) ξ - ξ‖ ^ 2) /
          (2 / Real.pi * boxRadius (φ g)) ^ 2) +
        2 * ‖f‖ * ‖ρ (inr g) ξ - ξ‖ := by
  set P := (ρ.restrict inl).spectralPVM (hρ.restrict _)
  set μ := P.diag ξ
  set Φ := Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g))
  have h1 : ∫ x, f (Φ • x) ∂(μ.map projMap) = ∫ χ, f (Φ • projMap χ) ∂μ :=
    integral_map measurable_projMap.aemeasurable
      (f.continuous.comp (continuous_const_smul Φ)).aestronglyMeasurable
  have h2 : ∫ x, f x ∂(μ.map projMap) = ∫ χ, f (projMap χ) ∂μ :=
    integral_map measurable_projMap.aemeasurable f.continuous.aestronglyMeasurable
  have h3 : ∫ χ, f (projMap (dualAction (φ g) χ)) ∂μ =
      ∫ χ, f (projMap χ) ∂(P.diag (ρ (inr g) ξ)) := by
    rw [← map_dualAction_diag hρ g ξ]
    exact (integral_map (map_continuous (dualAction (φ g))).measurable.aemeasurable
      (f.continuous.measurable.comp measurable_projMap).aestronglyMeasurable).symm
  have hint1 : Integrable (fun χ => f (Φ • projMap χ)) μ :=
    .of_bound (f.continuous.measurable.comp
      ((continuous_const_smul Φ).measurable.comp measurable_projMap)).aestronglyMeasurable
      ‖f‖ (.of_forall fun _ => f.norm_coe_le_norm _)
  have hint2 : Integrable (fun χ => f (projMap (dualAction (φ g) χ))) μ :=
    .of_bound (f.continuous.measurable.comp
      (measurable_projMap.comp (map_continuous (dualAction (φ g))).measurable)).aestronglyMeasurable
      ‖f‖ (.of_forall fun _ => f.norm_coe_le_norm _)
  have hsplit : (∫ x, f (Φ • x) ∂(μ.map projMap)) - (∫ x, f x ∂(μ.map projMap)) =
      (∫ χ, (f (Φ • projMap χ) - f (projMap (dualAction (φ g) χ))) ∂μ) +
        ((∫ χ, f (projMap χ) ∂(P.diag (ρ (inr g) ξ))) - (∫ χ, f (projMap χ) ∂μ)) := by
    rw [h1, h2, ← h3, integral_sub hint1 hint2]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add (abs_integral_smul_sub_dualAction_le hρ hinv0 ξ g f)
    (abs_integral_diag_sub_le hρ hξ (by rw [hρ.norm_map, hξ]) f))

/-- Along an almost invariant net of unit vectors, the pushforward integrals become asymptotically
invariant under `Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g))`. -/
private theorem tendsto_integral_map_projMap_sub (hρ : ρ.IsUnitary)
    (hinv0 : (ρ.restrict inl).invariants = ⊥) {ξ : Finset G × ℕ → H}
    (hξ1 : ∀ p, ‖ξ p‖ = 1)
    (hξ_inl : ∀ p (j : Fin 2), ‖ρ (inl (stdGen j)) (ξ p) - ξ p‖ < 1 / (p.2 + 1))
    (hξ_inr : ∀ p, ∀ g ∈ p.1, ‖ρ (inr g) (ξ p) - ξ p‖ < 1 / (p.2 + 1))
    (g : G) (f : OnePoint ℝ →ᵇ ℝ) :
    Tendsto (fun p : Finset G × ℕ =>
        (∫ x, f (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g)) • x)
            ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ξ p)).map projMap) -
          (∫ x, f x
            ∂(((ρ.restrict inl).spectralPVM (hρ.restrict _)).diag (ξ p)).map projMap))
      atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_atTop]
  set r2 : ℝ := (2 / Real.pi * boxRadius (φ g)) ^ 2
  have hr2 : 0 < r2 := by have := boxRadius_pos (φ g); positivity
  set C : ℝ := 4 * ‖f‖ / r2 + 2 * ‖f‖
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨({g}, N), fun p hp => ?_⟩
  have hg : g ∈ p.1 := Finset.singleton_subset_iff.1 hp.1
  have hNp : (N : ℝ) ≤ p.2 := Nat.cast_le.2 hp.2
  have hd_pos : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  have hd_le1 : 1 / ((p.2 : ℝ) + 1) ≤ 1 := (div_le_one hd_pos).2 (by linarith)
  have hsq_j (j : Fin 2) : ‖ρ (inl (stdGen j)) (ξ p) - ξ p‖ ^ 2 ≤ 1 / ((p.2 : ℝ) + 1) := by
    have hlt := pow_le_pow_left₀ (norm_nonneg _) (hξ_inl p j).le 2
    have hsq : (1 / ((p.2 : ℝ) + 1)) ^ 2 ≤ 1 / ((p.2 : ℝ) + 1) := by
      rw [sq]
      exact (mul_le_mul_of_nonneg_right hd_le1 (by positivity)).trans_eq (one_mul _)
    exact hlt.trans hsq
  have hsum_le : ∑ j : Fin 2, ‖ρ (inl (stdGen j)) (ξ p) - ξ p‖ ^ 2 ≤ 2 / ((p.2 : ℝ) + 1) := by
    rw [Fin.sum_univ_two]
    exact (add_le_add (hsq_j 0) (hsq_j 1)).trans_eq (by ring)
  have h1 : 2 * ‖f‖ * ((∑ j : Fin 2, ‖ρ (inl (stdGen j)) (ξ p) - ξ p‖ ^ 2) / r2) ≤
      (4 * ‖f‖ / r2) / ((p.2 : ℝ) + 1) :=
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum_le hr2.le)
      (by positivity : (0 : ℝ) ≤ 2 * ‖f‖)).trans_eq (by ring)
  have h2 : 2 * ‖f‖ * ‖ρ (inr g) (ξ p) - ξ p‖ ≤ (2 * ‖f‖) / ((p.2 : ℝ) + 1) :=
    (mul_le_mul_of_nonneg_left (hξ_inr p g hg).le (by positivity : (0 : ℝ) ≤ 2 * ‖f‖)).trans_eq
      (by ring)
  have hstep := (abs_integral_map_projMap_sub_le hρ hinv0 (hξ1 p) g f).trans (add_le_add h1 h2)
  have hlt_eps : C / ((p.2 : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hd_pos]
    have hCN : C < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
    nlinarith
  have hcombine : (4 * ‖f‖ / r2) / ((p.2 : ℝ) + 1) + 2 * ‖f‖ / ((p.2 : ℝ) + 1) =
      C / ((p.2 : ℝ) + 1) := by simp only [C]; ring
  simpa [Real.dist_eq] using hstep.trans_lt (hcombine ▸ hlt_eps)

/-- From almost invariant vectors and no nonzero `ℤ²`-invariant vector, extract a Borel probability
measure on `OnePoint ℝ` invariant under `Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g))`
for all `g : G`. -/
private theorem exists_invariant_probabilityMeasure_onePoint
    (hρ : ρ.IsUnitary) (halm : ρ.HasAlmostInvariantVectors)
    (hinv0 : (ρ.restrict inl).invariants = ⊥) :
    ∃ ν : ProbabilityMeasure (OnePoint ℝ), ∀ g : G,
      Measure.map (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g)) • ·)
        (ν : Measure (OnePoint ℝ)) = (ν : Measure (OnePoint ℝ)) := by
  classical
  have : TopologicalSpace.MetrizableSpace (OnePoint ℝ) :=
    (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).isEmbedding.metrizableSpace
  set P := (ρ.restrict inl).spectralPVM (hρ.restrict inl)
  have hchoose (p : Finset G × ℕ) :
      ∃ ξ : H, ‖ξ‖ = 1 ∧ (∀ j : Fin 2, ‖ρ (inl (stdGen j)) ξ - ξ‖ < 1 / (p.2 + 1)) ∧
        (∀ g ∈ p.1, ‖ρ (inr g) ξ - ξ‖ < 1 / (p.2 + 1)) := by
    let F : Finset (Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp φ] G) :=
      {inl (stdGen 0), inl (stdGen 1)} ∪ p.1.image inr
    obtain ⟨ξ, hξ1, hξF⟩ :=
      (ContRepresentation.hasAlmostInvariantVectors_def ρ).1 halm F (1 / (p.2 + 1))
        Nat.one_div_pos_of_nat
    exact ⟨ξ, hξ1, fun j => by fin_cases j <;> exact hξF _ (Finset.mem_union_left _ (by simp)),
      fun g hg => hξF _ (Finset.mem_union_right _ (Finset.mem_image_of_mem inr hg))⟩
  choose ξ hξ1 hξ_inl hξ_inr using hchoose
  let νSeq (p : Finset G × ℕ) : ProbabilityMeasure (OnePoint ℝ) :=
    ⟨(P.diag (ξ p)).map projMap, ⟨by
      rw [Measure.map_apply measurable_projMap MeasurableSet.univ, Set.preimage_univ, P.diag_univ,
        ← ofReal_norm, hξ1 p]
      simp⟩⟩
  obtain ⟨ν, -, hν⟩ := isCompact_univ.exists_mapClusterPt
    (f := (atTop : Filter (Finset G × ℕ))) (u := νSeq) (by simp)
  refine ⟨ν, fun g => ?_⟩
  set Φ := Matrix.SpecialLinearGroup.mapGL ℝ (contragredient (φ g))
  have : IsFiniteMeasure (Measure.map (Φ • ·) (ν : Measure (OnePoint ℝ))) :=
    Measure.isFiniteMeasure_map (ν : Measure (OnePoint ℝ)) (Φ • ·)
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (continuous_const_smul Φ).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  let fg : OnePoint ℝ →ᵇ ℝ := f.compContinuous ⟨(Φ • ·), continuous_const_smul Φ⟩
  let L : ProbabilityMeasure (OnePoint ℝ) → ℝ := fun μ => (∫ x, fg x ∂μ) - (∫ x, f x ∂μ)
  have hL_cont : Continuous L :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction fg).sub
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f)
  have hcluster : MapClusterPt (L ν) atTop (L ∘ νSeq) := hν.continuousAt_comp hL_cont.continuousAt
  have htend : Tendsto (L ∘ νSeq) atTop (𝓝 0) :=
    tendsto_integral_map_projMap_sub hρ hinv0 hξ1 hξ_inl hξ_inr g f
  exact sub_eq_zero.1 (eq_of_nhds_neBot (hcluster.clusterPt.mono htend))

end SpectralEstimates

/-! ### Relative property (T) for `(ℤ² ⋊ G, ℤ²)` -/

/-- **Burger's theorem (homomorphism form).** For any group `G` and any homomorphism
`φ : G →* SL(2, ℤ)` whose image `φ.range` is nonamenable (in some group topology), the pair
`(ℤ² ⋊ G, ℤ²)` has relative property (T). -/
theorem relativePropertyT_inl_comp_of_not_amenable_range {G : Type v} [Group G]
    (φ : G →* SL(2, ℤ)) [TopologicalSpace φ.range] [IsTopologicalGroup φ.range]
    (hφ : ¬ TauCeti.Amenable φ.range) :
    (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp φ)).range.RelativePropertyT.{u} := by
  rw [relativePropertyT_def]
  intro H _ _ _ ρ hρ halm
  by_contra hno
  have hinv0 : (ρ.restrict inl).invariants = ⊥ := by
    ext v
    simp only [Submodule.mem_bot]
    refine ⟨fun hv => ?_, fun hv => hv ▸ zero_mem _⟩
    by_contra hv0
    apply hno
    refine ⟨v, hv0, fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨n, rfl⟩ := hx
    exact hv n
  obtain ⟨ν, hν⟩ := exists_invariant_probabilityMeasure_onePoint hρ halm hinv0
  have hinv_range : ∀ k : φ.range,
      Measure.map (Matrix.SpecialLinearGroup.mapGL ℝ (contragredient k.1) • ·)
        (ν : Measure (OnePoint ℝ)) = (ν : Measure (OnePoint ℝ)) := by
    rintro ⟨_, g, rfl⟩
    exact hν g
  exact hφ (MonoidHom.amenable_of_map_smul_onePoint_eq (contragredient.comp φ.range.subtype)
    (contragredient_injective.comp φ.range.subtype_injective) hinv_range)

end SpectralProof

/-- **Converse to Burger's theorem (homomorphism form).** If `φ : G →* SL(2, ℤ)` has discrete
amenable image, then `(ℤ² ⋊ G, ℤ²)` does not have relative property (T), because `ℤ² ⋊ φ.range` is
amenable and therefore has the Haagerup property. -/
theorem not_relativePropertyT_inl_comp_of_amenable_range {G : Type v} [Group G]
    (φ : G →* SL(2, ℤ)) [TopologicalSpace φ.range] [IsTopologicalGroup φ.range]
    [DiscreteTopology φ.range] [TauCeti.Amenable φ.range] :
    ¬ (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp φ)).range.RelativePropertyT.{u} := by
  let K := φ.range
  let Γ := Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp K.subtype] K
  let : TopologicalSpace (Multiplicative (Fin 2 → ℤ)) := ⊥
  have : DiscreteTopology (Multiplicative (Fin 2 → ℤ)) := ⟨rfl⟩
  let : TopologicalSpace Γ := ⊥
  have : DiscreteTopology Γ := ⟨rfl⟩
  have : TauCeti.Amenable Γ :=
    TauCeti.Amenable.of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : TopologicalSpace (ULift.{u} Γ) := ⊥
  have : DiscreteTopology (ULift.{u} Γ) := ⟨rfl⟩
  have : TauCeti.Amenable (ULift.{u} Γ) :=
    TauCeti.Amenable.of_injective (MulEquiv.ulift (α := Γ)).toMonoidHom
      (MulEquiv.ulift (α := Γ)).injective
  have hU_haag : TauCeti.HasHaagerupProperty (ULift.{u} Γ) :=
    TauCeti.hasHaagerupProperty_of_amenable
  let q : (Multiplicative (Fin 2 → ℤ) ⋊[TauCeti.slTwoAction.comp φ] G) →* ULift.{u} Γ :=
    (MulEquiv.ulift (α := Γ)).symm.toMonoidHom.comp
      (SemidirectProduct.map (MonoidHom.id _) φ.rangeRestrict fun _ => rfl)
  intro hT
  have hfin : Finite (((SemidirectProduct.inl
      (φ := TauCeti.slTwoAction.comp φ)).range).map q) :=
    hU_haag.finite_of_relativePropertyT (hT.map q)
  let emb : ℤ → ((SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp φ)).range).map q :=
    fun n => ⟨q (SemidirectProduct.inl (Multiplicative.ofAdd ![n, 0])),
      ⟨SemidirectProduct.inl (Multiplicative.ofAdd ![n, 0]), ⟨_, rfl⟩, rfl⟩⟩
  have hemb : Function.Injective emb := fun _ _ hab =>
    congrArg (fun x => (Multiplicative.toAdd x.1.down.left) 0) hab
  have : Finite ℤ := Finite.of_injective emb hemb
  exact not_finite ℤ

/-- Complete characterization of relative property (T) for `(ℤ² ⋊ G, ℤ²)` under any homomorphism
`φ : G →* SL(2, ℤ)`: it holds if and only if `φ.range` is nonamenable as a discrete group. -/
theorem relativePropertyT_inl_comp_iff_not_amenable_range {G : Type v} [Group G]
    (φ : G →* SL(2, ℤ)) [TopologicalSpace φ.range] [IsTopologicalGroup φ.range]
    [DiscreteTopology φ.range] :
    (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp φ)).range.RelativePropertyT.{u} ↔
      ¬ TauCeti.Amenable φ.range :=
  ⟨fun hT _ => not_relativePropertyT_inl_comp_of_amenable_range φ hT,
    relativePropertyT_inl_comp_of_not_amenable_range φ⟩

/-- **Burger's theorem for an injective homomorphism.** If `G` embeds into `SL(2, ℤ)` and is
nonamenable in some group topology, then `(ℤ² ⋊ G, ℤ²)` has relative property (T). -/
theorem relativePropertyT_inl_comp_of_not_amenable {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* SL(2, ℤ)) (hφ : Function.Injective φ) (hG : ¬ TauCeti.Amenable G) :
    (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp φ)).range.RelativePropertyT.{u} := by
  let : TopologicalSpace φ.range := ⊥
  have : DiscreteTopology φ.range := ⟨rfl⟩
  refine relativePropertyT_inl_comp_of_not_amenable_range φ fun _ => hG ?_
  exact TauCeti.Amenable.of_injective φ.rangeRestrict
    (fun a b hab => hφ (congrArg Subtype.val hab))

/-- **Burger's theorem.** For any subgroup `G ≤ SL(2, ℤ)` that is nonamenable in some group
topology, the pair `(ℤ² ⋊ G, ℤ²)` has relative property (T). -/
theorem relativePropertyT_inl_of_not_amenable (G : Subgroup SL(2, ℤ))
    [TopologicalSpace G] [IsTopologicalGroup G] (hG : ¬ TauCeti.Amenable G) :
    (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp G.subtype)).range.RelativePropertyT.{u} :=
  relativePropertyT_inl_comp_of_not_amenable G.subtype G.subtype_injective hG

/-- A subgroup `G ≤ SL(2, ℤ)` with the discrete topology gives a relative property (T) pair
`(ℤ² ⋊ G, ℤ²)` if and only if `G` is nonamenable. -/
theorem relativePropertyT_inl_iff_not_amenable (G : Subgroup SL(2, ℤ))
    [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] :
    (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp G.subtype)).range.RelativePropertyT.{u} ↔
      ¬ TauCeti.Amenable G := by
  let : TopologicalSpace G.subtype.range := ⊥
  have : DiscreteTopology G.subtype.range := ⟨rfl⟩
  rw [relativePropertyT_inl_comp_iff_not_amenable_range G.subtype]
  refine not_congr ⟨fun _ => ?_, fun _ => ?_⟩
  · exact TauCeti.Amenable.of_injective G.subtype.rangeRestrict
      (fun a b hab => G.subtype_injective (congrArg (Subtype.val : G.subtype.range → SL(2, ℤ)) hab))
  · exact TauCeti.Amenable.of_denseRange
      ⟨G.subtype.rangeRestrict, continuous_of_discreteTopology⟩
      G.subtype.rangeRestrict_surjective.denseRange

/-- **Kazhdan–Margulis theorem.** The pair `(ℤ² ⋊ SL(2, ℤ), ℤ²)` has relative property (T). -/
theorem relativePropertyT_inl_slTwo :
    (SemidirectProduct.inl (φ := TauCeti.slTwoAction)).range.RelativePropertyT.{u} := by
  let : TopologicalSpace SL(2, ℤ) := ⊥
  have : DiscreteTopology SL(2, ℤ) := ⟨rfl⟩
  have hnot : ¬ TauCeti.Amenable SL(2, ℤ) :=
    TauCeti.not_amenable_of_injective_freeGroup _ TauCeti.injective_freeGroup_lift_transvection_two
  exact relativePropertyT_inl_comp_of_not_amenable (MonoidHom.id SL(2, ℤ)) Function.injective_id
    hnot

/-- For any root transvection subgroup `G ≤ SL(2, ℤ)` (such as the upper unitriangular subgroup
`{[[1, n], [0, 1]] : n ∈ ℤ}`), the pair `(ℤ² ⋊ G, ℤ²)` fails relative property (T). In particular,
the nonamenability hypothesis in Burger's theorem cannot be dropped. -/
theorem not_relativePropertyT_inl_range_transvectionHom {i j : Fin 2} (hij : i ≠ j) :
    ¬ (SemidirectProduct.inl (φ := TauCeti.slTwoAction.comp
        (Matrix.SpecialLinearGroup.transvectionHom
          (A := ℤ) hij).range.subtype)).range.RelativePropertyT.{u} := by
  let U := (Matrix.SpecialLinearGroup.transvectionHom (A := ℤ) hij).range
  let : TopologicalSpace U := ⊥
  have : DiscreteTopology U := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative ℤ) := ⊥
  have : DiscreteTopology (Multiplicative ℤ) := ⟨rfl⟩
  have hU : TauCeti.Amenable U :=
    TauCeti.Amenable.of_denseRange
      ⟨(Matrix.SpecialLinearGroup.transvectionHom (A := ℤ) hij).rangeRestrict,
        continuous_of_discreteTopology⟩
      (Matrix.SpecialLinearGroup.transvectionHom (A := ℤ) hij).rangeRestrict_surjective.denseRange
  exact (relativePropertyT_inl_iff_not_amenable U).not.2 (not_not.2 hU)

end Subgroup
