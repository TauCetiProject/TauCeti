/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.CharPowerSeries
import Mathlib.Topology.Instances.Matrix

/-!
# Cyclicity of Fredholm determinants of row-compact operators

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1` and Tate scalars, and
`I`, `J` discrete index types. For an endomorphism `w` of the model space `C₀(I, R)`, the
Fredholm determinant `det (1 - T w)` is the principal-minor series
`w.matrixCoeff.charPowerSeries` of its matrix.

This file proves that for continuous linear maps `u : C₀(J, R) →L[R] C₀(I, R)` and
`v : C₀(I, R) →L[R] C₀(J, R)`, one of which is row compact, the determinants of the two
composites agree:

`det (1 - T (u ∘ v)) = det (1 - T (v ∘ u))`
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_comp_comm`).

Both composites are endomorphisms, of `C₀(I, R)` and of `C₀(J, R)` respectively, and both are
row compact by the ideal property, so both series are entire
(`Matrix.isRestricted_charPowerSeries`). Consequently the Fredholm
determinant of a row-compact endomorphism is invariant under conjugation by any continuous linear
equivalence of model spaces, possibly between different index types
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_conj`); no isometry is assumed.

The proof first treats an output truncation `π_S ∘ u` to a finite set `S` of coordinates. The
determinant of `π_S ∘ u ∘ v` is the polynomial `det (1 - X (u ∘ v)_S)` of the finite block on
`S`, while `v ∘ π_S ∘ u` factors through the finite free module `R ^ S`; its finite compressions
are products of rectangular blocks, to which the finite identity `det (1 - X A B) = det (1 - X B A)`
(`Matrix.charpolyRev_mul_comm`) applies. The general case follows by approximating `u` by its
output truncations, since each Fredholm coefficient is continuous in operator norm on row-compact
operators (`ContinuousLinearMap.tendsto_charCoeff_matrixCoeff_of_tendsto`).

## Main results

* `ContinuousLinearMap.tendsto_charCoeff_matrixCoeff_of_tendsto`: the coefficients of the
  Fredholm determinant are continuous in operator norm on row-compact endomorphisms.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_comp_comm`: cyclicity
  `det (1 - T (u ∘ v)) = det (1 - T (v ∘ u))` when `u` is row compact.
* `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_conj`: invariance under
  conjugation by a continuous linear equivalence.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I J R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

/-- The principal minors of each size of a row-compact endomorphism of a model space form a
summable family, so the coefficients of its Fredholm determinant are genuine sums. -/
theorem IsRowCompact.summable_principalMinor {w : C₀(I, R) →L[R] C₀(I, R)}
    (hw : w.IsRowCompact) (n : ℕ) :
    Summable fun s : {s : Finset I // s.card = n} ↦ w.matrixCoeff.principalMinor s :=
  Matrix.summable_principalMinor hw.norm_matrixCoeff_le_rowNorm hw.tendsto_rowNorm n

variable [TauCeti.NormedRing.IsTate R]

/-- **Continuity of Fredholm coefficients in operator norm.** If row-compact endomorphisms
`w a` of a model space converge in operator norm to a row-compact endomorphism `w₀`, then each
coefficient of the Fredholm determinant of `w a` converges to the corresponding coefficient for
`w₀`. -/
theorem tendsto_charCoeff_matrixCoeff_of_tendsto {α : Type*} {l : Filter α}
    {w : α → C₀(I, R) →L[R] C₀(I, R)} {w₀ : C₀(I, R) →L[R] C₀(I, R)}
    (hw : ∀ᶠ a in l, (w a).IsRowCompact) (hw₀ : w₀.IsRowCompact)
    (h : Tendsto (fun a ↦ ‖w a - w₀‖) l (𝓝 0)) (n : ℕ) :
    Tendsto (fun a ↦ (w a).matrixCoeff.charCoeff n) l (𝓝 (w₀.matrixCoeff.charCoeff n)) := by
  refine TauCeti.tendsto_charCoeff_of_tendstoUniformly n w₀.norm_matrixCoeff_le
    (hw.mono fun a ha ↦ ha.summable_principalMinor n) (hw₀.summable_principalMinor n)
    (tendstoUniformly_matrixCoeff_of_tendsto h)

/-- **Cyclicity for an output truncation.** If `π_S` is the coordinate projection onto a finite
set `S` of output coordinates of `u`, then `π_S ∘ u ∘ v` and `v ∘ π_S ∘ u` have the same Fredholm
determinant, namely `det (1 - X (u ∘ v)_S)` for the finite block of `u ∘ v` on `S`. -/
private theorem charPowerSeries_matrixCoeff_comp_indicatorCLM_comp (S : Finset I)
    (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(I, R) →L[R] C₀(J, R)) :
    (v.comp ((indicatorCLM R (S : Set I)).comp u)).matrixCoeff.charPowerSeries =
      ((indicatorCLM R (S : Set I)).comp (u.comp v)).matrixCoeff.charPowerSeries := by
  set W := v.comp ((indicatorCLM R (S : Set I)).comp u)
  have hW : W.IsRowCompact := (isRowCompact_indicatorCLM_comp S u).clm_comp v
  -- The finite compressions of `W` factor through the finite free module `R ^ S`.
  have hfactor (T : Finset J) :
      W.matrixCoeff.submatrix (Subtype.val : T → J) (Subtype.val : T → J) =
        v.matrixCoeff.submatrix (Subtype.val : T → J) (Subtype.val : S → I) *
          u.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : T → J) := by
    ext j j'
    rw [Matrix.submatrix_apply, matrixCoeff_comp, Matrix.mul_apply,
      tsum_eq_sum (s := S) fun i hi ↦ by simp [hi], ← Finset.sum_coe_sort S]
    simp
  -- The rectangular products `u_{S,T} v_{T,S}` converge to the finite block of `u ∘ v` on `S`.
  have hblock : Tendsto (fun T : Finset J ↦
      u.matrixCoeff.submatrix (Subtype.val : S → I) (Subtype.val : T → J) *
        v.matrixCoeff.submatrix (Subtype.val : T → J) (Subtype.val : S → I)) atTop
      (𝓝 ((u.comp v).matrixCoeff.submatrix (Subtype.val : S → I) Subtype.val)) := by
    refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun i' ↦ ?_
    refine Tendsto.congr (fun T ↦ ?_) (u.hasSum_matrixCoeff_comp v i i')
    simp [Matrix.mul_apply, ← Finset.sum_coe_sort T]
  ext n
  have hcont : Continuous fun N : Matrix S S R ↦ N.charpolyRev.coeff n := by
    simp_rw [Matrix.coeff_charpolyRev]
    exact continuous_const.mul (continuous_finsetSum _ fun s _ ↦
      (continuous_id.matrix_submatrix _ _).matrix_det)
  have hlim := TauCeti.tendsto_coeff_charpolyRev_finiteCompression n (hW.summable_principalMinor n)
  -- Compare the limits of the compressions of `W` and of the products `u_{S,T} v_{T,S}`, using
  -- `det (1 - X A B) = det (1 - X B A)` for each `T`.
  rw [Matrix.coeff_charPowerSeries, tendsto_nhds_unique (hlim.congr fun T ↦ ?_)
    ((hcont.tendsto _).comp hblock)]
  swap
  · rw [hfactor, Matrix.charpolyRev_mul_comm, Function.comp_apply]
  rw [charPowerSeries_matrixCoeff_indicatorCLM_comp, Polynomial.coeff_coe]

/-- **Cyclicity of Fredholm determinants.** If `u : C₀(J, R) →L[R] C₀(I, R)` is row compact and
`v : C₀(I, R) →L[R] C₀(J, R)` is any continuous linear map, the endomorphisms `u ∘ v` of
`C₀(I, R)` and `v ∘ u` of `C₀(J, R)` have the same Fredholm determinant:
`det (1 - T (u ∘ v)) = det (1 - T (v ∘ u))`. If instead `v` is row compact, apply this to `v`. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_comp_comm {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (v : C₀(I, R) →L[R] C₀(J, R)) :
    (u.comp v).matrixCoeff.charPowerSeries = (v.comp u).matrixCoeff.charPowerSeries := by
  let uS := fun S : Finset I ↦ (indicatorCLM R (S : Set I)).comp u
  have huS : Tendsto (fun S ↦ ‖uS S - u‖) atTop (𝓝 0) :=
    hu.tendsto_ringOpNorm_indicatorCLM_comp_sub
  -- Approximate `u` by its output truncations, for which cyclicity holds by the finite case.
  have hleft : Tendsto (fun S ↦ ‖(uS S).comp v - u.comp v‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ ringOpNorm_nonneg _)
      (fun S ↦ (sub_comp (uS S) u v ▸ ringOpNorm_comp_le (uS S - u) v))
      (by simpa using huS.mul_const ‖v‖)
  have hright : Tendsto (fun S ↦ ‖v.comp (uS S) - v.comp u‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ ringOpNorm_nonneg _)
      (fun S ↦ (comp_sub v (uS S) u ▸ ringOpNorm_comp_le v (uS S - u)))
      (by simpa using huS.const_mul ‖v‖)
  ext n
  simp only [Matrix.coeff_charPowerSeries]
  refine tendsto_nhds_unique ((tendsto_charCoeff_matrixCoeff_of_tendsto
    (.of_forall fun S ↦ (isRowCompact_indicatorCLM_comp S u).comp_clm v) (hu.comp_clm v)
    hleft n).congr fun S ↦ ?_) (tendsto_charCoeff_matrixCoeff_of_tendsto
      (.of_forall fun S ↦ (isRowCompact_indicatorCLM_comp S u).clm_comp v) (hu.clm_comp v)
      hright n)
  rw [← Matrix.coeff_charPowerSeries, ← Matrix.coeff_charPowerSeries, comp_assoc,
    charPowerSeries_matrixCoeff_comp_indicatorCLM_comp]

/-- Cyclicity of Fredholm determinants for endomorphisms of one model space:
`det (1 - T (u * v)) = det (1 - T (v * u))` when `u` is row compact. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_mul_comm {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (v : C₀(I, R) →L[R] C₀(I, R)) :
    (u * v).matrixCoeff.charPowerSeries = (v * u).matrixCoeff.charPowerSeries :=
  hu.charPowerSeries_matrixCoeff_comp_comm v

/-- **Invariance under conjugation.** The Fredholm determinant of a row-compact endomorphism `u`
of `C₀(I, R)` is unchanged by conjugation `e ∘ u ∘ e⁻¹` by a continuous linear equivalence
`e : C₀(I, R) ≃L[R] C₀(J, R)`, which need not be an isometry. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_conj {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (e : C₀(I, R) ≃L[R] C₀(J, R)) :
    Matrix.charPowerSeries ((e : C₀(I, R) →L[R] C₀(J, R)).comp
      (u.comp (e.symm : C₀(J, R) →L[R] C₀(I, R)))).matrixCoeff =
        u.matrixCoeff.charPowerSeries := by
  rw [← comp_assoc,
    (hu.clm_comp (e : C₀(I, R) →L[R] C₀(J, R))).charPowerSeries_matrixCoeff_comp_comm,
    ← comp_assoc, ContinuousLinearEquiv.coe_symm_comp_coe, id_comp]

end ContinuousLinearMap
