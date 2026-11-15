/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Symplectic.WittExtension
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Symplectic.ContinuousAlternatingMap

/-!
# Standard Euclidean Darboux coordinates

A closed two-form, nondegenerate at a point of a finite-dimensional real normed space,
admits centered coordinates in a doubled Euclidean space in which it is the standard
symplectic form. The coordinate parametrization extends to a global diffeomorphism,
but its symplectic property is asserted only near the origin.

`exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq` supplies the nonlinear
change making the form constant. The linear Darboux theorem
`SymplecticForm.exists_isSymplectomorphism` then identifies this constant form with
`stdSymplecticForm`. In particular the sign is the convention
`ω₀((q,p),(q',p')) = ⟪q,p'⟫ - ⟪p,q'⟫`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 3.2 (Darboux's theorem).
-/

public section

open Filter Topology
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Standard Euclidean Darboux coordinates.** A closed `C^r` two-form, `r ≥ 1`,
nondegenerate at `x₀`, is the standard symplectic form in centered coordinates on a
doubled Euclidean space of the same dimension. The diffeomorphism parametrizes the
original space, sends zero to `x₀`, and is symplectic on a neighbourhood of zero.
Only nondegeneracy at `x₀` is assumed; the original open set may be disconnected. -/
theorem exists_diffeomorph_eventually_fderiv_eq_stdSymplecticForm
    {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} {n : ℕ}
    (hdim : Module.finrank ℝ V = 2 * n) (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W)
    (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, V)⟯ V,
      φ 0 = x₀ ∧ ∀ᶠ z in 𝓝 0, φ z ∈ W ∧ ∀ u v,
        ω (φ z) ![fderiv ℝ φ z u, fderiv ℝ φ z v] = stdSymplecticForm u v := by
  -- Read the value at the center as an algebraic symplectic form.
  let σ := SymplecticForm.ofContinuousAlternatingMap (ω x₀) hnd
  have hσ (v w : V) : σ v w = ω x₀ ![v, w] :=
    SymplecticForm.ofContinuousAlternatingMap_apply _ _ v w
  have hdim' : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ V := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin, hdim, two_mul]
  -- Choose the linear standard coordinates, then compose with the nonlinear Darboux map.
  obtain ⟨e₀, he₀⟩ := SymplecticForm.exists_isSymplectomorphism
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin n))) σ hdim'
  let e := e₀.toContinuousLinearEquiv
  obtain ⟨ψ, hψ₀, hψω⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq hr hW hx₀ hω hdω hnd
  let a := (e.toContDiffDiffeomorph r).trans (Diffeomorph.smulAdd r (1 : ℝ) x₀ one_ne_zero)
  have ha (z) : a z = e z + x₀ := by simp [a]
  have ha_fun : ⇑a = fun z ↦ e z + x₀ := funext ha
  have ha' (z) : HasFDerivAt a e.toContinuousLinearMap z := by
    rw [ha_fun]
    exact e.hasFDerivAt.add_const x₀
  let φ := a.trans ψ
  -- Composition of the two diffeomorphisms is evaluation in the affine coordinates.
  have hφa (z) : φ z = ψ (a z) := congrFun (Diffeomorph.coe_trans a ψ) z
  have hφ (z) : φ z = ψ (e z + x₀) := by rw [hφa, ha]
  have hφ₀ : φ 0 = x₀ := by simp [hφ, hψ₀]
  have hφcont : Continuous φ := φ.contMDiff.continuous
  refine ⟨φ, hφ₀, ?_⟩
  have hnear : Tendsto a (𝓝 0) (𝓝 x₀) := by
    have ha₀ : a 0 = x₀ := by simp [ha]
    exact ha₀ ▸ a.contMDiff.continuous.tendsto 0
  have hmem : ∀ᶠ z in 𝓝 0, φ z ∈ W := by
    have ht : Tendsto φ (𝓝 0) (𝓝 x₀) := hφ₀ ▸ hφcont.continuousAt
    exact ht.eventually (hW.mem_nhds hx₀)
  filter_upwards [hnear.eventually hψω, hmem] with z hz hzW
  refine ⟨hzW, fun u v ↦ ?_⟩
  have hψdiff : DifferentiableAt ℝ ψ (a z) :=
    (ψ.differentiable (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr).ne')) (a z)
  -- Pullback by the composite is the pullback by its linear coordinate map.
  have hderiv : fderiv ℝ φ z = (fderiv ℝ ψ (a z)).comp e.toContinuousLinearMap :=
    (hψdiff.hasFDerivAt.comp z (ha' z)).fderiv
  have hpull := DFunLike.congr_fun hz ![e u, e v]
  have hpull' : ω (ψ (a z)) ![fderiv ℝ ψ (a z) (e u),
      fderiv ℝ ψ (a z) (e v)] = σ (e u) (e v) := by
    have htuple : (fderiv ℝ ψ (a z)) ∘ ![e u, e v] =
        ![fderiv ℝ ψ (a z) (e u), fderiv ℝ ψ (a z) (e v)] := by
      ext i
      fin_cases i <;> rfl
    simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      htuple, ← hσ] using hpull
  calc
    ω (φ z) ![fderiv ℝ φ z u, fderiv ℝ φ z v] = σ (e u) (e v) := by
      simpa only [hφa, hderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe] using hpull'
    _ = stdSymplecticForm u v := he₀.apply u v

/-- **A centered standard Darboux chart.** A closed `C^r` two-form nondegenerate at `x₀`
is the pullback of the standard symplectic form by a chart sending `x₀` to zero.
The chart extends to a diffeomorphism of the model spaces; the pullback identity
is local near `x₀`. This is the chart-direction counterpart of
`exists_diffeomorph_eventually_fderiv_eq_stdSymplecticForm`. -/
theorem exists_diffeomorph_eventually_stdSymplecticForm_fderiv_eq
    {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} {n : ℕ}
    (hdim : Module.finrank ℝ V = 2 * n) (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W)
    (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ φ : V ≃ₘ^r⟮𝓘(ℝ, V),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      φ x₀ = 0 ∧ ∀ᶠ x in 𝓝 x₀, x ∈ W ∧ ∀ u v,
        stdSymplecticForm (fderiv ℝ φ x u) (fderiv ℝ φ x v) = ω x ![u, v] := by
  obtain ⟨ψ, hψ₀, hψω⟩ :=
    exists_diffeomorph_eventually_fderiv_eq_stdSymplecticForm hdim hr hW hx₀ hω hdω hnd
  have hψinv : ψ.symm x₀ = 0 := ψ.symm_apply_eq.mpr hψ₀.symm
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hr).ne'
  refine ⟨ψ.symm, hψinv, ?_⟩
  have ht : Tendsto ψ.symm (𝓝 x₀) (𝓝 0) :=
    hψinv ▸ ψ.symm.contMDiff.continuous.tendsto x₀
  filter_upwards [ht.eventually hψω] with x hx
  refine ⟨by simpa only [ψ.apply_symm_apply] using hx.1, fun u v ↦ ?_⟩
  have hpull := hx.2 (fderiv ℝ ψ.symm x u) (fderiv ℝ ψ.symm x v)
  simpa only [ψ.apply_symm_apply, ψ.fderiv_apply_fderiv_symm_apply hr0] using hpull.symm

end TauCeti
