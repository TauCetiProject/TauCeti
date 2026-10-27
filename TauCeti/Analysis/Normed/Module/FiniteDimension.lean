/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-dimensional normed spaces

Over a complete nontrivially normed field every linear functional on a finite-dimensional normed
space is continuous, so the continuous dual `E →L[𝕜] 𝕜` coincides with the algebraic dual
`Module.Dual 𝕜 E`. Mathlib records that coincidence as the linear equivalence
`LinearMap.toContinuousLinearMap`; this file reads off the one consequence of it that dimension
counts need, namely that the continuous dual has the same dimension as the space.

Two complements of the same space in a finite-dimensional space are continuously linearly
isomorphic. This allows pointwise choices of complements to be identified with a single model.
In real dimension one, equal-norm vectors agree up to sign; in particular, a nonzero-radius
sphere consists of two antipodal points.

A linear endomorphism of a finite-dimensional normed space that is bounded below by `c > 0` is
injective, hence invertible, and its inverse is bounded by `c⁻¹`.

A family of bases whose vectors depend continuously on a parameter has frame and coordinate maps
that depend continuously on the parameter in the operator norm.

## Main results

* `ContinuousLinearMap.dual_finrank_eq`: in finite dimensions the continuous dual has the same
  dimension as the space.
* `TauCeti.nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv`: complements of
  the same space in a finite-dimensional space are isomorphic.
* `TauCeti.continuous_det_div_conj`: the determinant phase `det A / conj (det A)` of a continuous
  family of continuous linear automorphisms varies continuously.
* `Module.Basis.continuous_equivFunL_symm_of_continuous`,
  `Module.Basis.continuous_equivFunL_of_continuous`: a family of bases whose vectors depend
  continuously on a parameter has continuously varying frame and coordinate maps.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- In finite dimensions the continuous dual `E →L[𝕜] 𝕜` has the same dimension as `E`: every
linear functional on a finite-dimensional space is continuous, so the continuous dual coincides
with the algebraic one. -/
theorem _root_.ContinuousLinearMap.dual_finrank_eq :
    Module.finrank 𝕜 (E →L[𝕜] 𝕜) = Module.finrank 𝕜 E := by
  rw [← LinearEquiv.finrank_eq
    (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] E →L[𝕜] 𝕜)]
  exact Subspace.dual_finrank_eq

/-- Over a complete field, two complements of the same space `V` in a finite-dimensional space `W`
are continuously linearly isomorphic: both have dimension `finrank W - finrank V`. -/
theorem nonempty_continuousLinearEquiv_of_prod_continuousLinearEquiv {V W F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [AddCommGroup V] [TopologicalSpace V] [Module 𝕜 V]
    [AddCommGroup W] [TopologicalSpace W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e : (V × F) ≃L[𝕜] W) (e' : (V × F') ≃L[𝕜] W) : Nonempty (F ≃L[𝕜] F') := by
  have : FiniteDimensional 𝕜 (V × F) := e.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 (V × F') := e'.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 F :=
    .of_injective (LinearMap.inr 𝕜 V F) LinearMap.inr_injective
  have : FiniteDimensional 𝕜 F' :=
    .of_injective (LinearMap.inr 𝕜 V F') LinearMap.inr_injective
  have : FiniteDimensional 𝕜 V :=
    .of_injective (LinearMap.inl 𝕜 V F) LinearMap.inl_injective
  apply FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
  have h := e.toLinearEquiv.finrank_eq.trans e'.toLinearEquiv.finrank_eq.symm
  rw [Module.finrank_prod, Module.finrank_prod] at h
  omega

/-- In a one-dimensional real normed space, vectors of equal norm agree up to sign. -/
theorem eq_or_eq_neg_of_norm_eq_of_finrank_eq_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : Module.finrank ℝ V = 1) {x y : V} (hn : ‖x‖ = ‖y‖) :
    x = y ∨ x = -y := by
  by_cases hy : y = 0
  · left
    simpa [hy] using hn
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h hy x
  have hc : |c| = 1 := by
    simpa [norm_smul, Real.norm_eq_abs, norm_ne_zero_iff.mpr hy] using hn
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ 1)).mp hc with hc | hc <;>
    simp [hc]

section Star

open scoped ComplexConjugate

variable {𝕜 E X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [StarRing 𝕜]
  [ContinuousStar 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace X]

/-- The determinant phase `det A / conj (det A)` of a continuous family of continuous linear
automorphisms varies continuously. Over `ℂ` this is the Maslov phase `ρ(L, A L)` of a maximal
totally real subspace `L`. -/
theorem continuous_det_div_conj (A : X → E ≃L[𝕜] E)
    (hA : Continuous fun x => (A x : E →L[𝕜] E)) :
    Continuous fun x => LinearMap.det ((A x).toLinearEquiv : E →ₗ[𝕜] E) /
      conj (LinearMap.det ((A x).toLinearEquiv : E →ₗ[𝕜] E)) := by
  have hd : Continuous fun x => LinearMap.det ((A x).toLinearEquiv : E →ₗ[𝕜] E) :=
    ContinuousLinearMap.continuous_det.comp hA
  refine hd.div (continuous_star.comp hd) fun x => (map_ne_zero _).2 ?_
  rw [← LinearEquiv.coe_det]
  exact (LinearEquiv.det (A x).toLinearEquiv).ne_zero

end Star

end TauCeti

namespace Module.Basis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {Y : Type*} [TopologicalSpace Y] {ι : Type*} [Finite ι] {B : Y → Basis ι 𝕜 F}

/-- **Continuity of a family of frames.** If every vector of a family of bases depends continuously
on the parameter, then so does the frame `x ↦ ∑ i, x i • B y i`, in the operator norm. -/
theorem continuous_equivFunL_symm_of_continuous (h : ∀ i, Continuous fun y ↦ B y i) :
    Continuous fun y ↦ ((B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F) := by
  have := Fintype.ofFinite ι
  refine continuous_clm_apply.2 fun x ↦ ?_
  simp only [ContinuousLinearEquiv.coe_coe, equivFunL_symm_apply]
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.smul (h i)

/-- **Continuity of a family of coordinate maps.** If every vector of a family of bases depends
continuously on the parameter, then so does the coordinate map `F → ι → 𝕜`, in the operator
norm. -/
theorem continuous_equivFunL_of_continuous (h : ∀ i, Continuous fun y ↦ B y i) :
    Continuous fun y ↦ ((B y).equivFunL : F →L[𝕜] ι → 𝕜) := by
  have := Fintype.ofFinite ι
  have h' : (fun y ↦ ((B y).equivFunL : F →L[𝕜] ι → 𝕜)) =
      fun y ↦ ((B y).equivFunL.symm : (ι → 𝕜) →L[𝕜] F).inverse := by
    ext1 y
    rw [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.symm_symm]
  rw [h', continuous_iff_continuousAt]
  intro y
  have := (B y).finiteDimensional_of_finite
  have := FiniteDimensional.complete 𝕜 F
  exact ContinuousAt.comp (g := ContinuousLinearMap.inverse)
    (contDiffAt_map_inverse (n := 0) (B y).equivFunL.symm).continuousAt
    (continuous_equivFunL_symm_of_continuous h).continuousAt

end Module.Basis

namespace LinearMap

variable {K V : Type*} [DivisionRing K] [NormedAddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A linear endomorphism of a finite-dimensional normed space bounded below by `c > 0` is
invertible, with inverse bounded by `c⁻¹`. -/
theorem exists_comp_eq_id_of_mul_norm_le {C : V →ₗ[K] V} {c : ℝ} (hc : 0 < c)
    (hC : ∀ v, c * ‖v‖ ≤ ‖C v‖) :
    ∃ G : V →ₗ[K] V, C ∘ₗ G = .id ∧ G ∘ₗ C = .id ∧ ∀ v, ‖G v‖ ≤ c⁻¹ * ‖v‖ := by
  have hinj : Function.Injective C := (injective_iff_map_eq_zero C).mpr fun v hv ↦
    norm_eq_zero.mp <| le_antisymm (nonpos_of_mul_nonpos_right (by simpa [hv] using hC v) hc)
      (norm_nonneg v)
  set e := LinearEquiv.ofInjectiveEndo C hinj
  refine ⟨e.symm, LinearEquiv.ofInjectiveEndo_right_inv C hinj,
    LinearEquiv.ofInjectiveEndo_left_inv C hinj, fun v ↦ ?_⟩
  rw [le_inv_mul_iff₀ hc]
  have hv : C (e.symm v) = v := by
    rw [← LinearEquiv.coe_ofInjectiveEndo C hinj]
    exact e.apply_symm_apply v
  simpa [hv] using hC (e.symm v)

end LinearMap

end
