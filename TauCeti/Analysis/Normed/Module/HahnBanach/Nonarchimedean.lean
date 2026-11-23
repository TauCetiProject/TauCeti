/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.LocallyConvex.HahnBanach.Nonarchimedean
import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Module.Bases.Orthogonal
import TauCeti.Analysis.Normed.Module.Seminorm.Nonarchimedean

/-!
# Nonarchimedean Hahn–Banach theorem for normed spaces

Over a nontrivially normed field, every continuous linear operator from a subspace of an
ultrapseudometric seminormed space `V` into a spherically complete ultrapseudometric space `W`
extends to all of `V` with the exact same operator norm. Unlike the archimedean Hahn–Banach
theorem, the target space `W` may be arbitrary (in particular infinite-dimensional) as long as it
is spherically complete, and the norm values of `V` need not lie in the value group of the scalar
field `K`.

When the scalar field `K` itself is ultrametric and spherically complete, this yields the standard
corollaries:
* exact separation of a vector outside the closure of a subspace by a functional of norm
  `(infDist v U)⁻¹`;
* exact norm-preserving functionals (`ℓ x = 1`, `‖ℓ‖ = ‖x‖⁻¹`) for every vector of nonzero norm;
* norm preservation of the canonical evaluation map `V →ₗᵢ[K] V''` into the strong bidual, without
  assuming `‖V‖ ⊆ ‖K‖` (hence an isometric embedding when `V` is normed);
* characterization of subspace closures by vanishing continuous functionals, and separation of
  points by `StrongDual K V` when `V` is normed;
* contractive (`‖P‖ ≤ 1`) continuous projections onto every spherically complete subspace and, in
  particular, onto every finite-dimensional subspace, making all such subspaces topologically
  complemented.

## Main results

* `ContinuousLinearMap.exists_extension_norm_eq_of_sphericallyComplete`: norm-preserving
  extension of a continuous linear operator from a subspace into a spherically complete
  ultrapseudometric space.
* `LinearIsometry.exists_extension_norm_eq_of_sphericallyComplete`: norm-preserving extension along
  a linear isometric embedding.
* `Submodule.exists_strongDual_eq_zero_apply_eq_one_norm_eq_inv_infDist`: separation from a
  subspace with exact operator norm `(infDist v U)⁻¹`.
* `TauCeti.exists_strongDual_apply_eq_one_norm_eq_inv`: existence of a continuous functional with
  `ℓ x = 1` and `‖ℓ‖ = ‖x‖⁻¹`.
* `NormedSpace.norm_inclusionInDoubleDual_of_sphericallyComplete` and
  `NormedSpace.inclusionInDoubleDualLiOfSphericallyComplete`: the canonical map into the strong
  bidual preserves norms (and is an isometric embedding when `V` is normed).
* `Submodule.mem_closure_iff_forall_strongDual_eq_zero_of_sphericallyComplete` and
  `TauCeti.separatingDual_of_sphericallyComplete`: closure characterization by vanishing continuous
  functionals, and separating dual when `V` is normed.
* `Submodule.exists_proj_norm_le_one_of_sphericallyComplete`,
  `Submodule.closedComplemented_of_sphericallyComplete`,
  `Submodule.exists_proj_norm_le_one_of_finiteDimensional_of_sphericallyComplete`, and
  `Submodule.closedComplemented_of_finiteDimensional_of_sphericallyComplete`: contractive
  projections and topological complementation of spherically complete and finite-dimensional
  subspaces.

## References

* A. W. Ingleton, *The Hahn–Banach theorem for non-Archimedean-valued fields*,
  Proc. Cambridge Philos. Soc. 48 (1952), 41–45.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §9, Proposition 9.2 and
  Corollaries 9.3–9.4.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*,
  Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010, Chapter 4.
-/

public section

open Metric Set Submodule Topology
open scoped NNReal

namespace ContinuousLinearMap

variable {K V W : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]
  [SeminormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]
  [TauCeti.SphericallyCompleteSpace W]

/-- **Nonarchimedean Hahn–Banach theorem** (Ingleton's theorem): every continuous linear map from
a subspace of an ultrapseudometric seminormed space into a spherically complete ultrapseudometric
space extends to the whole space with the same operator norm. -/
theorem exists_extension_norm_eq_of_sphericallyComplete {U : Submodule K V} (f : U →L[K] W) :
    ∃ g : V →L[K] W, (∀ u : U, g u = f u) ∧ ‖g‖ = ‖f‖ := by
  have hna : IsNonarchimedean (‖f‖₊ • normSeminorm K V) :=
    (IsUltrametricDist.isNonarchimedean_norm (R := V)).smul_seminorm ‖f‖₊
  have hcont : Continuous (‖f‖₊ • normSeminorm K V) := continuous_norm.const_smul ‖f‖₊
  obtain ⟨g, hgf, hgp⟩ :=
    f.toLinearMap.exists_continuous_extension_norm_le_of_isNonarchimedean hna hcont
      fun u ↦ f.le_opNorm u
  refine ⟨g, hgf, le_antisymm (g.opNorm_le_bound (norm_nonneg f) hgp) ?_⟩
  exact f.opNorm_le_bound (norm_nonneg g) fun u ↦ by simpa [hgf u] using g.le_opNorm (u : V)

end ContinuousLinearMap

namespace LinearIsometry

variable {K E F W : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]
  [SeminormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]
  [TauCeti.SphericallyCompleteSpace W]

/-- A continuous linear map into a spherically complete ultrapseudometric space extends along a
linear isometric embedding into an ultrapseudometric seminormed space with the same operator
norm. -/
theorem exists_extension_norm_eq_of_sphericallyComplete (i : E →ₗᵢ[K] F) (f : E →L[K] W) :
    ∃ g : F →L[K] W, g.comp i.toContinuousLinearMap = f ∧ ‖g‖ = ‖f‖ := by
  let e := i.equivRange
  let f' : i.toLinearMap.range →L[K] W := f.comp e.symm.toLinearIsometry.toContinuousLinearMap
  have hf'e (x : E) : f' (e x) = f x := by
    simpa only [f', ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using congrArg f (e.symm_apply_apply x)
  have hnorm' : ‖f'‖ = ‖f‖ := le_antisymm
    (f'.opNorm_le_bound (norm_nonneg f) fun x ↦
      (f.le_opNorm (e.symm x)).trans_eq (by rw [e.symm.norm_map]))
    (f.opNorm_le_bound (norm_nonneg f') fun x ↦ by
      simpa only [hf'e, e.norm_map] using f'.le_opNorm (e x))
  obtain ⟨g, hg, hnorm⟩ := f'.exists_extension_norm_eq_of_sphericallyComplete
  refine ⟨g, ?_, hnorm.trans hnorm'⟩
  ext x
  exact (hg (e x)).trans (hf'e x)

end LinearIsometry

namespace Submodule

section Separation

variable {K V : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [TauCeti.SphericallyCompleteSpace K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- Given a vector `v` outside the closure of a submodule `U` of an ultrapseudometric seminormed
space over a spherically complete ultrametric field, there exists a continuous linear functional
vanishing on `U`, taking the value `1` at `v`, and having operator norm exactly
`(Metric.infDist v U)⁻¹`. The distance `Metric.infDist v U` need not lie in the value group of
`K`. -/
theorem exists_strongDual_eq_zero_apply_eq_one_norm_eq_inv_infDist (U : Submodule K V) {v : V}
    (hv : v ∉ closure (U : Set V)) :
    ∃ ℓ : StrongDual K V,
      (∀ u ∈ U, ℓ u = 0) ∧ ℓ v = 1 ∧ ‖ℓ‖ = (Metric.infDist v (U : Set V))⁻¹ := by
  let d : ℝ := Metric.infDist v (U : Set V)
  have hd_pos : 0 < d := (Metric.infDist_pos_iff_notMem_closure ⟨0, U.zero_mem⟩).1 hv
  have hdist (u : V) (hu : u ∈ U) : d ≤ (normSeminorm K V) (u - v) := by
    simpa only [coe_normSeminorm, ← dist_eq_norm, dist_comm] using
      Metric.infDist_le_dist_of_mem hu (x := v)
  obtain ⟨ℓ, hℓU, hℓv, hℓ_le⟩ :=
    U.exists_strongDual_eq_zero_apply_eq_one_norm_le_of_isNonarchimedean
      IsUltrametricDist.isNonarchimedean_norm continuous_norm hd_pos hdist
  refine ⟨ℓ, hℓU, hℓv, le_antisymm (ℓ.opNorm_le_bound (inv_nonneg.2 hd_pos.le) hℓ_le) ?_⟩
  have hvu (u : V) (hu : u ∈ U) : 1 ≤ ‖ℓ‖ * dist v u := by
    have hle := ℓ.le_opNorm (v - u)
    rw [map_sub, hℓv, hℓU u hu, sub_zero, norm_one, ← dist_eq_norm] at hle
    exact hle
  have hℓ_pos : 0 < ‖ℓ‖ := by
    by_contra! hle
    have h0 : ‖ℓ‖ = 0 := le_antisymm hle (norm_nonneg ℓ)
    have h := hvu 0 U.zero_mem
    rw [h0, zero_mul] at h
    linarith
  have hinv_le : ‖ℓ‖⁻¹ ≤ d :=
    (Metric.le_infDist ⟨0, U.zero_mem⟩).2 fun u hu ↦
      (inv_le_iff_one_le_mul₀' hℓ_pos).2 (hvu u hu)
  have hinv := (inv_le_inv₀ hd_pos (inv_pos.2 hℓ_pos)).2 hinv_le
  rwa [inv_inv] at hinv

end Separation

end Submodule

namespace TauCeti

section DualVector

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K]
  {V : Type*} [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- For every vector `x` of nonzero norm in an ultrapseudometric seminormed space over a
spherically complete ultrametric field, there exists a continuous linear functional `ℓ` with
`ℓ x = 1` and `‖ℓ‖ = ‖x‖⁻¹`. -/
theorem exists_strongDual_apply_eq_one_norm_eq_inv {x : V} (hx : ‖x‖ ≠ 0) :
    ∃ ℓ : StrongDual K V, ℓ x = 1 ∧ ‖ℓ‖ = ‖x‖⁻¹ := by
  have hinf : Metric.infDist x ((⊥ : Submodule K V) : Set V) = ‖x‖ := by
    rw [Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
  have hxcl : x ∉ closure ((⊥ : Submodule K V) : Set V) := by
    rw [Metric.infDist_pos_iff_notMem_closure ⟨0, Submodule.zero_mem ⊥⟩, hinf]
    exact (norm_nonneg x).lt_of_ne' hx
  obtain ⟨ℓ, -, hℓx, hℓnorm⟩ :=
    (⊥ : Submodule K V).exists_strongDual_eq_zero_apply_eq_one_norm_eq_inv_infDist hxcl
  exact ⟨ℓ, hℓx, hℓnorm.trans (congrArg Inv.inv hinf)⟩

end DualVector

end TauCeti

namespace NormedSpace

section BidualIsometry

variable (K V : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [TauCeti.SphericallyCompleteSpace K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- The canonical evaluation map from an ultrapseudometric seminormed space over a spherically
complete ultrametric field into its strong bidual preserves norms exactly, even when the values of
the norm on `V` do not lie in the value group of `K`. -/
@[simp]
theorem norm_inclusionInDoubleDual_of_sphericallyComplete (x : V) :
    ‖inclusionInDoubleDual K V x‖ = ‖x‖ := by
  refine le_antisymm (double_dual_bound K V x) ?_
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    exact norm_nonneg (inclusionInDoubleDual K V x)
  · obtain ⟨ℓ, hℓx, hℓnorm⟩ := TauCeti.exists_strongDual_apply_eq_one_norm_eq_inv K hx
    have hle : 1 ≤ ‖inclusionInDoubleDual K V x‖ * ‖x‖⁻¹ := by
      have h := (inclusionInDoubleDual K V x).le_opNorm ℓ
      simpa only [dual_def, hℓx, norm_one, hℓnorm] using h
    have hxpos : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne' hx
    rwa [← div_eq_mul_inv, one_le_div hxpos] at hle

/-- The canonical evaluation map into the strong bidual as a linear isometry over a spherically
complete ultrametric field. -/
noncomputable def inclusionInDoubleDualLiOfSphericallyComplete :
    V →ₗᵢ[K] StrongDual K (StrongDual K V) :=
  { inclusionInDoubleDual K V with
    norm_map' := norm_inclusionInDoubleDual_of_sphericallyComplete K V }

@[simp]
theorem inclusionInDoubleDualLiOfSphericallyComplete_apply (x : V) :
    inclusionInDoubleDualLiOfSphericallyComplete K V x = inclusionInDoubleDual K V x :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_inclusionInDoubleDualLiOfSphericallyComplete :
    (inclusionInDoubleDualLiOfSphericallyComplete K V).toContinuousLinearMap =
      inclusionInDoubleDual K V := by
  ext x f
  rfl

variable {V}

/-- If `‖f x‖ ≤ M * ‖f‖` for every continuous linear functional `f` on an ultrapseudometric
seminormed space over a spherically complete ultrametric field, then `‖x‖ ≤ M`. -/
theorem norm_le_dual_bound_of_sphericallyComplete (x : V) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ f : StrongDual K V, ‖f x‖ ≤ M * ‖f‖) : ‖x‖ ≤ M := by
  rw [← norm_inclusionInDoubleDual_of_sphericallyComplete K V x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

end BidualIsometry

end NormedSpace

namespace Submodule

section Closure

variable {K V : Type*} [NormedField K] [IsUltrametricDist K]
  [TauCeti.SphericallyCompleteSpace K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- In an ultrapseudometric seminormed space over a spherically complete ultrametric field, a
vector lies in the closure of a submodule `U` iff every continuous linear functional vanishing on
`U` vanishes at `v`. -/
theorem mem_closure_iff_forall_strongDual_eq_zero_of_sphericallyComplete (U : Submodule K V)
    {v : V} : v ∈ closure (U : Set V) ↔ ∀ ℓ : StrongDual K V, (∀ u ∈ U, ℓ u = 0) → ℓ v = 0 :=
  (norm_withSeminorms K V).mem_closure_iff_forall_strongDual_eq_zero_of_isNonarchimedean
    (fun _ ↦ IsUltrametricDist.isNonarchimedean_norm) U

end Closure

end Submodule

namespace TauCeti

/-- Every ultrametric normed space over a spherically complete ultrametric field has separating
continuous dual. Not an instance to avoid adding a `SphericallyCompleteSpace` branch to every
`SeparatingDual` typeclass search. -/
theorem separatingDual_of_sphericallyComplete (K V : Type*) [NormedField K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] [NormedAddCommGroup V] [NormedSpace K V]
    [IsUltrametricDist V] : SeparatingDual K V :=
  (norm_withSeminorms K V).separatingDual_of_isNonarchimedean
    fun _ ↦ IsUltrametricDist.isNonarchimedean_norm

end TauCeti

namespace Submodule

section Projections

variable {K V : Type*} [NormedField K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- Every spherically complete submodule of an ultrapseudometric seminormed space admits a
continuous contractive projection onto it. -/
theorem exists_proj_norm_le_of_sphericallyComplete (U : Submodule K V)
    [TauCeti.SphericallyCompleteSpace U] :
    ∃ P : V →L[K] U, (∀ u : U, P u = u) ∧ ∀ x, ‖P x‖ ≤ ‖x‖ :=
  (LinearMap.id (R := K) (M := U)).exists_continuous_extension_norm_le_of_isNonarchimedean
    (p := normSeminorm K V) IsUltrametricDist.isNonarchimedean_norm continuous_norm
    fun _ ↦ le_rfl

/-- Every spherically complete submodule of an ultrapseudometric seminormed space is topologically
complemented. -/
theorem closedComplemented_of_sphericallyComplete (U : Submodule K V)
    [TauCeti.SphericallyCompleteSpace U] : U.ClosedComplemented :=
  let ⟨P, hP, _⟩ := U.exists_proj_norm_le_of_sphericallyComplete
  ⟨P, hP⟩

/-- Every finite-dimensional submodule of an ultrapseudometric seminormed space over a spherically
complete ultrametric field is topologically complemented. -/
theorem closedComplemented_of_finiteDimensional_of_sphericallyComplete [IsUltrametricDist K]
    [TauCeti.SphericallyCompleteSpace K] (U : Submodule K V) [FiniteDimensional K U] :
    U.ClosedComplemented :=
  have : TauCeti.SphericallyCompleteSpace U :=
    TauCeti.sphericallyCompleteSpace_of_finiteDimensional (K := K) (E := U)
  U.closedComplemented_of_sphericallyComplete

end Projections

section NormOneProjections

variable {K V : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- Every spherically complete submodule of an ultrapseudometric seminormed space over a
nontrivially normed field admits a continuous projection of operator norm at most `1`. -/
theorem exists_proj_norm_le_one_of_sphericallyComplete (U : Submodule K V)
    [TauCeti.SphericallyCompleteSpace U] :
    ∃ P : V →L[K] U, (∀ u : U, P u = u) ∧ ‖P‖ ≤ 1 := by
  obtain ⟨P, hP, hle⟩ := U.exists_proj_norm_le_of_sphericallyComplete
  exact ⟨P, hP, P.opNorm_le_bound zero_le_one fun x ↦ by simpa using hle x⟩

/-- Every finite-dimensional submodule of an ultrapseudometric seminormed space over a spherically
complete ultrametric nontrivially normed field admits a continuous projection of operator norm at
most `1`. -/
theorem exists_proj_norm_le_one_of_finiteDimensional_of_sphericallyComplete [IsUltrametricDist K]
    [TauCeti.SphericallyCompleteSpace K] (U : Submodule K V) [FiniteDimensional K U] :
    ∃ P : V →L[K] U, (∀ u : U, P u = u) ∧ ‖P‖ ≤ 1 :=
  have : TauCeti.SphericallyCompleteSpace U :=
    TauCeti.sphericallyCompleteSpace_of_finiteDimensional (K := K) (E := U)
  U.exists_proj_norm_le_one_of_sphericallyComplete

end NormOneProjections

end Submodule
