/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Topology.MetricSpace.SphericallyComplete
import Mathlib.LinearAlgebra.LinearPMap
import TauCeti.Analysis.Normed.Module.Bases.Orthogonal

/-!
# The nonarchimedean Hahn–Banach theorem

Over a nonarchimedean field, the classical Hahn–Banach theorem is replaced by Ingleton's theorem:
a linear map `f : S → F` from a subspace into a spherically complete ultrametric seminormed space
`F`, dominated by a nonarchimedean seminorm `p` on `E`, extends to a linear map `g : E → F`
satisfying `‖g x‖ ≤ p x` for all `x : E`
(`LinearMap.exists_extension_of_le_seminorm_of_isNonarchimedean`).

Unlike the real and complex case, the extension theorem holds directly for vector-valued maps into
any spherically complete ultrametric target `F` (including `F = K` when the ground field `K` is
spherically complete, or any finite-dimensional ultrametric space over such a field), and requires
no completeness hypothesis on `E` or `K` beyond spherical completeness of `F`. On the other hand,
spherical completeness of `F` is essential: over a complete field that is not spherically complete,
such as `ℂ_p`, norm-preserving extension fails in general.

## Main results

* `LinearMap.exists_extension_of_le_seminorm_of_isNonarchimedean`: Ingleton's seminorm-dominated
  extension theorem for vector-valued maps into a spherically complete ultrametric space.
* `ContinuousLinearMap.exists_extension_norm_eq_of_isUltrametricDist`: norm-preserving extension
  of continuous linear maps from a subspace into a spherically complete ultrametric space.
* `LinearIsometry.exists_extension_norm_eq_of_isUltrametricDist`: norm-preserving extension along
  a linear isometric embedding.
* `Submodule.exists_proj_norm_le_one_of_sphericallyComplete`,
  `Submodule.closedComplemented_of_sphericallyComplete`,
  `Submodule.exists_proj_norm_le_one_of_finiteDimensional_of_sphericallyComplete`,
  `Submodule.closedComplemented_of_finiteDimensional_of_sphericallyComplete`: contractive
  projections and topological complementation for spherically complete and finite-dimensional
  subspaces.
* `WithSeminorms.exists_extension_of_isNonarchimedean`,
  `WithSeminorms.exists_dual_eq_one_of_notMem_closure_of_isNonarchimedean`,
  `WithSeminorms.mem_closure_iff_forall_dual_eq_zero_of_isNonarchimedean`,
  `WithSeminorms.separatingDual_of_isNonarchimedean`: extension, subspace separation, weak closure,
  and point-separating duals for spaces defined by nonarchimedean seminorm families.
* `Submodule.exists_dual_eq_one_norm_eq_inv_infDist_of_sphericallyComplete`,
  `Submodule.mem_closure_iff_forall_dual_eq_zero_of_sphericallyComplete`,
  `TauCeti.exists_dual_eq_one_norm_eq_inv_of_sphericallyComplete`,
  `TauCeti.separatingDual_of_sphericallyComplete`: exact-norm separation from subspaces and
  norming functionals (note that `‖x‖` need not belong to the scalar value group `‖K‖`, so the
  sharp form prescribes `g x = 1` and `‖g‖ = ‖x‖⁻¹`).
* `NormedSpace.norm_inclusionInDoubleDual_of_sphericallyComplete`,
  `NormedSpace.inclusionInDoubleDualLiOfSphericallyComplete`: the canonical map into the bidual
  is a linear isometry over any spherically complete nontrivially normed ultrametric field.

## References

* A. W. Ingleton, *The Hahn–Banach theorem for non-Archimedean valued fields*,
  Proc. Cambridge Philos. Soc. **48** (1952), 41–45.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §9, Proposition 9.2 and
  Corollaries 9.3–9.4.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*,
  Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010, Chapter 4.
-/

public section

open Metric Set Topology TauCeti
open scoped NNReal

namespace Seminorm

variable {K E : Type*} [SeminormedRing K] [AddGroup E] [SMul K E]

/-- A nonnegative scalar multiple of a nonarchimedean seminorm is nonarchimedean. -/
theorem isNonarchimedean_smul {p : Seminorm K E} (hp : IsNonarchimedean p) (c : ℝ≥0) :
    IsNonarchimedean (c • p) := fun x y ↦ by
  simp only [FunLike.coe_smul, Pi.smul_apply, NNReal.smul_def, smul_eq_mul,
    ← mul_max_of_nonneg _ _ c.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (hp x y) c.coe_nonneg

/-- The pointwise supremum of two nonarchimedean seminorms is nonarchimedean. -/
theorem isNonarchimedean_sup {p q : Seminorm K E}
    (hp : IsNonarchimedean p) (hq : IsNonarchimedean q) :
    IsNonarchimedean (p ⊔ q) := fun x y ↦ by
  simp only [Pi.sup_apply, sup_le_iff]
  exact ⟨(hp x y).trans (sup_le_sup le_sup_left le_sup_left),
    (hq x y).trans (sup_le_sup le_sup_right le_sup_right)⟩

/-- A finite supremum of nonarchimedean seminorms is nonarchimedean. -/
theorem isNonarchimedean_finset_sup {K E ι : Type*} [SeminormedRing K] [AddCommGroup E]
    [Module K E] {p : ι → Seminorm K E} (hp : ∀ i, IsNonarchimedean (p i)) (s : Finset ι) :
    IsNonarchimedean (s.sup p : Seminorm K E) := by
  refine Finset.cons_induction_on s ?_ fun a t _ ht ↦ ?_
  · intro x y
    simp [Seminorm.bot_eq_zero]
  · rw [Finset.sup_cons]
    exact isNonarchimedean_sup (hp a) ht

end Seminorm

/-! ### Ingleton's seminorm extension theorem -/

section Ingleton

/-- One-step extension of a partial linear map dominated by a nonarchimedean seminorm into a
spherically complete ultrametric space. -/
private theorem ingletonStep {K E F : Type*} [NormedField K] [AddCommGroup E] [Module K E]
    [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    {p : Seminorm K E} (hp : IsNonarchimedean p) (f : E →ₗ.[K] F)
    (hf : ∀ x : f.domain, ‖f x‖ ≤ p x) {y : E} (hy : y ∉ f.domain) :
    ∃ g : E →ₗ.[K] F, f < g ∧ ∀ x : g.domain, ‖g x‖ ≤ p x := by
  have : Nonempty f.domain := ⟨⟨0, f.domain.zero_mem⟩⟩
  have hpair : ∀ u₁ u₂ : f.domain, dist (f u₁) (f u₂) ≤ max (p (y - u₁)) (p (y - u₂)) := by
    intro u₁ u₂
    calc
      dist (f u₁) (f u₂) = ‖f (u₁ - u₂)‖ := by rw [dist_eq_norm, ← f.map_sub]
      _ ≤ p (u₁ - u₂ : E) := hf (u₁ - u₂)
      _ = p ((y - u₂) + -(y - u₁)) := by congr 1; abel
      _ ≤ max (p (y - u₂)) (p (-(y - u₁))) := hp _ _
      _ = max (p (y - u₁)) (p (y - u₂)) := by rw [map_neg_eq_map, max_comm]
  obtain ⟨w, hw⟩ := SphericallyCompleteSpace.nonempty_iInter_closedBall_of_pairwise
    (c := fun u : f.domain ↦ f u) (r := fun u : f.domain ↦ p (y - u))
    (fun _ ↦ apply_nonneg p _) hpair
  refine ⟨f.supSpanSingleton y w hy, ?_, ?_⟩
  · refine lt_iff_le_not_ge.2 ⟨f.left_le_sup _ _, fun hle ↦ ?_⟩
    have hdom := LinearPMap.domain_mono.monotone hle
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, Submodule.span_le,
      singleton_subset_iff] at hdom
    exact hy hdom.2
  · rintro ⟨z, hz⟩
    rw [LinearPMap.domain_supSpanSingleton, Submodule.mem_sup] at hz
    rcases hz with ⟨x, hx, y', hy', rfl⟩
    rcases Submodule.mem_span_singleton.1 hy' with ⟨c, rfl⟩
    rw [LinearPMap.supSpanSingleton_apply_mk f y w hy x hx c]
    simp only [RingHom.id_apply]
    by_cases hc : c = 0
    · subst hc
      simpa using hf ⟨x, hx⟩
    · let u : f.domain := (-c⁻¹) • ⟨x, hx⟩
      have hfu : f ⟨x, hx⟩ + c • w = c • (w - f u) := by
        simp only [u, neg_smul, f.map_neg, f.map_smul, sub_neg_eq_add, smul_add,
          smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
      have hxu : x + c • y = c • (y - u) := by
        simp only [u, neg_smul, Submodule.coe_neg, Submodule.coe_smul_of_tower, sub_neg_eq_add,
          smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, add_comm]
      rw [hfu, hxu, norm_smul, map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [mem_closedBall, dist_eq_norm] using mem_iInter.1 hw u) (norm_nonneg c)

namespace LinearMap

/-- **Ingleton's nonarchimedean Hahn–Banach theorem** for seminorms: a linear map from a subspace
into a spherically complete ultrametric seminormed space, dominated by a nonarchimedean seminorm,
extends to the whole space while remaining dominated by the same seminorm. -/
theorem exists_extension_of_le_seminorm_of_isNonarchimedean
    {K E F : Type*} [NormedField K] [AddCommGroup E] [Module K E]
    [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    {S : Submodule K E} (f : S →ₗ[K] F) {p : Seminorm K E}
    (hp : IsNonarchimedean p) (hf : ∀ x : S, ‖f x‖ ≤ p x) :
    ∃ g : E →ₗ[K] F, (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ p x := by
  let 𝒜 : Set (E →ₗ.[K] F) := { g | ∀ x : g.domain, ‖g x‖ ≤ p x }
  have hchain : ∀ c ⊆ 𝒜, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ 𝒜, ∀ z ∈ c, z ≤ ub := by
    intro c hc𝒜 hc_chain y hy
    have hcd : DirectedOn (· ≤ ·) c := hc_chain.directedOn
    refine ⟨LinearPMap.sSup c hcd, ?_, fun _ hz ↦ LinearPMap.le_sSup hcd hz⟩
    rintro ⟨x, hx⟩
    obtain ⟨g, hgc, hgx⟩ := (LinearPMap.mem_domain_sSup_iff ⟨y, hy⟩ hcd).1 hx
    have hle : g ≤ LinearPMap.sSup c hcd := LinearPMap.le_sSup hcd hgc
    have heq : LinearPMap.sSup c hcd ⟨x, hx⟩ = g ⟨x, hgx⟩ := (hle.2 (x := ⟨x, hgx⟩) rfl).symm
    rw [heq]
    exact hc𝒜 hgc ⟨x, hgx⟩
  obtain ⟨g, hfg, hg𝒜, hmax⟩ := zorn_le_nonempty₀ 𝒜 hchain ⟨S, f⟩ hf
  have hdom : g.domain = ⊤ := by
    by_contra hne
    obtain ⟨y, -, hy⟩ : ∃ y ∈ (⊤ : Submodule K E), y ∉ g.domain :=
      IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨g', hgg', hg'𝒜⟩ := ingletonStep hp g hg𝒜 hy
    exact hgg'.ne' ((hmax hg'𝒜 hgg'.le).antisymm hgg'.le)
  refine ⟨g.toFun.comp (LinearMap.id.codRestrict g.domain fun _ ↦ hdom.symm ▸ trivial),
    fun x ↦ ?_, fun x ↦ hg𝒜 ⟨x, hdom.symm ▸ trivial⟩⟩
  exact (hfg.2 (x := x) rfl).symm

end LinearMap

namespace Submodule

/-- Given a nonarchimedean seminorm `q` on `E` and a vector `x` at `q`-distance at least `r > 0`
from a submodule `S`, there exists a linear functional into a spherically complete ultrametric
field `K` vanishing on `S`, sending `x` to `1`, and bounded by `r⁻¹ * q`. -/
theorem exists_linearMap_eq_one_le_seminorm_of_isNonarchimedean
    {K E : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [AddCommGroup E] [Module K E]
    (S : Submodule K E) {q : Seminorm K E} (hq : IsNonarchimedean q)
    {x : E} {r : ℝ} (hr : 0 < r) (hdist : ∀ y ∈ S, r ≤ q (x - y)) :
    ∃ g : E →ₗ[K] K, (∀ y ∈ S, g y = 0) ∧ g x = 1 ∧ ∀ z, ‖g z‖ ≤ r⁻¹ * q z := by
  have hxS : x ∉ S := fun hx ↦ by
    have := hdist x hx
    rw [sub_self, map_zero] at this
    linarith
  let f₀ : E →ₗ.[K] K := (⟨S, 0⟩ : E →ₗ.[K] K).supSpanSingleton x 1 hxS
  let c : ℝ≥0 := ⟨r⁻¹, inv_nonneg.2 hr.le⟩
  have hcq (v : E) : (c • q) v = r⁻¹ * q v := by
    rw [FunLike.coe_smul, Pi.smul_apply, NNReal.smul_def, smul_eq_mul]
    rfl
  have hf₀ : ∀ z : f₀.domain, ‖f₀ z‖ ≤ (c • q) z := by
    rintro ⟨z, hz⟩
    rw [LinearPMap.domain_supSpanSingleton, Submodule.mem_sup] at hz
    rcases hz with ⟨y, hy, x', hx', rfl⟩
    rcases Submodule.mem_span_singleton.1 hx' with ⟨a, rfl⟩
    rw [LinearPMap.supSpanSingleton_apply_mk _ x 1 hxS y hy a, hcq]
    simp only [LinearPMap.mk_apply, LinearMap.zero_apply, RingHom.id_apply, zero_add, smul_eq_mul,
      mul_one]
    by_cases ha : a = 0
    · subst ha
      simp only [norm_zero]
      exact mul_nonneg (inv_nonneg.2 hr.le) (apply_nonneg q _)
    · have hmem : (-a⁻¹) • y ∈ S := S.smul_mem (-a⁻¹) hy
      have hrew : y + a • x = a • (x - (-a⁻¹) • y) := by
        simp only [neg_smul, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul,
          add_comm]
      rw [hrew, map_smul_eq_mul, le_inv_mul_iff₀ hr, mul_comm r ‖a‖]
      exact mul_le_mul_of_nonneg_left (hdist _ hmem) (norm_nonneg a)
  obtain ⟨g, hgf, hgb⟩ := LinearMap.exists_extension_of_le_seminorm_of_isNonarchimedean
    f₀.toFun (Seminorm.isNonarchimedean_smul hq c) hf₀
  refine ⟨g, fun y hy ↦ ?_, ?_, fun z ↦ hcq z ▸ hgb z⟩
  · rw [hgf ⟨y, by rw [LinearPMap.domain_supSpanSingleton]; exact mem_sup_left hy⟩,
      LinearPMap.toFun_eq_coe]
    simpa [f₀] using LinearPMap.supSpanSingleton_apply_mk_of_mem
      (⟨S, 0⟩ : E →ₗ.[K] K) 1 hxS hy
  · rw [hgf ⟨x, by
      rw [LinearPMap.domain_supSpanSingleton]
      exact mem_sup_right (mem_span_singleton_self x)⟩, LinearPMap.toFun_eq_coe]
    exact LinearPMap.supSpanSingleton_apply_self (⟨S, 0⟩ : E →ₗ.[K] K) 1 hxS

end Submodule

end Ingleton

/-! ### Norm-preserving extension and projections -/

namespace ContinuousLinearMap

variable {K E F : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]

/-- **Nonarchimedean Hahn–Banach theorem** (Ingleton): every continuous linear map from a subspace
of an ultrametric seminormed space into a spherically complete ultrametric seminormed space extends
to the whole space with the same operator norm. -/
theorem exists_extension_norm_eq_of_isUltrametricDist {S : Submodule K E} (f : S →L[K] F) :
    ∃ g : E →L[K] F, (∀ x : S, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  have hp : IsNonarchimedean (‖f‖₊ • normSeminorm K E) :=
    Seminorm.isNonarchimedean_smul IsUltrametricDist.isNonarchimedean_norm ‖f‖₊
  have hp_apply (x : E) : (‖f‖₊ • normSeminorm K E) x = ‖f‖ * ‖x‖ := by
    rw [FunLike.coe_smul, Pi.smul_apply, NNReal.smul_def, smul_eq_mul, coe_nnNorm,
      coe_normSeminorm]
  obtain ⟨g₀, hg₀, hbound⟩ := LinearMap.exists_extension_of_le_seminorm_of_isNonarchimedean
    f.toLinearMap hp fun x ↦ by rw [hp_apply]; exact f.le_opNorm x
  let g : E →L[K] F := g₀.mkContinuous ‖f‖ fun x ↦ hp_apply x ▸ hbound x
  refine ⟨g, hg₀, le_antisymm (g₀.mkContinuous_norm_le (norm_nonneg f) _) ?_⟩
  exact f.opNorm_le_bound (norm_nonneg g) fun x ↦ by simpa [g, hg₀ x] using g.le_opNorm x

end ContinuousLinearMap

namespace LinearIsometry

variable {K E F G : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]
  [SeminormedAddCommGroup G] [NormedSpace K G] [IsUltrametricDist G] [SphericallyCompleteSpace G]

/-- A continuous linear map into a spherically complete ultrametric space extends along a linear
isometric embedding into an ultrametric space with the same operator norm. -/
theorem exists_extension_norm_eq_of_isUltrametricDist (i : E →ₗᵢ[K] F) (f : E →L[K] G) :
    ∃ g : F →L[K] G, g.comp i.toContinuousLinearMap = f ∧ ‖g‖ = ‖f‖ := by
  let e := i.equivRange
  let f' : i.toLinearMap.range →L[K] G :=
    f.comp e.symm.toLinearIsometry.toContinuousLinearMap
  have hnorm' : ‖f'‖ = ‖f‖ := by
    refine le_antisymm ?_ ?_
    · refine f'.opNorm_le_bound (norm_nonneg f) fun x ↦ ?_
      simpa [f', e.symm.norm_map] using f.le_opNorm (e.symm x)
    · refine f.opNorm_le_bound (norm_nonneg f') fun x ↦ ?_
      have hfx : f x = f' (e x) := by simp [f', e]
      simpa [hfx, e.norm_map] using f'.le_opNorm (e x)
  obtain ⟨g, hg, hnorm⟩ := f'.exists_extension_norm_eq_of_isUltrametricDist
  refine ⟨g, ?_, hnorm.trans hnorm'⟩
  ext x
  simpa [f', e] using hg (e x)

end LinearIsometry

namespace Submodule

/-- Every spherically complete subspace of an ultrametric seminormed space admits a continuous
linear projection of norm at most `1`. -/
theorem exists_proj_norm_le_one_of_sphericallyComplete
    {K E : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    (S : Submodule K E) [SphericallyCompleteSpace S] :
    ∃ P : E →L[K] S, (∀ x : S, P x = x) ∧ ‖P‖ ≤ 1 := by
  obtain ⟨P, hP, hnorm⟩ :=
    (ContinuousLinearMap.id K S).exists_extension_norm_eq_of_isUltrametricDist
  exact ⟨P, hP, hnorm.le.trans ContinuousLinearMap.norm_id_le⟩

/-- Every spherically complete subspace of an ultrametric seminormed space is topologically
complemented. -/
theorem closedComplemented_of_sphericallyComplete
    {K E : Type*} [NormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    (S : Submodule K E) [SphericallyCompleteSpace S] :
    S.ClosedComplemented := by
  obtain ⟨P₀, hP₀, hbound⟩ := LinearMap.exists_extension_of_le_seminorm_of_isNonarchimedean
    (p := normSeminorm K E) (LinearMap.id : S →ₗ[K] S) IsUltrametricDist.isNonarchimedean_norm
    fun x ↦ le_rfl
  exact ⟨P₀.mkContinuous 1 fun x ↦ by simpa using hbound x, hP₀⟩

/-- Every finite-dimensional subspace of an ultrametric normed space over a spherically complete
nontrivially normed field admits a continuous linear projection of norm at most `1`. -/
theorem exists_proj_norm_le_one_of_finiteDimensional_of_sphericallyComplete
    {K E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    (S : Submodule K E) [FiniteDimensional K S] :
    ∃ P : E →L[K] S, (∀ x : S, P x = x) ∧ ‖P‖ ≤ 1 := by
  have : SphericallyCompleteSpace S := sphericallyCompleteSpace_of_finiteDimensional K S
  exact S.exists_proj_norm_le_one_of_sphericallyComplete

/-- Every finite-dimensional subspace of an ultrametric normed space over a spherically complete
field is topologically complemented. -/
theorem closedComplemented_of_finiteDimensional_of_sphericallyComplete
    {K E : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    (S : Submodule K E) [FiniteDimensional K S] :
    S.ClosedComplemented := by
  have : SphericallyCompleteSpace S := sphericallyCompleteSpace_of_finiteDimensional K S
  exact S.closedComplemented_of_sphericallyComplete

end Submodule

/-! ### Nonarchimedean locally convex spaces -/

namespace WithSeminorms

/-- **Nonarchimedean locally convex Hahn–Banach theorem**: if the topology of `E` is defined by a
family of nonarchimedean seminorms over a nontrivially normed field `K`, then every continuous
linear map from a subspace of `E` into a spherically complete ultrametric seminormed space extends
to a continuous linear map on `E`. -/
theorem exists_extension_of_isNonarchimedean
    {K E F ι : Type*} [NontriviallyNormedField K]
    [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    {p : SeminormFamily K E ι} (hp : WithSeminorms p) (hp_na : ∀ i, IsNonarchimedean (p i))
    {S : Submodule K E} (f : S →L[K] F) :
    ∃ g : E →L[K] F, ∀ x : S, g x = f x := by
  let q : Seminorm K S := (normSeminorm K F).comp f.toLinearMap
  have hq_cont : Continuous q := f.continuous.norm
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_comp_of_isInducing hq_cont hp
    (f := S.subtype) IsInducing.subtypeVal
  have hna : IsNonarchimedean (C • s.sup p) :=
    Seminorm.isNonarchimedean_smul (Seminorm.isNonarchimedean_finset_sup hp_na s) C
  obtain ⟨g₀, hg₀, hbound⟩ := LinearMap.exists_extension_of_le_seminorm_of_isNonarchimedean
    f.toLinearMap hna hle
  exact ⟨⟨g₀, hp.continuous_normedSpace_rng F g₀ ⟨s, C, hbound⟩⟩, hg₀⟩

/-- In a space whose topology is defined by a family of nonarchimedean seminorms over a spherically
complete ultrametric field, any vector outside the closure of a submodule is sent to `1` by a
continuous linear functional vanishing on the submodule. -/
theorem exists_dual_eq_one_of_notMem_closure_of_isNonarchimedean
    {K E ι : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {p : SeminormFamily K E ι} (hp : WithSeminorms p) (hp_na : ∀ i, IsNonarchimedean (p i))
    {S : Submodule K E} {x : E} (hx : x ∉ closure (S : Set E)) :
    ∃ g : StrongDual K E, (∀ y ∈ S, g y = 0) ∧ g x = 1 := by
  have hnhds : (S : Set E)ᶜ ∈ 𝓝 x :=
    Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hx)
      (compl_subset_compl.2 subset_closure)
  obtain ⟨s, r, hr, hball⟩ := (hp.mem_nhds_iff x (S : Set E)ᶜ).1 hnhds
  have hdist : ∀ y ∈ S, r ≤ (s.sup p) (x - y) := fun y hy ↦ by
    by_contra hlt
    have hyb : y ∈ (s.sup p).ball x r := by
      rw [Seminorm.mem_ball, ← map_neg_eq_map, neg_sub]
      exact not_le.1 hlt
    exact hball hyb hy
  obtain ⟨g₀, hgS, hgx, hbound⟩ := S.exists_linearMap_eq_one_le_seminorm_of_isNonarchimedean
    (Seminorm.isNonarchimedean_finset_sup hp_na s) hr hdist
  let c : ℝ≥0 := ⟨r⁻¹, inv_nonneg.2 hr.le⟩
  have hle : (normSeminorm K K).comp g₀ ≤ c • s.sup p := fun z ↦ by
    rw [Seminorm.comp_apply, coe_normSeminorm, FunLike.coe_smul, Pi.smul_apply, NNReal.smul_def,
      smul_eq_mul]
    exact hbound z
  exact ⟨⟨g₀, hp.continuous_normedSpace_rng K g₀ ⟨s, c, hle⟩⟩, hgS, hgx⟩

/-- In a space whose topology is defined by a family of nonarchimedean seminorms over a spherically
complete ultrametric field, a vector lies in the closure of a submodule if and only if every
continuous linear functional vanishing on the submodule vanishes at that vector. -/
theorem mem_closure_iff_forall_dual_eq_zero_of_isNonarchimedean
    {K E ι : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {p : SeminormFamily K E ι} (hp : WithSeminorms p) (hp_na : ∀ i, IsNonarchimedean (p i))
    (S : Submodule K E) {x : E} :
    x ∈ closure (S : Set E) ↔ ∀ g : StrongDual K E, (∀ y ∈ S, g y = 0) → g x = 0 := by
  refine ⟨fun hx g hg ↦ ?_, fun h ↦ ?_⟩
  · have hsub : (S : Set E) ⊆ g ⁻¹' {0} := fun y hy ↦ hg y hy
    exact closure_minimal hsub (isClosed_singleton.preimage g.continuous) hx
  · by_contra hx
    obtain ⟨g, hgS, hgx⟩ := hp.exists_dual_eq_one_of_notMem_closure_of_isNonarchimedean hp_na hx
    exact one_ne_zero (hgx ▸ h g hgS)

/-- A `T1` space whose topology is defined by a family of nonarchimedean seminorms over a
spherically complete ultrametric field has a separating continuous dual. -/
theorem separatingDual_of_isNonarchimedean
    {K E ι : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [AddCommGroup E] [Module K E] [TopologicalSpace E] [T1Space E]
    {p : SeminormFamily K E ι} (hp : WithSeminorms p) (hp_na : ∀ i, IsNonarchimedean (p i)) :
    SeparatingDual K E := by
  refine ⟨fun x hx ↦ ?_⟩
  have hnot : x ∉ closure ((⊥ : Submodule K E) : Set E) := by
    simpa only [Submodule.bot_coe, closure_singleton, mem_singleton_iff] using hx
  obtain ⟨g, -, hgx⟩ := hp.exists_dual_eq_one_of_notMem_closure_of_isNonarchimedean hp_na hnot
  exact ⟨g, hgx.symm ▸ one_ne_zero⟩

end WithSeminorms

/-! ### Separation from subspaces, norming functionals, and the bidual isometry -/

namespace Submodule

/-- Over a spherically complete ultrametric nontrivially normed field, any vector outside the
closure of a submodule `S` of an ultrametric seminormed space is separated from `S` by a
continuous linear functional sending `x` to `1` of exact norm `(infDist x S)⁻¹`. -/
theorem exists_dual_eq_one_norm_eq_inv_infDist_of_sphericallyComplete
    {K E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    (S : Submodule K E) {x : E} (hx : x ∉ closure (S : Set E)) :
    ∃ g : StrongDual K E, (∀ y ∈ S, g y = 0) ∧ g x = 1 ∧
      ‖g‖ = (infDist x (S : Set E))⁻¹ := by
  have hS_ne : (S : Set E).Nonempty := ⟨0, S.zero_mem⟩
  have hd : 0 < infDist x (S : Set E) := (infDist_pos_iff_notMem_closure hS_ne).1 hx
  obtain ⟨g₀, hgS, hgx, hbound⟩ := S.exists_linearMap_eq_one_le_seminorm_of_isNonarchimedean
    (q := normSeminorm K E) IsUltrametricDist.isNonarchimedean_norm hd
    fun y hy ↦ by
      rw [coe_normSeminorm, ← dist_eq_norm]
      exact infDist_le_dist_of_mem hy
  let g : StrongDual K E := g₀.mkContinuous (infDist x (S : Set E))⁻¹ fun z ↦ by
    simpa only [coe_normSeminorm] using hbound z
  refine ⟨g, hgS, hgx, le_antisymm (g₀.mkContinuous_norm_le (inv_nonneg.2 hd.le) _) ?_⟩
  have h1 (y : E) (hy : y ∈ S) : 1 ≤ ‖g‖ * dist x y := by
    calc
      1 = ‖(1 : K)‖ := norm_one.symm
      _ = ‖g (x - y)‖ := by
        rw [map_sub, LinearMap.mkContinuous_apply, LinearMap.mkContinuous_apply, hgx, hgS y hy,
          sub_zero]
      _ ≤ ‖g‖ * ‖x - y‖ := g.le_opNorm (x - y)
      _ = ‖g‖ * dist x y := by rw [dist_eq_norm]
  have hgnorm_pos : 0 < ‖g‖ :=
    pos_of_mul_pos_left (one_pos.trans_le (h1 0 S.zero_mem)) dist_nonneg
  have hinv_le : ‖g‖⁻¹ ≤ infDist x (S : Set E) :=
    (le_infDist hS_ne).2 fun y hy ↦ (inv_le_iff_one_le_mul₀' hgnorm_pos).2 (h1 y hy)
  exact inv_le_of_inv_le₀ hgnorm_pos hinv_le

/-- In an ultrametric seminormed space over a spherically complete ultrametric field, a vector lies
in the closure of a submodule if and only if every continuous linear functional vanishing on the
submodule vanishes at that vector. -/
theorem mem_closure_iff_forall_dual_eq_zero_of_sphericallyComplete
    {K E : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    (S : Submodule K E) {x : E} :
    x ∈ closure (S : Set E) ↔ ∀ g : StrongDual K E, (∀ y ∈ S, g y = 0) → g x = 0 :=
  (norm_withSeminorms K E).mem_closure_iff_forall_dual_eq_zero_of_isNonarchimedean
    (fun _ ↦ IsUltrametricDist.isNonarchimedean_norm) S

end Submodule

namespace TauCeti

/-- Over a spherically complete ultrametric nontrivially normed field, any vector of nonzero norm in
an ultrametric seminormed space admits a continuous linear functional with `g x = 1` and
`‖g‖ = ‖x‖⁻¹`. Unlike the real and complex case, `‖x‖` need not belong to the scalar value group
`‖K‖`, so a norm-`1` functional attaining `‖x‖` need not exist. -/
theorem exists_dual_eq_one_norm_eq_inv_of_sphericallyComplete
    (K : Type*) {E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] [SeminormedAddCommGroup E] [NormedSpace K E]
    [IsUltrametricDist E] {x : E} (hx : ‖x‖ ≠ 0) :
    ∃ g : StrongDual K E, g x = 1 ∧ ‖g‖ = ‖x‖⁻¹ := by
  have hinf : infDist x ((⊥ : Submodule K E) : Set E) = ‖x‖ := by
    simp [dist_eq_norm]
  have hnot : x ∉ closure ((⊥ : Submodule K E) : Set E) := by
    rw [mem_closure_iff_infDist_zero ⟨0, Submodule.zero_mem _⟩, hinf]
    exact hx
  obtain ⟨g, -, hgx, hgnorm⟩ :=
    (⊥ : Submodule K E).exists_dual_eq_one_norm_eq_inv_infDist_of_sphericallyComplete hnot
  exact ⟨g, hgx, hinf ▸ hgnorm⟩

/-- Every ultrametric normed space over a spherically complete ultrametric field has a separating
continuous dual. -/
theorem separatingDual_of_sphericallyComplete
    {K E : Type*} [NormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] :
    SeparatingDual K E :=
  (norm_withSeminorms K E).separatingDual_of_isNonarchimedean fun _ ↦
    IsUltrametricDist.isNonarchimedean_norm

end TauCeti

namespace NormedSpace

variable {K E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K]
  [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]

/-- Over a spherically complete ultrametric nontrivially normed field, the canonical map of an
ultrametric seminormed space into its bidual preserves norms. -/
theorem norm_inclusionInDoubleDual_of_sphericallyComplete (x : E) :
    ‖inclusionInDoubleDual K E x‖ = ‖x‖ := by
  refine le_antisymm (double_dual_bound K E x) ?_
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    exact norm_nonneg (inclusionInDoubleDual K E x)
  · obtain ⟨g, hgx, hgnorm⟩ :=
      TauCeti.exists_dual_eq_one_norm_eq_inv_of_sphericallyComplete K hx
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    have hle : 1 ≤ ‖inclusionInDoubleDual K E x‖ * ‖x‖⁻¹ := by
      calc
        1 = ‖(1 : K)‖ := norm_one.symm
        _ = ‖inclusionInDoubleDual K E x g‖ := by rw [dual_def, hgx]
        _ ≤ ‖inclusionInDoubleDual K E x‖ * ‖g‖ := (inclusionInDoubleDual K E x).le_opNorm g
        _ = ‖inclusionInDoubleDual K E x‖ * ‖x‖⁻¹ := by rw [hgnorm]
    simpa only [one_mul] using (le_mul_inv_iff₀ hpos).1 hle

variable (K E) in
/-- Over a spherically complete ultrametric nontrivially normed field, the canonical map of an
ultrametric seminormed space into its bidual as a linear isometry. -/
noncomputable def inclusionInDoubleDualLiOfSphericallyComplete :
    E →ₗᵢ[K] StrongDual K (StrongDual K E) where
  toLinearMap := (inclusionInDoubleDual K E).toLinearMap
  norm_map' x := norm_inclusionInDoubleDual_of_sphericallyComplete x

/-- Evaluation of `inclusionInDoubleDualLiOfSphericallyComplete` agrees with
`inclusionInDoubleDual`. -/
@[simp]
theorem inclusionInDoubleDualLiOfSphericallyComplete_apply (x : E) :
    inclusionInDoubleDualLiOfSphericallyComplete K E x = inclusionInDoubleDual K E x := (rfl)

/-- Coercing `inclusionInDoubleDualLiOfSphericallyComplete` to a continuous linear map recovers
`inclusionInDoubleDual`. -/
@[simp]
theorem toContinuousLinearMap_inclusionInDoubleDualLiOfSphericallyComplete :
    (inclusionInDoubleDualLiOfSphericallyComplete K E).toContinuousLinearMap =
      inclusionInDoubleDual K E := (rfl)

end NormedSpace
