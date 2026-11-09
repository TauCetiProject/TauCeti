/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Maps tangent to a distribution

A map `f : N → M` is **horizontal** for a distribution `D` on `M`, or tangent to `D`, when every
tangent image `df_y(T_y N)` lies in `D (f y)` (`TauCeti.IsHorizontalMap`). Integral manifolds
(`TauCeti.IsIntegralManifold`) are the immersions whose tangent images are all of `D`; horizontal
maps only ask for containment, so they include horizontal curves of sub-Riemannian geometry and,
for a contact structure, the isotropic maps. The source is an arbitrary charted space and `f`
need not be injective. The differential is `mfderiv`, which is `0` where `f` is not
differentiable, so the predicate is meaningful for differentiable maps.

## Main declarations

* `TauCeti.IsHorizontalMap`: maps whose tangent images lie in a distribution.
* `TauCeti.IsHorizontalMap.comp`: precomposing a horizontal map keeps it horizontal.
* `TauCeti.IsHorizontalMap.eventually_sub_mem`: coordinates whose differential takes the
  distribution into a closed subspace are locally constant modulo that subspace along
  horizontal differentiable maps.
* `TauCeti.isHorizontalMap_comp_diffeomorph_iff`, `TauCeti.isHorizontalMap_diffeomorph_comp_iff`:
  independence of the parametrization and transport by diffeomorphisms preserving the
  distributions.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 19.16, p. 500 (local containment in a slice).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {f : N → M}

variable (J) in
/-- A map `f : N → M` is **horizontal** for a distribution `D`, or tangent to `D`, when every
tangent image `df_y(T_y N)` lies in `D (f y)`. For a contact structure `D` these are the
isotropic maps; when `f` is moreover a smooth immersion, it parametrizes an immersed isotropic
submanifold.

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not
differentiable, so there the condition holds trivially. -/
def IsHorizontalMap (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) (f : N → M) : Prop :=
  ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y)

/-- A map is horizontal exactly when every tangent image lies in the distribution. -/
theorem isHorizontalMap_iff_range_mfderiv_le : IsHorizontalMap J D f ↔
    ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y) :=
  Iff.rfl

/-- The tangent images of a horizontal map lie in the distribution. -/
theorem IsHorizontalMap.range_mfderiv_le (hf : IsHorizontalMap J D f) (y : N) :
    LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y) :=
  hf y

/-- A map is horizontal exactly when its differential sends every tangent vector into the
distribution. -/
theorem isHorizontalMap_iff :
    IsHorizontalMap J D f ↔ ∀ y (v : TangentSpace J y), mfderiv J I f y v ∈ D (f y) := by
  simp only [IsHorizontalMap, LinearMap.range_le_iff_comap, Submodule.eq_top_iff',
    Submodule.mem_comap, ContinuousLinearMap.coe_coe]

/-- The differential of a horizontal map takes values in the distribution. -/
theorem IsHorizontalMap.mfderiv_mem (hf : IsHorizontalMap J D f) (y : N)
    (v : TangentSpace J y) : mfderiv J I f y v ∈ D (f y) :=
  isHorizontalMap_iff.1 hf y v

/-- A map horizontal for a smaller distribution is horizontal for a larger one. -/
theorem IsHorizontalMap.mono {D' : Π x : M, Submodule 𝕜 (TangentSpace I x)}
    (hf : IsHorizontalMap J D f) (hDD' : ∀ x, D x ≤ D' x) : IsHorizontalMap J D' f :=
  fun y ↦ (hf y).trans (hDD' (f y))

section Transport

variable {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] {n : ℕ∞ω}

/-- Precomposing a horizontal map with a map `g` keeps it horizontal, wherever `g` and `f` are
differentiable, since the tangent image of `f ∘ g` lies in that of `f`. -/
theorem IsHorizontalMap.comp {g : P → N} (hf : IsHorizontalMap J D f)
    (hg : ∀ x, MDifferentiableAt K J g x) (hfg : ∀ x, MDifferentiableAt J I f (g x)) :
    IsHorizontalMap K D (f ∘ g) := fun x ↦ by
  rw [mfderiv_comp x (hfg x) (hg x)]
  exact (LinearMap.range_comp_le_range _ _).trans (hf (g x))

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is horizontal. -/
theorem isHorizontalMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    IsHorizontalMap K D (f ∘ φ) ↔ IsHorizontalMap J D f := by
  simp only [IsHorizontalMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

/-- **Transport by diffeomorphisms.** If the differential of a diffeomorphism `ψ : M → P` carries
the distribution `D` onto the distribution `D'`, then `ψ ∘ f` is horizontal for `D'` exactly when
`f` is horizontal for `D`. -/
theorem isHorizontalMap_diffeomorph_comp_iff {D' : Π z : P, Submodule 𝕜 (TangentSpace K z)}
    (ψ : M ≃ₘ^n⟮I, K⟯ P) (hn : n ≠ 0)
    (hψ : ∀ x (v : TangentSpace I x), v ∈ D x ↔ mfderiv I K ψ x v ∈ D' (ψ x)) :
    IsHorizontalMap J D' (ψ ∘ f) ↔ IsHorizontalMap J D f := by
  refine forall_congr' fun y ↦ ?_
  have hcoe (v : TangentSpace I (f y)) :
      (ψ.mfderivToContinuousLinearEquiv hn (f y)).toLinearEquiv.toLinearMap v =
        mfderiv I K ψ (f y) v :=
    congr($(ψ.mfderivToContinuousLinearEquiv_coe (x := f y) hn) v)
  rw [ψ.range_mfderiv_diffeomorph_comp hn, Function.comp_apply, Submodule.map_le_iff_le_comap]
  refine ⟨fun h v hv ↦ (hψ (f y) v).2 ?_, fun h v hv ↦ ?_⟩
  · simpa only [Submodule.mem_comap, hcoe] using h hv
  · simpa only [Submodule.mem_comap, hcoe] using (hψ (f y) v).1 (h hv)

end Transport

end General

section Real

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : N → M}

/-- Along a horizontal differentiable map, coordinates are locally constant modulo any closed
subspace containing the coordinate image of the distribution. -/
theorem IsHorizontalMap.eventually_sub_mem {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (hf : IsHorizontalMap J D f) {s : Set N}
    (hfd : MDifferentiableOn J I f s) (hs : IsOpen s)
    {p : M → V} {U : Set M} (hp : MDifferentiableOn I 𝓘(ℝ, V) p U) (hU : IsOpen U)
    {W : Submodule ℝ V} (hW : IsClosed (W : Set V))
    (hDp : ∀ z ∈ U, (D z).map (mvfderiv I p z).toLinearMap ≤ W)
    {x : N} (hxs : x ∈ s) (hx : f x ∈ U) : ∀ᶠ y in 𝓝 x, p (f y) - p (f x) ∈ W := by
  let _ : IsClosed (W : Set V) := hW
  let q : V →L[ℝ] V ⧸ W := W.mkQL
  let g : N → V := p ∘ f
  have hpre : IsOpen (s ∩ f ⁻¹' U) := hfd.continuousOn.isOpen_inter_preimage hs hU
  have hgd (y : N) (hy : y ∈ s ∩ f ⁻¹' U) : MDifferentiableAt J 𝓘(ℝ, V) g y :=
    ((hp (f y) hy.2).mdifferentiableAt (hU.mem_nhds hy.2)).comp y
      ((hfd y hy.1).mdifferentiableAt (hs.mem_nhds hy.1))
  have hzero (y : N) (hy : y ∈ s ∩ f ⁻¹' U) :
      mfderiv J 𝓘(ℝ, V ⧸ W) (q ∘ g) y = 0 := by
    rw [← mvfderiv_eq_zero_iff]
    ext v
    rw [mvfderiv_comp_apply_of_differentiableAt q.differentiableAt (hgd y hy),
      q.fderiv, zero_apply]
    apply (Submodule.Quotient.mk_eq_zero W).2
    have hmem := hDp (f y) hy.2 (Submodule.mem_map_of_mem (hf.mfderiv_mem y v))
    simpa only [g, mvfderiv_comp_apply y
      ((hp (f y) hy.2).mdifferentiableAt (hU.mem_nhds hy.2))
      ((hfd y hy.1).mdifferentiableAt (hs.mem_nhds hy.1)),
      ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply] using hmem
  have hconst := MDifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero
    (fun y hy ↦ (q.differentiableAt.comp_mdifferentiableAt (hgd y hy)).mdifferentiableWithinAt)
    hpre hzero ⟨hxs, hx⟩
  filter_upwards [hconst] with y hy
  simp only [Function.comp_apply] at hy
  apply (Submodule.Quotient.mk_eq_zero W).1
  rw [← Submodule.mkQ_apply, ← Submodule.mkQL_apply, map_sub, sub_eq_zero]
  exact hy

end Real

end TauCeti
