/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.VectorBundle.HomotopyInvariance
public import TauCeti.Topology.VectorBundle.OrthonormalTrivialization
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Vector bundles over contractible bases are trivial

Let `B` be a contractible paracompact R₁ space, for instance a closed disc or a convex subset of a
real normed space. Every vector bundle `E` over `B` is trivial: it has a linear trivialization
whose base set is all of `B` (`TauCeti.exists_trivialization_baseSet_eq_univ_of_contractibleSpace`).
Here the scalars `𝕜` form a normed `ℝ`-algebra, such as `ℝ` or `ℂ`, and the model fibre `F` may be
any Banach space.

The proof is homotopy invariance of bundles
(`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`): the identity of `B` is
homotopic to a constant map at some point `y`, so the pullbacks of `E` along the two maps are
isomorphic. The first pullback is `E` itself and the second is the product bundle with fibre
`E y`, which a trivialization of `E` near `y` identifies with `F`.

For a finite-rank real bundle with a continuous fibre metric, Gram–Schmidt applied to such a
global trivialization (`Bundle.Trivialization.orthonormal`) makes it isometric on every fibre
(`TauCeti.exists_orthonormal_trivialization_baseSet_eq_univ_of_contractibleSpace`). So `E` is
homeomorphic to `B × F` by a map covering the identity of `B` that is a linear isometry
`E b ≃ₗᵢ[ℝ] F` on each fibre (`TauCeti.exists_homeomorph_prod_of_contractibleSpace`). In
particular the unit disc bundle `D(E)` is homeomorphic to `B × D(F)`, the product of `B` with the
closed unit ball of `F`, by a homeomorphism carrying the unit sphere bundle `S(E)` onto
`B × S(F)` (`TauCeti.exists_homeomorph_discBundle_prod_closedBall_of_contractibleSpace`).

These are the product structures used to build cells of disc bundles over a CW complex: pulled
back along the characteristic map of a cell `Dᵠ → X`, a rank `r` bundle becomes
`Dᵠ × (Dʳ, Sʳ⁻¹)`.

## Main results

* `TauCeti.exists_trivialization_baseSet_eq_univ_of_contractibleSpace`: a vector bundle over a
  contractible paracompact R₁ base has a linear trivialization over the whole base.
* `TauCeti.exists_orthonormal_trivialization_baseSet_eq_univ_of_contractibleSpace`: for a
  finite-rank real bundle with continuous fibre metric, the trivialization can be chosen
  isometric on every fibre.
* `TauCeti.exists_homeomorph_prod_of_contractibleSpace`: such a bundle is homeomorphic to `B × F`
  by fibrewise linear isometries.
* `TauCeti.exists_homeomorph_discBundle_prod_closedBall_of_contractibleSpace`: its disc and sphere
  bundles form the product pair `B × (D(F), S(F))`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Corollary 1.8 (bundles over contractible paracompact
  bases are trivial).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (Euclidean metrics and orthonormal frames).
-/

public section

noncomputable section

open Bundle Metric Set

universe u

namespace TauCeti

section Linear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {B : Type*} [TopologicalSpace B] [R1Space B] [ParacompactSpace B] [ContractibleSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul 𝕜 (E b)]

variable (𝕜 F E) in
/-- **Vector bundles over contractible bases are trivial.** Over a contractible paracompact R₁
space `B`, for instance a paracompact Hausdorff one, every vector bundle has a linear
trivialization whose base set is the whole of `B`. The scalars `𝕜` form a normed `ℝ`-algebra, such
as `ℝ` or `ℂ`, and the model fibre `F` may be any Banach space. -/
theorem exists_trivialization_baseSet_eq_univ_of_contractibleSpace :
    ∃ e : Trivialization F (π F E), e.IsLinear 𝕜 ∧ e.baseSet = univ := by
  -- The identity of `B` is homotopic to a constant map at `y`, so `E x ≃ E y` continuously in `x`.
  obtain ⟨y, hy⟩ := id_nullhomotopic B
  obtain ⟨Φ, hΦ, hΦ'⟩ := hy.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜) (F := F) (E := E)
  -- A trivialization of `E` near `y` identifies `E y` with `F`.
  let e₀ := trivializationAt F E y
  have hy₀ : y ∈ e₀.baseSet := mem_baseSet_trivializationAt F E y
  let Ψ : ∀ x, E x ≃L[𝕜] F := fun x ↦ (Φ x).trans (e₀.continuousLinearEquivAt 𝕜 y hy₀)
  -- The fibre coordinate `Ψ` is continuous on the total space.
  have hpt : Continuous fun p : TotalSpace F E ↦ (TotalSpace.mk' F y (Φ p.proj p.2)) := by
    have hι : Continuous fun p : TotalSpace F E ↦
        (TotalSpace.mk' F (E := (ContinuousMap.id B : B → B) *ᵖ E) p.proj p.2) :=
      Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj F E, continuous_id⟩
    exact (Pullback.continuous_lift F E _).comp (hΦ.comp hι)
  have hfwd : Continuous fun p : TotalSpace F E ↦ Ψ p.proj p.2 :=
    (e₀.continuousOn.comp_continuous hpt fun _ ↦ e₀.mem_source.2 hy₀).snd
  -- Its inverse is continuous on `B × F`.
  have hinv : Continuous fun q : B × F ↦ TotalSpace.mk' F q.1 ((Ψ q.1).symm q.2) := by
    have hι : Continuous fun q : B × F ↦ (TotalSpace.mk' F
        (E := (ContinuousMap.const B y : B → B) *ᵖ E) q.1
        ((e₀.continuousLinearEquivAt 𝕜 y hy₀).symm q.2)) :=
      Pullback.continuous_iff.2 ⟨continuous_fst, (FiberBundle.continuous_totalSpaceMk F E y).comp
        ((e₀.continuousLinearEquivAt 𝕜 y hy₀).symm.continuous.comp continuous_snd)⟩
    exact (Pullback.continuous_lift F E _).comp (hΦ'.comp hι)
  refine ⟨{
    toFun p := (p.proj, Ψ p.proj p.2)
    invFun q := ⟨q.1, (Ψ q.1).symm q.2⟩
    source := univ
    target := univ
    map_source' _ _ := mem_univ _
    map_target' _ _ := mem_univ _
    left_inv' p _ := by simp
    right_inv' q _ := by simp
    open_source := isOpen_univ
    open_target := isOpen_univ
    continuousOn_toFun := ((FiberBundle.continuous_proj F E).prodMk hfwd).continuousOn
    continuousOn_invFun := hinv.continuousOn
    baseSet := univ
    open_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    proj_toFun _ _ := rfl }, ⟨fun b _ ↦ (Ψ b).toLinearEquiv.toLinearMap.isLinear⟩, rfl⟩

end Linear

section Riemannian

variable {B : Type*} [TopologicalSpace B] [R1Space B] [ParacompactSpace B] [ContractibleSpace B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

variable (F E) in
/-- **Orthonormal trivializations over contractible bases.** A finite-rank real vector bundle with
a continuous fibre metric over a contractible paracompact R₁ space has a linear trivialization
over the whole base which is isometric on every fibre. -/
theorem exists_orthonormal_trivialization_baseSet_eq_univ_of_contractibleSpace :
    ∃ e : Trivialization F (π F E), e.IsLinear ℝ ∧ e.baseSet = univ ∧
      ∀ (b : B) (v : E b), ‖(e ⟨b, v⟩).2‖ = ‖v‖ := by
  obtain ⟨e, _, he⟩ := exists_trivialization_baseSet_eq_univ_of_contractibleSpace ℝ F E
  refine ⟨e.orthonormal (stdOrthonormalBasis ℝ F), inferInstance, by simp [he], fun b v ↦ ?_⟩
  have hb : b ∈ e.baseSet := he ▸ mem_univ b
  simp [hb]

variable (F E) in
/-- **A bundle over a contractible base is a product.** A finite-rank real vector bundle with a
continuous fibre metric over a contractible paracompact R₁ space `B` is homeomorphic to `B × F` by
a map covering the identity of `B` which is a linear isometry `E b ≃ₗᵢ[ℝ] F` on each fibre. -/
theorem exists_homeomorph_prod_of_contractibleSpace :
    ∃ (h : TotalSpace F E ≃ₜ B × F) (L : ∀ b, E b ≃ₗᵢ[ℝ] F),
      ∀ (b : B) (v : E b), h ⟨b, v⟩ = (b, L b v) := by
  obtain ⟨e, _, he, hiso⟩ :=
    exists_orthonormal_trivialization_baseSet_eq_univ_of_contractibleSpace F E
  let L : ∀ b, E b ≃ₗᵢ[ℝ] F := fun b ↦
    { toLinearEquiv := e.linearEquivAt ℝ b (he ▸ mem_univ b)
      norm_map' := hiso b }
  refine ⟨e.toHomeomorphOfSourceEqUnivTargetEqUniv (by simp [e.source_eq, he])
    (by simp [e.target_eq, he]), L, fun b v ↦ ?_⟩
  exact e.apply_eq_prod_continuousLinearEquivAt ℝ b (he ▸ mem_univ b) v

end Riemannian

section Disc

variable {B : Type u} [TopologicalSpace B] [R1Space B] [ParacompactSpace B] [ContractibleSpace B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type u} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

variable (F E) in
/-- **Disc bundles over contractible bases are products.** For a finite-rank real vector bundle
with a continuous fibre metric over a contractible paracompact R₁ space `B`, the unit disc bundle
`D(E)` is homeomorphic to `B × D(F)`, the product with the closed unit ball of `F`, by a map
covering the identity of `B` which is a linear isometry `L b : E b ≃ₗᵢ[ℝ] F` on each fibre. It
carries the unit sphere bundle `S(E)` onto `B × S(F)`. -/
theorem exists_homeomorph_discBundle_prod_closedBall_of_contractibleSpace :
    ∃ (h : discBundle F E ≃ₜ B × closedBall (0 : F) 1) (L : ∀ b, E b ≃ₗᵢ[ℝ] F),
      (∀ v : discBundle F E,
        (h v).1 = (v : TotalSpace F E).proj ∧ ((h v).2 : F) = L _ (v : TotalSpace F E).2) ∧
      ∀ v : discBundle F E,
        (v : TotalSpace F E) ∈ sphereBundle F E ↔ ((h v).2 : F) ∈ sphere (0 : F) 1 := by
  obtain ⟨h, L, hL⟩ := exists_homeomorph_prod_of_contractibleSpace F E
  have hdisc : discBundle F E = h ⁻¹' (univ ×ˢ closedBall 0 1) := by
    ext ⟨b, v⟩
    simp [hL]
  let k : discBundle F E ≃ₜ B × closedBall (0 : F) 1 :=
    ((h.sets hdisc).trans (Homeomorph.Set.prod _ _)).trans
      ((Homeomorph.Set.univ B).prodCongr (Homeomorph.refl _))
  have hk (v : discBundle F E) :
      (k v).1 = (v : TotalSpace F E).proj ∧ ((k v).2 : F) = L _ (v : TotalSpace F E).2 := by
    obtain ⟨⟨b, w⟩, hw⟩ := v
    simp [k, Homeomorph.Set.prod_apply _ _ (h.sets hdisc ⟨⟨b, w⟩, hw⟩), hL]
  refine ⟨k, L, hk, fun v ↦ ?_⟩
  rw [mem_sphereBundle, (hk v).2, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]

end Disc

end TauCeti
