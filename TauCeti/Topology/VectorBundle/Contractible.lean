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
import TauCeti.Topology.VectorBundle.OrthonormalFrame.Pullback
import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Topology.VectorBundle.Trivialization

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

Pulling back along a continuous map `f : B → X` gives a **frame of `E` along `f`**, a family of
linear isomorphisms `φ y : F ≃ E (f y)` for which `(y, v) ↦ φ y v` is continuous into the total
space of `E` (`TauCeti.exists_continuous_frame`). Read in a linear trivialization `e`, such a
frame is a family `e ∘ φ y` of endomorphisms of `F`, continuous where `e` is defined when `F` is
finite-dimensional (`TauCeti.continuousOn_continuousLinearMapAt_comp`).

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
`Dᵠ × (Dʳ, Sʳ⁻¹)`. In the form used there, a map `g : Y → B` from a contractible paracompact R₁
space lifts continuously to the orthonormal frame bundle of a bundle with fibre inner products of
continuous norm, over `ℝ` or `ℂ`
(`TauCeti.exists_orthonormalFrameBundle_lift_of_contractibleSpace`): Gram–Schmidt applied to a
global trivialization of the pullback `g *ᵖ E` gives a continuous orthonormal frame of `E` along
`g`. No fibre metric on the model fibre and no continuity of the metric beyond that of the norm is
needed.

## Main results

* `TauCeti.exists_trivialization_baseSet_eq_univ_of_contractibleSpace`: a vector bundle over a
  contractible paracompact R₁ base has a linear trivialization over the whole base.
* `TauCeti.exists_continuous_frame`: a vector bundle has a frame along every continuous map from
  a contractible paracompact R₁ space.
* `TauCeti.continuous_trans_symm_of_continuous_frame`: two continuous frames of a finite-rank
  bundle along the same map differ by a continuous family of automorphisms of their common
  source, for instance the model fibre.
* `TauCeti.exists_orthonormal_trivialization_baseSet_eq_univ_of_contractibleSpace`: for a
  finite-rank real bundle with continuous fibre metric, the trivialization can be chosen
  isometric on every fibre.
* `TauCeti.exists_homeomorph_prod_of_contractibleSpace`: such a bundle is homeomorphic to `B × F`
  by fibrewise linear isometries.
* `TauCeti.exists_homeomorph_discBundle_prod_closedBall_of_contractibleSpace`: its disc and sphere
  bundles form the product pair `B × (D(F), S(F))`.
* `TauCeti.exists_orthonormalFrameBundle_lift_of_contractibleSpace`: a continuous orthonormal frame
  along a map out of a contractible paracompact R₁ space.

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
  have hpt : Continuous fun p : TotalSpace F E ↦ (TotalSpace.mk' F y (Φ p.proj p.snd)) := by
    have hι : Continuous fun p : TotalSpace F E ↦
        (TotalSpace.mk' F (E := (ContinuousMap.id B : B → B) *ᵖ E) p.proj p.snd) :=
      Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj F E, continuous_id⟩
    exact (Pullback.continuous_lift F E _).comp (hΦ.comp hι)
  have hfwd : Continuous fun p : TotalSpace F E ↦ Ψ p.proj p.snd :=
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
    toFun p := (p.proj, Ψ p.proj p.snd)
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

section Frame

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] {f : B → X}

/-- A continuous frame `φ` along `f` determines `f`, which is therefore continuous. -/
theorem continuous_of_continuous_frame {φ : ∀ y, F ≃L[𝕜] E (f y)}
    (hφ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2)) : Continuous f :=
  (FiberBundle.continuous_proj F E).comp (hφ.comp (Continuous.prodMk_left 0))

/-- **A frame in a trivialization.** Read in a linear trivialization `e`, a continuous frame `φ`
along `f` with finite-dimensional model fibre is a family of endomorphisms `e ∘ φ y` of `F` that is
continuous wherever `e` is defined. -/
theorem continuousOn_continuousLinearMapAt_comp [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {φ : ∀ y, F ≃L[𝕜] E (f y)}
    (hφ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    ContinuousOn (fun y ↦ (e.continuousLinearMapAt 𝕜 (f y)).comp (φ y : F →L[𝕜] E (f y)))
      (f ⁻¹' e.baseSet) := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  have hc : ContinuousOn (fun y ↦ (e (TotalSpace.mk' F (f y) (φ y v))).2) (f ⁻¹' e.baseSet) :=
    continuous_snd.comp_continuousOn (e.continuousOn.comp
      (hφ.comp (Continuous.prodMk_left v)).continuousOn fun y hy ↦ e.mem_source.2 hy)
  refine hc.congr fun y (hy : f y ∈ e.baseSet) ↦ ?_
  simp [e.coe_linearMapAt_of_mem hy]

/-- Two continuous frames with the model fibre `F` as their source differ by a continuous family
of automorphisms of `F`; `TauCeti.continuous_trans_symm_of_continuous_frame` allows any source. -/
private theorem continuous_trans_symm_of_continuous_frame_aux [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F]
    [VectorBundle 𝕜 F E] {φ ψ : ∀ y, F ≃L[𝕜] E (f y)}
    (hφ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (hψ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2)) :
    Continuous fun y ↦ (((φ y).trans (ψ y).symm : F ≃L[𝕜] F) : F →L[𝕜] F) := by
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  -- Read both frames in the trivialization `e` at `f y₀`, where they become automorphisms of `F`.
  let e := trivializationAt F E (f y₀)
  have hU : f ⁻¹' e.baseSet ∈ nhds y₀ :=
    (continuous_of_continuous_frame hφ).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (f y₀)))
  -- On the base set the coordinate of a frame `χ` is the automorphism `e ∘ χ y`.
  have hcoord {χ : ∀ y, F ≃L[𝕜] E (f y)} {y : B} (hy : f y ∈ e.baseSet) :
      (e.continuousLinearMapAt 𝕜 (f y)).comp (χ y : F →L[𝕜] E (f y)) =
        ((χ y).trans (e.continuousLinearEquivAt 𝕜 (f y) hy) : F →L[𝕜] F) := by
    rw [← ContinuousLinearEquiv.comp_coe, e.coe_continuousLinearEquivAt_eq' (R := 𝕜) hy]
  -- The coordinate of `ψ` is invertible at `y₀`, so its inverse is continuous there. The unit
  -- `toUnit` of an automorphism has that automorphism as its value.
  have hy₀ : f y₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (f y₀)
  have hinv : ContinuousAt (fun y ↦ Ring.inverse
      ((e.continuousLinearMapAt 𝕜 (f y)).comp (ψ y : F →L[𝕜] E (f y)))) y₀ := by
    refine (NormedRing.inverse_continuousAt ((ψ y₀).trans
      (e.continuousLinearEquivAt 𝕜 (f y₀) hy₀)).toUnit).comp_of_eq ?_ (hcoord hy₀)
    exact (continuousOn_continuousLinearMapAt_comp hψ e).continuousAt hU
  refine (hinv.mul ((continuousOn_continuousLinearMapAt_comp hφ e).continuousAt
    hU)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with y (hy : f y ∈ e.baseSet)
  rw [Pi.mul_apply, hcoord hy, hcoord hy, ContinuousLinearMap.ringInverse_equiv,
    ContinuousLinearMap.inverse_equiv]
  ext v
  simp [e.symm_apply_apply_mk hy]

/-- **Two frames differ by a continuous family of automorphisms.** If `φ` and `ψ` are continuous
frames of a finite-rank vector bundle `E` along the same map `f`, with source a normed space `W`,
for instance the model fibre `F`, the transition `y ↦ (ψ y)⁻¹ ∘ φ y` is a continuous map into the
automorphisms of `W`. -/
theorem continuous_trans_symm_of_continuous_frame [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [VectorBundle 𝕜 F E] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {φ ψ : ∀ y, W ≃L[𝕜] E (f y)}
    (hφ : Continuous fun q : B × W ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (hψ : Continuous fun q : B × W ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2)) :
    Continuous fun y ↦ (((φ y).trans (ψ y).symm : W ≃L[𝕜] W) : W →L[𝕜] W) := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨y₀⟩⟩
  · exact continuous_of_discreteTopology
  -- Identify `W` with `F` through the fibre at `f y₀`, and transport both frames to source `F`.
  let ι : W ≃L[𝕜] F := (φ y₀).trans ((trivializationAt F E (f y₀)).continuousLinearEquivAt 𝕜
    (f y₀) (FiberBundle.mem_baseSet_trivializationAt' (f y₀)))
  have hι {χ : ∀ y, W ≃L[𝕜] E (f y)}
      (hχ : Continuous fun q : B × W ↦ TotalSpace.mk' F (f q.1) (χ q.1 q.2)) :
      Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) ((ι.symm.trans (χ q.1)) q.2) :=
    hχ.comp (continuous_fst.prodMk (ι.symm.continuous.comp continuous_snd))
  refine (((continuous_const (y := (ι.symm : F →L[𝕜] W))).clm_comp
    (continuous_trans_symm_of_continuous_frame_aux (f := f) (φ := fun y ↦ ι.symm.trans (φ y))
      (ψ := fun y ↦ ι.symm.trans (ψ y)) (hι hφ) (hι hψ))).clm_comp
      (continuous_const (y := (ι : W →L[𝕜] F)))).congr fun y ↦ ?_
  ext v
  simp

/-- **Frames over contractible spaces.** Along every continuous map `f` from a contractible
paracompact R₁ space, for instance a cube, a vector bundle `E` has a frame: linear isomorphisms
`φ y : F ≃ E (f y)` depending continuously on `y`. This is the triviality of the pullback bundle
`f *ᵖ E`. -/
theorem exists_continuous_frame [NormedAlgebra ℝ 𝕜] [CompleteSpace F] [VectorBundle 𝕜 F E]
    [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
    [R1Space B] [ParacompactSpace B] [ContractibleSpace B] (hf : Continuous f) :
    ∃ φ : ∀ y, F ≃L[𝕜] E (f y),
      Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2) := by
  let g : C(B, X) := ⟨f, hf⟩
  have : ∀ y, IsTopologicalAddGroup ((g *ᵖ E) y) := fun y ↦
    inferInstanceAs (IsTopologicalAddGroup (E (f y)))
  have : ∀ y, ContinuousSMul 𝕜 ((g *ᵖ E) y) := fun y ↦
    inferInstanceAs (ContinuousSMul 𝕜 (E (f y)))
  obtain ⟨e, he, hbase⟩ :=
    exists_trivialization_baseSet_eq_univ_of_contractibleSpace 𝕜 F (g *ᵖ E)
  have hb (y : B) : y ∈ e.baseSet := hbase ▸ mem_univ y
  refine ⟨fun y ↦ (e.continuousLinearEquivAt 𝕜 y (hb y)).symm, ?_⟩
  have hsymm : Continuous fun q : B × F ↦ TotalSpace.mk' F q.1 (e.symm q.1 q.2) :=
    e.continuousOn_symm.comp_continuous continuous_id fun q ↦ ⟨hb q.1, mem_univ _⟩
  -- `Pullback.lift` and the inverse of `continuousLinearEquivAt` are the identity on fibres.
  exact (Pullback.continuous_lift F E g).comp hsymm

end Frame

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
  refine ⟨e.toHomeomorphOfBaseSetEqUniv he, L, fun b v ↦ ?_⟩
  rw [Trivialization.coe_toHomeomorphOfBaseSetEqUniv]
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
        (h v).1 = (v : TotalSpace F E).proj ∧ ((h v).2 : F) = L _ (v : TotalSpace F E).snd) ∧
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
      (k v).1 = (v : TotalSpace F E).proj ∧ ((k v).2 : F) = L _ (v : TotalSpace F E).snd := by
    obtain ⟨⟨b, w⟩, hw⟩ := v
    simp [k, Homeomorph.Set.prod_apply _ _ (h.sets hdisc ⟨⟨b, w⟩, hw⟩), hL]
  refine ⟨k, L, hk, fun v ↦ ?_⟩
  rw [mem_sphereBundle, (hk v).2, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]

end Disc

section Frame

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : B → Type*} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {Y : Type*} [TopologicalSpace Y] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]

variable (F E) in
/-- **Orthonormal frames along a map out of a contractible space.** Let `E` be a vector bundle over
`𝕜 = ℝ` or `ℂ` with finite-dimensional model fibre `F` and fibre inner products whose norm is
continuous on the total space, and let `V` be an inner product space of the dimension of `F`. Every
continuous map `g` from a contractible paracompact R₁ space `Y` to the base lifts to a continuous
map into the orthonormal frame bundle: a continuous family of orthonormal frames
`V ≃ₗᵢ[𝕜] E (g y)`. -/
theorem exists_orthonormalFrameBundle_lift_of_contractibleSpace
    (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (g : C(Y, B)) :
    ∃ s : C(Y, OrthonormalFrameBundle 𝕜 F E V), ∀ y, (s y).proj = g y := by
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  -- The pullback of `E` to the contractible space `Y` has a trivialization over all of `Y`.
  obtain ⟨e, he, hbase⟩ :=
    exists_trivialization_baseSet_eq_univ_of_contractibleSpace 𝕜 F ((g : Y → B) *ᵖ E)
  have hY (y : Y) : y ∈ e.baseSet := hbase ▸ mem_univ y
  -- Its Gram–Schmidt orthonormal frame, read as a frame of `E` along `g`. Gram–Schmidt reads the
  -- pullback fibres with the topology of their norms, which agrees with the pullback fibre topology
  -- only after unfolding instances, so the fibre and vector bundle structures of the pullback are
  -- restated for it.
  let fb : @FiberBundle Y F _ _ ((g : Y → B) *ᵖ E) _ fun _ ↦ UniformSpace.toTopologicalSpace :=
    FiberBundle.pullback (F := F) (E := E) g
  let : @VectorBundle 𝕜 Y F ((g : Y → B) *ᵖ E) _ _ _ _ _ _ _ _ fb :=
    VectorBundle.pullback 𝕜 (F := F) (E := E) g
  let c := Module.finBasisOfFinrankEq 𝕜 F h.symm
  let o := stdOrthonormalBasis 𝕜 V
  exact ⟨⟨fun y ↦ OrthonormalFrameBundle.pullbackLift g ⟨y, e.orthonormalFrame c o ⟨y, hY y⟩⟩,
    (OrthonormalFrameBundle.continuous_pullbackLift g).comp
      ((e.continuous_orthonormalFrame c o).comp (continuous_id.subtype_mk hY))⟩,
    fun _ ↦ OrthonormalFrameBundle.proj_pullbackLift _ _⟩

end Frame

end TauCeti
