/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import Mathlib.Topology.Algebra.Module.TransferInstance
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Compatible trivializations from fibrewise linear equivalences on open sets

Let `V → B` be a topological `𝕜`-vector bundle with finite-dimensional model fibre `F` over a
complete nontrivially normed field `𝕜` and a charted base `B`, and let `U ⊆ B` be open. Given
continuous linear maps `L : ∀ x, V x →L[𝕜] F` that are bijective over `U` and whose total-space
evaluation `(x, v) ↦ L x v` is `C^n` on `π⁻¹(U)`, `Bundle.Trivialization.ofContinuousLinearMapOn`
packages `(x, v) ↦ (x, L x v)` into a linear trivialization over `U` without requiring a separate
proof that the fibrewise inverses `(L x)⁻¹` vary smoothly (`ofContinuousLinearMapOn_apply`,
`coordChangeL_ofContinuousLinearMapOn_apply`).

Whereas `ofContinuousLinearMapOn` itself requires only `[VectorBundle 𝕜 F V]`, assuming
`[ContMDiffVectorBundle n F V IB]` places it in `(contMDiffFiberwiseLinear B F IB n).maximalAtlas`
(`ofContinuousLinearMapOn_mem_maximalAtlas`), providing the chart-construction step for level-set
trivializations of quotient normal bundles.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 10.
-/

public noncomputable section

open Bundle Set Module Filter
open scoped Manifold ContDiff Topology

namespace Bundle.Trivialization

section Algebra

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  {U : Set B} (L : ∀ x, V x →L[𝕜] F) (hbij : ∀ x ∈ U, Function.Bijective (L x))

private def equivAt {x : B} (hx : x ∈ U) : V x ≃ₗ[𝕜] F :=
  LinearEquiv.ofBijective (L x).toLinearMap (hbij x hx)

@[simp]
private theorem equivAt_apply {x : B} (hx : x ∈ U) (v : V x) :
    equivAt L hbij hx v = L x v := rfl

variable [FiniteDimensional 𝕜 F]

open scoped Classical in
private def invFrame (i : Fin (finrank 𝕜 F)) (x : B) : V x :=
  if hx : x ∈ U then (equivAt L hbij hx).symm (finBasis 𝕜 F i) else 0

private theorem invFrame_of_mem {x : B} (hx : x ∈ U) (i : Fin (finrank 𝕜 F)) :
    invFrame L hbij i x = (equivAt L hbij hx).symm (finBasis 𝕜 F i) := by
  simp [invFrame, hx]

end Algebra

section Construction

variable {𝕜 EB HB B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] {U : Set B}
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω} (hU : IsOpen U) (L : ∀ x, V x →L[𝕜] F)
  (hL : ContMDiffOn (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
    (fun p : TotalSpace F V ↦ L p.proj p.snd) (π F V ⁻¹' U))
  (hbij : ∀ x ∈ U, Function.Bijective (L x))

include hU hL in
private theorem isLocalFrameOn_invFrame : IsLocalFrameOn IB F n (invFrame L hbij) U := by
  have hbasis {x} (hx : x ∈ U) :
      (fun i ↦ invFrame L hbij i x) = (finBasis 𝕜 F).map (equivAt L hbij hx).symm :=
    funext fun i ↦ invFrame_of_mem L hbij hx i
  refine ⟨fun hx ↦ hbasis hx ▸ Basis.linearIndependent _,
    fun hx ↦ hbasis hx ▸ (Basis.span_eq _).ge, fun i x₀ hx₀ ↦ ?_⟩
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  have : ∀ x, IsTopologicalAddGroup (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have : ∀ x, ContinuousSMul 𝕜 (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  have : ∀ x, T2Space (V x) := FiberBundle.t2Space F V
  have : ∀ x, FiniteDimensional 𝕜 (V x) := fun x ↦ VectorBundle.finiteDimensional 𝕜 F V x
  let L' : ∀ x, V x →L[𝕜] Trivial B F x := L
  have hLhom : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun y ↦ V y →L[𝕜] Trivial B F y) x (L' x)) x₀ :=
    (TauCeti.contMDiffAt_hom_bundle_iff (IB := IB) (n := n) (F₁ := F) (F₂ := F) L' x₀).2 fun v ↦
      Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_proj V, by
        simpa using hL.contMDiffAt
          ((hU.preimage (FiberBundle.continuous_proj F V)).mem_nhds (hx₀ : ⟨x₀, v⟩ ∈ π F V ⁻¹' U))⟩
  have hinv₀ : (L' x₀).IsInvertible := ⟨(equivAt L hbij hx₀).toContinuousLinearEquiv, rfl⟩
  have hsec : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F (E := V) x ((L' x).inverse (finBasis 𝕜 F i))) x₀ :=
    (hLhom.clm_bundle_inverse hinv₀).clm_bundle_apply
      (Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_id, by simpa using contMDiffAt_const⟩)
  refine (hsec.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU.mem_nhds hx₀] with x hx
  congr 1
  have heq : L' x = ((equivAt L hbij hx).toContinuousLinearEquiv : V x →L[𝕜] F) := rfl
  rw [invFrame_of_mem L hbij hx, heq, ContinuousLinearMap.inverse_equiv]; simp

/-- The linear trivialization of a topological `𝕜`-vector bundle `V` over an open set `U` determined
by a family `L : ∀ x, V x →L[𝕜] F` of continuous linear maps that are bijective over `U` and whose
total-space evaluation is `C^n` on `π⁻¹(U)`. Over `U` it sends `⟨x, v⟩` to `(x, L x v)`; when `V`
carries `[ContMDiffVectorBundle n F V IB]`, it belongs to the `C^n` maximal atlas
(`ofContinuousLinearMapOn_mem_maximalAtlas`). -/
def ofContinuousLinearMapOn : Trivialization F (π F V) :=
  (isLocalFrameOn_invFrame hU L hL hbij).trivialization hU (finBasis 𝕜 F)

@[simp] theorem baseSet_ofContinuousLinearMapOn :
    (ofContinuousLinearMapOn hU L hL hbij).baseSet = U :=
  (isLocalFrameOn_invFrame hU L hL hbij).baseSet_trivialization hU (finBasis 𝕜 F)

/-- The trivialization `ofContinuousLinearMapOn` belongs to the maximal atlas of `C^n`
trivializations of `V`. -/
theorem ofContinuousLinearMapOn_mem_maximalAtlas [ContMDiffVectorBundle n F V IB] :
    (ofContinuousLinearMapOn hU L hL hbij).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) :=
  (isLocalFrameOn_invFrame hU L hL hbij).trivialization_mem_maximalAtlas hU (finBasis 𝕜 F)

/-- Over `U`, `ofContinuousLinearMapOn` evaluates `L` on the fibre component. -/
@[simp] theorem ofContinuousLinearMapOn_apply {p : TotalSpace F V} (hp : p.proj ∈ U) :
    ofContinuousLinearMapOn hU L hL hbij p = (p.proj, L p.proj p.snd) := by
  obtain ⟨x, v⟩ := p
  rw [ofContinuousLinearMapOn,
    (isLocalFrameOn_invFrame hU L hL hbij).trivialization_apply hU (finBasis 𝕜 F) hp]
  congr 1
  set hs := isLocalFrameOn_invFrame hU L hL hbij; set b := finBasis 𝕜 F
  have hv : v = ∑ i, b.repr (L x v) i • hs.toBasisAt hp i :=
    (equivAt L hbij hp).injective <| by
      rw [map_sum]; conv_lhs => rw [equivAt_apply, ← b.sum_repr (L x v)]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [map_smul, IsLocalFrameOn.toBasisAt_coe, invFrame_of_mem L hbij hp,
          LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hv]
  rw [map_sum]; conv_rhs => rw [← b.sum_repr (L x v)]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, Basis.equiv_apply, Equiv.refl_apply]

/-- `ofContinuousLinearMapOn` is `𝕜`-linear on every fibre over `U`. -/
instance isLinear_ofContinuousLinearMapOn : (ofContinuousLinearMapOn hU L hL hbij).IsLinear 𝕜 where
  linear x hx := by
    have hxU : x ∈ U := by simpa using hx
    simpa [ofContinuousLinearMapOn_apply hU L hL hbij (p := ⟨x, _⟩) hxU] using
      (L x).toLinearMap.isLinear

/-- Over `U`, the fibrewise continuous linear map of `ofContinuousLinearMapOn` is `L x`. -/
@[simp] theorem continuousLinearMapAt_ofContinuousLinearMapOn {x : B} (hx : x ∈ U) :
    (ofContinuousLinearMapOn hU L hL hbij).continuousLinearMapAt 𝕜 x = L x := by
  ext v
  rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ (by simpa using hx),
    ofContinuousLinearMapOn_apply hU L hL hbij (p := ⟨x, v⟩) hx]

/-- Over `U`, `L x` is left-inverse to `(ofContinuousLinearMapOn ...).symm x`. -/
@[simp] theorem apply_symm_ofContinuousLinearMapOn {x : B} (hx : x ∈ U) (w : F) :
    L x ((ofContinuousLinearMapOn hU L hL hbij).symm x w) = w := by
  have h := (ofContinuousLinearMapOn hU L hL hbij).apply_mk_symm (by simpa using hx) w
  rw [ofContinuousLinearMapOn_apply hU L hL hbij (p := ⟨x, _⟩) hx] at h; exact congrArg Prod.snd h

/-- Over `U`, `(ofContinuousLinearMapOn ...).symm x` is left-inverse to `L x`. -/
@[simp] theorem symm_apply_ofContinuousLinearMapOn {x : B} (hx : x ∈ U) (v : V x) :
    (ofContinuousLinearMapOn hU L hL hbij).symm x (L x v) = v :=
  (hbij x hx).1 (apply_symm_ofContinuousLinearMapOn hU L hL hbij hx (L x v))

section Overlap

variable {U' : Set B} (hU' : IsOpen U') (L' : ∀ x, V x →L[𝕜] F)
  (hL' : ContMDiffOn (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
    (fun p : TotalSpace F V ↦ L' p.proj p.snd) (π F V ⁻¹' U'))
  (hbij' : ∀ x ∈ U', Function.Bijective (L' x)) {x : B} (hx : x ∈ U ∩ U')

include hx

/-- On the overlap `U ∩ U'`, the coordinate change from `ofContinuousLinearMapOn` for `L` to that
for `L'` intertwines `L x` with `L' x`. -/
@[simp] theorem coordChangeL_ofContinuousLinearMapOn_apply (v : V x) :
    (ofContinuousLinearMapOn hU L hL hbij).coordChangeL 𝕜
      (ofContinuousLinearMapOn hU' L' hL' hbij') x (L x v) = L' x v := by
  rw [Trivialization.coordChangeL_apply _ _ ⟨by simpa using hx.1, by simpa using hx.2⟩,
    symm_apply_ofContinuousLinearMapOn hU L hL hbij hx.1 v,
    ofContinuousLinearMapOn_apply hU' L' hL' hbij' (p := ⟨x, v⟩) hx.2]

/-- On the overlap `U ∩ U'`, composing the coordinate change between two `ofContinuousLinearMapOn`
trivializations with `L x` recovers `L' x`. -/
theorem coordChangeL_ofContinuousLinearMapOn_comp :
    ((ofContinuousLinearMapOn hU L hL hbij).coordChangeL 𝕜
      (ofContinuousLinearMapOn hU' L' hL' hbij') x : F →L[𝕜] F).comp (L x) = L' x :=
  ContinuousLinearMap.ext <|
    coordChangeL_ofContinuousLinearMapOn_apply hU L hL hbij hU' L' hL' hbij' hx

end Overlap

/-- `ofContinuousLinearMapOn` depends only on the values of `L` over `U`. -/
theorem ofContinuousLinearMapOn_congr {L' : ∀ x, V x →L[𝕜] F}
    (hL' : ContMDiffOn (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun p : TotalSpace F V ↦ L' p.proj p.snd) (π F V ⁻¹' U))
    (hbij' : ∀ x ∈ U, Function.Bijective (L' x)) (heq : ∀ x ∈ U, L x = L' x) :
    ofContinuousLinearMapOn hU L hL hbij = ofContinuousLinearMapOn hU L' hL' hbij' := by
  have hframe : invFrame L hbij = invFrame L' hbij' := by
    ext i x
    by_cases hx : x ∈ U
    · refine (equivAt L' hbij' hx).injective ?_
      rw [invFrame_of_mem L hbij hx, invFrame_of_mem L' hbij' hx, LinearEquiv.apply_symm_apply,
        equivAt_apply, ← heq x hx, ← equivAt_apply L hbij hx, LinearEquiv.apply_symm_apply]
    · simp [invFrame, hx]
  unfold ofContinuousLinearMapOn; congr 1

end Construction

end Bundle.Trivialization
