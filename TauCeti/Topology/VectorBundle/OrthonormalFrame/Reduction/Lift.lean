/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.TotalSpace
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.FiberBundle.MapFiber
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction.Basic

/-!
# Reductions of the orthonormal frame bundle as principal bundles

Let `E → X` be a vector bundle with fibre inner products, `V` a real inner product space, `H` a
subgroup of the orthogonal group of `V`, and `S` a set of orthonormal frames of `E` modelled on
`V` which `H` preserves exactly (`TauCeti.OrthonormalFrameBundle.SMulMemIff H S`). The frames of
`S` over each point form the fibres `TauCeti.OrthonormalFrameBundle.ReductionFiber S`, on which
`H` acts on the right by precomposition. When `S` is locally trivial with fibre `H`, equivariantly
(as `exists_trivialization_unitaryFrames` and `exists_trivialization_orientedFrames` provide),
these fibres form a principal `H`-bundle (`TauCeti.OrthonormalFrameBundle.reductionFiberBundle`,
`TauCeti.OrthonormalFrameBundle.principalBundle_reductionFiber`): this is the reduction of the
structure group of the orthonormal frame bundle to `H`. Both come from the bundle of a locally
trivial map (`TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph`), applied to `S → X` and the
identification `TauCeti.OrthonormalFrameBundle.reductionTotalSpaceHomeomorph` of the total space
of the reduction with `S`. The fibres are `ReductionFiber S` rather than `TauCeti.MapFiber` so
that they lie in the universe of `E`, as `TauCeti.OrthonormalFrameLift` requires.

For `V = ℝⁿ` the inclusion of the reduced frames into all orthonormal frames makes the reduction
a lift of the orthonormal frame bundle along `H → O(n) → GL(ℝⁿ)`
(`TauCeti.OrthonormalFrameBundle.reductionLift`), where `O(n) → GL(ℝⁿ)` is
`TauCeti.euclideanLinearEquivHom n`. For the unitary frames of a fibrewise orthogonal complex
structure this is `TauCeti.OrthonormalFrameBundle.unitaryFrameLift`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.ReductionFiber S`: the frames of `S` over a point, with the
  right action of `H`.
* `TauCeti.OrthonormalFrameBundle.reductionFiberBundle`,
  `TauCeti.OrthonormalFrameBundle.principalBundle_reductionFiber`: a locally trivial reduction is
  a principal `H`-bundle.
* `TauCeti.OrthonormalFrameBundle.reductionLift`: a locally trivial reduction of the frames
  modelled on `ℝⁿ` as a lift of the orthonormal frame bundle.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

noncomputable section

open Bundle Set MulOpposite Module

universe w

namespace TauCeti.OrthonormalFrameBundle

section Fiber

variable {B : Type*} {F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] {H : Subgroup (unitary (V →L[ℝ] V))} (S : Set (OrthonormalFrameBundle ℝ F E V))

/-- The frames of `S` over the point `b`: the fibre over `b` of the reduction of the orthonormal
frame bundle given by `S`. -/
@[ext]
structure ReductionFiber (b : B) where
  /-- The frame. -/
  frame : V ≃ₗᵢ[ℝ] E b
  /-- The frame lies in `S`. -/
  mem : (⟨b, frame⟩ : OrthonormalFrameBundle ℝ F E V) ∈ S

variable {S}

/-- The right action of `H` on the frames of `S` over a point, by precomposition. -/
instance instSMulReductionFiber [SMulMemIff H S] (b : B) : SMul Hᵐᵒᵖ (ReductionFiber S b) where
  smul g φ := ⟨(Unitary.linearIsometryEquiv (g.unop : unitary (V →L[ℝ] V))).trans φ.frame,
    (SMulMemIff.smul_mem_iff φ.mem).2 g.unop.property⟩

/-- The action of `g` precomposes the frame with the orthogonal transformation `g`. -/
@[simp]
theorem ReductionFiber.smul_frame [SMulMemIff H S] {b : B} (g : Hᵐᵒᵖ) (φ : ReductionFiber S b) :
    (g • φ).frame = (Unitary.linearIsometryEquiv (g.unop : unitary (V →L[ℝ] V))).trans φ.frame :=
  (rfl)

/-- The right action of `H` on the frames of `S` over a point is an action. -/
instance [SMulMemIff H S] (b : B) : MulAction Hᵐᵒᵖ (ReductionFiber S b) where
  one_smul _ := ReductionFiber.ext (LinearIsometryEquiv.ext fun _ ↦ rfl)
  mul_smul _ _ _ := ReductionFiber.ext (LinearIsometryEquiv.ext fun _ ↦ rfl)

variable (H S) in
/-- The total space of the reduction is the set `S` of frames. -/
def reductionTotalSpaceEquiv : TotalSpace H (ReductionFiber S) ≃ S where
  toFun p := ⟨⟨p.proj, p.snd.frame⟩, p.snd.mem⟩
  invFun p := ⟨p.val.proj, ⟨p.val.frame, p.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_reductionTotalSpaceEquiv_apply (p : TotalSpace H (ReductionFiber S)) :
    (reductionTotalSpaceEquiv H S p : OrthonormalFrameBundle ℝ F E V) = ⟨p.proj, p.snd.frame⟩ :=
  (rfl)

@[simp]
theorem reductionTotalSpaceEquiv_symm_apply (p : S) :
    (reductionTotalSpaceEquiv H S).symm p =
      ⟨(p : OrthonormalFrameBundle ℝ F E V).proj, ⟨(p : OrthonormalFrameBundle ℝ F E V).frame,
        p.property⟩⟩ :=
  (rfl)

/-- The identification of the total space with `S` intertwines the right actions of `H`. -/
@[simp]
theorem reductionTotalSpaceEquiv_smul [SMulMemIff H S] (g : Hᵐᵒᵖ)
    (p : TotalSpace H (ReductionFiber S)) :
    reductionTotalSpaceEquiv H S (g • p) = g • reductionTotalSpaceEquiv H S p :=
  (rfl)

variable [TopologicalSpace (TotalSpace F E)]

/-- The topology on the total space of the reduction making `reductionTotalSpaceEquiv` a
homeomorphism onto `S` with the subspace topology of the orthonormal frame bundle. -/
instance instTopologicalSpaceReductionTotalSpace :
    TopologicalSpace (TotalSpace H (ReductionFiber S)) :=
  .induced (reductionTotalSpaceEquiv H S) inferInstance

/-- Each fibre of the reduction carries the topology of its frames in the orthonormal frame
bundle, which is the subspace topology of the total space. -/
instance instTopologicalSpaceReductionFiber (b : B) : TopologicalSpace (ReductionFiber S b) :=
  .induced (fun φ ↦ (⟨b, φ.frame⟩ : OrthonormalFrameBundle ℝ F E V)) inferInstance

variable (H S) in
/-- The total space of the reduction is homeomorphic to `S`. -/
def reductionTotalSpaceHomeomorph : TotalSpace H (ReductionFiber S) ≃ₜ S :=
  (reductionTotalSpaceEquiv H S).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem coe_reductionTotalSpaceHomeomorph :
    ⇑(reductionTotalSpaceHomeomorph H S) = reductionTotalSpaceEquiv H S :=
  (rfl)

@[simp]
theorem coe_reductionTotalSpaceHomeomorph_symm :
    ⇑(reductionTotalSpaceHomeomorph H S).symm = (reductionTotalSpaceEquiv H S).symm :=
  (rfl)

/-- The inclusion of the total space of the reduction into the orthonormal frame bundle is
continuous. -/
theorem continuous_coe_reductionTotalSpaceEquiv :
    Continuous fun p : TotalSpace H (ReductionFiber S) ↦
      (reductionTotalSpaceEquiv H S p : OrthonormalFrameBundle ℝ F E V) :=
  continuous_subtypeVal.comp (reductionTotalSpaceHomeomorph H S).continuous

variable (H) in
/-- Each fibre of the reduction is embedded in its total space, since both carry topologies
induced from the orthonormal frame bundle. -/
theorem ReductionFiber.isInducing_totalSpaceMk (b : B) :
    Topology.IsInducing (TotalSpace.mk b : ReductionFiber S b → TotalSpace H (ReductionFiber S)) :=
  (Topology.IsInducing.subtypeVal.comp
    (reductionTotalSpaceHomeomorph H S).isInducing).of_comp_iff.1 (Topology.IsInducing.induced _)

end Fiber

section Bundle

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] {H : Subgroup (unitary (V →L[ℝ] V))}
  {S : Set (OrthonormalFrameBundle ℝ F E V)} [SMulMemIff H S]

variable (H S) in
/-- `S` is locally trivial with fibre `H`, equivariantly: every point lies in the base set of a
trivialization of `S` turning the action of `H` into right multiplication. -/
def IsLocallyTrivialReduction : Prop :=
  ∀ x : B, ∃ t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
    x ∈ t.baseSet ∧ ∀ (g : H) (p : S), (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
      t (op g • p) = ((t p).1, (t p).2 * g)

/-- Unfolds `IsLocallyTrivialReduction`: every point lies in the base set of an equivariant
trivialization of `S`. -/
theorem isLocallyTrivialReduction_iff : IsLocallyTrivialReduction H S ↔
    ∀ x : B, ∃ t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : H) (p : S), (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
        t (op g • p) = ((t p).1, (t p).2 * g) :=
  Iff.rfl

variable (hS : IsLocallyTrivialReduction H S)

/-- The atlas of `S` given by the chosen equivariant trivializations of a locally trivial
reduction. -/
def IsLocallyTrivialReduction.atlas :
    MapFiber.Atlas H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj) :=
  ⟨fun x ↦ (isLocallyTrivialReduction_iff.1 hS x).choose,
    fun x ↦ (isLocallyTrivialReduction_iff.1 hS x).choose_spec.1⟩

/-- The trivialization of the atlas at `x` is the chosen equivariant trivialization at `x`. -/
theorem IsLocallyTrivialReduction.atlas_trivAt (x : B) :
    hS.atlas.trivAt x = (isLocallyTrivialReduction_iff.1 hS x).choose :=
  (rfl)

/-- **A locally trivial reduction of the orthonormal frame bundle is a fibre bundle** with fibre
`H`, with the chosen trivializations as its atlas. -/
@[instance_reducible]
def reductionFiberBundle : FiberBundle H (ReductionFiber S) :=
  hS.atlas.fiberBundleOfHomeomorph (reductionTotalSpaceHomeomorph H S) (fun _ ↦ rfl)
    (ReductionFiber.isInducing_totalSpaceMk H)

/-- The trivialization at `x` of the reduction is the chosen equivariant trivialization of `S` at
`x`, transported along `reductionTotalSpaceHomeomorph`. -/
theorem trivializationAt_reductionFiberBundle (x : B) :
    letI := reductionFiberBundle hS
    trivializationAt H (ReductionFiber S) x =
      (hS.atlas.trivAt x).compTotalSpaceHomeomorph (reductionTotalSpaceHomeomorph H S)
        (fun _ ↦ by simp) :=
  hS.atlas.trivializationAt_fiberBundleOfHomeomorph _ _ _ x

/-- **A locally trivial reduction of the orthonormal frame bundle is a principal `H`-bundle.** -/
theorem principalBundle_reductionFiber :
    letI := reductionFiberBundle hS
    PrincipalBundle H (ReductionFiber S) :=
  hS.atlas.principalBundleOfHomeomorph _ _ _ (fun _ _ _ ↦ rfl)
    fun x p hp g ↦ congrArg Prod.snd ((isLocallyTrivialReduction_iff.1 hS x).choose_spec.2 g p hp)

end Bundle

section Lift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {n : ℕ}
  {H : Subgroup (unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))}
  {S : Set (OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)))} [SMulMemIff H S]

omit [TopologicalSpace X] [TopologicalSpace (TotalSpace F E)] in
/-- The frame of `φ` acted on by `g` sends `v` to the frame of `φ` applied to the image of `v`
under `H → O(n) → GL(ℝⁿ)`. -/
theorem ReductionFiber.frame_smul_apply {x : X} (φ : ReductionFiber S x) (g : H)
    (v : Fin n → ℝ) :
    (op g • φ).frame (WithLp.toLp 2 v) =
      φ.frame (WithLp.toLp 2 ((euclideanLinearEquivHom n).comp H.subtype g v)) := by
  simp [← Unitary.coe_linearIsometryEquiv_apply]

/-- **A locally trivial reduction of the orthonormal frame bundle modelled on `ℝⁿ` is a lift of
the orthonormal frame bundle** along `H → O(n) → GL(ℝⁿ)`: its principal bundle is the reduction,
and the frame of a point of the reduction is that point itself. -/
@[expose] def reductionLift (hS : IsLocallyTrivialReduction H S) :
    OrthonormalFrameLift F E n H ((euclideanLinearEquivHom n).comp H.subtype) where
  P := ReductionFiber S
  fiberBundle := reductionFiberBundle hS
  principal := principalBundle_reductionFiber hS
  toFrame p := ⟨p.proj, p.snd.frame⟩
  continuous_toFrame :=
    continuous_coe_reductionTotalSpaceEquiv.congr coe_reductionTotalSpaceEquiv_apply
  proj_toFrame _ := rfl
  toFrame_smul x φ g v := congrArg (TotalSpace.mk' F x) (ReductionFiber.frame_smul_apply φ g v)

variable (hS : IsLocallyTrivialReduction H S)

@[simp]
theorem reductionLift_P : (reductionLift hS).P = ReductionFiber S :=
  (rfl)

/-- The frame of a point of the reduction is that point itself. -/
@[simp]
theorem reductionLift_toFrame (p : TotalSpace H (ReductionFiber S)) :
    (reductionLift hS).toFrame p = ⟨p.proj, p.snd.frame⟩ :=
  (rfl)

end Lift

end TauCeti.OrthonormalFrameBundle
