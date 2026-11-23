/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.TotalSpace
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.ComplexStructure
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift

/-!
# Reductions of the orthonormal frame bundle as principal bundles

Let `E → X` be a vector bundle with fibre inner products, `V` a real inner product space, `H` a
subgroup of the orthogonal group of `V`, and `S` a set of orthonormal frames of `E` modelled on
`V` which `H` preserves exactly (`TauCeti.OrthonormalFrameBundle.SMulMemIff H S`). The frames of
`S` over each point form the fibres `TauCeti.OrthonormalFrameBundle.ReductionFiber S`, on which
`H` acts on the right by precomposition. When `S` is locally trivial with fibre `H`, equivariantly
(as `exists_trivialization_unitaryFrames` and `exists_trivialization_orientedFrames` provide),
these fibres form a principal `H`-bundle (`TauCeti.OrthonormalFrameBundle.reductionFiberBundle`,
`TauCeti.OrthonormalFrameBundle.reductionPrincipalBundle`): this is the reduction of the
structure group of the orthonormal frame bundle to `H`.

For `V = ℝⁿ` the inclusion of the reduced frames into all orthonormal frames makes the reduction
a lift of the orthonormal frame bundle along `H → O(n) → GL(ℝⁿ)`
(`TauCeti.OrthonormalFrameBundle.reductionLift`). For a continuous fibrewise orthogonal complex
structure `J` on a rank-four bundle and an orthogonal complex structure `J₀` of `ℝ⁴`, the unitary
frames give the lift along `U(2) = U(ℝ⁴, J₀) ⊆ SO(4)`
(`TauCeti.OrthonormalFrameBundle.unitaryFrameLift`), the reduction to `U(2)` given by `J`. With
the canonical lift `U(2) → Spinᶜ(4)` this is the input of the canonical `Spinᶜ` structure of an
almost Hermitian four-manifold (`TauCeti.OrthonormalFrameLift.extendSpinC`).

## Main definitions

* `TauCeti.OrthonormalFrameBundle.ReductionFiber S`: the frames of `S` over a point, with the
  right action of `H`.
* `TauCeti.OrthonormalFrameBundle.reductionFiberBundle`,
  `TauCeti.OrthonormalFrameBundle.reductionPrincipalBundle`: a locally trivial reduction is a
  principal `H`-bundle.
* `TauCeti.OrthonormalFrameBundle.euclideanLinearEquivHom n`: an orthogonal transformation of
  `EuclideanSpace ℝ (Fin n)` as a linear automorphism of `Fin n → ℝ`.
* `TauCeti.OrthonormalFrameBundle.reductionLift`: a locally trivial reduction of the frames
  modelled on `ℝⁿ` as a lift of the orthonormal frame bundle.
* `TauCeti.OrthonormalFrameBundle.unitaryFrameLift`: the unitary frames of a rank-four bundle with
  a continuous fibrewise orthogonal complex structure, as a lift along `U(2) ⊆ SO(4)`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
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
structure ReductionFiber (b : B) where
  /-- The frame. -/
  frame : V ≃ₗᵢ[ℝ] E b
  /-- The frame lies in `S`. -/
  mem : (⟨b, frame⟩ : OrthonormalFrameBundle ℝ F E V) ∈ S

omit [CompleteSpace V] in
variable {S} in
/-- Two frames of `S` over the same point are equal when their frames are. -/
@[ext]
theorem ReductionFiber.ext {b : B} {φ ψ : ReductionFiber S b} (h : φ.frame = ψ.frame) :
    φ = ψ := by
  cases φ; cases ψ; cases h; rfl

variable {S}

/-- The right action of `H` on the frames of `S` over a point, by precomposition. -/
instance instSMulReductionFiber [SMulMemIff H S] (b : B) : SMul Hᵐᵒᵖ (ReductionFiber S b) where
  smul g φ := ⟨(Unitary.linearIsometryEquiv (g.unop : unitary (V →L[ℝ] V))).trans φ.frame,
    (SMulMemIff.smul_mem_iff φ.mem).2 g.unop.property⟩

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

/-- The identification of the total space with `S` intertwines the right actions of `H`. -/
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

end Fiber

section Bundle

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] {H : Subgroup (unitary (V →L[ℝ] V))}
  {S : Set (OrthonormalFrameBundle ℝ F E V)}

/-- An equivariant trivialization of `S`, as a trivialization of the total space of the
reduction. -/
def reductionTrivialization
    (t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj)) :
    Trivialization H (π H (ReductionFiber S)) :=
  t.compHomeomorph (reductionTotalSpaceHomeomorph H S)

@[simp]
theorem reductionTrivialization_apply
    (t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj))
    (p : TotalSpace H (ReductionFiber S)) :
    reductionTrivialization t p = t (reductionTotalSpaceEquiv H S p) :=
  (rfl)

@[simp]
theorem baseSet_reductionTrivialization
    (t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj)) :
    (reductionTrivialization t).baseSet = t.baseSet :=
  (rfl)

/-- The reduction of an equivariant trivialization of `S` is equivariant. -/
theorem isEquivariant_reductionTrivialization [SMulMemIff H S]
    (t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj))
    (ht : ∀ (g : H) (p : S), (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
      t (op g • p) = ((t p).1, (t p).2 * g)) :
    (reductionTrivialization t).IsEquivariant where
  snd_apply_smul b hb φ g := by
    rw [reductionTrivialization_apply, reductionTrivialization_apply,
      ← TotalSpace.smul_mk, reductionTotalSpaceEquiv_smul,
      ht g (reductionTotalSpaceEquiv H S ⟨b, φ⟩) hb]

variable [SMulMemIff H S]

variable (H S) in
/-- `S` is locally trivial with fibre `H`, equivariantly: every point lies in the base set of a
trivialization of `S` turning the action of `H` into right multiplication. -/
def IsLocallyTrivialReduction : Prop :=
  ∀ x : B, ∃ t : Trivialization H (fun p : S ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
    x ∈ t.baseSet ∧ ∀ (g : H) (p : S), (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
      t (op g • p) = ((t p).1, (t p).2 * g)

variable (hS : IsLocallyTrivialReduction H S)

/-- The chosen equivariant trivialization of a locally trivial reduction at a point. -/
def IsLocallyTrivialReduction.trivializationAt (x : B) :
    Trivialization H (π H (ReductionFiber S)) :=
  reductionTrivialization (hS x).choose

/-- **A locally trivial reduction of the orthonormal frame bundle is a fibre bundle** with fibre
`H`, with the chosen trivializations as its atlas. -/
@[instance_reducible]
def reductionFiberBundle : FiberBundle H (ReductionFiber S) where
  totalSpaceMk_isInducing' _ := ⟨by
    rw [instTopologicalSpaceReductionFiber, instTopologicalSpaceReductionTotalSpace,
      induced_compose, instTopologicalSpaceSubtype, induced_compose]; rfl⟩
  trivializationAtlas' := range hS.trivializationAt
  trivializationAt' := hS.trivializationAt
  mem_baseSet_trivializationAt' x := (hS x).choose_spec.1
  trivialization_mem_atlas' x := mem_range_self x

/-- **A locally trivial reduction of the orthonormal frame bundle is a principal `H`-bundle.** -/
theorem reductionPrincipalBundle :
    letI := reductionFiberBundle hS
    PrincipalBundle H (ReductionFiber S) := by
  let _ := reductionFiberBundle hS
  refine ⟨fun e he ↦ ?_⟩
  obtain ⟨x, rfl⟩ := he.out
  exact isEquivariant_reductionTrivialization _ (hS x).choose_spec.2

end Bundle

section Lift

/-- An orthogonal transformation of `EuclideanSpace ℝ (Fin n)`, as a linear automorphism of
`Fin n → ℝ`. -/
def euclideanLinearEquivHom (n : ℕ) :
    unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →*
      (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun g := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.trans
    ((Unitary.linearIsometryEquiv g).toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)))
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
theorem euclideanLinearEquivHom_apply (n : ℕ)
    (g : unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (v : Fin n → ℝ) :
    euclideanLinearEquivHom n g v =
      WithLp.ofLp ((g : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 v)) :=
  (rfl)

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {n : ℕ}
  {H : Subgroup (unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))}
  {S : Set (OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)))} [SMulMemIff H S]

omit [TopologicalSpace X] [SMulMemIff H S] in
/-- The inclusion of the total space of the reduction into the orthonormal frame bundle is
continuous. -/
theorem continuous_reductionToFrame :
    Continuous fun p : TotalSpace H (ReductionFiber S) ↦
      (⟨p.proj, p.snd.frame⟩ : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))) :=
  continuous_subtypeVal.comp (reductionTotalSpaceHomeomorph H S).continuous

omit [TopologicalSpace X] [TopologicalSpace (TotalSpace F E)] in
/-- The inclusion of the reduction into the orthonormal frame bundle is equivariant along
`H → O(n) → GL(ℝⁿ)`. -/
theorem reductionToFrame_smul (x : X) (φ : ReductionFiber S x) (g : H) (v : Fin n → ℝ) :
    TotalSpace.mk' F x ((op g • φ).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F x
        (φ.frame (WithLp.toLp 2 ((euclideanLinearEquivHom n).comp H.subtype g v))) :=
  (rfl)

/-- **A locally trivial reduction of the orthonormal frame bundle modelled on `ℝⁿ` is a lift of
the orthonormal frame bundle** along `H → O(n) → GL(ℝⁿ)`: its principal bundle is the reduction,
and the frame of a point of the reduction is that point itself. -/
@[expose] def reductionLift (hS : IsLocallyTrivialReduction H S) :
    OrthonormalFrameLift F E n H ((euclideanLinearEquivHom n).comp H.subtype) where
  P := ReductionFiber S
  fiberBundle := reductionFiberBundle hS
  principal := reductionPrincipalBundle hS
  toFrame p := ⟨p.proj, p.snd.frame⟩
  continuous_toFrame := continuous_reductionToFrame
  proj_toFrame _ := rfl
  toFrame_smul := reductionToFrame_smul

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

section Unitary

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}

/-- In rank four, the unitary frames of a continuous fibrewise orthogonal complex structure form a
locally trivial reduction of the orthonormal frame bundle to the unitary group `U(ℝ⁴, J₀)`. -/
theorem isLocallyTrivialReduction_unitaryFrames
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
    (hJ₂ : ∀ x v, J x (J x v) = -v)
    (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
    (hF : finrank ℝ F = 4) :
    IsLocallyTrivialReduction (Subgroup.centralizer {J₀}) (unitaryFrames F J J₀) :=
  exists_trivialization_unitaryFrames hJ hJ₂ hJ₀ (finrank_euclideanSpace_fin) hF

/-- **The unitary frame bundle** of a rank-four bundle with a continuous fibrewise orthogonal
complex structure `J`, as a lift of the orthonormal frame bundle along
`U(2) = U(ℝ⁴, J₀) ⊆ SO(4)`: the reduction of the structure group to `U(2)` given by `J`. -/
def unitaryFrameLift
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
    (hJ₂ : ∀ x v, J x (J x v) = -v)
    (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
    (hF : finrank ℝ F = 4) :
    OrthonormalFrameLift F E 4 (Subgroup.centralizer {J₀})
      ((euclideanLinearEquivHom 4).comp (Subgroup.centralizer {J₀}).subtype) :=
  reductionLift (isLocallyTrivialReduction_unitaryFrames hJ hJ₂ hJ₀ hF)

end Unitary

end TauCeti.OrthonormalFrameBundle
