/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.TotalSpace
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.FiberBundle.MapFiber
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift.Basic
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction.Basic

/-!
# Reductions of the orthonormal frame bundle as principal bundles

Let `E → X` be a vector bundle with fibre inner products, `V` a real inner product space, `H` a
subgroup of the orthogonal group of `V`, and `S` a set of orthonormal frames of `E` modelled on `V`
which `H` preserves exactly (`TauCeti.OrthonormalFrameBundle.SMulMemIff H S`). The frames of `S`
over each point form the fibres `TauCeti.OrthonormalFrameBundle.ReductionFiber S`, subtypes of the
fibres `TauCeti.OrthonormalFrameBundle.Fiber` of the orthonormal frame bundle, from which they take
their topology and the right action of `H` by precomposition. When `S` is locally trivial with fibre
`H`, equivariantly (`TauCeti.IsLocallyTrivialReduction`, as `exists_trivialization_unitaryFrames`
and `exists_trivialization_orientedFrames` provide), these fibres form a principal `H`-bundle
(`TauCeti.OrthonormalFrameBundle.reductionFiberBundle`,
`TauCeti.OrthonormalFrameBundle.principalBundle_reductionFiber`): this is the reduction of the
structure group of the orthonormal frame bundle to `H`. Both come from the bundle of a locally
trivial map (`TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph`), applied to `S → X` and the
identification `TauCeti.OrthonormalFrameBundle.reductionTotalSpaceHomeomorph` of the total space of
the reduction with `S`. The fibres are `ReductionFiber S` rather than `TauCeti.MapFiber` so that
they lie in the universe of `E`, as `TauCeti.OrthonormalFrameLift` requires.

For `V = ℝⁿ` the inclusion of the reduced frames into all orthonormal frames makes the reduction
a lift of the orthonormal frame bundle along `H → O(n) → GL(ℝⁿ)`
(`TauCeti.OrthonormalFrameBundle.reductionLift`), where `O(n) → GL(ℝⁿ)` is
`TauCeti.euclideanLinearEquivHom ℝ (Fin n)`. For the unitary frames of a fibrewise orthogonal
complex structure this is `TauCeti.OrthonormalFrameBundle.unitaryFrameLift`.

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

/-- The frames of `S` over the point `b`, as points of the fibre `Fiber ℝ F E V b` of the
orthonormal frame bundle: the fibre over `b` of the reduction of the orthonormal frame bundle given
by `S`. It carries the subspace topology of `Fiber ℝ F E V b`. -/
abbrev ReductionFiber (b : B) : Type _ :=
  {φ : Fiber ℝ F E V b // (⟨b, φ.frame⟩ : OrthonormalFrameBundle ℝ F E V) ∈ S}

variable {S}

/-- The right action of `H` on the frames of `S` over a point, restricted from the action of the
orthogonal group on `Fiber ℝ F E V b`. -/
instance instSMulReductionFiber [SMulMemIff H S] (b : B) : SMul Hᵐᵒᵖ (ReductionFiber S b) where
  smul g φ := ⟨op (g.unop : unitary (V →L[ℝ] V)) • φ.val,
    (SMulMemIff.smul_mem_iff φ.property).2 g.unop.property⟩

/-- The action of `g` is the action of `g` as an orthogonal transformation on `Fiber ℝ F E V b`. -/
@[simp]
theorem ReductionFiber.val_smul [SMulMemIff H S] {b : B} (g : Hᵐᵒᵖ) (φ : ReductionFiber S b) :
    (g • φ).val = op (g.unop : unitary (V →L[ℝ] V)) • φ.val :=
  (rfl)

/-- The right action of `H` on the frames of `S` over a point is an action. -/
instance [SMulMemIff H S] (b : B) : MulAction Hᵐᵒᵖ (ReductionFiber S b) where
  one_smul φ := Subtype.ext (one_smul _ φ.val)
  mul_smul g h φ := Subtype.ext (mul_smul (op (g.unop : unitary (V →L[ℝ] V)))
    (op (h.unop : unitary (V →L[ℝ] V))) φ.val)

variable (H S) in
/-- The total space of the reduction is the set `S` of frames: `totalSpaceEquiv` restricted to the
frames of `S` (`coe_reductionTotalSpaceEquiv_eq`). -/
def reductionTotalSpaceEquiv : TotalSpace H (ReductionFiber S) ≃ S where
  toFun p := ⟨⟨p.proj, p.snd.val.frame⟩, p.snd.property⟩
  invFun p := ⟨p.val.proj, ⟨.ofFrame p.val.frame, p.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_reductionTotalSpaceEquiv_apply (p : TotalSpace H (ReductionFiber S)) :
    (reductionTotalSpaceEquiv H S p : OrthonormalFrameBundle ℝ F E V) = ⟨p.proj, p.snd.val.frame⟩ :=
  (rfl)

@[simp]
theorem reductionTotalSpaceEquiv_symm_apply (p : S) :
    (reductionTotalSpaceEquiv H S).symm p =
      ⟨(p : OrthonormalFrameBundle ℝ F E V).proj,
        ⟨.ofFrame (p : OrthonormalFrameBundle ℝ F E V).frame, p.property⟩⟩ :=
  (rfl)

/-- The identification of the total space of the reduction with `S` is the identification
`totalSpaceEquiv` of the total space of `Fiber ℝ F E V` with the orthonormal frame bundle. -/
theorem coe_reductionTotalSpaceEquiv_eq (p : TotalSpace H (ReductionFiber S)) :
    (reductionTotalSpaceEquiv H S p : OrthonormalFrameBundle ℝ F E V) =
      totalSpaceEquiv ⟨p.proj, p.snd.val⟩ :=
  (totalSpaceEquiv_apply ⟨p.proj, p.snd.val⟩).symm

/-- The identification of the total space with `S` intertwines the right actions of `H`. -/
@[simp]
theorem reductionTotalSpaceEquiv_smul [SMulMemIff H S] (g : Hᵐᵒᵖ)
    (p : TotalSpace H (ReductionFiber S)) :
    reductionTotalSpaceEquiv H S (g • p) = g • reductionTotalSpaceEquiv H S p :=
  Subtype.ext (SMulMemIff.coe_smul g (reductionTotalSpaceEquiv H S p)).symm

variable [TopologicalSpace (TotalSpace F E)]

/-- The topology on the total space of the reduction induced from the total space of
`Fiber ℝ F E V`. -/
instance instTopologicalSpaceReductionTotalSpace :
    TopologicalSpace (TotalSpace H (ReductionFiber S)) :=
  .induced (fun p ↦ (⟨p.proj, p.snd.val⟩ : TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)))
    inferInstance

variable (H S) in
/-- The total space of the reduction is homeomorphic to `S`. -/
def reductionTotalSpaceHomeomorph : TotalSpace H (ReductionFiber S) ≃ₜ S :=
  (reductionTotalSpaceEquiv H S).toHomeomorphOfIsInducing <|
    (Topology.IsInducing.subtypeVal (t := S)).of_comp_iff.1 <| by
      simpa only [Function.comp_def, coe_reductionTotalSpaceEquiv_eq,
        coe_totalSpaceHomeomorph] using
        totalSpaceHomeomorph.isInducing.comp (Topology.IsInducing.induced
          fun p : TotalSpace H (ReductionFiber S) ↦
            (⟨p.proj, p.snd.val⟩ : TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)))

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
/-- Each fibre of the reduction is embedded in its total space, since each fibre of
`Fiber ℝ F E V` is embedded in its total space. -/
theorem ReductionFiber.isInducing_totalSpaceMk (b : B) :
    Topology.IsInducing (TotalSpace.mk b : ReductionFiber S b → TotalSpace H (ReductionFiber S)) :=
  (Topology.IsInducing.induced _).of_comp_iff.1
    ((Topology.IsInducing.induced _).comp Topology.IsEmbedding.subtypeVal.isInducing :
      Topology.IsInducing fun φ : ReductionFiber S b ↦
        (⟨b, φ.val⟩ : TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)))

end Fiber

section Bundle

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] {H : Subgroup (unitary (V →L[ℝ] V))}
  {S : Set (OrthonormalFrameBundle ℝ F E V)}

variable (hS : IsLocallyTrivialReduction (proj : OrthonormalFrameBundle ℝ F E V → B) H S)

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
      (hS.atlas.trivAt x).compHomeomorphOfEq (reductionTotalSpaceHomeomorph H S)
        (fun _ ↦ by simp) :=
  hS.atlas.trivializationAt_fiberBundleOfHomeomorph _ _ _ x

/-- **A locally trivial reduction of the orthonormal frame bundle is a principal `H`-bundle.** -/
theorem principalBundle_reductionFiber [SMulMemIff H S] :
    letI := reductionFiberBundle hS
    PrincipalBundle H (ReductionFiber S) :=
  hS.atlas.principalBundle_of_homeomorph _ _ _
    (fun x φ g ↦ reductionTotalSpaceEquiv_smul g ⟨x, φ⟩) fun t ht p hp g ↦ by
    rw [IsLocallyTrivialReduction.atlas, MapFiber.Atlas.charts_ofTrivAt] at ht
    obtain ⟨x, rfl⟩ := ht
    dsimp only at hp ⊢
    rw [← hS.atlas_trivAt x] at hp ⊢
    rw [SMulMemIff.smul_eq_mk g p ((SMulMemIff.smul_mem_iff p.property).2 g.property)]
    exact congrArg Prod.snd (hS.atlas_trivAt_mk_smul x g p _ hp)

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
    (op g • φ).val.frame (WithLp.toLp 2 v) =
      φ.val.frame (WithLp.toLp 2 ((euclideanLinearEquivHom ℝ (Fin n)).comp H.subtype g v)) := by
  simp [← Unitary.coe_linearIsometryEquiv_apply]

/-- **A locally trivial reduction of the orthonormal frame bundle modelled on `ℝⁿ` is a lift of
the orthonormal frame bundle** along `H → O(n) → GL(ℝⁿ)`: its principal bundle is the reduction,
and the frame of a point of the reduction is that point itself. -/
@[expose] def reductionLift
    (hS : IsLocallyTrivialReduction
      (proj : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)) → X) H S) :
    OrthonormalFrameLift F E n H ((euclideanLinearEquivHom ℝ (Fin n)).comp H.subtype) where
  P := ReductionFiber S
  fiberBundle := reductionFiberBundle hS
  principal := principalBundle_reductionFiber hS
  toFrame p := ⟨p.proj, p.snd.val.frame⟩
  continuous_toFrame :=
    continuous_coe_reductionTotalSpaceEquiv.congr coe_reductionTotalSpaceEquiv_apply
  proj_toFrame _ := rfl
  toFrame_smul x φ g v := congrArg (TotalSpace.mk' F x) (ReductionFiber.frame_smul_apply φ g v)

variable (hS : IsLocallyTrivialReduction
  (proj : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)) → X) H S)

@[simp]
theorem reductionLift_P : (reductionLift hS).P = ReductionFiber S :=
  (rfl)

/-- The frame of a point of the reduction is that point itself. -/
@[simp]
theorem reductionLift_toFrame (p : TotalSpace H (ReductionFiber S)) :
    (reductionLift hS).toFrame p = ⟨p.proj, p.snd.val.frame⟩ :=
  (rfl)

end Lift

end TauCeti.OrthonormalFrameBundle
