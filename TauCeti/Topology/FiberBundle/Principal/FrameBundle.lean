/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.ContinuousLinearEquiv
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Topology.FiberBundle.MapFiber
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The general linear frame bundle of a vector bundle

Let `E → B` be a topological vector bundle over a complete nontrivially normed field `𝕜` with
model fibre `F`. A **frame** of `E` at `x : B` modelled on `𝕜ⁿ` is a continuous linear
isomorphism `𝕜ⁿ ≃ E x`, that is, an ordered basis of `E x`. Frames are points of the total space of
the bundle `Hom(B × 𝕜ⁿ, E)` of continuous linear maps from the trivial bundle with fibre `𝕜ⁿ` to
`E`, namely those whose fibre component is invertible. These form an open set
(`TauCeti.isOpen_setOf_isInvertible`), and the frame bundle `TauCeti.FrameBundle 𝕜 n F E` is this
open subset, with the topology of an open subset of that total space. No other topology is put on
frames.

The general linear group `GL n 𝕜 = Matrix.GeneralLinearGroup (Fin n) 𝕜` acts on frames on the
right by precomposition, `f • g = f ∘ g`, where the matrix `g` acts on `𝕜ⁿ` by `Matrix.mulVec`.

A linear trivialization `e` of `E` and a continuous linear isomorphism `σ : F ≃ 𝕜ⁿ` give a local
frame of `E` over the base set of `e`, the frame `σ⁻¹` read through `e`. Reading a frame `f` at
`x` in this local frame gives the matrix of `σ ∘ e_x ∘ f` (`TauCeti.FrameBundle.matrixIn`), and
this trivializes the frame bundle over the base set of `e` with fibre `GL n 𝕜`
(`Bundle.Trivialization.frameBundle`). These trivializations intertwine the action with right
multiplication (`Bundle.Trivialization.frameBundle_smul`). So, when `F` has dimension `n`, the
fibres of the projection of the frame bundle form a principal `GL n 𝕜`-bundle presented by its
total space (`TauCeti.FrameBundle.principalBundle`), through Tau Ceti's bundles given by their
total space (`TauCeti.MapFiber.Atlas`).

The matrix algebra carries the `L∞` operator norm (`Matrix.linftyOpNormedRing`) and its topology
`Matrix.linftyOpTopologicalSpace`, which is the entrywise topology by definition
(`Matrix.linftyOpTopologicalSpace_eq`). This is the topology of the native Lie group structure of
the units of a complete normed algebra, used in the smooth theory of this bundle.

## Main definitions

* `TauCeti.FrameBundle 𝕜 n F E`: the frames of `E` modelled on `𝕜ⁿ`, an open subset of the total
  space of `Hom(B × 𝕜ⁿ, E)`.
* `TauCeti.FrameBundle.proj`: the base point of a frame.
* `TauCeti.FrameBundle.mk`: the frame given by an isomorphism `𝕜ⁿ ≃ E x`.
* `TauCeti.FrameBundle.frameEquiv`: the isomorphism `𝕜ⁿ ≃ E x` underlying a frame.
* `TauCeti.FrameBundle.matrixIn`: the matrix of a frame in the local frame of a trivialization.
* `TauCeti.FrameBundle.localFrame`: the local frame of a trivialization.
* `Bundle.Trivialization.frameBundle`: the trivialization of the frame bundle induced by a
  trivialization of `E`.
* `TauCeti.FrameBundle.atlas`: the atlas of these trivializations.

## Main results

* `TauCeti.isOpen_setOf_isInvertible`: invertible points of the Hom bundle form an open set.
* `TauCeti.FrameBundle.smul_localFrame`: over the base set of a trivialization, a frame is the local
  frame acted on by its matrix.
* `Bundle.Trivialization.frameBundle_smul`: the trivializations are equivariant.
* `TauCeti.FrameBundle.principalBundle`: the frame bundle is a principal `GL n 𝕜`-bundle.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Ch. I, §5, Example 5.2 (the bundle of linear frames).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.11 (the frame bundle of a vector bundle).
-/

public section

noncomputable section

open Bundle Set Function MulOpposite TopologicalSpace
open scoped Matrix Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (n : ℕ)
  {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]

omit [CompleteSpace 𝕜] in
/-- Read in a linear trivialization `e` of `E` over its base set, a point `v` of the bundle
`Hom(B × 𝕜ⁿ, E)` is `e_x ∘ v`. -/
private theorem snd_continuousLinearMap_trivialization {e : Trivialization F (π F E)}
    [MemTrivializationAtlas e]
    {v : TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x}
    (hv : v.proj ∈ e.baseSet) :
    haveI : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
    ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e v).2 =
      (e.continuousLinearEquivAt 𝕜 v.proj hv : E v.proj →L[𝕜] F) ∘L v.snd := by
  ext w
  rw [Trivialization.continuousLinearMap_apply]
  simp [e.coe_continuousLinearEquivAt_eq hv]

/-- **Frames form an open set.** The points of the bundle `Hom(B × 𝕜ⁿ, E)` whose fibre component
is an isomorphism `𝕜ⁿ ≃ E x` form an open subset of its total space: read in a trivialization of
`E` they are the points whose coordinate is an isomorphism `𝕜ⁿ ≃ F`, and these form an open set of
`𝕜ⁿ →L[𝕜] F`. -/
theorem isOpen_setOf_isInvertible :
    IsOpen {v : TotalSpace ((Fin n → 𝕜) →L[𝕜] F) (fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) |
      v.snd.IsInvertible} := by
  refine isOpen_iff_forall_mem_open.2 fun v _ ↦ ?_
  have : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
  let e := trivializationAt F E v.proj
  let eH := (Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e
  have hsource : eH.source = TotalSpace.proj ⁻¹' e.baseSet := by
    simp [eH, eH.source_eq, Trivialization.baseSet_continuousLinearMap]
  have hiff : ∀ w, w ∈ eH.source → (w.snd.IsInvertible ↔ (eH w).2.IsInvertible) := by
    intro w hw
    rw [hsource] at hw
    rw [snd_continuousLinearMap_trivialization 𝕜 n F E hw,
      ContinuousLinearMap.isInvertible_equiv_comp]
  refine ⟨eH.source ∩ eH ⁻¹' (univ ×ˢ {f | f.IsInvertible}), fun w hw ↦ (hiff w hw.1).2 hw.2.2,
    eH.continuousOn.isOpen_inter_preimage eH.open_source
      (isOpen_univ.prod ContinuousLinearMap.isOpen_setOfPred_isInvertible), ?_, ?_⟩
  · rw [hsource]
    exact mem_baseSet_trivializationAt F E v.proj
  · exact ⟨trivial, (hiff v (hsource ▸ mem_baseSet_trivializationAt F E v.proj)).1 ‹_›⟩

/-- The open set of frames of `E` modelled on `𝕜ⁿ`, in the total space of the bundle
`Hom(B × 𝕜ⁿ, E)`. -/
def frameBundleOpens :
    Opens (TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) :=
  ⟨{v | v.snd.IsInvertible}, isOpen_setOf_isInvertible 𝕜 n F E⟩

/-- **The frame bundle.** A frame of `E` at `x : B` modelled on `𝕜ⁿ` is a continuous linear
isomorphism `𝕜ⁿ ≃ E x`. The frames of `E` are the invertible points of the bundle
`Hom(B × 𝕜ⁿ, E)`, an open subset of its total space, whose topology they carry. -/
abbrev FrameBundle : Type _ := frameBundleOpens 𝕜 n F E

variable {𝕜 n F E} in
@[simp]
theorem mem_frameBundleOpens
    {v : TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x} :
    v ∈ frameBundleOpens 𝕜 n F E ↔ v.snd.IsInvertible :=
  Iff.rfl

namespace FrameBundle

variable {𝕜 n F E}

/-- The base point of a frame. -/
abbrev proj (v : FrameBundle 𝕜 n F E) : B := v.val.proj

theorem continuous_proj : Continuous (proj : FrameBundle 𝕜 n F E → B) :=
  (FiberBundle.continuous_proj _ _).comp continuous_subtypeVal

/-- A frame is a continuous linear isomorphism. -/
theorem isInvertible (v : FrameBundle 𝕜 n F E) : v.val.snd.IsInvertible :=
  v.property

/-- The frame given by a continuous linear isomorphism `𝕜ⁿ ≃ E x`. -/
@[expose] def mk (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) : FrameBundle 𝕜 n F E :=
  ⟨⟨x, (f : (Fin n → 𝕜) →L[𝕜] E x)⟩, mem_frameBundleOpens.2 ContinuousLinearMap.isInvertible_equiv⟩

@[simp]
theorem proj_mk (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) : (mk x f : FrameBundle 𝕜 n F E).proj = x :=
  (rfl)

@[simp]
theorem mk_apply (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) (w : Fin n → 𝕜) :
    (mk x f : FrameBundle 𝕜 n F E).val.snd w = f w :=
  (rfl)

/-- The isomorphism `𝕜ⁿ ≃ E x` underlying a frame at `x`. -/
def frameEquiv (v : FrameBundle 𝕜 n F E) : (Fin n → 𝕜) ≃L[𝕜] E v.proj :=
  v.isInvertible.choose

@[simp]
theorem coe_frameEquiv (v : FrameBundle 𝕜 n F E) :
    (v.frameEquiv : (Fin n → 𝕜) →L[𝕜] E v.proj) = v.val.snd :=
  v.isInvertible.choose_spec

@[simp]
theorem frameEquiv_apply (v : FrameBundle 𝕜 n F E) (w : Fin n → 𝕜) : v.frameEquiv w = v.val.snd w :=
  congrArg (· w) v.coe_frameEquiv

@[simp]
theorem mk_frameEquiv (v : FrameBundle 𝕜 n F E) : mk v.proj v.frameEquiv = v :=
  Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq v.coe_frameEquiv

@[simp]
theorem frameEquiv_mk (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) :
    (mk x f : FrameBundle 𝕜 n F E).frameEquiv = f :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ frameEquiv_apply (mk x f) w

theorem mk_injective (x : B) :
    Injective fun f : (Fin n → 𝕜) ≃L[𝕜] E x ↦ (mk x f : FrameBundle 𝕜 n F E) :=
  fun f f' h ↦ by
    have h' : (⟨x, f⟩ : TotalSpace ((Fin n → 𝕜) →L[𝕜] F)
        fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) = ⟨x, f'⟩ := congrArg Subtype.val h
    exact ContinuousLinearEquiv.coe_injective (eq_of_heq (TotalSpace.mk.inj h').2)

@[simp]
theorem mk_inj {x : B} {f f' : (Fin n → 𝕜) ≃L[𝕜] E x} :
    (mk x f : FrameBundle 𝕜 n F E) = mk x f' ↔ f = f' :=
  (mk_injective x).eq_iff

/-! ### The action of the general linear group -/

/-- The general linear group acts on frames on the right, by precomposition: `f • g = f ∘ g`. -/
instance : MulAction (GL (Fin n) 𝕜)ᵐᵒᵖ (FrameBundle 𝕜 n F E) where
  smul g v := ⟨⟨v.val.proj, v.val.snd ∘L
      (g.unop.toContinuousLinearEquiv : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜))⟩,
    mem_frameBundleOpens.2 <|
      (ContinuousLinearMap.isInvertible_comp_equiv (e := g.unop.toContinuousLinearEquiv)).2
        v.isInvertible⟩
  one_smul v := Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq <|
    ContinuousLinearMap.ext fun w ↦ congrArg v.val.snd (Matrix.one_mulVec w)
  mul_smul _ _ v := Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq <|
    ContinuousLinearMap.ext fun w ↦ (congrArg v.val.snd (Matrix.mulVec_mulVec w _ _)).symm

theorem smul_def (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) :
    g • v = mk v.proj (g.unop.toContinuousLinearEquiv.trans v.frameEquiv) :=
  Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq <| ContinuousLinearMap.ext fun _ ↦
    (frameEquiv_apply v _).symm

@[simp]
theorem proj_smul (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) : (g • v).proj = v.proj :=
  (rfl)

@[simp]
theorem smul_apply (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) (w : Fin n → 𝕜) :
    (g • v).val.snd w = v.val.snd ((g.unop : Matrix (Fin n) (Fin n) 𝕜) *ᵥ w) :=
  (rfl)

theorem smul_mk (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) :
    g • (mk x f : FrameBundle 𝕜 n F E) = mk x (g.unop.toContinuousLinearEquiv.trans f) :=
  (rfl)

/-! ### Matrices of frames in local frames -/

/-- For `σ : F ≃ 𝕜ⁿ`, the matrix of `σ ∘ φ`, for `φ : 𝕜ⁿ →L[𝕜] F`, as a continuous linear
isomorphism. Its inverse sends a matrix `M` to `w ↦ σ⁻¹ (M *ᵥ w)`. -/
def matrixEquiv (σ : F ≃L[𝕜] (Fin n → 𝕜)) :
    ((Fin n → 𝕜) →L[𝕜] F) ≃L[𝕜] Matrix (Fin n) (Fin n) 𝕜 :=
  ((ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)).arrowCongr σ).trans
    (LinearMap.toContinuousLinearMap.symm.trans LinearMap.toMatrix').toContinuousLinearEquiv

theorem matrixEquiv_apply (σ : F ≃L[𝕜] (Fin n → 𝕜)) (φ : (Fin n → 𝕜) →L[𝕜] F) :
    matrixEquiv σ φ = LinearMap.toMatrix' ((σ : F →L[𝕜] (Fin n → 𝕜)) ∘L φ) :=
  (rfl)

@[simp]
theorem matrixEquiv_symm_apply (σ : F ≃L[𝕜] (Fin n → 𝕜)) (M : Matrix (Fin n) (Fin n) 𝕜)
    (w : Fin n → 𝕜) : (matrixEquiv σ).symm M w = σ.symm (M *ᵥ w) := by
  simp [matrixEquiv, ContinuousLinearEquiv.arrowCongr_symm, Matrix.toLin'_apply]

variable (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (σ : F ≃L[𝕜] (Fin n → 𝕜))

/-- The matrix of a frame `v` at `x` in the local frame determined by a linear trivialization `e`
of `E` and an isomorphism `σ : F ≃ 𝕜ⁿ`: the matrix of `σ ∘ e_x ∘ v`. -/
def matrixIn (v : FrameBundle 𝕜 n F E) : Matrix (Fin n) (Fin n) 𝕜 :=
  matrixEquiv σ (e.continuousLinearMapAt 𝕜 v.proj ∘L v.val.snd)

/-- Over the base set of `e`, the matrix of a frame in the local frame of `e` is invertible. -/
theorem isUnit_matrixIn {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    IsUnit (matrixIn e σ v) := by
  have h := ContinuousLinearMap.isInvertible_equiv_comp
    (e := (e.continuousLinearEquivAt 𝕜 v.proj hv).trans σ) (f := v.val.snd) |>.2 v.isInvertible
  have hL := ((Module.End.isUnit_iff _).2 h.bijective).map
    (LinearMap.toMatrixAlgEquiv' (R := 𝕜) (n := Fin n))
  rw [matrixIn, matrixEquiv_apply]
  convert hL using 2
  ext w
  simp [e.coe_continuousLinearEquivAt_eq hv]

/-- The matrix of a frame changes by right multiplication under the action. -/
theorem matrixIn_smul (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) :
    matrixIn e σ (g • v) = matrixIn e σ v * (g.unop : Matrix (Fin n) (Fin n) 𝕜) := by
  rw [matrixIn, matrixIn, matrixEquiv_apply, matrixEquiv_apply, ← LinearMap.toMatrix'_toLin'
    (g.unop : Matrix (Fin n) (Fin n) 𝕜), ← LinearMap.toMatrix'_comp]
  congr 1

open Classical in
/-- The invertible matrix of a frame in the local frame of `e`, over the base set of `e`; it is
`1` elsewhere. -/
def unitIn (v : FrameBundle 𝕜 n F E) : GL (Fin n) 𝕜 :=
  if h : IsUnit (matrixIn e σ v) then h.unit else 1

theorem coe_unitIn {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    (unitIn e σ v : Matrix (Fin n) (Fin n) 𝕜) = matrixIn e σ v := by
  simp only [unitIn, isUnit_matrixIn e σ hv, ↓reduceDIte, IsUnit.unit_spec]

open Classical in
/-- The local frame of `E` determined by `e` and `σ` at a point `x` of the base set of `e`: the
frame `w ↦ e_x⁻¹ (σ⁻¹ w)`. Outside the base set it is the corresponding frame of the
trivialization of `E` at `x`. -/
def localFrame (x : B) : FrameBundle 𝕜 n F E :=
  if hx : x ∈ e.baseSet then mk x (σ.symm.trans (e.continuousLinearEquivAt 𝕜 x hx).symm)
  else mk x (σ.symm.trans ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F E x)).symm)

@[simp]
theorem proj_localFrame (x : B) : (localFrame e σ x).proj = x := by
  unfold localFrame
  split_ifs <;> rfl

theorem localFrame_of_mem {x : B} (hx : x ∈ e.baseSet) :
    localFrame e σ x = mk x (σ.symm.trans (e.continuousLinearEquivAt 𝕜 x hx).symm) := by
  simp only [localFrame, hx, ↓reduceDIte]

theorem matrixIn_mk (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) :
    matrixIn e σ (mk x f) =
      matrixEquiv σ (e.continuousLinearMapAt 𝕜 x ∘L (f : (Fin n → 𝕜) →L[𝕜] E x)) :=
  (rfl)

/-- The local frame has the identity matrix in its own trivialization. -/
theorem matrixIn_localFrame {x : B} (hx : x ∈ e.baseSet) :
    matrixIn e σ (localFrame e σ x) = 1 := by
  rw [localFrame_of_mem e σ hx, matrixIn_mk, matrixEquiv_apply, ← LinearMap.toMatrix'_id]
  congr 1
  ext w i
  simp [e.coe_linearMapAt_of_mem hx, e.apply_mk_symm hx]

/-- A frame over the base set of `e` is the local frame of `e` acted on by its matrix. -/
theorem smul_localFrame {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    op (unitIn e σ v) • localFrame e σ v.proj = v := by
  conv_rhs => rw [← mk_frameEquiv v]
  rw [localFrame_of_mem e σ hv, smul_mk, mk_inj, unop_op]
  refine ContinuousLinearEquiv.ext <| funext fun w ↦ ?_
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    Matrix.GeneralLinearGroup.toContinuousLinearEquiv_apply, coe_unitIn e σ hv, matrixIn,
    matrixEquiv_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    e.symm_continuousLinearEquivAt_eq hv, frameEquiv_apply]
  exact e.symmL_continuousLinearMapAt (R := 𝕜) hv _

/-! ### Comparison with the trivializations of the Hom bundle -/

section HomTrivialization

variable [MemTrivializationAtlas e]

/-- Over the base set of `e`, the matrix of a frame is read off its coordinate in the
trivialization of the bundle `Hom(B × 𝕜ⁿ, E)` induced by `e`. -/
theorem matrixIn_eq {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    haveI : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
    matrixIn e σ v = matrixEquiv σ
      ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e v.val).2 := by
  rw [snd_continuousLinearMap_trivialization 𝕜 n F E hv, e.coe_continuousLinearEquivAt_eq' hv]
  rfl

/-- Over the base set of `e`, the local frame of `e` acted on by `g` is the point of the bundle
`Hom(B × 𝕜ⁿ, E)` with coordinate `w ↦ σ⁻¹ (g *ᵥ w)` in the trivialization induced by `e`. -/
theorem coe_smul_localFrame {x : B} (hx : x ∈ e.baseSet) (g : GL (Fin n) 𝕜) :
    haveI : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
    ((op g • localFrame e σ x : FrameBundle 𝕜 n F E) :
        TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) =
      ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜)
        e).toPartialEquiv.symm (x, (matrixEquiv σ).symm g) := by
  have : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
  have h : ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜)
      e).toPartialEquiv.symm (x, (matrixEquiv σ).symm g) =
        (⟨x, (e.symmL 𝕜 x).comp (((matrixEquiv σ).symm g).comp
          ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMapAt 𝕜 x))⟩ :
          TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) :=
    rfl
  rw [h, localFrame_of_mem e σ hx, smul_mk, unop_op]
  refine congrArg (TotalSpace.mk (F := (Fin n → 𝕜) →L[𝕜] F) x)
    (ContinuousLinearMap.ext fun w ↦ ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, matrixEquiv_symm_apply,
    ← e.symm_continuousLinearEquivAt_eq' hx, Bundle.Trivial.continuousLinearMapAt_trivialization]
  rfl

/-- The invertible matrix of a frame in the local frame of `e` depends continuously on the frames
over the base set of `e`. -/
theorem continuousOn_unitIn :
    ContinuousOn (unitIn e σ : FrameBundle 𝕜 n F E → GL (Fin n) 𝕜) (proj ⁻¹' e.baseSet) := by
  have : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
  let eH := (Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e
  rw [Units.isOpenEmbedding_val.isInducing.continuousOn_iff]
  have hmaps : MapsTo (Subtype.val : FrameBundle 𝕜 n F E → _) (proj ⁻¹' e.baseSet) eH.source :=
    fun v hv ↦ by simpa [eH, eH.mem_source, Trivialization.baseSet_continuousLinearMap] using hv
  refine ((matrixEquiv σ).continuous.comp_continuousOn (continuous_snd.comp_continuousOn
    (eH.continuousOn.comp continuous_subtypeVal.continuousOn hmaps))).congr fun v hv ↦ ?_
  simp only [comp_apply, coe_unitIn e σ hv]
  exact matrixIn_eq e σ hv

/-- The local frame of `e` at `x` acted on by `g` depends continuously on `(x, g)` over the base
set of `e`. -/
theorem continuousOn_smul_localFrame :
    ContinuousOn (fun p : B × GL (Fin n) 𝕜 ↦ (op p.2 • localFrame e σ p.1 : FrameBundle 𝕜 n F E))
      (e.baseSet ×ˢ univ) := by
  have : MemTrivializationAtlas (Trivial.trivialization B (Fin n → 𝕜)) := ⟨mem_singleton _⟩
  let eH := (Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hmaps : MapsTo (fun p : B × GL (Fin n) 𝕜 ↦ (p.1, (matrixEquiv σ).symm p.2))
      (e.baseSet ×ˢ univ) eH.target := fun p hp ↦ by
    simpa [eH, eH.target_eq, Trivialization.baseSet_continuousLinearMap] using hp.1
  refine (eH.toOpenPartialHomeomorph.continuousOn_symm.comp (continuous_fst.prodMk
    ((matrixEquiv σ).symm.continuous.comp
      (Units.continuous_val.comp continuous_snd))).continuousOn hmaps).congr fun p hp ↦ ?_
  exact coe_smul_localFrame e σ hp.1 p.2

end HomTrivialization

end FrameBundle

end TauCeti

/-! ### The trivializations of the frame bundle -/

namespace Bundle.Trivialization

open TauCeti TauCeti.FrameBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ}
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (σ : F ≃L[𝕜] (Fin n → 𝕜))

/-- **The trivializations of the frame bundle.** A trivialization `e` of `E` and an isomorphism
`σ : F ≃ 𝕜ⁿ` trivialize the frame bundle over the base set of `e` with fibre `GL n 𝕜`: a frame is
sent to its base point and its matrix in the local frame `w ↦ e_x⁻¹ (σ⁻¹ w)`, and `(x, g)` is sent
back to that local frame at `x` acted on by `g`. -/
def frameBundle : Trivialization (GL (Fin n) 𝕜) (proj : FrameBundle 𝕜 n F E → B) where
  toFun v := (v.proj, unitIn e σ v)
  invFun p := op p.2 • localFrame e σ p.1
  source := proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hv := ⟨hv, trivial⟩
  map_target' p hp := by simpa using hp.1
  left_inv' _ hv := smul_localFrame e σ hv
  right_inv' p hp := by
    have hx : (op p.2 • localFrame e σ p.1 : FrameBundle 𝕜 n F E).proj ∈ e.baseSet := by
      simpa using hp.1
    refine Prod.ext (by simp) (Units.ext ?_)
    rw [coe_unitIn e σ hx, matrixIn_smul, matrixIn_localFrame e σ hp.1, one_mul, unop_op]
  open_source := e.open_baseSet.preimage continuous_proj
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := continuous_proj.continuousOn.prodMk (continuousOn_unitIn e σ)
  continuousOn_invFun := continuousOn_smul_localFrame e σ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem frameBundle_apply (v : FrameBundle 𝕜 n F E) : e.frameBundle σ v = (v.proj, unitIn e σ v) :=
  (rfl)

@[simp]
theorem frameBundle_symm_apply (x : B) (g : GL (Fin n) 𝕜) :
    (e.frameBundle σ).toOpenPartialHomeomorph.symm (x, g) = op g • localFrame e σ x :=
  (rfl)

@[simp]
theorem baseSet_frameBundle : (e.frameBundle σ : Trivialization (GL (Fin n) 𝕜)
    (proj : FrameBundle 𝕜 n F E → B)).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem source_frameBundle : (e.frameBundle σ : Trivialization (GL (Fin n) 𝕜)
    (proj : FrameBundle 𝕜 n F E → B)).source = proj ⁻¹' e.baseSet :=
  (rfl)

@[simp]
theorem target_frameBundle : (e.frameBundle σ : Trivialization (GL (Fin n) 𝕜)
    (proj : FrameBundle 𝕜 n F E → B)).target = e.baseSet ×ˢ univ :=
  (rfl)

/-- The trivializations of the frame bundle intertwine the action with right multiplication. -/
theorem frameBundle_smul {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet)
    (g : GL (Fin n) 𝕜) : (e.frameBundle σ (op g • v)).2 = (e.frameBundle σ v).2 * g := by
  refine Units.ext ?_
  rw [frameBundle_apply, frameBundle_apply, Units.val_mul, coe_unitIn e σ hv,
    coe_unitIn e σ (by simpa using hv), matrixIn_smul, unop_op]

end Bundle.Trivialization

/-! ### The frame bundle is a principal bundle -/

namespace TauCeti.FrameBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ}
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]

variable (E) in
/-- The atlas of the frame bundle consisting of the trivializations induced by the trivializations
of `E` at each point and an isomorphism `σ : F ≃ 𝕜ⁿ`. -/
def atlas (σ : F ≃L[𝕜] (Fin n → 𝕜)) :
    MapFiber.Atlas (GL (Fin n) 𝕜) (proj : FrameBundle 𝕜 n F E → B) where
  trivAt b := (trivializationAt F E b).frameBundle σ
  mem_baseSet_trivAt b := mem_baseSet_trivializationAt F E b

@[simp]
theorem atlas_trivAt (σ : F ≃L[𝕜] (Fin n → 𝕜)) (b : B) :
    (atlas E σ).trivAt b = (trivializationAt F E b).frameBundle σ :=
  (rfl)

variable (E) in
/-- **The frame bundle is a principal bundle.** For an isomorphism `σ : F ≃ 𝕜ⁿ`, the fibres of the
projection of the frame bundle, with the trivializations induced by those of `E`, form a principal
`GL n 𝕜`-bundle for the action by precomposition. -/
theorem principalBundle (σ : F ≃L[𝕜] (Fin n → 𝕜)) :
    letI := (atlas E σ).fiberBundle
    letI := MapFiber.mulAction (M := (GL (Fin n) 𝕜)ᵐᵒᵖ) (proj_smul (F := F) (E := E))
    PrincipalBundle (GL (Fin n) 𝕜) (MapFiber (proj : FrameBundle 𝕜 n F E → B)) :=
  (atlas E σ).principalBundle proj_smul fun b _ hv g ↦
    (trivializationAt F E b).frameBundle_smul σ hv g

end TauCeti.FrameBundle
