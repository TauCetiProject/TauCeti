/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.ContinuousLinearEquiv
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Topology.FiberBundle.MapFiber
public import TauCeti.Topology.FiberBundle.Trivial
public import TauCeti.Topology.VectorBundle.Hom
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
`E`, namely those whose fibre component is invertible. These form an open set, since invertibility
is an open condition along the continuous Hom-bundle section `v ↦ v`
(`Continuous.isOpen_setOf_clm_bundle_isInvertible`), and the frame bundle
`TauCeti.FrameBundle 𝕜 n F E` is this open subset, with the topology of an open subset of that
total space. No other topology is put on frames.

The general linear group `GL n 𝕜 = Matrix.GeneralLinearGroup (Fin n) 𝕜` acts on frames on the
right by precomposition, `f • g = f ∘ g`, where the matrix `g` acts on `𝕜ⁿ` by `Matrix.mulVec`.

A linear trivialization `e` of `E` and a continuous linear isomorphism `σ : F ≃ 𝕜ⁿ` give a local
frame of `E` over the base set of `e`, the frame `σ⁻¹` read through `e`
(`Bundle.Trivialization.frameAt`). Reading a frame `f` at `x` in this local frame gives the matrix
of `σ ∘ e_x ∘ f` (`Bundle.Trivialization.matrixIn`), and this trivializes the frame bundle over the
base set of `e` with fibre `GL n 𝕜` (`Bundle.Trivialization.frameBundle`). These trivializations
intertwine the action with right multiplication (`Bundle.Trivialization.frameBundle_smul`). So,
when `F` has dimension `n`, the fibres of the projection of the frame bundle form a principal
`GL n 𝕜`-bundle presented by its total space (`TauCeti.FrameBundle.principalBundle`), through Tau
Ceti's bundles given by their total space (`TauCeti.MapFiber.Atlas`).

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
* `Bundle.Trivialization.matrixIn`: the matrix of a frame in the local frame of a trivialization.
* `Bundle.Trivialization.frameAt`: the local frame of a trivialization.
* `Bundle.Trivialization.frameBundle`: the trivialization of the frame bundle induced by a
  trivialization of `E`.
* `TauCeti.FrameBundle.atlas`: the atlas of these trivializations.

## Main results

* `Bundle.Trivialization.smul_frameAt`: over the base set of a trivialization, a frame is the local
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
open Matrix.GeneralLinearGroup (toContinuousLinearEquiv toContinuousLinearEquiv_apply)
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

/-- The open set of frames of `E` modelled on `𝕜ⁿ`, in the total space of the bundle
`Hom(B × 𝕜ⁿ, E)`: the points whose fibre component is invertible. It is open because
invertibility is an open condition along the continuous Hom-bundle section `v ↦ v`. -/
def frameBundleOpens :
    Opens (TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) :=
  ⟨{v | v.snd.IsInvertible}, Continuous.isOpen_setOf_clm_bundle_isInvertible
    (E₁ := Trivial B (Fin n → 𝕜)) (E₂ := E) (b := TotalSpace.proj)
    (ϕ := fun v : TotalSpace ((Fin n → 𝕜) →L[𝕜] F) (fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) ↦
      v.snd) continuous_id⟩

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
      (toContinuousLinearEquiv g.unop : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜))⟩,
    mem_frameBundleOpens.2 <|
      (ContinuousLinearMap.isInvertible_comp_equiv (e := toContinuousLinearEquiv g.unop)).2
        v.isInvertible⟩
  one_smul v := Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq <|
    ContinuousLinearMap.ext fun w ↦ congrArg v.val.snd <|
      DFunLike.congr_fun (map_one toContinuousLinearEquiv) w
  mul_smul g h v := Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq <|
    ContinuousLinearMap.ext fun w ↦ congrArg v.val.snd <|
      DFunLike.congr_fun (map_mul toContinuousLinearEquiv h.unop g.unop) w

theorem smul_def (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) :
    g • v = mk v.proj ((toContinuousLinearEquiv g.unop).trans v.frameEquiv) :=
  Subtype.ext <| TotalSpace.ext rfl <| heq_of_eq <| ContinuousLinearMap.ext fun _ ↦
    (frameEquiv_apply v _).symm

@[simp]
theorem proj_smul (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) : (g • v).proj = v.proj :=
  (rfl)

@[simp]
theorem smul_apply (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) (w : Fin n → 𝕜) :
    (g • v).val.snd w = v.val.snd ((g.unop : Matrix (Fin n) (Fin n) 𝕜) *ᵥ w) :=
  congrArg v.val.snd (toContinuousLinearEquiv_apply g.unop w)

theorem smul_mk (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) :
    g • (mk x f : FrameBundle 𝕜 n F E) = mk x ((toContinuousLinearEquiv g.unop).trans f) :=
  (rfl)

/-- The isomorphism underlying `v • g` is that of `v` precomposed with `g`. -/
@[simp]
theorem frameEquiv_smul (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) :
    (g • v).frameEquiv = (toContinuousLinearEquiv g.unop).trans v.frameEquiv :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by simp

end FrameBundle

end TauCeti

/-! ### Matrices of frames in local frames -/

namespace Bundle.Trivialization

open TauCeti TauCeti.FrameBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ}
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]

section MatrixIn

variable (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (σ : F ≃L[𝕜] (Fin n → 𝕜))

/-- The matrix of a frame `v` at `x` in the local frame determined by a linear trivialization `e`
of `E` and an isomorphism `σ : F ≃ 𝕜ⁿ`: the matrix of `σ ∘ e_x ∘ v`. -/
def matrixIn (v : FrameBundle 𝕜 n F E) : Matrix (Fin n) (Fin n) 𝕜 :=
  σ.toMatrixCLE (e.continuousLinearMapAt 𝕜 v.proj ∘L v.val.snd)

/-- Over the base set of `e`, the matrix of a frame in the local frame of `e` is invertible. -/
theorem isUnit_matrixIn {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    IsUnit (e.matrixIn σ v) := by
  have h := ContinuousLinearMap.isInvertible_equiv_comp
    (e := (e.continuousLinearEquivAt 𝕜 v.proj hv).trans σ) (f := v.val.snd) |>.2 v.isInvertible
  have hL := ((Module.End.isUnit_iff _).2 h.bijective).map
    (LinearMap.toMatrixAlgEquiv' (R := 𝕜) (n := Fin n))
  rw [matrixIn, σ.toMatrixCLE_apply]
  convert hL using 2
  ext w
  simp [e.coe_continuousLinearEquivAt_eq hv]

theorem matrixIn_mk (x : B) (f : (Fin n → 𝕜) ≃L[𝕜] E x) :
    e.matrixIn σ (FrameBundle.mk x f) =
      σ.toMatrixCLE (e.continuousLinearMapAt 𝕜 x ∘L (f : (Fin n → 𝕜) →L[𝕜] E x)) :=
  (rfl)

/-- The matrix of a frame changes by right multiplication under the action. -/
theorem matrixIn_smul (g : (GL (Fin n) 𝕜)ᵐᵒᵖ) (v : FrameBundle 𝕜 n F E) :
    e.matrixIn σ (g • v) = e.matrixIn σ v * (g.unop : Matrix (Fin n) (Fin n) 𝕜) := by
  rw [smul_def, matrixIn_mk, matrixIn, ← σ.toMatrixCLE_comp_toContinuousLinearEquiv]
  congr 1
  ext w
  simp

open Classical in
/-- The invertible matrix of a frame in the local frame of `e`, over the base set of `e`; it is
`1` elsewhere. -/
def unitIn (v : FrameBundle 𝕜 n F E) : GL (Fin n) 𝕜 :=
  if h : IsUnit (e.matrixIn σ v) then h.unit else 1

theorem coe_unitIn {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    (e.unitIn σ v : Matrix (Fin n) (Fin n) 𝕜) = e.matrixIn σ v := by
  simp only [unitIn, e.isUnit_matrixIn σ hv, ↓reduceDIte, IsUnit.unit_spec]

open Classical in
/-- The local frame of `E` determined by `e` and `σ` at a point `x` of the base set of `e`: the
frame `w ↦ e_x⁻¹ (σ⁻¹ w)`. Outside the base set it is the corresponding frame of the
trivialization of `E` at `x`. -/
def frameAt (x : B) : FrameBundle 𝕜 n F E :=
  if hx : x ∈ e.baseSet then FrameBundle.mk x (σ.symm.trans (e.continuousLinearEquivAt 𝕜 x hx).symm)
  else FrameBundle.mk x (σ.symm.trans ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F E x)).symm)

@[simp]
theorem proj_frameAt (x : B) : (e.frameAt σ x).proj = x := by
  unfold frameAt
  split_ifs <;> rfl

theorem frameAt_of_mem {x : B} (hx : x ∈ e.baseSet) :
    e.frameAt σ x = FrameBundle.mk x (σ.symm.trans (e.continuousLinearEquivAt 𝕜 x hx).symm) := by
  simp only [frameAt, hx, ↓reduceDIte]

/-- The local frame has the identity matrix in its own trivialization. -/
theorem matrixIn_frameAt {x : B} (hx : x ∈ e.baseSet) :
    e.matrixIn σ (e.frameAt σ x) = 1 := by
  rw [e.frameAt_of_mem σ hx, matrixIn_mk, ← σ.toMatrixCLE_symm_self]
  congr 1
  ext w
  simp [e.coe_linearMapAt_of_mem hx, e.apply_mk_symm hx]

/-- A frame over the base set of `e` is the local frame of `e` acted on by its matrix. -/
theorem smul_frameAt {v : FrameBundle 𝕜 n F E} (hv : v.proj ∈ e.baseSet) :
    op (e.unitIn σ v) • e.frameAt σ v.proj = v := by
  conv_rhs => rw [← mk_frameEquiv v]
  rw [e.frameAt_of_mem σ hv, smul_mk, mk_inj, unop_op]
  refine ContinuousLinearEquiv.ext <| funext fun w ↦ ?_
  simp [e.coe_unitIn σ hv, matrixIn, e.symm_linearMapAt hv]

end MatrixIn

/-! ### Comparison with the trivializations of the Hom bundle -/

section HomTrivialization

variable (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (σ : F ≃L[𝕜] (Fin n → 𝕜))

/-- Frames over the base set of `e` lie in the source of the trivialization of the bundle
`Hom(B × 𝕜ⁿ, E)` induced by `e`. -/
theorem mapsTo_coe_source_continuousLinearMap :
    MapsTo (Subtype.val : FrameBundle 𝕜 n F E → _) (proj ⁻¹' e.baseSet)
      ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e).source :=
  fun v hv ↦ by
    simpa [Trivialization.mem_source, Trivialization.baseSet_continuousLinearMap] using hv

/-- Over the base set of `e`, the points with coordinate `w ↦ σ⁻¹ (g *ᵥ w)` lie in the target of
the trivialization of the bundle `Hom(B × 𝕜ⁿ, E)` induced by `e`. -/
theorem mapsTo_toMatrixCLE_symm_target_continuousLinearMap :
    MapsTo (fun p : B × GL (Fin n) 𝕜 ↦ (p.1, σ.toMatrixCLE.symm p.2)) (e.baseSet ×ˢ univ)
      ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e).target :=
  fun p hp ↦ by
    simpa [Trivialization.target_eq, Trivialization.baseSet_continuousLinearMap] using hp.1

/-- The matrix of a frame is read off its coordinate in the trivialization of the bundle
`Hom(B × 𝕜ⁿ, E)` induced by `e`. -/
theorem matrixIn_eq (v : FrameBundle 𝕜 n F E) :
    e.matrixIn σ v = σ.toMatrixCLE
      ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e v.val).2 := by
  rw [Trivialization.continuousLinearMap_apply, Trivial.symmL_trivialization,
    ContinuousLinearMap.comp_id, matrixIn]

/-- Over the base set of `e`, the local frame of `e` acted on by `g` is the point of the bundle
`Hom(B × 𝕜ⁿ, E)` with coordinate `w ↦ σ⁻¹ (g *ᵥ w)` in the trivialization induced by `e`. -/
theorem coe_smul_frameAt {x : B} (hx : x ∈ e.baseSet) (g : GL (Fin n) 𝕜) :
    ((op g • e.frameAt σ x : FrameBundle 𝕜 n F E) :
      TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) =
      ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜)
        e).toPartialEquiv.symm (x, σ.toMatrixCLE.symm g) := by
  -- The inverse of the Hom-bundle trivialization is that of its underlying pretrivialization.
  have h : ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜)
      e).toPartialEquiv.symm (x, σ.toMatrixCLE.symm g) =
      (⟨x, (e.symmL 𝕜 x).comp ((σ.toMatrixCLE.symm g).comp
        ((Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMapAt 𝕜 x))⟩ :
          TotalSpace ((Fin n → 𝕜) →L[𝕜] F) fun x ↦ Trivial B (Fin n → 𝕜) x →L[𝕜] E x) :=
    Pretrivialization.continuousLinearMap_symm_apply _ _ _ _
  rw [h, e.frameAt_of_mem σ hx, smul_mk, unop_op]
  refine congrArg (TotalSpace.mk (F := (Fin n → 𝕜) →L[𝕜] F) x)
    (ContinuousLinearMap.ext fun w ↦ ?_)
  simp [e.symm_continuousLinearEquivAt_eq hx]

/-- The invertible matrix of a frame in the local frame of `e` depends continuously on the frames
over the base set of `e`. -/
theorem continuousOn_unitIn :
    ContinuousOn (e.unitIn σ : FrameBundle 𝕜 n F E → GL (Fin n) 𝕜) (proj ⁻¹' e.baseSet) := by
  rw [Units.isOpenEmbedding_val.isInducing.continuousOn_iff]
  refine (σ.toMatrixCLE.continuous.comp_continuousOn (continuous_snd.comp_continuousOn
    ((Trivialization.continuousOn _).comp continuous_subtypeVal.continuousOn
      e.mapsTo_coe_source_continuousLinearMap))).congr fun v hv ↦ ?_
  simp only [comp_apply, e.coe_unitIn σ hv]
  exact e.matrixIn_eq σ v

/-- The local frame of `e` at `x` acted on by `g` depends continuously on `(x, g)` over the base
set of `e`. -/
theorem continuousOn_smul_frameAt :
    ContinuousOn (fun p : B × GL (Fin n) 𝕜 ↦ (op p.2 • e.frameAt σ p.1 : FrameBundle 𝕜 n F E))
      (e.baseSet ×ˢ univ) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  refine ((Trivialization.toOpenPartialHomeomorph _).continuousOn_symm.comp
    (continuous_fst.prodMk (σ.toMatrixCLE.symm.continuous.comp
      (Units.continuous_val.comp continuous_snd))).continuousOn
    (e.mapsTo_toMatrixCLE_symm_target_continuousLinearMap σ)).congr fun p hp ↦ ?_
  exact e.coe_smul_frameAt σ hp.1 p.2

end HomTrivialization

/-! ### The trivializations of the frame bundle -/

variable (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (σ : F ≃L[𝕜] (Fin n → 𝕜))

/-- **The trivializations of the frame bundle.** A trivialization `e` of `E` and an isomorphism
`σ : F ≃ 𝕜ⁿ` trivialize the frame bundle over the base set of `e` with fibre `GL n 𝕜`: a frame is
sent to its base point and its matrix in the local frame `w ↦ e_x⁻¹ (σ⁻¹ w)`, and `(x, g)` is sent
back to that local frame at `x` acted on by `g`. -/
def frameBundle : Trivialization (GL (Fin n) 𝕜) (proj : FrameBundle 𝕜 n F E → B) where
  toFun v := (v.proj, e.unitIn σ v)
  invFun p := op p.2 • e.frameAt σ p.1
  source := proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hv := ⟨hv, trivial⟩
  map_target' p hp := by simpa using hp.1
  left_inv' _ hv := e.smul_frameAt σ hv
  right_inv' p hp := by
    have hx : (op p.2 • e.frameAt σ p.1 : FrameBundle 𝕜 n F E).proj ∈ e.baseSet := by
      simpa using hp.1
    refine Prod.ext (by simp) (Units.ext ?_)
    rw [e.coe_unitIn σ hx, matrixIn_smul, e.matrixIn_frameAt σ hp.1, one_mul, unop_op]
  open_source := e.open_baseSet.preimage continuous_proj
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := continuous_proj.continuousOn.prodMk (e.continuousOn_unitIn σ)
  continuousOn_invFun := e.continuousOn_smul_frameAt σ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem frameBundle_apply (v : FrameBundle 𝕜 n F E) :
    e.frameBundle σ v = (v.proj, e.unitIn σ v) :=
  (rfl)

@[simp]
theorem frameBundle_symm_apply (x : B) (g : GL (Fin n) 𝕜) :
    (e.frameBundle σ).toOpenPartialHomeomorph.symm (x, g) = op g • e.frameAt σ x :=
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
  rw [frameBundle_apply, frameBundle_apply, Units.val_mul, e.coe_unitIn σ hv,
    e.coe_unitIn σ (by simpa using hv), matrixIn_smul, unop_op]

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
