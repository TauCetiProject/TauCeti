/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Homotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Incoming coordinates for mapping-path fibres

`IncomingPathFiber f k` is the space of pairs `(x, γ)` with `γ` a path from `k` to `f x`,
with the raw product/subspace compact-open topology. Path reversal gives
`IncomingPathFiber.outgoingHomeomorph` to the existing `MappingPathFiber f k`.
This is a change of coordinates, not a different homotopy-fibre construction.

The comparison preserves the source projection and constant-path basepoints and is natural
in endpoint-preserving commutative squares. The incoming path supplies a specified homotopy
from the constant map to the composite with `f`. Transporting the existing homotopy comparison
appends the track of the homotopy to the incoming path, rather than prepending its reverse.

For a map from a point, forgetting the source coordinate identifies the incoming fibre with
a native path space. At equal endpoints the coordinate comparison is loop reversal, and
therefore inverts the represented fundamental-group element.

## References

* C. Weibel, *The K-book*, IV.1.2 (homotopy fibres).
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

open unitInterval

universe u v u' v' u'' v''

namespace TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]

/-- Incoming-path coordinates on a mapping-path fibre, with the topology induced from
`B × C(I, K)`. The path starts at the chosen endpoint and ends at the image of the source. -/
abbrev IncomingPathFiber (f : C(B, K)) (k : K) :=
  {p : B × C(I, K) // p.2 0 = k ∧ p.2 1 = f p.1}

namespace IncomingPathFiber

/-- The native path represented by the incoming coordinate. -/
def path {f : C(B, K)} {k : K} (p : IncomingPathFiber f k) : Path k (f p.val.1) :=
  ⟨p.val.2, p.property.1, p.property.2⟩

@[simp]
theorem path_apply {f : C(B, K)} {k : K} (p : IncomingPathFiber f k) (t : I) :
    path p t = p.val.2 t := (rfl)

variable (f : C(B, K)) (k : K)

/-- Reverse the path to recover the supplied outgoing-path fibre. -/
def outgoingHomeomorph : IncomingPathFiber f k ≃ₜ MappingPathFiber f k where
  toFun p := ⟨(p.val.1, p.val.2.comp ⟨σ, continuous_symm⟩), by simpa using p.property.2,
    by simpa using p.property.1⟩
  invFun p := ⟨(p.val.1, p.val.2.comp ⟨σ, continuous_symm⟩), by simpa using p.property.2,
    by simpa using p.property.1⟩
  left_inv p := Subtype.ext (Prod.ext rfl (ContinuousMap.ext fun t ↦ by simp))
  right_inv p := Subtype.ext (Prod.ext rfl (ContinuousMap.ext fun t ↦ by simp))
  continuous_toFun := (continuous_subtype_val.fst.prodMk
    ((ContinuousMap.continuous_precomp _).comp continuous_subtype_val.snd)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.fst.prodMk
    ((ContinuousMap.continuous_precomp _).comp continuous_subtype_val.snd)).subtype_mk _

@[simp]
theorem outgoingHomeomorph_val (p : IncomingPathFiber f k) :
    (outgoingHomeomorph f k p).val = (p.val.1, p.val.2.comp ⟨σ, continuous_symm⟩) := (rfl)

@[simp]
theorem outgoingHomeomorph_symm_val (p : MappingPathFiber f k) :
    ((outgoingHomeomorph f k).symm p).val =
      (p.val.1, p.val.2.comp ⟨σ, continuous_symm⟩) := (rfl)

/-- The source projection in incoming coordinates, transported from the outgoing fibre. -/
def proj : C(IncomingPathFiber f k, B) :=
  (MappingPathFiber.proj f k).comp (outgoingHomeomorph f k)

@[simp]
theorem proj_apply (p : IncomingPathFiber f k) : proj f k p = p.val.1 := by
  simp [proj]

/-- The coordinate comparison lies strictly over the source. -/
@[simp]
theorem proj_comp_outgoingHomeomorph :
    (MappingPathFiber.proj f k).comp (outgoingHomeomorph f k) = proj f k := (rfl)

/-- Constant-path basepoints are unchanged by the coordinate comparison. -/
@[simp]
theorem outgoingHomeomorph_constant (x : B) (hx : f x = k) :
    outgoingHomeomorph f k ⟨(x, ContinuousMap.const I k), rfl, hx.symm⟩ =
      ⟨(x, ContinuousMap.const I k), hx.symm, rfl⟩ := by
  apply Subtype.ext
  rfl

/-- The incoming path is a specified homotopy from the constant map to `f` after projection. -/
def nullHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.const (IncomingPathFiber f k) k)
      (f.comp (proj f k)) where
  toFun q := q.2.val.2 q.1
  continuous_toFun := continuous_snd.subtype_val.snd.eval continuous_fst
  map_zero_left p := p.property.1
  map_one_left p := by simpa using p.property.2

@[simp]
theorem nullHomotopy_apply (s : I) (p : IncomingPathFiber f k) :
    nullHomotopy f k (s, p) = p.val.2 s := (rfl)

/-- In outgoing coordinates the specified incoming homotopy reads the path backwards. -/
theorem nullHomotopy_outgoing (s : I) (p : IncomingPathFiber f k) :
    nullHomotopy f k (s, p) = (outgoingHomeomorph f k p).val.2 (σ s) := by
  simp

variable {f k}
variable {B' : Type u'} {K' : Type v'} [TopologicalSpace B'] [TopologicalSpace K']
variable {f' : C(B', K')} {k' : K'}

/-- Transport the supplied fibre map of an endpoint-preserving commutative square to incoming
coordinates. -/
def map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a) (hk : b k = k') :
    C(IncomingPathFiber f k, IncomingPathFiber f' k') :=
  ((outgoingHomeomorph f' k').symm : C(_, _)).comp
    ((MappingPathFiber.map a b h hk).comp (outgoingHomeomorph f k))

@[simp]
theorem map_val (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') (p : IncomingPathFiber f k) :
    (map a b h hk p).val = (a p.val.1, b.comp p.val.2) := by
  apply Prod.ext
  · simp [map]
  · ext t
    simp [map]

/-- Reversal is natural in endpoint-preserving commutative squares. -/
@[simp]
theorem outgoingHomeomorph_map (a : C(B, B')) (b : C(K, K'))
    (h : b.comp f = f'.comp a) (hk : b k = k') (p : IncomingPathFiber f k) :
    outgoingHomeomorph f' k' (map a b h hk p) =
      MappingPathFiber.map a b h hk (outgoingHomeomorph f k p) :=
  (outgoingHomeomorph f' k').apply_symm_apply _

/-- The source projection is natural in the square. -/
@[simp]
theorem proj_comp_map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') :
    (proj f' k').comp (map a b h hk) = a.comp (proj f k) := by
  ext p
  simp

/-- The specified incoming homotopies are natural, including their time coordinate. -/
theorem nullHomotopy_map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') (s : I) (p : IncomingPathFiber f k) :
    nullHomotopy f' k' (s, map a b h hk p) = b (nullHomotopy f k (s, p)) := by
  simp

@[simp]
theorem map_id : map (f := f) (f' := f) (k := k) (k' := k) (.id B) (.id K) (by simp) rfl =
    ContinuousMap.id (IncomingPathFiber f k) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  simpa only [ContinuousMap.id_apply, ContinuousMap.id_comp] using
    (map_val (f := f) (f' := f) (k := k) (k' := k) (.id B) (.id K) (by simp) rfl p)

variable {B'' : Type u''} {K'' : Type v''} [TopologicalSpace B''] [TopologicalSpace K'']
variable {f'' : C(B'', K'')} {k'' : K''}

/-- Composition of squares agrees with composition of the transported maps. -/
theorem map_comp (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') (a' : C(B', B'')) (b' : C(K', K''))
    (h' : b'.comp f' = f''.comp a') (hk' : b' k' = k'') :
    (map a' b' h' hk').comp (map a b h hk) =
      map (a'.comp a) (b'.comp b) (by
        ext x
        exact (congrArg b' (ContinuousMap.congr_fun h x)).trans
          (ContinuousMap.congr_fun h' (a x))) ((congrArg b' hk).trans hk') := by
  ext p : 1
  apply Subtype.ext
  simp

/-- For a map from a point, incoming coordinates are native paths from the chosen endpoint. -/
def constHomeomorphPath (x k : K) :
    IncomingPathFiber (ContinuousMap.const Unit x) k ≃ₜ Path k x where
  toFun p := ⟨p.val.2, p.property.1, p.property.2⟩
  invFun γ := ⟨((), γ.toContinuousMap), γ.source, γ.target⟩
  left_inv _ := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_induced_dom).subtype_mk _

@[simp]
theorem constHomeomorphPath_apply (x k : K)
    (p : IncomingPathFiber (ContinuousMap.const Unit x) k) (t : I) :
    constHomeomorphPath x k p t = p.val.2 t := (rfl)

@[simp]
theorem constHomeomorphPath_symm_val (x k : K) (γ : Path k x) :
    ((constHomeomorphPath x k).symm γ).val = ((), γ.toContinuousMap) := (rfl)

/-- On point-source fibres the coordinate change reverses the native path, in particular
reversing loops when `x = k`. -/
@[simp]
theorem constHomeomorphPath_outgoingHomeomorph (x k : K)
    (p : IncomingPathFiber (ContinuousMap.const Unit x) k) :
    mappingPathFiberConstHomeomorphPath x k (outgoingHomeomorph _ k p) =
      (constHomeomorphPath x k p).symm := by
  ext t
  simp

/-- The loop represented after coordinate reversal is the inverse fundamental-group element.
Thus the comparison does not silently identify the two orientations of the connecting loop. -/
theorem fundamentalGroup_outgoingHomeomorph (k : K)
    (p : IncomingPathFiber (ContinuousMap.const Unit k) k) :
    FundamentalGroup.fromPath
        ⟦mappingPathFiberConstHomeomorphLoopSpace k (outgoingHomeomorph _ k p)⟧ =
      (FundamentalGroup.fromPath ⟦constHomeomorphPath k k p⟧)⁻¹ := by
  rw [mappingPathFiberConstHomeomorphLoopSpace, constHomeomorphPath_outgoingHomeomorph]
  exact (FundamentalGroup.inv_def
    (p := FundamentalGroup.fromPath ⟦constHomeomorphPath k k p⟧)).symm

end IncomingPathFiber

end TauCeti

namespace ContinuousMap.Homotopy

open TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]
variable {f g : C(B, K)} (H : f.Homotopy g) (k : K)

/-- Transport the supplied homotopy comparison to incoming coordinates, retaining `H`. -/
noncomputable def incomingPathFiberMap : C(IncomingPathFiber f k, IncomingPathFiber g k) :=
  ((IncomingPathFiber.outgoingHomeomorph g k).symm : C(_, _)).comp
    ((H.mappingPathFiberMap k).comp (IncomingPathFiber.outgoingHomeomorph f k))

@[simp]
theorem incomingPathFiberMap_val_fst (p : IncomingPathFiber f k) :
    (incomingPathFiberMap H k p).val.1 = p.val.1 := by
  simp [incomingPathFiberMap]

/-- The transported homotopy comparison commutes with the coordinate homeomorphisms. -/
@[simp]
theorem outgoingHomeomorph_incomingPathFiberMap (p : IncomingPathFiber f k) :
    IncomingPathFiber.outgoingHomeomorph g k (incomingPathFiberMap H k p) =
      H.mappingPathFiberMap k (IncomingPathFiber.outgoingHomeomorph f k p) :=
  (IncomingPathFiber.outgoingHomeomorph g k).apply_symm_apply _

/-- In incoming coordinates the homotopy track is appended to the original path. -/
@[simp]
theorem incomingPathFiberMap_val_snd (p : IncomingPathFiber f k) :
    (incomingPathFiberMap H k p).val.2 =
      ((IncomingPathFiber.path p).trans (H.evalAt p.val.1)).toContinuousMap := by
  -- The supplied outgoing comparison prepends a reversed track; reversal exchanges the factors.
  calc
    _ = (H.mappingPathFiberMap k (IncomingPathFiber.outgoingHomeomorph f k p)).val.2.comp
        ⟨σ, continuous_symm⟩ := rfl
    _ = ((H.evalAt p.val.1).symm.trans (IncomingPathFiber.path p).symm).symm.toContinuousMap := by
      rw [mappingPathFiberMap_val_snd]
      rfl
    _ = _ := by rw [Path.trans_symm, Path.symm_symm, Path.symm_symm]

/-- The transported homotopy comparison preserves the source projection. -/
@[simp]
theorem proj_comp_incomingPathFiberMap :
    (IncomingPathFiber.proj g k).comp (incomingPathFiberMap H k) =
      IncomingPathFiber.proj f k := by
  ext p
  simp

end ContinuousMap.Homotopy
