/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Subbundle

/-!
# Local frames of quotients of vector bundles by subbundles

Let `E` be a family of modules over a base `B`, and let `V` assign to every point `x` a subspace
`V x` of the fibre `E x`. A local frame of the quotient `E ⧸ V` on a set `U`
(`TauCeti.IsQuotientFrameOn V Y U`) is a family of sections `Y j` of `E` whose classes modulo `V`
form a basis of every fibre `E x ⧸ V x`, `x ∈ U`. When `X` is a local frame of `V` on `U`, this
holds exactly when `X` and `Y` together form a frame of `E`
(`TauCeti.IsSubbundleFrameOn.isQuotientFrameOn_iff`). A frame `Y` of `E ⧸ V` on an open set gives
the pretrivialization `TauCeti.IsQuotientFrameOn.pretrivialization`, sending a class to its
coordinates in the frame.

These frames are the local trivializations of the quotient bundle `E ⧸ V` of a `C^n` vector bundle
by a `C^n` subbundle, constructed in `TauCeti.Geometry.Manifold.VectorBundle.Quotient`.

## Main definitions

* `TauCeti.IsQuotientFrameOn V Y U`: the classes of the sections `Y j` form a basis of
  `E x ⧸ V x` at every point `x` of `U`.
* `TauCeti.IsQuotientFrameOn.pretrivialization`: the pretrivialization of `E ⧸ V` given by a local
  frame on an open set.

## Main results

* `TauCeti.IsSubbundleFrameOn.isQuotientFrameOn_iff`: completions of a frame of `V` to a frame of
  `E` are exactly the frames of `E ⧸ V`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (local frame criteria for vector bundles and subbundles).
-/

public section

noncomputable section

open Set Function Module Bundle

namespace TauCeti

section Frame

variable {𝕜 : Type*} [Ring 𝕜] {B : Type*} {E : B → Type*} [∀ x, AddCommGroup (E x)]
  [∀ x, Module 𝕜 (E x)] {κ : Type*}

/-- The sections `Y j` of `E` form a local frame of the quotient of `E` by the family of subspaces
`V` on the set `U`: at every point `x` of `U` the classes of the vectors `Y j x` modulo `V x` form
a basis of `E x ⧸ V x`. No regularity is required of the sections. -/
structure IsQuotientFrameOn (V : Π x, Submodule 𝕜 (E x)) (Y : κ → Π x, E x) (U : Set B) :
    Prop where
  /-- The classes of the frame at a point of `U` are linearly independent. -/
  linearIndependent {x : B} (hx : x ∈ U) :
    LinearIndependent 𝕜 fun j ↦ (Submodule.Quotient.mk (Y j x) : E x ⧸ V x)
  /-- The classes of the frame at a point of `U` span the quotient there. -/
  span_eq {x : B} (hx : x ∈ U) :
    Submodule.span 𝕜 (range fun j ↦ (Submodule.Quotient.mk (Y j x) : E x ⧸ V x)) = ⊤

namespace IsQuotientFrameOn

variable {V : Π x, Submodule 𝕜 (E x)} {Y : κ → Π x, E x} {U U' : Set B}

/-- A local frame of `E ⧸ V` on `U` is a local frame of `E ⧸ V` on every subset of `U`. -/
theorem mono (hY : IsQuotientFrameOn V Y U) (hU : U' ⊆ U) : IsQuotientFrameOn V Y U' where
  linearIndependent hx := hY.linearIndependent (hU hx)
  span_eq hx := hY.span_eq (hU hx)

/-- At a point `y` of `U`, a local frame of `E ⧸ V` on `U` gives a basis of `E y ⧸ V y`. -/
def basis (hY : IsQuotientFrameOn V Y U) {y : B} (hy : y ∈ U) : Basis κ 𝕜 (E y ⧸ V y) :=
  Basis.mk (hY.linearIndependent hy) (hY.span_eq hy).ge

@[simp]
theorem basis_apply (hY : IsQuotientFrameOn V Y U) {y : B} (hy : y ∈ U) (j : κ) :
    hY.basis hy j = Submodule.Quotient.mk (Y j y) :=
  Basis.mk_apply ..

/-- At a point `y` of `U`, the class with coordinates `c` in the frame `Y` is the class of the
combination `∑ j, c j • Y j y`. -/
theorem basis_equivFun_symm [Fintype κ] (hY : IsQuotientFrameOn V Y U) {y : B} (hy : y ∈ U)
    (c : κ → 𝕜) :
    (hY.basis hy).equivFun.symm c = Submodule.Quotient.mk (∑ j, c j • Y j y) := by
  simp only [Basis.equivFun_symm_apply, basis_apply, ← Submodule.mkQ_apply, map_sum, map_smul]

section Coordinates

variable [Finite κ] (hY : IsQuotientFrameOn V Y U)

open scoped Classical in
/-- The coordinates of a class of `E y ⧸ V y` in the frame `Y`, extended by zero off `U`. -/
private def coords (y : B) : (E y ⧸ V y) →ₗ[𝕜] κ → 𝕜 :=
  if hy : y ∈ U then (hY.basis hy).equivFun.toLinearMap else 0

open scoped Classical in
/-- The class of `E y ⧸ V y` with given coordinates in the frame `Y`, extended by zero off `U`. -/
private def vec (y : B) : (κ → 𝕜) →ₗ[𝕜] E y ⧸ V y :=
  if hy : y ∈ U then (hY.basis hy).equivFun.symm.toLinearMap else 0

private theorem coords_of_mem {y : B} (hy : y ∈ U) (v : E y ⧸ V y) :
    hY.coords y v = (hY.basis hy).equivFun v := by
  simp [coords, hy]

private theorem vec_of_mem {y : B} (hy : y ∈ U) (c : κ → 𝕜) :
    hY.vec y c = (hY.basis hy).equivFun.symm c := by
  simp [vec, hy]

private theorem vec_coords {y : B} (hy : y ∈ U) (v : E y ⧸ V y) :
    hY.vec y (hY.coords y v) = v := by
  rw [vec_of_mem hY hy, coords_of_mem hY hy, LinearEquiv.symm_apply_apply]

private theorem coords_vec {y : B} (hy : y ∈ U) (c : κ → 𝕜) : hY.coords y (hY.vec y c) = c := by
  rw [vec_of_mem hY hy, coords_of_mem hY hy, LinearEquiv.apply_symm_apply]

variable [TopologicalSpace 𝕜] [TopologicalSpace B]

/-- The local pretrivialization of the quotient `E ⧸ V` given by a local frame `Y` of it on an open
set `U`: over `U`, a class of `E y ⧸ V y` is sent to its coordinates in the frame. -/
def pretrivialization (hU : IsOpen U) :
    Pretrivialization (κ → 𝕜) (π (κ → 𝕜) fun x ↦ E x ⧸ V x) where
  toFun p := (p.proj, hY.coords p.proj p.snd)
  invFun q := TotalSpace.mk' (κ → 𝕜) (E := fun x ↦ E x ⧸ V x) q.1 (hY.vec q.1 q.2)
  source := π (κ → 𝕜) (fun x ↦ E x ⧸ V x) ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p hp := by
    dsimp only
    rw [vec_coords hY hp]
  right_inv' q hq := by
    dsimp only
    rw [coords_vec hY hq.1]
  open_target := hU.prod isOpen_univ
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (hU : IsOpen U)

@[simp]
theorem pretrivialization_baseSet : (hY.pretrivialization hU).baseSet = U :=
  (rfl)

private theorem pretrivialization_apply_eq (p : TotalSpace (κ → 𝕜) fun x ↦ E x ⧸ V x) :
    hY.pretrivialization hU p = (p.proj, hY.coords p.proj p.snd) :=
  (rfl)

/-- Over `U`, the frame pretrivialization sends a class to its coordinates in the frame. -/
@[simp]
theorem pretrivialization_apply {p : TotalSpace (κ → 𝕜) fun x ↦ E x ⧸ V x} (hp : p.proj ∈ U) :
    hY.pretrivialization hU p = (p.proj, (hY.basis hp).equivFun p.snd) := by
  rw [pretrivialization_apply_eq, coords_of_mem hY hp]

/-- Over `U`, the inverse of the frame pretrivialization sends coordinates to the corresponding
combination of the frame. -/
@[simp]
theorem pretrivialization_symm_apply {y : B} (hy : y ∈ U) (c : κ → 𝕜) :
    (hY.pretrivialization hU).symm y c = (hY.basis hy).equivFun.symm c := by
  rw [Pretrivialization.symm_apply _ hy]
  -- The cast is along an equality of base points that holds by definition of the inverse.
  exact vec_of_mem hY hy c

/-- The frame pretrivialization is fibrewise linear. -/
instance isLinear_pretrivialization : (hY.pretrivialization hU).IsLinear 𝕜 where
  linear y _ := (hY.coords y).isLinear

end Coordinates

end IsQuotientFrameOn

end Frame

section Combined

variable {𝕜 : Type*} [Ring 𝕜] {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
  {ι κ : Type*} {V : Π x, Submodule 𝕜 (E x)} {X : ι → Π x, E x} {Y : κ → Π x, E x} {U : Set B}

omit [TopologicalSpace B] [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] in
private theorem sumElim_apply_eq (y : B) :
    (fun k ↦ Sum.elim X Y k y) = Sum.elim (X · y) (Y · y) := by
  ext (i | j) <;> rfl

/-- **Quotient frames are complements of subbundle frames.** If `X` is a local frame of `V` on
`U`, then the sections `Y` form a local frame of `E ⧸ V` on `U` exactly when at every point `y` of
`U` the vectors `X i y` and `Y j y` together form a basis of `E y`. -/
theorem IsSubbundleFrameOn.isQuotientFrameOn_iff (hX : IsSubbundleFrameOn F V X U) :
    IsQuotientFrameOn V Y U ↔ ∀ y ∈ U, LinearIndependent 𝕜 (fun k ↦ Sum.elim X Y k y) ∧
      Submodule.span 𝕜 (range fun k ↦ Sum.elim X Y k y) = ⊤ := by
  have hrange (y : B) : (range fun j ↦ (Submodule.Quotient.mk (Y j y) : E y ⧸ V y)) =
      (V y).mkQ '' range (Y · y) := by
    simp only [← range_comp, comp_def, Submodule.mkQ_apply]
  -- The span of the combined family is `V y ⊔ span (Y · y)`, which is everything exactly when
  -- the classes of `Y · y` span the quotient.
  have hspan (y : B) (hy : y ∈ U) : Submodule.span 𝕜 (range fun k ↦ Sum.elim X Y k y) = ⊤ ↔
      Submodule.span 𝕜 (range fun j ↦ (Submodule.Quotient.mk (Y j y) : E y ⧸ V y)) = ⊤ := by
    rw [sumElim_apply_eq, Set.Sum.elim_range, Submodule.span_union, hX.span_eq hy, hrange,
      ← Submodule.map_span, Submodule.map_mkQ_eq_top]
  refine ⟨fun hY y hy ↦ ⟨?_, (hspan y hy).2 (hY.span_eq hy)⟩, fun h ↦ ⟨fun {y} hy ↦ ?_,
    fun hy ↦ (hspan _ hy).1 (h _ hy).2⟩⟩
  · rw [sumElim_apply_eq]
    have hX' : LinearIndependent 𝕜 fun i ↦ (⟨X i y, hX.apply_mem i hy⟩ : V y) :=
      .of_comp (V y).subtype (hX.linearIndependent hy)
    exact hX'.sumElim_of_quotient (Y · y) (hY.linearIndependent hy)
  · obtain ⟨-, hYi, hdisj⟩ := linearIndependent_sum.mp (sumElim_apply_eq (X := X) (Y := Y) y ▸
      (h y hy).1)
    refine hYi.map (f := (V y).mkQ) ?_
    rw [Submodule.ker_mkQ, ← hX.span_eq hy]
    exact hdisj.symm

end Combined

end TauCeti
