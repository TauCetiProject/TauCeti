/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
public import TauCeti.Topology.Homotopy.Lifting.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.Ball

/-!
# The normal coordinate of a framed tube

Let `τ : S × V → N` be a framed tube around `f : S → N` (`TauCeti.IsFramedTube`), with `V` a
normed group. Over the ball `D` of radius `ε` about `0`, the part `τ(S × D)` of the tube
(`TauCeti.IsFramedTube.tubeBall`) is an open neighbourhood of the core `f(S)` when `ε > 0`, and the
**normal coordinate** `τ(x, v) ↦ v` (`TauCeti.IsFramedTube.normalCoordinate`) is a continuous map
`τ(S × D) → D` whose zero set is the core
(`TauCeti.IsFramedTube.normalCoordinate_eq_zero_iff`). It is the projection of the trivial bundle
`S × D → D`, so it has the homotopy lifting property with respect to every space
(`TauCeti.IsFramedTube.hasHomotopyLiftingProperty_normalCoordinate`).

Unlike the Pontryagin–Thom collapse, which is the normal coordinate extended by `∞` outside the
tube, the normal coordinate needs no compactness of `S`. It is the local model of a framed
submanifold used to compute the local homology of a fibration along the preimage of the core, in
`TauCeti.AlgebraicTopology.Singular.Fibration.FramedTube`.

## Main definitions

* `TauCeti.IsFramedTube.tubeBall`: the part `τ(S × D)` of the tube over a ball about `0`.
* `TauCeti.IsFramedTube.tubeBallHomeomorph`: the homeomorphism `S × D ≃ₜ τ(S × D)`.
* `TauCeti.IsFramedTube.normalCoordinate`: the normal coordinate `τ(S × D) → D`.
* `TauCeti.IsFramedTube.tubeBallTrivialization`: a bundle trivialization over the tube, read as a
  product with the ball compatibly with the normal coordinate.
-/

public section

noncomputable section

open Metric Set Topology

namespace TauCeti

namespace IsFramedTube

variable {S N V : Type*} [TopologicalSpace S] [TopologicalSpace N] [NormedAddCommGroup V]
  {f : S → N} {τ : S × V → N}

/-- The part `τ(S × D)` of a tube `τ : S × V → N` over the ball `D` of radius `ε` about `0`. -/
def tubeBall (τ : S × V → N) (ε : ℝ) : Set N :=
  τ '' (Prod.snd ⁻¹' ball 0 ε)

omit [TopologicalSpace S] [TopologicalSpace N] in
@[simp]
lemma mem_tubeBall {ε : ℝ} {w : N} :
    w ∈ tubeBall τ ε ↔ ∃ x, ∃ v ∈ ball (0 : V) ε, τ (x, v) = w := by
  simp [tubeBall]

omit [TopologicalSpace S] [TopologicalSpace N] in
lemma apply_mem_tubeBall {ε : ℝ} (x : S) {v : V} (hv : v ∈ ball (0 : V) ε) :
    τ (x, v) ∈ tubeBall τ ε :=
  mem_tubeBall.2 ⟨x, v, hv, rfl⟩

omit [TopologicalSpace S] [TopologicalSpace N] in
lemma tubeBall_subset_range (ε : ℝ) : tubeBall τ ε ⊆ range τ :=
  image_subset_range _ _

lemma isOpen_tubeBall (h : IsFramedTube f τ) (ε : ℝ) : IsOpen (tubeBall τ ε) :=
  h.isOpenEmbedding.isOpenMap _ (isOpen_ball.preimage continuous_snd)

/-- For a positive radius, the core `f(S)` of a framed tube lies in the part of the tube over the
ball. -/
lemma range_subset_tubeBall (h : IsFramedTube f τ) {ε : ℝ} (hε₀ : 0 < ε) :
    range f ⊆ tubeBall τ ε := by
  rintro _ ⟨x, rfl⟩
  rw [← h.apply_zero]
  exact apply_mem_tubeBall x (mem_ball_self hε₀)

/-- The framed tube `S × D ≃ₜ τ(S × D)` over the ball `D` of radius `ε` about `0`. -/
def tubeBallHomeomorph (h : IsFramedTube f τ) (ε : ℝ) :
    S × ball (0 : V) ε ≃ₜ tubeBall τ ε :=
  ((Homeomorph.Set.univ S).symm.prodCongr (.refl _)).trans <|
    (Homeomorph.Set.prod univ (ball (0 : V) ε)).symm.trans <|
      (Homeomorph.setCongr univ_prod).trans <|
        h.isOpenEmbedding.isEmbedding.homeomorphImage _

@[simp]
lemma coe_tubeBallHomeomorph_apply (h : IsFramedTube f τ) {ε : ℝ}
    (q : S × ball (0 : V) ε) : (h.tubeBallHomeomorph ε q : N) = τ (q.1, q.2) :=
  (rfl)

/-- The **normal coordinate** `τ(x, v) ↦ v` of a framed tube `τ : S × V → N`, on the part of the
tube over the ball of radius `ε` about `0`. -/
def normalCoordinate (h : IsFramedTube f τ) (ε : ℝ) : C(tubeBall τ ε, ball (0 : V) ε) :=
  ⟨fun w ↦ ((h.tubeBallHomeomorph ε).symm w).2, by fun_prop⟩

private lemma coe_normalCoordinate (h : IsFramedTube f τ) (ε : ℝ) :
    ⇑(h.normalCoordinate ε) = Prod.fst ∘ ((h.tubeBallHomeomorph ε).symm.trans (.prodComm _ _)) :=
  (rfl)

@[simp]
lemma normalCoordinate_apply (h : IsFramedTube f τ) {ε : ℝ} (x : S) (v : V)
    (hv : τ (x, v) ∈ tubeBall τ ε) : (h.normalCoordinate ε ⟨τ (x, v), hv⟩ : V) = v := by
  have hv' : v ∈ ball (0 : V) ε := by
    obtain ⟨q, hq, hqv⟩ := hv
    rwa [h.isOpenEmbedding.injective hqv] at hq
  have hw : (⟨τ (x, v), hv⟩ : tubeBall τ ε) = h.tubeBallHomeomorph ε (x, ⟨v, hv'⟩) :=
    Subtype.ext (h.coe_tubeBallHomeomorph_apply (x, ⟨v, hv'⟩)).symm
  simp [coe_normalCoordinate, hw]

/-- The normal coordinate of a point `τ (x, v)` of the tube is `v`. -/
lemma normalCoordinate_eq_of_eq (h : IsFramedTube f τ) {ε : ℝ} {w : tubeBall τ ε} {x : S}
    {v : V} (hw : (w : N) = τ (x, v)) : (h.normalCoordinate ε w : V) = v := by
  obtain ⟨w, hwm⟩ := w
  subst hw
  exact h.normalCoordinate_apply x v hwm

/-- The normal coordinate of the point `τ (x, v)` of `τ(S × D)` given by the framed tube is `v`. -/
@[simp]
lemma normalCoordinate_tubeBallHomeomorph (h : IsFramedTube f τ) {ε : ℝ}
    (q : S × ball (0 : V) ε) : h.normalCoordinate ε (h.tubeBallHomeomorph ε q) = q.2 :=
  Subtype.ext (h.normalCoordinate_eq_of_eq (h.coe_tubeBallHomeomorph_apply q))

/-- The second coordinate of the inverse of the framed tube is the normal coordinate. -/
@[simp]
lemma tubeBallHomeomorph_symm_apply_snd (h : IsFramedTube f τ) {ε : ℝ} (w : tubeBall τ ε) :
    ((h.tubeBallHomeomorph ε).symm w).2 = h.normalCoordinate ε w :=
  (rfl)

/-- A point `w` of the part of the tube over the ball is `τ (x, v)`, where `x` is the first
coordinate of the inverse of the framed tube and `v` is the normal coordinate of `w`. -/
lemma apply_tubeBallHomeomorph_symm (h : IsFramedTube f τ) {ε : ℝ} (w : tubeBall τ ε) :
    τ (((h.tubeBallHomeomorph ε).symm w).1, h.normalCoordinate ε w) = w :=
  congrArg Subtype.val ((h.tubeBallHomeomorph ε).apply_symm_apply w)

/-- Every point of the part of the tube over the ball is `τ (x, v)`, with `v` its normal
coordinate. -/
lemma exists_apply_normalCoordinate (h : IsFramedTube f τ) {ε : ℝ} (w : tubeBall τ ε) :
    ∃ x, τ (x, h.normalCoordinate ε w) = w :=
  ⟨_, h.apply_tubeBallHomeomorph_symm w⟩

/-- The zero set of the normal coordinate is the core `f(S)`. -/
lemma normalCoordinate_eq_zero_iff (h : IsFramedTube f τ) {ε : ℝ} (w : tubeBall τ ε) :
    (h.normalCoordinate ε w : V) = 0 ↔ (w : N) ∈ range f := by
  obtain ⟨x, hx⟩ := h.exists_apply_normalCoordinate w
  refine ⟨fun h0 ↦ ⟨x, ?_⟩, ?_⟩
  · rw [← h.apply_zero, ← h0, hx]
  · rintro ⟨y, hy⟩
    have hw : (w : N) = τ (y, 0) := by rw [h.apply_zero, hy]
    obtain ⟨w, hwm⟩ := w
    subst hw
    exact h.normalCoordinate_apply y 0 hwm

/-- The normal coordinate of a framed tube has the homotopy lifting property with respect to every
space: it is the projection `S × D → D` of a trivial bundle. -/
lemma hasHomotopyLiftingProperty_normalCoordinate (h : IsFramedTube f τ) (ε : ℝ) (A : Type*)
    [TopologicalSpace A] : HasHomotopyLiftingProperty (h.normalCoordinate ε) A := by
  rw [coe_normalCoordinate]
  exact (hasHomotopyLiftingProperty_fst S A).comp
    (((h.tubeBallHomeomorph ε).symm.trans (.prodComm _ _)).hasHomotopyLiftingProperty A)
    (Homeomorph.continuous _)

section Trivialization

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {p : E → N}
  (hτ : IsFramedTube f τ) {ε : ℝ} (T : Bundle.Trivialization Y p) (hT : tubeBall τ ε ⊆ T.baseSet)

/-- Over the part `τ(S × D)` of a framed tube over the ball `D` of radius `ε` about `0`, a
trivialization of `p` over a base set containing `τ(S × D)` identifies the part of `E` over it with
`D × (S × Y)`: a point goes to the normal coordinate of its image, the coordinate of its image along
the core, and its fibre coordinate. -/
def tubeBallTrivialization : p ⁻¹' tubeBall τ ε ≃ₜ ball (0 : V) ε × (S × Y) :=
  (T.preimageHomeomorph hT).trans <|
    (((hτ.tubeBallHomeomorph ε).symm.trans (.prodComm _ _)).prodCongr (.refl Y)).trans
      (.prodAssoc _ _ _)

/-- The first coordinate of `TauCeti.IsFramedTube.tubeBallTrivialization` is the normal coordinate
of `p z` (`TauCeti.IsFramedTube.normalCoordinate`). -/
@[simp]
lemma tubeBallTrivialization_apply_fst (z : p ⁻¹' tubeBall τ ε) :
    (hτ.tubeBallTrivialization T hT z).1 = hτ.normalCoordinate ε ⟨p z, z.property⟩ := by
  simp [tubeBallTrivialization, T.preimageHomeomorph_apply, Homeomorph.prodAssoc]

/-- The second coordinate of `TauCeti.IsFramedTube.tubeBallTrivialization` is the coordinate along
the core given by the tube, together with the fibre coordinate of `T`. -/
@[simp]
lemma tubeBallTrivialization_apply_snd (z : p ⁻¹' tubeBall τ ε) :
    (hτ.tubeBallTrivialization T hT z).2 =
      (((hτ.tubeBallHomeomorph ε).symm ⟨p z, z.property⟩).1, (T z.val).2) := by
  simp [tubeBallTrivialization, T.preimageHomeomorph_apply, Homeomorph.prodAssoc]

/-- The inverse of `TauCeti.IsFramedTube.tubeBallTrivialization` is the inverse of `T` after reading
the normal coordinate and the coordinate along the core back in `N` through the framed tube. -/
@[simp]
lemma coe_tubeBallTrivialization_symm_apply (x : ball (0 : V) ε × (S × Y)) :
    ((hτ.tubeBallTrivialization T hT).symm x : E) =
      T.toOpenPartialHomeomorph.symm (τ (x.2.1, x.1), x.2.2) := by
  simp [tubeBallTrivialization, Homeomorph.prodAssoc]

end Trivialization

end IsFramedTube

section ChartBall

/-- If near `b'` the normal coordinate of `s` is a chart at `b'`, then `s b'` lies on the core. -/
lemma IsFramedTube.apply_mem_range_of_chartBall {V B B' S : Type*} [SeminormedAddCommGroup V]
    [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace S] {f : S → B} {τ : S × V → B}
    (hτ : IsFramedTube f τ) {s : B' → B} (e : OpenPartialHomeomorph B' V) {b' : B'}
    (hb : b' ∈ e.source) {ε : ℝ} (hs : ∀ x ∈ e.chartBall b' ε, ∃ y, τ (y, e x - e b') = s x)
    (hε₀ : 0 < ε) : s b' ∈ range f := by
  obtain ⟨y, hy⟩ := hs b' (e.mem_chartBall_self hb hε₀)
  exact ⟨y, by rw [← hτ.apply_zero, ← hy, sub_self]⟩

end ChartBall

end TauCeti
