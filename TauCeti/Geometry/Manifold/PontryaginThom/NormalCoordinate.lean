/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
public import TauCeti.Topology.Homotopy.Lifting.Basic

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
* `TauCeti.IsFramedTube.normalCoordinate`: the normal coordinate `τ(S × D) → D`.
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
private def tubeBallHomeomorph (h : IsFramedTube f τ) (ε : ℝ) :
    S × ball (0 : V) ε ≃ₜ tubeBall τ ε :=
  ((Homeomorph.Set.univ S).symm.prodCongr (.refl _)).trans <|
    (Homeomorph.Set.prod univ (ball (0 : V) ε)).symm.trans <|
      (Homeomorph.setCongr univ_prod).trans <|
        h.isOpenEmbedding.isEmbedding.homeomorphImage _

private lemma coe_tubeBallHomeomorph_apply (h : IsFramedTube f τ) {ε : ℝ}
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

/-- Every point of the part of the tube over the ball is `τ (x, v)`, with `v` its normal
coordinate. -/
lemma exists_apply_normalCoordinate (h : IsFramedTube f τ) {ε : ℝ} (w : tubeBall τ ε) :
    ∃ x, τ (x, h.normalCoordinate ε w) = w :=
  ⟨((h.tubeBallHomeomorph ε).symm w).1,
    congrArg Subtype.val ((h.tubeBallHomeomorph ε).apply_symm_apply w)⟩

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

end IsFramedTube

end TauCeti
