/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Flow.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Isomorphism

/-!
# Isomorphism invariance of weighted multigraph flows

A multigraph isomorphism `f : Graph.Iso G H` carries edge capacities `c : E(G) → K` to the
capacities `c ∘ f.edgeEquiv.symm` on `H`. This file proves that this relabelling preserves the
flows of the bidirected network together with their values and maximality.

`Graph.Iso.edgeCutCapacity_map` has exactly the shape of the set-function compatibility hypothesis
of the generic relabelling results along a vertex equivalence, such as
`TauCeti.TerminalCut.isMinimum_map_iff` and `TauCeti.TerminalCut.pairMinimumValue_map`. Minimum
cuts and minimum cut values of weighted multigraphs therefore transport through those results
applied to `f.vertexEquiv`, and cut trees through `TauCeti.TerminalCut.isCutTree_map_iff` for any
tree isomorphism with underlying equivalence `f.vertexEquiv`.

Flows of a weighted multigraph are flows of its bidirected arrow family `Graph.BidirectedHom G`
for the capacities `Graph.bidirectedCapacity`, an explicit assignment rather than a bundled
`TauCeti.Network`. They are transported by the arrow equivalence `Graph.Iso.bidirectedHomEquiv`,
which retains edge identities, so parallel edges and loops are transported individually.

## Main definitions

* `Graph.Iso.assignmentEquiv`: transport of assignments on the bidirected arrow families.
* `Graph.Iso.flowEquiv`: transport of `s`–`t` flows of a weighted multigraph.

## Main results

* `Graph.Iso.assignmentEquiv_refl`, `Graph.Iso.assignmentEquiv_trans`, and
  `Graph.Iso.assignmentEquiv_symm`: assignment transport is functorial.
* `Graph.Iso.flowEquiv_refl_toFun`, `Graph.Iso.flowEquiv_trans_toFun`, and
  `Graph.Iso.flowEquiv_symm_toFun`: the corresponding characterization laws for flows.
* `Graph.Iso.val_flowEquiv`, `Graph.Iso.isMaximum_flowEquiv_iff`: flow transport preserves the
  value and maximality of a flow.
-/

public section

open TauCeti

universe u v u' v' u'' v'' w w'

namespace Graph

namespace Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {K : Type w}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {I : Graph α'' β''}

/-! ### Assignments -/

/-- An assignment on the bidirected arrows takes equal values on arrows with the same edge and
endpoints, even when the endpoints are only propositionally equal. -/
private theorem apply_eq_of_fst_eq {R : Type w'} (φ : Assignment G.BidirectedHom R)
    {x y x' y' : V(G)} (a : G.BidirectedHom x y) (b : G.BidirectedHom x' y') (hx : x = x')
    (hy : y = y') (hab : a.val = b.val) : φ a = φ b := by
  subst hx hy
  rw [Subtype.ext hab]

/-- Transport of assignments on the bidirected arrow family along a graph isomorphism. The
transported assignment takes, on every arrow of `H`, the value of the corresponding arrow of `G`.
-/
def assignmentEquiv (f : Iso G H) (R : Type w') :
    Assignment G.BidirectedHom R ≃ Assignment H.BidirectedHom R where
  toFun φ _ _ b := φ (f.symm.mapHom b)
  invFun ψ _ _ a := ψ (f.mapHom a)
  left_inv φ := by
    funext x y a
    exact apply_eq_of_fst_eq φ _ a (by simp) (by simp) (by simp)
  right_inv ψ := by
    funext x y b
    exact apply_eq_of_fst_eq ψ _ b (by simp) (by simp) (by simp)

/-- A transported assignment takes, on an arrow of `H`, the value of the inverse image of that
arrow. -/
@[simp low]
theorem assignmentEquiv_apply (f : Iso G H) {R : Type w'} (φ : Assignment G.BidirectedHom R)
    {x y : V(H)} (b : H.BidirectedHom x y) :
    f.assignmentEquiv R φ b = φ (f.symm.mapHom b) :=
  (rfl)

/-- A transported assignment takes, on the image of an arrow, the original value. -/
@[simp]
theorem assignmentEquiv_apply_mapHom (f : Iso G H) {R : Type w'}
    (φ : Assignment G.BidirectedHom R) {x y : V(G)} (a : G.BidirectedHom x y) :
    f.assignmentEquiv R φ (f.mapHom a) = φ a :=
  apply_eq_of_fst_eq φ _ a (by simp) (by simp) (by simp)

/-- An assignment pulled back along an isomorphism takes, on an arrow of `G`, the value of its
image. -/
@[simp]
theorem assignmentEquiv_symm_apply (f : Iso G H) {R : Type w'}
    (ψ : Assignment H.BidirectedHom R) {x y : V(G)} (a : G.BidirectedHom x y) :
    (f.assignmentEquiv R).symm ψ a = ψ (f.mapHom a) :=
  (rfl)

/-- Inverse assignment transport is transport along the inverse graph isomorphism. -/
theorem assignmentEquiv_symm (f : Iso G H) (R : Type w') :
    (f.assignmentEquiv R).symm = f.symm.assignmentEquiv R := by
  apply Equiv.ext
  intro ψ
  funext x y a
  exact apply_eq_of_fst_eq ψ _ _ (by simp) (by simp) (by simp)

/-- Transport along the identity graph isomorphism is the identity on assignments. -/
@[simp]
theorem assignmentEquiv_refl (G : Graph α β) (R : Type w') :
    (Iso.refl G).assignmentEquiv R = Equiv.refl (Assignment G.BidirectedHom R) := by
  apply Equiv.ext
  intro φ
  funext x y a
  exact apply_eq_of_fst_eq φ _ a (by simp) (by simp) (by simp)

/-- Transporting assignments along a composite is the composite of the assignment transports. -/
@[simp]
theorem assignmentEquiv_trans (f : Iso G H) (g : Iso H I) (R : Type w') :
    (f.trans g).assignmentEquiv R = (f.assignmentEquiv R).trans (g.assignmentEquiv R) := by
  apply Equiv.ext
  intro φ
  funext x y a
  exact apply_eq_of_fst_eq φ _ _ (by simp) (by simp) (by simp)

/-- Assignment transport preserves the zero assignment. -/
@[simp]
theorem assignmentEquiv_zero (f : Iso G H) {R : Type w'} [Zero R] :
    f.assignmentEquiv R 0 = 0 :=
  (rfl)

/-- Assignment transport preserves and reflects the arrowwise order. -/
@[simp]
theorem assignmentEquiv_le_assignmentEquiv_iff (f : Iso G H) {R : Type w'} [LE R]
    {φ ψ : Assignment G.BidirectedHom R} :
    f.assignmentEquiv R φ ≤ f.assignmentEquiv R ψ ↔ φ ≤ ψ := by
  refine ⟨fun h x y a ↦ ?_, fun h _ _ b ↦ h _ _ _⟩
  simpa using h _ _ (f.mapHom a)

/-- Relabelling the edge capacities corresponds to transporting the bidirected capacities. -/
@[simp]
theorem assignmentEquiv_bidirectedCapacity (f : Iso G H) (c : E(G) → K) :
    f.assignmentEquiv K (G.bidirectedCapacity c) = H.bidirectedCapacity (c ∘ f.edgeEquiv.symm) := by
  funext x y b
  simp [assignmentEquiv_apply]

/-- Assignment transport preserves the excess at corresponding vertices. -/
@[simp]
theorem excessAt_assignmentEquiv [Fintype V(G)] [Fintype V(H)]
    [∀ x y, Fintype (G.BidirectedHom x y)] [∀ x y, Fintype (H.BidirectedHom x y)]
    {R : Type w'} [AddCommGroup R] (f : Iso G H) (φ : Assignment G.BidirectedHom R)
    (x : V(G)) :
    excessAt (f.assignmentEquiv R φ) (f.vertexEquiv x) = excessAt φ x := by
  rw [← excessAt_comp_equiv f.vertexEquiv f.bidirectedHomEquiv (f.assignmentEquiv R φ) x]
  simp

/-- The excess of an assignment pulled back along an isomorphism is the excess of the original
assignment at the corresponding vertex. -/
@[simp]
theorem excessAt_assignmentEquiv_symm [Fintype V(G)] [Fintype V(H)]
    [∀ x y, Fintype (G.BidirectedHom x y)] [∀ x y, Fintype (H.BidirectedHom x y)]
    {R : Type w'} [AddCommGroup R] (f : Iso G H) (ψ : Assignment H.BidirectedHom R)
    (x : V(G)) :
    excessAt ((f.assignmentEquiv R).symm ψ) x = excessAt ψ (f.vertexEquiv x) := by
  rw [← f.excessAt_assignmentEquiv ((f.assignmentEquiv R).symm ψ) x, Equiv.apply_symm_apply]

/-! ### Flows -/

variable [Fintype V(G)] [Fintype V(H)]
variable [∀ x y, Fintype (G.BidirectedHom x y)] [∀ x y, Fintype (H.BidirectedHom x y)]
variable [AddCommGroup K] [Preorder K]

/-- Transport of `s`–`t` flows of a weighted multigraph along a graph isomorphism, relabelling the
edge capacities and the terminals with it. -/
def flowEquiv (f : Iso G H) (c : E(G) → K) (s t : V(G)) :
    Flow (G.bidirectedCapacity c) s t ≃
      Flow (H.bidirectedCapacity (c ∘ f.edgeEquiv.symm)) (f.vertexEquiv s) (f.vertexEquiv t) where
  toFun φ :=
    { toFun := f.assignmentEquiv K φ.toFun
      mem_Icc :=
        ⟨by simpa using f.assignmentEquiv_le_assignmentEquiv_iff.2 φ.mem_Icc.1,
          by simpa using f.assignmentEquiv_le_assignmentEquiv_iff.2 φ.mem_Icc.2⟩
      conserve := fun y hys hyt ↦ by
        obtain ⟨x, rfl⟩ := f.vertexEquiv.surjective y
        rw [excessAt_assignmentEquiv]
        exact φ.conserve x (fun h ↦ hys (congrArg f.vertexEquiv h))
          (fun h ↦ hyt (congrArg f.vertexEquiv h))
      excessAt_sink_nonneg := by
        rw [excessAt_assignmentEquiv]
        exact φ.excessAt_sink_nonneg }
  invFun ψ :=
    { toFun := (f.assignmentEquiv K).symm ψ.toFun
      mem_Icc :=
        ⟨f.assignmentEquiv_le_assignmentEquiv_iff.1
            (by simpa only [assignmentEquiv_zero, Equiv.apply_symm_apply] using ψ.mem_Icc.1),
          f.assignmentEquiv_le_assignmentEquiv_iff.1
            (by simpa only [Equiv.apply_symm_apply, assignmentEquiv_bidirectedCapacity]
              using ψ.mem_Icc.2)⟩
      conserve := fun x hxs hxt ↦ by
        rw [excessAt_assignmentEquiv_symm]
        exact ψ.conserve _ (f.vertexEquiv.injective.ne hxs) (f.vertexEquiv.injective.ne hxt)
      excessAt_sink_nonneg := by
        rw [excessAt_assignmentEquiv_symm]
        exact ψ.excessAt_sink_nonneg }
  left_inv φ := Flow.ext (Equiv.symm_apply_apply _ _)
  right_inv ψ := Flow.ext (Equiv.apply_symm_apply _ _)

/-- The assignment of a transported flow is the transported assignment. -/
@[simp]
theorem flowEquiv_apply_toFun (f : Iso G H) {c : E(G) → K} {s t : V(G)}
    (φ : Flow (G.bidirectedCapacity c) s t) :
    (f.flowEquiv c s t φ).toFun = f.assignmentEquiv K φ.toFun :=
  (rfl)

/-- The assignment of a flow pulled back along an isomorphism is the pulled-back assignment. -/
@[simp]
theorem flowEquiv_symm_apply_toFun (f : Iso G H) {c : E(G) → K} {s t : V(G)}
    (ψ : Flow (H.bidirectedCapacity (c ∘ f.edgeEquiv.symm)) (f.vertexEquiv s) (f.vertexEquiv t)) :
    ((f.flowEquiv c s t).symm ψ).toFun = (f.assignmentEquiv K).symm ψ.toFun :=
  (rfl)

/-- The assignment of a flow transported along the identity graph isomorphism is unchanged. -/
theorem flowEquiv_refl_toFun (c : E(G) → K) (s t : V(G))
    (φ : Flow (G.bidirectedCapacity c) s t) :
    ((Iso.refl G).flowEquiv c s t φ).toFun = φ.toFun := by
  rw [flowEquiv_apply_toFun, assignmentEquiv_refl]
  rfl

/-- The assignment transported along a composite isomorphism is obtained by applying the two flow
transports in order. -/
theorem flowEquiv_trans_toFun [Fintype V(I)] [∀ x y, Fintype (I.BidirectedHom x y)]
    (f : Iso G H) (g : Iso H I) (c : E(G) → K) (s t : V(G))
    (φ : Flow (G.bidirectedCapacity c) s t) :
    ((f.trans g).flowEquiv c s t φ).toFun =
      (g.flowEquiv (c ∘ f.edgeEquiv.symm) (f.vertexEquiv s) (f.vertexEquiv t)
        (f.flowEquiv c s t φ)).toFun := by
  simp only [flowEquiv_apply_toFun, assignmentEquiv_trans, Equiv.trans_apply]

/-- Pulling back a flow is assignmentwise the same as transporting it along the inverse graph
isomorphism, with the already relabelled capacities and terminals. -/
theorem flowEquiv_symm_toFun (f : Iso G H) {c : E(G) → K} {s t : V(G)}
    (ψ : Flow (H.bidirectedCapacity (c ∘ f.edgeEquiv.symm))
      (f.vertexEquiv s) (f.vertexEquiv t)) :
    ((f.flowEquiv c s t).symm ψ).toFun =
      (f.symm.flowEquiv (c ∘ f.edgeEquiv.symm) (f.vertexEquiv s) (f.vertexEquiv t) ψ).toFun := by
  rw [flowEquiv_symm_apply_toFun, assignmentEquiv_symm, flowEquiv_apply_toFun]

/-- Flow transport preserves the value of a flow. -/
@[simp]
theorem val_flowEquiv (f : Iso G H) {c : E(G) → K} {s t : V(G)}
    (φ : Flow (G.bidirectedCapacity c) s t) : (f.flowEquiv c s t φ).val = φ.val := by
  simp [BoundedFlow.val_def]

/-- Flow transport preserves and reflects maximality of a flow. -/
@[simp]
theorem isMaximum_flowEquiv_iff (f : Iso G H) {c : E(G) → K} {s t : V(G)}
    {φ : Flow (G.bidirectedCapacity c) s t} : (f.flowEquiv c s t φ).IsMaximum ↔ φ.IsMaximum := by
  rw [Flow.isMaximum_iff, Flow.isMaximum_iff, val_flowEquiv]
  refine ⟨fun h g ↦ by simpa using h (f.flowEquiv c s t g), fun h g ↦ ?_⟩
  obtain ⟨g, rfl⟩ := (f.flowEquiv c s t).surjective g
  simpa using h g

end Iso

end Graph
