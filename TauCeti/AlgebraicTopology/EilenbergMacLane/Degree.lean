/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Eilenberg--Mac Lane spaces of type `K(G, n)`

For a positive integer `n` and a group `G`, a based space `(X, x)` is an Eilenberg--Mac Lane
space of type `K(G, n)` when it is path-connected, its homotopy groups `πₖ(X, x)` vanish for every
positive `k ≠ n`, and `πₙ(X, x)` is isomorphic to `G`
(`TauCeti.IsEilenbergMacLaneSpace`). For `n ≥ 2` the group `πₙ(X, x)` is abelian, so then `G` is
abelian; for `n = 1` this is the existing notion `TauCeti.IsEilenbergMacLaneSpaceOne`
(`TauCeti.isEilenbergMacLaneSpace_one_iff`).

As for `K(G, 1)` spaces, the definition is a property rather than a structure carrying a chosen
isomorphism. It does not depend on the base point, is invariant under homotopy equivalence and
under isomorphism of the target group, and is closed under binary and indexed products.

Since all other homotopy groups vanish, a map between two Eilenberg--Mac Lane spaces in the same
degree `n` is a weak homotopy equivalence exactly when it induces a bijection on `πₙ` at one base
point (`TauCeti.IsEilenbergMacLaneSpace.isWeakHomotopyEquivalence_iff`). Combined with
Whitehead's theorem `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`, such a map between
two `K(G, n)` spaces of CW type is a homotopy equivalence.

## Main declarations

* `TauCeti.IsEilenbergMacLaneSpace G n X x`: `(X, x)` is a `K(G, n)` space.
* `TauCeti.isEilenbergMacLaneSpace_one_iff`: in degree one this is
  `TauCeti.IsEilenbergMacLaneSpaceOne`.
* `TauCeti.IsEilenbergMacLaneSpace.of_basepoint`, `TauCeti.IsEilenbergMacLaneSpace.of_mulEquiv`,
  `TauCeti.IsEilenbergMacLaneSpace.of_homotopyEquiv`: invariance under change of base point, of
  the group and of the space up to homotopy equivalence.
* `TauCeti.IsEilenbergMacLaneSpace.prod`, `TauCeti.IsEilenbergMacLaneSpace.pi`: closure under
  products.
* `TauCeti.IsEilenbergMacLaneSpace.isWeakHomotopyEquivalence_iff`: a map between `K(G, n)` and
  `K(H, n)` spaces is a weak homotopy equivalence exactly when it is bijective on `πₙ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2,
  Eilenberg--MacLane spaces, and Proposition 4.30.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy ContinuousMap

universe u v w w'

/-- A based space `(X, x)` is an **Eilenberg--Mac Lane space of type `K(G, n)`**, for a positive
integer `n`, when it is path-connected, its homotopy groups `πₖ(X, x)` vanish for every positive
`k ≠ n`, and `πₙ(X, x)` is isomorphic to `G`. -/
def IsEilenbergMacLaneSpace (G : Type u) [Group G] (n : ℕ) [NeZero n]
    (X : Type v) [TopologicalSpace X] (x : X) : Prop :=
  PathConnectedSpace X ∧ (∀ k, k ≠ 0 → k ≠ n → Subsingleton (π_ k X x)) ∧
    Nonempty (π_ n X x ≃* G)

/-- Characteristic restatement of the `K(G, n)` property. -/
theorem isEilenbergMacLaneSpace_iff {G : Type u} [Group G] {n : ℕ} [NeZero n]
    {X : Type v} [TopologicalSpace X] {x : X} :
    IsEilenbergMacLaneSpace G n X x ↔
      PathConnectedSpace X ∧ (∀ k, k ≠ 0 → k ≠ n → Subsingleton (π_ k X x)) ∧
        Nonempty (π_ n X x ≃* G) :=
  Iff.rfl

/-- A based space is an Eilenberg--Mac Lane space of type `K(πₙ(X, x), n)` if and only if it is
path-connected and its other positive-dimensional homotopy groups vanish. -/
@[simp]
theorem isEilenbergMacLaneSpace_homotopyGroup_iff {n : ℕ} [NeZero n]
    {X : Type v} [TopologicalSpace X] {x : X} :
    IsEilenbergMacLaneSpace (π_ n X x) n X x ↔
      PathConnectedSpace X ∧ ∀ k, k ≠ 0 → k ≠ n → Subsingleton (π_ k X x) :=
  ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ⟨MulEquiv.refl _⟩⟩⟩

namespace IsEilenbergMacLaneSpace

variable {G : Type u} {H : Type v} [Group G] [Group H] {n : ℕ} [NeZero n]
  {X : Type w} {Y : Type w'} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- Construct the `K(G, n)` property from path-connectedness, the vanishing of the other
positive-dimensional homotopy groups and an isomorphism between `πₙ` and `G`. -/
protected theorem mk (hX : PathConnectedSpace X)
    (hπ : ∀ k, k ≠ 0 → k ≠ n → Subsingleton (π_ k X x)) (hG : Nonempty (π_ n X x ≃* G)) :
    IsEilenbergMacLaneSpace G n X x :=
  ⟨hX, hπ, hG⟩

/-- A `K(G, n)` space is path-connected. -/
protected theorem pathConnectedSpace (h : IsEilenbergMacLaneSpace G n X x) :
    PathConnectedSpace X :=
  h.1

/-- Every homotopy group of a `K(G, n)` space outside dimension `n` is trivial, including the set
`π₀` of path components. -/
protected theorem subsingleton_homotopyGroup (h : IsEilenbergMacLaneSpace G n X x) {k : ℕ}
    (hk : k ≠ n) : Subsingleton (π_ k X x) := by
  rcases eq_or_ne k 0 with rfl | hk0
  · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).1 h.pathConnectedSpace
  · exact h.2.1 k hk0 hk

/-- The `n`th homotopy group of a `K(G, n)` space is isomorphic to `G`. -/
protected theorem nonempty_homotopyGroupMulEquiv (h : IsEilenbergMacLaneSpace G n X x) :
    Nonempty (π_ n X x ≃* G) :=
  h.2.2

/-- **The `K(G, n)` property does not depend on the base point.** A `K(G, n)` space is path
connected, so its homotopy groups at any two points are isomorphic. -/
theorem of_basepoint (h : IsEilenbergMacLaneSpace G n X x) (x' : X) :
    IsEilenbergMacLaneSpace G n X x' := by
  have := h.pathConnectedSpace
  refine .mk h.pathConnectedSpace (fun k hk0 hk ↦ ?_) ?_
  · have : NeZero k := ⟨hk0⟩
    have := h.subsingleton_homotopyGroup hk
    obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv (N := Fin k) (x := x) (y := x')
    exact φ.toEquiv.subsingleton_congr.mp inferInstance
  · obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv (N := Fin n) (x := x') (y := x)
    exact h.nonempty_homotopyGroupMulEquiv.map φ.trans

/-- Transporting the target group along an isomorphism preserves the `K(G, n)` property. -/
theorem of_mulEquiv (h : IsEilenbergMacLaneSpace G n X x) (e : G ≃* H) :
    IsEilenbergMacLaneSpace H n X x :=
  .mk h.pathConnectedSpace h.2.1 (h.nonempty_homotopyGroupMulEquiv.map fun f ↦ f.trans e)

/-- **Being an Eilenberg--Mac Lane space of type `K(G, n)` is a homotopy invariant**, at every
base point of the homotopy equivalent space. -/
theorem of_homotopyEquiv (h : IsEilenbergMacLaneSpace G n X x) (e : X ≃ₕ Y) (y : Y) :
    IsEilenbergMacLaneSpace G n Y y := by
  have := h.pathConnectedSpace
  refine .mk e.pathConnectedSpace (fun k hk0 hk ↦ ?_) ?_
  · have : NeZero k := ⟨hk0⟩
    have := h.subsingleton_homotopyGroup hk
    obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv_of_homotopyEquiv (N := Fin k) e x y
    exact φ.toEquiv.subsingleton_congr.mp inferInstance
  · obtain ⟨φ⟩ := nonempty_homotopyGroupMulEquiv_of_homotopyEquiv (N := Fin n) e x y
    exact h.nonempty_homotopyGroupMulEquiv.map φ.symm.trans

variable {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
  {X₁ : Type w} {X₂ : Type w'} [TopologicalSpace X₁] [TopologicalSpace X₂]
  {x₁ : X₁} {x₂ : X₂}

/-- The product of a `K(G₁, n)` space and a `K(G₂, n)` space is a `K(G₁ × G₂, n)` space. -/
theorem prod (h₁ : IsEilenbergMacLaneSpace G₁ n X₁ x₁) (h₂ : IsEilenbergMacLaneSpace G₂ n X₂ x₂) :
    IsEilenbergMacLaneSpace (G₁ × G₂) n (X₁ × X₂) (x₁, x₂) := by
  have := h₁.pathConnectedSpace
  have := h₂.pathConnectedSpace
  refine .mk inferInstance (fun k hk0 hk ↦ ?_) ?_
  · have := h₁.subsingleton_homotopyGroup hk
    have := h₂.subsingleton_homotopyGroup hk
    exact (HomotopyGroup.prodEquiv (N := Fin k) x₁ x₂).subsingleton_congr.mpr inferInstance
  · obtain ⟨e₁⟩ := h₁.nonempty_homotopyGroupMulEquiv
    obtain ⟨e₂⟩ := h₂.nonempty_homotopyGroupMulEquiv
    exact ⟨(HomotopyGroup.prodMulEquiv x₁ x₂).trans (e₁.prodCongr e₂)⟩

variable {ι : Type w} {G' : ι → Type u} {Z : ι → Type v}
  [∀ i, Group (G' i)] [∀ i, TopologicalSpace (Z i)] {z : ∀ i, Z i}

/-- An indexed product of `K(Gᵢ, n)` spaces is a `K(Π i, Gᵢ, n)` space. -/
theorem pi (h : ∀ i, IsEilenbergMacLaneSpace (G' i) n (Z i) (z i)) :
    IsEilenbergMacLaneSpace (∀ i, G' i) n (∀ i, Z i) z := by
  have := fun i ↦ (h i).pathConnectedSpace
  refine .mk inferInstance (fun k hk0 hk ↦ ?_) ?_
  · have := fun i ↦ (h i).subsingleton_homotopyGroup hk
    exact inferInstance
  · exact ⟨(HomotopyGroup.piMulEquiv z).trans
      (MulEquiv.piCongrRight fun i ↦ Classical.choice (h i).nonempty_homotopyGroupMulEquiv)⟩

/-- **A map between Eilenberg--Mac Lane spaces in the same degree is a weak homotopy equivalence
exactly when it induces a bijection on `πₙ`.** Bijectivity at the single base point `x`
suffices, and the groups `G` and `H` play no role. -/
theorem isWeakHomotopyEquivalence_iff (hX : IsEilenbergMacLaneSpace G n X x)
    (hY : IsEilenbergMacLaneSpace H n Y y) {f : C(X, Y)} (hxy : f x = y) :
    f.IsWeakHomotopyEquivalence ↔ Function.Bijective (HomotopyGroup.map (N := Fin n) f hxy) := by
  subst hxy
  have := hX.pathConnectedSpace
  refine ⟨fun hf ↦ hf.bijective n x, fun hf ↦ ?_⟩
  refine (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective x).2 fun k ↦ ?_
  rcases eq_or_ne k n with rfl | hk
  · exact hf
  · -- Outside dimension `n` both homotopy groups are trivial.
    have := hX.subsingleton_homotopyGroup hk
    have := hY.subsingleton_homotopyGroup hk
    exact Function.bijective_of_subsingleton' _

end IsEilenbergMacLaneSpace

/-- **In degree one, the `K(G, n)` property is the `K(G, 1)` property.** -/
theorem isEilenbergMacLaneSpace_one_iff {G : Type u} [Group G]
    {X : Type v} [TopologicalSpace X] {x : X} :
    IsEilenbergMacLaneSpace G 1 X x ↔ IsEilenbergMacLaneSpaceOne G X x := by
  refine ⟨fun h ↦ .mk (.mk h.pathConnectedSpace fun k ↦ h.subsingleton_homotopyGroup (by omega))
    (h.nonempty_homotopyGroupMulEquiv.map HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans),
    fun h ↦ .mk h.isAspherical.pathConnectedSpace (fun k hk0 hk ↦ ?_)
      (h.nonempty_fundamentalGroupMulEquiv.map HomotopyGroup.pi1MulEquivFundamentalGroup.trans)⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  exact h.isAspherical.subsingleton_homotopyGroup m

end TauCeti
