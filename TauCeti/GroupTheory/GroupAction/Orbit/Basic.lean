/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.IterateAct

/-!
# Invariant-and-witness orbit criteria

To certify that the orbit `MulAction.orbit H a` of a point `a` under a subset-like structure `H`
(such as a subgroup or submonoid acting via `[SetLike S G] [SMul G α]`) equals a target set `s`, it
suffices to bound the orbit from above and below independently:

* **Upper bound (`MulAction.orbit_subset_of_invariant`):** an invariant function `f : α → β` taking
  the constant value `f a` along the orbit confines the orbit inside `s`, provided every point with
  `f x = f a` lies in `s`.
* **Lower bound (`MulAction.image_smul_subset_orbit`):** any witness set `W ⊆ (H : Set G)` maps
  into `MulAction.orbit H a` under `g ↦ g • a`.

Combining the two gives `MulAction.orbit_eq_of_invariant` for an arbitrary witness set `W : Set G`,
and `MulAction.orbit_eq_of_invariant_list` for an explicit witness list `ws : List G`. Separating
the witness membership condition (`∀ g ∈ ws, g ∈ H`) from the covering check
(`∀ x ∈ s, x ∈ ws.map (· • a)`) lets computational proofs discharge the covering check on concrete
ambient elements without packing subgroup-membership proofs into the witness list.

The file also identifies two orbits of cyclic actions: the orbit of `x` under the `ℕ`-action of
`IterateMulAct f` is its forward orbit `range fun n ↦ f^[n] x`, and the orbit under
`Subgroup.zpowers g` consists of the points `g ^ n • x`, `n : ℤ`.

## Main results

* `MulAction.orbit_subset_of_invariant`: a function constant along the `M`-orbit of `a` confines
  `orbit M a` inside any set containing its fiber through `a`.
* `MulAction.image_smul_subset_orbit`: the translates of `a` by elements of `W ⊆ H` lie in
  `orbit H a`.
* `MulAction.orbit_eq_of_invariant`: `orbit H a = s` from a function constant along the `H`-orbit
  of `a` whose fiber lies in `s`, together with a witness set `W ⊆ H` covering `s`.
* `MulAction.orbit_eq_of_invariant_list`: specialization of `MulAction.orbit_eq_of_invariant` to an
  explicit witness list `ws : List G`.
* `MulAction.orbit_iterateMulAct`: the orbit under `IterateMulAct f` is the forward orbit of `f`.
* `MulAction.mem_orbit_zpowers_iff`: membership in the orbit under `Subgroup.zpowers g`.
-/

public section

namespace MulAction

/-- If `f` takes the constant value `f a` along the `M`-orbit of `a`, and every point with
`f x = f a` lies in `s`, then `orbit M a ⊆ s`. -/
@[to_additive /-- If `f` takes the constant value `f a` along the additive `M`-orbit of `a`, and
every point with `f x = f a` lies in `s`, then `orbit M a ⊆ s`. -/]
theorem orbit_subset_of_invariant {M α : Type*} {β : Sort*} [SMul M α] {a : α} {s : Set α}
    (f : α → β) (hf : ∀ m : M, f (m • a) = f a) (hs : ∀ x, f x = f a → x ∈ s) :
    orbit M a ⊆ s := by
  rintro _ ⟨m, rfl⟩
  exact hs _ (hf m)

/-- The translates `(· • a) '' W` of `a` by elements of a subset `W ⊆ H` lie in `orbit H a`. -/
@[to_additive /-- The translates `(· +ᵥ a) '' W` of `a` by elements of a subset `W ⊆ H` lie in
`orbit H a`. -/]
theorem image_smul_subset_orbit {G α S : Type*} [SetLike S G] [SMul G α] {H : S} {a : α}
    {W : Set G} (hW : W ⊆ (H : Set G)) :
    (· • a) '' W ⊆ orbit H a := by
  rintro _ ⟨g, hg, rfl⟩
  exact mem_orbit_iff.mpr ⟨⟨g, hW hg⟩, rfl⟩

/-- The `H`-orbit of `a` equals `s` when a function `f` takes the constant value `f a` along the
orbit, every point with `f x = f a` lies in `s`, and a witness set `W ⊆ H` reaches every point of
`s` from `a`. -/
@[to_additive /-- The additive `H`-orbit of `a` equals `s` when a function `f` takes the constant
value `f a` along the orbit, every point with `f x = f a` lies in `s`, and a witness set `W ⊆ H`
reaches every point of `s` from `a`. -/]
theorem orbit_eq_of_invariant {G α S : Type*} {β : Sort*} [SetLike S G] [SMul G α]
    {H : S} {a : α} {s : Set α} (f : α → β) (W : Set G)
    (hf : ∀ g ∈ H, f (g • a) = f a) (hs : ∀ x, f x = f a → x ∈ s)
    (hW : W ⊆ (H : Set G)) (hcov : s ⊆ (· • a) '' W) :
    orbit H a = s :=
  Set.Subset.antisymm
    (orbit_subset_of_invariant f (fun g : H ↦ hf g g.property) hs)
    (hcov.trans (image_smul_subset_orbit hW))

/-- The `H`-orbit of `a` equals `s` when a function `f` takes the constant value `f a` along the
orbit, every point with `f x = f a` lies in `s`, and a list `ws` of elements of `H` reaches every
point of `s` from `a`. -/
@[to_additive /-- The additive `H`-orbit of `a` equals `s` when a function `f` takes the constant
value `f a` along the orbit, every point with `f x = f a` lies in `s`, and a list `ws` of elements
of `H` reaches every point of `s` from `a`. -/]
theorem orbit_eq_of_invariant_list {G α S : Type*} {β : Sort*} [SetLike S G] [SMul G α]
    {H : S} {a : α} {s : Set α} (f : α → β) (ws : List G)
    (hf : ∀ g ∈ H, f (g • a) = f a) (hs : ∀ x, f x = f a → x ∈ s)
    (hws : ∀ g ∈ ws, g ∈ H) (hcov : ∀ x ∈ s, x ∈ ws.map (· • a)) :
    orbit H a = s :=
  orbit_eq_of_invariant f {g | g ∈ ws} hf hs hws fun x hx ↦ by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (hcov x hx)
    exact ⟨g, hg, rfl⟩

/-- The orbit of `x` under the `ℕ`-action of `IterateMulAct f` is its forward orbit. -/
@[to_additive (attr := simp) /-- The orbit of `x` under the `ℕ`-action of `IterateAddAct f` is its
forward orbit. -/]
theorem orbit_iterateMulAct {α : Type*} (f : α → α) (x : α) :
    orbit (IterateMulAct f) x = Set.range fun n : ℕ ↦ f^[n] x := by
  ext y
  constructor
  · rintro ⟨⟨n⟩, rfl⟩
    exact ⟨n, (IterateMulAct.mk_smul n x).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨n⟩, IterateMulAct.mk_smul n x⟩

/-- The orbit of `x` under `Subgroup.zpowers g` consists of the points `g ^ n • x`, `n : ℤ`. -/
@[to_additive (attr := simp) /-- The orbit of `x` under `AddSubgroup.zmultiples g` consists of the
points `n • g +ᵥ x`, `n : ℤ`. -/]
theorem mem_orbit_zpowers_iff {G α : Type*} [Group G] [MulAction G α] {g : G} {x y : α} :
    y ∈ orbit (Subgroup.zpowers g) x ↔ ∃ n : ℤ, g ^ n • x = y := by
  simp only [mem_orbit_iff, Subgroup.exists_zpowers, Subgroup.smul_def]

end MulAction
