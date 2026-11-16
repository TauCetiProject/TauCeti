/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import TauCeti.GroupTheory.FreeGroup.Centralizer
public import TauCeti.GroupTheory.PushoutI.DehnTwist

/-!
# Examples of Dehn twists of amalgamated products

Two concrete amalgams of free groups of rank two illustrate the twists of
`Monoid.PushoutI.dehnTwist` and `Monoid.PushoutI.leftDehnTwist`.

* The amalgam `⟨a₁, b₁⟩ ∗_{c = [a₁, b₁] = [b₂, a₂]} ⟨a₂, b₂⟩` over an infinite cyclic group,
  which has the presentation `⟨a₁, b₁, a₂, b₂ | [a₁, b₁] [a₂, b₂]⟩` of the fundamental group of
  the closed orientable surface of genus two, split along a separating simple closed curve `c`.
  The twist `TauCeti.GenusTwoSplitting.twist` by `c` fixes `a₁` and `b₁` and conjugates `a₂` and
  `b₂` by `c`; it is not the identity. Conjugating the second factor by `a₂`, which does not
  commute with `c`, is not compatible with the amalgamation.
* The free product `F(a, b) ∗ F(c, d)`. The twists by `a` and `b`, which fix the first factor
  and conjugate the second, compose in the order opposite to multiplication of parameters:
  `τ_a (τ_b c) = b a c a⁻¹ b⁻¹`, and `τ_a ∘ τ_b ≠ τ_{ab}`.

The comparison of the first amalgam with a surface group given by its one-relator presentation
is not made here.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, §5.1.4 (twists around two-sided
  simple closed curves of surfaces) and §9 (the twist of `A ∗_C B` by a central element of `C`).
* J.-P. Serre, *Trees*, Chapter I, §1.1 (the amalgam universal property).
-/

public section

open Monoid.PushoutI

namespace TauCeti

namespace GenusTwoSplitting

/-- The commutator `[x₀, x₁] = x₀ x₁ x₀⁻¹ x₁⁻¹` of the basis of the free group of rank two. -/
def basisCommutator : FreeGroup (Fin 2) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

theorem basisCommutator_def :
    basisCommutator = FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ :=
  (rfl)

theorem basisCommutator_ne_one : basisCommutator ≠ 1 := by
  rw [basisCommutator_def]
  decide

/-- The boundary maps of the splitting of the genus two surface group along a separating curve:
the generator of the infinite cyclic edge group goes to the commutator `[a₁, b₁]` of the basis
of the left factor and to the commutator `[b₂, a₂] = [a₂, b₂]⁻¹` of the basis of the right
factor. -/
def boundary : Bool → Multiplicative ℤ →* FreeGroup (Fin 2)
  | false => zpowersHom _ basisCommutator
  | true => zpowersHom _ basisCommutator⁻¹

@[simp] theorem boundary_false (n : Multiplicative ℤ) :
    boundary false n = basisCommutator ^ n.toAdd := (rfl)

@[simp] theorem boundary_true (n : Multiplicative ℤ) :
    boundary true n = basisCommutator⁻¹ ^ n.toAdd := (rfl)

/-- Both boundary maps are injective: the amalgam is a splitting over an infinite cyclic
group. -/
theorem boundary_injective (i : Bool) : Function.Injective (boundary i) := by
  have hc := basisCommutator_ne_one
  intro m n h
  cases i <;> exact Multiplicative.toAdd.injective <|
    IsMulTorsionFree.zpow_right_injective (by simpa using hc) (by simpa using h)

/-- The separating curve: the image of the generator of the edge group in the amalgam. -/
def curve : Monoid.PushoutI boundary := base boundary (Multiplicative.ofAdd 1)

theorem curve_def : curve = base boundary (Multiplicative.ofAdd 1) := (rfl)

/-- The curve is the commutator `[a₁, b₁]` of the basis of the left factor. -/
theorem of_false_basisCommutator : of (φ := boundary) false basisCommutator = curve := by
  simp [curve, ← of_apply_eq_base boundary false]

/-- The curve is the commutator `[b₂, a₂]` of the basis of the right factor. -/
theorem of_true_basisCommutator_inv : of (φ := boundary) true basisCommutator⁻¹ = curve := by
  simp [curve, ← of_apply_eq_base boundary true]

/-- The Dehn twist along the separating curve: the twist of the amalgam by the image
`[b₂, a₂]` of the generator of the edge group in the right factor. -/
def twist : MulAut (Monoid.PushoutI boundary) :=
  dehnTwist boundary ⟨basisCommutator⁻¹, by
    rintro _ ⟨n, rfl⟩
    exact ((Commute.refl basisCommutator⁻¹).zpow_left n.toAdd).eq⟩

/-- The twist along the separating curve fixes the left factor `⟨a₁, b₁⟩`. -/
@[simp] theorem twist_of_false (x : FreeGroup (Fin 2)) : twist (of false x) = of false x :=
  dehnTwist_of_false ..

/-- The twist along the separating curve conjugates the right factor `⟨a₂, b₂⟩` by the
curve. -/
@[simp] theorem twist_of_true (x : FreeGroup (Fin 2)) :
    twist (of true x) = curve * of true x * curve⁻¹ := by
  rw [twist, dehnTwist_of_true, of_true_basisCommutator_inv]

/-- The twist along the separating curve is not the identity. -/
theorem twist_ne_one : twist ≠ 1 := by
  rw [twist, Ne, dehnTwist_eq_one_iff boundary boundary_injective,
    FreeGroup.center_eq_bot_of_nontrivial, Subgroup.mem_bot]
  exact inv_ne_one.mpr basisCommutator_ne_one

/-- The basis element `a₂` of the right factor does not commute with the curve, so no
endomorphism of the amalgam fixes the left factor and conjugates the right factor by `a₂`. -/
theorem not_exists_map_of_true_eq_conj_of_zero :
    ¬∃ f : Monoid.PushoutI boundary →* Monoid.PushoutI boundary,
      (∀ x, f (of false x) = of false x) ∧
        ∀ x, f (of true x) =
          of true (FreeGroup.of 0) * of true x * (of true (FreeGroup.of 0))⁻¹ := by
  rw [exists_map_of_true_eq_iff_mem_centralizer boundary boundary_injective,
    Subgroup.mem_centralizer_iff]
  intro h
  have h' := h _ ⟨Multiplicative.ofAdd 1, rfl⟩
  rw [boundary_true, toAdd_ofAdd, zpow_one, basisCommutator_def] at h'
  revert h'
  decide

end GenusTwoSplitting

namespace FreeSplitting

/-- The boundary maps of the free product `F(a, b) ∗ F(c, d)`, an amalgam over the trivial
group. -/
def boundary (_ : Bool) : Unit →* FreeGroup (Fin 2) := 1

/-- Every element of the left factor centralizes the trivial edge group. -/
theorem mem_centralizer (z : FreeGroup (Fin 2)) :
    z ∈ Subgroup.centralizer (Set.range (boundary false)) := by
  rintro _ ⟨c, rfl⟩
  simp [boundary]

/-- The twist of `F(a, b) ∗ F(c, d)` fixing the first factor and conjugating the second factor
by an element `z` of the first factor. -/
def twist (z : FreeGroup (Fin 2)) : MulAut (Monoid.PushoutI boundary) :=
  leftDehnTwist boundary ⟨z, mem_centralizer z⟩

/-- The twist by an element of the first factor fixes the first factor. -/
@[simp] theorem twist_of_false (z x : FreeGroup (Fin 2)) : twist z (of false x) = of false x :=
  leftDehnTwist_of_false ..

/-- The twist by an element `z` of the first factor conjugates the second factor by `z`. -/
@[simp] theorem twist_of_true (z x : FreeGroup (Fin 2)) :
    twist z (of true x) = of false z * of true x * (of false z)⁻¹ :=
  leftDehnTwist_of_true ..

/-- The twists by elements of the first factor compose in the order opposite to multiplication
of the parameters. -/
@[simp] theorem twist_mul (z w : FreeGroup (Fin 2)) : twist (z * w) = twist w * twist z :=
  leftDehnTwist_mul boundary ⟨z, mem_centralizer z⟩ ⟨w, mem_centralizer w⟩

/-- In `F(a, b) ∗ F(c, d)`, applying the twist by `b` and then the twist by `a` sends `c` to
`b a c a⁻¹ b⁻¹`. -/
theorem twist_twist_of_true :
    twist (FreeGroup.of 0) (twist (FreeGroup.of 1) (of true (FreeGroup.of 0))) =
      of false (FreeGroup.of 1 * FreeGroup.of 0) * of true (FreeGroup.of 0) *
        (of false (FreeGroup.of 1 * FreeGroup.of 0))⁻¹ := by
  rw [← MulAut.mul_apply, ← twist_mul, twist_of_true]

/-- A homomorphism from `F(a, b) ∗ F(c, d)` to the symmetric group on three letters separating
`b a c a⁻¹ b⁻¹` from `a b c b⁻¹ a⁻¹`. -/
private def toPerm : Monoid.PushoutI boundary →* Equiv.Perm (Fin 3) :=
  lift (fun _ => FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 1 2]) 1 fun _ => by
    ext
    simp [boundary]

/-- The twists of `F(a, b) ∗ F(c, d)` by elements of the first factor are not multiplicative in
the parameter: the twist by `a b` differs from the composite of the twists by `a` and `b`. -/
theorem twist_mul_ne :
    twist (FreeGroup.of 0 * FreeGroup.of 1) ≠ twist (FreeGroup.of 0) * twist (FreeGroup.of 1) := by
  intro h
  have h' := congrArg (fun τ : MulAut (Monoid.PushoutI boundary) =>
    toPerm (τ (of true (FreeGroup.of 0)))) h
  simp only [MulAut.mul_apply, twist_of_true, twist_of_false, map_mul, map_inv, toPerm, lift_of,
    FreeGroup.lift_apply_of] at h'
  revert h'
  decide

end FreeSplitting

end TauCeti
