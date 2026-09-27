/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Divisibility by the characteristic polynomial of a group action

Let a finite group `G` act on an integral domain `B`. Mathlib's
`MulSemiringAction.charpoly G b = ∏ g : G, (X - C (g • b))` is the monic polynomial whose roots
are the translates of `b`. When those translates are pairwise distinct, it divides every
polynomial vanishing on all of them. This is the step that turns "vanishes on the orbit" into
an explicit factorization, for instance when comparing the displacement of a generator of an
intermediate ring with a product of displacements of a generator of the top ring.

## Main results

* `TauCeti.MulSemiringAction.charpoly_dvd`: if `g ↦ g • b` is injective and `f` vanishes at every
  `g • b`, then `charpoly G b ∣ f`.
* `TauCeti.MulSemiringAction.eval_smul_charpoly`: the evaluation of a transformed
  characteristic polynomial is the product of the corresponding displacements.
-/

public section

open Polynomial

namespace TauCeti

namespace MulSemiringAction

variable {G H B : Type*} [Group G] [Group H] [Fintype H] [CommRing B]
  [MulSemiringAction G B] [MulSemiringAction H B]

/-- Evaluating a transformed characteristic polynomial gives a product of displacements,
when the action of `H` is the restriction of the action of `G` along a group homomorphism. -/
theorem eval_smul_charpoly (φ : H →* G) (hφ : ∀ (τ : H) (b : B), φ τ • b = τ • b)
    (σ : G) (b : B) :
    (σ • _root_.MulSemiringAction.charpoly H b).eval b =
      ∏ τ : H, (b - (σ * φ τ) • b) := by
  simp [_root_.MulSemiringAction.charpoly_eq, Finset.smul_prod', eval_prod,
    mul_smul, smul_sub, smul_C, hφ]

end MulSemiringAction

variable {G B : Type*} [Group G] [Fintype G] [CommRing B] [IsDomain B] [MulSemiringAction G B]

/-- The characteristic polynomial of a point with pairwise distinct translates divides every
polynomial vanishing on its orbit. -/
theorem MulSemiringAction.charpoly_dvd {b : B}
    (hb : Function.Injective fun g : G ↦ g • b) {f : B[X]}
    (hf : ∀ g : G, f.eval (g • b) = 0) : MulSemiringAction.charpoly G b ∣ f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact dvd_zero _
  have hprod : MulSemiringAction.charpoly G b =
      ((Finset.univ.val.map fun g : G ↦ g • b).map fun a ↦ X - C a).prod := by
    rw [MulSemiringAction.charpoly_eq, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots hf0,
    Multiset.le_iff_subset (Finset.univ.nodup.map hb)]
  intro a ha
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.1 ha
  exact (mem_roots hf0).2 (hf g)

end TauCeti
