/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import TauCeti.RingTheory.Huber.Pair.Invariant
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.RingTheory.Huber.Prod

/-!
# Tests: the invariant Huber pair

Two families of tests for `TauCeti.Huber.invariantPair` and the orbit product.

For an action fixing every element, the invariant ring is all of `A`, the invariant pair has plus
ring `A⁺`, and the orbit product of `a` is `a ^ #G`. In characteristic `p` with `#G = p`, the
trace `∑ g, g • a = p • a` vanishes identically although every element is invariant, so the
invariant ring is not the image of an averaging operator when `p` divides the group order.

For the swap of the factors of `K × K`, the invariant ring is the diagonal copy of `K`, the
orbit product of the diagonal element `(ϖ, ϖ)` is `(ϖ², ϖ²)`, and for the pair with plus ring
`(K × K)°` an invariant element `(a, a)` lies in the invariant plus ring exactly when `a ∈ K°`.
-/

public section

open TauCeti TauCeti.Huber

namespace TauCeti.Examples.InvariantPair

section TrivialAction

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A]

/-- For an action fixing every element, every element is invariant. -/
example (h : ∀ (g : G) (a : A), g • a = a) : FixedPoints.subring A G = ⊤ :=
  eq_top_iff.mpr fun a _ g ↦ h g a

/-- For an action fixing every element, the invariant plus ring is `A⁺`. -/
example [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [Finite G]
    [ContinuousConstSMul G A] (h : ∀ (g : G) (a : A), g • a = a) (P : Pair A) :
    (invariantPair G P).plus.map (FixedPoints.subring A G).subtype = P.plus := by
  rw [map_subtype_invariantPair_plus, inf_eq_left]
  exact fun a _ g ↦ h g a

/-- For an action fixing every element, the orbit product of `a` is `a ^ #G`. -/
example [Fintype G] (h : ∀ (g : G) (a : A), g • a = a) (a : A) :
    orbitProd G a = a ^ Fintype.card G :=
  orbitProd_eq_pow_card G (h · a)

/-- For the one-element group, the orbit product of `a` is `a`. -/
example [Fintype G] [Subsingleton G] (a : A) : orbitProd G a = a := by
  rw [orbitProd_def, Fintype.prod_subsingleton _ 1, one_smul]

/-- In characteristic `p`, for a group of order `p` acting by fixing every element, the trace
vanishes although every element is invariant. -/
example {p : ℕ} [CharP A p] [Fintype G] (hG : Fintype.card G = p)
    (h : ∀ (g : G) (a : A), g • a = a) (a : A) : ∑ g : G, g • a = 0 := by
  simp [h, hG]

/-- The orbit products of `0` and `1` are `0` and `1`. -/
example [Fintype G] : orbitProd G (0 : A) = 0 ∧ orbitProd G (1 : A) = 1 :=
  ⟨orbitProd_zero G, orbitProd_one G⟩

end TrivialAction

section Swap

variable {K : Type*} [CommRing K]

/-- The automorphism of `K × K` swapping the factors. -/
abbrev swap : RingAut (K × K) :=
  RingEquiv.prodComm

theorem swap_apply (x : K × K) : swap x = (x.2, x.1) :=
  (rfl)

theorem swap_sq : (swap (K := K)) ^ 2 = 1 :=
  RingEquiv.ext fun _ ↦ rfl

/-- The group `{1, swap}` acting on `K × K`. -/
abbrev Swap (K : Type*) [CommRing K] : Subgroup (RingAut (K × K)) :=
  Subgroup.zpowers swap

theorem mem_swap {g : RingAut (K × K)} (hg : g ∈ Swap K) : g = 1 ∨ g = swap :=
  (Subgroup.mem_zpowers_iff_of_sq_eq_one swap_sq).mp hg

instance : Finite (Swap K) :=
  Set.Finite.to_subtype <| (Set.toFinite {1, swap}).subset fun _ hg ↦ mem_swap hg

/-- The invariant ring of the swap is the diagonal. -/
theorem mem_fixedPoints_swap {x : K × K} :
    x ∈ FixedPoints.subring (K × K) (Swap K) ↔ x.1 = x.2 := by
  refine ⟨fun hx ↦ ?_, fun hx g ↦ ?_⟩
  · simpa [swap_apply] using (Prod.ext_iff.mp (hx ⟨swap, Subgroup.mem_zpowers _⟩)).2
  · rcases mem_swap g.property with h | h
    · simp [Subgroup.smul_def, h]
    · simp [Subgroup.smul_def, h, swap_apply, Prod.ext_iff, hx]

/-- The orbit product of the diagonal element `(a, a)` under the swap is `(a², a²)`. -/
theorem orbitProd_swap_diagonal [Nontrivial K] [Fintype (Swap K)] (a : K) :
    orbitProd (Swap K) (a, a) = (a ^ 2, a ^ 2) := by
  have hcard : Fintype.card (Swap K) = 2 := by
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers]
    refine orderOf_eq_prime swap_sq fun h ↦ ?_
    simpa [swap_apply] using congr_arg Prod.fst (RingEquiv.ext_iff.mp h (1, 0))
  rw [orbitProd_eq_pow_card _ fun g ↦ (mem_fixedPoints_swap.mpr rfl :
    (a, a) ∈ FixedPoints.subring (K × K) (Swap K)) g, hcard, Prod.pow_mk]

variable [TopologicalSpace K] [IsTopologicalRing K] [IsTateRing K]

instance : ContinuousConstSMul (Swap K) (K × K) where
  continuous_const_smul g := by
    rcases mem_swap g.property with h | h
    · exact (funext fun x ↦ by simp [Subgroup.smul_def, h] : (g • · : K × K → K × K) = id) ▸
        continuous_id
    · exact (funext fun x ↦ by simp [Subgroup.smul_def, h, swap_apply, Prod.swap] :
        (g • · : K × K → K × K) = Prod.swap) ▸ continuous_swap

/-- For the pair `(K × K, (K × K)°)`, an invariant element `(a, a)` lies in the invariant plus ring
exactly when `a` is power-bounded. -/
example (a : K) :
    (⟨(a, a), mem_fixedPoints_swap.mpr rfl⟩ : FixedPoints.subring (K × K) (Swap K)) ∈
      (invariantPair (Swap K) (Pair.powerBounded (K × K))).plus ↔ IsPowerBounded a := by
  rw [mem_invariantPair_plus, Pair.powerBounded_plus, mem_powerBoundedSubring,
    isPowerBounded_prod_iff, and_self]

end Swap

end TauCeti.Examples.InvariantPair
