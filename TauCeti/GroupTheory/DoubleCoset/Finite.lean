/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index

/-!
# Finiteness of the double-coset quotient

A double coset `HgK` is a union of left cosets of `K`, so the double cosets `H \ G / K` are a
quotient of `G ⧸ K`: the map `gK ↦ HgK` is well defined and surjective
(`TauCeti.doubleCosetMk_out_mk` is the well-definedness, in the form the surjection uses).
Consequently `H \ G / K` is finite as soon as `K` has finite index, with no finiteness assumption
on `G` itself.

This is the instance that lets a sum be taken over `H \ G / K`; the Mackey decomposition
(`TauCeti.RepresentationTheory.Induction.Mackey.Basic`) is its first consumer, where the index of
the subgroup being induced from is the only finiteness available.

A sum over `H \ G / K` of values at chosen representatives often comes with a proof that it does
not depend on the choice; `TauCeti.eq_of_sum_doubleCoset_rep_eq` extracts from this that each
value depends only on its double coset.

## Main statements

* `TauCeti.finite_doubleCosetQuotient`: `H \ G / K` is finite when `K` has finite index in `G`.
* `TauCeti.eq_of_sum_doubleCoset_rep_eq`: a value whose sum over double-coset representatives is
  independent of the representatives is itself constant on double cosets.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- Replacing an element by the chosen representative of its left `K`-coset does not change its
double coset. -/
theorem doubleCosetMk_out_mk (H K : Subgroup G) (g : G) :
    DoubleCoset.mk H K (Quotient.out (QuotientGroup.mk g : G ⧸ K)) = DoubleCoset.mk H K g := by
  have hmem : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g))
  rw [DoubleCoset.eq]
  exact ⟨1, H.one_mem, _, hmem, by simp⟩

/-- **The double cosets `H \ G / K` are finite when `K` has finite index**: they are the image of
the finite set `G ⧸ K` under `gK ↦ HgK`. -/
instance finite_doubleCosetQuotient (H K : Subgroup G) [K.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_surjective (fun t : G ⧸ K => DoubleCoset.mk H K t.out) fun d =>
    ⟨QuotientGroup.mk d.out, (doubleCosetMk_out_mk H K d.out).trans (DoubleCoset.out_eq' d)⟩

/-- **A value at a double-coset representative is determined by its double coset if the sum is**:
if the sum over `H \ G / K` of the values of `T` at representatives does not depend on the
choice of representatives, then `T s = T s'` whenever `s` and `s'` lie in the same double coset.
Comparing the canonical choice `Quotient.out` with the ones that replace the representative of a
single double coset by `s`, resp. `s'`, leaves only the terms at `s` and `s'`. -/
theorem eq_of_sum_doubleCoset_rep_eq {A : Type*} [AddCancelCommMonoid A] (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] (T : G → A)
    (hT : ∀ r : DoubleCoset.Quotient (H : Set G) (K : Set G) → G,
      (∀ D, DoubleCoset.mk H K (r D) = D) →
        ∑ D, T (r D) = ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G), T D.out)
    {s s' : G} (h : DoubleCoset.mk H K s = DoubleCoset.mk H K s') : T s = T s' := by
  classical
  have key (t : G) (ht : DoubleCoset.mk H K t = DoubleCoset.mk H K s) :
      T t + ∑ D ∈ {DoubleCoset.mk H K s}ᶜ, T (Quotient.out D) =
        ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G), T D.out := by
    have hr (D : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
        DoubleCoset.mk H K (Function.update
          (fun D' : DoubleCoset.Quotient (H : Set G) (K : Set G) => D'.out)
          (DoubleCoset.mk H K s) t D) = D := by
      rcases eq_or_ne D (DoubleCoset.mk H K s) with rfl | hD
      · rw [Function.update_self, ht]
      · rw [Function.update_of_ne hD]
        exact DoubleCoset.out_eq' D
    rw [← hT _ hr, Fintype.sum_eq_add_sum_compl (DoubleCoset.mk H K s), Function.update_self]
    refine congrArg (T t + ·) (Finset.sum_congr rfl fun D hD => ?_)
    rw [Function.update_of_ne fun hD' => Finset.mem_compl.mp hD (Finset.mem_singleton.mpr hD')]
  exact add_right_cancel ((key s rfl).trans (key s' h.symm).symm)

end TauCeti
