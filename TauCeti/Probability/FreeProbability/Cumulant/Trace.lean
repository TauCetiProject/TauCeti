/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Submonoid.Membership
public import TauCeti.Probability.FreeProbability.Cumulant.Cyclic
import TauCeti.Probability.FreeProbability.Cumulant.Product

/-!
# Traces from cyclic cumulants

Cyclic invariance of all joint cumulants of a family implies traciality on the algebra it
generates. The moment–cumulant formula transfers cyclicity from cumulants to moments by
rotating noncrossing partitions. Only cyclicity on words in the specified generators is
needed; no positivity, normalization, or trace on the ambient algebra is assumed.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 11.
-/

public section

open Finset

namespace TauCeti

section Monoid

variable {R A ι : Type*} [CommRing R] [Monoid A] {φ : A → R} {a : ι → A}

/-- Cyclicity of joint cumulants identifies the cumulants of any two cyclically rotated
subwords, each read in increasing order of its positions. -/
theorem freeCumulant_eq_of_isRotated_sort
    (hκ : ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ)
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β) (u : α → ι) (v : β → ι)
    (h : (s.sort.map u).IsRotated (t.sort.map v)) :
    freeCumulant φ (a ∘ u) s = freeCumulant φ (a ∘ v) t := by
  have hp (n : ℕ) (w : Fin n → ι) (k : ℕ) :
      freeCumulant φ (a ∘ w ∘ ⇑(finRotate n ^ k)) univ =
        freeCumulant φ (a ∘ w) univ := by
    rw [Equiv.Perm.coe_pow]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ]
      exact (hκ n (w ∘ (⇑(finRotate n))^[k])).trans ih
  obtain ⟨k, hk⟩ := h
  rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ (a ∘ u) s,
    freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ (a ∘ v) t]
  simp only [Function.comp_assoc]
  rw [← hp #s (u ∘ s.orderEmbOfFin rfl) k]
  apply freeCumulant_congr_of_ofFn_eq
  rw [← Function.comp_assoc, List.ofFn_comp_finRotate_pow]
  have hs := congrArg (List.map (a ∘ u)) (listMap_orderEmbOfFin_finRange s rfl)
  have ht := congrArg (List.map (a ∘ v)) (listMap_orderEmbOfFin_finRange t rfl)
  rw [List.map_map, ← List.ofFn_eq_map] at hs ht
  rw [← Function.comp_assoc a u, ← Function.comp_assoc a v, hs, ht]
  simpa only [List.map_rotate, List.map_map] using congrArg (List.map a) hk

/-- Cyclic joint cumulants give cyclic word moments. -/
theorem apply_prod_ofFn_comp_finRotate_of_freeCumulant
    (hκ : ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ)
    {n : ℕ} (w : Fin n → ι) :
    φ (List.ofFn (a ∘ w ∘ finRotate n)).prod = φ (List.ofFn (a ∘ w)).prod := by
  by_cases hn : n = 0
  · subst n
    simp
  calc
    _ = ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        ∏ B ∈ π.1.parts, freeCumulant φ (a ∘ w ∘ finRotate n) B :=
      apply_prod_ofFn_eq_sum_prod_freeCumulant φ hn _
    _ = ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        ∏ B ∈ (NoncrossingPartition.rotate n π).1.parts, freeCumulant φ (a ∘ w) B := by
      apply sum_congr rfl
      intro π _
      rw [NoncrossingPartition.prod_parts_rotate π (freeCumulant φ (a ∘ w))]
      apply prod_congr rfl
      intro B _
      exact freeCumulant_eq_of_isRotated_sort (φ := φ) (a := a) hκ B
        (B.map (finRotate n).toEmbedding) (w ∘ finRotate n) w
        (by simpa only [List.map_map] using B.isRotated_sort_map_finRotate.map w)
    _ = ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        ∏ B ∈ π.1.parts, freeCumulant φ (a ∘ w) B :=
      (NoncrossingPartition.rotate n).toEquiv.sum_comp
        (fun π => ∏ B ∈ π.1.parts, freeCumulant φ (a ∘ w) B)
    _ = _ := (apply_prod_ofFn_eq_sum_prod_freeCumulant φ hn (a ∘ w)).symm

/-- Cyclic joint cumulants give equal moments of any two cyclic rotations of a word,
including the empty word. -/
theorem apply_prod_map_rotate_of_freeCumulant
    (hκ : ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ)
    (w : List ι) (k : ℕ) :
    φ ((w.rotate k).map a).prod = φ (w.map a).prod := by
  have hstep (v : List ι) : φ ((v.rotate 1).map a).prod = φ (v.map a).prod := by
    have h := apply_prod_ofFn_comp_finRotate_of_freeCumulant hκ v.get
    have he : (finRotate v.length ^ 1 : Equiv.Perm (Fin v.length)) = finRotate v.length :=
      pow_one _
    rw [← he, ← Function.comp_assoc, List.ofFn_comp_finRotate_pow] at h
    simpa [← List.map_ofFn] using h
  induction k with
  | zero => simp
  | succ k ih => rw [← List.rotate_rotate, hstep, ih]

end Monoid

section Algebra

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A]
  {φ : A →ₗ[R] R} {a : ι → A}

/-- A functional whose joint cumulants on a family are cyclic is tracial on the unital
algebra generated by that family. -/
theorem apply_mul_comm_of_mem_adjoin_of_freeCumulant
    (hκ : ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ)
    {x y : A} (hx : x ∈ Algebra.adjoin R (Set.range a))
    (hy : y ∈ Algebra.adjoin R (Set.range a)) : φ (x * y) = φ (y * x) := by
  have hwords (u v : List ι) :
      φ ((u.map a).prod * (v.map a).prod) = φ ((v.map a).prod * (u.map a).prod) := by
    have h := apply_prod_map_rotate_of_freeCumulant hκ (u ++ v) u.length
    simpa [List.rotate_append_length_eq] using h.symm
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at hx hy
  have hG : ∀ x ∈ Submonoid.closure (Set.range a),
      ∀ y ∈ Submonoid.closure (Set.range a), φ (x * y) = φ (y * x) := by
    intro x hx y hy
    rw [← FreeMonoid.mrange_lift] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    simpa [FreeMonoid.lift_apply] using hwords u.toList v.toList
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact hG x hx y hy
  | zero_left => simp
  | zero_right => simp
  | add_left x y z _ _ _ hx hy => simp [mul_add, add_mul, hx, hy]
  | add_right x y z _ _ _ hy hz => simp [mul_add, add_mul, hy, hz]
  | smul_left r x y _ _ hx => simp [hx]
  | smul_right r x y _ _ hy => simp [hy]

end Algebra

end TauCeti
