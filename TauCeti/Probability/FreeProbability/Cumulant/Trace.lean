/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Submonoid.Membership
public import TauCeti.Probability.FreeProbability.Cumulant.Basic
import TauCeti.Probability.FreeProbability.Cumulant.Cyclic
import TauCeti.Probability.FreeProbability.Cumulant.Product

/-!
# Traces from cyclic cumulants

Cyclic invariance of all joint cumulants of a family is equivalent to traciality on the
submonoid it generates, or on the algebra it generates for a linear functional. The
moment–cumulant formula transfers cyclicity from cumulants to moments by rotating
noncrossing partitions. Neither direction requires positivity, normalization, or a trace
on the ambient algebra.

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
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β)
    (hκ : ∀ w : Fin #s → ι,
      freeCumulant φ (a ∘ w ∘ finRotate #s) univ = freeCumulant φ (a ∘ w) univ)
    (u : α → ι) (b : β → A) (h : (s.sort.map (a ∘ u)).IsRotated (t.sort.map b)) :
    freeCumulant φ (a ∘ u) s = freeCumulant φ b t := by
  have hp (w : Fin #s → ι) (k : ℕ) :
      freeCumulant φ (a ∘ w ∘ ⇑(finRotate #s ^ k)) univ =
        freeCumulant φ (a ∘ w) univ := by
    rw [Equiv.Perm.coe_pow]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ]
      exact (hκ (w ∘ (⇑(finRotate #s))^[k])).trans ih
  obtain ⟨k, hk⟩ := h
  rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ (a ∘ u) s,
    freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ b t,
    Function.comp_assoc, ← hp (u ∘ s.orderEmbOfFin rfl) k]
  apply freeCumulant_congr_of_ofFn_eq
  rw [← Function.comp_assoc, List.ofFn_comp_finRotate_pow]
  have hs := congrArg (List.map (a ∘ u)) (listMap_orderEmbOfFin_finRange s rfl)
  have ht := congrArg (List.map b) (listMap_orderEmbOfFin_finRange t rfl)
  rw [List.map_map, ← List.ofFn_eq_map] at hs ht
  rw [← Function.comp_assoc a u, hs, ht]
  exact hk

/-- Cyclic joint cumulants give cyclic word moments. -/
theorem apply_prod_ofFn_comp_finRotate_of_freeCumulant_comp_finRotate {n : ℕ}
    (hκ : ∀ m ≤ n, ∀ w : Fin m → ι,
      freeCumulant φ (a ∘ w ∘ finRotate m) univ = freeCumulant φ (a ∘ w) univ)
    (w : Fin n → ι) :
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
      exact freeCumulant_eq_of_isRotated_sort B (B.map (finRotate n).toEmbedding)
        (hκ #B (by simpa using card_le_card (subset_univ B))) (w ∘ finRotate n) (a ∘ w)
        (by simpa only [List.map_map, Function.comp_assoc] using
          B.isRotated_sort_map_finRotate.map (a ∘ w))
    _ = ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        ∏ B ∈ π.1.parts, freeCumulant φ (a ∘ w) B :=
      (NoncrossingPartition.rotate n).toEquiv.sum_comp
        (fun π => ∏ B ∈ π.1.parts, freeCumulant φ (a ∘ w) B)
    _ = _ := (apply_prod_ofFn_eq_sum_prod_freeCumulant φ hn (a ∘ w)).symm

/-- Cyclic joint cumulants give equal moments of any two cyclic rotations of a word,
including the empty word. -/
theorem apply_prod_map_rotate_of_freeCumulant_comp_finRotate (w : List ι)
    (hκ : ∀ m ≤ w.length, ∀ u : Fin m → ι,
      freeCumulant φ (a ∘ u ∘ finRotate m) univ = freeCumulant φ (a ∘ u) univ)
    (k : ℕ) : φ ((w.rotate k).map a).prod = φ (w.map a).prod := by
  have hstep (v : List ι) (hv : v.length = w.length) :
      φ ((v.rotate 1).map a).prod = φ (v.map a).prod := by
    have h := apply_prod_ofFn_comp_finRotate_of_freeCumulant_comp_finRotate
      (fun m hm => hκ m (hv ▸ hm)) v.get
    have he : (finRotate v.length ^ 1 : Equiv.Perm (Fin v.length)) = finRotate v.length :=
      pow_one _
    rw [← he, ← Function.comp_assoc, List.ofFn_comp_finRotate_pow] at h
    simpa [← List.map_ofFn] using h
  induction k with
  | zero => simp
  | succ k ih => rw [← List.rotate_rotate, hstep _ (by simp), ih]

/-- A trace on a submonoid has cyclic free cumulants on words in that submonoid. -/
theorem freeCumulant_comp_finRotate_of_apply_mul_comm {S : Submonoid A}
    (hφ : ∀ x ∈ S, ∀ y ∈ S, φ (x * y) = φ (y * x))
    {n : ℕ} {w : Fin n → A} (hw : ∀ i, w i ∈ S) :
    freeCumulant φ (w ∘ finRotate n) univ = freeCumulant φ w univ := by
  let v (i : Fin n) : S := ⟨w i, hw i⟩
  have htr (x y : S) :
      (φ ∘ S.subtype) (x * y) = (φ ∘ S.subtype) (y * x) := by
    simpa only [Function.comp_apply, map_mul, Submonoid.subtype_apply] using
      hφ x x.property y y.property
  have h := freeCumulant_comp_finRotate htr v
  rw [freeCumulant_comp_mulHom, freeCumulant_comp_mulHom] at h
  simpa only [Function.comp_def, Submonoid.subtype_apply, v, Subtype.coe_mk] using h

/-- Cyclic joint cumulants make the functional tracial on the submonoid of words in the
specified generators. -/
theorem apply_mul_comm_of_freeCumulant_comp_finRotate_of_mem_closure
    (hκ : ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ)
    {x y : A} (hx : x ∈ Submonoid.closure (Set.range a))
    (hy : y ∈ Submonoid.closure (Set.range a)) : φ (x * y) = φ (y * x) := by
  rw [← FreeMonoid.mrange_lift] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h := apply_prod_map_rotate_of_freeCumulant_comp_finRotate (u.toList ++ v.toList)
    (fun m _ => hκ m) u.toList.length
  simpa [FreeMonoid.lift_apply, List.rotate_append_length_eq] using h.symm

/-- Traciality on the submonoid generated by a family is equivalent to cyclic invariance of
its joint cumulants. -/
theorem forall_apply_mul_comm_mem_closure_iff_freeCumulant_comp_finRotate :
    (∀ x ∈ Submonoid.closure (Set.range a), ∀ y ∈ Submonoid.closure (Set.range a),
      φ (x * y) = φ (y * x)) ↔
    ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ :=
  ⟨fun h _ w => freeCumulant_comp_finRotate_of_apply_mul_comm h
    (fun i => Submonoid.subset_closure (Set.mem_range_self (w i))),
    fun h _ hx _ hy => apply_mul_comm_of_freeCumulant_comp_finRotate_of_mem_closure h hx hy⟩

end Monoid

section Algebra

variable {R A ι : Type*} [CommRing R] [Semiring A] [Algebra R A]
  {φ : A →ₗ[R] R} {a : ι → A}

/-- A functional whose joint cumulants on a family are cyclic is tracial on the unital
algebra generated by that family. -/
theorem apply_mul_comm_of_freeCumulant_comp_finRotate_of_mem_adjoin
    (hκ : ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ)
    {x y : A} (hx : x ∈ Algebra.adjoin R (Set.range a))
    (hy : y ∈ Algebra.adjoin R (Set.range a)) : φ (x * y) = φ (y * x) := by
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at hx hy
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    exact apply_mul_comm_of_freeCumulant_comp_finRotate_of_mem_closure hκ hx hy
  | zero_left => simp
  | zero_right => simp
  | add_left x y z _ _ _ hx hy => simp [mul_add, add_mul, hx, hy]
  | add_right x y z _ _ _ hy hz => simp [mul_add, add_mul, hy, hz]
  | smul_left r x y _ _ hx => simp [hx]
  | smul_right r x y _ _ hy => simp [hy]

/-- A linear functional is tracial on the algebra generated by a family if and only if
its joint cumulants are cyclically invariant. -/
theorem forall_apply_mul_comm_mem_adjoin_iff_freeCumulant_comp_finRotate :
    (∀ x ∈ Algebra.adjoin R (Set.range a), ∀ y ∈ Algebra.adjoin R (Set.range a),
      φ (x * y) = φ (y * x)) ↔
    ∀ (n : ℕ) (w : Fin n → ι),
      freeCumulant φ (a ∘ w ∘ finRotate n) univ = freeCumulant φ (a ∘ w) univ := by
  have hle : Submonoid.closure (Set.range a) ≤ (Algebra.adjoin R (Set.range a)).toSubmonoid :=
    Submonoid.closure_le.mpr Algebra.subset_adjoin
  exact ⟨fun h => forall_apply_mul_comm_mem_closure_iff_freeCumulant_comp_finRotate.mp
      (fun x hx y hy => h x (hle hx) y (hle hy)),
    fun h _ hx _ hy => apply_mul_comm_of_freeCumulant_comp_finRotate_of_mem_adjoin h hx hy⟩

end Algebra

end TauCeti
