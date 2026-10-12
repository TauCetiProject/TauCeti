/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
-- Private: the exhaustive degree filtration is used only to see that products of vectors span.
import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# Monomials of a spanning list span the Clifford algebra

Let `l` be a list of vectors spanning the quadratic module `M`. Each sublist `t` of `l` has an
ordered product `ι Q t₁ * ⋯ * ι Q tₖ` in `CliffordAlgebra Q`, the *monomial* of `t`, and the
monomials span the Clifford algebra as a module. Multiplying a monomial on the left by a member
`ι Q a` of the list either adjoins `a` or, after moving `ι Q a` past the earlier factors with the
Clifford relation `ι Q a * ι Q b = polar Q a b - ι Q b * ι Q a`, collapses `ι Q a * ι Q a` to the
scalar `Q a`, so the span of the monomials is stable under left multiplication by every member of
`l`, hence by every vector; it contains `1`, hence every product of vectors, and these exhaust the
Clifford algebra. No orthogonality is needed, and neither is a field or the invertibility of `2`.

This is the spanning half of the Clifford analogue of the Poincaré–Birkhoff–Witt theorem. The other
half, that the monomials of a basis are linearly independent, is not proved here: the low-rank
identifications of the Spin group sort an element along the monomials of each length of an
orthogonal basis and use only the spanning.

## Main results

* `CliffordAlgebra.ι_mul_mem_span_prod_map_ι_sublist`: for `a` a member of a list `l`, left
  multiplication by `ι Q a` preserves the span of the monomials of `l`.
* `CliffordAlgebra.span_prod_map_ι_sublist_eq_top`: the monomials of a spanning list span the
  Clifford algebra.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- Left multiplication by `ι Q b` sends the span of the monomials of `l` into the span of the
monomials of `b :: l`, each monomial of `l` going to a monomial of `b :: l`. -/
private theorem ι_mul_mem_span_prod_map_ι_sublist_cons (b : M) {l : List M} {z : CliffordAlgebra Q}
    (hz : z ∈ Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l})) :
    ι Q b * z ∈
      Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist (b :: l)}) := by
  refine Submodule.span_induction (p := fun z _ => ι Q b * z ∈ Submodule.span R
    ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist (b :: l)})) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨t, ht, rfl⟩
    exact Submodule.subset_span ⟨b :: t, ht.cons_cons b, by simp⟩
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro r x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

/-- **Left multiplication by a member of a list preserves the span of its monomials.** Adjoining
`ι Q a` to a monomial not containing `a` gives a monomial; if the monomial contains `a`, moving
`ι Q a` past the earlier factors with `ι Q a * ι Q b = polar Q a b - ι Q b * ι Q a` and collapsing
`ι Q a * ι Q a` to the scalar `Q a` gives a combination of shorter monomials. -/
theorem ι_mul_mem_span_prod_map_ι_sublist {l : List M} {a : M} (ha : a ∈ l) {z : CliffordAlgebra Q}
    (hz : z ∈ Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l})) :
    ι Q a * z ∈ Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l}) := by
  induction l generalizing z with
  | nil => exact absurd ha List.not_mem_nil
  | cons b l ih =>
    have hmono : Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l}) ≤
        Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist (b :: l)}) :=
      Submodule.span_mono (Set.image_mono fun t (ht : t.Sublist l) => ht.cons b)
    refine Submodule.span_induction (p := fun z _ => ι Q a * z ∈ Submodule.span R
      ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist (b :: l)})) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨t, ht, rfl⟩
      rcases List.sublist_cons_iff.mp ht with ht' | ⟨r, rfl, hr⟩
      · -- The monomial does not start with `b`.
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Submodule.subset_span ⟨a :: t, ht'.cons_cons a, by simp⟩
        · exact hmono (ih ha (Submodule.subset_span ⟨t, ht', rfl⟩))
      · -- The monomial is `ι Q b` times a monomial `ι Q r₁ * ⋯` of `l`.
        simp only [List.map_cons, List.prod_cons]
        have hr' : (r.map (ι Q)).prod ∈
            Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l}) :=
          Submodule.subset_span ⟨r, hr, rfl⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · rw [← mul_assoc, ι_sq_scalar, ← Algebra.smul_def]
          exact Submodule.smul_mem _ _ (hmono hr')
        · rw [← mul_assoc, ι_mul_ι_comm, sub_mul, ← Algebra.smul_def, mul_assoc]
          exact sub_mem (Submodule.smul_mem _ _ (hmono hr'))
            (ι_mul_mem_span_prod_map_ι_sublist_cons b (ih ha hr'))
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact add_mem hx hy
    · intro r x _ hx
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hx

/-- **The monomials of a spanning list span the Clifford algebra.** -/
theorem span_prod_map_ι_sublist_eq_top {l : List M}
    (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) :
    Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l}) = ⊤ := by
  set S := Submodule.span R ((fun t : List M => (t.map (ι Q)).prod) '' {t | t.Sublist l})
  -- `S` is stable under left multiplication by every vector, by linearity from the members of `l`.
  have hmul : ∀ v : M, ∀ z ∈ S, ι Q v * z ∈ S := by
    intro v
    have hv : v ∈ Submodule.span R {x : M | x ∈ l} := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun v _ => ∀ z ∈ S, ι Q v * z ∈ S) ?_ ?_ ?_ ?_ hv
    · intro a ha z hz
      exact ι_mul_mem_span_prod_map_ι_sublist ha hz
    · intro z _
      simp
    · intro v w _ _ hv hw z hz
      rw [map_add, add_mul]
      exact add_mem (hv z hz) (hw z hz)
    · intro r v _ hv z hz
      rw [map_smul, smul_mul_assoc]
      exact Submodule.smul_mem _ r (hv z hz)
  -- Every product of vectors lies in `S`, and these products exhaust the Clifford algebra.
  rw [eq_top_iff, ← iSup_filtration_eq_top Q]
  refine iSup_le fun k => (filtration_le_iff Q).2 fun w hw => ?_
  clear hw
  induction w with
  | nil => exact Submodule.subset_span ⟨[], List.nil_sublist l, by simp⟩
  | cons v w ih =>
    rw [List.map_cons, List.prod_cons]
    exact hmul v _ ih

end CliffordAlgebra
