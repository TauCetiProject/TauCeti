/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The ordered-product basis of a Clifford algebra

Let `b` be a basis of `M`, indexed by a linearly ordered type `I`, and let `Q` be a quadratic form
on `M` over a ring in which `2` is invertible. Transporting Mathlib's exterior basis
`Module.Basis.ExteriorAlgebra`, indexed by finite sets of indices, along the module isomorphism
`CliffordAlgebra.equivExterior` gives a basis `Module.Basis.cliffordAlgebra` of
`CliffordAlgebra Q`. When `b` is orthogonal for `Q` its member at `s` is the ordered product
`e_s = ι Q (b i₁) * ⋯ * ι Q (b iₖ)` over the elements `i₁ < ⋯ < iₖ` of `s`
(`Module.Basis.cliffordAlgebra_apply`). The form may be degenerate.

For an orthogonal basis the scalar part `τ = CliffordAlgebra.scalarTrace Q` pairs these monomials
diagonally:

  `τ (reverse e_s * e_t) = if s = t then ∏ i ∈ s, Q (b i) else 0`.

So the coordinates of `x` in this basis are read off by `τ`, and the form
`(x, y) ↦ τ (reverse x * y)` is diagonal in it, with weight `∏ i ∈ s, Q (b i)` at `s`. Over an
ordered ring, if every `Q (b i)` is nonnegative then `τ (reverse x * x) ≥ 0`, and if every
`Q (b i)` is positive then `τ (reverse x * x) = 0` only for `x = 0`.

## Main definitions

* `Module.Basis.cliffordAlgebra`: the basis of `CliffordAlgebra Q` transported from the exterior
  basis along `CliffordAlgebra.equivExterior`.

## Main results

* `Module.Basis.cliffordAlgebra_apply`: for an orthogonal basis, its members are the ordered
  products of basis vectors.
* `Module.Basis.cliffordAlgebra_repr_empty`: the coefficient of `1` is the scalar part.
* `CliffordAlgebra.scalarTrace_reverse_prod_mul_prod`: the scalar part pairs the ordered products
  of an orthogonal family diagonally, and `Module.Basis.scalarTrace_reverse_cliffordAlgebra_mul`
  is the basis form.
* `Module.Basis.prod_mul_cliffordAlgebra_repr`: `(∏ i ∈ s, Q (b i)) * xₛ = τ (reverse e_s * x)`.
* `Module.Basis.scalarTrace_reverse_mul`: `τ (reverse x * y) = ∑ₛ (∏ i ∈ s, Q (b i)) * xₛ * yₛ`.
* `Module.Basis.scalarTrace_reverse_mul_self_nonneg` and
  `Module.Basis.scalarTrace_reverse_mul_self_eq_zero_iff`: positivity and faithfulness.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} {I : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)] {Q : QuadraticForm R M} {v : I → M}

/-- The scalar part kills `ι Q (v i)` times the ordered product of `v` along a list of indices
different from `i`. -/
private theorem scalarTrace_ι_mul_prod_map_eq_zero
    (hv : Pairwise fun i j => Q.IsOrtho (v i) (v j)) {i : I} {l : List I} (h : ∀ k ∈ l, k ≠ i) :
    scalarTrace Q (ι Q (v i) * ((l.map v).map (ι Q)).prod) = 0 :=
  scalarTrace_ι_mul_prod_map_ι_eq_zero fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact hv (h k hk)

variable [LinearOrder I]

/-- The scalar-part pairing of the ordered products of an orthogonal family along two strictly
increasing lists of indices. The heads of the two lists are compared: equal heads cancel to
`Q (v i)`, and otherwise the smaller head moves, by cyclicity, to the front of a product of
vectors with larger indices, where `scalarTrace_ι_mul_prod_map_eq_zero` kills it. -/
private theorem scalarTrace_reverse_prod_mul_prod_of_pairwise_lt
    (hv : Pairwise fun i j => Q.IsOrtho (v i) (v j)) :
    ∀ {l₁ l₂ : List I}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      scalarTrace Q (reverse ((l₁.map v).map (ι Q)).prod * ((l₂.map v).map (ι Q)).prod) =
        if l₁ = l₂ then (l₁.map (Q ∘ v)).prod else 0
  | [], [], _, _ => by simp
  | [], j :: l₂, _, h₂ => by
    simp only [List.map_nil, List.prod_nil, reverse.map_one, one_mul, List.map_cons,
      List.prod_cons, reduceCtorEq, ↓reduceIte]
    exact scalarTrace_ι_mul_prod_map_eq_zero hv fun k hk => (List.rel_of_pairwise_cons h₂ hk).ne'
  | i :: l₁, [], h₁, _ => by
    simp only [List.map_nil, List.prod_nil, mul_one, scalarTrace_reverse, List.map_cons,
      List.prod_cons, reduceCtorEq, ↓reduceIte]
    exact scalarTrace_ι_mul_prod_map_eq_zero hv fun k hk => (List.rel_of_pairwise_cons h₁ hk).ne'
  | i :: l₁, j :: l₂, h₁, h₂ => by
    obtain ⟨hi, hl₁⟩ := List.pairwise_cons.mp h₁
    obtain ⟨hj, hl₂⟩ := List.pairwise_cons.mp h₂
    have hrev : reverse (((i :: l₁).map v).map (ι Q)).prod =
        ((l₁.reverse.map v).map (ι Q)).prod * ι Q (v i) := by
      rw [reverse_prod_map_ι]
      simp
    rw [hrev]
    rcases lt_trichotomy i j with hij | rfl | hji
    · -- `ι Q (v i)` moves, by cyclicity, to the front of a product of vectors with larger indices.
      have h : ((l₁.reverse.map v).map (ι Q)).prod * ι Q (v i) *
            (((j :: l₂).map v).map (ι Q)).prod =
          ((l₁.reverse.map v).map (ι Q)).prod *
            (ι Q (v i) * (((j :: l₂).map v).map (ι Q)).prod) :=
        mul_assoc _ _ _
      have h' : (((j :: l₂).map v).map (ι Q)).prod * ((l₁.reverse.map v).map (ι Q)).prod =
          (((j :: l₂ ++ l₁.reverse).map v).map (ι Q)).prod := by
        simp [mul_assoc]
      rw [h, scalarTrace_mul_comm, mul_assoc, h', ite_eq_right fun h => hij.ne (List.cons.inj h).1]
      refine scalarTrace_ι_mul_prod_map_eq_zero hv fun k hk => ?_
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at hk
      rcases hk with rfl | hk | hk
      exacts [hij.ne', (hij.trans (hj k hk)).ne', (hi k hk).ne']
    · -- Equal heads cancel to the scalar `Q (v i)`.
      have h : ((l₁.reverse.map v).map (ι Q)).prod * ι Q (v i) *
            (((i :: l₂).map v).map (ι Q)).prod =
          Q (v i) • (reverse ((l₁.map v).map (ι Q)).prod * ((l₂.map v).map (ι Q)).prod) := by
        rw [reverse_prod_map_ι]
        simp [mul_assoc, ← mul_assoc (ι Q (v i)), Algebra.smul_def, Algebra.commutes]
      rw [h, map_smul, scalarTrace_reverse_prod_mul_prod_of_pairwise_lt hv hl₁ hl₂, smul_eq_mul]
      simp only [List.cons.injEq, true_and, List.map_cons, List.prod_cons, Function.comp_apply]
      split_ifs <;> simp
    · -- `ι Q (v j)` moves, by cyclicity, to the front of a product of vectors with larger indices.
      have h : ((l₁.reverse.map v).map (ι Q)).prod * ι Q (v i) *
            (((j :: l₂).map v).map (ι Q)).prod =
          ((l₁.reverse.map v).map (ι Q)).prod * ι Q (v i) *
            (ι Q (v j) * ((l₂.map v).map (ι Q)).prod) := by
        simp
      have h' : ((l₂.map v).map (ι Q)).prod * (((l₁.reverse.map v).map (ι Q)).prod * ι Q (v i)) =
          (((l₂ ++ (l₁.reverse ++ [i])).map v).map (ι Q)).prod := by
        simp
      rw [h, scalarTrace_mul_comm, mul_assoc, h', ite_eq_right fun h => hji.ne' (List.cons.inj h).1]
      refine scalarTrace_ι_mul_prod_map_eq_zero hv fun k hk => ?_
      simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hk
      rcases hk with hk | hk | rfl
      exacts [(hj k hk).ne', (hji.trans (hi k hk)).ne', hji.ne']

/-- **The scalar part pairs the ordered products of an orthogonal family diagonally.** For
`v : I → M` pairwise orthogonal and finite sets `s` and `t` of indices, with products taken in
increasing order of the indices, `τ (reverse v_s * v_t)` is `∏ i ∈ s, Q (v i)` if `s = t` and `0`
otherwise. -/
theorem scalarTrace_reverse_prod_mul_prod (hv : Pairwise fun i j => Q.IsOrtho (v i) (v j))
    (s t : Finset I) :
    scalarTrace Q (reverse ((s.sort.map v).map (ι Q)).prod * ((t.sort.map v).map (ι Q)).prod) =
      if s = t then ∏ i ∈ s, Q (v i) else 0 := by
  rw [scalarTrace_reverse_prod_mul_prod_of_pairwise_lt hv
    (List.sortedLT_iff_pairwise.mp s.sortedLT_sort) (List.sortedLT_iff_pairwise.mp t.sortedLT_sort)]
  by_cases hst : s = t
  · subst hst
    rw [ite_eq_left rfl, ite_eq_left rfl, ← s.prod_map_toList]
    exact ((s.sort_perm_toList (· ≤ ·)).map _).prod_eq
  · have hsort : s.sort ≠ t.sort := fun h => hst (by
      rw [← s.sort_toFinset (· ≤ ·), h, t.sort_toFinset])
    rw [ite_eq_right hsort, ite_eq_right hst]

end CliffordAlgebra

namespace Module.Basis

open CliffordAlgebra

variable {R : Type u} {M : Type v} {I : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)] [LinearOrder I] (b : Basis I R M) (Q : QuadraticForm R M)

/-- The basis of `CliffordAlgebra Q` indexed by finite sets of indices, transported from the
exterior basis `Module.Basis.ExteriorAlgebra` along `CliffordAlgebra.equivExterior`. When `b` is
orthogonal for `Q`, its member at `s` is the product of the generators `ι Q (b i)`, `i ∈ s`, in
increasing order of the indices (`Module.Basis.cliffordAlgebra_apply`). -/
noncomputable def cliffordAlgebra : Basis (Finset I) R (CliffordAlgebra Q) :=
  b.ExteriorAlgebra.map (equivExterior Q).symm

/-- `CliffordAlgebra.equivExterior` sends `b.cliffordAlgebra Q` to the exterior basis.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`. -/
theorem equivExterior_cliffordAlgebra (s : Finset I) :
    equivExterior Q (b.cliffordAlgebra Q s) = b.ExteriorAlgebra s := by
  rw [cliffordAlgebra, map_apply, LinearEquiv.apply_symm_apply]

/-- **The ordered-product basis.** For a basis orthogonal for `Q`, the member of
`b.cliffordAlgebra Q` at `s` is the product of the generators `ι Q (b i)`, `i ∈ s`, in increasing
order of the indices. -/
theorem cliffordAlgebra_apply (hb : Pairwise fun i j => Q.IsOrtho (b i) (b j)) (s : Finset I) :
    b.cliffordAlgebra Q s = ((s.sort.map b).map (ι Q)).prod := by
  apply (equivExterior Q).injective
  rw [equivExterior_cliffordAlgebra, TauCeti.ExteriorAlgebra.basis_eq_prod_map_sort,
    equivExterior_prod_map_ι]
  exact List.pairwise_map.mpr ((List.sortedLT_iff_pairwise.mp s.sortedLT_sort).imp fun h =>
    hb h.ne)

/-- The member of `b.cliffordAlgebra Q` at the empty set is `1`. -/
@[simp]
theorem cliffordAlgebra_empty : b.cliffordAlgebra Q ∅ = 1 := by
  apply (equivExterior Q).injective
  rw [equivExterior_cliffordAlgebra, TauCeti.ExteriorAlgebra.basis_eq_prod_map_sort]
  simp [equivExterior]

/-- The member of `b.cliffordAlgebra Q` at `{i}` is the generator `ι Q (b i)`. -/
@[simp]
theorem cliffordAlgebra_singleton (i : I) : b.cliffordAlgebra Q {i} = ι Q (b i) := by
  apply (equivExterior Q).injective
  rw [equivExterior_cliffordAlgebra, TauCeti.ExteriorAlgebra.basis_singleton]
  simp [equivExterior]

/-- The scalar part of the member of `b.cliffordAlgebra Q` at `s` is `1` if `s` is empty and `0`
otherwise. -/
@[simp]
theorem scalarTrace_cliffordAlgebra (s : Finset I) :
    scalarTrace Q (b.cliffordAlgebra Q s) = if s = ∅ then 1 else 0 := by
  rw [scalarTrace_apply, equivExterior_cliffordAlgebra, ExteriorAlgebra.algebraMapInv_basis]

/-- The coefficient of `1` in the basis `b.cliffordAlgebra Q` is the scalar part. -/
@[simp]
theorem cliffordAlgebra_repr_empty (x : CliffordAlgebra Q) :
    (b.cliffordAlgebra Q).repr x ∅ = scalarTrace Q x := by
  have h : (b.cliffordAlgebra Q).coord ∅ = scalarTrace Q :=
    (b.cliffordAlgebra Q).ext fun s => by
      rw [coord_apply, repr_self, Finsupp.single_apply, scalarTrace_cliffordAlgebra]
  exact LinearMap.congr_fun h x

variable {b Q} (hb : Pairwise fun i j => Q.IsOrtho (b i) (b j))
include hb

/-- **The scalar part pairs the ordered-product basis diagonally**:
`τ (reverse e_s * e_t)` is `∏ i ∈ s, Q (b i)` if `s = t` and `0` otherwise. -/
theorem scalarTrace_reverse_cliffordAlgebra_mul (s t : Finset I) :
    scalarTrace Q (reverse (b.cliffordAlgebra Q s) * b.cliffordAlgebra Q t) =
      if s = t then ∏ i ∈ s, Q (b i) else 0 := by
  rw [b.cliffordAlgebra_apply Q hb, b.cliffordAlgebra_apply Q hb,
    scalarTrace_reverse_prod_mul_prod hb]

/-- **The scalar part reads off coordinates**: the coefficient of `x` at `s` in the ordered-product
basis, weighted by `∏ i ∈ s, Q (b i)`, is `τ (reverse e_s * x)`. -/
theorem prod_mul_cliffordAlgebra_repr (s : Finset I) (x : CliffordAlgebra Q) :
    (∏ i ∈ s, Q (b i)) * (b.cliffordAlgebra Q).repr x s =
      scalarTrace Q (reverse (b.cliffordAlgebra Q s) * x) := by
  have h : (∏ i ∈ s, Q (b i)) • (b.cliffordAlgebra Q).coord s =
      scalarTrace Q ∘ₗ LinearMap.mulLeft R (reverse (b.cliffordAlgebra Q s)) :=
    (b.cliffordAlgebra Q).ext fun t => by
      rw [LinearMap.smul_apply, coord_apply, repr_self, Finsupp.single_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, scalarTrace_reverse_cliffordAlgebra_mul hb, smul_eq_mul]
      by_cases hst : s = t
      · simp [hst]
      · simp [hst, Ne.symm hst]
  exact LinearMap.congr_fun h x

/-- **The scalar-part pairing is diagonal in the ordered-product basis**:
`τ (reverse x * y) = ∑ s, (∏ i ∈ s, Q (b i)) * xₛ * yₛ`. -/
theorem scalarTrace_reverse_mul [Fintype I] (x y : CliffordAlgebra Q) :
    scalarTrace Q (reverse x * y) =
      ∑ s, (∏ i ∈ s, Q (b i)) * (b.cliffordAlgebra Q).repr x s *
        (b.cliffordAlgebra Q).repr y s := by
  conv_lhs => rw [← (b.cliffordAlgebra Q).sum_repr y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, ← scalarTrace_reverse, reverse.map_mul,
    reverse_reverse, ← prod_mul_cliffordAlgebra_repr hb, mul_comm]

section Ordered

variable [LinearOrder R] [Finite I]

/-- **Positivity of the scalar-part pairing**: if `Q` is nonnegative on an orthogonal basis, then
`τ (reverse x * x) ≥ 0` for every `x`. -/
theorem scalarTrace_reverse_mul_self_nonneg [IsOrderedRing R] (hQ : ∀ i, 0 ≤ Q (b i))
    (x : CliffordAlgebra Q) : 0 ≤ scalarTrace Q (reverse x * x) := by
  cases nonempty_fintype I
  rw [scalarTrace_reverse_mul hb]
  exact Finset.sum_nonneg fun s _ => by
    rw [mul_assoc]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => hQ i) (mul_self_nonneg _)

/-- **Faithfulness of the scalar-part pairing**: if `Q` is positive on an orthogonal basis, then
`τ (reverse x * x) = 0` only for `x = 0`. -/
theorem scalarTrace_reverse_mul_self_eq_zero_iff [IsStrictOrderedRing R] (hQ : ∀ i, 0 < Q (b i))
    {x : CliffordAlgebra Q} : scalarTrace Q (reverse x * x) = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  cases nonempty_fintype I
  have hpos (s : Finset I) : 0 < ∏ i ∈ s, Q (b i) := Finset.prod_pos fun i _ => hQ i
  rw [scalarTrace_reverse_mul hb, Finset.sum_eq_zero_iff_of_nonneg fun s _ => by
    rw [mul_assoc]; exact mul_nonneg (hpos s).le (mul_self_nonneg _)] at h
  rw [← (b.cliffordAlgebra Q).repr.map_eq_zero_iff]
  ext s
  have hs := h s (Finset.mem_univ s)
  rwa [mul_assoc, mul_eq_zero, or_iff_right (hpos s).ne', mul_self_eq_zero] at hs

end Ordered

end Module.Basis
