/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Basic
-- Private: the product, reversal and exterior-basis lemmas below are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The ordered-product basis of an orthogonal basis, and the trace pairing

Let `b` be a basis of `M`, indexed by a linearly ordered type `I`, and let `Q` be a quadratic form
on `M` over a commutative ring in which `2` is invertible. The basis
`CliffordAlgebra.basis Q b` of `CliffordAlgebra Q`, indexed by the finite subsets of `I`, is
transported from the exterior-algebra basis along `CliffordAlgebra.equivExterior`, which corrects
a product of generators by lower-order contractions. When `b` is orthogonal for `Q` these
corrections all vanish, and the basis vector indexed by `s` is the ordered product
`e_s = ι Q (b i₁) * ⋯ * ι Q (b iₖ)` for `s.sort = [i₁, …, iₖ]`. So the ordered products of an
orthogonal basis form a basis of the Clifford algebra, for every `Q`, degenerate or not.

The scalar part `τ = CliffordAlgebra.scalarTrace Q` makes these basis vectors orthogonal for the
pairing `(x, y) ↦ τ (reverse x * y)`:

  `τ (reverse e_s * e_t) = if s = t then ∏ i ∈ s, Q (b i) else 0`.

For `s = t` the product `reverse e_s * e_s` collapses to the scalar `∏ i ∈ s, Q (b i)`. For
`s ≠ t` some index lies in exactly one of `s` and `t`, so its basis vector occurs exactly once in
the product and is orthogonal to every other factor, and the scalar part of such a product
vanishes. Expanding in the basis then computes the pairing of arbitrary elements coordinatewise,
`τ (reverse x * y) = ∑ₛ xₛ * (∏ i ∈ s, Q (b i)) * yₛ`. Over an ordered ring this gives positivity
of the pairing: if every `Q (b i)` is nonnegative then `τ (reverse x * x) ≥ 0`, and if every
`Q (b i)` is positive then `τ (reverse x * x) = 0` only for `x = 0`.

## Main results

* `CliffordAlgebra.basis_repr_empty`: for every basis, the coordinate at the empty index set is the
  scalar part.
* `CliffordAlgebra.basis_eq_prod_map_sort`: for an orthogonal basis, the basis vector indexed by
  `s` is the product of the generators of `s` in increasing order.
* `CliffordAlgebra.basis_mul_basis_of_disjoint`: for an orthogonal basis, basis vectors with
  disjoint index sets multiply to the signed basis vector of the union.
* `CliffordAlgebra.basis_mul_ι_of_mem` and `CliffordAlgebra.basis_mul_ι_of_notMem`: a basis
  vector `e_s` and a basis generator `ι Q (b i)` commute up to the sign `(-1) ^ (|s| - 1)` when
  `i ∈ s`, and up to `(-1) ^ |s|` when `i ∉ s`.
* `CliffordAlgebra.scalarTrace_reverse_basis_mul_basis`: the pairing of two basis vectors.
* `CliffordAlgebra.scalarTrace_reverse_basis_mul`: pairing against a basis vector extracts a
  coordinate, `τ (reverse e_s * x) = (∏ i ∈ s, Q (b i)) * xₛ`.
* `CliffordAlgebra.scalarTrace_reverse_mul`: the pairing in coordinates.
* `CliffordAlgebra.scalarTrace_reverse_mul_self_nonneg` and
  `CliffordAlgebra.scalarTrace_reverse_mul_self_eq_zero_iff`: positivity and faithfulness of the
  pairing over an ordered ring.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

namespace CliffordAlgebra

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  {Q : QuadraticForm R M} {I : Type*} [LinearOrder I]

/-- **The coordinate at the empty index set is the scalar part**, for the basis
`CliffordAlgebra.basis Q b` attached to any basis `b` of `M`. -/
@[simp]
theorem basis_repr_empty (b : Module.Basis I R M) (x : CliffordAlgebra Q) :
    (basis Q b).repr x ∅ = scalarTrace Q x := by
  rw [basis, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    Module.Basis.exteriorAlgebra_repr_empty, scalarTrace_apply]

variable {b : Module.Basis I R M}

/-- The generators of a finite set of indices of an orthogonal basis, listed in increasing order,
are pairwise orthogonal. -/
private theorem pairwise_isOrtho_map_sort (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (s : Finset I) : (s.sort.map b).Pairwise Q.IsOrtho :=
  List.pairwise_map.mpr <| (s.sort_nodup _).imp fun hij ↦
    QuadraticMap.associated_isOrtho.mp (hb hij)

/-- **For an orthogonal basis `b`, the Clifford basis vector indexed by `s` is the ordered product**
`ι Q (b i₁) * ⋯ * ι Q (b iₖ)` of the generators of `s.sort = [i₁, …, iₖ]`. No hypothesis on `Q`
is needed beyond the orthogonality of `b`; in particular `Q` may be degenerate. -/
theorem basis_eq_prod_map_sort (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (s : Finset I) :
    basis Q b s = ((s.sort.map b).map (ι Q)).prod := by
  rw [basis_apply, LinearEquiv.symm_apply_eq,
    equivExterior_prod_map_ι_of_pairwise_isOrtho Q (pairwise_isOrtho_map_sort hb s),
    Module.Basis.exteriorAlgebra_eq_prod_map_sort]

/-- **For an orthogonal basis, multiplying basis vectors with disjoint index sets is transported
from the exterior algebra**: the Clifford product of `e_s` and `e_t` is the image of the exterior
product of the corresponding exterior basis vectors, since no generator meets itself. -/
theorem basis_mul_basis_eq_symm_equivExterior (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    {s t : Finset I} (h : Disjoint s t) :
    basis Q b s * basis Q b t =
      (equivExterior Q).symm (b.ExteriorAlgebra s * b.ExteriorAlgebra t) := by
  have hl : ((s.sort ++ t.sort).map b).Pairwise Q.IsOrtho := by
    refine List.pairwise_map.mpr <| (List.nodup_append.2 ⟨s.sort_nodup _, t.sort_nodup _, ?_⟩).imp
      fun hij ↦ QuadraticMap.associated_isOrtho.mp (hb hij)
    rintro i hi _ hj rfl
    exact Finset.disjoint_left.1 h ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj)
  rw [LinearEquiv.eq_symm_apply, basis_eq_prod_map_sort hb, basis_eq_prod_map_sort hb,
    b.exteriorAlgebra_eq_prod_map_sort, b.exteriorAlgebra_eq_prod_map_sort]
  -- The concatenated list of generators is transported factorwise.
  simpa only [List.map_append, List.prod_append] using
    equivExterior_prod_map_ι_of_pairwise_isOrtho Q hl

/-- **The multiplication rule for basis vectors with disjoint index sets**: for an orthogonal basis,
`e_s * e_t = ε • e_{s ∪ t}`, where `ε` is the sign of the shuffle listing `s` before `t`. This is
the Clifford counterpart of Mathlib's `ExteriorAlgebra.basis_mul_of_disjoint`. -/
theorem basis_mul_basis_of_disjoint (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) {m n : ℕ}
    {s : Set.powersetCard I m} {t : Set.powersetCard I n} (h : Disjoint s.val t.val) :
    basis Q b s * basis Q b t =
      (Set.powersetCard.permOfDisjoint h).sign • basis Q b (Set.powersetCard.disjUnion h) := by
  rw [basis_mul_basis_eq_symm_equivExterior hb h, ExteriorAlgebra.basis_mul_of_disjoint b s t h,
    map_zsmul_unit, basis_apply]

/-- **A basis generator crosses a basis vector containing it at the cost of `(-1) ^ (|s| - 1)`**,
for an orthogonal basis: `e_s * ι Q (b i) = (-1) ^ (|s| - 1) • (ι Q (b i) * e_s)` when `i ∈ s`. -/
theorem basis_mul_ι_of_mem (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) {s : Finset I} {i : I}
    (hi : i ∈ s) :
    basis Q b s * ι Q (b i) = ((-1 : R) ^ (s.card - 1)) • (ι Q (b i) * basis Q b s) := by
  rw [basis_eq_prod_map_sort hb, ← s.length_sort (· ≤ ·), ← List.length_map b]
  exact prod_map_ι_mul_ι_of_mem_span (pairwise_isOrtho_map_sort hb s)
    (Submodule.subset_span (List.mem_map.2 ⟨i, (Finset.mem_sort _).2 hi, rfl⟩))

/-- **A basis generator crosses a basis vector not containing it at the cost of `(-1) ^ |s|`**,
for an orthogonal basis: `e_s * ι Q (b i) = (-1) ^ |s| • (ι Q (b i) * e_s)` when `i ∉ s`. -/
theorem basis_mul_ι_of_notMem (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) {s : Finset I}
    {i : I} (hi : i ∉ s) :
    basis Q b s * ι Q (b i) = ((-1 : R) ^ s.card) • (ι Q (b i) * basis Q b s) := by
  rw [basis_eq_prod_map_sort hb, ← s.length_sort (· ≤ ·), ← List.length_map b]
  refine prod_map_ι_mul_ι_of_forall_isOrtho fun x hx ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  refine QuadraticMap.associated_isOrtho.mp (hb ?_)
  rintro rfl
  exact hi ((Finset.mem_sort _).1 hj)

/-- The scalar part of a product of generators of an orthogonal basis vanishes as soon as one index
occurs exactly once. -/
private theorem scalarTrace_prod_map_map_eq_zero (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    {l : List I} {k : I} (hk : l.count k = 1) :
    scalarTrace Q ((l.map b).map (ι Q)).prod = 0 := by
  have hkl : k ∈ l := List.count_pos_iff.mp (by rw [hk]; exact Nat.one_pos)
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hkl
  have hnot : k ∉ l₁ ++ l₂ := by
    rw [← List.count_eq_zero]
    simp only [List.count_append, List.count_cons_self] at hk ⊢
    omega
  rw [List.map_append, List.map_cons]
  refine scalarTrace_prod_map_ι_append_cons_eq_zero fun x hx ↦ ?_
  rw [← List.map_append] at hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact QuadraticMap.associated_isOrtho.mp (hb (ne_of_mem_of_not_mem hj hnot))

/-- **The basis of an orthogonal basis is orthogonal for the trace pairing**
`(x, y) ↦ τ (reverse x * y)`, and the basis vector indexed by `s` pairs with itself to
`∏ i ∈ s, Q (b i)`. -/
theorem scalarTrace_reverse_basis_mul_basis (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (s t : Finset I) :
    scalarTrace Q (reverse (basis Q b s) * basis Q b t) =
      if s = t then ∏ i ∈ s, Q (b i) else 0 := by
  split_ifs with hst
  · subst hst
    rw [basis_eq_prod_map_sort hb, reverse_prod_map_ι_mul_prod_map_ι, scalarTrace_algebraMap,
      List.map_map, ← List.prod_toFinset _ (s.sort_nodup _), Finset.sort_toFinset,
      Function.comp_def]
  · rw [basis_eq_prod_map_sort hb, basis_eq_prod_map_sort hb, reverse_prod_map_ι,
      ← List.map_reverse, ← List.prod_append, ← List.map_append, ← List.map_reverse,
      ← List.map_append]
    -- Some index lies in exactly one of `s` and `t`, so it occurs once in the combined list.
    have hcount (k : I) (hks : k ∈ s ↔ k ∉ t) : (s.sort.reverse ++ t.sort).count k = 1 := by
      rw [List.count_append, List.count_reverse]
      by_cases hk : k ∈ s
      · rw [List.count_eq_one_of_mem (s.sort_nodup _) ((Finset.mem_sort _).mpr hk),
          List.count_eq_zero_of_not_mem fun h ↦ hks.mp hk ((Finset.mem_sort _).mp h)]
      · rw [List.count_eq_zero_of_not_mem fun h ↦ hk ((Finset.mem_sort _).mp h),
          List.count_eq_one_of_mem (t.sort_nodup _)
            ((Finset.mem_sort _).mpr (not_not.mp (mt hks.mpr hk)))]
    by_cases hsub : s ⊆ t
    · obtain ⟨k, hkt, hks⟩ := Finset.not_subset.mp fun h ↦ hst (hsub.antisymm h)
      exact scalarTrace_prod_map_map_eq_zero hb (hcount k (iff_of_false hks (not_not.mpr hkt)))
    · obtain ⟨k, hks, hkt⟩ := Finset.not_subset.mp hsub
      exact scalarTrace_prod_map_map_eq_zero hb (hcount k (iff_of_true hks hkt))

/-- **Pairing against a basis vector extracts a coordinate**: for an orthogonal basis,
`τ (reverse e_s * x) = (∏ i ∈ s, Q (b i)) * xₛ`, where `xₛ` is the coordinate of `x` at `s`. -/
theorem scalarTrace_reverse_basis_mul (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (s : Finset I) (x : CliffordAlgebra Q) :
    scalarTrace Q (reverse (basis Q b s) * x) = (∏ i ∈ s, Q (b i)) * (basis Q b).repr x s := by
  refine LinearMap.congr_fun ((basis Q b).ext
    (f₁ := scalarTrace Q ∘ₗ LinearMap.mulLeft R (reverse (basis Q b s)))
    (f₂ := (∏ i ∈ s, Q (b i)) • (basis Q b).coord s) fun t ↦ ?_) x
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
    scalarTrace_reverse_basis_mul_basis hb, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    eq_comm]

/-- **The trace pairing in coordinates**: for an orthogonal basis `b`,
`τ (reverse x * y) = ∑ₛ xₛ * ((∏ i ∈ s, Q (b i)) * yₛ)`, the sum running over the support of the
coordinates of `x`. -/
theorem scalarTrace_reverse_mul (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    (x y : CliffordAlgebra Q) :
    scalarTrace Q (reverse x * y) =
      ((basis Q b).repr x).sum fun s c ↦ c * ((∏ i ∈ s, Q (b i)) * (basis Q b).repr y s) := by
  conv_lhs => rw [← (basis Q b).linearCombination_repr x, Finsupp.linearCombination_apply]
  simp only [map_finsuppSum, Finsupp.sum_mul, map_smul, smul_mul_assoc, smul_eq_mul,
    scalarTrace_reverse_basis_mul hb]

section Ordered

variable [LinearOrder R]

omit [Invertible (2 : R)] [LinearOrder I] in
/-- A summand `c * ((∏ i ∈ s, Q (b i)) * c)` of the coordinate formula for `τ (reverse x * x)` is
nonnegative when `Q` is nonnegative on `b`. -/
lemma mul_prod_mul_self_nonneg [IsOrderedRing R] (hQ : ∀ i, 0 ≤ Q (b i)) (s : Finset I)
    (c : R) : 0 ≤ c * ((∏ i ∈ s, Q (b i)) * c) := by
  rw [mul_left_comm]
  exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ hQ i) (mul_self_nonneg _)

/-- **Positivity of the trace pairing**: if `Q` is nonnegative on an orthogonal basis, then
`τ (reverse x * x) ≥ 0` for every `x`. -/
theorem scalarTrace_reverse_mul_self_nonneg [IsOrderedRing R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, 0 ≤ Q (b i)) (x : CliffordAlgebra Q) :
    0 ≤ scalarTrace Q (reverse x * x) := by
  rw [scalarTrace_reverse_mul hb, Finsupp.sum]
  exact Finset.sum_nonneg fun s _ ↦ mul_prod_mul_self_nonneg hQ s _

/-- **Faithfulness of the trace pairing**: if `Q` is positive on an orthogonal basis, then
`τ (reverse x * x) = 0` only for `x = 0`. -/
theorem scalarTrace_reverse_mul_self_eq_zero_iff [IsStrictOrderedRing R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, 0 < Q (b i))
    {x : CliffordAlgebra Q} : scalarTrace Q (reverse x * x) = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hpos (s : Finset I) : 0 < ∏ i ∈ s, Q (b i) := Finset.prod_pos fun i _ ↦ hQ i
  rw [scalarTrace_reverse_mul hb, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg
    fun s _ ↦ mul_prod_mul_self_nonneg (fun i ↦ (hQ i).le) s _] at h
  rw [← (basis Q b).repr.map_eq_zero_iff, ← Finsupp.support_eq_empty,
    Finset.eq_empty_iff_forall_notMem]
  intro s hs
  have hs' := h s hs
  rw [mul_left_comm, mul_eq_zero, or_iff_right (hpos s).ne', mul_self_eq_zero] at hs'
  exact Finsupp.mem_support_iff.mp hs hs'

end Ordered

end CliffordAlgebra
