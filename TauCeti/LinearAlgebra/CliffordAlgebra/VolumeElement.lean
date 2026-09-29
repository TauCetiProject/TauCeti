/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# The volume element of a Clifford algebra

The **volume element** (or pseudoscalar) of a quadratic space is the ordered Clifford product
`ι Q v₁ * ⋯ * ι Q vₙ` of an orthogonal basis. This file proves the facts that make it useful:
how it commutes past a vector, how reversal acts on it, what its square is, and, over a field,
that it moves each of its anisotropic factors out of the vectors once there are at least three of
them and evenly many.

The ordered product is spelled `(l.map (ι Q)).prod` for a list `l` of vectors, the spelling Mathlib
already uses for it (`CliffordAlgebra.involute_prod_map_ι`, `CliffordAlgebra.reverse_prod_map_ι`)
and the one the sibling file `Filtration.lean` uses
(`CliffordAlgebra.prod_map_ι_mem_filtration`); the results below are named `prod_map_ι_*` to
match. Orthogonality is a hypothesis of each result rather than part of the object, so the name
"volume element" is reserved for the informal reading.

Both facts come from the single relation `ι Q a * ι Q b = -(ι Q b * ι Q a)` for orthogonal `a` and
`b`. Pushing a vector `ι Q m` from one side of a product of `n` mutually orthogonal vectors to the
other costs a sign `(-1) ^ n` when `m` is orthogonal to every factor
(`CliffordAlgebra.prod_map_ι_mul_ι_of_forall_isOrtho`). When `m` is instead *one of* the factors,
one of the `n` transpositions is a vector past itself, which is free, so the cost is
`(-1) ^ (n - 1)`. That sign does not depend on `m`, and the condition is linear in `m`, so it
propagates from the factors to their span (`CliffordAlgebra.prod_map_ι_mul_ι_of_mem_span`).

This is the even/odd dichotomy of the Clifford algebra as seen from the volume element. If there
are **oddly** many factors, the volume element commutes with every generator coming from their span
(`CliffordAlgebra.prod_map_ι_mul_ι_of_odd_length`), so once the factors span `M` it is **central**
(`CliffordAlgebra.prod_map_ι_mem_center_of_odd_length`); if there are evenly many, it
**anticommutes** with those generators instead
(`CliffordAlgebra.prod_map_ι_mul_ι_of_even_length`). Centrality is all the odd case claims: under
these hypotheses the volume element may well be a scalar already, and is `0` as soon as one of its
factors is. That it is a *further* central element, and that the centre is then exactly a rank-two
algebra rather than the scalars, is *not* proved here and needs hypotheses this file does not make
— a nondegenerate form over a field away from characteristic two, with the list an orthogonal
basis. For `Q = 0` on `R ^ 3` the Clifford algebra is the exterior algebra and its centre is much
larger instead. The odd-dimensional splitting does run on the volume element:
`TauCeti/LinearAlgebra/CliffordAlgebra/OddSplitting.lean` splits the Clifford algebra as two copies
of its even subalgebra along a central odd square root of one, and
`CliffordAlgebra.equivEvenProdOfOddLength` feeds it the volume element of an orthogonal spanning
list of odd length, rescaled so that the square below is `1`. What remains open there is the
identification of `even Q` with a matrix algebra, for which
`TauCeti/RepresentationTheory/Spin/Structure.lean` proves the even-dimensional structure theorem.

The square is a scalar,
`ω * ω = (-1) ^ (n.choose 2) * Q v₁ ⋯ Q vₙ` (`CliffordAlgebra.prod_map_ι_sq_scalar`), the sign
counting the `n.choose 2` transpositions needed to interleave two copies of the product. So the
volume element is a unit as soon as the product of the values `Q vᵢ` is a unit — over a field,
whenever no factor is isotropic. That last statement (`CliffordAlgebra.isUnit_prod_map_ι`) needs no
orthogonality at all, each factor being a unit already because its square `Q vᵢ` is.

Nothing here needs `2` to be invertible, a field, or any finiteness. Beyond pairwise orthogonality
of the list — which the unit statement does not even ask for — the only hypotheses are the ones
each statement names: that the vector crossing the product lies in the span of the list (or that
the list spans `M`, for the centrality statement), and, for the unit statement, that the product of
the values `Q vᵢ` is a unit.

## Main results

* `CliffordAlgebra.prod_map_ι_mul_ι_of_forall_isOrtho`: a vector orthogonal to every factor
  moves across the product at the cost of `(-1) ^ n`.
* `CliffordAlgebra.prod_map_ι_mul_ι_of_mem_span`: a vector in the span of a pairwise orthogonal
  list moves across the product at the cost of `(-1) ^ (n - 1)`.
* `CliffordAlgebra.prod_map_ι_mul_ι_of_odd_length`: the volume element of a pairwise orthogonal
  list of odd length commutes with every generator in the span of the list.
* `CliffordAlgebra.prod_map_ι_mem_center_of_odd_length`: the volume element of a pairwise
  orthogonal spanning list of odd length is central.
* `CliffordAlgebra.prod_map_ι_mul_ι_of_even_length`: of even length, it anticommutes with every
  generator in the span instead.
* `CliffordAlgebra.prod_map_ι_sq_scalar`: the square of the volume element of a pairwise
  orthogonal list is the scalar `(-1) ^ (n.choose 2) * ∏ᵢ Q vᵢ`.
* `CliffordAlgebra.reverse_prod_map_ι_of_pairwise_isOrtho`: reversal multiplies the volume
  element of a pairwise orthogonal list by the same sign `(-1) ^ (n.choose 2)`.
* `CliffordAlgebra.ι_mul_ι_mul_self_of_isOrtho`: the two-factor case, the square of the product
  of two orthogonal generators being the scalar `-(Q a * Q b)`.
* `CliffordAlgebra.isUnit_prod_map_ι`: an ordered product of generators — orthogonal or not — is
  a unit as soon as the product of the values `Q vᵢ` is.
* `CliffordAlgebra.prod_map_ι_mul_ι_notMem_range_ι`: over a field, the volume element of an
  orthogonal anisotropic list of even length at least three moves each member of the list out of
  the vectors.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §3.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-! ### Moving a vector across the volume element -/

/-- **A vector orthogonal to every factor crosses the volume element at the cost of `(-1) ^ n`**,
`n` the number of factors: each transposition with a factor contributes one sign. -/
theorem prod_map_ι_mul_ι_of_forall_isOrtho {l : List M} {m : M}
    (h : ∀ x ∈ l, Q.IsOrtho x m) :
    (l.map (ι Q)).prod * ι Q m = ((-1 : R) ^ l.length) • (ι Q m * (l.map (ι Q)).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : Q.IsOrtho a m := h a List.mem_cons_self
    have hl : ∀ x ∈ l, Q.IsOrtho x m := fun x hx => h x (List.mem_cons_of_mem _ hx)
    calc ((a :: l).map (ι Q)).prod * ι Q m
        = ι Q a * ((l.map (ι Q)).prod * ι Q m) := by
          simp only [List.map_cons, List.prod_cons, mul_assoc]
      _ = ((-1 : R) ^ l.length) • (ι Q a * ι Q m * (l.map (ι Q)).prod) := by
          rw [ih hl, mul_smul_comm, mul_assoc]
      _ = ((-1 : R) ^ l.length) • -(ι Q m * ((a :: l).map (ι Q)).prod) := by
          simp only [List.map_cons, List.prod_cons]
          rw [ι_mul_ι_comm_of_isOrtho ha, neg_mul, mul_assoc]
      _ = ((-1 : R) ^ (a :: l).length) • (ι Q m * ((a :: l).map (ι Q)).prod) := by
          rw [smul_neg, List.length_cons, pow_succ, mul_neg_one, neg_smul]

/-- **A factor of the volume element crosses it at the cost of `(-1) ^ (n - 1)`**: of the `n`
transpositions, the one exchanging the vector with the copy of itself inside the product is free.

The list is presented split at the chosen occurrence of the vector, so that the two halves can be
crossed separately; that presentation is chosen for the induction, so the lemma is private and
`prod_map_ι_mul_ι_of_mem_span` is the interface. -/
private theorem prod_map_ι_append_cons_mul_ι {l₁ l₂ : List M} {a : M}
    (h₁ : ∀ x ∈ l₁, Q.IsOrtho x a) (h₂ : ∀ x ∈ l₂, Q.IsOrtho x a) :
    ((l₁ ++ a :: l₂).map (ι Q)).prod * ι Q a
      = ((-1 : R) ^ (l₁.length + l₂.length))
          • (ι Q a * ((l₁ ++ a :: l₂).map (ι Q)).prod) := by
  have hmid : ((l₁ ++ a :: l₂).map (ι Q)).prod
      = (l₁.map (ι Q)).prod * (ι Q a * (l₂.map (ι Q)).prod) := by
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  -- Crossing `l₁` right-to-left costs the same sign, which is its own inverse.
  have hsq : ((-1 : R) ^ l₁.length) * (-1) ^ l₁.length = 1 := by
    simp [← mul_pow]
  calc ((l₁ ++ a :: l₂).map (ι Q)).prod * ι Q a
      = (l₁.map (ι Q)).prod * (ι Q a * ((l₂.map (ι Q)).prod * ι Q a)) := by
        rw [hmid]; simp only [mul_assoc]
    _ = ((-1 : R) ^ l₂.length)
          • ((l₁.map (ι Q)).prod * (ι Q a * (ι Q a * (l₂.map (ι Q)).prod))) := by
        rw [prod_map_ι_mul_ι_of_forall_isOrtho h₂, mul_smul_comm, mul_smul_comm]
    _ = ((-1 : R) ^ (l₁.length + l₂.length)) • ((((-1 : R) ^ l₁.length)
          • ((l₁.map (ι Q)).prod * ι Q a)) * (ι Q a * (l₂.map (ι Q)).prod)) := by
        rw [smul_mul_assoc, smul_smul, pow_add, mul_right_comm, hsq, one_mul]
        simp only [mul_assoc]
    _ = ((-1 : R) ^ (l₁.length + l₂.length))
          • (ι Q a * ((l₁ ++ a :: l₂).map (ι Q)).prod) := by
        rw [prod_map_ι_mul_ι_of_forall_isOrtho h₁, smul_smul, hsq, one_smul, hmid]
        simp only [mul_assoc]

/-- **A factor of a pairwise orthogonal volume element crosses it at the cost of `(-1) ^ (n - 1)`.**

This is the base case of `prod_map_ι_mul_ι_of_mem_span`, of which it is a special case once the
factor is viewed in the span; that lemma is the interface. -/
private theorem prod_map_ι_mul_ι_of_mem {l : List M} (hl : l.Pairwise Q.IsOrtho) {a : M}
    (ha : a ∈ l) :
    (l.map (ι Q)).prod * ι Q a
      = ((-1 : R) ^ (l.length - 1)) • (ι Q a * (l.map (ι Q)).prod) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  rw [List.pairwise_append, List.pairwise_cons] at hl
  obtain ⟨-, ⟨h₂, -⟩, h₁⟩ := hl
  have hlen : (l₁ ++ a :: l₂).length - 1 = l₁.length + l₂.length := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [hlen]
  exact prod_map_ι_append_cons_mul_ι (fun x hx => h₁ x hx a List.mem_cons_self)
    (fun x hx => (h₂ x hx).symm)

/-- **The crossing sign propagates from the factors to their span.** The sign `(-1) ^ (n - 1)` does
not depend on the vector, and both sides of the crossing identity are linear in it, so the identity
holds on the whole span of the list — in particular on all of `M` when the list spans. -/
theorem prod_map_ι_mul_ι_of_mem_span {l : List M} (hl : l.Pairwise Q.IsOrtho) {m : M}
    (hm : m ∈ Submodule.span R {x : M | x ∈ l}) :
    (l.map (ι Q)).prod * ι Q m
      = ((-1 : R) ^ (l.length - 1)) • (ι Q m * (l.map (ι Q)).prod) := by
  have key : Set.EqOn ((LinearMap.mulLeft R (l.map (ι Q)).prod).comp (ι Q))
      ((((-1 : R) ^ (l.length - 1)) • LinearMap.mulRight R (l.map (ι Q)).prod).comp (ι Q))
      {x : M | x ∈ l} := by
    intro x hx
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply, LinearMap.mulRight_apply]
    exact prod_map_ι_mul_ι_of_mem hl hx
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, LinearMap.mulRight_apply] using LinearMap.eqOn_span key hm

/-! ### The even/odd dichotomy -/

/-- **The volume element of an odd number of pairwise orthogonal vectors commutes with every
generator coming from their span**, the crossing sign `(-1) ^ (n - 1)` now being `1`.

This is the odd half of the dichotomy, in the same span-relative form as its even counterpart
`prod_map_ι_mul_ι_of_even_length`; `prod_map_ι_mem_center_of_odd_length` is the case of a
spanning list, where commuting with the generators upgrades to centrality. -/
theorem prod_map_ι_mul_ι_of_odd_length {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) {m : M} (hm : m ∈ Submodule.span R {x : M | x ∈ l}) :
    (l.map (ι Q)).prod * ι Q m = ι Q m * (l.map (ι Q)).prod := by
  have hpar : Even (l.length - 1) := Nat.Odd.sub_odd hlen odd_one
  have h := prod_map_ι_mul_ι_of_mem_span hl hm
  rwa [hpar.neg_one_pow, one_smul] at h

/-- **The volume element of an odd number of pairwise orthogonal vectors spanning `M` is central.**

Crossing a generator costs `(-1) ^ (n - 1)`, and `n - 1` is even, so the volume element commutes
with every generator; the generators generate the algebra, so it commutes with everything.

Centrality is all that is claimed. Under these hypotheses the volume element may already be a
scalar, and is `0` as soon as one of its factors is; it is the element *expected* to generate the
centre beyond the scalars in the odd-dimensional case, but that expectation rests on nondegeneracy
hypotheses made nowhere in this file. -/
theorem prod_map_ι_mem_center_of_odd_length {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) :
    (l.map (ι Q)).prod ∈ Subalgebra.center R (CliffordAlgebra Q) := by
  have key : ∀ m : M, (l.map (ι Q)).prod * ι Q m = ι Q m * (l.map (ι Q)).prod := fun m =>
    prod_map_ι_mul_ι_of_odd_length hl hlen (hspan.ge Submodule.mem_top)
  rw [Subalgebra.mem_center_iff]
  intro y
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (s := Set.range (ι Q))
    ((adjoin_range_ι (Q := Q)).ge Algebra.mem_top)
    (by rintro _ ⟨m, rfl⟩; exact key m)).symm.eq

/-- **The volume element of an even number of pairwise orthogonal vectors anticommutes with every
generator coming from their span**, the crossing sign `(-1) ^ (n - 1)` now being `-1`.

Anticommuting does not by itself rule out centrality: it says exactly that
`2 • (ι Q m * ω) = 0` whenever `ω` is central, which happens in characteristic two, and also
whenever `ω` annihilates the generators, as it does in an exterior algebra. -/
theorem prod_map_ι_mul_ι_of_even_length {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Even l.length) {m : M} (hm : m ∈ Submodule.span R {x : M | x ∈ l}) :
    (l.map (ι Q)).prod * ι Q m = -(ι Q m * (l.map (ι Q)).prod) := by
  rcases l with _ | ⟨a, l⟩
  · -- The empty list spans `⊥`, so the only vector to cross is `0`.
    have hm0 : m = 0 := by simpa using hm
    simp [hm0]
  · have hpos : 1 ≤ (a :: l).length := Nat.succ_le_succ (Nat.zero_le _)
    have hpar : Odd ((a :: l).length - 1) := Nat.Even.sub_odd hpos hlen odd_one
    have h := prod_map_ι_mul_ι_of_mem_span hl hm
    rwa [hpar.neg_one_pow, neg_one_smul] at h

/-! ### The square of the volume element -/

/-- **The square of the volume element of a pairwise orthogonal list is a scalar**,
`(-1) ^ (n.choose 2) * Q v₁ ⋯ Q vₙ`: interleaving the two copies of the product takes
`n.choose 2` transpositions, and each pair of equal adjacent factors collapses to `Q vᵢ`. -/
@[simp]
theorem prod_map_ι_sq_scalar {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    (l.map (ι Q)).prod * (l.map (ι Q)).prod
      = algebraMap R (CliffordAlgebra Q) (((-1 : R) ^ l.length.choose 2) * (l.map Q).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl'⟩ := hl
    have hsym : ∀ x ∈ l, Q.IsOrtho x a := fun x hx => (ha x hx).symm
    have hchoose : (a :: l).length.choose 2 = l.length + l.length.choose 2 := by
      rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
    calc ((a :: l).map (ι Q)).prod * ((a :: l).map (ι Q)).prod
        = ι Q a * ((l.map (ι Q)).prod * ι Q a) * (l.map (ι Q)).prod := by
          simp only [List.map_cons, List.prod_cons, mul_assoc]
      _ = ((-1 : R) ^ l.length)
            • (ι Q a * ι Q a * ((l.map (ι Q)).prod * (l.map (ι Q)).prod)) := by
          rw [prod_map_ι_mul_ι_of_forall_isOrtho hsym, mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
      _ = algebraMap R (CliffordAlgebra Q)
            (((-1 : R) ^ (a :: l).length.choose 2) * ((a :: l).map Q).prod) := by
          rw [ι_sq_scalar, ih hl', ← map_mul, Algebra.smul_def, ← map_mul]
          congr 1
          rw [hchoose, List.map_cons, List.prod_cons, pow_add]
          ring

/-- **Reversal multiplies the volume element of a pairwise orthogonal list by
`(-1) ^ (n.choose 2)`**, the same sign as in its square `CliffordAlgebra.prod_map_ι_sq_scalar`. In
particular the volume element is reverse-symmetric for `n ≡ 0, 1 (mod 4)` and reverse-antisymmetric
for `n ≡ 2, 3 (mod 4)`. -/
@[simp]
theorem reverse_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    reverse (l.map (ι Q)).prod = ((-1 : R) ^ l.length.choose 2) • (l.map (ι Q)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl'⟩ := hl
    have hsym : ∀ x ∈ l, Q.IsOrtho x a := fun x hx => (ha x hx).symm
    have hchoose : (a :: l).length.choose 2 = l.length + l.length.choose 2 := by
      rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
    rw [List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι, ih hl', smul_mul_assoc,
      prod_map_ι_mul_ι_of_forall_isOrtho hsym, smul_smul, hchoose, pow_add, mul_comm]

/-- **The square of the product of two orthogonal generators is the scalar `-(Q a * Q b)`.** This
is `CliffordAlgebra.prod_map_ι_sq_scalar` at the two-element list `[a, b]`, whose sign
`(-1) ^ Nat.choose 2 2` is the displayed minus. In particular the square vanishes as soon as one
of the two vectors is isotropic. -/
theorem ι_mul_ι_mul_self_of_isOrtho {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * ι Q b * (ι Q a * ι Q b) = -algebraMap R (CliffordAlgebra Q) (Q a * Q b) := by
  simpa using prod_map_ι_sq_scalar (Q := Q) (l := [a, b]) (by simpa using h)

/-- **An ordered product of generators is a unit as soon as the product of the values `Q vᵢ` is.**

No orthogonality is needed: each `Q vᵢ` divides the unit `∏ᵢ Q vᵢ`, hence is a unit, so each
factor `ι Q vᵢ` is a unit by `CliffordAlgebra.isUnit_ι_of_isUnit` and so is their product. For a
pairwise orthogonal list this is the volume element, and `prod_map_ι_sq_scalar` identifies its
square as that product up to sign; in particular the volume element of an orthogonal basis of a
quadratic space over a field is a unit whenever no basis vector is isotropic. -/
theorem isUnit_prod_map_ι {l : List M} (h : IsUnit ((l.map Q).prod)) :
    IsUnit ((l.map (ι Q)).prod) := by
  refine List.prod_isUnit fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  have hQm : IsUnit (Q m) := List.prod_isUnit_iff.mp h _ (List.mem_map_of_mem hm)
  exact isUnit_ι_of_isUnit Q hQm

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-! ### The volume element moves its factors out of the vectors -/

/-- Two members of a pairwise orthogonal list of length at least three, orthogonal to a given
member and to each other. -/
private theorem exists_isOrtho_pair_of_mem {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (h3 : 3 ≤ l.length) {v : V} (hv : v ∈ l) :
    ∃ u₁ ∈ l, ∃ u₂ ∈ l, Q.IsOrtho v u₁ ∧ Q.IsOrtho v u₂ ∧ Q.IsOrtho u₁ u₂ := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hv
  rw [List.pairwise_append, List.pairwise_cons] at hl
  obtain ⟨hs, ⟨hvt, ht⟩, hst⟩ := hl
  have hortho : ∀ u ∈ s ++ t, Q.IsOrtho v u := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact (hst u hu v List.mem_cons_self).symm
    · exact hvt u hu
  have hpair : (s ++ t).Pairwise Q.IsOrtho :=
    List.pairwise_append.mpr ⟨hs, ht, fun a ha b hb => hst a ha b (List.mem_cons_of_mem v hb)⟩
  have hmem : ∀ u ∈ s ++ t, u ∈ s ++ v :: t := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact List.mem_append_left _ hu
    · exact List.mem_append_right _ (List.mem_cons_of_mem v hu)
  have h0 : 0 < (s ++ t).length := by
    simp only [List.length_append, List.length_cons] at h3 ⊢
    omega
  have h1 : 1 < (s ++ t).length := by
    simp only [List.length_append, List.length_cons] at h3 ⊢
    omega
  exact ⟨(s ++ t)[0], hmem _ (List.getElem_mem h0), (s ++ t)[1], hmem _ (List.getElem_mem h1),
    hortho _ (List.getElem_mem h0), hortho _ (List.getElem_mem h1),
    List.pairwise_iff_getElem.mp hpair 0 1 h0 h1 zero_lt_one⟩

variable [Invertible (2 : K)]

/-- **The volume element of an orthogonal anisotropic list of even length at least three moves each
member of the list out of the vectors.** Length two is genuinely excluded: there the volume element
sends each member to a multiple of the other. -/
theorem prod_map_ι_mul_ι_notMem_range_ι {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Even l.length) (h3 : 3 ≤ l.length) (haniso : ∀ v ∈ l, Q v ≠ 0) {v : V}
    (hv : v ∈ l) : (l.map (ι Q)).prod * ι Q v ∉ LinearMap.range (ι Q) := by
  -- The volume element is a nonzero unit anticommuting with every member of the list
  -- (`prod_map_ι_mul_ι_of_even_length`), and `v` has two orthogonal anisotropic companions in the
  -- list, so `mul_ι_notMem_range_ι_of_mul_ι_eq_neg` applies.
  obtain ⟨u₁, hu₁, u₂, hu₂, hvu₁, hvu₂, hu₁u₂⟩ := exists_isOrtho_pair_of_mem hl h3 hv
  have hunit : IsUnit ((l.map Q).prod) :=
    List.prod_isUnit fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact isUnit_iff_ne_zero.mpr (haniso m hm)
  exact mul_ι_notMem_range_ι_of_mul_ι_eq_neg (isUnit_prod_map_ι hunit).ne_zero (haniso v hv)
    (haniso u₁ hu₁) (haniso u₂ hu₂) hvu₁ hvu₂ hu₁u₂
    (prod_map_ι_mul_ι_of_even_length hl hlen (Submodule.subset_span hu₁))
    (prod_map_ι_mul_ι_of_even_length hl hlen (Submodule.subset_span hu₂))

end Field

end CliffordAlgebra
