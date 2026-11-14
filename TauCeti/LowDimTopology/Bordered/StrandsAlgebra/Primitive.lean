/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic
import Mathlib.RingTheory.Idempotents

/-!
# The primitive idempotents of the strands algebra and of the matched subalgebra

Every strand of a strand diagram goes upwards, so the only way a concatenation of diagrams can
consist of horizontal strands is for each factor to consist of horizontal strands. This file
turns that observation into the structure of the idempotents of the strands algebra `A(n)` of
Lipshitz, Ozsváth and Thurston and of its matched subalgebra
`TauCeti.StrandsAlgebra.matchedSubalgebra`.

The *length* of a diagram `φ` (`TauCeti.StrandDiagram.length`, defined with the grading) is the
total distance its strands climb, measured by the positions of their end points in the order of
`α`. It is additive under concatenation, nonnegative, bounded by `(#α)²`, and it vanishes exactly
on the identity diagrams `idOn S`. Consequently:

* the *horizontal part* (`TauCeti.StrandsAlgebra.horizontalPart`), the projection onto the span
  of the idempotents `I(S)`, is an algebra endomorphism, and it is the sum
  `∑ₛ x_{I(S)} I(S)` of the coefficients of `x` on the identity diagrams;
* its kernel is nil: an element with zero horizontal part has vanishing `((#α)² + 1)`-st power
  (`TauCeti.StrandsAlgebra.pow_eq_zero_of_horizontalPart_eq_zero`), because a product of
  diagrams that are not identity diagrams has length at least the number of factors.

A diagram from `S` to `S` has length zero, so it is `idOn S`: over any commutative semiring the
corner `I(S) A(n) I(S)` is spanned by `I(S)`, with `I(S) x I(S) = x_{I(S)} I(S)`
(`TauCeti.StrandsAlgebra.idem_mul_mul_idem`). Hence the idempotents of the corner ring are the
`c I(S)` with `c` an idempotent of the coefficient ring
(`TauCeti.StrandsAlgebra.eq_smul_idem_of_isIdempotentElem`), and when the
coefficient ring has no idempotents besides `0` and `1`, as over `𝔽₂`, each `I(S)` is a primitive
idempotent of `A(n)` (`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`).

For the matched subalgebra of a matching `M`, the idempotent `I(s)` is the sum of the `I(S)` over
the sets `S` containing exactly one point over each element of `s`. An element of the matched
subalgebra has the same coefficient on all of these `I(S)`, because any two such sets are related
by moving horizontal strands between matched points one at a time. The corner of `I(s)` contains
diagrams that climb, so here the nilpotence of the kernel of the horizontal part is needed: an
idempotent `e` in that corner agrees with `c I(s)` modulo a nilpotent element, and the two
commute, so they are equal. Hence the idempotents of the matched subalgebra lying in the corner of
`I(s)` are the `c I(s)`
(`TauCeti.StrandsAlgebra.exists_isIdempotentElem_and_eq_smul_matchedIdem`); for coefficients
without nontrivial idempotents they are `0` and `I(s)`
(`TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`).

So the `I(s)` are primitive idempotents of the matched subalgebra, although for a matched pair
with two points `I(s)` splits in `A(n)` as the sum of the two orthogonal `I(S)`. Over any
commutative semiring the coefficient at an identity diagram `I(S)` is multiplicative
(`TauCeti.StrandsAlgebra.repr_mul_apply_idOn`), so a decomposition `I(s) = f₁ + f₂` into
orthogonal idempotents of the matched subalgebra gives a decomposition of `1` by the coefficients
at `I(S)`; an idempotent in the corner of `I(s)` whose coefficient at `I(S)` vanishes has zero
horizontal part and is zero. Hence `I(s)` is a primitive idempotent of the matched subalgebra
exactly when `s` is a set of matched pairs and `1` is primitive in the coefficient semiring
(`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`). Together with
`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`, the `I(s)` form a complete
family of orthogonal primitive idempotents of `A(Z)` over `𝔽₂`.

## Main definitions

* `TauCeti.StrandsAlgebra.horizontalPart`: the projection onto the span of the `I(S)`, as an
  algebra endomorphism.

## Main results

* `TauCeti.StrandsAlgebra.horizontalPart_eq_sum`: the horizontal part is `∑ₛ x_{I(S)} I(S)`.
* `TauCeti.StrandsAlgebra.pow_eq_zero_of_horizontalPart_eq_zero`: elements with zero horizontal
  part are nilpotent.
* `TauCeti.StrandsAlgebra.idem_mul_mul_idem`: the corner of `I(S)` in `A(n)` is spanned by
  `I(S)`.
* `TauCeti.StrandsAlgebra.eq_smul_idem_of_isIdempotentElem` and
  `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`: the idempotents of the corner of `I(S)` in
  `A(n)`, and primitivity of `I(S)`.
* `TauCeti.StrandsAlgebra.exists_isIdempotentElem_and_eq_smul_matchedIdem` and
  `TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`: the idempotents of the
  corner of `I(s)` in the matched subalgebra.
* `TauCeti.StrandsAlgebra.repr_mul_apply_idOn`: the coefficient at an identity diagram is
  multiplicative.
* `TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero`: an idempotent
  in the corner of `I(s)` in the matched subalgebra with a vanishing coefficient at an identity
  diagram over `s` is zero.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`: `I(s)` is a primitive
  idempotent of the matched subalgebra exactly when `s` is a set of matched pairs and `1` is
  primitive in the coefficient semiring.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 and
  §3.2 (the strands algebra, the algebra `A(Z)` and its idempotents `I(s)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

section CommSemiring

variable {R α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- The projection onto the identity diagrams, on basis elements. -/
private def horizontalPartLinear : StrandsAlgebra R α →ₗ[R] StrandsAlgebra R α :=
  (basis R α).constr R fun φ ↦ if φ = idOn φ.source then of φ else 0

private theorem horizontalPartLinear_of (φ : StrandDiagram α) :
    horizontalPartLinear (of φ : StrandsAlgebra R α) =
      if φ = idOn φ.source then of φ else 0 := by
  rw [horizontalPartLinear, ← basis_apply, Module.Basis.constr_basis, basis_apply]

private theorem horizontalPartLinear_idem (s : Finset α) :
    horizontalPartLinear (idem s : StrandsAlgebra R α) = idem s := by
  rw [idem_def, horizontalPartLinear_of, source_idOn, ite_eq_left rfl]

private theorem horizontalPartLinear_of_mul_of (φ ψ : StrandDiagram α) :
    horizontalPartLinear (of φ * of ψ : StrandsAlgebra R α) =
      horizontalPartLinear (of φ) * horizontalPartLinear (of ψ) := by
  simp only [horizontalPartLinear_of]
  by_cases hc : φ.Composable ψ
  · have key := trans_eq_idOn_source_iff hc.target_eq
    rw [of_mul_of_of_composable hc, horizontalPartLinear_of]
    by_cases hφ : φ = idOn φ.source <;> by_cases hψ : ψ = idOn ψ.source
    · rw [ite_eq_left (key.2 ⟨hφ, hψ⟩), ite_eq_left hφ, ite_eq_left hψ,
        of_mul_of_of_composable hc]
    · rw [ite_eq_right fun h ↦ hψ (key.1 h).2, ite_eq_right hψ, mul_zero]
    · rw [ite_eq_right fun h ↦ hφ (key.1 h).1, ite_eq_right hφ, zero_mul]
    · rw [ite_eq_right fun h ↦ hφ (key.1 h).1, ite_eq_right hφ, zero_mul]
  · rw [of_mul_of_of_not_composable hc, map_zero]
    split_ifs <;> simp [of_mul_of_of_not_composable hc]

variable (R α) in
/-- The **horizontal part** of an element of the strands algebra: the part of it supported on
the identity diagrams `I(S)`, which is `∑ₛ x_{I(S)} I(S)`
(`TauCeti.StrandsAlgebra.horizontalPart_eq_sum`). Since a concatenation of diagrams is an
identity diagram only when both factors are, it is an algebra endomorphism. Its kernel, the span
of the diagrams with a strand that climbs, consists of nilpotent elements
(`TauCeti.StrandsAlgebra.pow_eq_zero_of_horizontalPart_eq_zero`). -/
def horizontalPart : StrandsAlgebra R α →ₐ[R] StrandsAlgebra R α :=
  AlgHom.ofLinearMap horizontalPartLinear
    (by rw [← sum_idem, map_sum]; simp only [horizontalPartLinear_idem])
    (map_mul_of_basis _ horizontalPartLinear_of_mul_of)

/-- The horizontal part of a basis element is the element itself if it is an identity diagram,
and zero otherwise. -/
theorem horizontalPart_of (φ : StrandDiagram α) :
    horizontalPart R α (of φ) = if φ = idOn φ.source then of φ else 0 :=
  horizontalPartLinear_of φ

@[simp]
theorem horizontalPart_idem (s : Finset α) : horizontalPart R α (idem s) = idem s :=
  horizontalPartLinear_idem s

/-- The coefficients of the horizontal part are those of the element on the identity diagrams
and zero elsewhere. -/
theorem repr_horizontalPart_apply (x : StrandsAlgebra R α) (φ : StrandDiagram α) :
    (basis R α).repr (horizontalPart R α x) φ =
      if φ = idOn φ.source then (basis R α).repr x φ else 0 := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, ite_add_zero]
  | smul_of r ψ =>
    simp only [map_smul, Finsupp.smul_apply, horizontalPart_of]
    by_cases hψφ : ψ = φ
    · subst hψφ
      split_ifs <;> simp
    · split_ifs <;> simp [← basis_apply, hψφ]

/-- **The horizontal part is the combination of the `I(S)` with the coefficients of the element
on the identity diagrams.** -/
theorem horizontalPart_eq_sum (x : StrandsAlgebra R α) :
    horizontalPart R α x = ∑ s : Finset α, (basis R α).repr x (idOn s) • idem s := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply, add_smul, sum_add_distrib]
  | smul_of r φ =>
    have hterm (s : Finset α) : (basis R α).repr (r • of φ) (idOn s) •
        (idem s : StrandsAlgebra R α) = if φ = idOn s then r • of φ else 0 := by
      rw [map_smul, Finsupp.smul_apply, ← basis_apply, Module.Basis.repr_self_apply, smul_eq_mul]
      split_ifs with h
      · rw [mul_one, idem_def, h, basis_apply]
      · rw [mul_zero, zero_smul]
    -- Only `s = φ.source` can make `φ` the identity diagram on `s`.
    rw [sum_congr rfl fun s _ ↦ hterm s, map_smul, horizontalPart_of,
      sum_eq_single φ.source (fun s _ hs ↦ ite_eq_right fun h ↦ hs (by rw [h, source_idOn]))
        (fun h ↦ absurd (mem_univ _) h)]
    split_ifs <;> simp

/-- The horizontal part is a projection. -/
@[simp]
theorem horizontalPart_horizontalPart (x : StrandsAlgebra R α) :
    horizontalPart R α (horizontalPart R α x) = horizontalPart R α x := by
  rw [horizontalPart_eq_sum x, map_sum]
  simp only [map_smul, horizontalPart_idem]

/-- The horizontal part of `I(S) x` is `x_{I(S)} I(S)`. -/
theorem idem_mul_horizontalPart (s : Finset α) (x : StrandsAlgebra R α) :
    idem s * horizontalPart R α x = (basis R α).repr x (idOn s) • idem s := by
  simp only [horizontalPart_eq_sum, mul_sum, mul_smul_comm, idem_mul_idem, smul_ite, smul_zero,
    sum_ite_eq, mem_univ, ↓reduceIte]

/-- **The corner `I(S) A(n) I(S)` is spanned by `I(S)`**: a diagram from `S` to `S` has length
zero, so it is the identity diagram, and `I(S) x I(S)` is `x_{I(S)} I(S)`. -/
theorem idem_mul_mul_idem (s : Finset α) (x : StrandsAlgebra R α) :
    idem s * x * idem s = (basis R α).repr x (idOn s) • idem s := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy, map_add, Finsupp.add_apply, add_smul]
  | smul_of r φ =>
    rw [mul_smul_comm, smul_mul_assoc, idem_mul_of, map_smul, Finsupp.smul_apply, ← basis_apply,
      Module.Basis.repr_self_apply, basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul,
      zero_smul]
    by_cases hφ : s = φ.source ∧ φ.target = s
    · obtain ⟨rfl, ht⟩ := hφ
      have hid : φ = idOn φ.source :=
        length_eq_zero_iff.1 (by simp [length_def, boundary_apply, ht])
      rw [ite_eq_left rfl, of_mul_idem, ite_eq_left ht, ite_eq_left hid, idem_def, ← hid]
    · have hne : φ ≠ idOn s := fun h ↦ hφ ⟨by rw [h, source_idOn], by rw [h, target_idOn]⟩
      rw [ite_eq_right hne]
      split_ifs with hs
      · rw [of_mul_idem, ite_eq_right fun ht ↦ hφ ⟨hs, ht⟩, smul_zero]
      · rw [zero_mul, smul_zero]

/-- Every element `x` of the corner `I(S) A(n) I(S)`, that is with `I(S) x = x = x I(S)`, is the
multiple `x_{I(S)} I(S)` of `I(S)` by its coefficient on `I(S)`. -/
theorem eq_smul_idem_of_idem_mul_eq_of_mul_idem_eq {x : StrandsAlgebra R α} {s : Finset α}
    (hl : idem s * x = x) (hr : x * idem s = x) : x = (basis R α).repr x (idOn s) • idem s := by
  rw [← idem_mul_mul_idem, hl, hr]

/-- **The idempotents of the corner ring `I(S) A(n) I(S)`** are the multiples `c I(S)` by
idempotents `c` of the coefficient ring; `c` is the coefficient of the idempotent on `I(S)`. -/
theorem eq_smul_idem_of_isIdempotentElem {e : StrandsAlgebra R α} {s : Finset α}
    (he : IsIdempotentElem e) (hl : idem s * e = e) (hr : e * idem s = e) :
    IsIdempotentElem ((basis R α).repr e (idOn s)) ∧
      e = (basis R α).repr e (idOn s) • idem s := by
  have hes := eq_smul_idem_of_idem_mul_eq_of_mul_idem_eq hl hr
  set c := (basis R α).repr e (idOn s)
  refine ⟨?_, hes⟩
  have h := congrArg (fun y ↦ (basis R α).repr y (idOn s)) he.eq
  rw [hes, smul_mul_smul_comm, (isIdempotentElem_idem s).eq] at h
  simp only [map_smul, Finsupp.smul_apply, idem_def, ← basis_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at h
  exact h

/-- The horizontal part fixes the idempotents `I(s)` of the matched subalgebra. -/
@[simp]
theorem horizontalPart_matchedIdem {β : Type*} [DecidableEq β] (M : α → β) (s : Finset β) :
    horizontalPart R α (matchedIdem R M s) = matchedIdem R M s := by
  simp only [matchedIdem_def, map_sum, horizontalPart_idem]

/-- **The coefficient at an identity diagram is multiplicative**: the coefficient of `x y` at
`I(S)` is the product of those of `x` and `y`, because the horizontal part is multiplicative. -/
theorem repr_mul_apply_idOn (x y : StrandsAlgebra R α) (S : Finset α) :
    (basis R α).repr (x * y) (idOn S) =
      (basis R α).repr x (idOn S) * (basis R α).repr y (idOn S) := by
  have h := idem_mul_horizontalPart S (x * y)
  rw [map_mul, ← mul_assoc, idem_mul_horizontalPart, smul_mul_assoc, idem_mul_horizontalPart,
    smul_smul] at h
  have h' := congrArg (fun z ↦ (basis R α).repr z (idOn S)) h
  simp only [map_smul, Finsupp.smul_apply, idem_def, ← basis_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
  exact h'.symm

/-! ### The nilpotence of the kernel of the horizontal part -/

variable (R α) in
/-- The span of the diagrams of length at least `k`. These submodules form a multiplicative
filtration that vanishes beyond `(#α)²`. -/
private def lengthFiltration (k : ℤ) : Submodule R (StrandsAlgebra R α) :=
  Submodule.span R ((fun φ ↦ (of φ : StrandsAlgebra R α)) '' {φ | k ≤ φ.length})

private theorem mul_mem_lengthFiltration {k l : ℤ} {a b : StrandsAlgebra R α}
    (ha : a ∈ lengthFiltration R α k) (hb : b ∈ lengthFiltration R α l) :
    a * b ∈ lengthFiltration R α (k + l) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨φ, hφ, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨ψ, hψ, rfl⟩ := hb
      by_cases hc : φ.Composable ψ
      · rw [of_mul_of_of_composable hc]
        refine Submodule.subset_span ⟨φ.trans ψ, ?_, rfl⟩
        rw [Set.mem_ofPred_eq, length_trans_of_target_eq hc.target_eq]
        exact add_le_add hφ hψ
      · rw [of_mul_of_of_not_composable hc]
        exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

private theorem lengthFiltration_eq_bot {k : ℤ} (hk : (Fintype.card α : ℤ) ^ 2 < k) :
    lengthFiltration R α k = ⊥ := by
  refine Submodule.span_eq_bot.2 fun x ⟨φ, hφ, _⟩ ↦ ?_
  exact absurd ((φ.length_le.trans_lt hk).trans_le hφ) (lt_irrefl _)

private theorem mem_lengthFiltration_one {x : StrandsAlgebra R α}
    (hx : horizontalPart R α x = 0) : x ∈ lengthFiltration R α 1 := by
  rw [← (basis R α).linearCombination_repr x, Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun φ _ ↦ ?_
  rw [basis_apply]
  by_cases hφ : φ = idOn φ.source
  · have h := repr_horizontalPart_apply x φ
    rw [hx, ite_eq_left hφ, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    rw [← h, zero_smul]
    exact zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ, length_pos hφ, rfl⟩)

/-- **Elements with zero horizontal part are nilpotent:** a product of `n` diagrams that are not
identity diagrams has length at least `n`, and no diagram is longer than `(#α)²`. -/
theorem pow_eq_zero_of_horizontalPart_eq_zero {x : StrandsAlgebra R α}
    (hx : horizontalPart R α x = 0) : x ^ (Fintype.card α ^ 2 + 1) = 0 := by
  have hx₁ := mem_lengthFiltration_one hx
  have hpow (n : ℕ) : x ^ (n + 1) ∈ lengthFiltration R α (n + 1) := by
    induction n with
    | zero => simpa using hx₁
    | succ n ih =>
      rw [pow_succ]
      have := mul_mem_lengthFiltration ih hx₁
      push_cast
      exact this
  have h := hpow (Fintype.card α ^ 2)
  rw [lengthFiltration_eq_bot (by push_cast; omega), Submodule.mem_bot] at h
  exact h

/-- Elements with zero horizontal part are nilpotent. -/
theorem isNilpotent_of_horizontalPart_eq_zero {x : StrandsAlgebra R α}
    (hx : horizontalPart R α x = 0) : IsNilpotent x :=
  ⟨_, pow_eq_zero_of_horizontalPart_eq_zero hx⟩

end CommSemiring

/-! ### Idempotents in the corners of the idempotents -/

section CommRing

variable {R α : Type*} [CommRing R] [LinearOrder α] [Fintype α]

/-- An idempotent `e` in the corner of an idempotent `i` fixed by the horizontal part, whose own
horizontal part is `c i`, is `c i`, and `c` is idempotent when `i` has coefficient `1` on some
diagram: the difference `e - c i` has zero horizontal part, so it is nilpotent, and `e` commutes
with `c i`. -/
private theorem eq_smul_of_horizontalPart_eq_smul {e i : StrandsAlgebra R α} {c : R}
    {φ : StrandDiagram α} (he : IsIdempotentElem e) (hi : IsIdempotentElem i)
    (hih : horizontalPart R α i = i) (hiφ : (basis R α).repr i φ = 1)
    (hl : i * e = e) (hr : e * i = e) (hhe : horizontalPart R α e = c • i) :
    IsIdempotentElem c ∧ e = c • i := by
  have hc : IsIdempotentElem c := by
    have h := congrArg (fun y ↦ (basis R α).repr y φ) (he.map (horizontalPart R α)).eq
    simp only [hhe, smul_mul_smul_comm, hi.eq, map_smul, Finsupp.smul_apply, hiφ,
      smul_eq_mul, mul_one] at h
    exact h
  have hci : IsIdempotentElem (c • i) := by
    rw [IsIdempotentElem, smul_mul_smul_comm, hc.eq, hi.eq]
  refine ⟨hc, eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he hci
    (isNilpotent_of_horizontalPart_eq_zero ?_) ?_⟩
  · rw [map_sub, map_smul, hhe, hih, sub_self]
  · rw [Commute, SemiconjBy, mul_smul_comm, hr, smul_mul_assoc, hl]

/-- Over a coefficient ring without idempotents besides `0` and `1`, a multiple of an element by
an idempotent scalar is `0` or the element itself. -/
private theorem smul_eq_zero_or_eq_of_isIdempotentElem (hR : IsPrimitiveIdempotent (1 : R))
    {c : R} (hc : IsIdempotentElem c) (x : StrandsAlgebra R α) : c • x = 0 ∨ c • x = x := by
  have := hR.nontrivial
  rcases isPrimitiveIdempotent_one_iff.1 hR c hc with h | h
  · exact Or.inl (by rw [h, zero_smul])
  · exact Or.inr (by rw [h, one_smul])

/-- **The idempotents `I(S)` of the strands algebra are primitive** when the coefficient ring has
no idempotents besides `0` and `1`, for instance over a field such as `𝔽₂`. -/
theorem isPrimitiveIdempotent_idem (hR : IsPrimitiveIdempotent (1 : R)) (s : Finset α) :
    IsPrimitiveIdempotent (idem s : StrandsAlgebra R α) := by
  have := hR.nontrivial
  refine isPrimitiveIdempotent_of_eq_zero_or_eq (isIdempotentElem_idem s)
    (by rw [idem_def, ← basis_apply]; exact (basis R α).ne_zero _) fun f hf hl hr ↦ ?_
  obtain ⟨hc, hf'⟩ := eq_smul_idem_of_isIdempotentElem hf hl hr
  rw [hf']
  exact smul_eq_zero_or_eq_of_isIdempotentElem hR hc _

/-! ### Idempotents of the matched subalgebra -/

variable {β : Type*} [DecidableEq β] {M : α → β}

/-- **The idempotents of the matched subalgebra in the corner of `I(s)`** are the multiples
`c I(s)` by idempotents `c` of the coefficient ring. -/
theorem exists_isIdempotentElem_and_eq_smul_matchedIdem {e : StrandsAlgebra R α} {s : Finset β}
    (hm : e ∈ matchedSubalgebra R M) (he : IsIdempotentElem e)
    (hl : matchedIdem R M s * e = e) (hr : e * matchedIdem R M s = e) :
    ∃ c : R, IsIdempotentElem c ∧ e = c • matchedIdem R M s := by
  by_cases hsec : ∃ S : Finset α, S.image M = s ∧ #S = #s
  · obtain ⟨S₀, hS₀, hcard₀⟩ := hsec
    set c := (basis R α).repr e (idOn S₀)
    have hmem {S : Finset α} (h : S.image M = s ∧ #S = #s) : S ∈ matchedChoices M s :=
      mem_matchedChoices.2 ⟨h.1, card_image_iff.1 (by rw [h.1, h.2])⟩
    -- The horizontal part of `e` is that of `I(s) e`, and all its coefficients on the sets over
    -- `s` agree with `c`.
    have hhe : horizontalPart R α e = c • matchedIdem R M s := by
      conv_lhs => rw [← hl, map_mul, horizontalPart_matchedIdem, matchedIdem_def, sum_mul]
      rw [matchedIdem_def, smul_sum]
      refine sum_congr rfl fun S hS ↦ ?_
      rw [idem_mul_horizontalPart]
      congr 1
      exact repr_apply_idOn_eq hm (hmem (mem_filter.1 hS).2) (hmem ⟨hS₀, hcard₀⟩)
    refine ⟨c, eq_smul_of_horizontalPart_eq_smul (φ := idOn S₀) he
      (isIdempotentElem_matchedIdem M s) (horizontalPart_matchedIdem M s) ?_ hl hr hhe⟩
    rw [repr_matchedIdem_apply, source_idOn, ite_eq_left ⟨rfl, hS₀, hcard₀⟩]
  · -- No set lies over `s`, so `I(s) = 0` and hence `e = 0`.
    have h0 : matchedIdem R M s = 0 := by
      rw [matchedIdem_def]
      exact sum_eq_zero fun S hS ↦ absurd ⟨S, (mem_filter.1 hS).2⟩ hsec
    refine ⟨0, IsIdempotentElem.zero, ?_⟩
    rw [h0, smul_zero, ← hl, h0, zero_mul]

/-- **The idempotents `I(s)` do not split in the matched subalgebra** when the coefficient ring
has no idempotents besides `0` and `1`: the only idempotents of the matched subalgebra in the
corner of `I(s)` are `0` and `I(s)`. -/
theorem eq_zero_or_eq_matchedIdem_of_isIdempotentElem (hR : IsPrimitiveIdempotent (1 : R))
    {e : StrandsAlgebra R α} {s : Finset β} (hm : e ∈ matchedSubalgebra R M)
    (he : IsIdempotentElem e) (hl : matchedIdem R M s * e = e)
    (hr : e * matchedIdem R M s = e) : e = 0 ∨ e = matchedIdem R M s := by
  obtain ⟨c, hc, rfl⟩ := exists_isIdempotentElem_and_eq_smul_matchedIdem hm he hl hr
  exact smul_eq_zero_or_eq_of_isIdempotentElem hR hc _

end CommRing

/-! ### The primitive idempotents of the matched subalgebra -/

section MatchedSubalgebra

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [DecidableEq β]
  {M : α → β} {s : Finset β}

/-- **The idempotents of the corner of `I(s)` vanishing at an identity diagram.** An idempotent
`x` of the matched subalgebra with `I(s) x = x` whose coefficient vanishes at the identity diagram
of some set `S` of points over `s` is zero: its coefficients vanish at all the identity diagrams,
so it has zero horizontal part and is nilpotent. -/
theorem eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) (hxx : IsIdempotentElem x) (hex : matchedIdem R M s * x = x)
    {S : Finset α} (hS : S ∈ matchedChoices M s) (h0 : (basis R α).repr x (idOn S) = 0) :
    x = 0 := by
  refine hxx.eq_zero_of_isNilpotent (isNilpotent_of_horizontalPart_eq_zero
    ((basis R α).repr.injective (Finsupp.ext fun φ ↦ ?_)))
  rw [repr_horizontalPart_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  refine ite_eq_right_iff.2 fun hφ ↦ ?_
  rw [hφ]
  by_cases hT : φ.source ∈ matchedChoices M s
  · rw [← repr_apply_idOn_eq hx hS hT, h0]
  · rw [← hex, repr_matchedIdem_mul_apply, source_idOn]
    simp [hT]

/-- **The idempotents `I(s)` are primitive.** The idempotent `I(s)` of the matched subalgebra is
primitive exactly when `s` is a set of matched pairs and `1` is primitive in the ground semiring,
that is, the ground semiring is nontrivial and `1` is not the sum of two nonzero orthogonal
idempotents, as for `𝔽₂`. -/
theorem isPrimitiveIdempotent_matchedIdem_iff :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) ↔
      IsPrimitiveIdempotent (1 : R) ∧ s ⊆ univ.image M := by
  set e : matchedSubalgebra R M := ⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩
  have he : IsIdempotentElem e := Subtype.ext (isIdempotentElem_matchedIdem M s)
  constructor
  · intro hprim
    have hs : s ⊆ univ.image M := by
      by_contra hs
      exact hprim.ne_zero (Subtype.ext ((matchedIdem_eq_horizontalCompletion M s).trans
        (horizontalCompletion_eq_zero_of_not_subset _ hs)))
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    have : Nontrivial R := by
      refine (subsingleton_or_nontrivial R).resolve_left fun _ ↦ hprim.ne_zero ?_
      exact Subtype.ext ((basis R α).repr.injective (Subsingleton.elim _ _))
    -- A decomposition `1 = a + b` gives the decomposition `I(s) = a I(s) + b I(s)`, and the
    -- coefficient of `r I(s)` at `I(S)` is `r`.
    have hcoeff (r : R) : (basis R α).repr ((r • e : matchedSubalgebra R M) : StrandsAlgebra R α)
        (idOn S) = r := by
      rw [NonUnitalSubalgebra.coe_smul, map_smul, Finsupp.smul_apply,
        repr_matchedIdem_apply_idOn hS, smul_eq_mul, mul_one]
    have hidem {r : R} (hr : IsIdempotentElem r) : IsIdempotentElem (r • e) := by
      rw [IsIdempotentElem, smul_mul_smul_comm, hr.eq, he.eq]
    have horth {r r' : R} (h : r * r' = 0) : (r • e) * (r' • e) = 0 := by
      rw [smul_mul_smul_comm, h, zero_smul]
    refine ⟨⟨.one, one_ne_zero, fun {a b} ha hb hab hba hsum ↦ ?_⟩, hs⟩
    refine (hprim.eq_zero_or_eq_zero_of_add (hidem ha) (hidem hb) (horth hab) (horth hba)
      (by rw [← add_smul, hsum, one_smul])).imp (fun h ↦ ?_) fun h ↦ ?_
    · rw [← hcoeff a, h]
      simp
    · rw [← hcoeff b, h]
      simp
  · rintro ⟨h1, hs⟩
    have := h1.nontrivial
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    refine ⟨he, fun he0 ↦ ?_, fun {f₁ f₂} h₁ h₂ h₁₂ h₂₁ hsum ↦ ?_⟩
    · -- The ambient element of `e = 0` is `I(s) = 0`, but `I(s)` has coefficient `1` at `I(S)`.
      have h0 : matchedIdem R M s = 0 := by simpa [e] using congrArg Subtype.val he0
      simpa [h0] using repr_matchedIdem_apply_idOn (R := R) hS
    -- The coefficients at `I(S)` decompose `1` into orthogonal idempotents of `R`, so one of them
    -- vanishes, and then so does the corresponding summand.
    have hmul (f g : matchedSubalgebra R M) : (basis R α).repr (f * g : matchedSubalgebra R M)
        (idOn S) = (basis R α).repr f (idOn S) * (basis R α).repr g (idOn S) :=
      repr_mul_apply_idOn _ _ _
    have hcorner₁ : e * f₁ = f₁ := by rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero]
    have hcorner₂ : e * f₂ = f₂ := by rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add]
    have hone : (basis R α).repr f₁ (idOn S) + (basis R α).repr f₂ (idOn S) = 1 := by
      rw [← Finsupp.add_apply, ← map_add]
      exact (congrArg (fun y ↦ (basis R α).repr y (idOn S)) (congrArg Subtype.val hsum)).trans
        (repr_matchedIdem_apply_idOn hS)
    refine (h1.eq_zero_or_eq_zero_of_add (by rw [IsIdempotentElem, ← hmul, h₁.eq])
      (by rw [IsIdempotentElem, ← hmul, h₂.eq]) (by rw [← hmul, h₁₂]; simp)
      (by rw [← hmul, h₂₁]; simp) hone).imp (fun h ↦ ?_) fun h ↦ ?_
    · exact Subtype.ext (eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero f₁.2
        (congrArg Subtype.val h₁.eq) (congrArg Subtype.val hcorner₁) hS h)
    · exact Subtype.ext (eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero f₂.2
        (congrArg Subtype.val h₂.eq) (congrArg Subtype.val hcorner₂) hS h)

end MatchedSubalgebra

end StrandsAlgebra

end TauCeti
