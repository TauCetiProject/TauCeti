/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic
import Mathlib.RingTheory.Idempotents

/-!
# The primitive idempotents of the strands algebra and of the algebra of a matching

Every strand of a strand diagram goes upwards, so the only way a concatenation of diagrams can
consist of horizontal strands is for each factor to consist of horizontal strands. This file
turns that observation into the structure of the idempotents of the strands algebra `A(n)` of
Lipshitz, Ozsváth and Thurston and of its matched subalgebra `A(Z)`.

The *length* of a diagram `φ` (`TauCeti.StrandDiagram.length`) is the total distance its strands
climb, measured by the positions of their end points in the order of `α`. It is additive under
concatenation, nonnegative, bounded by `(#α)²`, and it vanishes exactly on the identity diagrams
`idOn S`. Consequently:

* the *horizontal part* (`TauCeti.StrandsAlgebra.horizontalPart`), the projection onto the span
  of the idempotents `I(S)`, is an algebra endomorphism, and it is the sum
  `∑ₛ x_{I(S)} I(S)` of the coefficients of `x` on the identity diagrams;
* its kernel is nil: an element with zero horizontal part has vanishing `((#α)² + 1)`-st power
  (`TauCeti.StrandsAlgebra.pow_eq_zero_of_horizontalPart_eq_zero`), because a product of
  diagrams that are not identity diagrams has length at least the number of factors.

An idempotent `e` with `I(S) e = e = e I(S)` therefore agrees with `c I(S)` modulo a nilpotent
element, `c` being its coefficient on `I(S)`; the two commute, so they are equal. Hence the
idempotents of the corner ring `I(S) A(n) I(S)` are the `c I(S)` with `c` an idempotent of the
coefficient ring (`TauCeti.StrandsAlgebra.eq_smul_idem_of_isIdempotentElem`), and when the
coefficient ring has no idempotents besides `0` and `1`, as over `𝔽₂`, each `I(S)` is a primitive
idempotent of `A(n)` (`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`).

For the matched subalgebra of a matching `M`, the idempotent `I(s)` is the sum of the `I(S)` over
the sets `S` containing exactly one point over each element of `s`. An element of the matched
subalgebra has the same coefficient on all of these `I(S)`, because any two such sets are related
by moving horizontal strands between matched points one at a time. The same argument then shows
that the idempotents of the matched subalgebra lying in the corner of `I(s)` are the `c I(s)`
(`TauCeti.StrandsAlgebra.eq_smul_matchedIdem_of_isIdempotentElem`); for coefficients without
nontrivial idempotents they are `0` and `I(s)`
(`TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`). So each nonzero `I(s)`
is a primitive idempotent of the algebra `A(Z)` of a pointed matched circle, although for a matched
pair with two points `I(s)` splits in `A(n)` as the sum of the two orthogonal `I(S)`.

## Main definitions

* `TauCeti.StrandDiagram.length`: the total length of the strands of a diagram.
* `TauCeti.StrandsAlgebra.horizontalPart`: the projection onto the span of the `I(S)`, as an
  algebra endomorphism.

## Main results

* `TauCeti.StrandDiagram.length_eq_zero_iff`: a diagram has length zero exactly when it is an
  identity diagram.
* `TauCeti.StrandDiagram.trans_eq_idOn_source_iff`: a concatenation is an identity diagram exactly
  when both factors are.
* `TauCeti.StrandsAlgebra.horizontalPart_eq_sum`: the horizontal part is `∑ₛ x_{I(S)} I(S)`.
* `TauCeti.StrandsAlgebra.pow_eq_zero_of_horizontalPart_eq_zero`: elements with zero horizontal
  part are nilpotent.
* `TauCeti.StrandsAlgebra.eq_smul_idem_of_isIdempotentElem` and
  `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`: the idempotents of the corner of `I(S)` in
  `A(n)`, and primitivity of `I(S)`.
* `TauCeti.StrandsAlgebra.eq_smul_matchedIdem_of_isIdempotentElem` and
  `TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`: the idempotents of the
  corner of `I(s)` in the matched subalgebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 and
  §3.2 (the strands algebra, the algebra `A(Z)` and its idempotents `I(s)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The total length of the strands of a diagram `φ : S → T`: the sum, over its strands, of the
number of points of `α` that the strand climbs, `∑_{x ∈ S} (r (φ x) - r x)` where `r x` is the
number of points below `x` (`TauCeti.StrandDiagram.length_eq_sum`). It is written through the
boundary of the class of `φ`, so that it is visibly additive under concatenation. -/
def length (φ : StrandDiagram α) : ℤ :=
  ∑ x, (#{y | y < x} : ℤ) * φ.boundary x

theorem length_def (φ : StrandDiagram α) :
    φ.length = ∑ x, (#{y | y < x} : ℤ) * φ.boundary x :=
  (rfl)

/-- A strand starts at or below its end point, so fewer points lie below its start. -/
private theorem card_filter_lt_le_card_filter_lt_endpoint {φ : StrandDiagram α} {x : α}
    (hx : x ∈ φ.source) : #{y | y < x} ≤ #{y | y < φ.endpoint x} :=
  card_le_card fun y hy ↦ by
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy.trans_le (φ.le_of_mem (endpoint_mem hx))

/-- A strand with as many points below its end point as below its start is horizontal. -/
private theorem endpoint_eq_of_card_filter_lt_eq {φ : StrandDiagram α} {x : α}
    (hx : x ∈ φ.source) (h : #{y | y < φ.endpoint x} = #{y | y < x}) : φ.endpoint x = x := by
  by_contra hne
  have hlt : x < φ.endpoint x := (φ.le_of_mem (endpoint_mem hx)).lt_of_ne (Ne.symm hne)
  refine h.not_gt (card_lt_card ⟨fun y hy ↦ ?_, fun hsub ↦ ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy.trans hlt
  · have hxx := hsub (by simpa using hlt)
    simp at hxx

/-- The length of a diagram is the sum, over its strands, of the number of points the strand
climbs. -/
theorem length_eq_sum (φ : StrandDiagram α) :
    φ.length = ∑ x ∈ φ.source, ((#{y | y < φ.endpoint x} : ℤ) - #{y | y < x}) := by
  have himage : ∑ x ∈ φ.target, (#{y | y < x} : ℤ) =
      ∑ x ∈ φ.source, (#{y | y < φ.endpoint x} : ℤ) := by
    rw [target_eq_image, sum_image φ.injOn_getD]
    simp only [endpoint_def]
  simp only [length_def, boundary_apply, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib,
    sum_ite_mem, univ_inter, himage]

/-- The length of a diagram is nonnegative: every strand goes upwards. -/
theorem length_nonneg (φ : StrandDiagram α) : 0 ≤ φ.length := by
  rw [length_eq_sum]
  exact sum_nonneg fun x hx ↦ sub_nonneg.2 (by
    exact_mod_cast card_filter_lt_le_card_filter_lt_endpoint hx)

@[simp]
theorem length_idOn (s : Finset α) : (idOn s).length = 0 := by
  simp [length_def]

/-- **A diagram has length zero exactly when it is an identity diagram.** -/
theorem length_eq_zero_iff {φ : StrandDiagram α} : φ.length = 0 ↔ φ = idOn φ.source := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ length_idOn _⟩
  rw [length_eq_sum] at h
  have hterm := (sum_eq_zero_iff_of_nonneg fun x hx ↦ sub_nonneg.2 (by
    exact_mod_cast card_filter_lt_le_card_filter_lt_endpoint hx)).1 h
  ext i j
  by_cases hi : i ∈ φ.source
  · have hend : φ.endpoint i = i :=
      endpoint_eq_of_card_filter_lt_eq hi (by exact_mod_cast sub_eq_zero.1 (hterm i hi))
    have hmem := endpoint_mem hi
    rw [hend] at hmem
    rw [idOn_apply, ite_eq_left hi, Option.mem_def.1 hmem]
  · rw [apply_eq_none_of_notMem_source hi, idOn_apply, ite_eq_right hi]

/-- A diagram that is not an identity diagram has positive length. -/
theorem length_pos {φ : StrandDiagram α} (h : φ ≠ idOn φ.source) : 0 < φ.length :=
  φ.length_nonneg.lt_of_ne fun h' ↦ h (length_eq_zero_iff.1 h'.symm)

/-- The length of a diagram is at most the square of the number of points. -/
theorem length_le (φ : StrandDiagram α) : φ.length ≤ Fintype.card α ^ 2 := by
  have hterm (x : α) : (#{y | y < x} : ℤ) * φ.boundary x ≤ Fintype.card α := by
    have hb : φ.boundary x ≤ 1 := by
      rw [boundary_apply]
      split_ifs <;> norm_num
    have hr : (#{y | y < x} : ℤ) ≤ Fintype.card α := by
      exact_mod_cast card_le_univ _
    calc (#{y | y < x} : ℤ) * φ.boundary x ≤ #{y | y < x} * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ Fintype.card α := by rwa [mul_one]
  calc φ.length ≤ ∑ _x : α, (Fintype.card α : ℤ) := sum_le_sum fun x _ ↦ hterm x
    _ = Fintype.card α ^ 2 := by simp [sq]

/-- **Lengths add under concatenation.** -/
theorem length_trans_of_target_eq {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).length = φ.length + ψ.length := by
  simp only [length_def, boundary_trans_of_target_eq h, Pi.add_apply, mul_add, sum_add_distrib]

/-- **A concatenation is an identity diagram exactly when both factors are.** -/
theorem trans_eq_idOn_source_iff {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    φ.trans ψ = idOn (φ.trans ψ).source ↔ φ = idOn φ.source ∧ ψ = idOn ψ.source := by
  rw [← length_eq_zero_iff, ← length_eq_zero_iff, ← length_eq_zero_iff,
    length_trans_of_target_eq h]
  have := φ.length_nonneg
  have := ψ.length_nonneg
  omega

end StrandDiagram

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

/-- The horizontal part of `I(S) x` is `x_{I(S)} I(S)`. -/
theorem idem_mul_horizontalPart (s : Finset α) (x : StrandsAlgebra R α) :
    idem s * horizontalPart R α x = (basis R α).repr x (idOn s) • idem s := by
  simp only [horizontalPart_eq_sum, mul_sum, mul_smul_comm, idem_mul_idem, smul_ite, smul_zero,
    sum_ite_eq, mem_univ, ↓reduceIte]

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
horizontal part is `c i` for an idempotent scalar `c`, is `c i`: the difference `e - c i` has zero
horizontal part, so it is nilpotent, and `e` commutes with `c i`. -/
private theorem eq_smul_of_horizontalPart_eq_smul {e i : StrandsAlgebra R α} {c : R}
    (he : IsIdempotentElem e) (hi : IsIdempotentElem i) (hih : horizontalPart R α i = i)
    (hl : i * e = e) (hr : e * i = e) (hc : IsIdempotentElem c)
    (hhe : horizontalPart R α e = c • i) : e = c • i := by
  have hci : IsIdempotentElem (c • i) := by
    rw [IsIdempotentElem, smul_mul_smul_comm, hc.eq, hi.eq]
  refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he hci
    (isNilpotent_of_horizontalPart_eq_zero ?_) ?_
  · rw [map_sub, map_smul, hhe, hih, sub_self]
  · rw [Commute, SemiconjBy, mul_smul_comm, hr, smul_mul_assoc, hl]

/-- **The idempotents of the corner ring `I(S) A(n) I(S)`** are the multiples `c I(S)` by
idempotents `c` of the coefficient ring; `c` is the coefficient of the idempotent on `I(S)`. -/
theorem eq_smul_idem_of_isIdempotentElem {e : StrandsAlgebra R α} {s : Finset α}
    (he : IsIdempotentElem e) (hl : idem s * e = e) (hr : e * idem s = e) :
    IsIdempotentElem ((basis R α).repr e (idOn s)) ∧
      e = (basis R α).repr e (idOn s) • idem s := by
  set c := (basis R α).repr e (idOn s)
  have hhe : horizontalPart R α e = c • idem s := by
    conv_lhs => rw [← hl, map_mul, horizontalPart_idem]
    exact idem_mul_horizontalPart s e
  have hc : IsIdempotentElem c := by
    have h := congrArg (fun y ↦ (basis R α).repr y (idOn s))
      ((he.map (horizontalPart R α)).eq)
    simp only [hhe, smul_mul_smul_comm, (isIdempotentElem_idem s).eq] at h
    exact (by simpa [idem_def, ← basis_apply, Module.Basis.repr_self_apply] using h : c * c = c)
  exact ⟨hc, eq_smul_of_horizontalPart_eq_smul he (isIdempotentElem_idem s)
    (horizontalPart_idem s) hl hr hc hhe⟩

/-- **The idempotents `I(S)` of the strands algebra are primitive** when the coefficient ring has
no idempotents besides `0` and `1`, for instance over a field such as `𝔽₂`. -/
theorem isPrimitiveIdempotent_idem (hR : IsPrimitiveIdempotent (1 : R)) (s : Finset α) :
    IsPrimitiveIdempotent (idem s : StrandsAlgebra R α) := by
  have := hR.nontrivial
  refine isPrimitiveIdempotent_of_eq_zero_or_eq (isIdempotentElem_idem s)
    (by rw [idem_def, ← basis_apply]; exact (basis R α).ne_zero _) fun f hf hl hr ↦ ?_
  obtain ⟨hc, hf'⟩ := eq_smul_idem_of_isIdempotentElem hf hl hr
  rcases (isPrimitiveIdempotent_one_iff.1 hR) _ hc with h | h
  · exact Or.inl (by rw [hf', h, zero_smul])
  · exact Or.inr (by rw [hf', h, one_smul])

/-! ### Idempotents of the matched subalgebra -/

variable {β : Type*} [DecidableEq β] {M : α → β}

/-- An element of the matched subalgebra has the same coefficient on the identity diagrams of any
two sets with the same image, each mapped injectively by `M`: such sets are related by moving
their points to matched points one at a time. The induction is on the number of points of `S`
outside `T`. -/
private theorem repr_idOn_eq_of_mem_matchedSubalgebra {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) :
    ∀ (n : ℕ) (S T : Finset α), #(S \ T) = n → S.image M = T.image M →
      #(S.image M) = #S → #(T.image M) = #T →
      (basis R α).repr x (idOn S) = (basis R α).repr x (idOn T) := by
  intro n
  induction n with
  | zero =>
    intro S T hn hST hS hT
    rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hn
    rw [eq_of_subset_of_card_le hn (by rw [← hS, ← hT, hST])]
  | succ n ih =>
    intro S T hn hST hS hT
    obtain ⟨a, ha⟩ : (S \ T).Nonempty := card_pos.1 (by omega)
    rw [mem_sdiff] at ha
    obtain ⟨b, hbT, hba⟩ : ∃ b ∈ T, M b = M a := by
      have hmem := mem_image_of_mem M ha.1
      rw [hST, mem_image] at hmem
      exact hmem
    have hinj : Set.InjOn M (S : Set α) := card_image_iff.1 hS
    have hbS : b ∉ S := fun hbS ↦ ha.2 (hinj ha.1 hbS hba.symm ▸ hbT)
    set S' := insert b (S.erase a)
    have hS'image : S'.image M = S.image M := by
      rw [image_insert, hba, ← image_insert, insert_erase ha.1]
    have hS'card : #S' = #S := by
      rw [card_insert_of_notMem fun h ↦ hbS (mem_of_mem_erase h), card_erase_of_mem ha.1]
      have := card_pos.2 ⟨a, ha.1⟩
      omega
    have hS'T : S' \ T = (S \ T).erase a := by
      ext y
      simp only [S', mem_sdiff, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hya, hyS⟩, hyT⟩
        · exact absurd hbT hyT
        · exact ⟨hya, hyS, hyT⟩
      · rintro ⟨hya, hyS, hyT⟩
        exact ⟨Or.inr ⟨hya, hyS⟩, hyT⟩
    have hswap := (mem_matchedSubalgebra.1 hx).2 (idOn S) a b hba.symm
    rw [swapHorizontal_idOn ha.1 hbS] at hswap
    rw [← hswap]
    refine ih S' T ?_ (hS'image.trans hST) (by rw [hS'image, hS'card, hS]) hT
    rw [hS'T, card_erase_of_mem (mem_sdiff.2 ha), hn, Nat.add_sub_cancel]

/-- **The idempotents of the matched subalgebra in the corner of `I(s)`** are the multiples
`c I(s)` by idempotents `c` of the coefficient ring. -/
theorem eq_smul_matchedIdem_of_isIdempotentElem {e : StrandsAlgebra R α} {s : Finset β}
    (hm : e ∈ matchedSubalgebra R M) (he : IsIdempotentElem e)
    (hl : matchedIdem R M s * e = e) (hr : e * matchedIdem R M s = e) :
    ∃ c : R, IsIdempotentElem c ∧ e = c • matchedIdem R M s := by
  by_cases hsec : ∃ S : Finset α, S.image M = s ∧ #S = #s
  · obtain ⟨S₀, hS₀, hcard₀⟩ := hsec
    set c := (basis R α).repr e (idOn S₀)
    have hhm : horizontalPart R α (matchedIdem R M s) = matchedIdem R M s := by
      simp only [matchedIdem_def, map_sum, horizontalPart_idem]
    -- The horizontal part of `e` is that of `I(s) e`, and all its coefficients on the sets over
    -- `s` agree with `c`.
    have hhe : horizontalPart R α e = c • matchedIdem R M s := by
      conv_lhs => rw [← hl, map_mul, hhm, matchedIdem_def, sum_mul]
      rw [matchedIdem_def, smul_sum]
      refine sum_congr rfl fun S hS ↦ ?_
      obtain ⟨hSim, hScard⟩ := (mem_filter.1 hS).2
      rw [idem_mul_horizontalPart]
      congr 1
      exact repr_idOn_eq_of_mem_matchedSubalgebra hm _ S S₀ rfl (hSim.trans hS₀.symm)
        (by rw [hSim, hScard]) (by rw [hS₀, hcard₀])
    have hc : IsIdempotentElem c := by
      have h := congrArg (fun y ↦ (basis R α).repr y (idOn S₀))
        ((he.map (horizontalPart R α)).eq)
      simp only [hhe, smul_mul_smul_comm, (isIdempotentElem_matchedIdem M s).eq] at h
      exact (by simpa [repr_matchedIdem_apply, hS₀, hcard₀] using h : c * c = c)
    exact ⟨c, hc, eq_smul_of_horizontalPart_eq_smul he (isIdempotentElem_matchedIdem M s) hhm
      hl hr hc hhe⟩
  · -- No set lies over `s`, so `I(s) = 0` and hence `e = 0`.
    have h0 : matchedIdem R M s = 0 := by
      rw [matchedIdem_def]
      exact sum_eq_zero fun S hS ↦ absurd ⟨S, (mem_filter.1 hS).2⟩ hsec
    refine ⟨0, IsIdempotentElem.zero, ?_⟩
    rw [h0, smul_zero, ← hl, h0, zero_mul]

/-- **The idempotents `I(s)` do not split in the matched subalgebra** when the coefficient ring
has no idempotents besides `0` and `1`: the only idempotents of the matched subalgebra in the
corner of `I(s)` are `0` and `I(s)`, so `I(s)`, when nonzero, is primitive there. -/
theorem eq_zero_or_eq_matchedIdem_of_isIdempotentElem (hR : IsPrimitiveIdempotent (1 : R))
    {e : StrandsAlgebra R α} {s : Finset β} (hm : e ∈ matchedSubalgebra R M)
    (he : IsIdempotentElem e) (hl : matchedIdem R M s * e = e)
    (hr : e * matchedIdem R M s = e) : e = 0 ∨ e = matchedIdem R M s := by
  have := hR.nontrivial
  obtain ⟨c, hc, rfl⟩ := eq_smul_matchedIdem_of_isIdempotentElem hm he hl hr
  rcases (isPrimitiveIdempotent_one_iff.1 hR) _ hc with h | h
  · exact Or.inl (by rw [h, zero_smul])
  · exact Or.inr (by rw [h, one_smul])

end CommRing

end StrandsAlgebra

end TauCeti
