/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

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
(`TauCeti.StrandsAlgebra.eq_smul_idem_of_isIdempotentElem`).

Primitivity holds over any commutative semiring in which `1` is primitive, such as a field or a
local ring (`TauCeti.isPrimitiveIdempotent_one`); bordered Floer theory uses `𝔽₂`. The coefficient
on an identity diagram `I(S)` is multiplicative (`TauCeti.StrandsAlgebra.repr_mul_idOn`), and an
idempotent with no coefficient on any identity diagram has zero horizontal part, so it is
nilpotent and hence zero
(`TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero`). If an
idempotent `e` splits as `f₁ + f₂` into orthogonal idempotents, the coefficients of `f₁` and `f₂`
on an identity diagram `I(S)` of coefficient `1` in `e` split `1` into orthogonal idempotents of
the coefficient ring, so one of them vanishes; when `f₁` and `f₂` have this coefficient on every
identity diagram of `e`, the vanishing summand is zero. This applies to `e = I(S)` in `A(n)`
(`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`), so the `I(S)` are a complete set of
primitive orthogonal idempotents of `A(n)`
(`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_idem`).

This splitting argument is adapted from the proof that the vertex idempotents of a path algebra
are primitive (`TauCeti.isPrimitiveIdempotent_vertexIdempotent`). The identity diagrams `idOn S`
take the place of the trivial paths: the multiplicative coordinate on a trivial path becomes the
coordinate on an identity diagram, and the arrow ideal, which contains no nonzero idempotent,
becomes the elements with no coefficient on any identity diagram, whose idempotents vanish
because they are nilpotent.

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
(`TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`). The equality of the
coefficients also makes the splitting argument above apply to `e = I(s)` in the matched
subalgebra, over any commutative semiring in which `1` is primitive: for every set `s` of pairs of
the matching, `I(s)` is a primitive idempotent of the matched subalgebra
(`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem`), although for a matched pair with two
points `I(s)` splits in `A(n)` as the sum of the two orthogonal `I(S)`. For the matching of a
pointed matched circle `Z`, the matched subalgebra is `A(Z)`, so the `I(s)` are a complete set of
primitive orthogonal idempotents of `A(Z)`
(`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`), and the left ideals
`A(Z) I(s)` are indecomposable modules over a coefficient ring
(`TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`).

## Main definitions

* `TauCeti.StrandsAlgebra.horizontalPart`: the projection onto the span of the `I(S)`, as an
  algebra endomorphism.

## Main results

* `TauCeti.StrandsAlgebra.horizontalPart_eq_sum`: the horizontal part is `∑ₛ x_{I(S)} I(S)`.
* `TauCeti.StrandsAlgebra.pow_eq_zero_of_horizontalPart_eq_zero`: elements with zero horizontal
  part are nilpotent.
* `TauCeti.StrandsAlgebra.idem_mul_mul_idem`: the corner of `I(S)` in `A(n)` is spanned by
  `I(S)`.
* `TauCeti.StrandsAlgebra.eq_smul_idem_of_isIdempotentElem`: the idempotents of the corner of
  `I(S)` in `A(n)`.
* `TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero`: an idempotent
  of the strands algebra with no coefficient on any identity diagram is zero.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem` and
  `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_idem`: the `I(S)` are a complete set of
  primitive orthogonal idempotents of `A(n)`.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem` and
  `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`: the `I(s)` are a complete set
  of primitive orthogonal idempotents of the matched subalgebra.
* `TauCeti.StrandsAlgebra.exists_isIdempotentElem_and_eq_smul_matchedIdem` and
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

/-! ### Primitivity of the idempotents -/

/-- **An idempotent of the strands algebra is detected by the identity diagrams.** An idempotent
with no coefficient on any identity diagram `I(S)` has zero horizontal part, so it is nilpotent,
hence zero. In other words, the span of the diagrams that are not identity diagrams contains no
nonzero idempotent. -/
theorem eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero {f : StrandsAlgebra R α}
    (hf : IsIdempotentElem f) (h : ∀ s, (basis R α).repr f (idOn s) = 0) : f = 0 := by
  have h0 : horizontalPart R α f = 0 := by simp [horizontalPart_eq_sum, h]
  calc f = f ^ (Fintype.card α ^ 2 + 1) := (hf.pow_eq (Nat.succ_ne_zero _)).symm
    _ = 0 := pow_eq_zero_of_horizontalPart_eq_zero h0

/-- The splitting step behind the primitivity of the idempotents. Let `e = f₁ + f₂` split into
orthogonal idempotents, with `I(S)` an identity diagram of coefficient `1` in `e`. If, on every
identity diagram with a nonzero coefficient in `e`, each `fᵢ` has its coefficient on `I(S)`, then
`f₁` or `f₂` vanishes. -/
private theorem eq_zero_or_eq_zero_of_add_eq (hR : IsPrimitiveIdempotent (1 : R))
    {e f₁ f₂ : StrandsAlgebra R α} {S : Finset α} (he : (basis R α).repr e (idOn S) = 1)
    (hcoord₁ : ∀ t, (basis R α).repr e (idOn t) ≠ 0 →
      (basis R α).repr f₁ (idOn t) = (basis R α).repr f₁ (idOn S))
    (hcoord₂ : ∀ t, (basis R α).repr e (idOn t) ≠ 0 →
      (basis R α).repr f₂ (idOn t) = (basis R α).repr f₂ (idOn S))
    (h₁ : IsIdempotentElem f₁) (h₂ : IsIdempotentElem f₂) (h₁₂ : f₁ * f₂ = 0)
    (h₂₁ : f₂ * f₁ = 0) (hsum : f₁ + f₂ = e) : f₁ = 0 ∨ f₂ = 0 := by
  -- A summand of `e` whose coefficient on `I(S)` vanishes has no coefficient on any identity
  -- diagram, since it equals `e` times itself.
  have key {f : StrandsAlgebra R α} (hf : IsIdempotentElem f) (hef : e * f = f)
      (hcoord : ∀ t, (basis R α).repr e (idOn t) ≠ 0 →
        (basis R α).repr f (idOn t) = (basis R α).repr f (idOn S))
      (hS : (basis R α).repr f (idOn S) = 0) : f = 0 := by
    refine eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero hf fun t ↦ ?_
    rw [← hef, repr_mul_idOn]
    by_cases ht : (basis R α).repr e (idOn t) = 0
    · rw [ht, zero_mul]
    · rw [hcoord t ht, hS, mul_zero]
  have hcoeff {f g : StrandsAlgebra R α} (hfg : f * g = 0) :
      (basis R α).repr f (idOn S) * (basis R α).repr g (idOn S) = 0 := by
    rw [← repr_mul_idOn, hfg, map_zero, Finsupp.zero_apply]
  refine (hR.eq_zero_or_eq_zero_of_add (by rw [IsIdempotentElem, ← repr_mul_idOn, h₁.eq])
    (by rw [IsIdempotentElem, ← repr_mul_idOn, h₂.eq]) (hcoeff h₁₂) (hcoeff h₂₁)
    (by rw [← Finsupp.add_apply, ← map_add, hsum, he])).imp (key h₁ ?_ hcoord₁)
    (key h₂ ?_ hcoord₂)
  · rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero]
  · rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add]

/-- **The idempotents `I(S)` of the strands algebra are primitive**, as soon as `1` is primitive in
the coefficient semiring. -/
theorem isPrimitiveIdempotent_idem (hR : IsPrimitiveIdempotent (1 : R)) (S : Finset α) :
    IsPrimitiveIdempotent (idem S : StrandsAlgebra R α) := by
  have := hR.nontrivial
  -- The only identity diagram with a nonzero coefficient in `I(S)` is `I(S)` itself.
  have hcoord (f : StrandsAlgebra R α) (t : Finset α)
      (ht : (basis R α).repr (idem S) (idOn t) ≠ 0) :
      (basis R α).repr f (idOn t) = (basis R α).repr f (idOn S) := by
    rw [idem_def, basis_repr_of, Finsupp.single_apply, ite_ne_right_iff] at ht
    rw [← source_idOn t, ← ht.1, source_idOn]
  refine ⟨isIdempotentElem_idem S, ?_, fun h₁ h₂ h₁₂ h₂₁ hsum ↦
    eq_zero_or_eq_zero_of_add_eq hR ?_ (hcoord _) (hcoord _) h₁ h₂ h₁₂ h₂₁ hsum⟩
  · rw [idem_def, ← basis_apply]
    exact (basis R α).ne_zero _
  · rw [idem_def, basis_repr_of, Finsupp.single_eq_same]

/-- **The idempotents `I(S)` of the strands algebra are a complete family of orthogonal
idempotents**, indexed by the subsets `S` of the points: they are orthogonal idempotents summing to
the unit. With `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`, they are a complete set of
primitive orthogonal idempotents of the strands algebra. -/
theorem completeOrthogonalIdempotents_idem :
    CompleteOrthogonalIdempotents (idem : Finset α → StrandsAlgebra R α) where
  idem := isIdempotentElem_idem
  ortho _ _ := idem_mul_idem_of_ne
  complete := sum_idem

section Matched

variable {β : Type*} [DecidableEq β] {M : α → β}

/-- **The idempotents `I(s)` of the matched subalgebra are primitive** there, for every set `s` of
pairs of the matching, as soon as `1` is primitive in the coefficient semiring. For the matching of
a pointed matched circle `Z`, these are the idempotents of the algebra `A(Z)`. -/
theorem isPrimitiveIdempotent_matchedIdem (hR : IsPrimitiveIdempotent (1 : R)) {s : Finset β}
    (hs : s ⊆ univ.image M) :
    IsPrimitiveIdempotent (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ :
      matchedSubalgebra R M) := by
  have := hR.nontrivial
  obtain ⟨S, hS⟩ := matchedChoices_nonempty_iff.2 hs
  have hsum : (matchedIdem R M s : StrandsAlgebra R α) = matchedSum R M (idOn S) := by
    rw [matchedIdem_eq_horizontalCompletion, horizontalCompletion_eq_matchedSum
      (isMatchedGenerator_idOn_empty M s) hS, idOn_addHorizontal, empty_union]
  have he : (basis R α).repr (matchedIdem R M s) (idOn S) = 1 := by
    classical
    rw [hsum, repr_matchedSum_apply, ite_eq_left ((matchedSetoid M).iseqv.refl _)]
  -- The identity diagrams with a nonzero coefficient in `I(s)` are related to `I(S)` by moving
  -- horizontal strands within matched pairs, so elements of the matched subalgebra have equal
  -- coefficients on them.
  have hcoord (f : matchedSubalgebra R M) (t : Finset α)
      (ht : (basis R α).repr (matchedIdem R M s) (idOn t) ≠ 0) :
      (basis R α).repr f (idOn t) = (basis R α).repr f (idOn S) := by
    classical
    rw [hsum, repr_matchedSum_apply, ite_ne_right_iff] at ht
    exact repr_eq_of_matchedSetoid f.2 ((matchedSetoid M).iseqv.symm ht.1)
  refine ⟨Subtype.ext (isIdempotentElem_matchedIdem M s), fun h0 ↦ ?_,
    fun {f₁ f₂} h₁ h₂ h₁₂ h₂₁ hsum ↦ ?_⟩
  · have := congrArg (fun x : matchedSubalgebra R M ↦ (basis R α).repr x (idOn S)) h0
    simp only [he, ZeroMemClass.coe_zero, map_zero, Finsupp.zero_apply] at this
    exact one_ne_zero this
  · refine (eq_zero_or_eq_zero_of_add_eq hR he (hcoord f₁) (hcoord f₂)
      (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) (congrArg Subtype.val h₁₂)
      (congrArg Subtype.val h₂₁) (congrArg Subtype.val hsum)).imp Subtype.ext Subtype.ext

/-- **The idempotents `I(s)` of the matched subalgebra are a complete family of orthogonal
idempotents**, indexed by the sets `s` of pairs of the matching: they are orthogonal idempotents
summing to its unit. With `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem`, they are a
complete set of primitive orthogonal idempotents of the matched subalgebra. -/
theorem completeOrthogonalIdempotents_matchedIdem :
    CompleteOrthogonalIdempotents fun s : (univ.image M).powerset ↦
      (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) where
  idem s := Subtype.ext (isIdempotentElem_matchedIdem M s)
  ortho s t hst := Subtype.ext <| by
    simp [matchedIdem_mul_matchedIdem, Subtype.coe_injective.ne hst]
  complete := Subtype.ext <| by
    simp [matchedOne_def, sum_attach (univ.image M).powerset (matchedIdem R M)]

end Matched

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
      rw [insert_sdiff_of_mem _ hbT, erase_sdiff_comm]
    have hswap := (mem_matchedSubalgebra.1 hx).2 (idOn S) a b hba.symm
    rw [swapHorizontal_idOn ha.1 hbS] at hswap
    rw [← hswap]
    refine ih S' T ?_ (hS'image.trans hST) (by rw [hS'image, hS'card, hS]) hT
    rw [hS'T, card_erase_of_mem (mem_sdiff.2 ha), hn, Nat.add_sub_cancel]

/-- **The idempotents of the matched subalgebra in the corner of `I(s)`** are the multiples
`c I(s)` by idempotents `c` of the coefficient ring. -/
theorem exists_isIdempotentElem_and_eq_smul_matchedIdem {e : StrandsAlgebra R α} {s : Finset β}
    (hm : e ∈ matchedSubalgebra R M) (he : IsIdempotentElem e)
    (hl : matchedIdem R M s * e = e) (hr : e * matchedIdem R M s = e) :
    ∃ c : R, IsIdempotentElem c ∧ e = c • matchedIdem R M s := by
  by_cases hsec : ∃ S : Finset α, S.image M = s ∧ #S = #s
  · obtain ⟨S₀, hS₀, hcard₀⟩ := hsec
    set c := (basis R α).repr e (idOn S₀)
    -- The horizontal part of `e` is that of `I(s) e`, and all its coefficients on the sets over
    -- `s` agree with `c`.
    have hhe : horizontalPart R α e = c • matchedIdem R M s := by
      conv_lhs => rw [← hl, map_mul, horizontalPart_matchedIdem, matchedIdem_def, sum_mul]
      rw [matchedIdem_def, smul_sum]
      refine sum_congr rfl fun S hS ↦ ?_
      obtain ⟨hSim, hScard⟩ := (mem_filter.1 hS).2
      rw [idem_mul_horizontalPart]
      congr 1
      exact repr_idOn_eq_of_mem_matchedSubalgebra hm _ S S₀ rfl (hSim.trans hS₀.symm)
        (by rw [hSim, hScard]) (by rw [hS₀, hcard₀])
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

end StrandsAlgebra

end TauCeti
