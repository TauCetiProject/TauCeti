/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.TraceForm

/-!
# Ad-nilpotent elements of a Killing Lie algebra as brackets with themselves

Let `L` be a finite-dimensional Lie algebra over a field whose Killing form `κ` is nondegenerate,
and let `x : L` be an element whose adjoint action `ad x` is nilpotent.  Then there is a `t : L`
with

`⁅x, t⁆ = x`,

which is `TauCeti.exists_lie_eq_self_of_isNilpotent_ad`.  Equivalently `⁅t, x⁆ = -x`, so when `x`
is nonzero it is an eigenvector of `ad t` for the eigenvalue `-1`.

The proof is the Killing-orthogonality of the kernel and the range of `ad x`, and it needs no
algebraically closed field, no Cartan subalgebra, and no `sl₂`-triple.  In two steps:

* **`x` is Killing-orthogonal to `ker (ad x)`.**  If `⁅x, z⁆ = 0` then `ad x` and `ad z` commute,
  so `ad x ∘ ad z` is nilpotent and its trace `κ x z` vanishes.  Only reducedness of the
  coefficients is used, and the statement is proved for the trace form of an arbitrary
  representation (`TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero`), the Killing form
  being the trace form of the adjoint representation.
* **The Killing-orthogonal complement of `range (ad x)` is `ker (ad x)`.**  This is invariance,
  `κ ⁅x, z⁆ y = - κ z ⁅x, y⁆`: the left-hand side vanishes for every `z` exactly when `⁅x, y⁆` is
  Killing-orthogonal to everything, which by nondegeneracy means `⁅x, y⁆ = 0`.  On a
  finite-dimensional space a nondegenerate symmetric form is reflexive and its double orthogonal
  complement is the original subspace, so `range (ad x)` is in turn the orthogonal complement of
  `ker (ad x)`, and the first step places `x` in it.

Nondegeneracy is what carries the argument: in an abelian Lie algebra every `ad x` is nilpotent
while `range (ad x)` is `⊥`, so no nonzero `x` is a bracket with itself there.  The hypothesis is
satisfied, nonvacuously, by every root vector of a split semisimple Lie algebra, which is
ad-nilpotent by `LieAlgebra.isNilpotent_ad_of_mem_rootSpace`.  For such a vector `e` the
conclusion is also visible in an `sl₂`-triple `(h, e, f)` over a field in which `2 ≠ 0`, since
`⁅h, e⁆ = 2 • e` then gives `t = -(2 : K)⁻¹ • h`; that route is genuinely characteristic-dependent,
and it fails in characteristic two.  What is proved here needs no triple, no Cartan subalgebra, no
root space decomposition, no triangularizability and no invertible `2`, only ad-nilpotence of `x`
and nondegeneracy of `κ`.

The same orthogonality holds for every power: `ker ((ad x) ^ n)` and `range ((ad x) ^ n)` are each
other's Killing-orthogonal complements, because `(ad x) ^ n` is adjoint to `(-1) ^ n (ad x) ^ n`.

## Characteristic zero: the neutral element of an `sl₂`-triple

Over a field of characteristic zero the argument goes one step further: an ad-nilpotent `x` lies in
`range ((ad x) ^ 2)`, which is `TauCeti.mem_range_ad_sq_self_of_isNilpotent_ad`. The required
orthogonality, `κ x z = 0` whenever `⁅x, ⁅x, z⁆⁆ = 0`, is no longer a statement about commuting
endomorphisms. It is `TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_lie_eq_zero` for the adjoint
representation, which rests on Jacobson's lemma on commutators. That lemma fails in positive
characteristic `p`: differentiation and multiplication by `X` on `K[X] ⧸ (X ^ p)` have commutator
`1`. Writing
`x = ⁅x, ⁅x, y⁆⁆` and `h = 2 • ⁅y, x⁆` gives an element `h` of `range (ad x)` with
`⁅h, x⁆ = 2 • x` (`TauCeti.exists_mem_range_ad_lie_eq_two_nsmul_of_isNilpotent_ad`). These are the
hypotheses of Morozov's lemma, which completes `h` and `x` to an `sl₂`-triple in the proof of the
Jacobson–Morozov theorem.

## Main results

* `TauCeti.killingForm_ad_pow_apply`: `(ad x) ^ n` moves across the Killing form with the sign
  `(-1) ^ n`.
* `TauCeti.orthogonal_range_ad_pow_eq_ker_ad_pow` and
  `TauCeti.range_ad_pow_eq_orthogonal_ker_ad_pow`: **the kernel and the range of `(ad x) ^ n`
  are each other's Killing-orthogonal complements**, with the case `n = 1` recorded as
  `TauCeti.orthogonal_range_ad_eq_ker_ad` and `TauCeti.range_ad_eq_orthogonal_ker_ad`.
* `TauCeti.mem_range_ad_self_of_isNilpotent_ad`: **an ad-nilpotent element lies in the range of
  its own adjoint action.**
* `TauCeti.exists_lie_eq_self_of_isNilpotent_ad`: **hence `⁅x, t⁆ = x` for some `t`.**
* `TauCeti.killingForm_eq_zero_of_isNilpotent_ad_of_lie_lie_eq_zero`: in characteristic zero, an
  ad-nilpotent `x` is Killing-orthogonal to every `z` with `⁅x, ⁅x, z⁆⁆ = 0`.
* `TauCeti.mem_range_ad_sq_self_of_isNilpotent_ad`: **in characteristic zero, an ad-nilpotent
  element lies in the range of `(ad x) ^ 2`.**
* `TauCeti.exists_mem_range_ad_lie_eq_two_nsmul_of_isNilpotent_ad`: **hence there is `h` in the
  range of `ad x` with `⁅h, x⁆ = 2 • x`.**

## References

* G. Hochschild, *An addition to Ado's theorem*, Proc. Amer. Math. Soc. **17** (1966), 531-533.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.1, for the
  invariance and nondegeneracy of the Killing form.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter III, §11, for the construction of `h`
  in the proof of the Jacobson–Morozov theorem.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

section KillingForm

variable {R L : Type*} [CommRing R] [IsReduced R] [LieRing L] [LieAlgebra R L]

/-- **An ad-nilpotent element is Killing-orthogonal to its own centraliser.**  This is
`TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero` for the adjoint representation. -/
theorem killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero {x y : L}
    (hx : IsNilpotent (ad R L x)) (hxy : ⁅x, y⁆ = 0) :
    killingForm R L x y = 0 :=
  traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero hx hxy

end KillingForm

section Orthogonal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **Powers of the adjoint action move across the Killing form up to sign.** Since `ad x` is
skew-adjoint for the Killing form, `κ ((ad x) ^ n y) z = (-1) ^ n * κ y ((ad x) ^ n z)`. -/
theorem killingForm_ad_pow_apply (x y z : L) (n : ℕ) :
    killingForm R L ((ad R L x ^ n) y) z = (-1) ^ n * killingForm R L y ((ad R L x ^ n) z) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    have h₁ : (ad R L x ^ (n + 1)) y = (ad R L x ^ n) ⁅x, y⁆ := by
      rw [pow_succ, Module.End.mul_apply, ad_apply]
    have h₂ : (ad R L x ^ (n + 1)) z = ⁅x, (ad R L x ^ n) z⁆ := by
      rw [pow_succ', Module.End.mul_apply, ad_apply]
    rw [h₁, h₂, ih, traceForm_apply_lie_apply', pow_succ]
    ring

/-- **The kernel of `(ad x) ^ n` is Killing-orthogonal to its range.** This half of
`TauCeti.orthogonal_range_ad_pow_eq_ker_ad_pow` is pure invariance of the Killing form and needs
no nondegeneracy. -/
theorem ker_ad_pow_le_orthogonal_range_ad_pow (x : L) (n : ℕ) :
    LinearMap.ker (ad R L x ^ n) ≤
      (killingForm R L).orthogonal (LinearMap.range (ad R L x ^ n)) := by
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rintro - ⟨z, rfl⟩
  rw [killingForm_ad_pow_apply, hy, map_zero, mul_zero]

/-- **The centraliser of `x` is Killing-orthogonal to the range of `ad x`.** This is the case
`n = 1` of `TauCeti.ker_ad_pow_le_orthogonal_range_ad_pow`. -/
theorem ker_ad_le_orthogonal_range_ad (x : L) :
    LinearMap.ker (ad R L x) ≤ (killingForm R L).orthogonal (LinearMap.range (ad R L x)) := by
  simpa using ker_ad_pow_le_orthogonal_range_ad_pow (R := R) x 1

variable [LieAlgebra.IsKilling R L]

/-- **The Killing-orthogonal complement of the range of `(ad x) ^ n` is its kernel.** Invariance
turns `κ ((ad x) ^ n z) y = 0` for all `z` into `κ ((ad x) ^ n y) z = 0` for all `z`, and
nondegeneracy then forces `(ad x) ^ n y = 0`. -/
@[simp]
theorem orthogonal_range_ad_pow_eq_ker_ad_pow (x : L) (n : ℕ) :
    (killingForm R L).orthogonal (LinearMap.range (ad R L x ^ n)) =
      LinearMap.ker (ad R L x ^ n) := by
  refine le_antisymm (fun y hy ↦ ?_) (ker_ad_pow_le_orthogonal_range_ad_pow x n)
  rw [LinearMap.mem_ker]
  refine (LieAlgebra.IsKilling.killingForm_nondegenerate R L).1 _ fun z ↦ ?_
  have h := hy ((ad R L x ^ n) z) ⟨z, rfl⟩
  rw [killingForm_ad_pow_apply,
    ((isUnit_neg_one (α := R)).pow n).mul_right_eq_zero, LieModule.traceForm_comm] at h
  exact h

/-- **The Killing-orthogonal complement of the range of `ad x` is the centraliser of `x`.** This is
the case `n = 1` of `TauCeti.orthogonal_range_ad_pow_eq_ker_ad_pow`. -/
@[simp]
theorem orthogonal_range_ad_eq_ker_ad (x : L) :
    (killingForm R L).orthogonal (LinearMap.range (ad R L x)) = LinearMap.ker (ad R L x) := by
  simpa using orthogonal_range_ad_pow_eq_ker_ad_pow (R := R) x 1

end Orthogonal

section Killing

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.IsKilling K L]

/-- **The range of `(ad x) ^ n` is the Killing-orthogonal complement of its kernel.** This is
`TauCeti.orthogonal_range_ad_pow_eq_ker_ad_pow` read backwards through the double orthogonal
complement of a nondegenerate symmetric form on a finite-dimensional space. -/
theorem range_ad_pow_eq_orthogonal_ker_ad_pow (x : L) (n : ℕ) :
    LinearMap.range (ad K L x ^ n) =
      (killingForm K L).orthogonal (LinearMap.ker (ad K L x ^ n)) := by
  rw [← orthogonal_range_ad_pow_eq_ker_ad_pow x n,
    LinearMap.BilinForm.orthogonal_orthogonal (LieAlgebra.IsKilling.killingForm_nondegenerate K L)
      (LieModule.traceForm_isSymm K L L).isRefl]

/-- **The range of `ad x` is the Killing-orthogonal complement of the centraliser of `x`.**  This
is the case `n = 1` of `TauCeti.range_ad_pow_eq_orthogonal_ker_ad_pow`. -/
theorem range_ad_eq_orthogonal_ker_ad (x : L) :
    LinearMap.range (ad K L x) = (killingForm K L).orthogonal (LinearMap.ker (ad K L x)) := by
  simpa using range_ad_pow_eq_orthogonal_ker_ad_pow (K := K) x 1

/-- **An ad-nilpotent element of a Killing Lie algebra lies in the range of its own adjoint
action.**  It is Killing-orthogonal to its centraliser by
`TauCeti.killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero`, and that orthogonal complement is
the range of `ad x`. -/
theorem mem_range_ad_self_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    x ∈ LinearMap.range (ad K L x) := by
  rw [range_ad_eq_orthogonal_ker_ad]
  intro z hz
  rw [LinearMap.mem_ker, ad_apply] at hz
  rw [LieModule.traceForm_comm]
  exact killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero hx hz

/-- **An ad-nilpotent element of a Killing Lie algebra is a bracket with itself**: there is a
`t : L` with `⁅x, t⁆ = x`.

This is the step that lets Hochschild's strengthening of Ado's theorem pass from ad-nilpotence of
a semisimple component to the solvable subalgebra spanned by `x` and `t`, with no algebraically
closed field and no `sl₂`-triple. -/
theorem exists_lie_eq_self_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    ∃ t : L, ⁅x, t⁆ = x := by
  obtain ⟨t, ht⟩ := mem_range_ad_self_of_isNilpotent_ad hx
  exact ⟨t, by rwa [ad_apply] at ht⟩

end Killing

section CharZero

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

/-- **An ad-nilpotent element is Killing-orthogonal to everything its adjoint action kills
twice.** This is `TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_lie_eq_zero` for the adjoint
representation. -/
theorem killingForm_eq_zero_of_isNilpotent_ad_of_lie_lie_eq_zero {x z : L}
    (hx : IsNilpotent (ad K L x)) (hz : ⁅x, ⁅x, z⁆⁆ = 0) :
    killingForm K L x z = 0 :=
  traceForm_eq_zero_of_isNilpotent_of_lie_lie_eq_zero hx hz

variable [LieAlgebra.IsKilling K L]

/-- **An ad-nilpotent element of a Killing Lie algebra over a field of characteristic zero lies in
the range of the square of its own adjoint action.** It is Killing-orthogonal to the kernel of
`(ad x) ^ 2` by `TauCeti.killingForm_eq_zero_of_isNilpotent_ad_of_lie_lie_eq_zero`, and that
orthogonal complement is the range of `(ad x) ^ 2`. -/
theorem mem_range_ad_sq_self_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    x ∈ LinearMap.range (ad K L x ^ 2) := by
  rw [range_ad_pow_eq_orthogonal_ker_ad_pow]
  intro z hz
  rw [LinearMap.mem_ker, sq, Module.End.mul_apply, ad_apply, ad_apply] at hz
  rw [LieModule.traceForm_comm]
  exact killingForm_eq_zero_of_isNilpotent_ad_of_lie_lie_eq_zero hx hz

/-- **The neutral element of a Jacobson–Morozov triple.** For an ad-nilpotent `e` in a Killing Lie
algebra over a field of characteristic zero there is an `h` in the range of `ad e` with
`⁅h, e⁆ = 2 • e`. Writing `e = ⁅e, ⁅e, y⁆⁆`, one can take `h = 2 • ⁅y, e⁆`.

These are the hypotheses of Morozov's lemma, which completes `h` and `e` to an `sl₂`-triple when
`e ≠ 0`. -/
theorem exists_mem_range_ad_lie_eq_two_nsmul_of_isNilpotent_ad {e : L}
    (he : IsNilpotent (ad K L e)) :
    ∃ h ∈ LinearMap.range (ad K L e), ⁅h, e⁆ = 2 • e := by
  obtain ⟨y, hy⟩ := mem_range_ad_sq_self_of_isNilpotent_ad he
  rw [sq, Module.End.mul_apply, ad_apply, ad_apply] at hy
  refine ⟨2 • ⁅y, e⁆, ⟨-(2 • y), ?_⟩, ?_⟩
  · rw [ad_apply, lie_neg, lie_nsmul, ← smul_neg, lie_skew]
  · rw [nsmul_lie, ← lie_skew y e, neg_lie, ← lie_skew, neg_neg, hy]

end CharZero

end TauCeti
