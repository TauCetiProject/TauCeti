/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Bounding a product of ideals by a span over a subsemiring

Let `S` be a subsemiring of a semiring `R`, let `G ⊆ R`, and let `J` be a two-sided ideal of `R`
whose elements lie in `S`. Then

```text
J * Ideal.span G ≤ Submodule.span S G,
```

the containment being of `S`-submodules of `R`. Taking `J = Ideal.span G`, legitimate when that
ideal itself lies inside `S`, bounds the *square* of the ideal.

## Why the coefficients can be moved

An element `Σ bᵢ gᵢ` of `Ideal.span G` has its coefficients `bᵢ` in `R`, and nothing puts them in
`S` — so `Ideal.span G` generally is **not** spanned by `G` over `S`. Multiplying by `x ∈ J`
rescues this, because the coefficients move onto the other factor:

```text
x * (Σ bᵢ gᵢ) = Σ (x * bᵢ) gᵢ
```

and each `x * bᵢ` lies in `J`, hence in `S`. The new coefficients are in `S` even though the old
ones were not. The elementwise statement needs only that every right multiple `x * c` lies in
`S`; the ideal `J` merely supplies such elements.

Only `Semiring` and `SubsemiringClass` are needed: no step uses negation or commutativity.

## What is and is not claimed

The conclusion is a **containment**, not an equality, and it does not say the left side is a
finitely generated `S`-submodule: a submodule of a finitely generated module need not be finitely
generated over a non-noetherian ring. What it gives, for finite `G`, is a finitely generated
`S`-submodule sitting *above* the product.

In the intended application — the intersection of two rings of definition, where the ideal must
descend to a *smaller* subring and `Ideal.map` is unavailable — `G` lies inside `Ideal.span G`,
which lies inside `S`, so `Submodule.span S G` is an ideal of `S`, is finitely generated when `G`
is, and sandwiches the square as `I * I ≤ Submodule.span S G ≤ I`.

## Main results

* `Submodule.mul_mem_span_of_mem_ideal_span`
* `Submodule.restrictScalars_mul_ideal_span_le_span`

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Corollary 6.4.
-/

public section

namespace Submodule

variable {R : Type*} [Semiring R] {T : Type*} [SetLike T R] [SubsemiringClass T R] (S : T)
  {G : Set R}

/-- Multiplying by an element whose right multiples all lie in `S` moves the coefficients into
`S`: if `x * c ∈ S` for every `c` and `y` lies in `Ideal.span G`, then `x * y` lies in the
`S`-span of `G`. -/
theorem mul_mem_span_of_mem_ideal_span {x y : R} (hx : ∀ c, x * c ∈ S)
    (hy : y ∈ Ideal.span G) : x * y ∈ span S G := by
  induction hy using span_induction generalizing x with
  | mem g hg => exact smul_mem _ (⟨x, by simpa using hx 1⟩ : S) (subset_span hg)
  | zero => simp
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [mul_add]; exact add_mem (ih₁ hx) (ih₂ hx)
  | smul c y _ ih =>
    rw [smul_eq_mul, ← mul_assoc]
    exact ih fun d ↦ by simpa [mul_assoc] using hx (c * d)

/-- **An ideal inside a subsemiring, times a span, is bounded by the span over that subsemiring.**
If `J` is a two-sided ideal of `R` lying inside `S`, then `J * Ideal.span G` is contained in the
`S`-span of `G`. Taking `J = Ideal.span G`, legitimate when that ideal itself lies inside `S`,
bounds the square of the ideal. -/
theorem restrictScalars_mul_ideal_span_le_span {J : Ideal R} [J.IsTwoSided]
    (hJS : ∀ x ∈ J, x ∈ S) : (J * Ideal.span G).restrictScalars S ≤ span S G :=
  fun _ ha ↦ Submodule.mul_induction_on ha
    (fun _ hx _ hy ↦ mul_mem_span_of_mem_ideal_span S (fun c ↦ hJS _ (J.mul_mem_right c hx)) hy)
    fun _ _ ↦ add_mem

end Submodule
