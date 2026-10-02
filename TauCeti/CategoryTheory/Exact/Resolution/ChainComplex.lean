/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The chain complex of a finite resolution

A finite `P`-resolution of `X` in an exact category is a chain of conflations

```text
K₁ ↪ Q₀ ↠ X,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁
```

ending at a syzygy `Kₙ` satisfying `P`. Splicing the conflations together gives the bounded
chain complex

```text
0 ⟶ Kₙ ⟶ Qₙ₋₁ ⟶ ⋯ ⟶ Q₁ ⟶ Q₀
```

augmented by the deflation `Q₀ ↠ X`: the differential `Qₖ₊₁ ⟶ Qₖ` is the composite
`Qₖ₊₁ ↠ Kₖ₊₁ ↪ Qₖ`, and the terms beyond `Kₙ` are zero. This file constructs that complex from the
recursive data, so that the comparison theory of resolutions can be phrased with Mathlib's chain
maps and chain homotopies.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.term`: the `n`-th term `Qₙ` of the complex, with
  `Kₙ` in degree `n` and zero beyond.
* `TauCeti.ExactStructure.FiniteResolution.aug`: the augmentation `Q₀ ⟶ X`.
* `TauCeti.ExactStructure.FiniteResolution.d`: the differential `Qₙ₊₁ ⟶ Qₙ`.
* `TauCeti.ExactStructure.FiniteResolution.toChainComplex`: the `ℕ`-indexed chain complex of the
  terms and differentials.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.d_comp_d` and
  `TauCeti.ExactStructure.FiniteResolution.d_comp_aug`: the differentials square to zero and
  the augmentation kills the first differential.
* `TauCeti.ExactStructure.FiniteResolution.isDeflation_aug`: the augmentation is a deflation.
* `TauCeti.ExactStructure.FiniteResolution.prop_term_of_le_length` and
  `TauCeti.ExactStructure.FiniteResolution.isZero_term_of_length_lt`: the terms up to the length
  satisfy `P`, and the terms beyond it are zero.

## Implementation notes

`TauCeti.ExactStructure.FiniteResolution.term` is exposed, for the same reason as
`TauCeti.ExactStructure.FiniteResolution.syzygy`: it is the type index of the augmentation, of the
differential, and of every family of morphisms between the complexes of two resolutions, and the
recursive constructions of those families only typecheck when `(step … r).term (n + 1)` reduces to
`r.term n`. It is moreover reducible, so that `simp` and `rw` unify a morphism typed with
`(step … r).term (n + 1)` against one typed with `r.term n`; without this every lemma mixing the
two would need an explicit `rfl` step. The price is that the equation lemmas of `term` are not simp
lemmas: `simp` indexes left-hand sides at reducible transparency, so `(base hX).term 0` is unfolded
before it could be matched and the lemmas would never fire. They are stated for `rw` and term-mode
use. The augmentation and the differential are sealed behind their equations. `toChainComplex` is
an abbreviation, exactly as Mathlib's `ChainComplex.of` is, so that its terms are the terms of the
resolution definitionally; `simp` therefore computes its differentials through
`ChainComplex.of_d`, and `toChainComplex_d` is the `rw` form of that lemma.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 12,
  for resolutions in a Quillen exact category as acyclic complexes.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {P : ObjectProperty C}

namespace FiniteResolution

/-- The `n`-th term of the chain complex of a finite resolution: the resolving term `Qₙ` for
`n` below the length, the last syzygy `Kₙ` in degree `n` equal to the length, and a zero object
beyond. -/
@[expose, reducible] noncomputable def term : ∀ {X : C}, FiniteResolution E P X → ℕ → C
  | X, .base _, 0 => X
  | _, .base _, _ + 1 => 0
  | _, .step (Q := Q) _ _ _ _ _ _, 0 => Q
  | _, .step _ _ _ _ _ r, n + 1 => r.term n

theorem term_base_zero {X : C} (hX : P X) : (base (E := E) hX).term 0 = X := rfl

theorem term_base_succ {X : C} (hX : P X) (n : ℕ) :
    (base (E := E) hX).term (n + 1) = 0 := rfl

theorem term_step_zero {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) : (step hQ i p zero hp r).term 0 = Q := rfl

theorem term_step_succ {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) (n : ℕ) :
    (step hQ i p zero hp r).term (n + 1) = r.term n := rfl

/-- Every term of index at most the length satisfies `P`. -/
theorem prop_term_of_le_length {X : C} (r : FiniteResolution E P X) {n : ℕ}
    (hn : n ≤ r.length) : P (r.term n) := by
  induction r generalizing n with
  | base hX =>
      obtain rfl : n = 0 := by simpa using hn
      exact hX
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => exact hQ
      | succ n => exact ih (by simpa using hn)

/-- Every term of index beyond the length is a zero object. -/
theorem isZero_term_of_length_lt {X : C} (r : FiniteResolution E P X) {n : ℕ}
    (hn : r.length < n) : IsZero (r.term n) := by
  induction r generalizing n with
  | base hX =>
      cases n with
      | zero => simp at hn
      | succ n => exact isZero_zero C
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => simp at hn
      | succ n => exact ih (by simpa using hn)

/-- The augmentation of the complex of a resolution: the deflation `Q₀ ↠ X` of its first
conflation, or the identity of `X` for the empty chain. -/
noncomputable def aug : ∀ {X : C} (r : FiniteResolution E P X), r.term 0 ⟶ X
  | _, .base _ => 𝟙 _
  | _, .step _ _ p _ _ _ => p

@[simp] theorem aug_base {X : C} (hX : P X) : (base (E := E) hX).aug = 𝟙 X := (rfl)

@[simp] theorem aug_step {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : E.Conflation (ShortComplex.mk i p zero)) (r : FiniteResolution E P K) :
    (step hQ i p zero hp r).aug = p := (rfl)

/-- The augmentation is a deflation. -/
theorem isDeflation_aug {X : C} (r : FiniteResolution E P X) : E.IsDeflation r.aug := by
  cases r with
  | base hX => exact E.isDeflation_id _
  | step hQ i p zero hp r => exact E.isDeflation_g hp

/-- The differential `Qₙ₊₁ ⟶ Qₙ` of the complex of a resolution: the composite of the
deflation `Qₙ₊₁ ↠ Kₙ₊₁` with the inflation `Kₙ₊₁ ↪ Qₙ`. -/
noncomputable def d : ∀ {X : C} (r : FiniteResolution E P X) (n : ℕ), r.term (n + 1) ⟶ r.term n
  | _, .base _, _ => 0
  | _, .step _ i _ _ _ r, 0 => r.aug ≫ i
  | _, .step _ _ _ _ _ r, n + 1 => r.d n

@[simp] theorem d_base {X : C} (hX : P X) (n : ℕ) : (base (E := E) hX).d n = 0 := (rfl)

@[simp] theorem d_step_zero {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : E.Conflation (ShortComplex.mk i p zero)) (r : FiniteResolution E P K) :
    (step hQ i p zero hp r).d 0 = r.aug ≫ i := (rfl)

@[simp] theorem d_step_succ {K Q X : C} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
    (hp : E.Conflation (ShortComplex.mk i p zero)) (r : FiniteResolution E P K) (n : ℕ) :
    (step hQ i p zero hp r).d (n + 1) = r.d n := (rfl)

/-- The augmentation kills the first differential. -/
@[reassoc (attr := simp)]
theorem d_comp_aug {X : C} (r : FiniteResolution E P X) : r.d 0 ≫ r.aug = 0 := by
  cases r with
  | base hX => simp
  | step hQ i p zero hp r => simp [zero]

/-- The differentials square to zero. -/
@[reassoc (attr := simp)]
theorem d_comp_d {X : C} (r : FiniteResolution E P X) (n : ℕ) : r.d (n + 1) ≫ r.d n = 0 := by
  induction r generalizing n with
  | base hX => simp
  | step hQ i p zero hp r ih =>
      cases n with
      | zero => simp
      | succ n => simpa using ih n

/-- The chain complex of a finite resolution: the resolving terms with the spliced
differentials, `Kₙ` in degree `n` equal to the length, and zero beyond. -/
noncomputable abbrev toChainComplex {X : C} (r : FiniteResolution E P X) : ChainComplex C ℕ :=
  ChainComplex.of r.term r.d r.d_comp_d

/-- The differential of the complex in consecutive degrees. Not a simp lemma, since `simp` proves
it from `ChainComplex.of_d` through the abbreviation; it is the form `rw` can use, which does not
see `ChainComplex.of.d` through the abbreviation, and unifies with offset degrees such as
`r.toChainComplex.d (n + 2) (n + 1)`. -/
theorem toChainComplex_d {X : C} (r : FiniteResolution E P X) (n : ℕ) :
    r.toChainComplex.d (n + 1) n = r.d n :=
  ChainComplex.of_d _ _ n

end FiniteResolution

end ExactStructure

end TauCeti
