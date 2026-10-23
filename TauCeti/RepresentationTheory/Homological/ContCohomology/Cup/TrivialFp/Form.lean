/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic

/-!
# The cup form of a linear functional on `H²(G, 𝔽_p)`

Composing the cup square `cupFp p G : H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)` with a linear
functional `φ : H²(G, 𝔽_p) →ₗ 𝔽_p` gives an `𝔽_p`-bilinear form `(a, b) ↦ φ (a ⌣ b)` on
`H¹(G, 𝔽_p)`, the **cup form** `φ.cupForm`. It is the object through which Mathlib's theory of
bilinear forms — alternation, symmetry, nondegeneracy, matrices with respect to a basis — applies to
the cup product; a Demushkin group is a pro-`p` group whose cup form, for an isomorphism
`φ : H²(G, 𝔽_p) ≅ 𝔽_p`, is nondegenerate.

Graded commutativity of the cup square makes the cup form skew-symmetric, hence reflexive; at an
odd prime every cup square `a ⌣ a` vanishes (`TauCeti.cupFp_self_eq_zero_of_ne_two`) and the
form is alternating, while at `p = 2` it is symmetric. When `φ` is injective the form is
alternating exactly when every cup square vanishes and nondegenerate exactly when the cup square
separates points, so neither property depends on the choice of `φ`: replacing `φ` by a nonzero
multiple rescales the form and changes nothing below.

## Main definitions

* `LinearMap.cupForm`: the bilinear form `(a, b) ↦ φ (a ⌣ b)` on `H¹(G, 𝔽_p)`.

## Main results

* `LinearMap.cupForm_gradedComm`, `LinearMap.isRefl_cupForm`: the cup form is skew-symmetric and
  reflexive.
* `LinearMap.isAlt_cupForm_of_ne_two`, `LinearMap.isSymm_cupForm_two`: it is alternating at an odd
  prime and symmetric at `p = 2`.
* `LinearMap.isAlt_cupForm_iff_of_injective`, `LinearMap.nondegenerate_cupForm_iff_of_injective`:
  for injective `φ`, alternation is the vanishing of all cup squares and nondegeneracy is the
  separating property of the cup square, independently of `φ`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The cup form

The form is a construction on the linear functional `φ`, so it and its lemmas live in the
`LinearMap` namespace: `φ.cupForm`. -/

/-- **The cup form** of a linear functional `φ : H²(G, 𝔽_p) →ₗ 𝔽_p`: the `𝔽_p`-bilinear form
`(a, b) ↦ φ (a ⌣ b)` on `H¹(G, 𝔽_p)`. For a Demushkin group, where `H²(G, 𝔽_p)` is
one-dimensional, an isomorphism `φ : H²(G, 𝔽_p) ≅ 𝔽_p` turns the cup square into the
nondegenerate bilinear form of Labute's definition. -/
noncomputable def _root_.LinearMap.cupForm (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) :
    LinearMap.BilinForm (ZMod p) (cohomFp p G 1) :=
  (cupFp p G).compr₂ φ

@[simp]
theorem _root_.LinearMap.cupForm_apply (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p)
    (a b : cohomFp p G 1) : φ.cupForm a b = φ (cupFp p G a b) := by
  simp only [LinearMap.cupForm, LinearMap.compr₂_apply]

/-- Rescaling the functional rescales the cup form. -/
@[simp]
theorem _root_.LinearMap.cupForm_smul (c : ZMod p) (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) :
    (c • φ).cupForm = c • φ.cupForm := by
  ext a b
  simp

/-- **The cup form is skew-symmetric**, by graded commutativity of the cup square. -/
theorem _root_.LinearMap.cupForm_gradedComm (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p)
    (a b : cohomFp p G 1) : φ.cupForm a b = -φ.cupForm b a := by
  rw [LinearMap.cupForm_apply, LinearMap.cupForm_apply, cupFp_gradedComm, map_neg]

/-- The cup form is reflexive: `φ (a ⌣ b) = 0` implies `φ (b ⌣ a) = 0`. -/
theorem _root_.LinearMap.isRefl_cupForm (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) :
    φ.cupForm.IsRefl :=
  fun a b h => by rw [LinearMap.cupForm_gradedComm, h, neg_zero]

/-- The cup form is alternating exactly when `φ` kills every cup square. -/
theorem _root_.LinearMap.isAlt_cupForm_iff (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) :
    φ.cupForm.IsAlt ↔ ∀ a : cohomFp p G 1, φ (cupFp p G a a) = 0 := by
  unfold LinearMap.BilinForm.IsAlt LinearMap.IsAlt
  simp only [LinearMap.cupForm_apply]

/-- For injective `φ`, the cup form is alternating exactly when every cup square `a ⌣ a`
vanishes; in particular alternation does not depend on the choice of `φ`. -/
theorem _root_.LinearMap.isAlt_cupForm_iff_of_injective (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p)
    (hφ : Function.Injective φ) :
    φ.cupForm.IsAlt ↔ ∀ a : cohomFp p G 1, cupFp p G a a = 0 := by
  simp only [LinearMap.isAlt_cupForm_iff, map_eq_zero_iff φ hφ]

/-- **At an odd prime the cup form is alternating.** -/
theorem _root_.LinearMap.isAlt_cupForm_of_ne_two [Fact p.Prime]
    (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) (hp : p ≠ 2) : φ.cupForm.IsAlt := fun a => by
  rw [LinearMap.cupForm_apply, cupFp_self_eq_zero_of_ne_two p G hp, map_zero]

/-- **At `p = 2` the cup form is symmetric**: skew-symmetry is symmetry in characteristic two. -/
theorem _root_.LinearMap.isSymm_cupForm_two (φ : cohomFp 2 G 2 →ₗ[ZMod 2] ZMod 2) :
    φ.cupForm.IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun a b => by
    rw [LinearMap.cupForm_gradedComm, ZMod.neg_eq_self_mod_two]

/-- **For injective `φ`, the cup form is nondegenerate exactly when the cup square separates
points on the left**: every nonzero class `a` has some `b` with `a ⌣ b ≠ 0`. By reflexivity the
right-separating condition is automatic, and nondegeneracy does not depend on the choice of
`φ`. -/
theorem _root_.LinearMap.nondegenerate_cupForm_iff_of_injective
    (φ : cohomFp p G 2 →ₗ[ZMod p] ZMod p) (hφ : Function.Injective φ) :
    φ.cupForm.Nondegenerate ↔
      ∀ a : cohomFp p G 1, a ≠ 0 → ∃ b : cohomFp p G 1, cupFp p G a b ≠ 0 := by
  -- `LinearMap.BilinForm.Nondegenerate` is an abbreviation for `LinearMap.Nondegenerate`
  refine φ.isRefl_cupForm.nondegenerate_iff_separatingLeft.trans ?_
  constructor
  · intro h a ha
    by_contra hb
    push Not at hb
    exact ha (h a fun b => by rw [LinearMap.cupForm_apply, hb b, map_zero])
  · intro h a ha
    by_contra hne
    obtain ⟨b, hb⟩ := h a hne
    have hab := ha b
    rw [LinearMap.cupForm_apply] at hab
    exact hb ((map_eq_zero_iff φ hφ).mp hab)

end TauCeti
