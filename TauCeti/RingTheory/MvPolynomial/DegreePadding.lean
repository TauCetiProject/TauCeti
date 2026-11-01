/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Zero-padding bounded-degree polynomial coordinates

Increasing a total-degree bound includes the old polynomial space in the new one. In monomial
coordinates this is `MvPolynomial.boundedCoefficientPadding`: it retains every old coefficient
and sets the additional coordinates to zero. Its range is precisely the vectors whose extra
coordinates vanish. Evaluation commutes with padding, so choosing a larger bound changes the
finite presentation, not the polynomial functions it represents.

The construction uses Mathlib's submodule inclusions and `LinearMap.piMap`, and the monomial
coordinate equivalence `MvPolynomial.boundedCoefficientEquiv`.
-/

public section

noncomputable section

namespace MvPolynomial

variable {σ R J : Type*} [CommSemiring R] [Finite σ] {d e f : ℕ}

/-- Include a tuple of bounded-degree polynomials in a larger degree bound, in monomial
coordinates. The new coordinates are zero. -/
def boundedCoefficientPadding (h : d ≤ e) :
    (J × {s : σ →₀ ℕ // s.degree ≤ d} → R) →ₗ[R]
      (J × {s : σ →₀ ℕ // s.degree ≤ e} → R) :=
  (boundedCoefficientEquiv σ R J e).toLinearMap ∘ₗ
    LinearMap.piMap (fun _ : J => Submodule.inclusion (restrictTotalDegree_mono σ R h)) ∘ₗ
      (boundedCoefficientEquiv σ R J d).symm.toLinearMap

/-- Padding the coefficients of a tuple gives the coefficients of its inclusion into the
larger bounded-degree space. -/
@[simp] theorem boundedCoefficientPadding_coefficients (h : d ≤ e)
    (v : J → restrictTotalDegree σ R d) :
    boundedCoefficientPadding h (boundedCoefficientEquiv σ R J d v) =
      boundedCoefficientEquiv σ R J e
        (fun j => Submodule.inclusion (restrictTotalDegree_mono σ R h) (v j)) := by
  simp only [boundedCoefficientPadding, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  congr 1

/-- Padding is extension by zero along the inclusion of the bounded exponent indices. -/
theorem boundedCoefficientPadding_eq_extendByZero_linearMap (h : d ≤ e) :
    boundedCoefficientPadding (σ := σ) (R := R) (J := J) h =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
        (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ e)
          fun _ hs => hs.trans h)) := by
  ext a : 1
  simpa only [LinearEquiv.apply_symm_apply] using
    (boundedCoefficientPadding_coefficients h ((boundedCoefficientEquiv σ R J d).symm a)).trans
      (boundedCoefficientEquiv_inclusion_comp h ((boundedCoefficientEquiv σ R J d).symm a))

/-- Padding preserves the coefficient at every exponent in the old degree bound. -/
theorem boundedCoefficientPadding_apply_le (h : d ≤ e)
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R)
    (j : J) (s : σ →₀ ℕ) (hs : s.degree ≤ d) :
    boundedCoefficientPadding h a (j, ⟨s, hs.trans h⟩) = a (j, ⟨s, hs⟩) := by
  rw [boundedCoefficientPadding_eq_extendByZero_linearMap,
    Function.ExtendByZero.linearMap_apply]
  exact (Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective).extend_apply
    a 0 (j, ⟨s, hs⟩)

/-- Every coordinate added by increasing the degree bound is zero. -/
@[simp] theorem boundedCoefficientPadding_apply_of_lt (h : d ≤ e)
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R)
    (j : J) (s : {s : σ →₀ ℕ // s.degree ≤ e}) (hs : d < s.val.degree) :
    boundedCoefficientPadding h a (j, s) = 0 := by
  rw [boundedCoefficientPadding_eq_extendByZero_linearMap,
    Function.ExtendByZero.linearMap_apply]
  apply Function.extend_apply'
  rintro ⟨⟨j', s', hs'⟩, he⟩
  exact (not_le_of_gt hs) (by cases he; exact hs')

/-- The coordinate formula for padding: keep old coefficients and fill with zeros. -/
@[simp] theorem boundedCoefficientPadding_apply (h : d ≤ e)
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R)
    (j : J) (s : {s : σ →₀ ℕ // s.degree ≤ e}) :
    boundedCoefficientPadding h a (j, s) =
      if hs : s.val.degree ≤ d then a (j, ⟨s.val, hs⟩) else 0 := by
  split_ifs with hs
  · exact boundedCoefficientPadding_apply_le h a j s.val hs
  · exact boundedCoefficientPadding_apply_of_lt h a j s (Nat.lt_of_not_ge hs)

/-- Enlarging the coordinate space loses no coefficients. -/
theorem boundedCoefficientPadding_injective (h : d ≤ e) :
    Function.Injective (boundedCoefficientPadding (σ := σ) (R := R) (J := J) h) := by
  rw [boundedCoefficientPadding_eq_extendByZero_linearMap]
  exact Function.extend_injective
    (Function.injective_id.prodMap
      (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ e)
        (fun _ hs => hs.trans h)).injective)
    (0 : J × {s : σ →₀ ℕ // s.degree ≤ e} → R)

/-- Padding without changing the degree bound is the identity. -/
@[simp] theorem boundedCoefficientPadding_refl :
    boundedCoefficientPadding (σ := σ) (R := R) (J := J) (le_refl d) = LinearMap.id := by
  ext a ⟨j, s⟩
  simp [s.property]

/-- Enlarging the degree bound in two steps agrees with enlarging it directly. -/
@[simp] theorem boundedCoefficientPadding_comp (hde : d ≤ e) (hef : e ≤ f) :
    (boundedCoefficientPadding (σ := σ) (R := R) (J := J) hef).comp
      (boundedCoefficientPadding hde) = boundedCoefficientPadding (hde.trans hef) := by
  ext a : 1
  simp only [LinearMap.comp_apply, boundedCoefficientPadding_eq_extendByZero_linearMap]
  exact ((Function.injective_id.prodMap
    (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ e)
      (fun _ hs => hs.trans hde)).injective).extend_comp
    (Function.injective_id.prodMap
      (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ e) (fun s => s.degree ≤ f)
        (fun _ hs => hs.trans hef)).injective) a 0).symm

/-- A vector in the larger coefficient space comes from the smaller one exactly when all
coordinates above the smaller degree bound vanish. -/
theorem mem_range_boundedCoefficientPadding_iff (h : d ≤ e)
    (b : J × {s : σ →₀ ℕ // s.degree ≤ e} → R) :
    b ∈ Set.range (boundedCoefficientPadding (σ := σ) (R := R) (J := J) h) ↔
      ∀ j s, d < s.val.degree → b (j, s) = 0 := by
  constructor
  · rintro ⟨a, rfl⟩ j s hs
    exact boundedCoefficientPadding_apply_of_lt h a j s hs
  · intro hb
    refine ⟨fun i => b (i.1, ⟨i.2.val, i.2.property.trans h⟩), ?_⟩
    funext ⟨j, s⟩
    by_cases hs : s.val.degree ≤ d
    · simp [hs]
    · simp [hs, hb j s (Nat.lt_of_not_ge hs)]

/-- Evaluating padded coefficients gives the same vector-valued polynomial function.
This equality does not require the scalars to be infinite. -/
@[simp] theorem boundedEvaluation_padding (h : d ≤ e)
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R) :
    boundedEvaluation σ R J e
        ((boundedCoefficientEquiv σ R J e).symm (boundedCoefficientPadding h a)) =
      boundedEvaluation σ R J d ((boundedCoefficientEquiv σ R J d).symm a) := by
  simp only [boundedCoefficientPadding, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  funext x j
  simp

end MvPolynomial
