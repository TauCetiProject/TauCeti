/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Data.Finsupp.MonomialOrder.WeightRefinement

/-!
# Weight initial forms

Let `w : σ → M` be a weight vector. The *initial form* `MvPolynomial.initialForm w f` of a
multivariate polynomial `f` is the sum of the terms of `f` of maximal weight, that is, its
weighted homogeneous component of weight `weightedTotalDegree w f`. Unlike the leading term for a
monomial order, an initial form may have several terms.

For a monomial order `m` and natural weights `w`, initial forms are compared with leading terms
through the refined monomial order `m.weightRefinement w`, which compares monomials first by
weight and then by `m`: the leading term of `f` for `m.weightRefinement w` is the leading term of
`initialForm w f` for `m`. Passing to ideals, the initial forms of the elements of an ideal `I`
span its *initial ideal* `in_w(I)`, and the leading terms of `I` for `m.weightRefinement w` span
the same ideal as the leading terms of `in_w(I)` for `m`. This is how a monomial initial ideal
is reached in two steps, first degenerating to the weight initial ideal: it underlies Gröbner
degenerations and the comparison of initial ideals for different weights.

## Main declarations

* `MvPolynomial.initialForm w f`: the initial form of `f` for the weight `w`.
* `MvPolynomial.initialForm_eq_zero_iff`: the initial form vanishes exactly when `f` does.
* `MvPolynomial.initialForm_add`, `MvPolynomial.initialForm_mul`: initial forms of sums and of
  products, when no cancellation occurs.
* `MvPolynomial.exists_initialForm_eq_weightedHomogeneousComponent`: every weighted homogeneous
  component of an element of the initial ideal `in_w(I)` is the initial form of an element of `I`.
* `MonomialOrder.leadingTerm_weightRefinement`: the leading term for `m.weightRefinement w` is the
  leading term for `m` of the initial form.
* `MonomialOrder.span_leadingTerm_weightRefinement`: the leading terms of `I` for
  `m.weightRefinement w` and those of `in_w(I)` for `m` span the same ideal.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 1 (Proposition 1.8).
-/

public section

open Finsupp

namespace MvPolynomial

variable {σ R M : Type*} [CommSemiring R]

section SemilatticeSup

variable [AddCommMonoid M] [SemilatticeSup M] [OrderBot M] (w : σ → M)
  {f g : MvPolynomial σ R} {n : M}

/-- The initial form of `f` for the weight vector `w`: the sum of the terms of `f` of maximal
weight, that is, the weighted homogeneous component of `f` of weight `weightedTotalDegree w f`. -/
noncomputable def initialForm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  weightedHomogeneousComponent w (weightedTotalDegree w f) f

theorem initialForm_def (f : MvPolynomial σ R) :
    initialForm w f = weightedHomogeneousComponent w (weightedTotalDegree w f) f :=
  (rfl)

@[simp]
theorem initialForm_zero : initialForm w (0 : MvPolynomial σ R) = 0 := by
  simp [initialForm_def]

/-- The initial form of `f` is weighted homogeneous of weight `weightedTotalDegree w f`. -/
theorem isWeightedHomogeneous_initialForm (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w (initialForm w f) (weightedTotalDegree w f) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- The coefficients of the initial form of `f` are those of `f` in maximal weight, and vanish in
every other weight. -/
theorem coeff_initialForm [DecidableEq M] (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (initialForm w f).coeff d = if weight w d = weightedTotalDegree w f then f.coeff d else 0 :=
  coeff_weightedHomogeneousComponent _ _ _

/-- The monomials of the initial form of `f` are the monomials of `f` of maximal weight. -/
theorem mem_support_initialForm {d : σ →₀ ℕ} :
    d ∈ (initialForm w f).support ↔ d ∈ f.support ∧ weight w d = weightedTotalDegree w f := by
  classical
  simp only [mem_support_iff, coeff_initialForm]
  split_ifs with h <;> simp [h]

theorem support_initialForm_subset (f : MvPolynomial σ R) :
    (initialForm w f).support ⊆ f.support :=
  fun _ hd ↦ ((mem_support_initialForm w).1 hd).1

/-- A weighted homogeneous polynomial is its own initial form. -/
theorem IsWeightedHomogeneous.initialForm_eq {w : σ → M} (h : IsWeightedHomogeneous w f n) :
    initialForm w f = f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hn : weightedTotalDegree w f = n := by
    simpa [weightedTotalDegree_coe w f hf] using h.weighted_total_degree hf
  rw [initialForm_def, hn, h.weightedHomogeneousComponent_same]

@[simp]
theorem initialForm_monomial (u : σ →₀ ℕ) (c : R) : initialForm w (monomial u c) = monomial u c :=
  (isWeightedHomogeneous_monomial w u c rfl).initialForm_eq

@[simp]
theorem initialForm_C (c : R) : initialForm w (C c : MvPolynomial σ R) = C c :=
  (isWeightedHomogeneous_C w c).initialForm_eq

@[simp]
theorem initialForm_initialForm (f : MvPolynomial σ R) :
    initialForm w (initialForm w f) = initialForm w f :=
  (isWeightedHomogeneous_initialForm w f).initialForm_eq

/-- If all monomials of `f` have weight at most `n` and the weighted homogeneous component of `f`
of weight `n` is nonzero, then this component is the initial form of `f`. -/
theorem initialForm_eq_weightedHomogeneousComponent (hfn : weightedTotalDegree w f ≤ n)
    (h : weightedHomogeneousComponent w n f ≠ 0) :
    initialForm w f = weightedHomogeneousComponent w n f := by
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero h
  have hdn := weightedHomogeneousComponent_isWeightedHomogeneous (w := w) n f hd
  have hdf : d ∈ f.support :=
    mem_support_iff.2 fun h0 ↦ hd (by classical simp [coeff_weightedHomogeneousComponent, h0])
  rw [initialForm_def, le_antisymm hfn (hdn ▸ le_weightedTotalDegree w hdf)]

/-- The initial form of a sum of two polynomials of the same weighted total degree is the sum of
their initial forms, unless these cancel. -/
theorem initialForm_add (hfg : weightedTotalDegree w f = weightedTotalDegree w g)
    (h : initialForm w f + initialForm w g ≠ 0) :
    initialForm w (f + g) = initialForm w f + initialForm w g := by
  have hcomp : weightedHomogeneousComponent w (weightedTotalDegree w f) (f + g) =
      initialForm w f + initialForm w g := by
    rw [map_add, initialForm_def, initialForm_def, hfg]
  rw [← hcomp]
  refine initialForm_eq_weightedHomogeneousComponent w ?_ (hcomp ▸ h)
  classical
  refine Finset.sup_le fun d hd ↦ ?_
  rcases Finset.mem_union.1 (support_add hd) with hd | hd
  · exact le_weightedTotalDegree w hd
  · exact hfg ▸ le_weightedTotalDegree w hd

end SemilatticeSup

section LinearOrder

variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] (w : σ → M) {f : MvPolynomial σ R}

/-- The initial form of `f` vanishes exactly when `f` does. -/
@[simp]
theorem initialForm_eq_zero_iff : initialForm w f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ by_contra fun hf ↦ ?_, fun h ↦ h ▸ initialForm_zero w⟩
  obtain ⟨d, hd, hdf⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.2 hf) (weight w)
  exact (mem_support_iff.1 ((mem_support_initialForm w).2 ⟨hd, hdf.symm⟩)) (by simp [h])

theorem initialForm_ne_zero_iff : initialForm w f ≠ 0 ↔ f ≠ 0 :=
  (initialForm_eq_zero_iff w).not

@[simp]
theorem weightedTotalDegree_initialForm (f : MvPolynomial σ R) :
    weightedTotalDegree w (initialForm w f) = weightedTotalDegree w f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hf' := (initialForm_ne_zero_iff w).2 hf
  simpa [weightedTotalDegree_coe w _ hf'] using
    (isWeightedHomogeneous_initialForm w f).weighted_total_degree hf'

end LinearOrder

section Mul

variable {w : σ → M} {t : MvPolynomial σ R} {i : M}

attribute [local instance] weightedGradedAlgebra in
/-- Multiplying by a polynomial `t` that is weighted homogeneous of weight `i` shifts weighted
homogeneous components by `i`. -/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_mul_left [AddCancelCommMonoid M]
    (ht : IsWeightedHomogeneous w t i)
    (f : MvPolynomial σ R) (n : M) :
    weightedHomogeneousComponent w (i + n) (t * f) = t * weightedHomogeneousComponent w n f := by
  classical
  have key (φ : MvPolynomial σ R) (k : M) :
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) φ k : MvPolynomial σ R) =
        weightedHomogeneousComponent w k φ :=
    weightedDecomposition.decompose'_apply R w φ k
  simpa only [key] using DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule R w) (j := n) (b := f)
    ((mem_weightedHomogeneousSubmodule R w i t).2 ht)

/-- The weighted homogeneous components of `t * f`, for `t` weighted homogeneous of weight `i`,
vanish in every weight not of the form `i + k`. -/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_mul_left_eq_zero [AddCommMonoid M]
    (ht : IsWeightedHomogeneous w t i) {n : M} (hn : ∀ k, n ≠ i + k) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (t * f) = 0 := by
  classical
  refine weightedHomogeneousComponent_eq_zero' _ _ fun d hd hdn ↦ ?_
  obtain ⟨x, hx, y, -, rfl⟩ := Finset.mem_add.1 (support_mul t f hd)
  exact hn (weight w y) (by rw [← hdn, map_add, ht (mem_support_iff.1 hx)])

variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] [IsOrderedCancelAddMonoid M] (w)
  {f g : MvPolynomial σ R}

/-- The initial form of a product is the product of the initial forms, unless this product
vanishes. -/
theorem initialForm_mul (h : initialForm w f * initialForm w g ≠ 0) :
    initialForm w (f * g) = initialForm w f * initialForm w g := by
  classical
  -- The component of `f * g` of weight `weightedTotalDegree w f + weightedTotalDegree w g` only
  -- receives products of terms of maximal weight.
  have hcomp : weightedHomogeneousComponent w
      (weightedTotalDegree w f + weightedTotalDegree w g) (f * g) =
        initialForm w f * initialForm w g := by
    ext d
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · simp only [coeff_mul]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      by_cases h₁ : p.1 ∈ f.support
      · by_cases h₂ : p.2 ∈ g.support
        · have := (add_eq_add_iff_eq_and_eq (le_weightedTotalDegree w h₁)
            (le_weightedTotalDegree w h₂)).1 (by rw [← map_add, hp, hd])
          simp [coeff_initialForm, this]
        · simp [notMem_support_iff.1 h₂, coeff_initialForm]
      · simp [notMem_support_iff.1 h₁, coeff_initialForm]
    · exact (((isWeightedHomogeneous_initialForm w f).mul
        (isWeightedHomogeneous_initialForm w g)).coeff_eq_zero d hd).symm
  rw [← hcomp]
  refine initialForm_eq_weightedHomogeneousComponent w (Finset.sup_le fun d hd ↦ ?_) (hcomp ▸ h)
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul f g hd)
  rw [map_add]
  exact add_le_add (le_weightedTotalDegree w hx) (le_weightedTotalDegree w hy)

end Mul

section Ideal

variable [AddCancelCommMonoid M] [LinearOrder M] [OrderBot M] [IsOrderedCancelAddMonoid M]
  (w : σ → M)

omit [IsOrderedCancelAddMonoid M] in
/-- If the initial forms of `f` and `g` in `I` are weighted homogeneous of the same weight, then
their sum is the initial form of an element of `I`. -/
private theorem exists_initialForm_eq_add {I : Ideal (MvPolynomial σ R)} {f g : MvPolynomial σ R}
    (hf : f ∈ I) (hg : g ∈ I) {n : M} (hfn : IsWeightedHomogeneous w (initialForm w f) n)
    (hgn : IsWeightedHomogeneous w (initialForm w g) n) :
    ∃ p ∈ I, initialForm w p = initialForm w f + initialForm w g := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨g, hg, by simp⟩
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨f, hf, by simp⟩
  by_cases h : initialForm w f + initialForm w g = 0
  · exact ⟨0, I.zero_mem, by simp [h]⟩
  have hfg : weightedTotalDegree w f = weightedTotalDegree w g :=
    (hfn.inj_right ((initialForm_ne_zero_iff w).2 hf0)
      (isWeightedHomogeneous_initialForm w f)).symm.trans
      (hgn.inj_right ((initialForm_ne_zero_iff w).2 hg0) (isWeightedHomogeneous_initialForm w g))
  exact ⟨f + g, I.add_mem hf hg, initialForm_add w hfg h⟩

/-- Every weighted homogeneous component of an element of the initial ideal `in_w(I)`, the ideal
spanned by the initial forms of the elements of `I`, is the initial form of an element of `I`. -/
theorem exists_initialForm_eq_weightedHomogeneousComponent {I : Ideal (MvPolynomial σ R)}
    {g : MvPolynomial σ R} (hg : g ∈ Ideal.span (initialForm w '' I)) (n : M) :
    ∃ f ∈ I, initialForm w f = weightedHomogeneousComponent w n g := by
  -- The property holds for initial forms and is preserved by sums and monomial multiples.
  have hadd {x y : MvPolynomial σ R}
      (hx : ∀ n, ∃ f ∈ I, initialForm w f = weightedHomogeneousComponent w n x)
      (hy : ∀ n, ∃ f ∈ I, initialForm w f = weightedHomogeneousComponent w n y) (n : M) :
      ∃ f ∈ I, initialForm w f = weightedHomogeneousComponent w n (x + y) := by
    obtain ⟨f, hf, hfx⟩ := hx n
    obtain ⟨f', hf', hfy⟩ := hy n
    rw [map_add, ← hfx, ← hfy]
    exact exists_initialForm_eq_add w hf hf'
      (hfx ▸ weightedHomogeneousComponent_isWeightedHomogeneous n x)
      (hfy ▸ weightedHomogeneousComponent_isWeightedHomogeneous n y)
  induction hg using Submodule.span_induction generalizing n with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    by_cases hn : n = weightedTotalDegree w f
    · exact ⟨f, hf, by
        rw [hn, (isWeightedHomogeneous_initialForm w f).weightedHomogeneousComponent_same]⟩
    · exact ⟨0, I.zero_mem, by
        rw [initialForm_zero,
          (isWeightedHomogeneous_initialForm w f).weightedHomogeneousComponent_ne n hn]⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ hx hy => exact hadd hx hy n
  | smul a x _ hx =>
    induction a using MvPolynomial.induction_on' generalizing n with
    | monomial u c =>
      have hu := isWeightedHomogeneous_monomial w u c rfl
      by_cases hk : ∃ k, n = weight w u + k
      · obtain ⟨k, rfl⟩ := hk
        obtain ⟨f, hf, hfx⟩ := hx k
        rw [smul_eq_mul, hu.weightedHomogeneousComponent_mul_left, ← hfx]
        by_cases h0 : monomial u c * initialForm w f = 0
        · exact ⟨0, I.zero_mem, by simp [h0]⟩
        · refine ⟨_, I.mul_mem_left (monomial u c) hf, ?_⟩
          rw [initialForm_mul w (by rwa [initialForm_monomial]), initialForm_monomial]
      · simp only [not_exists] at hk
        exact ⟨0, I.zero_mem, by
          rw [smul_eq_mul, hu.weightedHomogeneousComponent_mul_left_eq_zero hk, initialForm_zero]⟩
    | add p q hp hq =>
      rw [add_smul]
      exact hadd hp hq n

end Ideal

end MvPolynomial

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} [CommSemiring R] (m : MonomialOrder σ)

section Weight

variable {M : Type*} [AddCommMonoid M] (w : σ → M)

/-- The weighted homogeneous component of `f` containing its leading monomial has the same
leading monomial. -/
theorem degree_weightedHomogeneousComponent (f : MvPolynomial σ R) :
    m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f) = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  classical
  have hd : m.degree f ∈ (weightedHomogeneousComponent w (weight w (m.degree f)) f).support := by
    simpa [coeff_weightedHomogeneousComponent] using m.degree_mem_support hf
  have hsub : (weightedHomogeneousComponent w (weight w (m.degree f)) f).support ⊆ f.support :=
    fun d hd ↦ MvPolynomial.mem_support_iff.2 fun h0 ↦ MvPolynomial.mem_support_iff.1 hd (by
      simp [coeff_weightedHomogeneousComponent, h0])
  exact m.toSyn.injective <|
    le_antisymm (m.degree_le_degree_of_support_subset hsub) (m.le_degree hd)

/-- The weighted homogeneous component of `f` containing its leading monomial has the same
leading coefficient. -/
theorem leadingCoeff_weightedHomogeneousComponent (f : MvPolynomial σ R) :
    m.leadingCoeff (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingCoeff f := by
  classical
  simp [leadingCoeff, degree_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]

/-- The weighted homogeneous component of `f` containing its leading monomial has the same
leading term. -/
theorem leadingTerm_weightedHomogeneousComponent (f : MvPolynomial σ R) :
    m.leadingTerm (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingTerm f := by
  simp [leadingTerm, degree_weightedHomogeneousComponent,
    leadingCoeff_weightedHomogeneousComponent]

end Weight

variable (w : σ → ℕ)

/-- The leading monomial of `f` for `m.weightRefinement w` is the leading monomial of the initial
form of `f` for `m`. -/
theorem degree_weightRefinement (f : MvPolynomial σ R) :
    (m.weightRefinement w).degree f = m.degree (initialForm w f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  set d := (m.weightRefinement w).degree f
  have hd := (m.weightRefinement w).degree_mem_support hf
  have hle (c : σ →₀ ℕ) (hc : c ∈ f.support) : weight w c ≤ weight w d :=
    weight_le_weight_of_weightRefinement_le ((m.weightRefinement w).le_degree hc)
  have hdeg : weight w d = weightedTotalDegree w f :=
    le_antisymm (le_weightedTotalDegree w hd) (Finset.sup_le hle)
  have hd' : d ∈ (initialForm w f).support := (mem_support_initialForm w).2 ⟨hd, hdeg⟩
  -- Among the monomials of `f` of maximal weight, `d` is the largest for `m`.
  refine (m.toSyn.injective <| le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree hd'))
    |>.symm
  obtain ⟨hcf, hc⟩ := (mem_support_initialForm w).1 hc
  exact (weightRefinement_le_iff_of_weight_eq (hc.trans hdeg.symm)).1
    ((m.weightRefinement w).le_degree hcf)

/-- The leading coefficient of `f` for `m.weightRefinement w` is the leading coefficient of the
initial form of `f` for `m`. -/
theorem leadingCoeff_weightRefinement (f : MvPolynomial σ R) :
    (m.weightRefinement w).leadingCoeff f = m.leadingCoeff (initialForm w f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  classical
  have hd := m.degree_mem_support ((initialForm_ne_zero_iff w).2 hf)
  simp only [leadingCoeff, degree_weightRefinement, coeff_initialForm,
    ((mem_support_initialForm w).1 hd).2, ↓reduceIte]

/-- The leading term of `f` for `m.weightRefinement w` is the leading term of the initial form of
`f` for `m`. -/
theorem leadingTerm_weightRefinement (f : MvPolynomial σ R) :
    (m.weightRefinement w).leadingTerm f = m.leadingTerm (initialForm w f) := by
  simp [leadingTerm, degree_weightRefinement, leadingCoeff_weightRefinement]

/-- **Initial ideals of a refined order.** The leading terms of the elements of `I` for the
refined order `m.weightRefinement w` span the same ideal as the leading terms for `m` of the
elements of the weight initial ideal `in_w(I)`, the ideal spanned by the initial forms of the
elements of `I`: in symbols, `in_{m_w}(I) = in_m(in_w(I))`. -/
theorem span_leadingTerm_weightRefinement (I : Ideal (MvPolynomial σ R)) :
    Ideal.span ((m.weightRefinement w).leadingTerm '' I) = Ideal.span (m.leadingTerm ''
      ((Ideal.span (initialForm w '' I) : Ideal (MvPolynomial σ R)) : Set (MvPolynomial σ R))) := by
  refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, Ideal.subset_span ⟨f, hf, rfl⟩, (m.leadingTerm_weightRefinement w f).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    -- The leading term of `g` is that of its weighted homogeneous component containing its
    -- leading monomial, which is the initial form of an element of `I`.
    obtain ⟨f, hf, hfg⟩ := exists_initialForm_eq_weightedHomogeneousComponent w hg
      (weight w (m.degree g))
    rw [← m.leadingTerm_weightedHomogeneousComponent w, ← hfg,
      ← m.leadingTerm_weightRefinement w]
    exact Ideal.subset_span ⟨f, hf, rfl⟩

end MonomialOrder
