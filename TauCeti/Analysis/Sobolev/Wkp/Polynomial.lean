/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Polynomial classes in Sobolev spaces

On a bounded open set, every polynomial function defines a Sobolev class of every order and
exponent, including infinity. The map `TauCeti.Wkp.polynomialL` is continuous and linear for the
pointwise topology on the finite-dimensional space of bounded-degree polynomial functions.
It is injective when the open set is nonempty.

Its range `TauCeti.Wkp.polynomialClasses` is the finite-dimensional, closed subspace of classes
with a polynomial representative of the prescribed degree. This is the subspace used when
forming Sobolev spaces modulo polynomials. No connectedness or boundary regularity is required.

The construction uses the classical-to-weak Sobolev representative theorem and Mathlib's
continuity theorem for linear maps from finite-dimensional Hausdorff spaces.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace

variable {ι : Type*} [Fintype ι]
  {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
  {Ω : Opens (EuclideanSpace ℝ ι)} {p : ENNReal} [Fact (1 ≤ p)]

/-- A polynomial function on a bounded open set represents a Sobolev function of every order. -/
private theorem exists_value_ae_eq_polynomial
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k : ℕ) {m : ℕ} (q : polynomialsDegLE ι m) :
    ∃ u : Wkp μ Ω p k, (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict Ω] q :=
  exists_value_ae_eq_of_contDiffOn_of_isCompact k isOpen_univ
    (contDiff_of_mem_polynomialsDegLE q.property).contDiffOn
    hΩ.isCompact_closure subset_closure (Set.subset_univ _)

/-- Send a bounded-degree polynomial function to its Sobolev class on a bounded open set.
The domain has the topology induced by pointwise convergence of functions. -/
def polynomialL (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    polynomialsDegLE ι m →L[ℝ] Wkp μ Ω p k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => (exists_value_ae_eq_polynomial hΩ k q).choose
      map_add' := by
        intro q r
        apply ext k
        rw [value_add]
        apply Lp.ext
        filter_upwards [(exists_value_ae_eq_polynomial (p := p) hΩ k (q + r)).choose_spec,
          (exists_value_ae_eq_polynomial (p := p) hΩ k q).choose_spec,
          (exists_value_ae_eq_polynomial (p := p) hΩ k r).choose_spec,
          Lp.coeFn_add (value k (exists_value_ae_eq_polynomial (p := p) hΩ k q).choose)
            (value k (exists_value_ae_eq_polynomial (p := p) hΩ k r).choose)] with x hqr hq hr hsum
        simpa only [hsum, hq, hr, Submodule.coe_add, Pi.add_apply] using hqr
      map_smul' := by
        intro c q
        apply ext k
        simp only [RingHom.id_apply, value_smul]
        apply Lp.ext
        filter_upwards [(exists_value_ae_eq_polynomial (p := p) hΩ k (c • q)).choose_spec,
          (exists_value_ae_eq_polynomial (p := p) hΩ k q).choose_spec,
          Lp.coeFn_smul c (value k (exists_value_ae_eq_polynomial (p := p) hΩ k q).choose)]
          with x hcq hq hsmul
        simpa only [hsmul, hq, Submodule.coe_smul, Pi.smul_apply] using hcq }

/-- The value of the polynomial Sobolev class is the given polynomial almost everywhere. -/
theorem value_polynomialL_ae (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k m : ℕ) (q : polynomialsDegLE ι m) :
    (value k (polynomialL (μ := μ) (p := p) hΩ k m q) : EuclideanSpace ℝ ι → ℝ)
      =ᵐ[μ.restrict Ω] q :=
  (exists_value_ae_eq_polynomial hΩ k q).choose_spec

/-- A Sobolev function is the class of `q` exactly when its value is `q` almost everywhere. -/
theorem eq_polynomialL_iff (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k m : ℕ) (u : Wkp μ Ω p k) (q : polynomialsDegLE ι m) :
    u = polynomialL hΩ k m q ↔
      (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict Ω] q := by
  constructor
  · rintro rfl
    exact value_polynomialL_ae hΩ k m q
  · intro hu
    exact ext k (Lp.ext (hu.trans (value_polynomialL_ae hΩ k m q).symm))

/-- Forgetting the highest weak derivative preserves a polynomial's Sobolev class. -/
-- Avoid indexing through the reducible Sobolev type inside the class map, and rewrite
-- polynomial classes before `lowerOrder_zero` unfolds the projection.
@[simp high]
theorem lowerOrder_polynomialL
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k m : ℕ) (q : polynomialsDegLE ι m) :
    lowerOrder k (no_index (polynomialL (μ := μ) (p := p) hΩ (k + 1) m q)) =
      polynomialL hΩ k m q := by
  apply (eq_polynomialL_iff hΩ k m _ q).2
  rw [← value_succ]
  exact value_polynomialL_ae hΩ (k + 1) m q

/-- The highest weak derivative of a polynomial class is its classical iterated gradient
almost everywhere on the domain. -/
theorem iteratedGradient_polynomialL_ae
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k m : ℕ) (q : polynomialsDegLE ι m) :
    (iteratedGradient k (polynomialL (μ := μ) (p := p) hΩ (k + 1) m q) :
      EuclideanSpace ℝ ι → IteratedGradient (EuclideanSpace ℝ ι) k)
      =ᵐ[μ.restrict Ω] iteratedGradientChain q k :=
  iteratedGradient_ae_eq_of_contDiffOn k _
    (contDiff_of_mem_polynomialsDegLE q.property).contDiffOn
    (value_polynomialL_ae hΩ (k + 1) m q)

/-- The highest weak derivative of a polynomial class has the classical derivative's
`Lᵖ` seminorm. -/
theorem norm_iteratedGradient_polynomialL
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k m : ℕ) (q : polynomialsDegLE ι m) :
    ‖iteratedGradient k (polynomialL (μ := μ) (p := p) hΩ (k + 1) m q)‖ =
      lpNorm (iteratedFDeriv ℝ (k + 1) (q : EuclideanSpace ℝ ι → ℝ)) p (μ.restrict Ω) :=
  norm_iteratedGradient_eq_lpNorm_of_contDiffOn k _
    (contDiff_of_mem_polynomialsDegLE q.property).contDiffOn
    (value_polynomialL_ae hΩ (k + 1) m q)

/-- On a nonempty open set, taking a polynomial's Sobolev class loses no information. -/
theorem polynomialL_injective (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hΩne : (Ω : Set (EuclideanSpace ℝ ι)).Nonempty) (k m : ℕ) :
    Function.Injective (polynomialL (μ := μ) (p := p) hΩ k m) := by
  intro q r h
  have hae := (value_polynomialL_ae hΩ k m q).symm.trans
    (h ▸ value_polynomialL_ae hΩ k m r)
  exact Subtype.ext <| eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen q.property r.property
    Ω.isOpen hΩne hae

/-- The subspace of Sobolev classes represented by polynomials of degree at most `m`. -/
def polynomialClasses (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    Submodule ℝ (Wkp μ Ω p k) :=
  (polynomialL hΩ k m).toLinearMap.range

/-- The polynomial subspace is the range of the polynomial class map. -/
theorem polynomialClasses_def
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    polynomialClasses (μ := μ) (p := p) hΩ k m = (polynomialL hΩ k m).toLinearMap.range :=
  (rfl)

/-- A polynomial's Sobolev class belongs to the polynomial subspace. -/
@[simp]
theorem polynomialL_mem_polynomialClasses
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (k m : ℕ) (q : polynomialsDegLE ι m) :
    polynomialL (μ := μ) (p := p) hΩ k m q ∈ polynomialClasses hΩ k m := by
  rw [polynomialClasses_def]
  exact LinearMap.mem_range_self _ q

/-- Membership in the polynomial subspace means having a bounded-degree polynomial
representative almost everywhere. -/
theorem mem_polynomialClasses_iff
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) (u : Wkp μ Ω p k) :
    u ∈ polynomialClasses hΩ k m ↔ ∃ q : polynomialsDegLE ι m,
      (value k u : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict Ω] q := by
  simp only [polynomialClasses, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
    ← eq_polynomialL_iff hΩ k m, eq_comm]

/-- Increasing the degree bound enlarges the polynomial Sobolev subspace. -/
theorem polynomialClasses_mono
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k : ℕ) :
    Monotone (polynomialClasses (μ := μ) (p := p) hΩ k) := by
  intro m n hmn u hu
  obtain ⟨q, hq⟩ := (mem_polynomialClasses_iff hΩ k m u).1 hu
  exact (mem_polynomialClasses_iff hΩ k n u).2
    ⟨⟨q, polynomialsDegLE_mono ι hmn q.property⟩, hq⟩

/-- Polynomial Sobolev classes form a finite-dimensional subspace, including on the empty set. -/
instance finiteDimensional_polynomialClasses
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    FiniteDimensional ℝ (polynomialClasses (μ := μ) (p := p) hΩ k m) := by
  unfold polynomialClasses
  infer_instance

/-- Order-zero polynomial classes form a finite-dimensional subspace. This instance handles
the reduction of `Wkp` at order zero during instance search. -/
instance finiteDimensional_polynomialClasses_zero
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (m : ℕ) :
    FiniteDimensional ℝ (polynomialClasses (μ := μ) (p := p) hΩ 0 m) :=
  finiteDimensional_polynomialClasses hΩ 0 m

/-- Positive-order polynomial classes form a finite-dimensional subspace. This instance handles
the reduction of `Wkp` at successor orders during instance search. -/
instance finiteDimensional_polynomialClasses_succ
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    FiniteDimensional ℝ (polynomialClasses (μ := μ) (p := p) hΩ (k + 1) m) :=
  finiteDimensional_polynomialClasses hΩ (k + 1) m

/-- The finite-dimensional polynomial subspace is closed, giving a Hausdorff normed quotient. -/
instance isClosed_polynomialClasses
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    IsClosed (polynomialClasses (μ := μ) (p := p) hΩ k m : Set (Wkp μ Ω p k)) :=
  Submodule.isClosed_of_finiteDimensional _

/-- Order-zero polynomial classes are closed. This instance handles the reduction of `Wkp`
at order zero during instance search. -/
instance isClosed_polynomialClasses_zero
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (m : ℕ) :
    IsClosed (polynomialClasses (μ := μ) (p := p) hΩ 0 m : Set (Wkp μ Ω p 0)) :=
  isClosed_polynomialClasses hΩ 0 m

/-- Positive-order polynomial classes are closed. This instance handles the reduction of `Wkp`
at successor orders during instance search. -/
instance isClosed_polynomialClasses_succ
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (k m : ℕ) :
    IsClosed (polynomialClasses (μ := μ) (p := p) hΩ (k + 1) m : Set (Wkp μ Ω p (k + 1))) :=
  isClosed_polynomialClasses hΩ (k + 1) m

/-- On a nonempty open set the dimension of polynomial Sobolev classes is the number of
monomials of total degree at most `m`. -/
@[simp]
theorem finrank_polynomialClasses
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hΩne : (Ω : Set (EuclideanSpace ℝ ι)).Nonempty) (k m : ℕ) :
    Module.finrank ℝ (polynomialClasses (μ := μ) (p := p) hΩ k m) =
      (m + Fintype.card ι).choose (Fintype.card ι) := by
  rw [polynomialClasses,
    LinearMap.finrank_range_of_inj (polynomialL_injective hΩ hΩne k m),
    finrank_polynomialsDegLE]

end TauCeti.Wkp
