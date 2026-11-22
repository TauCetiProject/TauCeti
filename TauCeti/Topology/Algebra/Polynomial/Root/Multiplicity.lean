/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Multiplicities along continuous polynomial sections

For a coefficientwise continuous family of locally bounded degree, multiplicity at a continuous
point is locally bounded above by its central value, provided the central polynomial is nonzero.
Hasse derivatives give this statement in arbitrary characteristic. Over an integral domain,
if each factor is nonzero at the base point and the multiplicity in a finite product is locally
constant, every factor multiplicity is locally constant: none can increase, and their sum cannot
decrease.

This transfers the multiplicities of root sections of a product to its individual factors,
including factors sharing roots and roots of multiplicity greater than one. For fixed polynomials
over Hausdorff topological domains without isolated points, the same continuity of evaluation yields
root-multiplicity comparison and vanishing for `Q.eval w + g w * P.eval w = 0`.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Section 2 (delineability of a polynomial basis).
-/

public section

open Filter Topology

namespace Polynomial

variable {B R : Type*} [TopologicalSpace B] [TopologicalSpace R]
  {r : B → R} {x₀ : B} {d : ℕ}

/-- Evaluation of a Hasse derivative along a point continuous at `x₀` is continuous at `x₀`
for a family whose coefficients of indices from `m` through `d` are continuous at `x₀` and
whose degrees are bounded by `d` near `x₀`. Coefficients below `m` do not affect the derivative. -/
theorem continuousAt_hasseDeriv_eval [Semiring R] [IsTopologicalSemiring R] {F : B → R[X]}
    (m : ℕ) (hF : ∀ i, m ≤ i → i ≤ d → ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀) :
    ContinuousAt (fun x ↦ (hasseDeriv m (F x)).eval (r x)) x₀ := by
  have hcoeff (i : ℕ) : ContinuousAt (fun x ↦ (hasseDeriv m (F x)).coeff i) x₀ := by
    by_cases hi : i + m ≤ d
    · simp only [hasseDeriv_coeff]
      exact continuousAt_const.mul (hF _ (Nat.le_add_left m i) hi)
    · refine (continuousAt_const (y := (0 : R))).congr_of_eventuallyEq ?_
      filter_upwards [hdeg] with x hx
      simp [hasseDeriv_coeff, coeff_eq_zero_of_natDegree_lt (hx.trans_lt (Nat.lt_of_not_ge hi))]
  exact continuousAt_eval (fun i _ ↦ hcoeff i)
    (hdeg.mono fun x hx ↦
      (natDegree_hasseDeriv_le _ _).trans ((Nat.sub_le _ _).trans hx)) hr

variable [CommRing R] [IsTopologicalSemiring R] {F : B → R[X]}

/-- Multiplicity at a continuous point cannot increase nearby when the central polynomial
is nonzero. Zero nearby polynomials are allowed, with their usual multiplicity zero. -/
theorem eventually_rootMultiplicity_le [T1Space R]
    (hF : ∀ i ≤ d, ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀)
    (hne : F x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, (F x).rootMultiplicity (r x) ≤ (F x₀).rootMultiplicity (r x₀) := by
  filter_upwards [(continuousAt_hasseDeriv_eval _ (fun i _ hi ↦ hF i hi) hdeg hr).eventually_ne
    (eval_hasseDeriv_rootMultiplicity_ne_zero hne (r x₀))] with x hx
  rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
  exact natTrailingDegree_le_of_ne_zero (by rwa [taylor_coeff])

/-- Along a continuous point, locally constant multiplicity in a nonzero finite product
forces locally constant multiplicity in every factor. No coprimality is required. -/
theorem eventually_rootMultiplicity_eq_of_prod [IsDomain R] [T1Space R]
    {ι : Type*} {F : ι → B → R[X]} {d : ι → ℕ} (s : Finset ι)
    (hF : ∀ k ∈ s, ∀ i ≤ d k, ContinuousAt (fun x ↦ (F k x).coeff i) x₀)
    (hdeg : ∀ k ∈ s, ∀ᶠ x in 𝓝 x₀, (F k x).natDegree ≤ d k) (hr : ContinuousAt r x₀)
    (hne : ∀ k ∈ s, F k x₀ ≠ 0)
    (hmult : ∀ᶠ x in 𝓝 x₀,
      (∏ k ∈ s, F k x).rootMultiplicity (r x) =
        (∏ k ∈ s, F k x₀).rootMultiplicity (r x₀)) :
    ∀ᶠ x in 𝓝 x₀, ∀ k ∈ s, (F k x).rootMultiplicity (r x) =
      (F k x₀).rootMultiplicity (r x₀) := by
  classical
  have hsum (x : B) (hx : ∀ k ∈ s, F k x ≠ 0) :
      (∏ k ∈ s, F k x).rootMultiplicity (r x) =
        ∑ k ∈ s, (F k x).rootMultiplicity (r x) := by
    rw [← count_roots, roots_prod _ _ (Finset.prod_ne_zero_iff.2 hx), Multiset.count_bind]
    simp only [count_roots, Finset.sum_map_val]
  have hle := (eventually_all_finset s).2 fun k hk ↦
    eventually_rootMultiplicity_le (hF k hk) (hdeg k hk) hr (hne k hk)
  have hnonzero : ∀ᶠ x in 𝓝 x₀, ∀ k ∈ s, F k x ≠ 0 :=
    (eventually_all_finset s).2 fun k hk ↦ by
      have hc := (hF k hk _ (hdeg k hk).self_of_nhds).eventually_ne
        (by simpa only [coeff_natDegree] using (leadingCoeff_ne_zero.2 (hne k hk)))
      exact hc.mono fun x hx hzero ↦ hx (by simp [hzero])
  filter_upwards [hle, hnonzero, hmult] with x hx hxne hxm
  rw [hsum x hxne, hsum x₀ hne] at hxm
  exact (Finset.sum_eq_sum_iff_of_le hx).1 hxm

omit [IsTopologicalSemiring R] in
/-- If `Q.eval w + g w * P.eval w = 0` everywhere on a Hausdorff topological integral domain `R`,
with `P, Q ≠ 0` and `g` continuous at a non-isolated point `ζ`, then
`P.rootMultiplicity ζ ≤ Q.rootMultiplicity ζ`. -/
theorem rootMultiplicity_le_of_eval_add_mul_eval_eq_zero [IsTopologicalRing R] [IsDomain R]
    [T2Space R] {g : R → R} {ζ : R} [(𝓝[≠] ζ).NeBot] (hg : ContinuousAt g ζ) {P Q : R[X]}
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (h : ∀ w, Q.eval w + g w * P.eval w = 0) :
    P.rootMultiplicity ζ ≤ Q.rootMultiplicity ζ := by
  by_contra! hlt
  obtain ⟨Q₁, hQ₁, hndvd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ0 ζ
  obtain ⟨P₁, hP₁⟩ := (le_rootMultiplicity_iff hP0).mp hlt
  have hlim : Tendsto (fun w ↦ Q₁.eval w + g w * ((w - ζ) * P₁.eval w)) (𝓝[≠] ζ)
      (𝓝 (Q₁.eval ζ)) := by
    have hc : ContinuousAt (fun w ↦ Q₁.eval w + g w * ((w - ζ) * P₁.eval w)) ζ :=
      Q₁.continuous.continuousAt.add (hg.mul
        ((continuousAt_id.sub continuousAt_const).mul P₁.continuous.continuousAt))
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : (fun w ↦ Q₁.eval w + g w * ((w - ζ) * P₁.eval w)) =ᶠ[𝓝[≠] ζ] fun _ ↦ 0 := by
    filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ ζ)
    have hw0 : (w - ζ) ^ Q.rootMultiplicity ζ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
    have h0 := h w
    rw [hQ₁, hP₁, pow_succ] at h0
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h0
    exact mul_left_cancel₀ hw0 (by linear_combination h0)
  have hQ₁0 : Q₁.eval ζ = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero.symm)
  exact hndvd (dvd_iff_isRoot.mpr hQ₁0)

/-- If `Q.eval w + g w * P.eval w = 0` everywhere on a Hausdorff topological field `K` without
isolated points, where `P` splits, `Q.degree < P.degree`, and `g` is continuous at every root of
`P`, then `Q = 0`. -/
theorem eq_zero_of_eval_add_mul_eval_eq_zero {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [∀ ζ : K, (𝓝[≠] ζ).NeBot] {g : K → K} {P Q : K[X]}
    (hP : P.Splits) (hdeg : Q.degree < P.degree) (hg : ∀ ζ, P.IsRoot ζ → ContinuousAt g ζ)
    (h : ∀ w, Q.eval w + g w * P.eval w = 0) : Q = 0 := by
  have hP0 : P ≠ 0 := ne_zero_of_degree_gt hdeg
  by_contra hQ0
  classical
  have hdvd : P ∣ Q := hP.dvd_of_roots_le_roots hP0 <| Multiset.le_iff_count.mpr fun ζ ↦ by
    rw [count_roots, count_roots]
    rcases Nat.eq_zero_or_pos (P.rootMultiplicity ζ) with h0 | hpos
    · simp [h0]
    · exact rootMultiplicity_le_of_eval_add_mul_eval_eq_zero
        (hg ζ ((rootMultiplicity_pos hP0).mp hpos)) hP0 hQ0 h
  exact hQ0 (eq_zero_of_dvd_of_degree_lt hdvd hdeg)

end Polynomial

namespace TauCeti.Polynomial

variable {B R ι : Type*} [TopologicalSpace B] [PreconnectedSpace B]
  [TopologicalSpace R] [CommRing R] [IsTopologicalSemiring R] [IsDomain R] [T1Space R]
  {F : ι → B → _root_.Polynomial R} {r : B → R} {d : ι → ℕ}

/-- Constant multiplicity along a continuous point in a nonzero finite product forces
constant multiplicity in each factor on a preconnected base. Only degree bounds are needed;
the factors need not be coprime. -/
theorem rootMultiplicity_eq_of_prod (s : Finset ι)
    (hF : ∀ k ∈ s, ∀ i ≤ d k, Continuous fun x ↦ (F k x).coeff i)
    (hdeg : ∀ k ∈ s, ∀ x, (F k x).natDegree ≤ d k) (hr : Continuous r)
    (hne : ∀ k ∈ s, ∀ x, F k x ≠ 0)
    (hmult : ∀ x y, (∏ k ∈ s, F k x).rootMultiplicity (r x) =
      (∏ k ∈ s, F k y).rootMultiplicity (r y))
    (k : ι) (hk : k ∈ s) (x y : B) :
    (F k x).rootMultiplicity (r x) = (F k y).rootMultiplicity (r y) := by
  have hl : IsLocallyConstant fun x ↦ (F k x).rootMultiplicity (r x) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦ ?_
    exact (_root_.Polynomial.eventually_rootMultiplicity_eq_of_prod s
      (fun k hk i hi ↦ (hF k hk i hi).continuousAt)
      (fun k hk ↦ .of_forall (hdeg k hk)) hr.continuousAt
      (fun k hk ↦ hne k hk x₀) (.of_forall fun x ↦ hmult x x₀)).mono
        fun _ hx ↦ hx k hk
  exact hl.apply_eq_of_preconnectedSpace x y

end TauCeti.Polynomial
