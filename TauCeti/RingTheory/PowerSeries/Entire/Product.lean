/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.RingTheory.PowerSeries.Entire.Factorization
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
import Mathlib.Order.Northcott
import Mathlib.Topology.Algebra.InfiniteSum.Group
import TauCeti.Analysis.Normed.Ring.InfiniteProd.Ultra

/-!
# Weierstrass products of entire power series

Let `R` be an ultrametric normed commutative ring. Since the Gauss topology on the ring
`PowerSeries.IsEntire.subring R` of entire series is induced by the closed-disc restrictions at all
positive radii and its restriction image is determined by coefficient compatibility
(`TauCeti.PowerSeries.IsEntire.range_restrictFamily`), an infinite product converges in
`PowerSeries.IsEntire.subring R` if and only if its restrictions converge at every positive radius.
When `R` is complete, any family of entire series tending to `1` along the cofinite filter is
therefore unconditionally multipliable
(`TauCeti.PowerSeries.IsEntire.multipliable_of_tendsto_cofinite_one`).

In particular, for any family of slopes `a : ι → R` tending to `0` along `cofinite`, the linear
factors `1 - aᵢ X` have Gauss norm `‖aᵢ‖ r` away from `1` at each positive radius `r`, so the
Weierstrass product
```text
∏' i, (1 - aᵢ X)
```
converges unconditionally in `PowerSeries.IsEntire.subring R` (hence in every Gauss norm,
independently of any enumeration of `ι`), has constant coefficient `1`, and evaluates at any point
`b` of a complete normed commutative `R`-algebra as the infinite product `∏' i, (1 - aᵢ • b)`.

Over a complete ultrametric normed field `K`, specialising to `aᵢ = αᵢ⁻¹` for a family `α : ι → K`
of nonzero elements with `‖αᵢ‖ → ∞` along `cofinite` (equivalently, only finitely many `i` lie in
each closed disc) gives the converse of entire factorisation: at every positive radius `r`,
splitting off the finitely many factors with `‖αᵢ‖ ≤ r` exhibits the normalised disc preparation of
the product (`PowerSeries.IsEntire.isDiscPreparation_tprod_polynomialHom_one_sub_inv_mul_X`).
Consequently, in every complete normed field extension `L` of `K`, the zero multiset of the product
on each closed disc and its Taylor order at every point match `α` exactly. Allowing a power of `X`
for the zero at the origin constructs a nonzero entire series with any locally finite prescribed
multiplicity function `m : K → ℕ`.

Combining this converse with uniqueness by zero multiplicities
(`PowerSeries.IsEntire.eq_of_order_taylor_eq`) upgrades the disc-limit factorisation of
`TauCeti.RingTheory.PowerSeries.Entire.Factorization` over an algebraically closed complete
ultrametric field to unconditional `HasProd` convergence over any indexing of the zeros with
multiplicity, independent of enumeration.

## Main results

* `TauCeti.PowerSeries.IsEntire.hasProd_iff`, `TauCeti.PowerSeries.IsEntire.multipliable_iff` and
  `TauCeti.PowerSeries.IsEntire.multipliable_of_tendsto_cofinite_one`: unconditional products in
  the ring of entire series.
* `PowerSeries.IsEntire.multipliable_polynomialHom_one_sub_C_mul_X`,
  `PowerSeries.IsEntire.constantCoeff_tprod_polynomialHom_one_sub_C_mul_X` and
  `PowerSeries.IsEntire.hasProd_evalAt_tprod_polynomialHom_one_sub_C_mul_X`: convergence,
  normalisation and pointwise evaluation of `∏' i, (1 - aᵢ X)` over complete ultrametric rings.
* `PowerSeries.IsEntire.isDiscPreparation_tprod_polynomialHom_one_sub_inv_mul_X`,
  `PowerSeries.IsEntire.zeroMultiset_tprod_polynomialHom_one_sub_inv_mul_X`,
  `PowerSeries.IsEntire.order_taylor_map_tprod_polynomialHom_one_sub_inv_mul_X` and
  `PowerSeries.IsEntire.evalAt_map_tprod_polynomialHom_one_sub_inv_mul_X_eq_zero_iff`: disc
  preparation, zero multisets, multiplicities and zeros of `∏' i, (1 - αᵢ⁻¹ X)`.
* `PowerSeries.IsEntire.exists_isEntire_order_taylor_eq`,
  `PowerSeries.IsEntire.existsUnique_isEntire_constantCoeff_eq_one_order_taylor_eq` and
  `PowerSeries.IsEntire.exists_C_mul_eq_of_order_taylor_eq`: existence of entire series with
  prescribed locally finite zero multiplicities and uniqueness up to nonzero constants.
* `PowerSeries.IsEntire.tendsto_norm_cofinite_of_order_taylor_map_eq`,
  `PowerSeries.IsEntire.hasProd_polynomialHom_one_sub_inv_mul_X_of_order_taylor_eq`,
  `PowerSeries.IsEntire.hasProd_polynomialHom_one_sub_inv_mul_X` and
  `PowerSeries.IsEntire.hasProd_evalAt_one_sub_inv_smul`: norms of zeros tending to infinity and
  unconditional `HasProd` factorisation of normalised entire series.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §4, in particular (4.13).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate Texts
  in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open Filter PowerSeries
open scoped Topology

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
local instance (r : Set.Ioi (0 : ℝ)) : Fact (0 < (r : ℝ)) := ⟨r.2⟩

namespace TauCeti.PowerSeries.IsEntire

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- An infinite product converges in the Gauss topology of entire series if and only if its
restriction converges at every positive radius. -/
theorem hasProd_iff {ι : Type*} {f : ι → IsEntire.subring R} {g : IsEntire.subring R} :
    HasProd f g ↔ ∀ r : Set.Ioi (0 : ℝ), HasProd (fun i ↦ restrict r (f i)) (restrict r g) := by
  simp only [HasProd, tendsto_iff, map_prod]

/-- A family of entire series is unconditionally multipliable in the Gauss topology if and only if
its restriction to every positive-radius closed disc is multipliable. Completeness of `R` is not
required: the limit family automatically has radius-independent coefficients. -/
theorem multipliable_iff {ι : Type*} {f : ι → IsEntire.subring R} :
    Multipliable f ↔ ∀ r : Set.Ioi (0 : ℝ), Multipliable fun i ↦ restrict r (f i) := by
  refine ⟨fun ⟨g, hg⟩ r ↦ ⟨restrict r g, hasProd_iff.mp hg r⟩, fun h ↦ ?_⟩
  choose g hg using h
  have hmem : g ∈ Set.range (restrictFamily (R := R)) := by
    rw [range_restrictFamily]
    intro r s n
    have hr :=
      ((TauCeti.PowerSeries.uniformContinuous_coeff (R := R) (c := (r : ℝ)) n).continuous.tendsto
        (g r)).comp (hg r)
    have hs :=
      ((TauCeti.PowerSeries.uniformContinuous_coeff (R := R) (c := (s : ℝ)) n).continuous.tendsto
        (g s)).comp (hg s)
    refine tendsto_nhds_unique hr (hs.congr fun t ↦ ?_)
    dsimp only [Function.comp_def]
    rw [← map_prod, ← map_prod, coe_restrict, coe_restrict]
  obtain ⟨F, hF⟩ := hmem
  refine ⟨F, hasProd_iff.mpr fun r ↦ ?_⟩
  simpa only [← hF, restrictFamily_apply] using hg r

/-- **Unconditional products in the ring of entire series.** Over a complete ultrametric normed
commutative ring, any family of entire series tending to `1` along `cofinite` in the Gauss topology
is unconditionally multipliable. -/
theorem multipliable_of_tendsto_cofinite_one [CompleteSpace R] {ι : Type*}
    {f : ι → IsEntire.subring R} (hf : Tendsto f cofinite (𝓝 1)) : Multipliable f :=
  multipliable_iff.mpr fun r ↦
    TauCeti.multipliable_of_tendsto_cofinite_one <| by
      simpa only [map_one] using tendsto_iff.mp hf r

/-- A `HasProd` limit in the ring of entire series converges in the Gauss norm of every nonnegative
radius. -/
theorem tendsto_gaussNorm_sub_prod {ι : Type*} {f : ι → IsEntire.subring R}
    {g : IsEntire.subring R} (hf : HasProd f g) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t : Finset ι ↦ ((g : R⟦X⟧) - ∏ i ∈ t, (f i : R⟦X⟧)).gaussNorm norm s)
      atTop (𝓝 0) := by
  have hs1 : 0 < s + 1 := by linarith
  have : Fact (0 < s + 1) := ⟨hs1⟩
  let r : Set.Ioi (0 : ℝ) := ⟨s + 1, hs1⟩
  have hlim : Tendsto (fun t : Finset ι ↦ dist (restrict r g) (∏ i ∈ t, restrict r (f i)))
      atTop (𝓝 0) := by
    simpa only [dist_comm, SummationFilter.unconditional_filter] using
      tendsto_iff_dist_tendsto_zero.mp (hasProd_iff.mp hf r)
  refine squeeze_zero (fun t ↦ PowerSeries.gaussNorm_nonneg norm s _ norm_nonneg) (fun t ↦ ?_) hlim
  have hcoe : ((restrict r g - ∏ i ∈ t, restrict r (f i) :
      IsRestricted.subring (R := R) (r : ℝ)) : R⟦X⟧) = (g : R⟦X⟧) - ∏ i ∈ t, (f i : R⟦X⟧) := by
    simp only [AddSubgroupClass.coe_sub, coe_restrict]
    rw [← map_prod, coe_restrict,
      show ((∏ i ∈ t, f i : IsEntire.subring R) : R⟦X⟧) = ∏ i ∈ t, (f i : R⟦X⟧) from
        map_prod (IsEntire.subring R).subtype f t]
  rw [dist_eq_norm, TauCeti.PowerSeries.norm_eq_gaussNorm, hcoe]
  refine TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le norm_nonneg hs (by linarith) ?_
  rw [← hcoe]
  exact TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
    (restrict r g - ∏ i ∈ t, restrict r (f i)).2

/-- Taking constant coefficients commutes with `HasProd` in the ring of entire series. -/
theorem hasProd_constantCoeff {ι : Type*} {f : ι → IsEntire.subring R} {g : IsEntire.subring R}
    (hf : HasProd f g) :
    HasProd (fun i ↦ constantCoeff (f i : R⟦X⟧)) (constantCoeff (g : R⟦X⟧)) := by
  let φ : IsEntire.subring R →* R :=
    (constantCoeff : R⟦X⟧ →+* R).toMonoidHom.comp (IsEntire.subring R).subtype.toMonoidHom
  have hcont : Continuous φ := by
    change Continuous fun x : IsEntire.subring R ↦ constantCoeff (x : R⟦X⟧)
    simp_rw [← coeff_zero_eq_constantCoeff_apply]
    exact (uniformContinuous_coeff (R := R) 0).continuous
  exact hf.map φ hcont

/-- Evaluation at any point of a complete normed commutative `R`-algebra commutes with `HasProd` in
the ring of entire series. -/
theorem hasProd_evalAt {A ι : Type*} [NormedCommRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] {f : ι → IsEntire.subring R} {g : IsEntire.subring R} (hf : HasProd f g)
    (b : A) : HasProd (fun i ↦ (f i : R⟦X⟧).evalAt b) ((g : R⟦X⟧).evalAt b) := by
  simpa only [Function.comp_def, IsEntire.evalAtHom_apply] using
    hf.map (IsEntire.evalAtHom R b) (continuous_evalAtHom b)

end NormedCommRing

end TauCeti.PowerSeries.IsEntire

namespace PowerSeries.IsEntire

open TauCeti.PowerSeries

section CommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- The deviation `(1 - a X) - 1 = -a X` has Gauss norm `‖a‖ * r` at any positive radius `r`,
without requiring `‖1‖ = 1`. -/
private theorem norm_restrict_polynomialHom_one_sub_C_mul_X_sub_one (r : Set.Ioi (0 : ℝ)) (a : R) :
    ‖IsEntire.restrict r (IsEntire.polynomialHom (1 - Polynomial.C a * Polynomial.X)) - 1‖ =
      ‖a‖ * (r : ℝ) := by
  rw [norm_eq_gaussNorm]
  have hcoe : ((IsEntire.restrict r
      (IsEntire.polynomialHom (1 - Polynomial.C a * Polynomial.X)) - 1 :
        IsRestricted.subring (R := R) (r : ℝ)) : R⟦X⟧) = -(C a * X) := by
    simp
  rw [hcoe, gaussNorm_eq_of_forall_le (s := 1) fun m ↦ ?_]
  · simp
  · rcases m with _ | _ | m
    · simpa using mul_nonneg (norm_nonneg a) r.2.le
    · rfl
    · simpa using mul_nonneg (norm_nonneg a) r.2.le

/-- If `a : ι → R` tends to `0` along `cofinite`, then the linear polynomials `1 - aᵢ X` tend to
`1` along `cofinite` in the Gauss topology of entire series. -/
theorem tendsto_polynomialHom_one_sub_C_mul_X {ι : Type*} {a : ι → R}
    (ha : Tendsto a cofinite (𝓝 0)) :
    Tendsto (fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (a i) * Polynomial.X))
      cofinite (𝓝 1) := by
  rw [IsEntire.tendsto_iff]
  intro r
  rw [map_one, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_restrict_polynomialHom_one_sub_C_mul_X_sub_one]
  simpa using (ha.norm.mul_const (r : ℝ))

variable [CompleteSpace R]

/-- **Unconditional convergence of Weierstrass products over a complete ultrametric ring.** If
`a : ι → R` tends to `0` along `cofinite`, then `∏' i, (1 - aᵢ X)` converges unconditionally in
`PowerSeries.IsEntire.subring R`. -/
theorem multipliable_polynomialHom_one_sub_C_mul_X {ι : Type*} {a : ι → R}
    (ha : Tendsto a cofinite (𝓝 0)) :
    Multipliable fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (a i) * Polynomial.X) :=
  IsEntire.multipliable_of_tendsto_cofinite_one (tendsto_polynomialHom_one_sub_C_mul_X ha)

/-- A convergent Weierstrass product `∏' i, (1 - aᵢ X)` has constant coefficient `1`. -/
theorem constantCoeff_tprod_polynomialHom_one_sub_C_mul_X {ι : Type*} {a : ι → R}
    (ha : Tendsto a cofinite (𝓝 0)) :
    constantCoeff ((∏' i, IsEntire.polynomialHom
      (1 - Polynomial.C (a i) * Polynomial.X) : IsEntire.subring R) : R⟦X⟧) = 1 := by
  have hprod := IsEntire.hasProd_constantCoeff
    (multipliable_polynomialHom_one_sub_C_mul_X ha).hasProd
  have h1 : (fun i ↦ constantCoeff
      ((IsEntire.polynomialHom (1 - Polynomial.C (a i) * Polynomial.X) : IsEntire.subring R) :
        R⟦X⟧)) = fun _ ↦ (1 : R) := by
    ext i
    simp
  rw [h1] at hprod
  exact hprod.unique hasProd_one

/-- **Pointwise evaluation of a Weierstrass product.** At every element `b` of a complete normed
commutative `R`-algebra, evaluating `∏' i, (1 - aᵢ X)` gives the unconditional product
`∏' i, (1 - aᵢ • b)`. -/
theorem hasProd_evalAt_tprod_polynomialHom_one_sub_C_mul_X {A ι : Type*} [NormedCommRing A]
    [Algebra R A] [IsBoundedSMul R A] [CompleteSpace A] {a : ι → R}
    (ha : Tendsto a cofinite (𝓝 0)) (b : A) :
    HasProd (fun i ↦ 1 - a i • b)
      (((∏' i, IsEntire.polynomialHom
        (1 - Polynomial.C (a i) * Polynomial.X) : IsEntire.subring R) : R⟦X⟧).evalAt b) := by
  have hprod := IsEntire.hasProd_evalAt (multipliable_polynomialHom_one_sub_C_mul_X ha).hasProd b
  refine hprod.congr_fun fun i ↦ ?_
  rw [IsEntire.coe_polynomialHom, evalAt_coe, map_sub, map_one, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.smul_def]

/-- **Gauss-norm bound for a tail Weierstrass product.** If `a → 0` along `cofinite` and every
slope satisfies `‖aᵢ‖ * r < B` at a nonnegative radius `r` with `0 < B ≤ 1`, then the product
`F = ∏' i, (1 - aᵢ X)` satisfies `‖F - 1‖_r < B`. -/
theorem gaussNorm_tprod_polynomialHom_one_sub_C_mul_X_sub_one_lt {ι : Type*} {a : ι → R}
    (ha : Tendsto a cofinite (𝓝 0)) {r B : ℝ} (hr : 0 ≤ r) (hB0 : 0 < B) (hB1 : B ≤ 1)
    (h : ∀ i, ‖a i‖ * r < B) :
    ((((∏' i, IsEntire.polynomialHom
      (1 - Polynomial.C (a i) * Polynomial.X) : IsEntire.subring R) : R⟦X⟧) - 1)).gaussNorm
      norm r < B := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_]
    · rw [coeff_zero_eq_constantCoeff_apply, map_sub, map_one,
        constantCoeff_tprod_polynomialHom_one_sub_C_mul_X ha, sub_self, norm_zero, zero_mul]
      exact hB0
    · cases m with
      | zero => rfl
      | succ m => simp [zero_pow m.succ_ne_zero]
  · have : Fact (0 < r) := ⟨hr⟩
    let r' : Set.Ioi (0 : ℝ) := ⟨r, hr⟩
    have hprod := IsEntire.hasProd_iff.mp (multipliable_polynomialHom_one_sub_C_mul_X ha).hasProd r'
    have hlt := hprod.norm_sub_one_lt_of_forall_norm_sub_one_lt hB0 hB1 fun i ↦ by
      simpa only [norm_restrict_polynomialHom_one_sub_C_mul_X_sub_one] using h i
    simpa only [norm_eq_gaussNorm, AddSubgroupClass.coe_sub, IsEntire.coe_restrict,
      OneMemClass.coe_one] using hlt

end CommRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- If `‖α i‖ → ∞` along `cofinite`, then `(α i)⁻¹ → 0` along `cofinite`. -/
private theorem tendsto_inv_cofinite_zero {ι : Type*} {α : ι → K}
    (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) :
    Tendsto (fun i ↦ (α i)⁻¹) cofinite (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr <| by
    simpa only [Function.comp_def, norm_inv] using tendsto_inv_atTop_zero.comp hfin

omit [IsUltrametricDist K] in
/-- For a nonzero `a` with `‖a‖ * r ≥ 1` at a positive radius `r`, the linear polynomial `1 - a X`
is distinguished of degree `1` at `r`. -/
private theorem isDistinguished_one_sub_C_mul_X {r : ℝ} (hr : 0 < r) {a : K}
    (ha : 1 ≤ ‖a‖ * r) :
    IsDistinguished r 1 ((1 - Polynomial.C a * Polynomial.X : Polynomial K) : K⟦X⟧) := by
  simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X]
  have hgauss : (1 - C a * X : K⟦X⟧).gaussNorm norm r = ‖a‖ * r := by
    rw [gaussNorm_eq_of_forall_le (s := 1) fun m ↦ ?_]
    · simp
    · rcases m with _ | _ | m
      · simpa using ha
      · rfl
      · simpa using mul_nonneg (norm_nonneg a) hr.le
  refine ⟨by simp [hgauss], fun m hm ↦ ?_⟩
  rcases m with _ | _ | m
  · omega
  · omega
  · simpa [hgauss] using zero_lt_one.trans_le ha

/-- A finite product of factors `1 - αᵢ⁻¹ X` over points with `0 < ‖αᵢ‖ ≤ r` is distinguished of
degree equal to the number of factors. -/
private theorem isDistinguished_prod_one_sub_inv_mul_X {ι : Type*} {α : ι → K} {r : ℝ}
    (hr : 0 < r) (S : Finset ι) (hS : ∀ i ∈ S, α i ≠ 0 ∧ ‖α i‖ ≤ r) :
    IsDistinguished r S.card
      ((∏ i ∈ S, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) : Polynomial K) : K⟦X⟧) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using (gaussNorm_sub_one_lt_one_iff hr (isRestricted_one r) (map_one _)).mp (by simp)
  | insert i s hi ih =>
    obtain ⟨hαi, hle⟩ := hS i (Finset.mem_insert_self i s)
    have h1 : 1 ≤ ‖(α i)⁻¹‖ * r := by
      rw [norm_inv, inv_mul_eq_div]
      exact (one_le_div (norm_pos_iff.mpr hαi)).mpr hle
    have hstep := (isDistinguished_one_sub_C_mul_X hr h1).mul
      (ih fun j hj ↦ hS j (Finset.mem_insert_of_mem hj)) hr (norm_mul _ _)
    simpa only [Finset.prod_insert hi, Polynomial.coe_mul, Finset.card_insert_of_notMem hi,
      add_comm 1 s.card] using hstep

/-- Over a field, the polynomial `1 - c⁻¹ X` for `c ≠ 0` is nonzero, has degree `1`, and has single
root `c`. -/
private theorem one_sub_C_inv_mul_X_spec {L : Type*} [Field L] {c : L} (hc : c ≠ 0) :
    (1 - Polynomial.C c⁻¹ * Polynomial.X : Polynomial L) ≠ 0 ∧
      (1 - Polynomial.C c⁻¹ * Polynomial.X : Polynomial L).natDegree = 1 ∧
      (1 - Polynomial.C c⁻¹ * Polynomial.X : Polynomial L).roots = {c} := by
  have hfac : (1 - Polynomial.C c⁻¹ * Polynomial.X : Polynomial L) =
      Polynomial.C (-c⁻¹) * (Polynomial.X - Polynomial.C c) := by
    rw [mul_sub, ← Polynomial.C_mul, neg_mul, inv_mul_cancel₀ hc, map_neg, map_neg, map_one]
    ring
  have hC : (-c⁻¹ : L) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hC) (Polynomial.X_sub_C_ne_zero c)
  · rw [hfac, Polynomial.natDegree_C_mul hC, Polynomial.natDegree_X_sub_C]
  · rw [hfac, Polynomial.roots_C_mul _ hC, Polynomial.roots_X_sub_C]

variable [CompleteSpace K]

/-- **Convergence of the Weierstrass product of a locally finite family of zeros.** If `α : ι → K`
satisfies `‖αᵢ‖ → ∞` along `cofinite` (equivalently, only finitely many indices lie in each closed
disc), then `∏' i, (1 - αᵢ⁻¹ X)` converges unconditionally in `PowerSeries.IsEntire.subring K`. -/
theorem multipliable_polynomialHom_one_sub_inv_mul_X {ι : Type*} {α : ι → K}
    (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) :
    Multipliable fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :=
  multipliable_polynomialHom_one_sub_C_mul_X (tendsto_inv_cofinite_zero hfin)

/-- **Disc preparation of a Weierstrass product.** Let `α : ι → K` be a family of nonzero elements
with `‖αᵢ‖ → ∞` along `cofinite`, let `r > 0`, and let `S` be the finite set of indices with
`‖αᵢ‖ ≤ r`. Splitting `∏' i, (1 - αᵢ⁻¹ X)` into the finite product over `S` and the tail product
over its complement exhibits its normalised disc preparation at radius `r`. -/
theorem isDiscPreparation_tprod_polynomialHom_one_sub_inv_mul_X {ι : Type*} {α : ι → K}
    (hα : ∀ i, α i ≠ 0) (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) {r : ℝ} (hr : 0 < r)
    {S : Finset ι} (hS : ∀ i, i ∈ S ↔ ‖α i‖ ≤ r) :
    IsDiscPreparation r S.card
      ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧)
      (∏ i ∈ S, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X))
      ((∏' i : {i // i ∉ S},
        IsEntire.polynomialHom (1 - Polynomial.C (α i.1)⁻¹ * Polynomial.X) :
          IsEntire.subring K) : K⟦X⟧) := by
  classical
  set P : Polynomial K := ∏ i ∈ S, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  set f : ι → IsEntire.subring K :=
    fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  set U : IsEntire.subring K := ∏' i : {i // i ∉ S}, f i.1
  have hcompl_fin : Tendsto (fun i : {i // i ∉ S} ↦ ‖α i.1‖) cofinite atTop :=
    hfin.comp Subtype.val_injective.tendsto_cofinite
  have hcompl_inv : Tendsto (fun i : {i // i ∉ S} ↦ (α i.1)⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_cofinite_zero hcompl_fin
  -- Factor the unconditional product into the finite disc part `P` and the tail `U`.
  have hsplit : (∏' i, f i) = IsEntire.polynomialHom P * U := by
    have hs : Multipliable (f ∘ Subtype.val : ↑(S : Set ι) → IsEntire.subring K) :=
      (hasProd_fintype _).multipliable
    have hsc : Multipliable (f ∘ Subtype.val : ↑(S : Set ι)ᶜ → IsEntire.subring K) :=
      multipliable_polynomialHom_one_sub_inv_mul_X hcompl_fin
    rw [← hs.tprod_mul_tprod_compl hsc]
    congr 1
    rw [tprod_fintype, map_prod]
    convert Finset.prod_coe_sort S f
  have hU0 : constantCoeff (U : K⟦X⟧) = 1 :=
    constantCoeff_tprod_polynomialHom_one_sub_C_mul_X hcompl_inv
  have hUlt : ((U : K⟦X⟧) - 1).gaussNorm norm r < 1 := by
    refine gaussNorm_tprod_polynomialHom_one_sub_C_mul_X_sub_one_lt hcompl_inv hr.le zero_lt_one
      le_rfl fun i ↦ ?_
    have hgt : r < ‖α i.1‖ := not_le.mp fun hle ↦ i.2 ((hS i.1).mpr hle)
    rw [norm_inv, inv_mul_eq_div]
    exact (div_lt_one (hr.trans hgt)).mpr hgt
  have hPdist : IsDistinguished r S.card (P : K⟦X⟧) :=
    isDistinguished_prod_one_sub_inv_mul_X hr S fun i hi ↦ ⟨hα i, (hS i).mp hi⟩
  have hUdist : IsDistinguished r 0 (U : K⟦X⟧) :=
    (gaussNorm_sub_one_lt_one_iff hr (IsEntire.mem_subring.mp U.2 |>.isRestricted r) hU0).mp hUlt
  have hFdist : IsDistinguished r S.card ((∏' i, f i : IsEntire.subring K) : K⟦X⟧) := by
    have h := hPdist.mul hUdist hr (norm_mul _ _)
    simpa only [add_zero, hsplit, Subring.coe_mul, IsEntire.coe_polynomialHom] using h
  have hPdeg : P.natDegree = S.card := by
    rw [Polynomial.natDegree_prod _ _ fun i _ ↦ (one_sub_C_inv_mul_X_spec (hα i)).1]
    rw [Finset.sum_congr rfl fun i _ ↦ (one_sub_C_inv_mul_X_spec (hα i)).2.1]
    simp
  have hP0 : P.coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_apply, map_prod]
    exact Finset.prod_eq_one fun i _ ↦ by simp
  exact
    { isDistinguished := hFdist
      natDegree_eq := hPdeg
      coeff_zero_eq_one := hP0
      isRestricted := (IsEntire.mem_subring.mp U.2).isRestricted r
      constantCoeff_eq_one := hU0
      gaussNorm_sub_one_lt := hUlt
      eq_mul := by simp [hsplit] }

/-- **The zero multiset of a Weierstrass product.** Let `α : ι → K` be a family of nonzero elements
with `‖αᵢ‖ → ∞` along `cofinite`, and let `S` be the finite set of indices with `‖αᵢ‖ ≤ r`. In
every complete normed field extension `L` of `K`, the zero multiset of `∏' i, (1 - αᵢ⁻¹ X)` on the
closed disc of radius `r > 0` consists of the images of `αᵢ` for `i ∈ S`, counted with
multiplicity. -/
theorem zeroMultiset_tprod_polynomialHom_one_sub_inv_mul_X {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] {α : ι → K} (hα : ∀ i, α i ≠ 0)
    (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) {r : ℝ} (hr : 0 < r)
    {S : Finset ι} (hS : ∀ i, i ∈ S ↔ ‖α i‖ ≤ r) :
    ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
      IsEntire.subring K) : K⟦X⟧).zeroMultiset r L =
      S.val.map fun i ↦ algebraMap K L (α i) := by
  have hprep := isDiscPreparation_tprod_polynomialHom_one_sub_inv_mul_X hα hfin hr hS
  rw [hprep.zeroMultiset_eq_roots_map (L := L) hr, Polynomial.map_prod]
  have hfac (i : ι) :
      (1 - Polynomial.C (α i)⁻¹ * Polynomial.X).map (algebraMap K L) =
        1 - Polynomial.C (algebraMap K L (α i))⁻¹ * Polynomial.X := by
    simp
  simp_rw [hfac]
  rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ ↦
    (one_sub_C_inv_mul_X_spec ((map_ne_zero _).mpr (hα i))).1)]
  simpa [Multiset.bind_singleton] using Multiset.bind_congr fun i _ ↦
    (one_sub_C_inv_mul_X_spec ((map_ne_zero _).mpr (hα i))).2.2

/-- **Zero multiplicities of a Weierstrass product in an extension.** For a family `α : ι → K` of
nonzero elements with `‖αᵢ‖ → ∞` along `cofinite`, the multiplicity of `∏' i, (1 - αᵢ⁻¹ X)` at any
point `x` of a complete normed field extension `L` is the number of indices `i` with
`algebraMap K L (α i) = x`. -/
theorem order_taylor_map_tprod_polynomialHom_one_sub_inv_mul_X {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] {α : ι → K} (hα : ∀ i, α i ≠ 0)
    (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (x : L) :
    (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L)
      ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧))).order =
      Set.encard {i | algebraMap K L (α i) = x} := by
  classical
  set F : IsEntire.subring K :=
    ∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  have hF0 : (F : K⟦X⟧) ≠ 0 := by
    intro h0
    have h1 := constantCoeff_tprod_polynomialHom_one_sub_C_mul_X (tendsto_inv_cofinite_zero hfin)
    change constantCoeff (F : K⟦X⟧) = 1 at h1
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  set r : ℝ := ‖x‖ + 1
  have hr : 0 < r := by positivity
  set S : Finset ι := (((northcott_iff_tendsto _).2 hfin).finite_le r).toFinset
  have hS : ∀ i, i ∈ S ↔ ‖α i‖ ≤ r := fun _ ↦ Set.Finite.mem_toFinset _
  rw [((IsEntire.mem_subring.mp F.2).isRestricted r).order_taylor_eq_count_zeroMultiset hr hF0
    (by dsimp [r]; linarith), zeroMultiset_tprod_polynomialHom_one_sub_inv_mul_X hα hfin hr hS]
  have hsub : {i | algebraMap K L (α i) = x} =
      (S.filter fun i ↦ algebraMap K L (α i) = x : Set ι) := by
    ext i
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, hS, iff_and_self]
    intro hi
    have hnorm : ‖α i‖ = ‖x‖ := by rw [← hi, norm_algebraMap']
    dsimp [r]
    linarith
  rw [hsub, Set.encard_coe_eq_coe_finsetCard, Multiset.count_map]
  simp only [Finset.card_def, Finset.filter_val, eq_comm]

/-- **Zero multiplicities of a Weierstrass product.** For a family `α : ι → K` of nonzero elements
with `‖αᵢ‖ → ∞` along `cofinite`, the order of the Taylor translate of `∏' i, (1 - αᵢ⁻¹ X)` at
every `x : K` is the number of indices `i` with `α i = x`. -/
theorem order_taylor_tprod_polynomialHom_one_sub_inv_mul_X {ι : Type*} {α : ι → K}
    (hα : ∀ i, α i ≠ 0) (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (x : K) :
    (_root_.PowerSeries.taylor x
      ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧)).order =
      Set.encard {i | α i = x} := by
  simpa only [Algebra.algebraMap_self, map_id, id_eq, RingHom.id_apply] using
    order_taylor_map_tprod_polynomialHom_one_sub_inv_mul_X (L := K) hα hfin x

/-- **Zeros of a Weierstrass product in an extension.** For a family `α : ι → K` of nonzero
elements with `‖αᵢ‖ → ∞` along `cofinite`, the zeros of `∏' i, (1 - αᵢ⁻¹ X)` in any complete normed
field extension `L` are exactly the images of the `αᵢ`. -/
theorem evalAt_map_tprod_polynomialHom_one_sub_inv_mul_X_eq_zero_iff {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] {α : ι → K} (hα : ∀ i, α i ≠ 0)
    (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (x : L) :
    (_root_.PowerSeries.map (algebraMap K L)
      ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧)).evalAt x = 0 ↔
      ∃ i, algebraMap K L (α i) = x := by
  rw [← _root_.PowerSeries.constantCoeff_taylor,
    ← _root_.PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
    order_taylor_map_tprod_polynomialHom_one_sub_inv_mul_X hα hfin x,
    ne_eq, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  simp

/-- **Zeros of a Weierstrass product.** For a family `α : ι → K` of nonzero elements with
`‖αᵢ‖ → ∞` along `cofinite`, the zeros of `∏' i, (1 - αᵢ⁻¹ X)` in `K` are exactly the `αᵢ`. -/
theorem evalAt_tprod_polynomialHom_one_sub_inv_mul_X_eq_zero_iff {ι : Type*} {α : ι → K}
    (hα : ∀ i, α i ≠ 0) (hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (x : K) :
    ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
      IsEntire.subring K) : K⟦X⟧).evalAt x = 0 ↔ ∃ i, α i = x := by
  simpa only [Algebra.algebraMap_self, map_id, id_eq, RingHom.id_apply] using
    evalAt_map_tprod_polynomialHom_one_sub_inv_mul_X_eq_zero_iff (L := K) hα hfin x

/-! ### Prescribed zero multiplicities -/

/-- The fiber of `Sigma.fst : (Σ y, Fin (m y)) → α` over `x` has `encard` equal to `m x`. -/
private theorem encard_sigma_fst_eq {α : Type*} (m : α → ℕ) (x : α) :
    Set.encard {p : Σ y : α, Fin (m y) | p.1 = x} = m x := by
  have heq : {p : Σ y : α, Fin (m y) | p.1 = x} =
      Set.range (fun k : Fin (m x) ↦ (⟨x, k⟩ : Σ y : α, Fin (m y))) := by
    ext ⟨y, k⟩
    constructor
    · rintro (rfl : y = x)
      exact ⟨k, rfl⟩
    · rintro ⟨_, h⟩
      exact (congrArg Sigma.fst h).symm
  have hinj : Function.Injective (fun k : Fin (m x) ↦ (⟨x, k⟩ : Σ y : α, Fin (m y))) :=
    fun _ _ h ↦ by simpa using h
  rw [heq, hinj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- **Existence of an entire series with prescribed zero divisor (normalised at `0`).** Given
`m : K → ℕ` with `m 0 = 0` whose support meets every closed disc in a finite set, there exists an
entire series over `K` with constant coefficient `1` whose Taylor order at each `x : K` is
`m x`. -/
theorem exists_isEntire_constantCoeff_eq_one_order_taylor_eq {m : K → ℕ}
    (hm : ∀ r : ℝ, {x | ‖x‖ ≤ r ∧ m x ≠ 0}.Finite) (hm0 : m 0 = 0) :
    ∃ f : K⟦X⟧, f.IsEntire ∧ constantCoeff f = 1 ∧
      ∀ x : K, (_root_.PowerSeries.taylor x f).order = m x := by
  let ι := Σ x : K, Fin (m x)
  have hα : ∀ p : ι, p.1 ≠ 0 := by
    rintro ⟨x, hx⟩ rfl
    rw [hm0] at hx
    exact Fin.elim0 hx
  have hfin : Tendsto (fun p : ι ↦ ‖p.1‖) cofinite atTop := by
    rw [← northcott_iff_tendsto, northcott_iff]
    intro r
    refine Set.Finite.of_finite_fibers Sigma.fst ?_ fun x _ ↦ ?_
    · refine (hm r).subset ?_
      rintro x ⟨⟨y, hy⟩, hle, rfl⟩
      exact ⟨hle, Nat.ne_of_gt (Fin.pos hy)⟩
    · refine ((Set.finite_univ (α := Fin (m x))).image (fun k ↦ (⟨x, k⟩ : ι))).subset ?_
      rintro ⟨y, k⟩ ⟨_, rfl⟩
      exact ⟨k, trivial, rfl⟩
  set F : IsEntire.subring K :=
    ∏' p : ι, IsEntire.polynomialHom (1 - Polynomial.C p.1⁻¹ * Polynomial.X)
  refine ⟨F, IsEntire.mem_subring.mp F.2,
    constantCoeff_tprod_polynomialHom_one_sub_C_mul_X (tendsto_inv_cofinite_zero hfin), fun x ↦ ?_⟩
  rw [order_taylor_tprod_polynomialHom_one_sub_inv_mul_X hα hfin x, encard_sigma_fst_eq]

/-- **Existence of an entire series with arbitrary locally finite zero divisor.** Given `m : K → ℕ`
whose support meets every closed disc in a finite set, there exists a nonzero entire series over `K`
whose Taylor order at every `x : K` is `m x`. -/
theorem exists_isEntire_order_taylor_eq {m : K → ℕ}
    (hm : ∀ r : ℝ, {x | ‖x‖ ≤ r ∧ m x ≠ 0}.Finite) :
    ∃ f : K⟦X⟧, f.IsEntire ∧ f ≠ 0 ∧ ∀ x : K, (_root_.PowerSeries.taylor x f).order = m x := by
  classical
  let m' : K → ℕ := Function.update m 0 0
  have hm' : ∀ r : ℝ, {x | ‖x‖ ≤ r ∧ m' x ≠ 0}.Finite := fun r ↦
    (hm r).subset fun x ⟨hx, hne⟩ ↦ ⟨hx, by
      by_cases hx0 : x = 0
      · simp [m', hx0] at hne
      · simpa [m', hx0] using hne⟩
  obtain ⟨g, hg, hg0, hord⟩ :=
    exists_isEntire_constantCoeff_eq_one_order_taylor_eq hm' (by simp [m'])
  refine ⟨X ^ m 0 * g, (isEntire_X.pow _).mul hg, mul_ne_zero (pow_ne_zero _ X_ne_zero) ?_,
    fun x ↦ ?_⟩
  · rintro rfl
    simp at hg0
  · rw [(isEntire_X.pow _).taylor_mul hg x, order_mul, hord x]
    by_cases hx : x = 0
    · subst hx
      simp [m']
    · have hX : (_root_.PowerSeries.taylor x (X ^ m 0 : K⟦X⟧)).order =
          ((Polynomial.X ^ m 0 : Polynomial K).rootMultiplicity x : ℕ∞) := by
        have hcoe : (X ^ m 0 : K⟦X⟧) = ((Polynomial.X ^ m 0 : Polynomial K) : K⟦X⟧) := by
          simp
        rw [hcoe]
        exact isGoodZero_iff_order_taylor_eq.mp
          (isGoodZero_coe_iff_of_field.mpr ⟨pow_ne_zero _ Polynomial.X_ne_zero, rfl⟩)
      have hX0 : (Polynomial.X ^ m 0 : Polynomial K).rootMultiplicity x = 0 :=
        Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, hx])
      simp [m', hx, hX, hX0]

/-- **Unique normalised entire series with prescribed zeros.** Over an algebraically closed complete
ultrametric normed field, there is a unique entire series with constant coefficient `1` and a given
locally finite multiplicity function `m : K → ℕ` with `m 0 = 0`. -/
theorem existsUnique_isEntire_constantCoeff_eq_one_order_taylor_eq [IsAlgClosed K] {m : K → ℕ}
    (hm : ∀ r : ℝ, {x | ‖x‖ ≤ r ∧ m x ≠ 0}.Finite) (hm0 : m 0 = 0) :
    ∃! f : K⟦X⟧, f.IsEntire ∧ constantCoeff f = 1 ∧
      ∀ x : K, (_root_.PowerSeries.taylor x f).order = m x := by
  obtain ⟨f, hf, hf0, hord⟩ := exists_isEntire_constantCoeff_eq_one_order_taylor_eq hm hm0
  refine ⟨f, ⟨hf, hf0, hord⟩, fun g ⟨hg, hg0, hord'⟩ ↦
    eq_of_order_taylor_eq hg hf hg0 hf0 fun x ↦ (hord' x).trans (hord x).symm⟩

/-- **Entire series with the same zero divisor agree up to a nonzero constant.** Over an
algebraically closed complete ultrametric normed field, two entire series with the same Taylor
order at every point differ by a nonzero constant factor. -/
theorem exists_C_mul_eq_of_order_taylor_eq [IsAlgClosed K] {f g : K⟦X⟧} (hf : f.IsEntire)
    (hg : g.IsEntire)
    (h : ∀ x : K, (_root_.PowerSeries.taylor x f).order = (_root_.PowerSeries.taylor x g).order) :
    ∃ c : K, c ≠ 0 ∧ f = C c * g := by
  by_cases hf0 : f = 0
  · subst hf0
    have hg0 : g = 0 := by
      have h0 := h 0
      simpa [taylor_zero, order_eq_top] using h0.symm
    exact ⟨1, one_ne_zero, by simp [hg0]⟩
  obtain ⟨n, hnf⟩ := hf.exists_isGoodZero hf0 0
  have hng : g.IsGoodZero 0 n :=
    isGoodZero_iff_order_taylor_eq.mpr ((h 0).symm.trans (isGoodZero_iff_order_taylor_eq.mp hnf))
  obtain ⟨f₁, hf₁, hff₁, hf₁0⟩ := hf.isGoodZero_iff.mp hnf
  obtain ⟨g₁, hg₁, hgg₁, hg₁0⟩ := hg.isGoodZero_iff.mp hng
  rw [map_zero, sub_zero] at hff₁ hgg₁
  simp only [evalAt_at_zero, Algebra.algebraMap_self, RingHom.id_apply,
    isUnit_iff_ne_zero] at hf₁0 hg₁0
  -- Normalise `f₁` and `g₁` to constant coefficient `1`; their Taylor orders agree everywhere.
  set f₂ := C (constantCoeff f₁)⁻¹ * f₁
  set g₂ := C (constantCoeff g₁)⁻¹ * g₁
  have hf₂ : f₂.IsEntire := (isEntire_C _).mul hf₁
  have hg₂ : g₂.IsEntire := (isEntire_C _).mul hg₁
  have hord2 (x : K) : (_root_.PowerSeries.taylor x f₂).order =
      (_root_.PowerSeries.taylor x g₂).order := by
    have hX : (_root_.PowerSeries.taylor x (X ^ n : K⟦X⟧)).order ≠ ⊤ := by
      rw [show (X ^ n : K⟦X⟧) = ((Polynomial.X ^ n : Polynomial K) : K⟦X⟧) by simp,
        isGoodZero_iff_order_taylor_eq.mp
          (isGoodZero_coe_iff_of_field.mpr ⟨pow_ne_zero _ Polynomial.X_ne_zero, rfl⟩)]
      exact ENat.natCast_ne_top _
    have hconst (c : K) (hc : c ≠ 0) (u : K⟦X⟧) (hu : u.IsEntire) :
        (_root_.PowerSeries.taylor x (C c * u)).order = (_root_.PowerSeries.taylor x u).order := by
      rw [← smul_eq_C_mul, hu.taylor_smul, smul_eq_C_mul, order_mul]
      have hC0 : (C c : K⟦X⟧).order = 0 :=
        not_ne_iff.mp (mt order_ne_zero_iff_constCoeff_eq_zero.mp (by simp [hc]))
      rw [hC0, zero_add]
    have hfg1 : (_root_.PowerSeries.taylor x f₁).order =
        (_root_.PowerSeries.taylor x g₁).order := by
      have hx := h x
      rw [hff₁, hgg₁, (isEntire_X.pow n).taylor_mul hf₁, (isEntire_X.pow n).taylor_mul hg₁,
        order_mul, order_mul] at hx
      exact WithTop.add_left_cancel hX hx
    rw [hconst _ (inv_ne_zero hf₁0) f₁ hf₁, hconst _ (inv_ne_zero hg₁0) g₁ hg₁, hfg1]
  have heq : f₂ = g₂ :=
    eq_of_order_taylor_eq hf₂ hg₂ (by simp [f₂, hf₁0]) (by simp [g₂, hg₁0]) hord2
  refine ⟨constantCoeff f₁ * (constantCoeff g₁)⁻¹, mul_ne_zero hf₁0 (inv_ne_zero hg₁0), ?_⟩
  have hf₁eq : f₁ = C (constantCoeff f₁) * f₂ := by
    dsimp [f₂]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf₁0, map_one, one_mul]
  calc f = X ^ n * (C (constantCoeff f₁) * f₂) := by rw [hff₁, ← hf₁eq]
    _ = C (constantCoeff f₁ * (constantCoeff g₁)⁻¹) * g := by
        rw [heq, hgg₁, map_mul]
        dsimp [g₂]
        ring

/-! ### Unconditional factorisation of entire series -/

/-- **Norms of zeros of a nonzero entire series tend to infinity.** If `f` is a nonzero entire
series over `K` and `α : ι → L` indexes its zeros in a complete normed field extension `L` with
multiplicity, then `‖αᵢ‖ → ∞` along `cofinite`. In particular, for any enumeration `α : ℕ → L` of
infinitely many zeros with multiplicity, `‖α n‖ → ∞` as `n → ∞`. -/
theorem tendsto_norm_cofinite_of_order_taylor_map_eq {L ι : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] {f : K⟦X⟧} (hf : f.IsEntire) (hf0 : f ≠ 0)
    {α : ι → L}
    (hα : ∀ x : L,
      (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
        Set.encard {i | α i = x}) :
    Tendsto (fun i ↦ ‖α i‖) cofinite atTop := by
  classical
  rw [← northcott_iff_tendsto, northcott_iff]
  intro r
  set R : ℝ := max r 1
  have hR : 0 < R := by positivity
  refine Set.Finite.of_finite_fibers α ?_ fun x hx ↦ ?_
  · refine (Multiset.finite_toSet (f.zeroMultiset R L)).subset ?_
    rintro x ⟨i, hi, rfl⟩
    have hle : ‖α i‖ ≤ R := hi.trans (le_max_left r 1)
    have hpos : 0 < Set.encard {j | α j = α i} :=
      Set.encard_pos.mpr ⟨i, rfl⟩
    have hcount :=
      ((hf.isRestricted R).order_taylor_eq_count_zeroMultiset (L := L) hR hf0 hle).symm.trans
        (hα (α i))
    rw [← hcount] at hpos
    exact Multiset.count_pos.mp (Nat.cast_pos.mp hpos)
  · obtain ⟨i, hi, rfl⟩ := hx
    have hle : ‖α i‖ ≤ R := hi.trans (le_max_left r 1)
    have hfin : Set.encard {j | α j = α i} < ⊤ := by
      rw [← hα (α i), (hf.isRestricted R).order_taylor_eq_count_zeroMultiset (L := L) hR hf0 hle]
      exact ENat.natCast_lt_top _
    exact (Set.encard_lt_top_iff.mp hfin).subset fun j hj ↦ hj.2

/-- **Unconditional product expansion over any indexing of the zeros.** Let `f` be an entire series
with constant coefficient `1` over an algebraically closed complete ultrametric normed field `K`.
For any family `α : ι → K` hitting each `x : K` with cardinality `(PowerSeries.taylor x f).order`,
the product `∏' i, (1 - αᵢ⁻¹ X)` converges unconditionally to `f` in
`PowerSeries.IsEntire.subring K` (and hence in every nonnegative-radius Gauss norm), independently
of any enumeration. -/
theorem hasProd_polynomialHom_one_sub_inv_mul_X_of_order_taylor_eq [IsAlgClosed K] {f : K⟦X⟧}
    (hf : f.IsEntire) (h0 : constantCoeff f = 1) {ι : Type*} {α : ι → K}
    (hα : ∀ x : K, (_root_.PowerSeries.taylor x f).order = Set.encard {i | α i = x}) :
    HasProd (fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X))
      ⟨f, IsEntire.mem_subring.mpr hf⟩ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  have hne : ∀ i, α i ≠ 0 := by
    intro i hi
    have hpos : 0 < Set.encard {j | α j = 0} := Set.encard_pos.mpr ⟨i, hi⟩
    rw [← hα 0, taylor_zero] at hpos
    have hord0 : f.order = 0 :=
      not_ne_iff.mp (mt order_ne_zero_iff_constCoeff_eq_zero.mp (by simp [h0]))
    simp [hord0] at hpos
  have hfin : Tendsto (fun i ↦ ‖α i‖) cofinite atTop :=
    tendsto_norm_cofinite_of_order_taylor_map_eq (L := K) hf hf0 (by simpa using hα)
  have hm := multipliable_polynomialHom_one_sub_inv_mul_X hfin
  set G : IsEntire.subring K :=
    ∏' i, IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  have hGeq : G = ⟨f, IsEntire.mem_subring.mpr hf⟩ := Subtype.ext <|
    eq_of_order_taylor_eq (IsEntire.mem_subring.mp G.2) hf
      (constantCoeff_tprod_polynomialHom_one_sub_C_mul_X (tendsto_inv_cofinite_zero hfin)) h0
      fun x ↦ (order_taylor_tprod_polynomialHom_one_sub_inv_mul_X hne hfin x).trans (hα x).symm
  rw [← hGeq]
  exact hm.hasProd

/-- **Canonical unconditional product expansion of an entire series.** Over an algebraically closed
complete ultrametric normed field `K`, an entire series `f` with constant coefficient `1` is the
unconditional product `∏' p, (1 - p.1⁻¹ X)` over its zeros counted with multiplicity. -/
theorem hasProd_polynomialHom_one_sub_inv_mul_X [IsAlgClosed K] {f : K⟦X⟧} (hf : f.IsEntire)
    (h0 : constantCoeff f = 1) :
    HasProd (fun p : Σ x : K, Fin (_root_.PowerSeries.taylor x f).order.toNat ↦
      IsEntire.polynomialHom (1 - Polynomial.C p.1⁻¹ * Polynomial.X))
      ⟨f, IsEntire.mem_subring.mpr hf⟩ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  refine hasProd_polynomialHom_one_sub_inv_mul_X_of_order_taylor_eq hf h0 fun x ↦ ?_
  obtain ⟨n, hn⟩ := hf.exists_isGoodZero hf0 x
  have hord : (_root_.PowerSeries.taylor x f).order = n := isGoodZero_iff_order_taylor_eq.mp hn
  rw [encard_sigma_fst_eq, hord, ENat.toNat_natCast]

/-- **Pointwise unconditional product expansion of an entire series.** Over an algebraically closed
complete ultrametric normed field `K`, for any entire series `f` with constant coefficient `1`, any
indexing `α : ι → K` of its zeros with multiplicity, and any element `b` of a complete normed
commutative `K`-algebra, `f(b) = ∏' i, (1 - αᵢ⁻¹ • b)` unconditionally. -/
theorem hasProd_evalAt_one_sub_inv_smul [IsAlgClosed K] {A ι : Type*} [NormedCommRing A]
    [Algebra K A] [IsBoundedSMul K A] [CompleteSpace A] {f : K⟦X⟧} (hf : f.IsEntire)
    (h0 : constantCoeff f = 1) {α : ι → K}
    (hα : ∀ x : K, (_root_.PowerSeries.taylor x f).order = Set.encard {i | α i = x}) (b : A) :
    HasProd (fun i ↦ 1 - (α i)⁻¹ • b) (f.evalAt b) := by
  have hprod := IsEntire.hasProd_evalAt
    (hasProd_polynomialHom_one_sub_inv_mul_X_of_order_taylor_eq hf h0 hα) b
  refine hprod.congr_fun fun i ↦ ?_
  rw [IsEntire.coe_polynomialHom, evalAt_coe, map_sub, map_one, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.smul_def]

end Field

end PowerSeries.IsEntire
