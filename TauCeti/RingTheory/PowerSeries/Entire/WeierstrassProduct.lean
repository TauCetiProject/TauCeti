/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.InfiniteProd
public import TauCeti.RingTheory.PowerSeries.Entire.Factorization
import Mathlib.Order.Northcott
import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# The Weierstrass entire product theorem

Let `K` be a complete ultrametric normed field. Because the ring `PowerSeries.IsEntire.subring K`
of entire power series carries a complete Hausdorff nonarchimedean topology induced by the Gauss
norms at all positive radii, any family of entire series tending to `1` along the cofinite filter
is unconditionally multipliable in `PowerSeries.IsEntire.subring K`, even when its factors are not
units there.

For any family `a : ι → K` with `‖a i‖ → ∞` along the cofinite filter, the linear polynomial
factors `1 - (a i)⁻¹ X` satisfy `‖(1 - (a i)⁻¹ X) - 1‖_r = ‖a i‖⁻¹ r → 0` at every positive radius
`r`. Their unconditional infinite product

```text
∏' i, (1 - (a i)⁻¹ X)
```

therefore converges in `PowerSeries.IsEntire.subring K`, that is, in every positive-radius Gauss
norm and independently of any ordering of `ι`. When every `a i` is nonzero, splitting this product
at any radius `r > 0` into the finite subproduct `P_r` over `‖a i‖ ≤ r` and the complementary
infinite product `U_r` over `‖a i‖ > r` exhibits `W = P_r * U_r` directly as the normalised disc
preparation of `W` at `r`, without assuming `K` to be algebraically closed. In any complete normed
field extension `L` of `K`, the zero multiset of `W` on the closed disc of radius `r` is the image
of `{i | ‖a i‖ ≤ r}`, and the Taylor multiplicity of `W` at every `y ∈ L` is the cardinality
`{i | algebraMap K L (a i) = y}.encard`; in particular `W` has no zeros in `L` outside the images
of the prescribed points `a i`.

Conversely, for any nonzero entire series `f` over `K` and any family `a : ι → L` of points in a
complete normed field extension `L` repeated at most up to the Taylor multiplicity of `f`, only
finitely many indices lie in each closed disc, so `‖a i‖ → ∞` cofinitely. Over an algebraically
closed `K`, combining both directions with the uniqueness theorem
`PowerSeries.IsEntire.eq_of_order_taylor_eq` upgrades the disc-limit factorisation of
`TauCeti.RingTheory.PowerSeries.Entire.Factorization` to an unconditional `HasProd` expansion over
any indexing of the zeros of `f` with multiplicity, and factors every nonzero entire series as
`C c * X ^ m` times the unconditional Weierstrass product over its nonzero zeros.

## Main results

* `TauCeti.PowerSeries.IsEntire.multipliable_of_tendsto_cofinite_one`: unconditional convergence of
  infinite products in `PowerSeries.IsEntire.subring R` over a complete ultrametric normed
  commutative ring.
* `TauCeti.PowerSeries.IsEntire.multipliable_polynomialHom_one_sub_C_inv_mul_X`: when
  `‖a i‖ → ∞` cofinitely, `i ↦ 1 - (a i)⁻¹ X` is unconditionally multipliable in
  `PowerSeries.IsEntire.subring K`.
* `TauCeti.PowerSeries.IsEntire.exists_isEntire_isDiscPreparation_of_hasProd`: splitting the
  Weierstrass product at `r > 0` gives the normalised disc preparation with entire unit cofactor.
* `TauCeti.PowerSeries.IsEntire.zeroMultiset_of_hasProd`,
  `TauCeti.PowerSeries.IsEntire.order_taylor_map_of_hasProd` and
  `TauCeti.PowerSeries.IsEntire.evalAt_map_eq_zero_iff_of_hasProd`: the zero multisets, Taylor
  multiplicities and zero locus of an entire Weierstrass product in any complete normed field
  extension.
* `PowerSeries.IsEntire.tendsto_norm_cofinite_atTop_of_encard_le_order_taylor`: any family of zeros
  of a nonzero entire series repeated at most up to multiplicity has norms tending to infinity.
* `PowerSeries.IsEntire.hasProd_polynomialHom_of_order_taylor_eq`,
  `PowerSeries.IsEntire.hasProd_polynomialHom_zeros` and
  `PowerSeries.IsEntire.eq_C_mul_X_pow_mul_tprod_zeros`: the unconditional Weierstrass product
  theorem over an algebraically closed complete ultrametric field.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §4.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §4.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.PowerSeries

open _root_.PowerSeries

/-- At a nonnegative radius `r`, the Gauss norm of `(1 - c X) - 1 = -c X` is `‖c‖ * r`. -/
theorem gaussNorm_one_sub_C_mul_X_sub_one {R : Type*} [NormedCommRing R] (c : R) {r : ℝ}
    (hr : 0 ≤ r) :
    ((1 - C c * X : R⟦X⟧) - 1).gaussNorm norm r = ‖c‖ * r := by
  have heq : (1 - C c * X : R⟦X⟧) - 1 = monomial 1 (-c) := by
    rw [sub_sub_cancel_left]
    ext n
    by_cases hn : n = 1 <;> simp [hn, coeff_monomial, coeff_X]
  have hnorm : (monomial 1 (-c) : R⟦X⟧).gaussNorm norm r = ‖-c‖ * r ^ 1 :=
    _root_.PowerSeries.gaussNorm_monomial (v := normRingSeminorm R) (r := -c) hr 1
  rw [heq, hnorm, norm_neg, pow_one]

namespace IsEntire

local instance radius_pos' (r : Set.Ioi (0 : ℝ)) : Fact (0 < (r : ℝ)) := ⟨r.2⟩

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Restriction to the closed disc of a positive radius preserves convergent infinite products of
entire series. -/
theorem hasProd_restrict {ι : Type*} {f : ι → IsEntire.subring R} {g : IsEntire.subring R}
    (hf : HasProd f g) (r : Set.Ioi (0 : ℝ)) :
    HasProd (fun i ↦ restrict r (f i)) (restrict r g) := by
  simpa only [Function.comp_def] using hf.map (restrict r) (uniformContinuous_restrict r).continuous

/-- Evaluation at a point of a complete normed commutative algebra preserves convergent infinite
products of entire series. -/
theorem hasProd_evalAt {ι A : Type*} [NormedCommRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] {f : ι → IsEntire.subring R} {g : IsEntire.subring R}
    (hf : HasProd f g) (b : A) :
    HasProd (fun i ↦ (f i : R⟦X⟧).evalAt b) ((g : R⟦X⟧).evalAt b) := by
  simpa only [Function.comp_def, IsEntire.evalAtHom_apply] using
    hf.map (IsEntire.evalAtHom R b) (continuous_evalAtHom b)

/-- If every factor of a convergent infinite product of entire series has constant coefficient `1`,
then so does the product. -/
theorem constantCoeff_eq_one_of_hasProd {ι : Type*} {f : ι → IsEntire.subring R}
    {g : IsEntire.subring R} (hf : HasProd f g)
    (h : ∀ i, constantCoeff (f i : R⟦X⟧) = 1) :
    constantCoeff (g : R⟦X⟧) = 1 := by
  let φ : IsEntire.subring R →+* R := constantCoeff.comp (IsEntire.subring R).subtype
  have hc : Continuous φ :=
    (uniformContinuous_coeff (R := R) 0).continuous.congr fun q ↦ by simp [φ]
  have h1 : HasProd (fun _ : ι ↦ (1 : R)) 1 := hasProd_one
  exact (hf.map φ hc).unique
    (by simpa only [Function.comp_def, φ, RingHom.comp_apply, Subring.coe_subtype, h] using h1)

/-- If every factor of a convergent infinite product of entire series lies strictly within `ε ≤ 1`
of `1` in the Gauss norm at `r > 0`, then so does the infinite product. -/
theorem gaussNorm_sub_one_lt_of_hasProd {ι : Type*} {f : ι → IsEntire.subring R}
    {g : IsEntire.subring R} (hf : HasProd f g) {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (h : ∀ i, ((f i : R⟦X⟧) - 1).gaussNorm norm r < ε) :
    ((g : R⟦X⟧) - 1).gaussNorm norm r < ε := by
  have : Fact (0 < r) := ⟨hr⟩
  have hlt := (hasProd_restrict hf ⟨r, hr⟩).norm_sub_one_lt hε0 hε fun i ↦ by
    rw [TauCeti.PowerSeries.norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
      OneMemClass.coe_one]
    exact h i
  rwa [TauCeti.PowerSeries.norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
    OneMemClass.coe_one] at hlt

variable [CompleteSpace R]

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, if `f`
tends to `0` along the cofinite filter, then the family of finite products `s ↦ ∏ i ∈ s, f i` is
unconditionally summable. -/
theorem summable_prod_of_tendsto_cofinite_zero {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Summable fun s : Finset ι ↦ ∏ i ∈ s, f i := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_iff.mpr fun r ↦ ?_)
  have hr : Tendsto (fun i ↦ restrict r (f i)) cofinite (𝓝 0) := by
    simpa only [map_zero] using tendsto_iff.mp hf r
  simpa only [map_zero, map_prod] using hr.finset_prod_of_cofinite

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, if `f`
tends to `0` along the cofinite filter, then `i ↦ 1 + f i` is unconditionally multipliable. -/
theorem multipliable_one_add_of_tendsto_cofinite_zero {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 0)) :
    Multipliable fun i ↦ 1 + f i :=
  multipliable_one_add_of_summable_prod (summable_prod_of_tendsto_cofinite_zero hf)

/-- In `PowerSeries.IsEntire.subring R` over a complete ultrametric normed commutative ring, any
family tending to `1` along the cofinite filter is unconditionally multipliable, even when its
factors are not units of `PowerSeries.IsEntire.subring R`. -/
theorem multipliable_of_tendsto_cofinite_one {ι : Type*} {f : ι → IsEntire.subring R}
    (hf : Tendsto f cofinite (𝓝 1)) :
    Multipliable f := by
  have h0 : Tendsto (fun i ↦ f i - 1) cofinite (𝓝 0) := by
    simpa only [sub_self] using hf.sub_const 1
  simpa only [add_sub_cancel] using multipliable_one_add_of_tendsto_cofinite_zero h0

end NormedCommRing

section ConverseWeierstrass

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- When `‖a i‖ → ∞` along the cofinite filter, the linear entire factors `1 - (a i)⁻¹ X` tend to
`1` in the topology of entire series. -/
theorem tendsto_cofinite_polynomialHom_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) :
    Tendsto (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) cofinite (𝓝 1) := by
  rw [tendsto_iff]
  intro r
  rw [map_one]
  suffices Tendsto (fun i ↦ restrict r (IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) - 1) cofinite (𝓝 0) by
    simpa only [sub_add_cancel, zero_add] using
      this.add_const (1 : IsRestricted.subring (R := K) (r : ℝ))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun i ↦ ‖a i‖⁻¹ * (r : ℝ)) cofinite (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (tendsto_inv_atTop_zero.comp ha).mul_const (r : ℝ)
  refine h0.congr fun i ↦ ?_
  simp only [norm_eq_gaussNorm, AddSubgroupClass.coe_sub, coe_restrict,
    OneMemClass.coe_one, IsEntire.coe_polynomialHom, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
  rw [gaussNorm_one_sub_C_mul_X_sub_one _ r.2.le, norm_inv]

/-- A finite product of factors `1 - (a i)⁻¹ X` with `0 < ‖a i‖ ≤ r` is distinguished of degree
`s.card` at `r`, has degree `s.card` and constant coefficient `1`. -/
private theorem prod_one_sub_C_inv_mul_X_spec {ι : Type*} {s : Finset ι} {a : ι → K} {r : ℝ}
    (hr : 0 < r) (ha0 : ∀ i ∈ s, a i ≠ 0) (har : ∀ i ∈ s, ‖a i‖ ≤ r) :
    IsDistinguished r s.card
      ((∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) : Polynomial K) : K⟦X⟧) ∧
      (∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)).natDegree = s.card ∧
      (∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)).coeff 0 = 1 := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨?_, Polynomial.natDegree_one, AddMonoidAlgebra.coeff_one_zero⟩
    simpa only [Finset.card_empty, Finset.prod_empty, Polynomial.coe_one, monomial_zero_eq_C_apply,
      map_one] using isDistinguished_monomial (R := K) hr one_ne_zero 0
  | insert i t hit ih =>
    obtain ⟨hdist, hdeg, h0⟩ := ih (fun j hj ↦ ha0 j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ har j (Finset.mem_insert_of_mem hj))
    have hi0 : a i ≠ 0 := ha0 i (Finset.mem_insert_self i t)
    have hir : ‖a i‖ ≤ r := har i (Finset.mem_insert_self i t)
    have hfac : (1 - C (a i)⁻¹ * X : K⟦X⟧) = monomial 0 (-(a i)⁻¹) * (X - C (a i)) := by
      rw [monomial_zero_eq_C_apply, mul_sub, map_neg, neg_mul, neg_mul, ← map_mul,
        inv_mul_cancel₀ hi0, map_one, sub_neg_eq_add, sub_eq_neg_add]
    have hlin_dist : IsDistinguished r 1 (1 - C (a i)⁻¹ * X : K⟦X⟧) := by
      rw [hfac]
      simpa only [zero_add] using
        (isDistinguished_monomial hr (neg_ne_zero.mpr (inv_ne_zero hi0)) 0).mul
          (isDistinguished_X_sub_C hr hir) hr (norm_mul _ _)
    have hlin_deg : (1 - Polynomial.C (a i)⁻¹ * Polynomial.X).natDegree = 1 := by
      rw [sub_eq_add_neg, ← Polynomial.C_1, ← neg_mul, ← Polynomial.C_neg]
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
      · exact Polynomial.natDegree_C_mul_X _ (neg_ne_zero.mpr (inv_ne_zero hi0))
      · rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul_X _
          (neg_ne_zero.mpr (inv_ne_zero hi0))]
        exact zero_lt_one
    have hlin_ne : (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hlin_deg
      exact zero_ne_one hlin_deg
    have ht_ne : (∏ j ∈ t, (1 - Polynomial.C (a j)⁻¹ * Polynomial.X)) ≠ 0 := by
      intro h
      rw [h, Polynomial.coeff_zero] at h0
      exact zero_ne_one h0
    rw [Finset.prod_insert hit, Finset.card_insert_of_notMem hit]
    refine ⟨?_, ?_, ?_⟩
    · rw [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_X, add_comm t.card 1]
      exact hlin_dist.mul hdist hr (norm_mul _ _)
    · rw [Polynomial.natDegree_mul hlin_ne ht_ne, hlin_deg, hdeg, add_comm]
    · rw [Polynomial.mul_coeff_zero, h0, mul_one, Polynomial.coeff_sub,
        AddMonoidAlgebra.coeff_one_zero, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
        mul_zero, sub_zero]

/-- The constant coefficient of a convergent Weierstrass product `∏ (1 - (a i)⁻¹ X)` is `1`. -/
theorem constantCoeff_of_hasProd_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
    {W : IsEntire.subring K}
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W) :
    constantCoeff (W : K⟦X⟧) = 1 :=
  constantCoeff_eq_one_of_hasProd hW fun _ ↦ by simp

/-- A convergent Weierstrass product `∏ (1 - (a i)⁻¹ X)` is nonzero as a formal power series. -/
theorem ne_zero_of_hasProd_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
    {W : IsEntire.subring K}
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W) :
    (W : K⟦X⟧) ≠ 0 := by
  intro h0
  have h1 := constantCoeff_of_hasProd_one_sub_C_inv_mul_X hW
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

variable [CompleteSpace K]

/-- **Convergence of entire Weierstrass products.** Over a complete ultrametric normed field `K`,
if `‖a i‖ → ∞` along the cofinite filter, then the family of linear polynomials `1 - (a i)⁻¹ X`
is unconditionally multipliable in `PowerSeries.IsEntire.subring K`. -/
theorem multipliable_polynomialHom_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) :
    Multipliable fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :=
  multipliable_of_tendsto_cofinite_one (tendsto_cofinite_polynomialHom_one_sub_C_inv_mul_X ha)

/-- **Normalised disc preparation of an entire Weierstrass product.** Let `a : ι → K` be a family of
nonzero elements with `‖a i‖ → ∞` cofinitely, and let `W` be the product in
`PowerSeries.IsEntire.subring K` of the factors `1 - (a i)⁻¹ X`. At any radius `r > 0`, if `s` is
the finite set of indices with `‖a i‖ ≤ r`, then splitting `W` at `s` gives the normalised disc
preparation `W = P_s * U` at `r` with `P_s = ∏ i ∈ s, (1 - (a i)⁻¹ X)` and an entire unit cofactor
`U`. No algebraic-closure hypothesis on `K` is required. -/
theorem exists_isEntire_isDiscPreparation_of_hasProd {ι : Type*} {a : ι → K}
    {W : IsEntire.subring K} (ha0 : ∀ i, a i ≠ 0)
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    {r : ℝ} (hr : 0 < r) {s : Finset ι} (hs : ∀ i, ‖a i‖ ≤ r ↔ i ∈ s) :
    ∃ U : K⟦X⟧, U.IsEntire ∧ IsDiscPreparation r s.card (W : K⟦X⟧)
      (∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) U := by
  let factor : ι → IsEntire.subring K :=
    fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)
  have ha_compl : Tendsto (fun x : ↑(s : Set ι)ᶜ ↦ ‖a x.1‖) cofinite atTop :=
    ha.comp Subtype.val_injective.tendsto_cofinite
  have hm_compl : Multipliable (factor ∘ (↑) : ↑(s : Set ι)ᶜ → IsEntire.subring K) :=
    multipliable_polynomialHom_one_sub_C_inv_mul_X ha_compl
  let U₀ : IsEntire.subring K := ∏' x : ↑(s : Set ι)ᶜ, factor x.1
  have hU₀ : (U₀ : K⟦X⟧).IsEntire := IsEntire.mem_subring.mp U₀.2
  have hsplit : W = (∏ i ∈ s, factor i) * U₀ :=
    hW.unique ((s.hasProd factor).mul_compl hm_compl.hasProd)
  have hU_const : constantCoeff (U₀ : K⟦X⟧) = 1 :=
    constantCoeff_eq_one_of_hasProd hm_compl.hasProd fun _ ↦ by simp [factor]
  have hU_lt : ((U₀ : K⟦X⟧) - 1).gaussNorm norm r < 1 := by
    refine gaussNorm_sub_one_lt_of_hasProd hm_compl.hasProd hr zero_lt_one le_rfl fun x ↦ ?_
    have hx : r < ‖a x.1‖ := lt_of_not_ge fun hle ↦ x.2 ((hs x.1).mp hle)
    simp only [Function.comp_apply, factor, IsEntire.coe_polynomialHom, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
    rw [gaussNorm_one_sub_C_mul_X_sub_one _ hr.le, norm_inv, inv_mul_eq_div]
    exact (div_lt_one (hr.trans hx)).mpr hx
  obtain ⟨hP_dist, hP_deg, hP_zero⟩ := prod_one_sub_C_inv_mul_X_spec hr
    (fun i _ ↦ ha0 i) (fun i hi ↦ (hs i).mpr hi)
  have hU_dist : IsDistinguished r 0 (U₀ : K⟦X⟧) :=
    (gaussNorm_sub_one_lt_one_iff hr (hU₀.isRestricted r) hU_const).mp hU_lt
  have hmul : (W : K⟦X⟧) =
      ((∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) : Polynomial K) : K⟦X⟧) * U₀ := by
    rw [hsplit, Subring.coe_mul, ← map_prod IsEntire.polynomialHom, IsEntire.coe_polynomialHom]
  refine ⟨U₀, hU₀,
    { isDistinguished := by
        rw [hmul, ← Nat.add_zero s.card]
        exact hP_dist.mul hU_dist hr (norm_mul _ _)
      natDegree_eq := hP_deg
      coeff_zero_eq_one := hP_zero
      isRestricted := hU₀.isRestricted r
      constantCoeff_eq_one := hU_const
      gaussNorm_sub_one_lt := hU_lt
      eq_mul := hmul }⟩

/-- The multiset of roots of a finite product `∏ i ∈ s, (1 - b_i⁻¹ X)` over a domain is
`s.val.map b`. -/
private theorem roots_prod_one_sub_C_inv_mul_X {L ι : Type*} [Field L] (s : Finset ι)
    {b : ι → L} (hb : ∀ i ∈ s, b i ≠ 0) :
    (∏ i ∈ s, (1 - Polynomial.C (b i)⁻¹ * Polynomial.X)).roots = s.val.map b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i t hit ih =>
    have hi : b i ≠ 0 := hb i (Finset.mem_insert_self i t)
    have hfac : (1 - Polynomial.C (b i)⁻¹ * Polynomial.X) =
        Polynomial.C (-(b i)⁻¹) * (Polynomial.X - Polynomial.C (b i)) := by
      rw [mul_sub, Polynomial.C_neg, neg_mul, neg_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hi,
        sub_neg_eq_add, Polynomial.C_1, sub_eq_neg_add]
    have hlin_ne : (1 - Polynomial.C (b i)⁻¹ * Polynomial.X) ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero hi)))
        (Polynomial.X_sub_C_ne_zero _)
    have ht_ne : (∏ j ∈ t, (1 - Polynomial.C (b j)⁻¹ * Polynomial.X)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ h0 ↦ by
        have hc := congrArg (fun p : Polynomial L ↦ p.coeff 0) h0
        simp at hc
    rw [Finset.prod_insert hit, Polynomial.roots_mul (mul_ne_zero hlin_ne ht_ne), hfac,
      Polynomial.roots_C_mul _ (neg_ne_zero.mpr (inv_ne_zero hi)), Polynomial.roots_X_sub_C,
      ih (fun j hj ↦ hb j (Finset.mem_insert_of_mem hj)), Finset.insert_val_of_notMem hit,
      Multiset.map_cons, Multiset.singleton_add]

/-- **Zero multiset of an entire Weierstrass product.** Let `a : ι → K` be a family of nonzero
elements with `‖a i‖ → ∞` cofinitely, and `W` the product of `1 - (a i)⁻¹ X` in
`PowerSeries.IsEntire.subring K`. At every positive radius `r`, if `s` consists of the indices with
`‖a i‖ ≤ r`, then in any complete normed field extension `L` of `K` the zero multiset of `W` on the
closed disc of radius `r` is `(s.val.map a).map (algebraMap K L)`. -/
theorem zeroMultiset_of_hasProd {ι L : Type*} [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] {a : ι → K} {W : IsEntire.subring K} (ha0 : ∀ i, a i ≠ 0)
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    {r : ℝ} (hr : 0 < r) {s : Finset ι} (hs : ∀ i, ‖a i‖ ≤ r ↔ i ∈ s) :
    (W : K⟦X⟧).zeroMultiset r L = (s.val.map a).map (algebraMap K L) := by
  obtain ⟨U, -, hprep⟩ := exists_isEntire_isDiscPreparation_of_hasProd ha0 ha hW hr hs
  rw [hprep.zeroMultiset_eq_roots_map hr, Polynomial.map_prod]
  have hmap : (∏ x ∈ s, Polynomial.map (algebraMap K L)
      (1 - Polynomial.C (a x)⁻¹ * Polynomial.X)) =
      ∏ x ∈ s, (1 - Polynomial.C (algebraMap K L (a x))⁻¹ * Polynomial.X) := by
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    simp
  rw [hmap, roots_prod_one_sub_C_inv_mul_X s fun i _ ↦
    (map_ne_zero (algebraMap K L)).mpr (ha0 i), Multiset.map_map]
  rfl

/-- **Taylor multiplicities of an entire Weierstrass product in an extension.** Let `a : ι → K` be
a family of nonzero elements with `‖a i‖ → ∞` cofinitely, and `W` the product of `1 - (a i)⁻¹ X` in
`PowerSeries.IsEntire.subring K`. In any complete normed field extension `L` of `K`, the
multiplicity of `W` at every `y : L` is the cardinality `{i : ι | algebraMap K L (a i) = y}.encard`.
In particular, `W` has only the prescribed zeros with the prescribed multiplicities. -/
theorem order_taylor_map_of_hasProd {ι L : Type*} [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] {a : ι → K} {W : IsEntire.subring K} (ha0 : ∀ i, a i ≠ 0)
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (y : L) :
    (_root_.PowerSeries.taylor y (_root_.PowerSeries.map (algebraMap K L) (W : K⟦X⟧))).order =
      {i : ι | algebraMap K L (a i) = y}.encard := by
  classical
  let r : ℝ := max ‖y‖ 1
  have hr : 0 < r := lt_max_of_lt_right zero_lt_one
  have hyr : ‖y‖ ≤ r := le_max_left _ _
  have hfin : {i : ι | ‖a i‖ ≤ r}.Finite := ((northcott_iff_tendsto _).mpr ha).finite_le r
  let s : Finset ι := hfin.toFinset
  have hs (i : ι) : ‖a i‖ ≤ r ↔ i ∈ s := hfin.mem_toFinset.symm
  have hW_ent : (W : K⟦X⟧).IsEntire := IsEntire.mem_subring.mp W.2
  rw [(hW_ent.isRestricted r).order_taylor_eq_count_zeroMultiset hr
    (ne_zero_of_hasProd_one_sub_C_inv_mul_X hW) hyr,
    zeroMultiset_of_hasProd ha0 ha hW hr hs]
  have hset : {i : ι | algebraMap K L (a i) = y} =
      ↑(s.filter fun i ↦ algebraMap K L (a i) = y) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, ← hs]
    refine ⟨fun hi ↦ ⟨?_, hi⟩, fun hi ↦ hi.2⟩
    rw [← norm_algebraMap' L (a i), hi]
    exact hyr
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Multiset.map_map, Function.comp_def,
    Multiset.count_map]
  congr 1
  simp [Finset.card_def, Finset.filter_val, eq_comm]

/-- **Taylor multiplicities of an entire Weierstrass product.** Over `K`, the Taylor multiplicity
of `W = ∏ (1 - (a i)⁻¹ X)` at every `x : K` is `{i : ι | a i = x}.encard`. -/
theorem order_taylor_of_hasProd {ι : Type*} {a : ι → K} {W : IsEntire.subring K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (x : K) :
    (_root_.PowerSeries.taylor x (W : K⟦X⟧)).order = {i : ι | a i = x}.encard := by
  simpa using order_taylor_map_of_hasProd (L := K) ha0 ha hW x

/-- **Taylor multiplicities of `∏' i, (1 - (a i)⁻¹ X)`.** -/
theorem order_taylor_tprod_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) (x : K) :
    (_root_.PowerSeries.taylor x
      (((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧))).order = {i : ι | a i = x}.encard :=
  order_taylor_of_hasProd ha0 ha (multipliable_polynomialHom_one_sub_C_inv_mul_X ha).hasProd x

/-- **Zero locus of an entire Weierstrass product in an extension.** In any complete normed field
extension `L` of `K`, the zeros of `W = ∏ (1 - (a i)⁻¹ X)` are precisely the images of `a i`: no
new zeros appear in `L`. -/
theorem evalAt_map_eq_zero_iff_of_hasProd {ι L : Type*} [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] {a : ι → K} {W : IsEntire.subring K} (ha0 : ∀ i, a i ≠ 0)
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (y : L) :
    (_root_.PowerSeries.map (algebraMap K L) (W : K⟦X⟧)).evalAt y = 0 ↔
      ∃ i, algebraMap K L (a i) = y := by
  rw [← constantCoeff_taylor, ← order_ne_zero_iff_constCoeff_eq_zero,
    order_taylor_map_of_hasProd ha0 ha hW y, ne_eq, Set.encard_eq_zero,
    Set.eq_empty_iff_forall_notMem]
  simp

/-- **Zero locus of an entire Weierstrass product.** For `x : K`, `(W : K⟦X⟧).evalAt x = 0` holds
if and only if `x` occurs in the family `a`. -/
theorem evalAt_eq_zero_iff_of_hasProd {ι : Type*} {a : ι → K} {W : IsEntire.subring K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (x : K) :
    (W : K⟦X⟧).evalAt x = 0 ↔ ∃ i, a i = x := by
  simpa using evalAt_map_eq_zero_iff_of_hasProd (L := K) ha0 ha hW x

/-- **Zero locus of `∏' i, (1 - (a i)⁻¹ X)`.** -/
theorem evalAt_tprod_one_sub_C_inv_mul_X_eq_zero_iff {ι : Type*} {a : ι → K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) (x : K) :
    (((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :
      IsEntire.subring K) : K⟦X⟧)).evalAt x = 0 ↔ ∃ i, a i = x :=
  evalAt_eq_zero_iff_of_hasProd ha0 ha
    (multipliable_polynomialHom_one_sub_C_inv_mul_X ha).hasProd x

end ConverseWeierstrass

end IsEntire

end TauCeti.PowerSeries

namespace PowerSeries.IsEntire

open TauCeti.PowerSeries

section ZerosTendstoInfinity

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {f : K⟦X⟧}

/-- **Norms of zeros tend to infinity.** Let `f` be a nonzero entire power series over a complete
ultrametric normed field `K`, and let `L` be any complete normed field extension of `K`. If
`a : ι → L` is a family of points in `L` each occurring at most as often as the Taylor multiplicity
of `f` at that point, then `‖a i‖ → ∞` along the cofinite filter on `ι`. -/
theorem tendsto_norm_cofinite_atTop_of_encard_le_order_taylor {ι L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsEntire) (hf0 : f ≠ 0) {a : ι → L}
    (ha : ∀ y : L, {i : ι | a i = y}.encard ≤
      (_root_.PowerSeries.taylor y (_root_.PowerSeries.map (algebraMap K L) f)).order) :
    Tendsto (fun i ↦ ‖a i‖) cofinite atTop := by
  classical
  rw [← northcott_iff_tendsto, northcott_iff]
  intro b
  let r : ℝ := max b 1
  have hr : 0 < r := lt_max_of_lt_right zero_lt_one
  have hbr : b ≤ r := le_max_left _ _
  have hsub : {i : ι | ‖a i‖ ≤ b} ⊆ ⋃ y ∈ (f.zeroMultiset r L).toFinset, {i : ι | a i = y} := by
    intro i hi
    have hir : ‖a i‖ ≤ r := hi.trans hbr
    have hpos : 0 < (_root_.PowerSeries.taylor (a i)
        (_root_.PowerSeries.map (algebraMap K L) f)).order :=
      (Set.encard_pos.mpr ⟨i, rfl⟩).trans_le (ha (a i))
    have hz : (_root_.PowerSeries.map (algebraMap K L) f).evalAt (a i) = 0 := by
      rw [← constantCoeff_taylor, ← order_ne_zero_iff_constCoeff_eq_zero]
      exact hpos.ne'
    have hmem : a i ∈ (f.zeroMultiset r L).toFinset :=
      Multiset.mem_toFinset.mpr (((hf.isRestricted r).mem_zeroMultiset_iff hr hf0).mpr ⟨hir, hz⟩)
    exact Set.mem_biUnion hmem rfl
  refine (Set.Finite.biUnion (Finset.finite_toSet _) fun y hy ↦ ?_).subset hsub
  have hyr : ‖y‖ ≤ r := norm_le_of_mem_zeroMultiset (Multiset.mem_toFinset.mp hy)
  refine Set.encard_lt_top_iff.mp ((ha y).trans_lt ?_)
  rw [(hf.isRestricted r).order_taylor_eq_count_zeroMultiset hr hf0 hyr]
  exact ENat.natCast_lt_top _

/-- Along a sequence `a : ℕ → L` of zeros of a nonzero entire series `f` repeated at most up to
their Taylor multiplicities, `‖a n‖ → ∞` as `n → ∞`. -/
theorem tendsto_norm_atTop_of_encard_le_order_taylor {L : Type*} [NormedField L]
    [NormedAlgebra K L] [CompleteSpace L] (hf : f.IsEntire) (hf0 : f ≠ 0) {a : ℕ → L}
    (ha : ∀ y : L, {n : ℕ | a n = y}.encard ≤
      (_root_.PowerSeries.taylor y (_root_.PowerSeries.map (algebraMap K L) f)).order) :
    Tendsto (fun n ↦ ‖a n‖) atTop atTop := by
  simpa only [Nat.cofinite_eq_atTop] using
    hf.tendsto_norm_cofinite_atTop_of_encard_le_order_taylor hf0 ha

end ZerosTendstoInfinity

section WeierstrassProduct

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {f : K⟦X⟧}

/-- **Unconditional Weierstrass product expansion.** Let `f` be an entire power series with
constant coefficient `1` over an algebraically closed complete ultrametric normed field `K`. For
any indexing `a : ι → K` of the zeros of `f` counted with their Taylor multiplicities, the linear
factors `1 - (a i)⁻¹ X` have unconditional infinite product `f` in `PowerSeries.IsEntire.subring K`
(that is, in every positive-radius Gauss norm and independently of any ordering of `ι`). -/
theorem hasProd_polynomialHom_of_order_taylor_eq {ι : Type*} (hf : f.IsEntire)
    (h0 : constantCoeff f = 1) {a : ι → K}
    (ha : ∀ x : K, (_root_.PowerSeries.taylor x f).order = {i : ι | a i = x}.encard) :
    HasProd (fun i ↦ IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X))
      ⟨f, IsEntire.mem_subring.mpr hf⟩ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  have ha0 (i : ι) : a i ≠ 0 := by
    intro hi
    have hpos : 0 < (_root_.PowerSeries.taylor 0 f).order := by
      rw [ha 0]
      exact Set.encard_pos.mpr ⟨i, hi⟩
    have hz : f.evalAt (0 : K) = 0 := by
      rw [← constantCoeff_taylor, ← order_ne_zero_iff_constCoeff_eq_zero]
      exact hpos.ne'
    rw [evalAt_at_zero, Algebra.algebraMap_self_apply, h0] at hz
    exact one_ne_zero hz
  have hnorm : Tendsto (fun i ↦ ‖a i‖) cofinite atTop :=
    hf.tendsto_norm_cofinite_atTop_of_encard_le_order_taylor (L := K) hf0 fun x ↦ by
      simp [ha x]
  have hm := TauCeti.PowerSeries.IsEntire.multipliable_polynomialHom_one_sub_C_inv_mul_X hnorm
  let W : IsEntire.subring K := ∏' i,
    IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)
  have hW_const : constantCoeff (W : K⟦X⟧) = 1 :=
    TauCeti.PowerSeries.IsEntire.constantCoeff_of_hasProd_one_sub_C_inv_mul_X hm.hasProd
  have hfW : f = (W : K⟦X⟧) :=
    hf.eq_of_order_taylor_eq (IsEntire.mem_subring.mp W.2) h0 hW_const fun x ↦ by
      rw [ha x, TauCeti.PowerSeries.IsEntire.order_taylor_of_hasProd ha0 hnorm hm.hasProd x]
  have hsub : (⟨f, IsEntire.mem_subring.mpr hf⟩ : IsEntire.subring K) = W := Subtype.ext hfW
  exact hsub ▸ hm.hasProd

open Classical in
omit [IsAlgClosed K] in
/-- The canonical unlabelled family of nonzero zeros of `f` repeated according to their Taylor
multiplicities has fiber cardinality `(taylor y f).order` at every nonzero `y : K`, and `0` at
`0`. -/
private theorem encard_sigma_zeros_eq {f : K⟦X⟧} (hf : f.IsEntire) (hf0 : f ≠ 0) (y : K) :
    {p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
      Fin (_root_.PowerSeries.taylor x.1 f).order.toNat | p.1.1 = y}.encard =
      if y = 0 then 0 else (_root_.PowerSeries.taylor y f).order := by
  split_ifs with hy0
  · subst hy0
    rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    exact fun p hp ↦ p.1.2.1 hp
  · by_cases hyz : f.evalAt y = 0
    · let z₀ : {x : K // x ≠ 0 ∧ f.evalAt x = 0} := ⟨y, hy0, hyz⟩
      let e : {p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
          Fin (_root_.PowerSeries.taylor x.1 f).order.toNat | p.1.1 = y} ≃
          Fin (_root_.PowerSeries.taylor y f).order.toNat :=
        { toFun := fun ⟨⟨x, k⟩, hx⟩ ↦ Fin.cast (by rw [hx]) k
          invFun := fun k ↦ ⟨⟨z₀, k⟩, rfl⟩
          left_inv := by
            rintro ⟨⟨⟨x, hx0, hxz⟩, k⟩, hx⟩
            cases hx
            rfl
          right_inv := fun k ↦ rfl }
      have hord_ne_top : (_root_.PowerSeries.taylor y f).order ≠ ⊤ := by
        have hr : 0 < max ‖y‖ 1 := lt_max_of_lt_right zero_lt_one
        have hcount := (hf.isRestricted (max ‖y‖ 1)).order_taylor_eq_count_zeroMultiset (L := K)
          hr hf0 (le_max_left _ _)
        simpa using (hcount.trans_lt (ENat.natCast_lt_top _)).ne
      rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
        ENat.natCast_toNat hord_ne_top]
    · have hord0 : (_root_.PowerSeries.taylor y f).order = 0 :=
        not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr
          (by rwa [constantCoeff_taylor]))
      rw [hord0, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      intro p hp
      exact hyz (hp ▸ p.1.2.2)

/-- **Canonical unlabelled Weierstrass product for `f(0) = 1`.** Every entire series `f` with
`f(0) = 1` over an algebraically closed complete ultrametric normed field `K` is the unconditional
product in `PowerSeries.IsEntire.subring K` of `1 - x⁻¹ X` indexed directly by the pairs `(x, k)`
with `f(x) = 0` and `k < (taylor x f).order.toNat`, choosing no enumeration of the zeros. -/
theorem hasProd_polynomialHom_zeros (hf : f.IsEntire) (h0 : constantCoeff f = 1) :
    HasProd (fun p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
        Fin (_root_.PowerSeries.taylor x.1 f).order.toNat ↦
      IsEntire.polynomialHom (1 - Polynomial.C (p.1.1)⁻¹ * Polynomial.X))
      ⟨f, IsEntire.mem_subring.mpr hf⟩ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  refine hf.hasProd_polynomialHom_of_order_taylor_eq h0 fun y ↦ ?_
  rw [encard_sigma_zeros_eq hf hf0 y]
  by_cases hy0 : y = 0
  · subst hy0
    simp only [↓reduceIte, taylor_zero]
    exact not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr (h0.symm ▸ one_ne_zero))
  · simp [hy0]

/-- **Weierstrass factorisation of a nonzero entire series, indexed form.** Let `f` be a nonzero
entire power series over an algebraically closed complete ultrametric normed field `K`, of order
`m = f.order.toNat` at `0` with leading nonzero coefficient `c = coeff m f`. For any family
`a : ι → K` of nonzero elements repeating each nonzero zero `x` of `f` according to its Taylor
multiplicity `(taylor x f).order`,
`f = C c * X ^ m * ∏' i, (1 - (a i)⁻¹ X)`. -/
theorem eq_C_mul_X_pow_mul_tprod_of_order_taylor_eq {ι : Type*} (hf : f.IsEntire) (hf0 : f ≠ 0)
    {a : ι → K} (ha0 : ∀ i, a i ≠ 0)
    (ha : ∀ x : K, x ≠ 0 → (_root_.PowerSeries.taylor x f).order = {i : ι | a i = x}.encard) :
    f = C (coeff f.order.toNat f) * X ^ f.order.toNat *
      ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧) := by
  set m := f.order.toNat
  have hm : f.order = m := (ENat.natCast_toNat (order_eq_top.not.mpr hf0)).symm
  obtain ⟨hcoeff, hlt⟩ := order_eq_nat.mp hm
  obtain ⟨g, hg, hfg⟩ := hf.exists_eq_X_sub_C_pow_mul (a := 0) (h := m) fun j hj ↦ by
    simpa [evalAt_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_hasseDeriv] using hlt j hj
  rw [map_zero, sub_zero] at hfg
  have hg0 : constantCoeff g = coeff m f := by
    simp [hfg, coeff_X_pow_mul']
  set c := coeff m f
  let g₁ : K⟦X⟧ := C c⁻¹ * g
  have hg₁ : g₁.IsEntire := (isEntire_C c⁻¹).mul hg
  have hg₁_const : constantCoeff g₁ = 1 := by
    simp [g₁, hg0, inv_mul_cancel₀ hcoeff]
  have hfg₁ : f = C c * X ^ m * g₁ := by
    have hc1 : C c * C c⁻¹ = (1 : K⟦X⟧) := by
      rw [← map_mul, mul_inv_cancel₀ hcoeff, map_one]
    simp only [g₁]
    rw [hfg]
    linear_combination (-(X ^ m * g)) * hc1
  have hord (x : K) : (_root_.PowerSeries.taylor x g₁).order = {i : ι | a i = x}.encard := by
    by_cases hx0 : x = 0
    · subst hx0
      rw [taylor_zero,
        not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr (hg₁_const.symm ▸ one_ne_zero)),
        eq_comm, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      exact fun i hi ↦ ha0 i hi
    · have hmon : ((C c * X ^ m : K⟦X⟧)).IsEntire := (isEntire_C c).mul (isEntire_X.pow m)
      have hmon_ord : (_root_.PowerSeries.taylor x (C c * X ^ m : K⟦X⟧)).order = 0 := by
        refine not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr ?_)
        rw [constantCoeff_taylor, (isEntire_C c).evalAt_mul (isEntire_X.pow m), evalAt_C,
          Algebra.algebraMap_self_apply, isEntire_X.evalAt_pow m, evalAt_X]
        exact mul_ne_zero hcoeff (pow_ne_zero m hx0)
      have hmul_ord : (_root_.PowerSeries.taylor x f).order =
          (_root_.PowerSeries.taylor x g₁).order := by
        rw [hfg₁, hmon.taylor_mul hg₁ x, order_mul, hmon_ord, zero_add]
      rw [← hmul_ord, ha x hx0]
  have hprod : ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :
      IsEntire.subring K) : K⟦X⟧) = g₁ :=
    congrArg Subtype.val (hg₁.hasProd_polynomialHom_of_order_taylor_eq hg₁_const hord).tprod_eq
  rw [hprod, hfg₁]

/-- **The Weierstrass entire product theorem.** Over an algebraically closed complete ultrametric
normed field `K`, every nonzero entire series `f` equals `C (coeff m f) * X ^ m` (where
`m = f.order.toNat`) times the unconditional Weierstrass product of `1 - x⁻¹ X` over its nonzero
zeros `x`, each repeated according to its Taylor multiplicity `(taylor x f).order.toNat`. -/
theorem eq_C_mul_X_pow_mul_tprod_zeros (hf : f.IsEntire) (hf0 : f ≠ 0) :
    f = C (coeff f.order.toNat f) * X ^ f.order.toNat *
      ((∏' p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
          Fin (_root_.PowerSeries.taylor x.1 f).order.toNat,
        IsEntire.polynomialHom (1 - Polynomial.C (p.1.1)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧) :=
  hf.eq_C_mul_X_pow_mul_tprod_of_order_taylor_eq hf0 (fun p ↦ p.1.2.1) fun x hx ↦ by
    rw [encard_sigma_zeros_eq hf hf0 x]
    simp [hx]

end WeierstrassProduct

end PowerSeries.IsEntire
