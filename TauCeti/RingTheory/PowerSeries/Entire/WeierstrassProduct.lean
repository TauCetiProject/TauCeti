/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Product
import TauCeti.RingTheory.PowerSeries.GaussNorm.NearOne

/-!
# The Weierstrass entire product theorem

Let `K` be a complete ultrametric normed field. For any family `a : ι → K` with `‖a i‖ → ∞` along
the cofinite filter, the linear polynomial factors `1 - (a i)⁻¹ X` satisfy
`‖(1 - (a i)⁻¹ X) - 1‖_r = ‖a i‖⁻¹ r → 0` at every positive radius `r`, so they tend to `1` in the
topology of `PowerSeries.IsEntire.subring K`; their unconditional product is the canonical
Weierstrass product of `TauCeti.RingTheory.PowerSeries.Entire.Product`.

Over an algebraically closed `K`, the enumeration-independent factorisation
`PowerSeries.IsEntire.hasProd_polynomialHom_one_sub_C_inv_mul_X` of entire series with constant
coefficient `1` applies in particular to the canonical unlabelled family of zeros, indexed by the
pairs `(x, k)` with `f(x) = 0`, `x ≠ 0` and `k < (taylor x f).order.toNat`, so no enumeration of
the zeros has to be chosen. Splitting off the order `m` of `f` at `0` and its leading coefficient,
every nonzero entire series factors as

```text
f = C (coeff m f) * X ^ m * ∏' p, (1 - x⁻¹ X)
```

with the unconditional product over its nonzero zeros counted with multiplicity.

## Main results

* `Filter.Tendsto.isEntire_polynomialHom_one_sub_C_inv_mul_X`: when `‖a i‖ → ∞` cofinitely, the
  linear entire factors `1 - (a i)⁻¹ X` tend to `1` in `PowerSeries.IsEntire.subring K`.
* `PowerSeries.IsEntire.hasProd_polynomialHom_zeros`: every entire series with constant
  coefficient `1` is the unconditional product of `1 - x⁻¹ X` over its canonically indexed zeros.
* `PowerSeries.IsEntire.eq_C_mul_X_pow_mul_tprod_of_order_taylor_eq` and
  `PowerSeries.IsEntire.eq_C_mul_X_pow_mul_tprod_zeros`: the Weierstrass entire product theorem
  `f = C (coeff m f) * X ^ m * ∏' (1 - x⁻¹ X)` for every nonzero entire series over an
  algebraically closed complete ultrametric field.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §4.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §4.
-/

public section

open Filter
open scoped Topology

section WeierstrassFactors

open PowerSeries TauCeti.PowerSeries TauCeti.PowerSeries.IsEntire

attribute [local instance] TauCeti.PowerSeries.IsEntire.radius_pos

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- When `‖a i‖ → ∞` along the cofinite filter, the linear entire factors `1 - (a i)⁻¹ X` tend to
`1` in the topology of entire series. -/
theorem Filter.Tendsto.isEntire_polynomialHom_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
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
  rw [gaussNorm_one_sub_C_mul_X_sub_one _ r.property.le, norm_inv]

end WeierstrassFactors

namespace PowerSeries.IsEntire

open TauCeti.PowerSeries

section WeierstrassProduct

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  {f : K⟦X⟧}

open Classical in
omit [IsAlgClosed K] in
/-- The canonical unlabelled family of nonzero zeros of `f` repeated according to their Taylor
multiplicities has fiber cardinality `(taylor y f).order` at every nonzero `y : K`, and `0` at
`0`. -/
private theorem encard_sigma_zeros_eq {f : K⟦X⟧} (hf : f.IsEntire) (hf0 : f ≠ 0) (y : K) :
    {p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
      Fin (_root_.PowerSeries.taylor x.val f).order.toNat | p.1.val = y}.encard =
      if y = 0 then 0 else (_root_.PowerSeries.taylor y f).order := by
  split_ifs with hy0
  · subst hy0
    rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    exact fun p hp ↦ p.1.property.1 hp
  · by_cases hyz : f.evalAt y = 0
    · let z₀ : {x : K // x ≠ 0 ∧ f.evalAt x = 0} := ⟨y, hy0, hyz⟩
      let e : {p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
          Fin (_root_.PowerSeries.taylor x.val f).order.toNat | p.1.val = y} ≃
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
      exact hyz (hp ▸ p.1.property.2)

/-- **Canonical unlabelled Weierstrass product for `f(0) = 1`.** Every entire series `f` with
`f(0) = 1` over an algebraically closed complete ultrametric normed field `K` is the unconditional
product in `PowerSeries.IsEntire.subring K` of `1 - x⁻¹ X` indexed directly by the pairs `(x, k)`
with `f(x) = 0` and `k < (taylor x f).order.toNat`, choosing no enumeration of the zeros. -/
theorem hasProd_polynomialHom_zeros (hf : f.IsEntire) (h0 : constantCoeff f = 1) :
    HasProd (fun p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
        Fin (_root_.PowerSeries.taylor x.val f).order.toNat ↦
      IsEntire.polynomialHom (1 - Polynomial.C (p.1.val)⁻¹ * Polynomial.X))
      ⟨f, IsEntire.mem_subring.mpr hf⟩ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  refine hf.hasProd_polynomialHom_one_sub_C_inv_mul_X h0 fun y ↦ ?_
  rw [encard_sigma_zeros_eq hf hf0 y]
  by_cases hy0 : y = 0
  · subst hy0
    simp only [↓reduceIte, taylor_zero]
    exact (not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr (h0.symm ▸ one_ne_zero))).symm
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
  obtain ⟨g₁, hg₁, hg₁_const, hfg₁, hord_nz⟩ :=
    hf.exists_eq_C_mul_X_pow_mul_constantCoeff_one hf0
  have hord (x : K) : (_root_.PowerSeries.taylor x g₁).order = {i : ι | a i = x}.encard := by
    by_cases hx0 : x = 0
    · subst hx0
      rw [taylor_zero,
        not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr (hg₁_const.symm ▸ one_ne_zero)),
        eq_comm, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      exact fun i hi ↦ ha0 i hi
    · rw [hord_nz x hx0, ha x hx0]
  have hprod : ((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :
      IsEntire.subring K) : K⟦X⟧) = g₁ :=
    congrArg Subtype.val
      (hg₁.hasProd_polynomialHom_one_sub_C_inv_mul_X hg₁_const fun x ↦ (hord x).symm).tprod_eq
  rw [hprod, ← hfg₁]

/-- **The Weierstrass entire product theorem.** Over an algebraically closed complete ultrametric
normed field `K`, every nonzero entire series `f` equals `C (coeff m f) * X ^ m` (where
`m = f.order.toNat`) times the unconditional Weierstrass product of `1 - x⁻¹ X` over its nonzero
zeros `x`, each repeated according to its Taylor multiplicity `(taylor x f).order.toNat`. -/
theorem eq_C_mul_X_pow_mul_tprod_zeros (hf : f.IsEntire) (hf0 : f ≠ 0) :
    f = C (coeff f.order.toNat f) * X ^ f.order.toNat *
      ((∏' p : Σ x : {x : K // x ≠ 0 ∧ f.evalAt x = 0},
          Fin (_root_.PowerSeries.taylor x.val f).order.toNat,
        IsEntire.polynomialHom (1 - Polynomial.C (p.1.val)⁻¹ * Polynomial.X) :
        IsEntire.subring K) : K⟦X⟧) :=
  hf.eq_C_mul_X_pow_mul_tprod_of_order_taylor_eq hf0 (fun p ↦ p.1.property.1) fun x hx ↦ by
    rw [encard_sigma_zeros_eq hf hf0 x]
    simp [hx]

end WeierstrassProduct

end PowerSeries.IsEntire
