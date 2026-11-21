/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
import Mathlib.Order.Northcott
import TauCeti.NumberTheory.NewtonPolygon.ZeroCount

/-!
# Newton polygons of entire Weierstrass products

Let `K` be a complete ultrametric normed field whose norm comes from a real additive valuation `v`
with base `b > 1`, so `‖x‖ = b ^ (-(v x).untop₀)` for `x ≠ 0`. Let `a : ι → K` be a family of
nonzero elements with `‖a i‖ → ∞` along the cofinite filter, and let `W` be the unconditional
entire Weierstrass product

```text
W = ∏' i, (1 - (a i)⁻¹ X)
```

in `PowerSeries.IsEntire.subring K`. At every real slope `σ`, splitting `W` at the closed disc of
radius `b ^ σ` gives its normalised disc preparation `W = P_s * U` where `P_s` is the finite product
over `‖a i‖ ≤ b ^ σ`, which splits over `K` into linear factors without assuming `K` to be
algebraically closed. Consequently the finite Newton face of `W` of slope `σ` runs from
`{i | ‖a i‖ < b ^ σ}.ncard` to `{i | ‖a i‖ ≤ b ^ σ}.ncard`, and the multiplicity of the slope `σ`
in the Newton polygon of `W` is `{i | ‖a i‖ = b ^ σ}.ncard`, equivalently
`{i | v (a i) = -σ}.ncard`.

## Main results

* `TauCeti.PowerSeries.IsEntire.isFiniteFace_newtonPolygon_of_hasProd` and
  `TauCeti.PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_ncard_addValuation_of_hasProd`: the
  finite faces and valuation-form slope multiplicities of an entire Weierstrass product, without
  assuming `K` to be algebraically closed. The norm form of the slope multiplicities is
  `TauCeti.PowerSeries.IsEntire.newtonSlopeMultiplicity_tprod_polynomialHom_one_sub_C_inv_mul_X`.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 4.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open Filter

namespace TauCeti.PowerSeries.IsEntire

open _root_.PowerSeries

section WeierstrassSlopes

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Finite Newton faces of an entire Weierstrass product.** Let `a : ι → K` be a family of nonzero
elements with `‖a i‖ → ∞` cofinitely, and let `W` be the product of `1 - (a i)⁻¹ X` in
`PowerSeries.IsEntire.subring K`. For every real slope `σ`, the Newton polygon of `W` has a finite
face of slope `σ` from `{i | ‖a i‖ < b ^ σ}.ncard` to `{i | ‖a i‖ ≤ b ^ σ}.ncard`. No
algebraic-closure hypothesis on `K` is needed. -/
theorem isFiniteFace_newtonPolygon_of_hasProd {ι : Type*} {a : ι → K} {W : IsEntire.subring K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (σ : ℝ) :
    IsFiniteFace ((W : K⟦X⟧).newtonPolygon v) σ
      {i : ι | ‖a i‖ < b ^ σ}.ncard {i : ι | ‖a i‖ ≤ b ^ σ}.ncard := by
  classical
  rw [← hW.tprod_eq]
  let r : ℝ := b ^ σ
  have hr : 0 < r := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfin : {i : ι | ‖a i‖ ≤ r}.Finite := ((northcott_iff_tendsto _).mpr ha).finite_le r
  let s : Finset ι := hfin.toFinset
  have hs (i : ι) : i ∈ s ↔ ‖a i‖ ≤ r := hfin.mem_toFinset
  have hprep := isDiscPreparation_tprod_polynomialHom_one_sub_C_inv_mul_X ha ha0 hr.le hs
  set F : IsEntire.subring K :=
    ∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)
  let P : Polynomial K := ∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)
  have hF_ent : (F : K⟦X⟧).IsEntire := IsEntire.mem_subring.mp F.property
  have hF_ne : (F : K⟦X⟧) ≠ 0 := by
    intro h
    have h1 := constantCoeff_tprod_polynomialHom_one_sub_C_mul_X (fun i ↦ (a i)⁻¹)
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨l, u, hface⟩ := hF_ent.exists_isFiniteFace_newtonPolygon v hb hv hF_ne σ
  obtain ⟨-, hu_dist⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon
    (F : K⟦X⟧) v hb hv hface
  have hu_eq : u = s.card := hu_dist.unique hprep.isDistinguished
  have hroots : P.roots = s.val.map a := by
    have hz1 := hprep.zeroMultiset_eq_roots_map (L := K) hr
    have hz2 := zeroMultiset_tprod_polynomialHom_one_sub_C_inv_mul_X (L := K) ha ha0 hs
    simpa [P] using hz1.symm.trans hz2
  have hsplits : P.Splits := Polynomial.splits_iff_card_roots.mpr (by
    rw [hroots, Multiset.card_map, ← Finset.card_def, hprep.natDegree_eq])
  have hl_eq : l = {i : ι | ‖a i‖ < r}.ncard := by
    have hlt := card_filter_roots_norm_lt_of_isUnit_mul v hb hv hface
      (hprep.isUnit hr) (hprep.natDegree_eq.trans hu_eq.symm).le
      ((mul_comm _ _).trans hprep.eq_mul.symm) hsplits
    rw [← hlt, hroots]
    have hset : {i : ι | ‖a i‖ < r} = ↑(s.filter fun i ↦ ‖a i‖ < r) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, hs]
      exact ⟨fun hi ↦ ⟨hi.le, hi⟩, fun hi ↦ hi.2⟩
    rw [hset, Set.ncard_coe_finset, Finset.card_def, Finset.filter_val, Multiset.filter_map,
      Multiset.card_map]
    rfl
  have hs_ncard : s.card = {i : ι | ‖a i‖ ≤ r}.ncard := by
    have hset : {i : ι | ‖a i‖ ≤ r} = (s : Set ι) := by
      ext i
      exact (hs i).symm
    rw [hset, Set.ncard_coe_finset]
  rwa [hl_eq, hu_eq, hs_ncard] at hface

/-- **Slope multiplicities of an entire Weierstrass product, valuation form.** The multiplicity of
each real slope `σ` in the Newton polygon of `W = ∏ (1 - (a i)⁻¹ X)` is the number of indices `i`
with `v (a i) = -σ`. -/
theorem newtonSlopeMultiplicity_eq_ncard_addValuation_of_hasProd {ι : Type*} {a : ι → K}
    {W : IsEntire.subring K} (ha0 : ∀ i, a i ≠ 0)
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (σ : ℝ) :
    (W : K⟦X⟧).newtonSlopeMultiplicity v σ =
      {i : ι | v (a i) = ((-σ : ℝ) : WithTop ℝ)}.ncard := by
  rw [← hW.tprod_eq, newtonSlopeMultiplicity_tprod_polynomialHom_one_sub_C_inv_mul_X v hb hv ha σ]
  congr 1
  ext i
  have hne_top : v (a i) ≠ ⊤ := (v.ne_top_iff).mpr (ha0 i)
  simp only [Set.mem_ofPred_eq]
  rw [hv (a i) (ha0 i), Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne',
    ← WithTop.coe_untop₀_of_ne_top hne_top, WithTop.coe_eq_coe, WithTop.untop₀_coe]
  exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

end WeierstrassSlopes

end TauCeti.PowerSeries.IsEntire
