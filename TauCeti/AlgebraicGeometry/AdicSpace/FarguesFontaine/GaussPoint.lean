/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Window
public import TauCeti.Analysis.SpecialFunctions.Pow.NNRat
public import TauCeti.RingTheory.WittVector.GaussValuation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.SpecialFunctions.Log.Base

/-!
# Gauss points of `𝒴 = D(p) ∩ D([ϖ])`

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0`, perfect of characteristic
`p`, and let `ϖ ∈ O` be nonzero with `v(ϖ) < 1`; for instance `O = 𝒪_F` for a perfect
nonarchimedean field `F` of characteristic `p` with pseudouniformiser `ϖ`, so that `𝕎 O = A_inf`.
For `0 < ρ < 1` the Gauss valuation

```text
λ_ρ(∑ₙ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ
```

(`TauCeti.WittVector.gaussValuation`) defines a point `η_ρ` of `Spv(𝕎 O)`, the *Gauss point* of
radius `ρ`. It is continuous for the `(p, [ϖ])`-adic topology
(`TauCeti.WittVector.isContinuous_gaussValuation`), at most `1` everywhere, and does not vanish
at `p` or `[ϖ]`, since `λ_ρ(p) = ρ` and `λ_ρ([ϖ]) = v(ϖ)`. So `η_ρ` lies in the open
subset `𝒴 ⊆ Spa(𝕎 O, 𝕎 O)` whose quotient by Frobenius is the adic Fargues–Fontaine curve; in
particular `𝒴` is nonempty. Its support is trivial, and its radius `κ(η_ρ)` is
`log v(ϖ) / log ρ`, in the order-theoretic sense of `TauCeti.FarguesFontaine.IsRadiusLowerBound`:
`q = a / b ≤ κ(η_ρ)` exactly when `v(ϖ) ^ b ≤ ρ ^ a`. For `q ≠ 0` this says
`v(ϖ) ^ (1 / q) ≤ ρ`, so for `q, q' ≠ 0` the Gauss points with `q ≤ κ ≤ q'` are those of radius
`ρ ∈ [v(ϖ) ^ (1 / q), v(ϖ) ^ (1 / q')]`: the radius `κ` and the Gauss radius `ρ` are related
reciprocally.

The radius `ρ = 0` is allowed too: `λ_0(∑ₙ [xₙ] pⁿ) = v(x₀)` is the valuation `v` pulled back along
the projection `𝕎 O → O` to the first coordinate. The point `η_0` still lies in `Spa(𝕎 O, 𝕎 O)`,
but its support is `p 𝕎 O`, so it is not in `𝒴`.

## Main definitions

* `TauCeti.FarguesFontaine.gaussPoint` : the Gauss point `η_ρ ∈ Spv(𝕎 O)`.

## Main results

* `TauCeti.FarguesFontaine.gaussPoint_vle_iff` : `η_ρ` compares Witt vectors by `λ_ρ`.
* `TauCeti.FarguesFontaine.supp_gaussPoint` : the support of `η_ρ` is trivial.
* `TauCeti.FarguesFontaine.supp_gaussPoint_zero` : the support of `η_0` is `p 𝕎 O`.
* `TauCeti.FarguesFontaine.gaussPoint_mem_spa` : `η_ρ` is a point of `Spa(𝕎 O, 𝕎 O)`, for
  `0 ≤ ρ < 1`.
* `TauCeti.FarguesFontaine.gaussPoint_mem_spaY` : `η_ρ` is a point of `𝒴`.
* `TauCeti.FarguesFontaine.spaY_nonempty` : `𝒴` is nonempty.
* `TauCeti.FarguesFontaine.isRadiusLowerBound_gaussPoint_iff` and its upper analogue : the radius
  of `η_ρ` as a valuation inequality.
* `TauCeti.FarguesFontaine.isRadiusLowerBound_gaussPoint_iff_le_logb` and
  `TauCeti.FarguesFontaine.isRadiusUpperBound_gaussPoint_iff_logb_le` : the real-valued radius
  dictionary for `η_ρ`.
* `TauCeti.FarguesFontaine.isRadiusLowerBound_gaussPoint_iff_rpow` and its upper analogue : the
  reciprocal radius dictionary, `q ≤ κ(η_ρ) ↔ v(ϖ) ^ (1 / q) ≤ ρ` for `q ≠ 0`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  §2, for the radius parametrisation of the interval rings.
-/

public section

open scoped NNReal

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K] [CharP O p]
  [PerfectRing O p] {v : Valuation K ℝ≥0} {ρ : ℝ≥0}

variable (p) in
/-- **The Gauss point `η_ρ`** of `Spv(𝕎 O)`, for `ρ < 1`: the point given by the Gauss valuation
`λ_ρ(∑ₙ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ`. -/
noncomputable def gaussPoint (hv : v.Integers O) (ρ : ℝ≥0) (hρ : ρ < 1) :
    Spv (WittVector p O) :=
  ofValuation (gaussValuation p hv ρ hρ)

/-- The Gauss point `η_ρ` is the point defined by the Gauss valuation `λ_ρ`. -/
theorem gaussPoint_eq_ofValuation (hv : v.Integers O) (hρ : ρ < 1) :
    gaussPoint p hv ρ hρ = ofValuation (gaussValuation p hv ρ hρ) :=
  (rfl)

/-- The Gauss point `η_ρ` compares Witt vectors by their Gauss valuations. -/
@[simp]
theorem gaussPoint_vle_iff (hv : v.Integers O) (hρ : ρ < 1) (x y : WittVector p O) :
    (gaussPoint p hv ρ hρ).toValuativeRel.vle x y ↔
      gaussValuation p hv ρ hρ x ≤ gaussValuation p hv ρ hρ y :=
  vle_ofValuation _ x y

/-- **The support of a Gauss point is trivial**, for `0 < ρ`. -/
@[simp]
theorem supp_gaussPoint (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) :
    (gaussPoint p hv ρ hρ).supp = ⊥ :=
  Ideal.ext fun x ↦ by
    rw [mem_supp_iff, gaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero,
      gaussValuation_eq_zero_iff hv hρ₀, Ideal.mem_bot]

/-- **The support of the Gauss point of radius `0` is `p 𝕎 O`.** The valuation `λ_0` only sees
the first Teichmüller coordinate, `λ_0(∑ₙ [xₙ] pⁿ) = v(x₀)`, which vanishes exactly on the
multiples of `p`. -/
@[simp]
theorem supp_gaussPoint_zero (hv : v.Integers O) :
    (gaussPoint p hv 0 zero_lt_one).supp = Ideal.span {(p : WittVector p O)} := by
  -- `λ_0(x) = v(x₀)`, since the weights `0 ^ n` vanish for `n ≥ 1`
  have hval (x : WittVector p O) : gaussValuation p hv 0 zero_lt_one x =
      v (algebraMap O K (x.teichmullerCoeff 0)) := by
    refine le_antisymm ?_ (by simpa using le_gaussValuation hv zero_lt_one x 0)
    rw [gaussValuation_apply]
    exact ciSup_le fun n ↦ by cases n <;> simp
  ext x
  rw [mem_supp_iff, gaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero, hval, map_eq_zero,
    map_eq_zero_iff _ hv.hom_inj, teichmullerCoeff_zero, ← pow_one (p : WittVector p O),
    mem_span_p_pow_iff_le_coeff_eq_zero]
  simp

/-- **The Gauss point `η_ρ` lies in `Spa(𝕎 O, 𝕎 O)`**, for `ρ < 1`, `ϖ` with `v(ϖ) < 1`, and the
`(p, [ϖ])`-adic topology on `𝕎 O`. This includes the radius `ρ = 0`. -/
theorem gaussPoint_mem_spa [TopologicalSpace (WittVector p O)] {ϖ : O}
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hv : v.Integers O)
    (hρ : ρ < 1) (hϖ : v (algebraMap O K ϖ) < 1) :
    gaussPoint p hv ρ hρ ∈ spa (⊤ : Subring (WittVector p O)) := by
  rw [mem_spa_iff, gaussPoint_eq_ofValuation, isContinuous_ofValuation_iff,
    ← gaussPoint_eq_ofValuation]
  exact ⟨isContinuous_gaussValuation hI hv hρ hϖ, fun a _ ↦ by simp [gaussValuation_le_one]⟩

/-- **The Gauss point `η_ρ` lies in `𝒴 = D(p) ∩ D([ϖ])`**, for `0 < ρ < 1`, a nonzero `ϖ` with
`v(ϖ) < 1`, and the `(p, [ϖ])`-adic topology on `𝕎 O`. -/
theorem gaussPoint_mem_spaY [TopologicalSpace (WittVector p O)] {ϖ : O}
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hv : v.Integers O)
    (hρ₀ : 0 < ρ) (hρ : ρ < 1) (hϖ₀ : ϖ ≠ 0) (hϖ : v (algebraMap O K ϖ) < 1) :
    gaussPoint p hv ρ hρ ∈ spaY p ϖ := by
  rw [mem_spaY_iff]
  refine ⟨gaussPoint_mem_spa hI hv hρ hϖ, ?_, ?_⟩ <;>
    simp [hρ₀.ne', map_eq_zero_iff _ hv.hom_inj, hϖ₀]

/-- **`𝒴` is nonempty**: if `O` has a nonzero element `ϖ` with `v(ϖ) < 1`, then the open subset
`𝒴 = D(p) ∩ D([ϖ])` of `Spa(𝕎 O, 𝕎 O)` contains the Gauss points, for the `(p, [ϖ])`-adic
topology. -/
theorem spaY_nonempty [TopologicalSpace (WittVector p O)] {ϖ : O}
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hv : v.Integers O)
    (hϖ₀ : ϖ ≠ 0) (hϖ : v (algebraMap O K ϖ) < 1) : (spaY p ϖ).Nonempty :=
  ⟨_, gaussPoint_mem_spaY (ρ := 2⁻¹) hI hv (by norm_num) (by norm_num) hϖ₀ hϖ⟩

/-- **The radius of a Gauss point, from below.** For `q = a / b` in lowest terms, the predicate
`IsRadiusLowerBound p ϖ q η_ρ` holds exactly when `v(ϖ) ^ b ≤ ρ ^ a`. This holds for all `ρ < 1`
and `ϖ`; when moreover `0 < ρ` and `0 < v(ϖ) < 1`, it says that `q ≤ log v(ϖ) / log ρ`, so the
radius `κ(η_ρ)` is `log v(ϖ) / log ρ`. -/
theorem isRadiusLowerBound_gaussPoint_iff (hv : v.Integers O) (hρ : ρ < 1) (ϖ : O) (q : ℚ≥0) :
    IsRadiusLowerBound p ϖ q (gaussPoint p hv ρ hρ) ↔
      v (algebraMap O K ϖ) ^ q.den ≤ ρ ^ q.num := by
  rw [isRadiusLowerBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm]
  simp

/-- **The radius of a Gauss point, from above.** For `q = a / b` in lowest terms, the predicate
`IsRadiusUpperBound p ϖ q η_ρ` holds exactly when `ρ ^ a ≤ v(ϖ) ^ b`. This holds for all `ρ < 1`
and `ϖ`; when moreover `0 < ρ` and `0 < v(ϖ) < 1`, it says that `log v(ϖ) / log ρ ≤ q`. -/
theorem isRadiusUpperBound_gaussPoint_iff (hv : v.Integers O) (hρ : ρ < 1) (ϖ : O) (q : ℚ≥0) :
    IsRadiusUpperBound p ϖ q (gaussPoint p hv ρ hρ) ↔
      ρ ^ q.num ≤ v (algebraMap O K ϖ) ^ q.den := by
  rw [isRadiusUpperBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm]
  simp

/-- **The lower radius bound on a Gauss point is a real ratio inequality.** When the coefficient
norm of `ϖ` is positive and the Gauss radius lies in `(0, 1)`, the order-theoretic condition
`q ≤ κ(η_ρ)` is equivalent to `(q : ℝ) ≤ Real.logb ρ (v(ϖ))`. This is the real-valued
form of the radius dictionary used for interval rings. -/
theorem isRadiusLowerBound_gaussPoint_iff_le_logb (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    (ϖ : O) (hϖ₀ : 0 < v (algebraMap O K ϖ)) (q : ℚ≥0) :
    IsRadiusLowerBound p ϖ q (gaussPoint p hv ρ hρ) ↔
      (q : ℝ) ≤ Real.logb (ρ : ℝ) (v (algebraMap O K ϖ)) := by
  rw [isRadiusLowerBound_gaussPoint_iff hv hρ ϖ q, ← NNReal.coe_le_coe, NNRat.cast_def]
  push_cast
  exact Real.pow_le_pow_iff_div_le_logb_of_base_lt_one hρ₀ hρ hϖ₀ q.den_pos

/-- **The upper radius bound on a Gauss point is a real ratio inequality.** Under the same
positivity hypotheses, `κ(η_ρ) ≤ q` is equivalent to
`Real.logb ρ (v(ϖ)) ≤ (q : ℝ)`. -/
theorem isRadiusUpperBound_gaussPoint_iff_logb_le (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    (ϖ : O) (hϖ₀ : 0 < v (algebraMap O K ϖ)) (q : ℚ≥0) :
    IsRadiusUpperBound p ϖ q (gaussPoint p hv ρ hρ) ↔
      Real.logb (ρ : ℝ) (v (algebraMap O K ϖ)) ≤ (q : ℝ) := by
  rw [isRadiusUpperBound_gaussPoint_iff hv hρ ϖ q, ← NNReal.coe_le_coe, NNRat.cast_def]
  push_cast
  exact Real.pow_le_pow_iff_logb_le_div_of_base_lt_one hρ₀ hρ hϖ₀ q.den_pos

/-- **The reciprocal radius dictionary, from below.** For `q ≠ 0`, the bound `q ≤ κ(η_ρ)` holds
exactly when `v(ϖ) ^ (1 / q) ≤ ρ`. So for `q' ≠ 0` too, the Gauss points with `q ≤ κ ≤ q'` are
those of radius `ρ ∈ [v(ϖ) ^ (1 / q), v(ϖ) ^ (1 / q')]` (`isRadiusUpperBound_gaussPoint_iff_rpow`).
-/
theorem isRadiusLowerBound_gaussPoint_iff_rpow (hv : v.Integers O) (hρ : ρ < 1) (ϖ : O)
    {q : ℚ≥0} (hq : q ≠ 0) :
    IsRadiusLowerBound p ϖ q (gaussPoint p hv ρ hρ) ↔
      v (algebraMap O K ϖ) ^ ((q : ℝ)⁻¹) ≤ ρ := by
  have hnum : (0 : ℝ) < q.num := by exact_mod_cast NNRat.num_pos.mpr (pos_iff_ne_zero.mpr hq)
  rw [isRadiusLowerBound_gaussPoint_iff, NNReal.rpow_inv_nnratCast, NNReal.rpow_inv_le_iff hnum,
    NNReal.rpow_natCast]

/-- **The reciprocal radius dictionary, from above.** For `q ≠ 0`, the bound `κ(η_ρ) ≤ q` holds
exactly when `ρ ≤ v(ϖ) ^ (1 / q)`. -/
theorem isRadiusUpperBound_gaussPoint_iff_rpow (hv : v.Integers O) (hρ : ρ < 1) (ϖ : O)
    {q : ℚ≥0} (hq : q ≠ 0) :
    IsRadiusUpperBound p ϖ q (gaussPoint p hv ρ hρ) ↔
      ρ ≤ v (algebraMap O K ϖ) ^ ((q : ℝ)⁻¹) := by
  have hnum : (0 : ℝ) < q.num := by exact_mod_cast NNRat.num_pos.mpr (pos_iff_ne_zero.mpr hq)
  rw [isRadiusUpperBound_gaussPoint_iff, NNReal.rpow_inv_nnratCast, NNReal.le_rpow_inv_iff hnum,
    NNReal.rpow_natCast]

end TauCeti.FarguesFontaine
