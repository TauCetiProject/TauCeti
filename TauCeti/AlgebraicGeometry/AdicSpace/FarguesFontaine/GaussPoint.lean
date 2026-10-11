/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Window
public import TauCeti.RingTheory.WittVector.GaussValuation

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
`q = a / b ≤ κ(η_ρ)` exactly when `v(ϖ) ^ b ≤ ρ ^ a`.

## Main definitions

* `TauCeti.FarguesFontaine.gaussPoint` : the Gauss point `η_ρ ∈ Spv(𝕎 O)`.

## Main results

* `TauCeti.FarguesFontaine.gaussPoint_vle_iff` : `η_ρ` compares Witt vectors by `λ_ρ`.
* `TauCeti.FarguesFontaine.supp_gaussPoint` : the support of `η_ρ` is trivial.
* `TauCeti.FarguesFontaine.gaussPoint_mem_spaY` : `η_ρ` is a point of `𝒴`.
* `TauCeti.FarguesFontaine.spaY_nonempty` : `𝒴` is nonempty.
* `TauCeti.FarguesFontaine.isRadiusLowerBound_gaussPoint_iff` and its upper analogue : the radius
  of `η_ρ`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1.
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

/-- **The Gauss point `η_ρ` lies in `𝒴 = D(p) ∩ D([ϖ])`**, for `0 < ρ < 1`, a nonzero `ϖ` with
`v(ϖ) < 1`, and the `(p, [ϖ])`-adic topology on `𝕎 O`. -/
theorem gaussPoint_mem_spaY [TopologicalSpace (WittVector p O)] {ϖ : O}
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hv : v.Integers O)
    (hρ₀ : 0 < ρ) (hρ : ρ < 1) (hϖ₀ : ϖ ≠ 0) (hϖ : v (algebraMap O K ϖ) < 1) :
    gaussPoint p hv ρ hρ ∈ spaY p ϖ := by
  rw [mem_spaY_iff, mem_spa_iff, gaussPoint_eq_ofValuation, isContinuous_ofValuation_iff,
    ← gaussPoint_eq_ofValuation]
  refine ⟨⟨isContinuous_gaussValuation hI hv hρ hϖ, fun a _ ↦ ?_⟩, ?_, ?_⟩ <;>
    simp [gaussValuation_le_one, hρ₀.ne', map_eq_zero_iff _ hv.hom_inj, hϖ₀]

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

end TauCeti.FarguesFontaine
