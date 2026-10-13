/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.GaussPoint

/-!
# Analytic points of `Spa(A_inf, A_inf)` outside `𝒴`

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, let `ϖ ∈ O` be nonzero with `v(ϖ) < 1`, and give `𝕎 O` the `(p, [ϖ])`-adic
topology; for `O = 𝒪_F` and a pseudouniformiser `ϖ` this is `A_inf`. The analytic locus of
`Spa(𝕎 O, 𝕎 O)` is `D(p) ∪ D([ϖ])` (`TauCeti.FarguesFontaine.mem_spaAnalytic_iff_of_isAdic`),
and it contains `𝒴 = D(p) ∩ D([ϖ])`. This file shows that the containment is strict, with an
analytic point outside `𝒴` on either side.

* The Gauss point `η_0` of radius `0`, `∑ₙ [xₙ] pⁿ ↦ v(x₀)`, is the valuation `v` pulled back along
  the projection `𝕎 O → O` to the first coordinate. Its support is `p 𝕎 O`
  (`TauCeti.FarguesFontaine.supp_gaussPoint_zero`), so it kills `p` but not `[ϖ]`, and lies in
  `D([ϖ]) \ 𝒴`.
* A maximal ideal `𝔪` of `O` contains `ϖ`, which is not a unit, and the residue field `k = O ⧸ 𝔪`
  is perfect of characteristic `p`. This part only uses that `O` is perfect of characteristic `p`
  and that `ϖ` is not a unit. The `p`-adic valuation of `𝕎 k`, pulled back along
  `𝕎 O → 𝕎 k`, kills `[ϖ]` but not `p`, so it lies in `D(p) \ 𝒴`. The `p`-adic valuation
  `x ↦ ρ ^ (ord_p x)` of `𝕎 k` is the Gauss valuation `λ_ρ` for the trivial valuation of `k`
  (`Valuation.integers_one`).

In the usual picture of `Spa(A_inf, A_inf)` these are the points written `x_L` and `x_crys`.

## Main results

* `TauCeti.FarguesFontaine.gaussPoint_zero_mem_spaAnalytic` and
  `TauCeti.FarguesFontaine.gaussPoint_zero_notMem_spaY` : `η_0` is an analytic point outside `𝒴`.
* `TauCeti.FarguesFontaine.exists_mem_spa_natCast_notMem_supp_teichmuller_mem_supp` : some point
  of `Spa(𝕎 O, 𝕎 O)` kills `[ϖ]` but not `p`.
* `TauCeti.FarguesFontaine.spaY_ssubset_spaAnalytic` : `𝒴` is strictly contained in the analytic
  locus.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 12.
-/

public section

open scoped NNReal

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K] [CharP O p]
  [PerfectRing O p] {v : Valuation K ℝ≥0} [TopologicalSpace (WittVector p O)] {ϖ : O}

/-- **The Gauss point `η_0` of radius `0` is analytic**: it lies in `Spa(𝕎 O, 𝕎 O)` and does not
kill `[ϖ]`, for a nonzero `ϖ` with `v(ϖ) < 1` and the `(p, [ϖ])`-adic topology on `𝕎 O`. -/
theorem gaussPoint_zero_mem_spaAnalytic
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hv : v.Integers O)
    (hϖ₀ : ϖ ≠ 0) (hϖ : v (algebraMap O K ϖ) < 1) :
    gaussPoint p hv 0 zero_lt_one ∈ spaAnalytic (⊤ : Subring (WittVector p O)) := by
  refine (mem_spaAnalytic_iff_of_isAdic hI ⊤ _).mpr
    ⟨gaussPoint_mem_spa hI hv zero_lt_one hϖ, Or.inr ?_⟩
  rw [mem_supp_iff, gaussPoint_vle_iff]
  simp [map_eq_zero_iff _ hv.hom_inj, hϖ₀]

/-- **The Gauss point `η_0` of radius `0` is not in `𝒴`**: it kills `p`. -/
theorem gaussPoint_zero_notMem_spaY (hv : v.Integers O) :
    gaussPoint p hv 0 zero_lt_one ∉ spaY p ϖ := fun h ↦
  ((mem_spaY_iff p ϖ _).mp h).2.1 (supp_gaussPoint_zero hv ▸ Ideal.mem_span_singleton_self _)

omit [CharP O p] [PerfectRing O p] in
/-- The point of `Spa(𝕎 O, 𝕎 O)` attached to a ring homomorphism `φ : O → k` into a perfect field
of characteristic `p` killing `ϖ`: the `p`-adic valuation `λ_{1/2}(x) = 2 ^ (-ord_p x)` of `𝕎 k`,
pulled back along `𝕎 O → 𝕎 k`, kills `[ϖ]` but not `p`. -/
private theorem exists_mem_spa_natCast_notMem_supp_teichmuller_mem_supp_of_ringHom {k : Type*}
    [Field k] [CharP k p] [PerfectRing k p] (φ : O →+* k) (hφ : φ ϖ = 0)
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) :
    ∃ x ∈ spa (⊤ : Subring (WittVector p O)),
      (p : WittVector p O) ∉ x.supp ∧ teichmuller p ϖ ∈ x.supp := by
  classical
  -- the Gauss valuation of `𝕎 k` for the trivial valuation of `k`, pulled back to `𝕎 O`
  let w := (gaussValuation p (Valuation.integers_one (R := k) (Γ₀ := ℝ≥0)) 2⁻¹
    (by norm_num)).comap (WittVector.map φ)
  refine ⟨ofValuation w, ?_, ?_, ?_⟩
  · rw [mem_spa_iff, isContinuous_ofValuation_iff]
    refine ⟨Valuation.isContinuous_of_isAdic hI (fun a _ ↦ gaussValuation_le_one _ _ _)
      (c := 2⁻¹) (by norm_num) ?_, fun a _ ↦ ?_⟩
    · rintro t (rfl | rfl) <;> simp [w, hφ]
    · simpa [vle_ofValuation, w] using gaussValuation_le_one _ _ _
  · simp [w]
  · simp [w, hφ]

/-- **A point of `Spa(𝕎 O, 𝕎 O)` killing `[ϖ]` but not `p`**, for a perfect ring `O` of
characteristic `p`, a nonunit `ϖ ∈ O` (for instance `v(ϖ) < 1` when `O` is a ring of integers of
`v`), and the `(p, [ϖ])`-adic topology on `𝕎 O`: the `p`-adic valuation of the Witt vectors of a
residue field of `O`, pulled back to `𝕎 O`. It is an analytic point outside `𝒴`, in `D(p) \ 𝒴`. -/
theorem exists_mem_spa_natCast_notMem_supp_teichmuller_mem_supp
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hϖ : ¬IsUnit ϖ) :
    ∃ x ∈ spa (⊤ : Subring (WittVector p O)),
      (p : WittVector p O) ∉ x.supp ∧ teichmuller p ϖ ∈ x.supp := by
  -- `ϖ` is not a unit, so it lies in a maximal ideal `𝔪`, whose residue field is perfect
  obtain ⟨𝔪, h𝔪, hϖ𝔪⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hϖ)
  let := Ideal.Quotient.field 𝔪
  have : CharP (O ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), CharP.cast_eq_zero, map_zero]
  have : PerfectRing (O ⧸ 𝔪) p := PerfectRing.ofSurjective _ p fun x ↦ by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := surjective_frobenius O p y
    exact ⟨Ideal.Quotient.mk 𝔪 z, by simp [frobenius_def]⟩
  exact exists_mem_spa_natCast_notMem_supp_teichmuller_mem_supp_of_ringHom (Ideal.Quotient.mk 𝔪)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (hϖ𝔪 (Ideal.mem_span_singleton_self ϖ))) hI

/-- **`𝒴` is strictly contained in the analytic locus** of `Spa(𝕎 O, 𝕎 O)`, for a nonzero `ϖ` with
`v(ϖ) < 1` and the `(p, [ϖ])`-adic topology on `𝕎 O`: the Gauss point `η_0` is analytic and not in
`𝒴`. (`exists_mem_spa_natCast_notMem_supp_teichmuller_mem_supp` gives a second such point, on the
other side.) -/
theorem spaY_ssubset_spaAnalytic
    (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ})) (hv : v.Integers O)
    (hϖ₀ : ϖ ≠ 0) (hϖ : v (algebraMap O K ϖ) < 1) :
    spaY p ϖ ⊂ spaAnalytic (⊤ : Subring (WittVector p O)) :=
  (Set.ssubset_iff_of_subset (spaY_subset_spaAnalytic hI)).mpr
    ⟨_, gaussPoint_zero_mem_spaAnalytic hI hv hϖ₀ hϖ, gaussPoint_zero_notMem_spaY hv⟩

end TauCeti.FarguesFontaine
