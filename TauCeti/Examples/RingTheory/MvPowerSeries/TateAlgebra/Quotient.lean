/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
public import TauCeti.RingTheory.Huber.Restricted.BoundedLift
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal
public import TauCeti.Topology.MetricSpace.Ultra.Prod

/-!
# Sharpness and instantiations of restricted-series quotient and lifting theorems

Let `φ : R →+* S` be a bounded ring homomorphism between ultrametric normed rings. The quotient and
lifting theorems in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient` and
`TauCeti.RingTheory.Huber.Restricted.BoundedLift` separate three regimes on `φ`: algebraic
surjectivity, uniformly `L`-bounded preimages, and sharp `(1 + ε)`-approximate or exact
norm-attaining preimages. This file gives concrete `p`-adic and Tate-algebra witnesses separating
those regimes and instantiating the strongest one:

1. **Algebraic bijectivity + contractivity does not imply surjectivity of `restrictedMap`.**
   The identity ring isomorphism from trivially normed `ℤ_[p]` (`WithAbs AbsoluteValue.trivial`) to
   `p`-adically normed `ℤ_[p]` is contractive and bijective, yet `∑ pⁿ Xⁿ` lies in `ℤ_[p]⟨X⟩` and
   has no restricted preimage (`not_surjective_restrictedMap_trivialPadicInt`).
2. **Uniformly `L`-bounded linear sections yield open quotient maps with continuous additive lifts,
   but need not give an isometric quotient.** Witnessed by `evalZeroOneHom`: evaluating
   `f ∈ ℚ_[p]{Y/2}` at `Y = 0` and `Y = 1` gives a contractive ring homomorphism
   `ℚ_[p]{Y/2} →+* ℚ_[p] × ℚ_[p]` with `2`-bounded additive section `interpZeroOneAddHom` sending
   `(u, v)` to `u + (v - u) Y`. At every positive polyradius `c`, `restrictedMap` is an open
   quotient map (`isOpenQuotientMap_restrictedMap_evalZeroOneHom`) with continuous additive right
   inverse `restrictedAddMap` (`rightInverse_restrictedAddMap_interpZeroOneAddHom`), yet every
   preimage of `(0, 1)` in `ℚ_[p]{Y/2}` has Gauss norm at least `2 > ‖(0, 1)‖`, so the induced
   quotient equivalence is **not** an isometry
   (`not_isometry_quotientKerEquivOfSurjective_restrictedMap_evalZeroOneHom`).
3. **Quotients of Tate algebras satisfy exact Gauss-norm lifting and isometric quotient
   comparison.** Every ideal `I` of a finite-variable Tate algebra `K{Y/d}` over a complete
   ultrametric field `K` is strictly closed (`Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring`).
   Consequently, for any second variable set `σ` and positive polyradius `c`, reducing coefficients
   modulo `I` lifts restricted series with **exact** Gauss-norm equality
   (`exists_restrictedMap_mk_eq_and_norm_eq_tateQuotient`) and induces an isometric quotient
   equivalence (`isometry_quotientKerEquivOfSurjective_restrictedMap_mk_tateQuotient`), and likewise
   lifts elements of the completed Huber algebra `(K{Y/d} ⧸ I)⟨X₁, …, Xₖ⟩` with exact compared Gauss
   norm (`exists_weightedMapCompletion_eq_and_norm_eq_tateQuotient`).
-/

public section

namespace TauCeti.Examples.TateAlgebraQuotient

open Filter _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped Topology

section AlgebraicBijectionFailsSurjectivity

variable (p : ℕ) [hp : Fact p.Prime]

open Classical in
/-- The trivial absolute value on `ℤ_[p]` is nonarchimedean. -/
private theorem isNonarchimedean_trivial_padicInt :
    IsNonarchimedean (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ) := by
  intro x y
  by_cases hxy : x + y = 0
  · simp [hxy]
  · have hxy' : x ≠ 0 ∨ y ≠ 0 := by
      by_contra! h
      exact hxy (by simp [h.1, h.2])
    rcases hxy' with hx | hy
    · simp [AbsoluteValue.trivial_apply hxy, AbsoluteValue.trivial_apply hx]
    · simp [AbsoluteValue.trivial_apply hxy, AbsoluteValue.trivial_apply hy]

open Classical in
/-- `WithAbs AbsoluteValue.trivial` on `ℤ_[p]` carries an ultrametric distance. -/
local instance : IsUltrametricDist (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)) :=
  (isNonarchimedean_trivial_padicInt p).isUltrametricDist_withAbs

open Classical in
/-- The canonical ring isomorphism `WithAbs AbsoluteValue.trivial →+* ℤ_[p]` is contractive. -/
theorem norm_withAbs_trivial_padicInt_le
    (x : WithAbs (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)) :
    ‖(WithAbs.equiv (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)).toRingHom x‖ ≤ 1 * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : x.ofAbs ≠ 0 := fun h ↦
      hx (WithAbs.ofAbs_injective _ (h.trans (WithAbs.ofAbs_zero _).symm))
    rw [one_mul, WithAbs.norm_eq_apply_ofAbs, AbsoluteValue.trivial_apply hx']
    exact PadicInt.norm_le_one x.ofAbs

open Classical in
/-- **Algebraic bijectivity and contractivity do not make `restrictedMap` surjective.** Although
`WithAbs.equiv AbsoluteValue.trivial : WithAbs AbsoluteValue.trivial ≃+* ℤ_[p]` is a contractive
ring isomorphism, its induced unit-radius map on restricted univariate power series misses
`∑ₙ pⁿ Xⁿ`. -/
theorem not_surjective_restrictedMap_trivialPadicInt :
    ¬ Function.Surjective
      (restrictedMap (c := fun _ : Unit ↦ (1 : ℝ))
        (WithAbs.equiv (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)).toRingHom
        (norm_withAbs_trivial_padicInt_le p)) := by
  intro hsurj
  have hp0 : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr hp.out.one_lt)
  let g : MvPowerSeries Unit ℤ_[p] := fun t ↦ (p : ℤ_[p]) ^ t ()
  have hg : IsRestricted (fun _ : Unit ↦ (1 : ℝ)) g := by
    rw [IsRestricted]
    have hlim : Tendsto (fun n : ℕ ↦ ‖(p : ℤ_[p])‖ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp1
    have hev : Tendsto (fun t : Unit →₀ ℕ ↦ t ()) cofinite atTop :=
      (Finsupp.equivFunOnFinite.trans
        (Equiv.funUnique Unit ℕ)).injective.tendsto_cofinite.mono_right Nat.cofinite_eq_atTop.le
    refine (hlim.comp hev).congr fun t ↦ ?_
    simp only [Function.comp_apply, one_pow, Finsupp.prod, Finset.prod_const_one, mul_one,
      coeff_apply g, g, norm_pow]
  obtain ⟨f, hf⟩ := hsurj ⟨g, hg⟩
  have hfnorm (t : Unit →₀ ℕ) :
      ‖coeff t (f : MvPowerSeries Unit
        (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)))‖ = 1 := by
    have ht : ((coeff t (f : MvPowerSeries Unit
        (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)))).ofAbs : ℤ_[p]) =
        (p : ℤ_[p]) ^ t () := by
      have h := coeff_restrictedMap
        (WithAbs.equiv (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)).toRingHom
        (norm_withAbs_trivial_padicInt_le p) f t
      rw [hf] at h
      exact h.symm
    have hne : (coeff t (f : MvPowerSeries Unit
        (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℤ_[p] ℝ)))).ofAbs ≠ 0 := by
      rw [ht]
      exact pow_ne_zero _ hp0
    rw [WithAbs.norm_eq_apply_ofAbs, AbsoluteValue.trivial_apply hne]
  have hlim : Tendsto (fun _ : Unit →₀ ℕ ↦ (1 : ℝ)) cofinite (𝓝 0) := by
    refine f.2.congr' (Eventually.of_forall fun t ↦ ?_)
    simp [hfnorm t, Finsupp.prod]
  have : Infinite (Unit →₀ ℕ) :=
    Infinite.of_injective (fun n : ℕ ↦ Finsupp.single () n) fun m n h ↦ by
      simpa using congrArg (fun s : Unit →₀ ℕ ↦ s ()) h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

end AlgebraicBijectionFailsSurjectivity

section BoundedSectionNotIsometry

variable (p : ℕ) [Fact p.Prime]

/-- The radius `2` is positive. -/
local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- Evaluating `f ∈ ℚ_[p]{Y/2}` at `Y = 0` and `Y = 1` gives a ring homomorphism
`ℚ_[p]{Y/2} →+* ℚ_[p] × ℚ_[p]`. -/
noncomputable def evalZeroOneHom :
    IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ)) →+* ℚ_[p] × ℚ_[p] :=
  RingHom.prod
    ((MvPowerSeries.constantCoeff : MvPowerSeries (Fin 1) ℚ_[p] →+* ℚ_[p]).comp
      (IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ))).subtype)
    (restrictedEval₂ (RingHom.id ℚ_[p]) (fun _ : Fin 1 ↦ (1 : ℚ_[p]))
      (fun _ ↦ le_rfl) (fun _ ↦ by norm_num))

/-- `evalZeroOneHom` is contractive for the Gauss norm at radius `2` and the `max` norm on
`ℚ_[p] × ℚ_[p]`. -/
theorem norm_evalZeroOneHom_le
    (f : IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ))) :
    ‖evalZeroOneHom p f‖ ≤ ‖f‖ := by
  rw [Prod.norm_def]
  exact max_le (norm_constantCoeff_le f) (norm_restrictedEval₂_le _ _ _ _ f)

/-- Linear interpolation `(u, v) ↦ u + (v - u) Y` as an additive homomorphism
`ℚ_[p] × ℚ_[p] →+ ℚ_[p]{Y/2}`. -/
noncomputable def interpZeroOneAddHom :
    ℚ_[p] × ℚ_[p] →+ IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ)) :=
  (algebraMap ℚ_[p] _).toAddMonoidHom.comp (AddMonoidHom.fst ℚ_[p] ℚ_[p]) +
    (AddMonoidHom.mulRight ⟨X 0, isRestricted_X _ 0⟩).comp
      ((algebraMap ℚ_[p] _).toAddMonoidHom.comp
        (AddMonoidHom.snd ℚ_[p] ℚ_[p] - AddMonoidHom.fst ℚ_[p] ℚ_[p]))

/-- `interpZeroOneAddHom` is a right inverse to `evalZeroOneHom`. -/
theorem rightInverse_interpZeroOneAddHom :
    Function.RightInverse (interpZeroOneAddHom p) (evalZeroOneHom p) := by
  rintro ⟨u, v⟩
  ext
  · simp [evalZeroOneHom, interpZeroOneAddHom]
  · simp [evalZeroOneHom, interpZeroOneAddHom]

/-- `interpZeroOneAddHom` is `2`-bounded for the `max` norm on `ℚ_[p] × ℚ_[p]` and the Gauss norm on
`ℚ_[p]{Y/2}`. -/
theorem norm_interpZeroOneAddHom_le (x : ℚ_[p] × ℚ_[p]) :
    ‖interpZeroOneAddHom p x‖ ≤ 2 * ‖x‖ := by
  have hu : ‖algebraMap ℚ_[p]
      (IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ))) x.1‖ ≤ 2 * ‖x‖ := by
    rw [norm_algebraMap_isRestrictedSubring, Prod.norm_def]
    linarith [le_max_left ‖x.1‖ ‖x.2‖, norm_nonneg x.1]
  have hv : ‖algebraMap ℚ_[p]
      (IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ))) (x.2 - x.1) *
        ⟨X 0, isRestricted_X _ 0⟩‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul, norm_algebraMap_isRestrictedSubring, norm_X]
    have hsub : ‖x.2 - x.1‖ ≤ ‖x‖ := by
      rw [Prod.norm_def, max_comm, sub_eq_add_neg]
      simpa only [norm_neg] using IsUltrametricDist.norm_add_le_max x.2 (-x.1)
    linarith
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)

/-- Every preimage of `(0, 1)` under `evalZeroOneHom` in `ℚ_[p]{Y/2}` has Gauss norm at least `2`,
strictly larger than `‖((0, 1) : ℚ_[p] × ℚ_[p])‖ = 1`. -/
theorem two_le_norm_of_evalZeroOneHom_eq
    {f : IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ (2 : ℝ))}
    (hf : evalZeroOneHom p f = (0, 1)) : 2 ≤ ‖f‖ := by
  have h0 : constantCoeff (f : MvPowerSeries (Fin 1) ℚ_[p]) = 0 := congrArg Prod.fst hf
  have h1 : restrictedEval₂ (RingHom.id ℚ_[p]) (fun _ : Fin 1 ↦ (1 : ℚ_[p]))
      (fun _ ↦ le_rfl) (fun _ ↦ by norm_num) f = 1 := congrArg Prod.snd hf
  have hle : ‖restrictedEval₂ (RingHom.id ℚ_[p]) (fun _ : Fin 1 ↦ (1 : ℚ_[p]))
      (fun _ ↦ le_rfl) (fun _ ↦ by norm_num) f‖ ≤ ‖f‖ / 2 := by
    rw [restrictedEval₂_apply, TauCeti.Huber.weightedEval_def]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (div_nonneg (norm_nonneg f) zero_le_two) fun t ↦ ?_
    by_cases ht : t = 0
    · subst ht
      have hterm : TauCeti.Huber.weightedEvalTerm (RingHom.id ℚ_[p])
          (fun _ : Fin 1 ↦ (1 : ℚ_[p])) f 0 = 0 := by
        simp [TauCeti.Huber.weightedEvalTerm_def, h0]
      rw [hterm, norm_zero]
      exact div_nonneg (norm_nonneg f) zero_le_two
    · have ht0 : t 0 ≠ 0 := fun h ↦ ht (Finsupp.ext fun i ↦ by fin_cases i; exact h)
      have hpow : (2 : ℝ) ≤ t.prod (fun _ n ↦ (2 : ℝ) ^ n) := by
        rw [Finsupp.prod_of_support_subset t (Finset.subset_univ _)
          (fun _ n ↦ (2 : ℝ) ^ n) (fun _ _ ↦ pow_zero 2), Fin.prod_univ_one]
        exact le_self_pow₀ (by norm_num) ht0
      have hterm : ‖TauCeti.Huber.weightedEvalTerm (RingHom.id ℚ_[p])
          (fun _ : Fin 1 ↦ (1 : ℚ_[p])) f t‖ =
          ‖coeff t (f : MvPowerSeries (Fin 1) ℚ_[p])‖ := by
        simp [TauCeti.Huber.weightedEvalTerm_def]
      have hcoeff := norm_coeff_mul_prod_le f t
      nlinarith [norm_nonneg (coeff t (f : MvPowerSeries (Fin 1) ℚ_[p]))]
  rw [h1, norm_one] at hle
  linarith

/-- For every variable set `σ` and positive polyradius `c : σ → ℝ`, `evalZeroOneHom` induces an open
quotient map on restricted power series. -/
theorem isOpenQuotientMap_restrictedMap_evalZeroOneHom
    {σ : Type*} {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    IsOpenQuotientMap (restrictedMap (c := c) (evalZeroOneHom p)
      (fun f ↦ (one_mul ‖f‖).symm ▸ norm_evalZeroOneHom_le p f)) :=
  isOpenQuotientMap_restrictedMap (evalZeroOneHom p) _ fun x ↦
    ⟨interpZeroOneAddHom p x, rightInverse_interpZeroOneAddHom p x, norm_interpZeroOneAddHom_le p x⟩

/-- For every variable set `σ` and polyradius `c : σ → ℝ`,
`restrictedAddMap (interpZeroOneAddHom p)` is an additive right inverse to
`restrictedMap (evalZeroOneHom p)`. -/
theorem rightInverse_restrictedAddMap_interpZeroOneAddHom {σ : Type*} {c : σ → ℝ} :
    Function.RightInverse
      (restrictedAddMap (c := c) (interpZeroOneAddHom p) (norm_interpZeroOneAddHom_le p))
      (restrictedMap (c := c) (evalZeroOneHom p)
        (fun f ↦ (one_mul ‖f‖).symm ▸ norm_evalZeroOneHom_le p f)) :=
  rightInverse_restrictedAddMap _ _ _ _ (rightInverse_interpZeroOneAddHom p)

/-- For every variable set `σ` and positive polyradius `c : σ → ℝ`, the first-isomorphism
equivalence induced by `restrictedMap (evalZeroOneHom p)` is **not** an isometry, even though
`evalZeroOneHom p` admits the `2`-bounded additive section `interpZeroOneAddHom p`. -/
theorem not_isometry_quotientKerEquivOfSurjective_restrictedMap_evalZeroOneHom
    {σ : Type*} {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    ¬ Isometry (RingHom.quotientKerEquivOfSurjective
      (f := restrictedMap (c := c) (evalZeroOneHom p)
        (fun f ↦ (one_mul ‖f‖).symm ▸ norm_evalZeroOneHom_le p f))
      (isOpenQuotientMap_restrictedMap_evalZeroOneHom p).surjective) := by
  rw [isometry_quotientKerEquivOfSurjective_restrictedMap_iff]
  rintro ⟨-, hsharp⟩
  obtain ⟨f, hf, hlt⟩ := hsharp (0, 1) (1 / 2) (by norm_num)
  have hnorm01 : ‖((0, 1) : ℚ_[p] × ℚ_[p])‖ = 1 := by simp [Prod.norm_def]
  linarith [two_le_norm_of_evalZeroOneHom_eq p hf]

end BoundedSectionNotIsometry

section TateQuotientExactLifts

open TauCeti.Huber

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {τ : Type*} [Finite τ] {d : τ → ℝ} [∀ j, Fact (0 < d j)]
  (I : Ideal (IsRestricted.subring (R := K) d))

/-- **Exact Gauss-norm-attaining lifts over any Tate quotient algebra.** For any ideal `I` of
`K{Y/d}`, any second variable set `σ`, and any positive polyradius `c : σ → ℝ`, every restricted
series `G` over `K{Y/d} ⧸ I` lifts along `restrictedMap (Ideal.Quotient.mk I)` to a restricted
series `F` over `K{Y/d}` of the exact same Gauss norm. -/
theorem exists_restrictedMap_mk_eq_and_norm_eq_tateQuotient
    {σ : Type*} {c : σ → ℝ} [∀ i, Fact (0 < c i)]
    (G : IsRestricted.subring (R := IsRestricted.subring (R := K) d ⧸ I) c) :
    ∃ F : IsRestricted.subring (R := IsRestricted.subring (R := K) d) c,
      restrictedMap (Ideal.Quotient.mk I)
        (fun a ↦ (one_mul ‖a‖).symm ▸ Ideal.Quotient.norm_mk_le_norm I a) F = G ∧
      ‖F‖ = ‖G‖ :=
  exists_restrictedMap_eq_and_norm_eq (Ideal.Quotient.mk I) _
    (Ideal.Quotient.norm_mk_le_norm I)
    (fun q ↦ let ⟨f, hf, hnorm⟩ := I.exists_mk_eq_and_norm_eq_isRestricted_subring q
      ⟨f, hf, hnorm.le⟩)
    G

/-- **Isometric quotient equivalence over any Tate quotient algebra.** For any ideal `I` of
`K{Y/d}`, any second variable set `σ`, and any positive polyradius `c : σ → ℝ`, reducing
coefficients modulo `I` induces an isometric ring isomorphism
`(K{Y/d}){X/c} ⧸ ker ≃+* (K{Y/d} ⧸ I){X/c}`. -/
theorem isometry_quotientKerEquivOfSurjective_restrictedMap_mk_tateQuotient
    {σ : Type*} {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    Isometry (RingHom.quotientKerEquivOfSurjective
      (f := restrictedMap (c := c) (Ideal.Quotient.mk I)
        (fun a ↦ (one_mul ‖a‖).symm ▸ Ideal.Quotient.norm_mk_le_norm I a))
      (I.isOpenQuotientMap_restrictedMap_mk (c := c)).surjective) :=
  I.isometry_quotientKerEquivOfSurjective_restrictedMap_mk

/-- **Completed Huber counterpart over Tate quotient algebras.** For any `k : ℕ`, every element of
the completed Huber algebra `(K{Y/d} ⧸ I)⟨X₁, …, Xₖ⟩` lifts along `weightedMapCompletion` to an
element of `(K{Y/d})⟨X₁, …, Xₖ⟩` of the exact same compared Gauss norm. -/
theorem exists_weightedMapCompletion_eq_and_norm_eq_tateQuotient {k : ℕ}
    (G : restrictedMvPowerSeriesCompletion k (IsRestricted.subring (R := K) d ⧸ I)) :
    ∃ F : restrictedMvPowerSeriesCompletion k (IsRestricted.subring (R := K) d),
      weightedMapCompletion (QuotientRing.isOpenQuotientMap_mk I).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp) F = G ∧
      ‖restrictedMvPowerSeriesCompletionGaussEquiv F‖ =
        ‖restrictedMvPowerSeriesCompletionGaussEquiv G‖ :=
  exists_weightedMapCompletion_eq_and_norm_eq
    (QuotientRing.isOpenQuotientMap_mk I).continuous
    (fun a ↦ (one_mul ‖a‖).symm ▸ Ideal.Quotient.norm_mk_le_norm I a)
    (Ideal.Quotient.norm_mk_le_norm I)
    (fun q ↦ let ⟨f, hf, hnorm⟩ := I.exists_mk_eq_and_norm_eq_isRestricted_subring q
      ⟨f, hf, hnorm.le⟩)
    G

end TateQuotientExactLifts

end TauCeti.Examples.TateAlgebraQuotient
