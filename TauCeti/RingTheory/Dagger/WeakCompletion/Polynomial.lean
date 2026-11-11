/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Basic
public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Basic

/-!
# Weak completions of polynomial algebras

The weak completion of a polynomial algebra over the valuation unit ball of a complete
ultrametric field is the integral Monsky–Washnitzer algebra. The comparison preserves
polynomials and identifies the degree-growth definition with overconvergence. It is the
polynomial case used to present weak completions of finitely generated algebras.

## References

* M. van der Put, *The cohomology of Monsky and Washnitzer*, §2, (2.1)–(2.2).
* P. Monsky and G. Washnitzer, *Formal cohomology. I*, §2.
-/

public section

namespace TauCeti.Dagger

open MvPolynomial _root_.MvPowerSeries Finset

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "O" => Subring.unitClosedBall K
local notation "P" => MvPolynomial σ O
local notation "W" => intWashnitzerAlgebra σ K
local notation "T" => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))
local notation "T₀" => Subring.unitClosedBall T

namespace weakCompletion

omit [CompleteSpace K] in
private theorem polynomial_span_le (π : O) :
    Ideal.span {algebraMap O P π} ≤
      (Ideal.span {algebraMap O W π}).comap (intWashnitzerAlgebra.ofMvPolynomial σ K) := by
  simp only [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_span_singleton_self _

omit [CompleteSpace K] in
private theorem polynomial_quotient_bijective {π : O} (hπ : π ≠ 0) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (Ideal.span {algebraMap O W π} ^ n)
      (intWashnitzerAlgebra.ofMvPolynomial σ K).toRingHom
      ((Ideal.pow_right_mono (polynomial_span_le (σ := σ) π) n).trans
        (Ideal.le_comap_pow _ n))) := by
  have hπn : π ^ n ≠ 0 := pow_ne_zero n hπ
  refine ⟨Ideal.quotientMap_injective' (fun p hp ↦ ?_), fun z ↦ ?_⟩
  · have hm : intWashnitzerAlgebra.ofMvPolynomial σ K p ∈
        Ideal.span {algebraMap O W (π ^ n)} := by
      simpa only [Ideal.mem_comap, Ideal.span_singleton_pow, map_pow,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hp
    have hk : p ∈ RingHom.ker ((Ideal.Quotient.mkₐ O
        (Ideal.span {algebraMap O W (π ^ n)})).comp
        (intWashnitzerAlgebra.ofMvPolynomial σ K)) := by
      simpa only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem] using hm
    rw [intWashnitzerAlgebra.ker_mkₐ_comp_ofMvPolynomial] at hk
    simpa only [Ideal.span_singleton_pow, MvPolynomial.algebraMap_eq, map_pow] using hk
  · obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp⟩ := intWashnitzerAlgebra.surjective_mkₐ_comp_ofMvPolynomial hπn
      (Ideal.Quotient.mk _ w)
    refine ⟨Ideal.Quotient.mk _ p, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.span_singleton_pow, ← map_pow]
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hp

/-- The parameter-adic completion of the polynomial algebra is the integral Tate algebra.
The comparison extends the inclusion of polynomials. -/
noncomputable def polynomialAdicCompletionEquiv {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    piAdicCompletion π P ≃+* T₀ :=
  (RingEquiv.ofBijective _ (AdicCompletion.mapₐ_bijective
    (intWashnitzerAlgebra.ofMvPolynomial σ K) (polynomial_span_le π)
    (polynomial_quotient_bijective hπ))).trans
    (intWashnitzerAlgebra.adicCompletionEquiv σ hπ hπ1)

/-- On polynomials, the completion comparison is the usual inclusion into restricted series. -/
@[simp]
theorem polynomialAdicCompletionEquiv_of {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) (p : P) :
    polynomialAdicCompletionEquiv hπ hπ1
        (AdicCompletion.of (Ideal.span {MvPolynomial.C π}) P p) =
      intWashnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.ofMvPolynomial σ K p) := by
  exact (congrArg (intWashnitzerAlgebra.adicCompletionEquiv σ hπ hπ1)
    (AdicCompletion.mapₐ_of (intWashnitzerAlgebra.ofMvPolynomial σ K)
      (polynomial_span_le π) p)).trans (intWashnitzerAlgebra.adicCompletionEquiv_of hπ hπ1 _)

private theorem norm_sub_le_of_eval_eq {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : piAdicCompletion π P) (p : P) (n : ℕ)
    (hz : AdicCompletion.evalₐ _ n z = Ideal.Quotient.mk _ p) :
    ‖((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) -
      intWashnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.ofMvPolynomial σ K p)‖ ≤
        ‖(π : K)‖ ^ n := by
  let a : W := algebraMap O W π
  let J : Ideal T₀ := Ideal.span {intWashnitzerAlgebra.toTate σ K a}
  let e := intWashnitzerAlgebra.adicCompletionEquiv σ hπ hπ1
  let w := AdicCompletion.mapₐ (intWashnitzerAlgebra.ofMvPolynomial σ K)
    (polynomial_span_le π) z
  have hw : AdicCompletion.evalₐ _ n w =
      Ideal.Quotient.mk _ (intWashnitzerAlgebra.ofMvPolynomial σ K p) := by
    rw [AdicCompletion.evalₐ_mapₐ, hz, Ideal.quotientMap_mk]
    rfl
  have he : Ideal.Quotient.mk (J ^ n) (e w) =
      Ideal.Quotient.mk (J ^ n)
        (intWashnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.ofMvPolynomial σ K p)) := by
    rw [intWashnitzerAlgebra.mk_adicCompletionEquiv, hw, Ideal.quotientMap_mk]
  have hm := Ideal.Quotient.eq.mp he
  let u : NormedRing.PseudoUniformizer T :=
    .ofAlgebraMap (c := (π : K)) (by simpa using hπ) hπ1
  have hu : u.toUnitClosedBall = intWashnitzerAlgebra.toTate σ K a := by
    apply Subtype.ext
    simp [NormedRing.PseudoUniformizer.coe_toUnitClosedBall, u, a]
  dsimp only [J] at hm
  rw [← hu] at hm
  have hb := (NormedRing.PseudoUniformizer.mem_span_toUnitClosedBall_pow_iff u n).mp hm
  simpa only [polynomialAdicCompletionEquiv, RingEquiv.trans_apply,
    RingEquiv.ofBijective_apply, e, w, u, AddSubgroupClass.coe_sub,
    NormedRing.PseudoUniformizer.coe_unit_ofAlgebraMap, norm_algebraMap'] using hb

private theorem eval_eq_of_norm_sub_le {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : piAdicCompletion π P) (p : P) (n : ℕ)
    (hz : ‖((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) -
      intWashnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.ofMvPolynomial σ K p)‖ ≤
        ‖(π : K)‖ ^ n) :
    AdicCompletion.evalₐ _ n z = Ideal.Quotient.mk _ p := by
  let u : NormedRing.PseudoUniformizer T :=
    .ofAlgebraMap (c := (π : K)) (by simpa using hπ) hπ1
  have hu : u.toUnitClosedBall = intWashnitzerAlgebra.toTate σ K (algebraMap O W π) := by
    apply Subtype.ext
    simp [NormedRing.PseudoUniformizer.coe_toUnitClosedBall, u]
  have hm : polynomialAdicCompletionEquiv hπ hπ1 z -
      intWashnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.ofMvPolynomial σ K p) ∈
        Ideal.span {u.toUnitClosedBall} ^ n := by
    apply (NormedRing.PseudoUniformizer.mem_span_toUnitClosedBall_pow_iff u n).mpr
    simpa only [AddSubgroupClass.coe_sub, u,
      NormedRing.PseudoUniformizer.coe_unit_ofAlgebraMap, norm_algebraMap'] using hz
  rw [hu] at hm
  have he := Ideal.Quotient.eq.mpr hm
  rw [polynomialAdicCompletionEquiv, RingEquiv.trans_apply, RingEquiv.ofBijective_apply,
    intWashnitzerAlgebra.mk_adicCompletionEquiv, AdicCompletion.evalₐ_mapₐ] at he
  have hi := (intWashnitzerAlgebra.quotientMap_toTate_bijective (σ := σ) hπ hπ1 n).1
  have he' := hi (he.trans (Ideal.quotientMap_mk
    (f := intWashnitzerAlgebra.toTate σ K)
    (H := (Ideal.pow_right_mono intWashnitzerAlgebra.span_algebraMap_le_comap_toTate n).trans
      (Ideal.le_comap_pow _ n))
    (x := intWashnitzerAlgebra.ofMvPolynomial σ K p)).symm)
  apply (polynomial_quotient_bijective (σ := σ) hπ n).1
  simpa only [Ideal.quotientMap_mk, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using he'

variable [Finite σ]

private theorem integral_of_mem {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : piAdicCompletion π P) (hz : z ∈ weakCompletion π P) :
    (((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) : MvPowerSeries σ K) ∈ W := by
  classical
  have hx : Algebra.adjoin O (Set.range (MvPolynomial.X : σ → P)) = ⊤ :=
    MvPolynomial.adjoin_range_X
  obtain ⟨c, Q, hQ, hz⟩ := (mem_weakCompletion_iff π hx).mp hz
  have hπK : (π : K) ≠ 0 := by simpa using hπ
  apply (mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow
    (norm_pos_iff.mpr hπK) hπ1).mpr
  refine ⟨c + 1, Nat.succ_pos _, fun t ↦ ?_⟩
  let k := t.degree / (c + 1)
  by_cases hk : k = 0
  · dsimp only [k] at hk
    rw [hk, pow_zero]
    exact (MvPowerSeries.norm_coeff_le_norm (polynomialAdicCompletionEquiv hπ hπ1 z : T) t).trans
        (Subring.mem_unitClosedBall.mp (polynomialAdicCompletionEquiv hπ hπ1 z).property)
  let p : P := ∑ j ∈ range k, algebraMap O P π ^ j * Q j
  have hp : p.coeff t = 0 := by
    simp only [p, MvPolynomial.algebraMap_eq, ← map_pow, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_C_mul]
    apply Finset.sum_eq_zero
    intro j hj
    have hdeg : (Q j).totalDegree < t.degree := by
      have hdiv : (c + 1) * k ≤ t.degree := Nat.mul_div_le _ _
      have hj' := mem_range.mp hj
      have hk' : 0 < k := Nat.pos_of_ne_zero hk
      nlinarith [hQ j]
    rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt hdeg, mul_zero]
  have hb := norm_sub_le_of_eval_eq hπ hπ1 z p k (by
    simpa only [MvPolynomial.aeval_X_left_apply, p] using hz k)
  have hc := (MvPowerSeries.norm_coeff_le_norm
    ((polynomialAdicCompletionEquiv hπ hπ1 z : T) -
      (intWashnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.ofMvPolynomial σ K p) : T)) t).trans hb
  simpa only [AddSubgroupClass.coe_sub, map_sub, intWashnitzerAlgebra.coe_toTate,
    intWashnitzerAlgebra.coeff_ofMvPolynomial, hp, Subring.coe_zero, sub_zero] using hc

private theorem mem_of_coefficient_hasSum {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : piAdicCompletion π P) (c : ℕ) (Q : ℕ → P)
    (hdeg : ∀ j, (Q j).totalDegree ≤ c * (j + 1))
    (hsum : ∀ t, HasSum (fun j ↦ (π : K) ^ j * ((Q j).coeff t : K))
      (MvPowerSeries.coeff t
        (((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) : MvPowerSeries σ K))) :
    z ∈ weakCompletion π P := by
  classical
  have hx : Algebra.adjoin O (Set.range (MvPolynomial.X : σ → P)) = ⊤ :=
    MvPolynomial.adjoin_range_X
  rw [← SetLike.mem_coe, coe_weakCompletion π _ hx]
  refine mem_weakCompletionSet_iff.mpr ⟨c, Q, hdeg, fun k ↦ ?_⟩
  rw [MvPolynomial.aeval_X_left]
  apply eval_eq_of_norm_sub_le hπ hπ1
  apply (MvPowerSeries.norm_le_iff (pow_nonneg (norm_nonneg _) k)).mpr
  intro t
  -- Coefficientwise convergence suffices: every tail coefficient is bounded by ‖π‖^k.
  have htail : HasSum (fun j ↦ (π : K) ^ (j + k) * ((Q (j + k)).coeff t : K))
      (MvPowerSeries.coeff t
        (((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) : MvPowerSeries σ K) -
          ∑ j ∈ range k, (π : K) ^ j * ((Q j).coeff t : K)) := by
    apply (hasSum_nat_add_iff (f := fun j ↦ (π : K) ^ j * ((Q j).coeff t : K)) k).mpr
    simpa only [sub_add_cancel] using hsum t
  have hb := le_of_tendsto' htail.norm (fun s ↦
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) k)
      (fun j _ ↦ (by
        rw [norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (by positivity)
          (Subring.mem_unitClosedBall.mp ((Q (j + k)).coeff t).property)).trans
          (pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.le_add_left k j)))))
  simp only [AddSubgroupClass.coe_sub, map_sub, intWashnitzerAlgebra.coe_toTate,
    intWashnitzerAlgebra.coeff_ofMvPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.algebraMap_eq, ← map_pow, MvPolynomial.coeff_C_mul,
    AlgHom.id_apply, one_pow, Finsupp.prod_fun_one, mul_one]
  have he : ((∑ j ∈ range k, π ^ j * (Q j).coeff t : O) : K) =
      ∑ j ∈ range k, (π : K) ^ j * ((Q j).coeff t : K) := by
    exact (map_sum (Subring.unitClosedBall K).subtype _ _).trans (by
      simp only [map_mul, map_pow, Subring.subtype_apply])
  rwa [he]

private theorem mem_of_integral {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : piAdicCompletion π P)
    (hz : (((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) : MvPowerSeries σ K) ∈ W) :
    z ∈ weakCompletion π P := by
  classical
  have hπK : (π : K) ≠ 0 := by simpa using hπ
  open scoped MvPowerSeries.WithPiTopology in
    obtain ⟨c, Q, hQ1, hQdeg, hsum⟩ :=
      (mem_intWashnitzerAlgebra_iff_exists_hasSum hπK hπ1).mp hz
  have hQrange (j : ℕ) : ∃ p : P, p.map (Subring.unitClosedBall K).subtype = Q j := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro a ha
    obtain ⟨t, ht, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    exact ⟨⟨(Q j).coeff t, Subring.mem_unitClosedBall.mpr (hQ1 j t)⟩, rfl⟩
  choose Q' hQ' using hQrange
  apply mem_of_coefficient_hasSum hπ hπ1 z c Q'
  · intro j
    have hh := hQdeg j
    rw [← hQ' j] at hh
    simpa only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective _
      (Subring.unitClosedBall K).subtype_injective] using hh
  · intro t
    have ht := MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff.mp hsum t
    simpa only [MvPowerSeries.coeff_C_mul, MvPolynomial.coeff_coe, ← hQ',
      MvPolynomial.coeff_map, Subring.subtype_apply] using ht

/-- An element of the completed polynomial algebra is weakly overconvergent exactly when
its restricted power series is integral and overconvergent. -/
@[simp]
theorem mem_polynomial_iff {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : piAdicCompletion π P) :
    z ∈ weakCompletion π P ↔
      (((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) : MvPowerSeries σ K) ∈ W :=
  ⟨integral_of_mem hπ hπ1 z, mem_of_integral hπ hπ1 z⟩

/-- The weak completion of the polynomial algebra over the valuation unit ball is the integral
Monsky–Washnitzer algebra. No discreteness of the valuation is required. -/
noncomputable def polynomialEquiv {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    weakCompletion π P ≃ₐ[O] W where
  toFun z := ⟨((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T),
    integral_of_mem (σ := σ) hπ hπ1 z z.property⟩
  invFun f := ⟨(polynomialAdicCompletionEquiv hπ hπ1).symm
    (intWashnitzerAlgebra.toTate σ K f), mem_of_integral hπ hπ1 _ (by
      simpa only [RingEquiv.apply_symm_apply, intWashnitzerAlgebra.coe_toTate] using f.property)⟩
  left_inv z := Subtype.ext <| (polynomialAdicCompletionEquiv hπ hπ1).injective <| by
    apply Subtype.ext
    apply Subtype.ext
    simp only [RingEquiv.apply_symm_apply, intWashnitzerAlgebra.coe_toTate]
  right_inv f := Subtype.ext <| by
    simp only [RingEquiv.apply_symm_apply, intWashnitzerAlgebra.coe_toTate]
  map_mul' z w := Subtype.ext <| by simp only [map_mul, MulMemClass.coe_mul]
  map_add' z w := Subtype.ext <| by
    simp only [map_add, AddMemClass.coe_add]
  commutes' a := by
    apply Subtype.ext
    dsimp only
    rw [← (of π P).commutes, coe_of]
    exact (congrArg (fun x : T₀ ↦ ((x : T) : MvPowerSeries σ K))
      (polynomialAdicCompletionEquiv_of hπ hπ1 (algebraMap O P a))).trans (by
        rw [intWashnitzerAlgebra.coe_toTate, AlgHom.commutes])

/-- The polynomial weak-completion comparison is the restriction of the adic comparison
on the underlying restricted power series. -/
@[simp]
theorem coe_polynomialEquiv {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (z : weakCompletion π P) :
    (polynomialEquiv hπ hπ1 z : MvPowerSeries σ K) =
      (((polynomialAdicCompletionEquiv hπ hπ1 z : T₀) : T) : MvPowerSeries σ K) :=
  (rfl)

/-- The weak-completion comparison fixes every polynomial, not just its residue modulo the
parameter. -/
@[simp]
theorem polynomialEquiv_of {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) (p : P) :
    polynomialEquiv hπ hπ1 (of π P p) = intWashnitzerAlgebra.ofMvPolynomial σ K p := by
  apply Subtype.ext
  rw [coe_polynomialEquiv, coe_of]
  exact (congrArg (fun x : T₀ ↦ ((x : T) : MvPowerSeries σ K))
    (polynomialAdicCompletionEquiv_of hπ hπ1 p)).trans (intWashnitzerAlgebra.coe_toTate _)

/-- The inverse comparison takes an integral polynomial to its weak-completion image. -/
@[simp]
theorem polynomialEquiv_symm_ofMvPolynomial {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) (p : P) :
    (polynomialEquiv hπ hπ1).symm (intWashnitzerAlgebra.ofMvPolynomial σ K p) = of π P p := by
  apply (polynomialEquiv hπ hπ1).injective
  simp

end weakCompletion

end TauCeti.Dagger
