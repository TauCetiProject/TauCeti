/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra

/-!
# The integral Monsky–Washnitzer algebra

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1` and closed unit ball
`R° = {a | ‖a‖ ≤ 1}`. The *integral Monsky–Washnitzer algebra* is the subring

```text
R°⟨X⟩† = R⟨X⟩† ∩ R°[[X]]  ⊆  R[[X]]
```

of overconvergent power series with coefficients in `R°`. For a complete discretely valued field
`K` with ring of integers `O_K`, the ring `O_K⟨X⟩†` is the basic object of Monsky and Washnitzer's
formal cohomology: weak completions of finitely generated `O_K`-algebras are its quotients, and
inverting a uniformiser recovers the Monsky–Washnitzer algebra `K⟨X⟩†`. Its elements are the
overconvergent series of Gauss norm at most one.

## Main definitions

* `TauCeti.Dagger.intWashnitzerAlgebra σ R`: the subring `R°⟨X⟩†` of overconvergent series with
  coefficients of norm at most one.
* `TauCeti.Dagger.intWashnitzerAlgebra.toWashnitzerAlgebra`: its inclusion into `R⟨X⟩†`.

## Main results

* `TauCeti.Dagger.mem_intWashnitzerAlgebra_iff`: `f ∈ R°⟨X⟩†` iff `f` is overconvergent and all
  its coefficients have norm at most one; equivalently
  (`TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_norm_toTate_le_one`), `f` lies in the closed unit
  ball for the Gauss norm of the Tate algebra.
* `TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow`: the
  Monsky–Washnitzer degree growth condition in coefficient form. For finitely many variables and
  any `0 < q < 1`, `f ∈ R°⟨X⟩†` iff `‖aᵥ‖ ≤ q ^ ⌊|ν| / c⌋` for some integer `c > 0`.
* `TauCeti.Dagger.mem_intWashnitzerAlgebra_iff_exists_hasSum`: the degree growth condition as
  stated by Monsky and Washnitzer. Over an ultrametric normed field `K` with an element `π` of norm
  in `(0, 1)`, `f ∈ K°⟨X⟩†` iff `f = ∑ⱼ πʲ Pⱼ` for polynomials `Pⱼ` with integral coefficients
  and `deg Pⱼ ≤ c (j + 1)` for some `c`.
* `TauCeti.Dagger.mem_washnitzerAlgebra_iff_exists_C_pow_mul_mem`: `K⟨X⟩† = K°⟨X⟩†[1/π]`, that
  is, every overconvergent series becomes integral after multiplication by a power of `π`.
* `TauCeti.Dagger.isUnit_intWashnitzerAlgebra_iff`: over a complete ultrametric normed field, `f`
  is a unit of `K°⟨X⟩†` iff its constant coefficient has norm one and all other coefficients have
  norm less than one.
* `TauCeti.Dagger.mem_jacobson_bot_intWashnitzerAlgebra_iff`: the Jacobson radical of
  `K°⟨X⟩†` consists of the series all of whose coefficients have norm less than one. In
  particular every constant `π` with `‖π‖ < 1` lies in it, so `1 + π f` is a unit for every
  `f ∈ K°⟨X⟩†`.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006),
  §2.4.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

section Defs

variable (σ R : Type*) [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

/-- The **integral Monsky–Washnitzer algebra** `R°⟨X⟩† = R⟨X⟩† ∩ R°[[X]]`: the overconvergent
power series whose coefficients lie in the closed unit ball `R°` of `R`. -/
noncomputable def intWashnitzerAlgebra : Subring (MvPowerSeries σ R) :=
  (washnitzerAlgebra σ R).toSubring ⊓
    (MvPowerSeries.map (Subring.unitClosedBall R).subtype).range

variable {σ R}

/-- A series lies in `R°⟨X⟩†` iff it is overconvergent and all its coefficients have norm at most
one. -/
theorem mem_intWashnitzerAlgebra_iff {f : MvPowerSeries σ R} :
    f ∈ intWashnitzerAlgebra σ R ↔ f ∈ washnitzerAlgebra σ R ∧ ∀ t, ‖coeff t f‖ ≤ 1 := by
  refine Subring.mem_inf.trans (and_congr Iff.rfl ⟨?_, fun h ↦ ?_⟩)
  · rintro ⟨g, rfl⟩ t
    rw [coeff_map]
    exact Subring.mem_unitClosedBall.1 (coeff t g).2
  · let g : MvPowerSeries σ (Subring.unitClosedBall R) := fun t ↦
      ⟨coeff t f, Subring.mem_unitClosedBall.2 (h t)⟩
    exact ⟨g, MvPowerSeries.ext fun t ↦ by rw [coeff_map]; rfl⟩

/-- The integral Monsky–Washnitzer algebra lies in the Monsky–Washnitzer algebra. -/
theorem intWashnitzerAlgebra_le :
    intWashnitzerAlgebra σ R ≤ (washnitzerAlgebra σ R).toSubring :=
  inf_le_left

/-- A constant series lies in `R°⟨X⟩†` iff it has norm at most one. -/
@[simp]
theorem C_mem_intWashnitzerAlgebra_iff {a : R} :
    C a ∈ intWashnitzerAlgebra σ R ↔ ‖a‖ ≤ 1 := by
  classical
  refine mem_intWashnitzerAlgebra_iff.trans
    ⟨fun h ↦ by simpa using h.2 0, fun h ↦ ⟨C_mem_washnitzerAlgebra a, fun t ↦ ?_⟩⟩
  rw [coeff_C]
  split_ifs
  · exact h
  · simp

/-- A polynomial lies in `R°⟨X⟩†` iff all its coefficients have norm at most one. -/
@[simp]
theorem coe_mem_intWashnitzerAlgebra_iff {p : MvPolynomial σ R} :
    (p : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R ↔ ∀ t, ‖p.coeff t‖ ≤ 1 := by
  simp [mem_intWashnitzerAlgebra_iff, coe_mem_washnitzerAlgebra]

/-- The variables lie in `R°⟨X⟩†`. -/
theorem X_mem_intWashnitzerAlgebra (i : σ) :
    (MvPowerSeries.X i : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R := by
  classical
  refine mem_intWashnitzerAlgebra_iff.2 ⟨by simpa using (washnitzerAlgebra.X σ R i).2, fun t ↦ ?_⟩
  rw [coeff_X]
  split_ifs <;> simp

/-- With no variables, `R°⟨⟩†` consists of the constants of norm at most one. -/
theorem mem_intWashnitzerAlgebra_iff_of_isEmpty [IsEmpty σ] {f : MvPowerSeries σ R} :
    f ∈ intWashnitzerAlgebra σ R ↔ ‖constantCoeff f‖ ≤ 1 := by
  rw [mem_intWashnitzerAlgebra_iff, washnitzerAlgebra_eq_top]
  refine ⟨fun h ↦ by simpa using h.2 0, fun h ↦ ⟨trivial, fun t ↦ ?_⟩⟩
  rwa [Subsingleton.elim t 0, coeff_zero_eq_constantCoeff_apply]

/-- **Integrality is the Gauss unit ball.** An overconvergent series lies in `R°⟨X⟩†` iff its
Gauss norm in the Tate algebra is at most one. -/
theorem mem_intWashnitzerAlgebra_iff_norm_toTate_le_one {f : washnitzerAlgebra σ R} :
    (f : MvPowerSeries σ R) ∈ intWashnitzerAlgebra σ R ↔
      ‖washnitzerAlgebra.toTate σ R f‖ ≤ 1 := by
  rw [mem_intWashnitzerAlgebra_iff, MvPowerSeries.norm_le_iff zero_le_one]
  simp [f.2]

namespace intWashnitzerAlgebra

variable (σ R) in
/-- The inclusion of the integral Monsky–Washnitzer algebra into the Monsky–Washnitzer
algebra. -/
noncomputable def toWashnitzerAlgebra : intWashnitzerAlgebra σ R →+* washnitzerAlgebra σ R :=
  (intWashnitzerAlgebra σ R).subtype.codRestrict (washnitzerAlgebra σ R) fun f ↦
    intWashnitzerAlgebra_le f.2

/-- The inclusion into `R⟨X⟩†` does not change the underlying series. -/
@[simp]
theorem coe_toWashnitzerAlgebra (f : intWashnitzerAlgebra σ R) :
    (toWashnitzerAlgebra σ R f : MvPowerSeries σ R) = f :=
  (rfl)

end intWashnitzerAlgebra

/-- **The Monsky–Washnitzer degree growth condition**, in coefficient form. For finitely many
variables and any `0 < q < 1`, a series lies in `R°⟨X⟩†` iff for some integer `c > 0` its
coefficients satisfy `‖aᵥ‖ ≤ q ^ ⌊|ν| / c⌋`. Over a normed field and for `q = ‖π‖`, this says
that `aᵥ ∈ πʲ K°` as soon as `|ν| ≥ c j`. -/
theorem mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow [Finite σ] {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) {f : MvPowerSeries σ R} :
    f ∈ intWashnitzerAlgebra σ R ↔ ∃ c > 0, ∀ t, ‖coeff t f‖ ≤ q ^ (t.degree / c) := by
  rw [mem_intWashnitzerAlgebra_iff, mem_washnitzerAlgebra_iff_norm_coeff_le]
  constructor
  · rintro ⟨⟨ρ, hρ, C, hC⟩, h1⟩
    -- With `M = max C 1` and `M / q < ρ ^ c`, the bound `‖aᵥ‖ ≤ M ρ^{-|ν|}` gives
    -- `‖aᵥ‖ ≤ M (q / M) ^ j ≤ q ^ j` whenever `|ν| ≥ c j` with `j ≥ 1`.
    set M := max C 1
    have hM : 1 ≤ M := le_max_right _ _
    obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (M / q) hρ
    refine ⟨c + 1, c.succ_pos, fun t ↦ ?_⟩
    set j := t.degree / (c + 1)
    rcases Nat.eq_zero_or_pos j with hj | hj
    · simpa [hj] using h1 t
    have hqM : M / q < ρ ^ (c + 1) :=
      hc.trans_le (pow_le_pow_right₀ hρ.le c.le_succ)
    calc ‖coeff t f‖ ≤ C * (ρ ^ t.degree)⁻¹ := hC t
      _ ≤ M * ((ρ ^ (c + 1)) ^ j)⁻¹ := by
          rw [← pow_mul]
          gcongr
          · exact le_max_left _ _
          · exact hρ.le
          · exact Nat.mul_div_le _ _
      _ ≤ M * ((M / q) ^ j)⁻¹ := by gcongr
      _ = q ^ j * (M / M ^ j) := by
          rw [div_pow]
          field_simp
      _ ≤ q ^ j := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (le_self_pow₀ hM hj.ne'))
  · rintro ⟨c, hc, h⟩
    -- At the radius `ρ = q^{-1/c} > 1`, `‖aᵥ‖ ρ^{|ν|} ≤ q ^ j q ^ {-(j+1)} = q⁻¹`.
    have hq : 1 < q⁻¹ := one_lt_inv_iff₀.2 ⟨hq0, hq1⟩
    set ρ := q⁻¹ ^ ((c : ℝ)⁻¹)
    have hρc : ρ ^ c = q⁻¹ := Real.rpow_inv_natCast_pow (inv_nonneg.2 hq0.le) hc.ne'
    have hρ : 1 < ρ := Real.one_lt_rpow hq (by positivity)
    refine ⟨⟨ρ, hρ, q⁻¹, fun t ↦ ?_⟩, fun t ↦ (h t).trans (pow_le_one₀ hq0.le hq1.le)⟩
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖coeff t f‖ * ρ ^ t.degree ≤ q ^ (t.degree / c) * (ρ ^ c) ^ (t.degree / c + 1) := by
          rw [← pow_mul]
          gcongr
          · exact h t
          · exact hρ.le
          · exact (Nat.lt_mul_div_succ _ hc).le
      _ = q⁻¹ := by
          rw [hρc, inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity),
            one_mul]

end Defs

section NormedField

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The Monsky–Washnitzer degree growth condition.** Let `π ∈ K` with `0 < ‖π‖ < 1`. For
finitely many variables, a series lies in `K°⟨X⟩†` iff it is a sum `∑ⱼ πʲ Pⱼ`, converging
coefficientwise, of polynomials `Pⱼ` with coefficients of norm at most one and total degree at
most `c (j + 1)` for some `c`. -/
theorem mem_intWashnitzerAlgebra_iff_exists_hasSum [Finite σ] {π : K} (hπ0 : π ≠ 0)
    (hπ1 : ‖π‖ < 1) {f : MvPowerSeries σ K} :
    f ∈ intWashnitzerAlgebra σ K ↔ ∃ c : ℕ, ∃ P : ℕ → MvPolynomial σ K,
      (∀ j t, ‖(P j).coeff t‖ ≤ 1) ∧ (∀ j, (P j).totalDegree ≤ c * (j + 1)) ∧
        HasSum (fun j ↦ C (π ^ j) * (P j : MvPowerSeries σ K)) f := by
  classical
  have hπ : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  rw [mem_intWashnitzerAlgebra_iff_exists_norm_coeff_le_pow hπ hπ1]
  constructor
  · rintro ⟨c, hc, h⟩
    -- `Pⱼ` collects the monomials `(aᵥ / πʲ) Xᵛ` with `⌊|ν| / c⌋ = j`, of degree `< c (j + 1)`.
    have hfin (j : ℕ) : {t : σ →₀ ℕ | t.degree / c = j}.Finite :=
      (Finsupp.finite_of_degree_lt (c * (j + 1))).subset fun t (ht : t.degree / c = j) ↦
        (ht ▸ Nat.lt_mul_div_succ t.degree hc : t.degree < c * (j + 1))
    let P (j : ℕ) : MvPolynomial σ K :=
      ∑ t ∈ (hfin j).toFinset, MvPolynomial.monomial t (coeff t f / π ^ j)
    have hcoeff (j : ℕ) (t : σ →₀ ℕ) :
        (P j).coeff t = if t.degree / c = j then coeff t f / π ^ j else 0 := by
      simp [P, MvPolynomial.coeff_monomial]
    refine ⟨c, P, fun j t ↦ ?_, fun j ↦ ?_, ?_⟩
    · rw [hcoeff]
      split_ifs with ht
      · rw [norm_div, norm_pow, div_le_one (by positivity), ← ht]
        exact h t
      · simp
    · refine Finset.sup_le fun t ht ↦ ?_
      have ht' := MvPolynomial.mem_support_iff.1 ht
      rw [hcoeff] at ht'
      split_ifs at ht' with hj
      · rw [← hj]
        exact (Nat.lt_mul_div_succ t.degree hc).le
      · exact absurd rfl ht'
    · refine MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff.2 fun t ↦ ?_
      simp only [coeff_C_mul, MvPolynomial.coeff_coe, hcoeff, mul_ite, mul_zero]
      convert hasSum_ite_eq (t.degree / c) (coeff t f) using 1
      ext j
      simp only [eq_comm (a := t.degree / c)]
      split_ifs
      · exact mul_div_cancel₀ _ (pow_ne_zero _ hπ0)
      · rfl
  · rintro ⟨c, P, hP1, hPdeg, hsum⟩
    -- Only the terms `πʲ Pⱼ` with `|ν| ≤ c (j + 1)` contribute to the coefficient of `Xᵛ`, and
    -- these have norm at most `‖π‖ ^ j ≤ ‖π‖ ^ ⌊|ν| / (c + 1)⌋`.
    refine ⟨c + 1, c.succ_pos, fun t ↦ ?_⟩
    have ht := MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff.1 hsum t
    simp only [coeff_C_mul, MvPolynomial.coeff_coe] at ht
    refine le_of_tendsto' ht.norm fun s ↦
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ ↦ ?_
    rw [norm_mul, norm_pow]
    by_cases h0 : (P j).coeff t = 0
    · simp only [h0, norm_zero, mul_zero]
      positivity
    have hdeg : t.degree ≤ c * (j + 1) :=
      (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 h0)).trans (hPdeg j)
    have hj : t.degree / (c + 1) ≤ j :=
      Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul c.succ_pos).2 (by nlinarith))
    calc ‖π‖ ^ j * ‖(P j).coeff t‖ ≤ ‖π‖ ^ j * 1 := by gcongr; exact hP1 j t
      _ ≤ ‖π‖ ^ (t.degree / (c + 1)) := by
          rw [mul_one]
          exact pow_le_pow_of_le_one hπ.le hπ1.le hj

/-- **`K⟨X⟩† = K°⟨X⟩†[1/π]`.** For `π ∈ K` with `0 < ‖π‖ < 1`, a series is overconvergent iff
some power of `π` multiplies it into the integral Monsky–Washnitzer algebra. -/
theorem mem_washnitzerAlgebra_iff_exists_C_pow_mul_mem {π : K} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    {f : MvPowerSeries σ K} :
    f ∈ washnitzerAlgebra σ K ↔ ∃ k : ℕ, C (π ^ k) * f ∈ intWashnitzerAlgebra σ K := by
  refine ⟨fun hf ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · -- The coefficients of an overconvergent series are bounded, by `B` say, and `‖π‖ ^ k B ≤ 1`
    -- for large `k`.
    obtain ⟨ρ, hρ, hfρ⟩ := mem_washnitzerAlgebra.1 hf
    obtain ⟨B, hB⟩ := (isRestricted_const_iff.1 hfρ).bddAbove_range_of_cofinite
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le
      (le_max_right B 1))) hπ1
    refine ⟨k, mem_intWashnitzerAlgebra_iff.2
      ⟨mul_mem (C_mem_washnitzerAlgebra _) hf, fun t ↦ ?_⟩⟩
    have ht : ‖coeff t f‖ ≤ max B 1 :=
      calc ‖coeff t f‖ ≤ ‖coeff t f‖ * ρ ^ t.degree :=
            le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hρ.le)
        _ ≤ B := hB ⟨t, rfl⟩
        _ ≤ max B 1 := le_max_left _ _
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc ‖π‖ ^ k * ‖coeff t f‖ ≤ (max B 1)⁻¹ * max B 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (zero_lt_one.trans_le (le_max_right B 1)).ne'
  · have := mul_mem (C_mem_washnitzerAlgebra (π ^ k)⁻¹) (intWashnitzerAlgebra_le hk)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hπ0), map_one, one_mul] at this

variable [CompleteSpace K]

/-- **Units of the integral Monsky–Washnitzer algebra.** Over a complete ultrametric normed
field, a series in `K°⟨X⟩†` is a unit there iff its constant coefficient has norm one and every
other coefficient has norm less than one. -/
theorem isUnit_intWashnitzerAlgebra_iff {f : intWashnitzerAlgebra σ K} :
    IsUnit f ↔ ‖constantCoeff (f : MvPowerSeries σ K)‖ = 1 ∧
      ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ K)‖ < 1 := by
  set F := intWashnitzerAlgebra.toWashnitzerAlgebra σ K f
  have hF1 : ‖washnitzerAlgebra.toTate σ K F‖ ≤ 1 :=
    mem_intWashnitzerAlgebra_iff_norm_toTate_le_one.1 f.2
  refine ⟨fun hf ↦ ?_, fun ⟨h0, hlt⟩ ↦ ?_⟩
  · -- The constant coefficients of `f` and of its inverse have norm at most one and multiply to
    -- one, so both have norm one; the other coefficients are then controlled by the unit
    -- criterion in `K⟨X⟩†`.
    obtain ⟨g, hg⟩ := hf.exists_right_inv
    have hfg : ‖constantCoeff (f : MvPowerSeries σ K)‖ *
        ‖constantCoeff (g : MvPowerSeries σ K)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← Subring.coe_mul, hg, Subring.coe_one, map_one, norm_one]
    have hf0 : ‖constantCoeff (f : MvPowerSeries σ K)‖ ≤ 1 := by
      simpa using (mem_intWashnitzerAlgebra_iff.1 f.2).2 0
    have hg0 : ‖constantCoeff (g : MvPowerSeries σ K)‖ ≤ 1 := by
      simpa using (mem_intWashnitzerAlgebra_iff.1 g.2).2 0
    have h1 : ‖constantCoeff (f : MvPowerSeries σ K)‖ = 1 := by
      nlinarith [norm_nonneg (constantCoeff (f : MvPowerSeries σ K)),
        norm_nonneg (constantCoeff (g : MvPowerSeries σ K))]
    refine ⟨h1, fun t ht ↦ ?_⟩
    simpa [h1, F] using ((isUnit_washnitzerAlgebra_iff F).1
      (hf.map (intWashnitzerAlgebra.toWashnitzerAlgebra σ K))).2 t ht
  · -- `F` is a unit of `K⟨X⟩†` of Gauss norm one, so its inverse has Gauss norm one as well.
    have hF : IsUnit F := (isUnit_washnitzerAlgebra_iff F).2
      ⟨fun h ↦ by simp only [F, intWashnitzerAlgebra.coe_toWashnitzerAlgebra] at h; simp [h] at h0,
        fun t ht ↦ by simpa [F, h0] using hlt t ht⟩
    obtain ⟨u, hu⟩ := hF
    have hnorm : ‖washnitzerAlgebra.toTate σ K F‖ = 1 := by
      refine le_antisymm hF1 ?_
      simpa [F, h0, coeff_zero_eq_constantCoeff_apply] using
        MvPowerSeries.norm_coeff_mul_prod_le (washnitzerAlgebra.toTate σ K F) 0
    have hinv : ‖washnitzerAlgebra.toTate σ K ↑u⁻¹‖ ≤ 1 := by
      have h := congrArg (washnitzerAlgebra.toTate σ K) u.mul_inv
      rw [map_mul, map_one, hu] at h
      have := congrArg norm h
      rw [norm_mul, hnorm, one_mul, norm_one] at this
      exact this.le
    have hmem := mem_intWashnitzerAlgebra_iff_norm_toTate_le_one.2 hinv
    refine ⟨⟨f, ⟨_, hmem⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · simpa [hu, F] using congrArg Subtype.val u.mul_inv
    · simpa [hu, F] using congrArg Subtype.val u.inv_mul

/-- **The Jacobson radical of the integral Monsky–Washnitzer algebra.** Over a complete
ultrametric normed field, a series in `K°⟨X⟩†` lies in the Jacobson radical iff all its
coefficients have norm less than one. In particular, for every constant `π` with `‖π‖ < 1` and
every `f ∈ K°⟨X⟩†`, the series `1 + π f` is a unit. -/
theorem mem_jacobson_bot_intWashnitzerAlgebra_iff {f : intWashnitzerAlgebra σ K} :
    f ∈ Ideal.jacobson ⊥ ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ K)‖ < 1 := by
  classical
  rw [Ideal.mem_jacobson_bot]
  constructor
  · intro h t
    by_contra! ht
    by_cases h0 : ‖constantCoeff (f : MvPowerSeries σ K)‖ < 1
    · -- A coefficient of norm one in positive degree survives in `f + 1`.
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [coeff_zero_eq_constantCoeff_apply] at ht
        exact ht.not_gt h0
      have := (isUnit_intWashnitzerAlgebra_iff.1 (h 1)).2 t ht0
      simp [coeff_one, ht0] at this
      exact this.not_ge ht
    · -- A constant coefficient of norm one is cancelled by multiplying by `-f(0)⁻¹`.
      push Not at h0
      set a := constantCoeff (f : MvPowerSeries σ K)
      have ha : a ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans_le h0)
      have hy : C (-a⁻¹) ∈ intWashnitzerAlgebra σ K := by
        rw [C_mem_intWashnitzerAlgebra_iff, norm_neg, norm_inv]
        exact inv_le_one_of_one_le₀ h0
      have := (isUnit_intWashnitzerAlgebra_iff.1 (h ⟨_, hy⟩)).1
      simp [a, ha] at this
  · intro h y
    -- The coefficients of `f y` have norm less than one, so `f y + 1` passes the unit test.
    have hfy : ∀ t, ‖coeff t ((f * y : intWashnitzerAlgebra σ K) : MvPowerSeries σ K)‖ < 1 := by
      have hf : ‖washnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.toWashnitzerAlgebra σ K f)‖
          < 1 := by
        simpa [MvPowerSeries.norm_lt_iff] using h
      have hy : ‖washnitzerAlgebra.toTate σ K (intWashnitzerAlgebra.toWashnitzerAlgebra σ K y)‖
          ≤ 1 := mem_intWashnitzerAlgebra_iff_norm_toTate_le_one.1 y.2
      have hlt := (norm_mul_le _ _).trans_lt
        ((mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt hf)
      rw [← map_mul, ← map_mul, MvPowerSeries.norm_lt_iff] at hlt
      simpa using hlt
    refine isUnit_intWashnitzerAlgebra_iff.2 ⟨?_, fun t ht ↦ ?_⟩
    · have h0 := hfy 0
      rw [coeff_zero_eq_constantCoeff_apply] at h0
      rw [Subring.coe_add, Subring.coe_one, map_add, map_one,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using h0.ne), norm_one,
        max_eq_right h0.le]
    · simpa [coeff_one, ht] using hfy t

end NormedField

end TauCeti.Dagger
