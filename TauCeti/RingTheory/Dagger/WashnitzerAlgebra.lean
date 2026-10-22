/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.RingTheory.MvPowerSeries.Primitive.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Coefficients
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Units

/-!
# The Monsky–Washnitzer algebra of overconvergent power series

Let `R` be an ultrametric normed commutative ring. A formal power series `f = ∑ aᵥ Xᵛ` in the
variables `σ` is *overconvergent* if it is restricted at some constant radius `ρ > 1`, that is,
`‖aᵥ‖ ρ^|ν| → 0`. The overconvergent series form the `R`-subalgebra

```text
W = R⟨X⟩† = ⋃_{ρ > 1} R{X/ρ}  ⊆  R[[X]],
```

the algebra of Monsky and Washnitzer. Over a complete field `K` it is the basic object of
Grosse-Klönne's dagger geometry, playing the role that the Tate algebra `K⟨X⟩` plays in rigid
geometry: the overconvergent series are those converging on some polydisc strictly larger than
the closed unit polydisc. Every overconvergent series is restricted at radius `1`, so `W` lies in
the Tate algebra `T = R{X/1}` and carries the restricted Gauss norm.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra σ R`: the subalgebra of series restricted at some constant
  radius `ρ > 1`.
* `TauCeti.Dagger.washnitzerAlgebra.X`: the variables, and
  `TauCeti.Dagger.washnitzerAlgebra.ofMvPolynomial`: the inclusion of the polynomials.
* `TauCeti.Dagger.washnitzerAlgebra.toTate`: the inclusion of `W` into the unit-radius Tate
  algebra.

## Main results

* `TauCeti.Dagger.mem_washnitzerAlgebra_iff_norm_coeff_le`: for finitely many variables,
  `f ∈ W` iff `‖aᵥ‖ ≤ C ρ^{-|ν|}` for some `ρ > 1` and `C`.
* `TauCeti.Dagger.mem_washnitzerAlgebra_iff_exists_pow_eq_norm`: over a nontrivially normed
  field the radii may be taken in the divisible hull `√|K^×|` of the value group.
* `TauCeti.Dagger.washnitzerAlgebra.denseRange_toTate`: `W` is dense in the Tate algebra;
  `TauCeti.Dagger.washnitzerAlgebra_toSubring_lt`: over a nontrivially normed field it is a
  proper subring as soon as there is a variable, while `W` is everything when there is none
  (`TauCeti.Dagger.washnitzerAlgebra_eq_top`).
* `TauCeti.Dagger.exists_isRestricted_forall_norm_coeff_mul_pow_lt`: strict coefficient bounds
  on an overconvergent series persist to some radius `ρ > 1`; by
  `TauCeti.Dagger.exists_isRestricted_forall_mem_norm_coeff_mul_pow_lt` this holds for the
  coefficients at any set of exponents.
* `TauCeti.Dagger.isUnit_washnitzerAlgebra_iff` and
  `TauCeti.Dagger.washnitzerAlgebra.isUnit_toTate_iff`: over a complete ultrametric field an
  overconvergent series is a unit of `W` iff it is a unit of the Tate algebra, iff its constant
  coefficient is nonzero and strictly dominates all others. In Gauss norm form,
  `TauCeti.Dagger.isUnit_washnitzerAlgebra_iff_norm_sub_lt` reads `|f - f(0)| < |f(0)|`.
* `TauCeti.Dagger.primitive_mem_washnitzerAlgebra` and `TauCeti.Dagger.washnitzerAlgebra.primitive`:
  over a field of characteristic zero, termwise primitives `∑ aᵥ Xᵛ ↦ ∑ aᵥ Xᵛ⁺ᵉⁱ / (νᵢ + 1)` of
  overconvergent series are overconvergent.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968).
-/

public section

namespace TauCeti.Dagger

open Filter Topology _root_.MvPowerSeries
open TauCeti.MvPowerSeries (isRestricted_of_le denseRange_restrictedRadiusHom)

section ConstantRadius

variable {σ R : Type*} [NormedRing R]

/-- Series restricted at constant radii `ρ, ρ' > 1` are both restricted at `min ρ ρ' > 1`. -/
private theorem isRestricted_min_of_one_lt {f g : MvPowerSeries σ R} {ρ ρ' : ℝ} (hρ : 1 < ρ)
    (hρ' : 1 < ρ') (hf : IsRestricted (fun _ : σ ↦ ρ) f) (hg : IsRestricted (fun _ : σ ↦ ρ') g) :
    IsRestricted (fun _ : σ ↦ min ρ ρ') f ∧ IsRestricted (fun _ : σ ↦ min ρ ρ') g := by
  have h0 (_ : σ) : 0 ≤ min ρ ρ' := zero_le_one.trans (le_min hρ.le hρ'.le)
  exact ⟨isRestricted_of_le hf h0 fun _ ↦ min_le_left _ _,
    isRestricted_of_le hg h0 fun _ ↦ min_le_right _ _⟩

end ConstantRadius

section Defs

variable (σ R : Type*) [NormedCommRing R] [IsUltrametricDist R]

/-- The **Monsky–Washnitzer algebra** `R⟨X⟩†` of overconvergent power series: the series
restricted at some constant radius `ρ > 1`. -/
def washnitzerAlgebra : Subalgebra R (MvPowerSeries σ R) where
  carrier := {f | ∃ ρ > (1 : ℝ), IsRestricted (fun _ : σ ↦ ρ) f}
  mul_mem' := by
    rintro f g ⟨ρ, hρ, hf⟩ ⟨ρ', hρ', hg⟩
    obtain ⟨hf, hg⟩ := isRestricted_min_of_one_lt hρ hρ' hf hg
    exact ⟨min ρ ρ', lt_min hρ hρ', hf.mul hg⟩
  add_mem' := by
    rintro f g ⟨ρ, hρ, hf⟩ ⟨ρ', hρ', hg⟩
    obtain ⟨hf, hg⟩ := isRestricted_min_of_one_lt hρ hρ' hf hg
    exact ⟨min ρ ρ', lt_min hρ hρ', hf.add hg⟩
  algebraMap_mem' a := ⟨2, one_lt_two, by
    simpa [MvPowerSeries.algebraMap_apply] using isRestricted_C _ a⟩

variable {σ R}

/-- A series is overconvergent iff it is restricted at some constant radius `ρ > 1`. -/
theorem mem_washnitzerAlgebra {f : MvPowerSeries σ R} :
    f ∈ washnitzerAlgebra σ R ↔ ∃ ρ > (1 : ℝ), IsRestricted (fun _ : σ ↦ ρ) f :=
  Iff.rfl

/-- An overconvergent series is restricted at every constant radius in `[0, 1]`; in particular
it lies in the unit-radius Tate algebra. -/
theorem isRestricted_of_mem_washnitzerAlgebra {f : MvPowerSeries σ R}
    (hf : f ∈ washnitzerAlgebra σ R) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    IsRestricted (fun _ : σ ↦ ρ) f := by
  obtain ⟨ρ', hρ', hf⟩ := hf
  exact isRestricted_of_le hf (fun _ ↦ h0) fun _ ↦ h1.trans hρ'.le

/-- Constant series are overconvergent. -/
theorem C_mem_washnitzerAlgebra (a : R) : C a ∈ washnitzerAlgebra σ R :=
  ⟨2, one_lt_two, isRestricted_C _ a⟩

/-- Polynomials are overconvergent. -/
theorem coe_mem_washnitzerAlgebra (p : MvPolynomial σ R) :
    (p : MvPowerSeries σ R) ∈ washnitzerAlgebra σ R :=
  ⟨2, one_lt_two, p.isRestricted _⟩

/-- **Overconvergence by coefficient bounds.** For finitely many variables, a series is
overconvergent iff its coefficients satisfy `‖aᵥ‖ ≤ C ρ^{-|ν|}` for some `ρ > 1` and `C`. -/
theorem mem_washnitzerAlgebra_iff_norm_coeff_le [Finite σ] {f : MvPowerSeries σ R} :
    f ∈ washnitzerAlgebra σ R ↔ ∃ ρ > (1 : ℝ), ∃ C : ℝ, ∀ ν : σ →₀ ℕ,
      ‖coeff ν f‖ ≤ C * (ρ ^ ν.degree)⁻¹ := by
  constructor
  · rintro ⟨ρ, hρ, hf⟩
    obtain ⟨C, hC⟩ := (isRestricted_const_iff.1 hf).bddAbove_range_of_cofinite
    refine ⟨ρ, hρ, C, fun ν ↦ ?_⟩
    rw [le_mul_inv_iff₀ (pow_pos (by linarith) _)]
    exact hC ⟨ν, rfl⟩
  · rintro ⟨ρ, hρ, C, hC⟩
    -- The series is restricted at any radius `ρ' ∈ (1, ρ)`: its weighted norms are bounded by
    -- `C (ρ' / ρ)^|ν|`, which tends to zero because only finitely many exponents have bounded
    -- degree.
    obtain ⟨ρ', h1, h2⟩ := exists_between hρ
    have hq0 : 0 ≤ ρ' / ρ := by positivity
    have hq1 : ρ' / ρ < 1 := (div_lt_one (by linarith)).2 h2
    have hdeg : Tendsto (fun ν : σ →₀ ℕ ↦ ν.degree) cofinite atTop :=
      tendsto_atTop.2 fun N ↦
        (Finsupp.finite_of_degree_lt N).eventually_cofinite_notMem.mono fun ν hν ↦
          not_lt.1 hν
    refine ⟨ρ', h1, isRestricted_const_iff.2 ?_⟩
    have hlim : Tendsto (fun ν : σ →₀ ℕ ↦ C * (ρ' / ρ) ^ ν.degree) cofinite (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hdeg).const_mul C
    refine squeeze_zero (fun ν ↦ by positivity) (fun ν ↦ ?_) hlim
    calc ‖coeff ν f‖ * ρ' ^ ν.degree ≤ C * (ρ ^ ν.degree)⁻¹ * ρ' ^ ν.degree :=
          mul_le_mul_of_nonneg_right (hC ν) (by positivity)
      _ = C * (ρ' / ρ) ^ ν.degree := by rw [div_pow]; ring

/-- With no variables every power series is a constant, so every series is overconvergent. -/
theorem washnitzerAlgebra_eq_top [IsEmpty σ] : washnitzerAlgebra σ R = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ ⟨2, one_lt_two, isRestricted_of_finite_support _ (Set.toFinite _)⟩

/-- The Monsky–Washnitzer algebra lies in the unit-radius Tate algebra. -/
theorem washnitzerAlgebra_toSubring_le :
    (washnitzerAlgebra σ R).toSubring ≤ IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)) :=
  fun _ hf ↦ isRestricted_of_mem_washnitzerAlgebra hf zero_le_one le_rfl

namespace washnitzerAlgebra

variable (σ R) in
/-- The variable `Xᵢ` as an element of the Monsky–Washnitzer algebra. -/
noncomputable def X (i : σ) : washnitzerAlgebra σ R :=
  ⟨MvPowerSeries.X i, 2, one_lt_two, isRestricted_X _ i⟩

/-- The variable `Xᵢ ∈ W` is the formal variable `Xᵢ`. -/
@[simp]
theorem coe_X (i : σ) : (X σ R i : MvPowerSeries σ R) = MvPowerSeries.X i :=
  (rfl)

variable (σ R) in
/-- The inclusion of the polynomial algebra into the Monsky–Washnitzer algebra. -/
noncomputable def ofMvPolynomial : MvPolynomial σ R →ₐ[R] washnitzerAlgebra σ R :=
  (MvPolynomial.coeToMvPowerSeries.algHom R).codRestrict _ fun p ↦ by
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using coe_mem_washnitzerAlgebra p

/-- A polynomial viewed in `W` is the polynomial viewed as a power series. -/
@[simp]
theorem coe_ofMvPolynomial (p : MvPolynomial σ R) :
    (ofMvPolynomial σ R p : MvPowerSeries σ R) = p := by
  simp [ofMvPolynomial, MvPolynomial.coeToMvPowerSeries.algHom_apply]

/-- The polynomial inclusion sends the polynomial variables to the variables of `W`. -/
@[simp]
theorem ofMvPolynomial_X (i : σ) : ofMvPolynomial σ R (MvPolynomial.X i) = X σ R i :=
  Subtype.ext (by simp)

/-- Distinct polynomials are distinct overconvergent series. -/
theorem ofMvPolynomial_injective : Function.Injective (ofMvPolynomial σ R) :=
  fun p q h ↦ MvPolynomial.coe_inj.1 (by simpa using congrArg Subtype.val h)

variable (σ R) in
/-- The inclusion of the Monsky–Washnitzer algebra into the unit-radius Tate algebra `R{X/1}`,
through which `W` carries the Gauss norm. -/
noncomputable def toTate :
    washnitzerAlgebra σ R →ₐ[R] IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)) where
  __ := Subring.inclusion washnitzerAlgebra_toSubring_le
  commutes' _ := (rfl)

/-- The inclusion into the Tate algebra does not change the underlying series. -/
@[simp]
theorem coe_toTate (f : washnitzerAlgebra σ R) :
    (toTate σ R f : MvPowerSeries σ R) = f :=
  (rfl)

/-- The inclusion into the Tate algebra is injective. -/
theorem toTate_injective : Function.Injective (toTate σ R) :=
  fun f g h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)

/-- The Monsky–Washnitzer algebra is dense in the Tate algebra for the Gauss norm. -/
theorem denseRange_toTate : DenseRange (toTate σ R) := by
  refine (denseRange_restrictedRadiusHom (R := R) (r := fun _ : σ ↦ (1 : ℝ))
    (s := fun _ ↦ 2) (fun _ ↦ zero_le_one) fun _ ↦ one_le_two).mono ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f, 2, one_lt_two, f.2⟩, Subtype.ext (by simp)⟩

end washnitzerAlgebra

/-- **Radius selection on a set of exponents.** If the coefficients of an overconvergent series at
the exponents in `S` all have norm strictly less than `r`, then for some radius `ρ > 1` at which
the series is restricted, the weighted coefficient norms `‖aᵥ‖ ρ^|ν|` with `ν ∈ S` are still
strictly less than `r`. -/
theorem exists_isRestricted_forall_mem_norm_coeff_mul_pow_lt {f : MvPowerSeries σ R}
    (hf : f ∈ washnitzerAlgebra σ R) {S : Set (σ →₀ ℕ)} {r : ℝ}
    (h : ∀ t ∈ S, ‖coeff t f‖ < r) :
    ∃ ρ > (1 : ℝ), IsRestricted (fun _ : σ ↦ ρ) f ∧ ∀ t ∈ S, ‖coeff t f‖ * ρ ^ t.degree < r := by
  obtain ⟨ρ₀, hρ₀, hf⟩ := hf
  -- Only finitely many exponents in `S` have weighted norm at least `r` at radius `ρ₀`.
  have hS : {t ∈ S | r ≤ ‖coeff t f‖ * ρ₀ ^ t.degree}.Finite := by
    rcases le_or_gt r 0 with hr | hr
    · exact Set.Finite.subset Set.finite_empty fun t ht ↦ absurd ((norm_nonneg _).trans_lt
        (h t ht.1)) hr.not_gt
    · refine Set.Finite.subset (s := {t | r ≤ ‖coeff t f‖ * ρ₀ ^ t.degree}) ?_ fun t ht ↦ ht.2
      simpa [not_lt] using
        eventually_cofinite.1 ((isRestricted_const_iff.1 hf).eventually (gt_mem_nhds hr))
  -- For each of them, the strict bound at radius `1` persists to radii near `1`.
  have hnear : ∀ᶠ ρ in 𝓝 (1 : ℝ),
      ρ < ρ₀ ∧ ∀ t ∈ {t ∈ S | r ≤ ‖coeff t f‖ * ρ₀ ^ t.degree},
        ‖coeff t f‖ * ρ ^ t.degree < r := by
    refine (gt_mem_nhds hρ₀).and (hS.eventually_all.2 fun t ht ↦ ?_)
    have hc : Continuous fun ρ : ℝ ↦ ‖coeff t f‖ * ρ ^ t.degree := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using h t ht.1)
  obtain ⟨ρ, ⟨hρ₀', hρS⟩, hρ⟩ :=
    ((hnear.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi 1))).exists
  refine ⟨ρ, hρ, isRestricted_of_le hf (fun _ ↦ zero_le_one.trans hρ.le) fun _ ↦ hρ₀'.le,
    fun t htS ↦ ?_⟩
  by_cases ht : r ≤ ‖coeff t f‖ * ρ₀ ^ t.degree
  · exact hρS t ⟨htS, ht⟩
  · exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (le_of_lt hρ)) hρ₀'.le _)
      (norm_nonneg _)).trans_lt (not_le.1 ht)

/-- **Radius selection.** If every coefficient of an overconvergent series has norm strictly less
than `r`, then for some radius `ρ > 1` at which the series is restricted, every weighted
coefficient norm `‖aᵥ‖ ρ^|ν|` is still strictly less than `r`. -/
theorem exists_isRestricted_forall_norm_coeff_mul_pow_lt {f : MvPowerSeries σ R}
    (hf : f ∈ washnitzerAlgebra σ R) {r : ℝ} (h : ∀ t, ‖coeff t f‖ < r) :
    ∃ ρ > (1 : ℝ), IsRestricted (fun _ : σ ↦ ρ) f ∧ ∀ t, ‖coeff t f‖ * ρ ^ t.degree < r := by
  obtain ⟨ρ, hρ, hf, hρt⟩ :=
    exists_isRestricted_forall_mem_norm_coeff_mul_pow_lt hf (S := Set.univ) fun t _ ↦ h t
  exact ⟨ρ, hρ, hf, fun t ↦ hρt t trivial⟩

end Defs

section NontriviallyNormedField

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Radii in the divisible hull of the value group suffice.** Over a nontrivially normed field
`K`, a series is overconvergent iff it is restricted at some radius `ρ > 1` with `ρ^m = ‖a‖` for
some `m ≠ 0` and `a ∈ K`. -/
theorem mem_washnitzerAlgebra_iff_exists_pow_eq_norm {f : MvPowerSeries σ K} :
    f ∈ washnitzerAlgebra σ K ↔
      ∃ ρ > (1 : ℝ), (∃ m ≠ 0, ∃ a : K, ρ ^ m = ‖a‖) ∧ IsRestricted (fun _ : σ ↦ ρ) f := by
  refine ⟨fun ⟨ρ, hρ, hf⟩ ↦ ?_, fun ⟨ρ, hρ, _, hf⟩ ↦ ⟨ρ, hρ, hf⟩⟩
  -- Take the `m`-th root of `‖a‖ > 1`, where `m` is so large that `‖a‖ < ρ^m`.
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm K
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖a‖ hρ
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact ha.not_gt hm
  have hpow : (‖a‖ ^ (m⁻¹ : ℝ)) ^ m = ‖a‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) hm0
  have h1 : 1 < ‖a‖ ^ (m⁻¹ : ℝ) := Real.one_lt_rpow ha (by positivity)
  refine ⟨_, h1, ⟨m, hm0, a, hpow⟩, isRestricted_of_le hf (fun _ ↦ by positivity) fun _ ↦ ?_⟩
  refine le_of_pow_le_pow_left₀ hm0 (by linarith) ?_
  rw [hpow]
  exact hm.le

/-- A unit-radius restricted series which is not overconvergent: `∑ₖ c^⌊√k⌋ Xᵢᵏ` for any
`0 < ‖c‖ < 1`, whose weighted coefficients at radius `ρ > 1` grow along `k = m²` like
`(‖c‖ ρ^m)^m`. -/
private theorem exists_isRestricted_one_notMem_washnitzerAlgebra [Nonempty σ] :
    ∃ f : MvPowerSeries σ K, IsRestricted (fun _ : σ ↦ (1 : ℝ)) f ∧
      f ∉ washnitzerAlgebra σ K := by
  classical
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨i⟩ := ‹Nonempty σ›
  let f : MvPowerSeries σ K := fun t ↦
    if t = Finsupp.single i (t i) then c ^ Nat.sqrt (t i) else 0
  have hcoeff (t : σ →₀ ℕ) :
      coeff t f = if t = Finsupp.single i (t i) then c ^ Nat.sqrt (t i) else 0 :=
    coeff_apply f t
  refine ⟨f, isRestricted_one_iff.2 ?_, ?_⟩
  · refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc1).eventually
      (gt_mem_nhds hε) |>.exists
    -- The coefficients of norm at least `ε` sit at the exponents `k • eᵢ` with `k < n²`.
    refine eventually_cofinite.2 (((Set.finite_Iio (n ^ 2)).image
      fun k ↦ Finsupp.single i k).subset fun t ht ↦ ?_)
    simp only [Set.mem_ofPred_eq, not_lt, norm_norm, hcoeff] at ht
    split_ifs at ht with h
    · refine ⟨t i, Set.mem_Iio.2 (not_le.1 fun hk ↦ ?_), h.symm⟩
      rw [norm_pow] at ht
      exact (pow_le_pow_of_le_one (norm_nonneg c) hc1.le (Nat.le_sqrt'.2 hk)).not_gt
        (hn.trans_le ht)
    · rw [norm_zero] at ht
      exact absurd ht (not_le.2 hε)
  · rintro ⟨ρ, hρ, hf⟩
    have hinj : Function.Injective fun m : ℕ ↦ Finsupp.single i (m ^ 2) :=
      (Finsupp.single_injective i).comp (Nat.pow_left_injective two_ne_zero)
    have hlim := (isRestricted_const_iff.1 hf).comp hinj.tendsto_cofinite
    rw [Nat.cofinite_eq_atTop] at hlim
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ‖c‖⁻¹ hρ
    -- Along `k = m²` the weighted coefficient norm is `(‖c‖ ρ^m)^m ≥ 1` once `m ≥ M`.
    have hge : ∀ m ≥ M, 1 ≤ ‖coeff (Finsupp.single i (m ^ 2)) f‖ * ρ ^ (m ^ 2) := by
      intro m hm
      have hcm : 1 ≤ ‖c‖ * ρ ^ m := by
        rw [← inv_mul_le_iff₀ hc0, mul_one]
        exact hM.le.trans (pow_le_pow_right₀ hρ.le hm)
      simp only [hcoeff, Finsupp.single_eq_same, ↓reduceIte, Nat.sqrt_eq', norm_pow]
      rw [sq, pow_mul, ← mul_pow]
      exact one_le_pow₀ hcm
    obtain ⟨m, hm1, hm2⟩ :=
      ((hlim.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop M)).exists
    simp only [Function.comp_apply, Finsupp.degree_single] at hm1
    exact (hge m hm2).not_gt hm1

/-- Over a nontrivially normed field, the Monsky–Washnitzer algebra in at least one variable is
a proper subring of the Tate algebra. -/
theorem washnitzerAlgebra_toSubring_lt [Nonempty σ] :
    (washnitzerAlgebra σ K).toSubring < IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) := by
  obtain ⟨f, hf, hfW⟩ := exists_isRestricted_one_notMem_washnitzerAlgebra (σ := σ) (K := K)
  exact IsConcreteLE.lt_iff_le_and_exists.2 ⟨washnitzerAlgebra_toSubring_le, f, hf, hfW⟩

end NontriviallyNormedField

section Units

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The constant coefficient of a unit of the Tate algebra over an ultrametric normed field
strictly dominates every other coefficient. -/
private theorem norm_coeff_lt_of_isUnit_toTate {f : washnitzerAlgebra σ K}
    (hf : IsUnit (washnitzerAlgebra.toTate σ K f)) {t : σ →₀ ℕ} (ht : t ≠ 0) :
    ‖coeff t (f : MvPowerSeries σ K)‖ < ‖constantCoeff (f : MvPowerSeries σ K)‖ := by
  simpa using MvPowerSeries.norm_coeff_mul_prod_lt_of_isUnit hf ht

/-- The constant coefficient of a unit of the Tate algebra is nonzero. -/
private theorem constantCoeff_ne_zero_of_isUnit_toTate {f : washnitzerAlgebra σ K}
    (hf : IsUnit (washnitzerAlgebra.toTate σ K f)) :
    constantCoeff (f : MvPowerSeries σ K) ≠ 0 :=
  (hf.map (constantCoeff.comp
    (IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))).subtype)).ne_zero

variable [CompleteSpace K]

/-- **Units of the Monsky–Washnitzer algebra.** Over a complete ultrametric normed field, an
overconvergent series is a unit of `W` iff its constant coefficient is nonzero and strictly
dominates the norm of every other coefficient. -/
theorem isUnit_washnitzerAlgebra_iff (f : washnitzerAlgebra σ K) :
    IsUnit f ↔ constantCoeff (f : MvPowerSeries σ K) ≠ 0 ∧
      ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ K)‖ < ‖constantCoeff (f : MvPowerSeries σ K)‖ := by
  refine ⟨fun hf ↦ ⟨constantCoeff_ne_zero_of_isUnit_toTate (hf.map _),
    fun t ht ↦ norm_coeff_lt_of_isUnit_toTate (hf.map _) ht⟩, ?_⟩
  classical
  intro hf0
  have hsub := (forall_norm_coeff_sub_C_lt_iff (f : MvPowerSeries σ K)).2 hf0
  obtain ⟨h0, -⟩ := hf0
  set a := constantCoeff (f : MvPowerSeries σ K)
  have hmem : (f : MvPowerSeries σ K) - C a ∈ washnitzerAlgebra σ K :=
    sub_mem f.2 (C_mem_washnitzerAlgebra a)
  obtain ⟨ρ, hρ, hsubρ, hρt⟩ := exists_isRestricted_forall_norm_coeff_mul_pow_lt hmem hsub
  obtain ⟨ρ', hρ', hf⟩ := f.2
  -- At the radius `min ρ ρ' > 1`, `f` is a unit of the restricted series by the Tate-algebra
  -- unit criterion, and its inverse there is again overconvergent.
  have hm1 : 1 < min ρ ρ' := lt_min hρ hρ'
  have : Fact (0 < min ρ ρ') := ⟨zero_lt_one.trans hm1⟩
  let g : IsRestricted.subring (R := K) (fun _ : σ ↦ min ρ ρ') :=
    ⟨f, (isRestricted_min_of_one_lt hρ hρ' hsubρ hf).2⟩
  have hg : IsUnit g := by
    refine (isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt g).2
      ⟨h0, fun t ht ↦ ?_⟩
    have := hρt t
    simp only [map_sub, coeff_C, ht, ↓reduceIte, sub_zero] at this
    rw [Finsupp.prod_pow_eq_pow_degree]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_lt_one.trans hm1).le (min_le_left _ _) _)
      (norm_nonneg _)).trans_lt this
  obtain ⟨u, hu⟩ := hg
  let v : IsRestricted.subring (R := K) (fun _ : σ ↦ min ρ ρ') := ↑u⁻¹
  refine ⟨⟨f, ⟨v, min ρ ρ', hm1, v.2⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (by simpa [hu, g, v] using congrArg Subtype.val u.mul_inv)
  · exact Subtype.ext (by simpa [hu, g, v] using congrArg Subtype.val u.inv_mul)

/-- An overconvergent series is a unit of the Tate algebra iff it is a unit of the
Monsky–Washnitzer algebra: the inverse of an overconvergent series is overconvergent. -/
theorem washnitzerAlgebra.isUnit_toTate_iff (f : washnitzerAlgebra σ K) :
    IsUnit (washnitzerAlgebra.toTate σ K f) ↔ IsUnit f :=
  ⟨fun hf ↦ (isUnit_washnitzerAlgebra_iff f).2 ⟨constantCoeff_ne_zero_of_isUnit_toTate hf,
    fun _ ht ↦ norm_coeff_lt_of_isUnit_toTate hf ht⟩, fun hf ↦ hf.map _⟩

/-- **The unit criterion in Gauss norm form.** An overconvergent series `f` is a unit of `W` iff
`|f - f(0)| < |f(0)|` for the Gauss norm of the Tate algebra. -/
theorem isUnit_washnitzerAlgebra_iff_norm_sub_lt (f : washnitzerAlgebra σ K) :
    IsUnit f ↔ ‖washnitzerAlgebra.toTate σ K f -
        algebraMap K _ (constantCoeff (f : MvPowerSeries σ K))‖ <
      ‖constantCoeff (f : MvPowerSeries σ K)‖ := by
  rw [isUnit_washnitzerAlgebra_iff, MvPowerSeries.norm_lt_iff,
    ← forall_norm_coeff_sub_C_lt_iff]
  simp [coe_algebraMap_isRestrictedSubring]

end Units

section Primitive

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K]

/-- **Primitives of overconvergent series are overconvergent.** Over an ultrametric normed field
of characteristic zero, the termwise primitive with respect to `Xᵢ` of an overconvergent series is
overconvergent. See `MvPowerSeries.IsRestricted.primitive` for the radius-by-radius version. -/
theorem primitive_mem_washnitzerAlgebra {f : MvPowerSeries σ K} (hf : f ∈ washnitzerAlgebra σ K)
    (i : σ) : MvPowerSeries.primitive i f ∈ washnitzerAlgebra σ K := by
  obtain ⟨ρ, hρ, hf⟩ := hf
  obtain ⟨ρ', h1, h2⟩ := exists_between hρ
  exact ⟨ρ', h1, hf.primitive (fun _ ↦ zero_le_one.trans h1.le) (fun _ ↦ h2.le) h2⟩

variable (σ K) in
/-- The termwise primitive with respect to `Xᵢ`, as a `K`-linear endomorphism of the
Monsky–Washnitzer algebra. -/
noncomputable def washnitzerAlgebra.primitive (i : σ) :
    washnitzerAlgebra σ K →ₗ[K] washnitzerAlgebra σ K :=
  (MvPowerSeries.primitive i ∘ₗ (washnitzerAlgebra σ K).toSubmodule.subtype).codRestrict
    (washnitzerAlgebra σ K).toSubmodule fun f ↦ primitive_mem_washnitzerAlgebra f.2 i

/-- The primitive in `W` is the termwise primitive of the underlying series. -/
@[simp]
theorem washnitzerAlgebra.coe_primitive (i : σ) (f : washnitzerAlgebra σ K) :
    (washnitzerAlgebra.primitive σ K i f : MvPowerSeries σ K) = MvPowerSeries.primitive i f :=
  (rfl)

end Primitive

end TauCeti.Dagger
