/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.GaussNorm

import Mathlib.Data.Fintype.Lattice

/-!
# Polyradii and value-group radii for overconvergent power series

The Monsky–Washnitzer algebra `W = R⟨X⟩†` is defined using constant radii `ρ > 1`. In finitely many
variables this condition is equivalent to restrictedness at an arbitrary polyradius `c : σ → ℝ`
whose coordinates are all strictly greater than `1`, since the minimum coordinate of `c` is still
strictly greater than `1`. The resulting algebra homomorphisms `ofRestricted` and `ofOneLt` factor
radius restriction to the unit-radius Tate algebra through `toTate`, are contractive and continuous
for the Gauss norms, and have dense range.

While radii in the divisible hull `√|Kˣ|` always suffice to exhaust `K⟨X⟩†` over a nontrivially
normed field (`TauCeti.Dagger.mem_washnitzerAlgebra_iff_exists_pow_eq_norm`), radii in the value
group `|Kˣ|` itself need not suffice: over a discretely valued field with uniformiser `π`, every
scalar norm strictly greater than `1` is at least `‖π‖⁻¹`, whereas the geometric series
`∑ₖ πᵏ Xᵢᵏ` is restricted at `√‖π‖⁻¹ > 1` (hence overconvergent) yet fails to be restricted at
any polyradius whose `i`-th coordinate is at least `‖π‖⁻¹`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.ofOneLt`: in finitely many variables, the inclusion into `W`
  of the series restricted at a polyradius `c` with `∀ i, 1 < c i`.

## Main results

* `MvPowerSeries.IsRestricted.mem_washnitzerAlgebra` and
  `TauCeti.Dagger.mem_washnitzerAlgebra_iff_exists_forall_one_lt`: in finitely many variables,
  overconvergence is equivalent to restrictedness at some polyradius with all coordinates `> 1`.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_ofRestricted`,
  `TauCeti.Dagger.washnitzerAlgebra.norm_ofRestricted_le`, and
  `TauCeti.Dagger.washnitzerAlgebra.denseRange_ofRestricted`: compatibility with `toTate`,
  contractivity, continuity, and density of the polyradius inclusions.
* `TauCeti.Dagger.exists_mem_washnitzerAlgebra_not_isRestricted_of_norm_inv_le` and
  `TauCeti.Dagger.exists_mem_washnitzerAlgebra_not_isRestricted_of_norm_eq_zpow`: over an
  ultrametric ring with multiplicative norm and a uniform gap above `1` in its scalar norms (in
  particular, over a discretely valued field) in at least one variable, scalar-norm radii alone do
  not exhaust `R⟨X⟩†`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
-/

public section

open Filter Topology _root_.MvPowerSeries
open TauCeti.MvPowerSeries (isRestricted_of_le restrictedRadiusAlgHom restrictedRadiusAlgHom_apply
  restrictedRadiusHom norm_restrictedRadiusHom_le)

section Polyradius

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- In finitely many variables, a series restricted at a polyradius whose coordinates are all
strictly greater than `1` is overconvergent. -/
theorem _root_.MvPowerSeries.IsRestricted.mem_washnitzerAlgebra [Finite σ] {c : σ → ℝ}
    {f : MvPowerSeries σ R} (hf : IsRestricted c f) (hc : ∀ i, 1 < c i) :
    f ∈ TauCeti.Dagger.washnitzerAlgebra σ R := by
  rw [TauCeti.Dagger.mem_washnitzerAlgebra]
  by_cases hne : Nonempty σ
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min c
    exact ⟨c i₀, hc i₀, isRestricted_of_le hf (fun _ ↦ (zero_lt_one.trans (hc i₀)).le) hi₀⟩
  · have := not_nonempty_iff.mp hne
    exact ⟨2, one_lt_two, isRestricted_of_finite_support _ (Set.toFinite _)⟩

namespace TauCeti.Dagger

/-- **Polyradius criterion for overconvergence.** In finitely many variables, a formal power series
is overconvergent iff it is restricted at some polyradius `c` with `1 < c i` for every `i`. -/
theorem mem_washnitzerAlgebra_iff_exists_forall_one_lt [Finite σ] {f : MvPowerSeries σ R} :
    f ∈ washnitzerAlgebra σ R ↔ ∃ c : σ → ℝ, (∀ i, 1 < c i) ∧ IsRestricted c f := by
  rw [mem_washnitzerAlgebra]
  exact ⟨fun ⟨ρ, hρ, hf⟩ ↦ ⟨fun _ ↦ ρ, fun _ ↦ hρ, hf⟩,
    fun ⟨_, hc, hf⟩ ↦ (mem_washnitzerAlgebra.mp (hf.mem_washnitzerAlgebra hc))⟩

namespace washnitzerAlgebra

section OfRestricted

variable {c c' : σ → ℝ} {ρ : ℝ} (hρ : 1 < ρ) (hc : ∀ i, ρ ≤ c i)

/-- The inclusion of a restricted subring into `W` is injective. -/
theorem ofRestricted_injective : Function.Injective (ofRestricted (R := R) hρ hc) :=
  fun _ _ h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)

/-- Any two lower-bound witnesses for the same polyradius `c` define the same inclusion into `W`. -/
theorem ofRestricted_eq_ofRestricted {ρ' : ℝ} (hρ' : 1 < ρ') (hc' : ∀ i, ρ' ≤ c i) :
    ofRestricted (R := R) hρ hc = ofRestricted hρ' hc' :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp)

/-- The polyradius inclusion sends each variable `Xᵢ` to `Xᵢ`. -/
@[simp]
theorem ofRestricted_X (i : σ) :
    ofRestricted hρ hc ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩ = X σ R i :=
  Subtype.ext (by simp)

/-- The polyradius inclusion sends a polynomial to its image in `W`. -/
@[simp]
theorem ofRestricted_polynomial (p : MvPolynomial σ R) :
    ofRestricted hρ hc ⟨p, p.isRestricted c⟩ = ofMvPolynomial σ R p :=
  Subtype.ext (by simp)

/-- Composing a polyradius inclusion into `W` with `toTate` gives radius restriction to unit
radii. -/
@[simp]
theorem toTate_ofRestricted (f : IsRestricted.subring (R := R) c) :
    toTate σ R (ofRestricted hρ hc f) =
      restrictedRadiusAlgHom (fun _ ↦ zero_le_one) (fun i ↦ hρ.le.trans (hc i)) f :=
  Subtype.ext (by simp)

/-- Composing `ofRestricted` with `toTate` as `R`-algebra homomorphisms is `restrictedRadiusAlgHom`
to unit radii. -/
theorem toTate_comp_ofRestricted :
    (toTate σ R).comp (ofRestricted hρ hc) =
      restrictedRadiusAlgHom (fun _ ↦ zero_le_one) (fun i ↦ hρ.le.trans (hc i)) :=
  AlgHom.ext (toTate_ofRestricted hρ hc)

/-- Polyradius inclusions commute with restriction along nested polyradii `c ≤ c'`. -/
theorem ofRestricted_restrictedRadiusAlgHom (hcc' : c ≤ c')
    (f : IsRestricted.subring (R := R) c') :
    ofRestricted hρ hc
        (restrictedRadiusAlgHom (fun i ↦ (zero_lt_one.trans hρ).le.trans (hc i)) hcc' f) =
      ofRestricted hρ (fun i ↦ (hc i).trans (hcc' i)) f :=
  Subtype.ext (by simp)

/-- Polyradius inclusions commute with renaming the variables along an equivalence. -/
theorem ofRestricted_renameAlgEquiv {τ : Type*} (e : τ ≃ σ)
    (f : IsRestricted.subring (R := R) (c ∘ e)) :
    ofRestricted hρ hc (IsRestricted.renameAlgEquiv e c f) =
      renameAlgEquiv e (ofRestricted hρ (fun i ↦ hc (e i)) f) :=
  Subtype.ext (by simp)

section Norm

variable [∀ i, Fact (0 < c i)]

/-- A polyradius inclusion into `W` does not increase the Gauss norm. -/
theorem norm_ofRestricted_le (f : IsRestricted.subring (R := R) c) :
    ‖ofRestricted hρ hc f‖ ≤ ‖f‖ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [← norm_toTate, toTate_ofRestricted, restrictedRadiusAlgHom_apply]
  exact norm_restrictedRadiusHom_le (fun _ ↦ zero_le_one) (fun i ↦ hρ.le.trans (hc i)) f

/-- A polyradius inclusion into `W` is `1`-Lipschitz for the Gauss norms. -/
theorem lipschitzWith_ofRestricted : LipschitzWith 1 (ofRestricted (R := R) hρ hc) := by
  simpa only [Real.toNNReal_one] using
    AddMonoidHomClass.lipschitz_of_bound (ofRestricted (R := R) hρ hc) 1
      fun f ↦ by simpa only [one_mul] using norm_ofRestricted_le hρ hc f

/-- A polyradius inclusion into `W` is continuous for the Gauss norms. -/
@[continuity]
theorem continuous_ofRestricted : Continuous (ofRestricted (R := R) hρ hc) :=
  (lipschitzWith_ofRestricted hρ hc).continuous

end Norm

/-- Every polyradius inclusion into `W` has dense range for the unit Gauss norm, since its range
contains the polynomials. -/
theorem denseRange_ofRestricted : DenseRange (ofRestricted (R := R) hρ hc) := by
  refine denseRange_ofMvPolynomial.mono ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p, p.isRestricted c⟩, ofRestricted_polynomial hρ hc p⟩

end OfRestricted

section OfOneLt

variable [Finite σ] {c : σ → ℝ} (hc : ∀ i, 1 < c i)

/-- In finitely many variables, the inclusion into `W` of the series restricted at a polyradius
`c` whose coordinates are all strictly greater than `1`. -/
noncomputable def ofOneLt : IsRestricted.subring (R := R) c →ₐ[R] washnitzerAlgebra σ R where
  toRingHom := (IsRestricted.subring (R := R) c).subtype.codRestrict
    (washnitzerAlgebra σ R).toSubring fun f ↦ f.property.mem_washnitzerAlgebra hc
  commutes' _ := (rfl)

/-- The inclusion `ofOneLt` leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_ofOneLt (f : IsRestricted.subring (R := R) c) :
    (ofOneLt hc f : MvPowerSeries σ R) = f :=
  (rfl)

/-- `ofOneLt` agrees with `ofRestricted` for any uniform lower bound `ρ > 1` of `c`. -/
theorem ofOneLt_eq_ofRestricted {ρ : ℝ} (hρ : 1 < ρ) (hle : ∀ i, ρ ≤ c i) :
    ofOneLt (R := R) hc = ofRestricted hρ hle :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp)

/-- In finitely many variables, `ofOneLt` is `ofRestricted` for some uniform lower bound `ρ > 1`. -/
theorem exists_ofOneLt_eq_ofRestricted :
    ∃ (ρ : ℝ) (hρ : 1 < ρ) (hle : ∀ i, ρ ≤ c i), ofOneLt (R := R) hc = ofRestricted hρ hle := by
  by_cases hne : Nonempty σ
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min c
    exact ⟨c i₀, hc i₀, hi₀, ofOneLt_eq_ofRestricted hc (hc i₀) hi₀⟩
  · have := not_nonempty_iff.mp hne
    exact ⟨2, one_lt_two, fun i ↦ IsEmpty.elim this i,
      ofOneLt_eq_ofRestricted hc one_lt_two fun i ↦ IsEmpty.elim this i⟩

/-- The polyradius inclusion `ofOneLt` is injective. -/
theorem ofOneLt_injective : Function.Injective (ofOneLt (R := R) hc) := by
  obtain ⟨_, hρ, hle, h⟩ := exists_ofOneLt_eq_ofRestricted (R := R) hc
  exact h ▸ ofRestricted_injective hρ hle

/-- `ofOneLt` sends each variable `Xᵢ` to `Xᵢ`. -/
@[simp]
theorem ofOneLt_X (i : σ) :
    ofOneLt hc ⟨_root_.MvPowerSeries.X i, isRestricted_X c i⟩ = X σ R i :=
  Subtype.ext (by simp)

/-- `ofOneLt` sends a polynomial to its image in `W`. -/
@[simp]
theorem ofOneLt_polynomial (p : MvPolynomial σ R) :
    ofOneLt hc ⟨p, p.isRestricted c⟩ = ofMvPolynomial σ R p :=
  Subtype.ext (by simp)

/-- Composing `ofOneLt` with `toTate` gives radius restriction to unit radii. -/
@[simp]
theorem toTate_ofOneLt (f : IsRestricted.subring (R := R) c) :
    toTate σ R (ofOneLt hc f) =
      restrictedRadiusAlgHom (fun _ ↦ zero_le_one) (fun i ↦ (hc i).le) f :=
  Subtype.ext (by simp)

/-- `ofOneLt` does not increase the Gauss norm. -/
theorem norm_ofOneLt_le [∀ i, Fact (0 < c i)] (f : IsRestricted.subring (R := R) c) :
    ‖ofOneLt hc f‖ ≤ ‖f‖ := by
  obtain ⟨_, hρ, hle, h⟩ := exists_ofOneLt_eq_ofRestricted (R := R) hc
  exact h ▸ norm_ofRestricted_le hρ hle f

/-- `ofOneLt` is continuous for the Gauss norms. -/
@[continuity]
theorem continuous_ofOneLt [∀ i, Fact (0 < c i)] : Continuous (ofOneLt (R := R) hc) := by
  obtain ⟨_, hρ, hle, h⟩ := exists_ofOneLt_eq_ofRestricted (R := R) hc
  exact h ▸ continuous_ofRestricted hρ hle

/-- `ofOneLt` has dense range for the unit Gauss norm. -/
theorem denseRange_ofOneLt : DenseRange (ofOneLt (R := R) hc) := by
  obtain ⟨_, hρ, hle, h⟩ := exists_ofOneLt_eq_ofRestricted (R := R) hc
  exact h ▸ denseRange_ofRestricted hρ hle

end OfOneLt

end washnitzerAlgebra

end TauCeti.Dagger

end Polyradius

namespace TauCeti.Dagger

section ValueGroup

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]

/-- **Scalar-norm radii need not exhaust `R⟨X⟩†`.** Suppose `0 < ‖π‖ < 1` and `‖π‖⁻¹` is a lower
bound on all norms of scalars strictly larger than `1` (as when `π` is a uniformiser of a
discretely valued field). In at least one variable, the geometric series `∑ₖ πᵏ Xᵢᵏ` is restricted
at `√‖π‖⁻¹ > 1`, hence overconvergent, yet fails to be restricted at every polyradius `c` with all
coordinates strictly greater than `1` and lying in `|R|`. -/
theorem exists_mem_washnitzerAlgebra_not_isRestricted_of_norm_inv_le [Nonempty σ]
    {π : R} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (hgap : ∀ a : R, 1 < ‖a‖ → ‖π‖⁻¹ ≤ ‖a‖) :
    ∃ f ∈ washnitzerAlgebra σ R,
      ∀ c : σ → ℝ, (∀ j, 1 < c j) → (∀ j, ∃ a : R, c j = ‖a‖) → ¬IsRestricted c f := by
  classical
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have : NormOneClass R :=
    ⟨by have h := congrArg (‖·‖) (one_mul π); rw [norm_mul] at h; nlinarith⟩
  have hinv1 : 1 < ‖π‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hπpos, hπ1⟩
  let f : MvPowerSeries σ R := fun t ↦ if t = Finsupp.single i (t i) then π ^ t i else 0
  have hcoeff (t : σ →₀ ℕ) :
      coeff t f = if t = Finsupp.single i (t i) then π ^ t i else 0 := coeff_apply f t
  -- At `ρ = √‖π‖⁻¹ > 1`, `‖π‖ * ρ = √‖π‖ < 1`, so `f` is restricted at the constant radius `ρ`.
  set ρ := √(‖π‖⁻¹)
  have hρ1 : 1 < ρ := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hinv1
  have hπρ0 : 0 ≤ ‖π‖ * ρ := by positivity
  have hπρ1 : ‖π‖ * ρ < 1 := by
    have hsq : (‖π‖ * ρ) ^ 2 = ‖π‖ := by
      rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hπpos.le), sq, mul_assoc,
        mul_inv_cancel₀ hπpos.ne', mul_one]
    nlinarith [hsq, hπ1]
  have hfW : f ∈ washnitzerAlgebra σ R := by
    rw [mem_washnitzerAlgebra]
    refine ⟨ρ, hρ1, isRestricted_const_iff.mpr (NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ ?_)⟩
    obtain ⟨N, hN⟩ :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hπρ0 hπρ1).eventually (gt_mem_nhds hε)).exists
    refine eventually_cofinite.mpr
      (((Set.finite_Iio N).image (Finsupp.single i)).subset fun t ht ↦ ?_)
    simp only [Set.mem_ofPred_eq, Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans hρ1.le) _)), not_lt, hcoeff] at ht
    split_ifs at ht with h
    · refine ⟨t i, Set.mem_Iio.mpr (not_le.mp fun hk ↦ ?_), h.symm⟩
      have hdeg : t.degree = t i := by conv_lhs => rw [h, Finsupp.degree_single]
      rw [hdeg, norm_pow, ← mul_pow] at ht
      exact ((pow_le_pow_of_le_one hπρ0 hπρ1.le hk).trans_lt hN).not_ge ht
    · rw [norm_zero, zero_mul] at ht
      exact absurd ht hε.not_ge
  refine ⟨f, hfW, fun c hc1 hca hfc ↦ ?_⟩
  obtain ⟨a, ha⟩ := hca i
  have hci : ‖π‖⁻¹ ≤ c i := ha ▸ hgap a (ha ▸ hc1 i)
  have h1le : 1 ≤ ‖π‖ * c i := (inv_mul_le_iff₀ hπpos).mp (by simpa using hci)
  have hlim := hfc.comp (Finsupp.single_injective i).tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists
  simp only [Function.comp_apply, hcoeff, Finsupp.single_eq_same, ↓reduceIte, norm_pow] at hk
  have hprod : ((Finsupp.single i k).prod fun j e ↦ c j ^ e) = c i ^ k :=
    Finsupp.prod_single_index (pow_zero _)
  rw [hprod, ← mul_pow] at hk
  exact (one_le_pow₀ h1le).not_gt hk

/-- Under a uniform lower bound `‖π‖⁻¹` on scalar norms above `1`, some overconvergent series in
at least one variable is not restricted at any constant scalar-norm radius `‖a‖ > 1`. -/
theorem exists_mem_washnitzerAlgebra_not_isRestricted_const_norm_of_norm_inv_le [Nonempty σ]
    {π : R} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (hgap : ∀ a : R, 1 < ‖a‖ → ‖π‖⁻¹ ≤ ‖a‖) :
    ∃ f ∈ washnitzerAlgebra σ R, ∀ a : R, 1 < ‖a‖ → ¬IsRestricted (fun _ : σ ↦ ‖a‖) f := by
  obtain ⟨f, hf, hnot⟩ :=
    exists_mem_washnitzerAlgebra_not_isRestricted_of_norm_inv_le (σ := σ) hπ0 hπ1 hgap
  exact ⟨f, hf, fun a ha ↦ hnot _ (fun _ ↦ ha) fun _ ↦ ⟨a, rfl⟩⟩

/-- **Discretely valued rings and fields: radii in `|R|` do not suffice.** If the nonzero norms of
`R` are the integer powers of `‖π‖` for some `0 < ‖π‖ < 1`, then in at least one variable there is
an overconvergent series that is not restricted at any polyradius with coordinates in
`|R| ∩ (1, ∞)`. In particular, constant radii in `|Kˣ|` do not exhaust `K⟨X⟩†` over a discretely
valued field `K`. -/
theorem exists_mem_washnitzerAlgebra_not_isRestricted_of_norm_eq_zpow [Nonempty σ]
    {π : R} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hdisc : ∀ x : R, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) :
    ∃ f ∈ washnitzerAlgebra σ R,
      ∀ c : σ → ℝ, (∀ j, 1 < c j) → (∀ j, ∃ a : R, c j = ‖a‖) → ¬IsRestricted c f := by
  refine exists_mem_washnitzerAlgebra_not_isRestricted_of_norm_inv_le (norm_pos_iff.mp hπ0) hπ1
    fun a ha ↦ ?_
  have ha0 : a ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans ha)
  obtain ⟨k, hk⟩ := hdisc a ha0
  have hkneg : k ≤ -1 := by
    by_contra! hk0
    have hk' : 0 ≤ k := by omega
    have hle : ‖π‖ ^ k ≤ 1 := by
      simpa using zpow_le_zpow_right_of_le_one₀ hπ0 hπ1.le hk'
    exact hle.not_gt (hk ▸ ha)
  have hle : ‖π‖ ^ (-1 : ℤ) ≤ ‖π‖ ^ k := zpow_le_zpow_right_of_le_one₀ hπ0 hπ1.le hkneg
  simpa only [zpow_neg_one, ← hk] using hle

end ValueGroup

end TauCeti.Dagger
