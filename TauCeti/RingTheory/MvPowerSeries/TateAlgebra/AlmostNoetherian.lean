/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.Topology.Algebra.Valued.Discrete

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Division
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Noetherianity and almost noetherianity of the Gauss unit ball of a Tate algebra

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
and let `T = K⟨X⟩` be the Tate algebra of unit-radius restricted power series in finitely many
variables `σ`, with Gauss unit ball `T° = Subring.unitClosedBall T`.

When `K°` is noetherian — equivalently when `K` has a strict norm gap below `1`, that is, when `K`
is either trivially normed or discretely valued — `K°` carries a Euclidean valuation degree
compatible with its ultrametric norm: an element of larger norm divides one of smaller norm in `K°`,
while an element of strictly larger degree has strictly smaller norm and can be left as remainder.
Kedlaya's Gröbner-basis theorem
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`) therefore makes
`K°⟨X⟩` and `T°` noetherian rings. Conversely, the constant-coefficient retraction
descends noetherianity from `T°` to `K°`.

Over an arbitrary complete ultrametric normed field `K`, such as `ℂ_p`, `T°` need not be noetherian.
Kiehl's Satz 5.1 proves that finite `T°`-modules are nevertheless *almost noetherian*: for every
finitely generated `T°`-module `M`, every submodule `N ≤ M`, and every `0 < ε < 1`, there is a
single finitely generated submodule `N' ≤ N` containing `c • N` for **all** scalars `c ∈ K°` with
`‖c‖ ≤ ε`. When `K°` is noetherian one takes `N' = N`. Otherwise the norms below `1` are dense up to
`1`, so any `0 < ε < 1` factors through elements of `K°` of norm strictly between `√ε` and `1`:

* exactness on finite free modules reduces the statement from finite `T°`-modules to ideals `I` of
  `T°`;
* for `I ≠ ⊥`, an element `g ∈ I` whose Gauss norm exceeds `‖d‖ · sup_{f ∈ I} ‖f‖` normalizes to a
  series `g₀` of Gauss norm `1`, which an isometric triangular automorphism makes distinguished of
  some degree `s` in one separated variable `Y`;
* Weierstrass division by `g₀` writes `d • f` as an integral multiple of `g` plus a remainder in `I`
  of degree less than `s` in `Y`, reducing to a submodule of `(T'°)^s` in one fewer variable.

## Main definitions

* `TauCeti.MvPowerSeries.unitClosedBallCoeffHom`: the scalar inclusion `K° →+* T°`.
* `TauCeti.MvPowerSeries.unitClosedBallConstantCoeffHom`: the constant-coefficient retraction
  `T° →+* K°`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionIntegerEquiv`: the coefficient-preserving ring
  equivalence `𝒪[K]⟨X₁, …, Xₙ⟩ ≃+* K⟨X₁, …, Xₙ⟩°` for a complete nontrivially normed ultrametric
  field `K`.

## Main results

* `TauCeti.MvPowerSeries.isLocalizationAway_unitClosedBallCoeffHom`: inverting any nonzero constant
  of norm `< 1` localizes `K⟨X⟩°` to `K⟨X⟩`.
* `TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall`: `T°` is noetherian when `K°` is.
* `TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall_iff`: in finitely many variables, `T°` is
  noetherian if and only if `K°` is.
* `TauCeti.Huber.continuous_restrictedMvPowerSeriesCompletionIntegerEquiv`,
  `TauCeti.Huber.continuous_restrictedMvPowerSeriesCompletionIntegerEquiv_symm`: the identification
  `𝒪[K]⟨X₁, …, Xₙ⟩ ≃+* K⟨X₁, …, Xₙ⟩°` is a homeomorphism.
* `TauCeti.Huber.isNoetherianRing_restrictedMvPowerSeriesCompletion_integer`: over a complete
  nontrivially normed ultrametric field whose valuation ring `𝒪[K]` is a discrete valuation ring,
  `restrictedMvPowerSeriesCompletion n 𝒪[K]` is noetherian.
* `TauCeti.MvPowerSeries.exists_fg_le_forall_smul_mem_unitClosedBall`: Kiehl's Satz 5.1 for finite
  modules over `T°`, and `TauCeti.MvPowerSeries.exists_fg_le_forall_smul_mem_of_surjective` for
  finite modules over any ring receiving a surjection from `T°`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.3, Lemma 8 and Proposition 7.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, Int. Math. Res. Not. 2016
  (2016), no. 8, 2544–2567.
-/

public section

open _root_.MvPowerSeries Filter Topology

namespace TauCeti.MvPowerSeries

section CoeffHom

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Scalar inclusion into the Gauss unit ball.** Constants of norm at most one in `K` embed as
constant series of Gauss norm at most one in `K⟨X⟩°`. -/
noncomputable def unitClosedBallCoeffHom :
    Subring.unitClosedBall K →+* Subring.unitClosedBall (Tate σ) :=
  ((algebraMap K (Tate σ)).comp (Subring.unitClosedBall K).subtype).codRestrict _ fun c ↦
    Subring.mem_unitClosedBall.mpr <| by
      rw [RingHom.comp_apply, Subring.coe_subtype, norm_algebraMap_isRestrictedSubring]
      exact Subring.mem_unitClosedBall.mp c.2

@[simp]
theorem coe_unitClosedBallCoeffHom (c : Subring.unitClosedBall K) :
    (unitClosedBallCoeffHom (σ := σ) c : Tate σ) = algebraMap K (Tate σ) (c : K) := (rfl)

/-- **Constant-coefficient retraction on Gauss unit balls.** The constant coefficient maps `K⟨X⟩°`
back onto `K°`. -/
noncomputable def unitClosedBallConstantCoeffHom :
    Subring.unitClosedBall (Tate σ) →+* Subring.unitClosedBall K :=
  ((constantCoeff : MvPowerSeries σ K →+* K).comp
    ((Tate σ).subtype.comp (Subring.unitClosedBall (Tate σ)).subtype)).codRestrict _ fun f ↦
    Subring.mem_unitClosedBall.mpr ((norm_constantCoeff_le (f : Tate σ)).trans
      (Subring.mem_unitClosedBall.mp f.2))

@[simp]
theorem coe_unitClosedBallConstantCoeffHom (f : Subring.unitClosedBall (Tate σ)) :
    (unitClosedBallConstantCoeffHom f : K) =
      constantCoeff ((f : Tate σ) : MvPowerSeries σ K) := (rfl)

@[simp]
theorem unitClosedBallConstantCoeffHom_comp_coeffHom (c : Subring.unitClosedBall K) :
    unitClosedBallConstantCoeffHom (unitClosedBallCoeffHom (σ := σ) c) = c := by
  ext
  simp [coe_algebraMap_isRestrictedSubring]

/-- **Inverting any nonzero constant of norm `< 1` localizes `K⟨X⟩°` to `K⟨X⟩`.** -/
theorem isLocalizationAway_unitClosedBallCoeffHom (π : Subring.unitClosedBall K)
    (hπ0 : (π : K) ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    IsLocalization.Away (unitClosedBallCoeffHom (σ := σ) π) (Tate σ) :=
  (Subring.unitClosedBall (Tate σ)).isLocalizationAway_of_isOpen
    (Subring.isOpen_unitClosedBall (Tate σ)) (unitClosedBallCoeffHom π)
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one <| by
      simpa [coe_unitClosedBallCoeffHom, norm_algebraMap_isRestrictedSubring] using hπ1)
    (by
      rw [coe_unitClosedBallCoeffHom]
      exact (isUnit_iff_ne_zero.mpr hπ0).map (algebraMap K (Tate σ)))

/-- If the Gauss unit ball `K⟨X⟩°` is noetherian, then `K°` is noetherian, via the constant
coefficient retraction. -/
theorem isNoetherianRing_unitClosedBall_of_tate (σ : Type*)
    [IsNoetherianRing (Subring.unitClosedBall (Tate σ))] :
    IsNoetherianRing (Subring.unitClosedBall K) :=
  isNoetherianRing_of_surjective _ _ (unitClosedBallConstantCoeffHom (σ := σ)) fun c ↦
    ⟨unitClosedBallCoeffHom c, unitClosedBallConstantCoeffHom_comp_coeffHom c⟩

end CoeffHom

section Noetherian

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

private theorem norm_unitClosedBall_subtype_le (x : Subring.unitClosedBall K) :
    ‖(Subring.unitClosedBall K).subtype x‖ ≤ 1 * ‖x‖ :=
  (one_mul ‖x‖).symm.le

/-- Including coefficients identifies unit-radius restricted series over `Subring.unitClosedBall K`
with `Subring.unitClosedBall (K⟨X⟩)`, without assuming that `K` is nontrivially normed. -/
private noncomputable def restrictedUnitClosedBallEquiv :
    IsRestricted.subring (R := Subring.unitClosedBall K) (fun _ : σ ↦ 1) ≃+*
      Subring.unitClosedBall (Tate σ) := by
  let hom : IsRestricted.subring (R := Subring.unitClosedBall K) (fun _ : σ ↦ 1) →+*
      Subring.unitClosedBall (Tate σ) :=
    (restrictedMap (Subring.unitClosedBall K).subtype norm_unitClosedBall_subtype_le).codRestrict _
      fun f ↦ mem_unitClosedBall_iff.mpr fun t ↦ by
        rw [coeff_restrictedMap]
        exact Subring.mem_unitClosedBall.mp
          (coeff t (f : MvPowerSeries σ (Subring.unitClosedBall K))).2
  refine RingEquiv.ofBijective hom ⟨fun f g h ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦
    Subtype.ext ?_, fun f ↦ ?_⟩
  · simpa [hom] using congrArg (fun g : Subring.unitClosedBall (Tate σ) ↦
      coeff t ((g : Tate σ) : MvPowerSeries σ K)) h
  · let g : MvPowerSeries σ (Subring.unitClosedBall K) :=
      fun t ↦ ⟨coeff t ((f : Tate σ) : MvPowerSeries σ K),
        Subring.mem_unitClosedBall.mpr (norm_coeff_le_one f t)⟩
    have hgc (t : σ →₀ ℕ) :
        coeff t g = ⟨coeff t ((f : Tate σ) : MvPowerSeries σ K),
          Subring.mem_unitClosedBall.mpr (norm_coeff_le_one f t)⟩ := (rfl)
    have hg : IsRestricted (fun _ : σ ↦ 1) g := by
      have hf : IsRestricted (fun _ : σ ↦ 1) ((f : Tate σ) : MvPowerSeries σ K) := (f : Tate σ).2
      simp only [IsRestricted] at hf ⊢
      simpa [hgc] using hf
    exact ⟨⟨g, hg⟩, Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ by
      simp [hom, hgc]⟩

/-- When `K°` is noetherian and `K` is complete, `K°` carries a Euclidean valuation degree
compatible with its ultrametric norm, so restricted power series over `K°` are noetherian. -/
private theorem isNoetherianRing_restricted_unitClosedBall [CompleteSpace K] [Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (IsRestricted.subring (R := Subring.unitClosedBall K) (fun _ : σ ↦ 1)) := by
  classical
  let O := Subring.unitClosedBall K
  have hclosed : IsClosed ((O : Subring K) : Set K) := by
    rw [Subring.coe_unitClosedBall]
    exact Metric.isClosed_closedBall
  have : CompleteSpace O := hclosed.completeSpace_coe
  obtain ⟨π, hπ1, hπ⟩ := exists_norm_lt_one_forall_norm_le_of_fg
    (IsNoetherian.noetherian (unitBallIdeal K))
  rcases eq_or_ne π 0 with rfl | hπ0
  · -- `K` is trivially normed, so every nonzero element of `K°` is invertible in `K°`.
    refine isNoetherianRing_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
      fun x y hx ↦ ?_
    have hxK : (x : K) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hx1 : ‖(x : K)‖ = 1 := (Subring.mem_unitClosedBall.mp x.2).antisymm <| not_lt.mp fun hlt ↦
      hxK (norm_le_zero_iff.mp ((hπ _ hlt).trans (by simp)))
    have hzx : ‖(y : K) * (x : K)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, hx1, inv_one, mul_one]
      exact Subring.mem_unitClosedBall.mp y.2
    exact ⟨⟨(y : K) * (x : K)⁻¹, Subring.mem_unitClosedBall.mpr hzx⟩, 0,
      Subtype.ext (by simp [inv_mul_cancel_right₀ hxK]), by simp, Or.inl rfl⟩
  · -- `0 < ‖π‖ < 1`, so nonzero elements of `K°` have norm `‖π‖ ^ n` for a unique `n : ℕ`.
    have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
    have hnat (x : O) (hx : x ≠ 0) : ∃ n : ℕ, ‖(x : K)‖ = ‖π‖ ^ n :=
      exists_norm_eq_pow_of_le_one hπpos hπ1 hπ (fun h ↦ hx (Subtype.ext h))
        (Subring.mem_unitClosedBall.mp x.2)
    let deg : O → ℕ := fun x ↦ if hx : x = 0 then 0 else Nat.find (hnat x hx)
    have hdeg_spec {x : O} (hx : x ≠ 0) : ‖(x : K)‖ = ‖π‖ ^ deg x := by
      simpa [deg, hx] using Nat.find_spec (hnat x hx)
    refine isNoetherianRing_isRestricted_subring_of_division deg (fun x y hxy ↦ ?_)
      fun x y hx ↦ ?_
    · have hx0 : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg (x - y)).trans_lt hxy)
      have hnorm : ‖x‖ = ‖y‖ := by
        simpa only [norm_neg] using IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := x) (y := -y)
          (by simpa only [sub_eq_add_neg] using hxy.trans_le (le_max_left ‖x‖ ‖-y‖))
      have hy0 : y ≠ 0 := norm_pos_iff.mp (hnorm ▸ norm_pos_iff.mpr hx0)
      have hpow : ‖π‖ ^ deg y = ‖π‖ ^ deg x := by
        rw [← hdeg_spec hy0, ← hdeg_spec hx0]
        exact hnorm.symm
      exact pow_right_injective₀ hπpos hπ1.ne hpow
    · rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨0, 0, by simp, by simp, Or.inl rfl⟩
      rcases le_or_gt (deg x) (deg y) with hle | hlt
      · have hnorm_le : ‖(y : K)‖ ≤ ‖(x : K)‖ := by
          rw [hdeg_spec hy0, hdeg_spec hx]
          exact pow_le_pow_of_le_one hπpos.le hπ1.le hle
        have hxK : (x : K) ≠ 0 := fun h ↦ hx (Subtype.ext h)
        have hzx : ‖(y : K) * (x : K)⁻¹‖ ≤ 1 := by
          rw [norm_mul, norm_inv, ← div_eq_mul_inv]
          exact div_le_one_of_le₀ hnorm_le (norm_nonneg _)
        exact ⟨⟨(y : K) * (x : K)⁻¹, Subring.mem_unitClosedBall.mpr hzx⟩, 0,
          Subtype.ext (by simp [inv_mul_cancel_right₀ hxK]), by simp, Or.inl rfl⟩
      · exact ⟨0, y, by simp, le_rfl, Or.inr hlt⟩

/-- **The Gauss unit ball of a Tate algebra over a complete field with noetherian unit ball is
noetherian.** This applies in particular when `K` is a complete discretely valued field. -/
instance isNoetherianRing_unitClosedBall [CompleteSpace K] [Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (Subring.unitClosedBall (Tate σ)) :=
  have := isNoetherianRing_restricted_unitClosedBall (σ := σ) (K := K)
  isNoetherianRing_of_ringEquiv _ restrictedUnitClosedBallEquiv

/-- **In finitely many variables, the Gauss unit ball `K⟨X⟩°` is noetherian if and only if `K°` is
noetherian.** -/
theorem isNoetherianRing_unitClosedBall_iff [CompleteSpace K] [Finite σ] :
    IsNoetherianRing (Subring.unitClosedBall (Tate σ)) ↔
      IsNoetherianRing (Subring.unitClosedBall K) :=
  ⟨fun _ ↦ isNoetherianRing_unitClosedBall_of_tate σ, fun _ ↦ inferInstance⟩

end Noetherian

section AlmostNoetherian

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- Uniform scalar approximation of submodules of an `R`-module `M` with respect to a scalar ring
map `φ : K° →+* R`. -/
private def IsAlmostNoetherianModule {R : Type*} [CommRing R]
    (φ : Subring.unitClosedBall K →+* R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (N : Submodule R M) {ε : ℝ}, 0 < ε → ε < 1 →
    ∃ N' : Submodule R M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, φ c • x ∈ N'

/-- Subsingleton modules are trivially almost noetherian. -/
private theorem isAlmostNoetherianModule_of_subsingleton {R : Type*} [CommRing R]
    (φ : Subring.unitClosedBall K →+* R) {M : Type*} [AddCommGroup M] [Module R M]
    [Subsingleton M] : IsAlmostNoetherianModule φ M := fun _ _ _ _ ↦
  ⟨⊥, Submodule.fg_bot, bot_le, fun _ _ _ _ ↦ by simp [Subsingleton.elim _ (0 : M)]⟩

/-- Surjective `R`-linear maps preserve `IsAlmostNoetherianModule`, with no loss in `ε`. -/
private theorem isAlmostNoetherianModule_of_surjective_linearMap {R : Type*} [CommRing R]
    {φ : Subring.unitClosedBall K →+* R} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f)
    (hM₁ : IsAlmostNoetherianModule φ M₁) : IsAlmostNoetherianModule φ M₂ := by
  intro N ε hε0 hε1
  obtain ⟨N₁', hfg, hle, hsmul⟩ := hM₁ (N.comap f) hε0 hε1
  refine ⟨N₁'.map f, hfg.map f, Submodule.map_le_iff_le_comap.mpr hle, fun c hc x hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hf x
  exact ⟨φ c • y, hsmul c hc y hx, map_smul f (φ c) y⟩

/-- When `K°` has no strict norm gap below `1`, every `0 < ε < 1` factors through an element
`d ∈ K°` with `√ε < ‖d‖ < 1`, so every `c ∈ K°` of norm at most `ε` writes as `c' * d` with
`‖c'‖ ≤ √ε`. -/
private theorem exists_factor_of_not_exists_forall_norm_le
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (δ : ℝ) (d : Subring.unitClosedBall K),
      0 < δ ∧ δ < 1 ∧ 0 < ‖(d : K)‖ ∧ ‖(d : K)‖ < 1 ∧ δ < ‖(d : K)‖ ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε →
        ∃ c' : Subring.unitClosedBall K, c = c' * d ∧ ‖(c' : K)‖ ≤ δ := by
  set δ := Real.sqrt ε
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr hε0
  have hδ1 : δ < 1 := (Real.sqrt_lt_sqrt hε0.le hε1).trans_eq Real.sqrt_one
  have hδ_sq : δ * δ = ε := Real.mul_self_sqrt hε0.le
  push Not at hdense
  obtain ⟨a, ha1, hδa⟩ := hdense δ hδ1
  let d : Subring.unitClosedBall K := ⟨a, Subring.mem_unitClosedBall.mpr ha1.le⟩
  have hd_pos : 0 < ‖(d : K)‖ := hδ0.trans hδa
  have hd0 : (d : K) ≠ 0 := norm_pos_iff.mp hd_pos
  refine ⟨δ, d, hδ0, hδ1, hd_pos, ha1, hδa, fun c hc ↦ ?_⟩
  have hdiv_le : ‖(c : K) / (d : K)‖ ≤ δ := by
    rw [norm_div, div_le_iff₀ hd_pos]
    calc ‖(c : K)‖ ≤ ε := hc
      _ = δ * δ := hδ_sq.symm
      _ ≤ δ * ‖(d : K)‖ := mul_le_mul_of_nonneg_left hδa.le hδ0.le
  exact ⟨⟨(c : K) / (d : K), Subring.mem_unitClosedBall.mpr (hdiv_le.trans hδ1.le)⟩,
    Subtype.ext (div_mul_cancel₀ _ hd0).symm, hdiv_le⟩

/-- Binary products preserve `IsAlmostNoetherianModule` when `K°` has dense norms below `1`. -/
private theorem isAlmostNoetherianModule_prod
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) {R : Type*} [CommRing R]
    {φ : Subring.unitClosedBall K →+* R} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (hM₁ : IsAlmostNoetherianModule φ M₁)
    (hM₂ : IsAlmostNoetherianModule φ M₂) : IsAlmostNoetherianModule φ (M₁ × M₂) := by
  classical
  intro N ε hε0 hε1
  obtain ⟨δ, d, hδ0, hδ1, hd0, hd1, -, hfac⟩ :=
    exists_factor_of_not_exists_forall_norm_le hdense hε0 hε1
  -- Approximate the projection to `M₂` at threshold `‖d‖` and lift finite generators back to `N`.
  obtain ⟨N₂', hN₂'fg, hN₂'le, hN₂'smul⟩ :=
    hM₂ (N.map (LinearMap.snd R M₁ M₂)) hd0 hd1
  obtain ⟨S₂, hS₂⟩ := hN₂'fg
  have hlift : ∀ z : S₂, ∃ w ∈ N, w.2 = (z : M₂) := fun z ↦ by
    obtain ⟨w, hw, hwz⟩ := hN₂'le (hS₂ ▸ Submodule.subset_span z.2)
    exact ⟨w, hw, hwz⟩
  choose liftF hliftN hlift_snd using hlift
  let L : Finset (M₁ × M₂) := Finset.univ.image liftF
  let Nlift : Submodule R (M₁ × M₂) := Submodule.span R (L : Set (M₁ × M₂))
  have hNlift_le : Nlift ≤ N := Submodule.span_le.mpr fun w hw ↦ by
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hw
    exact hliftN z
  have hN₂'_le_map : N₂' ≤ Nlift.map (LinearMap.snd R M₁ M₂) := by
    rw [← hS₂, Submodule.span_le]
    intro z hz
    exact ⟨liftF ⟨z, hz⟩, Submodule.subset_span (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
      hlift_snd ⟨z, hz⟩⟩
  -- Approximate the kernel slice `N ∩ (M₁ × 0)` at threshold `δ`.
  obtain ⟨N₁', hN₁'fg, hN₁'le, hN₁'smul⟩ :=
    hM₁ (N.comap (LinearMap.inl R M₁ M₂)) hδ0 hδ1
  refine ⟨N₁'.map (LinearMap.inl R M₁ M₂) ⊔ Nlift,
    (hN₁'fg.map _).sup (Submodule.fg_span L.finite_toSet),
    sup_le (Submodule.map_le_iff_le_comap.mpr hN₁'le) hNlift_le, fun c hc x hx ↦ ?_⟩
  obtain ⟨c', rfl, hc'δ⟩ := hfac c hc
  have hdx2 : φ d • x.2 ∈ N₂' := hN₂'smul d le_rfl x.2 ⟨x, hx, rfl⟩
  obtain ⟨w, hw_lift, hw_snd⟩ := hN₂'_le_map hdx2
  have hw_snd' : w.2 = φ d • x.2 := hw_snd
  have huN : φ d • x - w ∈ N := N.sub_mem (N.smul_mem (φ d) hx) (hNlift_le hw_lift)
  have hu2 : (φ d • x - w).2 = 0 := sub_eq_zero.mpr hw_snd'.symm
  have hu1_mem : (φ d • x - w).1 ∈ N.comap (LinearMap.inl R M₁ M₂) := by
    rw [Submodule.mem_comap, LinearMap.inl_apply, ← hu2, Prod.mk.eta]
    exact huN
  have hdecomp : φ (c' * d) • x =
      LinearMap.inl R M₁ M₂ (φ c' • (φ d • x - w).1) + φ c' • w := by
    ext
    · simp [map_mul, mul_smul, smul_sub]
    · simp [map_mul, mul_smul, hw_snd']
  rw [hdecomp]
  exact Submodule.add_mem_sup ⟨_, hN₁'smul c' hc'δ _ hu1_mem, rfl⟩ (Nlift.smul_mem _ hw_lift)

/-- Finite free `R`-modules `Fin n → R` inherit `IsAlmostNoetherianModule` from `R` when `K°` has
dense norms below `1`. -/
private theorem isAlmostNoetherianModule_fin_pi
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) {R : Type*} [CommRing R]
    {φ : Subring.unitClosedBall K →+* R} (hR : IsAlmostNoetherianModule φ R) :
    ∀ n : ℕ, IsAlmostNoetherianModule φ (Fin n → R)
  | 0 => isAlmostNoetherianModule_of_subsingleton φ
  | n + 1 => by
    let p : R × (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
      { toFun := fun q ↦ Fin.cons q.1 q.2
        map_add' := fun q₁ q₂ ↦ funext fun i ↦ Fin.cases (by simp) (by simp) i
        map_smul' := fun r q ↦ funext fun i ↦ Fin.cases (by simp) (by simp) i }
    have hp : Function.Surjective p := fun u ↦
      ⟨(u 0, fun i ↦ u i.succ), funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i⟩
    exact isAlmostNoetherianModule_of_surjective_linearMap p hp
      (isAlmostNoetherianModule_prod hdense hR (isAlmostNoetherianModule_fin_pi hdense hR n))

/-- Base case `IsEmpty σ`: `K⟨X⟩°` is isomorphic to `K°`, whose ideals are almost principal. -/
private theorem isAlmostNoetherianModule_of_isEmpty {σ : Type*} [IsEmpty σ] :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (K := K))
      (Subring.unitClosedBall (Tate σ)) := by
  intro I ε hε0 hε1
  let e : Subring.unitClosedBall K ≃+* Subring.unitClosedBall (Tate σ) :=
    RingEquiv.ofBijective (unitClosedBallCoeffHom (σ := σ) (K := K))
      ⟨fun a b h ↦ by
        have := congrArg (unitClosedBallConstantCoeffHom (σ := σ) (K := K)) h
        simpa using this,
       fun f ↦ ⟨unitClosedBallConstantCoeffHom f, Subtype.ext <| Subtype.ext <|
        MvPowerSeries.ext fun t ↦ by
          rw [Subsingleton.elim t 0]
          simp [coe_algebraMap_isRestrictedSubring, coeff_zero_eq_constantCoeff_apply]⟩⟩
  obtain ⟨x, hxI, hsmul⟩ :=
    (Ideal.comap e.toRingHom I).exists_span_singleton_le_forall_smul_mem_unitClosedBall hε0 hε1
  refine ⟨Ideal.span {e x}, Submodule.fg_span_singleton (e x),
    (Ideal.span_singleton_le_iff_mem _).mpr hxI, fun c hc y hy ↦ ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective y
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (hsmul c hc z hy)
  refine Ideal.mem_span_singleton'.mpr ⟨e q, ?_⟩
  have hce : unitClosedBallCoeffHom c = e c := (rfl)
  rw [smul_eq_mul, hce, ← map_mul, ← map_mul]
  exact congrArg e hq

/-- Restrict an isometric `K`-algebra equivalence of Tate algebras to a ring equivalence of their
Gauss unit balls. -/
private noncomputable def unitClosedBallRingEquivOfAlgEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖) :
    Subring.unitClosedBall (Tate σ) ≃+* Subring.unitClosedBall (Tate τ) where
  toFun f := ⟨e f, Subring.mem_unitClosedBall.mpr
    ((he f).le.trans (Subring.mem_unitClosedBall.mp f.2))⟩
  invFun g := ⟨e.symm g, Subring.mem_unitClosedBall.mpr <| by
    have hs : ‖e.symm g‖ = ‖(g : Tate τ)‖ := by
      conv_rhs => rw [← e.apply_symm_apply g]
      exact (he _).symm
    exact hs.le.trans (Subring.mem_unitClosedBall.mp g.2)⟩
  left_inv f := Subtype.ext (e.symm_apply_apply f)
  right_inv g := Subtype.ext (e.apply_symm_apply g)
  map_mul' f₁ f₂ := Subtype.ext (map_mul e (f₁ : Tate σ) (f₂ : Tate σ))
  map_add' f₁ f₂ := Subtype.ext (map_add e (f₁ : Tate σ) (f₂ : Tate σ))

@[simp]
private theorem coe_unitClosedBallRingEquivOfAlgEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖)
    (f : Subring.unitClosedBall (Tate σ)) :
    (unitClosedBallRingEquivOfAlgEquiv e he f : Tate τ) = e f := (rfl)

/-- Isometric `K`-algebra equivalences transport `IsAlmostNoetherianModule` between Gauss unit
balls. -/
private theorem isAlmostNoetherianModule_of_algEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖)
    (hσ : IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (K := K))
      (Subring.unitClosedBall (Tate σ))) :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := τ) (K := K))
      (Subring.unitClosedBall (Tate τ)) := by
  let e₀ := unitClosedBallRingEquivOfAlgEquiv e he
  have hec (c : Subring.unitClosedBall K) :
      e₀ (unitClosedBallCoeffHom c) = unitClosedBallCoeffHom c :=
    Subtype.ext (e.commutes (c : K))
  intro I ε hε0 hε1
  obtain ⟨I₁', hfg, hle, hsmul⟩ := hσ (Ideal.comap e₀.toRingHom I) hε0 hε1
  refine ⟨Ideal.map e₀.toRingHom I₁', Ideal.FG.map hfg e₀.toRingHom,
    Ideal.map_le_iff_le_comap.mpr hle, fun c hc y hy ↦ ?_⟩
  obtain ⟨z, rfl⟩ := e₀.surjective y
  have hmap := Ideal.mem_map_of_mem e₀.toRingHom (hsmul c hc z hy)
  simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, smul_eq_mul, map_mul, hec] using hmap

/-- Embed `K⟨X⟩°` into `K⟨X, Y⟩°` as series constant in the separated variable `X none`. -/
private noncomputable def optionEmbedHom (σ : Type*) :
    Subring.unitClosedBall (Tate σ) →+* Subring.unitClosedBall (Tate (Option σ)) where
  toFun b := ⟨(restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).symm
      ⟨PowerSeries.C (b : Tate σ), PowerSeries.isRestricted_C 1 (b : Tate σ)⟩,
    Subring.mem_unitClosedBall.mpr <| by
      rw [← norm_restrictedOptionEquiv (c := fun _ ↦ 1), AlgEquiv.apply_symm_apply,
        TauCeti.PowerSeries.norm_C]
      exact Subring.mem_unitClosedBall.mp b.2⟩
  map_one' := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective <| Subtype.ext (by simp)
  map_mul' u v := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective <| Subtype.ext (by simp)
  map_zero' := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective <| Subtype.ext (by simp)
  map_add' u v := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective <| Subtype.ext (by simp)

private theorem optionEmbedHom_coeff (σ : Type*) (c : Subring.unitClosedBall K) :
    optionEmbedHom σ (unitClosedBallCoeffHom c) = unitClosedBallCoeffHom c := by
  apply Subtype.ext
  apply (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective
  apply Subtype.ext
  simp only [optionEmbedHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    AlgEquiv.apply_symm_apply, coe_unitClosedBallCoeffHom, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply K (Tate σ) (PowerSeries.IsRestricted.subring (R := Tate σ) 1)]
  exact (MvPowerSeries.coe_algebraMap_isRestrictedSubring _).symm

/-- Parameterize series in `K⟨X, Y⟩°` of degree `< s` in `X none` by `Fin s → K⟨X⟩°`,
semilinearly over `optionEmbedHom σ`. -/
private noncomputable def optionTruncHom (σ : Type*) (s : ℕ) :
    (Fin s → Subring.unitClosedBall (Tate σ)) →ₛₗ[optionEmbedHom (K := K) σ]
      Subring.unitClosedBall (Tate (Option σ)) where
  toFun u :=
    let p : PowerSeries (Tate σ) :=
      PowerSeries.mk fun m ↦ if hm : m < s then (u ⟨m, hm⟩ : Tate σ) else 0
    have hp : PowerSeries.IsRestricted 1 p :=
      TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero (n := s) fun m hm ↦ by
        rw [PowerSeries.coeff_mk]
        split_ifs with h
        · exact absurd h (not_lt.mpr hm)
        · rfl
    ⟨(restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).symm ⟨p, hp⟩,
      Subring.mem_unitClosedBall.mpr <| by
        rw [← norm_restrictedOptionEquiv (c := fun _ ↦ 1), AlgEquiv.apply_symm_apply,
          TauCeti.PowerSeries.norm_le_iff]
        intro m
        simp only [p, PowerSeries.coeff_mk, one_pow, mul_one]
        split_ifs with hm
        · exact Subring.mem_unitClosedBall.mp (u ⟨m, hm⟩).2
        · simp⟩
  map_add' u₁ u₂ := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective <| Subtype.ext <|
      PowerSeries.ext fun m ↦ by
        simp only [AddMemClass.coe_add, map_add, AlgEquiv.apply_symm_apply,
          PowerSeries.coeff_mk, Pi.add_apply]
        split_ifs <;> simp
  map_smul' b u := Subtype.ext <|
    (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective <| Subtype.ext <|
      PowerSeries.ext fun m ↦ by
        simp only [optionEmbedHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, smul_eq_mul,
          MulMemClass.coe_mul, map_mul, AlgEquiv.apply_symm_apply, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_mk, Pi.smul_apply]
        split_ifs <;> simp

private theorem exists_optionTruncHom_eq {σ : Type*} {s : ℕ}
    (rd : Subring.unitClosedBall (Tate (Option σ)))
    (hrd : ∀ t : Option σ →₀ ℕ,
      s ≤ t none → coeff t ((rd : Tate (Option σ)) : MvPowerSeries (Option σ) K) = 0) :
    ∃ u : Fin s → Subring.unitClosedBall (Tate σ), optionTruncHom σ s u = rd := by
  let Riter := restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1) (rd : Tate (Option σ))
  have hzero := (forall_coeff_restrictedOptionEquiv_eq_zero_iff (rd : Tate (Option σ)) s).mpr hrd
  refine ⟨fun k ↦ ⟨PowerSeries.coeff (k : ℕ) (Riter : PowerSeries _),
    Subring.mem_unitClosedBall.mpr <| by
      have hle := TauCeti.PowerSeries.norm_coeff_mul_pow_le Riter (k : ℕ)
      rw [one_pow, mul_one, norm_restrictedOptionEquiv] at hle
      exact hle.trans (Subring.mem_unitClosedBall.mp rd.2)⟩, ?_⟩
  apply Subtype.ext
  apply (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective
  apply Subtype.ext
  refine PowerSeries.ext fun m ↦ ?_
  simp only [optionTruncHom, LinearMap.coe_mk, AddHom.coe_mk, AlgEquiv.apply_symm_apply,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · rfl
  · exact (hzero m (not_lt.mp hm)).symm

/-- Rescaled Weierstrass division in the Gauss unit ball: if `g' = a • g₀ ∈ K⟨X, Y⟩°` with
`‖g₀‖ = 1` distinguished of degree `s` in `X none` and `‖d‖ * α ≤ ‖a‖`, then for every
`h ∈ K⟨X, Y⟩°` of Gauss norm at most `α`, `d • h` decomposes in `K⟨X, Y⟩°` as an integral multiple
of `g'` plus an integral remainder of degree `< s` in `X none`. -/
private theorem exists_mul_add_optionTruncHom_of_isMulDistinguished [CompleteSpace K]
    {σ : Type*} {s : ℕ}
    {g' : Subring.unitClosedBall (Tate (Option σ))} {a : K} (ha_pos : 0 < ‖a‖)
    {g₀ : Tate (Option σ)} (hg' : (g' : Tate (Option σ)) = a • g₀) (hg₀_norm : ‖g₀‖ = 1)
    (hmul_dist : PowerSeries.IsMulDistinguished (1 : ℝ) s
      (restrictedOptionEquiv g₀ : PowerSeries (Tate σ)))
    {d : Subring.unitClosedBall K} {α : ℝ} (hα1 : α ≤ 1) (hdα : ‖(d : K)‖ * α ≤ ‖a‖)
    {h : Subring.unitClosedBall (Tate (Option σ))} (hh_norm : ‖(h : Tate (Option σ))‖ ≤ α) :
    ∃ (qd : Subring.unitClosedBall (Tate (Option σ)))
      (u : Fin s → Subring.unitClosedBall (Tate σ)),
      unitClosedBallCoeffHom d * h = g' * qd + optionTruncHom σ s u := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha_pos
  obtain ⟨q, r, hr_deg, hqr, hq_norm, hr_norm⟩ :=
    exists_mul_add_eq_of_isMulDistinguished
      (c := fun _ : Option σ ↦ (1 : ℝ)) hmul_dist (h : Tate (Option σ))
  rw [hg₀_norm, div_one] at hq_norm
  have hqd_le : ‖((d : K) * a⁻¹) • q‖ ≤ 1 := by
    rw [norm_smul, norm_mul, norm_inv]
    calc ‖(d : K)‖ * ‖a‖⁻¹ * ‖q‖
        ≤ ‖(d : K)‖ * ‖a‖⁻¹ * α :=
          mul_le_mul_of_nonneg_left (hq_norm.trans hh_norm) (by positivity)
      _ = (‖(d : K)‖ * α) / ‖a‖ := by ring
      _ ≤ 1 := div_le_one_of_le₀ hdα ha_pos.le
  let qd : Subring.unitClosedBall (Tate (Option σ)) :=
    ⟨((d : K) * a⁻¹) • q, Subring.mem_unitClosedBall.mpr hqd_le⟩
  have hrd_le : ‖(d : K) • r‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg r) (Subring.mem_unitClosedBall.mp d.2)).trans
      (hr_norm.trans (hh_norm.trans hα1))
  let rd : Subring.unitClosedBall (Tate (Option σ)) :=
    ⟨(d : K) • r, Subring.mem_unitClosedBall.mpr hrd_le⟩
  obtain ⟨u, hrem_u⟩ := exists_optionTruncHom_eq rd fun t ht ↦ by
    simp [rd, coe_smul_isRestrictedSubring, hr_deg t ht]
  refine ⟨qd, u, ?_⟩
  rw [hrem_u]
  apply Subtype.ext
  have hda : a * ((d : K) * a⁻¹) = (d : K) := by rw [mul_comm (d : K), mul_inv_cancel_left₀ ha0]
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, coe_unitClosedBallCoeffHom, qd, rd]
  rw [← Algebra.smul_def, hg', smul_mul_smul_comm, hda, ← smul_add, hqr]

/-- The inductive step `σ → Option σ` via triangular normalization and Weierstrass division when
`K°` has dense norms below `1`. -/
private theorem isAlmostNoetherianModule_option [CompleteSpace K] {σ : Type*} [Finite σ]
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ)
    (hσ : IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (K := K))
      (Subring.unitClosedBall (Tate σ))) :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := Option σ) (K := K))
      (Subring.unitClosedBall (Tate (Option σ))) := by
  classical
  intro I ε hε0 hε1
  set S : Set ℝ :=
    (fun f : Subring.unitClosedBall (Tate (Option σ)) ↦ ‖(f : Tate (Option σ))‖) '' (I : Set _)
  have hSne : S.Nonempty := ⟨0, 0, I.zero_mem, by simp⟩
  have hSbdd : BddAbove S := ⟨1, by rintro _ ⟨f, -, rfl⟩; exact Subring.mem_unitClosedBall.mp f.2⟩
  set α := sSup S
  have hα0 : 0 ≤ α := le_csSup_of_le hSbdd ⟨0, I.zero_mem, rfl⟩ (by simp)
  rcases hα0.eq_or_lt with hα | hα
  · refine ⟨⊥, Submodule.fg_bot, bot_le, fun _ _ f hf ↦ ?_⟩
    have hf0 : ‖(f : Tate (Option σ))‖ ≤ 0 := hα ▸ le_csSup hSbdd ⟨f, hf, rfl⟩
    have hfeq : f = 0 := Subtype.ext (norm_le_zero_iff.mp hf0)
    simp [hfeq]
  obtain ⟨δ, d, hδ0, hδ1, hd0, hd1, -, hfac⟩ :=
    exists_factor_of_not_exists_forall_norm_le hdense hε0 hε1
  -- Pick `g ∈ I` with `‖d‖ * α < ‖g‖ ≤ α`, normalize to `‖g₀‖ = 1`, and distinguish `g₀`.
  obtain ⟨_, ⟨g, hgI, rfl⟩, hgdα⟩ :=
    (lt_csSup_iff hSbdd hSne).mp (mul_lt_of_lt_one_left hα hd1)
  obtain ⟨t₀, ht₀⟩ := exists_norm_coeff_eq_norm (g : Tate (Option σ))
  set a : K := coeff t₀ ((g : Tate (Option σ)) : MvPowerSeries (Option σ) K)
  have ha_pos : 0 < ‖a‖ := (mul_pos hd0 hα).trans (ht₀ ▸ hgdα)
  set g₀ : Tate (Option σ) := a⁻¹ • (g : Tate (Option σ))
  have hg₀_norm : ‖g₀‖ = 1 := by rw [norm_smul, norm_inv, ← ht₀, inv_mul_cancel₀ ha_pos.ne']
  obtain ⟨β, hβ, s, hd_dist, hu_dist⟩ :=
    exists_restrictedTriangularEquiv_isDistinguished_isUnit g₀
      (norm_pos_iff.mp (one_pos.trans_eq hg₀_norm.symm))
  let e : Tate (Option σ) ≃ₐ[K] Tate (Option σ) := restrictedTriangularEquiv (R := K) β hβ
  have he_norm (f : Tate (Option σ)) : ‖e f‖ = ‖f‖ := norm_restrictedTriangularEquiv β hβ f
  let e₀ := unitClosedBallRingEquivOfAlgEquiv e he_norm
  have hec_symm (c : Subring.unitClosedBall K) :
      e₀.symm (unitClosedBallCoeffHom c) = unitClosedBallCoeffHom c :=
    Subtype.ext (e.symm.commutes (c : K))
  let J : Ideal (Subring.unitClosedBall (Tate (Option σ))) := Ideal.map e₀.toRingHom I
  have heg_mem : e₀ g ∈ J := Ideal.mem_map_of_mem _ hgI
  have hmul_dist : PowerSeries.IsMulDistinguished (1 : ℝ) s
      (restrictedOptionEquiv (e g₀) : PowerSeries (Tate σ)) :=
    PowerSeries.isMulDistinguished_iff_isUnit.mpr ⟨hd_dist, hu_dist⟩
  obtain ⟨Nrem', hNrem'fg, hNrem'le, hNrem'smul⟩ :=
    isAlmostNoetherianModule_fin_pi hdense hσ s (Submodule.comap (optionTruncHom σ s) J) hδ0 hδ1
  obtain ⟨G, hG⟩ := hNrem'fg
  let F : Finset (Subring.unitClosedBall (Tate (Option σ))) :=
    insert (e₀ g) (G.image (optionTruncHom σ s))
  let J' : Ideal (Subring.unitClosedBall (Tate (Option σ))) := Ideal.span (F : Set _)
  have hJ'le : J' ≤ J := Ideal.span_le.mpr fun z hz ↦ by
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact heg_mem
    · obtain ⟨u, huG, rfl⟩ := Finset.mem_image.mp hz'
      exact hNrem'le (hG ▸ Submodule.subset_span huG)
  have hα1 : α ≤ 1 := csSup_le hSne <| by
    rintro _ ⟨f, -, rfl⟩
    exact Subring.mem_unitClosedBall.mp f.2
  have heg : (e₀ g : Tate (Option σ)) = a • e g₀ := by
    rw [coe_unitClosedBallRingEquivOfAlgEquiv, ← map_smul, smul_inv_smul₀ (norm_pos_iff.mp ha_pos)]
  have hJ'smul (c : Subring.unitClosedBall K) (hc : ‖(c : K)‖ ≤ ε)
      (h : Subring.unitClosedBall (Tate (Option σ))) (hh : h ∈ J) :
      unitClosedBallCoeffHom (σ := Option σ) c • h ∈ J' := by
    obtain ⟨c', rfl, hc'δ⟩ := hfac c hc
    have hh_norm : ‖(h : Tate (Option σ))‖ ≤ α := by
      obtain ⟨f, hfI, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e₀.surjective).mp hh
      rw [coe_unitClosedBallRingEquivOfAlgEquiv, he_norm]
      exact le_csSup hSbdd ⟨f, hfI, rfl⟩
    obtain ⟨qd, u, hdh_eq⟩ := exists_mul_add_optionTruncHom_of_isMulDistinguished
      ha_pos heg ((he_norm g₀).trans hg₀_norm) hmul_dist hα1 (hgdα.le.trans_eq ht₀.symm) hh_norm
    have hu_mem : u ∈ Submodule.comap (optionTruncHom σ s) J := by
      rw [Submodule.mem_comap, eq_sub_of_add_eq' hdh_eq.symm]
      exact J.sub_mem (J.mul_mem_left _ hh) (J.mul_mem_right _ heg_mem)
    have hcu_mem : unitClosedBallCoeffHom (σ := σ) c' • u ∈ Submodule.span _ (G : Set _) :=
      hG ▸ hNrem'smul c' hc'δ u hu_mem
    have hrem_cu_mem : optionTruncHom σ s (unitClosedBallCoeffHom (σ := σ) c' • u) ∈ J' :=
      Submodule.span_induction
        (fun v hv ↦ Ideal.subset_span
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (optionTruncHom σ s) hv)))
        (by simp)
        (fun v₁ v₂ _ _ hv₁ hv₂ ↦ by rw [map_add]; exact J'.add_mem hv₁ hv₂)
        (fun b v _ hv ↦ by rw [map_smulₛₗ]; exact J'.smul_mem _ hv) hcu_mem
    have hfinal : unitClosedBallCoeffHom (σ := Option σ) (c' * d) • h =
        e₀ g * (unitClosedBallCoeffHom c' * qd) +
          optionTruncHom σ s (unitClosedBallCoeffHom (σ := σ) c' • u) := by
      rw [map_smulₛₗ, smul_eq_mul, optionEmbedHom_coeff, smul_eq_mul, map_mul, mul_assoc,
        hdh_eq, mul_add]
      ring
    rw [hfinal]
    exact J'.add_mem (J'.mul_mem_right _ (Ideal.subset_span (Finset.mem_insert_self _ _)))
      hrem_cu_mem
  -- Pull `J'` back along `e₀.symm` to obtain a finitely generated ideal `I' ≤ I`.
  refine ⟨Ideal.map e₀.symm.toRingHom J',
    Ideal.FG.map (Submodule.fg_span F.finite_toSet) e₀.symm.toRingHom,
    Ideal.map_le_iff_le_comap.mpr fun z hz ↦ ?_, fun c hc f hf ↦ ?_⟩
  · obtain ⟨f, hfI, hzf⟩ := (Ideal.mem_map_iff_of_surjective _ e₀.surjective).mp (hJ'le hz)
    simpa [← hzf] using hfI
  · have hmap := Ideal.mem_map_of_mem e₀.symm.toRingHom
      (hJ'smul c hc (e₀ f) (Ideal.mem_map_of_mem _ hf))
    simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, smul_eq_mul, map_mul, hec_symm,
      RingEquiv.symm_apply_apply] using hmap

/-- In the densely normed case, every Gauss unit ball `K⟨X⟩°` in finitely many variables satisfies
`IsAlmostNoetherianModule`. -/
private theorem isAlmostNoetherianModule_unitClosedBall_of_dense [CompleteSpace K] {σ : Type*}
    [Finite σ] (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (K := K))
      (Subring.unitClosedBall (Tate σ)) :=
  Finite.induction_empty_option
    (P := fun τ ↦ ∀ [Finite τ], IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := τ) (K := K))
      (Subring.unitClosedBall (Tate τ)))
    (fun {α β} e h _ ↦ by
      have : Finite α := .of_equiv β e.symm
      exact isAlmostNoetherianModule_of_algEquiv (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1)
        (IsRestricted.norm_renameAlgEquiv e fun _ ↦ 1) h)
    (fun {_} ↦ isAlmostNoetherianModule_of_isEmpty)
    (fun {_} _ h _ ↦ isAlmostNoetherianModule_option hdense h) σ

/-- **Kiehl's almost noetherianity theorem for any ring quotient of `K⟨X⟩°` (Satz 5.1).** Let `S`
be a commutative ring admitting a surjective ring homomorphism `ρ : K⟨X⟩° →+* S` in finitely many
variables over a complete ultrametric normed field `K`. For every finitely generated `S`-module `M`,
every submodule `N ≤ M`, and every `0 < ε < 1`, there is a single finitely generated `S`-submodule
`N' ≤ N` containing `ρ (unitClosedBallCoeffHom c) • x` for all `c ∈ K°` with `‖c‖ ≤ ε` and all
`x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_of_surjective [CompleteSpace K] {σ : Type*} [Finite σ]
    {S : Type*} [CommRing S] (ρ : Subring.unitClosedBall (Tate σ) →+* S)
    (hρ : Function.Surjective ρ) {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (N : Submodule S M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule S M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N,
        ρ (unitClosedBallCoeffHom c) • x ∈ N' := by
  classical
  by_cases hdisc : ∃ r : ℝ, r < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ r
  · -- Discrete or trivial norm: `K°`, hence `K⟨X⟩°`, hence `S` is noetherian, so `N` itself is FG.
    have : IsNoetherianRing (Subring.unitClosedBall K) :=
      isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr hdisc
    have : IsNoetherianRing S := isNoetherianRing_of_surjective _ _ ρ hρ
    exact ⟨N, IsNoetherian.noetherian N, le_rfl, fun _ _ _ hx ↦ N.smul_mem _ hx⟩
  · -- Dense norms below `1`: pull `N` back to a finite free `K⟨X⟩°`-module and push forward.
    have : RingHomSurjective ρ := ⟨hρ⟩
    obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' S M
    let p : (Fin r → Subring.unitClosedBall (Tate σ)) →ₛₗ[ρ] M :=
      { toFun := fun u ↦ f (fun i ↦ ρ (u i))
        map_add' := fun u₁ u₂ ↦ by
          have hadd : (fun i ↦ ρ ((u₁ + u₂) i)) = (fun i ↦ ρ (u₁ i)) + fun i ↦ ρ (u₂ i) := by
            funext i; simp
          rw [hadd, map_add]
        map_smul' := fun b u ↦ by
          have hsmul : (fun i ↦ ρ ((b • u) i)) = ρ b • fun i ↦ ρ (u i) := by
            funext i; simp [smul_eq_mul]
          rw [hsmul, map_smul] }
    have hp_surj : Function.Surjective p := fun x ↦ by
      obtain ⟨v, rfl⟩ := hf x
      choose u hu using fun i ↦ hρ (v i)
      exact ⟨u, by simp [p, hu]⟩
    obtain ⟨N₀', hN₀'fg, hN₀'le, hN₀'smul⟩ :=
      isAlmostNoetherianModule_fin_pi hdisc
        (isAlmostNoetherianModule_unitClosedBall_of_dense hdisc) r (N.comap p) hε0 hε1
    refine ⟨N₀'.map p, hN₀'fg.map p, Submodule.map_le_iff_le_comap.mpr hN₀'le, fun c hc x hx ↦ ?_⟩
    obtain ⟨u, rfl⟩ := hp_surj x
    exact ⟨unitClosedBallCoeffHom c • u, hN₀'smul c hc u hx, map_smulₛₗ p _ u⟩

/-- **Kiehl's almost noetherianity theorem for the Gauss unit ball `K⟨X⟩°` (Satz 5.1).** Over any
complete ultrametric normed field `K`, for every finitely generated `K⟨X⟩°`-module `M`, every
submodule `N ≤ M`, and every `0 < ε < 1`, there is a single finitely generated submodule `N' ≤ N`
containing `unitClosedBallCoeffHom c • x` for all `c ∈ K°` with `‖c‖ ≤ ε` and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_unitClosedBall [CompleteSpace K] {σ : Type*} [Finite σ]
    {M : Type*} [AddCommGroup M] [Module (Subring.unitClosedBall (Tate σ)) M]
    [Module.Finite (Subring.unitClosedBall (Tate σ)) M]
    (N : Submodule (Subring.unitClosedBall (Tate σ)) M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule (Subring.unitClosedBall (Tate σ)) M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N,
        unitClosedBallCoeffHom (σ := σ) c • x ∈ N' :=
  exists_fg_le_forall_smul_mem_of_surjective (RingHom.id (Subring.unitClosedBall (Tate σ)))
    Function.surjective_id N hε0 hε1

end AlmostNoetherian

end TauCeti.MvPowerSeries

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Completed integral restricted series agree with the Gauss unit ball.** Over a complete
nontrivially normed ultrametric field `K`, `restrictedMvPowerSeriesCompletion n 𝒪[K]` is identified
with `Subring.unitClosedBall (K⟨X₁, …, Xₙ⟩)`, preserving scalar constants from `𝒪[K]`. -/
noncomputable def restrictedMvPowerSeriesCompletionIntegerEquiv (n : ℕ) :
    restrictedMvPowerSeriesCompletion n 𝒪[K] ≃+*
      Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
  (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := 𝒪[K])).trans restrictedIntegerEquiv

theorem restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap (n : ℕ) (c : 𝒪[K]) :
    restrictedMvPowerSeriesCompletionIntegerEquiv n (algebraMap 𝒪[K] _ c) =
      unitClosedBallCoeffHom (integerUnitClosedBallEquiv c) := by
  have halg : restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := 𝒪[K])
      (algebraMap 𝒪[K] _ c) = algebraMap 𝒪[K] _ c := by
    rw [← coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv, AlgEquiv.commutes]
  rw [restrictedMvPowerSeriesCompletionIntegerEquiv, RingEquiv.trans_apply, halg]
  apply Subtype.ext
  apply Subtype.ext
  ext t
  rw [coeff_restrictedIntegerEquiv, coe_unitClosedBallCoeffHom, coe_algebraMap_isRestrictedSubring,
    coe_algebraMap_isRestrictedSubring, coeff_C, coeff_C]
  split_ifs <;> simp

/-- `restrictedMvPowerSeriesCompletionIntegerEquiv` is continuous from the completion topology on
`𝒪[K]⟨X₁, …, Xₙ⟩` to the subspace Gauss-norm topology on `K⟨X₁, …, Xₙ⟩°`. -/
theorem continuous_restrictedMvPowerSeriesCompletionIntegerEquiv (n : ℕ) :
    Continuous (restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n) := by
  have hisom : Isometry (restrictedIntegerEquiv (σ := Fin n) (K := K)) :=
    Isometry.of_dist_eq fun f g ↦ by
      rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm, ← AddSubgroupClass.coe_sub, ← map_sub,
        norm_restrictedIntegerEquiv]
  rw [restrictedMvPowerSeriesCompletionIntegerEquiv, RingEquiv.coe_trans]
  exact hisom.continuous.comp
    (continuous_restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := 𝒪[K]))

/-- The inverse of `restrictedMvPowerSeriesCompletionIntegerEquiv` is continuous. -/
theorem continuous_restrictedMvPowerSeriesCompletionIntegerEquiv_symm (n : ℕ) :
    Continuous (restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n).symm := by
  have hisom : Isometry (restrictedIntegerEquiv (σ := Fin n) (K := K)).symm :=
    Isometry.of_dist_eq fun f g ↦ by
      rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, ← norm_restrictedIntegerEquiv,
        map_sub, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddSubgroupClass.coe_sub]
  rw [restrictedMvPowerSeriesCompletionIntegerEquiv, RingEquiv.symm_trans, RingEquiv.coe_trans]
  exact (continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm (n := n) (R := 𝒪[K])).comp
    hisom.continuous

/-- **Noetherianity of `𝒪[K]⟨X₁, …, Xₙ⟩` over a complete discretely valued field.** When `𝒪[K]` is a
discrete valuation ring, the completed integral restricted-series ring
`restrictedMvPowerSeriesCompletion n 𝒪[K]` is noetherian. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion_integer (n : ℕ)
    [IsDiscreteValuationRing 𝒪[K]] :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion n 𝒪[K]) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_ringEquiv 𝒪[K] (integerUnitClosedBallEquiv (K := K))
  exact isNoetherianRing_of_ringEquiv _ (restrictedMvPowerSeriesCompletionIntegerEquiv n).symm

end TauCeti.Huber
