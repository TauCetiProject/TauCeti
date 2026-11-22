/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.Noetherian.Almost

import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Division

/-!
# Noetherianity and almost noetherianity of the Gauss unit ball of a Tate algebra

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
and let `T = K⟨X⟩` be the Tate algebra of unit-radius restricted power series in finitely many
variables `σ`, with Gauss unit ball `T° = Subring.unitClosedBall T`.

When `K°` is noetherian — equivalently when `K` has a strict norm gap below `1`, that is, when `K`
is either trivially normed or discretely valued — `K°` carries a Euclidean valuation degree
compatible with its ultrametric norm: an element of larger norm (smaller degree) divides one of
smaller norm in `K°`, while an element of strictly smaller degree (strictly larger norm) is left as
remainder. Kedlaya's Gröbner-basis theorem
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`) therefore makes
`K°{X/r}`, `𝒪[K]{X/r}`, and `T°` noetherian rings for every positive polyradius `r`. Conversely,
the constant-coefficient retraction descends noetherianity from `R{X/r}°` to `R°` over any
ultrametric normed commutative ring `R` with `‖1‖ = 1`.

Over an arbitrary complete ultrametric normed field `K`, such as `ℂ_p`, `T°` need not be noetherian.
Kiehl's Satz 5.1 proves that finite `T°`-modules are nevertheless *almost noetherian*
(`TauCeti.IsAlmostNoetherianModule`): for every finitely generated `T°`-module `M`, every submodule
`N ≤ M`, and every `0 < ε < 1`, there is a single finitely generated submodule `N' ≤ N` containing
`c • N` for **all** scalars `c ∈ K°` with `‖c‖ ≤ ε`. When `K°` is noetherian one takes `N' = N`.
Otherwise the norms below `1` are dense up to `1`, so any `0 < ε < 1` factors through elements of
`K°` of norm strictly between `√ε` and `1`:

* exactness on finite free modules (`TauCeti.IsAlmostNoetherianModule.of_finite`) reduces the
  statement from finite `T°`-modules to ideals `I` of `T°`;
* for `I ≠ ⊥`, an element `g ∈ I` whose Gauss norm exceeds `‖d‖ · sup_{f ∈ I} ‖f‖` normalizes to a
  series `g₀` of Gauss norm `1`, which an isometric triangular automorphism makes distinguished of
  some degree `s` in one separated variable `Y`;
* Weierstrass division by `g₀` writes `d • f` as an integral multiple of `g` plus a remainder in `I`
  of degree less than `s` in `Y`, reducing to a submodule of `(T'°)^s` in one fewer variable.

## Main results

* `isNoetherianRing_unitClosedBall_of_isNoetherianRing_restrictedUnitClosedBall` (in
  `TauCeti.MvPowerSeries`): if `R{X/r}°` is noetherian, then `R°` is noetherian.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_unitClosedBall` and
  `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_integer`: in finitely many variables
  at any positive polyradius `r`, `K°{X/r}` (and `𝒪[K]{X/r}` for nontrivially normed `K`) is
  noetherian whenever `K°` (respectively `𝒪[K]`) is noetherian and `K` is complete.
* `TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall`: `T°` is noetherian when `K°` is.
* `TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall_iff`: in finitely many variables, `T°` is
  noetherian if and only if `K°` is.
* `TauCeti.MvPowerSeries.isAlmostNoetherianModule_unitClosedBall`: `T°` is almost noetherian over
  `K°`.
* `RingHom.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall`: Kiehl's Satz 5.1 for finite
  modules over any ring receiving a surjection from `T°`.
* `Submodule.exists_fg_le_forall_smul_mem_unitClosedBall`: Kiehl's Satz 5.1 for finite modules over
  `T°`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, Int. Math. Res. Not. 2016
  (2016), no. 8, 2544–2567.
-/

public section

open _root_.MvPowerSeries Filter Topology
open scoped NormedField Valued

namespace TauCeti.MvPowerSeries

section Noetherian

/-- If the Gauss unit ball `R{X/r}°` of a restricted power-series ring is noetherian, then `R°` is
noetherian, via the constant-coefficient retraction. -/
theorem isNoetherianRing_unitClosedBall_of_isNoetherianRing_restrictedUnitClosedBall {R : Type*}
    [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] (σ : Type*) (r : σ → ℝ)
    [∀ i, Fact (0 < r i)]
    [IsNoetherianRing (Subring.unitClosedBall (IsRestricted.subring (R := R) r))] :
    IsNoetherianRing (Subring.unitClosedBall R) :=
  isNoetherianRing_of_surjective _ _ (unitClosedBallConstantCoeffHom (σ := σ) (r := r)) fun c ↦
    ⟨unitClosedBallCoeffHom c, unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom c⟩

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Restricted power series over `K°` are noetherian when `K°` is noetherian.** Over a complete
ultrametric normed field `K` with noetherian closed unit ball `K°`, `K°` carries a Euclidean
valuation degree compatible with its ultrametric norm, so `K°{X/r}` is noetherian for every finite
variable set `σ` and positive polyradius `r`. -/
instance isNoetherianRing_isRestricted_subring_unitClosedBall [CompleteSpace K] [Finite σ]
    {r : σ → ℝ} [∀ i, Fact (0 < r i)] [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (IsRestricted.subring (R := Subring.unitClosedBall K) r) := by
  classical
  let O := Subring.unitClosedBall K
  have hclosed : IsClosed ((O : Subring K) : Set K) := by
    rw [Subring.coe_unitClosedBall]
    exact Metric.isClosed_closedBall
  have : CompleteSpace O := hclosed.completeSpace_coe
  obtain ⟨π, hπ1, hπ⟩ := exists_norm_lt_one_forall_norm_le_of_fg
    (IsNoetherian.noetherian (unitBallIdeal K))
  rcases eq_or_ne π 0 with rfl | hπ0
  · -- `K` is trivially normed, so every nonzero element of `K°` has norm `1` and divides every
    -- element of `K°`.
    refine isNoetherianRing_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
      fun x y hx ↦ ?_
    have hxK : (x : K) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hx1 : ‖(x : K)‖ = 1 :=
      (Subring.mem_unitClosedBall.mp x.property).antisymm <| not_lt.mp fun hlt ↦
        hxK (norm_le_zero_iff.mp ((hπ _ hlt).trans (by simp)))
    obtain ⟨q, hq⟩ := Subring.unitClosedBall.dvd_iff_norm_le.mpr
      ((Subring.mem_unitClosedBall.mp y.property).trans_eq hx1.symm)
    exact ⟨q, 0, by rw [add_zero, mul_comm, hq], by simp, Or.inl rfl⟩
  · -- `0 < ‖π‖ < 1`, so nonzero elements of `K°` have norm `‖π‖ ^ n` for a unique `n : ℕ`.
    have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
    have hnat (x : O) (hx : x ≠ 0) : ∃ n : ℕ, ‖(x : K)‖ = ‖π‖ ^ n :=
      exists_norm_eq_pow_of_forall_norm_le_of_norm_le_one hπpos hπ1 hπ
        (fun h ↦ hx (Subtype.ext h)) (Subring.mem_unitClosedBall.mp x.property)
    let deg : O → ℕ := fun x ↦ if hx : x = 0 then 0 else Nat.find (hnat x hx)
    have hdeg_spec {x : O} (hx : x ≠ 0) : ‖(x : K)‖ = ‖π‖ ^ deg x := by
      simpa [deg, hx] using Nat.find_spec (hnat x hx)
    refine isNoetherianRing_isRestricted_subring_of_division deg (fun x y hxy ↦ ?_)
      fun x y hx ↦ ?_
    · have hx0 : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg (x - y)).trans_lt hxy)
      have hnorm : ‖x‖ = ‖y‖ := IsUltrametricDist.norm_eq_of_norm_sub_lt_left hxy
      have hy0 : y ≠ 0 := norm_pos_iff.mp (hnorm ▸ norm_pos_iff.mpr hx0)
      have hpow : ‖π‖ ^ deg y = ‖π‖ ^ deg x := by
        rw [← hdeg_spec hy0, ← hdeg_spec hx0, ← AddSubgroupClass.coe_norm,
          ← AddSubgroupClass.coe_norm, hnorm]
      exact pow_right_injective₀ hπpos hπ1.ne hpow
    · rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨0, 0, by simp, by simp, Or.inl rfl⟩
      rcases le_or_gt (deg x) (deg y) with hle | hlt
      · have hnorm_le : ‖(y : K)‖ ≤ ‖(x : K)‖ := by
          rw [hdeg_spec hy0, hdeg_spec hx]
          exact pow_le_pow_of_le_one hπpos.le hπ1.le hle
        obtain ⟨q, hq⟩ := Subring.unitClosedBall.dvd_iff_norm_le.mpr hnorm_le
        exact ⟨q, 0, by rw [add_zero, mul_comm, hq], by simp, Or.inl rfl⟩
      · exact ⟨0, y, by simp, le_rfl, Or.inr hlt⟩

/-- **Restricted power series over `𝒪[K]` are noetherian when `𝒪[K]` is noetherian.** Over a
complete nontrivially normed ultrametric field `K` with noetherian valuation ring `𝒪[K]`
(equivalently, a discrete valuation ring), `𝒪[K]{X/r}` is noetherian for every finite variable set
`σ` and positive polyradius `r`. -/
instance isNoetherianRing_isRestricted_subring_integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ] {r : σ → ℝ} [∀ i, Fact (0 < r i)]
    [IsNoetherianRing 𝒪[K]] :
    IsNoetherianRing (IsRestricted.subring (R := 𝒪[K]) r) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_ringEquiv 𝒪[K] (integerUnitClosedBallEquiv (K := K))
  exact isNoetherianRing_of_ringEquiv _
    (restrictedIntegerUnitClosedBallEquiv (σ := σ) (K := K) (r := r)).symm

/-- **The Gauss unit ball of a Tate algebra over a complete field with noetherian unit ball is
noetherian.** This applies in particular when `K` is a complete discretely valued field. -/
instance isNoetherianRing_unitClosedBall [CompleteSpace K] [Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] :
    IsNoetherianRing (Subring.unitClosedBall (Tate σ)) :=
  isNoetherianRing_of_ringEquiv _ restrictedUnitClosedBallEquiv

/-- **In finitely many variables, the Gauss unit ball `K⟨X⟩°` is noetherian if and only if `K°` is
noetherian.** -/
theorem isNoetherianRing_unitClosedBall_iff [CompleteSpace K] [Finite σ] :
    IsNoetherianRing (Subring.unitClosedBall (Tate σ)) ↔
      IsNoetherianRing (Subring.unitClosedBall K) :=
  ⟨fun _ ↦
      isNoetherianRing_unitClosedBall_of_isNoetherianRing_restrictedUnitClosedBall σ (fun _ ↦ 1),
    fun _ ↦ inferInstance⟩

end Noetherian

section AlmostNoetherian

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- Base case `IsEmpty σ`: `K⟨X⟩°` is isomorphic to `K°`, whose ideals are almost principal. -/
private theorem isAlmostNoetherianModule_of_isEmpty {σ : Type*} [IsEmpty σ] :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ)) := by
  rw [isAlmostNoetherianModule_iff]
  intro I ε _ hε1
  let e : Subring.unitClosedBall K ≃+* Subring.unitClosedBall (Tate σ) :=
    (IsRestricted.isEmptyEquiv (R := K) (fun _ : σ ↦ (1 : ℝ))).symm.toRingEquiv.restrict
      (Subring.unitClosedBall K) (Subring.unitClosedBall (Tate σ)) fun c ↦ by
        simp [Subring.mem_unitClosedBall, IsRestricted.isEmptyEquiv_symm_apply]
  have hce (c : Subring.unitClosedBall K) :
      unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c = e c :=
    Subtype.ext <| by
      simp [e, RingEquiv.restrict_apply_coe, IsRestricted.isEmptyEquiv_symm_apply]
  obtain ⟨x, hxI, hsmul⟩ :=
    (Ideal.comap e.toRingHom I).exists_mem_forall_smul_mem_span_singleton_unitClosedBall hε1
  refine ⟨Ideal.span {e x}, Submodule.fg_span_singleton (e x),
    (Ideal.span_singleton_le_iff_mem _).mpr hxI, fun c hc y hy ↦ ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective y
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (hsmul c hc z hy)
  refine Ideal.mem_span_singleton'.mpr ⟨e q, ?_⟩
  rw [smul_eq_mul, hce, ← map_mul, ← map_mul]
  exact congrArg e hq

/-- Isometric `K`-algebra equivalences transport `IsAlmostNoetherianModule` between Gauss unit
balls. -/
private theorem isAlmostNoetherianModule_of_algEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖)
    (hσ : IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ))) :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := τ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate τ)) := by
  let e₀ := e.toRingEquiv.restrict (Subring.unitClosedBall _) (Subring.unitClosedBall _)
    fun f ↦ by simp [Subring.mem_unitClosedBall, he]
  have hcomp : e₀.toRingHom.comp (unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1)) =
      unitClosedBallCoeffHom (σ := τ) (r := fun _ ↦ 1) :=
    RingHom.ext fun c ↦ Subtype.ext <| by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.restrict_apply_coe, AlgEquiv.coe_toRingEquiv, coe_unitClosedBallCoeffHom,
        coe_unitClosedBallCoeffHom]
      exact e.commutes (c : K)
  rw [← hcomp]
  exact hσ.of_surjective_ringHom e₀.surjective

/-- Embed `K⟨X⟩°` into `K⟨X, Y⟩°` as series constant in the separated variable `X none`. -/
private noncomputable def optionEmbedHom (σ : Type*) :
    Subring.unitClosedBall (Tate σ) →+* Subring.unitClosedBall (Tate (Option σ)) :=
  ((restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).symm.toRingHom.comp
    (algebraMap (Tate σ) (PowerSeries.IsRestricted.subring (R := Tate σ) 1))).restrict _ _
    fun b hb ↦ Subring.mem_unitClosedBall.mpr <| by
      have ha : algebraMap (Tate σ) (PowerSeries.IsRestricted.subring (R := Tate σ) 1) b =
          ⟨PowerSeries.C b, PowerSeries.isRestricted_C 1 b⟩ := Subtype.ext (by simp)
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toRingEquiv, ← norm_restrictedOptionEquiv (c := fun _ ↦ 1),
        AlgEquiv.apply_symm_apply, ha, TauCeti.PowerSeries.norm_C]
      exact Subring.mem_unitClosedBall.mp hb

private theorem optionEmbedHom_coeff (σ : Type*) (c : Subring.unitClosedBall K) :
    optionEmbedHom σ (unitClosedBallCoeffHom c) = unitClosedBallCoeffHom c := by
  apply Subtype.ext
  apply (restrictedOptionEquiv (σ := σ) (R := K) (c := fun _ ↦ 1)).injective
  simp only [optionEmbedHom, RingHom.coe_restrict_apply, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.apply_symm_apply, coe_unitClosedBallCoeffHom, AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply K (Tate σ)
    (PowerSeries.IsRestricted.subring (R := Tate σ) 1) (c : K)).symm

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
        · exact Subring.mem_unitClosedBall.mp (u ⟨m, hm⟩).property
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
        simp only [optionEmbedHom, smul_eq_mul, MulMemClass.coe_mul, map_mul,
          RingHom.coe_restrict_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.apply_symm_apply,
          TauCeti.PowerSeries.coe_algebraMap_isRestrictedSubring,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Pi.smul_apply]
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
      exact hle.trans (Subring.mem_unitClosedBall.mp rd.property)⟩, ?_⟩
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
`‖g₀‖ = 1` distinguished of degree `s` in `X none` and `‖d‖ * ‖h‖ ≤ ‖a‖`, then `d • h` decomposes
in `K⟨X, Y⟩°` as an integral multiple of `g'` plus an integral remainder of degree `< s` in
`X none`. -/
private theorem exists_mul_add_optionTruncHom_of_isMulDistinguished [CompleteSpace K]
    {σ : Type*} {s : ℕ}
    {g' : Subring.unitClosedBall (Tate (Option σ))} {a : K} (ha_pos : 0 < ‖a‖)
    {g₀ : Tate (Option σ)} (hg' : (g' : Tate (Option σ)) = a • g₀) (hg₀_norm : ‖g₀‖ = 1)
    (hmul_dist : PowerSeries.IsMulDistinguished (1 : ℝ) s
      (restrictedOptionEquiv g₀ : PowerSeries (Tate σ)))
    {d : Subring.unitClosedBall K} {h : Subring.unitClosedBall (Tate (Option σ))}
    (hdh : ‖(d : K)‖ * ‖(h : Tate (Option σ))‖ ≤ ‖a‖) :
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
        ≤ ‖(d : K)‖ * ‖a‖⁻¹ * ‖(h : Tate (Option σ))‖ :=
          mul_le_mul_of_nonneg_left hq_norm (by positivity)
      _ = (‖(d : K)‖ * ‖(h : Tate (Option σ))‖) / ‖a‖ := by ring
      _ ≤ 1 := div_le_one_of_le₀ hdh ha_pos.le
  let qd : Subring.unitClosedBall (Tate (Option σ)) :=
    ⟨((d : K) * a⁻¹) • q, Subring.mem_unitClosedBall.mpr hqd_le⟩
  have hrd_le : ‖(d : K) • r‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg r) (Subring.mem_unitClosedBall.mp d.property)).trans
      (hr_norm.trans (Subring.mem_unitClosedBall.mp h.property))
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

/-- Weierstrass-remainder approximation for an ideal `J` of `K⟨X, Y⟩°` containing a rescaled
multiplicatively distinguished series `g' = a • g₀` dominating `‖d‖ * ‖h‖` on `J`. -/
private theorem exists_fg_le_forall_smul_mem_of_isMulDistinguished [CompleteSpace K] {σ : Type*}
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ)
    (hσ : IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ)))
    {s : ℕ} {J : Ideal (Subring.unitClosedBall (Tate (Option σ)))}
    {g' : Subring.unitClosedBall (Tate (Option σ))} (hg'J : g' ∈ J) {a : K} (ha_pos : 0 < ‖a‖)
    {g₀ : Tate (Option σ)} (hg' : (g' : Tate (Option σ)) = a • g₀) (hg₀_norm : ‖g₀‖ = 1)
    (hmul_dist : PowerSeries.IsMulDistinguished (1 : ℝ) s
      (restrictedOptionEquiv g₀ : PowerSeries (Tate σ)))
    {ε δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {d : Subring.unitClosedBall K}
    (hfac : ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε →
      ∃ c' : Subring.unitClosedBall K, c = c' * d ∧ ‖(c' : K)‖ ≤ δ)
    (hdom : ∀ h ∈ J, ‖(d : K)‖ * ‖(h : Tate (Option σ))‖ ≤ ‖a‖) :
    ∃ J' : Ideal (Subring.unitClosedBall (Tate (Option σ))), J'.FG ∧ J' ≤ J ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ h ∈ J,
        unitClosedBallCoeffHom (σ := Option σ) (r := fun _ ↦ 1) c • h ∈ J' := by
  classical
  obtain ⟨Nrem', hNrem'fg, hNrem'le, hNrem'smul⟩ :=
    (hσ.fin_pi hdense s).exists_fg_le_forall_smul_mem (Submodule.comap (optionTruncHom σ s) J)
      hδ0 hδ1
  obtain ⟨G, hG⟩ := hNrem'fg
  let F : Finset (Subring.unitClosedBall (Tate (Option σ))) :=
    insert g' (G.image (optionTruncHom σ s))
  let J' : Ideal (Subring.unitClosedBall (Tate (Option σ))) := Ideal.span (F : Set _)
  have hJ'le : J' ≤ J := Ideal.span_le.mpr fun z hz ↦ by
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hg'J
    · obtain ⟨u, huG, rfl⟩ := Finset.mem_image.mp hz'
      exact hNrem'le (hG ▸ Submodule.subset_span huG)
  have hNrem'_le_comap : Nrem' ≤ Submodule.comap (optionTruncHom σ s) J' := by
    rw [← hG, Submodule.span_le]
    intro v hv
    exact Ideal.subset_span (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))
  refine ⟨J', Submodule.fg_span F.finite_toSet, hJ'le, fun c hc h hh ↦ ?_⟩
  obtain ⟨c', rfl, hc'δ⟩ := hfac c hc
  obtain ⟨qd, u, hdh_eq⟩ := exists_mul_add_optionTruncHom_of_isMulDistinguished
    ha_pos hg' hg₀_norm hmul_dist (hdom h hh)
  have hu_mem : u ∈ Submodule.comap (optionTruncHom σ s) J := by
    rw [Submodule.mem_comap, eq_sub_of_add_eq' hdh_eq.symm]
    exact J.sub_mem (J.mul_mem_left _ hh) (J.mul_mem_right _ hg'J)
  have hrem_cu_mem : optionTruncHom σ s
      (unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c' • u) ∈ J' :=
    hNrem'_le_comap (hNrem'smul c' hc'δ u hu_mem)
  have hfinal : unitClosedBallCoeffHom (σ := Option σ) (r := fun _ ↦ 1) (c' * d) • h =
      g' * (unitClosedBallCoeffHom c' * qd) +
        optionTruncHom σ s (unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c' • u) := by
    rw [map_smulₛₗ, smul_eq_mul, optionEmbedHom_coeff, smul_eq_mul, map_mul, mul_assoc,
      hdh_eq, mul_add]
    ring
  rw [hfinal]
  exact J'.add_mem (J'.mul_mem_right _ (Ideal.subset_span (Finset.mem_insert_self _ _)))
    hrem_cu_mem

/-- The inductive step `σ → Option σ` via triangular normalization and Weierstrass division when
`K°` has dense norms below `1`. -/
private theorem isAlmostNoetherianModule_option [CompleteSpace K] {σ : Type*} [Finite σ]
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ)
    (hσ : IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ))) :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := Option σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate (Option σ))) := by
  rw [isAlmostNoetherianModule_iff]
  intro I ε hε0 hε1
  obtain ⟨δ, d, hδ0, hδ1, -, hd1, -, hfac⟩ :=
    exists_factor_of_not_exists_forall_norm_le hdense hε0 hε1
  rcases Ideal.eq_bot_or_exists_mem_forall_mul_norm_le_unitClosedBall I hd1 with
    rfl | ⟨g, hgI, hg0, hgd⟩
  · exact ⟨⊥, Submodule.fg_bot, bot_le, fun _ _ _ hf ↦ by simp_all⟩
  -- Normalize `g ∈ I` to Gauss norm `1` and apply an isometric triangular automorphism.
  obtain ⟨t₀, ht₀⟩ := exists_norm_coeff_eq_norm (g : Tate (Option σ))
  set a : K := coeff t₀ ((g : Tate (Option σ)) : MvPowerSeries (Option σ) K)
  have ha_pos : 0 < ‖a‖ := ht₀.symm ▸ hg0
  set g₀ : Tate (Option σ) := a⁻¹ • (g : Tate (Option σ))
  have hg₀_norm : ‖g₀‖ = 1 := by rw [norm_smul, norm_inv, ← ht₀, inv_mul_cancel₀ ha_pos.ne']
  obtain ⟨β, hβ, s, hd_dist, hu_dist⟩ :=
    exists_restrictedTriangularEquiv_isDistinguished_isUnit g₀
      (norm_pos_iff.mp (one_pos.trans_eq hg₀_norm.symm))
  let e : Tate (Option σ) ≃ₐ[K] Tate (Option σ) := restrictedTriangularEquiv (R := K) β hβ
  have he_norm (f : Tate (Option σ)) : ‖e f‖ = ‖f‖ := norm_restrictedTriangularEquiv β hβ f
  let e₀ := e.toRingEquiv.restrict (Subring.unitClosedBall _) (Subring.unitClosedBall _)
    fun f ↦ by simp [Subring.mem_unitClosedBall, he_norm]
  have hec_symm (c : Subring.unitClosedBall K) :
      e₀.symm (unitClosedBallCoeffHom c) = unitClosedBallCoeffHom c :=
    Subtype.ext <| by
      rw [RingEquiv.restrict_symm_apply_coe, coe_unitClosedBallCoeffHom,
        RingEquiv.symm_apply_eq, AlgEquiv.coe_toRingEquiv]
      exact (e.commutes (c : K)).symm
  let J : Ideal (Subring.unitClosedBall (Tate (Option σ))) := Ideal.map e₀.toRingHom I
  have heg : (e₀ g : Tate (Option σ)) = a • e g₀ := by
    rw [RingEquiv.restrict_apply_coe, AlgEquiv.coe_toRingEquiv, ← map_smul,
      smul_inv_smul₀ (norm_pos_iff.mp ha_pos)]
  have hdom (h : Subring.unitClosedBall (Tate (Option σ))) (hh : h ∈ J) :
      ‖(d : K)‖ * ‖(h : Tate (Option σ))‖ ≤ ‖a‖ := by
    obtain ⟨f, hfI, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e₀.surjective).mp hh
    rw [RingEquiv.restrict_apply_coe, AlgEquiv.coe_toRingEquiv, he_norm, ht₀]
    exact hgd f hfI
  obtain ⟨J', hJ'fg, hJ'le, hJ'smul⟩ := exists_fg_le_forall_smul_mem_of_isMulDistinguished
    hdense hσ
    (Ideal.mem_map_of_mem _ hgI) ha_pos heg ((he_norm g₀).trans hg₀_norm)
    (PowerSeries.isMulDistinguished_iff_isUnit.mpr ⟨hd_dist, hu_dist⟩) hδ0 hδ1 hfac hdom
  -- Pull `J'` back along `e₀.symm` to obtain a finitely generated ideal `I' ≤ I`.
  refine ⟨Ideal.map e₀.symm.toRingHom J', Ideal.FG.map hJ'fg e₀.symm.toRingHom,
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
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ)) :=
  Finite.induction_empty_option
    (P := fun τ ↦ IsAlmostNoetherianModule
      (unitClosedBallCoeffHom (σ := τ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate τ)))
    (fun e h ↦ isAlmostNoetherianModule_of_algEquiv
      (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1)
      (IsRestricted.norm_renameAlgEquiv e fun _ ↦ 1) h)
    isAlmostNoetherianModule_of_isEmpty
    (fun h ↦ isAlmostNoetherianModule_option hdense h) σ

/-- **The Gauss unit ball `K⟨X⟩°` is almost noetherian.** Over any complete ultrametric normed
field `K` and finite variable set `σ`, `K⟨X⟩°` satisfies `TauCeti.IsAlmostNoetherianModule` with
respect to `unitClosedBallCoeffHom`. -/
theorem isAlmostNoetherianModule_unitClosedBall [CompleteSpace K] {σ : Type*} [Finite σ] :
    IsAlmostNoetherianModule (unitClosedBallCoeffHom (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ)) := by
  by_cases hdisc : ∃ r : ℝ, r < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ r
  · have : IsNoetherianRing (Subring.unitClosedBall K) :=
      isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr hdisc
    exact .of_isNoetherian
  · exact isAlmostNoetherianModule_unitClosedBall_of_dense hdisc

/-- **Kiehl's almost noetherianity theorem for any ring quotient of `K⟨X⟩°` (Satz 5.1).** Let `S`
be a commutative ring admitting a surjective ring homomorphism `ρ : K⟨X⟩° →+* S` in finitely many
variables over a complete ultrametric normed field `K`. For every finitely generated `S`-module `M`,
every submodule `N ≤ M`, and every `0 < ε < 1`, there is a single finitely generated `S`-submodule
`N' ≤ N` containing `ρ (unitClosedBallCoeffHom c) • x` for all `c ∈ K°` with `‖c‖ ≤ ε` and all
`x ∈ N`. -/
theorem _root_.RingHom.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall [CompleteSpace K]
    {σ : Type*} [Finite σ] {S : Type*} [CommRing S]
    (ρ : Subring.unitClosedBall (Tate σ) →+* S) (hρ : Function.Surjective ρ)
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (N : Submodule S M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule S M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N,
        ρ (unitClosedBallCoeffHom c) • x ∈ N' := by
  by_cases hdisc : ∃ r : ℝ, r < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ r
  · -- Discrete or trivial norm: `K°`, hence `K⟨X⟩°`, hence `S` is noetherian, so `N` itself is FG.
    have : IsNoetherianRing (Subring.unitClosedBall K) :=
      isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr hdisc
    have : IsNoetherianRing S := isNoetherianRing_of_surjective _ _ ρ hρ
    exact (IsAlmostNoetherianModule.of_isNoetherian
      (φ := ρ.comp (unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1)))).exists_fg_le_forall_smul_mem
      N hε0 hε1
  · -- Dense norms below `1`: descend almost noetherianity along `ρ` and lift to finite modules.
    exact ((isAlmostNoetherianModule_unitClosedBall.of_surjective_ringHom hρ).of_finite
      hdisc M).exists_fg_le_forall_smul_mem N hε0 hε1

/-- **Kiehl's almost noetherianity theorem for the Gauss unit ball `K⟨X⟩°` (Satz 5.1).** Over any
complete ultrametric normed field `K`, for every finitely generated `K⟨X⟩°`-module `M`, every
submodule `N ≤ M`, and every `0 < ε < 1`, there is a single finitely generated submodule `N' ≤ N`
containing `unitClosedBallCoeffHom c • x` for all `c ∈ K°` with `‖c‖ ≤ ε` and all `x ∈ N`. -/
theorem _root_.Submodule.exists_fg_le_forall_smul_mem_unitClosedBall [CompleteSpace K] {σ : Type*}
    [Finite σ] {M : Type*} [AddCommGroup M] [Module (Subring.unitClosedBall (Tate σ)) M]
    [Module.Finite (Subring.unitClosedBall (Tate σ)) M]
    (N : Submodule (Subring.unitClosedBall (Tate σ)) M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule (Subring.unitClosedBall (Tate σ)) M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N,
        unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c • x ∈ N' :=
  (RingHom.id (Subring.unitClosedBall (Tate σ)))
    |>.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall Function.surjective_id N hε0 hε1

end AlmostNoetherian

end TauCeti.MvPowerSeries
