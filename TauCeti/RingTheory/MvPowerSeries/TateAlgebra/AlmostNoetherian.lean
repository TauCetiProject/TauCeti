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
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Noetherian
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBallIterate
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Division

/-!
# Kiehl's almost noetherianity theorem for the Gauss unit ball of a Tate algebra

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
and let `T = K⟨X⟩` be the Tate algebra of unit-radius restricted power series in finitely many
variables `σ`, with Gauss unit ball `T° = Subring.unitClosedBall T`.

When `K°` is noetherian — equivalently when `K` is either trivially normed or discretely valued —
`K°{X/r}` and `T°` in finitely many variables are noetherian rings
(`TauCeti.MvPowerSeries.isNoetherianRing_unitClosedBall`), and when `K` is moreover nontrivially
normed, `𝒪[K]{X/r}` is likewise noetherian whenever `𝒪[K]` is
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_integer`).

Over an arbitrary complete ultrametric normed field `K`, such as `ℂ_p`, `T°` need not be noetherian.
Kiehl's Satz 5.1 proves that finite `T°`-modules are nevertheless *almost noetherian*
(`TauCeti.IsAlmostNoetherianModule`): for every finitely generated `T°`-module `M`, every submodule
`N ≤ M`, and every `0 < ε < 1`, there is a single finitely generated submodule `N' ≤ N` containing
`c • N` for **all** scalars `c ∈ K°` with `‖c‖ ≤ ε`. When `K°` is noetherian one takes `N' = N`.
Otherwise the norms below `1` are dense up to `1`, so for each `0 < ε < 1` there is a single
`d ∈ K°` that divides every scalar `c ∈ K°` with `‖c‖ ≤ ε`, with quotient norm at most `√ε`:

* reduction via finite powers of the regular module and descent along a surjection onto a finitely
  generated module (`TauCeti.IsAlmostNoetherianModule.of_finite`) passes from ideals `I` of `T°` to
  arbitrary finite `T°`-modules;
* for `I ≠ ⊥`, an element `g ∈ I` whose Gauss norm exceeds `‖d‖ · sup_{f ∈ I} ‖f‖` normalizes to a
  series `g₀` of Gauss norm `1`, which Nagata's isometric triangular change of variables
  (`TauCeti.MvPowerSeries.restrictedTriangularEquiv`, via
  `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished_isUnit`) makes
  multiplicatively distinguished of some degree `s` in one separated variable `Y`;
* Weierstrass division by the normalized distinguished series
  (`TauCeti.MvPowerSeries.exists_mul_add_eq_of_isMulDistinguished`) writes `d • f` as an integral
  multiple of `g` plus a remainder in `I` of degree less than `s` in `Y`, reducing to a submodule
  of `(T'°)^s` in one fewer variable.

## Main results

* `TauCeti.MvPowerSeries.isAlmostNoetherianModule_unitClosedBall`: `T°` is almost noetherian over
  `K°`.
* `RingHom.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall`: Kiehl's Satz 5.1 for finite
  modules over any ring receiving a surjection from `T°`.
* `Submodule.exists_fg_le_forall_smul_mem_unitClosedBall`: Kiehl's Satz 5.1 for finite modules over
  `T°`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.2.1 and 5.2.4,
  for Weierstrass division and Nagata's triangular change of variables.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
-/

public section

open _root_.MvPowerSeries Filter Topology
open scoped NormedField Valued

namespace TauCeti.MvPowerSeries

section AlmostNoetherian

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- Base case `IsEmpty σ`: `K⟨X⟩°` is isomorphic to `K°`, whose ideals are almost principal. -/
private theorem isAlmostNoetherianModule_of_isEmpty {σ : Type*} [IsEmpty σ] :
    IsAlmostNoetherianModule (unitClosedBallC (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ)) := by
  rw [isAlmostNoetherianModule_iff]
  intro I ε _ hε1
  let e : Subring.unitClosedBall K ≃+* Subring.unitClosedBall (Tate σ) :=
    (IsRestricted.isEmptyEquiv (R := K) (fun _ : σ ↦ (1 : ℝ))).symm.toRingEquiv.restrict
      (Subring.unitClosedBall K) (Subring.unitClosedBall (Tate σ)) fun c ↦ by
        simp [Subring.mem_unitClosedBall, IsRestricted.isEmptyEquiv_symm_apply]
  have hce (c : Subring.unitClosedBall K) :
      unitClosedBallC (σ := σ) (r := fun _ ↦ 1) c = e c :=
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

/-- Restrict an isometric `K`-algebra equivalence `Tate σ ≃ₐ[K] Tate τ` to the Gauss unit
balls. -/
private noncomputable def unitClosedBallAlgEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖) :
    Subring.unitClosedBall (Tate σ) ≃+* Subring.unitClosedBall (Tate τ) :=
  e.toRingEquiv.restrict (Subring.unitClosedBall _) (Subring.unitClosedBall _) fun f ↦ by
    simp [Subring.mem_unitClosedBall, he]

private theorem coe_unitClosedBallAlgEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖) (f : Subring.unitClosedBall (Tate σ)) :
    (unitClosedBallAlgEquiv e he f : Tate τ) = e f := (rfl)

private theorem unitClosedBallAlgEquiv_unitClosedBallC {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖) (c : Subring.unitClosedBall K) :
    unitClosedBallAlgEquiv e he (unitClosedBallC c) = unitClosedBallC c :=
  Subtype.ext <| by
    rw [coe_unitClosedBallAlgEquiv, coe_unitClosedBallC, coe_unitClosedBallC]
    exact e.commutes (c : K)

private theorem unitClosedBallAlgEquiv_symm_unitClosedBallC {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖) (c : Subring.unitClosedBall K) :
    (unitClosedBallAlgEquiv e he).symm (unitClosedBallC c) = unitClosedBallC c :=
  (unitClosedBallAlgEquiv e he).injective <| by
    rw [RingEquiv.apply_symm_apply, unitClosedBallAlgEquiv_unitClosedBallC]

/-- Isometric `K`-algebra equivalences transport `IsAlmostNoetherianModule` between Gauss unit
balls. -/
private theorem isAlmostNoetherianModule_of_algEquiv {σ τ : Type*}
    (e : Tate σ ≃ₐ[K] Tate τ) (he : ∀ f, ‖e f‖ = ‖f‖)
    (hσ : IsAlmostNoetherianModule (unitClosedBallC (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ))) :
    IsAlmostNoetherianModule (unitClosedBallC (σ := τ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate τ)) := by
  let e₀ := unitClosedBallAlgEquiv e he
  have hcomp : e₀.toRingHom.comp (unitClosedBallC (σ := σ) (r := fun _ ↦ 1)) =
      unitClosedBallC (σ := τ) (r := fun _ ↦ 1) :=
    RingHom.ext (unitClosedBallAlgEquiv_unitClosedBallC e he)
  rw [← hcomp]
  exact hσ.of_surjective_ringHom e₀.surjective

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
      unitClosedBallC d * h = g' * qd + optionTruncHom σ s u := by
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
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, coe_unitClosedBallC, qd, rd]
  rw [← Algebra.smul_def, hg', smul_mul_smul_comm, hda, ← smul_add, hqr]

/-- Weierstrass-remainder approximation for an ideal `J` of `K⟨X, Y⟩°` containing a rescaled
multiplicatively distinguished series `g' = a • g₀` dominating `‖d‖ * ‖h‖` on `J`. -/
private theorem exists_fg_le_forall_smul_mem_of_isMulDistinguished [CompleteSpace K] {σ : Type*}
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ)
    (hσ : IsAlmostNoetherianModule (unitClosedBallC (σ := σ) (R := K) (r := fun _ ↦ 1))
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
        unitClosedBallC (σ := Option σ) (r := fun _ ↦ 1) c • h ∈ J' := by
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
      (unitClosedBallC (σ := σ) (r := fun _ ↦ 1) c' • u) ∈ J' :=
    hNrem'_le_comap (hNrem'smul c' hc'δ u hu_mem)
  have hfinal : unitClosedBallC (σ := Option σ) (r := fun _ ↦ 1) (c' * d) • h =
      g' * (unitClosedBallC c' * qd) +
        optionTruncHom σ s (unitClosedBallC (σ := σ) (r := fun _ ↦ 1) c' • u) := by
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
    (hσ : IsAlmostNoetherianModule (unitClosedBallC (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ))) :
    IsAlmostNoetherianModule (unitClosedBallC (σ := Option σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate (Option σ))) := by
  rw [isAlmostNoetherianModule_iff]
  intro I ε hε0 hε1
  obtain ⟨δ, d, hδ0, hδ1, -, hd1, -, hfac⟩ :=
    exists_forall_exists_eq_mul_and_norm_le_of_not_exists_forall_norm_le hdense hε0 hε1
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
  let e₀ := unitClosedBallAlgEquiv e he_norm
  let J : Ideal (Subring.unitClosedBall (Tate (Option σ))) := Ideal.map e₀.toRingHom I
  have heg : (e₀ g : Tate (Option σ)) = a • e g₀ := by
    rw [coe_unitClosedBallAlgEquiv, ← map_smul, smul_inv_smul₀ (norm_pos_iff.mp ha_pos)]
  have hdom (h : Subring.unitClosedBall (Tate (Option σ))) (hh : h ∈ J) :
      ‖(d : K)‖ * ‖(h : Tate (Option σ))‖ ≤ ‖a‖ := by
    obtain ⟨f, hfI, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e₀.surjective).mp hh
    rw [coe_unitClosedBallAlgEquiv, he_norm, ht₀]
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
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, smul_eq_mul, map_mul,
      RingEquiv.symm_apply_apply] at hmap
    change e₀.symm (unitClosedBallC c) * f ∈ Ideal.map e₀.symm.toRingHom J' at hmap
    dsimp [e₀] at hmap
    rwa [unitClosedBallAlgEquiv_symm_unitClosedBallC] at hmap

/-- In the densely normed case, every Gauss unit ball `K⟨X⟩°` in finitely many variables satisfies
`IsAlmostNoetherianModule`. -/
private theorem isAlmostNoetherianModule_unitClosedBall_of_dense [CompleteSpace K] {σ : Type*}
    [Finite σ] (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsAlmostNoetherianModule (unitClosedBallC (σ := σ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate σ)) :=
  Finite.induction_empty_option
    (P := fun τ ↦ IsAlmostNoetherianModule
      (unitClosedBallC (σ := τ) (R := K) (r := fun _ ↦ 1))
      (Subring.unitClosedBall (Tate τ)))
    (fun e h ↦ isAlmostNoetherianModule_of_algEquiv
      (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1)
      (IsRestricted.norm_renameAlgEquiv e fun _ ↦ 1) h)
    isAlmostNoetherianModule_of_isEmpty
    (fun h ↦ isAlmostNoetherianModule_option hdense h) σ

/-- **The Gauss unit ball `K⟨X⟩°` is almost noetherian.** Over any complete ultrametric normed
field `K` and finite variable set `σ`, `K⟨X⟩°` satisfies `TauCeti.IsAlmostNoetherianModule` with
respect to `unitClosedBallC`. -/
theorem isAlmostNoetherianModule_unitClosedBall [CompleteSpace K] {σ : Type*} [Finite σ] :
    IsAlmostNoetherianModule (unitClosedBallC (σ := σ) (R := K) (r := fun _ ↦ 1))
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
`N' ≤ N` containing `ρ (unitClosedBallC c) • x` for all `c ∈ K°` with `‖c‖ ≤ ε` and all
`x ∈ N`. -/
theorem _root_.RingHom.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall [CompleteSpace K]
    {σ : Type*} [Finite σ] {S : Type*} [CommRing S]
    (ρ : Subring.unitClosedBall (Tate σ) →+* S) (hρ : Function.Surjective ρ)
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (N : Submodule S M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule S M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N,
        ρ (unitClosedBallC c) • x ∈ N' := by
  by_cases hdisc : ∃ r : ℝ, r < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ r
  · -- Discrete or trivial norm: `K°`, hence `K⟨X⟩°`, hence `S` is noetherian, so `N` itself is FG.
    have : IsNoetherianRing (Subring.unitClosedBall K) :=
      isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr hdisc
    have : IsNoetherianRing S := isNoetherianRing_of_surjective _ _ ρ hρ
    exact (IsAlmostNoetherianModule.of_isNoetherian
      (φ := ρ.comp (unitClosedBallC (σ := σ) (r := fun _ ↦ 1)))).exists_fg_le_forall_smul_mem
      N hε0 hε1
  · -- Dense norms below `1`: descend almost noetherianity along `ρ` and lift to finite modules.
    exact ((isAlmostNoetherianModule_unitClosedBall.of_surjective_ringHom hρ).of_finite
      hdisc M).exists_fg_le_forall_smul_mem N hε0 hε1

/-- **Kiehl's almost noetherianity theorem for the Gauss unit ball `K⟨X⟩°` (Satz 5.1).** Over any
complete ultrametric normed field `K`, for every finitely generated module `M` over `K⟨X⟩°` in
finitely many variables, every submodule `N ≤ M`, and every `0 < ε < 1`, there is a single finitely
generated submodule `N' ≤ N` containing `unitClosedBallC c • x` for all `c ∈ K°` with `‖c‖ ≤ ε`
and all `x ∈ N`. -/
theorem _root_.Submodule.exists_fg_le_forall_smul_mem_unitClosedBall [CompleteSpace K] {σ : Type*}
    [Finite σ] {M : Type*} [AddCommGroup M] [Module (Subring.unitClosedBall (Tate σ)) M]
    [Module.Finite (Subring.unitClosedBall (Tate σ)) M]
    (N : Submodule (Subring.unitClosedBall (Tate σ)) M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule (Subring.unitClosedBall (Tate σ)) M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N,
        unitClosedBallC (σ := σ) (r := fun _ ↦ 1) c • x ∈ N' :=
  (RingHom.id (Subring.unitClosedBall (Tate σ)))
    |>.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall Function.surjective_id N hε0 hε1

end AlmostNoetherian

end TauCeti.MvPowerSeries
