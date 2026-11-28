/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.Analysis.Normed.Ring.Ultra

import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# Almost noetherian modules over ultrametric scalar rings

Let `K` be an ultrametric seminormed ring with `‖1‖ = 1` and closed unit ball
`K° = Subring.unitClosedBall K`, and let `φ : K° →+* R` be a ring homomorphism. An `R`-module `M`
is *almost noetherian* with respect to `φ` (`TauCeti.IsAlmostNoetherianModule φ M`) if for every
submodule `N ≤ M` and every `0 < ε < 1`, there exists a single finitely generated `R`-submodule
`N' ≤ N` containing `φ c • x` for **all** scalars `c ∈ K°` with `‖(c : K)‖ ≤ ε` and all `x ∈ N`.

Every noetherian `R`-module and every subsingleton `R`-module is almost noetherian, and the
property descends along surjective semilinear maps, surjective linear maps, and surjective ring
homomorphisms with no loss in `ε`. Over an ultrametric normed field `K` whose norms below `1` have
no strict upper bound below `1` (the non-noetherian case for `K°`, such as `ℂ_p`), for each
`0 < ε < 1` there is a single scalar `d ∈ K°` with `√ε < ‖d‖ < 1` that divides every `c ∈ K°` of
norm at most `ε` as `c = c' * d` with quotient norm `‖c'‖ ≤ √ε`
(`TauCeti.exists_forall_exists_eq_mul_and_norm_le_of_not_exists_forall_norm_le`). This implies that
almost noetherianity is preserved under finite products (`TauCeti.IsAlmostNoetherianModule.prod`,
`TauCeti.IsAlmostNoetherianModule.fin_pi`) and passes from `R` to every finitely generated
`R`-module (`TauCeti.IsAlmostNoetherianModule.of_finite`).

## Main definitions

* `TauCeti.IsAlmostNoetherianModule`: uniform scalar approximation of submodules by finitely
  generated submodules with respect to `φ : Subring.unitClosedBall K →+* R`.

## Main results

* `TauCeti.isAlmostNoetherianModule_iff` and
  `TauCeti.IsAlmostNoetherianModule.exists_fg_le_forall_smul_mem`: unfolding characterizations.
* `TauCeti.IsAlmostNoetherianModule.of_isNoetherian` and
  `TauCeti.IsAlmostNoetherianModule.of_subsingleton`: noetherian and subsingleton modules are
  almost noetherian.
* `TauCeti.IsAlmostNoetherianModule.of_surjective_semilinearMap`,
  `TauCeti.IsAlmostNoetherianModule.of_surjective_linearMap`, and
  `TauCeti.IsAlmostNoetherianModule.of_surjective_ringHom`: descent along surjections.
* `TauCeti.IsAlmostNoetherianModule.prod`, `TauCeti.IsAlmostNoetherianModule.fin_pi`, and
  `TauCeti.IsAlmostNoetherianModule.of_finite`: closure under finite products and finitely
  generated modules when `K` has no strict norm gap below `1`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
-/

public section

namespace TauCeti

section Semiring

variable {K : Type*} [SeminormedRing K] [IsUltrametricDist K] [NormOneClass K]
  {R : Type*} [Semiring R]

/-- **Almost noetherian modules over an ultrametric scalar ring.** An `R`-module `M` is almost
noetherian with respect to `φ : Subring.unitClosedBall K →+* R` if for every submodule `N ≤ M` and
every `0 < ε < 1`, there is a single finitely generated submodule `N' ≤ N` containing `φ c • x` for
all scalars `c ∈ K°` with `‖(c : K)‖ ≤ ε` and all `x ∈ N`. -/
def IsAlmostNoetherianModule (φ : Subring.unitClosedBall K →+* R) (M : Type*)
    [AddCommMonoid M] [Module R M] : Prop :=
  ∀ (N : Submodule R M) {ε : ℝ}, 0 < ε → ε < 1 →
    ∃ N' : Submodule R M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, φ c • x ∈ N'

/-- Unfolding `IsAlmostNoetherianModule`. -/
theorem isAlmostNoetherianModule_iff {φ : Subring.unitClosedBall K →+* R} {M : Type*}
    [AddCommMonoid M] [Module R M] :
    IsAlmostNoetherianModule φ M ↔
      ∀ (N : Submodule R M) {ε : ℝ}, 0 < ε → ε < 1 →
        ∃ N' : Submodule R M, N'.FG ∧ N' ≤ N ∧
          ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, φ c • x ∈ N' :=
  Iff.rfl

namespace IsAlmostNoetherianModule

/-- Extract a finitely generated approximating submodule from `IsAlmostNoetherianModule`. -/
theorem exists_fg_le_forall_smul_mem {φ : Subring.unitClosedBall K →+* R} {M : Type*}
    [AddCommMonoid M] [Module R M] (hM : IsAlmostNoetherianModule φ M) (N : Submodule R M)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule R M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, φ c • x ∈ N' :=
  hM N hε0 hε1

/-- Every noetherian module is almost noetherian (taking `N' = N`). -/
theorem of_isNoetherian {φ : Subring.unitClosedBall K →+* R} {M : Type*} [AddCommMonoid M]
    [Module R M] [IsNoetherian R M] : IsAlmostNoetherianModule φ M := fun N _ _ _ ↦
  ⟨N, IsNoetherian.noetherian N, le_rfl, fun _ _ _ hx ↦ N.smul_mem _ hx⟩

/-- Every subsingleton module is trivially almost noetherian. -/
theorem of_subsingleton {φ : Subring.unitClosedBall K →+* R} {M : Type*} [AddCommMonoid M]
    [Module R M] [Subsingleton M] : IsAlmostNoetherianModule φ M := fun _ _ _ _ ↦
  ⟨⊥, Submodule.fg_bot, bot_le, fun _ _ _ _ ↦ by simp [Subsingleton.elim _ (0 : M)]⟩

/-- Surjective semilinear maps along a surjective ring homomorphism preserve
`IsAlmostNoetherianModule`, with no loss in `ε`. -/
theorem of_surjective_semilinearMap {S : Type*} [Semiring S] {φ : Subring.unitClosedBall K →+* R}
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module S M₂]
    (hM₁ : IsAlmostNoetherianModule φ M₁) {ρ : R →+* S} (hρ : Function.Surjective ρ)
    (f : M₁ →ₛₗ[ρ] M₂) (hf : Function.Surjective f) :
    IsAlmostNoetherianModule (ρ.comp φ) M₂ := by
  have : RingHomSurjective ρ := ⟨hρ⟩
  intro N ε hε0 hε1
  obtain ⟨N₁', hfg, hle, hsmul⟩ := hM₁ (N.comap f) hε0 hε1
  refine ⟨N₁'.map f, hfg.map f, Submodule.map_le_iff_le_comap.mpr hle, fun c hc x hx ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hf x
  exact ⟨φ c • y, hsmul c hc y hx, map_smulₛₗ f (φ c) y⟩

/-- Surjective `R`-linear maps preserve `IsAlmostNoetherianModule`, with no loss in `ε`. -/
theorem of_surjective_linearMap {φ : Subring.unitClosedBall K →+* R} {M₁ M₂ : Type*}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    (hM₁ : IsAlmostNoetherianModule φ M₁) (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f) :
    IsAlmostNoetherianModule φ M₂ := by
  simpa only [RingHom.id_comp] using
    hM₁.of_surjective_semilinearMap Function.surjective_id f hf

/-- Surjective ring homomorphisms preserve `IsAlmostNoetherianModule` on the regular module. -/
theorem of_surjective_ringHom {S : Type*} [Semiring S] {φ : Subring.unitClosedBall K →+* R}
    (hR : IsAlmostNoetherianModule φ R) {ρ : R →+* S} (hρ : Function.Surjective ρ) :
    IsAlmostNoetherianModule (ρ.comp φ) S :=
  hR.of_surjective_semilinearMap hρ ρ.toSemilinearMap hρ

end IsAlmostNoetherianModule

end Semiring

section DenseNormField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {R : Type*} [Ring R]

namespace IsAlmostNoetherianModule

/-- Binary products preserve `IsAlmostNoetherianModule` when `K` has no strict norm gap below `1`.
-/
theorem prod {φ : Subring.unitClosedBall K →+* R} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (hM₁ : IsAlmostNoetherianModule φ M₁)
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ)
    (hM₂ : IsAlmostNoetherianModule φ M₂) : IsAlmostNoetherianModule φ (M₁ × M₂) := by
  intro N ε hε0 hε1
  obtain ⟨δ, d, hδ0, hδ1, hd0, hd1, -, hfac⟩ :=
    exists_forall_exists_eq_mul_and_norm_le_of_not_exists_forall_norm_le hdense hε0 hε1
  -- Approximate the projection to `M₂` at threshold `‖d‖` and lift finite generators back to `N`.
  obtain ⟨N₂', hN₂'fg, hN₂'le, hN₂'smul⟩ :=
    hM₂ (N.map (LinearMap.snd R M₁ M₂)) hd0 hd1
  obtain ⟨S₂, hS₂⟩ := hN₂'fg
  obtain ⟨T, hTN, hTfin, hTspan⟩ := Set.exists_subset_image_finite_and
    (f := LinearMap.snd R M₁ M₂) (s := (N : Set (M₁ × M₂)))
    (p := fun t ↦ Submodule.span R t = N₂').mp
    ⟨S₂, fun _ hz ↦ hN₂'le (hS₂ ▸ Submodule.subset_span hz), S₂.finite_toSet, hS₂⟩
  let Nlift : Submodule R (M₁ × M₂) := Submodule.span R T
  have hNlift_le : Nlift ≤ N := Submodule.span_le.mpr hTN
  have hN₂'_le_map : N₂' ≤ Nlift.map (LinearMap.snd R M₁ M₂) := by
    rw [Submodule.map_span, hTspan]
  -- Approximate the kernel slice `N ∩ (M₁ × 0)` at threshold `δ`.
  obtain ⟨N₁', hN₁'fg, hN₁'le, hN₁'smul⟩ :=
    hM₁ (N.comap (LinearMap.inl R M₁ M₂)) hδ0 hδ1
  refine ⟨N₁'.map (LinearMap.inl R M₁ M₂) ⊔ Nlift,
    (hN₁'fg.map _).sup (Submodule.fg_span hTfin),
    sup_le (Submodule.map_le_iff_le_comap.mpr hN₁'le) hNlift_le, fun c hc x hx ↦ ?_⟩
  obtain ⟨c', rfl, hc'δ⟩ := hfac c hc
  have hdx2 : φ d • x.2 ∈ N₂' := hN₂'smul d le_rfl x.2 ⟨x, hx, rfl⟩
  obtain ⟨w, hw_lift, hw_snd⟩ := hN₂'_le_map hdx2
  rw [LinearMap.snd_apply] at hw_snd
  have huN : φ d • x - w ∈ N := N.sub_mem (N.smul_mem (φ d) hx) (hNlift_le hw_lift)
  have hu2 : (φ d • x - w).2 = 0 := sub_eq_zero.mpr hw_snd.symm
  have hu1_mem : (φ d • x - w).1 ∈ N.comap (LinearMap.inl R M₁ M₂) := by
    rw [Submodule.mem_comap, LinearMap.inl_apply, ← hu2, Prod.mk.eta]
    exact huN
  have hdecomp : φ (c' * d) • x =
      LinearMap.inl R M₁ M₂ (φ c' • (φ d • x - w).1) + φ c' • w := by
    ext
    · simp [map_mul, mul_smul, smul_sub]
    · simp [map_mul, mul_smul, hw_snd]
  rw [hdecomp]
  exact Submodule.add_mem_sup ⟨_, hN₁'smul c' hc'δ _ hu1_mem, rfl⟩ (Nlift.smul_mem _ hw_lift)

/-- Finite powers `Fin n → M` preserve `IsAlmostNoetherianModule` when `K` has no strict norm gap
below `1`. -/
theorem fin_pi {φ : Subring.unitClosedBall K →+* R} {M : Type*} [AddCommGroup M] [Module R M]
    (hM : IsAlmostNoetherianModule φ M)
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    ∀ n : ℕ, IsAlmostNoetherianModule φ (Fin n → M)
  | 0 => .of_subsingleton
  | n + 1 =>
    (hM.prod hdense (hM.fin_pi hdense n)).of_surjective_linearMap
      (Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ M)).toLinearMap
      (Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ M)).surjective

/-- Finitely generated `R`-modules inherit `IsAlmostNoetherianModule` from `R` when `K` has no
strict norm gap below `1`. -/
theorem of_finite {φ : Subring.unitClosedBall K →+* R} (hR : IsAlmostNoetherianModule φ R)
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : IsAlmostNoetherianModule φ M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact (hR.fin_pi hdense n).of_surjective_linearMap f hf

end IsAlmostNoetherianModule

end DenseNormField

end TauCeti
