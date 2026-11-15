/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AlmostNoetherian

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Huber.Normed
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Integral presentation rings of affinoid algebras and Kiehl's almost noetherianity theorem

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
(equal as a set to `𝒪[K]` when `K` is nontrivially normed). Given a `K`-algebra homomorphism
`π : K⟨X⟩ →ₐ[K] A` from a finite-variable Tate algebra, its *integral presentation subring* is the
image `A₀ = (Subring.unitClosedBall K⟨X⟩).map π.toRingHom` of the Gauss unit ball.

When `π` is a surjective presentation of an affinoid algebra `A`, `A₀` is an open bounded subring
of `A` (a ring of definition for every complete ultrametric algebra norm on `A`) over which `A°` is
integral (`AlgHom.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one`). In zero variables `A₀`
recovers the image of `K°`, and in particular equals `K°` for `A = K` — whereas `(⊤ : Subring K)` is
unbounded when `K` is nontrivially normed. Conversely, any commutative `K`-algebra `A` equipped
with a subring `A₀` receiving a `K`-compatible surjection from `𝒪[K]⟨X₁, …, Xₙ⟩`
(`TauCeti.Huber.restrictedMvPowerSeriesCompletion n 𝒪[K]`) inherits a unique `K`-algebra
homomorphism `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` with `π(K⟨X₁, …, Xₙ⟩°) = A₀`; when `A₀` is open for a
topology on `A` with separately continuous multiplication making `algebraMap K A` continuous, `π` is
surjective onto `A`, so `A` is an affinoid `K`-algebra.

Over a discretely valued field (`IsDiscreteValuationRing 𝒪[K]`), every integral presentation ring
`A₀` and every ring quotient of `𝒪[K]⟨X₁, …, Xₙ⟩` is noetherian. Over an arbitrary complete
ultrametric normed field `K`, `A₀` need not be noetherian, but Kiehl's Satz 5.1 holds for every
finitely generated `A₀`-module `M` (without requiring `M` to embed in a `K`-module): for every
submodule `N ≤ M` and every `0 < ε < 1`, there is a single finitely generated `A₀`-submodule
`N' ≤ N` containing `c • N` for **all** scalars `c ∈ K°` with `‖c‖ ≤ ε`.

## Main definitions

* `AlgHom.unitClosedBallMapHom`: for `π : K⟨X⟩ →ₐ[K] A`, the canonical surjection from the Gauss
  unit ball `K⟨X⟩°` onto `π(K⟨X⟩°)`.

## Main results

* `AlgHom.map_unitClosedBall_of_isEmpty`, `AlgHom.map_unitClosedBall_self_of_isEmpty`: in zero
  variables, `π(K⟨X⟩°)` is the image of `K°` in `A`, and equals `K°` on `A = K`.
* `AlgHom.isNoetherianRing_map_unitClosedBall`: when `K°` is noetherian, `π(K⟨X⟩°)` is noetherian.
* `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall`: Kiehl's Satz 5.1 for finitely generated
  modules over `π(K⟨X⟩°)`.
* `TauCeti.Huber.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion`,
  `TauCeti.Huber.exists_fg_le_forall_smul_mem_of_restrictedMvPowerSeriesCompletion_algHom`: Kiehl's
  almost noetherianity theorem directly for quotients of `𝒪[K]⟨X₁, …, Xₙ⟩`, together with honest
  noetherianity
  (`TauCeti.Huber.isNoetherianRing_of_surjective_restrictedMvPowerSeriesCompletion_integer`) when
  `𝒪[K]` is a discrete valuation ring.
* `TauCeti.Huber.existsUnique_algHom_of_restrictedMvPowerSeriesCompletion`,
  `TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`: inverting a pseudouniformiser
  uniquely extends any `K`-compatible integral presentation `𝒪[K]⟨X₁, …, Xₙ⟩ ↠ A₀ ⊆ A` to
  `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` with `π(K⟨X₁, …, Xₙ⟩°) = A₀`, and `π` is surjective onto `A` (making
  `A` affinoid) whenever `A₀` is open.
* `TauCeti.IsAffinoidAlgebra.isOpen_map_unitClosedBall`,
  `TauCeti.IsAffinoidAlgebra.isBounded_map_unitClosedBall`,
  `TauCeti.IsAffinoidAlgebra.map_unitClosedBall_le_powerBoundedSubring`: for a completely normed
  affinoid algebra, `π(K⟨X⟩°)` is bounded and power-bounded, and open when `π` is surjective.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.3, Proposition 7, and §6.4.
-/

public section

namespace AlgHom

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
  {A : Type*} [CommRing A] [Algebra K A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Canonical surjection onto an integral presentation subring.** A `K`-algebra homomorphism
`π : K⟨X⟩ →ₐ[K] A` restricts to a surjective ring homomorphism from the Gauss unit ball `K⟨X⟩°`
onto its image `(Subring.unitClosedBall (K⟨X⟩)).map π.toRingHom`. -/
noncomputable def unitClosedBallMapHom (π : Tate σ →ₐ[K] A) :
    Subring.unitClosedBall (Tate σ) →+* (Subring.unitClosedBall (Tate σ)).map π.toRingHom :=
  (π.toRingHom.comp (Subring.unitClosedBall (Tate σ)).subtype).codRestrict _ fun f ↦
    ⟨f, f.2, rfl⟩

theorem coe_unitClosedBallMapHom (π : Tate σ →ₐ[K] A) (f : Subring.unitClosedBall (Tate σ)) :
    (π.unitClosedBallMapHom f : A) = π f := (rfl)

theorem unitClosedBallMapHom_surjective (π : Tate σ →ₐ[K] A) :
    Function.Surjective π.unitClosedBallMapHom :=
  fun ⟨_, f, hf, hfa⟩ ↦ ⟨⟨f, hf⟩, Subtype.ext hfa⟩

/-- Constants of norm at most one in `K` map into the integral presentation subring `π(K⟨X⟩°)`. -/
theorem algebraMap_mem_map_unitClosedBall (π : Tate σ →ₐ[K] A) {c : K} (hc : ‖c‖ ≤ 1) :
    algebraMap K A c ∈ (Subring.unitClosedBall (Tate σ)).map π.toRingHom :=
  ⟨algebraMap K (Tate σ) c, Subring.mem_unitClosedBall.mpr
    ((norm_algebraMap_isRestrictedSubring c).trans_le hc), π.commutes c⟩

theorem coe_unitClosedBallMapHom_coeffHom (π : Tate σ →ₐ[K] A) (c : Subring.unitClosedBall K) :
    (π.unitClosedBallMapHom (TauCeti.MvPowerSeries.unitClosedBallCoeffHom (σ := σ) c) : A) =
      algebraMap K A c := by
  rw [coe_unitClosedBallMapHom, TauCeti.MvPowerSeries.coe_unitClosedBallCoeffHom]
  exact π.commutes (c : K)

/-- **Zero-variable check.** When the variable index type `σ` is empty, the integral presentation
subring `π(K⟨X⟩°)` is the image of `K°` under `algebraMap K A`. -/
theorem map_unitClosedBall_of_isEmpty [_root_.IsEmpty σ] (π : Tate σ →ₐ[K] A) :
    (Subring.unitClosedBall (Tate σ)).map π.toRingHom =
      (Subring.unitClosedBall K).map (algebraMap K A) := by
  ext a
  simp only [Subring.mem_map]
  refine ⟨fun ⟨f, hf, hfa⟩ ↦ ?_, fun ⟨c, hc, hca⟩ ↦
    ⟨algebraMap K (Tate σ) c, Subring.mem_unitClosedBall.mpr
      ((norm_algebraMap_isRestrictedSubring c).trans_le (Subring.mem_unitClosedBall.mp hc)),
      (π.commutes c).trans hca⟩⟩
  set c : K := constantCoeff (f : MvPowerSeries σ K)
  have hfeq : f = algebraMap K (Tate σ) c := Subtype.ext <| MvPowerSeries.ext fun t ↦ by
    rw [Subsingleton.elim t 0]
    simp [c, coe_algebraMap_isRestrictedSubring, coeff_zero_eq_constantCoeff_apply]
  exact ⟨c, Subring.mem_unitClosedBall.mpr
    ((norm_constantCoeff_le f).trans (Subring.mem_unitClosedBall.mp hf)),
    by rw [← π.commutes c, ← hfeq]; exact hfa⟩

/-- **Zero-variable check on `K` itself.** Any `K`-algebra map `K⟨∅⟩ →ₐ[K] K` has integral
presentation subring equal to `Subring.unitClosedBall K` (`K°`). -/
@[simp]
theorem map_unitClosedBall_self_of_isEmpty [_root_.IsEmpty σ] (π : Tate σ →ₐ[K] K) :
    (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* K) = Subring.unitClosedBall K := by
  rw [← AlgHom.toRingHom_eq_coe, π.map_unitClosedBall_of_isEmpty]
  ext c
  simp

/-- **Noetherianity of integral presentation rings.** Over a complete ultrametric normed field `K`
whose closed unit ball `K°` is noetherian (for instance a complete discretely valued field), every
integral presentation subring `π(K⟨X⟩°)` in finitely many variables is noetherian. -/
theorem isNoetherianRing_map_unitClosedBall [CompleteSpace K] [_root_.Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] (π : Tate σ →ₐ[K] A) :
    IsNoetherianRing ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) :=
  isNoetherianRing_of_surjective _ _ π.unitClosedBallMapHom π.unitClosedBallMapHom_surjective

/-- When `K` has a strict norm gap `ρ < 1` above `{‖a‖ < 1}`, every integral presentation subring
`π(K⟨X⟩°)` in finitely many variables is noetherian. -/
theorem isNoetherianRing_map_unitClosedBall_of_forall_norm_le [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {ρ : ℝ} (hρ1 : ρ < 1) (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsNoetherianRing ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    TauCeti.isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr ⟨ρ, hρ1, hρ⟩
  exact π.isNoetherianRing_map_unitClosedBall

/-- **Kiehl's almost noetherianity theorem for integral presentation rings (Satz 5.1).** Let `K` be
a complete ultrametric normed field, `σ` a finite variable set, and `π : K⟨X⟩ →ₐ[K] A` a `K`-algebra
homomorphism with integral presentation subring
`A₀ = (Subring.unitClosedBall (K⟨X⟩)).map π.toRingHom`. For every finitely generated `A₀`-module
`M`, every submodule `N ≤ M`, and every `0 < ε < 1`, there exists a single finitely generated
`A₀`-submodule `N' ≤ N` containing `c • x` for all `c ∈ K` with `‖c‖ ≤ ε` and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_map_unitClosedBall [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {M : Type*} [AddCommGroup M]
    [Module ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M]
    [Module.Finite ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M]
    (N : Submodule ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M,
      N'.FG ∧ N' ≤ N ∧ ∀ (c : K) (hc : ‖c‖ ≤ ε), ∀ x ∈ N,
        (⟨algebraMap K A c, π.algebraMap_mem_map_unitClosedBall (hc.trans hε1.le)⟩ :
          (Subring.unitClosedBall (Tate σ)).map π.toRingHom) • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    TauCeti.MvPowerSeries.exists_fg_le_forall_smul_mem_of_surjective
      π.unitClosedBallMapHom π.unitClosedBallMapHom_surjective N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  let c₀ : Subring.unitClosedBall K := ⟨c, Subring.mem_unitClosedBall.mpr (hc.trans hε1.le)⟩
  have heq : π.unitClosedBallMapHom (TauCeti.MvPowerSeries.unitClosedBallCoeffHom c₀) =
      ⟨algebraMap K A c, π.algebraMap_mem_map_unitClosedBall (hc.trans hε1.le)⟩ :=
    Subtype.ext (π.coe_unitClosedBallMapHom_coeffHom c₀)
  exact heq ▸ hsmul c₀ hc x hx

/-- Scalar-tower form of `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall`: when `M` is an
`A`-module (with compatible `K`-action) that is finitely generated over `A₀ = π(K⟨X⟩°)`, the uniform
approximation is expressed directly using the `K`-action `c • x ∈ N'`. -/
theorem exists_fg_le_forall_smul_mem_of_isScalarTower [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {M : Type*} [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [Module.Finite ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M]
    (N : Submodule ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule ((Subring.unitClosedBall (Tate σ)).map π.toRingHom) M,
      N'.FG ∧ N' ≤ N ∧ ∀ c : K, ‖c‖ ≤ ε → ∀ x ∈ N, c • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ := π.exists_fg_le_forall_smul_mem_map_unitClosedBall N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  have hact : (⟨algebraMap K A c, π.algebraMap_mem_map_unitClosedBall (hc.trans hε1.le)⟩ :
      (Subring.unitClosedBall (Tate σ)).map π.toRingHom) • x = c • x :=
    algebraMap_smul A c x
  exact hact ▸ hsmul c hc x hx

end AlgHom

namespace TauCeti.Huber

open _root_.MvPowerSeries Filter Topology TauCeti.MvPowerSeries
open scoped NormedField Valued

/-- Over a nontrivially normed field `K`, the whole field `Set.univ` is not bounded in the sense of
`TauCeti.Huber.IsBounded`; in particular `(⊤ : Subring K)` is not a ring of definition of `K`. -/
theorem not_isBounded_univ_of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K] :
    ¬ IsBounded (Set.univ : Set K) := by
  obtain ⟨ϖ, h0, h1⟩ := NormedField.exists_norm_lt_one K
  have hϖ : IsPseudoUniformizer ϖ :=
    isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp h0, h1⟩
  intro h
  obtain ⟨C, hC⟩ := hϖ.isBounded_iff_forall_norm_le.mp h
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K C
  exact hx.not_ge (hC x trivial)

section IntegralPresentation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Noetherianity of quotients of `𝒪[K]⟨X₁, …, Xₙ⟩` in the discretely valued case.** When `𝒪[K]`
is a discrete valuation ring, every commutative ring `A₀` receiving a surjective homomorphism from
`restrictedMvPowerSeriesCompletion n 𝒪[K]` is noetherian. -/
theorem isNoetherianRing_of_surjective_restrictedMvPowerSeriesCompletion_integer {n : ℕ}
    [IsDiscreteValuationRing 𝒪[K]] {A₀ : Type*} [CommRing A₀]
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ : Function.Surjective φ) :
    IsNoetherianRing A₀ := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_integer (K := K) n
  exact isNoetherianRing_of_surjective _ _ φ hφ

/-- Over a complete discretely valued field, every submodule of a finitely generated module over a
quotient of `restrictedMvPowerSeriesCompletion n 𝒪[K]` is finitely generated. -/
theorem fg_of_surjective_restrictedMvPowerSeriesCompletion_integer {n : ℕ}
    [IsDiscreteValuationRing 𝒪[K]] {A₀ : Type*} [CommRing A₀]
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ : Function.Surjective φ)
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M] (N : Submodule A₀ M) :
    N.FG := by
  have := isNoetherianRing_of_surjective_restrictedMvPowerSeriesCompletion_integer φ hφ
  exact IsNoetherian.noetherian N

/-- **Kiehl's almost noetherianity theorem for quotients of `𝒪[K]⟨X₁, …, Xₙ⟩` (ring-homomorphism
form).** For any surjective ring homomorphism `φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀`,
any finitely generated `A₀`-module `M`, any submodule `N ≤ M`, and any `0 < ε < 1`, there exists a
finitely generated submodule `N' ≤ N` containing `φ (algebraMap 𝒪[K] _ c) • x` for all `c ∈ 𝒪[K]`
with `‖(c : K)‖ ≤ ε` and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion {n : ℕ}
    {A₀ : Type*} [CommRing A₀] (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀)
    (hφ : Function.Surjective φ) {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : 𝒪[K], ‖(c : K)‖ ≤ ε → ∀ x ∈ N, φ (algebraMap 𝒪[K] _ c) • x ∈ N' := by
  let e := restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n
  have hsurj : Function.Surjective (φ.comp e.symm.toRingHom) := hφ.comp e.symm.surjective
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    exists_fg_le_forall_smul_mem_of_surjective (φ.comp e.symm.toRingHom) hsurj N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  have heq : (φ.comp e.symm.toRingHom) (unitClosedBallCoeffHom (integerUnitClosedBallEquiv c)) =
      φ (algebraMap 𝒪[K] _ c) := by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact congrArg φ (e.symm_apply_eq.mpr
      (restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap n c).symm)
  have hc' : ‖(integerUnitClosedBallEquiv c : K)‖ ≤ ε := by
    rwa [coe_integerUnitClosedBallEquiv]
  exact heq ▸ hsmul (integerUnitClosedBallEquiv c) hc' x hx

/-- **Kiehl's almost noetherianity theorem for `𝒪[K]`-algebra quotients of `𝒪[K]⟨X₁, …, Xₙ⟩`.** Let
`A₀` be a commutative `𝒪[K]`-algebra admitting a surjective `𝒪[K]`-algebra homomorphism from
`restrictedMvPowerSeriesCompletion n 𝒪[K]`, and let `M` be a finitely generated `A₀`-module with the
induced `𝒪[K]`-module structure. For every `N : Submodule A₀ M` and every `0 < ε < 1`, there exists
a finitely generated `A₀`-submodule `N' ≤ N` such that `c • x ∈ N'` for all `c : 𝒪[K]` with
`‖(c : K)‖ ≤ ε` and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_of_restrictedMvPowerSeriesCompletion_algHom {n : ℕ}
    {A₀ : Type*} [CommRing A₀] [Algebra 𝒪[K] A₀]
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →ₐ[𝒪[K]] A₀) (hφ : Function.Surjective φ)
    {M : Type*} [AddCommGroup M] [Module 𝒪[K] M] [Module A₀ M] [IsScalarTower 𝒪[K] A₀ M]
    [Module.Finite A₀ M] (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : 𝒪[K], ‖(c : K)‖ ≤ ε → ∀ x ∈ N, c • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion
      φ.toRingHom hφ N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    algebraMap_smul] using hsmul c hc x hx

/-- **Unique extension of an integral presentation to a `K`-algebra Tate homomorphism.** Let `A` be
a commutative `K`-algebra and `A₀ : Subring A` a subring receiving a surjective ring homomorphism
`φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀` compatible with `algebraMap K A` on `𝒪[K]`.
Then there is a unique `K`-algebra homomorphism `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` extending
`φ ∘ (restrictedMvPowerSeriesCompletionIntegerEquiv n).symm` on `K⟨X₁, …, Xₙ⟩°`, and its Gauss
unit-ball image `(Subring.unitClosedBall _).map π.toRingHom` equals `A₀`. -/
theorem existsUnique_algHom_of_restrictedMvPowerSeriesCompletion {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] {A₀ : Subring A}
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    ∃! π : Tate (Fin n) →ₐ[K] A,
      (∀ f : Subring.unitClosedBall (Tate (Fin n)),
        π f = φ ((restrictedMvPowerSeriesCompletionIntegerEquiv n).symm f)) ∧
      (Subring.unitClosedBall (Tate (Fin n))).map π.toRingHom = A₀ := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  let p : Subring.unitClosedBall K := ⟨ϖ, Subring.mem_unitClosedBall.mpr hϖ1.le⟩
  have hp0 : (p : K) ≠ 0 := norm_pos_iff.mp hϖ0
  have : IsLocalization.Away p K :=
    (Subring.unitClosedBall K).isLocalizationAway_of_isOpen
      (Subring.isOpen_unitClosedBall K) p
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1)
      (isUnit_iff_ne_zero.mpr hp0)
  let x := unitClosedBallCoeffHom (σ := Fin n) p
  have : IsLocalization.Away x (Tate (Fin n)) :=
    isLocalizationAway_unitClosedBallCoeffHom p hp0 hϖ1
  let e := restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n
  let ψ : Subring.unitClosedBall (Tate (Fin n)) →+* A :=
    A₀.subtype.comp (φ.comp e.symm.toRingHom)
  have hψ_coeff (c : Subring.unitClosedBall K) :
      ψ (unitClosedBallCoeffHom c) = algebraMap K A (c : K) := by
    let c₀ : 𝒪[K] := integerUnitClosedBallEquiv.symm c
    have hc_eq : c = integerUnitClosedBallEquiv c₀ :=
      (integerUnitClosedBallEquiv.apply_symm_apply c).symm
    rw [hc_eq, ← restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap n c₀,
      coe_integerUnitClosedBallEquiv]
    simpa [ψ, e] using hφ_alg c₀
  have hx : IsUnit (ψ x) := by
    rw [hψ_coeff p]
    exact (isUnit_iff_ne_zero.mpr hp0).map (algebraMap K A)
  let π₀ : Tate (Fin n) →+* A := IsLocalization.Away.lift x hx
  have hπ₀_ball (f : Subring.unitClosedBall (Tate (Fin n))) : π₀ f = ψ f := by
    have h := IsLocalization.Away.lift_eq (S := Tate (Fin n)) x hx f
    rwa [Algebra.algebraMap_ofSubring, Subring.coe_subtype] at h
  have hcomm : π₀.comp (algebraMap K (Tate (Fin n))) = algebraMap K A :=
    IsLocalization.ringHom_ext (Submonoid.powers p) <| RingHom.ext fun c ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        Algebra.algebraMap_ofSubring, Subring.coe_subtype,
        ← coe_unitClosedBallCoeffHom (σ := Fin n), hπ₀_ball, hψ_coeff]
  let π : Tate (Fin n) →ₐ[K] A := { π₀ with commutes' := RingHom.congr_fun hcomm }
  have hπ_ball (f : Subring.unitClosedBall (Tate (Fin n))) : π f = ψ f := hπ₀_ball f
  have hmap : (Subring.unitClosedBall (Tate (Fin n))).map π.toRingHom = A₀ := by
    ext a
    simp only [Subring.mem_map]
    refine ⟨fun ⟨f, hf, hfa⟩ ↦ ?_, fun ha ↦ ?_⟩
    · have : π f = (φ (e.symm ⟨f, hf⟩) : A) := hπ_ball ⟨f, hf⟩
      rw [← hfa, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this]
      exact (φ (e.symm ⟨f, hf⟩)).2
    · obtain ⟨w, hw⟩ := hφ_surj ⟨a, ha⟩
      exact ⟨e w, (e w).2, by
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hπ_ball (e w)]
        simpa [ψ] using congrArg Subtype.val hw⟩
  refine ⟨π, ⟨hπ_ball, hmap⟩, fun π' ⟨hπ', _⟩ ↦ AlgHom.toRingHom_injective ?_⟩
  refine IsLocalization.ringHom_ext (Submonoid.powers x) (RingHom.ext fun f ↦ ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.algebraMap_ofSubring, Subring.coe_subtype]
  exact (hπ' f).trans (hπ_ball f).symm

/-- **Topological integral presentations make `A` an affinoid algebra.** Let `A` be a topological
`K`-algebra with separately continuous multiplication and continuous `algebraMap K A`, and let
`A₀ : Subring A` be an open subring receiving a `K`-compatible surjective ring homomorphism from
`restrictedMvPowerSeriesCompletion n 𝒪[K]`. Then the canonical extension `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`
is **surjective onto `A`** and satisfies `(Subring.unitClosedBall _).map π.toRingHom = A₀`; in
particular `IsAffinoidAlgebra K A` holds. -/
theorem exists_surjective_algHom_map_unitClosedBall_eq {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : Continuous (algebraMap K A)) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    ∃ π : Tate (Fin n) →ₐ[K] A, Function.Surjective π ∧
      (∀ f : Subring.unitClosedBall (Tate (Fin n)),
        π f = φ ((restrictedMvPowerSeriesCompletionIntegerEquiv n).symm f)) ∧
      (Subring.unitClosedBall (Tate (Fin n))).map π.toRingHom = A₀ := by
  obtain ⟨π, ⟨hπ_ball, hπ_map⟩, -⟩ :=
    existsUnique_algHom_of_restrictedMvPowerSeriesCompletion φ hφ_surj hφ_alg
  refine ⟨π, fun a ↦ ?_, hπ_ball, hπ_map⟩
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ_ne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  have hs : IsTopologicallyNilpotent (algebraMap K A ϖ) := by
    simpa only [IsTopologicallyNilpotent, Function.comp_def, ← map_pow,
      ← map_zero (algebraMap K A)] using
      (hcont.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1)
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hs hA₀ a
  rw [← map_pow, mul_comm, ← hπ_map] at hk
  obtain ⟨g, -, hg⟩ := hk
  refine ⟨(ϖ ^ k)⁻¹ • g, ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hg
  rw [map_smul, hg, ← Algebra.smul_def, inv_smul_smul₀ (pow_ne_zero k hϖ_ne)]

/-- Corollary of `exists_surjective_algHom_map_unitClosedBall_eq`: any topological `K`-algebra with
separately continuous multiplication containing an open subring presented as a `K`-compatible
quotient of `𝒪[K]⟨X₁, …, Xₙ⟩` is an affinoid `K`-algebra. -/
theorem isAffinoidAlgebra_of_restrictedMvPowerSeriesCompletion {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : Continuous (algebraMap K A)) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    IsAffinoidAlgebra K A := by
  obtain ⟨π, hπ, -⟩ :=
    exists_surjective_algHom_map_unitClosedBall_eq hcont hA₀ φ hφ_surj hφ_alg
  exact (isAffinoidAlgebra_iff K A).mpr ⟨n, π, hπ⟩

end IntegralPresentation

end TauCeti.Huber

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Integral presentation subrings are bounded.** For any completely normed affinoid algebra `A`
and any `K`-algebra homomorphism `π : K⟨X⟩ →ₐ[K] A`, the image `π(K⟨X⟩°)` is bounded in `A`. -/
theorem isBounded_map_unitClosedBall (hA : IsAffinoidAlgebra K A) (π : Tate σ →ₐ[K] A) :
    Huber.IsBounded (((Subring.unitClosedBall (Tate σ)).map π.toRingHom : Subring A) : Set A) := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  let g : Tate σ →L[K] A := ⟨π.toLinearMap, hA.continuous_algHom π⟩
  refine (Huber.isBounded_closedBall_zero ‖g‖).subset ?_
  rintro _ ⟨f, hf, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (g.le_opNorm f).trans
    (mul_le_of_le_one_right (norm_nonneg g) (Subring.mem_unitClosedBall.mp hf))

/-- **Integral presentation subrings consist of power-bounded elements.** For any completely normed
affinoid algebra `A` and any `π : K⟨X⟩ →ₐ[K] A`, `π(K⟨X⟩°) ≤ Huber.powerBoundedSubring A`. -/
theorem map_unitClosedBall_le_powerBoundedSubring (hA : IsAffinoidAlgebra K A)
    (π : Tate σ →ₐ[K] A) :
    (Subring.unitClosedBall (Tate σ)).map π.toRingHom ≤ Huber.powerBoundedSubring A := by
  intro a ha
  refine Huber.mem_powerBoundedSubring.mpr (Huber.isPowerBounded_iff.mpr ?_)
  refine (hA.isBounded_map_unitClosedBall π).subset ?_
  rintro _ ⟨k, rfl⟩
  exact ((Subring.unitClosedBall (Tate σ)).map π.toRingHom).pow_mem ha k

/-- **Surjective presentations map the Gauss unit ball to an open subring.** For a completely
normed affinoid algebra `A` and a surjective presentation `π : K⟨X⟩ →ₐ[K] A`, the integral
presentation subring `π(K⟨X⟩°)` is open in `A` (hence a ring of definition of `A`). -/
theorem isOpen_map_unitClosedBall (hA : IsAffinoidAlgebra K A) (π : Tate σ →ₐ[K] A)
    (hπ : Function.Surjective π) :
    IsOpen (((Subring.unitClosedBall (Tate σ)).map π.toRingHom : Subring A) : Set A) := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  rw [Subring.coe_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact (hA.isOpenQuotientMap π hπ).isOpenMap _ (Subring.isOpen_unitClosedBall (Tate σ))

/-- Composing `π.unitClosedBallMapHom` with `restrictedMvPowerSeriesCompletionIntegerEquiv` gives a
continuous surjective ring homomorphism `𝒪[K]⟨X₁, …, Xₙ⟩ →+* π(K⟨X₁, …, Xₙ⟩°)` into the subspace
topology of `A`. -/
theorem continuous_unitClosedBallMapHom_comp_restrictedMvPowerSeriesCompletionIntegerEquiv
    (hA : IsAffinoidAlgebra K A) {n : ℕ} (π : Tate (Fin n) →ₐ[K] A) :
    Continuous (π.unitClosedBallMapHom.comp
      (Huber.restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n).toRingHom) := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
  have hcont_map : Continuous π.unitClosedBallMapHom :=
    continuous_induced_rng.mpr <| by
      simpa only [Function.comp_def, AlgHom.coe_unitClosedBallMapHom] using
        (hA.continuous_algHom π).comp continuous_subtype_val
  exact hcont_map.comp (Huber.continuous_restrictedMvPowerSeriesCompletionIntegerEquiv n)

end TauCeti.IsAffinoidAlgebra
