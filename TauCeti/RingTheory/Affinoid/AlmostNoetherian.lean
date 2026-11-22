/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AlmostNoetherian

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.Affinoid.Continuity

/-!
# Integral presentation rings of affinoid algebras and Kiehl's almost noetherianity theorem

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
(equal as a subring to `𝒪[K]` when `K` is nontrivially normed). Given a `K`-algebra homomorphism
`π : K⟨X⟩ →ₐ[K] A` from a finite-variable Tate algebra, its *integral presentation subring* is the
image `A₀ = (Subring.unitClosedBall K⟨X⟩).map (π : K⟨X⟩ →+* A)` of the Gauss unit ball.

When `K` is nontrivially normed and `π` is a surjective presentation of an affinoid algebra `A`,
`A₀` is an open bounded subring of `A` (a ring of definition for every complete ultrametric
algebra norm on `A`, see `TauCeti.IsAffinoidAlgebra.isOpen_map_unitClosedBall` and
`TauCeti.IsAffinoidAlgebra.isBounded_map_unitClosedBall`) over which `A°` is integral
(`AlgHom.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one`). In zero variables `A₀` recovers
the image of `K°`, and in particular equals `K°` for `A = K` — whereas `(⊤ : Subring K)` is
unbounded when `K` is nontrivially normed
(`TauCeti.Huber.not_isBounded_univ_of_nontriviallyNormedField`). Conversely, when `K` is
nontrivially normed, any `K`-compatible ring homomorphism `φ : 𝒪[K]⟨X₁, …, Xₙ⟩ →+* A` extends
uniquely to `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` with `π(K⟨X₁, …, Xₙ⟩°) = φ.range`
(`RingHom.existsUnique_algHom_of_restrictedMvPowerSeriesCompletion`), and `π` is surjective onto
`A` when `φ` surjects onto an open subring
(`TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`).

When `K°` is noetherian (for instance when `K` is a complete discretely valued field, so `𝒪[K]` is
a discrete valuation ring), every integral presentation ring `A₀` is noetherian. Over an arbitrary
complete ultrametric normed field `K`, `A₀` need not be noetherian, but Kiehl's Satz 5.1 holds for
every finitely generated `A₀`-module `M` (without requiring `M` to embed in a `K`-module): for
every submodule `N ≤ M` and every `0 < ε < 1`, there is a single finitely generated `A₀`-submodule
`N' ≤ N` containing `c • N` for **all** scalars `c ∈ K°` with `‖c‖ ≤ ε`. (For the corresponding
statements directly for quotients of `𝒪[K]⟨X₁, …, Xₙ⟩`, see
`TauCeti.RingTheory.Huber.Restricted.AlmostNoetherian`.)

## Main definitions

* `AlgHom.unitClosedBallMapHom`: for `π : K⟨X⟩ →ₐ[K] A`, the canonical surjection from the Gauss
  unit ball `K⟨X⟩°` onto `π(K⟨X⟩°)`.

## Main results

* `AlgHom.map_unitClosedBall_of_isEmpty`, `AlgHom.map_unitClosedBall_self_of_isEmpty`: in zero
  variables, `π(K⟨X⟩°)` is the image of `K°` in `A`, and equals `K°` on `A = K`.
* `AlgHom.isNoetherianRing_map_unitClosedBall` (registered as an instance),
  `AlgHom.isNoetherianRing_map_unitClosedBall_of_isNoetherianRing_integer`: when `K°` (or `𝒪[K]`) is
  noetherian, `π(K⟨X⟩°)` is noetherian.
* `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall`,
  `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall_of_isScalarTower`: Kiehl's Satz 5.1 for
  finitely generated modules over `π(K⟨X⟩°)`.
* `TauCeti.IsAffinoidAlgebra.continuous_unitClosedBallMapHom` and its composition with
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionIntegerEquiv`: over a complete nontrivially
  normed ultrametric field `K`, continuity of `π.unitClosedBallMapHom` and its precomposition with
  `𝒪[K]⟨X₁, …, Xₙ⟩ ≃+* K⟨X₁, …, Xₙ⟩°` for any complete ultrametric `K`-algebra norm on an affinoid
  algebra `A`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
-/

public section

namespace AlgHom

open _root_.MvPowerSeries
open scoped NormedField Valued

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
  {A : Type*} [CommRing A] [Algebra K A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Canonical surjection onto an integral presentation subring.** A `K`-algebra homomorphism
`π : K⟨X⟩ →ₐ[K] A` restricts to a surjective ring homomorphism from the Gauss unit ball `K⟨X⟩°`
onto its image `(Subring.unitClosedBall (K⟨X⟩)).map (π : K⟨X⟩ →+* A)`. -/
noncomputable def unitClosedBallMapHom (π : Tate σ →ₐ[K] A) :
    Subring.unitClosedBall (Tate σ) →+* (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A) :=
  (π : Tate σ →+* A).restrict (Subring.unitClosedBall (Tate σ))
    ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) fun f hf ↦ ⟨f, hf, rfl⟩

@[simp]
theorem coe_unitClosedBallMapHom (π : Tate σ →ₐ[K] A) (f : Subring.unitClosedBall (Tate σ)) :
    (π.unitClosedBallMapHom f : A) = π f := (rfl)

@[simp]
theorem subtype_comp_unitClosedBallMapHom (π : Tate σ →ₐ[K] A) :
    ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)).subtype.comp
        π.unitClosedBallMapHom =
      (π : Tate σ →+* A).comp (Subring.unitClosedBall (Tate σ)).subtype :=
  RingHom.ext fun _ ↦ rfl

theorem unitClosedBallMapHom_surjective (π : Tate σ →ₐ[K] A) :
    Function.Surjective π.unitClosedBallMapHom :=
  fun ⟨_, f, hf, hfa⟩ ↦ ⟨⟨f, hf⟩, Subtype.ext hfa⟩

/-- Constants of norm at most one in `K` map into the integral presentation subring `π(K⟨X⟩°)`. -/
theorem algebraMap_mem_map_unitClosedBall (π : Tate σ →ₐ[K] A) {c : K} (hc : ‖c‖ ≤ 1) :
    algebraMap K A c ∈ (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A) :=
  ⟨algebraMap K (Tate σ) c, Subring.mem_unitClosedBall.mpr
    ((norm_algebraMap_isRestrictedSubring c).trans_le hc), π.commutes c⟩

@[simp]
theorem unitClosedBallMapHom_unitClosedBallCoeffHom (π : Tate σ →ₐ[K] A)
    (c : Subring.unitClosedBall K) :
    π.unitClosedBallMapHom
        (TauCeti.MvPowerSeries.unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c) =
      ⟨algebraMap K A c,
        π.algebraMap_mem_map_unitClosedBall (Subring.mem_unitClosedBall.mp c.property)⟩ :=
  Subtype.ext <| by
    rw [coe_unitClosedBallMapHom, TauCeti.MvPowerSeries.coe_unitClosedBallCoeffHom]
    exact π.commutes (c : K)

theorem coe_unitClosedBallMapHom_unitClosedBallCoeffHom (π : Tate σ →ₐ[K] A)
    (c : Subring.unitClosedBall K) :
    (π.unitClosedBallMapHom
        (TauCeti.MvPowerSeries.unitClosedBallCoeffHom (σ := σ) (r := fun _ ↦ 1) c) : A) =
      algebraMap K A c := by
  rw [coe_unitClosedBallMapHom, TauCeti.MvPowerSeries.coe_unitClosedBallCoeffHom]
  exact π.commutes (c : K)

/-- **Zero-variable check.** When the variable index type `σ` is empty, the integral presentation
subring `π(K⟨X⟩°)` is the image of `K°` under `algebraMap K A`. -/
theorem map_unitClosedBall_of_isEmpty [_root_.IsEmpty σ] (π : Tate σ →ₐ[K] A) :
    (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A) =
      (Subring.unitClosedBall K).map (algebraMap K A) := by
  ext a
  simp only [Subring.mem_map]
  refine ⟨fun ⟨f, hf, hfa⟩ ↦ ?_, fun ⟨c, hc, hca⟩ ↦
    ⟨algebraMap K (Tate σ) c, Subring.mem_unitClosedBall.mpr
      ((norm_algebraMap_isRestrictedSubring c).trans_le (Subring.mem_unitClosedBall.mp hc)),
      (π.commutes c).trans hca⟩⟩
  obtain ⟨c, rfl⟩ := algebraMap_isRestrictedSubring_surjective (R := K) (c := fun _ : σ ↦ 1) f
  refine ⟨c, Subring.mem_unitClosedBall.mpr ?_, by rwa [← π.commutes c]⟩
  simpa only [Subring.mem_unitClosedBall, norm_algebraMap_isRestrictedSubring] using hf

/-- **Zero-variable check on `K` itself.** Any `K`-algebra map `K⟨∅⟩ →ₐ[K] K` has integral
presentation subring equal to `Subring.unitClosedBall K` (`K°`). -/
@[simp]
theorem map_unitClosedBall_self_of_isEmpty [_root_.IsEmpty σ] (π : Tate σ →ₐ[K] K) :
    (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* K) = Subring.unitClosedBall K := by
  rw [π.map_unitClosedBall_of_isEmpty]
  ext c
  simp

/-- **Noetherianity of integral presentation rings.** Over a complete ultrametric normed field `K`
whose closed unit ball `K°` is noetherian (for instance a complete discretely valued field), every
integral presentation subring `π(K⟨X⟩°)` in finitely many variables is noetherian. -/
instance isNoetherianRing_map_unitClosedBall [CompleteSpace K] [_root_.Finite σ]
    [IsNoetherianRing (Subring.unitClosedBall K)] (π : Tate σ →ₐ[K] A) :
    IsNoetherianRing ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) :=
  isNoetherianRing_of_surjective _ _ π.unitClosedBallMapHom π.unitClosedBallMapHom_surjective

/-- Over a complete nontrivially normed ultrametric field `K` whose valuation ring `𝒪[K]` is
noetherian (for instance a complete discretely valued field), every integral presentation subring
`π(K⟨X⟩°)` in finitely many variables is noetherian. -/
theorem isNoetherianRing_map_unitClosedBall_of_isNoetherianRing_integer
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsNoetherianRing 𝒪[K]] {σ : Type*} [_root_.Finite σ]
    {A : Type*} [CommRing A] [Algebra K A]
    (π : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →ₐ[K] A) :
    IsNoetherianRing ((Subring.unitClosedBall
      (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))).map
        (π : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →+* A)) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_surjective _ _ TauCeti.integerUnitClosedBallEquiv.toRingHom
      TauCeti.integerUnitClosedBallEquiv.surjective
  infer_instance

/-- Over a complete ultrametric normed field `K` with a strict norm gap `ρ < 1` above
`{‖a‖ < 1}`, every integral presentation subring `π(K⟨X⟩°)` in finitely many variables is
noetherian. -/
theorem isNoetherianRing_map_unitClosedBall_of_forall_norm_le [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {ρ : ℝ} (hρ1 : ρ < 1) (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsNoetherianRing ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) := by
  have : IsNoetherianRing (Subring.unitClosedBall K) :=
    TauCeti.isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mpr ⟨ρ, hρ1, hρ⟩
  infer_instance

/-- **Kiehl's almost noetherianity theorem for integral presentation rings (Satz 5.1).** Let `K` be
a complete ultrametric normed field, `σ` a finite variable set, and `π : K⟨X⟩ →ₐ[K] A` a `K`-algebra
homomorphism with integral presentation subring
`A₀ = (Subring.unitClosedBall (K⟨X⟩)).map (π : K⟨X⟩ →+* A)`. For every finitely generated
`A₀`-module `M`, every submodule `N ≤ M`, and every `0 < ε < 1`, there exists a single finitely
generated `A₀`-submodule `N' ≤ N` containing `c • x` for all `c ∈ K` with `‖c‖ ≤ ε` and all
`x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_map_unitClosedBall [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {M : Type*} [AddCommGroup M]
    [Module ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M]
    [Module.Finite ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M]
    (N : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M,
      N'.FG ∧ N' ≤ N ∧ ∀ (c : K) (hc : ‖c‖ ≤ ε), ∀ x ∈ N,
        (⟨algebraMap K A c, π.algebraMap_mem_map_unitClosedBall (hc.trans hε1.le)⟩ :
          (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    π.unitClosedBallMapHom.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall
      π.unitClosedBallMapHom_surjective N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  let c₀ : Subring.unitClosedBall K := ⟨c, Subring.mem_unitClosedBall.mpr (hc.trans hε1.le)⟩
  simpa only [π.unitClosedBallMapHom_unitClosedBallCoeffHom c₀] using hsmul c₀ hc x hx

/-- Scalar-tower form of `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall`: over a complete
ultrametric normed field `K`, for any finitely generated `A₀`-submodule `M` of an ambient
`A`-module `E` (with compatible `K`-action, where `A₀ = π(K⟨X⟩°)`), every `A₀`-submodule `N ≤ M`
and every `0 < ε < 1` admit a single finitely generated `A₀`-submodule `N' ≤ N` containing `c • x`
for all `c : K` with `‖c‖ ≤ ε` and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_map_unitClosedBall_of_isScalarTower [CompleteSpace K]
    [_root_.Finite σ] (π : Tate σ →ₐ[K] A)
    {E : Type*} [AddCommGroup E] [Module K E] [Module A E] [IsScalarTower K A E]
    {M N : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) E}
    (hM : M.FG) (hNM : N ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) E,
      N'.FG ∧ N' ≤ N ∧ ∀ c : K, ‖c‖ ≤ ε → ∀ x ∈ N, c • x ∈ N' := by
  let A₀ := (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)
  have : Module.Finite A₀ M := Module.Finite.iff_fg.mpr hM
  obtain ⟨N₀', hfg, hle, hsmul⟩ :=
    π.exists_fg_le_forall_smul_mem_map_unitClosedBall (N.comap M.subtype) hε0 hε1
  refine ⟨N₀'.map M.subtype, hfg.map M.subtype, Submodule.map_le_iff_le_comap.mpr hle,
    fun c hc x hx ↦ ?_⟩
  have hxM : x ∈ M := hNM hx
  refine ⟨_, hsmul c hc ⟨x, hxM⟩ hx, ?_⟩
  rw [map_smul, Submodule.subtype_apply, Subring.smul_def, algebraMap_smul]

end AlgHom

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- Over a complete nontrivially normed ultrametric field `K`, for any affinoid algebra `A` carrying
a complete ultrametric `K`-algebra norm, any finite variable set `σ`, and any `K`-algebra
homomorphism `π : K⟨X⟩ →ₐ[K] A`, the restricted homomorphism
`π.unitClosedBallMapHom : K⟨X⟩° →+* π(K⟨X⟩°)` is continuous into the subspace topology of `A`. -/
theorem continuous_unitClosedBallMapHom (hA : IsAffinoidAlgebra K A) (π : Tate σ →ₐ[K] A) :
    Continuous π.unitClosedBallMapHom := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  exact continuous_induced_rng.mpr <| by
    simpa only [Function.comp_def, AlgHom.coe_unitClosedBallMapHom] using
      (hA.continuous_algHom π).comp continuous_subtypeVal

/-- Over a complete nontrivially normed ultrametric field `K`, for any affinoid algebra `A` carrying
a complete ultrametric `K`-algebra norm and any `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`, composing
`π.unitClosedBallMapHom` with `restrictedMvPowerSeriesCompletionIntegerEquiv n` gives a continuous
ring homomorphism `𝒪[K]⟨X₁, …, Xₙ⟩ →+* π(K⟨X₁, …, Xₙ⟩°)` into the subspace topology of `A`. -/
theorem continuous_unitClosedBallMapHom_comp_restrictedMvPowerSeriesCompletionIntegerEquiv
    (hA : IsAffinoidAlgebra K A) {n : ℕ} (π : Tate (Fin n) →ₐ[K] A) :
    Continuous (π.unitClosedBallMapHom.comp
      (Huber.restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n).toRingHom) :=
  (hA.continuous_unitClosedBallMapHom π).comp
    (Huber.continuous_restrictedMvPowerSeriesCompletionIntegerEquiv n)

end TauCeti.IsAffinoidAlgebra
