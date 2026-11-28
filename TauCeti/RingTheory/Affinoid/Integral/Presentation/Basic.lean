/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.QuotientNorm

/-!
# Integral presentations of affinoid algebras

Let `K` be a complete ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K`
(identified with `𝒪[K]` when `K` is nontrivially normed). Given a `K`-algebra homomorphism
`π : K⟨X⟩ →ₐ[K] A` from a Tate algebra, its *integral presentation subring* is the image
`A₀ = (Subring.unitClosedBall K⟨X⟩).map (π : K⟨X⟩ →+* A)` of the Gauss unit ball. The range
restriction of `(π : K⟨X⟩ →+* A).comp (Subring.unitClosedBall K⟨X⟩).subtype` surjects onto `A₀`,
and when `K` is nontrivially normed and `A` carries a complete ultrametric `K`-algebra norm making
it affinoid, this map and its precomposition with `𝒪[K]⟨X₁, …, Xₙ⟩ ≃+* K⟨X₁, …, Xₙ⟩°` are
continuous into the subspace topology of `A`.

Conversely, when `K` is nontrivially normed and complete, any topological `K`-algebra `A` with
separately continuous multiplication and `algebraMap K A` continuous at `0` containing an open
subring `A₀` receiving a `K`-compatible surjection `φ : 𝒪[K]⟨X₁, …, Xₙ⟩ →+* A₀` extends uniquely
to a surjective Tate presentation `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` with `π(K⟨X₁, …, Xₙ⟩°) = A₀`.
Bundling this data as `TauCeti.Huber.IntegralAffinoidPresentation` lets callers extend `K°`-linear
presentations to Tate presentations (`tateHom`) and construct presentations from surjective Tate
maps (`ofSurjective`), on `K` itself (`unitClosedBallSelf`), or on zero algebras
(`ofSubsingleton`).

## Main definitions

* `TauCeti.Huber.IntegralAffinoidPresentation`: a chosen continuous integral presentation of an
  open bounded subring `A₀ ≤ A` over `K°⟨X₁, …, Xₙ⟩`, together with constructors `ofSurjective`,
  `unitClosedBallSelf`, and `ofSubsingleton`.
* `TauCeti.Huber.IntegralAffinoidPresentation.tateHom`: canonical extension of a continuous integral
  affinoid presentation to a surjective Tate presentation `K⟨X₁, …, Xₙ⟩ →ₐ[K] A`.

## Main results

* `AlgHom.range_comp_subtype_unitClosedBall`: the range of `π` restricted to `K⟨X⟩°` is
  `π(K⟨X⟩°)`.
* `AlgHom.map_unitClosedBall_of_isEmpty`, `AlgHom.map_unitClosedBall_self_of_isEmpty`: in zero
  variables, `π(K⟨X⟩°)` is the image of `K°` in `A`, and equals `K°` on `A = K`.
* `TauCeti.IsAffinoidAlgebra.continuous_rangeRestrict_unitClosedBall` (and its composition with
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionIntegerEquiv`): continuity of the unit-ball
  range restriction and its `𝒪[K]⟨X₁, …, Xₙ⟩` pullback.
* `TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`,
  `TauCeti.Huber.isAffinoidAlgebra_of_restrictedMvPowerSeriesCompletion`: an open subring presented
  over `𝒪[K]⟨X₁, …, Xₙ⟩` yields a surjective Tate presentation and makes `A` affinoid.

## References

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

/-- The range of `π : K⟨X⟩ →ₐ[K] A` restricted to the Gauss unit ball `K⟨X⟩°` is the
integral presentation subring `π(K⟨X⟩°)`. -/
theorem range_comp_subtype_unitClosedBall (π : Tate σ →ₐ[K] A) :
    ((π : Tate σ →+* A).comp (Subring.unitClosedBall (Tate σ)).subtype).range =
      (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A) := by
  ext a
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

/-- Constants of norm at most one in `K` map into the integral presentation subring `π(K⟨X⟩°)`. -/
theorem algebraMap_mem_map_unitClosedBall (π : Tate σ →ₐ[K] A) {c : K} (hc : ‖c‖ ≤ 1) :
    algebraMap K A c ∈ (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A) :=
  ⟨algebraMap K (Tate σ) c, Subring.mem_unitClosedBall.mpr
    ((norm_algebraMap_isRestrictedSubring c).trans_le hc), π.commutes c⟩

/-- Evaluating the range restriction of `π` on a constant series `unitClosedBallC c` yields
`algebraMap K A c` in `π(K⟨X⟩°)`. -/
@[simp]
theorem subringCongr_rangeRestrict_unitClosedBallC (π : Tate σ →ₐ[K] A)
    (c : Subring.unitClosedBall K) :
    RingEquiv.subringCongr π.range_comp_subtype_unitClosedBall
        (((π : Tate σ →+* A).comp (Subring.unitClosedBall (Tate σ)).subtype).rangeRestrict
          (TauCeti.MvPowerSeries.unitClosedBallC (σ := σ) (r := fun _ ↦ 1) c)) =
      ⟨algebraMap K A c,
        π.algebraMap_mem_map_unitClosedBall (Subring.mem_unitClosedBall.mp c.property)⟩ :=
  Subtype.ext <| by
    simp only [RingEquiv.coe_subringCongr_apply, RingHom.coe_rangeRestrict, RingHom.comp_apply,
      Subring.coe_subtype, TauCeti.MvPowerSeries.coe_unitClosedBallC]
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

end AlgHom

namespace TauCeti

namespace IsAffinoidAlgebra

open _root_.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- Over a complete nontrivially normed ultrametric field `K`, for any affinoid algebra `A` carrying
a complete ultrametric `K`-algebra norm, any finite variable set `σ`, and any `K`-algebra
homomorphism `π : K⟨X⟩ →ₐ[K] A`, the range restriction of `π` on `K⟨X⟩°` is continuous into the
subspace topology of `A`. -/
theorem continuous_rangeRestrict_unitClosedBall (hA : IsAffinoidAlgebra K A)
    (π : Tate σ →ₐ[K] A) :
    Continuous ((π : Tate σ →+* A).comp
      (Subring.unitClosedBall (Tate σ)).subtype).rangeRestrict := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  exact continuous_induced_rng.mpr <| by
    simpa only [Function.comp_def, RingHom.coe_rangeRestrict, RingHom.comp_apply,
      Subring.coe_subtype, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
      (hA.continuous_algHom π).comp continuous_subtypeVal

/-- Over a complete nontrivially normed ultrametric field `K`, for any affinoid algebra `A` carrying
a complete ultrametric `K`-algebra norm and any `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`, composing the range
restriction of `π` on `K⟨X₁, …, Xₙ⟩°` with `restrictedMvPowerSeriesCompletionIntegerEquiv n` gives
a continuous ring homomorphism from `𝒪[K]⟨X₁, …, Xₙ⟩` into the subspace topology of `A`. -/
theorem continuous_rangeRestrict_unitClosedBall_comp_restrictedMvPowerSeriesCompletionIntegerEquiv
    (hA : IsAffinoidAlgebra K A) {n : ℕ} (π : Tate (Fin n) →ₐ[K] A) :
    Continuous
      ((((π : Tate (Fin n) →+* A).comp
          (Subring.unitClosedBall (Tate (Fin n))).subtype).rangeRestrict).comp
        (Huber.restrictedMvPowerSeriesCompletionIntegerEquiv (K := K) n).toRingHom) :=
  (hA.continuous_rangeRestrict_unitClosedBall π).comp
    (Huber.continuous_restrictedMvPowerSeriesCompletionIntegerEquiv n)

end IsAffinoidAlgebra

namespace Huber

open _root_.MvPowerSeries Filter Topology TauCeti.MvPowerSeries
open scoped NormedField Valued

/-- **Topological integral presentations make `A` an affinoid algebra** (Bosch, *Lectures on
Formal and Rigid Geometry*, §6.4, proof of Lemma 5, pp. 137–138). Let `K` be a complete
nontrivially normed ultrametric field, `A` a topological `K`-algebra with separately continuous
multiplication and `algebraMap K A` continuous at `0`, and `A₀ : Subring A` an open subring
receiving a `K`-compatible surjective ring homomorphism from
`restrictedMvPowerSeriesCompletion n 𝒪[K]`. Extending along `𝒪[K]⟨X₁, …, Xₙ⟩ ≃+* K⟨X₁, …, Xₙ⟩°`
and rescaling by a topologically nilpotent pseudouniformizer shows that the canonical extension
`π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` is **surjective onto `A`** and satisfies
`(Subring.unitClosedBall _).map π.toRingHom = A₀`. -/
theorem exists_surjective_algHom_map_unitClosedBall_eq {K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : ContinuousAt (algebraMap K A) 0) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    ∃ π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A, Function.Surjective π ∧
      (∀ f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)),
        π f = φ ((restrictedMvPowerSeriesCompletionIntegerEquiv n).symm f)) ∧
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map π.toRingHom = A₀ := by
  have hrange : (A₀.subtype.comp φ).range = A₀ := by
    ext a
    refine ⟨fun ⟨w, hw⟩ ↦ hw ▸ (φ w).property, fun ha ↦ ?_⟩
    obtain ⟨w, hw⟩ := hφ_surj ⟨a, ha⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  obtain ⟨π, ⟨hπ_ball, hπ_map⟩, -⟩ :=
    (A₀.subtype.comp φ).existsUnique_algHom_of_restrictedMvPowerSeriesCompletion hφ_alg
  rw [hrange] at hπ_map
  refine ⟨π, fun a ↦ ?_,
    fun f ↦ by simpa only [RingHom.comp_apply, Subring.coe_subtype] using hπ_ball f, hπ_map⟩
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hs : IsTopologicallyNilpotent (algebraMap K A ϖ) := by
    simpa only [IsTopologicallyNilpotent, Function.comp_def, ← map_pow,
      ← map_zero (algebraMap K A)] using
      hcont.tendsto.comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1)
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hs hA₀ a
  rw [← map_pow, mul_comm, ← hπ_map] at hk
  obtain ⟨g, -, hg⟩ := hk
  refine ⟨(ϖ ^ k)⁻¹ • g, ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hg
  rw [map_smul, hg, ← Algebra.smul_def, inv_smul_smul₀ (pow_ne_zero k (norm_pos_iff.mp hϖ0))]

/-- **Affinoidness from a topological integral presentation** (Bosch, *Lectures on Formal and
Rigid Geometry*, §6.4, proof of Lemma 5, pp. 137–138): over a complete nontrivially normed
ultrametric field `K`, any topological `K`-algebra with separately continuous multiplication and
`algebraMap K A` continuous at `0` containing an open subring presented as a `K`-compatible
quotient of `𝒪[K]⟨X₁, …, Xₙ⟩` is an affinoid `K`-algebra. -/
theorem isAffinoidAlgebra_of_restrictedMvPowerSeriesCompletion {K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : ContinuousAt (algebraMap K A) 0) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    IsAffinoidAlgebra K A := by
  obtain ⟨π, hπ, -⟩ :=
    exists_surjective_algHom_map_unitClosedBall_eq hcont hA₀ φ hφ_surj hφ_alg
  exact (isAffinoidAlgebra_iff K A).mpr ⟨n, π, hπ⟩

/-- **A continuous integral affinoid presentation** of a topological `K`-algebra `A`: a chosen open
bounded subring `A₀ : Subring A` equipped with a continuous surjective ring homomorphism
`hom : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K) →+* A₀` compatible with
`Subring.unitClosedBall K` via `coeffHom : Subring.unitClosedBall K →+* A₀`.

Bundling the presentation data as a single object lets callers extend `hom` to a surjective Tate
presentation `K⟨X₁, …, Xₙ⟩ →ₐ[K] A` (`tateHom`) and deduce noetherianity or Kiehl's almost
noetherianity for `A₀`-modules in downstream modules. -/
structure IntegralAffinoidPresentation (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A] [TopologicalSpace A]
    (n : ℕ) (A₀ : Subring A) where
  /-- The coefficient map `K° →+* A₀`. -/
  coeffHom : Subring.unitClosedBall K →+* A₀
  /-- Compatibility of `coeffHom` with the `K`-algebra structure on `A`. -/
  coe_coeffHom : ∀ c : Subring.unitClosedBall K, (coeffHom c : A) = algebraMap K A c
  /-- The continuous surjective presentation `K°⟨X₁, …, Xₙ⟩ →+* A₀`. -/
  hom : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K) →+* A₀
  /-- Continuity of `hom` into the subspace topology of `A₀`. -/
  continuous_hom : Continuous hom
  /-- Surjectivity of `hom`. -/
  surjective_hom : Function.Surjective hom
  /-- Compatibility of `hom` on constant series with `coeffHom`. -/
  hom_algebraMap : ∀ c : Subring.unitClosedBall K,
    hom (algebraMap (Subring.unitClosedBall K) _ c) = coeffHom c
  /-- Openness of `A₀` in `A`. -/
  isOpen_subring : IsOpen (A₀ : Set A)
  /-- Boundedness of `A₀` in `A`. -/
  isBounded_subring : IsBounded (A₀ : Set A)

attribute [simp] IntegralAffinoidPresentation.coe_coeffHom

namespace IntegralAffinoidPresentation

section Basic

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A]
  {n : ℕ} {A₀ : Subring A}

/-- Continuity of the coefficient map `P.coeffHom : K° →+* A₀` into the subspace topology of
`A₀`. -/
theorem continuous_coeffHom (P : IntegralAffinoidPresentation K A n A₀) :
    Continuous P.coeffHom := by
  have hfn : (P.coeffHom : Subring.unitClosedBall K → A₀) =
      fun c ↦ P.hom (algebraMap (Subring.unitClosedBall K) _ c) :=
    funext fun c ↦ (P.hom_algebraMap c).symm
  rw [hfn]
  exact P.continuous_hom.comp
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K))

/-- Continuity of `algebraMap K A` at `0`, deduced from `P.continuous_coeffHom` and openness of
`Subring.unitClosedBall K` in `K`. -/
theorem continuousAt_algebraMap (P : IntegralAffinoidPresentation K A n A₀) :
    ContinuousAt (algebraMap K A) 0 := by
  have hcomp : ContinuousAt ((algebraMap K A) ∘ (Subring.unitClosedBall K).subtype) 0 := by
    have hsub : ((algebraMap K A) ∘ (Subring.unitClosedBall K).subtype :
          Subring.unitClosedBall K → A) = A₀.subtype ∘ P.coeffHom :=
      funext fun c ↦ (P.coe_coeffHom c).symm
    rw [hsub]
    exact (continuous_subtypeVal.comp P.continuous_coeffHom).continuousAt
  exact ((Subring.isOpen_unitClosedBall K).isOpenEmbedding_subtypeVal.continuousAt_iff).mp hcomp

section TateExtension

variable [CompleteSpace K] [SeparatelyContinuousMul A]

/-- The transported integral presentation `𝒪[K]⟨X₁, …, Xₙ⟩ →+* A₀`. -/
private noncomputable def integerHom (P : IntegralAffinoidPresentation K A n A₀) :
    restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀ :=
  P.hom.comp (restrictedMvPowerSeriesCompletionIntegerUnitClosedBallEquiv (K := K) n).toRingHom

/-- Existence of the surjective Tate extension of `P`, via
`TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`. -/
private theorem exists_tateHom_spec (P : IntegralAffinoidPresentation K A n A₀) :
    ∃ π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A,
      Function.Surjective π ∧
      (∀ f : Subring.unitClosedBall
          (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)),
        π f = P.hom ((restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n).symm f)) ∧
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map π.toRingHom = A₀ := by
  have hsurj : Function.Surjective P.integerHom :=
    P.surjective_hom.comp (RingEquiv.surjective _)
  have halg (c : 𝒪[K]) : (P.integerHom (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c := by
    rw [integerHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      restrictedMvPowerSeriesCompletionIntegerUnitClosedBallEquiv_algebraMap, P.hom_algebraMap,
      P.coe_coeffHom, coe_integerUnitClosedBallEquiv]
  obtain ⟨π, hπ_surj, hball, hmap⟩ :=
    Huber.exists_surjective_algHom_map_unitClosedBall_eq P.continuousAt_algebraMap P.isOpen_subring
      P.integerHom hsurj halg
  refine ⟨π, hπ_surj, fun f ↦ (hball f).trans ?_, hmap⟩
  rw [integerHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    restrictedMvPowerSeriesCompletionIntegerEquiv_symm_apply, RingEquiv.apply_symm_apply]

/-- **Tate extension of an integral affinoid presentation.** Over a complete nontrivially normed
ultrametric field `K`, for a topological `K`-algebra `A` with separately continuous multiplication,
`P.hom` extends to a surjective `K`-algebra homomorphism `K⟨X₁, …, Xₙ⟩ →ₐ[K] A` mapping the Gauss
unit ball onto `A₀`. -/
noncomputable def tateHom (P : IntegralAffinoidPresentation K A n A₀) :
    IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A :=
  P.exists_tateHom_spec.choose

/-- `P.tateHom` is surjective onto `A`. -/
theorem tateHom_surjective (P : IntegralAffinoidPresentation K A n A₀) :
    Function.Surjective P.tateHom :=
  P.exists_tateHom_spec.choose_spec.1

/-- Restricting `P.tateHom` to the Gauss unit ball recovers `P.hom` transported along
`restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n`. -/
@[simp]
theorem tateHom_coe (P : IntegralAffinoidPresentation K A n A₀)
    (f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))) :
    P.tateHom f = P.hom ((restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n).symm f) :=
  P.exists_tateHom_spec.choose_spec.2.1 f

/-- `P.tateHom` is continuous when `A` is a topological additive group. -/
theorem continuous_tateHom [IsTopologicalAddGroup A]
    (P : IntegralAffinoidPresentation K A n A₀) :
    Continuous P.tateHom := by
  refine continuous_of_continuousAt_zero P.tateHom ?_
  let T := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  have hB : IsOpen (Subring.unitClosedBall T : Set T) := Subring.isOpen_unitClosedBall T
  have hcomp : Continuous (P.tateHom ∘ (Subring.unitClosedBall T).subtype) := by
    have hsub : (P.tateHom ∘ (Subring.unitClosedBall T).subtype :
          Subring.unitClosedBall T → A) =
        A₀.subtype ∘ P.hom ∘ (restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n).symm :=
      funext fun f ↦ P.tateHom_coe f
    rw [hsub]
    exact continuous_subtypeVal.comp
      (P.continuous_hom.comp
        (continuous_restrictedMvPowerSeriesCompletionUnitClosedBallEquiv_symm n))
  exact hB.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hcomp.continuousAt (x := 0))

/-- **Uniqueness of the Tate extension.** Any `K`-algebra homomorphism `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`
whose restriction to the Gauss unit ball agrees with
`P.hom ∘ (restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n).symm` equals `P.tateHom`. -/
theorem tateHom_unique (P : IntegralAffinoidPresentation K A n A₀)
    {π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A}
    (hπ : ∀ f : Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)),
      π f = P.hom ((restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n).symm f)) :
    π = P.tateHom := by
  let ψ : Subring.unitClosedBall
      (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) →+* A :=
    A₀.subtype.comp
      (P.hom.comp (restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n).symm.toRingHom)
  have hψ (c : Subring.unitClosedBall K) :
      ψ (unitClosedBallC c) = algebraMap K A c := by
    rw [RingHom.comp_apply, RingHom.comp_apply, Subring.coe_subtype,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      restrictedMvPowerSeriesCompletionUnitClosedBallEquiv_symm_unitClosedBallC,
      P.hom_algebraMap, P.coe_coeffHom]
  exact (ψ.existsUnique_algHom_of_unitClosedBall hψ).unique hπ P.tateHom_coe

/-- The Gauss unit ball of `K⟨X₁, …, Xₙ⟩` maps under `P.tateHom` onto the presented open bounded
subring `A₀`. -/
theorem map_unitClosedBall_tateHom (P : IntegralAffinoidPresentation K A n A₀) :
    (Subring.unitClosedBall
      (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map P.tateHom.toRingHom =
      A₀ :=
  P.exists_tateHom_spec.choose_spec.2.2

/-- An integral affinoid presentation witnesses that `A` is an affinoid `K`-algebra. -/
theorem isAffinoidAlgebra (P : IntegralAffinoidPresentation K A n A₀) : IsAffinoidAlgebra K A :=
  (isAffinoidAlgebra_iff K A).mpr ⟨n, P.tateHom, P.tateHom_surjective⟩

/-- Existential formulation of `P.tateHom`, `P.tateHom_surjective`, and
`P.map_unitClosedBall_tateHom`. -/
theorem exists_surjective_algHom_map_unitClosedBall_eq
    (P : IntegralAffinoidPresentation K A n A₀) :
    ∃ π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A,
      Function.Surjective π ∧
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map π.toRingHom = A₀ :=
  ⟨P.tateHom, P.tateHom_surjective, P.map_unitClosedBall_tateHom⟩

end TateExtension

end Basic

section Constructors

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Integral affinoid presentation induced by a surjective Tate presentation.** Given a complete
ultrametric normed `K`-algebra `A` and a surjective `K`-algebra homomorphism
`π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`, the Gauss comparison followed by the range restriction of `π` on
`K⟨X₁, …, Xₙ⟩°` equips the integral presentation subring `π(K⟨X₁, …, Xₙ⟩°)` with a continuous
integral affinoid presentation over `K°`. -/
noncomputable def ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) :
    IntegralAffinoidPresentation K A n
      ((Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map
        (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →+* A)) :=
  let hA : IsAffinoidAlgebra K A := (isAffinoidAlgebra_iff K A).mpr ⟨n, π, hπ⟩
  let eComp := restrictedMvPowerSeriesCompletionUnitClosedBallEquiv (R := K) n
  let q := (RingEquiv.subringCongr π.range_comp_subtype_unitClosedBall).toRingHom.comp
    ((π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →+* A).comp
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).subtype).rangeRestrict
  { coeffHom := q.comp unitClosedBallC
    coe_coeffHom := fun c ↦ by
      simp only [q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.subringCongr_rangeRestrict_unitClosedBallC]
    hom := q.comp eComp.toRingHom
    continuous_hom := by
      have := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
      refine continuous_induced_rng.mpr ?_
      simpa only [q, eComp, Function.comp_def, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, RingEquiv.coe_subringCongr_apply, RingHom.coe_rangeRestrict,
        Subring.coe_subtype, AlgHom.coe_toRingHom] using
        ((hA.continuous_algHom π).comp continuous_subtypeVal).comp
          (continuous_restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n)
    surjective_hom := by
      have hq : Function.Surjective q := by
        simpa only [q, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using
          (RingEquiv.surjective _).comp (RingHom.rangeRestrict_surjective _)
      simpa only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using
        hq.comp eComp.surjective
    hom_algebraMap := fun c ↦ by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, eComp,
        restrictedMvPowerSeriesCompletionUnitClosedBallEquiv_algebraMap]
    isOpen_subring := by
      have := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
      simpa only [AlgHom.toRingHom_eq_coe] using hA.isOpen_map_unitClosedBall π hπ
    isBounded_subring := by
      have := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
      simpa only [AlgHom.toRingHom_eq_coe] using hA.isBounded_map_unitClosedBall π }

/-- The coefficient map of `ofSurjective π hπ` agrees with `algebraMap K A` on `K°`. -/
@[simp]
theorem coeffHom_ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) (c : Subring.unitClosedBall K) :
    (ofSurjective π hπ).coeffHom c =
      ⟨algebraMap K A c,
        π.algebraMap_mem_map_unitClosedBall (Subring.mem_unitClosedBall.mp c.property)⟩ :=
  π.subringCongr_rangeRestrict_unitClosedBallC c

/-- The presentation map `(ofSurjective π hπ).hom` is the Gauss comparison
`restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n` followed by the range restriction of `π`
onto `π(K⟨X₁, …, Xₙ⟩°)`. -/
theorem hom_ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π)
    (w : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) :
    (ofSurjective π hπ).hom w =
      RingEquiv.subringCongr π.range_comp_subtype_unitClosedBall
        (((π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →+* A).comp
          (Subring.unitClosedBall
            (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).subtype).rangeRestrict
          (restrictedMvPowerSeriesCompletionUnitClosedBallEquiv n w)) := by
  rfl

/-- Extending `ofSurjective π hπ` back to a Tate homomorphism recovers `π`. -/
@[simp]
theorem tateHom_ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) :
    (ofSurjective π hπ).tateHom = π := by
  symm
  refine (ofSurjective π hπ).tateHom_unique fun g ↦ ?_
  rw [hom_ofSurjective, RingEquiv.apply_symm_apply, RingEquiv.coe_subringCongr_apply,
    RingHom.coe_rangeRestrict, RingHom.comp_apply, Subring.coe_subtype, AlgHom.coe_toRingHom]

/-- **Canonical self-presentation (`A = K`).** Over a complete nontrivially normed ultrametric
field `K`, the closed unit ball `K°` admits a canonical zero-variable continuous integral affinoid
presentation over `K` itself. -/
noncomputable def unitClosedBallSelf [CompleteSpace K] :
    IntegralAffinoidPresentation K K 0 (Subring.unitClosedBall K) :=
  let eComp := restrictedMvPowerSeriesCompletionUnitClosedBallEquiv (R := K) 0
  let r : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1)) →+*
      Subring.unitClosedBall K :=
    unitClosedBallConstantCoeffHom
  { coeffHom := RingHom.id _
    coe_coeffHom := fun _ ↦ rfl
    hom := r.comp eComp.toRingHom
    continuous_hom := by
      have hr : Continuous r :=
        AddMonoidHomClass.continuous_of_bound r 1 fun f ↦ by
          simpa only [r, one_mul, AddSubgroupClass.coe_norm,
            coe_unitClosedBallConstantCoeffHom] using
            norm_constantCoeff_le (f : IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1))
      exact hr.comp (continuous_restrictedMvPowerSeriesCompletionUnitClosedBallEquiv 0)
    surjective_hom := fun c ↦
      ⟨eComp.symm (unitClosedBallC c), by
        simp [r, unitClosedBallConstantCoeffHom_unitClosedBallC]⟩
    hom_algebraMap := fun c ↦ by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingHom.id_apply, eComp, r,
        restrictedMvPowerSeriesCompletionUnitClosedBallEquiv_algebraMap,
        unitClosedBallConstantCoeffHom_unitClosedBallC]
    isOpen_subring := Subring.isOpen_unitClosedBall K
    isBounded_subring := Subring.coe_unitClosedBall K ▸ isBounded_closedBall_zero 1 }

/-- The coefficient map of `unitClosedBallSelf` is the identity on `K°`. -/
@[simp]
theorem coeffHom_unitClosedBallSelf [CompleteSpace K] :
    (unitClosedBallSelf (K := K)).coeffHom = RingHom.id (Subring.unitClosedBall K) := by
  rfl

/-- **Zero-algebra presentation.** Any subsingleton topological `K`-algebra `A` admits a
zero-variable continuous integral affinoid presentation onto any (hence its unique) subring
`A₀ : Subring A`. -/
def ofSubsingleton {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A]
    [Subsingleton A] (A₀ : Subring A) :
    IntegralAffinoidPresentation K A 0 A₀ where
  coeffHom :=
    { toFun := fun _ ↦ 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  coe_coeffHom := fun _ ↦ Subsingleton.elim _ _
  hom :=
    { toFun := fun _ ↦ 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  continuous_hom := continuous_const
  surjective_hom := fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  hom_algebraMap := fun _ ↦ Subsingleton.elim _ _
  isOpen_subring := by
    have h : (A₀ : Set A) = Set.univ :=
      Set.eq_univ_of_forall fun a ↦ (Subsingleton.elim a 0).symm ▸ A₀.zero_mem
    exact h ▸ isOpen_univ
  isBounded_subring := isBounded_singleton_zero.subset fun a _ ↦ Subsingleton.elim a 0

/-- **Zero-variable image.** Any continuous integral affinoid presentation with zero variables has
open bounded subring `A₀` equal to the image of `K°` under `algebraMap K A`. -/
theorem subring_eq_map_unitClosedBall [CompleteSpace K]
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    {A₀ : Subring A} (P : IntegralAffinoidPresentation K A 0 A₀) :
    A₀ = (Subring.unitClosedBall K).map (algebraMap K A) := by
  rw [← P.map_unitClosedBall_tateHom, AlgHom.toRingHom_eq_coe,
    P.tateHom.map_unitClosedBall_of_isEmpty]

/-- `(⊤ : Subring K)` cannot admit a continuous integral affinoid presentation over `K`, since a
nontrivially normed field is not bounded in its own topology. -/
theorem isEmpty_top (n : ℕ) :
    _root_.IsEmpty (IntegralAffinoidPresentation K K n ⊤) :=
  ⟨fun P ↦ not_isBounded_univ_of_nontriviallyNormedField K (by simpa using P.isBounded_subring)⟩

end Constructors

end IntegralAffinoidPresentation

end Huber

end TauCeti
