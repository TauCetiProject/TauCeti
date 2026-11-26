/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.AlmostNoetherian
public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.ResidueField

import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Huber.Restricted.AlmostNoetherian
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Affinoid algebras are the algebras topologically of finite type

Let `K` be a complete nonarchimedean field with a nontrivial absolute value. There are two
notions of an affinoid `K`-algebra in the library.

* The classical one, `TauCeti.IsAffinoidAlgebra K B`, is purely algebraic: `B` is a quotient of a
  Tate algebra `K⟨X₁, …, Xₙ⟩` as a `K`-algebra, with no norm or topology on `B`.
* Huber's one is topological: `B` is a topological `K`-algebra admitting an open quotient map of
  `K`-algebras from the completed Tate algebra, that is
  `TauCeti.Huber.IsTopologicallyFiniteType (algebraMap K B)` (Wedhorn, Definition 5.57). Together
  with its power-bounded subring `B°`, such an algebra is what Wedhorn's Definition 7.56 calls an
  affinoid `K`-algebra.

This file proves that the two notions agree on every complete ultrametric normed `K`-algebra `B`
(`TauCeti.Huber.isTopologicallyFiniteType_algebraMap_iff_isAffinoidAlgebra`). One direction holds
for any topology on `B` (`TauCeti.Huber.IsTopologicallyFiniteType.exists_surjective_algHom`). For
the other, every surjection `π : K⟨X₁, …, Xₙ⟩ → B` of `K`-algebras is automatically continuous
(`TauCeti.IsAffinoidAlgebra.continuous_algHom`). Read through the identification of the completed
Huber Tate algebra with the Gauss-normed one
(`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv`), it is then a presentation in
Huber's sense by the open mapping theorem
(`TauCeti.Huber.isStrictlyTopologicallyFiniteType_of_surjective`). Thus every algebraic Tate
presentation of `B` induces its norm topology.

So the theory of algebras topologically of finite type applies to the classical affinoid algebras
with their Banach topology. In particular they are strongly noetherian Tate rings
(`TauCeti.IsAffinoidAlgebra.isStronglyNoetherian`), and their adic spectra are affinoid adic
spaces (`TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isAffinoidAlgebra`).

We also record the integral-presentation converse (Bosch, *Lectures on Formal and Rigid Geometry*,
§6.4, proof of Lemma 5, pp. 137–138): by
`RingHom.existsUnique_algHom_of_restrictedMvPowerSeriesCompletion`, any `K`-compatible ring
homomorphism `φ : 𝒪[K]⟨X₁, …, Xₙ⟩ →+* A` extends uniquely to a `K`-algebra homomorphism
`π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` with `π(K⟨X₁, …, Xₙ⟩°) = φ.range`. When `φ` surjects onto an open
subring `A₀ : Subring A` for a topology on `A` with separately continuous multiplication and
`algebraMap K A` continuous at `0`, rescaling by a topologically nilpotent pseudouniformizer shows
`π` is surjective onto `A`, so `A` is affinoid. Bundling this data as
`TauCeti.Huber.IntegralAffinoidPresentation` lets callers extend to `K⟨X₁, …, Xₙ⟩ →ₐ[K] A` and
invoke both Kiehl's almost noetherianity theorem (`exists_fg_le_forall_smul_mem`) and Noetherian
finiteness in the discrete valuation ring case (`fg_of_isDiscreteValuationRing`).

## Main definitions

* `TauCeti.Huber.IntegralAffinoidPresentation`: a chosen continuous integral presentation of an
  open bounded subring `A₀ : Subring A` over `K°`, with constructor
  `TauCeti.Huber.IntegralAffinoidPresentation.ofSurjective` from a surjective Tate presentation
  and specializations `TauCeti.Huber.IntegralAffinoidPresentation.unitClosedBallSelf` and
  `TauCeti.Huber.IntegralAffinoidPresentation.ofSubsingleton`.

## Main results

* `TauCeti.IsAffinoidAlgebra.isTopologicallyFiniteType`: a complete ultrametric normed affinoid
  `K`-algebra is topologically of finite type over `K`.
* `TauCeti.Huber.isTopologicallyFiniteType_algebraMap_iff_isAffinoidAlgebra`: for a complete
  ultrametric normed `K`-algebra, being topologically of finite type over `K` is equivalent to
  being affinoid.
* `TauCeti.IsAffinoidAlgebra.isStronglyNoetherian`: a complete ultrametric normed affinoid
  `K`-algebra is strongly noetherian.
* `TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq` and
  `TauCeti.Huber.isAffinoidAlgebra_of_restrictedMvPowerSeriesCompletion`: an open subring presented
  as a `K`-compatible quotient of `𝒪[K]⟨X₁, …, Xₙ⟩` yields a surjective Tate presentation of `A`.
* `TauCeti.Huber.IntegralAffinoidPresentation.tateHom`,
  `TauCeti.Huber.IntegralAffinoidPresentation.tateHom_coe`,
  `TauCeti.Huber.IntegralAffinoidPresentation.continuous_tateHom`,
  `TauCeti.Huber.IntegralAffinoidPresentation.tateHom_unique`,
  `TauCeti.Huber.IntegralAffinoidPresentation.exists_fg_le_forall_smul_mem`, and
  `TauCeti.Huber.IntegralAffinoidPresentation.fg_of_isDiscreteValuationRing`: Tate extension,
  continuity, restriction and uniqueness laws, almost noetherianity, and Noetherian finiteness
  for a bundled integral affinoid presentation.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 5.57 and
  Definition 7.56.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1 and
  §6.1.3.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
-/

public section

namespace TauCeti

open Huber

section AffinoidEquivalence

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

namespace IsAffinoidAlgebra

/-- **A complete ultrametric normed affinoid algebra is topologically of finite type** (Wedhorn,
Definition 5.57): its norm topology is the quotient topology of a Tate presentation. Every
surjection `K⟨X₁, …, Xₙ⟩ → B` of `K`-algebras is a presentation in Huber's sense, by automatic
continuity and the open mapping theorem. -/
theorem isTopologicallyFiniteType (hB : IsAffinoidAlgebra K B) :
    IsTopologicallyFiniteType (algebraMap K B) := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K B).mp hB
  have := MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K) (c := fun _ : Fin n ↦ 1)
  -- precompose with the identification of the completed Tate algebra with the Gauss-normed one
  let e := restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)
  have hc : Continuous (π.comp e.toAlgHom) := by
    simpa [e] using
      (hB.continuous_algHom π).comp continuous_restrictedMvPowerSeriesCompletionGaussEquiv
  exact (isStrictlyTopologicallyFiniteType_of_surjective (π.comp e.toAlgHom) hc.continuousAt
    (hπ.comp e.surjective)).isTopologicallyFiniteType

/-- **A complete ultrametric normed affinoid algebra is strongly noetherian**: being topologically
of finite type over the strongly noetherian Tate ring `K`, every completed Tate algebra over it is
noetherian. -/
theorem isStronglyNoetherian (hB : IsAffinoidAlgebra K B) : IsStronglyNoetherian B :=
  have : IsTateRing B := IsTateRing.of_normedAlgebra K B
  hB.isTopologicallyFiniteType.isStronglyNoetherian

end IsAffinoidAlgebra

/-- **Affinoid algebras are the algebras topologically of finite type.** A complete ultrametric
normed `K`-algebra `B` is topologically of finite type over `K` in Huber's sense (Wedhorn,
Definition 5.57) exactly when it is a quotient of a Tate algebra `K⟨X₁, …, Xₙ⟩` as a
`K`-algebra. -/
theorem Huber.isTopologicallyFiniteType_algebraMap_iff_isAffinoidAlgebra :
    IsTopologicallyFiniteType (algebraMap K B) ↔ IsAffinoidAlgebra K B :=
  ⟨fun h ↦ (isAffinoidAlgebra_iff K B).mpr h.exists_surjective_algHom,
    IsAffinoidAlgebra.isTopologicallyFiniteType⟩

end AffinoidEquivalence

section IntegralPresentation

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
theorem Huber.exists_surjective_algHom_map_unitClosedBall_eq {K : Type*}
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
theorem Huber.isAffinoidAlgebra_of_restrictedMvPowerSeriesCompletion {K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : ContinuousAt (algebraMap K A) 0) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    IsAffinoidAlgebra K A := by
  obtain ⟨π, hπ, -⟩ :=
    Huber.exists_surjective_algHom_map_unitClosedBall_eq hcont hA₀ φ hφ_surj hφ_alg
  exact (isAffinoidAlgebra_iff K A).mpr ⟨n, π, hπ⟩

/-- **A continuous integral affinoid presentation** of a topological `K`-algebra `A`: a chosen open
bounded subring `A₀ : Subring A` equipped with a continuous surjective ring homomorphism
`hom : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K) →+* A₀` compatible with
`Subring.unitClosedBall K` via `coeffHom : Subring.unitClosedBall K →+* A₀`.

Bundling the presentation data as a single object lets callers transport between `K°` and `𝒪[K]`,
extend `hom` to a surjective Tate presentation `K⟨X₁, …, Xₙ⟩ →ₐ[K] A` (`tateHom`), and invoke
both Kiehl's almost noetherianity theorem (`exists_fg_le_forall_smul_mem`) and Noetherian
finiteness in the discrete valuation ring case (`fg_of_isDiscreteValuationRing`). -/
structure Huber.IntegralAffinoidPresentation (K : Type*) [NontriviallyNormedField K]
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

attribute [simp] Huber.IntegralAffinoidPresentation.coe_coeffHom

namespace Huber.IntegralAffinoidPresentation

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

/-- **Canonical identification of `K°⟨X₁, …, Xₙ⟩` with the Gauss unit ball `K⟨X₁, …, Xₙ⟩°`.**
Obtained by transporting `K° ≃+* 𝒪[K]` to
`restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)` and applying
`restrictedMvPowerSeriesCompletionIntegerEquiv`. -/
noncomputable def completionUnitClosedBallEquiv [CompleteSpace K]
    (_P : IntegralAffinoidPresentation K A n A₀) :
    restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K) ≃+*
      Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
  (weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
    continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
    isWeightFamily_one_weight isWeightFamily_one_weight
    (fun _ ↦ by simp [Set.image_singleton, map_one])
    (fun _ ↦ by simp [Set.image_singleton, map_one])).symm.trans
    (restrictedMvPowerSeriesCompletionIntegerEquiv n)

/-- `P.completionUnitClosedBallEquiv` is continuous from the completion topology on
`K°⟨X₁, …, Xₙ⟩` to the subspace Gauss-norm topology on `K⟨X₁, …, Xₙ⟩°`. -/
theorem continuous_completionUnitClosedBallEquiv [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀) :
    Continuous P.completionUnitClosedBallEquiv := by
  have hc : Continuous (weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
      continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
      (isWeightFamily_one_weight (k := n)) (isWeightFamily_one_weight (k := n))
      (fun _ ↦ by simp [Set.image_singleton, map_one])
      (fun _ ↦ by simp [Set.image_singleton, map_one])).symm :=
    continuous_weightedMapCompletionEquiv_symm integerUnitClosedBallEquiv
      continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
      isWeightFamily_one_weight isWeightFamily_one_weight
      (fun _ ↦ by simp [Set.image_singleton, map_one])
      (fun _ ↦ by simp [Set.image_singleton, map_one])
  exact (continuous_restrictedMvPowerSeriesCompletionIntegerEquiv n).comp hc

/-- The inverse of `P.completionUnitClosedBallEquiv` is continuous. -/
theorem continuous_completionUnitClosedBallEquiv_symm [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀) :
    Continuous P.completionUnitClosedBallEquiv.symm := by
  have hc : Continuous (weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
      continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
      (isWeightFamily_one_weight (k := n)) (isWeightFamily_one_weight (k := n))
      (fun _ ↦ by simp [Set.image_singleton, map_one])
      (fun _ ↦ by simp [Set.image_singleton, map_one])) :=
    continuous_weightedMapCompletionEquiv integerUnitClosedBallEquiv
      continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
      isWeightFamily_one_weight isWeightFamily_one_weight
      (fun _ ↦ by simp [Set.image_singleton, map_one])
      (fun _ ↦ by simp [Set.image_singleton, map_one])
  exact hc.comp (continuous_restrictedMvPowerSeriesCompletionIntegerEquiv_symm n)

/-- `P.completionUnitClosedBallEquiv` maps constants in `K°` to constant series in
`K⟨X₁, …, Xₙ⟩°`. -/
theorem completionUnitClosedBallEquiv_algebraMap [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀) (c : Subring.unitClosedBall K) :
    P.completionUnitClosedBallEquiv (algebraMap (Subring.unitClosedBall K) _ c) =
      unitClosedBallCoeffHom c := by
  let e := weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
    continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
    (isWeightFamily_one_weight (k := n)) (isWeightFamily_one_weight (k := n))
    (fun _ ↦ by simp [Set.image_singleton, map_one])
    (fun _ ↦ by simp [Set.image_singleton, map_one])
  have hc : e.symm (algebraMap (Subring.unitClosedBall K) _ c) =
      algebraMap 𝒪[K] _ (integerUnitClosedBallEquiv.symm c) := by
    apply e.injective
    rw [e.apply_symm_apply, algebraMap_completion_weightedRestrictedSubring_apply,
      algebraMap_completion_weightedRestrictedSubring_apply,
      weightedMapCompletionEquiv_coe_weightedC]
    simp
  rw [completionUnitClosedBallEquiv, RingEquiv.trans_apply]
  change restrictedMvPowerSeriesCompletionIntegerEquiv n
    (e.symm (algebraMap (Subring.unitClosedBall K) _ c)) = unitClosedBallCoeffHom c
  rw [hc, restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- `P.completionUnitClosedBallEquiv` maps canonical constant series in `K°⟨X₁, …, Xₙ⟩` to
constant series in `K⟨X₁, …, Xₙ⟩°`. -/
@[simp]
theorem completionUnitClosedBallEquiv_coe_weightedC [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀) (c : Subring.unitClosedBall K) :
    P.completionUnitClosedBallEquiv
        ((weightedC (fun _ : Fin n ↦ ({1} : Set (Subring.unitClosedBall K)))
          isWeightFamily_one_weight c :
            weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set (Subring.unitClosedBall K)))
              isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) =
      unitClosedBallCoeffHom c := by
  rw [← algebraMap_completion_weightedRestrictedSubring_apply,
    P.completionUnitClosedBallEquiv_algebraMap]

/-- The inverse of `P.completionUnitClosedBallEquiv` sends constant series in `K⟨X₁, …, Xₙ⟩°`
back to constants in `K°`. -/
@[simp]
theorem completionUnitClosedBallEquiv_symm_unitClosedBallCoeffHom [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀) (c : Subring.unitClosedBall K) :
    P.completionUnitClosedBallEquiv.symm (unitClosedBallCoeffHom c) =
      algebraMap (Subring.unitClosedBall K) _ c := by
  apply P.completionUnitClosedBallEquiv.injective
  rw [RingEquiv.apply_symm_apply, P.completionUnitClosedBallEquiv_algebraMap]

/-- Under `P.completionUnitClosedBallEquiv`, the polynomial inclusion into `K°⟨X₁, …, Xₙ⟩`
corresponds to `restrictedUnitClosedBallEquiv ∘ polynomialToRestricted`. -/
theorem completionUnitClosedBallEquiv_comp_weightedPolynomialHom [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀) :
    P.completionUnitClosedBallEquiv.toRingHom.comp
        (UniformSpace.Completion.coeRingHom.comp
          (weightedPolynomialHom _ isWeightFamily_one_weight)) =
      (restrictedUnitClosedBallEquiv (σ := Fin n) (R := K)).toRingHom.comp
        (polynomialToRestricted (R := Subring.unitClosedBall K)
          fun _ : Fin n ↦ (1 : ℝ)).toRingHom := by
  refine RingHom.ext fun p ↦ Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun t ↦ ?_
  change MvPowerSeries.coeff t
      ((P.completionUnitClosedBallEquiv
          (weightedPolynomialHom _ isWeightFamily_one_weight p :
            restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) :
          IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :
        MvPowerSeries (Fin n) K) =
    MvPowerSeries.coeff t
      ((restrictedUnitClosedBallEquiv
          (polynomialToRestricted (R := Subring.unitClosedBall K)
            (fun _ : Fin n ↦ (1 : ℝ)) p) :
          IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :
        MvPowerSeries (Fin n) K)
  have hc : Continuous ((integerUnitClosedBallEquiv (K := K)).symm :
      Subring.unitClosedBall K →+* 𝒪[K]) := continuous_integerUnitClosedBallEquiv_symm
  rw [completionUnitClosedBallEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_symm_apply, weightedMapCompletion_coe hc,
    restrictedMvPowerSeriesCompletionIntegerEquiv_coe, coeff_restrictedIntegerEquiv]
  simp only [coe_restrictedMvPowerSeriesGaussEquiv, coe_weightedMap, coe_weightedPolynomialHom,
    coeff_restrictedUnitClosedBallEquiv, coe_polynomialToRestricted, MvPowerSeries.coeff_map,
    MvPolynomial.coeff_coe, RingHom.coe_coe, coe_integerUnitClosedBallEquiv_symm]

/-- The transported integral presentation `𝒪[K]⟨X₁, …, Xₙ⟩ →+* A₀`. -/
private noncomputable def integerHom (P : IntegralAffinoidPresentation K A n A₀) :
    restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀ :=
  P.hom.comp (weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
    continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
    isWeightFamily_one_weight isWeightFamily_one_weight
    (fun _ ↦ by simp [Set.image_singleton, map_one])
    (fun _ ↦ by simp [Set.image_singleton, map_one])).toRingHom

private theorem integerHom_surjective (P : IntegralAffinoidPresentation K A n A₀) :
    Function.Surjective P.integerHom :=
  P.surjective_hom.comp (RingEquiv.surjective _)

private theorem integerHom_algebraMap (P : IntegralAffinoidPresentation K A n A₀) (c : 𝒪[K]) :
    P.integerHom (algebraMap 𝒪[K] _ c) = P.coeffHom (integerUnitClosedBallEquiv c) := by
  rw [integerHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    algebraMap_completion_weightedRestrictedSubring_apply,
    weightedMapCompletionEquiv_coe_weightedC,
    ← algebraMap_completion_weightedRestrictedSubring_apply, P.hom_algebraMap]

private theorem coe_integerHom_algebraMap (P : IntegralAffinoidPresentation K A n A₀) (c : 𝒪[K]) :
    (P.integerHom (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c := by
  rw [P.integerHom_algebraMap, P.coe_coeffHom, coe_integerUnitClosedBallEquiv]

/-- **Kiehl's almost noetherianity theorem for an integral affinoid presentation.** Over a
complete nontrivially normed ultrametric field `K`, for any finitely generated `A₀`-module `M`, any
`A₀`-submodule `N ≤ M`, and any `0 < ε < 1`, there exists a finitely generated `A₀`-submodule
`N' ≤ N` containing `P.coeffHom c • x` for all `c : Subring.unitClosedBall K` with `‖(c : K)‖ ≤ ε`
and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀)
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, P.coeffHom c • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    P.integerHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion
      P.integerHom_surjective N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  let c₀ : 𝒪[K] := integerUnitClosedBallEquiv.symm c
  have hc₀ : ‖(c₀ : K)‖ ≤ ε := by
    simpa only [c₀, coe_integerUnitClosedBallEquiv_symm] using hc
  have heq : P.integerHom (algebraMap 𝒪[K] _ c₀) = P.coeffHom c := by
    rw [P.integerHom_algebraMap, RingEquiv.apply_symm_apply]
  exact heq ▸ hsmul c₀ hc₀ x hx

/-- **Noetherianity over a discrete valuation ring.** When `K°` is a discrete valuation ring, the
presented open bounded subring `A₀` is noetherian (without assuming completeness of `K`). -/
theorem isNoetherianRing_subring (P : IntegralAffinoidPresentation K A n A₀)
    [IsDiscreteValuationRing (Subring.unitClosedBall K)] : IsNoetherianRing A₀ := by
  have : IsNoetherianRing 𝒪[K] :=
    isNoetherianRing_of_ringEquiv (Subring.unitClosedBall K) integerUnitClosedBallEquiv.symm
  have : IsNoetherianRing (restrictedMvPowerSeriesCompletion n 𝒪[K]) :=
    (IsStronglyNoetherian.integer (K := K)).isNoetherianRing n
  have : IsNoetherianRing (restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) :=
    isNoetherianRing_of_ringEquiv _
      (weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
        continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
        isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp [Set.image_singleton, map_one])
        (fun _ ↦ by simp [Set.image_singleton, map_one]))
  exact isNoetherianRing_of_surjective _ _ P.hom P.surjective_hom

/-- **Finite generation over a discrete valuation ring.** When `K°` is a discrete valuation ring,
every submodule `N` of a finitely generated `A₀`-module `M` is finitely generated (without assuming
completeness of `K`). -/
theorem fg_of_isDiscreteValuationRing (P : IntegralAffinoidPresentation K A n A₀)
    [IsDiscreteValuationRing (Subring.unitClosedBall K)]
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) : N.FG := by
  have := P.isNoetherianRing_subring
  exact IsNoetherian.noetherian N

section TateExtension

variable [CompleteSpace K] [SeparatelyContinuousMul A]

/-- Existence of the surjective Tate extension of `P`, via
`TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`. -/
private theorem exists_tateHom_spec (P : IntegralAffinoidPresentation K A n A₀) :
    ∃ π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A,
      Function.Surjective π ∧
      (∀ f : Subring.unitClosedBall
          (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)),
        π f = P.hom (P.completionUnitClosedBallEquiv.symm f)) ∧
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map π.toRingHom = A₀ := by
  obtain ⟨π, hsurj, hball, hmap⟩ :=
    Huber.exists_surjective_algHom_map_unitClosedBall_eq P.continuousAt_algebraMap P.isOpen_subring
      P.integerHom P.integerHom_surjective P.coe_integerHom_algebraMap
  refine ⟨π, hsurj, fun f ↦ ?_, hmap⟩
  exact (hball f).trans rfl

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
`P.completionUnitClosedBallEquiv`. -/
@[simp]
theorem tateHom_coe (P : IntegralAffinoidPresentation K A n A₀)
    (f : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))) :
    P.tateHom f = P.hom (P.completionUnitClosedBallEquiv.symm f) :=
  P.exists_tateHom_spec.choose_spec.2.1 f

/-- Evaluating `P.tateHom` on `P.completionUnitClosedBallEquiv w` recovers `P.hom w`. -/
theorem tateHom_completionUnitClosedBallEquiv (P : IntegralAffinoidPresentation K A n A₀)
    (w : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) :
    P.tateHom (P.completionUnitClosedBallEquiv w) = P.hom w := by
  simp

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
        A₀.subtype ∘ P.hom ∘ P.completionUnitClosedBallEquiv.symm :=
      funext fun f ↦ P.tateHom_coe f
    rw [hsub]
    exact continuous_subtypeVal.comp
      (P.continuous_hom.comp P.continuous_completionUnitClosedBallEquiv_symm)
  exact hB.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hcomp.continuousAt (x := 0))

/-- **Uniqueness of the Tate extension.** Any `K`-algebra homomorphism `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`
whose restriction to the Gauss unit ball agrees with `P.hom ∘ P.completionUnitClosedBallEquiv.symm`
equals `P.tateHom`. -/
theorem tateHom_unique (P : IntegralAffinoidPresentation K A n A₀)
    {π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A}
    (hπ : ∀ f : Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)),
      π f = P.hom (P.completionUnitClosedBallEquiv.symm f)) :
    π = P.tateHom := by
  let ψ : Subring.unitClosedBall
      (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) →+* A :=
    A₀.subtype.comp (P.hom.comp P.completionUnitClosedBallEquiv.symm.toRingHom)
  have hψ (c : Subring.unitClosedBall K) :
      ψ (unitClosedBallCoeffHom c) = algebraMap K A c := by
    rw [RingHom.comp_apply, RingHom.comp_apply, Subring.coe_subtype,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      P.completionUnitClosedBallEquiv_symm_unitClosedBallCoeffHom,
      P.hom_algebraMap, P.coe_coeffHom]
  exact (ψ.existsUnique_algHom_of_unitClosedBall hψ).unique hπ P.tateHom_coe

/-- Uniqueness of `P.tateHom` via agreement on `P.completionUnitClosedBallEquiv`. -/
theorem tateHom_unique_of_completionUnitClosedBallEquiv (P : IntegralAffinoidPresentation K A n A₀)
    {π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A}
    (hπ : ∀ w : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K),
      π (P.completionUnitClosedBallEquiv w) = P.hom w) :
    π = P.tateHom :=
  P.tateHom_unique fun f ↦ by simpa using hπ (P.completionUnitClosedBallEquiv.symm f)

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
`π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`, the Gauss comparison followed by `π.unitClosedBallMapHom` equips the
integral presentation subring `π(K⟨X₁, …, Xₙ⟩°)` with a continuous integral affinoid presentation
over `K°`. -/
noncomputable def ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) :
    IntegralAffinoidPresentation K A n
      ((Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))).map
        (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →+* A)) :=
  let hA : IsAffinoidAlgebra K A := (isAffinoidAlgebra_iff K A).mpr ⟨n, π, hπ⟩
  let e := weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
    continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
    (isWeightFamily_one_weight (k := n)) (isWeightFamily_one_weight (k := n))
    (fun _ ↦ by simp [Set.image_singleton, map_one])
    (fun _ ↦ by simp [Set.image_singleton, map_one])
  let eComp := e.symm.trans (restrictedMvPowerSeriesCompletionIntegerEquiv n)
  { coeffHom := π.unitClosedBallMapHom.comp unitClosedBallCoeffHom
    coe_coeffHom := fun c ↦ π.coe_unitClosedBallMapHom_unitClosedBallCoeffHom c
    hom := π.unitClosedBallMapHom.comp eComp.toRingHom
    continuous_hom := by
      have hc : Continuous e.symm :=
        continuous_weightedMapCompletionEquiv_symm integerUnitClosedBallEquiv
          continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
          (isWeightFamily_one_weight (k := n)) (isWeightFamily_one_weight (k := n))
          (fun _ ↦ by simp [Set.image_singleton, map_one])
          (fun _ ↦ by simp [Set.image_singleton, map_one])
      exact (hA.continuous_unitClosedBallMapHom π).comp
        ((continuous_restrictedMvPowerSeriesCompletionIntegerEquiv n).comp hc)
    surjective_hom :=
      π.unitClosedBallMapHom_surjective.comp eComp.surjective
    hom_algebraMap := fun c ↦ by
      have he : e.symm (algebraMap (Subring.unitClosedBall K) _ c) =
          algebraMap 𝒪[K] _ (integerUnitClosedBallEquiv.symm c) := by
        apply e.injective
        rw [e.apply_symm_apply, algebraMap_completion_weightedRestrictedSubring_apply,
          algebraMap_completion_weightedRestrictedSubring_apply,
          weightedMapCompletionEquiv_coe_weightedC]
        simp
      change π.unitClosedBallMapHom (restrictedMvPowerSeriesCompletionIntegerEquiv n
        (e.symm (algebraMap (Subring.unitClosedBall K) _ c))) =
          π.unitClosedBallMapHom (unitClosedBallCoeffHom c)
      rw [he, restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap, RingEquiv.apply_symm_apply]
    isOpen_subring := by
      have := MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K) (c := fun _ : Fin n ↦ 1)
      simpa only [AlgHom.toRingHom_eq_coe] using hA.isOpen_map_unitClosedBall π hπ
    isBounded_subring := by
      have := MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K) (c := fun _ : Fin n ↦ 1)
      simpa only [AlgHom.toRingHom_eq_coe] using hA.isBounded_map_unitClosedBall π }

/-- The coefficient map of `ofSurjective π hπ` is `π.unitClosedBallMapHom.comp
unitClosedBallCoeffHom`. -/
@[simp]
theorem coeffHom_ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π) :
    (ofSurjective π hπ).coeffHom = π.unitClosedBallMapHom.comp unitClosedBallCoeffHom := by
  rfl

/-- The presentation map `(ofSurjective π hπ).hom` is the Gauss comparison
`(ofSurjective π hπ).completionUnitClosedBallEquiv` followed by `π.unitClosedBallMapHom`. -/
theorem hom_ofSurjective [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (π : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A)
    (hπ : Function.Surjective π)
    (w : restrictedMvPowerSeriesCompletion n (Subring.unitClosedBall K)) :
    (ofSurjective π hπ).hom w =
      π.unitClosedBallMapHom ((ofSurjective π hπ).completionUnitClosedBallEquiv w) := by
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
  rw [hom_ofSurjective, RingEquiv.apply_symm_apply]
  exact (π.coe_unitClosedBallMapHom g).symm

/-- **Canonical self-presentation (`A = K`).** Over a complete nontrivially normed ultrametric
field `K`, the closed unit ball `K°` admits a canonical zero-variable continuous integral affinoid
presentation over `K` itself. -/
noncomputable def unitClosedBallSelf [CompleteSpace K] :
    IntegralAffinoidPresentation K K 0 (Subring.unitClosedBall K) :=
  let e := weightedMapCompletionEquiv (integerUnitClosedBallEquiv (K := K))
    continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
    (isWeightFamily_one_weight (k := 0)) (isWeightFamily_one_weight (k := 0))
    (fun _ ↦ by simp [Set.image_singleton, map_one])
    (fun _ ↦ by simp [Set.image_singleton, map_one])
  let eComp := e.symm.trans (restrictedMvPowerSeriesCompletionIntegerEquiv 0)
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
      have hc : Continuous e.symm :=
        continuous_weightedMapCompletionEquiv_symm integerUnitClosedBallEquiv
          continuous_integerUnitClosedBallEquiv continuous_integerUnitClosedBallEquiv_symm
          (isWeightFamily_one_weight (k := 0)) (isWeightFamily_one_weight (k := 0))
          (fun _ ↦ by simp [Set.image_singleton, map_one])
          (fun _ ↦ by simp [Set.image_singleton, map_one])
      exact hr.comp ((continuous_restrictedMvPowerSeriesCompletionIntegerEquiv 0).comp hc)
    surjective_hom := fun c ↦
      ⟨eComp.symm (unitClosedBallCoeffHom c), by
        simp [r, unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom]⟩
    hom_algebraMap := fun c ↦ by
      have he : e.symm (algebraMap (Subring.unitClosedBall K) _ c) =
          algebraMap 𝒪[K] _ (integerUnitClosedBallEquiv.symm c) := by
        apply e.injective
        rw [e.apply_symm_apply, algebraMap_completion_weightedRestrictedSubring_apply,
          algebraMap_completion_weightedRestrictedSubring_apply,
          weightedMapCompletionEquiv_coe_weightedC]
        simp
      change r (restrictedMvPowerSeriesCompletionIntegerEquiv 0
        (e.symm (algebraMap (Subring.unitClosedBall K) _ c))) = c
      rw [he, restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap, RingEquiv.apply_symm_apply]
      simp [r, unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom]
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

end Huber.IntegralAffinoidPresentation

end IntegralPresentation

end TauCeti
