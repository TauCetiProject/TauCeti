/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.ResidueField

import TauCeti.RingTheory.Affinoid.Continuity
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

We also record the integral-presentation converse: by
`RingHom.existsUnique_algHom_of_restrictedMvPowerSeriesCompletion`, any `K`-compatible ring
homomorphism `φ : 𝒪[K]⟨X₁, …, Xₙ⟩ →+* A` extends uniquely to a `K`-algebra homomorphism
`π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A` with `π(K⟨X₁, …, Xₙ⟩°) = φ.range`. When `φ` surjects onto an open
subring `A₀ : Subring A` for a topology on `A` with separately continuous multiplication and
`algebraMap K A` continuous at `0`, `π` is surjective onto `A`, so `A` is affinoid.

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

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 5.57 and
  Definition 7.56.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1 and
  §6.1.3.
-/

public section

namespace TauCeti

open Huber

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

section IntegralPresentation

open _root_.MvPowerSeries Filter Topology TauCeti.MvPowerSeries
open scoped NormedField Valued

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Topological integral presentations make `A` an affinoid algebra.** Let `K` be a complete
nontrivially normed ultrametric field, `A` a topological `K`-algebra with separately continuous
multiplication and `algebraMap K A` continuous at `0`, and `A₀ : Subring A` an open subring
receiving a `K`-compatible surjective ring homomorphism from
`restrictedMvPowerSeriesCompletion n 𝒪[K]`. Then the canonical extension `π : K⟨X₁, …, Xₙ⟩ →ₐ[K] A`
is **surjective onto `A`** and satisfies `(Subring.unitClosedBall _).map π.toRingHom = A₀`; in
particular `IsAffinoidAlgebra K A` holds. -/
theorem Huber.exists_surjective_algHom_map_unitClosedBall_eq {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : ContinuousAt (algebraMap K A) 0) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    ∃ π : Tate (Fin n) →ₐ[K] A, Function.Surjective π ∧
      (∀ f : Subring.unitClosedBall (Tate (Fin n)),
        π f = φ ((restrictedMvPowerSeriesCompletionIntegerEquiv n).symm f)) ∧
      (Subring.unitClosedBall (Tate (Fin n))).map π.toRingHom = A₀ := by
  have hrange : (A₀.subtype.comp φ).range = A₀ := by
    ext a
    refine ⟨fun ⟨w, hw⟩ ↦ hw ▸ (φ w).2, fun ha ↦ ?_⟩
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

/-- Corollary of `TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`: over a complete
nontrivially normed ultrametric field `K`, any topological `K`-algebra with separately continuous
multiplication and `algebraMap K A` continuous at `0` containing an open subring presented as a
`K`-compatible quotient of `𝒪[K]⟨X₁, …, Xₙ⟩` is an affinoid `K`-algebra. -/
theorem Huber.isAffinoidAlgebra_of_restrictedMvPowerSeriesCompletion {n : ℕ}
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    (hcont : ContinuousAt (algebraMap K A) 0) {A₀ : Subring A} (hA₀ : IsOpen (A₀ : Set A))
    (φ : restrictedMvPowerSeriesCompletion n 𝒪[K] →+* A₀) (hφ_surj : Function.Surjective φ)
    (hφ_alg : ∀ c : 𝒪[K], (φ (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c) :
    IsAffinoidAlgebra K A := by
  obtain ⟨π, hπ, -⟩ :=
    Huber.exists_surjective_algHom_map_unitClosedBall_eq hcont hA₀ φ hφ_surj hφ_alg
  exact (isAffinoidAlgebra_iff K A).mpr ⟨n, π, hπ⟩

end IntegralPresentation

end TauCeti
