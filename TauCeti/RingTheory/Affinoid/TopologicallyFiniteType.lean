/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.ResidueField

import TauCeti.RingTheory.Affinoid.AlmostNoetherian
import TauCeti.RingTheory.Affinoid.Continuity
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
invoke both Kiehl's almost noetherianity theorem (`almost_noetherian`) and Noetherian finiteness in
the discrete valuation ring case (`fg_of_discrete`).

## Main definitions

* `TauCeti.Huber.IntegralAffinoidPresentation`: a chosen continuous integral presentation of an
  open bounded subring `A₀ : Subring A` over `V = K°`.

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
  `TauCeti.Huber.IntegralAffinoidPresentation.almost_noetherian`, and
  `TauCeti.Huber.IntegralAffinoidPresentation.fg_of_discrete`: Tate extension, image equality,
  almost noetherianity, and Noetherian finiteness for a bundled integral affinoid presentation.

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
`hom : restrictedMvPowerSeriesCompletion numVars V →+* A₀` compatible with the subring
`V = Subring.unitClosedBall K` via `coeffHom : V →+* A₀`.

Bundling the presentation data as a single object lets callers transport between `V` and `𝒪[K]`,
extend `hom` to a surjective Tate presentation `K⟨X₁, …, Xₙ⟩ →ₐ[K] A` (`tateHom`), and invoke
both Kiehl's almost noetherianity theorem (`almost_noetherian`) and Noetherian finiteness in the
discrete valuation ring case (`fg_of_discrete`). -/
structure Huber.IntegralAffinoidPresentation (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (A : Type*) [CommRing A] [Algebra K A] [TopologicalSpace A]
    (V : Subring K) (A₀ : Subring A) where
  /-- Identification of `V` with the closed unit ball `K°` of `K`. -/
  unitClosedBall_eq : V = Subring.unitClosedBall K
  /-- The number of restricted power-series variables. -/
  numVars : ℕ
  /-- The coefficient map `V →+* A₀`. -/
  coeffHom : V →+* A₀
  /-- Compatibility of `coeffHom` with the `K`-algebra structure on `A`. -/
  coe_coeffHom : ∀ c : V, (coeffHom c : A) = algebraMap K A c
  /-- The continuous surjective presentation `V⟨X₁, …, Xₙ⟩ →+* A₀`. -/
  hom : restrictedMvPowerSeriesCompletion numVars V →+* A₀
  /-- Continuity of `hom` into the subspace topology of `A₀`. -/
  continuous_hom : Continuous hom
  /-- Surjectivity of `hom`. -/
  surjective_hom : Function.Surjective hom
  /-- Compatibility of `hom` on constant series with `coeffHom`. -/
  hom_algebraMap : ∀ c : V, hom (algebraMap V _ c) = coeffHom c
  /-- Openness of `A₀` in `A`. -/
  isOpen_subring : IsOpen (A₀ : Set A)
  /-- Boundedness of `A₀` in `A`. -/
  isBounded_subring : IsBounded (A₀ : Set A)

attribute [simp] Huber.IntegralAffinoidPresentation.coe_coeffHom

namespace Huber.IntegralAffinoidPresentation

section Basic

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A]
  {V : Subring K} {A₀ : Subring A}

/-- Membership in the base integral subring `V` is equivalent to having norm at most `1`. -/
theorem mem_iff_norm_le_one (P : IntegralAffinoidPresentation K A V A₀) (c : K) :
    c ∈ V ↔ ‖c‖ ≤ 1 := by
  rw [P.unitClosedBall_eq, Subring.mem_unitClosedBall]

/-- Continuity of the canonical constant-series inclusion `V →+* V⟨X₁, …, Xₙ⟩`. -/
private theorem continuous_algebraMap_completion (P : IntegralAffinoidPresentation K A V A₀) :
    Continuous (algebraMap V (restrictedMvPowerSeriesCompletion P.numVars V)) := by
  have hfn :
      (algebraMap V (restrictedMvPowerSeriesCompletion P.numVars V) :
          V → restrictedMvPowerSeriesCompletion P.numVars V) =
        fun c ↦ (weightedC (fun _ : Fin P.numVars ↦ ({1} : Set V))
          isWeightFamily_one_weight c : restrictedMvPowerSeriesCompletion P.numVars V) := by
    ext c
    exact algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight c
  rw [hfn]
  exact (UniformSpace.Completion.continuous_coe _).comp
    (continuous_weightedC isWeightFamily_one_weight)

/-- Continuity of the coefficient map `P.coeffHom : V →+* A₀` into the subspace topology of
`A₀`. -/
theorem continuous_coeffHom (P : IntegralAffinoidPresentation K A V A₀) :
    Continuous P.coeffHom := by
  have hfn : (P.coeffHom : V → A₀) = fun c ↦ P.hom (algebraMap V _ c) :=
    funext fun c ↦ (P.hom_algebraMap c).symm
  rw [hfn]
  exact P.continuous_hom.comp P.continuous_algebraMap_completion

/-- Continuity of `algebraMap K A` at `0`, deduced from `P.continuous_coeffHom` and openness of
`V = Subring.unitClosedBall K` in `K`. -/
theorem continuousAt_algebraMap (P : IntegralAffinoidPresentation K A V A₀) :
    ContinuousAt (algebraMap K A) 0 := by
  have hV : IsOpen (V : Set K) := P.unitClosedBall_eq.symm ▸ Subring.isOpen_unitClosedBall K
  have hcomp : ContinuousAt ((algebraMap K A) ∘ V.subtype) 0 := by
    have hsub : ((algebraMap K A) ∘ V.subtype : V → A) = A₀.subtype ∘ P.coeffHom :=
      funext fun c ↦ (P.coe_coeffHom c).symm
    rw [hsub]
    exact (continuous_subtypeVal.comp P.continuous_coeffHom).continuousAt
  exact (hV.isOpenEmbedding_subtypeVal.continuousAt_iff).mp hcomp

/-- Canonical topological ring isomorphism `𝒪[K] ≃+* V` between the valuation ring of `K` and
`V`. -/
private noncomputable def integerRingEquiv (P : IntegralAffinoidPresentation K A V A₀) :
    𝒪[K] ≃+* V :=
  RingEquiv.subringCongr (integer_eq_unitClosedBall.trans P.unitClosedBall_eq.symm)

private theorem continuous_integerRingEquiv (P : IntegralAffinoidPresentation K A V A₀) :
    Continuous P.integerRingEquiv :=
  continuous_induced_rng.mpr continuous_subtypeVal

private theorem continuous_integerRingEquiv_symm (P : IntegralAffinoidPresentation K A V A₀) :
    Continuous P.integerRingEquiv.symm :=
  continuous_induced_rng.mpr continuous_subtypeVal

/-- Transporting `𝒪[K]⟨X₁, …, Xₙ⟩` to `V⟨X₁, …, Xₙ⟩` along `P.integerRingEquiv`. -/
private noncomputable def completionIntegerEquiv (P : IntegralAffinoidPresentation K A V A₀) :
    restrictedMvPowerSeriesCompletion P.numVars 𝒪[K] ≃+*
      restrictedMvPowerSeriesCompletion P.numVars V :=
  weightedMapCompletionEquiv P.integerRingEquiv P.continuous_integerRingEquiv
    P.continuous_integerRingEquiv_symm isWeightFamily_one_weight isWeightFamily_one_weight
    (fun _ ↦ by simp [Set.image_singleton]) (fun _ ↦ by simp [Set.image_singleton])

/-- The transported integral presentation `𝒪[K]⟨X₁, …, Xₙ⟩ →+* A₀`. -/
private noncomputable def integerHom (P : IntegralAffinoidPresentation K A V A₀) :
    restrictedMvPowerSeriesCompletion P.numVars 𝒪[K] →+* A₀ :=
  P.hom.comp P.completionIntegerEquiv.toRingHom

private theorem integerHom_surjective (P : IntegralAffinoidPresentation K A V A₀) :
    Function.Surjective P.integerHom :=
  P.surjective_hom.comp P.completionIntegerEquiv.surjective

private theorem integerHom_algebraMap (P : IntegralAffinoidPresentation K A V A₀) (c : 𝒪[K]) :
    P.integerHom (algebraMap 𝒪[K] _ c) = P.coeffHom (P.integerRingEquiv c) := by
  rw [integerHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    algebraMap_completion_weightedRestrictedSubring_apply, completionIntegerEquiv,
    weightedMapCompletionEquiv_coe_weightedC,
    ← algebraMap_completion_weightedRestrictedSubring_apply, P.hom_algebraMap]

private theorem coe_integerHom_algebraMap (P : IntegralAffinoidPresentation K A V A₀) (c : 𝒪[K]) :
    (P.integerHom (algebraMap 𝒪[K] _ c) : A) = algebraMap K A c := by
  rw [P.integerHom_algebraMap, P.coe_coeffHom]
  rfl

/-- **Kiehl's almost noetherianity theorem for an integral affinoid presentation.** Over a
complete nontrivially normed ultrametric field `K`, for any finitely generated `A₀`-module `M`, any
`A₀`-submodule `N ≤ M`, and any `0 < ε < 1`, there exists a finitely generated `A₀`-submodule
`N' ≤ N` containing `P.coeffHom c • x` for all `c : V` with `‖(c : K)‖ ≤ ε` and all `x ∈ N`. -/
theorem almost_noetherian [CompleteSpace K] (P : IntegralAffinoidPresentation K A V A₀)
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : V, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, P.coeffHom c • x ∈ N' := by
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    P.integerHom.exists_fg_le_forall_smul_mem_of_surjective_restrictedMvPowerSeriesCompletion
      P.integerHom_surjective N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  let c₀ : 𝒪[K] := P.integerRingEquiv.symm c
  have hc₀ : ‖(c₀ : K)‖ ≤ ε := by simpa [c₀, integerRingEquiv] using hc
  have heq : P.integerHom (algebraMap 𝒪[K] _ c₀) = P.coeffHom c := by
    rw [P.integerHom_algebraMap, RingEquiv.apply_symm_apply]
  exact heq ▸ hsmul c₀ hc₀ x hx

/-- **Noetherianity over a discrete valuation ring.** When `V` is a discrete valuation ring, the
presented open bounded subring `A₀` is noetherian (without assuming completeness of `K`). -/
theorem isNoetherianRing_subring (P : IntegralAffinoidPresentation K A V A₀)
    [IsDiscreteValuationRing V] : IsNoetherianRing A₀ := by
  have : IsNoetherianRing 𝒪[K] := isNoetherianRing_of_ringEquiv V P.integerRingEquiv.symm
  have : IsNoetherianRing (restrictedMvPowerSeriesCompletion P.numVars 𝒪[K]) :=
    (IsStronglyNoetherian.integer (K := K)).isNoetherianRing P.numVars
  have : IsNoetherianRing (restrictedMvPowerSeriesCompletion P.numVars V) :=
    isNoetherianRing_of_ringEquiv _ P.completionIntegerEquiv
  exact isNoetherianRing_of_surjective _ _ P.hom P.surjective_hom

/-- **Finite generation over a discrete valuation ring.** When `V` is a discrete valuation ring,
every submodule `N` of a finitely generated `A₀`-module `M` is finitely generated (without assuming
completeness of `K`). -/
theorem fg_of_discrete (P : IntegralAffinoidPresentation K A V A₀) [IsDiscreteValuationRing V]
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) : N.FG := by
  have := P.isNoetherianRing_subring
  exact IsNoetherian.noetherian N

section TateExtension

variable [CompleteSpace K] [SeparatelyContinuousMul A]

/-- Existence of the surjective Tate extension of `P`, via
`TauCeti.Huber.exists_surjective_algHom_map_unitClosedBall_eq`. -/
private theorem exists_tateHom_spec (P : IntegralAffinoidPresentation K A V A₀) :
    ∃ π : IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1) →ₐ[K] A,
      Function.Surjective π ∧
      (∀ f : Subring.unitClosedBall
          (IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1)),
        π f = P.integerHom ((restrictedMvPowerSeriesCompletionIntegerEquiv P.numVars).symm f)) ∧
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1))).map π.toRingHom = A₀ :=
  Huber.exists_surjective_algHom_map_unitClosedBall_eq P.continuousAt_algebraMap P.isOpen_subring
    P.integerHom P.integerHom_surjective P.coe_integerHom_algebraMap

/-- **Tate extension of an integral affinoid presentation.** Over a complete nontrivially normed
ultrametric field `K`, for a topological `K`-algebra `A` with separately continuous multiplication,
`P.hom` extends to a surjective `K`-algebra homomorphism `K⟨X₁, …, Xₙ⟩ →ₐ[K] A` mapping the Gauss
unit ball onto `A₀`. -/
noncomputable def tateHom (P : IntegralAffinoidPresentation K A V A₀) :
    IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1) →ₐ[K] A :=
  P.exists_tateHom_spec.choose

/-- `P.tateHom` is surjective onto `A`. -/
theorem surjective_tateHom (P : IntegralAffinoidPresentation K A V A₀) :
    Function.Surjective P.tateHom :=
  P.exists_tateHom_spec.choose_spec.1

/-- The Gauss unit ball of `K⟨X₁, …, Xₙ⟩` maps under `P.tateHom` onto the presented open bounded
subring `A₀`. -/
theorem map_unitClosedBall_tateHom (P : IntegralAffinoidPresentation K A V A₀) :
    (Subring.unitClosedBall
      (IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1))).map P.tateHom.toRingHom =
      A₀ :=
  P.exists_tateHom_spec.choose_spec.2.2

/-- An integral affinoid presentation witnesses that `A` is an affinoid `K`-algebra. -/
theorem isAffinoidAlgebra (P : IntegralAffinoidPresentation K A V A₀) : IsAffinoidAlgebra K A :=
  (isAffinoidAlgebra_iff K A).mpr ⟨P.numVars, P.tateHom, P.surjective_tateHom⟩

/-- Existential formulation of `P.tateHom`, `P.surjective_tateHom`, and
`P.map_unitClosedBall_tateHom`. -/
theorem exists_surjective_algHom_map_unitClosedBall_eq
    (P : IntegralAffinoidPresentation K A V A₀) :
    ∃ π : IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1) →ₐ[K] A,
      Function.Surjective π ∧
      (Subring.unitClosedBall
        (IsRestricted.subring (R := K) (fun _ : Fin P.numVars ↦ 1))).map π.toRingHom = A₀ :=
  ⟨P.tateHom, P.surjective_tateHom, P.map_unitClosedBall_tateHom⟩

end TateExtension

end Basic

section Checks

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Field check (`A = K`).** Over a complete nontrivially normed ultrametric field `K`, the
closed unit ball `K°` admits a canonical zero-variable continuous integral affinoid presentation
over `K` itself. -/
noncomputable def testField [CompleteSpace K] :
    IntegralAffinoidPresentation K K (Subring.unitClosedBall K) (Subring.unitClosedBall K) :=
  let eV : Subring.unitClosedBall K ≃+* 𝒪[K] := integerUnitClosedBallEquiv.symm
  let eC : restrictedMvPowerSeriesCompletion 0 (Subring.unitClosedBall K) ≃+*
      restrictedMvPowerSeriesCompletion 0 𝒪[K] :=
    weightedMapCompletionEquiv eV continuous_integerUnitClosedBallEquiv_symm
      continuous_integerUnitClosedBallEquiv isWeightFamily_one_weight isWeightFamily_one_weight
      (fun _ ↦ by simp [Set.image_singleton]) (fun _ ↦ by simp [Set.image_singleton])
  let eI : restrictedMvPowerSeriesCompletion 0 𝒪[K] ≃+*
      Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1)) :=
    restrictedMvPowerSeriesCompletionIntegerEquiv 0
  let r : Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1)) →+*
      Subring.unitClosedBall K :=
    unitClosedBallConstantCoeffHom
  { unitClosedBall_eq := rfl
    numVars := 0
    coeffHom := RingHom.id _
    coe_coeffHom := fun _ ↦ rfl
    hom := r.comp (eI.toRingHom.comp eC.toRingHom)
    continuous_hom := by
      have hr : Continuous r :=
        AddMonoidHomClass.continuous_of_bound r 1 fun f ↦ by
          simpa only [r, one_mul, AddSubgroupClass.coe_norm,
            coe_unitClosedBallConstantCoeffHom] using
            norm_constantCoeff_le (f : IsRestricted.subring (R := K) (fun _ : Fin 0 ↦ 1))
      exact hr.comp ((continuous_restrictedMvPowerSeriesCompletionIntegerEquiv 0).comp
        (continuous_weightedMapCompletionEquiv eV continuous_integerUnitClosedBallEquiv_symm
          continuous_integerUnitClosedBallEquiv isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ by simp [Set.image_singleton]) (fun _ ↦ by simp [Set.image_singleton])))
    surjective_hom := fun c ↦
      ⟨eC.symm (eI.symm (unitClosedBallCoeffHom c)), by
        simp [r, unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom]⟩
    hom_algebraMap := fun c ↦ by
      have heC : eC (algebraMap (Subring.unitClosedBall K) _ c) = algebraMap 𝒪[K] _ (eV c) := by
        rw [algebraMap_completion_weightedRestrictedSubring_apply,
          algebraMap_completion_weightedRestrictedSubring_apply]
        exact weightedMapCompletionEquiv_coe_weightedC eV
          continuous_integerUnitClosedBallEquiv_symm continuous_integerUnitClosedBallEquiv
          isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ by simp [Set.image_singleton]) (fun _ ↦ by simp [Set.image_singleton]) c
      dsimp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [heC]
      dsimp only [eI, r]
      rw [restrictedMvPowerSeriesCompletionIntegerEquiv_algebraMap,
        unitClosedBallConstantCoeffHom_unitClosedBallCoeffHom]
      exact integerUnitClosedBallEquiv.apply_symm_apply c
    isOpen_subring := Subring.isOpen_unitClosedBall K
    isBounded_subring := Subring.coe_unitClosedBall K ▸ isBounded_closedBall_zero 1 }

/-- **Zero-variable check.** Any continuous integral affinoid presentation with zero variables
has open bounded subring `A₀` equal to the image of `K°` under `algebraMap K A`. -/
theorem test_zero [CompleteSpace K]
    {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    {V : Subring K} {A₀ : Subring A}
    (P : IntegralAffinoidPresentation K A V A₀) (h0 : P.numVars = 0) :
    A₀ = (Subring.unitClosedBall K).map (algebraMap K A) := by
  have : _root_.IsEmpty (Fin P.numVars) := ⟨fun i ↦ Fin.elim0 (Fin.cast h0 i)⟩
  rw [← P.map_unitClosedBall_tateHom, AlgHom.toRingHom_eq_coe,
    P.tateHom.map_unitClosedBall_of_isEmpty]

/-- **Unboundedness check.** `(⊤ : Subring K)` cannot admit a continuous integral affinoid
presentation over `K`, since a nontrivially normed field is not bounded in its own topology. -/
theorem test_unbounded (V : Subring K) :
    _root_.IsEmpty (IntegralAffinoidPresentation K K V ⊤) :=
  ⟨fun P ↦ not_isBounded_univ_of_nontriviallyNormedField K (by simpa using P.isBounded_subring)⟩

end Checks

end Huber.IntegralAffinoidPresentation

end IntegralPresentation

end TauCeti
