/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.RingTheory.Huber.CompleteRankOneBase.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.FinitePresentation
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Module

import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Analysis.Normed.Module.StrictGenerators
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Huber.CompleteRankOneBase.FractionRing
import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.RingTheory.Huber.Restricted.GaussNorm
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Submodule
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Saturated submodules, Artin–Rees, and adhesiveness over complete rank-one bases

Let `O` be a valuation domain carrying `TauCeti.Huber.IsCompleteRankOneBase O ϖ` with
pseudouniformiser `ϖ`. Even when `O` is non-noetherian (such as `𝒪_{ℂ_p}`), its valued fraction
field `K = O[1/ϖ]` is a complete nonarchimedean field of rank one, and the completed restricted
power-series algebra `P = O⟨ξ₁, …, ξₙ⟩` is isomorphic to the closed Gauss unit ball of the
noetherian Tate algebra `T = K⟨ξ₁, …, ξₙ⟩`, with `T ≅ P[1/ϖ]`.

Every submodule of a finite free `T`-module `ι → T` admits a finite set of norm-one strict
generators (`Submodule.exists_finset_norm_eq_one_isRestricted_subring`). Clearing denominators of
those generators by a single power `ϖ ^ k` yields a simultaneous uniform approximation lemma for
arbitrary `P`-submodules of `ι → P`, from which all module-theoretic finiteness and topological
properties of algebras presented over `O⟨ξ₁, …, ξₙ⟩` follow (Bosch–Lütkebohmert I, §1,
Proposition 1.1(c), Lemma 1.2, and Corollary 1.4; Fujiwara–Kato, Ch. 0, §8.5, Proposition 8.5.3):

* **Noetherian generic fibre**: for any quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, the localisation
  `A[1/ϖ]` (`Localization.Away (algebraMap O A ϖ)`) is noetherian
  (`TauCeti.Huber.isNoetherianRing_localization_away_of_surjective`).
* **Artin–Rees, subspace topology, and strictness**: for any finite `A`-module `E` and any
  `A`-submodule `M ≤ E` (not necessarily finitely generated or saturated), there exists `k : ℕ`
  such that `M ⊓ ((ϖ) ^ (m + k) • ⊤) ≤ (ϖ) ^ m • M` for all `m : ℕ`
  (`TauCeti.Huber.exists_inf_pow_smul_le_of_surjective`). Consequently the `ϖ`-adic topology on `M`
  coincides with the subspace topology induced from `E`
  (`TauCeti.Huber.isEmbedding_subtype_adicModuleTopology_of_surjective`), and every `A`-linear map
  into `E` is strict for the `ϖ`-adic module topologies
  (`TauCeti.Huber.isStrictMap_adicModuleTopology_of_surjective`).
* **Finite generation of `ϖ`-saturated submodules**: every `ϖ`-saturated `A`-submodule `M` of a
  finite `A`-module `E` (including any finite free `A`-module) — that is, `M` satisfying
  `∀ x : E, ϖ • x ∈ M → x ∈ M`, equivalently `E ⧸ M` having no `ϖ`-torsion — is finitely generated
  (`TauCeti.Huber.fg_of_forall_smul_mem_of_surjective`).
* **Adhesiveness (`ϖ`-power torsion and finite presentation)**: for every finite `A`-module `E`,
  the `ϖ`-primary torsion submodule `Ideal.primaryComponent E (Ideal.span {algebraMap O A ϖ})` is
  `ϖ`-saturated, hence finitely generated (`TauCeti.Huber.fg_primaryComponent_of_surjective`) and
  annihilated by a single power of `ϖ`
  (`TauCeti.Huber.exists_pow_smul_eq_zero_primaryComponent_of_surjective`). Every finite `A`-module
  without `ϖ`-torsion is finitely presented over `A`
  (`TauCeti.Huber.finitePresentation_of_torsionBy_eq_bot_of_surjective`), and for an arbitrary
  finite `A`-module `E` the torsion-free quotient `E ⧸ E[ϖ^∞]` is finitely presented
  (`TauCeti.Huber.finitePresentation_quotient_primaryComponent_of_surjective`).
* **Adic completeness and closedness**: every finite `A`-module is `ϖ`-adically precomplete
  (`TauCeti.Huber.isPrecomplete_module_of_surjective`). Inside a `ϖ`-adically separated finite
  `A`-module `E` (for instance a finite free module over a separated `A`), every finitely generated
  submodule `M` is `ϖ`-adically complete and closed in `E`, and `E ⧸ M` is `ϖ`-adically complete
  (`TauCeti.Huber.isClosed_adicModuleTopology_of_fg_of_surjective`,
  `TauCeti.Huber.isAdicComplete_quotient_of_fg_of_surjective`). In particular, every algebra `A`
  topologically of finite presentation over `O` is automatically `ϖ`-adically separated and
  complete (`TauCeti.Huber.IsTopologicallyFinitePresentation.isAdicComplete`), as is every finitely
  presented `A`-module
  (`TauCeti.Huber.IsTopologicallyFinitePresentation.isAdicComplete_of_finitePresentation`).

The core theorems take a surjective `O`-algebra homomorphism `π : O⟨ξ₁, …, ξₙ⟩ →ₐ[O] A` and
require no topology on `A`; specializations are provided both for
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType` and for
`TauCeti.Huber.IsTopologicallyFinitePresentation`.

## References

* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*, Math. Ann. 295
  (1993), §1, Proposition 1.1(c), Lemma 1.2, and Corollary 1.4.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Math. 2105, Springer, 2014,
  §7.3, Corollary 6, Lemma 7, and Proposition 8.
* K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, Ch. 0, §8.5, Proposition 8.5.3.
-/

public section

namespace TauCeti.Huber

/-! ### Unit-ball comparison and generic-fibre noetherianity -/

section UnitBallAndGenericFibre

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [ValuationRing O] [TopologicalSpace O]
  [NonarchimedeanRing O] (ϖ : O) [IsCompleteRankOneBase O ϖ]

/-- The valued fraction field `WithVal (ValuationRing.valuation O (FractionRing O))` used internally
to realise `O⟨ξ₁, …, ξₙ⟩` as the closed Gauss unit ball of a Tate algebra. -/
private abbrev ValuedFractionField (O : Type u) [CommRing O] [IsDomain O] [ValuationRing O] :
    Type u :=
  WithVal (ValuationRing.valuation O (FractionRing O))

omit [NonarchimedeanRing O] in
include ϖ in
/-- Identify `O` as a topological ring with the `NormedField.valuation` integer subring of
`ValuedFractionField O`. -/
private theorem exists_normedIntegerEquiv
    [(Valued.v (R := ValuedFractionField O)).RankOne] :
    open scoped Valued in
    ∃ e₀ : O ≃+* (NormedField.valuation (K := ValuedFractionField O)).integer,
      Continuous e₀ ∧ Continuous e₀.symm ∧
      CompleteSpace (NormedField.valuation (K := ValuedFractionField O)).integer ∧
      ∀ a : O, ((e₀ a : (NormedField.valuation (K := ValuedFractionField O)).integer) :
        ValuedFractionField O) = algebraMap O (ValuedFractionField O) a := by
  open scoped Valued in
  have : CompleteSpace (ValuedFractionField O) :=
    IsCompleteRankOneBase.completeSpace_withVal ϖ (FractionRing O)
  open scoped Valued in
  let OK : Subring (ValuedFractionField O) :=
    (NormedField.valuation (K := ValuedFractionField O)).integer
  open scoped Valued in
  have hOK : (Valued.v : Valuation (ValuedFractionField O) _).integer = OK :=
    Subring.ext fun x ↦ by
      rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, NormedField.valuation_apply,
        ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, Valued.toNormedField.norm_le_one_iff]
  open scoped Valued in
  have hcomp : CompleteSpace OK :=
    hOK ▸ (inferInstance : CompleteSpace (Valued.v : Valuation (ValuedFractionField O) _).integer)
  open scoped Valued in
  let e₀ : O ≃+* OK :=
    (IsCompleteRankOneBase.equivIntegerWithVal O (FractionRing O)).trans
      (RingEquiv.subringCongr hOK)
  open scoped Valued in
  refine ⟨e₀, (Continuous.subtype_mk continuous_subtypeVal _).comp
      (IsCompleteRankOneBase.continuous_equivIntegerWithVal ϖ _),
    (IsCompleteRankOneBase.continuous_equivIntegerWithVal_symm ϖ _).comp
      (Continuous.subtype_mk continuous_subtypeVal _),
    hcomp, fun a ↦ by simp [e₀]⟩

include ϖ in
/-- Identify `O⟨ξ₁, …, ξₙ⟩` with the closed Gauss unit ball of the Tate algebra over
`ValuedFractionField O`, matching `algebraMap` on constants. -/
private theorem exists_unitClosedBallEquiv (n : ℕ)
    [(Valued.v (R := ValuedFractionField O)).RankOne] :
    open scoped Valued in
    ∃ e : restrictedMvPowerSeriesCompletion n O ≃+*
        Subring.unitClosedBall
          (MvPowerSeries.IsRestricted.subring (R := ValuedFractionField O) (fun _ : Fin n ↦ 1)),
      ∀ a : O,
        ((e (algebraMap O _ a) :
          Subring.unitClosedBall
            (MvPowerSeries.IsRestricted.subring (R := ValuedFractionField O)
              (fun _ : Fin n ↦ 1))) :
          MvPowerSeries.IsRestricted.subring (R := ValuedFractionField O) (fun _ : Fin n ↦ 1)) =
        algebraMap (ValuedFractionField O) _ (algebraMap O (ValuedFractionField O) a) := by
  open scoped Valued in
  have : CompleteSpace (ValuedFractionField O) :=
    IsCompleteRankOneBase.completeSpace_withVal ϖ (FractionRing O)
  open scoped Valued in
  let OK : Subring (ValuedFractionField O) :=
    (NormedField.valuation (K := ValuedFractionField O)).integer
  open scoped Valued in
  obtain ⟨e₀, he₀, he₀_symm, hcomp, he₀_coe⟩ := exists_normedIntegerEquiv ϖ
  open scoped Valued in
  have : CompleteSpace OK := hcomp
  open scoped Valued in
  set e₁ : restrictedMvPowerSeriesCompletion n O ≃+* restrictedMvPowerSeriesCompletion n OK :=
    weightedMapCompletionEquiv e₀ he₀ he₀_symm isWeightFamily_one_weight isWeightFamily_one_weight
      (fun _ ↦ by simp) (fun _ ↦ by simp) with he₁_def
  open scoped Valued in
  set e₂ : restrictedMvPowerSeriesCompletion n OK ≃+*
      MvPowerSeries.IsRestricted.subring (R := OK) (fun _ : Fin n ↦ 1) :=
    restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := OK) with he₂_def
  open scoped Valued in
  refine ⟨(e₁.trans e₂).trans
    (TauCeti.MvPowerSeries.restrictedIntegerEquiv (σ := Fin n) (K := ValuedFractionField O)),
    fun a ↦ ?_⟩
  open scoped Valued in
  have he₁₂ : e₂ (e₁ (algebraMap O (restrictedMvPowerSeriesCompletion n O) a)) =
      algebraMap OK _ (e₀ a) := by
    rw [algebraMap_completion_weightedRestrictedSubring_apply, he₁_def,
      weightedMapCompletionEquiv_apply, weightedMapCompletion_coe (φ := (e₀ : O →+* OK)) he₀,
      weightedMap_weightedC (φ := (e₀ : O →+* OK)) he₀, he₂_def,
      restrictedMvPowerSeriesCompletionGaussEquiv_coe, restrictedMvPowerSeriesGaussEquiv_weightedC,
      RingEquiv.coe_toRingHom]
  open scoped Valued in
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, he₁₂]
  apply Subtype.ext; ext ν
  rw [TauCeti.MvPowerSeries.coeff_restrictedIntegerEquiv,
    MvPowerSeries.coe_algebraMap_isRestrictedSubring,
    MvPowerSeries.coe_algebraMap_isRestrictedSubring, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs <;> [exact he₀_coe a; rfl]

/-- Core bridge from `P = O⟨ξ₁, …, ξₙ⟩` into a noetherian normed `P`-algebra `T` (the Gauss-normed
Tate algebra over `ValuedFractionField O`): `algebraMap P T` is injective with range the closed unit
ball of `T`, realising `T` as `P[1/ϖ]`, together with strict norm-one generation for submodules of
finite free `T`-modules. Packaging this avoids leaking the non-canonical `Valuation.RankOne` choice
outside private proofs. -/
private theorem exists_tate_bridge (n : ℕ) :
    ∃ (T : Type u) (_ : NormedCommRing T) (_ : IsUltrametricDist T) (_ : IsNoetherianRing T)
      (_ : Algebra (restrictedMvPowerSeriesCompletion n O) T),
      Function.Injective (algebraMap (restrictedMvPowerSeriesCompletion n O) T) ∧
      (∀ f : T, f ∈ Set.range (algebraMap (restrictedMvPowerSeriesCompletion n O) T) ↔ ‖f‖ ≤ 1) ∧
      IsLocalization.Away (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ) T ∧
      (∀ {ι : Type} [Fintype ι] (N : Submodule T (ι → T)),
        ∃ F : Finset (ι → T), (∀ x ∈ F, x ∈ N ∧ ‖x‖ = 1) ∧
          ∀ y ∈ N, ∃ a : (ι → T) → T, y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ ≤ ‖y‖) := by
  let _ : (Valued.v (R := ValuedFractionField O)).RankOne :=
    Classical.choice (IsCompleteRankOneBase.nonempty_rankOne_withVal ϖ (FractionRing O))
  open scoped Valued in
  have : CompleteSpace (ValuedFractionField O) :=
    IsCompleteRankOneBase.completeSpace_withVal ϖ (FractionRing O)
  open scoped Valued in
  obtain ⟨e, he_alg⟩ := exists_unitClosedBallEquiv ϖ n
  open scoped Valued in
  set T := MvPowerSeries.IsRestricted.subring (R := ValuedFractionField O) (fun _ : Fin n ↦ 1)
  open scoped Valued in
  let _ : Algebra (restrictedMvPowerSeriesCompletion n O) T :=
    ((Subring.unitClosedBall T).subtype.comp e.toRingHom).toAlgebra
  open scoped Valued in
  have halg (p : restrictedMvPowerSeriesCompletion n O) :
      algebraMap (restrictedMvPowerSeriesCompletion n O) T p = (e p : T) := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Subring.coe_subtype,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  open scoped Valued in
  have hj_inj : Function.Injective (algebraMap (restrictedMvPowerSeriesCompletion n O) T) :=
    Subtype.val_injective.comp e.injective
  open scoped Valued in
  have hj_range (f : T) :
      f ∈ Set.range (algebraMap (restrictedMvPowerSeriesCompletion n O) T) ↔ ‖f‖ ≤ 1 := by
    rw [← Subring.mem_unitClosedBall]
    refine ⟨by rintro ⟨p, rfl⟩; rw [halg]; exact (e p).property, fun hf ↦ ⟨e.symm ⟨f, hf⟩, ?_⟩⟩
    rw [halg, RingEquiv.apply_symm_apply]
  open scoped Valued in
  have hϖK : algebraMap O (ValuedFractionField O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (WithVal.algebraMap_right_injective _
      (IsFractionRing.injective O (FractionRing O)))).mpr (IsCompleteRankOneBase.ne_zero (ϖ := ϖ))
  open scoped Valued in
  have hjϖ_unit : IsUnit ((e (algebraMap O _ ϖ) : Subring.unitClosedBall T) : T) := by
    rw [he_alg]
    exact (IsUnit.mk0 _ hϖK).map (algebraMap (ValuedFractionField O) T)
  open scoped Valued in
  have hϖT1 : ‖((e (algebraMap O _ ϖ) : Subring.unitClosedBall T) : T)‖ < 1 := by
    rw [he_alg, MvPowerSeries.norm_algebraMap_isRestrictedSubring,
      Valued.toNormedField.norm_lt_one_iff]
    refine lt_of_le_of_ne ((ValuationRing.integers O (FractionRing O)).map_le_one ϖ) fun h1 ↦
      IsCompleteRankOneBase.not_isUnit (O := O) (ϖ := ϖ)
        ((ValuationRing.integers O (FractionRing O)).isUnit_of_one
          (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _
            (IsFractionRing.injective O (FractionRing O))).mpr
              (IsCompleteRankOneBase.ne_zero (ϖ := ϖ)))) h1)
  open scoped Valued in
  have : IsLocalization.Away (e (algebraMap O _ ϖ)) T :=
    (Subring.unitClosedBall T).isLocalizationAway_of_isOpen (Subring.isOpen_unitClosedBall T)
      (e (algebraMap O _ ϖ))
      (TauCeti.MvPowerSeries.isTopologicallyNilpotent_iff_norm_lt_one.mpr hϖT1) hjϖ_unit
  open scoped Valued in
  have hloc : IsLocalization.Away (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ) T :=
    IsLocalization.of_ringEquiv_left e (Submonoid.map_powers e _) halg
  open scoped Valued in
  exact ⟨T, inferInstance, inferInstance,
    TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring
      (K := ValuedFractionField O) (c := fun _ : Fin n ↦ 1),
    inferInstance, hj_inj, hj_range, hloc,
    fun N ↦ N.exists_finset_norm_eq_one_isRestricted_subring⟩

include ϖ in
/-- Over a complete rank-one valuation base `O` with pseudouniformiser `ϖ`, the generic fibre
`O⟨ξ₁, …, ξₙ⟩[1/ϖ]` is a noetherian ring. -/
theorem isNoetherianRing_localization_away_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsNoetherianRing (Localization.Away
      (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ)) := by
  obtain ⟨T, _, _, _, _, _, _, hloc, _⟩ := exists_tate_bridge ϖ n
  have : IsLocalization.Away (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ) T := hloc
  exact isNoetherianRing_of_ringEquiv T
    (IsLocalization.algEquiv
      (Submonoid.powers (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ)) T
      (Localization.Away (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ))).toRingEquiv

include ϖ in
/-- For any `O`-algebra `A` receiving a surjective `O`-algebra homomorphism from
`O⟨ξ₁, …, ξₙ⟩`, the generic fibre `A[1/ϖ]` is noetherian. -/
theorem isNoetherianRing_localization_away_of_surjective {A : Type*} [CommRing A] [Algebra O A]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π) :
    IsNoetherianRing (Localization.Away (algebraMap O A ϖ)) := by
  have := isNoetherianRing_localization_away_restrictedMvPowerSeriesCompletion ϖ n
  have : IsLocalization.Away (π (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ))
      (Localization.Away (algebraMap O A ϖ)) := by
    rw [π.commutes ϖ]
    infer_instance
  exact isNoetherianRing_of_surjective _ _
    (IsLocalization.Away.mapₐ
      (Localization.Away (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ))
      (Localization.Away (algebraMap O A ϖ)) π
      (algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ)).toRingHom
    (IsLocalization.Away.mapₐ_surjective_of_surjective _ hπ)

include ϖ in
/-- If `A` is strictly topologically of finite type over a complete rank-one valuation base `O`,
its generic fibre `A[1/ϖ]` is noetherian. -/
theorem IsStrictlyTopologicallyFiniteType.isNoetherianRing_localization_away
    {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra O A]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap O A)) :
    IsNoetherianRing (Localization.Away (algebraMap O A ϖ)) := by
  obtain ⟨n, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact isNoetherianRing_localization_away_of_surjective ϖ
    (π := { π with commutes' := RingHom.congr_fun hcomm }) hπ.surjective

include ϖ in
/-- If `A` is topologically of finite presentation over a complete rank-one valuation base `O`,
its generic fibre `A[1/ϖ]` is noetherian. -/
theorem IsTopologicallyFinitePresentation.isNoetherianRing_localization_away
    {A : Type*} [CommRing A] [Algebra O A] (h : IsTopologicallyFinitePresentation O A) :
    IsNoetherianRing (Localization.Away (algebraMap O A ϖ)) := by
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact isNoetherianRing_localization_away_of_surjective ϖ hπ

/-! ### Uniform approximation in finite free modules over `O⟨ξ₁, …, ξₙ⟩` -/

include ϖ in
/-- **Simultaneous integral generator lemma over `O⟨ξ₁, …, ξₙ⟩`.** Let `P = O⟨ξ₁, …, ξₙ⟩` and
`ι` be a finite index type. For ANY `P`-submodule `M` of `ι → P` (not assumed saturated or
finitely generated), there exist a finite set `G ⊆ ι → P` and `k : ℕ` such that:
1. `(ϖ ^ k) • g ∈ M` for every `g ∈ G`, and
2. every `v : ι → P` with `(ϖ ^ r) • v ∈ M` for some `r : ℕ` is a `P`-linear combination of `G`. -/
private theorem exists_finset_pow_smul_mem_and_eq_sum {n : ℕ} {ι : Type} [Finite ι]
    (M : Submodule (restrictedMvPowerSeriesCompletion n O)
      (ι → restrictedMvPowerSeriesCompletion n O)) :
    ∃ (G : Finset (ι → restrictedMvPowerSeriesCompletion n O)) (k : ℕ),
      (∀ g ∈ G, (ϖ ^ k) • g ∈ M) ∧
      ∀ (r : ℕ) (v : ι → restrictedMvPowerSeriesCompletion n O),
        (ϖ ^ r) • v ∈ M →
          ∃ p : (ι → restrictedMvPowerSeriesCompletion n O) →
            restrictedMvPowerSeriesCompletion n O, v = ∑ g ∈ G, p g • g := by
  let _ := Fintype.ofFinite ι
  set P := restrictedMvPowerSeriesCompletion n O
  obtain ⟨T, _, _, _, _, hj_inj, hj_range, _, hstrict⟩ := exists_tate_bridge ϖ n
  let J : (ι → P) →ₗ[P] (ι → T) :=
    { toFun u i := algebraMap P T (u i)
      map_add' _ _ := funext fun _ ↦ map_add (algebraMap P T) _ _
      map_smul' _ _ := funext fun _ ↦ by simp [Algebra.smul_def] }
  have hJ_inj : Function.Injective J := fun _ _ h ↦ funext fun i ↦ hj_inj (congrFun h i)
  have hJ_range (w : ι → T) : w ∈ Set.range J ↔ ‖w‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    refine ⟨by rintro ⟨u, rfl⟩ i; exact (hj_range (algebraMap P T (u i))).mp ⟨u i, rfl⟩,
      fun hw ↦ ?_⟩
    choose u hu using fun i ↦ (hj_range (w i)).mpr (hw i)
    exact ⟨u, funext hu⟩
  let N : Submodule T (ι → T) := Submodule.span T (J '' (M : Set (ι → P)))
  have hN : ∃ F : Finset (ι → T), (∀ x ∈ F, x ∈ N ∧ ‖x‖ ≤ 1) ∧
      ∀ y ∈ N, ∃ a : (ι → T) → T, y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ ≤ ‖y‖ := by
    obtain ⟨F, hF1, hFgen⟩ := hstrict N
    exact ⟨F, fun x hx ↦ ⟨(hF1 x hx).1, (hF1 x hx).2.le⟩, hFgen⟩
  obtain ⟨G, hGN, hGsum⟩ := N.exists_finset_subset_preimage_and_eq_sum_smul hJ_inj
    (fun a ha ↦ (hj_range a).mpr ha) hJ_range hN
  have hG_clear (g : G) : ∃ s : ℕ, (ϖ ^ s) • g.val ∈ M := by
    obtain ⟨a, ha, hs⟩ :=
      (J.apply_mem_span_image_iff_exists_smul_mem_span hJ_inj
        (Submonoid.powers (algebraMap O P ϖ))).mp (hGN g.val g.property)
    obtain ⟨s, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ha
    rw [M.span_eq, ← map_pow, algebraMap_smul] at hs
    exact ⟨s, hs⟩
  choose s₀ hs₀ using hG_clear
  let k : ℕ := Finset.univ.sup s₀
  refine ⟨G, k, fun g hg ↦ ?_, fun r v hv ↦ hGsum v ?_⟩
  · have hsplit :
        (ϖ ^ k) • g = algebraMap O P ϖ ^ (k - s₀ ⟨g, hg⟩) • ((ϖ ^ s₀ ⟨g, hg⟩) • g) := by
      rw [← map_pow, algebraMap_smul, ← mul_smul, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ (⟨g, hg⟩ : G)))]
    exact hsplit ▸ M.smul_mem _ (hs₀ ⟨g, hg⟩)
  · refine (J.apply_mem_span_image_iff_exists_smul_mem_span hJ_inj
        (Submonoid.powers (algebraMap O P ϖ))).mpr
      ⟨algebraMap O P ϖ ^ r, (Submonoid.mem_powers_iff _ _).mpr ⟨r, rfl⟩, ?_⟩
    rwa [M.span_eq, ← map_pow, algebraMap_smul]

/-! ### Artin–Rees, subspace `ϖ`-adic topology, and strictness -/

include ϖ in
/-- **Artin–Rees over `O⟨ξ₁, …, ξₙ⟩` on finite products.** Every submodule `M` of `ι → O⟨ξ₁, …, ξₙ⟩`
(`ι` finite) satisfies a uniform Artin–Rees bound for `(ϖ)`. -/
theorem exists_inf_pow_smul_le_pi_restrictedMvPowerSeriesCompletion {n : ℕ} {ι : Type} [Finite ι]
    (M : Submodule (restrictedMvPowerSeriesCompletion n O)
      (ι → restrictedMvPowerSeriesCompletion n O)) :
    ∃ k : ℕ, ∀ m : ℕ,
      M ⊓ (Ideal.span {algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ} ^ (m + k) • ⊤) ≤
        Ideal.span {algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ} ^ m • M := by
  set P := restrictedMvPowerSeriesCompletion n O
  set ϖP := algebraMap O P ϖ
  obtain ⟨G, k, hGk, hGsum⟩ := exists_finset_pow_smul_mem_and_eq_sum ϖ M
  refine ⟨k, fun m u ⟨huM, huPow⟩ ↦ ?_⟩
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, SetLike.mem_coe,
    Submodule.mem_smul_pointwise_iff_exists] at huPow
  obtain ⟨v, -, rfl⟩ := huPow
  have hvM : (ϖ ^ (m + k)) • v ∈ M := by
    rwa [← algebraMap_smul P, map_pow]
  obtain ⟨p, rfl⟩ := hGsum (m + k) v hvM
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun g hg ↦ ?_
  have hterm : ϖP ^ (m + k) • (p g • g) = ϖP ^ m • (p g • ((ϖ ^ k) • g)) := by
    rw [← algebraMap_smul P (ϖ ^ k) g, map_pow, smul_smul, smul_smul, smul_smul,
      pow_add, mul_right_comm (ϖP ^ m) (ϖP ^ k) (p g)]
  rw [hterm]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (M.smul_mem (p g) (hGk g hg))

include ϖ in
/-- **Artin–Rees for submodules of finite modules over quotients of `O⟨ξ₁, …, ξₙ⟩`**
(Bosch–Lütkebohmert I, Lemma 1.2(a); Bosch 2014, §7.3, Lemma 7(ii)). Let `π : O⟨ξ₁, …, ξₙ⟩ →ₐ[O] A`
be surjective and `E` be a finite `A`-module. Every `A`-submodule `M` of `E` (not assumed finitely
generated or saturated) satisfies `M ⊓ ((ϖ) ^ (m + k) • ⊤) ≤ (ϖ) ^ m • M` for some `k : ℕ` and
all `m : ℕ`. -/
theorem exists_inf_pow_smul_le_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π)
    (M : Submodule A E) :
    ∃ k : ℕ, ∀ m : ℕ,
      M ⊓ (Ideal.span {algebraMap O A ϖ} ^ (m + k) • ⊤) ≤
        Ideal.span {algebraMap O A ϖ} ^ m • M := by
  set P := restrictedMvPowerSeriesCompletion n O
  let _ : Algebra P A := π.toRingHom.toAlgebra
  let _ : Module P E := Module.compHom E π.toRingHom
  have : IsScalarTower P A E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite P E :=
    ⟨by simpa only [Submodule.restrictScalars_top] using
      (Module.Finite.fg_top (R := A) (M := E)).restrictScalars_of_surjective hπ⟩
  obtain ⟨r, qP, hqP⟩ := Module.Finite.exists_fin' P E
  set M' : Submodule P (Fin r → P) := (M.restrictScalars P).comap qP with hM'_def
  obtain ⟨k, hk⟩ := exists_inf_pow_smul_le_pi_restrictedMvPowerSeriesCompletion ϖ M'
  refine ⟨k, fun m x ⟨hxM, hxPow⟩ ↦ ?_⟩
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, SetLike.mem_coe,
    Submodule.mem_smul_pointwise_iff_exists] at hxPow
  obtain ⟨y, -, rfl⟩ := hxPow
  obtain ⟨v, rfl⟩ := hqP y
  have hπϖ : π (algebraMap O P ϖ) = algebraMap O A ϖ := π.commutes ϖ
  have hqv : qP (algebraMap O P ϖ ^ (m + k) • v) = algebraMap O A ϖ ^ (m + k) • qP v := by
    rw [map_smul, ← algebraMap_smul A, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_pow, hπϖ]
  have hv_mem : algebraMap O P ϖ ^ (m + k) • v ∈
      M' ⊓ (Ideal.span {algebraMap O P ϖ} ^ (m + k) • ⊤) :=
    Submodule.mem_inf.mpr ⟨by
      rw [hM'_def, Submodule.mem_comap, Submodule.restrictScalars_mem, hqv]; exact hxM, by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩
  have hv_in := hk m hv_mem
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hv_in ⊢
  rw [← hqv]
  rw [Submodule.mem_smul_pointwise_iff_exists] at hv_in
  obtain ⟨w, hwM', hwEq⟩ := hv_in
  rw [← hwEq, map_smul, ← algebraMap_smul A, RingHom.algebraMap_toAlgebra,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, hπϖ]
  rw [hM'_def, Submodule.mem_comap, Submodule.restrictScalars_mem] at hwM'
  exact Submodule.smul_mem_pointwise_smul _ _ _ hwM'

include ϖ in
/-- The `ϖ`-adic topology on any submodule `M` of a finite module `E` over a quotient `A` of
`O⟨ξ₁, …, ξₙ⟩` equals the subspace topology induced from `E` (Bosch–Lütkebohmert I, Lemma 1.2(a)).
-/
theorem isEmbedding_subtype_adicModuleTopology_of_surjective {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A}
    (hπ : Function.Surjective π) (M : Submodule A E) :
    @Topology.IsEmbedding M E
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology M)
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) M.subtype :=
  M.isEmbedding_subtype_adicModuleTopology_of_exists_inf_pow_smul_le _
    (exists_inf_pow_smul_le_of_surjective ϖ hπ M)

include ϖ in
/-- Every `A`-linear map from an arbitrary `A`-module `F` into a finite `A`-module `E` over a
quotient `A` of `O⟨ξ₁, …, ξₙ⟩` is strict for the `ϖ`-adic module topologies. -/
theorem isStrictMap_adicModuleTopology_of_surjective {A F E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup F] [Module A F] [AddCommGroup E] [Module A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A}
    (hπ : Function.Surjective π) (f : F →ₗ[A] E) :
    @Topology.IsStrictMap F E
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology F)
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) f :=
  f.isStrictMap_adicModuleTopology_of_isEmbedding _
    (isEmbedding_subtype_adicModuleTopology_of_surjective ϖ hπ (LinearMap.range f))

include ϖ in
/-- Artin–Rees for submodules of finite modules over an algebra strictly topologically of finite
type over `O`. -/
theorem IsStrictlyTopologicallyFiniteType.exists_inf_pow_smul_le {A E : Type*} [CommRing A]
    [TopologicalSpace A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap O A)) (M : Submodule A E) :
    ∃ k : ℕ, ∀ m : ℕ,
      M ⊓ (Ideal.span {algebraMap O A ϖ} ^ (m + k) • ⊤) ≤
        Ideal.span {algebraMap O A ϖ} ^ m • M := by
  obtain ⟨n, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact exists_inf_pow_smul_le_of_surjective ϖ
    (π := { π with commutes' := RingHom.congr_fun hcomm }) hπ.surjective M

include ϖ in
/-- Subspace `ϖ`-adic topology for submodules of finite modules over an algebra strictly
topologically of finite type over `O`. -/
theorem IsStrictlyTopologicallyFiniteType.isEmbedding_subtype_adicModuleTopology {A E : Type*}
    [CommRing A] [TopologicalSpace A] [Algebra O A] [AddCommGroup E] [Module A E]
    [Module.Finite A E] (h : IsStrictlyTopologicallyFiniteType (algebraMap O A))
    (M : Submodule A E) :
    @Topology.IsEmbedding M E
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology M)
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) M.subtype :=
  M.isEmbedding_subtype_adicModuleTopology_of_exists_inf_pow_smul_le _
    (h.exists_inf_pow_smul_le ϖ M)

include ϖ in
/-- Strictness of linear maps into finite modules over an algebra strictly topologically of finite
type over `O`. -/
theorem IsStrictlyTopologicallyFiniteType.isStrictMap_adicModuleTopology {A F E : Type*}
    [CommRing A] [TopologicalSpace A] [Algebra O A] [AddCommGroup F] [Module A F]
    [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap O A)) (f : F →ₗ[A] E) :
    @Topology.IsStrictMap F E
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology F)
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) f :=
  f.isStrictMap_adicModuleTopology_of_isEmbedding _
    (h.isEmbedding_subtype_adicModuleTopology ϖ (LinearMap.range f))

include ϖ in
/-- Artin–Rees for submodules of finite modules over an algebra topologically of finite
presentation over `O`. -/
theorem IsTopologicallyFinitePresentation.exists_inf_pow_smul_le {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsTopologicallyFinitePresentation O A) (M : Submodule A E) :
    ∃ k : ℕ, ∀ m : ℕ,
      M ⊓ (Ideal.span {algebraMap O A ϖ} ^ (m + k) • ⊤) ≤
        Ideal.span {algebraMap O A ϖ} ^ m • M := by
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact exists_inf_pow_smul_le_of_surjective ϖ hπ M

include ϖ in
/-- Subspace `ϖ`-adic topology for submodules of finite modules over an algebra topologically of
finite presentation over `O`. -/
theorem IsTopologicallyFinitePresentation.isEmbedding_subtype_adicModuleTopology {A E : Type*}
    [CommRing A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsTopologicallyFinitePresentation O A) (M : Submodule A E) :
    @Topology.IsEmbedding M E
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology M)
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) M.subtype :=
  M.isEmbedding_subtype_adicModuleTopology_of_exists_inf_pow_smul_le _
    (h.exists_inf_pow_smul_le ϖ M)

include ϖ in
/-- Strictness of linear maps into finite modules over an algebra topologically of finite
presentation over `O`. -/
theorem IsTopologicallyFinitePresentation.isStrictMap_adicModuleTopology {A F E : Type*}
    [CommRing A] [Algebra O A] [AddCommGroup F] [Module A F] [AddCommGroup E] [Module A E]
    [Module.Finite A E] (h : IsTopologicallyFinitePresentation O A) (f : F →ₗ[A] E) :
    @Topology.IsStrictMap F E
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology F)
      ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) f :=
  f.isStrictMap_adicModuleTopology_of_isEmbedding _
    (h.isEmbedding_subtype_adicModuleTopology ϖ (LinearMap.range f))

/-! ### Finite generation of `ϖ`-saturated submodules and adhesiveness -/

include ϖ in
/-- **Saturated submodules of finite free modules over `O⟨ξ₁, …, ξₙ⟩` are finitely generated.** -/
theorem fg_of_forall_smul_mem_pi_restrictedMvPowerSeriesCompletion {n : ℕ} {ι : Type} [Finite ι]
    {M : Submodule (restrictedMvPowerSeriesCompletion n O)
      (ι → restrictedMvPowerSeriesCompletion n O)}
    (hsat : ∀ u : ι → restrictedMvPowerSeriesCompletion n O, ϖ • u ∈ M → u ∈ M) :
    M.FG := by
  obtain ⟨G, k, hGk, hGsum⟩ := exists_finset_pow_smul_mem_and_eq_sum ϖ M
  have hpow := (M.forall_pow_smul_mem_iff_forall_smul_mem ϖ).mpr hsat
  refine ⟨G, le_antisymm ?_ fun u hu ↦ ?_⟩
  · exact Submodule.span_le.mpr fun g hg ↦ hpow k g (hGk g hg)
  · obtain ⟨p, rfl⟩ := hGsum 0 u (by simpa only [pow_zero, one_smul] using hu)
    exact Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ (p g) (Submodule.subset_span hg)

include ϖ in
/-- **Saturated submodules of finite modules over quotients of `O⟨ξ₁, …, ξₙ⟩` are finitely
generated** (Bosch–Lütkebohmert I, Lemma 1.2(c); Bosch 2014, §7.3, Lemma 7(i)). Let `A` be a
quotient of `O⟨ξ₁, …, ξₙ⟩` and `E` be a finite `A`-module (for instance any finite free
`A`-module). Every `A`-submodule `M ≤ E` satisfying `∀ x : E, ϖ • x ∈ M → x ∈ M` is finitely
generated. -/
theorem fg_of_forall_smul_mem_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module O E] [IsScalarTower O A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π)
    {M : Submodule A E} (hsat : ∀ x : E, ϖ • x ∈ M → x ∈ M) :
    M.FG := by
  set P := restrictedMvPowerSeriesCompletion n O
  let _ : Algebra P A := π.toRingHom.toAlgebra
  let _ : Module P E := Module.compHom E π.toRingHom
  have : IsScalarTower P A E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower O P E := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    rw [← algebraMap_smul A, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, π.commutes, algebraMap_smul]
  have : Module.Finite P E :=
    ⟨by simpa only [Submodule.restrictScalars_top] using
      (Module.Finite.fg_top (R := A) (M := E)).restrictScalars_of_surjective hπ⟩
  obtain ⟨r, qP, hqP⟩ := Module.Finite.exists_fin' P E
  set M' : Submodule P (Fin r → P) := (M.restrictScalars P).comap qP with hM'_def
  have hM'_sat (u : Fin r → P) (hu : ϖ • u ∈ M') : u ∈ M' := by
    rw [hM'_def, Submodule.mem_comap, Submodule.restrictScalars_mem] at hu ⊢
    apply hsat
    rwa [← algebraMap_smul P ϖ u, map_smul, algebraMap_smul] at hu
  have hM' : M'.FG := fg_of_forall_smul_mem_pi_restrictedMvPowerSeriesCompletion ϖ hM'_sat
  exact (Submodule.map_comap_eq_of_surjective hqP (M.restrictScalars P) ▸
    hM'.map qP).of_restrictScalars P

include ϖ in
/-- **Saturated submodules of finite modules over strictly topologically finite type `O`-algebras
are finitely generated** (including all finite free modules). -/
theorem IsStrictlyTopologicallyFiniteType.fg_of_forall_smul_mem {A E : Type*} [CommRing A]
    [TopologicalSpace A] [Algebra O A] [AddCommGroup E] [Module A E] [Module O E]
    [IsScalarTower O A E] [Module.Finite A E]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap O A)) {M : Submodule A E}
    (hsat : ∀ x : E, ϖ • x ∈ M → x ∈ M) :
    M.FG := by
  obtain ⟨n, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact fg_of_forall_smul_mem_of_surjective ϖ
    (π := { π with commutes' := RingHom.congr_fun hcomm }) hπ.surjective hsat

include ϖ in
/-- **Saturated submodules of finite modules over algebras topologically of finite presentation
are finitely generated** (including all finite free modules). -/
theorem IsTopologicallyFinitePresentation.fg_of_forall_smul_mem {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module O E] [IsScalarTower O A E]
    [Module.Finite A E] (h : IsTopologicallyFinitePresentation O A) {M : Submodule A E}
    (hsat : ∀ x : E, ϖ • x ∈ M → x ∈ M) :
    M.FG := by
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact fg_of_forall_smul_mem_of_surjective ϖ hπ hsat

include ϖ in
/-- **Finiteness of `ϖ`-power torsion (adhesiveness).** Over any quotient `A` of `O⟨ξ₁, …, ξₙ⟩`,
the `(ϖ)`-primary torsion submodule `E[ϖ^∞]` of a finite `A`-module `E` is finitely generated
(Bosch–Lütkebohmert I, Lemma 1.2(c); Fujiwara–Kato, Ch. 0, Proposition 8.5.3). -/
theorem fg_primaryComponent_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π) :
    ((Ideal.span {algebraMap O A ϖ}).primaryComponent E).FG := by
  let _ : Module O E := Module.compHom E (algebraMap O A)
  have : IsScalarTower O A E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine fg_of_forall_smul_mem_of_surjective ϖ hπ fun x hx ↦ ?_
  rw [Ideal.mem_primaryComponent_span_singleton_iff] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  refine ⟨m + 1, ?_⟩
  rw [pow_succ, mul_smul, algebraMap_smul A ϖ x]
  exact hm

include ϖ in
/-- **Bounded `ϖ`-power torsion.** Over any quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, the `(ϖ)`-primary
torsion of a finite `A`-module `E` is annihilated by a single power of `ϖ`. -/
theorem exists_pow_smul_eq_zero_primaryComponent_of_surjective {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module O E] [IsScalarTower O A E]
    [Module.Finite A E] {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A}
    (hπ : Function.Surjective π) :
    ∃ k : ℕ, ∀ x ∈ (Ideal.span {algebraMap O A ϖ}).primaryComponent E, (ϖ ^ k) • x = 0 := by
  obtain ⟨k, hk⟩ :=
    (Ideal.span {algebraMap O A ϖ}).exists_le_torsionBySet_pow_of_le_primaryComponent
      (fg_primaryComponent_of_surjective (E := E) ϖ hπ) le_rfl
  refine ⟨k, fun x hx ↦ ?_⟩
  have hmem := (Submodule.mem_torsionBySet_iff _ _).mp (hk hx)
    ⟨algebraMap O A ϖ ^ k, Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k⟩
  simpa only [← map_pow, algebraMap_smul] using hmem

include ϖ in
/-- **Finite `ϖ`-torsion-free modules are finitely presented** (Bosch–Lütkebohmert I, Lemma 1.2(c)).
Over any quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, every finite `A`-module `E` with no `ϖ`-torsion is
finitely presented over `A`. -/
theorem finitePresentation_of_torsionBy_eq_bot_of_surjective {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module O E] [IsScalarTower O A E]
    [Module.Finite A E] {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A}
    (hπ : Function.Surjective π) (htors : Submodule.torsionBy O E ϖ = ⊥) :
    Module.FinitePresentation A E := by
  obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' A E
  refine Module.finitePresentation_of_surjective q hq ?_
  refine fg_of_forall_smul_mem_of_surjective ϖ hπ fun u hu ↦ ?_
  rw [LinearMap.mem_ker] at hu ⊢
  have hqu : q u ∈ Submodule.torsionBy O E ϖ := by
    rw [Submodule.mem_torsionBy_iff, ← algebraMap_smul A, ← map_smul, algebraMap_smul, hu]
  exact (Submodule.mem_bot _).mp (htors ▸ hqu)

include ϖ in
/-- For any finite module `E` over a quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, the quotient of `E` by its
`ϖ`-primary torsion submodule `E[ϖ^∞]` is finitely presented over `A`. -/
theorem finitePresentation_quotient_primaryComponent_of_surjective {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    {n : ℕ} {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π) :
    Module.FinitePresentation A (E ⧸ (Ideal.span {algebraMap O A ϖ}).primaryComponent E) := by
  let _ : Module O E := Module.compHom E (algebraMap O A)
  have : IsScalarTower O A E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  set P₀ := (Ideal.span {algebraMap O A ϖ}).primaryComponent E
  have hprim : (Ideal.span {algebraMap O A ϖ}).primaryComponent (E ⧸ P₀) = ⊥ :=
    Ideal.primaryComponent_quotient_primaryComponent (Submodule.fg_span_singleton _)
  have htors : Submodule.torsionBy O (E ⧸ P₀) ϖ = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    rw [Submodule.mem_torsionBy_iff] at hq
    have hq' : q ∈ (Ideal.span {algebraMap O A ϖ}).primaryComponent (E ⧸ P₀) := by
      rw [Ideal.mem_primaryComponent_span_singleton_iff]
      exact ⟨1, by simpa only [pow_one, algebraMap_smul] using hq⟩
    rwa [hprim] at hq'
  exact finitePresentation_of_torsionBy_eq_bot_of_surjective ϖ hπ htors

include ϖ in
/-- Finiteness of `(ϖ)`-primary torsion over an algebra strictly topologically of finite type. -/
theorem IsStrictlyTopologicallyFiniteType.fg_primaryComponent {A E : Type*} [CommRing A]
    [TopologicalSpace A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap O A)) :
    ((Ideal.span {algebraMap O A ϖ}).primaryComponent E).FG := by
  obtain ⟨n, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact fg_primaryComponent_of_surjective ϖ
    (π := { π with commutes' := RingHom.congr_fun hcomm }) hπ.surjective

include ϖ in
/-- Finiteness of `(ϖ)`-primary torsion over an algebra topologically of finite presentation. -/
theorem IsTopologicallyFinitePresentation.fg_primaryComponent {A E : Type*} [CommRing A]
    [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsTopologicallyFinitePresentation O A) :
    ((Ideal.span {algebraMap O A ϖ}).primaryComponent E).FG := by
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact fg_primaryComponent_of_surjective ϖ hπ

include ϖ in
/-- Finite `ϖ`-torsion-free modules over an algebra strictly topologically of finite type are
finitely presented. -/
theorem IsStrictlyTopologicallyFiniteType.finitePresentation_of_torsionBy_eq_bot {A E : Type*}
    [CommRing A] [TopologicalSpace A] [Algebra O A] [AddCommGroup E] [Module A E] [Module O E]
    [IsScalarTower O A E] [Module.Finite A E]
    (h : IsStrictlyTopologicallyFiniteType (algebraMap O A))
    (htors : Submodule.torsionBy O E ϖ = ⊥) :
    Module.FinitePresentation A E := by
  obtain ⟨n, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact finitePresentation_of_torsionBy_eq_bot_of_surjective ϖ
    (π := { π with commutes' := RingHom.congr_fun hcomm }) hπ.surjective htors

include ϖ in
/-- Finite `ϖ`-torsion-free modules over an algebra topologically of finite presentation are
finitely presented. -/
theorem IsTopologicallyFinitePresentation.finitePresentation_of_torsionBy_eq_bot {A E : Type*}
    [CommRing A] [Algebra O A] [AddCommGroup E] [Module A E] [Module O E] [IsScalarTower O A E]
    [Module.Finite A E] (h : IsTopologicallyFinitePresentation O A)
    (htors : Submodule.torsionBy O E ϖ = ⊥) :
    Module.FinitePresentation A E := by
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact finitePresentation_of_torsionBy_eq_bot_of_surjective ϖ hπ htors

include ϖ in
/-- Over an algebra topologically of finite presentation, the quotient of any finite module by its
`ϖ`-primary torsion is finitely presented. -/
theorem IsTopologicallyFinitePresentation.finitePresentation_quotient_primaryComponent
    {A E : Type*} [CommRing A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (h : IsTopologicallyFinitePresentation O A) :
    Module.FinitePresentation A (E ⧸ (Ideal.span {algebraMap O A ϖ}).primaryComponent E) := by
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact finitePresentation_quotient_primaryComponent_of_surjective ϖ hπ

/-! ### Adic completeness and closedness -/

omit [IsDomain O] [ValuationRing O] in
include ϖ in
/-- The restricted power-series algebra `O⟨ξ₁, …, ξₙ⟩` over a complete rank-one valuation base is
`ϖ`-adically separated and complete. -/
theorem isAdicComplete_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsAdicComplete (Ideal.span {algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ})
      (restrictedMvPowerSeriesCompletion n O) := by
  have hmap : Ideal.span {algebraMap O (restrictedMvPowerSeriesCompletion n O) ϖ} =
      (Ideal.span {ϖ}).map (algebraMap O (restrictedMvPowerSeriesCompletion n O)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hmap]
  exact (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion n
    (IsCompleteRankOneBase.isAdic (O := O) (ϖ := ϖ))
    (Submodule.fg_span_singleton ϖ)).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

omit [IsDomain O] [ValuationRing O] in
include ϖ in
/-- Every quotient `A` of `O⟨ξ₁, …, ξₙ⟩` is `ϖ`-adically precomplete. -/
theorem isPrecomplete_of_surjective {A : Type*} [CommRing A] [Algebra O A] {n : ℕ}
    {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π) :
    IsPrecomplete (Ideal.span {algebraMap O A ϖ}) A := by
  set P := restrictedMvPowerSeriesCompletion n O
  have hc := isAdicComplete_restrictedMvPowerSeriesCompletion ϖ n
  have : IsPrecomplete (Ideal.span {ϖ}) P := by
    have hmap : Ideal.span {algebraMap O P ϖ} = (Ideal.span {ϖ}).map (algebraMap O P) := by
      rw [Ideal.map_span, Set.image_singleton]
    exact IsPrecomplete.map_algebraMap_iff.mp (hmap ▸ hc.toIsPrecomplete)
  have : IsPrecomplete (Ideal.span {ϖ}) A :=
    IsPrecomplete.of_surjective (Ideal.span {ϖ}) π.toLinearMap hπ
  have hmapA : Ideal.span {algebraMap O A ϖ} = (Ideal.span {ϖ}).map (algebraMap O A) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hmapA]
  exact IsPrecomplete.map_algebraMap_iff.mpr inferInstance

omit [IsDomain O] [ValuationRing O] in
include ϖ in
/-- Every finite module `E` over a quotient `A` of `O⟨ξ₁, …, ξₙ⟩` is `ϖ`-adically precomplete. -/
theorem isPrecomplete_module_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module.Finite A E] {n : ℕ}
    {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π) :
    IsPrecomplete (Ideal.span {algebraMap O A ϖ}) E := by
  have := isPrecomplete_of_surjective ϖ hπ
  exact IsPrecomplete.of_finite (Ideal.span {algebraMap O A ϖ}) E

omit [IsDomain O] [ValuationRing O] in
include ϖ in
/-- In a `ϖ`-adically separated module `E` over a quotient `A` of `O⟨ξ₁, …, ξₙ⟩` (for instance a
finite free module over a separated `A`, via `IsHausdorff.of_free`), every finitely generated
submodule `M` is `ϖ`-adically separated and complete. -/
theorem isAdicComplete_submodule_of_fg_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E]
    [IsHausdorff (Ideal.span {algebraMap O A ϖ}) E] {n : ℕ}
    {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π)
    {M : Submodule A E} (hM : M.FG) :
    IsAdicComplete (Ideal.span {algebraMap O A ϖ}) M := by
  have : Module.Finite A M := Module.Finite.iff_fg.mpr hM
  exact { toIsHausdorff := inferInstance
          toIsPrecomplete := isPrecomplete_module_of_surjective ϖ hπ }

include ϖ in
/-- **Finitely generated submodules of separated finite modules are closed** (Bosch–Lütkebohmert I,
Lemma 1.2(b)). In a `ϖ`-adically separated finite module `E` over a quotient `A` of
`O⟨ξ₁, …, ξₙ⟩`, every finitely generated submodule `M` is closed for the `ϖ`-adic module topology
on `E`. -/
theorem isClosed_adicModuleTopology_of_fg_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module.Finite A E]
    [IsHausdorff (Ideal.span {algebraMap O A ϖ}) E] {n : ℕ}
    {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π)
    {M : Submodule A E} (hM : M.FG) :
    @IsClosed E ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) (M : Set E) := by
  have : Module.Finite A M := Module.Finite.iff_fg.mpr hM
  have : IsPrecomplete (Ideal.span {algebraMap O A ϖ}) M :=
    isPrecomplete_module_of_surjective ϖ hπ
  exact M.isClosed_adicModuleTopology_of_exists_inf_pow_smul_le _
    (exists_inf_pow_smul_le_of_surjective ϖ hπ M)

include ϖ in
/-- If `M` is a finitely generated submodule of a `ϖ`-adically separated finite module `E` over a
quotient `A` of `O⟨ξ₁, …, ξₙ⟩`, then `E ⧸ M` is `ϖ`-adically separated and complete. -/
theorem isAdicComplete_quotient_of_fg_of_surjective {A E : Type*} [CommRing A] [Algebra O A]
    [AddCommGroup E] [Module A E] [Module.Finite A E]
    [IsHausdorff (Ideal.span {algebraMap O A ϖ}) E] {n : ℕ}
    {π : restrictedMvPowerSeriesCompletion n O →ₐ[O] A} (hπ : Function.Surjective π)
    {M : Submodule A E} (hM : M.FG) :
    IsAdicComplete (Ideal.span {algebraMap O A ϖ}) (E ⧸ M) where
  toIsHausdorff := M.isHausdorff_quotient_of_isClosed_adicModuleTopology _
    (isClosed_adicModuleTopology_of_fg_of_surjective ϖ hπ hM)
  toIsPrecomplete := isPrecomplete_module_of_surjective ϖ hπ

include ϖ in
/-- **Algebras topologically of finite presentation are `ϖ`-adically separated and complete**
(Bosch–Lütkebohmert I, Proposition 1.1(c)). Because the presentation ideal in `O⟨ξ₁, …, ξₙ⟩` is
finitely generated, it is closed for the `ϖ`-adic topology without assuming `A` separated in
advance. -/
theorem IsTopologicallyFinitePresentation.isAdicComplete {A : Type*} [CommRing A] [Algebra O A]
    (h : IsTopologicallyFinitePresentation O A) :
    IsAdicComplete (Ideal.span {algebraMap O A ϖ}) A := by
  obtain ⟨n, π, hπ, hker⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  set P := restrictedMvPowerSeriesCompletion n O
  have := isAdicComplete_restrictedMvPowerSeriesCompletion ϖ n
  have hQ : IsAdicComplete (Ideal.span {algebraMap O P ϖ}) (P ⧸ RingHom.ker π.toRingHom) :=
    isAdicComplete_quotient_of_fg_of_surjective ϖ (π := AlgHom.id O P) Function.surjective_id hker
  let e : (P ⧸ RingHom.ker π.toRingHom) ≃+* A := RingHom.quotientKerEquivOfSurjective hπ
  have hQ' : IsAdicComplete
      ((Ideal.span {algebraMap O P ϖ}).map (Ideal.Quotient.mk (RingHom.ker π.toRingHom)))
      (P ⧸ RingHom.ker π.toRingHom) :=
    (IsAdicComplete.map_algebraMap_iff (Ideal.span {algebraMap O P ϖ}) _).mpr hQ
  have hmap : ((Ideal.span {algebraMap O P ϖ}).map
      (Ideal.Quotient.mk (RingHom.ker π.toRingHom))).map e =
        Ideal.span {algebraMap O A ϖ} := by
    rw [← Ideal.map_coe, ← e.toRingHom_eq_coe, Ideal.map_map]
    have hcomp : e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker π.toRingHom)) = π.toRingHom :=
      RingHom.ext fun _ ↦ rfl
    rw [hcomp, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x ↦ Ideal.span {x}) (π.commutes ϖ)
  rw [← hmap]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr hQ'

include ϖ in
/-- **Finitely presented modules over an algebra topologically of finite presentation are
`ϖ`-adically separated and complete** (Bosch–Lütkebohmert I, Corollary 1.4). -/
theorem IsTopologicallyFinitePresentation.isAdicComplete_of_finitePresentation {A E : Type*}
    [CommRing A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.FinitePresentation A E]
    (h : IsTopologicallyFinitePresentation O A) :
    IsAdicComplete (Ideal.span {algebraMap O A ϖ}) E := by
  have := h.isAdicComplete ϖ
  obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' A E
  have hker : (LinearMap.ker q).FG := Module.FinitePresentation.fg_ker q hq
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  have hQ : IsAdicComplete (Ideal.span {algebraMap O A ϖ}) ((Fin r → A) ⧸ LinearMap.ker q) :=
    isAdicComplete_quotient_of_fg_of_surjective ϖ hπ hker
  let eqv := q.quotKerEquivOfSurjective hq
  exact
    { toIsHausdorff := IsHausdorff.of_injective _ eqv.symm.toLinearMap eqv.symm.injective
      toIsPrecomplete := IsPrecomplete.of_surjective _ eqv.toLinearMap eqv.surjective }

include ϖ in
/-- Every finitely generated submodule of a finitely presented module over an algebra topologically
of finite presentation is `ϖ`-adically separated and complete. -/
theorem IsTopologicallyFinitePresentation.isAdicComplete_submodule_of_fg {A E : Type*}
    [CommRing A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.FinitePresentation A E]
    (h : IsTopologicallyFinitePresentation O A) {M : Submodule A E} (hM : M.FG) :
    IsAdicComplete (Ideal.span {algebraMap O A ϖ}) M := by
  have := h.isAdicComplete_of_finitePresentation (E := E) ϖ
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact isAdicComplete_submodule_of_fg_of_surjective ϖ hπ hM

include ϖ in
/-- Every finitely generated submodule of a finitely presented module over an algebra topologically
of finite presentation is closed for the `ϖ`-adic module topology. -/
theorem IsTopologicallyFinitePresentation.isClosed_adicModuleTopology_of_fg {A E : Type*}
    [CommRing A] [Algebra O A] [AddCommGroup E] [Module A E] [Module.FinitePresentation A E]
    (h : IsTopologicallyFinitePresentation O A) {M : Submodule A E} (hM : M.FG) :
    @IsClosed E ((Ideal.span {algebraMap O A ϖ}).adicModuleTopology E) (M : Set E) := by
  have := h.isAdicComplete_of_finitePresentation (E := E) ϖ
  obtain ⟨n, π, hπ, -⟩ := (isTopologicallyFinitePresentation_iff O A).mp h
  exact isClosed_adicModuleTopology_of_fg_of_surjective ϖ hπ hM

end UnitBallAndGenericFibre

end TauCeti.Huber

