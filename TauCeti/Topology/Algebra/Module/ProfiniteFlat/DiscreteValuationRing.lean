/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.PrincipalIdealRing
public import TauCeti.Topology.Algebra.Ring.Compact
import TauCeti.RingTheory.Ideal.Operations.Pi
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.Topology.Algebra.Module.Compact.LocalRing
import TauCeti.Topology.Algebra.Module.LinearTopology.CompactVectorSpace
import TauCeti.Topology.Algebra.Module.Nakayama

/-!
# Pseudobases of profinite flat modules over compact discrete valuation rings

Over a compact Hausdorff discrete valuation ring `O`, every profinite flat `O`-module `M : Type v`
admits a *pseudobasis*: a topological `O`-linear isomorphism `M ≃L[O] (I → O)` for some `I : Type v`
(`TauCeti.IsProfiniteFlat.exists_pseudobasis`, `TauCeti.IsProfiniteFlat.iff_exists_pseudobasis`).
The proof lifts a continuous dual basis of the residue vector space `M ⧸ maximalIdeal O • ⊤`
inductively along the uniformizer power quotients `O ⧸ (ϖ ^ (n + 1))` using Baer's criterion
(`TauCeti.IsProfiniteFlat.exists_continuousLinearMap_mk_maximalIdeal_eq`) and applies topological
Nakayama.

## References

* [P. Chojecki, D. Hansen, C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*], Doc. Math. 22 (2017), 191–262 (`arXiv:1507.04875v2`, §6.1, Definition 6.1 and
  Proposition 6.2).
* [M. Demazure, A. Grothendieck, *Schémas en groupes* (SGA 3)], Exp. VII_B, §0.3.8, for
  pseudobases of linearly compact flat modules over discrete valuation rings.
-/

public section

open Filter IsLocalRing Topology

namespace TauCeti.IsProfiniteFlat

section DiscreteValuationRing

universe u v

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]

variable (O) in
/-- Over a compact Hausdorff discrete valuation ring `O`, every product `I → O` with the product
topology is profinite flat. -/
theorem pi_self_of_isDiscreteValuationRing (I : Type*) : IsProfiniteFlat O (I → O) :=
  have := IsLocalRing.totallyDisconnectedSpace_of_compactSpace O; pi_self I

section Pseudobasis

variable {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M] (hM : IsProfiniteFlat O M)
include hM

/-- **Continuous linear functionals lift modulo the maximal ideal.** Over a compact Hausdorff
discrete valuation ring `O`, every continuous `O`-linear map `φ₀ : M →L[O] (O ⧸ maximalIdeal O)`
from a profinite flat `O`-module `M` lifts to a continuous `O`-linear map `F : M →L[O] O`. -/
theorem exists_continuousLinearMap_mk_maximalIdeal_eq (φ₀ : M →L[O] (O ⧸ maximalIdeal O)) :
    ∃ F : M →L[O] O, ∀ m : M, Ideal.Quotient.mk (maximalIdeal O) (F m) = φ₀ m := by
  have := hM.isTopologicalAddGroup; have hadic := IsLocalRing.isAdic_maximalIdeal O
  have := hadic.discreteTopology_quotient
  have : IsAdicComplete (maximalIdeal O) O :=
    IsLocalRing.isAdicComplete_maximalIdeal_of_compactSpace O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let TowerStep (n : ℕ) :=
    { g : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)} // IsOpen (LinearMap.ker g : Set M) }
  have hstep : ∀ n (s : TowerStep n), { g' : TowerStep (n + 1) // ∀ m, Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
      (g'.val m) = s.val m } := fun n s ↦ by
    choose g' hg'_open hg'_comp using hM.exists_lift_span_pow_succ hϖ.ne_zero n s.val s.property
    exact ⟨⟨g', hg'_open⟩, hg'_comp⟩
  let e₀ : (O ⧸ maximalIdeal O) ≃ₗ[O] (O ⧸ Ideal.span {ϖ ^ 1}) :=
    Submodule.quotEquivOfEq _ _ (by rw [hϖ.maximalIdeal_eq, pow_one])
  have hker₀ : IsOpen (LinearMap.ker (e₀.toLinearMap.comp φ₀.toLinearMap) : Set M) := by
    convert (isOpen_discrete ({0} : Set (O ⧸ maximalIdeal O))).preimage φ₀.continuous; ext; simp
  let tower : (n : ℕ) → TowerStep n :=
    Nat.rec ⟨e₀.toLinearMap.comp φ₀.toLinearMap, hker₀⟩ fun n s ↦ (hstep n s).val
  have hK (n : ℕ) : Ideal.span {ϖ ^ (n + 1)} = (maximalIdeal O) ^ (id n + 1) := by
    rw [hϖ.maximalIdeal_eq, id_eq, Ideal.span_singleton_pow]
  let F : M →L[O] O := hadic.liftIdealTower (strictMono_id.add_const 1) hK (fun n ↦ (tower n).val)
    (fun n ↦ (tower n).property) (fun n m ↦ (hstep n (tower n)).property m)
  -- `tower 0` is definitionally the base step of the `Nat.rec` tower.
  have htower0 : (tower 0).val = e₀.toLinearMap ∘ₗ φ₀.toLinearMap := rfl
  refine ⟨F, fun m ↦ e₀.injective ?_⟩
  rw [Submodule.quotEquivOfEq_ideal_mk, hadic.mk_liftIdealTower _ hK _ _ _ 0 m, htower0]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ContinuousLinearMap.coe_coe]

/-- **Existence of a pseudobasis.** Every profinite flat module `M : Type v` over a compact
Hausdorff discrete valuation ring `O` is topologically `O`-linearly isomorphic to `I → O` for some
`I : Type v`. -/
theorem exists_pseudobasis : ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) := by
  have := hM.isTopologicalAddGroup
  have := (IsLocalRing.isAdic_maximalIdeal O).discreteTopology_quotient
  let := Ideal.Quotient.field (maximalIdeal O)
  have : CompactSpace (O ⧸ maximalIdeal O) := Quotient.compactSpace
  let M₀ := M ⧸ ((maximalIdeal O) • (⊤ : Submodule O M))
  obtain ⟨I, ⟨e₀⟩⟩ :=
    hM.toIsCompactModule.quotient_maximalIdeal_smul_top.exists_continuousLinearEquiv_pi_of_field
  let φ₀ (i : I) : M →L[O] (O ⧸ maximalIdeal O) :=
    ⟨((ContinuousLinearMap.proj i).comp e₀.toContinuousLinearMap).toLinearMap.restrictScalars O ∘ₗ
      ((maximalIdeal O) • (⊤ : Submodule O M)).mkQ,
      ((ContinuousLinearMap.proj i).comp e₀.toContinuousLinearMap).continuous.comp
        continuous_quot_mk⟩
  choose F hF using fun i : I ↦ hM.exists_continuousLinearMap_mk_maximalIdeal_eq (φ₀ i)
  let Φ : M →L[O] (I → O) := ContinuousLinearMap.pi F
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let Φbar := Submodule.mapQ ((maximalIdeal O) • ⊤) ((maximalIdeal O) • ⊤) Φ.toLinearMap
    (Submodule.smul_top_le_comap_smul_top (maximalIdeal O) Φ.toLinearMap)
  let ePi :=
    ((isNoetherianRing_iff_ideal_fg O).mp inferInstance (maximalIdeal O)).quotientSmulTopEquivPi I
  have hπΦ (y₀ : M₀) : ePi (Φbar y₀) = e₀ y₀ := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y₀
    ext i
    simp [ePi, Φbar, Φ, φ₀, hF i m]
  have hbij : Function.Bijective Φbar := by
    have hcomp : (ePi ∘ Φbar) = e₀ := funext hπΦ
    exact (ePi.bijective.of_comp_iff' Φbar).mp (hcomp ▸ e₀.bijective)
  refine ⟨I, ⟨hM.toIsCompactModule.continuousLinearEquivOfBijectiveMapQ
    (pi_self_of_isDiscreteValuationRing O I).toIsCompactModule hϖ.maximalIdeal_eq
    ((IsLocalRing.isAdic_maximalIdeal O).isTopologicallyNilpotent_of_mem
      (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ))
    (smul_right_injective (I → O) hϖ.ne_zero) Φ hbij⟩⟩

end Pseudobasis

/-- **Characterization of profinite flat modules by pseudobases.** Over a compact Hausdorff discrete
valuation ring `O`, a topological `O`-module `M : Type v` is profinite flat if and only if it is
topologically `O`-linearly isomorphic to `I → O` for some `I : Type v`. -/
theorem iff_exists_pseudobasis {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M] :
    IsProfiniteFlat O M ↔ ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) :=
  ⟨fun hM ↦ hM.exists_pseudobasis,
    fun ⟨I, ⟨e⟩⟩ ↦ (pi_self_of_isDiscreteValuationRing O I).of_continuousLinearEquiv e.symm⟩

end DiscreteValuationRing

end TauCeti.IsProfiniteFlat
