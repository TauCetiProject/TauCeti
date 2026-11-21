/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Basic
public import TauCeti.Topology.Algebra.Ring.Compact
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.RingTheory.AdicCompletion.Topology
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Ideal.Quotient.Pi
import TauCeti.RingTheory.Ideal.Quotient.PowTransition
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
  have := IsLocalRing.totallyDisconnectedSpace_of_compactSpace O
  pi_self I

section Pseudobasis

variable {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M] (hM : IsProfiniteFlat O M)
include hM

omit [IsDiscreteValuationRing O] [IsTopologicalRing O] [T2Space O] in
/-- Given `φ : M →ₗ[O] O ⧸ (ϖ ^ (n + 1))` with open kernel on a profinite flat `O`-module `M`,
there is an open submodule `V ≤ ker φ` containing `(ϖ ^ (n + 2)) • ⊤` such that `ϖ • m ∈ V` forces
`m ∈ ker φ`. -/
private theorem exists_open_submodule_ker_of_mul {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ V : Submodule O M, IsOpen (V : Set M) ∧ Ideal.span {ϖ ^ (n + 2)} • (⊤ : Submodule O M) ≤ V ∧
      V ≤ LinearMap.ker φ ∧ ∀ ⦃m : M⦄, ϖ • m ∈ V → m ∈ LinearMap.ker φ := by
  have := hM.isTorsionFree; have ⟨⟨_, _, _, _⟩, _⟩ := hM
  have := hM.t2Space; have := hM.isLinearTopology
  let J₁ : Ideal O := Ideal.span {ϖ ^ (n + 1)}; let J₂ : Ideal O := Ideal.span {ϖ ^ (n + 2)}
  have hC_closed : IsClosed ((fun m : M ↦ ϖ • m) '' (LinearMap.ker φ : Set M)ᶜ) :=
    (hker.isClosed_compl.isCompact.image (continuous_const.smul continuous_id)).isClosed
  have h0C : (0 : M) ∉ (fun m : M ↦ ϖ • m) '' (LinearMap.ker φ : Set M)ᶜ := by
    rintro ⟨m, hm, hm0⟩
    exact hm (smul_right_injective M hϖ (hm0.trans (smul_zero ϖ).symm) ▸ (LinearMap.ker φ).zero_mem)
  obtain ⟨V₀, hV₀_open, hV₀C⟩ :=
    (IsLinearTopology.hasBasis_open_submodule O).mem_iff.mp (hC_closed.compl_mem_nhds h0C)
  have hJ₁_ker : J₁ • (⊤ : Submodule O M) ≤ LinearMap.ker φ := Submodule.smul_le.mpr fun r hr m _ ↦
    by rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  refine ⟨(V₀ ⊓ LinearMap.ker φ) ⊔ (J₂ • (⊤ : Submodule O M)), AddSubgroup.isOpen_mono
    (H₁ := (V₀ ⊓ LinearMap.ker φ).toAddSubgroup)
    (H₂ := ((V₀ ⊓ LinearMap.ker φ) ⊔ (J₂ • (⊤ : Submodule O M))).toAddSubgroup)
    (fun _ hx ↦ Submodule.mem_sup_left hx) (hV₀_open.inter hker), le_sup_right, sup_le inf_le_right
    ((Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))).trans hJ₁_ker), fun {m} hm ↦ ?_⟩
  obtain ⟨v₁, hv₁, y, hy, heq⟩ := Submodule.mem_sup.mp hm
  have hy' : y ∈ Ideal.span ({ϖ} : Set O) • (J₁ • (⊤ : Submodule O M)) := by
    have hJ₂ : J₂ = Ideal.span ({ϖ} : Set O) * J₁ := by
      simp [J₁, J₂, Ideal.span_singleton_mul_span_singleton, pow_succ']
    simpa [hJ₂, mul_smul] using hy
  rw [Submodule.ideal_span_singleton_smul] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  have hmz : m - z ∈ LinearMap.ker φ := by
    by_contra hm_ker
    exact hV₀C hv₁.1 ⟨m - z, hm_ker, by simp [smul_sub, ← heq]⟩
  simpa using add_mem hmz (hJ₁_ker hz)

omit [IsDiscreteValuationRing O] [IsTopologicalRing O] [T2Space O] in
/-- One-step lifting of continuous `O`-linear functionals along `(ϖ ^ (n + 2)) → (ϖ ^ (n + 1))`. -/
private theorem exists_lift_span_pow_succ [IsPrincipalIdealRing O] {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ φ' : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 2)}, IsOpen (LinearMap.ker φ' : Set M) ∧
      ∀ m : M, Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
        (φ' m) = φ m := by
  have := hM.isTopologicalAddGroup; let J₂ : Ideal O := Ideal.span {ϖ ^ (n + 2)}
  obtain ⟨V, hV_open, hJ₂_le, hV_le_ker, hV_ker⟩ :=
    hM.exists_open_submodule_ker_of_mul hϖ n φ hker
  have htor : Module.IsTorsionBySet O (M ⧸ V) J₂ := (Module.isTorsionBySet_quotient_iff V J₂).mpr
    fun _ _ hr ↦ hJ₂_le (Submodule.smul_mem_smul hr Submodule.mem_top)
  let := htor.module; have : IsScalarTower O (O ⧸ J₂) (M ⧸ V) := htor.isScalarTower
  let β : M →ₗ[O] (O ⧸ J₂) := (Ideal.Quotient.mulSpanPowSucc ϖ (n + 1)).comp φ
  let βbar : (M ⧸ V) →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    (V.liftQ β (hV_le_ker.trans (LinearMap.ker_le_ker_comp φ _))).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let μ : (M ⧸ V) →ₗ[O ⧸ J₂] (M ⧸ V) := LinearMap.lsmul (O ⧸ J₂) (M ⧸ V) (Ideal.Quotient.mk J₂ ϖ)
  have hker_μ : LinearMap.ker μ.rangeRestrict ≤ LinearMap.ker βbar := fun x hx ↦ by
    obtain ⟨m, rfl⟩ := V.mkQ_surjective x
    have hμ0 : V.mkQ (ϖ • m) = 0 := by
      simpa [μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using
        congr_arg Subtype.val (LinearMap.mem_ker.mp hx)
    simp [LinearMap.mem_ker, βbar, β,
      LinearMap.mem_ker.mp (hV_ker ((Submodule.Quotient.mk_eq_zero V).mp hμ0))]
  let ψ₀ : LinearMap.range μ →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    (μ.rangeRestrict.liftOfSurjective μ.surjective_rangeRestrict) ⟨βbar, hker_μ⟩
  obtain ⟨ψ, hψ⟩ := (Module.Baer.quotient_span_singleton_self
    (pow_ne_zero (n + 2) hϖ)).extension_property _ (LinearMap.range μ).injective_subtype ψ₀
  let φ' : M →ₗ[O] (O ⧸ J₂) := (ψ.restrictScalars O).comp V.mkQ
  refine ⟨φ', AddSubgroup.isOpen_mono (H₁ := V.toAddSubgroup)
    (H₂ := (LinearMap.ker φ').toAddSubgroup)
    (fun m hm ↦ by simp [φ', (Submodule.Quotient.mk_eq_zero V).mpr hm]) hV_open, fun m ↦ ?_⟩
  apply Ideal.Quotient.mulSpanPowSucc_injective (mul_right_injective₀ hϖ) (n + 1)
  rw [Ideal.Quotient.mulSpanPowSucc_factor, ← map_smul]
  calc φ' (ϖ • m) = (ψ.comp (LinearMap.range μ).subtype) (μ.rangeRestrict (V.mkQ m)) := by
        simp [φ', μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    _ = ψ₀ (μ.rangeRestrict (V.mkQ m)) := by rw [hψ]
    _ = Ideal.Quotient.mulSpanPowSucc ϖ (n + 1) (φ m) := by simp [ψ₀, βbar, β]

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
  refine ⟨F, fun m ↦ e₀.injective ?_⟩
  rw [Submodule.quotEquivOfEq_ideal_mk, hadic.mk_liftIdealTower _ hK _ _ _ 0 m]; rfl

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
  have hπΦ (y₀ : M₀) : (maximalIdeal O).quotPiSMulTopToPiQuot I (Φbar y₀) = e₀ y₀ := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y₀; ext i; simp [Φbar, Φ, hF i m, φ₀]
  refine ⟨I, ⟨hM.toIsCompactModule.continuousLinearEquivOfBijectiveMapQ
    (pi_self_of_isDiscreteValuationRing O I).toIsCompactModule hϖ.maximalIdeal_eq
    ((IsLocalRing.isAdic_maximalIdeal O).isTopologicallyNilpotent_of_mem
      (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ))
    (smul_right_injective (I → O) hϖ.ne_zero) Φ ⟨fun y₁ y₂ hy ↦ e₀.injective ((hπΦ y₁).symm.trans
      ((congr_arg ((maximalIdeal O).quotPiSMulTopToPiQuot I) hy).trans (hπΦ y₂))), fun z ↦ ?_⟩⟩⟩
  obtain ⟨y₀, hy₀⟩ := e₀.surjective ((maximalIdeal O).quotPiSMulTopToPiQuot I z)
  exact ⟨y₀, ((isNoetherianRing_iff_ideal_fg O).mp inferInstance
    (maximalIdeal O)).quotPiSMulTopToPiQuot_injective I ((hπΦ y₀).trans hy₀)⟩

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
