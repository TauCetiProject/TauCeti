/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Order
public import TauCeti.RingTheory.PowerSeries.PiTopology
public import TauCeti.Topology.Algebra.Module.Compact
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.RingTheory.Flat.Pi
import TauCeti.Topology.Algebra.Module.LinearTopology.CompactVectorSpace
import TauCeti.Topology.Algebra.Module.Nakayama
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic
import TauCeti.Topology.Algebra.Ring.Compact

/-!
# Profinite flat modules and pseudobases

A topological module `M` over a commutative topological ring `R` is *profinite flat*
(`TauCeti.IsProfiniteFlat`) if it is a compact module (`TauCeti.IsCompactModule R M` — a compact,
Hausdorff, totally disconnected topological `R`-module) and is algebraically flat over `R`
(`Module.Flat R M`).

Over the valuation ring `O` of a nonarchimedean local field — and more generally over any compact
Hausdorff discrete valuation ring — profinite flat `O`-modules serve as the integral coefficient
modules of continuous `p`-adic representations and completed group or distribution algebras. Their
fundamental structure theorem asserts that every profinite flat `O`-module admits a *pseudobasis*:
a topological `O`-linear isomorphism `M ≃L[O] (I → O)` to an arbitrary product of copies of `O`
equipped with the product topology. Consequently, a topological `O`-module is profinite flat if and
only if it is topologically `O`-linearly isomorphic to `I → O` for some index type `I`, and any
such coordinate isomorphism induces a basis of open `O`-submodule neighbourhoods of `0` given by
bounding finitely many coordinates in powers of the maximal ideal.

## Main definitions and results

* `TauCeti.IsProfiniteFlat`: bundled predicate combining `TauCeti.IsCompactModule R M` and
  `Module.Flat R M`, with stability under finite products (`prod`, `pi_of_finite`), continuous
  linear equivalences, and (over a Dedekind domain) closed submodules and arbitrary products.
* `ContinuousLinearEquiv.openSubmodulePi`,
  `ContinuousLinearEquiv.hasBasis_nhds_zero_openSubmodulePi`: for `e : M ≃L[R] (I → R)` over a ring
  whose topology is `J`-adic, the submodules `{m | ∀ i ∈ s, e m i ∈ J ^ n}` (`s : Finset I`,
  `n : ℕ`) are open and form a neighbourhood basis of `0` in `M`.
* `TauCeti.IsProfiniteFlat.exists_continuousLinearMap_lift_mkQ`: over a compact Hausdorff discrete
  valuation ring `O`, every continuous `O`-linear map `M →L[O] (O ⧸ maximalIdeal O)` lifts to a
  continuous `O`-linear map `M →L[O] O`.
* `TauCeti.IsProfiniteFlat.exists_pseudobasis`,
  `TauCeti.IsProfiniteFlat.iff_exists_pseudobasis`: over a compact Hausdorff discrete valuation
  ring `O`, a topological `O`-module `M : Type v` is profinite flat if and only if
  `∃ I : Type v, Nonempty (M ≃L[O] (I → O))`.
* `TauCeti.IsProfiniteFlat.mvPowerSeries`, `TauCeti.IsProfiniteFlat.powerSeries`: formal power
  series `MvPowerSeries σ O` and `PowerSeries O` with the product topology on coefficients are
  profinite flat `O`-modules.
* Separation of the hypotheses: `not_isProfiniteFlat_quotient_maximalIdeal` (compact, not flat),
  `not_isProfiniteFlat_self_of_discreteTopology` (flat, discrete, not compact),
  `not_isProfiniteFlat_of_isFractionRing` (fraction field, not profinite flat for any topology),
  and `not_isProfiniteFlat_of_indiscreteTopology` /
  `isEmpty_continuousLinearEquiv_pi_of_indiscreteTopology` (compact, linearly topologized, flat,
  not Hausdorff).

## References

* [P. Chojecki, D. Hansen, C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*], Ann. Inst. Fourier 67 (2017), §6.1, Definition 6.1 and Proposition 6.2.
* [M. Demazure, A. Grothendieck, *Schémas en groupes* (SGA 3)], Exp. VII_B, §0.3.8, for
  pseudobases of linearly compact flat modules over discrete valuation rings.
-/

public section

open Filter IsLocalRing Topology

namespace ContinuousLinearEquiv

section PseudobasisBasis

variable {R M I : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- Given a topological coordinate isomorphism `e : M ≃L[R] (I → R)` and an ideal `J` of `R`, the
`R`-submodule `{m : M | ∀ i ∈ s, e m i ∈ J ^ n}` cut out on a finite set of coordinates `s`. -/
def openSubmodulePi (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) (n : ℕ) :
    Submodule R M :=
  (Submodule.pi (s : Set I) fun _ ↦ J ^ n).comap e.toLinearMap

@[simp]
theorem mem_openSubmodulePi_iff (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) (n : ℕ)
    (m : M) : m ∈ e.openSubmodulePi J s n ↔ ∀ i ∈ s, e m i ∈ J ^ n :=
  Iff.rfl

/-- When the topology of `R` is `J`-adic, each coordinate congruence submodule
`e.openSubmodulePi J s n` is open in `M`. -/
theorem isOpen_openSubmodulePi (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J)
    (s : Finset I) (n : ℕ) : IsOpen (e.openSubmodulePi J s n : Set M) :=
  (isOpen_set_pi s.finite_toSet fun _ _ ↦ hJ.isOpen_pow n).preimage e.continuous

/-- **Neighbourhood basis from a pseudobasis.** If `e : M ≃L[R] (I → R)` and the topology of `R`
is `J`-adic, then the open submodules `e.openSubmodulePi J s n` (`s : Finset I`, `n : ℕ`) form a
basis of neighbourhoods of `0` in `M`. -/
theorem hasBasis_nhds_zero_openSubmodulePi (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J) :
    (𝓝 (0 : M)).HasBasis (fun _ : Finset I × ℕ ↦ True)
      (fun p ↦ (e.openSubmodulePi J p.1 p.2 : Set M)) := by
  rw [hasBasis_iff]
  intro W
  refine ⟨fun hW ↦ ?_, fun ⟨⟨s, n⟩, _, hsub⟩ ↦
    mem_of_superset ((e.isOpen_openSubmodulePi hJ s n).mem_nhds (zero_mem _)) hsub⟩
  have hW' : e.symm ⁻¹' W ∈ 𝓝 (0 : I → R) := by
    rw [← e.symm.map_zero] at hW
    exact e.symm.continuous.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi'] at hW'
  obtain ⟨s, t, ht, hst⟩ := hW'
  have hk : ∀ i : I, ∃ k : ℕ, ((J ^ k : Ideal R) : Set R) ⊆ t i := fun i ↦ by
    obtain ⟨k, -, hk⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp (ht i)
    exact ⟨k, hk⟩
  choose k hk using hk
  refine ⟨(s, s.sup k), trivial, fun m hm ↦ ?_⟩
  have hem : e m ∈ (s : Set I).pi t := fun i hi ↦
    hk i (Ideal.pow_le_pow_right (Finset.le_sup hi) (hm i hi))
  simpa using hst hem

end PseudobasisBasis

end ContinuousLinearEquiv

namespace TauCeti

/-- A topological `R`-module `M` over a commutative ring `R` is *profinite flat* if it is a compact
module (`IsCompactModule R M`, i.e. a compact, Hausdorff, totally disconnected topological
`R`-module) and is algebraically flat over `R` (`Module.Flat R M`). -/
structure IsProfiniteFlat (R M : Type*) [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] : Prop extends IsCompactModule R M where
  /-- The underlying `R`-module is flat. -/
  flat : Module.Flat R M

theorem isProfiniteFlat_iff {R M : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] :
    IsProfiniteFlat R M ↔ IsCompactModule R M ∧ Module.Flat R M :=
  ⟨fun h ↦ ⟨h.toIsCompactModule, h.flat⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

end TauCeti

namespace ContinuousLinearEquiv

variable {R M N : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- A continuous linear equivalence preserves `TauCeti.IsProfiniteFlat`. -/
theorem isProfiniteFlat_iff (e : M ≃L[R] N) :
    TauCeti.IsProfiniteFlat R M ↔ TauCeti.IsProfiniteFlat R N := by
  rw [TauCeti.isProfiniteFlat_iff, TauCeti.isProfiniteFlat_iff]
  exact and_congr e.isCompactModule_iff (Module.Flat.equiv_iff e.toLinearEquiv)

end ContinuousLinearEquiv

namespace TauCeti.IsProfiniteFlat

section CommRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- Every profinite flat module is torsion-free over `R`. -/
theorem isTorsionFree (hM : IsProfiniteFlat R M) : Module.IsTorsionFree R M :=
  have := hM.flat
  inferInstance

/-- A compact, totally disconnected commutative topological ring is profinite flat over itself. -/
theorem self [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] :
    IsProfiniteFlat R R :=
  ⟨.self, inferInstance⟩

/-- Any subsingleton topological `R`-module is profinite flat. -/
theorem subsingleton [Subsingleton M] : IsProfiniteFlat R M :=
  ⟨.subsingleton,
    Module.Flat.of_retract (M := R) 0 0 (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)⟩

/-- Binary products of profinite flat modules are profinite flat. -/
theorem prod {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hM : IsProfiniteFlat R M) (hN : IsProfiniteFlat R N) :
    IsProfiniteFlat R (M × N) :=
  have := hM.flat
  have := hN.flat
  ⟨hM.toIsCompactModule.prod hN.toIsCompactModule, inferInstance⟩

/-- Finite products of profinite flat modules over any commutative ring are profinite flat. -/
theorem pi_of_finite {ι : Type*} [Finite ι] {P : ι → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] [∀ i, TopologicalSpace (P i)] (hP : ∀ i, IsProfiniteFlat R (P i)) :
    IsProfiniteFlat R (∀ i, P i) :=
  have := fun i ↦ (hP i).flat
  ⟨IsCompactModule.pi fun i ↦ (hP i).toIsCompactModule, inferInstance⟩

/-- Transport `IsProfiniteFlat` along a continuous linear equivalence. -/
theorem of_continuousLinearEquiv {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hM : IsProfiniteFlat R M) (e : M ≃L[R] N) : IsProfiniteFlat R N :=
  e.isProfiniteFlat_iff.mp hM

end CommRing

section DedekindDomain

variable {R M : Type*} [CommRing R] [IsDedekindDomain R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- Over a Dedekind domain, a topological module is profinite flat if and only if it is a compact
module and torsion-free. -/
theorem _root_.TauCeti.isProfiniteFlat_iff_isCompactModule_and_isTorsionFree :
    IsProfiniteFlat R M ↔ IsCompactModule R M ∧ Module.IsTorsionFree R M :=
  ⟨fun h ↦ ⟨h.toIsCompactModule, h.isTorsionFree⟩,
    fun ⟨hc, _⟩ ↦ ⟨hc, inferInstance⟩⟩

/-- Over a Dedekind domain, a closed submodule of a profinite flat module is profinite flat. -/
theorem submodule (hM : IsProfiniteFlat R M) (N : Submodule R M) (hN : IsClosed (N : Set M)) :
    IsProfiniteFlat R N :=
  have := hM.isTorsionFree
  ⟨hM.toIsCompactModule.submodule N hN, inferInstance⟩

/-- Over a Dedekind domain, an arbitrary product of profinite flat modules is profinite flat. -/
theorem pi {ι : Type*} {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, TopologicalSpace (P i)] (hP : ∀ i, IsProfiniteFlat R (P i)) :
    IsProfiniteFlat R (∀ i, P i) :=
  have := fun i ↦ (hP i).isTorsionFree
  ⟨IsCompactModule.pi fun i ↦ (hP i).toIsCompactModule, inferInstance⟩

/-- Over a compact totally disconnected Dedekind domain, every product `I → R` is profinite flat. -/
theorem pi_self [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] (I : Type*) :
    IsProfiniteFlat R (I → R) :=
  pi fun _ : I ↦ self

end DedekindDomain

section CompactLocalRing

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R]

/-- A compact Hausdorff noetherian local ring is profinite flat over itself. -/
theorem self_of_isLocalRing : IsProfiniteFlat R R :=
  ⟨IsCompactModule.self_of_isLocalRing R, inferInstance⟩

end CompactLocalRing

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

/-- Multiplication by a nonzero element `ϖ` induces an injective `O`-linear map
`(O ⧸ (ϖ ^ (n + 1))) →ₗ[O] (O ⧸ (ϖ ^ (n + 2)))`. -/
private def mulUniformizerQuot {ϖ : O} (n : ℕ) :
    (O ⧸ Ideal.span {ϖ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 2)}) :=
  Submodule.liftQ (Ideal.span {ϖ ^ (n + 1)})
    ((Ideal.span {ϖ ^ (n + 2)}).mkQ.comp (LinearMap.lsmul O O ϖ)) <| by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.lsmul_apply, smul_eq_mul,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      rw [Ideal.mem_span_singleton] at hr
      obtain ⟨c, rfl⟩ := hr
      exact ⟨c, by ring⟩

omit [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
  [T2Space O] in
private theorem injective_mulUniformizerQuot {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    Function.Injective (mulUniformizerQuot n (ϖ := ϖ)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.mem_ker] at hq
  dsimp only [mulUniformizerQuot] at hq
  rw [Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.lsmul_apply, smul_eq_mul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, pow_succ'] at hq
  have hdvd : ϖ ^ (n + 1) ∣ r := (mul_dvd_mul_iff_left hϖ).mp hq
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton.mpr hdvd)

omit [IsDiscreteValuationRing O] [IsTopologicalRing O] [T2Space O] in
/-- Given `φ : M →ₗ[O] O ⧸ (ϖ ^ (n + 1))` with open kernel on a profinite flat `O`-module `M`,
there is an open submodule `V` containing `(ϖ ^ (n + 2)) • ⊤` such that `ϖ • m ∈ V` forces
`m ∈ ker φ`. -/
private theorem exists_open_submodule_ker_of_mul {M : Type v} [AddCommGroup M] [Module O M]
    [TopologicalSpace M] (hM : IsProfiniteFlat O M) {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ V : Submodule O M,
      IsOpen (V : Set M) ∧
        Ideal.span {ϖ ^ (n + 2)} • (⊤ : Submodule O M) ≤ V ∧
          ∀ ⦃m : M⦄, ϖ • m ∈ V → m ∈ LinearMap.ker φ := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.t2Space
  have := hM.isLinearTopology
  have := hM.isTorsionFree
  let J₁ : Ideal O := Ideal.span {ϖ ^ (n + 1)}
  let J₂ : Ideal O := Ideal.span {ϖ ^ (n + 2)}
  -- Separate `0` from the compact image `ϖ • (ker φ)ᶜ` by an open submodule `V₀`.
  let C : Set M := (fun m : M ↦ ϖ • m) '' (LinearMap.ker φ : Set M)ᶜ
  have hC_closed : IsClosed C :=
    (hker.isClosed_compl.isCompact.image (continuous_const.smul continuous_id)).isClosed
  have h0C : (0 : M) ∉ C := by
    rintro ⟨m, hm, hm0⟩
    have hm_eq : m = 0 := smul_right_injective M hϖ (by simpa using hm0)
    exact hm (hm_eq ▸ (LinearMap.ker φ).zero_mem)
  obtain ⟨V₀, hV₀_open, hV₀C⟩ :=
    (IsLinearTopology.hasBasis_open_submodule O).mem_iff.mp (hC_closed.compl_mem_nhds h0C)
  have hV₀_ker : ∀ {m : M}, ϖ • m ∈ V₀ → m ∈ LinearMap.ker φ := fun {m} hm ↦ by
    by_contra hm_ker
    exact hV₀C hm ⟨m, hm_ker, rfl⟩
  -- Enlarge `V₀` by `J₂ • ⊤` so `M ⧸ V` is annihilated by `J₂` while preserving `hV₀_ker`.
  let V : Submodule O M := V₀ ⊔ (J₂ • (⊤ : Submodule O M))
  have hV_open : IsOpen (V : Set M) :=
    AddSubgroup.isOpen_mono (H₁ := V₀.toAddSubgroup) (H₂ := V.toAddSubgroup)
      (fun _ hx ↦ Submodule.mem_sup_left hx) hV₀_open
  have hJ₁_ker : J₁ • (⊤ : Submodule O M) ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  refine ⟨V, hV_open, le_sup_right, fun {m} hm ↦ ?_⟩
  obtain ⟨v₀, hv₀, y, hy, heq⟩ := Submodule.mem_sup.mp hm
  have hy' : y ∈ Ideal.span ({ϖ} : Set O) • (J₁ • (⊤ : Submodule O M)) := by
    have hJ₂_eq : J₂ = Ideal.span ({ϖ} : Set O) * J₁ := by
      simp [J₁, J₂, Ideal.span_singleton_mul_span_singleton, pow_succ']
    simpa [hJ₂_eq, mul_smul] using hy
  rw [Submodule.ideal_span_singleton_smul] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  have hmz : m - z ∈ LinearMap.ker φ := hV₀_ker (by
    have : ϖ • (m - z) = v₀ := by simp [smul_sub, ← heq]
    exact this ▸ hv₀)
  simpa using add_mem hmz (hJ₁_ker hz)

omit [IsTopologicalRing O] [T2Space O] in
/-- One-step lifting of continuous `O`-linear functionals along `(ϖ ^ (n + 2)) → (ϖ ^ (n + 1))`:
an `O`-linear map `φ : M →ₗ[O] O ⧸ (ϖ ^ (n + 1))` with open kernel on a profinite flat `O`-module
lifts to `φ' : M →ₗ[O] O ⧸ (ϖ ^ (n + 2))` with open kernel. -/
private theorem exists_lift_span_pow_succ {M : Type v} [AddCommGroup M] [Module O M]
    [TopologicalSpace M] (hM : IsProfiniteFlat O M) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ φ' : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 2)},
      IsOpen (LinearMap.ker φ' : Set M) ∧
        ∀ m : M,
          Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
            (φ' m) = φ m := by
  have := hM.isTopologicalAddGroup
  let J₂ : Ideal O := Ideal.span {ϖ ^ (n + 2)}
  obtain ⟨V, hV_open, hJ₂_le, hV_ker⟩ :=
    hM.exists_open_submodule_ker_of_mul hϖ.ne_zero n φ hker
  -- Equip `M ⧸ V` with its `(O ⧸ J₂)`-module structure and extend via Baer's criterion on `O ⧸ J₂`.
  have htor : Module.IsTorsionBySet O (M ⧸ V) J₂ :=
    (Module.isTorsionBySet_quotient_iff V J₂).mpr fun _ _ hr ↦
      hJ₂_le (Submodule.smul_mem_smul hr Submodule.mem_top)
  let := htor.module
  have : IsScalarTower O (O ⧸ J₂) (M ⧸ V) := htor.isScalarTower
  let αO : M →ₗ[O] (M ⧸ V) := V.mkQ.comp (LinearMap.lsmul O M ϖ)
  let β : M →ₗ[O] (O ⧸ J₂) := (mulUniformizerQuot n).comp φ
  have hker_le : LinearMap.ker αO ≤ LinearMap.ker β := fun m hm ↦ by
    have hmV : ϖ • m ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hm
    simp [β, LinearMap.mem_ker.mp (hV_ker hmV)]
  let S : Submodule (O ⧸ J₂) (M ⧸ V) :=
    { (LinearMap.range αO).toAddSubgroup with
      smul_mem' := fun r _ ⟨m, hm⟩ ↦ by
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
        refine ⟨c • m, ?_⟩
        rw [map_smul, hm, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
  let ψ₀O : LinearMap.range αO →ₗ[O] (O ⧸ J₂) :=
    (Submodule.liftQ (LinearMap.ker αO) β hker_le).comp αO.quotKerEquivRange.symm.toLinearMap
  let ψ₀ : S →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    { toFun := fun x ↦ ψ₀O ⟨x.1, x.2⟩
      map_add' := fun x y ↦ ψ₀O.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_smul' := fun r x ↦ by
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
        dsimp only [RingHom.id_apply]
        have hx :
            (⟨↑((Ideal.Quotient.mk J₂ c) • x), ((Ideal.Quotient.mk J₂ c) • x).2⟩ :
              LinearMap.range αO) = c • ⟨x.1, x.2⟩ :=
          Subtype.ext (by
            rw [Submodule.coe_smul, Submodule.coe_smul, ← Ideal.Quotient.algebraMap_eq,
              algebraMap_smul])
        rw [hx, ψ₀O.map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
  obtain ⟨ψ, hψ⟩ :=
    (Module.Baer.quotient_span_singleton (pow_ne_zero (n + 2) hϖ.ne_zero)).extension_property
      S.subtype S.injective_subtype ψ₀
  let φ' : M →ₗ[O] (O ⧸ J₂) := (ψ.restrictScalars O).comp V.mkQ
  refine ⟨φ', AddSubgroup.isOpen_mono (H₁ := V.toAddSubgroup)
    (H₂ := (LinearMap.ker φ').toAddSubgroup)
    (fun m hm ↦ by simp [φ', (Submodule.Quotient.mk_eq_zero V).mpr hm]) hV_open, fun m ↦ ?_⟩
  apply injective_mulUniformizerQuot hϖ.ne_zero n
  have hcompat : ∀ q : O ⧸ J₂,
      mulUniformizerQuot n (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1)))) q) =
        ϖ • q :=
    fun q ↦ Quotient.inductionOn' q fun _ ↦ rfl
  rw [hcompat, ← map_smul]
  have happ : φ' (ϖ • m) = (ψ.comp S.subtype) ⟨αO m, ⟨m, rfl⟩⟩ := rfl
  have hψ₀ : ψ₀ ⟨αO m, ⟨m, rfl⟩⟩ = ψ₀O ⟨αO m, ⟨m, rfl⟩⟩ := rfl
  have hq : αO.quotKerEquivRange.symm ⟨αO m, ⟨m, rfl⟩⟩ = Submodule.Quotient.mk m :=
    αO.quotKerEquivRange.symm_apply_apply (Submodule.Quotient.mk m)
  rw [happ, hψ, hψ₀]
  dsimp only [ψ₀O, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [hq, Submodule.liftQ_apply]
  rfl

/-- **Continuous linear functionals lift modulo the maximal ideal.** Over a compact Hausdorff
discrete valuation ring `O`, every continuous `O`-linear map `φ₀ : M →L[O] (O ⧸ maximalIdeal O)`
from a profinite flat `O`-module `M` lifts to a continuous `O`-linear map `F : M →L[O] O`. -/
theorem exists_continuousLinearMap_lift_mkQ {M : Type v} [AddCommGroup M] [Module O M]
    [TopologicalSpace M] (hM : IsProfiniteFlat O M) (φ₀ : M →L[O] (O ⧸ maximalIdeal O)) :
    ∃ F : M →L[O] O, ∀ m : M, Ideal.Quotient.mk (maximalIdeal O) (F m) = φ₀ m := by
  have := hM.isTopologicalAddGroup
  have hadic : IsAdic (maximalIdeal O) := IsLocalRing.isAdic_maximalIdeal O
  have := hadic.discreteTopology_quotient
  have : IsAdicComplete (maximalIdeal O) O :=
    IsLocalRing.isAdicComplete_maximalIdeal_of_compactSpace O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  -- Build a compatible tower `g n : M →ₗ[O] O ⧸ (ϖ ^ (n + 1))` with open kernels by recursion.
  let TowerStep (n : ℕ) :=
    { g : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)} // IsOpen (LinearMap.ker g : Set M) }
  have hstep : ∀ n (s : TowerStep n),
      { g' : TowerStep (n + 1) //
        ∀ m, Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
          (g'.1 m) = s.1 m } := fun n s ↦ by
    choose g' hg'_open hg'_comp using hM.exists_lift_span_pow_succ hϖ n s.1 s.2
    exact ⟨⟨g', hg'_open⟩, hg'_comp⟩
  let e₀ : (O ⧸ maximalIdeal O) ≃ₗ[O] (O ⧸ Ideal.span {ϖ ^ 1}) :=
    Submodule.quotEquivOfEq _ _ (by rw [hmax, pow_one])
  have hker₀ : IsOpen (LinearMap.ker (e₀.toLinearMap.comp φ₀.toLinearMap) : Set M) := by
    have hset : (LinearMap.ker (e₀.toLinearMap.comp φ₀.toLinearMap) : Set M) = φ₀ ⁻¹' {0} := by
      ext m; simp
    rw [hset]
    exact (isOpen_discrete ({0} : Set (O ⧸ maximalIdeal O))).preimage φ₀.continuous
  let tower : (n : ℕ) → TowerStep n :=
    Nat.rec ⟨e₀.toLinearMap.comp φ₀.toLinearMap, hker₀⟩ fun n s ↦ (hstep n s).1
  have htower_comp : ∀ (n : ℕ) (m : M),
      Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
        ((tower (n + 1)).1 m) = (tower n).1 m :=
    fun n m ↦ (hstep n (tower n)).2 m
  -- Translate `O ⧸ (ϖ ^ (n + 1))` to `O ⧸ (maximalIdeal O ^ (n + 1) • ⊤)` and assemble via
  -- `IsAdicComplete.StrictMono.lift`.
  have heq_pow (n : ℕ) :
      Ideal.span {ϖ ^ (n + 1)} = (maximalIdeal O ^ (n + 1)) • (⊤ : Submodule O O) := by
    rw [hmax, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  let eqv (n : ℕ) :
      (O ⧸ Ideal.span {ϖ ^ (n + 1)}) ≃ₗ[O]
        (O ⧸ ((maximalIdeal O ^ (n + 1)) • (⊤ : Submodule O O))) :=
    Submodule.quotEquivOfEq _ _ (heq_pow n)
  let f (n : ℕ) : M →ₗ[O] O ⧸ ((maximalIdeal O ^ (n + 1)) • (⊤ : Submodule O O)) :=
    (eqv n).toLinearMap.comp (tower n).1
  have ha : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1
  have hf_comp : ∀ {n : ℕ},
      Submodule.factorPow (maximalIdeal O) O (ha.monotone n.le_succ) ∘ₗ f (n + 1) = f n := by
    intro n
    ext m
    dsimp only [f]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← htower_comp n m]
    generalize (tower (n + 1)).1 m = q
    exact Quotient.inductionOn' q fun _ ↦ rfl
  let Flin : M →ₗ[O] O := IsAdicComplete.StrictMono.lift (maximalIdeal O) ha f hf_comp
  have hF_mod (n : ℕ) (m : M) :
      Ideal.Quotient.mk (Ideal.span {ϖ ^ (n + 1)}) (Flin m) = (tower n).1 m := by
    apply (eqv n).injective
    have hmk : eqv n (Ideal.Quotient.mk (Ideal.span {ϖ ^ (n + 1)}) (Flin m)) =
        Submodule.Quotient.mk (p := (maximalIdeal O ^ (n + 1)) • ⊤) (Flin m) := rfl
    rw [hmk, IsAdicComplete.StrictMono.mk_lift]
    rfl
  -- Continuity of `Flin` follows from openness of `ker (tower n).1` and the adic basis on `O`.
  have hF_cont : Continuous Flin := by
    refine continuous_of_continuousAt_zero Flin.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, hadic.hasBasis_nhds_zero.tendsto_right_iff]
    rintro (_ | n) -
    · exact Eventually.of_forall fun _ ↦ by simp [pow_zero]
    · refine Filter.mem_of_superset ((tower n).2.mem_nhds (zero_mem _)) fun m hm ↦ ?_
      have h0 : Ideal.Quotient.mk (Ideal.span {ϖ ^ (n + 1)}) (Flin m) = 0 := by
        rw [hF_mod n m]
        exact hm
      rw [hmax, Ideal.span_singleton_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  refine ⟨⟨Flin, hF_cont⟩, fun m ↦ ?_⟩
  apply e₀.injective
  have he₀_mk : e₀ (Ideal.Quotient.mk (maximalIdeal O) (Flin m)) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ 1}) (Flin m) := rfl
  exact he₀_mk.trans (hF_mod 0 m)

/-- The reduction `M ⧸ (maximalIdeal O • ⊤)` of a compact module over `O` is a compact module over
the discrete residue field `O ⧸ maximalIdeal O`. -/
private theorem isCompactModule_quotient_maximalIdeal_smul_top {M : Type v} [AddCommGroup M]
    [Module O M] [TopologicalSpace M] (hM : IsCompactModule O M) :
    IsCompactModule (O ⧸ maximalIdeal O) (M ⧸ ((maximalIdeal O) • (⊤ : Submodule O M))) := by
  have := (IsLocalRing.isAdic_maximalIdeal O).discreteTopology_quotient
  have hclosed₀ : IsClosed (((maximalIdeal O) • (⊤ : Submodule O M) : Submodule O M) : Set M) := by
    simpa [pow_one] using hM.isClosed_maximalIdeal_pow_smul_top 1
  have hM₀O := hM.quotient _ hclosed₀
  have := hM₀O.isTopologicalAddGroup
  have := hM₀O.continuousSMul
  have := hM₀O.compactSpace
  have := hM₀O.totallyDisconnectedSpace
  refine ⟨inferInstance, ⟨continuous_prod_of_discrete_left.mpr fun r ↦ ?_⟩,
    inferInstance, inferInstance⟩
  exact Quotient.inductionOn' r fun c ↦
    (continuous_const_smul c :
      Continuous fun x : M ⧸ ((maximalIdeal O) • (⊤ : Submodule O M)) ↦ c • x).congr
      fun x ↦ Quotient.inductionOn' x fun _ ↦ rfl

/-- **Existence of a pseudobasis.** Every profinite flat module `M : Type v` over a compact
Hausdorff discrete valuation ring `O` is topologically `O`-linearly isomorphic to a product
`I → O` for some index type `I : Type v`. -/
theorem exists_pseudobasis {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    (hM : IsProfiniteFlat O M) :
    ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.t2Space
  have hadic : IsAdic (maximalIdeal O) := IsLocalRing.isAdic_maximalIdeal O
  have := hadic.discreteTopology_quotient
  let := Ideal.Quotient.field (maximalIdeal O)
  have : CompactSpace (O ⧸ maximalIdeal O) := Quotient.compactSpace
  let M₀ := M ⧸ ((maximalIdeal O) • (⊤ : Submodule O M))
  have hM₀k : IsCompactModule (O ⧸ maximalIdeal O) M₀ :=
    isCompactModule_quotient_maximalIdeal_smul_top hM.toIsCompactModule
  obtain ⟨I, ⟨e₀⟩⟩ := hM₀k.exists_continuousLinearEquiv_pi_of_field
  -- Lift each mod-`m` coordinate functional `M → M₀ → O ⧸ m` to a continuous linear form
  -- `M →L[O] O`.
  let φ₀_k (i : I) : M₀ →L[O ⧸ maximalIdeal O] (O ⧸ maximalIdeal O) :=
    (ContinuousLinearMap.proj i).comp e₀.toContinuousLinearMap
  let φ₀ (i : I) : M →L[O] (O ⧸ maximalIdeal O) :=
    ⟨(φ₀_k i).toLinearMap.restrictScalars O ∘ₗ ((maximalIdeal O) • (⊤ : Submodule O M)).mkQ,
      (φ₀_k i).continuous.comp continuous_quot_mk⟩
  choose F hF using fun i : I ↦ hM.exists_continuousLinearMap_lift_mkQ (φ₀ i)
  let Φ : M →L[O] (I → O) :=
    ⟨LinearMap.pi fun i ↦ (F i).toLinearMap, continuous_pi fun i ↦ (F i).continuous⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hnil : ∀ a ∈ maximalIdeal O, IsTopologicallyNilpotent a :=
    fun a ha ↦ hadic.isTopologicallyNilpotent_of_mem ha
  -- Surjectivity of `Φ` from mod-`m` surjectivity via topological Nakayama.
  have hsurj : Function.Surjective Φ.toLinearMap := by
    refine LinearMap.surjective_of_surjective_comp_mkQ_of_compactSpace
      (IsNoetherian.noetherian (maximalIdeal O)) hnil Φ.toLinearMap Φ.continuous ?_
    intro q
    refine Quotient.inductionOn' q fun x ↦ ?_
    obtain ⟨y₀, hy₀⟩ := e₀.surjective (fun i : I ↦ Ideal.Quotient.mk (maximalIdeal O) (x i))
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ y₀
    refine ⟨m, (Submodule.Quotient.eq _).mpr ?_⟩
    have hcoord : ∀ i : I, ∃ c : O, Φ m i - x i = ϖ * c := fun i ↦ by
      have hmk : Ideal.Quotient.mk (maximalIdeal O) (Φ m i) =
          Ideal.Quotient.mk (maximalIdeal O) (x i) :=
        (hF i m).trans (congr_fun hy₀ i)
      have hmem : Φ m i - x i ∈ Ideal.span {ϖ} :=
        hmax ▸ Ideal.Quotient.eq.mp hmk
      exact Ideal.mem_span_singleton.mp hmem
    choose c hc using hcoord
    rw [hmax, Submodule.ideal_span_singleton_smul]
    exact ⟨c, Submodule.mem_top, funext fun i ↦ (hc i).symm⟩
  -- Injectivity of `Φ` via `ker Φ ≤ m • ker Φ` and topological Nakayama on the compact kernel.
  have hinj : Function.Injective Φ.toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    have hker_closed : IsClosed (LinearMap.ker Φ.toLinearMap : Set M) := by
      have hset : (LinearMap.ker Φ.toLinearMap : Set M) = Φ ⁻¹' {0} := by ext m; simp
      rw [hset]
      exact isClosed_singleton.preimage Φ.continuous
    refine Submodule.eq_bot_of_le_smul_of_isCompact (IsNoetherian.noetherian (maximalIdeal O)) hnil
      hker_closed.isCompact fun m hm ↦ ?_
    have hm_zero : ∀ i : I, F i m = 0 := fun i ↦ congr_fun hm i
    have he₀_zero : e₀ (((maximalIdeal O) • (⊤ : Submodule O M)).mkQ m) = 0 := by
      ext i
      have hi := hF i m
      rw [hm_zero i, map_zero] at hi
      exact hi.symm
    have hm_smul : m ∈ Ideal.span ({ϖ} : Set O) • (⊤ : Submodule O M) := by
      rw [← hmax]
      exact (Submodule.Quotient.mk_eq_zero _).mp (e₀.injective (he₀_zero.trans e₀.map_zero.symm))
    rw [Submodule.ideal_span_singleton_smul] at hm_smul
    obtain ⟨m', -, hm'⟩ := hm_smul
    have hm'_ker : m' ∈ LinearMap.ker Φ.toLinearMap := by
      rw [LinearMap.mem_ker]
      ext i
      have hmul : ϖ * Φ m' i = 0 := by
        have hΦm : Φ (ϖ • m') i = 0 := by
          have hm_eq : ϖ • m' = m := hm'
          rw [hm_eq]
          exact congr_fun hm i
        simpa [Φ] using hΦm
      exact (mul_eq_zero.mp hmul).resolve_left hϖ.ne_zero
    rw [hmax, Submodule.ideal_span_singleton_smul]
    exact ⟨m', hm'_ker, hm'⟩
  let e := LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩
  exact ⟨I, ⟨{ toLinearEquiv := e
               continuous_toFun := Φ.continuous
               continuous_invFun :=
                 Φ.continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }⟩⟩

/-- **Characterization of profinite flat modules by pseudobases.** Over a compact Hausdorff discrete
valuation ring `O`, a topological `O`-module `M : Type v` is profinite flat if and only if it is
topologically `O`-linearly isomorphic to `I → O` for some `I : Type v`. -/
theorem iff_exists_pseudobasis {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M] :
    IsProfiniteFlat O M ↔ ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) :=
  ⟨fun hM ↦ hM.exists_pseudobasis,
    fun ⟨I, ⟨e⟩⟩ ↦ (pi_self_of_isDiscreteValuationRing O I).of_continuousLinearEquiv e.symm⟩

section PowerSeries

open scoped MvPowerSeries.WithPiTopology PowerSeries.WithPiTopology

variable (O)

/-- With the coefficientwise product topology, multivariate formal power series `MvPowerSeries σ O`
over a compact Hausdorff discrete valuation ring `O` form a profinite flat `O`-module. -/
theorem mvPowerSeries (σ : Type*) : IsProfiniteFlat O (MvPowerSeries σ O) :=
  (pi_self_of_isDiscreteValuationRing O (σ →₀ ℕ)).of_continuousLinearEquiv
    (MvPowerSeries.WithPiTopology.continuousLinearEquivPi σ O).symm

/-- With the coefficientwise product topology, formal power series `PowerSeries O` over a compact
Hausdorff discrete valuation ring `O` form a profinite flat `O`-module. -/
theorem powerSeries : IsProfiniteFlat O (PowerSeries O) :=
  (pi_self_of_isDiscreteValuationRing O ℕ).of_continuousLinearEquiv
    (PowerSeries.WithPiTopology.continuousLinearEquivPi O).symm

end PowerSeries

end DiscreteValuationRing

end TauCeti.IsProfiniteFlat

namespace TauCeti

section NonExamples

/-- Over a compact Hausdorff noetherian local ring `R`, the residue field `R ⧸ maximalIdeal R` with
its quotient topology is a compact `R`-module. -/
theorem IsCompactModule.quotient_maximalIdeal (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R] :
    IsCompactModule R (R ⧸ maximalIdeal R) :=
  (IsCompactModule.self_of_isLocalRing R).quotient (maximalIdeal R)
    (by simpa [pow_one] using (IsLocalRing.isAdic_maximalIdeal R).isClosed_pow 1)

/-- For any nonzero proper ideal `I` of an integral domain `R`, the quotient `R ⧸ I` is not
profinite flat over `R` (for any topologies on `R` and `R ⧸ I`). -/
theorem not_isProfiniteFlat_quotient_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] {I : Ideal R} (hI_bot : I ≠ ⊥) (hI_top : I ≠ ⊤)
    [TopologicalSpace (R ⧸ I)] : ¬ IsProfiniteFlat R (R ⧸ I) := by
  intro h
  have := h.isTorsionFree
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI_bot
  have hsmul : a • (1 : R ⧸ I) = 0 := by
    simpa [Algebra.smul_def] using Ideal.Quotient.eq_zero_iff_mem.mpr haI
  have hone : (1 : R ⧸ I) = 0 :=
    (smul_eq_zero_iff_right ha0).mp hsmul
  exact hI_top (Ideal.eq_top_of_isUnit_mem I (Ideal.Quotient.eq_zero_iff_mem.mp hone) isUnit_one)

/-- Over a discrete valuation ring `O`, the residue field `O ⧸ maximalIdeal O` is not profinite
flat (even though it is a compact `O`-module when `O` is compact and Hausdorff). -/
theorem not_isProfiniteFlat_quotient_maximalIdeal (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (O ⧸ maximalIdeal O)] :
    ¬ IsProfiniteFlat O (O ⧸ maximalIdeal O) :=
  not_isProfiniteFlat_quotient_of_ne_bot (IsDiscreteValuationRing.not_a_field O)
    (maximalIdeal.isMaximal O).ne_top

/-- An integral domain `R` that is not a field (for instance any discrete valuation ring) equipped
with the discrete topology is not profinite flat over itself. -/
theorem not_isProfiniteFlat_self_of_discreteTopology {R : Type*} [CommRing R] [IsDomain R]
    [TopologicalSpace R] [DiscreteTopology R] (hnotfield : ¬ IsField R) :
    ¬ IsProfiniteFlat R R := by
  intro h
  have := h.compactSpace
  have : Finite R := finite_of_compact_of_discrete
  obtain ⟨a, ha0, haU⟩ : ∃ a : R, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra! hall
    exact hnotfield ⟨exists_pair_ne R, mul_comm, fun {x} hx ↦
      let ⟨u, hu⟩ := hall x hx
      ⟨↑u⁻¹, hu ▸ u.mul_inv⟩⟩
  have hunit_of_pow_eq : ∀ {m k : ℕ}, a ^ m = a ^ (m + k + 1) → False := fun {m k} hmk ↦ by
    have h1 : a ^ m * 1 = a ^ m * (a * a ^ k) :=
      calc
        a ^ m * 1 = a ^ (m + k + 1) := by rw [mul_one, hmk]
        _ = a ^ m * (a * a ^ k) := by ring
    exact haU (isUnit_iff_exists_inv.mpr ⟨a ^ k, (mul_left_cancel₀ (pow_ne_zero m ha0) h1).symm⟩)
  have hinj : Function.Injective (fun n : ℕ ↦ a ^ n) := by
    intro m n hmn
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      exact (hunit_of_pow_eq hmn).elim
    · rfl
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      exact (hunit_of_pow_eq hmn.symm).elim
  exact (Infinite.of_injective _ hinj).false

/-- Over a compact Hausdorff discrete valuation ring `O`, its fraction field `K` is never profinite
flat over `O` for any topology on `K` (despite being flat over `O`). -/
theorem not_isProfiniteFlat_of_isFractionRing (O K : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    [T2Space O] [Field K] [Algebra O K] [IsFractionRing O K] [TopologicalSpace K] :
    ¬ IsProfiniteFlat O K := by
  intro hK
  have := hK.isTopologicalAddGroup
  have := hK.continuousSMul
  have := hK.compactSpace
  have := hK.t2Space
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hnil : ∀ a ∈ Ideal.span ({ϖ} : Set O), IsTopologicallyNilpotent a := by
    rw [← hϖ.maximalIdeal_eq]
    exact fun a ha ↦ (IsLocalRing.isAdic_maximalIdeal O).isTopologicallyNilpotent_of_mem ha
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff (algebraMap O K) (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  have htop_le : (⊤ : Submodule O K) ≤ Ideal.span ({ϖ} : Set O) • (⊤ : Submodule O K) := by
    rw [Submodule.ideal_span_singleton_smul]
    intro x _
    refine ⟨(algebraMap O K ϖ)⁻¹ * x, Submodule.mem_top, ?_⟩
    simp [Algebra.smul_def, mul_inv_cancel_left₀ hϖK]
  have hbot : (⊤ : Submodule O K) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_isCompact (Submodule.fg_span_singleton ϖ) hnil
      isCompact_univ htop_le
  have h10 : (1 : K) = 0 := (Submodule.mem_bot O).mp (hbot ▸ Submodule.mem_top)
  exact one_ne_zero h10

/-- A nontrivial module `M` equipped with the indiscrete topology is never profinite flat over any
commutative ring `R` (even though it is compact, linearly topologized, and flat when `M = R`). -/
theorem not_isProfiniteFlat_of_indiscreteTopology {R M : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IndiscreteTopology M] [Nontrivial M] :
    ¬ IsProfiniteFlat R M := by
  intro hM
  have := hM.t2Space
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  obtain ⟨U, V, hU, hV, hxU, hyV, hdisj⟩ := t2_separation hxy
  rcases (IndiscreteTopology.isOpen_iff U).mp hU with rfl | rfl
  · exact hxU
  · rcases (IndiscreteTopology.isOpen_iff V).mp hV with rfl | rfl
    · exact hyV
    · exact Set.disjoint_iff.mp hdisj ⟨hxU, hyV⟩

/-- A nontrivial module `M` equipped with the indiscrete topology admits no continuous linear
equivalence `M ≃L[R] (I → R)` over a `T₂` ring `R` (even when `M` is compact, linearly
topologized, and flat). -/
theorem isEmpty_continuousLinearEquiv_pi_of_indiscreteTopology {R M : Type*} (I : Type*)
    [Ring R] [TopologicalSpace R] [T2Space R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IndiscreteTopology M] [Nontrivial M] :
    IsEmpty (M ≃L[R] (I → R)) := by
  refine ⟨fun e ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  obtain ⟨U, V, hU, hV, hxU, hyV, hdisj⟩ := t2_separation (e.injective.ne hxy)
  rcases (IndiscreteTopology.isOpen_iff (e ⁻¹' U)).mp (hU.preimage e.continuous) with heU | _
  · exact Set.eq_empty_iff_forall_notMem.mp heU x hxU
  · rcases (IndiscreteTopology.isOpen_iff (e ⁻¹' V)).mp (hV.preimage e.continuous) with heV | heV
    · exact Set.eq_empty_iff_forall_notMem.mp heV y hyV
    · have hxV : e x ∈ V := Set.eq_univ_iff_forall.mp heV x
      exact Set.disjoint_iff.mp hdisj ⟨hxU, hxV⟩

end NonExamples

end TauCeti
