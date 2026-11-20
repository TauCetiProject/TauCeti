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
public import Mathlib.Topology.Order
public import TauCeti.RingTheory.MvPowerSeries.PiTopology
public import TauCeti.RingTheory.PowerSeries.PiTopology
public import TauCeti.Topology.Algebra.Ring.Compact
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.RingTheory.AdicCompletion.Topology
import TauCeti.RingTheory.Flat.Pi
import TauCeti.RingTheory.Ideal.Quotient.Pi
import TauCeti.RingTheory.Ideal.Quotient.PowTransition
import TauCeti.Topology.Algebra.Module.LinearTopology.CompactVectorSpace
import TauCeti.Topology.Algebra.Module.Nakayama

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
* `ContinuousLinearEquiv.submodulePiPow`,
  `ContinuousLinearEquiv.hasBasis_nhds_zero_submodulePiPow`: for `e : M ≃L[R] (I → R)` over a ring
  whose topology is `J`-adic, the submodules `{m | ∀ i ∈ s, e m i ∈ J ^ n}` (`s : Finset I`,
  `n : ℕ`) are open and form a neighbourhood basis of `0` in `M`.
* `TauCeti.IsProfiniteFlat.exists_continuousLinearMap_mk_maximalIdeal_eq`: over a compact Hausdorff
  discrete valuation ring `O`, every continuous `O`-linear map `M →L[O] (O ⧸ maximalIdeal O)` lifts
  to a continuous `O`-linear map `M →L[O] O`.
* `TauCeti.IsProfiniteFlat.exists_pseudobasis`,
  `TauCeti.IsProfiniteFlat.iff_exists_pseudobasis`: over a compact Hausdorff discrete valuation
  ring `O`, a topological `O`-module `M : Type v` is profinite flat if and only if
  `∃ I : Type v, Nonempty (M ≃L[O] (I → O))`.
* `TauCeti.IsProfiniteFlat.mvPowerSeries`, `TauCeti.IsProfiniteFlat.powerSeries`: over a Dedekind
  domain `R`, formal power series `MvPowerSeries σ S` and `PowerSeries S` over any profinite flat
  `R`-module ring `S`, equipped with the product topology on coefficients, are profinite flat
  `R`-modules.
* Separation of the hypotheses: `not_isProfiniteFlat_quotient_maximalIdeal` (compact, not flat),
  `not_isProfiniteFlat_self_of_discreteTopology` (flat, discrete, not compact),
  `not_isProfiniteFlat_of_isFractionRing` (fraction field, not profinite flat for any topology),
  and `not_isProfiniteFlat_of_indiscreteTopology` /
  `isEmpty_continuousLinearEquiv_pi_of_indiscreteTopology` (compact, linearly topologized, flat,
  not Hausdorff).

## References

* [P. Chojecki, D. Hansen, C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*], Doc. Math. 22 (2017), 1915–1962, §6.1, Definition 6.1 and Proposition 6.2.
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
def submodulePiPow (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) (n : ℕ) :
    Submodule R M :=
  (Submodule.pi (s : Set I) fun _ ↦ J ^ n).comap e.toLinearMap

theorem submodulePiPow_def (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) (n : ℕ) :
    e.submodulePiPow J s n = (Submodule.pi (s : Set I) fun _ ↦ J ^ n).comap e.toLinearMap := by
  rfl

@[simp, grind =]
theorem mem_submodulePiPow_iff (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) (n : ℕ)
    (m : M) : m ∈ e.submodulePiPow J s n ↔ ∀ i ∈ s, e m i ∈ J ^ n := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_empty (e : M ≃L[R] (I → R)) (J : Ideal R) (n : ℕ) :
    e.submodulePiPow J ∅ n = ⊤ := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_zero (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) :
    e.submodulePiPow J s 0 = ⊤ := by
  simp [submodulePiPow_def]

@[simp, grind =]
theorem submodulePiPow_union [DecidableEq I] (e : M ≃L[R] (I → R)) (J : Ideal R)
    (s₁ s₂ : Finset I) (n : ℕ) :
    e.submodulePiPow J (s₁ ∪ s₂) n = e.submodulePiPow J s₁ n ⊓ e.submodulePiPow J s₂ n := by
  ext m
  simp [or_imp, forall_and]

@[simp, grind =]
theorem map_submodulePiPow (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) (n : ℕ) :
    (e.submodulePiPow J s n).map e.toLinearMap = Submodule.pi (s : Set I) fun _ ↦ J ^ n := by
  rw [submodulePiPow_def]
  exact Submodule.map_comap_eq_of_surjective e.surjective _

/-- `e.submodulePiPow J s n` is antitone in both the finite coordinate set `s` and the exponent
`n`. -/
theorem submodulePiPow_anti (e : M ≃L[R] (I → R)) (J : Ideal R) {s₁ s₂ : Finset I} {n₁ n₂ : ℕ}
    (hs : s₁ ⊆ s₂) (hn : n₁ ≤ n₂) :
    e.submodulePiPow J s₂ n₂ ≤ e.submodulePiPow J s₁ n₁ := by
  intro m hm
  rw [mem_submodulePiPow_iff] at hm ⊢
  exact fun i hi ↦ Ideal.pow_le_pow_right hn (hm i (hs hi))

/-- `e.submodulePiPow J s n` is antitone in the finite coordinate set `s`. -/
theorem submodulePiPow_left_antitone (e : M ≃L[R] (I → R)) (J : Ideal R) (n : ℕ) :
    Antitone (fun s : Finset I ↦ e.submodulePiPow J s n) :=
  fun _ _ hs ↦ e.submodulePiPow_anti J hs le_rfl

/-- `e.submodulePiPow J s n` is antitone in the exponent `n`. -/
theorem submodulePiPow_right_antitone (e : M ≃L[R] (I → R)) (J : Ideal R) (s : Finset I) :
    Antitone (e.submodulePiPow J s) :=
  fun _ _ hn ↦ e.submodulePiPow_anti J Finset.Subset.rfl hn

/-- When the topology of `R` is `J`-adic, each coordinate congruence submodule
`e.submodulePiPow J s n` is open in `M`. -/
theorem isOpen_submodulePiPow (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J)
    (s : Finset I) (n : ℕ) : IsOpen (e.submodulePiPow J s n : Set M) := by
  rw [submodulePiPow_def, Submodule.comap_coe, Submodule.coe_pi,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  exact (isOpen_set_pi s.finite_toSet fun _ _ ↦ hJ.isOpen_pow n).preimage e.continuous

/-- **Neighbourhood basis from a pseudobasis.** If `e : M ≃L[R] (I → R)` and the topology of `R`
is `J`-adic, then the open submodules `e.submodulePiPow J s n` (`s : Finset I`, `n : ℕ`) form a
basis of neighbourhoods of `0` in `M`. -/
theorem hasBasis_nhds_zero_submodulePiPow (e : M ≃L[R] (I → R)) {J : Ideal R} (hJ : IsAdic J) :
    (𝓝 (0 : M)).HasBasis (fun _ : Finset I × ℕ ↦ True)
      (fun p ↦ (e.submodulePiPow J p.1 p.2 : Set M)) := by
  rw [hasBasis_iff]
  intro W
  refine ⟨fun hW ↦ ?_, fun ⟨⟨s, n⟩, _, hsub⟩ ↦
    mem_of_superset ((e.isOpen_submodulePiPow hJ s n).mem_nhds (zero_mem _)) hsub⟩
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
  rw [SetLike.mem_coe, mem_submodulePiPow_iff] at hm
  have hem : e m ∈ (s : Set I).pi t := fun i hi ↦
    hk i (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_coe.mp hi))
      (hm i (Finset.mem_coe.mp hi)))
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

@[grind =]
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

/-- A compact Hausdorff commutative ring whose topology is `I`-adic is profinite flat over
itself. -/
theorem self_of_isAdic [CompactSpace R] [T2Space R] {I : Ideal R} (hI : IsAdic I) :
    IsProfiniteFlat R R :=
  ⟨.self_of_isAdic hI, inferInstance⟩

/-- Any subsingleton topological `R`-module is profinite flat. -/
theorem of_subsingleton [Subsingleton M] : IsProfiniteFlat R M :=
  ⟨.of_subsingleton, inferInstance⟩

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

section PowerSeries

open scoped MvPowerSeries.WithPiTopology PowerSeries.WithPiTopology

/-- Over a Dedekind domain `R`, multivariate formal power series `MvPowerSeries σ S` with
coefficients in a profinite flat `R`-module ring `S`, equipped with the coefficientwise product
topology, form a profinite flat `R`-module. -/
theorem mvPowerSeries {S : Type*} [Ring S] [Module R S] [TopologicalSpace S]
    (hS : IsProfiniteFlat R S) (σ : Type*) : IsProfiniteFlat R (MvPowerSeries σ S) :=
  (pi fun _ : σ →₀ ℕ ↦ hS).of_continuousLinearEquiv
    (MvPowerSeries.WithPiTopology.continuousLinearEquivPi σ R S).symm

/-- Over a Dedekind domain `R`, formal power series `PowerSeries S` with coefficients in a
profinite flat `R`-module ring `S`, equipped with the coefficientwise product topology, form a
profinite flat `R`-module. -/
theorem powerSeries {S : Type*} [Ring S] [Module R S] [TopologicalSpace S]
    (hS : IsProfiniteFlat R S) : IsProfiniteFlat R (PowerSeries S) :=
  (pi fun _ : ℕ ↦ hS).of_continuousLinearEquiv
    (PowerSeries.WithPiTopology.continuousLinearEquivPi R S).symm

end PowerSeries

end DedekindDomain

section CompactLocalRing

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R]

/-- A compact Hausdorff noetherian local ring is profinite flat over itself. -/
theorem self_of_isLocalRing : IsProfiniteFlat R R :=
  self_of_isAdic (IsLocalRing.isAdic_maximalIdeal R)

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

omit [IsDiscreteValuationRing O] [IsTopologicalRing O] [T2Space O] in
/-- Given `φ : M →ₗ[O] O ⧸ (ϖ ^ (n + 1))` with open kernel on a profinite flat `O`-module `M`,
there is an open submodule `V ≤ ker φ` containing `(ϖ ^ (n + 2)) • ⊤` such that `ϖ • m ∈ V` forces
`m ∈ ker φ`. -/
private theorem exists_open_submodule_ker_of_mul {M : Type v} [AddCommGroup M] [Module O M]
    [TopologicalSpace M] (hM : IsProfiniteFlat O M) {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ V : Submodule O M,
      IsOpen (V : Set M) ∧
        Ideal.span {ϖ ^ (n + 2)} • (⊤ : Submodule O M) ≤ V ∧
          V ≤ LinearMap.ker φ ∧
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
  -- Intersect `V₀` with `ker φ` and enlarge by `J₂ • ⊤`.
  let V₁ : Submodule O M := V₀ ⊓ LinearMap.ker φ
  let V : Submodule O M := V₁ ⊔ (J₂ • (⊤ : Submodule O M))
  have hV_open : IsOpen (V : Set M) :=
    AddSubgroup.isOpen_mono (H₁ := V₁.toAddSubgroup) (H₂ := V.toAddSubgroup)
      (fun _ hx ↦ Submodule.mem_sup_left hx) (hV₀_open.inter hker)
  have hJ₁_ker : J₁ • (⊤ : Submodule O M) ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  have hJ₂_J₁ : J₂ ≤ J₁ :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1)))
  refine ⟨V, hV_open, le_sup_right,
    sup_le inf_le_right ((Submodule.smul_mono_left hJ₂_J₁).trans hJ₁_ker), fun {m} hm ↦ ?_⟩
  obtain ⟨v₁, hv₁, y, hy, heq⟩ := Submodule.mem_sup.mp hm
  have hy' : y ∈ Ideal.span ({ϖ} : Set O) • (J₁ • (⊤ : Submodule O M)) := by
    have hJ₂_eq : J₂ = Ideal.span ({ϖ} : Set O) * J₁ := by
      simp [J₁, J₂, Ideal.span_singleton_mul_span_singleton, pow_succ']
    simpa [hJ₂_eq, mul_smul] using hy
  rw [Submodule.ideal_span_singleton_smul] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  have hmz : m - z ∈ LinearMap.ker φ := hV₀_ker (by
    have : ϖ • (m - z) = v₁ := by simp [smul_sub, ← heq]
    exact this ▸ hv₁.1)
  simpa using add_mem hmz (hJ₁_ker hz)

omit [IsDiscreteValuationRing O] [IsTopologicalRing O] [T2Space O] in
/-- One-step lifting of continuous `O`-linear functionals along `(ϖ ^ (n + 2)) → (ϖ ^ (n + 1))`:
an `O`-linear map `φ : M →ₗ[O] O ⧸ (ϖ ^ (n + 1))` with open kernel on a profinite flat `O`-module
lifts to `φ' : M →ₗ[O] O ⧸ (ϖ ^ (n + 2))` with open kernel. -/
private theorem exists_lift_span_pow_succ [IsPrincipalIdealRing O] {M : Type v} [AddCommGroup M]
    [Module O M] [TopologicalSpace M] (hM : IsProfiniteFlat O M) {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ φ' : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 2)},
      IsOpen (LinearMap.ker φ' : Set M) ∧
        ∀ m : M,
          Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
            (φ' m) = φ m := by
  have := hM.isTopologicalAddGroup
  let J₂ : Ideal O := Ideal.span {ϖ ^ (n + 2)}
  obtain ⟨V, hV_open, hJ₂_le, hV_le_ker, hV_ker⟩ :=
    hM.exists_open_submodule_ker_of_mul hϖ n φ hker
  -- Equip `M ⧸ V` with its `(O ⧸ J₂)`-module structure and extend via Baer's criterion on `O ⧸ J₂`.
  have htor : Module.IsTorsionBySet O (M ⧸ V) J₂ :=
    (Module.isTorsionBySet_quotient_iff V J₂).mpr fun _ _ hr ↦
      hJ₂_le (Submodule.smul_mem_smul hr Submodule.mem_top)
  let := htor.module
  have : IsScalarTower O (O ⧸ J₂) (M ⧸ V) := htor.isScalarTower
  let β : M →ₗ[O] (O ⧸ J₂) := (Ideal.Quotient.mulSpanPowSucc ϖ (n + 1)).comp φ
  let βbar : (M ⧸ V) →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    (V.liftQ β (hV_le_ker.trans (LinearMap.ker_le_ker_comp φ _))).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let μ : (M ⧸ V) →ₗ[O ⧸ J₂] (M ⧸ V) := LinearMap.lsmul (O ⧸ J₂) (M ⧸ V) (Ideal.Quotient.mk J₂ ϖ)
  have hker_μ : LinearMap.ker μ.rangeRestrict ≤ LinearMap.ker βbar := by
    intro x hx
    obtain ⟨m, rfl⟩ := V.mkQ_surjective x
    have hμ0 : V.mkQ (ϖ • m) = 0 := by
      simpa [μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using
        congr_arg Subtype.val (LinearMap.mem_ker.mp hx)
    have hm_ker : φ m = 0 :=
      LinearMap.mem_ker.mp (hV_ker ((Submodule.Quotient.mk_eq_zero V).mp hμ0))
    simp [LinearMap.mem_ker, βbar, β, hm_ker]
  let ψ₀ : LinearMap.range μ →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    (μ.rangeRestrict.liftOfSurjective μ.surjective_rangeRestrict) ⟨βbar, hker_μ⟩
  obtain ⟨ψ, hψ⟩ :=
    (Module.Baer.quotient_span_singleton_self (pow_ne_zero (n + 2) hϖ)).extension_property
      (LinearMap.range μ).subtype (LinearMap.range μ).injective_subtype ψ₀
  let φ' : M →ₗ[O] (O ⧸ J₂) := (ψ.restrictScalars O).comp V.mkQ
  refine ⟨φ', AddSubgroup.isOpen_mono (H₁ := V.toAddSubgroup)
    (H₂ := (LinearMap.ker φ').toAddSubgroup)
    (fun m hm ↦ by simp [φ', (Submodule.Quotient.mk_eq_zero V).mpr hm]) hV_open, fun m ↦ ?_⟩
  apply Ideal.Quotient.mulSpanPowSucc_injective (mul_right_injective₀ hϖ) (n + 1)
  rw [Ideal.Quotient.mulSpanPowSucc_factor, ← map_smul]
  calc
    φ' (ϖ • m) = (ψ.comp (LinearMap.range μ).subtype) (μ.rangeRestrict (V.mkQ m)) := by
      simp [φ', μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    _ = ψ₀ (μ.rangeRestrict (V.mkQ m)) := by rw [hψ]
    _ = Ideal.Quotient.mulSpanPowSucc ϖ (n + 1) (φ m) := by simp [ψ₀, βbar, β]

/-- **Continuous linear functionals lift modulo the maximal ideal.** Over a compact Hausdorff
discrete valuation ring `O`, every continuous `O`-linear map `φ₀ : M →L[O] (O ⧸ maximalIdeal O)`
from a profinite flat `O`-module `M` lifts to a continuous `O`-linear map `F : M →L[O] O`. -/
theorem exists_continuousLinearMap_mk_maximalIdeal_eq {M : Type v} [AddCommGroup M] [Module O M]
    [TopologicalSpace M] (hM : IsProfiniteFlat O M) (φ₀ : M →L[O] (O ⧸ maximalIdeal O)) :
    ∃ F : M →L[O] O, ∀ m : M, Ideal.Quotient.mk (maximalIdeal O) (F m) = φ₀ m := by
  have := hM.isTopologicalAddGroup
  have hadic : IsAdic (maximalIdeal O) := IsLocalRing.isAdic_maximalIdeal O
  have := hadic.discreteTopology_quotient
  have : IsAdicComplete (maximalIdeal O) O :=
    IsLocalRing.isAdicComplete_maximalIdeal_of_compactSpace O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  let TowerStep (n : ℕ) :=
    { g : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)} // IsOpen (LinearMap.ker g : Set M) }
  have hstep : ∀ n (s : TowerStep n),
      { g' : TowerStep (n + 1) //
        ∀ m, Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
          (g'.val m) = s.val m } := fun n s ↦ by
    choose g' hg'_open hg'_comp using hM.exists_lift_span_pow_succ hϖ.ne_zero n s.val s.property
    exact ⟨⟨g', hg'_open⟩, hg'_comp⟩
  let e₀ : (O ⧸ maximalIdeal O) ≃ₗ[O] (O ⧸ Ideal.span {ϖ ^ 1}) :=
    Submodule.quotEquivOfEq _ _ (by rw [hmax, pow_one])
  have hker₀ : IsOpen (LinearMap.ker (e₀.toLinearMap.comp φ₀.toLinearMap) : Set M) := by
    convert (isOpen_discrete ({0} : Set (O ⧸ maximalIdeal O))).preimage φ₀.continuous
    ext m; simp
  let tower : (n : ℕ) → TowerStep n :=
    Nat.rec ⟨e₀.toLinearMap.comp φ₀.toLinearMap, hker₀⟩ fun n s ↦ (hstep n s).val
  have htower0 : (tower 0).val = e₀.toLinearMap.comp φ₀.toLinearMap := rfl
  have hK (n : ℕ) : Ideal.span {ϖ ^ (n + 1)} = (maximalIdeal O) ^ (id n + 1) := by
    rw [hmax, id_eq, Ideal.span_singleton_pow]
  let F : M →L[O] O := hadic.liftIdealTower (strictMono_id.add_const 1) hK (fun n ↦ (tower n).val)
    (fun n ↦ (tower n).property) (fun n m ↦ (hstep n (tower n)).property m)
  refine ⟨F, fun m ↦ e₀.injective ?_⟩
  calc
    e₀ (Ideal.Quotient.mk (maximalIdeal O) (F m))
      = Ideal.Quotient.mk (Ideal.span {ϖ ^ 1}) (F m) := Submodule.quotEquivOfEq_ideal_mk _ _
    _ = (tower 0).val m := hadic.mk_liftIdealTower _ hK _ _ _ 0 m
    _ = e₀ (φ₀ m) := by
        rw [htower0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ContinuousLinearMap.coe_coe]

/-- **Existence of a pseudobasis.** Every profinite flat module `M : Type v` over a compact
Hausdorff discrete valuation ring `O` is topologically `O`-linearly isomorphic to a product
`I → O` for some index type `I : Type v`. -/
theorem exists_pseudobasis {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    (hM : IsProfiniteFlat O M) :
    ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) := by
  have := hM.isTopologicalAddGroup
  have := (IsLocalRing.isAdic_maximalIdeal O).discreteTopology_quotient
  let := Ideal.Quotient.field (maximalIdeal O)
  have : CompactSpace (O ⧸ maximalIdeal O) := Quotient.compactSpace
  let M₀ := M ⧸ ((maximalIdeal O) • (⊤ : Submodule O M))
  obtain ⟨I, ⟨e₀⟩⟩ :=
    hM.toIsCompactModule.quotient_maximalIdeal_smul_top.exists_continuousLinearEquiv_pi_of_field
  -- Lift each mod-`m` coordinate functional `M → M₀ → O ⧸ m` to `M →L[O] O`.
  let φ₀_k (i : I) : M₀ →L[O ⧸ maximalIdeal O] (O ⧸ maximalIdeal O) :=
    (ContinuousLinearMap.proj i).comp e₀.toContinuousLinearMap
  let φ₀ (i : I) : M →L[O] (O ⧸ maximalIdeal O) :=
    ⟨(φ₀_k i).toLinearMap.restrictScalars O ∘ₗ ((maximalIdeal O) • (⊤ : Submodule O M)).mkQ,
      (φ₀_k i).continuous.comp continuous_quot_mk⟩
  have hφ₀ (i : I) (m : M) : φ₀ i m = e₀ (Submodule.Quotient.mk m) i := by
    simp [φ₀, φ₀_k, M₀]
  choose F hF using fun i : I ↦ hM.exists_continuousLinearMap_mk_maximalIdeal_eq (φ₀ i)
  let Φ : M →L[O] (I → O) := ContinuousLinearMap.pi F
  -- Identify the mod-`m` reduction of `Φ` with `e₀` via coordinatewise reduction on `I → O`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ_inj : Function.Injective ((maximalIdeal O).quotPiSMulTopToPiQuot I) :=
    ((isNoetherianRing_iff_ideal_fg O).mp inferInstance
      (maximalIdeal O)).quotPiSMulTopToPiQuot_injective I
  let Φbar := Submodule.mapQ ((maximalIdeal O) • ⊤) ((maximalIdeal O) • ⊤) Φ.toLinearMap
    (Submodule.smul_top_le_comap_smul_top (maximalIdeal O) Φ.toLinearMap)
  have hπΦ (y₀ : M₀) : (maximalIdeal O).quotPiSMulTopToPiQuot I (Φbar y₀) = e₀ y₀ := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y₀
    ext i
    dsimp only [Φbar]
    rw [Submodule.mapQ_apply, Ideal.quotPiSMulTopToPiQuot_mk, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.pi_apply, hF i m, hφ₀]
  have hϖ_nil : IsTopologicallyNilpotent ϖ :=
    (IsLocalRing.isAdic_maximalIdeal O).isTopologicallyNilpotent_of_mem
      (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
  have hϖ_reg : IsSMulRegular (I → O) ϖ := smul_right_injective (I → O) hϖ.ne_zero
  refine ⟨I, ⟨hM.toIsCompactModule.continuousLinearEquivOfBijectiveMapQ
    (pi_self_of_isDiscreteValuationRing O I).toIsCompactModule hϖ.maximalIdeal_eq hϖ_nil hϖ_reg
    Φ ⟨?_, ?_⟩⟩⟩
  · intro y₁ y₂ hy
    exact e₀.injective ((hπΦ y₁).symm.trans
      ((congr_arg ((maximalIdeal O).quotPiSMulTopToPiQuot I) hy).trans (hπΦ y₂)))
  · intro z
    obtain ⟨y₀, hy₀⟩ := e₀.surjective ((maximalIdeal O).quotPiSMulTopToPiQuot I z)
    exact ⟨y₀, hπ_inj ((hπΦ y₀).trans hy₀)⟩

/-- **Characterization of profinite flat modules by pseudobases.** Over a compact Hausdorff discrete
valuation ring `O`, a topological `O`-module `M : Type v` is profinite flat if and only if it is
topologically `O`-linearly isomorphic to `I → O` for some `I : Type v`. -/
theorem iff_exists_pseudobasis {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M] :
    IsProfiniteFlat O M ↔ ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) :=
  ⟨fun hM ↦ hM.exists_pseudobasis,
    fun ⟨I, ⟨e⟩⟩ ↦ (pi_self_of_isDiscreteValuationRing O I).of_continuousLinearEquiv e.symm⟩

end DiscreteValuationRing

end TauCeti.IsProfiniteFlat

namespace TauCeti

section NonExamples

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
  exact hnotfield (Finite.isField_of_domain R)

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
theorem not_isProfiniteFlat_of_indiscreteTopology (R M : Type*) [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IndiscreteTopology M] [Nontrivial M] :
    ¬ IsProfiniteFlat R M := by
  intro hM
  have := hM.t2Space
  have := subsingleton_iff_indiscreteTopology.mpr ‹IndiscreteTopology M›
  exact false_of_nontrivial_of_subsingleton M

/-- A nontrivial module `M` equipped with the indiscrete topology admits no continuous linear
equivalence `M ≃L[R] (I → R)` over a `T₂` ring `R` (even when `M` is compact, linearly
topologized, and flat). -/
theorem isEmpty_continuousLinearEquiv_pi_of_indiscreteTopology (R M I : Type*)
    [Ring R] [TopologicalSpace R] [T2Space R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IndiscreteTopology M] [Nontrivial M] :
    IsEmpty (M ≃L[R] (I → R)) := by
  refine ⟨fun e ↦ ?_⟩
  have := T2Space.of_injective_continuous e.injective e.continuous
  have := subsingleton_iff_indiscreteTopology.mpr ‹IndiscreteTopology M›
  exact false_of_nontrivial_of_subsingleton M

end NonExamples

end TauCeti
