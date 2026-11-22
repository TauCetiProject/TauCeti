/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.Basic
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.LocallyConstant.Basic

import Mathlib.RingTheory.AdicCompletion.Topology
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology
import TauCeti.Topology.Discrete

/-!
# Inverse-limit topology and universal property of the cyclotomic completion

`CycloCompletion R S` carries the inverse-limit topology of the polynomial-family limit
`TauCeti.PolyFamilyLimit`, induced from the product of discrete quotients
`∀ f : cycloIndex R S, AdjoinRoot (f : R[X])`; the projections are locally constant
(`TauCeti.PolyFamilyLimit.isLocallyConstant_proj`) and continuity into it is tested coordinatewise
(`TauCeti.PolyFamilyLimit.continuous_iff`). Under this topology:

* the open-and-closed principal ideals `RingHom.ker (proj f) = Ideal.span {fromPoly R S f}` form a
  neighborhood basis of `0`, making `CycloCompletion R S` a Hausdorff linearly topologized
  nonarchimedean commutative ring;
* `CycloCompletion R S` is a closed subalgebra of the discrete product and hence complete and
  separated for its canonical additive-group uniformity (`CycloCompletion.isCompleteSeparated`,
  `CycloCompletion.completeSeparatedObj`);
* when `S` is finite, the topology coincides with the adic topology of
  `Ideal.span {fromPoly R S (cycloProd R hS)}`, for which `CycloCompletion R S` is adically
  complete;
* the image of `fromPoly R S : R[X] →ₐ[R] CycloCompletion R S` is dense, approximated along the
  countable cofinal chain `cycloChainIndex R S`;
* every cyclotomically continuous ring homomorphism `ψ : R[X] →+* B` into a complete Hausdorff
  topological ring `B` (not assumed commutative) extends uniquely to a continuous ring homomorphism
  `CycloCompletion R S →+* B` (`TauCeti.CycloCompletion.existsUnique_continuous_comp_fromPoly_eq`).

## Main definitions

* `TauCeti.CycloCompletion.completeSeparatedObj`: `CycloCompletion R S` bundled in
  `TauCeti.CompleteSeparatedTopCommRingCat`.
* `TauCeti.CycloCompletion.approxPoly`: reduced polynomial approximants of `x : CycloCompletion R S`
  along `cycloChainIndex R S`.
* `TauCeti.IsCycloContinuous`: cyclotomic continuity of a ring homomorphism `ψ : R[X] →+* B`.
* `TauCeti.CycloCompletion.lift`, `TauCeti.CycloCompletion.liftAlgHom`: the continuous extension
  of a cyclotomically continuous polynomial map to `CycloCompletion R S`.

## Main results

* `TauCeti.CycloCompletion.hasBasis_nhds_zero`, `TauCeti.CycloCompletion.hasBasis_nhds_zero_span`:
  neighborhood basis of `0` given by `RingHom.ker (proj f)` / `Ideal.span {fromPoly R S f}`.
* `TauCeti.CycloCompletion.isCompleteSeparated`: completeness and separatedness of
  `CycloCompletion R S` for its group uniformity.
* `TauCeti.CycloCompletion.isAdic_span_cycloProd`,
  `TauCeti.CycloCompletion.isAdicComplete_span_cycloProd`: adic characterization and completeness
  when `S` is finite.
* `TauCeti.CycloCompletion.denseRange_fromPoly`: density of `fromPoly R S`.
* `TauCeti.CycloCompletion.existsUnique_continuous_comp_fromPoly_eq`: unique continuous extension of
  cyclotomically continuous homomorphisms out of `R[X]`.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §§3.1, 4.
-/

public section

universe u

open Filter Polynomial
open scoped Topology Uniformity TauCeti.TopCommRingCat

namespace TauCeti

namespace CycloCompletion

open PolyFamilyLimit

section InverseLimitTopology

variable {R : Type*} [CommRing R] {S : Set ℕ}

/-- Each projection kernel `RingHom.ker (proj f)` is open in `CycloCompletion R S`. -/
theorem isOpen_ker_proj (f : cycloIndex R S) :
    IsOpen (RingHom.ker (proj f : CycloCompletion R S →ₐ[R] _) : Set (CycloCompletion R S)) :=
  (isLocallyConstant_proj f).isOpen_fiber 0

/-- Each projection kernel `RingHom.ker (proj f)` is closed in `CycloCompletion R S`. -/
theorem isClosed_ker_proj (f : cycloIndex R S) :
    IsClosed (RingHom.ker (proj f : CycloCompletion R S →ₐ[R] _) : Set (CycloCompletion R S)) :=
  (isLocallyConstant_proj f).isClosed_fiber 0

/-- Each principal ideal `Ideal.span {fromPoly R S f}` (`f ∈ cycloIndex R S`) is open in
`CycloCompletion R S`. -/
theorem isOpen_span_fromPoly (f : cycloIndex R S) :
    IsOpen (Ideal.span {fromPoly R S (f : R[X])} : Set (CycloCompletion R S)) := by
  rw [← ker_proj]
  exact isOpen_ker_proj f

/-- Each principal ideal `Ideal.span {fromPoly R S f}` (`f ∈ cycloIndex R S`) is closed in
`CycloCompletion R S`. -/
theorem isClosed_span_fromPoly (f : cycloIndex R S) :
    IsClosed (Ideal.span {fromPoly R S (f : R[X])} : Set (CycloCompletion R S)) := by
  rw [← ker_proj]
  exact isClosed_ker_proj f

/-- The open ideals `RingHom.ker (proj f)` (`f : cycloIndex R S`) form a neighborhood basis of `0`
in `CycloCompletion R S`. -/
theorem hasBasis_nhds_zero (R : Type*) [CommRing R] (S : Set ℕ) :
    (𝓝 (0 : CycloCompletion R S)).HasBasis (fun _ : cycloIndex R S ↦ True)
      fun f ↦ (RingHom.ker (proj f : CycloCompletion R S →ₐ[R] _) : Set (CycloCompletion R S)) := by
  have hnhds : 𝓝 (0 : CycloCompletion R S) =
      ⨅ f : cycloIndex R S,
        𝓟 (RingHom.ker (proj f : CycloCompletion R S →ₐ[R] _) : Set (CycloCompletion R S)) := by
    rw [topologicalSpace_eq_iInf_induced, nhds_iInf]
    refine iInf_congr fun f ↦ ?_
    rw [TauCeti.nhds_induced_bot]
    congr 1
    ext x
    simp [RingHom.mem_ker]
  rw [hnhds]
  refine hasBasis_iInf_principal fun f g ↦ ⟨f * g, ?_, ?_⟩
  · rw [ker_proj, ker_proj]
    exact span_fromPoly_le_of_dvd (dvd_mul_right (f : R[X]) (g : R[X]))
  · rw [ker_proj, ker_proj]
    exact span_fromPoly_le_of_dvd (dvd_mul_left (g : R[X]) (f : R[X]))

/-- The principal ideals `Ideal.span {fromPoly R S f}` (`f : cycloIndex R S`) form a neighborhood
basis of `0` in `CycloCompletion R S`. -/
theorem hasBasis_nhds_zero_span (R : Type*) [CommRing R] (S : Set ℕ) :
    (𝓝 (0 : CycloCompletion R S)).HasBasis (fun _ : cycloIndex R S ↦ True)
      fun f ↦ (Ideal.span {fromPoly R S (f : R[X])} : Set (CycloCompletion R S)) := by
  simpa only [ker_proj] using hasBasis_nhds_zero R S

/-- Neighborhoods of `0` along the countable cofinal chain `cycloChainIndex R S` also form a basis
of `𝓝 0` in `CycloCompletion R S`. -/
theorem hasBasis_nhds_zero_cycloChain (R : Type*) [CommRing R] (S : Set ℕ) :
    (𝓝 (0 : CycloCompletion R S)).HasBasis (fun _ : ℕ ↦ True)
      fun N ↦ (RingHom.ker (proj (cycloChainIndex R S N) : CycloCompletion R S →ₐ[R] _) :
        Set (CycloCompletion R S)) := by
  refine (hasBasis_nhds_zero R S).to_hasBasis (fun f _ ↦ ?_) fun N _ ↦
    ⟨cycloChainIndex R S N, trivial, subset_rfl⟩
  obtain ⟨N, hN⟩ := exists_dvd_cycloChain f.property
  rw [← coe_cycloChainIndex] at hN
  refine ⟨N, trivial, ?_⟩
  rw [ker_proj, ker_proj]
  exact span_fromPoly_le_of_dvd hN

instance (R : Type*) [CommRing R] (S : Set ℕ) :
    IsLinearTopology (CycloCompletion R S) (CycloCompletion R S) :=
  IsLinearTopology.mk_of_hasBasis' (CycloCompletion R S) (hasBasis_nhds_zero R S)
    fun I r _ hm ↦ I.mul_mem_left r hm

instance (R : Type*) [CommRing R] (S : Set ℕ) : NonarchimedeanRing (CycloCompletion R S) :=
  IsLinearTopology.nonarchimedeanRing (CycloCompletion R S)

end InverseLimitTopology

section CompleteSeparatedAndAdic

/-- `CycloCompletion R S` is complete and separated for the canonical group uniformity of its
inverse-limit topology. -/
theorem isCompleteSeparated (R : Type u) [CommRing R] (S : Set ℕ) :
    TopCommRingCat.IsCompleteSeparated (TopCommRingCat.of (CycloCompletion R S)) :=
  TopCommRingCat.isCompleteSeparated_of_completeSpace_of_t0Space _

/-- `CycloCompletion R S` bundled as an object of `CompleteSeparatedTopCommRingCat`. -/
noncomputable def completeSeparatedObj (R : Type u) [CommRing R] (S : Set ℕ) :
    CompleteSeparatedTopCommRingCat.{u} :=
  ⟨TopCommRingCat.of (CycloCompletion R S),
    (TopCommRingCat.isCompleteSeparated_iff _).mpr (isCompleteSeparated R S)⟩

@[simp]
theorem completeSeparatedObj_obj (R : Type u) [CommRing R] (S : Set ℕ) :
    (completeSeparatedObj R S).obj = TopCommRingCat.of (CycloCompletion R S) :=
  (rfl)

/-- When `S` is finite, the inverse-limit topology on `CycloCompletion R S` is the adic topology
defined by the principal ideal `Ideal.span {fromPoly R S (cycloProd R hS)}`. -/
theorem isAdic_span_cycloProd {R : Type*} [CommRing R] {S : Set ℕ} (hS : S.Finite) :
    IsAdic (Ideal.span {fromPoly R S (cycloProd R hS)}) := by
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun U hU ↦ ?_⟩
  · rw [Ideal.span_singleton_pow, ← map_pow]
    exact isOpen_span_fromPoly ⟨cycloProd R hS ^ n, pow_mem (cycloProd_mem_cycloIndex R hS) n⟩
  · obtain ⟨f, -, hfU⟩ := (hasBasis_nhds_zero_span R S).mem_iff.mp hU
    obtain ⟨n, hn⟩ := exists_dvd_cycloProd_pow hS f.property
    refine ⟨n, Set.Subset.trans ?_ hfU⟩
    rw [Ideal.span_singleton_pow, ← map_pow]
    exact span_fromPoly_le_of_dvd (g := ⟨cycloProd R hS ^ n,
      pow_mem (cycloProd_mem_cycloIndex R hS) n⟩) hn

/-- When `S` is finite, `CycloCompletion R S` is adically complete with respect to
`Ideal.span {fromPoly R S (cycloProd R hS)}`. -/
theorem isAdicComplete_span_cycloProd {R : Type*} [CommRing R] {S : Set ℕ} (hS : S.Finite) :
    IsAdicComplete (Ideal.span {fromPoly R S (cycloProd R hS)}) (CycloCompletion R S) :=
  (isAdic_span_cycloProd hS).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

end CompleteSeparatedAndAdic

section Density

variable {R : Type*} [CommRing R] {S : Set ℕ}

/-- The reduced polynomial representative of `x : CycloCompletion R S` modulo
`cycloChain R S N`. -/
noncomputable def approxPoly (x : CycloCompletion R S) (N : ℕ) : R[X] :=
  AdjoinRoot.modByMonicHom (cycloIndex.monic (cycloChainIndex R S N))
    (proj (cycloChainIndex R S N) x)

@[simp]
theorem mk_approxPoly (x : CycloCompletion R S) (N : ℕ) :
    AdjoinRoot.mk ((cycloChainIndex R S N : cycloIndex R S) : R[X]) (approxPoly x N) =
      proj (cycloChainIndex R S N) x :=
  AdjoinRoot.mk_leftInverse (cycloIndex.monic (cycloChainIndex R S N))
    (proj (cycloChainIndex R S N) x)

@[simp]
theorem approxPoly_modByMonic (x : CycloCompletion R S) (N : ℕ) :
    approxPoly x N %ₘ cycloChain R S N = approxPoly x N := by
  rw [← coe_cycloChainIndex, ← AdjoinRoot.modByMonicHom_mk
    (cycloIndex.monic (cycloChainIndex R S N)), mk_approxPoly]
  rfl

@[simp]
theorem approxPoly_zero (x : CycloCompletion R S) : approxPoly x 0 = 0 := by
  rw [← approxPoly_modByMonic x 0, cycloChain_zero, modByMonic_one]

/-- Whenever `f ∈ cycloIndex R S` divides `cycloChain R S N`, the polynomial approximant
`approxPoly x N` has the same `f`-projection as `x`. -/
theorem proj_fromPoly_approxPoly_of_dvd {f : cycloIndex R S} {N : ℕ}
    (h : (f : R[X]) ∣ cycloChain R S N) (x : CycloCompletion R S) :
    proj f (fromPoly R S (approxPoly x N)) = proj f x := by
  have h' : (f : R[X]) ∣ ((cycloChainIndex R S N : cycloIndex R S) : R[X]) := by
    rwa [coe_cycloChainIndex]
  rw [proj_fromPoly, ← algHomOfDvd_proj h' x, ← mk_approxPoly x N, AdjoinRoot.algHomOfDvd_mk]

/-- Successive polynomial approximants satisfy `cycloChain R S M ∣ approxPoly x N - approxPoly x M`
for `M ≤ N`. -/
theorem dvd_approxPoly_sub_of_le {M N : ℕ} (hMN : M ≤ N) (x : CycloCompletion R S) :
    cycloChain R S M ∣ approxPoly x N - approxPoly x M := by
  rw [← coe_cycloChainIndex (R := R) S M, ← AdjoinRoot.mk_eq_zero, map_sub]
  have hMN' : ((cycloChainIndex R S M : cycloIndex R S) : R[X]) ∣ cycloChain R S N := by
    rw [coe_cycloChainIndex]
    exact cycloChain_dvd_cycloChain S hMN
  have hN := proj_fromPoly_approxPoly_of_dvd hMN' x
  rw [proj_fromPoly] at hN
  rw [hN, mk_approxPoly, sub_self]

/-- For every `x : CycloCompletion R S`, the images `fromPoly R S (approxPoly x N)` converge to `x`
as `N → ∞`. -/
theorem tendsto_fromPoly_approxPoly (x : CycloCompletion R S) :
    Tendsto (fun N ↦ fromPoly R S (approxPoly x N)) atTop (𝓝 x) := by
  have hsub : Tendsto (fun N ↦ fromPoly R S (approxPoly x N) - x) atTop (𝓝 0) := by
    rw [(hasBasis_nhds_zero R S).tendsto_right_iff]
    intro f _
    obtain ⟨M, hM⟩ := exists_dvd_cycloChain f.property
    refine eventually_atTop.mpr ⟨M, fun N hMN ↦ ?_⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub,
      proj_fromPoly_approxPoly_of_dvd (hM.trans (cycloChain_dvd_cycloChain S hMN)) x, sub_self]
  simpa only [sub_add_cancel, zero_add] using hsub.add_const x

/-- The canonical polynomial map `fromPoly R S : R[X] →ₐ[R] CycloCompletion R S` has dense image. -/
theorem denseRange_fromPoly (R : Type*) [CommRing R] (S : Set ℕ) :
    DenseRange (fromPoly R S) := fun x ↦
  mem_closure_of_tendsto (tendsto_fromPoly_approxPoly x)
    (Eventually.of_forall fun N ↦ ⟨approxPoly x N, rfl⟩)

/-- Continuous ring homomorphisms from `CycloCompletion R S` into a Hausdorff space are determined
by their restriction to `R[X]`. -/
theorem ringHom_ext_of_continuous {B : Type*} [NonAssocSemiring B] [TopologicalSpace B] [T2Space B]
    {φ₁ φ₂ : CycloCompletion R S →+* B} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (h : φ₁.comp (fromPoly R S : R[X] →+* CycloCompletion R S) =
      φ₂.comp (fromPoly R S : R[X] →+* CycloCompletion R S)) : φ₁ = φ₂ :=
  DFunLike.coe_injective <| (denseRange_fromPoly R S).equalizer h₁ h₂ <|
    funext fun p ↦ RingHom.congr_fun h p

/-- Continuous `A`-algebra homomorphisms from `CycloCompletion R S` into a Hausdorff `A`-algebra are
determined by their restriction to `R[X]`. -/
theorem algHom_ext_of_continuous {A : Type*} [CommSemiring A] [Algebra A R]
    {B : Type*} [Semiring B] [Algebra A B] [TopologicalSpace B] [T2Space B]
    {φ₁ φ₂ : CycloCompletion R S →ₐ[A] B} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (h : φ₁.comp ((fromPoly R S).restrictScalars A) =
      φ₂.comp ((fromPoly R S).restrictScalars A)) : φ₁ = φ₂ :=
  DFunLike.coe_injective <| (denseRange_fromPoly R S).equalizer h₁ h₂ <|
    funext fun p ↦ AlgHom.congr_fun h p

end Density

end CycloCompletion

section UniversalProperty

/-- A ring homomorphism `ψ : R[X] →+* B` into a topological ring `B` is `S`-cyclotomically
continuous if every neighborhood of `0` in `B` contains `ψ` of the ideal generated by some
`f ∈ cycloIndex R S`. -/
def IsCycloContinuous {R : Type*} [CommRing R] (S : Set ℕ)
    {B : Type*} [NonAssocSemiring B] [TopologicalSpace B] (ψ : R[X] →+* B) : Prop :=
  ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U

theorem isCycloContinuous_iff {R : Type*} [CommRing R] {S : Set ℕ}
    {B : Type*} [NonAssocSemiring B] [TopologicalSpace B] {ψ : R[X] →+* B} :
    IsCycloContinuous S ψ ↔
      ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U :=
  Iff.rfl

/-- The canonical polynomial map `CycloCompletion.fromPoly R S` is itself `S`-cyclotomically
continuous. -/
theorem isCycloContinuous_fromPoly (R : Type*) [CommRing R] (S : Set ℕ) :
    IsCycloContinuous S (CycloCompletion.fromPoly R S : R[X] →+* CycloCompletion R S) := by
  intro U hU
  obtain ⟨f, -, hfU⟩ := (CycloCompletion.hasBasis_nhds_zero_span R S).mem_iff.mp hU
  refine ⟨f, fun p hp ↦ hfU ?_⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  exact map_dvd (CycloCompletion.fromPoly R S) hp

/-- Composing an `S`-cyclotomically continuous homomorphism with a continuous ring homomorphism
preserves `S`-cyclotomic continuity. -/
theorem IsCycloContinuous.comp {R : Type*} [CommRing R] {S : Set ℕ}
    {B C : Type*} [NonAssocSemiring B] [TopologicalSpace B]
    [NonAssocSemiring C] [TopologicalSpace C]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) {θ : B →+* C} (hθ : Continuous θ) :
    IsCycloContinuous S (θ.comp ψ) := by
  intro U hU
  have hmem : θ ⁻¹' U ∈ 𝓝 (0 : B) :=
    hθ.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨f, hf⟩ := hψ (θ ⁻¹' U) hmem
  exact ⟨f, fun p hp ↦ hf p hp⟩

/-- Precomposing an `S`-cyclotomically continuous homomorphism with `Polynomial.mapRingHom φ`
preserves `S`-cyclotomic continuity. -/
theorem IsCycloContinuous.comp_mapRingHom {R R' : Type*} [CommRing R] [CommRing R'] {S : Set ℕ}
    {B : Type*} [NonAssocSemiring B] [TopologicalSpace B]
    {ψ : R'[X] →+* B} (hψ : IsCycloContinuous S ψ) (φ : R →+* R') :
    IsCycloContinuous S (ψ.comp (Polynomial.mapRingHom φ)) := by
  intro U hU
  obtain ⟨f', hf'⟩ := hψ U hU
  obtain ⟨f, hf⟩ := exists_map_eq_of_mem_cycloIndex φ f'.property
  refine ⟨f, fun p hp ↦ hf' (p.map φ) ?_⟩
  rw [← hf]
  exact Polynomial.map_dvd φ hp

namespace CycloCompletion

/-- The uniform structure on `R[X]` induced along `fromPoly R S` from `CycloCompletion R S`. -/
private noncomputable abbrev comapUniformSpace (R : Type*) [CommRing R] (S : Set ℕ) :
    UniformSpace R[X] :=
  UniformSpace.comap (fromPoly R S : R[X] →+* CycloCompletion R S) inferInstance

private theorem isUniformInducing_fromPoly (R : Type*) [CommRing R] (S : Set ℕ) :
    letI := comapUniformSpace R S
    IsUniformInducing (fromPoly R S : R[X] →+* CycloCompletion R S) :=
  letI := comapUniformSpace R S
  ⟨rfl⟩

private theorem uniformContinuous_of_isCycloContinuous {R : Type*} [CommRing R] {S : Set ℕ}
    {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    letI := comapUniformSpace R S
    UniformContinuous ψ := by
  let := comapUniformSpace R S
  have : IsUniformAddGroup R[X] :=
    IsUniformAddGroup.comap (fromPoly R S : R[X] →+ CycloCompletion R S)
  refine uniformContinuous_of_continuousAt_zero ψ ?_
  rw [ContinuousAt, map_zero, (isUniformInducing_fromPoly R S).isInducing.nhds_eq_comap, map_zero,
    ((hasBasis_nhds_zero R S).comap
      (fromPoly R S : R[X] →+* CycloCompletion R S)).tendsto_iff (𝓝 (0 : B)).basis_sets]
  intro U hU
  obtain ⟨f, hf⟩ := hψ U hU
  refine ⟨f, trivial, fun p hp ↦ hf p ?_⟩
  simpa [RingHom.mem_ker] using hp

/-- For any `S`-cyclotomically continuous ring homomorphism `ψ : R[X] →+* B` into a uniform
additive group `B`, the sequence `N ↦ ψ (approxPoly x N)` is Cauchy. -/
theorem cauchySeq_approxPoly {R : Type*} [CommRing R] {S : Set ℕ}
    {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    (x : CycloCompletion R S) : CauchySeq fun N ↦ ψ (approxPoly x N) := by
  let := comapUniformSpace R S
  have hcauchy : CauchySeq (approxPoly x) := by
    rw [CauchySeq, ← (isUniformInducing_fromPoly R S).cauchy_map_iff, Filter.map_map]
    exact (tendsto_fromPoly_approxPoly x).cauchySeq
  exact (uniformContinuous_of_isCycloContinuous hψ).comp_cauchySeq hcauchy

section Lift

variable {R : Type*} [CommRing R] {S : Set ℕ}
  {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [T2Space B] [CompleteSpace B]

/-- The continuous ring homomorphism `CycloCompletion R S →+* B` extending an `S`-cyclotomically
continuous polynomial map `ψ : R[X] →+* B` into a complete Hausdorff topological ring `B`. -/
noncomputable def lift (S : Set ℕ) {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    CycloCompletion R S →+* B :=
  letI := comapUniformSpace R S
  IsDenseInducing.extendRingHom (isUniformInducing_fromPoly R S) (denseRange_fromPoly R S)
    (uniformContinuous_of_isCycloContinuous hψ)

@[fun_prop, continuity]
theorem continuous_lift {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    Continuous (lift S hψ) :=
  letI := comapUniformSpace R S
  (uniformContinuous_uniformly_extend (isUniformInducing_fromPoly R S) (denseRange_fromPoly R S)
    (uniformContinuous_of_isCycloContinuous hψ)).continuous

@[simp]
theorem lift_fromPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) (p : R[X]) :
    lift S hψ (fromPoly R S p) = ψ p :=
  letI := comapUniformSpace R S
  ((isUniformInducing_fromPoly R S).isDenseInducing (denseRange_fromPoly R S)).extend_eq
    (uniformContinuous_of_isCycloContinuous hψ).continuous p

@[simp]
theorem lift_comp_fromPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    (lift S hψ).comp (fromPoly R S : R[X] →+* CycloCompletion R S) = ψ :=
  RingHom.ext (lift_fromPoly hψ)

@[simp]
theorem lift_algebraMap {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) (r : R) :
    lift S hψ (algebraMap R (CycloCompletion R S) r) = ψ (C r) := by
  rw [← fromPoly_C, lift_fromPoly]

/-- For every `x : CycloCompletion R S`, `ψ (approxPoly x N)` converges to `lift S hψ x`. -/
theorem tendsto_approxPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    (x : CycloCompletion R S) :
    Tendsto (fun N ↦ ψ (approxPoly x N)) atTop (𝓝 (lift S hψ x)) := by
  simpa only [Function.comp_def, lift_fromPoly] using
    (continuous_lift hψ).continuousAt.tendsto.comp (tendsto_fromPoly_approxPoly x)

/-- A continuous ring homomorphism out of `CycloCompletion R S` into a complete Hausdorff
topological ring `B` equals `lift S hψ` whenever its restriction along `fromPoly R S` is `ψ`. -/
theorem eq_lift {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    {φ : CycloCompletion R S →+* B} (hφ : Continuous φ)
    (hcomp : φ.comp (fromPoly R S : R[X] →+* CycloCompletion R S) = ψ) :
    φ = lift S hψ :=
  ringHom_ext_of_continuous hφ (continuous_lift hψ) (hcomp.trans (lift_comp_fromPoly hψ).symm)

/-- Post-composing `lift S hψ` with a continuous ring homomorphism `θ : B →+* C` into another
complete Hausdorff topological ring yields `lift S (hψ.comp hθ)`. -/
theorem comp_lift {C : Type*} [Ring C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    {θ : B →+* C} (hθ : Continuous θ) :
    θ.comp (lift S hψ) = lift S (hψ.comp hθ) :=
  eq_lift (hψ.comp hθ) (hθ.comp (continuous_lift hψ)) <| by
    rw [RingHom.comp_assoc, lift_comp_fromPoly]

@[simp]
theorem comp_lift_apply {C : Type*} [Ring C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    {θ : B →+* C} (hθ : Continuous θ) (x : CycloCompletion R S) :
    θ (lift S hψ x) = lift S (hψ.comp hθ) x :=
  RingHom.congr_fun (comp_lift hψ hθ) x

/-- `A`-algebra homomorphism version of `CycloCompletion.lift` when `B` is a complete Hausdorff
topological `A`-algebra. -/
noncomputable def liftAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    (S : Set ℕ) {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) :
    CycloCompletion R S →ₐ[A] B :=
  { lift S hψ with
    commutes' a := by
      rw [RingHom.toFun_eq_coe, IsScalarTower.algebraMap_apply A R (CycloCompletion R S),
        lift_algebraMap, ← Polynomial.algebraMap_apply]
      exact ψ.commutes a }

@[simp]
theorem coe_liftAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) :
    ⇑(liftAlgHom S hψ) = ⇑(lift S hψ) :=
  (rfl)

@[simp]
theorem toRingHom_liftAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) :
    (liftAlgHom S hψ : CycloCompletion R S →+* B) = lift S hψ :=
  (rfl)

theorem liftAlgHom_fromPoly {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) (p : R[X]) :
    liftAlgHom S hψ (fromPoly R S p) = ψ p :=
  lift_fromPoly hψ p

theorem liftAlgHom_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) (a : A) :
    liftAlgHom S hψ (algebraMap A (CycloCompletion R S) a) = algebraMap A B a :=
  (liftAlgHom S hψ).commutes a

@[simp]
theorem liftAlgHom_comp_restrictScalars_fromPoly
    {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) :
    (liftAlgHom S hψ).comp ((fromPoly R S).restrictScalars A) = ψ :=
  AlgHom.ext (liftAlgHom_fromPoly hψ)

@[simp]
theorem liftAlgHom_comp_fromPoly [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) :
    (liftAlgHom S hψ).comp (fromPoly R S) = ψ :=
  AlgHom.ext (liftAlgHom_fromPoly hψ)

@[fun_prop, continuity]
theorem continuous_liftAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B)) :
    Continuous (liftAlgHom S hψ) :=
  continuous_lift hψ

/-- A continuous `A`-algebra homomorphism out of `CycloCompletion R S` into a complete Hausdorff
topological `A`-algebra `B` equals `liftAlgHom S hψ` whenever its restriction along `fromPoly R S`
is `ψ`. -/
theorem eq_liftAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B))
    {φ : CycloCompletion R S →ₐ[A] B} (hφ : Continuous φ)
    (hcomp : φ.comp ((fromPoly R S).restrictScalars A) = ψ) :
    φ = liftAlgHom S hψ :=
  algHom_ext_of_continuous hφ (continuous_liftAlgHom hψ)
    (hcomp.trans (liftAlgHom_comp_restrictScalars_fromPoly hψ).symm)

/-- Post-composing `liftAlgHom S hψ` with a continuous `A`-algebra homomorphism `θ : B →ₐ[A] C` into
another complete Hausdorff topological `A`-algebra yields `liftAlgHom S (hψ.comp hθ)`. -/
theorem comp_liftAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {C : Type*} [Ring C] [Algebra A C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B))
    {θ : B →ₐ[A] C} (hθ : Continuous θ) :
    θ.comp (liftAlgHom S hψ) = liftAlgHom S (ψ := θ.comp ψ) (hψ.comp hθ) :=
  AlgHom.toRingHom_injective (comp_lift hψ hθ)

theorem comp_liftAlgHom_apply {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A B]
    {C : Type*} [Ring C] [Algebra A C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    {ψ : R[X] →ₐ[A] B} (hψ : IsCycloContinuous S (ψ : R[X] →+* B))
    {θ : B →ₐ[A] C} (hθ : Continuous θ) (x : CycloCompletion R S) :
    θ (liftAlgHom S hψ x) = liftAlgHom S (ψ := θ.comp ψ) (hψ.comp hθ) x :=
  AlgHom.congr_fun (comp_liftAlgHom hψ hθ) x

/-- **Universal property of the cyclotomic completion.** Every `S`-cyclotomically continuous ring
homomorphism `ψ : R[X] →+* B` into a complete Hausdorff topological ring `B` extends uniquely to a
continuous ring homomorphism `CycloCompletion R S →+* B`. -/
theorem existsUnique_continuous_comp_fromPoly_eq (R : Type*) [CommRing R] (S : Set ℕ)
    {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    (ψ : R[X] →+* B) (hψ : IsCycloContinuous S ψ) :
    ∃! φ : CycloCompletion R S →+* B,
      Continuous φ ∧ φ.comp (fromPoly R S : R[X] →+* CycloCompletion R S) = ψ :=
  ⟨lift S hψ, ⟨continuous_lift hψ, lift_comp_fromPoly hψ⟩,
    fun _ ⟨hcont, hcomp⟩ ↦ eq_lift hψ hcont hcomp⟩

end Lift

section LiftSelf

@[simp]
theorem lift_fromPoly_self (R : Type*) [CommRing R] (S : Set ℕ) :
    lift S (isCycloContinuous_fromPoly R S) = RingHom.id (CycloCompletion R S) :=
  (eq_lift (isCycloContinuous_fromPoly R S) continuous_id (RingHom.id_comp _)).symm

theorem lift_fromPoly_self_apply {R : Type*} [CommRing R] {S : Set ℕ}
    (x : CycloCompletion R S) :
    lift S (isCycloContinuous_fromPoly R S) x = x := by
  rw [lift_fromPoly_self, RingHom.id_apply]

@[simp]
theorem liftAlgHom_restrictScalars_fromPoly_self (A R : Type*) [CommSemiring A] [CommRing R]
    [Algebra A R] (S : Set ℕ) :
    liftAlgHom S (ψ := (fromPoly R S).restrictScalars A) (isCycloContinuous_fromPoly R S) =
      AlgHom.id A (CycloCompletion R S) :=
  AlgHom.toRingHom_injective (lift_fromPoly_self R S)

@[simp]
theorem liftAlgHom_fromPoly_self (R : Type*) [CommRing R] (S : Set ℕ) :
    liftAlgHom S (ψ := fromPoly R S) (isCycloContinuous_fromPoly R S) =
      AlgHom.id R (CycloCompletion R S) :=
  AlgHom.toRingHom_injective (lift_fromPoly_self R S)

end LiftSelf

end CycloCompletion

end UniversalProperty

end TauCeti
