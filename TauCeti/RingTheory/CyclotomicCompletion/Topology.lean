/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclotomicCompletion.Basic
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.LocallyConstant.Basic

import Mathlib.RingTheory.AdicCompletion.Topology
import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology
import TauCeti.Topology.Discrete
import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Inverse-limit topology and universal property of the cyclotomic completion

We equip `CycloCompletion R S` with the inverse-limit topology induced from the product of discrete
quotients `∀ f : cycloIndex R S, AdjoinRoot (f : R[X])`. Under this topology:

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
  `CycloCompletion R S →+* B` (`TauCeti.completion_universal_property`).

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
* `TauCeti.completion_universal_property`: unique continuous extension of cyclotomically continuous
  homomorphisms out of `R[X]`.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §§3.1, 3.3.
-/

public section

universe u

open Filter Polynomial
open scoped Topology Uniformity TauCeti.TopCommRingCat

namespace TauCeti

/-- The inverse-limit topology on `CycloCompletion R S`, induced from the product of discrete
polynomial quotients `∀ f : cycloIndex R S, AdjoinRoot (f : R[X])`. -/
instance instTopologicalSpaceCycloCompletion (R : Type*) [CommRing R] (S : Set ℕ) :
    TopologicalSpace (CycloCompletion R S) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace (cycloIndex R S) (fun f ↦ AdjoinRoot (f : R[X])) (fun _ ↦ ⊥))

namespace CycloCompletion

section InverseLimitTopology

variable {R : Type*} [CommRing R] {S : Set ℕ}

theorem topologicalSpace_def (R : Type*) [CommRing R] (S : Set ℕ) :
    instTopologicalSpaceCycloCompletion R S =
      TopologicalSpace.induced Subtype.val
        (@Pi.topologicalSpace (cycloIndex R S) (fun f ↦ AdjoinRoot (f : R[X])) (fun _ ↦ ⊥)) :=
  (rfl)

/-- The topology on `CycloCompletion R S` is the initial topology of all quotient projections
`proj f` into discrete `AdjoinRoot (f : R[X])`. -/
theorem topologicalSpace_eq_iInf_induced (R : Type*) [CommRing R] (S : Set ℕ) :
    instTopologicalSpaceCycloCompletion R S =
      ⨅ f : cycloIndex R S, TopologicalSpace.induced (proj f) ⊥ := by
  let _ : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ ↦ ⊥
  rw [topologicalSpace_def, Pi.topologicalSpace, induced_iInf]
  refine iInf_congr fun f ↦ ?_
  rw [induced_compose]
  have hcomp : ((fun x : ∀ g : cycloIndex R S, AdjoinRoot (g : R[X]) ↦ x f) ∘ Subtype.val) =
      (proj f : CycloCompletion R S → AdjoinRoot (f : R[X])) :=
    funext fun x ↦ (proj_apply f x).symm
  rw [hcomp]

/-- Every coordinate projection `proj f` is locally constant on `CycloCompletion R S`. -/
theorem isLocallyConstant_proj (f : cycloIndex R S) :
    IsLocallyConstant (proj f : CycloCompletion R S → AdjoinRoot (f : R[X])) := by
  let _ : TopologicalSpace (AdjoinRoot (f : R[X])) := ⊥
  have : DiscreteTopology (AdjoinRoot (f : R[X])) := discreteTopology_bot _
  rw [IsLocallyConstant.iff_continuous, continuous_iff_le_induced, topologicalSpace_eq_iInf_induced]
  exact iInf_le _ f

/-- A map into `CycloCompletion R S` is continuous if and only if its composition with each
coordinate projection `proj f` is locally constant. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : X → CycloCompletion R S} :
    Continuous g ↔ ∀ f : cycloIndex R S, IsLocallyConstant (proj f ∘ g) := by
  rw [topologicalSpace_eq_iInf_induced, continuous_iInf_rng]
  refine forall_congr' fun f ↦ ?_
  let _ : TopologicalSpace (AdjoinRoot (f : R[X])) := ⊥
  have : DiscreteTopology (AdjoinRoot (f : R[X])) := discreteTopology_bot _
  rw [continuous_induced_rng, IsLocallyConstant.iff_continuous]

instance (R : Type*) [CommRing R] (S : Set ℕ) : IsTopologicalRing (CycloCompletion R S) := by
  let _ : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ ↦ ⊥
  have : ∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X])) :=
    fun _ ↦ discreteTopology_bot _
  exact Subring.instIsTopologicalRing (compatSubalgebra R S).toSubring

instance (R : Type*) [CommRing R] (S : Set ℕ) : T2Space (CycloCompletion R S) := by
  let _ : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ ↦ ⊥
  have : ∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X])) :=
    fun _ ↦ discreteTopology_bot _
  exact inferInstance

/-- Each projection kernel `RingHom.ker (proj f)` is open in `CycloCompletion R S`. -/
theorem isOpen_ker_proj (f : cycloIndex R S) :
    IsOpen (RingHom.ker (proj f) : Set (CycloCompletion R S)) :=
  (isLocallyConstant_proj f).isOpen_fiber 0

/-- Each projection kernel `RingHom.ker (proj f)` is closed in `CycloCompletion R S`. -/
theorem isClosed_ker_proj (f : cycloIndex R S) :
    IsClosed (RingHom.ker (proj f) : Set (CycloCompletion R S)) :=
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
      fun f ↦ (RingHom.ker (proj f) : Set (CycloCompletion R S)) := by
  have hnhds : 𝓝 (0 : CycloCompletion R S) =
      ⨅ f : cycloIndex R S, 𝓟 (RingHom.ker (proj f) : Set (CycloCompletion R S)) := by
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
      fun N ↦ (RingHom.ker (proj (cycloChainIndex R S N)) : Set (CycloCompletion R S)) := by
  refine (hasBasis_nhds_zero R S).to_hasBasis (fun f _ ↦ ?_) fun N _ ↦
    ⟨cycloChainIndex R S N, trivial, subset_rfl⟩
  obtain ⟨N, hN⟩ := exists_dvd_cycloChain f.2
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

/-- `compatSubalgebra R S` is closed in the product of discrete quotients
`∀ f : cycloIndex R S, AdjoinRoot (f : R[X])`. -/
theorem isClosed_compatSubalgebra (R : Type*) [CommRing R] (S : Set ℕ) :
    @IsClosed (∀ f : cycloIndex R S, AdjoinRoot (f : R[X]))
      (@Pi.topologicalSpace (cycloIndex R S) (fun f ↦ AdjoinRoot (f : R[X])) (fun _ ↦ ⊥))
      (compatSubalgebra R S : Set (∀ f : cycloIndex R S, AdjoinRoot (f : R[X]))) := by
  let _ : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ ↦ ⊥
  have : ∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X])) :=
    fun _ ↦ discreteTopology_bot _
  have hset : (compatSubalgebra R S : Set (∀ f : cycloIndex R S, AdjoinRoot (f : R[X]))) =
      ⋂ (f : cycloIndex R S) (g : cycloIndex R S) (h : (f : R[X]) ∣ g),
        {x | AdjoinRoot.algHomOfDvd R (g : R[X]) (f : R[X]) h (x g) = x f} := by
    ext x
    simp [mem_compatSubalgebra_iff]
  rw [hset]
  refine isClosed_iInter fun f ↦ isClosed_iInter fun g ↦ isClosed_iInter fun h ↦ ?_
  exact isClosed_eq
    (continuous_of_discreteTopology.comp (continuous_apply g)) (continuous_apply f)

/-- `CycloCompletion R S` is complete and separated for the canonical group uniformity of its
inverse-limit topology. -/
theorem isCompleteSeparated (R : Type u) [CommRing R] (S : Set ℕ) :
    TopCommRingCat.IsCompleteSeparated (TopCommRingCat.of (CycloCompletion R S)) := by
  let _ : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ ↦ ⊥
  have : ∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X])) :=
    fun _ ↦ discreteTopology_bot _
  have hfactor : ∀ f : cycloIndex R S,
      TopCommRingCat.IsCompleteSeparated (TopCommRingCat.of (AdjoinRoot (f : R[X]))) := by
    intro f
    let _ : UniformSpace (AdjoinRoot (f : R[X])) :=
      IsTopologicalAddGroup.rightUniformSpace (AdjoinRoot (f : R[X]))
    have : IsUniformAddGroup (AdjoinRoot (f : R[X])) := isUniformAddGroup_of_addCommGroup
    have : DiscreteUniformity (AdjoinRoot (f : R[X])) :=
      IsRightUniformAddGroup.discreteUniformity
    exact ⟨inferInstance, inferInstance⟩
  have hpi : TopCommRingCat.IsCompleteSeparated
      (TopCommRingCat.of (∀ f : cycloIndex R S, AdjoinRoot (f : R[X]))) :=
    TopCommRingCat.IsCompleteSeparated.pi hfactor
  let ι : TopCommRingCat.of (CycloCompletion R S) ⟶
      TopCommRingCat.of (∀ f : cycloIndex R S, AdjoinRoot (f : R[X])) :=
    ⟨(compatSubalgebra R S).val.toRingHom, continuous_subtype_val⟩
  exact TopCommRingCat.IsCompleteSeparated.of_isClosedEmbedding ι
    (Topology.IsClosedEmbedding.subtypeVal (isClosed_compatSubalgebra R S)) hpi

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
    obtain ⟨n, hn⟩ := exists_dvd_cycloProd_pow hS f.2
    refine ⟨n, Set.Subset.trans ?_ hfU⟩
    rw [Ideal.span_singleton_pow, ← map_pow]
    exact span_fromPoly_le_of_dvd (g := ⟨cycloProd R hS ^ n,
      pow_mem (cycloProd_mem_cycloIndex R hS) n⟩) hn

/-- When `S` is finite, `CycloCompletion R S` is adically complete with respect to
`Ideal.span {fromPoly R S (cycloProd R hS)}`. -/
theorem isAdicComplete_span_cycloProd {R : Type*} [CommRing R] {S : Set ℕ} (hS : S.Finite) :
    IsAdicComplete (Ideal.span {fromPoly R S (cycloProd R hS)}) (CycloCompletion R S) := by
  let _ : UniformSpace (CycloCompletion R S) :=
    IsTopologicalAddGroup.rightUniformSpace (CycloCompletion R S)
  have : IsUniformAddGroup (CycloCompletion R S) := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace (CycloCompletion R S) := (isCompleteSeparated R S).completeSpace
  exact (isAdic_span_cycloProd hS).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

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
  rw [proj_fromPoly, ← algHomOfDvd_proj h' x, ← mk_approxPoly x N,
    AdjoinRoot.algHom_mk, AdjoinRoot.algHomOfDvd_root, AdjoinRoot.aeval_eq]

/-- Successive polynomial approximants satisfy `cycloChain R S M ∣ approxPoly x N - approxPoly x M`
for `M ≤ N`. -/
theorem dvd_approxPoly_sub_of_le {M N : ℕ} (hMN : M ≤ N) (x : CycloCompletion R S) :
    cycloChain R S M ∣ approxPoly x N - approxPoly x M := by
  rw [← coe_cycloChainIndex R S M, ← AdjoinRoot.mk_eq_zero, map_sub]
  have hMN' : ((cycloChainIndex R S M : cycloIndex R S) : R[X]) ∣ cycloChain R S N := by
    rw [coe_cycloChainIndex]
    exact cycloChain_dvd_of_le hMN
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
    obtain ⟨M, hM⟩ := exists_dvd_cycloChain f.2
    refine eventually_atTop.mpr ⟨M, fun N hMN ↦ ?_⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub,
      proj_fromPoly_approxPoly_of_dvd (hM.trans (cycloChain_dvd_of_le hMN)) x, sub_self]
  simpa only [sub_add_cancel, zero_add] using hsub.add_const x

/-- The canonical polynomial map `fromPoly R S : R[X] →ₐ[R] CycloCompletion R S` has dense image. -/
theorem denseRange_fromPoly (R : Type*) [CommRing R] (S : Set ℕ) :
    DenseRange (fromPoly R S) := fun x ↦
  mem_closure_of_tendsto (tendsto_fromPoly_approxPoly x)
    (Eventually.of_forall fun N ↦ ⟨approxPoly x N, rfl⟩)

/-- Continuous ring homomorphisms from `CycloCompletion R S` into a Hausdorff space are determined
by their restriction to `R[X]`. -/
theorem ringHom_ext_of_continuous {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]
    {φ₁ φ₂ : CycloCompletion R S →+* B} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (h : φ₁.comp (fromPoly R S).toRingHom = φ₂.comp (fromPoly R S).toRingHom) : φ₁ = φ₂ :=
  DFunLike.coe_injective <| (denseRange_fromPoly R S).equalizer h₁ h₂ <|
    funext fun p ↦ RingHom.congr_fun h p

/-- Continuous `R`-algebra homomorphisms from `CycloCompletion R S` into a Hausdorff `R`-algebra are
determined by their restriction to `R[X]`. -/
theorem algHom_ext_of_continuous {B : Type*} [Semiring B] [Algebra R B] [TopologicalSpace B]
    [T2Space B] {φ₁ φ₂ : CycloCompletion R S →ₐ[R] B} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (h : φ₁.comp (fromPoly R S) = φ₂.comp (fromPoly R S)) : φ₁ = φ₂ :=
  DFunLike.coe_injective <| (denseRange_fromPoly R S).equalizer h₁ h₂ <|
    funext fun p ↦ AlgHom.congr_fun h p

end Density

end CycloCompletion

section UniversalProperty

/-- A ring homomorphism `ψ : R[X] →+* B` into a topological ring `B` is `S`-cyclotomically
continuous if every neighborhood of `0` in `B` contains `ψ` of the ideal generated by some
`f ∈ cycloIndex R S`. -/
def IsCycloContinuous {R : Type*} [CommRing R] (S : Set ℕ)
    {B : Type*} [Ring B] [TopologicalSpace B] (ψ : R[X] →+* B) : Prop :=
  ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U

theorem isCycloContinuous_iff {R : Type*} [CommRing R] {S : Set ℕ}
    {B : Type*} [Ring B] [TopologicalSpace B] {ψ : R[X] →+* B} :
    IsCycloContinuous S ψ ↔
      ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U :=
  Iff.rfl

/-- The canonical polynomial map `fromPoly R S` is itself `S`-cyclotomically continuous. -/
theorem isCycloContinuous_fromPoly (R : Type*) [CommRing R] (S : Set ℕ) :
    IsCycloContinuous S (fromPoly R S).toRingHom := by
  intro U hU
  obtain ⟨f, -, hfU⟩ := (CycloCompletion.hasBasis_nhds_zero_span R S).mem_iff.mp hU
  refine ⟨f, fun p hp ↦ hfU ?_⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  exact map_dvd (fromPoly R S) hp

/-- Composing an `S`-cyclotomically continuous homomorphism with a continuous ring homomorphism
preserves `S`-cyclotomic continuity. -/
theorem IsCycloContinuous.comp {R : Type*} [CommRing R] {S : Set ℕ}
    {B C : Type*} [Ring B] [TopologicalSpace B] [Ring C] [TopologicalSpace C]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) {θ : B →+* C} (hθ : Continuous θ) :
    IsCycloContinuous S (θ.comp ψ) := by
  intro U hU
  have hmem : θ ⁻¹' U ∈ 𝓝 (0 : B) :=
    hθ.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨f, hf⟩ := hψ (θ ⁻¹' U) hmem
  exact ⟨f, fun p hp ↦ hf p hp⟩

namespace CycloCompletion

private theorem tendsto_of_mk_eq {R : Type*} [CommRing R] {S : Set ℕ}
    {B : Type*} [Ring B] [TopologicalSpace B] [ContinuousAdd B]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    (x : CycloCompletion R S) {b : B}
    (hb : Tendsto (fun N ↦ ψ (approxPoly x N)) atTop (𝓝 b))
    {p : ℕ → R[X]}
    (hp : ∀ N : ℕ, AdjoinRoot.mk ((cycloChainIndex R S N : cycloIndex R S) : R[X]) (p N) =
      proj (cycloChainIndex R S N) x) :
    Tendsto (fun N ↦ ψ (p N)) atTop (𝓝 b) := by
  have hdiff : Tendsto (fun N ↦ ψ (p N) - ψ (approxPoly x N)) atTop (𝓝 0) := by
    rw [(𝓝 (0 : B)).basis_sets.tendsto_right_iff]
    intro U hU
    obtain ⟨f, hf⟩ := hψ U hU
    obtain ⟨M, hM⟩ := exists_dvd_cycloChain f.2
    refine eventually_atTop.mpr ⟨M, fun N hMN ↦ ?_⟩
    have hdvd : (f : R[X]) ∣ p N - approxPoly x N := by
      refine (hM.trans (cycloChain_dvd_of_le hMN)).trans ?_
      rw [← coe_cycloChainIndex R S N, ← AdjoinRoot.mk_eq_zero, map_sub, hp N,
        mk_approxPoly, sub_self]
    simpa only [id_eq, map_sub] using hf (p N - approxPoly x N) hdvd
  simpa only [sub_add_cancel, zero_add] using hdiff.add hb

/-- For any `S`-cyclotomically continuous ring homomorphism `ψ : R[X] →+* B` into a uniform
additive group `B`, the sequence `N ↦ ψ (approxPoly x N)` is Cauchy. -/
theorem cauchySeq_approxPoly {R : Type*} [CommRing R] {S : Set ℕ}
    {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
    {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    (x : CycloCompletion R S) : CauchySeq fun N ↦ ψ (approxPoly x N) := by
  have hbasis : (𝓤 B).HasBasis (· ∈ 𝓝 (0 : B)) fun U : Set B ↦ {q : B × B | q.2 - q.1 ∈ U} := by
    rw [uniformity_eq_comap_nhds_zero B]
    exact (𝓝 (0 : B)).basis_sets.comap _
  rw [hbasis.cauchySeq_iff]
  intro U hU
  have hsub : Continuous fun q : B × B ↦ q.1 - q.2 := continuous_sub
  have hpre : (fun q : B × B ↦ q.1 - q.2) ⁻¹' U ∈ 𝓝 ((0 : B), (0 : B)) :=
    hsub.continuousAt (x := ((0 : B), (0 : B))).preimage_mem_nhds
      (by simpa only [sub_self] using hU)
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨f, hf⟩ := hψ (V ∩ W) (inter_mem hV hW)
  obtain ⟨M, hM⟩ := exists_dvd_cycloChain f.2
  refine ⟨M, fun m hm n hn ↦ ?_⟩
  have hn_mem : ψ (approxPoly x n) - ψ (approxPoly x M) ∈ V := by
    rw [← map_sub]
    exact (hf _ (hM.trans (dvd_approxPoly_sub_of_le hn x))).1
  have hm_mem : ψ (approxPoly x m) - ψ (approxPoly x M) ∈ W := by
    rw [← map_sub]
    exact (hf _ (hM.trans (dvd_approxPoly_sub_of_le hm x))).2
  have hdiff := hVW (Set.mk_mem_prod hn_mem hm_mem)
  rw [Set.mem_ofPred_eq]
  simpa only [Set.mem_preimage, sub_sub_sub_cancel_right] using hdiff

variable {R : Type*} [CommRing R] {S : Set ℕ}
  {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [T2Space B] [CompleteSpace B]

/-- The continuous ring homomorphism `CycloCompletion R S →+* B` extending an `S`-cyclotomically
continuous polynomial map `ψ : R[X] →+* B` into a complete Hausdorff topological ring `B`. -/
noncomputable def lift (S : Set ℕ) {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    CycloCompletion R S →+* B where
  toFun x := Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ x))
  map_one' := by
    have h1 := tendsto_of_mk_eq hψ 1
      (Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ 1)))
      (p := fun _ ↦ 1) (fun _ ↦ by rw [map_one, map_one])
    simpa only [map_one] using tendsto_nhds_unique h1 tendsto_const_nhds
  map_mul' x y := by
    have hx := Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ x))
    have hy := Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ y))
    have hxy := tendsto_of_mk_eq hψ (x * y)
      (Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ (x * y))))
      (p := fun N ↦ approxPoly x N * approxPoly y N)
      (fun N ↦ by rw [map_mul, mk_approxPoly, mk_approxPoly, map_mul])
    have hmul : Tendsto (fun N ↦ ψ (approxPoly x N * approxPoly y N)) atTop
        (𝓝 (Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ x)) *
          Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ y)))) := by
      simpa only [map_mul] using hx.mul hy
    exact tendsto_nhds_unique hxy hmul
  map_zero' := by
    have h0 := tendsto_of_mk_eq hψ 0
      (Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ 0)))
      (p := fun _ ↦ 0) (fun _ ↦ by rw [map_zero, map_zero])
    simpa only [map_zero] using tendsto_nhds_unique h0 tendsto_const_nhds
  map_add' x y := by
    have hx := Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ x))
    have hy := Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ y))
    have hxy := tendsto_of_mk_eq hψ (x + y)
      (Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ (x + y))))
      (p := fun N ↦ approxPoly x N + approxPoly y N)
      (fun N ↦ by rw [map_add, mk_approxPoly, mk_approxPoly, map_add])
    have hadd : Tendsto (fun N ↦ ψ (approxPoly x N + approxPoly y N)) atTop
        (𝓝 (Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ x)) +
          Classical.choose (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ y)))) := by
      simpa only [map_add] using hx.add hy
    exact tendsto_nhds_unique hxy hadd

/-- For every `x : CycloCompletion R S`, `ψ (approxPoly x N)` converges to `lift S hψ x`. -/
theorem tendsto_approxPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ)
    (x : CycloCompletion R S) :
    Tendsto (fun N ↦ ψ (approxPoly x N)) atTop (𝓝 (lift S hψ x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchySeq_approxPoly hψ x))

@[simp]
theorem lift_fromPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) (p : R[X]) :
    lift S hψ (fromPoly R S p) = ψ p :=
  tendsto_nhds_unique
    (tendsto_of_mk_eq hψ (fromPoly R S p) (tendsto_approxPoly hψ (fromPoly R S p))
      (p := fun _ ↦ p) (fun N ↦ (proj_fromPoly (cycloChainIndex R S N) p).symm))
    tendsto_const_nhds

theorem lift_comp_fromPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    (lift S hψ).comp (fromPoly R S).toRingHom = ψ :=
  RingHom.ext (lift_fromPoly hψ)

@[simp]
theorem lift_comp_coe_fromPoly {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    (lift S hψ).comp (fromPoly R S : R[X] →+* CycloCompletion R S) = ψ :=
  lift_comp_fromPoly hψ

@[fun_prop, continuity]
theorem continuous_lift {ψ : R[X] →+* B} (hψ : IsCycloContinuous S ψ) :
    Continuous (lift S hψ) := by
  refine continuous_of_continuousAt_zero (lift S hψ) ?_
  rw [ContinuousAt, map_zero, ((hasBasis_nhds_zero R S).tendsto_iff (closed_nhds_basis (0 : B)))]
  rintro V ⟨hV, hVclosed⟩
  obtain ⟨f, hf⟩ := hψ V hV
  obtain ⟨M, hM⟩ := exists_dvd_cycloChain f.2
  refine ⟨f, trivial, fun x hx ↦ ?_⟩
  rw [SetLike.mem_coe, RingHom.mem_ker] at hx
  refine hVclosed.mem_of_tendsto (tendsto_approxPoly hψ x)
    (eventually_atTop.mpr ⟨M, fun N hMN ↦ ?_⟩)
  refine hf _ ?_
  rw [← AdjoinRoot.mk_eq_zero, ← proj_fromPoly,
    proj_fromPoly_approxPoly_of_dvd (hM.trans (cycloChain_dvd_of_le hMN)) x, hx]

/-- `R`-algebra homomorphism version of `CycloCompletion.lift` when `B` is a complete Hausdorff
topological `R`-algebra. -/
noncomputable def liftAlgHom [Algebra R B] (S : Set ℕ) {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) : CycloCompletion R S →ₐ[R] B :=
  { lift S hψ with
    commutes' r := by
      rw [RingHom.toFun_eq_coe, ← (fromPoly R S).commutes r, lift_fromPoly]
      exact ψ.commutes r }

@[simp]
theorem coe_liftAlgHom [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) :
    ⇑(liftAlgHom S hψ) = ⇑(lift S hψ) :=
  (rfl)

@[simp]
theorem coe_ringHom_liftAlgHom [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) :
    (liftAlgHom S hψ : CycloCompletion R S →+* B) = lift S hψ :=
  (rfl)

theorem liftAlgHom_toRingHom [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) :
    (liftAlgHom S hψ).toRingHom = lift S hψ :=
  (rfl)

@[simp]
theorem liftAlgHom_fromPoly [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) (p : R[X]) :
    liftAlgHom S hψ (fromPoly R S p) = ψ p :=
  lift_fromPoly hψ p

@[simp]
theorem liftAlgHom_comp_fromPoly [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) :
    (liftAlgHom S hψ).comp (fromPoly R S) = ψ :=
  AlgHom.ext (liftAlgHom_fromPoly hψ)

@[fun_prop, continuity]
theorem continuous_liftAlgHom [Algebra R B] {ψ : R[X] →ₐ[R] B}
    (hψ : IsCycloContinuous S ψ.toRingHom) :
    Continuous (liftAlgHom S hψ) :=
  continuous_lift hψ

end CycloCompletion

/-- **Universal property of the cyclotomic completion.** Every `S`-cyclotomically continuous ring
homomorphism `ψ : R[X] →+* B` into a complete Hausdorff topological ring `B` extends uniquely to a
continuous ring homomorphism `CycloCompletion R S →+* B`. -/
theorem completion_universal_property (R : Type*) [CommRing R] (S : Set ℕ)
    {B : Type*} [Ring B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
    (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S,
      ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    ∃! φ : CycloCompletion R S →+* B,
      Continuous φ ∧ φ.comp (fromPoly R S).toRingHom = ψ := by
  refine ⟨CycloCompletion.lift S hψ,
    ⟨CycloCompletion.continuous_lift hψ, CycloCompletion.lift_comp_fromPoly hψ⟩, ?_⟩
  rintro φ ⟨hφ_cont, hφ_comp⟩
  exact CycloCompletion.ringHom_ext_of_continuous hφ_cont (CycloCompletion.continuous_lift hψ)
    (hφ_comp.trans (CycloCompletion.lift_comp_fromPoly hψ).symm)

end UniversalProperty

end TauCeti
