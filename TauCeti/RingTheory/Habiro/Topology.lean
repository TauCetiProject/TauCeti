/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import TauCeti.RingTheory.Habiro.Basic
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic

import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
# Inverse-limit topology and universal property of cyclotomic completions

For a commutative ring `R` and a set `S : Set ℕ` of root orders, the classical Habiro cyclotomic
completion `CycloCompletion R S = lim←_{f ∈ Φ_S^*} R[q]/(f)` carries the inverse-limit uniformity
and topology induced by the product embedding `CycloCompletion.toPi` into
`∀ f : cycloIndex R S, AdjoinRoot (f : R[X])` where each finite quotient is discrete.

This file equips `CycloCompletion R S` with its uniform topological ring structure, proves that
`toPi` is a closed uniform embedding into the discrete product, packages `CycloCompletion R S` as a
complete separated topological commutative ring via `TauCeti.TopCommRingCat.IsCompleteSeparated`,
describes its neighborhood and uniformity bases by the projection kernels `ker (proj R S f)` (and
equivalently by the principal ideals `(f)` and the countable cofinal chain `cycloChain R S`),
proves density of `fromPoly R S`, and establishes the universal extension property for
cyclotomically continuous ring and `R`-algebra homomorphisms into arbitrary complete Hausdorff
uniform topological rings.

## Main definitions

* `TauCeti.Habiro.CycloCompletion.instUniformSpace`: the inverse-limit uniformity pulled back along
  `toPi R S` from the product of discrete uniformities on `AdjoinRoot (f : R[X])`.
* `TauCeti.Habiro.CycloCompletion.completeSeparated`: `CycloCompletion R S` as an object of
  `TauCeti.CompleteSeparatedTopCommRingCat`.
* `TauCeti.Habiro.CycloCompletion.lift`: the unique continuous ring homomorphism
  `CycloCompletion R S →+* B` extending a cyclotomically continuous ring homomorphism
  `ψ : R[X] →+* B` into a complete Hausdorff uniform topological ring `B`.
* `TauCeti.Habiro.CycloCompletion.liftAlgHom`: the `R`-algebra homomorphism version of `lift`.

## Main results

* `TauCeti.Habiro.CycloCompletion.isClosedEmbedding_toPi`: `toPi R S` is a closed embedding into
  the product of discrete quotients.
* `TauCeti.Habiro.CycloCompletion.isCompleteSeparated`: `CycloCompletion R S` is a complete
  separated topological commutative ring.
* `TauCeti.Habiro.CycloCompletion.hasBasis_nhds_zero`,
  `TauCeti.Habiro.CycloCompletion.hasBasis_nhds_zero_span`, and
  `TauCeti.Habiro.CycloCompletion.hasBasis_nhds_zero_cycloChain`: neighborhood bases at `0` given
  by projection kernels, principal cyclotomic ideals, and the countable cofinal chain.
* `TauCeti.Habiro.CycloCompletion.denseRange_fromPoly`: the polynomial map `fromPoly R S` has dense
  range.
* `TauCeti.Habiro.CycloCompletion.ringHom_ext_of_continuous` and
  `TauCeti.Habiro.CycloCompletion.algHom_ext_of_continuous`: two continuous homomorphisms out of
  `CycloCompletion R S` into a Hausdorff space agreeing on `R[X]` are equal.
* `TauCeti.Habiro.CycloCompletion.completion_universal_property`: every cyclotomically continuous
  ring homomorphism `ψ : R[X] →+* B` into a complete Hausdorff uniform topological ring extends
  uniquely to a continuous ring homomorphism `CycloCompletion R S →+* B`.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. RIMS **40** (2004), 1127–1146,
  §3.1.
-/

public noncomputable section

open Polynomial Filter Topology
open scoped Uniformity

universe u v w

namespace TauCeti.Habiro.CycloCompletion

/-! ### Inverse-limit uniformity, topology, and completeness -/

section Topology

variable (R : Type u) [CommRing R] (S : Set ℕ)

/-- The inverse-limit uniformity on `CycloCompletion R S`, pulled back along `toPi R S` from the
product of discrete uniformities on the quotients `AdjoinRoot (f : R[X])`. -/
instance instUniformSpace : UniformSpace (CycloCompletion R S) :=
  UniformSpace.comap (toPi R S)
    (@Pi.uniformSpace (cycloIndex R S) (fun f => AdjoinRoot (f : R[X])) (fun _ => ⊥))

/-- `toPi R S` is uniformly inducing into the product of discrete quotients. -/
theorem isUniformInducing_toPi
    [u : ∀ f : cycloIndex R S, UniformSpace (AdjoinRoot (f : R[X]))]
    [∀ f : cycloIndex R S, DiscreteUniformity (AdjoinRoot (f : R[X]))] :
    IsUniformInducing (toPi R S) := by
  have hu : u = fun _ => ⊥ := funext fun f => DiscreteUniformity.eq_bot (X := AdjoinRoot (f : R[X]))
  refine ⟨?_⟩
  subst hu
  rfl

/-- `toPi R S` is a uniform embedding into the product of discrete quotients. -/
theorem isUniformEmbedding_toPi
    [∀ f : cycloIndex R S, UniformSpace (AdjoinRoot (f : R[X]))]
    [∀ f : cycloIndex R S, DiscreteUniformity (AdjoinRoot (f : R[X]))] :
    IsUniformEmbedding (toPi R S) :=
  ⟨isUniformInducing_toPi R S, toPi_injective R S⟩

/-- `toPi R S` is topologically inducing into the product of discrete quotients. -/
theorem isInducing_toPi
    [t : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X]))]
    [∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X]))] :
    IsInducing (toPi R S) := by
  have ht : t = fun _ => ⊥ := funext fun f => DiscreteTopology.eq_bot (α := AdjoinRoot (f : R[X]))
  refine ⟨?_⟩
  subst ht
  let : ∀ f : cycloIndex R S, UniformSpace (AdjoinRoot (f : R[X])) := fun _ => ⊥
  have : ∀ f : cycloIndex R S, DiscreteUniformity (AdjoinRoot (f : R[X])) := fun _ => ⟨rfl⟩
  exact (isUniformInducing_toPi R S).isInducing.eq_induced

/-- `toPi R S` is a topological embedding into the product of discrete quotients. -/
theorem isEmbedding_toPi
    [∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X]))]
    [∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X]))] :
    IsEmbedding (toPi R S) :=
  ⟨isInducing_toPi R S, toPi_injective R S⟩

/-- The compatible-family locus `Set.range (toPi R S)` is closed in the product of discrete
quotients. -/
theorem isClosed_range_toPi
    [∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X]))]
    [∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X]))] :
    IsClosed (Set.range (toPi R S)) := by
  rw [range_toPi]
  have hset : (compatSubalgebra R S : Set (∀ f : cycloIndex R S, AdjoinRoot (f : R[X]))) =
      ⋂ (f : cycloIndex R S) (g : cycloIndex R S) (h : (f : R[X]) ∣ g),
        {x | AdjoinRoot.algHomOfDvd R (g : R[X]) (f : R[X]) h (x g) = x f} := by
    ext x
    simp [mem_compatSubalgebra_iff]
  rw [hset]
  refine isClosed_iInter fun f => isClosed_iInter fun g => isClosed_iInter fun h => ?_
  exact isClosed_eq
    (continuous_of_discreteTopology.comp (continuous_apply g))
    (continuous_apply f)

/-- `toPi R S` is a closed embedding into the product of discrete quotients. -/
theorem isClosedEmbedding_toPi
    [∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X]))]
    [∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X]))] :
    IsClosedEmbedding (toPi R S) :=
  ⟨isEmbedding_toPi R S, isClosed_range_toPi R S⟩

/-- `CycloCompletion R S` is a uniform additive group. -/
instance instIsUniformAddGroup : IsUniformAddGroup (CycloCompletion R S) := by
  let : ∀ f : cycloIndex R S, UniformSpace (AdjoinRoot (f : R[X])) := fun _ => ⊥
  have : ∀ f : cycloIndex R S, DiscreteUniformity (AdjoinRoot (f : R[X])) := fun _ => ⟨rfl⟩
  exact IsUniformAddGroup.comap (toPi R S).toAddMonoidHom

/-- `CycloCompletion R S` is a topological ring. -/
instance instIsTopologicalRing : IsTopologicalRing (CycloCompletion R S) := by
  let : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ => ⊥
  have : ∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X])) := fun _ => ⟨rfl⟩
  exact { toContinuousMul := (isInducing_toPi R S).continuousMul (toPi R S) }

/-- `CycloCompletion R S` is a complete separated topological commutative ring. -/
theorem isCompleteSeparated :
    TopCommRingCat.IsCompleteSeparated (TopCommRingCat.of (CycloCompletion R S)) := by
  let : ∀ f : cycloIndex R S, UniformSpace (AdjoinRoot (f : R[X])) := fun _ => ⊥
  have : ∀ f : cycloIndex R S, DiscreteUniformity (AdjoinRoot (f : R[X])) := fun _ => ⟨rfl⟩
  have hpi : TopCommRingCat.IsCompleteSeparated
      (TopCommRingCat.of (∀ f : cycloIndex R S, AdjoinRoot (f : R[X]))) :=
    TopCommRingCat.IsCompleteSeparated.pi
      (f := fun f : cycloIndex R S => TopCommRingCat.of (AdjoinRoot (f : R[X])))
      fun _ => TopCommRingCat.isCompleteSeparated_of_completeSpace_of_t0Space _
  exact TopCommRingCat.IsCompleteSeparated.of_isClosedEmbedding
    (R := TopCommRingCat.of (CycloCompletion R S))
    (S := TopCommRingCat.of (∀ f : cycloIndex R S, AdjoinRoot (f : R[X])))
    ⟨(toPi R S).toRingHom, (isInducing_toPi R S).continuous⟩
    (isClosedEmbedding_toPi R S) hpi

/-- `CycloCompletion R S` is Hausdorff. -/
instance instT2Space : T2Space (CycloCompletion R S) :=
  (isCompleteSeparated R S).t2Space

/-- `CycloCompletion R S` is complete for its inverse-limit uniformity. -/
instance instCompleteSpace : CompleteSpace (CycloCompletion R S) :=
  ((TopCommRingCat.isCompleteSeparated_of_iff_completeSpace_and_t0Space _).mp
    (isCompleteSeparated R S)).1

/-- `CycloCompletion R S` packaged as an object of `CompleteSeparatedTopCommRingCat`. -/
def completeSeparated : CompleteSeparatedTopCommRingCat.{u} :=
  CompleteSeparatedTopCommRingCat.of (CycloCompletion R S)

/-- The underlying `TopCommRingCat` object of `completeSeparated R S`. -/
@[simp]
theorem completeSeparated_obj :
    (completeSeparated R S).obj = TopCommRingCat.of (CycloCompletion R S) :=
  CompleteSeparatedTopCommRingCat.of_obj (CycloCompletion R S)

/-! ### Projections, neighborhood bases, and density -/

/-- Every finite projection `proj R S f` is uniformly continuous into the discrete quotient. -/
theorem uniformContinuous_proj (f : cycloIndex R S)
    [u₀ : UniformSpace (AdjoinRoot (f : R[X]))] [DiscreteUniformity (AdjoinRoot (f : R[X]))] :
    UniformContinuous (proj R S f) := by
  have hu : u₀ = ⊥ := DiscreteUniformity.eq_bot
  subst hu
  let : ∀ g : cycloIndex R S, UniformSpace (AdjoinRoot (g : R[X])) := fun _ => ⊥
  have : ∀ g : cycloIndex R S, DiscreteUniformity (AdjoinRoot (g : R[X])) := fun _ => ⟨rfl⟩
  have hfun : ⇑(proj R S f) = (fun x : ∀ g : cycloIndex R S, AdjoinRoot (g : R[X]) => x f) ∘
      ⇑(toPi R S) := funext fun x => (toPi_apply R S x f).symm
  rw [hfun]
  exact (uniformContinuous_pi.mp uniformContinuous_id f).comp
    (isUniformInducing_toPi R S).uniformContinuous

/-- Every finite projection `proj R S f` is continuous into the discrete quotient. -/
@[fun_prop, continuity]
theorem continuous_proj (f : cycloIndex R S)
    [t₀ : TopologicalSpace (AdjoinRoot (f : R[X]))] [DiscreteTopology (AdjoinRoot (f : R[X]))] :
    Continuous (proj R S f) := by
  have ht : t₀ = ⊥ := DiscreteTopology.eq_bot
  subst ht
  let : ∀ g : cycloIndex R S, TopologicalSpace (AdjoinRoot (g : R[X])) := fun _ => ⊥
  have : ∀ g : cycloIndex R S, DiscreteTopology (AdjoinRoot (g : R[X])) := fun _ => ⟨rfl⟩
  have hfun : ⇑(proj R S f) = (fun x : ∀ g : cycloIndex R S, AdjoinRoot (g : R[X]) => x f) ∘
      ⇑(toPi R S) := funext fun x => (toPi_apply R S x f).symm
  rw [hfun]
  exact (continuous_apply f).comp (isInducing_toPi R S).continuous

/-- The kernel of every finite projection `proj R S f` is clopen in `CycloCompletion R S`. -/
theorem isClopen_ker_proj (f : cycloIndex R S) :
    IsClopen (RingHom.ker (proj R S f).toRingHom : Set (CycloCompletion R S)) := by
  let : TopologicalSpace (AdjoinRoot (f : R[X])) := ⊥
  have : DiscreteTopology (AdjoinRoot (f : R[X])) := ⟨rfl⟩
  exact (isClopen_discrete ({0} : Set (AdjoinRoot (f : R[X])))).preimage (continuous_proj R S f)

/-- The kernel of every finite projection `proj R S f` is open in `CycloCompletion R S`. -/
theorem isOpen_ker_proj (f : cycloIndex R S) :
    IsOpen (RingHom.ker (proj R S f).toRingHom : Set (CycloCompletion R S)) :=
  (isClopen_ker_proj R S f).isOpen

/-- The kernel of every finite projection `proj R S f` is closed in `CycloCompletion R S`. -/
theorem isClosed_ker_proj (f : cycloIndex R S) :
    IsClosed (RingHom.ker (proj R S f).toRingHom : Set (CycloCompletion R S)) :=
  (isClopen_ker_proj R S f).isClosed

/-- Every principal cyclotomic ideal `(f)` is clopen in `CycloCompletion R S`. -/
theorem isClopen_span_fromPoly (f : cycloIndex R S) :
    IsClopen (Ideal.span {fromPoly R S (f : R[X])} : Set (CycloCompletion R S)) := by
  rw [← ker_proj_eq_span]
  exact isClopen_ker_proj R S f

/-- The projection kernels `ker (proj R S f)` form a neighborhood basis at `0`. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : CycloCompletion R S)).HasBasis (fun _ : cycloIndex R S => True)
      (fun f => (RingHom.ker (proj R S f).toRingHom : Set (CycloCompletion R S))) := by
  refine Filter.hasBasis_iff.mpr fun U => ⟨fun hU => ?_, ?_⟩
  · let : ∀ f : cycloIndex R S, TopologicalSpace (AdjoinRoot (f : R[X])) := fun _ => ⊥
    have : ∀ f : cycloIndex R S, DiscreteTopology (AdjoinRoot (f : R[X])) := fun _ => ⟨rfl⟩
    rw [(isInducing_toPi R S).nhds_eq_comap, map_zero, nhds_pi] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    obtain ⟨I, hI, t, ht, hIt⟩ := Filter.mem_pi.mp hV
    refine ⟨∏ g ∈ hI.toFinset, g, trivial, fun x hx => hVU (hIt fun g hg => ?_)⟩
    have hg' : g ∈ hI.toFinset := hI.mem_toFinset.mpr hg
    have hdvd : (g : R[X]) ∣ ((∏ k ∈ hI.toFinset, k : cycloIndex R S) : R[X]) := by
      have hprod : ((∏ k ∈ hI.toFinset, k : cycloIndex R S) : R[X]) =
          ∏ k ∈ hI.toFinset, (k : R[X]) :=
        map_prod (cycloIndex R S).subtype (fun k => k) hI.toFinset
      rw [hprod]
      exact Finset.dvd_prod_of_mem (fun k : cycloIndex R S => (k : R[X])) hg'
    have hgx : proj R S g x = 0 := by
      rw [← map_proj hdvd x]
      rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx
      rw [hx, map_zero]
    have ht0 : (0 : AdjoinRoot (g : R[X])) ∈ t g := mem_of_mem_nhds (ht g)
    simpa only [toPi_apply, hgx] using ht0
  · rintro ⟨f, -, hfU⟩
    exact Filter.mem_of_superset ((isOpen_ker_proj R S f).mem_nhds (by simp)) hfU

/-- The principal cyclotomic ideals `Ideal.span {fromPoly R S f}` form a neighborhood basis at
`0`. -/
theorem hasBasis_nhds_zero_span :
    (𝓝 (0 : CycloCompletion R S)).HasBasis (fun _ : cycloIndex R S => True)
      (fun f => (Ideal.span {fromPoly R S (f : R[X])} : Set (CycloCompletion R S))) := by
  simpa only [ker_proj_eq_span] using hasBasis_nhds_zero R S

/-- The kernels along the countable cofinal chain `cycloChain R S` form a neighborhood basis at
`0`. -/
theorem hasBasis_nhds_zero_cycloChain :
    (𝓝 (0 : CycloCompletion R S)).HasBasis (fun _ : ℕ => True)
      (fun N => (RingHom.ker
        (proj R S ⟨cycloChain R S N, cycloChain_mem R S N⟩).toRingHom :
          Set (CycloCompletion R S))) := by
  refine Filter.hasBasis_iff.mpr fun U => ⟨fun hU => ?_, ?_⟩
  · obtain ⟨f, -, hfU⟩ := (hasBasis_nhds_zero R S).mem_iff.mp hU
    obtain ⟨N, hN⟩ := exists_dvd_cycloChain f.2
    refine ⟨N, trivial, fun x hx => hfU ?_⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx ⊢
    rw [← map_proj (g := ⟨cycloChain R S N, cycloChain_mem R S N⟩) hN x, hx, map_zero]
  · rintro ⟨N, -, hNU⟩
    exact Filter.mem_of_superset
      ((isOpen_ker_proj R S ⟨cycloChain R S N, cycloChain_mem R S N⟩).mem_nhds (by simp)) hNU

variable {R S} in
/-- Neighborhood basis at an arbitrary element `x : CycloCompletion R S` by agreement modulo
`f ∈ cycloIndex R S`. -/
theorem hasBasis_nhds (x : CycloCompletion R S) :
    (𝓝 x).HasBasis (fun _ : cycloIndex R S => True)
      (fun f => {y | proj R S f y = proj R S f x}) := by
  rw [← nhds_translation_sub x]
  refine (hasBasis_nhds_zero R S).comap (· - x) |>.congr (fun _ => Iff.rfl) fun f _ => ?_
  ext y
  rw [Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, map_sub, sub_eq_zero, Set.mem_ofPred_eq]

/-- Uniformity basis on `CycloCompletion R S` by agreement modulo `f ∈ cycloIndex R S`. -/
theorem hasBasis_uniformity :
    (𝓤 (CycloCompletion R S)).HasBasis (fun _ : cycloIndex R S => True)
      (fun f => {p : CycloCompletion R S × CycloCompletion R S |
        proj R S f p.1 = proj R S f p.2}) := by
  rw [uniformity_eq_comap_nhds_zero]
  refine (hasBasis_nhds_zero R S).comap (fun p : CycloCompletion R S × CycloCompletion R S =>
    p.2 - p.1) |>.congr (fun _ => Iff.rfl) fun f _ => ?_
  ext ⟨x, y⟩
  rw [Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, map_sub, sub_eq_zero, eq_comm, Set.mem_ofPred_eq]

/-- `CycloCompletion R S` is first-countable, witnessed by `cycloChain R S`. -/
instance instFirstCountableTopology : FirstCountableTopology (CycloCompletion R S) where
  nhds_generated_countable x := by
    rw [← nhds_translation_sub x]
    have : (𝓝 (0 : CycloCompletion R S)).IsCountablyGenerated :=
      (hasBasis_nhds_zero_cycloChain R S).isCountablyGenerated
    exact Filter.comap.isCountablyGenerated _ _

/-- The polynomial image `fromPoly R S` is dense in `CycloCompletion R S`. -/
theorem denseRange_fromPoly : DenseRange (fromPoly R S) := by
  intro x
  rw [mem_closure_iff_nhds_basis (hasBasis_nhds x)]
  intro f _
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj R S f x)
  exact ⟨fromPoly R S p, Set.mem_range_self p,
    by simpa only [Set.mem_ofPred_eq, proj_fromPoly] using hp⟩

variable {R S}

/-- Two continuous ring homomorphisms out of `CycloCompletion R S` into a Hausdorff space that
agree on `R[X]` are equal. -/
theorem ringHom_ext_of_continuous {B : Type v} [NonAssocSemiring B] [TopologicalSpace B]
    [T2Space B] {φ₁ φ₂ : CycloCompletion R S →+* B}
    (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hcomp : φ₁.comp (fromPoly R S).toRingHom = φ₂.comp (fromPoly R S).toRingHom) :
    φ₁ = φ₂ :=
  DFunLike.ext' <| (denseRange_fromPoly R S).equalizer h₁ h₂ <|
    funext fun p => RingHom.congr_fun hcomp p

/-- Two continuous `R`-algebra homomorphisms out of `CycloCompletion R S` into a Hausdorff space
that agree on `R[X]` are equal. -/
theorem algHom_ext_of_continuous {B : Type v} [Semiring B] [Algebra R B] [TopologicalSpace B]
    [T2Space B] {φ₁ φ₂ : CycloCompletion R S →ₐ[R] B}
    (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hcomp : φ₁.comp (fromPoly R S) = φ₂.comp (fromPoly R S)) :
    φ₁ = φ₂ :=
  DFunLike.ext' <| (denseRange_fromPoly R S).equalizer h₁ h₂ <|
    funext fun p => AlgHom.congr_fun hcomp p

/-- A continuous ring homomorphism out of `CycloCompletion R S` restricts to a cyclotomically
continuous polynomial map. -/
theorem exists_dvd_mem_of_continuous {B : Type v} [NonAssocSemiring B] [TopologicalSpace B]
    {φ : CycloCompletion R S →+* B} (hφ : Continuous φ) {U : Set B} (hU : U ∈ 𝓝 (0 : B)) :
    ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → φ (fromPoly R S p) ∈ U := by
  have hpre : φ ⁻¹' U ∈ 𝓝 (0 : CycloCompletion R S) := by
    have h0 : ContinuousAt φ 0 := hφ.continuousAt
    rw [ContinuousAt, map_zero] at h0
    exact h0 hU
  obtain ⟨f, -, hfU⟩ := (hasBasis_nhds_zero R S).mem_iff.mp hpre
  refine ⟨f, fun p hp => hfU ?_⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    proj_fromPoly, AdjoinRoot.mk_eq_zero]
  exact hp

end Topology

/-! ### Universal extension property -/

section UniversalProperty

variable (R : Type u) [CommRing R] (S : Set ℕ)
variable {B : Type v} [Ring B] [UniformSpace B] [IsUniformAddGroup B]

/-- Internal uniform-continuity criterion for cyclotomically continuous polynomial homomorphisms
under the uniformity pulled back along `fromPoly R S`. -/
private theorem uniformContinuous_of_cyclotomic (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    letI : UniformSpace R[X] := UniformSpace.comap (fromPoly R S) inferInstance
    UniformContinuous ψ := by
  let : UniformSpace R[X] := UniformSpace.comap (fromPoly R S) inferInstance
  have : IsUniformAddGroup R[X] := IsUniformAddGroup.comap (fromPoly R S).toAddMonoidHom
  refine uniformContinuous_of_continuousAt_zero ψ ?_
  rw [ContinuousAt, map_zero]
  intro U hU
  obtain ⟨f, hf⟩ := hψ U hU
  have hker : (RingHom.ker (proj R S f).toRingHom : Set (CycloCompletion R S)) ∈
      𝓝 (0 : CycloCompletion R S) :=
    (isOpen_ker_proj R S f).mem_nhds (by simp)
  have hind : IsInducing (fromPoly R S) := (⟨rfl⟩ : IsUniformInducing (fromPoly R S)).isInducing
  rw [Filter.mem_map, hind.nhds_eq_comap, map_zero]
  refine Filter.mem_of_superset (Filter.preimage_mem_comap hker) fun p hp => hf p ?_
  rw [Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, proj_fromPoly, AdjoinRoot.mk_eq_zero] at hp
  exact hp

variable [IsTopologicalRing B] [T2Space B] [CompleteSpace B]

/-- The unique continuous ring homomorphism `CycloCompletion R S →+* B` extending a cyclotomically
continuous polynomial ring homomorphism `ψ : R[X] →+* B` into a complete Hausdorff uniform
topological ring. -/
def lift (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    CycloCompletion R S →+* B :=
  letI : UniformSpace R[X] := UniformSpace.comap (fromPoly R S) inferInstance
  IsDenseInducing.extendRingHom (i := (fromPoly R S).toRingHom) (f := ψ)
    ⟨rfl⟩ (denseRange_fromPoly R S) (uniformContinuous_of_cyclotomic R S ψ hψ)

/-- The extended ring homomorphism `lift R S ψ hψ` is uniformly continuous. -/
theorem uniformContinuous_lift (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    UniformContinuous (lift R S ψ hψ) := by
  let : UniformSpace R[X] := UniformSpace.comap (fromPoly R S) inferInstance
  exact uniformContinuous_uniformly_extend (e := (fromPoly R S).toRingHom) (f := ψ)
    ⟨rfl⟩ (denseRange_fromPoly R S) (uniformContinuous_of_cyclotomic R S ψ hψ)

/-- The extended ring homomorphism `lift R S ψ hψ` is continuous. -/
@[fun_prop, continuity]
theorem continuous_lift (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    Continuous (lift R S ψ hψ) :=
  (uniformContinuous_lift R S ψ hψ).continuous

/-- `lift R S ψ hψ` agrees with `ψ` on every polynomial `p : R[X]`. -/
@[simp]
theorem lift_fromPoly (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U)
    (p : R[X]) :
    lift R S ψ hψ (fromPoly R S p) = ψ p := by
  let : UniformSpace R[X] := UniformSpace.comap (fromPoly R S) inferInstance
  have hue : IsUniformInducing (fromPoly R S).toRingHom := ⟨rfl⟩
  exact (hue.isDenseInducing (denseRange_fromPoly R S)).extend_eq
    (uniformContinuous_of_cyclotomic R S ψ hψ).continuous p

/-- Composition of `lift R S ψ hψ` with `fromPoly R S` equals `ψ`. -/
@[simp]
theorem lift_comp_fromPoly (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    (lift R S ψ hψ).comp (fromPoly R S : R[X] →+* CycloCompletion R S) = ψ :=
  RingHom.ext (lift_fromPoly R S ψ hψ)

/-- Any continuous ring homomorphism extending `ψ` equals `lift R S ψ hψ`. -/
theorem lift_unique (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U)
    {φ : CycloCompletion R S →+* B} (hφ : Continuous φ)
    (hcomp : φ.comp (fromPoly R S).toRingHom = ψ) :
    φ = lift R S ψ hψ :=
  ringHom_ext_of_continuous hφ (continuous_lift R S ψ hψ)
    (hcomp.trans (lift_comp_fromPoly R S ψ hψ).symm)

/-- Composing `lift` with a continuous ring homomorphism `g : B →+* C` coincides with lifting
`g.comp ψ`. -/
theorem comp_lift {C : Type w} [Ring C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U)
    (g : B →+* C) (hg : Continuous g)
    (hgψ : ∀ U ∈ 𝓝 (0 : C), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → g (ψ p) ∈ U :=
      fun U hU => hψ (g ⁻¹' U) (hg.continuousAt (x := 0) (by rwa [map_zero]))) :
    g.comp (lift R S ψ hψ) = lift R S (g.comp ψ) hgψ :=
  lift_unique R S (g.comp ψ) hgψ (hg.comp (continuous_lift R S ψ hψ)) <| by
    rw [RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, lift_comp_fromPoly]

/-- Universal property of the cyclotomic completion: every cyclotomically continuous ring
homomorphism `ψ : R[X] →+* B` into a complete Hausdorff uniform topological ring extends uniquely
to a continuous ring homomorphism `CycloCompletion R S →+* B`. -/
theorem completion_universal_property (ψ : R[X] →+* B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    ∃! φ : CycloCompletion R S →+* B,
      Continuous φ ∧ φ.comp (fromPoly R S).toRingHom = ψ :=
  ⟨lift R S ψ hψ, ⟨continuous_lift R S ψ hψ, lift_comp_fromPoly R S ψ hψ⟩,
    fun _ ⟨hcont, hcomp⟩ => lift_unique R S ψ hψ hcont hcomp⟩

section AlgHom

variable [Algebra R B]

/-- The unique continuous `R`-algebra homomorphism `CycloCompletion R S →ₐ[R] B` extending a
cyclotomically continuous `R`-algebra homomorphism `ψ : R[X] →ₐ[R] B`. -/
def liftAlgHom (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    CycloCompletion R S →ₐ[R] B where
  __ := lift R S ψ.toRingHom hψ
  commutes' r := by
    rw [← (fromPoly R S).commutes r]
    exact (lift_fromPoly R S ψ.toRingHom hψ _).trans (ψ.commutes r)

/-- The ring homomorphism underlying `liftAlgHom R S ψ hψ` is `lift R S ψ.toRingHom hψ`. -/
@[simp]
theorem toRingHom_liftAlgHom (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    (liftAlgHom R S ψ hψ : CycloCompletion R S →+* B) = lift R S ψ.toRingHom hψ :=
  (rfl)

/-- `liftAlgHom R S ψ hψ` has the same underlying function as `lift R S ψ.toRingHom hψ`. -/
theorem coe_liftAlgHom (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    ⇑(liftAlgHom R S ψ hψ) = ⇑(lift R S ψ.toRingHom hψ) :=
  (rfl)

/-- The extended `R`-algebra homomorphism `liftAlgHom R S ψ hψ` is uniformly continuous. -/
theorem uniformContinuous_liftAlgHom (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    UniformContinuous (liftAlgHom R S ψ hψ) :=
  uniformContinuous_lift R S ψ.toRingHom hψ

/-- The extended `R`-algebra homomorphism `liftAlgHom R S ψ hψ` is continuous. -/
@[fun_prop, continuity]
theorem continuous_liftAlgHom (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    Continuous (liftAlgHom R S ψ hψ) :=
  continuous_lift R S ψ.toRingHom hψ

/-- `liftAlgHom R S ψ hψ` agrees with `ψ` on every polynomial `p : R[X]`. -/
@[simp]
theorem liftAlgHom_fromPoly (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U)
    (p : R[X]) :
    liftAlgHom R S ψ hψ (fromPoly R S p) = ψ p :=
  lift_fromPoly R S ψ.toRingHom hψ p

/-- Composition of `liftAlgHom R S ψ hψ` with `fromPoly R S` equals `ψ`. -/
@[simp]
theorem liftAlgHom_comp_fromPoly (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U) :
    (liftAlgHom R S ψ hψ).comp (fromPoly R S) = ψ :=
  AlgHom.ext (liftAlgHom_fromPoly R S ψ hψ)

/-- Any continuous `R`-algebra homomorphism extending `ψ` equals `liftAlgHom R S ψ hψ`. -/
theorem liftAlgHom_unique (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U)
    {φ : CycloCompletion R S →ₐ[R] B} (hφ : Continuous φ)
    (hcomp : φ.comp (fromPoly R S) = ψ) :
    φ = liftAlgHom R S ψ hψ :=
  algHom_ext_of_continuous hφ (continuous_liftAlgHom R S ψ hψ)
    (hcomp.trans (liftAlgHom_comp_fromPoly R S ψ hψ).symm)

/-- Composing `liftAlgHom` with a continuous `R`-algebra homomorphism `g : B →ₐ[R] C` coincides
with lifting `g.comp ψ`. -/
theorem comp_liftAlgHom {C : Type w} [Ring C] [Algebra R C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    (ψ : R[X] →ₐ[R] B)
    (hψ : ∀ U ∈ 𝓝 (0 : B), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → ψ p ∈ U)
    (g : B →ₐ[R] C) (hg : Continuous g)
    (hgψ : ∀ U ∈ 𝓝 (0 : C), ∃ f : cycloIndex R S, ∀ p : R[X], (f : R[X]) ∣ p → g (ψ p) ∈ U :=
      fun U hU => hψ (g ⁻¹' U) (hg.continuousAt (x := 0) (by rwa [map_zero]))) :
    g.comp (liftAlgHom R S ψ hψ) = liftAlgHom R S (g.comp ψ) hgψ :=
  liftAlgHom_unique R S (g.comp ψ) hgψ (hg.comp (continuous_liftAlgHom R S ψ hψ)) <| by
    rw [AlgHom.comp_assoc, liftAlgHom_comp_fromPoly]

end AlgHom

end UniversalProperty

end TauCeti.Habiro.CycloCompletion
