/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MaximalIdealPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.GlobalSections

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.LocalRing
import TauCeti.RingTheory.Affinoid.MaximalSpectrum
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.ResidueField

/-!
# The Zariski topology on an adic spectrum

A common zero locus in `Spa(A, A⁺)` is the inverse image of an algebraic zero locus along the
support map to `Spec A`. These loci are the closed sets of the Zariski topology on the adic
spectrum. For an affinoid algebra over a complete nonarchimedean field, the classical points of
a zero locus already determine its radical ideal. In particular, this lets one compare closed
subsets of a rigid affinoid by comparing their classical traces.

The affinoid zero loci are those of Howe and Klevdal, *Admissible pairs and p-adic Hodge structures
II: the bi-analytic Ax–Lindemann theorem*, arXiv:2308.11064v2, §1.1. The construction uses the
algebraic zero locus and vanishing ideal in Mathlib's `PrimeSpectrum`, and
`TauCeti.ValuationSpectrum.maximalSpectrumToSpa` for the classical points.
-/

public section

namespace TauCeti.ValuationSpectrum

open Set TopologicalSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] (Aplus : Subring A)

/-- The common zero locus of an ideal in `Spa(A, A⁺)`. -/
def spaZeroLocus (I : Ideal A) : Set (spa Aplus) :=
  (suppFun ∘ Subtype.val) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)

/-- A point lies in the zero locus if its support contains the ideal. -/
@[simp]
theorem mem_spaZeroLocus {I : Ideal A} {x : spa Aplus} :
    x ∈ spaZeroLocus Aplus I ↔ I ≤ x.val.supp := by
  simp only [spaZeroLocus, mem_preimage, Function.comp_apply, PrimeSpectrum.mem_zeroLocus,
    suppFun_asIdeal, SetLike.coe_subset_coe]

/-- The vanishing ideal of a subset of `Spa(A, A⁺)` is the intersection of the supports of
its points. -/
def spaVanishingIdeal (Z : Set (spa Aplus)) : Ideal A :=
  PrimeSpectrum.vanishingIdeal ((suppFun ∘ Subtype.val) '' Z)

/-- An element belongs to the vanishing ideal if it vanishes at every point of the set. -/
@[simp]
theorem mem_spaVanishingIdeal {Z : Set (spa Aplus)} {a : A} :
    a ∈ spaVanishingIdeal Aplus Z ↔ ∀ x ∈ Z, a ∈ x.val.supp := by
  simp only [spaVanishingIdeal, PrimeSpectrum.mem_vanishingIdeal, forall_mem_image,
    Function.comp_apply, suppFun_asIdeal]

/-- Containment in a zero locus is equivalent to containment in the vanishing ideal in the
opposite direction. -/
theorem subset_spaZeroLocus_iff_le_spaVanishingIdeal {Z : Set (spa Aplus)} {I : Ideal A} :
    Z ⊆ spaZeroLocus Aplus I ↔ I ≤ spaVanishingIdeal Aplus Z := by
  rw [spaVanishingIdeal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal,
    image_subset_iff, spaZeroLocus]

/-- The vanishing ideal of every subset of the adic spectrum is radical. -/
theorem isRadical_spaVanishingIdeal (Z : Set (spa Aplus)) :
    (spaVanishingIdeal Aplus Z).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- Taking the radical leaves the zero locus unchanged. -/
@[simp]
theorem spaZeroLocus_radical (I : Ideal A) :
    spaZeroLocus Aplus I.radical = spaZeroLocus Aplus I := by
  rw [spaZeroLocus, spaZeroLocus, PrimeSpectrum.zeroLocus_radical]

/-- The zero locus of the zero ideal is the whole spectrum. -/
@[simp]
theorem spaZeroLocus_bot : spaZeroLocus Aplus ⊥ = univ := by
  simp [spaZeroLocus]

/-- The unit ideal has empty zero locus. -/
@[simp]
theorem spaZeroLocus_top : spaZeroLocus Aplus ⊤ = ∅ := by
  simp [spaZeroLocus, PrimeSpectrum.zeroLocus_univ]

/-- The zero locus of a product is the union of the two zero loci. -/
theorem spaZeroLocus_mul (I J : Ideal A) :
    spaZeroLocus Aplus (I * J) = spaZeroLocus Aplus I ∪ spaZeroLocus Aplus J := by
  simp only [spaZeroLocus, PrimeSpectrum.zeroLocus_mul, preimage_union]

/-- The zero locus of a sum of ideals is the intersection of their zero loci. -/
theorem spaZeroLocus_iSup {ι : Sort*} (I : ι → Ideal A) :
    spaZeroLocus Aplus (⨆ i, I i) = ⋂ i, spaZeroLocus Aplus (I i) := by
  simp only [spaZeroLocus, PrimeSpectrum.zeroLocus_iSup, preimage_iInter]

/-- The Zariski topology on `Spa(A, A⁺)` is induced by the support map to `Spec A`. -/
@[implicit_reducible]
def spaZariskiTopology : TopologicalSpace (spa Aplus) :=
  induced (suppFun ∘ Subtype.val) inferInstance

/-- The Zariski topology is coarser than the adic topology. -/
theorem le_spaZariskiTopology : inferInstanceAs (TopologicalSpace (spa Aplus)) ≤
    spaZariskiTopology Aplus :=
  continuous_iff_le_induced.mp (continuous_suppFun.comp continuous_subtypeVal)

/-- The Zariski closed sets of `Spa(A, A⁺)` are exactly the common zero loci of ideals. -/
theorem isClosed_spaZariskiTopology_iff {Z : Set (spa Aplus)} :
    @IsClosed _ (spaZariskiTopology Aplus) Z ↔ ∃ I : Ideal A, spaZeroLocus Aplus I = Z := by
  rw [spaZariskiTopology, isClosed_induced_iff]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal T).mp hT
    exact ⟨I, rfl⟩
  · rintro ⟨I, rfl⟩
    exact ⟨_, PrimeSpectrum.isClosed_zeroLocus (I : Set A), rfl⟩

/-- The zero locus of the vanishing ideal is the Zariski closure. -/
theorem spaZeroLocus_spaVanishingIdeal_eq_closure (Z : Set (spa Aplus)) :
    spaZeroLocus Aplus (spaVanishingIdeal Aplus Z) = @closure _ (spaZariskiTopology Aplus) Z := by
  let : TopologicalSpace (spa Aplus) := spaZariskiTopology Aplus
  have h : Topology.IsInducing (suppFun ∘ (Subtype.val : spa Aplus → Spv A)) :=
    Topology.IsInducing.induced _
  rw [spaZeroLocus, spaVanishingIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (h.closure_eq_preimage_closure_image Z).symm

/-- Inverse images of zero loci along continuous ring homomorphisms preserving the chosen
subrings are zero loci of extended ideals. -/
theorem spaComap_preimage_spaZeroLocus
    {B : Type*} [CommRing B] [TopologicalSpace B] (φ : A →+* B) (hφ : Continuous φ)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (I : Ideal A) :
    spaComap φ hφ Aplus Bplus hplus ⁻¹' spaZeroLocus Aplus I =
      spaZeroLocus Bplus (I.map φ) := by
  ext x
  simp only [mem_preimage, mem_spaZeroLocus, spaComap_val, supp_comap,
    Ideal.map_le_iff_le_comap]

/-- Inverse images of zero loci along Huber-pair morphisms are zero loci of extended ideals. -/
@[simp]
theorem _root_.TauCeti.Huber.Pair.Hom.preimage_spaZeroLocus
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing A] [Huber.IsHuberRing A]
    [IsTopologicalRing B] [Huber.IsHuberRing B]
    {S : Huber.Pair A} {T : Huber.Pair B} (f : S.Hom T) (I : Ideal A) :
    f.spaComap ⁻¹' spaZeroLocus S.plus I = spaZeroLocus T.plus (I.map f.toRingHom) := by
  rw [Huber.Pair.Hom.spaComap_def, spaComap_preimage_spaZeroLocus]

section Stalk

open Huber

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [CompleteSpace R] [T0Space R]
  (P : PairOfDefinition R) {Rplus : Subring R}

/-- A point of a complete affinoid spectrum lies in the zero locus of `I` exactly when the
extension of `I` to its stalk is proper. Equivalently, the quotient of the stalk by that extension
is nonzero. -/
theorem mem_spaZeroLocus_iff_map_globalGerm_ne_top
    (hRplus : ∀ ⦃a⦄, a ∈ Rplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Rplus)
    (I : Ideal R) (x : spa Rplus) :
    x ∈ spaZeroLocus Rplus I ↔ I.map (presentationLimitGlobalGerm P Rplus x) ≠ ⊤ := by
  let := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hRplus hP x
  rw [mem_spaZeroLocus, ← comap_presentationLimitGlobalGerm P Rplus hRplus hP x, supp_comap,
    ← Ideal.map_le_iff_le_comap, supp_presentationLimitStalkValuation]
  exact ⟨ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    IsLocalRing.le_maximalIdeal⟩

end Stalk

section Affinoid

open Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NonarchimedeanRing A] [Algebra K A] [ContinuousSMul K A]
  (hA : IsTopologicallyFiniteType (algebraMap K A))

/-- Intersecting the supports of just the classical points in the zero locus recovers the radical
of the defining ideal. -/
theorem spaVanishingIdeal_classicalTrace_spaZeroLocus (I : Ideal A) :
    spaVanishingIdeal (powerBoundedSubring A)
      (range (maximalSpectrumToSpa K hA) ∩ spaZeroLocus (powerBoundedSubring A) I) =
        I.radical := by
  have : IsJacobsonRing A :=
    ((isAffinoidAlgebra_iff K A).mpr hA.exists_surjective_algHom).isJacobsonRing
  rw [I.radical_eq_jacobson]
  ext a
  rw [mem_spaVanishingIdeal, Ideal.jacobson, Submodule.mem_sInf]
  constructor
  · intro ha m hm
    let p : MaximalSpectrum A := ⟨m, hm.2⟩
    have h := ha (maximalSpectrumToSpa K hA p)
      ⟨mem_range_self p, by simpa only [mem_spaZeroLocus, supp_maximalSpectrumToSpa] using hm.1⟩
    rwa [supp_maximalSpectrumToSpa] at h
  · rintro ha _ ⟨⟨m, rfl⟩, hx⟩
    simp only [mem_spaZeroLocus, supp_maximalSpectrumToSpa] at hx ⊢
    exact ha m.asIdeal ⟨hx, m.isMaximal⟩

include hA in
/-- The vanishing ideal of the zero locus in a rigid affinoid spectrum is the radical of the
defining ideal. -/
theorem spaVanishingIdeal_spaZeroLocus (I : Ideal A) :
    spaVanishingIdeal (powerBoundedSubring A) (spaZeroLocus (powerBoundedSubring A) I) =
      I.radical := by
  apply le_antisymm
  · rw [← spaVanishingIdeal_classicalTrace_spaZeroLocus hA I]
    intro a ha
    rw [mem_spaVanishingIdeal] at ha ⊢
    exact fun x hx ↦ ha x hx.2
  · rw [← subset_spaZeroLocus_iff_le_spaVanishingIdeal, spaZeroLocus_radical]

include hA in
/-- Inclusion of zero loci in a rigid affinoid spectrum is reverse inclusion of the corresponding
radical ideals. -/
theorem spaZeroLocus_subset_spaZeroLocus_iff (I J : Ideal A) :
    spaZeroLocus (powerBoundedSubring A) I ⊆ spaZeroLocus (powerBoundedSubring A) J ↔
      J ≤ I.radical := by
  rw [subset_spaZeroLocus_iff_le_spaVanishingIdeal, spaVanishingIdeal_spaZeroLocus hA]

include hA in
/-- Every Zariski closed subset of a rigid affinoid is the zero locus of a unique radical ideal. -/
theorem existsUnique_radical_spaZeroLocus {Z : Set (spa (powerBoundedSubring A))}
    (hZ : @IsClosed _ (spaZariskiTopology (powerBoundedSubring A)) Z) :
    ∃! I : Ideal A, I.IsRadical ∧ spaZeroLocus (powerBoundedSubring A) I = Z := by
  obtain ⟨I, rfl⟩ := (isClosed_spaZariskiTopology_iff _).mp hZ
  refine ⟨I.radical, ⟨I.radical_isRadical, spaZeroLocus_radical _ I⟩, ?_⟩
  rintro J ⟨hJ, hJI⟩
  simpa only [spaVanishingIdeal_spaZeroLocus hA, hJ.radical] using
    congrArg (spaVanishingIdeal (powerBoundedSubring A)) hJI

/-- Zariski closed subsets of a rigid affinoid are determined by their classical traces. -/
theorem eq_of_classicalTrace_eq {Z W : Set (spa (powerBoundedSubring A))}
    (hZ : @IsClosed _ (spaZariskiTopology (powerBoundedSubring A)) Z)
    (hW : @IsClosed _ (spaZariskiTopology (powerBoundedSubring A)) W)
    (h : range (maximalSpectrumToSpa K hA) ∩ Z = range (maximalSpectrumToSpa K hA) ∩ W) :
    Z = W := by
  obtain ⟨I, rfl⟩ := (isClosed_spaZariskiTopology_iff _).mp hZ
  obtain ⟨J, rfl⟩ := (isClosed_spaZariskiTopology_iff _).mp hW
  have heq := congrArg (spaVanishingIdeal (powerBoundedSubring A)) h
  rw [spaVanishingIdeal_classicalTrace_spaZeroLocus hA,
    spaVanishingIdeal_classicalTrace_spaZeroLocus hA] at heq
  rw [← spaZeroLocus_radical _ I, heq, spaZeroLocus_radical]

end Affinoid

end TauCeti.ValuationSpectrum
