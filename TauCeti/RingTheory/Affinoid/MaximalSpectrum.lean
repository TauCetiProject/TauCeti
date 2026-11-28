/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Jacobson
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Nullstellensatz

public import TauCeti.RingTheory.Spectrum.Maximal.Integral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.RingTheory.Spectrum.Maximal.Topology

/-!
# Maximal ideals of affinoid algebras

The residue field at every maximal ideal of an affinoid algebra over a complete ultrametric
field is finite over the ground field. Consequently, an algebra map into an affinoid algebra
contracts maximal ideals to maximal ideals, even when its source is not affinoid. This gives the
contravariant map on maximal spectra used for classical points of affinoid spaces, which is
surjective for integral maps whose kernel lies in the Jacobson radical; and residue fields at
maximal ideals containing the kernel of an integral algebra map into an affinoid algebra are finite
over the ground field as well. Every affinoid
algebra is moreover a Jacobson ring, so its maximal ideals, the classical points, determine every
radical ideal: each prime ideal is the intersection of the maximal ideals containing it. In
particular, `Sp A` is Zariski connected if and only if `A` is nontrivial and has only trivial
idempotents (`TauCeti.IsAffinoidAlgebra.connectedSpace_maximalSpectrum_iff_idempotent`).

The residue-field finiteness is the affinoid form of the Tate-algebra Nullstellensatz proved in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Nullstellensatz`, and the Jacobson property descends
from `TauCeti.MvPowerSeries.isJacobsonRing` along a presentation.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]

namespace IsAffinoidAlgebra

/-- The residue field of a maximal ideal of an affinoid algebra is finite over the ground
field. -/
theorem finite_quotient_of_isMaximal (hA : IsAffinoidAlgebra K A) (m : Ideal A)
    [m.IsMaximal] : Module.Finite K (A ⧸ m) := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  exact _root_.TauCeti.MvPowerSeries.finite_quotient_of_surjective hπ m

/-- **Affinoid algebras are Jacobson rings.** Every prime ideal of an affinoid algebra is the
intersection of the maximal ideals containing it. -/
theorem isJacobsonRing (hA : IsAffinoidAlgebra K A) : IsJacobsonRing A := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  exact isJacobsonRing_of_surjective ⟨π.toRingHom, hπ⟩

/-- An algebra map into an affinoid algebra contracts a maximal ideal to a maximal ideal.
The source algebra need not itself be affinoid. -/
theorem comap_isMaximal (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) (m : Ideal B)
    [m.IsMaximal] : (m.comap f).IsMaximal := by
  let q : A ⧸ m.comap f →ₐ[K] B ⧸ m := Ideal.quotientMapₐ m f le_rfl
  have : Module.Finite K (B ⧸ m) := hB.finite_quotient_of_isMaximal m
  have : Module.Finite K (A ⧸ m.comap f) :=
    Module.Finite.of_injective q.toLinearMap Ideal.quotientMap_injective
  have : IsDomain (A ⧸ m.comap f) :=
    (Ideal.Quotient.isDomain_iff_prime (m.comap f)).mpr inferInstance
  have hfield : IsField (A ⧸ m.comap f) := IsField.of_isDomain_of_finite K _
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfield

/-- The contravariant map on maximal spectra induced by an algebra map whose target is
affinoid. -/
def maximalSpectrumComap (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    MaximalSpectrum B → MaximalSpectrum A :=
  fun x ↦ ⟨x.asIdeal.comap f, hB.comap_isMaximal f x.asIdeal⟩

@[simp]
theorem maximalSpectrumComap_asIdeal (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (x : MaximalSpectrum B) :
    (hB.maximalSpectrumComap f x).asIdeal = x.asIdeal.comap f := (rfl)

/-- For an integral algebra map into an affinoid algebra, `maximalSpectrumComap` agrees
pointwise with `MaximalSpectrum.comapOfIsIntegral`. -/
theorem maximalSpectrumComap_eq_comapOfIsIntegral (hB : IsAffinoidAlgebra K B)
    (f : A →ₐ[K] B) (hf : f.toRingHom.IsIntegral) (x : MaximalSpectrum B) :
    hB.maximalSpectrumComap f x = MaximalSpectrum.comapOfIsIntegral f.toRingHom hf x :=
  MaximalSpectrum.ext
    ((maximalSpectrumComap_asIdeal hB f x).trans
      (MaximalSpectrum.comapOfIsIntegral_asIdeal f.toRingHom hf x).symm)

/-- For an integral algebra map `f : A →ₐ[K] B` into an affinoid algebra, a maximal ideal `x` of
`A` lies in the range of `hB.maximalSpectrumComap f` if and only if `RingHom.ker f ≤ x.asIdeal`. -/
theorem mem_range_maximalSpectrumComap_of_isIntegral (hB : IsAffinoidAlgebra K B)
    (f : A →ₐ[K] B) (hf : f.toRingHom.IsIntegral) {x : MaximalSpectrum A} :
    x ∈ Set.range (hB.maximalSpectrumComap f) ↔ RingHom.ker f ≤ x.asIdeal := by
  have hfun : hB.maximalSpectrumComap f = MaximalSpectrum.comapOfIsIntegral f.toRingHom hf :=
    funext (hB.maximalSpectrumComap_eq_comapOfIsIntegral f hf)
  rw [hfun]
  exact MaximalSpectrum.mem_range_comapOfIsIntegral_iff f.toRingHom hf

@[simp]
theorem maximalSpectrumComap_id (hA : IsAffinoidAlgebra K A) :
    hA.maximalSpectrumComap (AlgHom.id K A) = id := by
  funext x
  apply MaximalSpectrum.ext
  exact Ideal.comap_idₐ (R := K) x.asIdeal

@[simp]
theorem maximalSpectrumComap_comp {C : Type*} [CommRing C] [Algebra K C]
    (hB : IsAffinoidAlgebra K B) (hC : IsAffinoidAlgebra K C)
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    hC.maximalSpectrumComap (g.comp f) =
      hB.maximalSpectrumComap f ∘ hC.maximalSpectrumComap g := by
  funext x
  apply MaximalSpectrum.ext
  exact (Ideal.comap_comapₐ f g).symm

/-- A surjective algebra map into an affinoid algebra induces an injective map on maximal
spectra. -/
theorem maximalSpectrumComap_injective (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : Function.Injective (hB.maximalSpectrumComap f) := by
  intro x y hxy
  apply MaximalSpectrum.ext
  exact Ideal.comap_injective_of_surjective f hf
    (congrArg MaximalSpectrum.asIdeal hxy)

/-- An integral algebra map into an affinoid algebra whose kernel is contained in the Jacobson
radical induces a surjective map on maximal spectra. -/
theorem maximalSpectrumComap_surjective (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : f.toRingHom.IsIntegral) (hker : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Function.Surjective (hB.maximalSpectrumComap f) :=
  fun x ↦ (hB.mem_range_maximalSpectrumComap_of_isIntegral f hf).mpr
    (hker.trans (sInf_le ⟨bot_le, x.isMaximal⟩))

/-- The residue field of a maximal ideal `m` of `A` is finite over the ground field when `A` maps
integrally into an affinoid algebra with `RingHom.ker f ≤ m`, since `m` lies under a maximal
ideal of the affinoid algebra. The source algebra need not itself be affinoid. -/
theorem finite_quotient_of_isIntegral (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : f.toRingHom.IsIntegral) (m : Ideal A) [m.IsMaximal]
    (hker : RingHom.ker f ≤ m) :
    Module.Finite K (A ⧸ m) := by
  obtain ⟨y, hy⟩ :=
    (hB.mem_range_maximalSpectrumComap_of_isIntegral f hf (x := ⟨m, inferInstance⟩)).mpr hker
  obtain rfl : y.asIdeal.comap f = m := congrArg MaximalSpectrum.asIdeal hy
  have := hB.finite_quotient_of_isMaximal y.asIdeal
  exact Module.Finite.of_injective (Ideal.quotientMapₐ y.asIdeal f le_rfl).toLinearMap
    Ideal.quotientMap_injective

/-- **Zariski connectedness criterion for affinoid spectra.** The classical spectrum `Sp A` of an
affinoid algebra is connected in the Zariski topology if and only if `A` is nontrivial and its only
idempotents are `0` and `1`. -/
theorem connectedSpace_maximalSpectrum_iff_idempotent
    (hA : IsAffinoidAlgebra K A) :
    ConnectedSpace (MaximalSpectrum A) ↔
      Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  have := hA.isJacobsonRing
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · have : IsEmpty (MaximalSpectrum A) := ⟨fun x ↦ x.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    exact ⟨fun h ↦ False.elim (IsEmpty.false h.toNonempty.some),
      fun ⟨hnt, _⟩ ↦ False.elim ((not_nontrivial_iff_subsingleton.mpr hsub) hnt)⟩
  · simp [hnt, MaximalSpectrum.connectedSpace_iff_idempotent (R := A)]

end IsAffinoidAlgebra

end TauCeti
