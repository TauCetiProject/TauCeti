/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom

/-!
# The spectrum point and section defined by an augmentation

For a commutative ring `R` and a commutative `R`-algebra `A`, an augmentation `f : A →ₐ[R] R` is a
retraction of the structure map `algebraMap R A`. Hence `Spec f : Spec R ⟶ Spec A` is a section of
the structure morphism `Spec A ⟶ Spec R`.

For example, the projection `TrivSqZeroExt.fstHom R R R` from the dual numbers `R[ε]` to `R`,
`ε ↦ 0`, is an augmentation, so the structure morphism `Spec R[ε] ⟶ Spec R` is split by the section
`Spec R ⟶ Spec R[ε]` that it induces. Base change along `Spec R[ε] ⟶ Spec R` is the trivial
first-order deformation of a scheme over `R`, and base change along the section
`Spec R ⟶ Spec R[ε]` is reduction modulo `ε`;
`TauCeti.AlgebraicGeometry.PrestableMap.infinitesimalAut` uses this splitting.

An algebra homomorphism `f : H →ₐ[k] k` from a commutative `k`-algebra to an integral domain `k`
determines a point of the algebra's prime spectrum, whose prime ideal is `ker f`: the image of the
generic point of `Spec k`. When `k` is a field this is the `k`-rational point cut out by `f`. This
file records that point and its underlying prime ideal.

## Main declarations

* `AlgHom.specSplitEpi`: the structure morphism `Spec A ⟶ Spec R`, split by the section induced
  by an augmentation `A →ₐ[R] R`.
* `AlgHom.kernelPoint`: the point cut out by the kernel of an augmentation.
* `AlgHom.comap_kernelPoint`: contraction of a kernel point is the kernel point of the
  composite algebra homomorphism.
* `AlgHom.comap_kernelPoint_of_apply_eq`: contraction of a kernel point along a ring homomorphism
  compatible with the augmentations up to an injection of the base rings.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgHom

universe u v w

section SplitEpi

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The structure morphism `Spec A ⟶ Spec R` of a commutative `R`-algebra `A`, split by the
section `Spec R ⟶ Spec A` induced by an augmentation `f : A →ₐ[R] R`. -/
noncomputable def specSplitEpi (f : A →ₐ[R] R) :
    SplitEpi (Spec.map (CommRingCat.ofHom (algebraMap R A))) where
  section_ := Spec.map (CommRingCat.ofHom (f : A →+* R))
  id := by simp

/-- The section of `f.specSplitEpi` is induced by the augmentation `f`. -/
@[simp]
theorem specSplitEpi_section (f : A →ₐ[R] R) :
    f.specSplitEpi.section_ = Spec.map (CommRingCat.ofHom (f : A →+* R)) :=
  (rfl)

end SplitEpi

variable {k : Type u} [CommRing k] [IsDomain k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

/-- The point of `Spec H` defined by an augmentation `f : H →ₐ[k] k` to an integral domain: the
contraction of the zero ideal of `k`. Its prime ideal is `ker f`. -/
def kernelPoint : Spec (CommRingCat.of H) :=
  PrimeSpectrum.comap (f : H →+* k) ⊥

/-- The prime ideal of an augmentation point is the kernel of the augmentation. -/
@[simp]
theorem kernelPoint_asIdeal :
    (kernelPoint f).asIdeal = RingHom.ker (f : H →+* k) := by
  rw [kernelPoint, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot,
    RingHom.ker_eq_comap_bot]

/-- A kernel point belongs to a basic open exactly when its defining homomorphism is
nonzero on the defining element. -/
@[simp]
theorem kernelPoint_mem_basicOpen_iff (a : H) :
    (kernelPoint f : PrimeSpectrum H) ∈ PrimeSpectrum.basicOpen a ↔ f a ≠ 0 := by
  -- Expose ideal membership to bridge the scheme carrier and the prime-spectrum basic open.
  change a ∉ (kernelPoint f).asIdeal ↔ f a ≠ 0
  rw [kernelPoint_asIdeal, RingHom.mem_ker, AlgHom.coe_toRingHom]

/-- Contracting a kernel point along an algebra homomorphism gives the kernel point of the
composite algebra homomorphism. -/
@[simp]
theorem comap_kernelPoint {A : Type w} [CommRing A] [Algebra k A] (g : A →ₐ[k] H) :
    PrimeSpectrum.comap (g : A →+* H) (kernelPoint f) = kernelPoint (f.comp g) :=
  PrimeSpectrum.comap_comp_apply (g : A →+* H) (f : H →+* k) ⊥

/-- Contracting a kernel point along a ring homomorphism `φ` gives the kernel point of `f`, when
`φ` carries `f` to the given augmentation up to an injective homomorphism `ι` of the base rings. -/
theorem comap_kernelPoint_of_apply_eq {k' : Type*} [CommRing k'] [IsDomain k'] {S : Type*}
    [CommRing S] [Algebra k' S] (g : S →ₐ[k'] k') (φ : H →+* S) (ι : k →+* k')
    (hι : Function.Injective ι) (h : ∀ y, g (φ y) = ι (f y)) :
    PrimeSpectrum.comap φ (kernelPoint g) = kernelPoint f := by
  have hφ : (g : S →+* k').comp φ = ι.comp f := RingHom.ext h
  refine PrimeSpectrum.ext ((PrimeSpectrum.comap_asIdeal φ (kernelPoint g)).trans ?_)
  rw [kernelPoint_asIdeal, kernelPoint_asIdeal, RingHom.comap_ker, hφ,
    RingHom.ker_comp_of_injective _ hι]

end AlgHom
