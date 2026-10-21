/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny
public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial
public import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Abelian varieties of dimension zero

An abelian variety of dimension zero is the zero abelian variety `Spec K`. The underlying scheme
of an abelian variety `A` over `K` is integral, so it has dimension zero exactly when it is a single
point (`TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton`). In that case the zero section
`Spec K ⟶ A` is a surjective closed immersion, being a section of the separated structure morphism,
into a reduced scheme; hence it is an isomorphism, and so is the structure morphism `A ⟶ Spec K`.
Consequently `A` is a zero object of the category of abelian varieties, and conversely a zero object
is isomorphic to `AbelianVariety.trivial K`, which has dimension zero.

This settles multiplication by integers in the degenerate dimension: on an abelian variety of
dimension zero every `[n]`, including `[0]`, is the identity. In positive dimension `[0]` is not an
isogeny: it is the constant morphism through the zero section, whose image is a single point, so it
is not surjective. Hence `[0]` is an isogeny exactly in dimension zero, which is why the theorem
that `[n]` is an isogeny must assume `n ≠ 0` for positive-dimensional abelian varieties.

## Main results

* `AbelianVariety.surjective_zeroSection_iff`: the zero section is surjective if and only if `A`
  has dimension zero.
* `AbelianVariety.isIso_zeroSection_iff`, `AbelianVariety.isIso_toOver_hom_iff`: the zero section,
  equivalently the structure morphism `A ⟶ Spec K`, is an isomorphism if and only if `A` has
  dimension zero.
* `AbelianVariety.isZero_iff_dim_eq_zero`: `A` is a zero object of the category of abelian
  varieties over `K` if and only if it has dimension zero.
* `AbelianVariety.mulBy_eq_id_of_dim_eq_zero`: in dimension zero every `[n]` is the identity.
* `AbelianVariety.isIsogeny_mulBy_zero_iff`: `[0]` is an isogeny if and only if `A` has dimension
  zero.

## References

* J. S. Milne, *Abelian Varieties*, I §7, Theorem 7.2: `[n]` is an isogeny for `n ≠ 0`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

namespace AbelianVariety

open scoped Hom

universe u

variable {K : Type u} [Field K] (A : AbelianVariety K)

/-- The zero section of an abelian variety is surjective if and only if the abelian variety has
dimension zero. -/
theorem surjective_zeroSection_iff : Surjective A.zeroSection ↔ A.dim = 0 := by
  rw [dim_def, topologicalKrullDim_eq_zero_iff_subsingleton, surjective_iff]
  constructor
  · intro h
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := h x
    obtain ⟨b, rfl⟩ := h y
    rw [Subsingleton.elim a b]
  · intro _ x
    exact ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩

/-- The zero section `Spec K ⟶ A` of an abelian variety is an isomorphism if and only if the
abelian variety has dimension zero. -/
theorem isIso_zeroSection_iff : IsIso A.zeroSection ↔ A.dim = 0 := by
  refine ⟨fun _ ↦ (surjective_zeroSection_iff A).mp inferInstance, fun h ↦ ?_⟩
  have := (surjective_zeroSection_iff A).mpr h
  have := isClosedImmersion_of_comp_eq_id A.toOver.hom A.zeroSection
    A.zeroSection_comp_toOver_hom
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The structure morphism `A ⟶ Spec K` of an abelian variety is an isomorphism if and only if
the abelian variety has dimension zero. -/
theorem isIso_toOver_hom_iff : IsIso A.toOver.hom ↔ A.dim = 0 := by
  rw [← isIso_zeroSection_iff]
  have h := A.zeroSection_comp_toOver_hom
  constructor
  · intro _
    rw [← IsIso.inv_eq_of_inv_hom_id h]
    infer_instance
  · intro _
    rw [← IsIso.inv_eq_of_hom_inv_id h]
    infer_instance

/-- An abelian variety is a zero object of the category of abelian varieties over `K`, that is,
isomorphic to `AbelianVariety.trivial K`, if and only if it has dimension zero. -/
theorem isZero_iff_dim_eq_zero : IsZero A ↔ A.dim = 0 := by
  refine ⟨fun h ↦ by rw [dim_eq_of_iso (h.iso (isZeroTrivial K)), dim_trivial], fun h ↦ ?_⟩
  have := (isIso_zeroSection_iff A).mpr h
  refine (isZeroTrivial K).of_iso ⟨toTrivial A, fromTrivial A, ?_, Subsingleton.elim _ _⟩
  ext1
  rw [toTrivial_comp_fromTrivial, Hom.toSchemeHom_one, Hom.toSchemeHom_id,
    ← cancel_epi A.zeroSection]
  simp [reassoc_of% A.zeroSection_comp_toOver_hom]

variable {A}

/-- On an abelian variety of dimension zero, multiplication by every integer `n`, including `0`,
is the identity. -/
theorem mulBy_eq_id_of_dim_eq_zero (h : A.dim = 0) (n : ℤ) : mulBy A n = 𝟙 A :=
  ((isZero_iff_dim_eq_zero A).mpr h).eq_of_src _ _

variable (A)

/-- Multiplication by `0` is an isogeny if and only if the abelian variety has dimension zero. In
particular `[0]` is not an isogeny of a positive-dimensional abelian variety. -/
theorem isIsogeny_mulBy_zero_iff : IsIsogeny (mulBy A 0) ↔ A.dim = 0 := by
  refine ⟨fun hf ↦ ?_, fun h ↦ mulBy_eq_id_of_dim_eq_zero h 0 ▸ isIsogeny_id A⟩
  have := hf.surjective
  rw [mulBy_zero, Hom.toSchemeHom_one] at this
  exact (surjective_zeroSection_iff A).mp (Surjective.of_comp A.toOver.hom A.zeroSection)

end AbelianVariety

end AlgebraicGeometry

end TauCeti
