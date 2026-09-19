/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.Algebra.MonoidAlgebra.Localization
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme

/-!
# Face localizations of affine toric schemes

A character `m` in the dual semigroup of a cone `σ` is nonnegative on `σ`, so it cuts out the face
`σ ⊓ ker m` of `σ` (`PointedCone.isFaceOf_inf_ker`). The inclusion of that face into `σ` induces
the restriction map from the coordinate ring of `σ` to the coordinate ring of the face. When `σ`
is finitely generated, this map is the localization away from the monomial of `m`: the dual
semigroup of the face is obtained from that of `σ` by adjoining `-m`
(`TauCeti.Toric.dualSemigroup_inf_ker_eq_sup`). On spectra, the affine toric scheme of the face is
therefore the basic open subscheme of the affine toric scheme of `σ` where the monomial of `m`
does not vanish, and the induced morphism is an open immersion.

These open immersions are the maps along which the affine toric schemes of a fan are glued.

## Main declarations

* `TauCeti.Toric.isLocalization_away_affineCoordinateRingMap_inf_ker`: the coordinate ring of the
  face `σ ⊓ ker m` is the localization of the coordinate ring of `σ` away from the monomial of
  `m`.
* `TauCeti.Toric.isOpenImmersion_affineToricSchemeMap_inf_ker`: the affine toric scheme of the
  face is an open subscheme of the affine toric scheme of `σ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.3.
-/

public section

open AlgebraicGeometry Multiplicative

namespace TauCeti.Toric

universe u

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ : PointedCone ℝ V}

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, the restriction
map from the coordinate ring of `σ` to that of the face `σ ⊓ ker m` is the localization away from
the monomial of `m`. -/
theorem isLocalization_away_affineCoordinateRingMap_inf_ker (hi : IsIntegralLattice i)
    (hσ : σ.FG) (m : dualSemigroup hi σ) :
    letI := (affineCoordinateRingMap
      (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ) hi hi
      (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)).toRingHom.toAlgebra
    IsLocalization.Away (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) := by
  set F := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))
  have hmaps : Set.MapsTo (LinearMap.id : V →ₗ[ℝ] V) F σ := fun _ hx ↦ hx.1
  set f := AddMonoidHom.toMultiplicative
    (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) hmaps)
  have hf : ∀ u, ((toAdd (f u) : dualSemigroup hi F) : N →+ ℤ) = toAdd u := fun u ↦
    coe_dualSemigroupMap_id hi hmaps _
  have hring : (affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      hmaps).toRingHom = MonoidAlgebra.mapDomainRingHom ℂ f := by
    have halg : affineCoordinateRingMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        hmaps = MonoidAlgebra.mapDomainAlgHom ℂ ℂ f := by
      refine MonoidAlgebra.algHom_ext (fun u ↦ ?_) (Subsingleton.elim _ _)
      obtain ⟨u, rfl⟩ := ofAdd.surjective u
      simp [f]
    rw [halg]
    ext <;> simp
  rw [hring]
  refine MonoidAlgebra.isLocalization_away_mapDomainRingHom ℂ f ?_ (ofAdd m) ?_ ?_
  · intro u v huv
    apply toAdd.injective
    apply Subtype.ext
    rw [← hf, ← hf, huv]
  · -- The image of `m` is invertible because `-m` lies in the dual semigroup of the face.
    refine IsUnit.of_mul_eq_one (ofAdd ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩) ?_
    apply toAdd.injective
    apply Subtype.ext
    simp [hf]
  · intro y
    obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ m.2 (toAdd y).2
    refine ⟨n, ofAdd ⟨_, hn⟩, ?_⟩
    apply toAdd.injective
    apply Subtype.ext
    simp [hf]

/-- For a character `m` in the dual semigroup of a finitely generated cone `σ`, the morphism from
the affine toric scheme of the face `σ ⊓ ker m` to that of `σ` is an open immersion. -/
theorem isOpenImmersion_affineToricSchemeMap_inf_ker {N : Type u} [AddCommGroup N]
    {i : N →+ V} (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ) :
    IsOpenImmersion (affineToricSchemeMap
      (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ)
      hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)) := by
  let := (affineCoordinateRingMap
    (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ)
    hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)).toRingHom.toAlgebra
  have := isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  have h := IsOpenImmersion.of_isLocalization
    (S := affineCoordinateRing hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
    (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
  rw [RingHom.algebraMap_toAlgebra] at h
  convert h using 1
  exact affineToricSchemeMap_def ..

end TauCeti.Toric
