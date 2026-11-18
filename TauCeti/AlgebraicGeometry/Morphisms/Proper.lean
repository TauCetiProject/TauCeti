/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper morphisms and affine schemes

A morphism of affine schemes `Spec S ⟶ Spec R` is proper exactly when `S` is a finite
`R`-module. This is the affine case of Mathlib's characterization of finite morphisms as the
proper affine ones (`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), combined with
the description of finite morphisms of affine schemes
(`AlgebraicGeometry.IsFinite.SpecMap_iff`).

For example, the affine line `Spec R[t] ⟶ Spec R` over a nonzero ring is not proper, since
`R[t]` is not a finite `R`-module.

Over a field, a preconnected scheme that is both affine and universally closed has at most one
point (`AlgebraicGeometry.Scheme.Hom.subsingleton_of_isAffine_of_universallyClosed`): its global
functions are integral over the field (`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`),
and two distinct points would be separated by a clopen set pulled back from the discrete spectrum
of a finite-dimensional subalgebra. So a connected scheme of positive dimension that is proper over
a field, such as a proper curve, is not affine.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes `Spec S ⟶ Spec R` is proper if and only if the ring map
`R → S` is finite. -/
@[simp]
lemma IsProper.SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsProper (Spec.map f) ↔ f.hom.Finite := by
  rw [← IsFinite.SpecMap_iff, IsFinite.iff_isProper_and_isAffineHom,
    and_iff_left (by infer_instance)]

/-- A preconnected scheme that is affine and universally closed over a field has at most one
point. -/
theorem Scheme.Hom.subsingleton_of_isAffine_of_universallyClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [PreconnectedSpace X] [IsAffine X]
    [UniversallyClosed f] : Subsingleton X := by
  -- The ring of global functions `Γ(X, ⊤)` is integral over `K`.
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  -- Two points of `X ≅ Spec Γ(X, ⊤)` are equal when they define the same prime ideal, so it is
  -- enough to show that each global function `r` lies in both primes or in neither.
  let g : X → PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom
  refine ⟨fun x y ↦ X.isoSpec.hom.isOpenEmbedding.injective
    (PrimeSpectrum.ext (Ideal.ext fun r ↦ ?_))⟩
  -- The subalgebra `K[r]` is finite-dimensional, hence Artinian, so its spectrum is discrete and
  -- the induced continuous map from the preconnected space `X` to it is constant.
  let A := Algebra.adjoin K {r}
  have : Module.Finite K A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral r)
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  let h : X → PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A Γ(X, ⊤)) ∘ g
  have hxy : h x = h y :=
    ((PrimeSpectrum.continuous_comap _).comp X.isoSpec.hom.continuous).isConst_of_preconnectedSpace
      x y
  -- The function `r` lies in the prime of a point exactly when `r ∈ K[r]` lies in its image.
  have key (z : X) :
      r ∈ (g z).asIdeal ↔ (⟨r, Algebra.self_mem_adjoin_singleton K r⟩ : A) ∈ (h z).asIdeal := by
    simp [h, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  exact (key x).trans (hxy ▸ (key y).symm)

end AlgebraicGeometry
