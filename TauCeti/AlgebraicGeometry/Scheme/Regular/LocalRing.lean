/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Regular local rings of schemes

On an affine open with Noetherian ring of sections, regularity of that ring is equivalent to
regularity of the local rings at every point of the open. In particular, a Noetherian ring is
regular exactly when the local rings of its spectrum are regular. Open immersions identify local
rings, so they preserve and reflect their regularity.

More generally, an étale morphism `f : X ⟶ Y` induces at each point `x` a flat local
homomorphism `𝒪_{Y, f x} ⟶ 𝒪_{X, x}`, essentially of finite type, under which the maximal ideal
of the source generates the maximal ideal of the target. Such a homomorphism is faithfully flat,
so Noetherianity descends along it, and it ascends because the target is a localization of a
finitely generated algebra. Between Noetherian local rings it preserves the Krull dimension and
both preserves and reflects regularity
(`TauCeti.isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq`).

## Main declarations

* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_isRegularRing`
* `TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk`
* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_Spec`
* `TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk_Spec`
* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_isOpenImmersion`
* `TauCeti.AlgebraicGeometry.isNoetherianRing_stalk_iff_of_etale`
* `TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale`
* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etale`
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- If the sections over an affine open `U` form a regular ring, the local rings at the points of
`U` are regular. -/
theorem isRegularLocalRing_stalk_of_isRegularRing {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsRegularRing Γ(X, U)] {x : X} (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact .of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- The sections over an affine open `U` with Noetherian ring of sections form a regular ring
exactly when the local rings at the points of `U` are regular. -/
theorem isRegularRing_iff_isRegularLocalRing_stalk {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    IsRegularRing Γ(X, U) ↔ ∀ x ∈ U, IsRegularLocalRing (X.presheaf.stalk x) := by
  refine ⟨fun _ _ hx ↦ isRegularLocalRing_stalk_of_isRegularRing hU hx, fun h ↦ ?_⟩
  refine isRegularRing_iff.mpr fun p _ ↦ ?_
  -- The prime `p` is the prime of the point `hU.fromSpec y` of `U`, whose stalk is `Γ(X, U)_p`.
  let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  have := h _ hy
  exact .of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

/-- The local rings of the spectrum of a regular ring are regular. -/
instance isRegularLocalRing_stalk_Spec (R : CommRingCat.{u}) [IsRegularRing R] (x : Spec R) :
    IsRegularLocalRing ((Spec R).presheaf.stalk x) :=
  have : IsRegularRing Γ(Spec R, ⊤) :=
    .of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  isRegularLocalRing_stalk_of_isRegularRing (isAffineOpen_top _) (Set.mem_univ x)

/-- A Noetherian ring is regular exactly when the local rings of its spectrum are regular. -/
theorem isRegularRing_iff_isRegularLocalRing_stalk_Spec (R : CommRingCat.{u})
    [IsNoetherianRing R] :
    IsRegularRing R ↔ ∀ x : Spec R, IsRegularLocalRing ((Spec R).presheaf.stalk x) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec R, ⊤) := isNoetherianRing_of_ringEquiv R e.symm
  have := (isRegularRing_iff_isRegularLocalRing_stalk (isAffineOpen_top (Spec R))).mpr
    fun x _ ↦ h x
  exact .of_ringEquiv e

/-- An open immersion `f : X ⟶ Y` identifies the local ring of `X` at `x` with the local ring of
`Y` at `f x`, so one is regular exactly when the other is. -/
theorem isRegularLocalRing_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

section Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X)

/-- The stalk map of an étale morphism, as an algebra, is local, flat and essentially of finite
type, and the maximal ideal of its source generates the maximal ideal of its target. -/
private theorem stalkMap_properties_of_etale :
    letI := (f.stalkMap x).hom.toAlgebra
    IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) ∧
      Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) ∧
      (maximalIdeal (Y.presheaf.stalk (f x))).map
          (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) =
        maximalIdeal (X.presheaf.stalk x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  exact ⟨inferInstance, Flat.stalkMap f x, inferInstance,
    Algebra.FormallyUnramified.map_maximalIdeal⟩

/-- An étale morphism `f : X ⟶ Y` preserves and reflects Noetherian local rings: the local ring of
`Y` at `f x` is Noetherian exactly when the local ring of `X` at `x` is. -/
theorem isNoetherianRing_stalk_iff_of_etale :
    IsNoetherianRing (Y.presheaf.stalk (f x)) ↔ IsNoetherianRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  obtain ⟨_, _, _, -⟩ := stalkMap_properties_of_etale f x
  refine ⟨fun _ ↦
    Algebra.EssFiniteType.isNoetherianRing (Y.presheaf.stalk (f x)) (X.presheaf.stalk x),
    fun _ ↦ ?_⟩
  -- a flat local homomorphism is faithfully flat, and Noetherianity descends along it
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_flat_of_isLocalHom
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (A := X.presheaf.stalk x) <| isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (X.presheaf.stalk x)).toLinearEquiv.symm

/-- An étale morphism `f : X ⟶ Y` preserves the Krull dimension of Noetherian local rings: the
local rings of `Y` at `f x` and of `X` at `x` have the same dimension. -/
theorem ringKrullDim_stalk_eq_of_etale [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    ringKrullDim (Y.presheaf.stalk (f x)) = ringKrullDim (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  obtain ⟨_, _, _, h⟩ := stalkMap_properties_of_etale f x
  have := (isNoetherianRing_stalk_iff_of_etale f x).mp ‹_›
  exact (TauCeti.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq h).symm

/-- An étale morphism `f : X ⟶ Y` preserves and reflects regularity of local rings: the local
ring of `Y` at `f x` is regular exactly when the local ring of `X` at `x` is. -/
theorem isRegularLocalRing_stalk_iff_of_etale :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) ↔ IsRegularLocalRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  obtain ⟨_, _, _, h⟩ := stalkMap_properties_of_etale f x
  refine ⟨fun hy ↦ ?_, fun hx ↦ ?_⟩
  · have := (isNoetherianRing_stalk_iff_of_etale f x).mp inferInstance
    exact (TauCeti.isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq h).mpr hy
  · have := (isNoetherianRing_stalk_iff_of_etale f x).mpr inferInstance
    exact (TauCeti.isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq h).mp hx

end Etale

end AlgebraicGeometry

end TauCeti
