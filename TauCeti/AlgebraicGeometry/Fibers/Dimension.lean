/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Codimension inside closed subsets and fibres of an affine scheme

For a point `x` of `Spec A`, its codimension inside the closed subset `V(I)` is the height of its
image in `A ⧸ I`. For a ring map `φ : R ⟶ S`, the generizations of a point of `Spec S` in its
fibre over `Spec R` are exactly its generizations in `V(q S)`, where `q` is the prime of `R`
below it, so the codimension in the fibre is the height of its image in `S ⧸ q S`.

## Main declarations

* `TauCeti.AlgebraicGeometry.coheight_zeroLocus_eq_height_map`: the codimension of a point of
  `Spec A` inside `V(I)` is the height of its image in `A ⧸ I`.
* `TauCeti.AlgebraicGeometry.coheight_fiber_eq_height_map`: the codimension of a point in its
  fibre over `Spec R` is the height of its image in `S ⧸ q S`.
-/

public section

open CategoryTheory Order Topology TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- In `Spec A`, the codimension of a point `x` of the closed subset `V(I)`, written as
`{y | I ≤ y.asIdeal}`, inside `V(I)` is the height of the image of `x` in `A ⧸ I`. -/
theorem coheight_zeroLocus_eq_height_map {A : CommRingCat.{u}} (I : Ideal A) (x : Spec A)
    (hx : I ≤ x.asIdeal) :
    coheight (⟨x, hx⟩ : {y : Spec A | I ≤ y.asIdeal}) =
      (x.asIdeal.map (Ideal.Quotient.mk I)).height := by
  let e : {y : Spec A | I ≤ y.asIdeal} ≃o (PrimeSpectrum.zeroLocus (R := A) I)ᵒᵈ :=
    { toEquiv := (Equiv.refl _).trans OrderDual.toDual
      map_rel_iff' := fun {a b} ↦ PrimeSpectrum.le_iff_specializes b.1 a.1 }
  rw [← coheight_orderIso e, ← height_ofDual,
    ← height_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus.symm,
    ← PrimeSpectrum.height_eq_orderHeight]
  congr 1

/-- In `Spec S`, for a ring map `φ : R ⟶ S`, the codimension of a point `x` in its fibre
`{v | Spec.map φ v = Spec.map φ x}` is the height of its image in `S ⧸ q S`, where `q` is the prime
of `R` below `x`: the generizations of `x` in the fibre are exactly its generizations in
`V(q S)`. -/
theorem coheight_fiber_eq_height_map {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : Spec S) :
    coheight (⟨x, rfl⟩ : {v : Spec S | Spec.map φ v = Spec.map φ x}) =
      (x.asIdeal.map (Ideal.Quotient.mk ((Spec.map φ x).asIdeal.map φ.hom))).height := by
  let T : Set (Spec S) := {v | Spec.map φ v = Spec.map φ x}
  let I : Ideal S := (Spec.map φ x).asIdeal.map φ.hom
  have hTI {v : Spec S} (hv : v ∈ T) : I ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (congrArg PrimeSpectrum.asIdeal hv).ge
  have hTup {v v' : Spec S} (hv : v ∈ T) (hvv' : v ≤ v') (hv' : I ≤ v'.asIdeal) : v' ∈ T := by
    have hle : v'.asIdeal ≤ v.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hvv'
    refine PrimeSpectrum.ext (le_antisymm ?_ (Ideal.map_le_iff_le_comap.mp hv'))
    rw [← hv]
    exact Ideal.comap_mono hle
  rw [← coheight_zeroLocus_eq_height_map I x (hTI rfl)]
  exact coheight_eq_of_strictMono
    (fun v : T ↦ (⟨v, hTI v.2⟩ : {v : Spec S | I ≤ v.asIdeal})) (fun _ _ h ↦ h)
    (fun v b h ↦ ⟨⟨b, hTup v.2 h.le b.2⟩, h, rfl⟩) ⟨x, rfl⟩

end TauCeti.AlgebraicGeometry

end
