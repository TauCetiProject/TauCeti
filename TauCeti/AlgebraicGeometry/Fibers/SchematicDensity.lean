/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Fibers
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Image
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic density of the generic fibre

For a flat scheme over a commutative ring, scalar extension along an injective algebra map is
scheme-theoretically dominant. For a domain and its fraction field, this is the canonical
generic-fibre inclusion.
Consequently, two morphisms into a separated target agree whenever their restrictions to this
fibre agree. Neither reducedness nor finite presentation of the source is needed.

Over a Bezout domain `R`, for instance a discrete valuation ring, the converse holds: a scheme over
`R` whose generic fibre is scheme-theoretically dense is flat, because it is then the
scheme-theoretic image of a scheme over the fraction field. Hence flatness over `R` passes from
a flat scheme to the target of any scheme-theoretically dominant morphism out of it; for instance,
from the complement of an effective Cartier divisor to the whole scheme.

This is the density argument used for uniqueness of extensions on flat models over valuation
rings; see Q. Liu, *Algebraic Geometry and Arithmetic Curves*, §4.3 (Proposition 4.3.9 for the
flatness criterion over Dedekind schemes). The construction uses Mathlib's stability of schematic
dominance under flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

variable (R K : Type u) [CommRing R]
variable [CommRing K] [Algebra R K]
variable {X Y : Scheme.{u}}

/-- Scalar extension of a flat scheme along an injective algebra map is schematically dominant.
For a domain and its fraction field, the generic fibre is schematically dense in the total space. -/
theorem isSchemeTheoreticallyDominant_genericFiberι
    (hRK : Function.Injective (algebraMap R K)) (toBase : X ⟶ Spec (.of R)) [Flat toBase] :
    IsSchemeTheoreticallyDominant (genericFiberι R K toBase) := by
  have : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rwa [isSchemeTheoreticallyDominant_SpecMap_iff, CommRingCat.hom_ofHom]
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (isPullback_genericFiber R K toBase).flip

/-- Morphisms over a ring from a flat source to a separated target are determined by their
restriction after an injective scalar extension. In particular the source need not be reduced. -/
theorem ext_of_genericFiberι_eq (hRK : Function.Injective (algebraMap R K))
    (toBase : X ⟶ Spec (.of R)) [Flat toBase]
    (s : Y ⟶ Spec (.of R)) [IsSeparated s] {f g : X ⟶ Y}
    (h : f ≫ s = g ≫ s) (hK : genericFiberι R K toBase ≫ f = genericFiberι R K toBase ≫ g) :
    f = g := by
  have := isSchemeTheoreticallyDominant_genericFiberι R K hRK toBase
  exact ext_of_isSchemeTheoreticallyDominant (genericFiberι R K toBase) s h hK

/-- Over a Bezout domain `R`, a scheme whose generic fibre is scheme-theoretically dense is flat.
This is the converse of `TauCeti.isSchemeTheoreticallyDominant_genericFiberι`. -/
theorem flat_of_isSchemeTheoreticallyDominant_genericFiberι {R : Type u} (K : Type u) [CommRing R]
    [IsDomain R] [IsBezout R] [Field K] [Algebra R K] [FaithfulSMul R K]
    (toBase : X ⟶ Spec (.of R)) [IsSchemeTheoreticallyDominant (genericFiberι R K toBase)] :
    Flat toBase := by
  have := (genericFiberι R K toBase).flat_imageι_comp toBase (genericFiber R K toBase).hom
    (genericFiberι_toBase R K toBase)
  -- A scheme-theoretically dominant morphism has trivial kernel, so its image is everything.
  have : IsIso (genericFiberι R K toBase).imageι := by
    delta Scheme.Hom.imageι Scheme.Hom.image
    rw [(genericFiberι R K toBase).ker_eq_bot]
    infer_instance
  rw [← IsIso.inv_hom_id_assoc (genericFiberι R K toBase).imageι toBase]
  infer_instance

/-- Over a Bezout domain `R`, the target of a scheme-theoretically dominant morphism from a flat
scheme over `R` is flat over `R`. -/
theorem flat_of_isSchemeTheoreticallyDominant_of_flat_comp {R : Type u} [CommRing R] [IsDomain R]
    [IsBezout R] {Z : Scheme.{u}} (h : Z ⟶ X) [IsSchemeTheoreticallyDominant h]
    (toBase : X ⟶ Spec (.of R)) [Flat (h ≫ toBase)] : Flat toBase := by
  let K := FractionRing R
  have := isSchemeTheoreticallyDominant_genericFiberι R K
    (FaithfulSMul.algebraMap_injective R K) (h ≫ toBase)
  -- The generic fibre of `Z` maps to `X` through the generic fibre of `X`.
  let m := pullback.map (h ≫ toBase) (Spec.map (CommRingCat.ofHom (algebraMap R K))) toBase
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) h (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsSchemeTheoreticallyDominant (m ≫ genericFiberι R K toBase) := by
    rw [show m ≫ genericFiberι R K toBase = genericFiberι R K (h ≫ toBase) ≫ h from
      pullback.lift_fst _ _ _]
    infer_instance
  have := IsSchemeTheoreticallyDominant.of_comp m (genericFiberι R K toBase)
  exact flat_of_isSchemeTheoreticallyDominant_genericFiberι K toBase

end TauCeti
