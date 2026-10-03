/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import TauCeti.RingTheory.Invariant.Basic

/-!
# Affine invariant quotients by finite groups

For a group acting on an algebra `A` over an invariant base ring `R`, the affine invariant
quotient is `Spec (Aᴳ)`, with projection induced by the inclusion of the fixed subalgebra.
This file proves its universal property for affine target schemes. When the group is finite,
the projection is integral and surjective, and its topological fibres are precisely the
orbits of prime ideals. If `A` is of finite type over `R`, the projection is finite.

The universal property for affine targets does not require finiteness of the group. Neither
flatness nor finite presentation of the quotient projection is asserted. This file does not
construct the fppf sheaf quotient or prove the universal property for non-affine targets.

The integrality and orbit arguments reuse Mathlib's `Algebra.IsInvariant.isIntegral` and
`Algebra.IsInvariant.exists_smul_of_under_eq`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace TauCeti.AffineInvariantQuotient

universe u v

variable (R A : Type u) (G : Type v) [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- The spectrum of the fixed subalgebra, the affine invariant quotient of `Spec A`. -/
noncomputable abbrev quotient : Scheme.{u} :=
  Spec (CommRingCat.of (FixedPoints.subalgebra R A G))

instance : IsAffine (quotient R A G) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The quotient projection, induced by the inclusion of invariant functions. -/
noncomputable def projection : Spec (CommRingCat.of A) ⟶ quotient R A G :=
  Spec.map (CommRingCat.ofHom (FixedPoints.subalgebra R A G).val.toRingHom)

/-- The structure morphism of the invariant quotient over `Spec R`. -/
noncomputable def structureMap : quotient R A G ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))

/-- The quotient projection lies over the invariant base ring. -/
@[reassoc (attr := simp)]
theorem projection_structureMap :
    projection R A G ≫ structureMap R A G = Spec.algebraMap R A := by
  rw [projection, structureMap, ← Spec.map_comp]
  rfl

/-- The automorphism of the spectrum induced contravariantly by an element of the group. -/
noncomputable def translate (g : G) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g))

@[simp]
theorem translate_one : translate A G 1 = 𝟙 _ := by
  rw [translate, ← Spec.map_id]
  congr 1
  ext a
  exact one_smul G a

/-- Pullback reverses composition: these morphisms form a right action on the spectrum. -/
theorem translate_mul (g h : G) :
    translate A G (g * h) = translate A G g ≫ translate A G h := by
  rw [translate, translate, translate, ← Spec.map_comp]
  congr 1
  ext a
  exact mul_smul g h a

instance (g : G) : IsIso (translate A G g) := by
  refine ⟨⟨translate A G g⁻¹, ?_, ?_⟩⟩
  · rw [← translate_mul, mul_inv_cancel, translate_one]
  · rw [← translate_mul, inv_mul_cancel, translate_one]

/-- The quotient projection is invariant under every group element. -/
@[reassoc (attr := simp)]
theorem translate_projection (g : G) :
    translate A G g ≫ projection R A G = projection R A G := by
  rw [translate, projection, ← Spec.map_comp]
  congr 1
  ext a
  exact a.property g

variable {R A G}

/-- An invariant morphism to an affine scheme pulls back functions to invariant functions. -/
private theorem preimage_mem_fixed {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, translate A G g ≫ f = f) (a : Γ(Y, ⊤)) :
    (Spec.preimage (f ≫ Y.isoSpec.hom)).hom a ∈ FixedPoints.subalgebra R A G := by
  intro g
  have h := congrArg Spec.preimage (congrArg (fun k => k ≫ Y.isoSpec.hom) (hf g))
  simpa [translate, Spec.preimage_comp, CommRingCat.hom_comp] using
    congrArg (fun k => k.hom a) h

/-- Descend an invariant morphism to an affine target through the fixed-subalgebra spectrum. -/
noncomputable def desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, translate A G g ≫ f = f) : quotient R A G ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
      (FixedPoints.subalgebra R A G).toSubring (preimage_mem_fixed (R := R) f hf))) ≫ Y.isoSpec.inv

/-- The descended morphism factors the given invariant morphism. -/
@[reassoc (attr := simp)]
theorem projection_desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, translate A G g ≫ f = f) :
    projection R A G ≫ desc f hf = f := by
  rw [desc, projection, ← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom
      ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
        (FixedPoints.subalgebra R A G).toSubring (preimage_mem_fixed (R := R) f hf)) ≫
      CommRingCat.ofHom (FixedPoints.subalgebra R A G).val.toRingHom =
      Spec.preimage (f ≫ Y.isoSpec.hom) := by
    ext a
    rfl
  rw [h, Spec.map_preimage]
  simp

/-- Morphisms from the invariant quotient to an affine target are determined by their
composition with the projection. -/
@[ext]
theorem hom_ext {Y : Scheme.{u}} [IsAffine Y] {f h : quotient R A G ⟶ Y}
    (hfh : projection R A G ≫ f = projection R A G ≫ h) : f = h := by
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (FixedPoints.subalgebra R A G).val.toRingHom)
    (Subtype.val_injective) ⊤ (isAffineOpen_top Y) (by simp) (by simp)
  exact hfh

/-- The affine-target universal property: every invariant morphism factors uniquely through
the invariant quotient. -/
theorem existsUnique_desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, translate A G g ≫ f = f) :
    ∃! h : quotient R A G ⟶ Y, projection R A G ≫ h = f := by
  exact ⟨desc f hf, projection_desc f hf, fun h hh =>
    hom_ext (hh.trans (projection_desc f hf).symm)⟩

/-- Descending the pullback of an affine-target morphism recovers that morphism. -/
@[simp]
theorem desc_projection {Y : Scheme.{u}} [IsAffine Y] (f : quotient R A G ⟶ Y) :
    desc (projection R A G ≫ f) (fun g => by simp) = f := by
  apply hom_ext
  exact projection_desc _ _

variable (R A G) [Finite G]

instance : IsIntegralHom (projection R A G) := by
  exact IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (Algebra.IsInvariant.isIntegral _ _ G))

/-- The quotient projection is surjective, by lying over for the integral inclusion. -/
instance : Surjective (projection R A G) := by
  let := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R A G) A G
  exact ⟨Algebra.IsIntegral.comap_surjective _ _⟩

/-- A finite-type algebra over an invariant base is module-finite over its fixed subalgebra;
consequently its quotient projection is finite. -/
instance [Algebra.FiniteType R A] : IsFinite (projection R A G) := by
  let := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R A G) A G
  let := Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R A G) A
  let := Algebra.IsIntegral.finite (R := FixedPoints.subalgebra R A G) (A := A)
  exact IsFinite.SpecMap_iff _ |>.mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The projection is a quotient map of topological spaces. -/
theorem isQuotientMap_projection : Topology.IsQuotientMap (projection R A G) :=
  (projection R A G).isClosedMap.isQuotientMap
    (projection R A G).continuous (Surjective.surj (f := projection R A G))

/-- Two points have the same image exactly when their prime ideals are in the same orbit. -/
theorem projection_eq_iff_exists_smul (x y : PrimeSpectrum A) :
    projection R A G x = projection R A G y ↔
      ∃ g : G, y.asIdeal = g • x.asIdeal := by
  -- The underlying map of `Spec.map` is contraction of prime ideals.
  change PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R A G) A) x =
    PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R A G) A) y ↔ _
  rw [PrimeSpectrum.ext_iff]
  simp only [PrimeSpectrum.comap_asIdeal, ← Ideal.under_def]
  constructor
  · intro h
    exact Algebra.IsInvariant.exists_smul_of_under_eq (FixedPoints.subalgebra R A G) A G
      x.asIdeal y.asIdeal h
  · rintro ⟨g, hg⟩
    simpa only [hg] using (Ideal.under_smul (FixedPoints.subalgebra R A G) x.asIdeal g).symm

end TauCeti.AffineInvariantQuotient
