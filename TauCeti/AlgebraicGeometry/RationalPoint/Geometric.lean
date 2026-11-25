/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Geometric points of a scheme locally quasi-finite over a field

Let `f : X ⟶ Spec K` be locally quasi-finite, for instance finite, and let `Ω` be an
algebraically closed field over `K`. A *geometric point* of `X` with values in `Ω` is a morphism
`Spec Ω ⟶ X` over `Spec K`.

The residue field of every point `x` of `X` is a finite extension of `K`, so it embeds into `Ω`
over `K`, and `x` is the image of a geometric point
(`Scheme.Hom.exists_comp_eq_and_apply_eq_of_isAlgClosed`). Like `Spec K`, the scheme `X` is
locally Artinian (`IsLocallyArtinian.of_locallyQuasiFinite`), so it is discrete.

Together these read connectedness off geometric points: when `f` has a section `s`, the scheme `X`
is connected exactly when its only geometric point is the one through `s`
(`Scheme.Hom.connectedSpace_iff_forall_eq_comp_of_isAlgClosed`). For instance, a finite group
scheme over a field is connected exactly when it has no geometric point other than the identity.
The field `Ω` must be algebraically closed, not merely separably closed: for a purely inseparable
extension `K' ≠ K`, the disjoint union of `Spec K` and `Spec K'`, with the section through
`Spec K`, is not connected, but `K'` has no embedding over `K` into a separable closure of `K`, so
the only point with values in a separable closure is the one through the section.

For an arbitrary field `Ω` over `K`, the same finiteness of residue fields bounds the Galois
symmetry of points with values in `Ω`: a point `Spec Ω ⟶ X` over `Spec K` corresponds to a point
`y` of `X` with an embedding `κ(y) → Ω` over `K`, so it is fixed by every element of `Gal(Ω/K)`
fixing the image of `κ(y)`, a finite extension of `K`
(`Scheme.Hom.exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_and_apply_eq_of_isAlgClosed`: every point of a
  scheme locally quasi-finite over `K` is the image of a geometric point with values in `Ω`.
* `AlgebraicGeometry.Scheme.Hom.connectedSpace_iff_forall_eq_comp_of_isAlgClosed`: a scheme
  locally quasi-finite over `K` with a section `s` is connected if and only if every geometric
  point with values in `Ω` factors through `s`.
* `AlgebraicGeometry.Scheme.Hom.exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq`:
  for any field `Ω` over `K`, a point of a scheme locally quasi-finite over `K` with values in `Ω`
  is fixed by the elements of `Gal(Ω/K)` fixing a finite extension of `K` in `Ω`.

## References

* [Stacks Project, Tag 00PK](https://stacks.math.columbia.edu/tag/00PK), residue field extensions
  of quasi-finite ring maps are finite.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **A point of a locally quasi-finite `K`-scheme with values in `Ω` is fixed by the fixing
subgroup of a finite extension of `K` in `Ω`.** If `f : X ⟶ Spec K` is locally quasi-finite and
`t : Spec Ω ⟶ X` lifts `Spec Ω ⟶ Spec K` along `f`, then there is a finite-dimensional
intermediate field `L` of `Ω/K` such that `Spec σ ≫ t = t` for every `σ ∈ L.fixingSubgroup`. -/
theorem exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyQuasiFinite f] (t : Spec (.of Ω) ⟶ X)
    (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
      ∀ σ ∈ L.fixingSubgroup, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t = t := by
  -- The lift `t` is a point `y` of `X` together with an embedding `φ : κ(y) → Ω`; the image of
  -- `φ` is the required finite extension `L`.
  obtain ⟨⟨y, φ⟩, rfl⟩ := (X.SpecToEquivOfField Ω).symm.surjective t
  simp only [SpecToEquivOfField_symm_apply] at ht ⊢
  -- The embedding `φ` restricted to the residue field of `Spec K` at the image of `y` is the
  -- algebra map of `K`, after identifying that residue field with `K`.
  have := (f y).isPrime
  have h : CommRingCat.ofHom (algebraMap K (f y).asIdeal.ResidueField) ≫
      (Spec.residueFieldIso (.of K) (f y)).inv ≫ f.residueFieldMap y ≫ φ =
        CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    rw [← ht]
    simp only [Spec.map_comp, Category.assoc]
    rw [Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hφ (k : K) : φ (f.residueFieldMap y ((Spec.residueFieldIso (.of K) (f y)).inv
      (algebraMap K (f y).asIdeal.ResidueField k))) = algebraMap K Ω k := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using congr($h k)
  -- Make `κ(y)` a `K`-algebra through the residue field of `Spec K` at the image of `y`, which is
  -- finite over `K`. Then `κ(y)` is finite over `K`, because `f` is locally quasi-finite, and `φ`
  -- is a `K`-algebra map.
  let ψ : K →+* (Spec (.of K)).residueField (f y) :=
    (Spec.residueFieldIso (.of K) (f y)).inv.hom.comp (algebraMap K (f y).asIdeal.ResidueField)
  have hψ : Function.Surjective ψ := by
    rw [RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
      (Spec.residueFieldIso (.of K) (f y)).inv).surjective.comp
        (f y).asIdeal.algebraMap_residueField_surjective
  algebraize [ψ, (f.residueFieldMap y).hom, (f.residueFieldMap y).hom.comp ψ]
  have : Module.Finite K ((Spec (.of K)).residueField (f y)) :=
    Module.Finite.of_surjective (Algebra.linearMap K _) hψ
  have : Module.Finite K (X.residueField y) :=
    Module.Finite.trans ((Spec (.of K)).residueField (f y)) _
  let φ' : X.residueField y →ₐ[K] Ω := { φ.hom with commutes' := hφ }
  -- Every `σ` fixing the image of `φ` fixes `t`.
  refine ⟨φ'.fieldRange, φ'.equivFieldRange.toLinearEquiv.finiteDimensional, fun σ hσ ↦ ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ ⟨a, rfl⟩

variable {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyQuasiFinite f]

/-- **Points of a scheme quasi-finite over a field are images of geometric points.** If
`f : X ⟶ Spec K` is locally quasi-finite and `Ω` is an algebraically closed field over `K`, every
point `x` of `X` is the image of a morphism `Spec Ω ⟶ X` over `Spec K`. -/
theorem exists_comp_eq_and_apply_eq_of_isAlgClosed (x : X) :
    ∃ g : Spec (.of Ω) ⟶ X, g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ∧
      ∀ p, g p = x := by
  -- `Spec Ω ⟶ Spec K` is an embedding `j` into `Ω` of the residue field at the point of `Spec K`
  obtain ⟨⟨y, j⟩, hj⟩ : ∃ q, (Scheme.SpecToEquivOfField Ω (Spec (.of K))).symm q =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  obtain rfl : f x = y := Subsingleton.elim _ _
  -- `κ(x)` is finite over `κ(f x)`, so it embeds into `Ω` over `κ(f x)` along `j`
  let := (f.residueFieldMap x).hom.toAlgebra
  let := j.hom.toAlgebra
  let ψ : X.residueField x →ₐ[(Spec (.of K)).residueField (f x)] Ω := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, ?_,
    fun _ ↦ X.fromSpecResidueField_apply x _⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hj,
    ← Spec.map_comp_assoc]
  congr 2
  ext a
  exact ψ.commutes a

/-- **Connectedness is read off geometric points.** Let `f : X ⟶ Spec K` be locally quasi-finite,
with a section `s`, and let `Ω` be an algebraically closed field over `K`. Then `X` is connected if
and only if every morphism `Spec Ω ⟶ X` over `Spec K` factors through `s`, that is, `X` has a
single geometric point with values in `Ω`. -/
theorem connectedSpace_iff_forall_eq_comp_of_isAlgClosed {s : Spec (.of K) ⟶ X}
    (hs : s ≫ f = 𝟙 _) :
    ConnectedSpace X ↔ ∀ g : Spec (.of Ω) ⟶ X,
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) →
        g = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ s := by
  -- `X` is locally Artinian, hence discrete, as `Spec K` is
  have : IsLocallyArtinian X := .of_locallyQuasiFinite f
  refine ⟨fun _ g hg ↦ ?_, fun h ↦ ?_⟩
  · -- a connected discrete space is a single point, which is the point of `s`
    have : Subsingleton X := subsingleton_of_preconnected_totallyDisconnected
    rw [← hg]
    exact (TauCeti.AlgebraicGeometry.eq_comp_comp_iff_of_section hs g
      (IsLocalRing.closedPoint Ω)).mpr (Subsingleton.elim _ _)
  · -- every point is the image of a geometric point, which factors through `s`
    have : Subsingleton X := ⟨fun x x' ↦ by
      obtain ⟨g, hg, hgx⟩ := f.exists_comp_eq_and_apply_eq_of_isAlgClosed (Ω := Ω) x
      obtain ⟨g', hg', hgx'⟩ := f.exists_comp_eq_and_apply_eq_of_isAlgClosed (Ω := Ω) x'
      rw [← hgx (IsLocalRing.closedPoint Ω), ← hgx' (IsLocalRing.closedPoint Ω), h g hg,
        h g' hg']⟩
    exact { isPreconnected_univ := Set.subsingleton_univ.isPreconnected
            toNonempty := ⟨s (IsLocalRing.closedPoint K)⟩ }

end AlgebraicGeometry.Scheme.Hom
