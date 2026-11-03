/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Punctured affine space

For a commutative ring `R` and an index type `ι`, the punctured affine space over `R` is the
open subscheme of `𝔸^ι_R = Spec R[Xᵢ]` on which the coordinates `Xᵢ` do not all vanish, that is,
the complement of the zero section. For finite `ι` it is quasi-affine, and for `ι` with at least
two elements over a nonzero ring it is not affine: the punctured plane `𝔸²_R \ 0` is the
standard example.

Following Mathlib's `AlgebraicGeometry.AffineSpace`, the index type lives in `Type v` and the base
ring in `Type (max u v)`, so that the coordinate ring `R[Xᵢ]` lies in the universe of `R` and
punctured affine space is a scheme over `Spec R` in the universe of its test algebras; this covers
`𝔸ⁿ_R \ 0`, indexed by `Fin n`, over a ring in any universe.

Its points with values in an `R`-algebra `A` are the unimodular vectors `v : ι → A`, those whose
entries generate the unit ideal. This file constructs the scheme and the bijection between its
`A`-points and unimodular vectors, natural in `A`; its fppf sheaf of points is
`TauCeti.CommAlgCat.pointsSheaf (puncturedAffineSpace R ι)`.
The punctured plane appears as the quotient of `SL₂` by its upper unipotent subgroup, through the
first column of a matrix.

## Main declarations

* `TauCeti.puncturedAffineSpaceOpens`: the open subset of `Spec R[Xᵢ]` where some coordinate is
  invertible.
* `TauCeti.puncturedAffineSpace`: the punctured affine space as a scheme over `Spec R`.
* `TauCeti.PuncturedAffineSpace.range_specMap_subset_iff`: a morphism `Spec A ⟶ Spec R[Xᵢ]`
  factors through the punctured affine space exactly when the coordinates generate the unit
  ideal of `A`.
* `TauCeti.PuncturedAffineSpace.homEquiv`: morphisms `Spec A ⟶ 𝔸^ι_R \ 0` over `Spec R` are
  unimodular vectors in `A`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise I.3.6 (the punctured plane is quasi-affine but
  not affine).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u v

variable (R : Type (max u v)) [CommRing R] (ι : Type v)

/-- The open subset of `𝔸^ι_R = Spec R[Xᵢ]` where the coordinates do not all vanish: the
complement of the zero locus of the coordinates. -/
noncomputable def puncturedAffineSpaceOpens : (Spec (.of (MvPolynomial ι R))).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (Set.range (MvPolynomial.X : ι → MvPolynomial ι R)))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A prime of `R[Xᵢ]` lies in the punctured affine space exactly when it does not contain every
coordinate. -/
theorem mem_puncturedAffineSpaceOpens_iff (x : Spec (.of (MvPolynomial ι R))) :
    x ∈ puncturedAffineSpaceOpens R ι ↔
      x ∉ PrimeSpectrum.zeroLocus (Set.range (MvPolynomial.X : ι → MvPolynomial ι R)) :=
  Iff.rfl

/-- **Punctured affine space** `𝔸^ι_R \ 0`, the open subscheme of `Spec R[Xᵢ]` where the
coordinates do not all vanish, as a scheme over `Spec R`.

The body is exposed so that its underlying scheme and structure morphism compute: morphisms into
it are built from morphisms into the open subscheme. -/
@[expose] noncomputable def puncturedAffineSpace : Over (Spec (.of R)) :=
  Over.mk ((puncturedAffineSpaceOpens R ι).ι ≫
    ((algSpec (.of R)).obj (op (CommAlgCat.of R (MvPolynomial ι R)))).hom)

namespace PuncturedAffineSpace

/-- The open immersion of punctured affine space into affine space, over `Spec R`. -/
noncomputable def toAffineSpace :
    puncturedAffineSpace R ι ⟶ (algSpec (.of R)).obj (op (CommAlgCat.of R (MvPolynomial ι R))) :=
  Over.homMk (puncturedAffineSpaceOpens R ι).ι

@[simp]
theorem puncturedAffineSpace_hom :
    (puncturedAffineSpace R ι).hom = (puncturedAffineSpaceOpens R ι).ι ≫
      ((algSpec (.of R)).obj (op (CommAlgCat.of R (MvPolynomial ι R)))).hom :=
  (rfl)

@[simp]
theorem toAffineSpace_left :
    (toAffineSpace R ι).left = (puncturedAffineSpaceOpens R ι).ι :=
  (rfl)

variable {R ι}

/-- **Points of punctured affine space.** A morphism `Spec A ⟶ Spec R[Xᵢ]`, given by a ring map
`φ : R[Xᵢ] → A`, factors through punctured affine space exactly when the images of the
coordinates generate the unit ideal of `A`. -/
theorem range_specMap_subset_iff {A : Type (max u v)} [CommRing A] (φ : MvPolynomial ι R →+* A) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆ puncturedAffineSpaceOpens R ι ↔
      Ideal.span (Set.range (φ ∘ MvPolynomial.X)) = ⊤ := by
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span, Set.range_comp,
    ← PrimeSpectrum.preimage_comap_zeroLocus, Set.range_subset_iff,
    Set.eq_empty_iff_forall_notMem]
  simp only [Spec.map_apply, CommRingCat.hom_ofHom]
  -- The points of `Spec A` are the primes of `A`, and membership in the open set is avoidance of
  -- the zero locus (`mem_puncturedAffineSpaceOpens_iff`); both are definitional.
  rfl

instance : Mono (toAffineSpace R ι) :=
  (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono (puncturedAffineSpaceOpens R ι).ι))

variable {A B : CommAlgCat.{max u v} R}

/-- The `R`-algebra map `R[Xᵢ] → A` corresponding to a point of punctured affine space, viewed as
a point of affine space. -/
noncomputable def coordinateAlgHom
    (s : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) :
    MvPolynomial ι R →ₐ[R] A :=
  (algSpec.fullyFaithful.preimage (s ≫ toAffineSpace R ι)).unop.hom

/-- The point of affine space underlying a point of punctured affine space is the spectrum of
its coordinate algebra map. -/
theorem algSpec_map_coordinateAlgHom
    (s : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) :
    (algSpec (.of R)).map (CommAlgCat.ofHom (coordinateAlgHom s)).op =
      s ≫ toAffineSpace R ι := by
  rw [coordinateAlgHom, CommAlgCat.ofHom_hom, Quiver.Hom.op_unop,
    Functor.FullyFaithful.map_preimage]

/-- The coordinates of a point of punctured affine space generate the unit ideal. -/
theorem span_range_coordinateAlgHom_X
    (s : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) :
    Ideal.span (Set.range fun i ↦ coordinateAlgHom s (MvPolynomial.X i)) = ⊤ := by
  refine (range_specMap_subset_iff (coordinateAlgHom s : MvPolynomial ι R →+* A)).mp ?_
  rw [← algSpec_map_left_ofAlgHom, algSpec_map_coordinateAlgHom, Over.comp_left,
    toAffineSpace_left, ← Scheme.Opens.range_ι (puncturedAffineSpaceOpens R ι)]
  rintro _ ⟨x, rfl⟩
  exact ⟨s.left x, (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- Evaluation at a unimodular vector is a morphism `Spec A ⟶ 𝔸^ι_R` landing in punctured affine
space. -/
theorem range_specMap_aeval_subset (v : ι → A) (hv : Ideal.span (Set.range v) = ⊤) :
    Set.range
        (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) v : MvPolynomial ι R →+* A))) ⊆
      Set.range (puncturedAffineSpaceOpens R ι).ι := by
  have hX : (⇑(MvPolynomial.aeval (R := R) v : MvPolynomial ι R →+* A) ∘ MvPolynomial.X) = v :=
    funext fun i ↦ MvPolynomial.aeval_X v i
  rw [Scheme.Opens.range_ι, range_specMap_subset_iff, hX]
  exact hv

/-- Evaluation at a unimodular vector, as a morphism into the open subscheme. -/
private noncomputable def toOpens (v : ι → A) (hv : Ideal.span (Set.range v) = ⊤) :
    Spec (.of A) ⟶ (puncturedAffineSpaceOpens R ι : Scheme) :=
  IsOpenImmersion.lift (puncturedAffineSpaceOpens R ι).ι
    (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) v : MvPolynomial ι R →+* A)))
    (range_specMap_aeval_subset v hv)

private theorem toOpens_ι (v : ι → A) (hv : Ideal.span (Set.range v) = ⊤) :
    toOpens v hv ≫ (puncturedAffineSpaceOpens R ι).ι =
      ((algSpec (.of R)).map (CommAlgCat.ofHom (MvPolynomial.aeval (R := R) v)).op).left :=
  (IsOpenImmersion.lift_fac _ _ _).trans (algSpec_map_left_ofAlgHom R _).symm

/-- The morphism `Spec A ⟶ 𝔸^ι_R \ 0` attached to a unimodular vector of `A`. -/
noncomputable def ofUnimodular (v : ι → A) (hv : Ideal.span (Set.range v) = ⊤) :
    (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι :=
  Over.homMk (toOpens v hv) <| by
    have h := congrArg (· ≫ ((algSpec (.of R)).obj (op (CommAlgCat.of R (MvPolynomial ι R)))).hom)
      (toOpens_ι v hv)
    exact ((Category.assoc _ _ _).symm.trans h).trans (Over.w _)

/-- The point attached to a unimodular vector `v` is, in affine space, the spectrum of evaluation
at `v`. -/
theorem ofUnimodular_comp_toAffineSpace (v : ι → A) (hv : Ideal.span (Set.range v) = ⊤) :
    ofUnimodular v hv ≫ toAffineSpace R ι =
      (algSpec (.of R)).map (CommAlgCat.ofHom (MvPolynomial.aeval (R := R) v)).op :=
  Over.OverMorphism.ext (toOpens_ι v hv)

/-- The coordinate algebra map of the point attached to a unimodular vector `v` is evaluation
at `v`. -/
@[simp]
theorem coordinateAlgHom_ofUnimodular (v : ι → A) (hv : Ideal.span (Set.range v) = ⊤) :
    coordinateAlgHom (ofUnimodular v hv) = MvPolynomial.aeval (R := R) v := by
  rw [coordinateAlgHom, ofUnimodular_comp_toAffineSpace, Functor.FullyFaithful.preimage_map,
    Quiver.Hom.unop_op, CommAlgCat.hom_ofHom]

/-- A point of punctured affine space is the point attached to its coordinates. -/
@[simp]
theorem ofUnimodular_coordinateAlgHom
    (s : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) :
    ofUnimodular (fun i ↦ coordinateAlgHom s (MvPolynomial.X i))
      (span_range_coordinateAlgHom_X s) = s := by
  rw [← cancel_mono (toAffineSpace R ι), ofUnimodular_comp_toAffineSpace,
    ← algSpec_map_coordinateAlgHom]
  congr 3
  exact (MvPolynomial.aeval_unique (R := R) _).symm

variable (R ι A) in
/-- **The points of punctured affine space are the unimodular vectors.** Morphisms
`Spec A ⟶ 𝔸^ι_R \ 0` over `Spec R` correspond to vectors `v : ι → A` whose entries generate the
unit ideal, through the coordinates of `𝔸^ι_R`. -/
noncomputable def homEquiv :
    ((algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) ≃
      {v : ι → A // Ideal.span (Set.range v) = ⊤} where
  toFun s := ⟨fun i ↦ coordinateAlgHom s (MvPolynomial.X i), span_range_coordinateAlgHom_X s⟩
  invFun v := ofUnimodular v.1 v.2
  left_inv s := ofUnimodular_coordinateAlgHom s
  right_inv v := Subtype.ext <| funext fun i ↦ by simp

/-- The `i`-th coordinate of a point of punctured affine space. -/
@[simp]
theorem coe_homEquiv_apply
    (s : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) (i : ι) :
    (homEquiv R ι A s : ι → A) i = coordinateAlgHom s (MvPolynomial.X i) :=
  (rfl)

@[simp]
theorem homEquiv_symm_apply (v : {v : ι → A // Ideal.span (Set.range v) = ⊤}) :
    (homEquiv R ι A).symm v = ofUnimodular v.1 v.2 :=
  (rfl)

/-- The coordinates of a point of punctured affine space are natural in the value algebra:
restricting along `f : A ⟶ B` applies `f` to each coordinate. -/
@[simp]
theorem coordinateAlgHom_comp (f : A ⟶ B)
    (s : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι) :
    coordinateAlgHom ((algSpec (.of R)).map f.op ≫ s) = f.hom.comp (coordinateAlgHom s) := by
  rw [coordinateAlgHom, coordinateAlgHom, Category.assoc, Functor.FullyFaithful.preimage_comp,
    Functor.FullyFaithful.preimage_map, unop_comp, Quiver.Hom.unop_op, CommAlgCat.hom_comp]

/-- Points of punctured affine space are determined by their coordinates. -/
theorem hom_ext {s s' : (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R ι}
    (h : ∀ i, coordinateAlgHom s (MvPolynomial.X i) = coordinateAlgHom s' (MvPolynomial.X i)) :
    s = s' :=
  (homEquiv R ι A).injective <| Subtype.ext <| funext h

end PuncturedAffineSpace

end TauCeti
