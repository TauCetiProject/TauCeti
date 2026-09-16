/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Group.ZPow
public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import TauCeti.Algebra.Group.FreeCommMonoidCharacter
public import TauCeti.Algebra.Group.Prod
public import TauCeti.Geometry.Toric.Analytic.AffinePoint

/-!
# Mixed coordinates on the complex points of a split affine semigroup

An affine semigroup that splits as a product `(ι →₀ ℕ) × (κ →₀ ℤ)` of a free commutative monoid
and a free abelian group has a completely explicit space of complex points: a `ℂ`-algebra
homomorphism out of its monoid algebra is the same data as a family of complex numbers indexed by
`ι` together with a family of units of `ℂ` indexed by `κ`. The exponents of the free monoid factor
are nonnegative, so the corresponding coordinates are unconstrained, while the free abelian factor
contains the inverse of each of its generators and therefore forces the remaining coordinates to
be invertible.

This is the mixed chart `ℂ ^ k × (ℂ ^ *) ^ l` of toric geometry. The dual semigroup of a smooth
`k`-dimensional cone in a lattice of rank `k + l` splits in exactly this way, with `ι` indexing
the rays of the cone and `κ` the remaining vectors of an integral basis extending their primitive
generators; the coordinates indexed by `ι` are the ones that vanish on the boundary of the chart.

The identification is assembled from the universal properties of the two free factors, so it is a
bijection of the functor-of-points carrier and mentions no generating family. The main result is
that it is a homeomorphism for the monomial-embedding topology attached to an arbitrary finite
generating family of the semigroup: the topology of the complex points, defined with no reference
to a splitting, is the product topology of the mixed coordinates. Both directions are computed by
named lemmas, so no consumer has to unfold the equivalence: a coordinate of a point is its value
on the monomial of the corresponding standard generator, and conversely the value of a point on an
arbitrary monomial is the expected mixed monomial in the coordinates.

## Main declarations

* `TauCeti.Toric.regularAffinePointEquiv`: the mixed coordinates of the complex points of a split
  affine semigroup, with `TauCeti.Toric.regularAffinePointEquiv_fst_apply`,
  `TauCeti.Toric.val_regularAffinePointEquiv_snd_apply` and
  `TauCeti.Toric.regularAffinePointEquiv_symm_apply_single` computing the two directions.
* `TauCeti.Toric.continuous_regularAffinePointEquiv` and
  `TauCeti.Toric.continuous_regularAffinePointEquiv_symm`: both directions are continuous for the
  monomial-embedding topology of any finite generating family.
* `TauCeti.Toric.regularAffinePointHomeomorph`: the resulting homeomorphism.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
-/

public section

open Multiplicative Topology

namespace TauCeti.Toric

variable {S : Type*} [AddCommMonoid S] {ι κ : Type*} {r : ℕ}

-- Source: the names `regularAffinePointEquiv` and `regularAffinePointHomeomorph`, the
-- coordinate model `(ι →₀ ℕ) × (κ →₀ ℤ)` and the shape of the two statements follow the target
-- signatures in `AnalyticToricGeometry/Suggested.lean` of the TauCetiProject/TauCetiRoadmap
-- repository.
/-- The mixed coordinates of the complex points of an affine semigroup `S` split as
`(ι →₀ ℕ) × (κ →₀ ℤ)`: a complex point is the same data as a family of complex numbers indexed by
`ι`, the values on the generators of the free commutative monoid factor, and a family of units
indexed by `κ`, the values on the generators of the free abelian factor. -/
noncomputable def regularAffinePointEquiv (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    AffineSemigroupComplexPoint S ≃ (ι → ℂ) × (κ → ℂˣ) :=
  (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm.trans <|
    (MulEquiv.monoidHomCongrLeft e.toMultiplicative).toEquiv.trans <|
      (MulEquiv.monoidHomCongrLeft (MulEquiv.prodMultiplicative (ι →₀ ℕ) (κ →₀ ℤ))).toEquiv.trans <|
        MonoidHom.coprodEquiv.symm.toEquiv.trans <|
          Equiv.prodCongr freeCommMonoidCharEquiv.toEquiv
            (MonoidHom.toHomUnitsMulEquiv.trans freeAbelianCharEquiv).toEquiv

/-- The coordinate of a complex point indexed by `i : ι` is its value on the monomial of the
`i`-th generator of the free commutative monoid factor. -/
@[simp]
theorem regularAffinePointEquiv_fst_apply (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ)))
    (x : AffineSemigroupComplexPoint S) (i : ι) :
    (regularAffinePointEquiv e x).1 i =
      x (MonoidAlgebra.single (ofAdd (e.symm (Finsupp.single i 1, 0))) 1) := by
  simp [regularAffinePointEquiv, MonoidAlgebra.lift_symm_apply]

/-- The coordinate of a complex point indexed by `j : κ` is, as a complex number, its value on the
monomial of the `j`-th generator of the free abelian factor. -/
@[simp]
theorem val_regularAffinePointEquiv_snd_apply (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ)))
    (x : AffineSemigroupComplexPoint S) (j : κ) :
    ((regularAffinePointEquiv e x).2 j : ℂ) =
      x (MonoidAlgebra.single (ofAdd (e.symm (0, Finsupp.single j 1))) 1) := by
  simp [regularAffinePointEquiv, MonoidAlgebra.lift_symm_apply]

/-- The inverse of the coordinate indexed by `j : κ` is the value of the point on the monomial of
the opposite generator; this is what makes that coordinate a unit. -/
theorem inv_val_regularAffinePointEquiv_snd_apply (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ)))
    (x : AffineSemigroupComplexPoint S) (j : κ) :
    (((regularAffinePointEquiv e x).2 j)⁻¹ : ℂ) =
      x (MonoidAlgebra.single (ofAdd (e.symm (0, -Finsupp.single j 1))) 1) := by
  have key : ((regularAffinePointEquiv e x).2 j : ℂ) *
      x (MonoidAlgebra.single (ofAdd (e.symm (0, -Finsupp.single j 1))) 1) = 1 := by
    rw [val_regularAffinePointEquiv_snd_apply, ← map_mul, MonoidAlgebra.single_mul_single,
      one_mul, ← ofAdd_add, ← map_add]
    simp [Prod.mk_zero_zero, ← MonoidAlgebra.one_def]
  exact inv_eq_of_mul_eq_one_right key

/-- The complex point attached to a family of mixed coordinates takes, on the monomial of `s : S`,
the mixed monomial value prescribed by the exponents of `s`: a product of natural powers of the
unconstrained coordinates times a product of integral powers of the invertible ones. -/
@[simp]
theorem regularAffinePointEquiv_symm_apply_single (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ)))
    (z : (ι → ℂ) × (κ → ℂˣ)) (s : S) :
    (regularAffinePointEquiv e).symm z (MonoidAlgebra.single (ofAdd s) 1) =
      ((e s).1.prod fun i n => z.1 i ^ n) * ((e s).2.prod fun j n => z.2 j ^ n : ℂˣ) := by
  simp [regularAffinePointEquiv, MonoidAlgebra.lift_single]

/-- Reading off the mixed coordinates is continuous for the monomial-embedding topology of any
finite generating family: each coordinate is evaluation at a fixed monomial, and so is the inverse
of each invertible coordinate. -/
theorem continuous_regularAffinePointEquiv (g : AddGeneratingFamily S r)
    (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    Continuous[affinePointTopology g, inferInstance] (regularAffinePointEquiv e) := by
  -- install the monomial-embedding topology as an instance so that the continuity combinators apply
  let _ := affinePointTopology g
  have hfst : Continuous fun x : AffineSemigroupComplexPoint S => (regularAffinePointEquiv e x).1 :=
    continuous_pi fun i => by
      simpa using continuous_apply_single g (e.symm (Finsupp.single i 1, 0))
  have hsnd : Continuous fun x : AffineSemigroupComplexPoint S => (regularAffinePointEquiv e x).2 :=
    continuous_pi fun j => Units.continuous_iff.mpr ⟨by
        simpa [Function.comp_def] using continuous_apply_single g (e.symm (0, Finsupp.single j 1)),
      by
        simp only [Units.val_inv_eq_inv_val, inv_val_regularAffinePointEquiv_snd_apply]
        exact continuous_apply_single g (e.symm (0, -Finsupp.single j 1))⟩
  exact hfst.prodMk hsnd

/-- Building a complex point from mixed coordinates is continuous for the monomial-embedding
topology of any finite generating family: the monomial-embedding topology is the coarsest one
making evaluation at every monomial continuous, and evaluation at the monomial of `s` is a mixed
monomial in the coordinates. -/
theorem continuous_regularAffinePointEquiv_symm (g : AddGeneratingFamily S r)
    (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    Continuous[inferInstance, affinePointTopology g] (regularAffinePointEquiv e).symm := by
  rw [affinePointTopology_eq_iInf g, continuous_iInf_rng]
  intro s
  rw [continuous_induced_rng]
  simp only [Function.comp_def, regularAffinePointEquiv_symm_apply_single, Finsupp.prod]
  exact (continuous_finsetProd _ fun i _ => ((continuous_apply i).comp continuous_fst).pow _).mul
    (Units.continuous_val.comp
      (continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_snd).zpow _))

/-- A splitting of an affine semigroup as `(ι →₀ ℕ) × (κ →₀ ℤ)` identifies its complex points,
with the monomial-embedding topology of any finite generating family, with the mixed chart
`(ι → ℂ) × (κ → ℂˣ)`. -/
noncomputable def regularAffinePointHomeomorph (g : AddGeneratingFamily S r)
    (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    @Homeomorph (AffineSemigroupComplexPoint S) ((ι → ℂ) × (κ → ℂˣ))
      (affinePointTopology g) inferInstance :=
  @Homeomorph.mk _ _ (affinePointTopology g) _ (regularAffinePointEquiv e)
    (continuous_regularAffinePointEquiv g e) (continuous_regularAffinePointEquiv_symm g e)

@[simp]
theorem coe_regularAffinePointHomeomorph (g : AddGeneratingFamily S r)
    (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    ⇑(regularAffinePointHomeomorph g e) = regularAffinePointEquiv e :=
  (rfl)

@[simp]
theorem coe_regularAffinePointHomeomorph_symm (g : AddGeneratingFamily S r)
    (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    ⇑(@Homeomorph.symm _ _ (affinePointTopology g) _ (regularAffinePointHomeomorph g e)) =
      (regularAffinePointEquiv e).symm :=
  (rfl)

end TauCeti.Toric
