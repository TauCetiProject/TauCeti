/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import TauCeti.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Points of the reduction of a scheme

Let `X` be a scheme over `Spec k` and `R` a reduced `k`-algebra. Since `Spec R` is reduced,
every `R`-point of `X` factors uniquely through the reduction `X.nilradical.subscheme`, so the
closed immersion `X.nilradical.subschemeι` is a bijection on `R`-points
(`reductionEquiv`). Over a local topological ring with open units and continuous inversion on
the units, such as `ℂ`, this bijection is a homeomorphism for the chart topology
(`reductionHomeomorph`). No finiteness or separation hypothesis is needed.

On an affine open chart `Spec A → X`, points with values in a reduced ring are the points of
`A ⧸ nilradical A` (`TauCeti.PointTopology.quotientNilradicalHomeomorph`), and
`Spec (A ⧸ nilradical A) → Spec A → X` lifts to an affine open chart of the reduction, namely
the pullback of `Spec A → X` along `X.nilradical.subschemeι`. Hence lifting points to the
reduction is continuous over every reduced topological ring (`continuous_reductionLift`); the
locality and unit hypotheses on `R` are needed only for continuity of `reductionMap`.

The algebraic local rings of `X` and of its reduction differ in general: on `Spec ℂ[ε]/(ε²)`
both point spaces are a single point. The statement concerns points only.

## References

* M. Raynaud, *Géométrie algébrique et géométrie analytique*, Exposé XII in A. Grothendieck and
  M. Raynaud, *Revêtements étales et groupe fondamental (SGA 1)*, revised edition
  (arXiv:math/0206203), §§1.1–1.2 and Proposition 2.1, pp. 239–242.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The map on `R`-points induced by the reduction `X.nilradical.subscheme → X`. -/
noncomputable abbrev reductionMap :
    Points (R := R) (X.nilradical.subschemeι ≫ f) → Points (R := R) f :=
  map X.nilradical.subschemeι rfl

/-- The reduction is injective on points over any coefficient ring. -/
theorem reductionMap_injective : Function.Injective (reductionMap (R := R) f) :=
  map_injective _ _

variable [IsReduced R]

/-- The `R`-point of the reduction through which an `R`-point of `X` factors, for `R` reduced. -/
noncomputable def reductionLift (x : Points (R := R) f) :
    Points (R := R) (X.nilradical.subschemeι ≫ f) :=
  ⟨IsClosedImmersion.lift X.nilradical.subschemeι x.val (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact x.val.nilradical_le_ker),
    by rw [← Category.assoc, IsClosedImmersion.lift_fac, x.property]⟩

/-- The lift of a point to the reduction composes with `X.nilradical.subschemeι` to the
original morphism. -/
@[reassoc (attr := simp)]
theorem reductionLift_val_subschemeι (x : Points (R := R) f) :
    (reductionLift f x).val ≫ X.nilradical.subschemeι = x.val :=
  IsClosedImmersion.lift_fac _ _ _

/-- The lifted point maps back to the original point. -/
@[simp]
theorem reductionMap_reductionLift (x : Points (R := R) f) :
    reductionMap f (reductionLift f x) = x := by
  apply Subtype.ext
  rw [map_val, reductionLift_val_subschemeι]

/-- Lifting the image of a point of the reduction recovers that point. -/
@[simp]
theorem reductionLift_reductionMap (x : Points (R := R) (X.nilradical.subschemeι ≫ f)) :
    reductionLift f (reductionMap f x) = x :=
  reductionMap_injective f (reductionMap_reductionLift f _)

/-- Over a reduced ring, the reduction induces a bijection on points. -/
theorem reductionMap_bijective : Function.Bijective (reductionMap (R := R) f) :=
  ⟨reductionMap_injective f, fun x ↦ ⟨reductionLift f x, reductionMap_reductionLift f x⟩⟩

/-- Over a reduced ring, the points of a scheme and of its reduction correspond. -/
noncomputable def reductionEquiv :
    Points (R := R) (X.nilradical.subschemeι ≫ f) ≃ Points (R := R) f where
  toFun := reductionMap f
  invFun := reductionLift f
  left_inv := reductionLift_reductionMap f
  right_inv := reductionMap_reductionLift f

/-- The bijection `reductionEquiv` is the map induced by the reduction. -/
@[simp]
theorem reductionEquiv_apply (x : Points (R := R) (X.nilradical.subschemeι ≫ f)) :
    reductionEquiv f x = reductionMap f x :=
  (rfl)

/-- The inverse of `reductionEquiv` lifts points to the reduction. -/
@[simp]
theorem reductionEquiv_symm_apply (x : Points (R := R) f) :
    (reductionEquiv f).symm x = reductionLift f x :=
  (rfl)

variable [TopologicalSpace R]

/-- On an affine open chart, lifting points to the reduction is an affine open chart of the
reduction composed with the passage to the quotient by the nilradical. -/
private theorem reductionLift_comp_chartPoint (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] :
    ∃ (j : Spec (.of (CommAlgCat.of k (A ⧸ nilradical A))) ⟶ X.nilradical.subscheme)
      (hj : j ≫ X.nilradical.subschemeι ≫ f =
        Spec.algebraMap k (CommAlgCat.of k (A ⧸ nilradical A))),
      IsOpenImmersion j ∧ reductionLift (R := R) f ∘ chartPoint f A i hi =
        chartPoint _ (CommAlgCat.of k (A ⧸ nilradical A)) j hj ∘
          (PointTopology.quotientNilradicalHomeomorph k A R).symm := by
  let y := reductionLift f (chartPoint f A i hi (Ideal.Quotient.mkₐ k (nilradical A)))
  have hy : y.val ≫ X.nilradical.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (nilradical A)).toRingHom) ≫ i := by
    rw [reductionLift_val_subschemeι, chartPoint_val]
  refine ⟨y.val, y.property,
    Scheme.isOpenImmersion_of_comp_nilradical_subschemeι (A := .of A) i y.val
      (by rw [hy, Ideal.Quotient.mkₐ_toRingHom]),
    funext fun x ↦ reductionMap_injective f ?_⟩
  rw [Function.comp_apply, reductionMap_reductionLift, Function.comp_apply, reductionMap,
    map_chartPoint]
  apply Subtype.ext
  conv_lhs => rw [← (PointTopology.quotientNilradicalHomeomorph k A R).apply_symm_apply x]
  rw [chartPoint_val, chartPoint_val, hy, PointTopology.quotientNilradicalHomeomorph_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  simp only [AlgHom.toRingHom_eq_coe]

/-- Over a reduced topological ring, lifting points to the reduction is continuous. -/
@[continuity, fun_prop]
theorem continuous_reductionLift : Continuous (reductionLift (R := R) f) := by
  refine (continuous_iff f _).2 fun A i hi _ ↦ ?_
  obtain ⟨j, hj, _, h⟩ := reductionLift_comp_chartPoint (R := R) f A i hi
  rw [h]
  exact (continuous_chartPoint (X.nilradical.subschemeι ≫ f) _ j hj).comp
    (PointTopology.quotientNilradicalHomeomorph k A R).symm.continuous

variable [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- Over a reduced local topological ring with open units and continuous inversion on the
units, for instance `ℂ`, the reduction induces a homeomorphism on points. -/
noncomputable def reductionHomeomorph :
    Points (R := R) (X.nilradical.subschemeι ≫ f) ≃ₜ Points (R := R) f where
  toEquiv := reductionEquiv f
  continuous_toFun := continuous_map _ _
  continuous_invFun := continuous_reductionLift f

/-- The underlying bijection of `reductionHomeomorph` is `reductionEquiv`. -/
@[simp]
theorem toEquiv_reductionHomeomorph :
    (reductionHomeomorph (R := R) f).toEquiv = reductionEquiv f :=
  (rfl)

/-- The homeomorphism `reductionHomeomorph` is the map induced by the reduction. -/
@[simp]
theorem reductionHomeomorph_apply (x : Points (R := R) (X.nilradical.subschemeι ≫ f)) :
    reductionHomeomorph f x = reductionMap f x :=
  (rfl)

/-- The inverse of `reductionHomeomorph` lifts points to the reduction. -/
@[simp]
theorem reductionHomeomorph_symm_apply (x : Points (R := R) f) :
    (reductionHomeomorph f).symm x = reductionLift f x :=
  (rfl)

/-- Over a reduced local topological ring with open units and continuous inversion on the
units, the reduction is a homeomorphism on points. -/
theorem isHomeomorph_reductionMap : IsHomeomorph (reductionMap (R := R) f) :=
  (reductionHomeomorph f).isHomeomorph

end TauCeti.SchemePointTopology
