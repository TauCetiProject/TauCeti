/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality
public import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Points of the reduction of a scheme

Let `X` be a scheme over `Spec k` and `R` a reduced `k`-algebra. Since `Spec R` is reduced,
every `R`-point of `X` factors uniquely through the reduction `X.nilradical.subscheme`, so the
closed immersion `X.nilradical.subschemeι` is a bijection on `R`-points
(`reductionEquiv`). Over a local topological ring with open units and continuous inversion on
the units, such as `ℂ`, this bijection is a homeomorphism for the chart topology
(`reductionHomeomorph`). No finiteness or separation hypothesis is needed.

Continuity of the inverse is checked on affine charts `Spec A → X`. Their points factor
through `A ⧸ nilradical A` (`TauCeti.PointTopology.quotientNilradicalHomeomorph`), and
`Spec (A ⧸ nilradical A) → Spec A → X` lifts to the reduction; this lift need not be an open
immersion, which is why the argument uses `continuous_chartPoint_of_isLocalRing`.

The algebraic local rings of `X` and of its reduction differ in general: on `Spec ℂ[ε]/(ε²)`
both point spaces are a single point. The statement concerns points only.

## References

* A. Grothendieck, *SGA 1*, Exposé XII, §1.1–1.2 and Proposition 2.1, pp. 239–242.
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
      exact Scheme.nilradical_le_ker x.val),
    by rw [← Category.assoc, IsClosedImmersion.lift_fac, x.property]⟩

/-- The lifted point maps back to the original point. -/
@[simp]
theorem reductionMap_reductionLift (x : Points (R := R) f) :
    reductionMap f (reductionLift f x) = x := by
  apply Subtype.ext
  rw [map_val]
  exact IsClosedImmersion.lift_fac _ _ _

/-- Lifting the image of a point of the reduction recovers that point. -/
@[simp]
theorem reductionLift_reductionMap (x : Points (R := R) (X.nilradical.subschemeι ≫ f)) :
    reductionLift f (reductionMap f x) = x :=
  reductionMap_injective f (reductionMap_reductionLift f _)

/-- Over a reduced ring, the reduction induces a bijection on points. -/
theorem reductionMap_bijective : Function.Bijective (reductionMap (R := R) f) :=
  ⟨reductionMap_injective f, fun x ↦ ⟨reductionLift f x, reductionMap_reductionLift f x⟩⟩

/-- Over a reduced ring, the points of a scheme and of its reduction correspond. -/
@[expose, simps]
noncomputable def reductionEquiv :
    Points (R := R) (X.nilradical.subschemeι ≫ f) ≃ Points (R := R) f where
  toFun := reductionMap f
  invFun := reductionLift f
  left_inv := reductionLift_reductionMap f
  right_inv := reductionMap_reductionLift f

variable [TopologicalSpace R]

/-- On an affine chart, lifting points to the reduction is a chart of the reduction composed
with the passage to the quotient by the nilradical. -/
private theorem reductionLift_comp_chartPoint (A : CommAlgCat.{u} k) (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.algebraMap k A) :
    ∃ (j : Spec (.of (CommAlgCat.of k (A ⧸ nilradical A))) ⟶ X.nilradical.subscheme)
      (hj : j ≫ X.nilradical.subschemeι ≫ f =
        Spec.algebraMap k (CommAlgCat.of k (A ⧸ nilradical A))),
      reductionLift (R := R) f ∘ chartPoint f A i hi =
        chartPoint _ (CommAlgCat.of k (A ⧸ nilradical A)) j hj ∘
          (PointTopology.quotientNilradicalHomeomorph (k := k)).symm := by
  have : _root_.IsReduced (A ⧸ nilradical A) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  let q : Spec (.of (A ⧸ nilradical A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (nilradical A)).toRingHom)
  let j := IsClosedImmersion.lift X.nilradical.subschemeι (q ≫ i) (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.nilradical_le_ker _)
  have hjι : j ≫ X.nilradical.subschemeι = q ≫ i := IsClosedImmersion.lift_fac _ _ _
  have hj : j ≫ X.nilradical.subschemeι ≫ f = Spec.algebraMap k (A ⧸ nilradical A) := by
    rw [← Category.assoc, hjι, Category.assoc, hi, ← Spec.map_comp]
    congr 1
  refine ⟨j, hj, funext fun x ↦ reductionMap_injective f ?_⟩
  rw [Function.comp_apply, reductionMap_reductionLift, Function.comp_apply, reductionMap,
    map_chartPoint]
  apply Subtype.ext
  simp only [chartPoint_val, hjι, q, ← Spec.map_comp_assoc]
  congr 2
  ext a
  exact (PointTopology.quotientNilradicalHomeomorph_symm_apply_mk x a).symm

variable [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- Over a local topological ring with open units and continuous inversion on the units,
lifting points to the reduction is continuous. -/
theorem continuous_reductionLift : Continuous (reductionLift (R := R) f) := by
  refine (continuous_iff f _).2 fun A i hi _ ↦ ?_
  obtain ⟨j, hj, h⟩ := reductionLift_comp_chartPoint (R := R) f A i hi
  rw [h]
  exact (continuous_chartPoint_of_isLocalRing (X.nilradical.subschemeι ≫ f) _ j hj).comp
    PointTopology.quotientNilradicalHomeomorph.symm.continuous

/-- Over a reduced local topological ring with open units and continuous inversion on the
units, for instance `ℂ`, the reduction induces a homeomorphism on points. -/
@[expose, simps! apply symm_apply]
noncomputable def reductionHomeomorph :
    Points (R := R) (X.nilradical.subschemeι ≫ f) ≃ₜ Points (R := R) f where
  toEquiv := reductionEquiv f
  continuous_toFun := continuous_map _ _
  continuous_invFun := continuous_reductionLift f

end TauCeti.SchemePointTopology
