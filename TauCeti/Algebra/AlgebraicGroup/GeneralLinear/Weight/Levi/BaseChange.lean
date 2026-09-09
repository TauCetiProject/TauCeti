/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Base change of general-linear weight Levis

The weight Levi attached to `w : Fin N → ℤ` commutes with arbitrary extension of the
commutative base ring as an affine group scheme. Its coordinate Hopf algebra is the quotient
of `O(GL_N)` by the entries between distinct weight blocks. The general-linear base-change
isomorphism preserves those entries, so the quotient comparison preserves the Hopf structure.
This permits transporting closed subgroups and their unipotence to the geometric fibre.

The comparison is compatible with the ambient general-linear coordinate maps, and its action
on scalar tensors of quotient coordinates is explicit. Repeated weights and rank zero are
allowed. The universe restriction on the bundled isomorphism is inherited from
`coordinateHopfAlgebraBaseChangeIso`.

The quotient-transport construction follows
`TauCeti.SpecialLinear.coordinateHopfAlgebraBaseChangeIso`, using the two opposite
weight-parabolic relation sets in place of the determinant-one relation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 2 and 13.
* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable {N : ℕ} (w : Fin N → ℤ)

/-- The ambient general-linear base-change isomorphism carries the scalar extension of the
weight-Levi defining Hopf ideal onto the defining Hopf ideal over the extended base. -/
theorem map_baseChangeHopfIdeal_weightLeviDefiningHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (weightLeviDefiningHopfIdeal R w)).map
        (coordinateHopfAlgebraBaseChangeIso R K N).hom.hom =
      weightLeviDefiningHopfIdeal K w := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (S := weightParabolicRelationSet R w ∪ weightParabolicRelationSet R (-w))
    (S' := weightParabolicRelationSet K w ∪ weightParabolicRelationSet K (-w))
    (weightLeviDefiningHopfIdeal R w) (weightLeviDefiningHopfIdeal K w)
    (coordinateHopfAlgebraBaseChangeIso R K N)
    (by rw [weightLeviDefiningHopfIdeal_def, HopfIdeal.sup_toIdeal,
      weightParabolicDefiningHopfIdeal_toIdeal, weightParabolicDefiningHopfIdeal_toIdeal,
      Ideal.span_union])
    (by rw [weightLeviDefiningHopfIdeal_def, HopfIdeal.sup_toIdeal,
      weightParabolicDefiningHopfIdeal_toIdeal, weightParabolicDefiningHopfIdeal_toIdeal,
      Ideal.span_union]) ?_
  have hentry (i j : Fin N) :
      (coordinateHopfAlgebraBaseChangeIso R K N).hom.hom
          (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R N
            (coordinateRingMap R N (MvPolynomial.X (i, j)))) =
        coordinateHopfAlgebraAlgEquiv K N
          (coordinateRingMap K N (MvPolynomial.X (i, j))) := by
    simpa only [MvPolynomial.map_X, one_smul] using
      coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v} R K N 1 (MvPolynomial.X (i, j))
  have hrel (a : Fin N → ℤ) :
      (fun x : coordinateHopfAlgebra R N ↦
        (coordinateHopfAlgebraBaseChangeIso R K N).hom.hom (1 ⊗ₜ[R] x)) ''
          weightParabolicRelationSet R a = weightParabolicRelationSet K a := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨i, j, hij, rfl⟩ := (mem_weightParabolicRelationSet_iff R a y).mp hy
      exact (mem_weightParabolicRelationSet_iff K a _).mpr ⟨i, j, hij, hentry i j⟩
    · intro hx
      obtain ⟨i, j, hij, rfl⟩ := (mem_weightParabolicRelationSet_iff K a x).mp hx
      exact ⟨_, X_mem_weightParabolicRelationSet R a hij, hentry i j⟩
  rw [Set.image_union, hrel, hrel]

/-- Scalar extension of a weight-Levi coordinate Hopf algebra is canonically the weight-Levi
coordinate Hopf algebra over the new base. -/
noncomputable def weightLeviCoordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (weightLeviCoordinateHopfAlgebra R w) ≅
      weightLeviCoordinateHopfAlgebra K w :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (weightLeviDefiningHopfIdeal R w) (weightLeviDefiningHopfIdeal K w)
    (coordinateHopfAlgebraBaseChangeIso R K N)
    (map_baseChangeHopfIdeal_weightLeviDefiningHopfIdeal R K w)

/-- The weight-Levi base-change isomorphism commutes with restriction of ambient
general-linear coordinates to the Levi. -/
@[simp]
theorem baseChangeMap_mkQuotient_comp_weightLeviCoordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (weightLeviDefiningHopfIdeal R w)) ≫
      (weightLeviCoordinateHopfAlgebraBaseChangeIso R K w).hom =
    (coordinateHopfAlgebraBaseChangeIso R K N).hom ≫
      CommHopfAlgCat.mkQuotient _ (weightLeviDefiningHopfIdeal K w) := by
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (weightLeviDefiningHopfIdeal R w) (weightLeviDefiningHopfIdeal K w)
    (coordinateHopfAlgebraBaseChangeIso R K N)
    (map_baseChangeHopfIdeal_weightLeviDefiningHopfIdeal R K w)

/-- On a scalar tensor of a quotient coordinate, the Levi comparison is induced by the
ambient general-linear comparison. -/
@[simp]
theorem weightLeviCoordinateHopfAlgebraBaseChangeIso_hom_tmul_mk
    (s : K) (x : coordinateHopfAlgebra R N) :
    (weightLeviCoordinateHopfAlgebraBaseChangeIso R K w).hom
        (s ⊗ₜ[R] Ideal.Quotient.mk (weightLeviDefiningHopfIdeal R w).toIdeal x) =
      Ideal.Quotient.mk (weightLeviDefiningHopfIdeal K w).toIdeal
        ((coordinateHopfAlgebraBaseChangeIso R K N).hom (s ⊗ₜ[R] x)) := by
  have h := congrArg (fun f ↦ f.hom (s ⊗ₜ[R] x))
    (baseChangeMap_mkQuotient_comp_weightLeviCoordinateHopfAlgebraBaseChangeIso_hom R K w)
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    CommHopfAlgCat.baseChangeMap_apply_tmul (K := K)
      (CommHopfAlgCat.mkQuotient _ (weightLeviDefiningHopfIdeal R w)),
    CommHopfAlgCat.mkQuotient_apply _ (weightLeviDefiningHopfIdeal R w),
    CommHopfAlgCat.mkQuotient_apply _ (weightLeviDefiningHopfIdeal K w),
    Ideal.Quotient.mkₐ_eq_mk] using h

/-- The inverse Levi comparison sends a quotient of an ambient base-changed coordinate
back to the corresponding scalar tensor of a quotient coordinate. -/
@[simp]
theorem weightLeviCoordinateHopfAlgebraBaseChangeIso_inv_mk
    (s : K) (x : coordinateHopfAlgebra R N) :
    (weightLeviCoordinateHopfAlgebraBaseChangeIso R K w).inv
        (Ideal.Quotient.mk (weightLeviDefiningHopfIdeal K w).toIdeal
          ((coordinateHopfAlgebraBaseChangeIso R K N).hom (s ⊗ₜ[R] x))) =
      s ⊗ₜ[R] Ideal.Quotient.mk (weightLeviDefiningHopfIdeal R w).toIdeal x := by
  rw [← weightLeviCoordinateHopfAlgebraBaseChangeIso_hom_tmul_mk]
  simp

end TauCeti.GeneralLinear
