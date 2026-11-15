/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.SmoothConnected

/-!
# Geometric connectedness of the upper-triangular subgroup of `SLₙ`

The upper-triangular subgroup `B` of `SLₙ` is geometrically connected over every field. It is a
retract, as a scheme, of the upper-triangular subgroup `B'` of `GLₙ`, which is geometrically
connected: the inclusion `B → B'` has the left inverse

```text
g ↦ g · diag((det g)⁻¹, 1, …, 1),
```

which rescales the first column so that the determinant becomes one and keeps the matrix upper
triangular. This retraction is not a group homomorphism, but on coordinate rings it is an
algebra homomorphism `O(B) → O(B')` with a left inverse. Hence `O(B)` embeds into `O(B')`, and
geometric connectedness descends along such embeddings.

In rank zero both groups are trivial and the retraction is the identity.

## Main declaration

* `TauCeti.SpecialLinear.UpperTriangular.
    geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular subgroup of `SLₙ` is geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear.UpperTriangular

universe u w

noncomputable section

section Rescale

variable {n : ℕ} {A : Type w} [CommRing A]

private theorem detOneRescale_mem {g : GL (Fin n) A} (hg : g ∈ upperTriangularGroup (Fin n) A) :
    detOneRescale g ∈ upperTriangularGroup (Fin n) A := by
  rw [detOneRescale_def]
  refine (upperTriangularGroup (Fin n) A).mul_mem hg ?_
  rw [← UpperTriangularGroup.coe_diagonalHom]
  exact Subtype.property _

/-- The determinant-one rescaling of an invertible upper-triangular matrix, as an
upper-triangular element of `SLₙ`. -/
private def detOneRescalePoint (g : upperTriangularGroup (Fin n) A) :
    (upperTriangularGroup (Fin n) A).comap Matrix.SpecialLinearGroup.toGL :=
  ⟨⟨detOneRescale (g : GL (Fin n) A), by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, det_detOneRescale, Units.val_one]⟩,
    UpperTriangularGroup.mem_comap_toGL_iff.mpr
      (UpperTriangularGroup.mem_iff.mp (detOneRescale_mem g.2))⟩

private theorem coe_detOneRescalePoint (g : upperTriangularGroup (Fin n) A) :
    (((detOneRescalePoint g : _) : Matrix.SpecialLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) = (detOneRescale (g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) :=
  rfl

end Rescale

section Retraction

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The generic point of the upper-triangular subgroup of `GLₙ`, as a matrix. -/
private abbrev genericPointGL :
    upperTriangularGroup (Fin n) (GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n) :=
  GeneralLinear.UpperTriangular.pointsMulEquiv (R := R) (n := n)
    (A := GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n)
    (toConv (AlgHom.id R (GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n)))

/-- The coordinate map of the retraction `B' → B`, `g ↦ g · diag((det g)⁻¹, 1, …, 1)`, from the
upper-triangular subgroup of `GLₙ` onto that of `SLₙ`: the `B`-point it represents is the
rescaling of the generic point of `B'`. -/
private def retractionAlgHom :
    coordinateHopfAlgebra R n →ₐ[R] GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n :=
  ((pointsMulEquiv R n (A := GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n)).symm
    (detOneRescalePoint (genericPointGL R n))).ofConv

/-- The generic point of the upper-triangular subgroup of `SLₙ`, as a matrix. -/
private abbrev genericPoint :
    (upperTriangularGroup (Fin n) (coordinateHopfAlgebra R n)).comap
      Matrix.SpecialLinearGroup.toGL :=
  pointsMulEquiv R n (A := coordinateHopfAlgebra R n)
    (toConv (AlgHom.id R (coordinateHopfAlgebra R n)))

/-- The coordinate map of the inclusion `B → B'` of the upper-triangular subgroup of `SLₙ` into
that of `GLₙ`: the `B'`-point it represents is the generic point of `B`. -/
private def inclusionAlgHom :
    GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n :=
  ((GeneralLinear.UpperTriangular.pointsMulEquiv (R := R) (n := n)
      (A := coordinateHopfAlgebra R n)).symm
    ⟨Matrix.SpecialLinearGroup.toGL (genericPoint R n : _), (genericPoint R n).2⟩).ofConv

/-- The retraction restricts to the identity on `B`: in coordinates, the inclusion map is a left
inverse of the retraction map. -/
private theorem inclusionAlgHom_comp_retractionAlgHom :
    (inclusionAlgHom R n).comp (retractionAlgHom R n) =
      AlgHom.id R (coordinateHopfAlgebra R n) := by
  -- Pushing the generic point of `B'` along the inclusion gives the generic point of `B`.
  have hgeneric : Matrix.GeneralLinearGroup.map (inclusionAlgHom R n).toRingHom
      (genericPointGL R n : GL (Fin n) _) =
        Matrix.SpecialLinearGroup.toGL (genericPoint R n).1 := by
    have h := GeneralLinear.UpperTriangular.pointsMulEquiv_mapValue (R := R) (n := n)
      (inclusionAlgHom R n)
      (toConv (AlgHom.id R (GeneralLinear.UpperTriangular.coordinateHopfAlgebra R n)))
    rw [ofConv_toConv, AlgHom.comp_id] at h
    have h' := congrArg Subtype.val h
    rw [UpperTriangularGroup.coe_map] at h'
    rw [← h', inclusionAlgHom, toConv_ofConv, MulEquiv.apply_symm_apply]
  -- The rescaling of that generic point is the generic point itself, as it has determinant one.
  have hrescale : Matrix.GeneralLinearGroup.map (inclusionAlgHom R n).toRingHom
      (detOneRescale (genericPointGL R n : GL (Fin n) _)) =
        Matrix.SpecialLinearGroup.toGL (genericPoint R n).1 := by
    rw [map_detOneRescale, hgeneric,
      detOneRescale_of_det_eq_one (Matrix.SpecialLinearGroup.coeToGL_det _)]
  apply toConv_injective
  apply (pointsMulEquiv R n (A := coordinateHopfAlgebra R n)).injective
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toGL_injective
  have h := pointsMulEquiv_mapValue R n (inclusionAlgHom R n) (toConv (retractionAlgHom R n))
  rw [AlgHom.mapValue_apply, ofConv_toConv] at h
  rw [h, retractionAlgHom, toConv_ofConv, MulEquiv.apply_symm_apply, ← hrescale]
  ext a b
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, coe_detOneRescalePoint,
    Matrix.GeneralLinearGroup.map_apply]

/-- The coordinate map of the retraction is injective, since it has a left inverse. -/
private theorem retractionAlgHom_injective : Function.Injective (retractionAlgHom R n) :=
  Function.LeftInverse.injective fun x ↦
    DFunLike.congr_fun (inclusionAlgHom_comp_retractionAlgHom R n) x

end Retraction

variable (n : ℕ)

/-- **The upper-triangular subgroup of `SLₙ` is geometrically connected over every field.** -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  (GeneralLinear.UpperTriangular.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    n k).of_injective (retractionAlgHom k n) (retractionAlgHom_injective k n)

end

end TauCeti.SpecialLinear.UpperTriangular
