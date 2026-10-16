/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

/-!
# Conjugation by a rational point in a representation

Let `g` be a rational point of an affine group `G` and `π` an algebra-valued point. In a
representation `V` of `G`, the point `π` acts on `g v` as `g` acts on the result of letting the
conjugate point `g⁻¹ π g` act on `v`. In particular, if the conjugate point scales `v`, then `π`
scales `g v` by the same scalar. This is how rational points normalizing a subgroup permute its
weight spaces: the subgroup's universal point `π` scales a weight vector by its character, and the
conjugated character is read off from `g⁻¹ π g`.

No reducedness, finite type, or field hypothesis is needed, and the value algebra of `π` may be
nonreduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

variable {R H V C : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V] [CommSemiring C] [Algebra R C]

/-- If the conjugate `g⁻¹ π g` of an algebra-valued point `π` by a rational point `g` scales `v`
by `y`, then `π` scales `g v` by `y`. -/
theorem endOfPoint_one_tmul_basePointsRepresentation_of_conj (π : H →ₐ[R] C)
    (g : WithConv (H →ₐ[R] R)) {v : V} {y : C}
    (h : endOfPoint V (π.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹)) (1 ⊗ₜ[R] v) =
      y ⊗ₜ[R] v) :
    endOfPoint V π (1 ⊗ₜ[R] basePointsRepresentation (H := H) V g v) =
      y ⊗ₜ[R] basePointsRepresentation (H := H) V g v := by
  -- With `c` the point `g` valued in `C`, the conjugate point is `c⁻¹ * π * c`, and
  -- `π * c = c * (c⁻¹ * π * c)`.
  let c := AlgHom.mapValue (H := H) (Algebra.ofId R C) g
  have hconj : toConv (π.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹)) =
      c⁻¹ * toConv π * c := by
    simpa only [c, map_inv, inv_inv] using HopfAlgebra.comp_pointConjugationAlgHom g⁻¹ (toConv π)
  rw [← ofConv_toConv (π.comp (HopfAlgebra.pointConjugationAlgHom g⁻¹)), hconj] at h
  have he := LinearMap.congr_fun (endOfPoint_convMul V (toConv π) c) (1 ⊗ₜ[R] v)
  have he' := LinearMap.congr_fun (endOfPoint_convMul V c (c⁻¹ * toConv π * c)) (1 ⊗ₜ[R] v)
  simp only [LinearMap.comp_apply] at he he'
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at he'
  rw [← endOfPoint_mapValue_algebraOfId_tmul (A := C) g 1 v, ← he, he', h]
  exact endOfPoint_mapValue_algebraOfId_tmul (A := C) g y v

end TauCeti.Comodule
