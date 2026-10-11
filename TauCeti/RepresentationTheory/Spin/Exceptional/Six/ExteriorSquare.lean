/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.RepresentationTheory.ClassicalGroups.Volume

/-!
# The exterior-square action of the four-dimensional special linear group

The wedge product identifies two bivectors in a four-dimensional vector space with a top-degree
exterior vector. The standard volume map therefore gives a symmetric perfect bilinear form on
`⋀²(K⁴)`. The exterior-square standard action of `SL₄(K)` preserves this form: acting on both
bivectors is the same as acting on their wedge, while `SL₄(K)` acts trivially in top degree.

This file bundles that action as a homomorphism from `SL₄(K)` to the isometry group of the wedge
form. Over `ℂ`, it is the six-dimensional orthogonal representation underlying the exceptional
comparison between the four-dimensional special linear group and the six-dimensional spin group.

## Main definitions

* `TauCeti.spinSixWedgeForm`: the symmetric perfect wedge form on `⋀²(K⁴)`.
* `TauCeti.spinSixSpecialLinearToIsometryGroup`: the induced homomorphism from `SL₄(K)` to the
  isometry group.

## Main results

* `TauCeti.spinSixWedgeForm_ιMulti`: the wedge form evaluates to a determinant on pure wedges.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

variable (K : Type u) [CommRing K] [Nontrivial K]

/-- The symmetric wedge-product form on the second exterior power of `K⁴`. The top-degree
trivialisation is the determinant with respect to the standard ordered basis. -/
noncomputable def spinSixWedgeForm :
    LinearMap.BilinForm K (⋀[K]^2 (Fin 4 → K)) :=
  exteriorPower.wedgePairing
    ((LinearEquiv.ofEq
      (⋀[K]^(Module.finrank K (Fin 4 → K)) (Fin 4 → K))
      (⋀[K]^4 (Fin 4 → K)) (by simp)).trans
        (Pi.basisFun K (Fin 4)).exteriorPowerTopEquiv)
    (by simp)

/-- On pure wedges, the wedge form is the determinant of the concatenated vectors. -/
@[simp]
theorem spinSixWedgeForm_ιMulti (u v : Fin 2 → (Fin 4 → K)) :
    spinSixWedgeForm K (exteriorPower.ιMulti K 2 u)
      (exteriorPower.ιMulti K 2 v) =
      (Matrix.of (Fin.append u v)).det := by
  -- `wedgePairing` stores its degree equalities as transports; expose the fixed-degree wedge map.
  rw [show spinSixWedgeForm K =
      (exteriorPower.wedge K (Fin 4 → K) 2 2).compr₂
        (Pi.basisFun K (Fin 4)).exteriorPowerTopEquiv by
    unfold spinSixWedgeForm
    simpa only using exteriorPower.wedgePairing_eq_compr₂_of_finrank_eq 4 (by simp) rfl
      (Pi.basisFun K (Fin 4)).exteriorPowerTopEquiv]
  simp only [LinearMap.compr₂_apply]
  rw [exteriorPower.wedge_ιMulti]
  -- Remove the remaining linear-map coercion so the top-degree basis theorem matches the goal.
  change (Pi.basisFun K (Fin 4)).exteriorPowerTopEquiv
      (exteriorPower.ιMulti K 4 (Fin.append u v)) =
    (Matrix.of (Fin.append u v)).det
  rw [Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, Pi.basisFun_det_apply]

/-- The wedge-product form on `⋀²(K⁴)` is a perfect pairing. -/
theorem spinSixWedgeForm_isPerfPair : (spinSixWedgeForm K).IsPerfPair := by
  unfold spinSixWedgeForm
  infer_instance

/-- The wedge-product form on `⋀²(K⁴)` is symmetric. -/
theorem spinSixWedgeForm_isSymm : (spinSixWedgeForm K).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_iff_eq_flip]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro u
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, spinSixWedgeForm,
    exteriorPower.wedgePairing, LinearMap.compr₂_apply, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply]
  congr 1
  apply Subtype.ext
  simp only [SetLike.coe_gMul, exteriorPower.ιMulti_apply_coe]
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm]
  have hsign : (-1 : ℤˣ) ^ 4 = 1 := by
    apply Units.ext
    norm_num
  rw [hsign, one_smul]

/-- The exterior-square standard representation of `SL₄(K)` preserves the wedge form. -/
theorem spinSixWedgeForm_invariant (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    BilinForm.IsIsometry (spinSixWedgeForm K) ((stdSLRep K 4).exteriorPower 2 g) := by
  rw [BilinForm.isIsometry_iff_comp]
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro u
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.BilinForm.comp_apply]
  rw [Representation.exteriorPower_apply_ιMulti,
    Representation.exteriorPower_apply_ιMulti]
  simp only [spinSixWedgeForm, exteriorPower.wedgePairing, LinearMap.compr₂_apply,
    exteriorPower.wedge, DirectSum.gMulLHom_apply_apply]
  have htop := congrArg (fun f : Module.End K (⋀[K]^4 (Fin 4 → K)) =>
      f (exteriorPower.ιMulti K 4 (Fin.append u v)))
    (stdSLRep_exteriorPower_self_apply K 4 g)
  rw [Representation.exteriorPower_apply, exteriorPower.map_apply_ιMulti] at htop
  simp only [LinearMap.id_coe, id_eq] at htop
  have happ : ((stdSLRep K 4 g) ∘ Fin.append u v) =
      Fin.append ((stdSLRep K 4 g) ∘ u) ((stdSLRep K 4 g) ∘ v) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Function.comp_apply, Fin.append_left, Fin.append_left, Function.comp_apply]
    · intro j
      rw [Function.comp_apply, Fin.append_right, Fin.append_right, Function.comp_apply]
  congr 1
  apply Subtype.ext
  simpa only [SetLike.coe_gMul, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_mul_ιMulti, happ] using congrArg Subtype.val htop

/-- The exterior-square action of `SL₄(K)` lands in the isometry group of the wedge form. -/
noncomputable def spinSixSpecialLinearToIsometryGroup :
    Matrix.SpecialLinearGroup (Fin 4) K →*
      BilinForm.isometryGroup (spinSixWedgeForm K) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (⋀[K]^2 (Fin 4 → K))).toMonoidHom.comp
        ((stdSLRep K 4).exteriorPower 2).asGroupHom).codRestrict
    (BilinForm.isometryGroup (spinSixWedgeForm K))
    (fun g ↦ by
      rw [BilinForm.mem_isometryGroup]
      simpa only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        Representation.asGroupHom_apply,
        LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap] using
          spinSixWedgeForm_invariant K g)

/-- The isometry-group homomorphism acts through the exterior-square representation. -/
@[simp]
theorem spinSixSpecialLinearToIsometryGroup_apply
    (g : Matrix.SpecialLinearGroup (Fin 4) K) (x : ⋀[K]^2 (Fin 4 → K)) :
    (spinSixSpecialLinearToIsometryGroup K g).1 x = (stdSLRep K 4).exteriorPower 2 g x := by
  simp [spinSixSpecialLinearToIsometryGroup,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Representation.asGroupHom_apply]

end TauCeti
