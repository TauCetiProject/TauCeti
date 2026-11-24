/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Prod

import TauCeti.Algebra.Ring.Opposite

/-!
# Algebraic `K₀` of a binary product ring

For two rings `R` and `S`, `TauCeti.KZero.prodEquiv R S` identifies `KZero (R × S)` with
`KZero R × KZero S`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Prop. 2.4.
-/

public section

open CategoryTheory MulOpposite

universe u

namespace TauCeti.KZero

/-- **Product decomposition:** `KZero (R × S) ≃+ KZero R × KZero S`. The forward map sends a
class over `R × S` to `(map (RingHom.fst R S) x, map (RingHom.snd R S) x)` via extension of
scalars along the projections `RingHom.fst R S` and `RingHom.snd R S`; the inverse sends `(x, y)`
to the sum of the restrictions of scalars of `x` along `RingHom.op (RingHom.fst R S)` and of `y`
along `RingHom.op (RingHom.snd R S)`. -/
noncomputable def prodEquiv (R S : Type u) [Ring R] [Ring S] :
    KZero (R × S) ≃+ KZero R × KZero S :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.prodMulOpposite R S)).symm.finiteProjectiveModulesSplitK0Equiv.trans
    (finiteProjectiveModulesProdSplitK0Equiv Rᵐᵒᵖ Sᵐᵒᵖ)

@[simp] theorem prodEquiv_apply (R S : Type u) [Ring R] [Ring S] (x : KZero (R × S)) :
    prodEquiv R S x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) := by
  have hx : (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (RingEquiv.prodMulOpposite R S)).symm.finiteProjectiveModulesSplitK0Equiv x =
      SplitK0.map.{u, u}
        (RingEquiv.prodMulOpposite R S).toRingHom.finiteProjectiveModulesExtendScalars x :=
    (DFunLike.congr_fun
      (RingEquiv.splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars
        (RingEquiv.prodMulOpposite R S)) x).symm
  rw [prodEquiv, AddEquiv.trans_apply, hx, finiteProjectiveModulesProdSplitK0Equiv_apply]
  simp only [SplitK0.map_finiteProjectiveModulesExtendScalars_apply_map]
  exact Prod.ext (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
    (RingEquiv.fst_comp_prodMulOpposite R S)) x) (DFunLike.congr_fun
      (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
        (RingEquiv.snd_comp_prodMulOpposite R S)) x)

private theorem map_restrictScalars_comp_prodMulOpposite {R S A : Type u} [Ring R] [Ring S] [Ring A]
    (p : Rᵐᵒᵖ × Sᵐᵒᵖ →+* A) (hfin : letI := p.toModule; Module.Finite (Rᵐᵒᵖ × Sᵐᵒᵖ) A)
    (hproj : letI := p.toModule; Module.Projective (Rᵐᵒᵖ × Sᵐᵒᵖ) A)
    (q : (R × S)ᵐᵒᵖ →+* A) (hq : q = p.comp (RingEquiv.prodMulOpposite R S).toRingHom)
    (hfin' : letI := q.toModule; Module.Finite (R × S)ᵐᵒᵖ A)
    (hproj' : letI := q.toModule; Module.Projective (R × S)ᵐᵒᵖ A) :
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (RingEquiv.prodMulOpposite R S)).symm.finiteProjectiveModulesSplitK0Equiv.symm
        : _ ≃+ _).toAddMonoidHom.comp
      (SplitK0.map.{u, u} (p.finiteProjectiveModulesRestrictScalars hfin hproj)) =
      SplitK0.map.{u, u} (q.finiteProjectiveModulesRestrictScalars hfin' hproj') :=
  SplitK0.hom_ext fun P ↦ by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, SplitK0.map_of,
      CategoryTheory.Equivalence.finiteProjectiveModulesSplitK0Equiv_symm_of]
    refine SplitK0.of_congr.{u} <| CategoryTheory.ObjectProperty.isoMk _ <|
      eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (RingEquiv.prodMulOpposite R S)).symm.finiteProjectiveModulesEquivalence_inverse_obj_obj
        _) ≪≫
      (ModuleCat.restrictScalars (RingEquiv.prodMulOpposite R S).toRingHom).mapIso
        (eqToIso (p.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj P)) ≪≫
      (ModuleCat.restrictScalarsComp'App (RingEquiv.prodMulOpposite R S).toRingHom p q hq
        P.obj).symm ≪≫
      eqToIso (q.finiteProjectiveModulesRestrictScalars_obj_obj hfin' hproj' P).symm

@[simp] theorem prodEquiv_symm_apply (R S : Type u) [Ring R] [Ring S]
    (x : KZero R × KZero S) : (prodEquiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.op (RingHom.fst R S)).finiteProjectiveModulesRestrictScalars
        (RingHom.finite_toModule_op_fst R S) (RingHom.projective_toModule_op_fst R S)) x.1 +
      SplitK0.map.{u, u} ((RingHom.op (RingHom.snd R S)).finiteProjectiveModulesRestrictScalars
        (RingHom.finite_toModule_op_snd R S) (RingHom.projective_toModule_op_snd R S)) x.2 := by
  rw [prodEquiv, AddEquiv.symm_trans_apply, finiteProjectiveModulesProdSplitK0Equiv_symm_apply,
    map_add]
  congr 1
  · exact DFunLike.congr_fun (map_restrictScalars_comp_prodMulOpposite
      (RingHom.fst Rᵐᵒᵖ Sᵐᵒᵖ) _ _ (RingHom.op (RingHom.fst R S))
      (RingEquiv.fst_comp_prodMulOpposite R S).symm _ _) x.1
  · exact DFunLike.congr_fun (map_restrictScalars_comp_prodMulOpposite
      (RingHom.snd Rᵐᵒᵖ Sᵐᵒᵖ) _ _ (RingHom.op (RingHom.snd R S))
      (RingEquiv.snd_comp_prodMulOpposite R S).symm _ _) x.2

end TauCeti.KZero
