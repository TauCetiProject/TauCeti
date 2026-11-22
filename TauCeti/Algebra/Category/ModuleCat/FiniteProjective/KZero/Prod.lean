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

open MulOpposite

universe u

namespace TauCeti.KZero

/-- **Product decomposition:** `KZero (R × S) ≃+ KZero R × KZero S`. The forward map sends a
class over `R × S` to `(map (RingHom.fst R S) x, map (RingHom.snd R S) x)` via extension of
scalars along the projections `RingHom.fst R S` and `RingHom.snd R S`; the inverse sends `(x, y)`
to the sum of the restrictions of scalars of `x` along `RingHom.op (RingHom.fst R S)` and of `y`
along `RingHom.op (RingHom.snd R S)`. -/
noncomputable def prodEquiv (R S : Type u) [Ring R] [Ring S] :
    KZero (R × S) ≃+ KZero R × KZero S :=
  (RingEquiv.prodMulOpposite R S).finiteProjectiveModulesSplitK0Equiv.trans
    (finiteProjectiveModulesProdSplitK0Equiv Rᵐᵒᵖ Sᵐᵒᵖ)

@[simp] theorem prodEquiv_apply (R S : Type u) [Ring R] [Ring S] (x : KZero (R × S)) :
    prodEquiv R S x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) := by
  simp only [prodEquiv, AddEquiv.trans_apply, RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply,
    finiteProjectiveModulesProdSplitK0Equiv_apply,
    SplitK0.map_finiteProjectiveModulesExtendScalars_apply_map]
  exact Prod.ext (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
    (RingEquiv.fst_comp_prodMulOpposite R S)) x) (DFunLike.congr_fun
      (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
        (RingEquiv.snd_comp_prodMulOpposite R S)) x)

@[simp] theorem prodEquiv_symm_apply (R S : Type u) [Ring R] [Ring S]
    (x : KZero R × KZero S) : (prodEquiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.op (RingHom.fst R S)).finiteProjectiveModulesRestrictScalars
        (RingHom.finite_op_fst R S) (RingHom.projective_op_fst R S)) x.1 +
      SplitK0.map.{u, u} ((RingHom.op (RingHom.snd R S)).finiteProjectiveModulesRestrictScalars
        (RingHom.finite_op_snd R S) (RingHom.projective_op_snd R S)) x.2 := by
  apply (prodEquiv R S).injective
  rw [AddEquiv.apply_symm_apply, prodEquiv_apply, map_add, map_add]
  refine Prod.ext ?_ ?_ <;>
    (dsimp only; rw [map, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply])
  · rw [SplitK0.map_extendScalars_comp_restrictScalars_self _ (fun a ↦ ⟨op (a.unop, 0), rfl⟩),
      SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (op (1, 0)) rfl rfl]; simp
  · rw [SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (op (0, 1)) rfl rfl,
      SplitK0.map_extendScalars_comp_restrictScalars_self _ (fun b ↦ ⟨op (0, b.unop), rfl⟩)]; simp

end TauCeti.KZero
