/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Basic
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Matlis duality and indecomposable modules

Let `R` be a commutative ring, `A` an `R`-algebra, and `E` an injective `R`-module such that
`Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪`. On modules of finite length over `R`,
the Matlis dual `D_R = Hom_R(-, E)` reverses endomorphism rings, so it preserves and reflects
indecomposability, of right modules as of left modules.

These are the statements for unbundled modules, in every universe. The bundled forms, for modules
of finite length over `R` in one universe, are `ModuleCat.indecomposable_matlisDualObj_iff` and
`ModuleCat.indecomposable_matlisDualOpObj_iff`.

## Main results

* `TauCeti.MatlisDual.isIndecomposableModule_iff`: the dual of a right module of finite length over
  `R` is an indecomposable left module exactly when the right module is indecomposable.
* `TauCeti.MatlisDual.isIndecomposableModule_op_iff`: the same for the dual of a left module.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3.
-/

public section

namespace TauCeti.MatlisDual

open MulOpposite

universe u v w t

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Module.Injective R E] [Small.{v} R] {A : Type t} [Ring A] [Algebra R A]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- For a cogenerator `E`, the dual of a module is nonzero exactly when the module is. -/
private theorem nontrivial_iff (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E)) :
    Nontrivial (MatlisDual R E N) ↔ Nontrivial N := by
  simp only [← not_subsingleton_iff_nontrivial, subsingleton_matlisDual_iff hE]

variable (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **Matlis duality preserves and reflects indecomposability of right modules**: for a right
`A`-module `N` of finite length over `R`, the left module `D_R N` is indecomposable exactly when
`N` is. -/
theorem isIndecomposableModule_iff [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    (hN : IsFiniteLength R N) :
    IsIndecomposableModule A (MatlisDual R E N) ↔ IsIndecomposableModule Aᵐᵒᵖ N :=
  -- Dualizing endomorphisms is a bijective ring anti-homomorphism.
  RingEquiv.isIndecomposableModule_iff (RingEquiv.ofBijective
    ({ toFun f := mapOp f.unop
       map_one' := mapOp_id
       map_mul' _ _ := mapOp_comp _ _
       map_zero' := LinearMap.ext fun _ ↦ MatlisDual.ext fun _ ↦ by simp
       map_add' _ _ := LinearMap.ext fun _ ↦ MatlisDual.ext fun _ ↦ by simp } :
      (Module.End Aᵐᵒᵖ N)ᵐᵒᵖ →+* Module.End A (MatlisDual R E N))
    ((bijective_mapOp hE hN).comp unop_bijective))
    (nontrivial_iff (nontrivial_linearMap_of_isMaximal hE))

/-- **Matlis duality preserves and reflects indecomposability of left modules**: for a left
`A`-module `N` of finite length over `R`, the right module `D_R N` is indecomposable exactly when
`N` is. -/
theorem isIndecomposableModule_op_iff [Module A N] [IsScalarTower R A N]
    (hN : IsFiniteLength R N) :
    IsIndecomposableModule Aᵐᵒᵖ (MatlisDual R E N) ↔ IsIndecomposableModule A N :=
  RingEquiv.isIndecomposableModule_iff (RingEquiv.ofBijective
    ({ toFun f := map f.unop
       map_one' := map_id
       map_mul' _ _ := map_comp _ _
       map_zero' := LinearMap.ext fun _ ↦ MatlisDual.ext fun _ ↦ by simp
       map_add' _ _ := LinearMap.ext fun _ ↦ MatlisDual.ext fun _ ↦ by simp } :
      (Module.End A N)ᵐᵒᵖ →+* Module.End Aᵐᵒᵖ (MatlisDual R E N))
    ((bijective_map hE hN).comp unop_bijective))
    (nontrivial_iff (nontrivial_linearMap_of_isMaximal hE))

end TauCeti.MatlisDual
