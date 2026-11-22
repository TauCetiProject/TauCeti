/-
Copyright (c) 2026 The TauCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TauCeti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Adjunction
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.Invariants

/-!
# The invariants of the cofree functor

Counit evaluation identifies the invariants of a cofree comodule `M ⊗ H` naturally with `M`.
This packages `Comodule.cofreeFixedEquiv` into a natural isomorphism without assuming flatness.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985), §4.7(a).
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.ComoduleCat

universe u v w

variable (R : Type u) (H : Type v) [CommRing R] [Semiring H] [Bialgebra R H]

-- Use the additive group carried by the functor object rather than the one inferred on the
-- tensor product by `LinearEquiv.toModuleIso`; the underlying linear maps are unchanged.
private noncomputable def cofreeInvariantsComponent (M : ModuleCat.{max v w} R) :
    (cofreeFunctor.{u, v, w} R H ⋙ invariantsFunctor R H).obj M ≅ M where
  hom := ConcreteCategory.ofHom
    (X := (cofreeFunctor.{u, v, w} R H ⋙ invariantsFunctor R H).obj M) (Y := M)
    (Comodule.cofreeFixedEquiv R H M).symm.toLinearMap
  inv := ConcreteCategory.ofHom
    (X := M) (Y := (cofreeFunctor.{u, v, w} R H ⋙ invariantsFunctor R H).obj M)
    (Comodule.cofreeFixedEquiv R H M).toLinearMap
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (Comodule.cofreeFixedEquiv R H M).apply_symm_apply z
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (Comodule.cofreeFixedEquiv R H M).symm_apply_apply m

/-- The invariants of a cofree comodule are naturally its coefficient module, via the counit. -/
noncomputable def cofreeInvariantsIso :
    cofreeFunctor.{u, v, w} R H ⋙ invariantsFunctor R H ≅ 𝟭 (ModuleCat.{max v w} R) :=
  NatIso.ofComponents (cofreeInvariantsComponent R H) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Comodule.cofreeFixedEquiv_symm_naturality f.hom z)

-- Simplify the component applications before `ConcreteCategory.hom` changes their form.
/-- The comparison on a cofree comodule is evaluation by the counit. -/
@[simp↓]
theorem cofreeInvariantsIso_hom_app_apply (M : ModuleCat.{max v w} R)
    (z : (cofreeFunctor.{u, v, w} R H ⋙ invariantsFunctor R H).obj M) :
    (cofreeInvariantsIso.{u, v, w} R H).hom.app M z = Comodule.cofreeCounit R H M z.val := by
  exact (Comodule.cofreeFixedEquiv_symm_apply (R := R) (H := H) (N := M) z).trans
    (LinearMap.congr_fun Comodule.cofreeCounit_def z.val).symm

/-- The inverse comparison is inclusion via tensoring with `1`. -/
@[simp↓]
theorem coe_cofreeInvariantsIso_inv_app_apply (M : ModuleCat.{max v w} R) (m : M) :
    (((cofreeInvariantsIso.{u, v, w} R H).inv.app M m).val : M ⊗[R] H) = m ⊗ₜ[R] (1 : H) :=
  Comodule.cofreeFixedEquiv_apply (R := R) (H := H) (N := M) m

end TauCeti.ComoduleCat
