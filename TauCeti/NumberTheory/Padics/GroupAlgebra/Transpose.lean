/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.GroupAlgebra
public import TauCeti.NumberTheory.Padics.TorsionDual
import TauCeti.Algebra.Module.AuslanderReiten.StableTranspose
import TauCeti.Algebra.Module.Projective.Trans
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The transpose of a `ℤ_p[G]`-module of projective dimension one

Let `G` be a finite group and `0 → P₁ → P₀ → M → 0` an exact sequence of `ℤ_p[G]`-modules with
`P₀, P₁` finitely generated projective, so that `M` has projective dimension at most one. Its
Auslander–Reiten transpose `Tr f`, the cokernel of
`Hom_{ℤ_p[G]}(P₀, ℤ_p[G]) → Hom_{ℤ_p[G]}(P₁, ℤ_p[G])`, is `E¹(M) = Ext¹_{ℤ_p[G]}(M, ℤ_p[G])`.
This file identifies it with the Pontryagin dual `Hom_{ℤ_p}(M[p^∞], ℚ_p / ℤ_p)` of the `p`-power
torsion of `M`, compatibly with the action of `ℤ_p[G]ᵐᵒᵖ`. The identification composes the
symmetric Frobenius duality of `ℤ_p[G]` (`TauCeti.AuslanderReitenTranspose.groupAlgebraDualEquiv`),
which rewrites the transpose through `ℤ_p`-linear duals, with the connecting map
`TauCeti.torsionDualMap` over `ℤ_p`.

Since the transpose determines a finitely presented module up to projective summands
(`TauCeti.AuslanderReitenTranspose.nonempty_linearEquiv_prod_of_linearEquiv`), two such modules
with isomorphic `p`-power torsion are stably isomorphic. This is how Neukirch–Schmidt–Wingberg
compare modules of projective dimension one over `ℤ_p[G]` before cancelling projective summands.

## Main definitions

* `TauCeti.instModulePadicCharacterContragredient`: the contragredient action of `ℤ_p[G]ᵐᵒᵖ` on
  the `ℚ_p / ℤ_p`-valued characters of a `ℤ_p[G]`-module.
* `TauCeti.AuslanderReitenTranspose.torsionDualLinearEquiv`: the transpose `Tr f` is
  `ℤ_p[G]ᵐᵒᵖ`-linearly isomorphic to the Pontryagin dual of the `p`-power torsion of `M`.

## Main results

* `TauCeti.nonempty_linearEquiv_prod_of_pPowerTorsion_linearEquiv`: modules of projective dimension
  one with isomorphic `p`-power torsion satisfy `M ⊕ P₁ ⊕ Q₀ ≃ N ⊕ P₀ ⊕ Q₁`.
* `TauCeti.exists_projective_prod_linearEquiv_of_torsion`: the same, as `M ⊕ P ≃ N ⊕ Q` for some
  finitely generated projective `P` and `Q`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Springer (2008), (5.4.11) and (5.6.9).
* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

noncomputable section

open Module

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]

section ContragredientCharacter

variable {X : Type*} [AddCommGroup X] [Module (MonoidAlgebra ℤ_[p] G) X] [Module ℤ_[p] X]
  [SMulCommClass ℤ_[p] (MonoidAlgebra ℤ_[p] G) X]

/-- The contragredient action of `ℤ_p[G]` on the `ℚ_p / ℤ_p`-valued characters of a
`ℤ_p[G]`-module: `op a` sends `χ` to `x ↦ χ (a • x)`. -/
noncomputable instance instModulePadicCharacterContragredient :
    Module (MonoidAlgebra ℤ_[p] G)ᵐᵒᵖ (X →ₗ[ℤ_[p]] ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) :=
  inferInstanceAs (Module (DomMulAct (MonoidAlgebra ℤ_[p] G)) _)

end ContragredientCharacter

variable [Finite G]

namespace AuslanderReitenTranspose

variable {P₁ P₀ M : Type*} [AddCommGroup P₁] [Module (MonoidAlgebra ℤ_[p] G) P₁] [Module ℤ_[p] P₁]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P₁]
  [AddCommGroup P₀] [Module (MonoidAlgebra ℤ_[p] G) P₀] [Module ℤ_[p] P₀]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P₀] [Module.Projective ℤ_[p] P₀]
  [AddCommGroup M] [Module (MonoidAlgebra ℤ_[p] G) M] [Module ℤ_[p] M]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M] [Module.Finite ℤ_[p] M]
  {f : P₁ →ₗ[MonoidAlgebra ℤ_[p] G] P₀} {π : P₀ →ₗ[MonoidAlgebra ℤ_[p] G] M}
  (hf : Function.Exact f π) (hfi : Function.Injective f) (hπ : Function.Surjective π)

/-- The additive part of `TauCeti.AuslanderReitenTranspose.torsionDualLinearEquiv`. -/
private def torsionDualAddEquiv :
    AuslanderReitenTranspose f ≃+
      (pPowerTorsion p (MonoidAlgebra ℤ_[p] G) M →ₗ[ℤ_[p]] ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) :=
  (groupAlgebraDualEquiv f).toAddEquiv.trans <|
    (LinearMap.quotientRangeContragredientDualMapEquiv f).toAddEquiv.trans
      (torsionDualEquiv p hf hfi hπ).toAddEquiv

private theorem torsionDualAddEquiv_mk (φ : Dual (MonoidAlgebra ℤ_[p] G) P₁) :
    torsionDualAddEquiv hf hfi hπ (mk f φ) =
      torsionDualMap p hf hfi hπ (MonoidAlgebra.dualLinearEquiv φ) := by
  simp [torsionDualAddEquiv]

/-- **The transpose of a `ℤ_p[G]`-module of projective dimension one is the Pontryagin dual of
its `p`-power torsion.** For a finite group `G` and an exact sequence `0 → P₁ → P₀ → M → 0` of
`ℤ_p[G]`-modules with `P₀` projective over `ℤ_p` and `M` finitely generated over `ℤ_p`, the
transpose `Tr f` (which is `E¹(M)` when `P₀` and `P₁` are projective over `ℤ_p[G]`) is isomorphic
to `Hom_{ℤ_p}(M[p^∞], ℚ_p / ℤ_p)`, compatibly with the action of `ℤ_p[G]ᵐᵒᵖ` on the transpose and
the contragredient action on characters. -/
def torsionDualLinearEquiv :
    AuslanderReitenTranspose f ≃ₗ[(MonoidAlgebra ℤ_[p] G)ᵐᵒᵖ]
      (pPowerTorsion p (MonoidAlgebra ℤ_[p] G) M →ₗ[ℤ_[p]]
        ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) where
  __ := torsionDualAddEquiv hf hfi hπ
  map_smul' a x := LinearMap.ext fun t ↦ by
    induction x using induction_on with | h φ => ?_
    rw [AddEquiv.toFun_eq_coe, ← map_smul, torsionDualAddEquiv_mk,
      torsionDualAddEquiv_mk, RingHom.id_apply, ← MulOpposite.op_unop a]
    erw [DomMulAct.mk_smul_linearMap_apply (MulOpposite.unop a)]
    rw [map_smul, ← torsionDualMap_comp_toLinearMap_apply]
    -- The contragredient action of `op a` on a base-ring functional is precomposition with `a`.
    refine congrArg (torsionDualMap p hf hfi hπ · t) (LinearMap.ext fun m ↦ ?_)
    erw [DomMulAct.mk_smul_linearMap_apply (MulOpposite.unop a)]

/-- `TauCeti.AuslanderReitenTranspose.torsionDualLinearEquiv` sends the class of a group-algebra
functional to the image of its coefficient-at-one functional under the connecting map. -/
@[simp]
theorem torsionDualLinearEquiv_mk (φ : Dual (MonoidAlgebra ℤ_[p] G) P₁) :
    torsionDualLinearEquiv hf hfi hπ (mk f φ) =
      torsionDualMap p hf hfi hπ (MonoidAlgebra.dualLinearEquiv φ) :=
  torsionDualAddEquiv_mk hf hfi hπ φ

end AuslanderReitenTranspose

section Stable

open AuslanderReitenTranspose

universe u₀ u₁ v₀ v₁

variable {M N : Type*} {P₀ : Type u₀} {P₁ : Type u₁} {Q₀ : Type v₀} {Q₁ : Type v₁}
  [AddCommGroup M] [Module (MonoidAlgebra ℤ_[p] G) M]
  [AddCommGroup N] [Module (MonoidAlgebra ℤ_[p] G) N]
  [AddCommGroup P₀] [Module (MonoidAlgebra ℤ_[p] G) P₀]
  [Module.Finite (MonoidAlgebra ℤ_[p] G) P₀] [Module.Projective (MonoidAlgebra ℤ_[p] G) P₀]
  [AddCommGroup P₁] [Module (MonoidAlgebra ℤ_[p] G) P₁]
  [Module.Finite (MonoidAlgebra ℤ_[p] G) P₁] [Module.Projective (MonoidAlgebra ℤ_[p] G) P₁]
  [AddCommGroup Q₀] [Module (MonoidAlgebra ℤ_[p] G) Q₀]
  [Module.Finite (MonoidAlgebra ℤ_[p] G) Q₀] [Module.Projective (MonoidAlgebra ℤ_[p] G) Q₀]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ_[p] G) Q₁]
  [Module.Finite (MonoidAlgebra ℤ_[p] G) Q₁] [Module.Projective (MonoidAlgebra ℤ_[p] G) Q₁]
  {f : P₁ →ₗ[MonoidAlgebra ℤ_[p] G] P₀} {π : P₀ →ₗ[MonoidAlgebra ℤ_[p] G] M}
  {g : Q₁ →ₗ[MonoidAlgebra ℤ_[p] G] Q₀} {ρ : Q₀ →ₗ[MonoidAlgebra ℤ_[p] G] N}

/-- **Modules of projective dimension one with isomorphic `p`-power torsion are stably
isomorphic** (NSW (5.4.11) with (5.6.9)). Let `G` be a finite group and let
`0 → P₁ → P₀ → M → 0` and `0 → Q₁ → Q₀ → N → 0` be exact sequences of `ℤ_p[G]`-modules with
finitely generated projective `P₀, P₁, Q₀, Q₁`. If the `p`-power torsion submodules of `M` and `N`
are isomorphic as `ℤ_p[G]`-modules, then `M ⊕ P₁ ⊕ Q₀ ≃ N ⊕ P₀ ⊕ Q₁` as `ℤ_p[G]`-modules. -/
theorem nonempty_linearEquiv_prod_of_pPowerTorsion_linearEquiv
    (hf : Function.Exact f π) (hfi : Function.Injective f) (hπ : Function.Surjective π)
    (hg : Function.Exact g ρ) (hgi : Function.Injective g) (hρ : Function.Surjective ρ)
    (e : pPowerTorsion p (MonoidAlgebra ℤ_[p] G) M ≃ₗ[MonoidAlgebra ℤ_[p] G]
      pPowerTorsion p (MonoidAlgebra ℤ_[p] G) N) :
    Nonempty ((M × (P₁ × Q₀)) ≃ₗ[MonoidAlgebra ℤ_[p] G] (N × (P₀ × Q₁))) := by
  -- Restrict all scalars to `ℤ_p`.
  let _ : Module ℤ_[p] P₁ := .compHom P₁ (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P₁ := .of_compHom _ _ _
  let _ : Module ℤ_[p] P₀ := .compHom P₀ (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P₀ := .of_compHom _ _ _
  let _ : Module ℤ_[p] M := .compHom M (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M := .of_compHom _ _ _
  let _ : Module ℤ_[p] Q₁ := .compHom Q₁ (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) Q₁ := .of_compHom _ _ _
  let _ : Module ℤ_[p] Q₀ := .compHom Q₀ (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) Q₀ := .of_compHom _ _ _
  let _ : Module ℤ_[p] N := .compHom N (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) N := .of_compHom _ _ _
  have : Module.Projective ℤ_[p] P₀ := .trans (S := MonoidAlgebra ℤ_[p] G)
  have : Module.Projective ℤ_[p] Q₀ := .trans (S := MonoidAlgebra ℤ_[p] G)
  have : Module.Finite (MonoidAlgebra ℤ_[p] G) M := .of_surjective π hπ
  have : Module.Finite ℤ_[p] M := .trans (MonoidAlgebra ℤ_[p] G) M
  have : Module.Finite (MonoidAlgebra ℤ_[p] G) N := .of_surjective ρ hρ
  have : Module.Finite ℤ_[p] N := .trans (MonoidAlgebra ℤ_[p] G) N
  -- Precomposition with `e.symm` is a `ℤ_p[G]ᵐᵒᵖ`-linear isomorphism of the character groups.
  let eT : (pPowerTorsion p (MonoidAlgebra ℤ_[p] G) M →ₗ[ℤ_[p]]
      ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) ≃ₗ[(MonoidAlgebra ℤ_[p] G)ᵐᵒᵖ]
      (pPowerTorsion p (MonoidAlgebra ℤ_[p] G) N →ₗ[ℤ_[p]] ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) :=
    { (e.restrictScalars ℤ_[p]).arrowCongrAddEquiv (.refl ℤ_[p] _) with
      map_smul' a χ := LinearMap.ext fun t ↦ by
        simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply,
          LinearEquiv.arrowCongrAddEquiv_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.refl_apply, LinearEquiv.restrictScalars_symm_apply]
        erw [DomMulAct.mk_smul_linearMap_apply (MulOpposite.unop a),
          DomMulAct.mk_smul_linearMap_apply (MulOpposite.unop a)]
        exact congrArg χ (e.symm.map_smul (MulOpposite.unop a) t).symm }
  -- Both transposes are the Pontryagin duals of the `p`-power torsion, compatibly with the
  -- action of `ℤ_p[G]ᵐᵒᵖ`, so `e` induces an isomorphism of transposes.
  exact nonempty_linearEquiv_prod_of_linearEquiv hf hπ hg hρ
    ((torsionDualLinearEquiv hf hfi hπ).trans (eT.trans (torsionDualLinearEquiv hg hgi hρ).symm))

/-- **The stable class of a module of projective dimension one is determined by its torsion**
(NSW (5.4.11) with (5.6.9)). For a finite group `G`, two `ℤ_p[G]`-modules presented as quotients
of finitely generated projectives by projective submodules, with isomorphic `p`-power torsion
submodules, become isomorphic after adding finitely generated projective `ℤ_p[G]`-modules:
`M ⊕ P ≃ N ⊕ Q`. The summands are explicit in
`TauCeti.nonempty_linearEquiv_prod_of_pPowerTorsion_linearEquiv`. -/
theorem exists_projective_prod_linearEquiv_of_torsion
    (hf : Function.Exact f π) (hfi : Function.Injective f) (hπ : Function.Surjective π)
    (hg : Function.Exact g ρ) (hgi : Function.Injective g) (hρ : Function.Surjective ρ)
    (e : pPowerTorsion p (MonoidAlgebra ℤ_[p] G) M ≃ₗ[MonoidAlgebra ℤ_[p] G]
      pPowerTorsion p (MonoidAlgebra ℤ_[p] G) N) :
    ∃ (P : Type (max u₁ v₀)) (Q : Type (max u₀ v₁)) (_ : AddCommGroup P)
      (_ : Module (MonoidAlgebra ℤ_[p] G) P) (_ : AddCommGroup Q)
      (_ : Module (MonoidAlgebra ℤ_[p] G) Q),
      Module.Finite (MonoidAlgebra ℤ_[p] G) P ∧ Module.Projective (MonoidAlgebra ℤ_[p] G) P ∧
      Module.Finite (MonoidAlgebra ℤ_[p] G) Q ∧ Module.Projective (MonoidAlgebra ℤ_[p] G) Q ∧
      Nonempty ((M × P) ≃ₗ[MonoidAlgebra ℤ_[p] G] (N × Q)) :=
  ⟨P₁ × Q₀, P₀ × Q₁, _, _, _, _, inferInstance, inferInstance, inferInstance, inferInstance,
    nonempty_linearEquiv_prod_of_pPowerTorsion_linearEquiv hf hfi hπ hg hgi hρ e⟩

end Stable

end TauCeti
