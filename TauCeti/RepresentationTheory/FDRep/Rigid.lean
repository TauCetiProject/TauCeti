/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.Algebra.Category.FGModuleCat.Rigid

/-!
# Duals of finite-dimensional group representations

For a field `k` and a group `G`, the monoidal category `FDRep k G` of finite-dimensional
representations inherits right and left duals as `Action (FGModuleCat k) G` from the rigid
structure on `FGModuleCat k`. On underlying vector spaces, both `Vᘁ` and `ᘁV` have carrier
`Module.Dual k V`, and a group element `g` acts through the adjoint mate of `V.ρ g⁻¹`
(`Action.rightDual_ρ` and `Action.leftDual_ρ`). Since both right and left adjoint mates in
`FGModuleCat k` are linear transposes (`FGModuleCat.rightAdjointMate_hom` and
`FGModuleCat.leftAdjointMate_hom`), both categorical duals carry the contragredient representation
`Representation.dual V.ρ`.

## Main results

* `FDRep.rightDual_ρ`: the right dual `Vᘁ` carries `Representation.dual V.ρ`;
* `FDRep.leftDual_ρ`: the left dual `ᘁV` carries `Representation.dual V.ρ`.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Section 2.10, for duals of group representations.
-/

public section

open CategoryTheory MonoidalCategory

namespace FDRep

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The right dual of a finite-dimensional representation carries the contragredient
representation `Representation.dual V.ρ`. -/
@[simp]
theorem rightDual_ρ (V : FDRep k G) : (Vᘁ : FDRep k G).ρ = Representation.dual V.ρ := by
  ext g φ
  have h := congrArg (fun u : V.Vᘁ ⟶ V.Vᘁ => u.hom.hom) (Action.rightDual_ρ V g)
  rw [FGModuleCat.rightAdjointMate_hom, FDRep.hom_hom_action_ρ V, LinearMap.dualMap_def] at h
  -- The carrier of `Vᘁ` is `V.Vᘁ` by `Action.rightDual_v`, which is `Module.Dual k V` by
  -- `FGModuleCat.FGModuleCatDual_coe`.
  exact (LinearMap.congr_fun (FDRep.hom_hom_action_ρ (Vᘁ : FDRep k G) g).symm φ).trans
    ((LinearMap.congr_fun h φ).trans
      (LinearMap.congr_fun (Representation.dual_apply (ρV := V.ρ) g).symm φ))

/-- The left dual of a finite-dimensional representation carries the contragredient
representation `Representation.dual V.ρ`. -/
@[simp]
theorem leftDual_ρ (V : FDRep k G) : (ᘁV : FDRep k G).ρ = Representation.dual V.ρ := by
  ext g φ
  have h := congrArg (fun u : (ᘁV.V : FGModuleCat k) ⟶ ᘁV.V => u.hom.hom) (Action.leftDual_ρ V g)
  rw [FGModuleCat.leftAdjointMate_hom, FDRep.hom_hom_action_ρ V, LinearMap.dualMap_def] at h
  -- The carrier of `ᘁV` is `ᘁV.V` by `Action.leftDual_v`, which is `Module.Dual k V` by
  -- `FGModuleCat.leftDual_eq` and `FGModuleCat.FGModuleCatDual_coe`.
  exact (LinearMap.congr_fun (FDRep.hom_hom_action_ρ (ᘁV : FDRep k G) g).symm φ).trans
    ((LinearMap.congr_fun h φ).trans
      (LinearMap.congr_fun (Representation.dual_apply (ρV := V.ρ) g).symm φ))

end FDRep
