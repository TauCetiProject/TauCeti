/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.DirectSum

/-!
# Morphisms out of an external direct sum of Lie modules

A morphism out of an external direct sum `⨁ i, P i` of Lie modules is the family of its
restrictions to the summands, and conversely a family of morphisms out of the summands assembles to
one by the universal property `DirectSum.toModule` of the direct sum. This is the additivity of the
morphism space over a direct sum in its *source*, the counterpart of
`TauCeti.LieModule.lieModuleHomDirectSumEquiv` for the target.

## Main definitions

* `TauCeti.LieModule.directSumLieModuleHomEquiv`: a morphism out of an external direct sum is the
  family of its restrictions to the summands.
-/

public section

open scoped DirectSum

universe u v w w₁ w₂

namespace TauCeti.LieModule

variable {R : Type u} {L : Type v} {ι : Type w₂} [DecidableEq ι]
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable (R L)
variable (P : ι → Type w₁) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
  [∀ i, LieRingModule L (P i)]
variable (S : Type w) [AddCommGroup S] [Module R S] [LieRingModule L S] [_root_.LieModule R L S]

/-- **The morphism space is additive over a direct sum in its source.** A morphism out of an
external direct sum of Lie modules is the family of its restrictions to the summands; this is an
isomorphism of `R`-modules. -/
def directSumLieModuleHomEquiv :
    ((⨁ i, P i) →ₗ⁅R,L⁆ S) ≃ₗ[R] Π i, (P i →ₗ⁅R,L⁆ S) where
  toFun f i := f.comp (DirectSum.lieModuleOf R ι L P i)
  map_add' _ _ := by ext i p; simp
  map_smul' _ _ := by ext i p; simp
  invFun g :=
    { toLinearMap := DirectSum.toModule R ι S fun i ↦ (g i : P i →ₗ[R] S)
      map_lie' := fun {x m} ↦ by
        induction m using DirectSum.induction_on with
        | zero => simp
        | of i p =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
          rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_lie, DirectSum.toModule_lof,
            DirectSum.toModule_lof]
          exact (g i).map_lie x p
        | add m n hm hn =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at hm hn ⊢
          rw [lie_add, map_add, map_add, hm, hn, lie_add] }
  left_inv f := by
    refine LieModuleHom.ext fun x ↦ ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i p => simp [← DirectSum.lof_eq_of R]
    | add m n hm hn => rw [map_add, hm, hn, map_add]
  right_inv g := by
    ext j p
    simp [← DirectSum.lof_eq_of R]

@[simp]
theorem directSumLieModuleHomEquiv_apply (f : (⨁ i, P i) →ₗ⁅R,L⁆ S) (i : ι) (p : P i) :
    directSumLieModuleHomEquiv R L P S f i p = f (DirectSum.of P i p) :=
  (rfl)

@[simp]
theorem directSumLieModuleHomEquiv_symm_apply_of (g : Π i, (P i →ₗ⁅R,L⁆ S)) (i : ι) (p : P i) :
    (directSumLieModuleHomEquiv R L P S).symm g (DirectSum.of P i p) = g i p := by
  simp [directSumLieModuleHomEquiv, ← DirectSum.lof_eq_of R]

end TauCeti.LieModule
