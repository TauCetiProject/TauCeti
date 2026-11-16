/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Transitivity of cotensor induction

For coalgebra maps `f : C →ₗc[R] D` and `g : D →ₗc[R] E`, induction first along `g`
and then along `f` agrees with induction along `g.comp f`. The comparison is an
isomorphism of `C`-comodules, natural in the coefficient comodule, and carries successive
counit evaluations to the evaluation for the composite map.

Only `C` and `D` need be flat. No flatness or finiteness condition is imposed on the
coefficient comodule or on `E`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.3.3–I.3.7
  (transitivity of induction).
* M. Takeuchi, *Morita theorems for categories of comodules*, J. Fac. Sci. Univ. Tokyo 24
  (1977), for cotensor induction and its reciprocity.
-/

public section

open CategoryTheory
open scoped TensorProduct
open TauCeti TauCeti.Comodule

namespace CoalgHom

universe u v w x y z

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable {D : Type w} [AddCommMonoid D] [Module R D] [Coalgebra R D] [Module.Flat R D]
variable {E : Type x} [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable (f : C →ₗc[R] D) (g : D →ₗc[R] E)
variable {M : Type (max v w y)} [AddCommMonoid M] [Module R M] [Comodule R E M]
variable {N : Type z} [AddCommMonoid N] [Module R N] [Comodule R C N]

private noncomputable def transReciprocity :
    Hom R C N (induced f (induced g M)) ≃ₗ[R]
      (letI := Corestrict (M := N) (g.comp f); Hom R E N M) := by
  letI := Corestrict (M := N) f
  let e : Hom R D N (induced g M) ≃ₗ[R]
      (letI := Corestrict (M := N) (g.comp f); Hom R E N M) := by
    let a := inducedEquiv g (N := N) (M := M)
    letI := Corestrict (M := N) (g.comp f)
    -- Repackage the same linear map using the equality of the composite and successive
    -- coactions. Keeping its underlying map explicit gives computation without casts.
    let b : Hom R E N M ≃ₗ[R]
        (letI := Corestrict (M := N) g; Hom R E N M) :=
      { toFun h := by
          let l := h.toLinearMap
          have hl := h.map_coact
          letI := Corestrict (M := N) g
          exact
            { toLinearMap := l
              map_coact := by
                simpa only [corestrict_coact, corestrictCoact_comp] using hl }
        invFun h := by
          letI := Corestrict (M := N) g
          let l := h.toLinearMap
          have hl := h.map_coact
          letI := Corestrict (M := N) (g.comp f)
          exact
            { toLinearMap := l
              map_coact := by
                simpa only [corestrict_coact, corestrictCoact_comp] using hl }
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    exact a.trans b.symm
  exact (inducedEquiv f).trans e

private theorem transReciprocity_apply (h : Hom R C N (induced f (induced g M))) :
    letI := Corestrict (M := induced g M) g
    letI := Corestrict (M := N) (g.comp f)
    ∀ n, transReciprocity f g h n = inducedEval g (inducedEquiv f h n) := by
  intro n
  simp only [transReciprocity, LinearEquiv.trans_apply, inducedEquiv_apply,
    Hom.comp_apply, corestrictHom_apply]
  rfl

private theorem transReciprocity_comp
    {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (h : Hom R C N (induced f (induced g M))) (k : Hom R C P N) :
    letI := Corestrict (M := N) (g.comp f)
    letI := Corestrict (M := P) (g.comp f)
    transReciprocity f g (h.comp k) =
      (transReciprocity f g h).comp (corestrictHom (g.comp f) k) := by
  let := Corestrict (M := N) (g.comp f)
  let := Corestrict (M := P) (g.comp f)
  apply Hom.ext
  intro p
  simp only [transReciprocity_apply, Hom.comp_apply, corestrictHom_apply,
    inducedEquiv_comp]

private noncomputable def transHomEquiv :
    Hom R C N (induced f (induced g M)) ≃ₗ[R] Hom R C N (induced (g.comp f) M) :=
  (transReciprocity f g).trans (inducedEquiv (g.comp f)).symm

private theorem transHomEquiv_comp
    {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (h : Hom R C N (induced f (induced g M))) (k : Hom R C P N) :
    transHomEquiv f g (h.comp k) = (transHomEquiv f g h).comp k := by
  apply (inducedEquiv (g.comp f)).injective
  simp only [transHomEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    inducedEquiv_comp, transReciprocity_comp]

variable (M) in
/-- Transitivity of cotensor induction as an isomorphism of comodules. Successive evaluation
along `f` and `g` is evaluation along `g.comp f`. -/
noncomputable def inducedTransIso :
    ComoduleCat.of R C (induced f (induced g M)) ≅
      ComoduleCat.of R C (induced (g.comp f) M) :=
  Yoneda.ext _ _ (fun h ↦ transHomEquiv f g h) (fun h ↦ (transHomEquiv f g).symm h)
    (fun h ↦ (transHomEquiv f g).symm_apply_apply h)
    (fun h ↦ (transHomEquiv f g).apply_symm_apply h)
    (fun k h ↦ transHomEquiv_comp f g h k)

private theorem inducedTransIso_hom_eq :
    (inducedTransIso f g M).hom =
      transHomEquiv f g (Hom.id R C (induced f (induced g M))) :=
  (rfl)

private theorem inducedTransIso_hom_comp (h : Hom R C N (induced f (induced g M))) :
    (inducedTransIso f g M).hom.comp h = transHomEquiv f g h := by
  rw [inducedTransIso_hom_eq, ← transHomEquiv_comp, Hom.id_comp]

/-- On the ambient cotensor products, transitivity applies the counit of `D` to the
intermediate induction and leaves the `C` factor unchanged. -/
@[simp]
theorem coe_inducedTransIso_hom_apply (t : induced f (induced g M)) :
    letI := Corestrict (M := induced g M) g
    (ComoduleCat.hom R C (inducedTransIso f g M).hom t : M ⊗[R] C) =
      (inducedEval g).toLinearMap.rTensor C t := by
  let := Corestrict (M := induced g M) g
  let := Corestrict (M := induced f (induced g M)) f
  have hf := congrArg (fun k ↦ (k t : (induced g M) ⊗[R] C))
    ((inducedEquiv f).symm_apply_apply (Hom.id R C (induced f (induced g M))))
  simp only [inducedEquiv_symm_apply, coe_inducedLift_apply, inducedEquiv_apply,
    Hom.comp_toLinearMap, corestrictHom_toLinearMap, Hom.id_toLinearMap,
    LinearMap.comp_id, Hom.id_apply] at hf
  let := Corestrict (M := induced f (induced g M)) (g.comp f)
  have he : (transReciprocity f g (Hom.id R C (induced f (induced g M)))).toLinearMap =
      (inducedEval g).toLinearMap ∘ₗ (inducedEval f).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [Hom.coe_toLinearMap, transReciprocity_apply, inducedEquiv_apply, Hom.comp_apply,
      corestrictHom_apply, Hom.id_apply, LinearMap.comp_apply]
  rw [inducedTransIso_hom_eq, transHomEquiv, LinearEquiv.trans_apply,
    inducedEquiv_symm_apply, coe_inducedLift_apply, he, LinearMap.rTensor_comp_apply, hf]

/-- The transitivity isomorphism carries successive counit evaluation to the counit
evaluation for the composite coalgebra map. -/
theorem inducedEval_inducedTransIso_hom (t : induced f (induced g M)) :
    letI := Corestrict (M := induced (g.comp f) M) (g.comp f)
    letI := Corestrict (M := induced f (induced g M)) f
    letI := Corestrict (M := induced g M) g
    inducedEval (g.comp f) (ComoduleCat.hom R C (inducedTransIso f g M).hom t) =
      inducedEval g (inducedEval f t) := by
  have h := (inducedEquiv (g.comp f)).apply_symm_apply
    (transReciprocity f g (Hom.id R C (induced f (induced g M))))
  have ht := congrArg (fun k ↦ k t) h
  simpa only [inducedTransIso_hom_eq, transHomEquiv, LinearEquiv.trans_apply,
    inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply, transReciprocity_apply,
    Hom.id_apply] using ht

/-- Evaluation after the inverse transitivity map is the original composite evaluation. -/
theorem inducedEval_inducedTransIso_inv (t : induced (g.comp f) M) :
    letI := Corestrict (M := induced (g.comp f) M) (g.comp f)
    letI := Corestrict (M := induced f (induced g M)) f
    letI := Corestrict (M := induced g M) g
    inducedEval g (inducedEval f (ComoduleCat.hom R C (inducedTransIso f g M).inv t)) =
      inducedEval (g.comp f) t := by
  rw [← inducedEval_inducedTransIso_hom]
  exact congrArg (inducedEval (g.comp f))
    (ConcreteCategory.congr_hom (inducedTransIso f g M).inv_hom_id t)

variable {M' : Type (max v w y)} [AddCommMonoid M'] [Module R M'] [Comodule R E M']

/-- Transitivity of induction is natural in the coefficient comodule. -/
theorem inducedTransIso_naturality (h : Hom R E M M') :
    (inducedTransIso f g M').hom.comp (inducedMap f (inducedMap g h)) =
      (inducedMap (g.comp f) h).comp (inducedTransIso f g M).hom := by
  apply (inducedEquiv (g.comp f)).injective
  rw [inducedTransIso_hom_comp, inducedEquiv_inducedMap_comp]
  let := Corestrict (M := induced f (induced g M)) (g.comp f)
  apply Hom.ext
  intro t
  simp only [transHomEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    transReciprocity_apply, inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply]
  rw [inducedEval_inducedTransIso_hom]
  have hf := congrArg (fun k ↦ k t)
    (inducedEquiv_inducedMap_comp f (inducedMap g h)
      (Hom.id R C (induced f (induced g M))))
  simp only [inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply, Hom.id_apply] at hf
  rw [hf]
  have hg := congrArg (fun k ↦ k (inducedEval f t))
    (inducedEquiv_inducedMap_comp g h (Hom.id R D (induced g M)))
  simpa only [inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply, Hom.id_apply]
    using hg

end CoalgHom
