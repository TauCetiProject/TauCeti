/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced.Basic

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

universe u v w x y y' z

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable {D : Type w} [AddCommMonoid D] [Module R D] [Coalgebra R D] [Module.Flat R D]
variable {E : Type x} [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable (f : C →ₗc[R] D) (g : D →ₗc[R] E)
variable {M : Type y} [AddCommMonoid M] [Module R M] [Comodule R E M]
variable {N : Type z} [AddCommMonoid N] [Module R N] [Comodule R C N]

private def corestrictCompHomEquiv :
    (letI := Corestrict (M := N) f
     letI := Corestrict (M := N) g
     Hom R E N M) ≃ₗ[R]
      (letI := Corestrict (M := N) (g.comp f); Hom R E N M) :=
  letI := Corestrict (M := N) f
  { toFun h :=
      letI := Corestrict (M := N) g
      let l := h.toLinearMap
      have hl := h.map_coact
      letI := Corestrict (M := N) (g.comp f)
      { toLinearMap := l
        map_coact := by simpa only [corestrict_coact, corestrictCoact_comp] using hl }
    invFun h :=
      letI := Corestrict (M := N) (g.comp f)
      let l := h.toLinearMap
      have hl := h.map_coact
      letI := Corestrict (M := N) g
      { toLinearMap := l
        map_coact := by simpa only [corestrict_coact, corestrictCoact_comp] using hl }
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

omit [Module.Flat R C] [Module.Flat R D] in
private theorem corestrictCompHomEquiv_apply
    (h : letI := Corestrict (M := N) f
         letI := Corestrict (M := N) g
         Hom R E N M) (n : N) : corestrictCompHomEquiv f g h n = h n :=
  rfl

private noncomputable def transReciprocity :
    Hom R C N (induced f (induced g M)) ≃ₗ[R]
      (letI := Corestrict (M := N) (g.comp f); Hom R E N M) :=
  letI := Corestrict (M := N) f
  (inducedEquiv f).trans ((inducedEquiv g).trans (corestrictCompHomEquiv f g))

private theorem transReciprocity_apply (h : Hom R C N (induced f (induced g M))) :
    letI := Corestrict (M := induced g M) g
    letI := Corestrict (M := N) (g.comp f)
    ∀ n, transReciprocity f g h n = inducedEval g (inducedEquiv f h n) := by
  intro n
  simp only [transReciprocity, LinearEquiv.trans_apply, corestrictCompHomEquiv_apply,
    inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply]

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

/-- The comparison from successive cotensor induction to induction along the composite. -/
noncomputable def inducedTransHom :
    Hom R C (induced f (induced g M)) (induced (g.comp f) M) :=
  transHomEquiv f g (Hom.id R C (induced f (induced g M)))

/-- The comparison from induction along the composite to successive cotensor induction. -/
noncomputable def inducedTransInv :
    Hom R C (induced (g.comp f) M) (induced f (induced g M)) :=
  (transHomEquiv f g).symm (Hom.id R C (induced (g.comp f) M))

private theorem inducedTransHom_comp (h : Hom R C N (induced f (induced g M))) :
    (inducedTransHom f g).comp h = transHomEquiv f g h := by
  rw [inducedTransHom, ← transHomEquiv_comp, Hom.id_comp]

/-- Successive induction followed by the inverse comparison is the identity. -/
@[simp]
theorem inducedTransInv_comp_inducedTransHom :
    (inducedTransInv f g (M := M)).comp (inducedTransHom f g) =
      Hom.id R C (induced f (induced g M)) := by
  apply (transHomEquiv f g).injective
  rw [transHomEquiv_comp, inducedTransInv, LinearEquiv.apply_symm_apply,
    Hom.id_comp, inducedTransHom]

/-- The inverse comparison followed by the forward comparison is the identity. -/
@[simp]
theorem inducedTransHom_comp_inducedTransInv :
    (inducedTransHom f g (M := M)).comp (inducedTransInv f g) =
      Hom.id R C (induced (g.comp f) M) := by
  rw [inducedTransHom_comp, inducedTransInv, LinearEquiv.apply_symm_apply]

/-- Applying the inverse comparison after the forward comparison recovers the input. -/
@[simp]
theorem inducedTransInv_inducedTransHom (t : induced f (induced g M)) :
    inducedTransInv f g (inducedTransHom f g t) = t := by
  simpa only [Hom.comp_apply, Hom.id_apply] using
    DFunLike.congr_fun (inducedTransInv_comp_inducedTransHom f g) t

/-- Applying the forward comparison after the inverse comparison recovers the input. -/
@[simp]
theorem inducedTransHom_inducedTransInv (t : induced (g.comp f) M) :
    inducedTransHom f g (inducedTransInv f g t) = t := by
  simpa only [Hom.comp_apply, Hom.id_apply] using
    DFunLike.congr_fun (inducedTransHom_comp_inducedTransInv f g) t

/-- On the ambient tensor products, transitivity applies the counit of `D` to the
intermediate induction and leaves the `C` factor unchanged. -/
@[simp]
theorem coe_inducedTransHom_apply (t : induced f (induced g M)) :
    letI := Corestrict (M := induced g M) g
    (inducedTransHom f g t : M ⊗[R] C) =
      (inducedEval g).toLinearMap.rTensor C t := by
  let := Corestrict (M := induced g M) g
  let := Corestrict (M := induced f (induced g M)) f
  let := Corestrict (M := induced f (induced g M)) (g.comp f)
  have he : (transReciprocity f g (Hom.id R C (induced f (induced g M)))).toLinearMap =
      (inducedEval g).toLinearMap ∘ₗ (inducedEval f).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [Hom.coe_toLinearMap, transReciprocity_apply, inducedEquiv_apply, Hom.comp_apply,
      corestrictHom_apply, Hom.id_apply, LinearMap.comp_apply]
  rw [inducedTransHom, transHomEquiv, LinearEquiv.trans_apply,
    inducedEquiv_symm_apply, coe_inducedLift_apply, he, LinearMap.rTensor_comp_apply,
    rTensor_inducedEval_coact]

/-- On ambient tensors, the inverse comparison comultiplies the `C` factor and applies
`f` to its first component. -/
@[simp]
theorem subtype_rTensor_coe_inducedTransInv_apply (t : induced (g.comp f) M) :
    (SMulMemClass.subtype (induced g M)).rTensor C
        (inducedTransInv f g t : (induced g M) ⊗[R] C) =
      (TensorProduct.assoc R M D C).symm
        (((f : C →ₗ[R] D).rTensor C ∘ₗ Coalgebra.comul).lTensor M t) := by
  let := Corestrict (M := induced g M) g
  let e := (inducedEval g (M := M)).toLinearMap
  let l := (f : C →ₗ[R] D).rTensor C ∘ₗ Coalgebra.comul
  have he : e.rTensor D ∘ₗ coact (R := R) (C := D) =
      SMulMemClass.subtype (induced g M) :=
    LinearMap.ext (rTensor_inducedEval_coact g)
  have hn (s : (induced g M) ⊗[R] C) :
      (e.rTensor D).rTensor C ((TensorProduct.assoc R (induced g M) D C).symm
        (l.lTensor (induced g M) s)) =
      (TensorProduct.assoc R M D C).symm (l.lTensor M (e.rTensor C s)) := by
    simp only [LinearMap.rTensor_def, LinearMap.lTensor_def,
      TensorProduct.map_map_assoc_symm, TensorProduct.map_id, TensorProduct.map_map,
      LinearMap.comp_id, LinearMap.id_comp]
  have ht := congrArg ((e.rTensor D).rTensor C)
    ((mem_induced_iff f).mp (inducedTransInv f g t).property)
  rw [← LinearMap.rTensor_comp_apply, he, hn] at ht
  rw [ht, ← coe_inducedTransHom_apply, inducedTransHom_inducedTransInv]

/-- The transitivity isomorphism carries successive counit evaluation to the counit
evaluation for the composite coalgebra map. -/
theorem inducedEval_inducedTransHom (t : induced f (induced g M)) :
    letI := Corestrict (M := induced (g.comp f) M) (g.comp f)
    letI := Corestrict (M := induced f (induced g M)) f
    letI := Corestrict (M := induced g M) g
    inducedEval (g.comp f) (inducedTransHom f g t) =
      inducedEval g (inducedEval f t) := by
  have h := (inducedEquiv (g.comp f)).apply_symm_apply
    (transReciprocity f g (Hom.id R C (induced f (induced g M))))
  have ht := congrArg (fun k ↦ k t) h
  simpa only [inducedTransHom, transHomEquiv, LinearEquiv.trans_apply,
    inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply, transReciprocity_apply,
    Hom.id_apply] using ht

/-- Evaluation after the inverse transitivity map is the original composite evaluation. -/
theorem inducedEval_inducedEval_inducedTransInv (t : induced (g.comp f) M) :
    letI := Corestrict (M := induced (g.comp f) M) (g.comp f)
    letI := Corestrict (M := induced f (induced g M)) f
    letI := Corestrict (M := induced g M) g
    inducedEval g (inducedEval f (inducedTransInv f g t)) =
      inducedEval (g.comp f) t := by
  rw [← inducedEval_inducedTransHom, inducedTransHom_inducedTransInv]

variable {M' : Type y'} [AddCommMonoid M'] [Module R M'] [Comodule R E M']

/-- Transitivity of induction is natural in the coefficient comodule. -/
theorem inducedTransHom_naturality (h : Hom R E M M') :
    (inducedTransHom f g (M := M')).comp (inducedMap f (inducedMap g h)) =
      (inducedMap (g.comp f) h).comp (inducedTransHom f g (M := M)) := by
  apply (inducedEquiv (g.comp f)).injective
  rw [inducedTransHom_comp, inducedEquiv_inducedMap_comp]
  let := Corestrict (M := induced f (induced g M)) (g.comp f)
  apply Hom.ext
  intro t
  simp only [transHomEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    transReciprocity_apply, inducedEquiv_apply, Hom.comp_apply, corestrictHom_apply]
  rw [inducedEval_inducedTransHom, inducedEval_inducedMap, inducedEval_inducedMap]

/-- The inverse transitivity comparison is natural in the coefficient comodule. -/
theorem inducedTransInv_naturality (h : Hom R E M M') :
    (inducedTransInv f g (M := M')).comp (inducedMap (g.comp f) h) =
      (inducedMap f (inducedMap g h)).comp (inducedTransInv f g (M := M)) := by
  apply (transHomEquiv f g).injective
  rw [transHomEquiv_comp, inducedTransInv, LinearEquiv.apply_symm_apply, Hom.id_comp,
    ← inducedTransHom_comp, ← Hom.comp_assoc, inducedTransHom_naturality,
    Hom.comp_assoc, inducedTransHom_comp_inducedTransInv, Hom.comp_id]

section Bundled

variable {M : Type (max w y)} [AddCommMonoid M] [Module R M] [Comodule R E M]
variable {M' : Type (max w y)} [AddCommMonoid M'] [Module R M'] [Comodule R E M']

variable (M) in
/-- Transitivity of cotensor induction as an isomorphism of comodules. Successive evaluation
along `f` and `g` is evaluation along `g.comp f`. -/
noncomputable def inducedTransIso :
    ComoduleCat.of R C (induced f (induced g M)) ≅
      ComoduleCat.of R C (induced (g.comp f) M) where
  hom := ComoduleCat.ofHom R C (inducedTransHom f g)
  inv := ComoduleCat.ofHom R C (inducedTransInv f g)
  hom_inv_id := by
    rw [← ComoduleCat.ofHom_comp, inducedTransInv_comp_inducedTransHom, ComoduleCat.ofHom_id]
  inv_hom_id := by
    rw [← ComoduleCat.ofHom_comp, inducedTransHom_comp_inducedTransInv, ComoduleCat.ofHom_id]

/-- The forward map of the bundled transitivity isomorphism is the unbundled comparison. -/
@[simp]
theorem inducedTransIso_hom :
    (inducedTransIso f g M).hom = ComoduleCat.ofHom R C (inducedTransHom f g) :=
  (rfl)

/-- The inverse map of the bundled transitivity isomorphism is the unbundled comparison. -/
@[simp]
theorem inducedTransIso_inv :
    (inducedTransIso f g M).inv = ComoduleCat.ofHom R C (inducedTransInv f g) :=
  (rfl)

/-- The bundled transitivity isomorphism is natural in the coefficient comodule. -/
theorem inducedTransIso_naturality (h : Hom R E M M') :
    ComoduleCat.ofHom R C (inducedMap f (inducedMap g h)) ≫ (inducedTransIso f g M').hom =
      (inducedTransIso f g M).hom ≫ ComoduleCat.ofHom R C (inducedMap (g.comp f) h) := by
  simp only [inducedTransIso_hom, ← ComoduleCat.ofHom_comp, inducedTransHom_naturality]

end Bundled

end CoalgHom
