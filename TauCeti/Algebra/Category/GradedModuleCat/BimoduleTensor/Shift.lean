/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Shift

/-!
# Internal shifts and balanced tensor composition

The tensor of two internally shifted graded bimodules is the internal shift of their
balanced tensor by the sum of the two shifts. The isomorphism sends each pure tensor to
itself; internal degrees add and introduce no sign. Cohomological tensor signs are separate
and remain those of Mathlib totalization.

The construction uses the public homogeneous balanced lift and pure-tensor extensionality.
It applies to independently sized bimodules over three graded algebras. Both directions
have pure-tensor formulas, and the comparison is natural in the two bimodule maps.

The shift convention is `M{a}_p = M_{p-a}`, as in `GradedModuleCat.shiftObj`.
-/

public section

noncomputable section
open CategoryTheory MulOpposite
open scoped TensorProduct
namespace TauCeti.GradedModuleCat

universe vM vN uk uA uB uC
variable {k : Type uk} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing k] [Ring A] [Ring B] [Ring C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B) (Θ : InternalGrading k C)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece]
  (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece)

private abbrev shiftPair (a b : ℤ) :
    (M.shiftObj a) →ₗ[k] (N.shiftObj b) →ₗ[k]
      (bimoduleTensorObj Γ Δ Θ M N).shiftObj (a + b) where
  toFun m :=
    { toFun := bimoduleTensorTmul Γ Δ Θ M N m
      map_add' n n' := bimoduleTensorTmul_add_right Γ Δ Θ M N m n n'
      map_smul' r n := bimoduleTensorTmul_smul_right Γ Δ Θ M N r m n }
  map_add' m m' := by ext n; exact bimoduleTensorTmul_add_left Γ Δ Θ M N m m' n
  map_smul' r m := by ext n; exact bimoduleTensorTmul_smul_left Γ Δ Θ M N r m n

private theorem shiftPair_degree (a b : ℤ)
    {p q : ℤ} {m : M.shiftObj a} {n : N.shiftObj b}
    (hm : m ∈ (M.shiftObj a).grading.piece p) (hn : n ∈ (N.shiftObj b).grading.piece q) :
    shiftPair Γ Δ Θ M N a b m n ∈
      ((bimoduleTensorObj Γ Δ Θ M N).shiftObj (a + b)).grading.piece (p + q) := by
  rw [mem_shiftObj_piece_iff] at hm hn ⊢
  simp only [shiftPair, LinearMap.coe_mk, AddHom.coe_mk]
  have h := bimoduleTensorTmul_mem Γ Δ Θ M N hm hn
  have hdeg : p - a + (q - b) = p + q - (a + b) := by omega
  simpa only [hdeg] using h

private def shiftHom (a b : ℤ) :
    bimoduleTensorObj Γ Δ Θ (M.shiftObj a) (N.shiftObj b) ⟶
      (bimoduleTensorObj Γ Δ Θ M N).shiftObj (a + b) :=
  bimoduleTensorLift Γ Δ Θ (shiftPair Γ Δ Θ M N a b)
    (by intro x m n; exact bimoduleTensorTmul_balance Γ Δ Θ M N x m n)
    (fun x m n ↦ by
      simp only [shiftPair, LinearMap.coe_mk, AddHom.coe_mk,
        tmul_smul_bimoduleTensorTmul,
        ← Algebra.TensorProduct.one_def, one_smul])
    (fun x m n ↦ by
      simp only [shiftPair, LinearMap.coe_mk, AddHom.coe_mk,
        tmul_smul_bimoduleTensorTmul,
        ← Algebra.TensorProduct.one_def, one_smul])
    (shiftPair_degree Γ Δ Θ M N a b)

private theorem shiftHom_tmul (a b : ℤ) (m : M) (n : N) :
    (shiftHom Γ Δ Θ M N a b).hom
        (bimoduleTensorTmul Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m n) =
      bimoduleTensorTmul Γ Δ Θ M N m n := by
  rw [shiftHom, bimoduleTensorLift_tmul (M := M.shiftObj a) (N := N.shiftObj b)
    (hdegree := shiftPair_degree Γ Δ Θ M N a b)]
  rfl

private abbrev unshiftPair (a b : ℤ) :
    M →ₗ[k] N →ₗ[k]
      (bimoduleTensorObj Γ Δ Θ (M.shiftObj a) (N.shiftObj b)).shiftObj (-(a + b)) where
  toFun m :=
    { toFun := bimoduleTensorTmul Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m
      map_add' n n' := bimoduleTensorTmul_add_right Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m n n'
      map_smul' r n := bimoduleTensorTmul_smul_right Γ Δ Θ (M.shiftObj a) (N.shiftObj b) r m n }
  map_add' m m' := by
    ext n
    exact bimoduleTensorTmul_add_left Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m m' n
  map_smul' r m := by
    ext n
    exact bimoduleTensorTmul_smul_left Γ Δ Θ (M.shiftObj a) (N.shiftObj b) r m n

private theorem unshiftPair_degree (a b : ℤ)
    {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ N.grading.piece q) :
    unshiftPair Γ Δ Θ M N a b m n ∈
      ((bimoduleTensorObj Γ Δ Θ (M.shiftObj a) (N.shiftObj b)).shiftObj (-(a + b))).grading.piece
        (p + q) := by
  have hm' : m ∈ (M.shiftObj a).grading.piece (p + a) := by
    exact (M.mem_shiftObj_piece_iff a (p + a) m).2 (by
      simpa only [add_sub_cancel_right] using hm)
  have hn' : n ∈ (N.shiftObj b).grading.piece (q + b) := by
    exact (N.mem_shiftObj_piece_iff b (q + b) n).2 (by
      simpa only [add_sub_cancel_right] using hn)
  rw [mem_shiftObj_piece_iff]
  simp only [unshiftPair, LinearMap.coe_mk, AddHom.coe_mk]
  have h := bimoduleTensorTmul_mem Γ Δ Θ (M.shiftObj a) (N.shiftObj b) hm' hn'
  have hdeg : p + a + (q + b) = p + q + (a + b) := by omega
  simpa only [hdeg, sub_neg_eq_add] using h

private def unshiftHom (a b : ℤ) :
    bimoduleTensorObj Γ Δ Θ M N ⟶
      (bimoduleTensorObj Γ Δ Θ (M.shiftObj a) (N.shiftObj b)).shiftObj (-(a + b)) :=
  bimoduleTensorLift Γ Δ Θ (unshiftPair Γ Δ Θ M N a b)
    (by
      intro x m n
      exact bimoduleTensorTmul_balance Γ Δ Θ (M.shiftObj a) (N.shiftObj b) x m n)
    (fun x m n ↦ by
      simp only [unshiftPair, LinearMap.coe_mk, AddHom.coe_mk,
        tmul_smul_bimoduleTensorTmul,
        ← Algebra.TensorProduct.one_def, one_smul])
    (fun x m n ↦ by
      simp only [unshiftPair, LinearMap.coe_mk, AddHom.coe_mk,
        tmul_smul_bimoduleTensorTmul,
        ← Algebra.TensorProduct.one_def, one_smul])
    (unshiftPair_degree Γ Δ Θ M N a b)

private theorem unshiftHom_tmul (a b : ℤ) (m : M) (n : N) :
    (unshiftHom Γ Δ Θ M N a b).hom (bimoduleTensorTmul Γ Δ Θ M N m n) =
      bimoduleTensorTmul Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m n := by
  rw [unshiftHom, bimoduleTensorLift_tmul (M := M) (N := N)
    (hdegree := unshiftPair_degree Γ Δ Θ M N a b)]
  rfl

private def shiftInv (a b : ℤ) :
    (bimoduleTensorObj Γ Δ Θ M N).shiftObj (a + b) ⟶
      bimoduleTensorObj Γ Δ Θ (M.shiftObj a) (N.shiftObj b) :=
  ofHom (unshiftHom Γ Δ Θ M N a b).hom
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [add_zero]
      have h := map_mem (unshiftHom Γ Δ Θ M N a b)
        ((mem_shiftObj_piece_iff _ _ _ _).1 hz)
      rw [mem_shiftObj_piece_iff, sub_neg_eq_add, sub_add_cancel] at h
      exact h)

/-- Internal shifts add under balanced tensor composition of graded bimodules. -/
def bimoduleTensorShiftIso (a b : ℤ) :
    bimoduleTensorObj Γ Δ Θ (M.shiftObj a) (N.shiftObj b) ≅
      (bimoduleTensorObj Γ Δ Θ M N).shiftObj (a + b) where
  hom := shiftHom Γ Δ Θ M N a b
  inv := shiftInv Γ Δ Θ M N a b
  hom_inv_id := by
    apply bimoduleTensor_hom_ext
    intro m n
    simp only [hom_comp, LinearMap.comp_apply, shiftInv, hom_id, LinearMap.id_apply]
    rw [shiftHom_tmul Γ Δ Θ M N a b, unshiftHom_tmul Γ Δ Θ M N a b]
  inv_hom_id := by
    apply hom_ext
    apply LinearMap.ext
    intro z
    induction z using bimoduleTensor_induction_on Γ Δ Θ M N with
    | ht m n =>
      simp only [hom_comp, LinearMap.comp_apply, shiftInv, hom_id, LinearMap.id_apply]
      rw [unshiftHom_tmul Γ Δ Θ M N a b, shiftHom_tmul Γ Δ Θ M N a b]
    | ha x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem bimoduleTensorShiftIso_hom_tmul (a b : ℤ) (m : M) (n : N) :
    (bimoduleTensorShiftIso Γ Δ Θ M N a b).hom.hom
        (bimoduleTensorTmul Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m n) =
      bimoduleTensorTmul Γ Δ Θ M N m n := shiftHom_tmul Γ Δ Θ M N a b m n

@[simp]
theorem bimoduleTensorShiftIso_inv_tmul (a b : ℤ) (m : M) (n : N) :
    (bimoduleTensorShiftIso Γ Δ Θ M N a b).inv.hom
        (bimoduleTensorTmul Γ Δ Θ M N m n) =
      bimoduleTensorTmul Γ Δ Θ (M.shiftObj a) (N.shiftObj b) m n :=
  unshiftHom_tmul Γ Δ Θ M N a b m n

/-- The tensor-shift comparison is natural in both graded bimodule maps. -/
@[reassoc]
theorem bimoduleTensorShiftIso_naturality
    {M' : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece}
    {N' : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece}
    (a b : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ Δ Θ (M := M.shiftObj a) (N := N.shiftObj b)
        (M' := M'.shiftObj a) (N' := N'.shiftObj b)
        ((shiftFunctor a).map f) ((shiftFunctor b).map g) ≫
        (bimoduleTensorShiftIso Γ Δ Θ M' N' a b).hom =
      (bimoduleTensorShiftIso Γ Δ Θ M N a b).hom ≫
        (shiftFunctor (a + b)).map (bimoduleTensorMap Γ Δ Θ f g) := by
  apply bimoduleTensor_hom_ext
  intro m n
  simp only [hom_comp, LinearMap.comp_apply, hom_shiftFunctor_map]
  rw [bimoduleTensorMap_tmul Γ Δ Θ (M := M.shiftObj a) (N := N.shiftObj b)
    (M' := M'.shiftObj a) (N' := N'.shiftObj b)
    ((shiftFunctor a).map f) ((shiftFunctor b).map g)]
  simp only [hom_shiftFunctor_map]
  rw [bimoduleTensorShiftIso_hom_tmul Γ Δ Θ M' N' a b,
    bimoduleTensorShiftIso_hom_tmul Γ Δ Θ M N a b, bimoduleTensorMap_tmul]

end TauCeti.GradedModuleCat
