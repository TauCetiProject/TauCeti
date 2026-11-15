/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Hamilton
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Character
public import TauCeti.RepresentationTheory.Induction.Mackey.Sufficient
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.CategoryTheory.Simple.Endomorphism
import TauCeti.RepresentationTheory.FDRep.Endomorphism
import TauCeti.CategoryTheory.Linear.Conj

/-!
# Real quaternion induction

The left quaternion representation of Q₈ is simple over ℝ. It is induced from the real
plane on which the rotation generator acts by multiplication by i. Its endomorphisms
are right quaternion multiplications, so its endomorphism algebra is the opposite
quaternion division algebra, rather than the scalar field.

This example distinguishes the arbitrary-field division-algebra criterion from the
splitting-field Mackey criterion: the nonidentity intertwining term need not vanish
for a simple induced representation over a nonsplitting field.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.4 and §13.2.
-/

public section

open CategoryTheory
open scoped Quaternion

namespace TauCeti

local notation "Q₈" => QuaternionGroup 2
local notation "C₄" => quaternionRotations 2

/-- The real representation of Q₈ on ℍ by left multiplication. -/
noncomputable def quaternionRealRepresentation : Representation ℝ Q₈ ℍ :=
  (Algebra.lmul ℝ ℍ).toMonoidHom.comp quaternionGroupTwoToQuaternion

/-- The quaternion representation acts by left multiplication. -/
@[simp]
theorem quaternionRealRepresentation_apply (g : Q₈) (v : ℍ) :
    quaternionRealRepresentation g v = quaternionGroupTwoToQuaternion g * v := (rfl)

private theorem quaternion_span (v : ℍ) :
    v = v.re • quaternionGroupTwoToQuaternion (.a 0) +
      v.imI • quaternionGroupTwoToQuaternion (.a 1) +
      v.imJ • quaternionGroupTwoToQuaternion (.xa 0) +
      v.imK • quaternionGroupTwoToQuaternion (.xa 3) := by
  ext <;> norm_num [-QuaternionGroup.a_zero, quaternionGroupTwoToQuaternion_a,
    quaternionGroupTwoToQuaternion_xa,
    Quaternion.coe_ofComplex, Quaternion.coeComplex, ZMod.val_add, ZMod.val_sub, ZMod.neg_val',
    ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_one_eq_one_mod,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem quaternion_subrep_mul_mem (S : Subrepresentation quaternionRealRepresentation)
    (v : ℍ) (hv : v ∈ S) (q : ℍ) : q * v ∈ S := by
  rw [quaternion_span q, add_mul, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
    smul_mul_assoc, smul_mul_assoc]
  exact S.toSubmodule.add_mem (S.toSubmodule.add_mem (S.toSubmodule.add_mem
    (S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (.a 0) hv))
    (S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (.a 1) hv)))
    (S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (.xa 0) hv)))
    (S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (.xa 3) hv))

/-- Left multiplication by Q₈ on ℍ is irreducible over ℝ. -/
instance quaternionRealRepresentation_isIrreducible :
    Representation.IsIrreducible quaternionRealRepresentation := by
  refine ⟨?_⟩
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp
      (fun h ↦ hS (Subrepresentation.toSubmodule_injective h))
    apply top_unique
    intro w _
    simpa [hv0] using quaternion_subrep_mul_mem S v hv (w * v⁻¹)

private theorem quaternion_intertwiner_apply
    (f : Representation.IntertwiningMap quaternionRealRepresentation quaternionRealRepresentation)
    (q : ℍ) : f q = q * f 1 := by
  have h (g : Q₈) : f (quaternionGroupTwoToQuaternion g) =
      quaternionGroupTwoToQuaternion g * f 1 := by
    simpa [ZMod.val_one_eq_one_mod] using Representation.IntertwiningMap.isIntertwining _ _ f g 1
  conv_lhs => rw [quaternion_span q]
  simp only [map_add, map_smul, h]
  rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc,
    ← add_mul, ← add_mul, ← add_mul, ← quaternion_span]

private noncomputable def quaternionRightMulHom : ℍᵐᵒᵖ →ₐ[ℝ]
    Representation.IntertwiningMap quaternionRealRepresentation quaternionRealRepresentation where
  toFun q := (LinearMap.mulRight ℝ q.unop).intertwiningMap_of_isIntertwiningMap
    _ _ (fun g v ↦ by simp [mul_assoc])
  map_one' := by ext x : 2; exact mul_one x
  map_mul' := by intro q r; ext x : 2; exact (mul_assoc x r.unop q.unop).symm
  map_zero' := by ext x : 2; exact mul_zero x
  map_add' := by intro q r; ext x : 2; exact mul_add x q.unop r.unop
  commutes' := by intro r; ext x : 2; exact Quaternion.mul_coe_eq_smul (R := ℝ) (a := x) (r := r)

/-- Right multiplication gives all real Q₈-equivariant endomorphisms of ℍ. The opposite
algebra records the reversal of multiplication under composition. -/
noncomputable def quaternionRealEndAlgEquiv : ℍᵐᵒᵖ ≃ₐ[ℝ]
    Representation.IntertwiningMap quaternionRealRepresentation quaternionRealRepresentation :=
  AlgEquiv.ofBijective quaternionRightMulHom
    ⟨fun q r h ↦ MulOpposite.unop_injective (by
        have he : (1 : ℍ) * q.unop = 1 * r.unop := congrArg (fun f ↦ f 1) h
        simpa only [one_mul] using he),
      fun f ↦ ⟨MulOpposite.op (f 1), by ext q : 2; exact (quaternion_intertwiner_apply f q).symm⟩⟩

/-- The endomorphism algebra equivalence sends an opposite quaternion to right multiplication. -/
@[simp]
theorem quaternionRealEndAlgEquiv_apply (q : ℍᵐᵒᵖ) (v : ℍ) :
    quaternionRealEndAlgEquiv q v = v * q.unop := (rfl)

/-- The inverse endomorphism comparison evaluates an intertwiner at one. -/
@[simp]
theorem quaternionRealEndAlgEquiv_symm_apply
    (f : Representation.IntertwiningMap quaternionRealRepresentation quaternionRealRepresentation) :
    quaternionRealEndAlgEquiv.symm f = MulOpposite.op (f 1) := by
  apply quaternionRealEndAlgEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  ext q : 2
  exact quaternion_intertwiner_apply f q

/-- The faithful rotation character of Q₈, regarded as a real two-dimensional representation. -/
noncomputable def quaternionRotationRealRepresentation : Representation ℝ C₄ ℂ :=
  (Algebra.lmul ℝ ℂ).toMonoidHom.comp
    ((Units.coeHom ℂ).comp quaternionGroupTwoRotationChar)

/-- The real rotation plane acts by the complex rotation character. -/
@[simp]
theorem quaternionRotationRealRepresentation_apply (g : C₄) (z : ℂ) :
    quaternionRotationRealRepresentation g z = (quaternionGroupTwoRotationChar g : ℂ) * z := (rfl)

private noncomputable def quaternionRotationInclusion :
    Rep.of quaternionRotationRealRepresentation ⟶
      Rep.res (quaternionRotations 2).subtype (Rep.of quaternionRealRepresentation) :=
  Rep.ofHom <| Quaternion.ofComplex.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
    rintro ⟨g, hg⟩ z
    obtain ⟨i, rfl⟩ := mem_quaternionRotations_iff.mp hg
    simp [quaternionRealRepresentation_apply, quaternionRotationRealRepresentation_apply,
      quaternionGroupTwoToQuaternion_a, coe_quaternionGroupTwoRotationChar_a,
      map_mul])

private noncomputable def quaternionIndHom :
    Rep.ind (quaternionRotations 2).subtype (Rep.of quaternionRotationRealRepresentation) ⟶
      Rep.of quaternionRealRepresentation :=
  (Rep.indResHomEquiv (quaternionRotations 2).subtype _ _).symm quaternionRotationInclusion

private theorem quaternionIndHom_mk (g : Q₈) (z : ℂ) :
    quaternionIndHom.hom (Representation.IndV.mk (quaternionRotations 2).subtype
      quaternionRotationRealRepresentation g z) =
        quaternionGroupTwoToQuaternion g⁻¹ * Quaternion.ofComplex z := by
  simp [quaternionIndHom, Rep.indResHomEquiv, quaternionRotationInclusion,
    quaternionRealRepresentation_apply]

/-- Induction of the real rotation plane is the left Hamilton quaternion representation.
In native coinvariant coordinates the comparison is `⟦g ⊗ z⟧ ↦ g⁻¹z`. -/
noncomputable def quaternionRealIndEquiv :
    (Representation.ind (quaternionRotations 2).subtype quaternionRotationRealRepresentation).Equiv
      quaternionRealRepresentation := by
  have hsurj : Function.Surjective quaternionIndHom.hom := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero quaternionIndHom.hom with h | h
    · exact h
    · have he := congrArg (fun f ↦ f (Representation.IndV.mk (quaternionRotations 2).subtype
          quaternionRotationRealRepresentation 1 1)) h
      rw [quaternionIndHom_mk] at he
      simp at he
  have hdim : Module.finrank ℝ (Rep.ind (quaternionRotations 2).subtype
      (Rep.of quaternionRotationRealRepresentation)) = Module.finrank ℝ ℍ := by
    rw [Rep.finrank_ind, index_quaternionRotations, Quaternion.finrank_eq_four]
    simp only [Rep.of, Complex.finrank_real_complex]
  exact .mk (LinearEquiv.ofBijective quaternionIndHom.hom.toLinearMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩)
    quaternionIndHom.hom.isIntertwining'

/-- The induction comparison on a coinvariant generator, with the inverse dictated by
Mathlib's right-translation model of induction. -/
@[simp]
theorem quaternionRealIndEquiv_mk (g : Q₈) (z : ℂ) :
    (dsimp% only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply]
      (quaternionRealIndEquiv (Representation.IndV.mk (quaternionRotations 2).subtype
        quaternionRotationRealRepresentation g z))) =
        quaternionGroupTwoToQuaternion g⁻¹ * Quaternion.ofComplex z :=
  quaternionIndHom_mk g z

/-- The quaternion induction comparison on native finite-dimensional representations. -/
noncomputable def quaternionRealIndIso :
    indFDRep (FDRep.of quaternionRotationRealRepresentation) ≅
      FDRep.of quaternionRealRepresentation :=
  let e := (indFDRepForgetEquiv (FDRep.of quaternionRotationRealRepresentation)).trans
    quaternionRealIndEquiv
  Action.mkIso e.toLinearEquiv.toFGModuleCatIso (fun g ↦
    FGModuleCat.hom_ext (LinearMap.ext (fun x ↦ LinearMap.congr_fun (e.isIntertwining' g) x)))

/-- The finite-dimensional induction isomorphism agrees with the coinvariant comparison. -/
@[simp]
theorem quaternionRealIndIso_hom_apply
    (x : indFDRep (FDRep.of quaternionRotationRealRepresentation)) :
    quaternionRealIndIso.hom.hom.hom.hom x =
      quaternionRealIndEquiv
        (indFDRepForgetEquiv (FDRep.of quaternionRotationRealRepresentation) x) := by
  unfold quaternionRealIndIso
  erw [Action.mkIso_hom_hom _ _, LinearEquiv.toFGModuleCatIso_hom]
  rfl

/-- The inverse finite-dimensional isomorphism agrees with the inverse coinvariant comparison. -/
@[simp]
theorem quaternionRealIndIso_inv_apply (q : ℍ) :
    quaternionRealIndIso.inv.hom.hom.hom q =
      (indFDRepForgetEquiv (FDRep.of quaternionRotationRealRepresentation)).symm
        (quaternionRealIndEquiv.symm q) := by
  unfold quaternionRealIndIso
  erw [Action.mkIso_inv_hom _ _, LinearEquiv.toFGModuleCatIso_inv]
  rfl

/-- The real quaternion representation is a simple finite-dimensional object. -/
instance quaternionReal_simple : Simple (FDRep.of quaternionRealRepresentation) :=
  (FDRep.simple_iff_isIrreducible _).mpr quaternionRealRepresentation_isIrreducible

/-- The real representation induced from the rotation plane of Q₈ is simple. -/
instance quaternionRealInd_simple :
    Simple (indFDRep (FDRep.of quaternionRotationRealRepresentation)) :=
  Simple.of_iso quaternionRealIndIso

/-- The native endomorphism algebra of the induced real representation is the opposite
Hamilton quaternion division algebra. -/
noncomputable def quaternionRealIndEndAlgEquiv :
    End (indFDRep (FDRep.of quaternionRotationRealRepresentation)) ≃ₐ[ℝ] ℍᵐᵒᵖ :=
  (quaternionRealIndIso.conjAlgEquiv ℝ).trans
    ((FDRep.of quaternionRealRepresentation).endIntertwiningAlgEquiv.trans
      quaternionRealEndAlgEquiv.symm)

/-- The induced endomorphism comparison evaluates the transported operator at one. -/
@[simp]
theorem quaternionRealIndEndAlgEquiv_apply
    (f : End (indFDRep (FDRep.of quaternionRotationRealRepresentation))) :
    quaternionRealIndEndAlgEquiv f =
      MulOpposite.op ((FDRep.isoToLinearEquiv quaternionRealIndIso)
        (f.asHom.hom.hom.hom ((FDRep.isoToLinearEquiv quaternionRealIndIso).symm 1))) := by
  unfold quaternionRealIndEndAlgEquiv
  erw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, quaternionRealEndAlgEquiv_symm_apply,
    FDRep.endIntertwiningAlgEquiv_apply]
  rw [Iso.conjAlgEquiv_apply, FDRep.Iso.conj_apply_asHom_apply]

/-- The induced simple representation has four real dimensions of endomorphisms. -/
theorem finrank_end_quaternionRealInd :
    Module.finrank ℝ (End (indFDRep (FDRep.of quaternionRotationRealRepresentation))) = 4 := by
  rw [quaternionRealIndEndAlgEquiv.toLinearEquiv.finrank_eq,
    ← (MulOpposite.opLinearEquiv ℝ (M := ℍ)).finrank_eq, Quaternion.finrank_eq_four]

/-- Complex conjugation identifies the real rotation plane with its conjugate by j. -/
noncomputable def quaternionRotationRealConjIso :
    FDRep.of quaternionRotationRealRepresentation ≅
      conjNormalFDRep (QuaternionGroup.xa 0) (FDRep.of quaternionRotationRealRepresentation) :=
  Action.mkIso Complex.conjAe.toLinearEquiv.toFGModuleCatIso (fun x ↦
    FGModuleCat.hom_ext (LinearMap.ext (fun z ↦ by
    -- The action-category commutation law is read on the underlying real-linear maps.
    change Complex.conjAe ((FDRep.of quaternionRotationRealRepresentation).ρ x z) =
      (conjNormalFDRep (QuaternionGroup.xa 0)
        (FDRep.of quaternionRotationRealRepresentation)).ρ x (Complex.conjAe z)
    rw [conjNormalFDRep_ρ]
    have hx : MulAut.conjNormal (QuaternionGroup.xa 0)⁻¹ x = x⁻¹ := by
      apply Subtype.ext
      exact (conj_eq_inv_of_notMem_quaternionRotations
        (s := (QuaternionGroup.xa 0)⁻¹)
        (by simpa only [inv_mem_iff] using xa_notMem_quaternionRotations (n := 2) 0)
        x.property).trans (by simp)
    rw [hx]
    obtain ⟨i, hi⟩ := mem_quaternionRotations_iff.mp x.property
    have hχ : star (quaternionGroupTwoRotationChar x : ℂ) =
        (quaternionGroupTwoRotationChar x : ℂ)⁻¹ := by
      rcases x with ⟨_, hx⟩
      subst hi
      rw [coe_quaternionGroupTwoRotationChar_a]
      have hc : ∀ i : ZMod (2 * 2), i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
      rcases hc i with rfl | rfl | rfl | rfl <;>
        norm_num [ZMod.val_ofNat, ZMod.val_one_eq_one_mod, Complex.inv_I]
    -- Unbundle the FDRep action and the real-linear conjugation equivalence; the constructor
    -- uses the bundled module's scalar instance, whereas the action formula uses ℝ's field.
    change star ((quaternionGroupTwoRotationChar x : ℂ) * z) =
      (quaternionGroupTwoRotationChar x⁻¹ : ℂ) * star z
    simp only [star_mul, map_inv, Units.val_inv_eq_inv_val, hχ, mul_comm])))

/-- The conjugation comparison acts by complex conjugation on the rotation plane. -/
@[simp]
theorem quaternionRotationRealConjIso_hom_apply (z : ℂ) :
    quaternionRotationRealConjIso.hom.hom.hom.hom z = star z := by
  unfold quaternionRotationRealConjIso
  erw [Action.mkIso_hom_hom _ _, LinearEquiv.toFGModuleCatIso_hom]
  rfl

/-- The inverse conjugation comparison is complex conjugation as well. -/
@[simp]
theorem quaternionRotationRealConjIso_inv_apply (z : ℂ) :
    quaternionRotationRealConjIso.inv.hom.hom.hom z = star z := by
  unfold quaternionRotationRealConjIso
  erw [Action.mkIso_inv_hom _ _, LinearEquiv.toFGModuleCatIso_inv]
  rfl

private theorem quaternion_rotation_intertwiner_apply
    (f : Representation.IntertwiningMap quaternionRotationRealRepresentation
      quaternionRotationRealRepresentation) (z : ℂ) : f z = z * f 1 := by
  have hI : f Complex.I = Complex.I * f 1 := by
    simpa [ZMod.val_one_eq_one_mod] using Representation.IntertwiningMap.isIntertwining _ _ f
      ⟨QuaternionGroup.a 1, a_mem_quaternionRotations 1⟩ 1
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using z.re_add_im.symm
  rw [hz, map_add, map_smul, map_smul, hI]
  simp only [Complex.real_smul, add_mul, mul_assoc, mul_one]

private noncomputable def quaternionRotationScalarHom : ℂ →ₐ[ℝ]
    Representation.IntertwiningMap quaternionRotationRealRepresentation
      quaternionRotationRealRepresentation where
  toFun z := (LinearMap.mulLeft ℝ z).intertwiningMap_of_isIntertwiningMap _ _
    (fun g v ↦ by simp [mul_left_comm])
  map_one' := by ext x : 2; exact one_mul x
  map_mul' := by intro z w; ext x : 2; exact mul_assoc z w x
  map_zero' := by ext x : 2; exact zero_mul x
  map_add' := by intro z w; ext x : 2; exact add_mul z w x
  commutes' := by intro r; ext x : 2; exact Complex.real_smul.symm

/-- The endomorphism algebra of the real rotation plane is ℂ, not ℝ. -/
noncomputable def quaternionRotationRealEndAlgEquiv :
    ℂ ≃ₐ[ℝ] End (FDRep.of quaternionRotationRealRepresentation) :=
  (AlgEquiv.ofBijective quaternionRotationScalarHom
    ⟨fun z w h ↦ by
        have he : z * (1 : ℂ) = w * 1 := congrArg (fun f ↦ f 1) h
        simpa only [mul_one] using he,
      fun f ↦ ⟨f 1, by
        ext z : 2
        exact (mul_comm _ _).trans (quaternion_rotation_intertwiner_apply f z).symm⟩⟩).trans
    (FDRep.of quaternionRotationRealRepresentation).endIntertwiningAlgEquiv.symm

/-- A complex scalar acts on the real rotation plane by multiplication. -/
@[simp]
theorem quaternionRotationRealEndAlgEquiv_apply (z w : ℂ) :
    (quaternionRotationRealEndAlgEquiv z).asHom.hom.hom.hom w = z * w := by
  erw [quaternionRotationRealEndAlgEquiv, AlgEquiv.trans_apply,
    FDRep.endIntertwiningAlgEquiv_symm_apply]
  rfl

/-- The inverse rotation-plane endomorphism comparison evaluates at one. -/
@[simp]
theorem quaternionRotationRealEndAlgEquiv_symm_apply
    (f : End (FDRep.of quaternionRotationRealRepresentation)) :
    quaternionRotationRealEndAlgEquiv.symm f = f.asHom.hom.hom.hom 1 := by
  obtain ⟨z, rfl⟩ := quaternionRotationRealEndAlgEquiv.surjective f
  rw [AlgEquiv.symm_apply_apply]
  exact ((quaternionRotationRealEndAlgEquiv_apply z 1).trans (mul_one z)).symm

/-- The identity Mackey term has real dimension two. -/
theorem finrank_end_quaternionRotationReal :
    Module.finrank ℝ (End (FDRep.of quaternionRotationRealRepresentation)) = 2 := by
  rw [← quaternionRotationRealEndAlgEquiv.toLinearEquiv.finrank_eq,
    Complex.finrank_real_complex]

/-- The nonidentity Mackey term also has real dimension two. -/
theorem finrank_hom_quaternionRotationReal_conj :
    Module.finrank ℝ (FDRep.of quaternionRotationRealRepresentation ⟶
      conjNormalFDRep (QuaternionGroup.xa 0)
        (FDRep.of quaternionRotationRealRepresentation)) = 2 := by
  rw [← (Linear.homCongr ℝ (Iso.refl _) quaternionRotationRealConjIso).finrank_eq,
    ← (End.linearEquiv (R := ℝ)).finrank_eq, finrank_end_quaternionRotationReal]

/-- The nonidentity Mackey term of the simple real quaternion induction does not vanish. -/
theorem not_mackeyDisjoint_quaternionRotationReal :
    ¬ MackeyDisjoint (FDRep.of quaternionRotationRealRepresentation) (QuaternionGroup.xa 0) := by
  rw [mackeyDisjoint_iff_finrank_eq_zero, finrank_hom_res_mackeyToH_of_normal,
    finrank_hom_quaternionRotationReal_conj]
  norm_num

/-- The rotation plane is simple over ℝ, with a two-dimensional division endomorphism algebra. -/
instance quaternionRotationReal_simple :
    Simple (FDRep.of quaternionRotationRealRepresentation) := by
  have : NeZero (Nat.card C₄ : ℝ) := ⟨by exact_mod_cast (Nat.card_pos (α := C₄)).ne'⟩
  exact simple_of_ringEquiv_end _ quaternionRotationRealEndAlgEquiv.toRingEquiv

/-- The scalar-Schur hypothesis fails for the real quaternion group, even though Maschke's
hypothesis holds. Its simple quaternion representation has endomorphism dimension four. -/
theorem not_scalarSchur_quaternionGroupTwo :
    ¬ ∀ W : FDRep ℝ Q₈, Simple W → Module.finrank ℝ (W ⟶ W) = 1 := by
  intro h
  have hdim := h (indFDRep (FDRep.of quaternionRotationRealRepresentation)) inferInstance
  have hfour := finrank_end_quaternionRealInd
  rw [(End.linearEquiv (R := ℝ)).finrank_eq] at hfour
  omega

end TauCeti
