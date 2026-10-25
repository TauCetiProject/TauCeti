/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.SelfTensor
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Shift

/-!
# Shifted self-tensor maps for graded inverse braid complexes

The diagonal corner has a vertex and a volume summand. After internal shift by −2,
these give Ui{−2} ⊞ Ui in either tensor order. Evaluation on the vertex insertion and
coevaluation followed by the volume projection give identity blocks. These maps are
the graded input to cancellation of the actual three-term inverse products. The proofs
use a cyclic generator of Ui, balanced tensor composition and the diagonal corner
calculation; no adjacency or nonzero coefficient hypothesis is needed.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "E" => Z ⊗[k] Zᵐᵒᵖ
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "F" => (GradedModuleCat.bimoduleTensor Γ Γ Γ :
  GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private def tensorShiftSecond (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) ((U i).shiftObj (-2)) ≅
      (GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i)).shiftObj (-2) := by
  let e : GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) ((U i).shiftObj (-2)) ≅
      GradedModuleCat.bimoduleTensorObj Γ Γ Γ ((U i).shiftObj 0) ((U i).shiftObj (-2)) :=
    ((F).flip.obj ((U i).shiftObj (-2))).mapIso
      ((GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i)).symm
  exact e ≪≫ (by simpa only [zero_add] using
    GradedModuleCat.bimoduleTensorShiftIso Γ Γ Γ (U i) (U i) 0 (-2))

private theorem tensorShiftSecond_hom_tmul (i : V) (m n : U i) :
    (tensorShiftSecond k G i).hom.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) m n) =
        GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n := by
  -- Expose the two constructed maps before applying their public pure-tensor formulas.
  change (GradedModuleCat.bimoduleTensorShiftIso Γ Γ Γ (U i) (U i) 0 (-2)).hom.hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (M := U i) (N := (U i).shiftObj (-2))
      (M' := (U i).shiftObj 0) (N' := (U i).shiftObj (-2))
      ((GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i)).inv
      (𝟙 ((U i).shiftObj (-2)))).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) m n)) = _
  rw [GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
    (M := U i) (N := (U i).shiftObj (-2))
    (M' := (U i).shiftObj 0) (N' := (U i).shiftObj (-2))]
  simp only [Iso.app_inv, GradedModuleCat.hom_shiftFunctorZeroIso_inv_app,
    GradedModuleCat.hom_id, LinearMap.id_apply]
  exact GradedModuleCat.bimoduleTensorShiftIso_hom_tmul Γ Γ Γ (U i) (U i) 0 (-2) m n

private def shiftTwoMinusTwoIso (i : V) : ((U i).shiftObj 2).shiftObj (-2) ≅ U i :=
  (GradedModuleCat.shiftFunctorAddIso (zigzagEnvelopingGrading k G).piece 2 (-2)).app (U i) ≪≫
    (by simpa only [show (2 : ℤ) + (-2) = 0 by decide,
      GradedModuleCat.shiftFunctor_obj, Functor.id_obj] using
      (GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i))

private theorem shiftTwoMinusTwoIso_hom (i : V) :
    (shiftTwoMinusTwoIso k G i).hom.hom = LinearMap.id := by
  simp [shiftTwoMinusTwoIso]

/-- The internally shifted right self-tensor decomposes as Ui{−2} ⊞ Ui. -/
def zigzagBraidSelfTensorShiftRightIso (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) ((U i).shiftObj (-2)) ≅
      (U i).shiftObj (-2) ⊞ U i := by
  let S := GradedModuleCat.shiftFunctor (𝒜 := (zigzagEnvelopingGrading k G).piece) (-2)
  haveI : PreservesBinaryBiproduct (U i) ((U i).shiftObj 2) S :=
    preservesBinaryBiproduct_of_preservesBiproduct S (U i) ((U i).shiftObj 2)
  exact tensorShiftSecond k G i ≪≫ (S).mapIso (zigzagBraidSelfTensorIso k G i) ≪≫
    (S).mapBiprod (U i) ((U i).shiftObj 2) ≪≫
      biprod.mapIso (Iso.refl _) (shiftTwoMinusTwoIso k G i)

/-- The right shifted volume projection agrees with the unshifted self-tensor projection. -/
theorem zigzagBraidSelfTensorShiftRightIso_snd_tmul (i : V) (m n : U i) :
    ((zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) m n) =
    ((zigzagBraidSelfTensorIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n) := by
  simp only [zigzagBraidSelfTensorShiftRightIso, Iso.trans_hom, Category.assoc, biprod.mapIso_hom,
    biprod.map_snd, Functor.mapBiprod_hom, biprod.lift_snd_assoc, Functor.mapIso_hom,
    GradedModuleCat.hom_comp, LinearMap.comp_apply, shiftTwoMinusTwoIso_hom,
    GradedModuleCat.hom_shiftFunctor_map, LinearMap.id_apply]
  rw [tensorShiftSecond_hom_tmul]

private def vertexGenerator (i : V) : zigzagBraidBimodule k G i :=
  (zigzagBraidBimoduleFactorsEquiv k G i).symm
    (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)) ⊗ₜ[k]
      spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))

private theorem coe_vertexGenerator (i : V) :
    ((vertexGenerator k G i : zigzagBraidBimodule k G i) : E) =
      zigzagAlgebraBasis k G (.inl i) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inl i)) := by
  simp only [vertexGenerator, coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul,
    coe_spanSingletonGenerator]

-- The vertex bimodule inherits its action from the regular enveloping-algebra module:
-- including a scalar multiple in the left ideal gives multiplication in that algebra.
private theorem coe_vertex_smul (i : V) (a : E) (x : zigzagBraidBimodule k G i) :
    ((a • x : zigzagBraidBimodule k G i) : E) = a * (x : E) := by
  rw [Submodule.coe_smul, smul_eq_mul]

private theorem generator_left_vertex (i : V) :
    ((zigzagAlgebraBasis k G (.inl i) ⊗ₜ[k] (1 : Zᵐᵒᵖ)) : E) •
      (vertexGenerator k G i : U i) = (vertexGenerator k G i : U i) := by
  apply Subtype.ext
  rw [coe_vertex_smul, coe_vertexGenerator]
  simp [Algebra.TensorProduct.tmul_mul_tmul,
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i).eq]

private theorem vertex_linearMap_ext (i : V)
    {M : Type*} [AddCommGroup M] [Module E M]
    {f g : zigzagBraidBimodule k G i →ₗ[E] M}
    (h : f (vertexGenerator k G i) = g (vertexGenerator k G i)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : (x : E) • vertexGenerator k G i = x := by
    apply Subtype.ext
    rw [coe_vertex_smul, coe_vertexGenerator]
    exact mem_zigzagBraidBimodule_iff.mp x.property
  calc
    f x = f ((x : E) • vertexGenerator k G i) := congrArg f hx.symm
    _ = (x : E) • f (vertexGenerator k G i) := f.map_smul _ _
    _ = (x : E) • g (vertexGenerator k G i) := congrArg ((x : E) • ·) h
    _ = g ((x : E) • vertexGenerator k G i) := (g.map_smul _ _).symm
    _ = g x := congrArg g hx

private theorem eval_vertexGenerator (i : V) :
    zigzagBraidEvaluation k G i (vertexGenerator k G i) =
      Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i)) := by
  rw [zigzagBraidEvaluation_apply, coe_vertexGenerator]
  simp [Bimodule.smul_of, (isIdempotentElem_zigzagAlgebraBasis_inl k G i).eq]

private def leftVolume (i : V) : zigzagBraidBimodule k G i :=
  (zigzagAlgebraBasis k G (.inr (.inr i)) ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • vertexGenerator k G i

private def rightVolume (i : V) : zigzagBraidBimodule k G i :=
  ((1 : Z) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inr (.inr i)))) • vertexGenerator k G i

private theorem coevaluation_vertex (i : V) :
    zigzagBraidCoevaluation k G i (Bimodule.of (AlgHom.id k Z)
      (zigzagAlgebraBasis k G (.inl i))) = rightVolume k G i + leftVolume k G i := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have ha : ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = i),
      (zigzagAlgebraBasis k G (.inl i) * zigzagAlgebraBasis k G (.inr (.inl d))) ⊗ₜ[k]
        op (zigzagAlgebraBasis k G (.inr (.inl d.symm))) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hd' : d.fst = i := (Finset.mem_filter.mp hd).2
    have hi : i ≠ d.snd := by simpa only [← hd'] using d.fst_ne_snd
    simp [hi]
  apply Subtype.ext
  rw [Submodule.coe_add, rightVolume, leftVolume, coe_vertex_smul, coe_vertex_smul]
  rw [coe_zigzagBraidCoevaluation_of, ha, coe_vertexGenerator]
  simp [Algebra.TensorProduct.tmul_mul_tmul, ← op_mul]

private abbrev selfVolumeProjection (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i) →ₗ[E] (U i).shiftObj 2 :=
  ((zigzagBraidSelfTensorIso k G i).hom ≫ biprod.snd).hom

private theorem selfVolumeProjection_inl (i : V) (m : U i) :
    selfVolumeProjection k G i ((zigzagBraidSelfTensorInl k G i).hom m) = 0 := by
  have h : zigzagBraidSelfTensorInl k G i ≫
      (zigzagBraidSelfTensorIso k G i).hom ≫ biprod.snd = 0 := by simp
  have hp := LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom h) m
  simpa only [selfVolumeProjection, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.hom_zero, LinearMap.zero_apply] using hp

private theorem selfVolumeProjection_inr (i : V) (m : (U i).shiftObj 2) :
    selfVolumeProjection k G i ((zigzagBraidSelfTensorInr k G i).hom m) = m := by
  have h : zigzagBraidSelfTensorInr k G i ≫
      (zigzagBraidSelfTensorIso k G i).hom ≫ biprod.snd = 𝟙 _ := by simp
  have hp := LinearMap.congr_fun (congrArg GradedModuleCat.Hom.hom h) m
  simpa only [selfVolumeProjection, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.hom_id, LinearMap.id_apply] using hp

private theorem rightVolume_factors (i : V) :
    rightVolume k G i = (zigzagBraidBimoduleFactorsEquiv k G i).symm
      (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)) ⊗ₜ[k]
        (op (zigzagAlgebraBasis k G (.inr (.inr i))) •
          spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))) := by
  apply Subtype.ext
  rw [rightVolume, coe_vertex_smul, coe_vertexGenerator,
    coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem leftVolume_factors (i : V) :
    leftVolume k G i = (zigzagBraidBimoduleFactorsEquiv k G i).symm
      ((zigzagAlgebraBasis k G (.inr (.inr i)) •
        spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i))) ⊗ₜ[k]
        spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i)))) := by
  apply Subtype.ext
  rw [leftVolume, coe_vertex_smul, coe_vertexGenerator,
    coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem selfVolumeProjection_rightVolume (i : V) :
    selfVolumeProjection k G i (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
      (vertexGenerator k G i) (rightVolume k G i)) = 0 := by
  let g : U i := vertexGenerator k G i
  let w : U i := rightVolume k G i
  change selfVolumeProjection k G i
    (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) g w) = 0
  have h := zigzagBraidSelfTensorInl_hom_factors k G i
    (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)))
    (op (zigzagAlgebraBasis k G (.inr (.inr i))) •
      spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))
  have hw : w = (zigzagBraidBimoduleFactorsEquiv k G i).symm
    (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)) ⊗ₜ[k]
      (op (zigzagAlgebraBasis k G (.inr (.inr i))) •
        spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))) :=
    rightVolume_factors k G i
  rw [← hw] at h
  change (zigzagBraidSelfTensorInl k G i).hom w =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) g w at h
  rw [← h]
  exact selfVolumeProjection_inl k G i _

private theorem selfVolumeProjection_leftVolume (i : V) :
    selfVolumeProjection k G i (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
      (vertexGenerator k G i) (leftVolume k G i)) = vertexGenerator k G i := by
  let g : U i := vertexGenerator k G i
  let g2 : (U i).shiftObj 2 := vertexGenerator k G i
  let w : U i := leftVolume k G i
  change selfVolumeProjection k G i
    (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) g w) = g2
  have h := zigzagBraidSelfTensorInr_hom_factors k G i
    (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)))
    (spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))
  have hw : w = (zigzagBraidBimoduleFactorsEquiv k G i).symm
    ((zigzagAlgebraBasis k G (.inr (.inr i)) •
      spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i))) ⊗ₜ[k]
      spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i)))) :=
    leftVolume_factors k G i
  rw [← hw] at h
  change (zigzagBraidSelfTensorInr k G i).hom g2 =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) g w at h
  rw [← h]
  exact selfVolumeProjection_inr k G i _

private theorem generator_right_vertex (i : V) :
    (((1 : Z) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inl i))) : E) •
      (vertexGenerator k G i : U i) = (vertexGenerator k G i : U i) := by
  apply Subtype.ext
  rw [coe_vertex_smul, coe_vertexGenerator]
  simp [Algebra.TensorProduct.tmul_mul_tmul, ← op_mul,
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i).eq]

private theorem coevaluation_tensor_generator (i : V) :
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2))
      (vertexGenerator k G i)
      ((zigzagBraidCoevaluationHom k G i).hom (Bimodule.of (AlgHom.id k Z) 1)) =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2))
      (vertexGenerator k G i) (rightVolume k G i + leftVolume k G i) := by
  let g : U i := vertexGenerator k G i
  let z1 : zigzagGradedBimodule k G := Bimodule.of (AlgHom.id k Z) 1
  let ze : zigzagGradedBimodule k G :=
    Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i))
  let c1 : (U i).shiftObj (-2) := (zigzagBraidCoevaluationHom k G i).hom z1
  have hz : (zigzagAlgebraBasis k G (.inl i) ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • z1 = ze := by
    -- Select the regular bimodule action before applying its public action formula.
    change (zigzagAlgebraBasis k G (.inl i) ⊗ₜ[k] (1 : Zᵐᵒᵖ)) •
      (Bimodule.of (AlgHom.id k Z) 1 : Bimodule (AlgHom.id k Z)) =
        Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i))
    rw [Bimodule.smul_of, AlgHom.id_apply, unop_one, mul_one, mul_one]
  have hscalar : (zigzagAlgebraBasis k G (.inl i) ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • c1 =
      (zigzagBraidCoevaluationHom k G i).hom ze := by
    exact ((zigzagBraidCoevaluationHom k G i).hom.map_smul _ z1).symm.trans
      (congrArg (zigzagBraidCoevaluationHom k G i).hom hz)
  have hcut : (zigzagBraidCoevaluationHom k G i).hom ze =
      (rightVolume k G i + leftVolume k G i : (U i).shiftObj (-2)) :=
    (LinearMap.congr_fun (hom_zigzagBraidCoevaluationHom (k := k) (G := G) i) ze).trans
      (coevaluation_vertex k G i)
  have h := GradedModuleCat.bimoduleTensorTmul_balance Γ Γ Γ (U i) ((U i).shiftObj (-2))
    (zigzagAlgebraBasis k G (.inl i)) g c1
  have hg : ((1 : Z) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inl i))) • g = g :=
    generator_right_vertex k G i
  rw [hg, hscalar, hcut] at h
  exact h

private theorem coevaluation_identity_block (i : V) :
    (zigzagBimoduleRightUnitor k G (U i)).inv ≫
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i)) (zigzagBraidCoevaluationHom k G i) ≫
        (zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd = 𝟙 (U i) := by
  let g : U i := vertexGenerator k G i
  let z1 : zigzagGradedBimodule k G := Bimodule.of (AlgHom.id k Z) 1
  apply GradedModuleCat.hom_ext
  apply vertex_linearMap_ext k G i
  -- Expand only the constructed composite at the graded cyclic generator.
  change ((zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd).hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidCoevaluationHom k G i)).hom
      ((zigzagBimoduleRightUnitor k G (U i)).inv.hom g)) = g
  rw [zigzagBimoduleRightUnitor_inv_apply]
  -- Keep the regular-unit vector typed in the graded carrier for the tensor-map formula.
  change ((zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd).hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidCoevaluationHom k G i)).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (zigzagGradedBimodule k G) g z1)) = g
  rw [GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (M := U i) (N := zigzagGradedBimodule k G)
      (M' := U i) (N' := (U i).shiftObj (-2)),
    GradedModuleCat.hom_id, LinearMap.id_apply]
  have ht : GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g
      ((zigzagBraidCoevaluationHom k G i).hom z1) =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g
      (rightVolume k G i + leftVolume k G i) := coevaluation_tensor_generator k G i
  rw [ht]
  let r : (U i).shiftObj (-2) := rightVolume k G i
  let l : (U i).shiftObj (-2) := leftVolume k G i
  -- The two volume vectors have now entered the internally shifted graded carrier.
  change ((zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd).hom
    (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g (r + l)) = g
  rw [GradedModuleCat.bimoduleTensorTmul_add_right, map_add]
  have hr : ((zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g r) = 0 :=
    (zigzagBraidSelfTensorShiftRightIso_snd_tmul k G i g (rightVolume k G i : U i)).trans
      (selfVolumeProjection_rightVolume k G i)
  have hl : ((zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g l) = g :=
    (zigzagBraidSelfTensorShiftRightIso_snd_tmul k G i g (leftVolume k G i : U i)).trans
      (selfVolumeProjection_leftVolume k G i)
  exact (congrArg₂ (· + ·) hr hl).trans (zero_add _)

private theorem tensorShiftSecond_inv_tmul (i : V) (m n : U i) :
    (tensorShiftSecond k G i).inv.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n) =
        GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) m n := by
  -- Expand the constructed inverse to its two maps; each has a public pure-tensor equation.
  change (GradedModuleCat.bimoduleTensorMap Γ Γ Γ
    (M := (U i).shiftObj 0) (N := (U i).shiftObj (-2))
    (M' := U i) (N' := (U i).shiftObj (-2))
    ((GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i)).hom
    (𝟙 ((U i).shiftObj (-2)))).hom
    ((GradedModuleCat.bimoduleTensorShiftIso Γ Γ Γ (U i) (U i) 0 (-2)).inv.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n)) = _
  rw [GradedModuleCat.bimoduleTensorShiftIso_inv_tmul,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (M := (U i).shiftObj 0) (N := (U i).shiftObj (-2))
      (M' := U i) (N' := (U i).shiftObj (-2))]
  simp only [Iso.app_hom, GradedModuleCat.hom_shiftFunctorZeroIso_hom_app,
    GradedModuleCat.hom_id, LinearMap.id_apply]

/-- The shifted degree-zero insertion into Ui tensor_Z Ui{−2}. -/
def zigzagBraidSelfTensorShiftRightInl (i : V) :
    (U i).shiftObj (-2) ⟶ GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) ((U i).shiftObj (-2)) :=
  (GradedModuleCat.shiftFunctor (𝒜 := (zigzagEnvelopingGrading k G).piece) (-2)).map
      (zigzagBraidSelfTensorInl k G i) ≫ (tensorShiftSecond k G i).inv

private theorem shiftedSelfInl_generator (i : V) :
    (zigzagBraidSelfTensorShiftRightInl k G i).hom (vertexGenerator k G i) =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2))
      (vertexGenerator k G i) (vertexGenerator k G i) := by
  let g : U i := vertexGenerator k G i
  let gs : (U i).shiftObj (-2) := vertexGenerator k G i
  have hinsert : (zigzagBraidSelfTensorInl k G i).hom g =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) g g :=
    zigzagBraidSelfTensorInl_hom_factors k G i
      (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)))
      (spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))
  simp only [zigzagBraidSelfTensorShiftRightInl, GradedModuleCat.hom_comp,
    GradedModuleCat.hom_shiftFunctor_map]
  -- Type the same cyclic vector in the unshifted carrier of the insertion formula.
  change (tensorShiftSecond k G i).inv.hom ((zigzagBraidSelfTensorInl k G i).hom g) =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g gs
  rw [hinsert]
  exact tensorShiftSecond_inv_tmul k G i g g

/-- Left evaluation on the shifted right insertion is the identity. -/
@[reassoc]
theorem zigzagBraidSelfTensorShiftRightInl_evaluation (i : V) :
    zigzagBraidSelfTensorShiftRightInl k G i ≫ GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (zigzagBraidEvaluationHom k G i) (𝟙 ((U i).shiftObj (-2))) ≫
        (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom =
      𝟙 ((U i).shiftObj (-2)) := by
  let g : U i := vertexGenerator k G i
  let gs : (U i).shiftObj (-2) := vertexGenerator k G i
  let z : zigzagGradedBimodule k G :=
    Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i))
  have heval : (zigzagBraidEvaluationHom k G i).hom g = z :=
    (LinearMap.congr_fun (hom_zigzagBraidEvaluationHom (k := k) (G := G) i) g).trans
      (eval_vertexGenerator k G i)
  have hinsert : (zigzagBraidSelfTensorShiftRightInl k G i).hom gs =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) ((U i).shiftObj (-2)) g gs :=
    shiftedSelfInl_generator k G i
  have hscalar : ((Bimodule.of (AlgHom.id k Z)).symm z ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • gs = gs := by
    have hz : (Bimodule.of (AlgHom.id k Z)).symm z = zigzagAlgebraBasis k G (.inl i) :=
      LinearEquiv.symm_apply_apply _ _
    rw [hz]
    -- An internal shift preserves the vertex ideal's carrier and enveloping action.
    exact generator_left_vertex k G i
  apply GradedModuleCat.hom_ext
  apply vertex_linearMap_ext k G i
  -- Evaluate the composite at the cyclic generator in its internally shifted carrier.
  change (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom.hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (zigzagBraidEvaluationHom k G i) (𝟙 ((U i).shiftObj (-2)))).hom
      ((zigzagBraidSelfTensorShiftRightInl k G i).hom gs)) = gs
  rw [hinsert, GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
    (M := U i) (N := (U i).shiftObj (-2))
    (M' := zigzagGradedBimodule k G) (N' := (U i).shiftObj (-2)),
    heval, GradedModuleCat.hom_id, LinearMap.id_apply]
  exact (zigzagBimoduleLeftUnitor_hom_tmul k G ((U i).shiftObj (-2)) z gs).trans hscalar

private def tensorShiftFirst (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ ((U i).shiftObj (-2)) (U i) ≅
      (GradedModuleCat.bimoduleTensorObj Γ Γ Γ (U i) (U i)).shiftObj (-2) := by
  let e : GradedModuleCat.bimoduleTensorObj Γ Γ Γ ((U i).shiftObj (-2)) (U i) ≅
      GradedModuleCat.bimoduleTensorObj Γ Γ Γ ((U i).shiftObj (-2)) ((U i).shiftObj 0) :=
    ((F).obj ((U i).shiftObj (-2))).mapIso
      ((GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i)).symm
  exact e ≪≫ (by simpa only [add_zero] using
    GradedModuleCat.bimoduleTensorShiftIso Γ Γ Γ (U i) (U i) (-2) 0)

private theorem tensorShiftFirst_hom_tmul (i : V) (m n : U i) :
    (tensorShiftFirst k G i).hom.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) m n) =
        GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n := by
  -- Compute the two maps defining the first-factor shift comparison.
  change (GradedModuleCat.bimoduleTensorShiftIso Γ Γ Γ (U i) (U i) (-2) 0).hom.hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (M := (U i).shiftObj (-2)) (N := U i)
      (M' := (U i).shiftObj (-2)) (N' := (U i).shiftObj 0)
      (𝟙 ((U i).shiftObj (-2)))
      ((GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i)).inv).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) m n)) = _
  rw [GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
    (M := (U i).shiftObj (-2)) (N := U i)
    (M' := (U i).shiftObj (-2)) (N' := (U i).shiftObj 0)]
  simp only [Iso.app_inv, GradedModuleCat.hom_shiftFunctorZeroIso_inv_app,
    GradedModuleCat.hom_id, LinearMap.id_apply]
  exact GradedModuleCat.bimoduleTensorShiftIso_hom_tmul Γ Γ Γ (U i) (U i) (-2) 0 m n

/-- The internally shifted left self-tensor decomposes as Ui{−2} ⊞ Ui. -/
def zigzagBraidSelfTensorShiftLeftIso (i : V) :
    GradedModuleCat.bimoduleTensorObj Γ Γ Γ ((U i).shiftObj (-2)) (U i) ≅
      (U i).shiftObj (-2) ⊞ U i := by
  let S := GradedModuleCat.shiftFunctor (𝒜 := (zigzagEnvelopingGrading k G).piece) (-2)
  have : PreservesBinaryBiproduct (U i) ((U i).shiftObj 2) S :=
    preservesBinaryBiproduct_of_preservesBiproduct S (U i) ((U i).shiftObj 2)
  exact tensorShiftFirst k G i ≪≫ (S).mapIso (zigzagBraidSelfTensorIso k G i) ≪≫
    (S).mapBiprod (U i) ((U i).shiftObj 2) ≪≫
      biprod.mapIso (Iso.refl _) (shiftTwoMinusTwoIso k G i)

/-- The left shifted volume projection agrees with the unshifted self-tensor projection. -/
theorem zigzagBraidSelfTensorShiftLeftIso_snd_tmul (i : V) (m n : U i) :
    ((zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) m n) =
    ((zigzagBraidSelfTensorIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n) := by
  simp only [zigzagBraidSelfTensorShiftLeftIso, Iso.trans_hom, Category.assoc, biprod.mapIso_hom,
    biprod.map_snd, Functor.mapBiprod_hom, biprod.lift_snd_assoc, Functor.mapIso_hom,
    GradedModuleCat.hom_comp, LinearMap.comp_apply, shiftTwoMinusTwoIso_hom,
    GradedModuleCat.hom_shiftFunctor_map, LinearMap.id_apply]
  rw [tensorShiftFirst_hom_tmul]

private theorem selfVolumeProjection_leftVolume_first (i : V) :
    selfVolumeProjection k G i (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
      (leftVolume k G i) (vertexGenerator k G i)) = 0 := by
  let g : U i := vertexGenerator k G i
  let w : U i := leftVolume k G i
  change selfVolumeProjection k G i
    (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) w g) = 0
  have h := zigzagBraidSelfTensorInl_hom_factors k G i
    (zigzagAlgebraBasis k G (.inr (.inr i)) •
      spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)))
    (spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))
  have hw : w = (zigzagBraidBimoduleFactorsEquiv k G i).symm
    ((zigzagAlgebraBasis k G (.inr (.inr i)) •
      spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i))) ⊗ₜ[k]
      spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i)))) :=
    leftVolume_factors k G i
  rw [← hw] at h
  change (zigzagBraidSelfTensorInl k G i).hom w =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) w g at h
  rw [← h]
  exact selfVolumeProjection_inl k G i _

private theorem selfVolumeProjection_rightVolume_first (i : V) :
    selfVolumeProjection k G i (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i)
      (rightVolume k G i) (vertexGenerator k G i)) = vertexGenerator k G i := by
  have h := GradedModuleCat.bimoduleTensorTmul_balance Γ Γ Γ (U i) (U i)
    (zigzagAlgebraBasis k G (.inr (.inr i)))
    (vertexGenerator k G i) (vertexGenerator k G i)
  exact (congrArg (selfVolumeProjection k G i) h).trans
    (selfVolumeProjection_leftVolume k G i)

private theorem coevaluation_tensor_generator_first (i : V) :
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i)
      ((zigzagBraidCoevaluationHom k G i).hom (Bimodule.of (AlgHom.id k Z) 1))
      (vertexGenerator k G i) =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i)
      (rightVolume k G i + leftVolume k G i) (vertexGenerator k G i) := by
  let g : U i := vertexGenerator k G i
  let z1 : zigzagGradedBimodule k G := Bimodule.of (AlgHom.id k Z) 1
  let ze : zigzagGradedBimodule k G :=
    Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i))
  let c1 : (U i).shiftObj (-2) := (zigzagBraidCoevaluationHom k G i).hom z1
  have hz : ((1 : Z) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inl i))) • z1 = ze := by
    -- Select the regular bimodule carrier for the right vertex action.
    change ((1 : Z) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inl i))) •
      (Bimodule.of (AlgHom.id k Z) 1 : Bimodule (AlgHom.id k Z)) =
        Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i))
    rw [Bimodule.smul_of, AlgHom.id_apply, unop_op, one_mul, one_mul]
  have hscalar : ((1 : Z) ⊗ₜ[k] op (zigzagAlgebraBasis k G (.inl i))) • c1 =
      (zigzagBraidCoevaluationHom k G i).hom ze := by
    exact ((zigzagBraidCoevaluationHom k G i).hom.map_smul _ z1).symm.trans
      (congrArg (zigzagBraidCoevaluationHom k G i).hom hz)
  have hcut : (zigzagBraidCoevaluationHom k G i).hom ze =
      (rightVolume k G i + leftVolume k G i : (U i).shiftObj (-2)) :=
    (LinearMap.congr_fun (hom_zigzagBraidCoevaluationHom (k := k) (G := G) i) ze).trans
      (coevaluation_vertex k G i)
  have h := GradedModuleCat.bimoduleTensorTmul_balance Γ Γ Γ ((U i).shiftObj (-2)) (U i)
    (zigzagAlgebraBasis k G (.inl i)) c1 g
  have hg : (zigzagAlgebraBasis k G (.inl i) ⊗ₜ[k] (1 : Zᵐᵒᵖ)) • g = g :=
    generator_left_vertex k G i
  rw [hg, hscalar, hcut] at h
  exact h.symm

private theorem coevaluation_first_identity_block (i : V) :
    (zigzagBimoduleLeftUnitor k G (U i)).inv ≫
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidCoevaluationHom k G i) (𝟙 (U i)) ≫
        (zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd = 𝟙 (U i) := by
  let g : U i := vertexGenerator k G i
  let z1 : zigzagGradedBimodule k G := Bimodule.of (AlgHom.id k Z) 1
  apply GradedModuleCat.hom_ext
  apply vertex_linearMap_ext k G i
  -- Evaluate the tensor composite on the cyclic generator in its graded carrier.
  change ((zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd).hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (zigzagBraidCoevaluationHom k G i) (𝟙 (U i))).hom
      ((zigzagBimoduleLeftUnitor k G (U i)).inv.hom g)) = g
  rw [zigzagBimoduleLeftUnitor_inv_apply]
  -- Keep the regular unit typed in the graded carrier when computing its tensor map.
  change ((zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd).hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (zigzagBraidCoevaluationHom k G i) (𝟙 (U i))).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (zigzagGradedBimodule k G) (U i) z1 g)) = g
  rw [GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (M := zigzagGradedBimodule k G) (N := U i)
      (M' := (U i).shiftObj (-2)) (N' := U i),
    GradedModuleCat.hom_id, LinearMap.id_apply]
  have ht : GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i)
      ((zigzagBraidCoevaluationHom k G i).hom z1) g =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i)
      (rightVolume k G i + leftVolume k G i) g := coevaluation_tensor_generator_first k G i
  rw [ht]
  let r : (U i).shiftObj (-2) := rightVolume k G i
  let l : (U i).shiftObj (-2) := leftVolume k G i
  -- Both volume vectors now belong to the internally shifted first tensor factor.
  change ((zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd).hom
    (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) (r + l) g) = g
  rw [GradedModuleCat.bimoduleTensorTmul_add_left, map_add]
  have hr : ((zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) r g) = g :=
    (zigzagBraidSelfTensorShiftLeftIso_snd_tmul k G i (rightVolume k G i : U i) g).trans
      (selfVolumeProjection_rightVolume_first k G i)
  have hl : ((zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) l g) = 0 :=
    (zigzagBraidSelfTensorShiftLeftIso_snd_tmul k G i (leftVolume k G i : U i) g).trans
      (selfVolumeProjection_leftVolume_first k G i)
  exact (congrArg₂ (· + ·) hr hl).trans (add_zero _)

private theorem tensorShiftFirst_inv_tmul (i : V) (m n : U i) :
    (tensorShiftFirst k G i).inv.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n) =
        GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) m n := by
  -- Undo the generic shift comparison, then undo the zero shift in the second factor.
  change (GradedModuleCat.bimoduleTensorMap Γ Γ Γ
    (M := (U i).shiftObj (-2)) (N := (U i).shiftObj 0)
    (M' := (U i).shiftObj (-2)) (N' := U i)
    (𝟙 ((U i).shiftObj (-2)))
    ((GradedModuleCat.shiftFunctorZeroIso (zigzagEnvelopingGrading k G).piece).app (U i)).hom).hom
    ((GradedModuleCat.bimoduleTensorShiftIso Γ Γ Γ (U i) (U i) (-2) 0).inv.hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) m n)) = _
  rw [GradedModuleCat.bimoduleTensorShiftIso_inv_tmul Γ Γ Γ (U i) (U i) (-2) 0 m n,
    GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
      (M := (U i).shiftObj (-2)) (N := (U i).shiftObj 0)
      (M' := (U i).shiftObj (-2)) (N' := U i)]
  simp only [Iso.app_hom, GradedModuleCat.hom_shiftFunctorZeroIso_hom_app,
    GradedModuleCat.hom_id, LinearMap.id_apply]

/-- The shifted degree-zero insertion into Ui{−2} tensor_Z Ui. -/
def zigzagBraidSelfTensorShiftLeftInl (i : V) :
    (U i).shiftObj (-2) ⟶ GradedModuleCat.bimoduleTensorObj Γ Γ Γ ((U i).shiftObj (-2)) (U i) :=
  (GradedModuleCat.shiftFunctor (-2)).map (zigzagBraidSelfTensorInl k G i) ≫
    (tensorShiftFirst k G i).inv

private theorem shiftedSelfFirstInl_generator (i : V) :
    (zigzagBraidSelfTensorShiftLeftInl k G i).hom (vertexGenerator k G i) =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i)
        (vertexGenerator k G i) (vertexGenerator k G i) := by
  have h := zigzagBraidSelfTensorInl_hom_factors k G i
    (spanSingletonGenerator (zigzagAlgebraBasis k G (.inl i)))
    (spanSingletonGenerator (op (zigzagAlgebraBasis k G (.inl i))))
  let g : U i := vertexGenerator k G i
  change (zigzagBraidSelfTensorInl k G i).hom g =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U i) g g at h
  -- Compute the shifted morphism on the generator typed in the graded carrier.
  change (tensorShiftFirst k G i).inv.hom ((zigzagBraidSelfTensorInl k G i).hom g) =
    GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) g g
  rw [h]
  exact tensorShiftFirst_inv_tmul k G i g g

/-- Right evaluation on the shifted left insertion is the identity. -/
@[reassoc]
theorem zigzagBraidSelfTensorShiftLeftInl_evaluation (i : V) :
    zigzagBraidSelfTensorShiftLeftInl k G i ≫ GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (𝟙 ((U i).shiftObj (-2))) (zigzagBraidEvaluationHom k G i) ≫
      (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom =
        𝟙 ((U i).shiftObj (-2)) := by
  let g : U i := vertexGenerator k G i
  let gs : (U i).shiftObj (-2) := vertexGenerator k G i
  let z : zigzagGradedBimodule k G :=
    Bimodule.of (AlgHom.id k Z) (zigzagAlgebraBasis k G (.inl i))
  have heval : (zigzagBraidEvaluationHom k G i).hom g = z :=
    (LinearMap.congr_fun (hom_zigzagBraidEvaluationHom (k := k) (G := G) i) g).trans
      (eval_vertexGenerator k G i)
  have hinsert : (zigzagBraidSelfTensorShiftLeftInl k G i).hom gs =
      GradedModuleCat.bimoduleTensorTmul Γ Γ Γ ((U i).shiftObj (-2)) (U i) gs g :=
    shiftedSelfFirstInl_generator k G i
  have hscalar : ((1 : Z) ⊗ₜ[k] op ((Bimodule.of (AlgHom.id k Z)).symm z)) • gs = gs := by
    have hz : (Bimodule.of (AlgHom.id k Z)).symm z = zigzagAlgebraBasis k G (.inl i) :=
      LinearEquiv.symm_apply_apply _ _
    rw [hz]
    exact generator_right_vertex k G i
  apply GradedModuleCat.hom_ext
  apply vertex_linearMap_ext k G i
  -- Evaluate the right-unit composite in the internally shifted carrier.
  change (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom.hom
    ((GradedModuleCat.bimoduleTensorMap Γ Γ Γ
      (𝟙 ((U i).shiftObj (-2))) (zigzagBraidEvaluationHom k G i)).hom
      ((zigzagBraidSelfTensorShiftLeftInl k G i).hom gs)) = gs
  rw [hinsert, GradedModuleCat.bimoduleTensorMap_tmul Γ Γ Γ
    (M := (U i).shiftObj (-2)) (N := U i)
    (M' := (U i).shiftObj (-2)) (N' := zigzagGradedBimodule k G),
    GradedModuleCat.hom_id, LinearMap.id_apply, heval]
  exact (zigzagBimoduleRightUnitor_hom_tmul k G ((U i).shiftObj (-2)) gs z).trans hscalar

/-- Coevaluation followed by the right volume projection is the right unitor. -/
@[reassoc]
theorem zigzagBraidSelfTensorShiftRightIso_coevaluation_snd (i : V) :
    ((F).obj (U i)).map (zigzagBraidCoevaluationHom k G i) ≫
      (zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd =
        (zigzagBimoduleRightUnitor k G (U i)).hom := by
  -- The bifunctor map is the previously checked graded tensor map.
  change GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
    (zigzagBraidCoevaluationHom k G i) ≫
    (zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd = _
  have h := congrArg (fun f ↦ (zigzagBimoduleRightUnitor k G (U i)).hom ≫ f)
    (coevaluation_identity_block k G i)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using h

/-- The first summand of the right shifted decomposition is the shifted insertion. -/
@[reassoc]
theorem zigzagBraidSelfTensorShiftRightIso_inl_inv (i : V) :
    biprod.inl ≫ (zigzagBraidSelfTensorShiftRightIso k G i).inv =
      zigzagBraidSelfTensorShiftRightInl k G i := by
  let S := GradedModuleCat.shiftFunctor (𝒜 := (zigzagEnvelopingGrading k G).piece) (-2)
  have : PreservesBinaryBiproduct (U i) ((U i).shiftObj 2) S :=
    preservesBinaryBiproduct_of_preservesBiproduct S (U i) ((U i).shiftObj 2)
  have h : S.map (biprod.inl : U i ⟶ U i ⊞ (U i).shiftObj 2) ≫
      S.map (zigzagBraidSelfTensorIso k G i).inv = S.map (zigzagBraidSelfTensorInl k G i) := by
    rw [← S.map_comp, zigzagBraidSelfTensorIso_inv, biprod.inl_desc]
  -- The shift comparison and biproduct comparison specify this inverse on its first summand.
  change biprod.inl ≫ biprod.map (𝟙 _) (shiftTwoMinusTwoIso k G i).inv ≫
    (S.mapBiprod (U i) ((U i).shiftObj 2)).inv ≫
    S.map (zigzagBraidSelfTensorIso k G i).inv ≫ (tensorShiftSecond k G i).inv =
      S.map (zigzagBraidSelfTensorInl k G i) ≫ (tensorShiftSecond k G i).inv
  simp only [biprod.inl_map_assoc, Category.id_comp, Functor.mapBiprod_inv,
    biprod.inl_desc_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (tensorShiftSecond k G i).inv) h)

/-- Coevaluation followed by the left volume projection is the left unitor. -/
@[reassoc]
theorem zigzagBraidSelfTensorShiftLeftIso_coevaluation_snd (i : V) :
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidCoevaluationHom k G i) (𝟙 (U i)) ≫
      (zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd =
        (zigzagBimoduleLeftUnitor k G (U i)).hom := by
  have h := congrArg (fun f ↦ (zigzagBimoduleLeftUnitor k G (U i)).hom ≫ f)
    (coevaluation_first_identity_block k G i)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using h

/-- The first summand of the left shifted decomposition is the shifted insertion. -/
@[reassoc]
theorem zigzagBraidSelfTensorShiftLeftIso_inl_inv (i : V) :
    biprod.inl ≫ (zigzagBraidSelfTensorShiftLeftIso k G i).inv =
      zigzagBraidSelfTensorShiftLeftInl k G i := by
  let S := GradedModuleCat.shiftFunctor (𝒜 := (zigzagEnvelopingGrading k G).piece) (-2)
  have : PreservesBinaryBiproduct (U i) ((U i).shiftObj 2) S :=
    preservesBinaryBiproduct_of_preservesBiproduct S (U i) ((U i).shiftObj 2)
  have h : S.map (biprod.inl : U i ⟶ U i ⊞ (U i).shiftObj 2) ≫
      S.map (zigzagBraidSelfTensorIso k G i).inv = S.map (zigzagBraidSelfTensorInl k G i) := by
    rw [← S.map_comp, zigzagBraidSelfTensorIso_inv, biprod.inl_desc]
  -- The shift comparison and biproduct comparison specify this inverse on its first summand.
  change biprod.inl ≫ biprod.map (𝟙 _) (shiftTwoMinusTwoIso k G i).inv ≫
    (S.mapBiprod (U i) ((U i).shiftObj 2)).inv ≫
    S.map (zigzagBraidSelfTensorIso k G i).inv ≫ (tensorShiftFirst k G i).inv =
      S.map (zigzagBraidSelfTensorInl k G i) ≫ (tensorShiftFirst k G i).inv
  simp only [biprod.inl_map_assoc, Category.id_comp, Functor.mapBiprod_inv,
    biprod.inl_desc_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (tensorShiftFirst k G i).inv) h)

end TauCeti
