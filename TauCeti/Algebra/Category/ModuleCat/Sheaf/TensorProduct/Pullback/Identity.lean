/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward

/-!
# Identity coherence for pullback of sheaves of modules

The canonical identification of pullback along the identity with the identity functor respects
both the unit and the tensor comparison. Thus the oplax tensor map for identity pullback is
exactly the map induced by the identity comparison on each tensor factor, not a separately
chosen identification.

Mathlib's `SheafOfModules.pushforwardId` and `SheafOfModules.pullbackId` are the canonical
identity comparisons. Identity pushforward respects the lax monoidal structure, and identity
pullback respects the oplax monoidal structure. The unit and tensor formulas supply the identity
normalization needed when comparing successive pullbacks of tensor products.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The canonical comparison for identity pushforward is the identity on each module. -/
private lemma pushforwardId_hom_app (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (_root_.SheafOfModules.pushforwardId (ringCatSheaf R)).hom.app M = 𝟙 M :=
  rfl

/-- The unit map of identity pushforward acts identically on sections of the structure sheaf. -/
private lemma pushforward_id_ε :
    let := pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pushforward.{u}
      (J := J) (K := J) (S := ringCatSheaf R) (R := ringCatSheaf R)
      (F := 𝟭 C) (𝟙 (ringCatSheaf R))) = 𝟙 (𝟙_ _) := by
  dsimp only
  -- The identity sheaf pushforward agrees with `R` after unfolding its wrapper.
  erw [pushforward_ε]
  ext U
  -- Both section maps are induced by the identity ring homomorphism.
  rfl

/-- On pure tensors of sections, identity presheaf pushforward leaves the tensor inclusion
of sheaves into presheaves unchanged. -/
private lemma presheafPushforward_id_μ_comp_app_tmul
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    let := presheafPushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C)
      (𝟙 (ringCatSheaf R))
    ((Functor.LaxMonoidal.μ
        (presheafPushforward (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M.val N.val ≫
      (presheafPushforward (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))).map
        (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N)).app U).hom
      (m ⊗ₜ[R.obj.obj U] n) =
      ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app U).hom
        (m ⊗ₜ[R.obj.obj U] n) := by
  dsimp only
  -- The source modules are restriction of scalars along the identity ring homomorphism.
  erw [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    presheafPushforward_μ_app_tmul (S := R) (R := R) (F := 𝟭 C)
      (𝟙 (ringCatSheaf R)) M.val N.val U m n]
  -- Identity pushforward leaves both the section map and its scalar action unchanged.
  rfl

/-- The canonical identity comparison for pushforward is lax monoidal. -/
instance isMonoidal_pushforwardId_hom :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (_root_.SheafOfModules.pushforwardId.{u} (ringCatSheaf R)).hom
      (pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
      Functor.LaxMonoidal.id := by
  -- Identity pushforward is definitionally the identity functor. Specify its canonical
  -- pushforward structure, rather than the identity functor's monoidal structure.
  let := pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  refine { unit := ?_, tensor := fun M N ↦ ?_ }
  · simp only [pushforwardId_hom_app, pushforward_id_ε, Functor.LaxMonoidal.id_ε]
    exact Category.comp_id _
  · apply tensor_hom_ext
    simp only [Functor.map_comp]
    -- The characterization uses `M.val` rather than `(forget _).obj M`.
    erw [forget_μ_comp_map_pushforward_μ_assoc (S := R) (R := R) (F := 𝟭 C)
      (𝟙 (ringCatSheaf R)) M N]
    simp only [pushforwardId_hom_app, Functor.LaxMonoidal.id_μ]
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    erw [tensorHom_id, id_whiskerRight]
    let := presheafPushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C)
      (𝟙 (ringCatSheaf R))
    exact presheafPushforward_id_μ_comp_app_tmul R M N U m n

/-- The unit comparison for identity pullback is the component of its canonical identity
isomorphism at the structure sheaf. -/
@[simp]
theorem pullback_id_η :
    letI := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    Functor.OplaxMonoidal.η
        (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
          (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) =
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app (𝟙_ _) := by
  let := pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  let := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  have := isMonoidal_pullbackPushforwardAdjunction (S := R) (R := R)
    (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  have := isMonoidal_pushforwardId_hom R
  -- The two right adjoints are definitionally the same functor but carry different structures.
  -- Pass the identity functor's standard structure explicitly in the mate theorem.
  have h := @Adjunction.app_tensorUnit_comp_η_of_conjugateEquiv _ _ _ _ _ _ _ _ _ _
    Adjunction.id
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    Functor.OplaxMonoidal.id
    (pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    Functor.LaxMonoidal.id
    (pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    (by infer_instance) (by infer_instance) _ _ (by infer_instance)
    (_root_.SheafOfModules.conjugateEquiv_pullbackId_hom (ringCatSheaf R))
  simpa using h.symm

/-- Through the canonical identity isomorphism, the tensor comparison for identity pullback
is the tensor product of the identity comparisons on its two factors. -/
@[reassoc (attr := simp)]
theorem pullback_id_δ (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
          (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N ≫
      ((_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app M ⊗ₘ
        (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app N) =
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app (M ⊗ N) := by
  let := pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  let := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  have := isMonoidal_pullbackPushforwardAdjunction (S := R) (R := R)
    (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  have := isMonoidal_pushforwardId_hom R
  -- As for the unit formula, distinguish the two lax structures on identity pushforward.
  have h := @Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _ _ _ _ _ _ _ _ _
    Adjunction.id
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    Functor.OplaxMonoidal.id
    (pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    Functor.LaxMonoidal.id
    (pushforwardLaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    (by infer_instance) (by infer_instance) _ _ (by infer_instance)
    (_root_.SheafOfModules.conjugateEquiv_pullbackId_hom (ringCatSheaf R)) M N
  simpa using h.symm

end

end TauCeti.SheafOfModules
