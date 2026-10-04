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

The proof uses Mathlib's `SheafOfModules.pushforwardId` and
`SheafOfModules.conjugateEquiv_pullbackId_hom`: identity pushforward is lax monoidally identified
with the identity, and passage to adjunction mates gives the pullback formulas. These formulas
supply the identity normalization needed when comparing successive pullbacks of tensor products.
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
  · -- The identity sheaf pushforward is only definitionally equal to `R` at full transparency.
    erw [pushforward_ε (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))]
    ext U
    rfl
  · apply tensor_hom_ext
    simp only [Functor.map_comp]
    -- Unfold the same identity-pushforward wrapper when using the presheaf characterization.
    erw [forget_μ_comp_map_pushforward_μ_assoc (S := R) (R := R) (F := 𝟭 C)
      (𝟙 (ringCatSheaf R)) M N]
    simp only [_root_.SheafOfModules.pushforwardId, Iso.refl_hom, NatTrans.id_app,
      Functor.LaxMonoidal.id_μ]
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    -- Identity pushforward and its comparison act as identities on the underlying sections.
    convert congrArg ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R))
      M N).app U) (presheafPushforward_μ_app_tmul (S := R) (R := R) (F := 𝟭 C)
        (𝟙 (ringCatSheaf R)) M.val N.val U m n) using 1
    all_goals first | rfl | (erw [tensorHom_id, id_whiskerRight]; rfl)

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
