/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Balanced
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Torsor

/-!
# Torsor modifications of pivotal structures and functorial preservation

On a rigid monoidal category `C`, the commutative group `Aut (LaxMonoidalFunctor.of (𝟭 C))` of
monoidal natural automorphisms of the identity functor acts freely and transitively on
`PivotalCategory C` by `(u • P).pivotalIso = u ≪≫ P.pivotalIso`
(`TauCeti.PivotalCategory.instTorsor`).

This file records how torsor modifications interact with induced twists and with pivotal- and
twist-preserving functors:

* On a braided rigid category `C`, twisting a pivotal structure `P` by `u` multiplies its induced
  twist `TauCeti.balancedOfBraidedPivotal` by `u`:
  `(@balancedOfBraidedPivotal C _ _ _ _ (u • P)).twist = u ≪≫ (balancedOfBraidedPivotal C).twist`.
  In particular, when `C` is symmetric rigid and `P` is its canonical Drinfeld pivotal structure
  (whose twist is `𝟙`), the twist induced by `u • P` is `u` itself.
* If `F : C ⥤ D` is a strong monoidal functor already pivotal for `(P, Q)`, then `F` is pivotal for
  `(v • P, u • Q)` if and only if `F.map (v_X) = u_{F X}` for every `X : C`. When `F` is strong
  braided, the exact same criterion governs twist preservation for the induced balanced structures,
  both globally and objectwise.
* Specializing to `F = 𝟭 C`, the identity functor is pivotal (and, in the braided case, balanced
  for the induced twists) from `v • P` to `u • P` if and only if `v = u`, and from `P` to `u • P`
  if and only if `u = 1`. In a symmetric rigid category, modifying the canonical pivotal structure
  by a nontrivial monoidal automorphism `u` (such as a nontrivial grading character) therefore
  causes both pivotal preservation and twist preservation for `𝟭 C` to fail at every object `X`
  with `u_X ≠ 𝟙 X`.

## Main declarations

* `TauCeti.PivotalCategory.smul_right_inj`, `TauCeti.PivotalCategory.smul_eq_self_iff`,
  `TauCeti.balancedOfBraidedPivotal_inj`, and `TauCeti.pivotalOfBalanced_inj`: injectivity and
  fixed-point lemmas for the torsor action and `TauCeti.pivotalBalancedEquiv`;
* `TauCeti.balancedOfBraidedPivotal_smul_twist` and
  `TauCeti.balancedOfBraidedPivotal_smul_twist_hom_app`: twisting a pivotal structure by `u`
  precomposes the induced twist with `u`;
* `TauCeti.balancedOfBraidedPivotal_smul_canonical_twist`: in a symmetric rigid category, twisting
  the canonical pivotal structure by `u` yields induced twist `u`;
* `CategoryTheory.Functor.isPivotal_smul_iff` and
  `CategoryTheory.Functor.isBalanced_balancedOfBraidedPivotal_smul_iff`: criterion for a pivotal
  (or braided pivotal) functor `F` to remain pivotal or balanced after torsor modifications on
  source and target;
* `CategoryTheory.Functor.isPivotal_id_iff_eq`, `CategoryTheory.Functor.isPivotal_id_smul_iff`, and
  `CategoryTheory.Functor.isBalanced_id_balancedOfBraidedPivotal_smul_iff`: `𝟭 C` preserves pivotal
  structures or induced twists between torsor translates if and only if the translates coincide.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 8.10
* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
-/

public section

open CategoryTheory MonoidalCategory TauCeti

namespace TauCeti

universe v u

section Torsor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Acting on a pivotal structure `P` by two monoidal automorphisms of `𝟭 C` produces equal pivotal
structures if and only if the automorphisms are equal, without needing an ambient `Nonempty`
typeclass assumption. -/
@[simp]
theorem PivotalCategory.smul_right_inj (P : PivotalCategory C)
    {v u : Aut (LaxMonoidalFunctor.of (𝟭 C))} :
    v • P = u • P ↔ v = u := by
  have : Nonempty (PivotalCategory C) := ⟨P⟩
  exact smul_right_cancel_iff P

/-- A torsor modification `u • P` fixes `P` if and only if `u = 1`. -/
@[simp]
theorem PivotalCategory.smul_eq_self_iff (P : PivotalCategory C)
    {u : Aut (LaxMonoidalFunctor.of (𝟭 C))} :
    u • P = P ↔ u = 1 :=
  ⟨fun h ↦ (PivotalCategory.smul_right_inj P).mp (h.trans (one_smul _ P).symm),
    fun h ↦ by rw [h, one_smul]⟩

/-- Symmetric form of `PivotalCategory.smul_eq_self_iff`. -/
@[simp]
theorem PivotalCategory.self_eq_smul_iff (P : PivotalCategory C)
    {u : Aut (LaxMonoidalFunctor.of (𝟭 C))} :
    P = u • P ↔ u = 1 :=
  eq_comm.trans (PivotalCategory.smul_eq_self_iff P)

end Torsor

section Twist

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Passing from pivotal structures to induced balanced structures on a braided rigid category is
injective. -/
@[simp]
theorem balancedOfBraidedPivotal_inj [BraidedCategory C] [RigidCategory C]
    {P Q : PivotalCategory C} :
    @balancedOfBraidedPivotal C _ _ _ _ P = @balancedOfBraidedPivotal C _ _ _ _ Q ↔ P = Q :=
  ⟨fun h ↦ by
    rw [← pivotalOfBalanced_balancedOfBraidedPivotal P,
      ← pivotalOfBalanced_balancedOfBraidedPivotal Q, h],
    fun h ↦ h ▸ rfl⟩

/-- Passing from balanced structures to induced pivotal structures on a braided rigid category is
injective. -/
@[simp]
theorem pivotalOfBalanced_inj [BraidedCategory C] [RigidCategory C]
    {B₁ B₂ : BalancedCategory C} :
    @pivotalOfBalanced C _ _ _ _ B₁ = @pivotalOfBalanced C _ _ _ _ B₂ ↔ B₁ = B₂ :=
  ⟨fun h ↦ by
    rw [← balancedOfBraidedPivotal_pivotalOfBalanced B₁,
      ← balancedOfBraidedPivotal_pivotalOfBalanced B₂, h],
    fun h ↦ h ▸ rfl⟩

/-- Twisting a pivotal structure `P` on a braided rigid category by a monoidal natural automorphism
`u` of `𝟭 C` precomposes the induced twist with `u`. -/
@[simp]
theorem balancedOfBraidedPivotal_smul_twist [BraidedCategory C] [RigidCategory C]
    (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) (P : PivotalCategory C) :
    (@balancedOfBraidedPivotal C _ _ _ _ (u • P)).twist =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso ≪≫
        (@balancedOfBraidedPivotal C _ _ _ _ P).twist := by
  ext X
  simp [balancedOfBraidedPivotal_twist_hom_app, PivotalCategory.smul_pivotalIsoApp]

/-- At an object `X`, the twist induced by `u • P` is `u_X` followed by the twist induced by `P`. -/
theorem balancedOfBraidedPivotal_smul_twist_hom_app [BraidedCategory C] [RigidCategory C]
    (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) (P : PivotalCategory C) (X : C) :
    (@balancedOfBraidedPivotal C _ _ _ _ (u • P)).twist.hom.app X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso.hom.app X ≫
        (@balancedOfBraidedPivotal C _ _ _ _ P).twist.hom.app X := by
  rw [balancedOfBraidedPivotal_smul_twist, Iso.trans_hom, NatTrans.comp_app]

/-- In a symmetric rigid category, twisting the canonical Drinfeld pivotal structure by a monoidal
natural automorphism `u` of `𝟭 C` produces the balanced structure whose twist is `u`. -/
theorem balancedOfBraidedPivotal_smul_canonical_twist [SymmetricCategory C] [RigidCategory C]
    (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    (@balancedOfBraidedPivotal C _ _ _ _ (u • (inferInstance : PivotalCategory C))).twist =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso := by
  rw [balancedOfBraidedPivotal_smul_twist, balancedOfBraidedPivotal_twist_eq_refl, Iso.trans_refl]

/-- At an object `X` of a symmetric rigid category, the twist induced by modifying the canonical
pivotal structure by `u` has component `u_X`. -/
theorem balancedOfBraidedPivotal_smul_canonical_twist_hom_app [SymmetricCategory C]
    [RigidCategory C] (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) :
    (@balancedOfBraidedPivotal C _ _ _ _
        (u • (inferInstance : PivotalCategory C))).twist.hom.app X =
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso.hom.app X := by
  rw [balancedOfBraidedPivotal_smul_canonical_twist]

end Twist

end TauCeti

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

section Rigid

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [RigidCategory D]

/-- If `F : C ⥤ D` is pivotal for `(P, Q)`, then at a fixed object `X : C` it satisfies the pivotal
preservation equation for `(v • P, u • Q)` if and only if `F.map (v_X) = u_{F X}`. -/
theorem map_smul_pivotalIsoApp_comp_mapDoubleRightDualIso_iff
    [P : PivotalCategory C] [Q : PivotalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.IsPivotal]
    (v : Aut (LaxMonoidalFunctor.of (𝟭 C))) (u : Aut (LaxMonoidalFunctor.of (𝟭 D))) (X : C) :
    F.map (@pivotalIsoApp C _ _ _ (v • P) X).hom ≫ (F.mapDoubleRightDualIso X).hom =
        (@pivotalIsoApp D _ _ _ (u • Q) (F.obj X)).hom ↔
      F.map ((LaxMonoidalFunctor.forgetAut (𝟭 C) v).asIso.hom.app X) =
        (LaxMonoidalFunctor.forgetAut (𝟭 D) u).asIso.hom.app (F.obj X) := by
  have hX : F.map (@pivotalIsoApp C _ _ _ P X).hom ≫ (F.mapDoubleRightDualIso X).hom =
      (@pivotalIsoApp D _ _ _ Q (F.obj X)).hom :=
    (isPivotal_iff_map_pivotalIsoApp_hom_comp_mapDoubleRightDualIso_hom (F := F)).mp
      inferInstance X
  rw [PivotalCategory.smul_pivotalIsoApp, PivotalCategory.smul_pivotalIsoApp]
  simp only [Iso.trans_hom, Iso.app_hom, F.map_comp, Category.assoc, hX]
  exact cancel_mono (@pivotalIsoApp D _ _ _ Q (F.obj X)).hom

/-- A strong monoidal functor `F : C ⥤ D` that is pivotal for `(P, Q)` remains pivotal after
modifying `P` by `v` and `Q` by `u` if and only if `F.map (v_X) = u_{F X}` for all `X : C`. -/
theorem isPivotal_smul_iff [P : PivotalCategory C] [Q : PivotalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.IsPivotal]
    (v : Aut (LaxMonoidalFunctor.of (𝟭 C))) (u : Aut (LaxMonoidalFunctor.of (𝟭 D))) :
    @IsPivotal C _ _ D _ _ _ (v • P) _ (u • Q) F _ ↔
      ∀ X : C, F.map ((LaxMonoidalFunctor.forgetAut (𝟭 C) v).asIso.hom.app X) =
        (LaxMonoidalFunctor.forgetAut (𝟭 D) u).asIso.hom.app (F.obj X) := by
  rw [@isPivotal_iff_map_pivotalIsoApp_hom_comp_mapDoubleRightDualIso_hom C _ _ D _ _ _
    (v • P) _ (u • Q) F _]
  exact forall_congr' (F.map_smul_pivotalIsoApp_comp_mapDoubleRightDualIso_iff v u)

/-- A pivotal functor `F : C ⥤ D` remains pivotal when the target pivotal structure `Q` is modified
by `u` if and only if `u` is the identity on every object in the image of `F`. -/
theorem isPivotal_smul_right_iff [P : PivotalCategory C] [Q : PivotalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.IsPivotal] (u : Aut (LaxMonoidalFunctor.of (𝟭 D))) :
    @IsPivotal C _ _ D _ _ _ P _ (u • Q) F _ ↔
      ∀ X : C, (LaxMonoidalFunctor.forgetAut (𝟭 D) u).asIso.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  have h := F.isPivotal_smul_iff (1 : Aut (LaxMonoidalFunctor.of (𝟭 C))) u
  rw [one_smul] at h
  simpa [eq_comm] using h

/-- A pivotal functor `F : C ⥤ D` remains pivotal when the source pivotal structure `P` is modified
by `v` if and only if `F` maps every component of `v` to an identity morphism. -/
theorem isPivotal_smul_left_iff [P : PivotalCategory C] [Q : PivotalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.IsPivotal] (v : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    @IsPivotal C _ _ D _ _ _ (v • P) _ Q F _ ↔
      ∀ X : C, F.map ((LaxMonoidalFunctor.forgetAut (𝟭 C) v).asIso.hom.app X) = 𝟙 (F.obj X) := by
  have h := F.isPivotal_smul_iff v (1 : Aut (LaxMonoidalFunctor.of (𝟭 D)))
  rw [one_smul] at h
  simpa using h

/-- The identity functor `𝟭 C` is pivotal from a pivotal structure `P` to a pivotal structure `Q`
if and only if `P = Q`. -/
@[simp]
theorem isPivotal_id_iff_eq (P Q : PivotalCategory C) :
    @IsPivotal C _ _ C _ _ _ P _ Q (𝟭 C) _ ↔ P = Q := by
  constructor
  · intro h
    have hEq := (@isPivotal_iff_map_pivotalIsoApp_hom_comp_mapDoubleRightDualIso_hom
      C _ _ C _ _ _ P _ Q (𝟭 C) _).mp h
    apply PivotalCategory.ext
    ext X
    have hX := hEq X
    simp only [Functor.id_obj, Functor.id_map, mapDoubleRightDualIso_id, Iso.refl_hom,
      Category.comp_id] at hX
    exact (@pivotalIso_hom_app C _ _ _ P X).trans
      (hX.trans (@pivotalIso_hom_app C _ _ _ Q X).symm)
  · rintro rfl
    let := P
    infer_instance

/-- The identity functor `𝟭 C` is pivotal from `v • P` to `u • P` if and only if `v = u`. -/
theorem isPivotal_id_smul_iff (P : PivotalCategory C)
    (v u : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    @IsPivotal C _ _ C _ _ _ (v • P) _ (u • P) (𝟭 C) _ ↔ v = u := by
  simp

/-- The identity functor `𝟭 C` is pivotal from `P` to `u • P` if and only if `u = 1`. -/
theorem isPivotal_id_smul_right_iff (P : PivotalCategory C)
    (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    @IsPivotal C _ _ C _ _ _ P _ (u • P) (𝟭 C) _ ↔ u = 1 := by
  simp

end Rigid

section Braided

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C] [RigidCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] [RigidCategory D]

/-- A strong braided functor `F : C ⥤ D` that is pivotal for `(P, Q)` preserves the twists induced
by `(v • P, u • Q)` if and only if `F.map (v_X) = u_{F X}` for every `X : C`. -/
theorem isBalanced_balancedOfBraidedPivotal_smul_iff [P : PivotalCategory C] [Q : PivotalCategory D]
    (F : C ⥤ D) [F.Braided] [F.IsPivotal]
    (v : Aut (LaxMonoidalFunctor.of (𝟭 C))) (u : Aut (LaxMonoidalFunctor.of (𝟭 D))) :
    @IsBalanced C _ _ _ (@balancedOfBraidedPivotal C _ _ _ _ (v • P))
        D _ _ _ (@balancedOfBraidedPivotal D _ _ _ _ (u • Q)) F _ ↔
      ∀ X : C, F.map ((LaxMonoidalFunctor.forgetAut (𝟭 C) v).asIso.hom.app X) =
        (LaxMonoidalFunctor.forgetAut (𝟭 D) u).asIso.hom.app (F.obj X) :=
  (@isBalanced_iff_isPivotal C _ _ _ _ D _ _ _ _ (v • P) (u • Q) F _).trans
    (F.isPivotal_smul_iff v u)

/-- The identity braided functor `𝟭 C` is balanced from `B₁` to `B₂` if and only if `B₁ = B₂`. -/
@[simp]
theorem isBalanced_id_iff_eq {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [BraidedCategory C] (B₁ B₂ : BalancedCategory C) :
    @IsBalanced C _ _ _ B₁ C _ _ _ B₂ (𝟭 C) _ ↔ B₁ = B₂ := by
  constructor
  · intro h
    apply BalancedCategory.ext
    ext X
    exact h.map_twist_hom_app X
  · rintro rfl
    let := B₁
    infer_instance

/-- The identity braided functor `𝟭 C` preserves the twists induced by `v • P` and `u • P` if and
only if `v = u`. -/
theorem isBalanced_id_balancedOfBraidedPivotal_smul_iff (P : PivotalCategory C)
    (v u : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    @IsBalanced C _ _ _ (@balancedOfBraidedPivotal C _ _ _ _ (v • P))
        C _ _ _ (@balancedOfBraidedPivotal C _ _ _ _ (u • P)) (𝟭 C) _ ↔ v = u := by
  simp

/-- The identity braided functor `𝟭 C` preserves the twist from `P` to `u • P` if and only if
`u = 1`. -/
theorem isBalanced_id_balancedOfBraidedPivotal_smul_right_iff (P : PivotalCategory C)
    (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    @IsBalanced C _ _ _ (@balancedOfBraidedPivotal C _ _ _ _ P)
        C _ _ _ (@balancedOfBraidedPivotal C _ _ _ _ (u • P)) (𝟭 C) _ ↔ u = 1 := by
  simp

/-- At a fixed object `X : C`, the identity braided functor `𝟭 C` preserves the twist from `P` to
`u • P` if and only if `u_X = 𝟙 X`. -/
theorem id_map_balancedOfBraidedPivotal_smul_twist_iff (P : PivotalCategory C)
    (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) (X : C) :
    (𝟭 C).map ((@balancedOfBraidedPivotal C _ _ _ _ P).twist.hom.app X) =
        (@balancedOfBraidedPivotal C _ _ _ _ (u • P)).twist.hom.app X ↔
      (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso.hom.app X = 𝟙 X := by
  rw [Functor.id_map, balancedOfBraidedPivotal_smul_twist_hom_app]
  -- Chain `Category.id_comp` with `Eq.trans` so `(𝟭 C).obj X` and `X` unify definitionally.
  refine ⟨fun h ↦ ?_, fun h ↦ (Category.id_comp _).symm.trans (congrArg (· ≫ _) h.symm)⟩
  exact (cancel_mono ((@balancedOfBraidedPivotal C _ _ _ _ P).twist.hom.app X)).mp
    (h.symm.trans (Category.id_comp _).symm)

end Braided

end CategoryTheory.Functor
