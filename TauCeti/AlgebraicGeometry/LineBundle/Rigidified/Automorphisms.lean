/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# Automorphisms and rescalings of rigidified line bundles

Let `s : T ⟶ Y` be a morphism of schemes and `P` a line bundle `L` on `Y` rigidified along `s`,
with trivialization `α : s^* L ≅ 𝒪_T`. The automorphisms of `L` are the global units
`Γ(Y, 𝒪_Y)ˣ` (`Scheme.Modules.unitsGlobalSectionsMulEquivAut`), and the automorphism given by
a unit `u` respects the rigidification exactly when the pullback `s^♯ u` of `u` is `1`. So the
automorphism group of the rigidified line bundle is the kernel of `Γ(Y, 𝒪_Y)ˣ → Γ(T, 𝒪_T)ˣ`,
and the rigidified line bundle has no automorphisms other than the identity exactly when this map
is injective, for instance when `s` is a section of a morphism `f : Y ⟶ T` with `f_* 𝒪_Y = 𝒪_T`.
This *rigidity* removes the automorphisms from the moduli problem: an isomorphism of rigidified line
bundles is then unique when it exists, so the isomorphism classes of rigidified line bundles form a
set-valued functor with no automorphism ambiguity, the rigidified Picard functor.

The trivializations of a fixed line bundle `L` along `s` are permuted by the global units
`Γ(T, 𝒪_T)ˣ`, acting through the automorphisms of `𝒪_T`. This action descends to isomorphism
classes of rigidified line bundles. There it is transitive on the classes with a given underlying
line bundle, and the stabilizer of every class is the image of `Γ(Y, 𝒪_Y)ˣ → Γ(T, 𝒪_T)ˣ`.
Consequently, forgetting the rigidification is injective on classes exactly when
`Γ(Y, 𝒪_Y)ˣ → Γ(T, 𝒪_T)ˣ` is surjective, as it is when `s` is a section of a morphism `Y ⟶ T`,
and its image consists of the classes of the line bundles whose pullback along `s` is trivial.

## Main declarations

* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle.autSubgroup`: the automorphisms of the
  underlying line bundle respecting the rigidification, identified with the kernel of
  `Γ(Y, 𝒪_Y)ˣ → Γ(T, 𝒪_T)ˣ` by
  `RigidifiedLineBundle.unitsGlobalSectionsMulEquivAut_mem_autSubgroup_iff`;
* `RigidifiedLineBundle.autSubgroup_eq_bot_iff`: **rigidity**, a rigidified line bundle has only
  the identity automorphism exactly when `Γ(Y, 𝒪_Y)ˣ → Γ(T, 𝒪_T)ˣ` is injective;
* the actions of `Γ(T, 𝒪_T)ˣ` on `RigidifiedLineBundle s` and on `RigidifiedLineBundleClass s`
  by rescaling the trivialization;
* `RigidifiedLineBundleClass.mk_mk_eq_mk_mk_iff`: two rigidifications of the same line bundle
  give the same class exactly when they differ by the pullback of a global unit of `Y`;
* `RigidifiedLineBundleClass.exists_smul_eq_of_toLineBundleClass_eq` and
  `RigidifiedLineBundleClass.stabilizer_eq_range`: rescaling is transitive on the classes over a
  fixed line bundle, with stabilizer the image of `Γ(Y, 𝒪_Y)ˣ`;
* `RigidifiedLineBundleClass.toLineBundleClass_injective_iff` and
  `RigidifiedLineBundleClass.mem_range_toLineBundleClass_iff`: the fibres and the image of
  forgetting the rigidification;
* `RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id`: forgetting the
  rigidification is injective when `s` is a section of a morphism `Y ⟶ T`, and
  `RigidifiedLineBundleClass.range_toLineBundleClass` describes its image as the line-bundle classes
  whose pullback along `s` is trivial.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1 (rigidified line bundles).
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {T Y : Scheme.{u}} {s : T ⟶ Y}

namespace RigidifiedLineBundle

section Automorphisms

variable (P : RigidifiedLineBundle s)

/-- The automorphisms of the line bundle underlying a rigidified line bundle `P` that respect
its rigidification: those whose pullback along `s` carries the trivialization to itself. -/
def autSubgroup : Subgroup (Aut P.lineBundle.obj) where
  carrier := {e | (Scheme.Modules.pullback s).map e.hom ≫ P.rigidification.hom =
    P.rigidification.hom}
  one_mem' := by
    rw [Set.mem_ofPred_eq]
    -- The unit of `Aut` is the identity isomorphism; Mathlib has no lemma for its `hom`.
    have hone : (1 : Aut P.lineBundle.obj).hom = 𝟙 _ := rfl
    rw [hone, CategoryTheory.Functor.map_id, Category.id_comp]
  mul_mem' {e e'} he he' := by
    rw [Set.mem_ofPred_eq] at he he' ⊢
    have hmul : (e * e').hom = e'.hom ≫ e.hom :=
      (congrArg Iso.hom (Aut.Aut_mul_def _ e e')).trans (Iso.trans_hom e' e)
    rw [hmul, Functor.map_comp, Category.assoc, he, he']
  inv_mem' {e} he := by
    rw [Set.mem_ofPred_eq] at he ⊢
    have hinv : (e⁻¹).hom = e.inv := (congrArg Iso.hom (Aut.Aut_inv_def _ e)).trans (Iso.symm_hom e)
    rw [hinv]
    conv_lhs => rw [← he]
    rw [← Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]

/-- An automorphism of the line bundle respects the rigidification when its pullback along `s`
carries the trivialization to itself. -/
@[simp]
lemma mem_autSubgroup_iff (e : Aut P.lineBundle.obj) :
    e ∈ P.autSubgroup ↔
      (Scheme.Modules.pullback s).map e.hom ≫ P.rigidification.hom = P.rigidification.hom :=
  Iff.rfl

/-- The automorphism of the line bundle given by a global unit `u` of `Y` respects the
rigidification exactly when `u` pulls back to `1` along `s`. -/
lemma unitsGlobalSectionsMulEquivAut_mem_autSubgroup_iff (u : Γ(Y, ⊤)ˣ) :
    unitsGlobalSectionsMulEquivAut P.lineBundle.obj u ∈ P.autSubgroup ↔ s.appTop u = 1 := by
  rw [mem_autSubgroup_iff, unitsGlobalSectionsMulEquivAut_apply_hom,
    pullback_map_globalSectionsSmul, globalSectionsSmul_naturality]
  -- `isInvertible_unit` is stated at `SheafOfModules.unit T.ringCatSheaf`, which instance
  -- resolution does not recognise as `𝟙_ T.Modules`.
  have : SheafOfModules.isInvertible T (𝟙_ T.Modules) := SheafOfModules.isInvertible_unit T
  refine ⟨fun h ↦ globalSectionsAction_injective (𝟙_ T.Modules) ?_,
    fun h ↦ by rw [h, globalSectionsSmul_one, Category.comp_id]⟩
  rw [globalSectionsAction_apply, globalSectionsAction_apply, globalSectionsSmul_one]
  exact (cancel_epi P.rigidification.hom).mp (h.trans (Category.comp_id _).symm)

/-- **Rigidity of rigidified line bundles.** A rigidified line bundle has no automorphisms other
than the identity exactly when the pullback of global units along `s` is injective. -/
lemma autSubgroup_eq_bot_iff :
    P.autSubgroup = ⊥ ↔
      Function.Injective (Units.map (s.appTop.hom : Γ(Y, ⊤) →* Γ(T, ⊤))) := by
  have key (u : Γ(Y, ⊤)ˣ) : u ∈ (Units.map (s.appTop.hom : Γ(Y, ⊤) →* Γ(T, ⊤))).ker ↔
      unitsGlobalSectionsMulEquivAut P.lineBundle.obj u ∈ P.autSubgroup := by
    rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, MonoidHom.coe_ofClass, Units.val_one,
      unitsGlobalSectionsMulEquivAut_mem_autSubgroup_iff]
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall, Subgroup.eq_bot_iff_forall]
  constructor
  · intro h u hu
    exact (unitsGlobalSectionsMulEquivAut P.lineBundle.obj).map_eq_one_iff.mp
      (h _ ((key u).mp hu))
  · intro h e he
    obtain ⟨u, rfl⟩ := (unitsGlobalSectionsMulEquivAut P.lineBundle.obj).surjective e
    rw [h u ((key u).mpr he), map_one]

end Automorphisms

section Rescaling

/-- Global units of `T` act on line bundles rigidified along `s : T ⟶ Y` by rescaling the
trivialization through multiplication by the unit on `𝒪_T`. -/
instance : SMul Γ(T, ⊤)ˣ (RigidifiedLineBundle s) where
  smul v P := ⟨P.lineBundle, P.rigidification ≪≫ asIso (globalSectionsSmul (𝟙_ T.Modules) v)⟩

variable (v : Γ(T, ⊤)ˣ) (P : RigidifiedLineBundle s)

/-- Rescaling the trivialization does not change the underlying line bundle. -/
@[simp]
lemma smul_lineBundle : (v • P).lineBundle = P.lineBundle :=
  rfl

/-- The trivialization of a rescaled rigidified line bundle is the original trivialization
followed by multiplication by the unit. -/
@[simp]
lemma smul_rigidification :
    (v • P).rigidification = P.rigidification ≪≫ asIso (globalSectionsSmul (𝟙_ T.Modules) v) :=
  rfl

/-- Rescaling the trivialization is an action of the global units of `T`. -/
instance : MulAction Γ(T, ⊤)ˣ (RigidifiedLineBundle s) where
  one_smul P := by
    -- Compare the two fields of the structure; only the trivializations differ syntactically.
    change RigidifiedLineBundle.mk ((1 : Γ(T, ⊤)ˣ) • P).lineBundle
      ((1 : Γ(T, ⊤)ˣ) • P).rigidification = RigidifiedLineBundle.mk P.lineBundle P.rigidification
    congr 1
    ext1
    simp only [smul_rigidification, Iso.trans_hom, asIso_hom, Units.val_one,
      globalSectionsSmul_one, Category.comp_id]
  mul_smul v w P := by
    -- Compare the two fields of the structure; only the trivializations differ syntactically.
    change RigidifiedLineBundle.mk ((v * w) • P).lineBundle ((v * w) • P).rigidification =
      RigidifiedLineBundle.mk (v • w • P).lineBundle (v • w • P).rigidification
    congr 1
    ext1
    simp only [smul_rigidification, Iso.trans_hom, asIso_hom, Units.val_mul,
      globalSectionsSmul_mul, Category.assoc]

end Rescaling

end RigidifiedLineBundle

namespace RigidifiedLineBundleClass

/-- Rescaling the trivialization by a global unit of `T` descends to isomorphism classes of
rigidified line bundles. -/
instance : SMul Γ(T, ⊤)ˣ (RigidifiedLineBundleClass s) where
  smul v := lift (fun P ↦ mk (v • P)) fun _ _ ⟨e, he⟩ ↦ mk_eq_mk_iff.mpr ⟨e, by
    rw [RigidifiedLineBundle.smul_rigidification, RigidifiedLineBundle.smul_rigidification,
      Iso.trans_hom, Iso.trans_hom, ← he, Category.assoc]⟩

variable (v : Γ(T, ⊤)ˣ)

/-- Rescaling the class of a rigidified line bundle is the class of its rescaling. -/
@[simp]
lemma smul_mk (P : RigidifiedLineBundle s) : v • mk P = mk (v • P) :=
  lift_mk P

/-- Rescaling the trivialization is an action of the global units of `T` on classes. -/
instance : MulAction Γ(T, ⊤)ˣ (RigidifiedLineBundleClass s) where
  one_smul a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    rw [smul_mk, one_smul]
  mul_smul v w a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    rw [smul_mk, smul_mk, smul_mk, mul_smul]

/-- Rescaling the trivialization does not change the underlying line-bundle class. -/
@[simp]
lemma toLineBundleClass_smul (a : RigidifiedLineBundleClass s) :
    toLineBundleClass (v • a) = toLineBundleClass a := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  rw [smul_mk, toLineBundleClass_mk, toLineBundleClass_mk, RigidifiedLineBundle.smul_lineBundle]

/-- Two rigidifications `α`, `β` of the same line bundle `L` give the same class of rigidified line
bundles exactly when they differ by the pullback along `s` of a global unit of `Y`. -/
lemma mk_mk_eq_mk_mk_iff (L : InvertibleSheaf Y)
    (α β : (Scheme.Modules.pullback s).obj L.obj ≅ 𝟙_ T.Modules) :
    mk ⟨L, α⟩ = mk ⟨L, β⟩ ↔
      ∃ u : Γ(Y, ⊤)ˣ, α.hom = β.hom ≫ globalSectionsSmul (𝟙_ T.Modules) (s.appTop u) := by
  rw [mk_eq_mk_iff]
  dsimp only
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨u, hu⟩ := (unitsGlobalSectionsMulEquivAut L.obj).surjective e
    refine ⟨u, ?_⟩
    rw [← hu, unitsGlobalSectionsMulEquivAut_apply_hom, pullback_map_globalSectionsSmul,
      globalSectionsSmul_naturality] at he
    exact he.symm
  · rintro ⟨u, hu⟩
    refine ⟨unitsGlobalSectionsMulEquivAut L.obj u, ?_⟩
    rw [unitsGlobalSectionsMulEquivAut_apply_hom, pullback_map_globalSectionsSmul,
      globalSectionsSmul_naturality, hu]

/-- Two classes of rigidified line bundles with the same underlying line-bundle class differ by
rescaling the trivialization by a global unit of `T`. -/
lemma exists_smul_eq_of_toLineBundleClass_eq {a b : RigidifiedLineBundleClass s}
    (h : toLineBundleClass a = toLineBundleClass b) :
    ∃ v : Γ(T, ⊤)ˣ, v • a = b := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  obtain ⟨Q, rfl⟩ := mk_surjective b
  rw [toLineBundleClass_mk, toLineBundleClass_mk, LineBundleClass.mk_eq_mk_iff] at h
  obtain ⟨e⟩ := h
  -- The unit comparing the two trivializations through `e`.
  have : SheafOfModules.isInvertible T (𝟙_ T.Modules) := SheafOfModules.isInvertible_unit T
  obtain ⟨v, hv⟩ := (unitsGlobalSectionsMulEquivAut (𝟙_ T.Modules)).surjective
    (P.rigidification.symm ≪≫ (Scheme.Modules.pullback s).mapIso e ≪≫ Q.rigidification)
  have hv' := congrArg Iso.hom hv
  rw [unitsGlobalSectionsMulEquivAut_apply_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom] at hv'
  refine ⟨v, ?_⟩
  rw [smul_mk, mk_eq_mk_iff]
  refine ⟨e, ?_⟩
  rw [RigidifiedLineBundle.smul_rigidification, Iso.trans_hom, asIso_hom, hv',
    Iso.hom_inv_id_assoc]

/-- The stabilizer of a class of rigidified line bundles under rescaling by the global units of
`T` is the image of the global units of `Y`. -/
lemma stabilizer_eq_range (a : RigidifiedLineBundleClass s) :
    MulAction.stabilizer Γ(T, ⊤)ˣ a =
      (Units.map (s.appTop.hom : Γ(Y, ⊤) →* Γ(T, ⊤))).range := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  ext v
  rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_range, smul_mk]
  -- `v • P` is `P` with its trivialization rescaled by `v`, and `P` is the pair of its fields.
  refine (mk_mk_eq_mk_mk_iff P.lineBundle
    (P.rigidification ≪≫ asIso (globalSectionsSmul (𝟙_ T.Modules) v)) P.rigidification).trans ?_
  simp only [Iso.trans_hom, asIso_hom, cancel_epi, Units.ext_iff, Units.coe_map,
    MonoidHom.coe_ofClass]
  have : SheafOfModules.isInvertible T (𝟙_ T.Modules) := SheafOfModules.isInvertible_unit T
  constructor
  · rintro ⟨u, hu⟩
    rw [← globalSectionsAction_apply, ← globalSectionsAction_apply] at hu
    exact ⟨u, (globalSectionsAction_injective (𝟙_ T.Modules) hu).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg (globalSectionsSmul (𝟙_ T.Modules)) hu.symm⟩

/-- Forgetting the rigidification is injective on classes exactly when every global unit of `T`
is the pullback of a global unit of `Y`. -/
lemma toLineBundleClass_injective_iff :
    Function.Injective (toLineBundleClass : RigidifiedLineBundleClass s → LineBundleClass Y) ↔
      Function.Surjective (Units.map (s.appTop.hom : Γ(Y, ⊤) →* Γ(T, ⊤))) := by
  constructor
  · intro h v
    have hv : v • mk (RigidifiedLineBundle.trivial s) = mk (RigidifiedLineBundle.trivial s) :=
      h (toLineBundleClass_smul v _)
    rw [← MulAction.mem_stabilizer_iff, stabilizer_eq_range, MonoidHom.mem_range] at hv
    exact hv
  · intro h a b hab
    obtain ⟨v, rfl⟩ := exists_smul_eq_of_toLineBundleClass_eq hab
    have hv : v ∈ MulAction.stabilizer Γ(T, ⊤)ˣ a := by
      rw [stabilizer_eq_range, MonoidHom.mem_range]
      exact h v
    exact (MulAction.mem_stabilizer_iff.mp hv).symm

/-- If `s` is a section of a morphism `p : Y ⟶ T`, then forgetting the rigidification is injective
on classes: every global unit of `T` is the pullback along `s` of its pullback along `p`. -/
lemma toLineBundleClass_injective_of_comp_eq_id {p : Y ⟶ T} (h : s ≫ p = 𝟙 T) :
    Function.Injective (toLineBundleClass : RigidifiedLineBundleClass s → LineBundleClass Y) := by
  refine toLineBundleClass_injective_iff.mpr fun v ↦
    ⟨Units.map (p.appTop.hom : Γ(T, ⊤) →* Γ(Y, ⊤)) v, Units.ext ?_⟩
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h, Scheme.Hom.id_appTop,
    CommRingCat.id_apply]

/-- A line-bundle class is the class of a rigidified line bundle exactly when its pullback along
`s` is trivial. -/
lemma mem_range_toLineBundleClass_iff (L : InvertibleSheaf Y) :
    LineBundleClass.mk L ∈ Set.range (toLineBundleClass : RigidifiedLineBundleClass s → _) ↔
      Nonempty ((Scheme.Modules.pullback s).obj L.obj ≅ 𝟙_ T.Modules) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨P, rfl⟩ := mk_surjective a
    rw [toLineBundleClass_mk, LineBundleClass.mk_eq_mk_iff] at ha
    obtain ⟨e⟩ := ha
    exact ⟨(Scheme.Modules.pullback s).mapIso e.symm ≪≫ P.rigidification⟩
  · rintro ⟨α⟩
    exact ⟨mk ⟨L, α⟩, toLineBundleClass_mk _⟩

/-- The line-bundle classes underlying classes of rigidified line bundles are exactly those whose
pullback along `s` is trivial. -/
@[simp]
lemma range_toLineBundleClass :
    Set.range (toLineBundleClass : RigidifiedLineBundleClass s → LineBundleClass Y) =
      {a | LineBundleClass.pullback s a = 1} := by
  ext a
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  rw [mem_range_toLineBundleClass_iff, Set.mem_ofPred_eq, LineBundleClass.pullback_mk,
    LineBundleClass.mk_eq_one_iff, InvertibleSheaf.pullback_obj_obj]

end RigidifiedLineBundleClass

end

end AlgebraicGeometry

end TauCeti
