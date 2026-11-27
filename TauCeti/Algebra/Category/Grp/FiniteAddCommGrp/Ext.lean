/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import TauCeti.Algebra.Category.Grp.FiniteAddCommGrp.Basic
public import TauCeti.CategoryTheory.Exact.YonedaExt.TrivialIdeal
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.Data.ZMod.MulCastHom

/-!
# Yoneda self-extensions of finite cyclic groups

In the abelian category of finite abelian groups, the self-extension group of `ℤ/nℤ` is
`ℤ/nℤ`. The element `1` corresponds to the sequence `0 → ℤ/nℤ → ℤ/n²ℤ → ℤ/nℤ → 0`, with
multiplication by `n` followed by reduction modulo `n`.

In any self-extension, a lift of `1` to the middle group has its `n`-fold multiple in the
kernel and is therefore killed by `n²`. This gives a morphism from the displayed sequence
to the given extension. The resulting connecting map identifies the extension group with the
endomorphism group of `ℤ/nℤ`, since restriction along the first map of the sequence vanishes.

## References

* O. Iyama, H. Nakaoka and Y. Palu, *Auslander–Reiten theory in extriangulated categories*,
  Fact 1.20(1), for the Hom–Ext connecting sequence.
* M. Linckelmann, *A course in homological algebra*, Example 4.3(1), for the ambient cyclic
  group presentation whose pushout along reduction modulo `n` gives the displayed sequence.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.FiniteAddCommGrp

universe u

local notation "ι" => AddCommGrpCat.isFinite.ι
local notation "E" => ExactStructure.abelian FiniteAddCommGrp

variable (n : ℕ) [NeZero n]

/-- The extension of `ℤ/nℤ` by itself with middle group `ℤ/n²ℤ`. -/
def zmodSqExtension : (E).Extension (zmod.{u} n) (zmod n) :=
  let i := ZMod.mulCastHom n (pow_two n).symm
  let q := ZMod.castHom (dvd_pow_self n (by decide : 2 ≠ 0)) (ZMod n)
  have hz : AddCommGrpCat.ofHom i ≫ AddCommGrpCat.ofHom q.toAddMonoidHom = 0 := by
    have h : q.toAddMonoidHom.comp i = 0 :=
      AddMonoidHom.ext (ZMod.castHom_mulCastHom n (pow_two n).symm)
    rw [← AddCommGrpCat.ofHom_comp, h]
    exact AddCommGrpCat.homAddEquiv.symm.map_zero
  let S := ShortComplex.mk _ _ hz
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' (S.ab_exact_iff_function_exact.mpr ?_)
      ((AddCommGrpCat.mono_iff_injective _).mpr ?_) ((AddCommGrpCat.epi_iff_surjective _).mpr ?_)
    all_goals
      simp only [S, ConcreteCategory.hom_ofHom, RingHom.toAddMonoidHom_eq_coe, i, q]
    · exact ZMod.exact_mulCastHom_castHom n (pow_two n).symm
    · exact ZMod.mulCastHom_injective _ _ (NeZero.ne n)
    · exact ZMod.castHom_surjective (dvd_pow_self n (by decide : 2 ≠ 0))
  let T := S.map AddCommGrpCat.uliftFunctor.{u, 0}
  let f : zmod n ⟶ zmod (n ^ 2) := ObjectProperty.homMk T.f
  let g : zmod (n ^ 2) ⟶ zmod n := ObjectProperty.homMk T.g
  have hf : f ≫ g = 0 := by
    apply (ι).map_injective
    rw [Functor.map_comp, Functor.map_zero]
    -- The inclusion takes the full-subcategory morphisms back to the maps of `T`.
    exact T.zero
  ⟨zmod (n ^ 2), f, g, hf, (ExactStructure.abelian_conflation _).mpr
    (ShortExact.reflects_shortExact_of_faithful ι
      (hS.map_of_exact AddCommGrpCat.uliftFunctor.{u, 0}))⟩

/-- The middle group of the cyclic-square extension is `ℤ/n²ℤ`. -/
@[simp]
theorem zmodSqExtension_obj : (zmodSqExtension.{u} n).obj = zmod (n ^ 2) :=
  (rfl)

/-- After identifying the middle group with `ℤ/n²ℤ`, the first map multiplies by `n`. -/
@[simp]
theorem zmodSqExtension_f_comp_eqToHom :
    (zmodSqExtension.{u} n).f ≫ eqToHom (zmodSqExtension_obj n) =
      ObjectProperty.homMk (AddCommGrpCat.uliftFunctor.{u, 0}.map
        (AddCommGrpCat.ofHom (ZMod.mulCastHom n (pow_two n).symm))) :=
  (rfl)

/-- After identifying the middle group with `ℤ/n²ℤ`, the second map reduces modulo `n`. -/
@[simp]
theorem zmodSqExtension_eqToHom_comp_g :
    eqToHom (zmodSqExtension_obj.{u} n).symm ≫ (zmodSqExtension.{u} n).g =
      ObjectProperty.homMk (AddCommGrpCat.uliftFunctor.{u, 0}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (dvd_pow_self n (by decide : 2 ≠ 0)) (ZMod n)).toAddMonoidHom)) :=
  (rfl)

/-- The first map of the cyclic-square extension sends `1` to `n` in its cyclic middle group. -/
@[simp↓]
theorem zmodSqExtension_f_one :
    ((zmodSqExtension.{u} n).f ≫ eqToHom (zmodSqExtension_obj n)).hom (ULift.up 1) =
      ULift.up (n : ZMod (n ^ 2)) := by
  rw [zmodSqExtension_f_comp_eqToHom]
  have h : ZMod.mulCastHom n (pow_two n).symm (1 : ZMod n) = (n : ZMod (n ^ 2)) := by
    simpa only [Int.cast_one, one_mul] using ZMod.mulCastHom_intCast n (pow_two n).symm 1
  -- The map of the universe-lift functor lifts the value of the original homomorphism.
  exact congrArg ULift.up h

/-- The second map of the cyclic-square extension sends the lifted generator to the generator. -/
@[simp↓]
theorem zmodSqExtension_g_one :
    (eqToHom (zmodSqExtension_obj.{u} n).symm ≫ (zmodSqExtension.{u} n).g).hom
      (ULift.up 1) = ULift.up (1 : ZMod n) := by
  rw [zmodSqExtension_eqToHom_comp_g]
  -- The map of the universe-lift functor lifts the value of the original homomorphism.
  exact congrArg ULift.up (map_one (ZMod.castHom (dvd_pow_self n (by decide : 2 ≠ 0)) (ZMod n)))

private abbrev zmodSqExtensionIso : (zmodSqExtension.{u} n).obj ≅ zmod (n ^ 2) :=
  eqToIso (zmodSqExtension_obj n)

private theorem zmodSqExtension_f_comp_apply_one {Y : FiniteAddCommGrp.{u}}
    (g : zmod (n ^ 2) ⟶ Y) :
    ((zmodSqExtension n).f ≫ (zmodSqExtensionIso n).hom ≫ g).hom (ULift.up 1) =
      g.hom (ULift.up (n : ZMod (n ^ 2))) := by
  rw [← Category.assoc, ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.comp_apply,
    eqToIso.hom, zmodSqExtension_f_one]

private theorem zmodSqExtension_f_comp_eq_zero (g : (zmodSqExtension.{u} n).obj ⟶ zmod n) :
    (zmodSqExtension n).f ≫ g = 0 := by
  rw [← (zmodSqExtensionIso n).hom_inv_id_assoc g]
  apply zmod_hom_ext
  -- Every map to the left endpoint kills multiples of `n`.
  rw [zmodSqExtension_f_comp_apply_one]
  rw [ObjectProperty.zero_hom]
  have h : ULift.up (n : ZMod (n ^ 2)) = n • ULift.up (1 : ZMod (n ^ 2)) :=
    congrArg ULift.up (nsmul_one n).symm
  rw [h, map_nsmul, ZModModule.char_nsmul_eq_zero n]
  exact (AddCommGrpCat.zero_apply _ _ _).symm

private theorem exists_zmodSqExtension_pushout
    (e : (E).Extension (zmod.{u} n) (zmod n)) :
    ∃ a : ZMod n, (ExactStructure.Ext1.mk (zmodSqExtension n)).pushout (zmodMul n a) =
      ExactStructure.Ext1.mk e := by
  have he : (e.shortComplex.map ι).ShortExact := e.shortExact.map_of_exact ι
  have hmaps : Function.Exact e.f.hom e.g.hom ∧ Function.Surjective e.g.hom := by
    simpa only [ShortComplex.map_f, ShortComplex.map_g, ObjectProperty.ι_map,
      ExactStructure.Extension.shortComplex] using
      And.intro ((e.shortComplex.map ι).ab_exact_iff_function_exact.mp he.exact) he.ab_surjective_g
  obtain ⟨y, hy⟩ := hmaps.2 (ULift.up (1 : ZMod n))
  have hy' : e.g.hom (n • y) = 0 := by
    rw [map_nsmul, ZModModule.char_nsmul_eq_zero n]
  obtain ⟨a, ha⟩ := (hmaps.1 (n • y)).mp hy'
  have hy'' : (n ^ 2) • y = 0 := by
    rw [pow_two, mul_nsmul, ← ha, ← map_nsmul, ZModModule.char_nsmul_eq_zero n, map_zero]
  let lift : zmod (n ^ 2) ⟶ e.obj :=
    ObjectProperty.homMk (AddCommGrpCat.ofHom
      ((ZMod.lift (n ^ 2) ⟨zmultiplesHom _ y, by
        rw [zmultiplesHom_apply, natCast_zsmul, hy'']⟩).comp AddEquiv.ulift.toAddMonoidHom))
  have hlift (b : ℤ) : lift.hom (ULift.up (b : ZMod (n ^ 2))) = b • y := by
    simp only [lift, ObjectProperty.homMk_hom, ConcreteCategory.hom_ofHom,
      AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    -- The domain equivalence sends the lifted residue back to its representative in `ZMod`.
    exact (ZMod.lift_coe _ _ b).trans (zmultiplesHom_apply _ _ _)
  refine ⟨a.down, (ExactStructure.Ext1.pushout_mk_eq_pullback_mk (e := zmodSqExtension n)
    (e' := e) (c := 𝟙 _) ((zmodSqExtensionIso n).hom ≫ lift) ?_ ?_).trans
      (ExactStructure.Ext1.pullback_id _)⟩
  · apply zmod_hom_ext
    have h := hlift (n : ℤ)
    rw [Int.cast_natCast, natCast_zsmul] at h
    rw [zmodSqExtension_f_comp_apply_one]
    simp only [ObjectProperty.FullSubcategory.comp_hom, ConcreteCategory.comp_apply]
    rw [zmodMul_apply, ULift.down_up, mul_one, ULift.up_down]
    exact h.trans ha.symm
  · rw [Category.comp_id, Category.assoc, ← (zmodSqExtensionIso n).eq_inv_comp]
    apply zmod_hom_ext
    have h : lift.hom (ULift.up (1 : ZMod (n ^ 2))) = y := by
      simpa only [Int.cast_one, one_zsmul] using hlift 1
    rw [ObjectProperty.FullSubcategory.comp_hom, ConcreteCategory.comp_apply, h, hy,
      eqToIso.inv, zmodSqExtension_g_one]

/-- The self-extension group of `ℤ/nℤ` among finite abelian groups is `ℤ/nℤ` under the Baer sum.
The residue `a` gives the pushout of the sequence with middle group `ℤ/n²ℤ` along multiplication
by `a`. -/
def zmodExt1AddEquiv : ZMod n ≃+ (E).Ext1 (zmod.{u} n) (zmod n) := by
  let f : ZMod n →+ (E).Ext1 (zmod n) (zmod n) :=
    { toFun a := (ExactStructure.Ext1.mk (zmodSqExtension n)).pushout (zmodMul n a)
      map_zero' := by simp [ExactStructure.Ext1.pushout_zero]
      map_add' a b := by rw [map_add, ExactStructure.Ext1.pushout_add] }
  refine AddEquiv.ofBijective f ⟨(AddMonoidHom.ker_eq_bot_iff f).mp ?_, ?_⟩
  · refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha ↦ ?_
    have h := (ExactStructure.Ext1.mk_pushout_eq_zero_iff (zmodSqExtension n)
      (zmodMul n a)).mp (AddMonoidHom.mem_ker.mp ha)
    obtain ⟨g, hg⟩ := h
    have hz : zmodMul n a = 0 := hg.symm.trans (zmodSqExtension_f_comp_eq_zero n g)
    exact zmodMul_injective n (hz.trans (map_zero (zmodMul n)).symm)
  · intro ξ
    induction ξ using ExactStructure.Ext1.induction with
    | h e => exact exists_zmodSqExtension_pushout n e

/-- The comparison sends a residue to the pushout along multiplication by that residue. -/
@[simp]
theorem zmodExt1AddEquiv_apply (a : ZMod n) :
    zmodExt1AddEquiv.{u} n a =
      (ExactStructure.Ext1.mk (zmodSqExtension n)).pushout (zmodMul n a) :=
  (rfl)

/-- The residue `1` represents the extension with cyclic middle group of order `n²`. -/
theorem zmodExt1AddEquiv_one :
    zmodExt1AddEquiv.{u} n 1 = ExactStructure.Ext1.mk (zmodSqExtension n) := by
  rw [zmodExt1AddEquiv_apply, zmodMul_one, ExactStructure.Ext1.pushout_id]

/-- There are exactly `n` self-extension classes of the cyclic group of order `n`. -/
@[simp]
theorem natCard_ext1_zmod : Nat.card ((E).Ext1 (zmod.{u} n) (zmod n)) = n :=
  (Nat.card_congr (zmodExt1AddEquiv n).toEquiv.symm).trans (Nat.card_zmod n)

/-- The cyclic-square sequence represents a nonzero class for a nontrivial cyclic group. -/
theorem mk_zmodSqExtension_ne_zero [Nontrivial (ZMod n)] :
    ExactStructure.Ext1.mk (zmodSqExtension.{u} n) ≠ 0 := by
  rw [← zmodExt1AddEquiv_one, ← map_zero (zmodExt1AddEquiv n)]
  exact fun h ↦ one_ne_zero ((zmodExt1AddEquiv n).injective h)

/-- The identity of a nontrivial finite cyclic group acts nontrivially on Yoneda extensions. -/
theorem id_notMem_projectivelyTrivialIdeal_zmod [Nontrivial (ZMod n)] :
    𝟙 (zmod.{u} n) ∉ (E).projectivelyTrivialIdeal.hom (zmod n) (zmod n) := by
  intro h
  have hz := ExactStructure.mem_projectivelyTrivialIdeal_iff_forall_ext1.mp h
    (zmod n) (ExactStructure.Ext1.mk (zmodSqExtension n))
  exact mk_zmodSqExtension_ne_zero n (by simpa only [ExactStructure.Ext1.pullback_id] using hz)

end TauCeti.FiniteAddCommGrp
