/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.Grp.FiniteAbelian.Basic
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

namespace TauCeti.FiniteAbelianGrp

local notation "ι" => AddCommGrpCat.isFinite.ι
local notation "E" => ExactStructure.abelian FiniteAbelianGrp

variable (n : ℕ) [NeZero n]

/-- The extension of `ℤ/nℤ` by itself with middle group `ℤ/n²ℤ`. -/
abbrev zmodSqExtension : (E).Extension (zmod n) (zmod n) := by
  let i := ZMod.mulCastHom n (pow_two n).symm
  let q := ZMod.castHom (dvd_pow_self n (by decide : 2 ≠ 0)) (ZMod n)
  let f : zmod n ⟶ zmod (n ^ 2) := ObjectProperty.homMk (AddCommGrpCat.ofHom i)
  let g : zmod (n ^ 2) ⟶ zmod n := ObjectProperty.homMk (AddCommGrpCat.ofHom q.toAddMonoidHom)
  have hf : f ≫ g = 0 := by
    apply (ι).map_injective
    ext x
    exact ZMod.castHom_mulCastHom n (pow_two n).symm x
  let S := ShortComplex.mk f g hf
  refine ⟨zmod (n ^ 2), f, g, hf, (ExactStructure.abelian_conflation _).mpr ?_⟩
  refine ShortExact.reflects_shortExact_of_faithful ι (?_ : (S.map ι).ShortExact)
  exact
    { exact := ((S.map ι).ab_exact_iff_function_exact).mpr
        (ZMod.exact_mulCastHom_castHom n (pow_two n).symm)
      mono_f := (AddCommGrpCat.mono_iff_injective ((S.map ι).f)).mpr
        (ZMod.mulCastHom_injective _ _ (NeZero.ne n))
      epi_g := (AddCommGrpCat.epi_iff_surjective ((S.map ι).g)).mpr
        (ZMod.castHom_surjective (dvd_pow_self n (by decide : 2 ≠ 0))) }

private theorem zmodSqExtension_f_comp_eq_zero (g : zmod (n ^ 2) ⟶ zmod n) :
    (zmodSqExtension n).f ≫ g = 0 := by
  apply zmod_hom_ext
  have h : (zmodSqExtension n).f.hom (1 : ZMod n) = (n : ZMod (n ^ 2)) := by
    simpa only [ObjectProperty.homMk_hom, ConcreteCategory.hom_ofHom, Int.cast_one, one_mul]
      using ZMod.mulCastHom_intCast n (pow_two n).symm 1
  -- Every map to the left endpoint kills multiples of `n`.
  simp only [ObjectProperty.FullSubcategory.comp_hom, ConcreteCategory.comp_apply, h]
  rw [← nsmul_one, map_nsmul, ZModModule.char_nsmul_eq_zero]
  rfl

private theorem exists_zmodSqExtension_pushout
    (e : (E).Extension (zmod n) (zmod n)) :
    ∃ a : ZMod n, (ExactStructure.Ext1.mk (zmodSqExtension n)).pushout (zmodMul n a) =
      ExactStructure.Ext1.mk e := by
  have he : (e.shortComplex.map ι).ShortExact := e.shortExact.map_of_exact ι
  obtain ⟨y, hy⟩ : ∃ y : e.obj.obj, e.g.hom y = (1 : ZMod n) :=
    he.ab_surjective_g (1 : ZMod n)
  have hy' : e.g.hom (n • y) = 0 := by
    rw [map_nsmul, hy, ZModModule.char_nsmul_eq_zero]
  obtain ⟨a, ha⟩ : ∃ a : ZMod n, e.f.hom a = n • y :=
    ((e.shortComplex.map ι).ab_exact_iff.mp he.exact) (n • y) hy'
  have hy'' : (n ^ 2) • y = 0 := by
    rw [pow_two, mul_nsmul, ← ha, ← map_nsmul, ZModModule.char_nsmul_eq_zero, map_zero]
  let lift : zmod (n ^ 2) ⟶ e.obj :=
    ObjectProperty.homMk (AddCommGrpCat.ofHom
      (ZMod.lift (n ^ 2) ⟨zmultiplesHom _ y, by
        rw [zmultiplesHom_apply, natCast_zsmul, hy'']⟩))
  have hlift (b : ℤ) : lift.hom (b : ZMod (n ^ 2)) = b • y :=
    (ZMod.lift_coe _ _ _).trans (zmultiplesHom_apply _ _ b)
  refine ⟨a, (ExactStructure.Ext1.pushout_mk_eq_pullback_mk (e := zmodSqExtension n)
    (e' := e) (c := 𝟙 _) lift ?_ ?_).trans (ExactStructure.Ext1.pullback_id _)⟩
  · apply zmod_hom_ext
    have hf : (zmodSqExtension n).f.hom (1 : ZMod n) = (n : ZMod (n ^ 2)) := by
      simpa only [ObjectProperty.homMk_hom, ConcreteCategory.hom_ofHom, Int.cast_one, one_mul]
      using ZMod.mulCastHom_intCast n (pow_two n).symm 1
    have hmul := zmodMul_apply n a 1
    rw [mul_one] at hmul
    simp only [ObjectProperty.FullSubcategory.comp_hom, ConcreteCategory.comp_apply, hf, hmul]
    have h := hlift (n : ℤ)
    rw [Int.cast_natCast, natCast_zsmul] at h
    exact h.trans ha.symm
  · apply zmod_hom_ext
    have hg : (zmodSqExtension n).g.hom (1 : ZMod (n ^ 2)) = (1 : ZMod n) :=
      map_one (ZMod.castHom (dvd_pow_self n (by decide : 2 ≠ 0)) (ZMod n))
    have h := hlift 1
    simp only [Int.cast_one, one_zsmul] at h
    simp only [ObjectProperty.FullSubcategory.comp_hom, ConcreteCategory.comp_apply,
      ObjectProperty.FullSubcategory.id_hom, h, hg, hy]
    rfl

/-- The self-extension group of `ℤ/nℤ` among finite abelian groups is `ℤ/nℤ` under the Baer sum.
The residue `a` gives the pushout of the sequence with middle group `ℤ/n²ℤ` along multiplication
by `a`. -/
def zmodExt1AddEquiv : ZMod n ≃+ (E).Ext1 (zmod n) (zmod n) := by
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
    have h := ConcreteCategory.congr_hom (congrArg (fun f ↦ (ι).map f) hz) (1 : ZMod n)
    exact (mul_one a).symm.trans ((zmodMul_apply n a 1).symm.trans h)
  · intro ξ
    induction ξ using ExactStructure.Ext1.induction with
    | h e => exact exists_zmodSqExtension_pushout n e

/-- The comparison sends a residue to the pushout along multiplication by that residue. -/
@[simp]
theorem zmodExt1AddEquiv_apply (a : ZMod n) :
    zmodExt1AddEquiv n a =
      (ExactStructure.Ext1.mk (zmodSqExtension n)).pushout (zmodMul n a) :=
  (rfl)

/-- The residue `1` represents the extension with cyclic middle group of order `n²`. -/
theorem zmodExt1AddEquiv_one :
    zmodExt1AddEquiv n 1 = ExactStructure.Ext1.mk (zmodSqExtension n) := by
  rw [zmodExt1AddEquiv_apply, zmodMul_one, ExactStructure.Ext1.pushout_id]

/-- There are exactly `n` self-extension classes of the cyclic group of order `n`. -/
@[simp]
theorem natCard_zmod_ext1 : Nat.card ((E).Ext1 (zmod n) (zmod n)) = n :=
  (Nat.card_congr (zmodExt1AddEquiv n).toEquiv.symm).trans (Nat.card_zmod n)

/-- The cyclic-square sequence represents a nonzero class for a nontrivial cyclic group. -/
theorem zmodSqExtension_class_ne_zero [Nontrivial (ZMod n)] :
    ExactStructure.Ext1.mk (zmodSqExtension n) ≠ 0 := by
  rw [← zmodExt1AddEquiv_one, ← map_zero (zmodExt1AddEquiv n)]
  exact fun h ↦ one_ne_zero ((zmodExt1AddEquiv n).injective h)

/-- The identity of a nontrivial finite cyclic group acts nontrivially on Yoneda extensions. -/
theorem id_notMem_projectivelyTrivialIdeal_zmod [Nontrivial (ZMod n)] :
    𝟙 (zmod n) ∉ (E).projectivelyTrivialIdeal.hom (zmod n) (zmod n) := by
  intro h
  have hz := ExactStructure.mem_projectivelyTrivialIdeal_iff_forall_ext1.mp h
    (zmod n) (ExactStructure.Ext1.mk (zmodSqExtension n))
  exact zmodSqExtension_class_ne_zero n (by simpa only [ExactStructure.Ext1.pullback_id] using hz)

end TauCeti.FiniteAbelianGrp
