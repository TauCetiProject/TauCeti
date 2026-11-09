/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic

/-!
# Degree-one Ext from a coproduct

In an abelian category with enough injectives, extensions from a coproduct are families
of extensions from its summands. The comparison is restriction along the coproduct inclusions;
no finiteness of the index set or exactness of coproducts is required.

This permits extension descent to be checked on summands of a presenting coproduct, for
example on the cyclic quotients presenting an ideal-power torsion module.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.6.
* The Stacks Project, Lemma 15.91.8 (05EG), for the cyclic-quotient reduction in formal glueing.
-/

public section

open CategoryTheory Limits

universe w v u t

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [EnoughInjectives C] {J : Type t} {X : J → C} {c : Cofan X}

/-- Extensions from a coproduct are families of extensions from its summands, by restriction
along the coproduct inclusions. This holds for arbitrary index sets. -/
noncomputable def coproductAddEquiv₁ (hc : IsColimit c) (Y : C) :
    Ext.{w} c.pt Y 1 ≃+ ∀ i, Ext.{w} (X i) Y 1 := by
  let f : Ext.{w} c.pt Y 1 →+ ∀ i, Ext.{w} (X i) Y 1 :=
    { toFun := fun e i ↦ (mk₀ (c.inj i)).comp e (zero_add 1)
      map_zero' := by ext i; simp
      map_add' := by intros; ext i; simp }
  -- A single injective copresentation computes every component and the coproduct at once.
  let S := TauCeti.injectiveCokernelSequence Y
  have hS := TauCeti.injectiveCokernelSequence_shortExact Y
  have hrep (Z : C) (e : Ext.{w} Z Y 1) :
      ∃ a : Z ⟶ S.X₃, (mk₀ a).comp hS.extClass (zero_add 1) = e := by
    obtain ⟨a, ha⟩ := covariant_sequence_exact₁ Z hS e (eq_zero_of_injective _) rfl
    exact ⟨addEquiv₀ a, by simpa using ha⟩
  refine AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).mpr ?_, ?_⟩
  · intro e he
    obtain ⟨a, rfl⟩ := hrep c.pt e
    have hlocal (i : J) : ∃ b : X i ⟶ S.X₂, b ≫ S.g = c.inj i ≫ a := by
      have hi := congrFun he i
      have hz : (mk₀ (c.inj i ≫ a)).comp hS.extClass (zero_add 1) = 0 := by
        simpa [f, ← mk₀_comp_mk₀_assoc] using hi
      obtain ⟨b, hb⟩ := covariant_sequence_exact₃ (X i) hS (mk₀ (c.inj i ≫ a)) rfl hz
      refine ⟨addEquiv₀ b, (mk₀_bijective _ _).1 ?_⟩
      simpa only [← mk₀_comp_mk₀, mk₀_addEquiv₀_apply] using hb
    choose b hb using hlocal
    have ha : Cofan.IsColimit.desc hc b ≫ S.g = a := by
      apply Cofan.IsColimit.hom_ext hc
      intro i
      simp [hb]
    rw [← ha, ← mk₀_comp_mk₀_assoc, hS.comp_extClass, comp_zero]
  · intro e
    choose a ha using fun i ↦ hrep (X i) (e i)
    refine ⟨(mk₀ (Cofan.IsColimit.desc hc a)).comp hS.extClass (zero_add 1), ?_⟩
    ext i
    simpa [f] using ha i

/-- The coproduct comparison restricts an extension along the indicated inclusion. -/
@[simp]
theorem coproductAddEquiv₁_apply (hc : IsColimit c) (Y : C)
    (e : Ext.{w} c.pt Y 1) (i : J) :
    coproductAddEquiv₁ hc Y e i = (mk₀ (c.inj i)).comp e (zero_add 1) :=
  (rfl)

/-- Restriction of the extension assembled from a family recovers its indicated component. -/
@[simp]
theorem mk₀_comp_coproductAddEquiv₁_symm (hc : IsColimit c) (Y : C)
    (e : ∀ i, Ext.{w} (X i) Y 1) (i : J) :
    (mk₀ (c.inj i)).comp ((coproductAddEquiv₁ hc Y).symm e) (zero_add 1) = e i :=
  congrFun ((coproductAddEquiv₁ hc Y).apply_symm_apply e) i

end CategoryTheory.Abelian.Ext
