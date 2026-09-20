/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Correspondence
import TauCeti.RepresentationTheory.Irreducible

/-!
# Injectivity in the Clifford correspondence

Let `N` be a normal subgroup of a finite group `G`, let `V` be an irreducible representation of
`N`, and put `T = inertia V`.  Induction from `T` to `G` sends irreducible representations lying
over `V` to irreducible representations lying over `V`.  This file proves the uniqueness half of
the Clifford correspondence: two such representations of `T` are isomorphic whenever their
inductions to `G` are isomorphic.

The proof uses the off-diagonal Mackey intertwining formula.  A Mackey term indexed by
`s ∉ T` vanishes because the restrictions of both representations are spanned by copies of `V`,
whereas conjugation by `s` moves `V` out of its isomorphism class.  The identity double coset then
recovers the intertwining space over `T`, so an isomorphism between the induced representations
forces an isomorphism before induction.

## Main statements

* `FDRep.subsingleton_hom_res_mackeyToH_of_not_mem_inertia`: the off-inertia Mackey
  intertwining space between two irreducibles lying over `V` is trivial.
* `FDRep.nonempty_iso_of_indFDRep_iso_of_liesOver_inertia`: induction from the inertia group is
  injective on the relevant irreducible isomorphism classes.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11.
-/

public section

open CategoryTheory
open Representation (IntertwiningMap)

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- On `N`, a Mackey intertwiner between representations of `inertia V` intertwines the
restriction of its source with the conjugate by the Mackey representative of the restriction of
its target. -/
private theorem mackey_hom_apply_inclusion {V : FDRep k N}
    {A B : FDRep k (inertia V)} {s : G}
    (phi : resFDRep ((mackeySubgroup s (inertia V) (inertia V)).subgroupOf (inertia V)) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s (inertia V) (inertia V))).obj B)
    (n : N) (a : A) :
    phi.hom.hom.hom (A.ρ (Subgroup.inclusion (le_inertia V) n) a) =
      B.ρ (Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n))
        (phi.hom.hom.hom a) := by
  have hn : ((Subgroup.inclusion (le_inertia V) n : inertia V) : G) ∈
      mackeySubgroup s (inertia V) (inertia V) :=
    mem_mackeySubgroup_iff.mpr ⟨le_inertia V n.2, le_inertia V (by
      simpa using (inferInstance : N.Normal).conj_mem' _ n.2 s)⟩
  have hy : mackeyToH s _ _ ⟨_, Subgroup.mem_subgroupOf.mpr hn⟩ =
      Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n) :=
    Subtype.ext (by simp)
  have h := congrArg (fun chi => chi.hom.hom a) (phi.comm ⟨_, Subgroup.mem_subgroupOf.mpr hn⟩)
  simp only [FGModuleCat.obj_carrier, ObjectProperty.FullSubcategory.comp_hom,
    ModuleCat.hom_comp, FDRep.hom_hom_action_ρ, LinearMap.coe_comp] at h
  have hres (y) : FDRep.ρ ((Action.res (FGModuleCat k) (mackeyToH s _ _)).obj B) y =
      B.ρ (mackeyToH s (inertia V) (inertia V) y) := rfl
  rw [hres, hy] at h
  exact h

/-- **Off-inertia Mackey terms vanish.** If `A` and `B` are irreducible representations of the
inertia group of `V`, both lying over `V`, then an intertwiner from the relevant restriction of
`A` to the Mackey conjugate of `B` is zero whenever the representative is outside `inertia V`. -/
theorem subsingleton_hom_res_mackeyToH_of_not_mem_inertia [Finite G] [IsAlgClosed k] [CharZero k]
    (V : FDRep k N) [Simple V] (A B : FDRep k (inertia V)) [Simple A] [Simple B]
    (hA : A.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hB : B.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    {s : G} (hs : s ∉ inertia V) :
    Subsingleton
      (resFDRep ((mackeySubgroup s (inertia V) (inertia V)).subgroupOf (inertia V)) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s (inertia V) (inertia V))).obj B) := by
  let hV : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  let _ : Representation.IsIrreducible V.ρ := hV
  let _ : Nontrivial V := _root_.Representation.IsIrreducible.nontrivial hV
  obtain ⟨fA, hfA⟩ := liesOver_iff.mp hA
  obtain ⟨fB, hfB⟩ := liesOver_iff.mp hB
  have hspanA : ⨆ g : IntertwiningMap V.ρ
      (A.ρ.comp (Subgroup.inclusion (le_inertia V))),
      LinearMap.range g.toLinearMap = ⊤ := by
    refine V.iSup_range_intertwiningMap_inertia_eq_top A
      ((FDRep.forget₂HomLinearEquiv _ _).symm fA).hom fun hzero => hfA ?_
    apply Action.Hom.ext
    ext v
    exact DFunLike.congr_fun hzero v
  have hspanB : ⨆ g : IntertwiningMap V.ρ
      (B.ρ.comp (Subgroup.inclusion (le_inertia V))),
      LinearMap.range g.toLinearMap = ⊤ := by
    refine V.iSup_range_intertwiningMap_inertia_eq_top B
      ((FDRep.forget₂HomLinearEquiv _ _).symm fB).hom fun hzero => hfB ?_
    apply Action.Hom.ext
    ext v
    exact DFunLike.congr_fun hzero v
  have hkillA {W : Type u} [AddCommGroup W] [Module k W] (l : A →ₗ[k] W)
      (hl : ∀ g : IntertwiningMap V.ρ
        (A.ρ.comp (Subgroup.inclusion (le_inertia V))),
        l ∘ₗ g.toLinearMap = 0) : l = 0 := by
    refine LinearMap.ker_eq_top.mp (top_le_iff.mp (hspanA ▸ iSup_le fun g => ?_))
    rintro _ ⟨v, rfl⟩
    exact DFunLike.congr_fun (hl g) v
  have hkillB {W : Type u} [AddCommGroup W] [Module k W] (l : B →ₗ[k] W)
      (hl : ∀ g : IntertwiningMap V.ρ
        (B.ρ.comp (Subgroup.inclusion (le_inertia V))),
        l ∘ₗ g.toLinearMap = 0) : l = 0 := by
    refine LinearMap.ker_eq_top.mp (top_le_iff.mp (hspanB ▸ iSup_le fun g => ?_))
    rintro _ ⟨v, rfl⟩
    exact DFunLike.congr_fun (hl g) v
  let vanish (phi :
      resFDRep ((mackeySubgroup s (inertia V) (inertia V)).subgroupOf (inertia V)) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s (inertia V) (inertia V))).obj B) :
      phi = 0 := by
    let linearPhi : A →ₗ[k] B := phi.hom.hom.hom
    have hphi (n : N) (a : A) :
        linearPhi (A.ρ (Subgroup.inclusion (le_inertia V) n) a) =
          B.ρ (Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n))
            (linearPhi a) :=
      mackey_hom_apply_inclusion phi n a
    suffices linearPhi = 0 by
      apply Action.Hom.ext
      ext a
      exact DFunLike.congr_fun this a
    by_contra hphiZero
    obtain ⟨g, hg⟩ : ∃ g : IntertwiningMap V.ρ
        (A.ρ.comp (Subgroup.inclusion (le_inertia V))),
        linearPhi ∘ₗ g.toLinearMap ≠ 0 := by
      by_contra! h
      exact hphiZero (hkillA linearPhi h)
    let h : IntertwiningMap V.ρ
        ((B.ρ.comp (Subgroup.inclusion (le_inertia V))).comp
          (MulAut.conjNormal s⁻¹).toMonoidHom) :=
      LinearMap.intertwiningMap_of_isIntertwiningMap _ _
        (linearPhi ∘ₗ g.toLinearMap) fun n v => by
          simp [IntertwiningMap.isIntertwining, hphi]
    have hh : Function.Injective h :=
      (_root_.Representation.IsIrreducible.injective_or_eq_zero h).resolve_right fun hzero =>
        hg (LinearMap.ext fun v => DFunLike.congr_fun hzero v)
    obtain ⟨p, hp⟩ := IntertwiningMap.exists_leftInverse_of_injective h hh
    obtain ⟨gB, hgB⟩ : ∃ gB : IntertwiningMap V.ρ
        (B.ρ.comp (Subgroup.inclusion (le_inertia V))),
        p.toLinearMap ∘ₗ gB.toLinearMap ≠ 0 := by
      by_contra! hBzero
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hz := DFunLike.congr_fun (hkillB p.toLinearMap hBzero) (h v)
      rw [LinearMap.zero_apply, IntertwiningMap.coe_toLinearMap, ← IntertwiningMap.comp_apply,
        hp, IntertwiningMap.id_apply] at hz
      exact hv hz
    let qLinear : V →ₗ[k] V := p.toLinearMap ∘ₗ gB.toLinearMap
    have qLinear_apply (v : V) : qLinear v = p (gB v) := rfl
    let q : IntertwiningMap V.ρ (conjNormalFDRep s⁻¹ V).ρ :=
      LinearMap.intertwiningMap_of_isIntertwiningMap _ _ qLinear fun n v => by
        have hp' := IntertwiningMap.isIntertwining _ _ p (MulAut.conjNormal s n) (gB v)
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at hp'
        have hconj : (conjNormalFDRep s⁻¹ V).ρ n =
            V.ρ (MulAut.conjNormal s n) := by
          rw [conjNormalFDRep_ρ, inv_inv]
        refine (qLinear_apply _).trans <|
          ((congrArg p (IntertwiningMap.isIntertwining _ _ gB n v)).trans hp').trans ?_
        rw [hconj]
        exact congrArg (V.ρ (MulAut.conjNormal s n)) (qLinear_apply v).symm
    have hq : q ≠ 0 := fun hzero =>
      hgB (LinearMap.ext fun v => DFunLike.congr_fun hzero v)
    exact hs (by simpa using (inertia V).inv_mem (q.mem_inertia hq))
  exact ⟨fun phi psi => (vanish phi).trans (vanish psi).symm⟩

/-- **Injectivity in the Clifford correspondence.** Two irreducible representations of
`inertia V` lying over `V` are isomorphic if their inductions to `G` are isomorphic. -/
theorem nonempty_iso_of_indFDRep_iso_of_liesOver_inertia [Finite G] [IsAlgClosed k] [CharZero k]
    (V : FDRep k N) [Simple V] (A B : FDRep k (inertia V)) [Simple A] [Simple B]
    (hA : A.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hB : B.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hInd : Nonempty (indFDRep A ≅ indFDRep B)) : Nonempty (A ≅ B) := by
  classical
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (inertia V : Set G) (inertia V : Set G))
  let _ : Simple (indFDRep A) := simple_indFDRep_of_inertia V A hA
  let _ : Simple (indFDRep B) := simple_indFDRep_of_inertia V B hB
  by_contra hAB
  have hBA : ¬ Nonempty (B ≅ A) := fun ⟨e⟩ ↦ hAB ⟨e.symm⟩
  have hterm (D : DoubleCoset.Quotient (inertia V : Set G) (inertia V : Set G)) :
      Module.finrank k
          (resFDRep ((mackeySubgroup D.out (inertia V) (inertia V)).subgroupOf (inertia V)) B ⟶
            (Action.res (FGModuleCat k)
              (mackeyToH D.out (inertia V) (inertia V))).obj A) = 0 := by
    by_cases hs : D.out ∈ inertia V
    · have hchange := finrank_hom_res_mackeyToH_mul_left_mul_right B A hs
          (one_mem (inertia V)) 1
      have hrepresentative : D.out * 1 * 1 = D.out := by simp
      rw [hrepresentative] at hchange
      rw [hchange, finrank_hom_res_mackeyToH_one, FDRep.finrank_hom_simple_simple,
        ite_eq_right hBA]
    · let _ := subsingleton_hom_res_mackeyToH_of_not_mem_inertia V B A hB hA hs
      exact Module.finrank_zero_of_subsingleton
  have hzero : Module.finrank k (indFDRep A ⟶ indFDRep B) = 0 := by
    rw [finrank_hom_indFDRep_mackey B A, Finset.sum_eq_zero fun D _ ↦ hterm D]
  rw [FDRep.finrank_hom_simple_simple, ite_eq_left hInd] at hzero
  exact one_ne_zero hzero

end FDRep
