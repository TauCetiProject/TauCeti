/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.LiesOver
public import TauCeti.RepresentationTheory.Induction.Mackey.Irreducible
public import TauCeti.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Induction from the inertia group

Let `N` be a normal subgroup of a finite group `G`, let `V` be an irreducible representation of
`N`, and let `T = inertia V` be its inertia group.  An irreducible representation `U` of `T`
**lies over** `V` when `V` occurs in the restriction of `U` to `N`, that is, when there is a
nonzero intertwiner `V ⟶ Res_N U` (`FDRep.LiesOver`).  This file proves the Clifford
correspondence's irreducibility theorem: for such a `U` the induced representation `Ind_T^G U` is
irreducible (`FDRep.simple_indFDRep_of_inertia`).

The proof reads the Mackey irreducibility criterion `TauCeti.simple_indFDRep_iff`.  Two facts
about the restriction of `U` to `N` do the work.

* The images of the intertwiners `V → Res_N U` span `U`
  (`FDRep.iSup_range_intertwiningMap_inertia_eq_top`).  Their span is stable under `T`, because
  translating such an image by `t ∈ T` gives the image of an intertwiner out of `{}^t V ≅ V`; it
  is nonzero because `U` lies over `V`; and `U` is irreducible, so the span is everything.
* A Mackey intertwiner `ψ` at `s ∉ T` intertwines, on `N`, the restriction `Res_N U` with its
  conjugate by `s`.  If `ψ ≠ 0` it is nonzero on some copy of `V`, which it therefore embeds in
  that conjugate.  Maschke's theorem
  (`Representation.IntertwiningMap.exists_leftInverse_of_injective`) retracts the embedding, and
  as the copies of `V` span `U` the retraction is nonzero on some copy of `V`.  The composite is a
  nonzero intertwiner from `V` to `{}^{s⁻¹} V`, so Schur's lemma puts `s⁻¹`, hence `s`, in `T`
  (`Representation.IntertwiningMap.mem_inertia`).

The spanning argument uses `le_inertia V`, while the Mackey argument derives membership in
`inertia V` from a nonzero intertwiner and contradicts `s ∉ inertia V`.

## Main statements

* `FDRep.iSup_range_intertwiningMap_inertia_eq_top`: if `U` lies over `V`, the images of the
  intertwiners `V → Res_N U` span `U`.
* `FDRep.subsingleton_hom_res_mackeyToH_of_not_mem_inertia`: an off-inertia Mackey
  intertwining space between two irreducibles lying over `V` is trivial.
* `FDRep.simple_indFDRep_of_inertia`: **induction from the inertia group preserves
  irreducibility** for representations lying over `V`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11.
-/

public section

open CategoryTheory
open scoped Pointwise
open Representation (IntertwiningMap)

universe u

namespace FDRep

open TauCeti

section Inertia

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- An element `t` of the inertia group of `V` gives a linear automorphism of `V` carrying the
action of `n` to the action of `t⁻¹ n t`: the isomorphism `{}^t V ≅ V`, read on the common
underlying space. -/
private theorem exists_linearEquiv_of_mem_inertia {V : FDRep k N} {t : G} (ht : t ∈ inertia V) :
    ∃ ε : V ≃ₗ[k] V, ∀ (n : N) (v : V),
      ε (V.ρ n v) = V.ρ (MulAut.conjNormal t⁻¹ n) (ε v) := by
  obtain ⟨e⟩ := mem_inertia_iff.1 ht
  -- `{}^t V` has the same underlying space as `V` (`conjNormalFDRep_V`), so `e⁻¹` is itself a
  -- linear automorphism of `V`.
  let ε : V ≃ₗ[k] conjNormalFDRep t V := isoToLinearEquiv e.symm
  refine ⟨ε, fun n v => ?_⟩
  have h := DFunLike.congr_fun (FDRep.Iso.conj_ρ e.symm n) (isoToLinearEquiv e.symm v)
  have hv := congrArg (fun w => isoToLinearEquiv e.symm (V.ρ n w))
    ((isoToLinearEquiv e.symm).symm_apply_apply v)
  rw [← conjNormalFDRep_ρ]
  exact (h.trans hv).symm

/-- **The images of intertwiners from `V` span a representation of the inertia group lying over
`V`.**  If `U` is an irreducible representation of the inertia group of `V` and some intertwiner
`V → Res_N U` is nonzero, then the images of all such intertwiners span `U`. -/
theorem iSup_range_intertwiningMap_inertia_eq_top (V : FDRep k N) (U : FDRep k (inertia V))
    [Simple U] (f : IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V))))
    (hf : f ≠ 0) :
    ⨆ g : IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V))),
      LinearMap.range g.toLinearMap = ⊤ := by
  have hU := FDRep.isIrreducible_of_simple U
  set J := ⨆ g : IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V))),
    LinearMap.range g.toLinearMap
  -- `J` is stable under the inertia group: translating the image of `g` by `t` gives the image of
  -- `ρ t ∘ g ∘ ε`, where `ε` is the automorphism of `V` witnessing `{}^t V ≅ V`.
  have hstable (t : inertia V) {x : U} (hx : x ∈ J) : U.ρ t x ∈ J := by
    obtain ⟨ε, hε⟩ := exists_linearEquiv_of_mem_inertia t.2
    let g' (g : IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V)))) :
        IntertwiningMap V.ρ (U.ρ.comp (Subgroup.inclusion (le_inertia V))) :=
      LinearMap.intertwiningMap_of_isIntertwiningMap _ _
        (U.ρ t ∘ₗ g.toLinearMap ∘ₗ ε.toLinearMap) fun n v => by
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, IntertwiningMap.coe_toLinearMap,
            hε, IntertwiningMap.isIntertwining, MonoidHom.coe_comp, Function.comp_apply]
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          exact Subtype.ext (by simp [mul_assoc])
    refine Submodule.iSup_induction _ (motive := fun x => U.ρ t x ∈ J) hx ?_ ?_ ?_
    · rintro g _ ⟨v, rfl⟩
      have hv : U.ρ t (g.toLinearMap v) = g' g (ε.symm v) := by
        simp [g']
      rw [hv]
      exact Submodule.mem_iSup_of_mem (g' g) (LinearMap.mem_range_self _ _)
    · simp
    · intro x y hx hy
      rw [map_add]
      exact J.add_mem hx hy
  let S : Subrepresentation U.ρ := ⟨J, fun t _ hx => hstable t hx⟩
  rcases hU.eq_bot_or_eq_top S with h | h
  · refine absurd (IntertwiningMap.ext (LinearMap.ext fun v => ?_)) hf
    have hv : f v ∈ S.toSubmodule := Submodule.mem_iSup_of_mem f (LinearMap.mem_range_self _ v)
    rw [h] at hv
    exact hv
  · exact congrArg Subrepresentation.toSubmodule h

/-- A linear map out of an irreducible representation of `inertia V` lying over `V` is zero if it
vanishes on every copy of `V` in the restriction to `N`. -/
theorem linearMap_eq_zero_of_comp_intertwiningMap_eq_zero (V : FDRep k N)
    (U : FDRep k (inertia V)) [Simple U]
    (hU : U.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    {W : Type u} [AddCommGroup W] [Module k W] (l : U →ₗ[k] W)
    (hl : ∀ g : IntertwiningMap V.ρ
      (U.ρ.comp (Subgroup.inclusion (le_inertia V))), l ∘ₗ g.toLinearMap = 0) :
    l = 0 := by
  obtain ⟨f, hf⟩ := liesOver_iff.mp hU
  have hspan := V.iSup_range_intertwiningMap_inertia_eq_top U
    ((FDRep.forget₂HomLinearEquiv _ _).symm f).hom fun hzero => hf (by
      apply Action.Hom.ext
      ext v
      exact DFunLike.congr_fun hzero v)
  refine LinearMap.ker_eq_top.mp (top_le_iff.mp (hspan ▸ iSup_le fun g => ?_))
  rintro _ ⟨v, rfl⟩
  exact DFunLike.congr_fun (hl g) v

/-- On the normal subgroup `N`, a Mackey intertwiner at `s` intertwines the restriction of its
source to `N` with the conjugate by `s` of the restriction of its target: the Mackey subgroup
contains `N`, and on `N` the map `TauCeti.mackeyToH` is conjugation by `s⁻¹`. -/
theorem mackey_hom_apply_inclusion {V : FDRep k N} {A B : FDRep k (inertia V)} {s : G}
    (φ : resFDRep ((mackeySubgroup s (inertia V) (inertia V)).subgroupOf (inertia V)) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s (inertia V) (inertia V))).obj B)
    (n : N) (a : A) :
    φ.hom.hom.hom (A.ρ (Subgroup.inclusion (le_inertia V) n) a) =
      B.ρ (Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n)) (φ.hom.hom.hom a) := by
  have hn : ((Subgroup.inclusion (le_inertia V) n : inertia V) : G) ∈ mackeySubgroup s _ _ :=
    mem_mackeySubgroup_iff.mpr ⟨le_inertia V n.2, le_inertia V (by
      simpa using (inferInstance : N.Normal).conj_mem' _ n.2 s)⟩
  have hy : mackeyToH s _ _ ⟨_, Subgroup.mem_subgroupOf.mpr hn⟩ =
      Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n) :=
    Subtype.ext (by simp)
  have h := congrArg (fun χ => χ.hom.hom a) (φ.comm ⟨_, Subgroup.mem_subgroupOf.mpr hn⟩)
  simp only [FGModuleCat.obj_carrier, ObjectProperty.FullSubcategory.comp_hom,
    ModuleCat.hom_comp, FDRep.hom_hom_action_ρ, LinearMap.coe_comp] at h
  have hres (y) : FDRep.ρ ((Action.res (FGModuleCat k) (mackeyToH s _ _)).obj B) y =
      B.ρ (mackeyToH s (inertia V) (inertia V) y) := by
    rw [← FDRep.hom_hom_action_ρ, ← FDRep.hom_hom_action_ρ, Action.res_obj_ρ]
    exact congrArg (fun f : B.V ⟶ B.V => f.hom.hom)
      (MonoidHom.comp_apply (Action.ρ B) (mackeyToH s (inertia V) (inertia V)) y)
  rw [hres, hy] at h
  exact h

/-- **A nonzero intertwiner into a conjugate of a representation lying over `V`.**  If `B` is an
irreducible representation of the inertia group of `V` lying over `V`, and some intertwiner from
`V` to the conjugate by `s⁻¹` of the restriction of `B` to `N` is nonzero, then `s ∈ inertia V`. -/
private theorem mem_inertia_of_intertwiningMap_conj_ne_zero [Finite N] [NeZero (Nat.card N : k)]
    {V : FDRep k N} [Simple V] {B : FDRep k (inertia V)} [Simple B]
    (hB : B.LiesOver (Subgroup.inclusion (le_inertia V)) V) {s : G}
    (h : IntertwiningMap V.ρ ((B.ρ.comp (Subgroup.inclusion (le_inertia V))).comp
      (MulAut.conjNormal s⁻¹).toMonoidHom)) (hh : h ≠ 0) : s ∈ inertia V := by
  have hV := FDRep.isIrreducible_of_simple V
  have := hV.nontrivial
  -- Schur's lemma makes `h` injective and Maschke's theorem retracts it.
  obtain ⟨p, hp⟩ := IntertwiningMap.exists_leftInverse_of_injective h
    ((hV.injective_or_eq_zero h).resolve_right hh)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hp0 : p.toLinearMap ≠ 0 := fun hzero => hv <| by
    have hpv := DFunLike.congr_fun hp v
    rwa [IntertwiningMap.comp_apply, IntertwiningMap.id_apply,
      ← IntertwiningMap.toLinearMap_apply, hzero, eq_comm] at hpv
  obtain ⟨gB, hgB⟩ :=
    not_forall.mp (mt (linearMap_eq_zero_of_comp_intertwiningMap_eq_zero V B hB _) hp0)
  exact (inertia V).inv_mem_iff.mp (p.inv_mem_inertia_of_comp_ne_zero gB hgB)

/-- **Off-inertia Mackey terms vanish.** If `A` and `B` are irreducible representations of the
inertia group of `V`, both lying over `V`, then an intertwiner from the relevant restriction of
`A` to the Mackey conjugate of `B` is zero whenever the representative is outside `inertia V`. -/
theorem subsingleton_hom_res_mackeyToH_of_not_mem_inertia [Finite N]
    [NeZero (Nat.card N : k)] (V : FDRep k N) [Simple V]
    (A B : FDRep k (inertia V)) [Simple A] [Simple B]
    (hA : A.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hB : B.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    {s : G} (hs : s ∉ inertia V) :
    Subsingleton
      (resFDRep ((mackeySubgroup s (inertia V) (inertia V)).subgroupOf (inertia V)) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s (inertia V) (inertia V))).obj B) := by
  refine subsingleton_of_forall_eq 0 fun φ => ?_
  suffices φ.hom.hom.hom = 0 from Action.Hom.ext (FGModuleCat.hom_ext this)
  -- `resFDRep` and `Action.res` keep the carriers of `A` and `B`, so `φ` is a linear map `A → B`.
  let f : A →ₗ[k] B := φ.hom.hom.hom
  refine linearMap_eq_zero_of_comp_intertwiningMap_eq_zero V A hA f fun g => ?_
  by_contra hg
  -- On `N`, `f` intertwines `Res_N A` with the conjugate by `s⁻¹` of `Res_N B`.
  have hf (n : N) (a : A) : f (A.ρ (Subgroup.inclusion (le_inertia V) n) a) =
      B.ρ (Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n)) (f a) :=
    mackey_hom_apply_inclusion φ n a
  let h : IntertwiningMap V.ρ ((B.ρ.comp (Subgroup.inclusion (le_inertia V))).comp
      (MulAut.conjNormal s⁻¹).toMonoidHom) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (f ∘ₗ g.toLinearMap) fun n v => by
      simp [IntertwiningMap.isIntertwining, hf]
  exact hs (mem_inertia_of_intertwiningMap_conj_ne_zero hB h fun hzero =>
    hg (LinearMap.ext fun v => DFunLike.congr_fun hzero v))

end Inertia

section Criterion

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {N : Subgroup G} [N.Normal]

/-- **Induction from the inertia group preserves irreducibility.**  Let `V` be an irreducible
representation of a normal subgroup `N` of a finite group `G`, over an algebraically closed field
of characteristic zero, and let `U` be an irreducible representation of the inertia group of `V`
lying over `V`, that is, with a nonzero intertwiner from `V` to the restriction of `U` to `N`.
Then the representation of `G` induced from `U` is irreducible.
-/
theorem simple_indFDRep_of_inertia (V : FDRep k N) [Simple V] (U : FDRep k (inertia V))
    [Simple U] (hU : U.LiesOver (Subgroup.inclusion (le_inertia V)) V) :
    Simple (indFDRep U) := by
  have : NeZero (Nat.card N : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  refine (simple_indFDRep_iff U).mpr ⟨inferInstance, fun s hs => ?_⟩
  exact (mackeyDisjoint_iff_subsingleton U s).mpr
    (subsingleton_hom_res_mackeyToH_of_not_mem_inertia V U U hU hU hs)

end Criterion

end FDRep
