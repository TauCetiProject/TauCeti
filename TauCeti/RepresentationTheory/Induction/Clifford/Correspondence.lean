/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
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
nonzero intertwiner `V ⟶ Res_N U`.  This file proves the Clifford correspondence's
irreducibility step: for such a `U` the induced representation `Ind_T^G U` is
irreducible (`FDRep.simple_indFDRep_of_inertia`).  Showing that the induced representation lies
over `V`, and hence defining the map between the corresponding irreducible classes, remains
separate.

The proof reads the Mackey irreducibility criterion `TauCeti.simple_indFDRep_iff`.  Two facts
about the restriction of `U` to `N` do the work.

* The images of the intertwiners `V → Res_N U` span `U`
  (`FDRep.iSup_range_intertwiningMap_inertia_eq_top`).  Their span is stable under `T`, because
  translating such an image by `t ∈ T` gives the image of an intertwiner out of `{}^t V ≅ V`; it
  is nonzero because `U` lies over `V`; and `U` is irreducible, so the span is everything.
* A Mackey intertwiner `ψ` at `s ∉ T` intertwines, on `N`, the restriction `Res_N U` with its
  conjugate by `s`.  If `ψ ≠ 0` it is nonzero on some copy of `V`, which it therefore embeds in
  that conjugate.  Maschke's theorem
  (`Representation.IntertwiningMap.exists_comp_eq_id_of_injective`) retracts the embedding, and
  as the copies of `V` span `U` the retraction is nonzero on some copy of `V`.  The composite is a
  nonzero intertwiner from `V` to `{}^{s⁻¹} V`, so Schur's lemma puts `s⁻¹`, hence `s`, in `T`
  (`Representation.IntertwiningMap.mem_inertia`).

The first step uses that `T` is contained in the inertia group, the second that it contains it.
Before this gives the Clifford-correspondence map, one must also prove that the induced
representation lies over `V`.  Surjectivity and uniqueness—that every irreducible representation of
`G` lying over `V` arises this way from exactly one `U` up to isomorphism—are separate statements.

## Main statements

* `FDRep.iSup_range_intertwiningMap_inertia_eq_top`: if `U` lies over `V`, the images of the
  intertwiners `V → Res_N U` span `U`.
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
  -- `{}^t V` and `V` have the same underlying module (`conjNormalFDRep_V`), so the components of
  -- `e` are linear endomorphisms of `V`, and the identities below hold by unfolding the
  -- composition of `FDRep` morphisms.
  let ε : V →ₗ[k] V := e.inv.hom.hom.hom
  let ε' : V →ₗ[k] V := ModuleCat.Hom.hom e.hom.hom.hom
  refine ⟨LinearEquiv.ofLinearMap ε ε' ?_ ?_, fun n v => ?_⟩
  · ext v
    exact congrArg
      (fun φ : conjNormalFDRep t V ⟶ conjNormalFDRep t V => φ.hom.hom.hom v) e.hom_inv_id
  · ext v
    exact congrArg (fun φ : V ⟶ V => φ.hom.hom.hom v) e.inv_hom_id
  · have h := congrArg (fun φ => φ.hom.hom v) (e.inv.comm n)
    simp only [FGModuleCat.obj_carrier, ObjectProperty.FullSubcategory.comp_hom,
      ModuleCat.hom_comp, FDRep.hom_hom_action_ρ, LinearMap.coe_comp, Function.comp_apply,
      conjNormalFDRep_ρ, map_inv, MulAut.inv_apply] at h
    exact h

/-- **The copies of `V` span a representation of the inertia group lying over `V`.**  If `U` is an
irreducible representation of the inertia group of `V` and some intertwiner `V → Res_N U` is
nonzero, then the images of all such intertwiners span `U`. -/
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

/-- On the normal subgroup `N`, an intertwiner between the two restrictions of `U` to the Mackey
subgroup at `s` intertwines `Res_N U` with its conjugate by `s`: the Mackey subgroup contains `N`,
and on `N` the map `TauCeti.mackeyToH` is conjugation by `s⁻¹`. -/
private theorem mackey_hom_apply_inclusion {V : FDRep k N} {U : FDRep k (inertia V)} {s : G}
    (φ : resFDRep ((mackeySubgroup s (inertia V) (inertia V)).subgroupOf (inertia V)) U ⟶
      (Action.res (FGModuleCat k) (mackeyToH s (inertia V) (inertia V))).obj U)
    (n : N) (u : U) :
    φ.hom.hom.hom (U.ρ (Subgroup.inclusion (le_inertia V) n) u) =
      U.ρ (Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n)) (φ.hom.hom.hom u) := by
  have hn : ((Subgroup.inclusion (le_inertia V) n : inertia V) : G) ∈ mackeySubgroup s _ _ :=
    mem_mackeySubgroup_iff.mpr ⟨le_inertia V n.2, le_inertia V (by
      simpa using (inferInstance : N.Normal).conj_mem' _ n.2 s)⟩
  have hy : mackeyToH s _ _ ⟨_, Subgroup.mem_subgroupOf.mpr hn⟩ =
      Subgroup.inclusion (le_inertia V) (MulAut.conjNormal s⁻¹ n) :=
    Subtype.ext (by simp)
  have h := congrArg (fun χ => χ.hom.hom u) (φ.comm ⟨_, Subgroup.mem_subgroupOf.mpr hn⟩)
  simp only [FGModuleCat.obj_carrier, ObjectProperty.FullSubcategory.comp_hom,
    ModuleCat.hom_comp, FDRep.hom_hom_action_ρ, LinearMap.coe_comp] at h
  -- Both restrictions act through `U.ρ`, along the inclusion and along `mackeyToH`.
  have hres (y) : FDRep.ρ ((Action.res (FGModuleCat k) (mackeyToH s _ _)).obj U) y =
      U.ρ (mackeyToH s (inertia V) (inertia V) y) := rfl
  rw [hres, hy] at h
  exact h

end Inertia

section Criterion

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {N : Subgroup G} [N.Normal]

/-- **Induction from the inertia group preserves irreducibility.**  Let `V` be an irreducible
representation of a normal subgroup `N` of a finite group `G`, over an algebraically closed field
of characteristic zero, and let `U` be an irreducible representation of the inertia group of `V`
lying over `V`, that is, with a nonzero intertwiner from `V` to the restriction of `U` to `N`.
Then the representation of `G` induced from `U` is irreducible.

This is the irreducibility step toward the Clifford correspondence.  One must additionally prove
that the induced representation lies over `V` before induction defines a map
`Irr(inertia V ∣ V) → Irr(G ∣ V)`. -/
theorem simple_indFDRep_of_inertia (V : FDRep k N) [Simple V] (U : FDRep k (inertia V))
    [Simple U] (f : V ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia V))).obj U)
    (hf : f ≠ 0) :
    Simple (indFDRep U) := by
  have : NeZero (Nat.card N : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV := FDRep.isIrreducible_of_simple V
  have : Nontrivial V := _root_.Representation.IsIrreducible.nontrivial hV
  set ρN := U.ρ.comp (Subgroup.inclusion (le_inertia V))
  -- The copies of `V` in `Res_N U` span `U`.
  have hspan : ⨆ g : IntertwiningMap V.ρ ρN, LinearMap.range g.toLinearMap = ⊤ := by
    refine V.iSup_range_intertwiningMap_inertia_eq_top U
      ((FDRep.forget₂HomLinearEquiv _ _).symm f).hom fun h0 => hf ?_
    apply Action.Hom.ext
    ext v
    exact DFunLike.congr_fun h0 v
  -- A linear map on `U` killing every copy of `V` is zero.
  have hkill {W : Type u} [AddCommGroup W] [Module k W] (l : U →ₗ[k] W)
      (hl : ∀ g : IntertwiningMap V.ρ ρN, l ∘ₗ g.toLinearMap = 0) : l = 0 := by
    refine LinearMap.ker_eq_top.mp (top_le_iff.mp (hspan ▸ iSup_le fun g => ?_))
    rintro _ ⟨v, rfl⟩
    exact DFunLike.congr_fun (hl g) v
  refine (simple_indFDRep_iff U).mpr ⟨inferInstance, fun s hs => ?_⟩
  refine mackeyDisjoint_of_forall_eq_zero fun φ => ?_
  -- On `N`, the Mackey intertwiner `ψ` at `s` intertwines `Res_N U` with its conjugate by `s`.
  let ψ : U →ₗ[k] U := φ.hom.hom.hom
  have hψ (n : N) (u : U) : ψ (ρN n u) = ρN (MulAut.conjNormal s⁻¹ n) (ψ u) :=
    mackey_hom_apply_inclusion φ n u
  suffices hψ0 : ψ = 0 by
    apply Action.Hom.ext
    ext u
    exact DFunLike.congr_fun hψ0 u
  by_contra hψ0
  -- Some copy `g` of `V` is not killed by `ψ`.
  obtain ⟨g, hg⟩ : ∃ g : IntertwiningMap V.ρ ρN, ψ ∘ₗ g.toLinearMap ≠ 0 := by
    by_contra! h
    exact hψ0 (hkill ψ h)
  -- `ψ ∘ g` embeds `V` into the conjugate of `Res_N U`, and Maschke's theorem retracts it.
  let h : IntertwiningMap V.ρ (ρN.comp (MulAut.conjNormal s⁻¹).toMonoidHom) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (ψ ∘ₗ g.toLinearMap) fun n v => by
      simp [IntertwiningMap.isIntertwining, hψ]
  have hh : Function.Injective h :=
    (_root_.Representation.IsIrreducible.injective_or_eq_zero h).resolve_right fun h0 =>
      hg (LinearMap.ext fun v => DFunLike.congr_fun h0 v)
  obtain ⟨p, hp⟩ := IntertwiningMap.exists_comp_eq_id_of_injective h hh
  -- The retraction does not kill every copy of `V`, since it is nonzero.
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : IntertwiningMap V.ρ ρN, p.toLinearMap ∘ₗ g₂.toLinearMap ≠ 0 := by
    by_contra! h2
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have := DFunLike.congr_fun (hkill p.toLinearMap h2) (h v)
    rw [LinearMap.zero_apply, IntertwiningMap.coe_toLinearMap, ← IntertwiningMap.comp_apply, hp,
      IntertwiningMap.id_apply] at this
    exact hv this
  -- `p ∘ g₂` is a nonzero intertwiner from `V` to `{}^{s⁻¹} V`, hence an isomorphism by Schur.
  let q : IntertwiningMap V.ρ (conjNormalFDRep s⁻¹ V).ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (p.toLinearMap ∘ₗ g₂.toLinearMap)
      fun n v => by
        have hp' := IntertwiningMap.isIntertwining _ _ p (MulAut.conjNormal s n) (g₂ v)
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at hp'
        have hc : (conjNormalFDRep s⁻¹ V).ρ n = V.ρ (MulAut.conjNormal s n) := by
          rw [conjNormalFDRep_ρ, inv_inv]
        refine ((congrArg p (IntertwiningMap.isIntertwining _ _ g₂ n v)).trans hp').trans ?_
        rw [hc]
        rfl
  have hq : q ≠ 0 := fun h0 => hg₂ (LinearMap.ext fun v => DFunLike.congr_fun h0 v)
  exact hs (by simpa using (inertia V).inv_mem (q.mem_inertia hq))

end Criterion

end FDRep
