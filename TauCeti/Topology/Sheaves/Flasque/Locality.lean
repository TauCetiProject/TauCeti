/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Order.Zorn

/-!
# Flasqueness is a local property

A sheaf is flasque when all of its restriction maps are surjective. This file proves that this
can be checked locally: if every point of `X` has an open neighbourhood `W` such that every
restriction map `F(V) → F(U)` with `U ⊆ V ⊆ W` is surjective, then every restriction map of `F`
is surjective.

The proof is the classical Zorn argument. Fix `U ⊆ V` and a section `s` over `U`, and order the
extensions of `s` to opens between `U` and `V` by extension of domain. A chain of extensions glues
to an upper bound, so there is a maximal extension `t` over some `O`. Given a point `x ∈ V`, choose
a neighbourhood `W` as above; the restriction of `t` to `O ∩ V ∩ W` extends to `V ∩ W` because
restrictions inside `W` are surjective, and the two sections glue to an extension over
`O ∪ (V ∩ W)`. Maximality forces `x ∈ O`, hence `O = V`.

The argument is carried out for presheaves of types satisfying the sheaf condition, and is then
transported to sheaves valued in a concrete category whose forgetful functor preserves limits and
reflects isomorphisms, such as sheaves of modules or of abelian groups. For such sheaves the
conclusion is expressed by Mathlib's `TopCat.Sheaf.IsFlasque`, and flasqueness is shown to be
equivalent to flasqueness of the restrictions to the members of some open cover.

## Main declarations

* `TopCat.Presheaf.IsSheaf.map_surjective_of_locally_flasque`: the locality statement for
  sheaves of types;
* `TopCat.Sheaf.map_surjective_of_locally_flasque`: the same statement for sheaves valued in a
  concrete category;
* `TopCat.Sheaf.isFlasque_of_locally_flasque`: local surjectivity of restrictions implies
  flasqueness;
* `TopCat.Sheaf.isFlasque_iff_locally_isFlasque`: a sheaf is flasque if and only if every point
  has an open neighbourhood on which its restriction is flasque.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Chapitre II, §3.
* G. E. Bredon, *Sheaf Theory*, Chapter II, §5.
-/

public section

universe u w

open CategoryTheory Limits Opposite TopologicalSpace Topology

namespace TopCat

variable {X : TopCat.{u}}

namespace Presheaf

/-- If every restriction map of a sheaf of types inside some neighbourhood of each point is
surjective, then every restriction map is surjective. -/
theorem IsSheaf.map_surjective_of_locally_flasque {F : Presheaf (Type w) X} (hF : F.IsSheaf)
    (h : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), V ≤ W →
      Function.Surjective (F.map (homOfLE hUV).op))
    {U V : Opens X} (hUV : U ≤ V) : Function.Surjective (F.map (homOfLE hUV).op) := by
  intro s
  -- The extensions of `s` to opens between `U` and `V`, preordered by extension of domain.
  let E := {p : Σ O : Opens X, F.obj (op O) //
    ∃ hUO : U ≤ p.1, p.1 ≤ V ∧ F.map (homOfLE hUO).op p.2 = s}
  let r : E → E → Prop := fun p q ↦ ∃ h : p.1.1 ≤ q.1.1, F.map (homOfLE h).op q.1.2 = p.1.2
  -- Below, `rfl` closes goals that differ only in the choice of a morphism between two opens,
  -- and these morphisms are unique.
  have r_trans {p q q' : E} (hpq : r p q) (hqq' : r q q') : r p q' := by
    obtain ⟨h, hq⟩ := hpq
    obtain ⟨h', hq'⟩ := hqq'
    exact ⟨h.trans h', by rw [← hq, ← hq', ← Functor.map_comp_apply]; rfl⟩
  have : Nonempty E := ⟨⟨⟨U, s⟩, le_rfl, hUV, by simp⟩⟩
  -- A nonempty chain of extensions glues to an extension over the union of its domains.
  have hbound (c : Set E) (hc : IsChain r c) (hne : c.Nonempty) : ∃ ub, ∀ p ∈ c, r p ub := by
    obtain ⟨p₀, hp₀⟩ := hne
    have hcompat : IsCompatible F (fun p : c ↦ p.1.1.1) (fun p ↦ p.1.1.2) := by
      intro p q
      -- Comparable extensions agree on every open inside both domains.
      have key {p q : c} (hpq : r p q) (Z : Opens X) (hp : Z ≤ p.1.1.1) (hq : Z ≤ q.1.1.1) :
          F.map (homOfLE hp).op p.1.1.2 = F.map (homOfLE hq).op q.1.1.2 := by
        obtain ⟨hle, hq'⟩ := hpq
        rw [← hq', ← Functor.map_comp_apply]
        rfl
      rcases eq_or_ne p q with rfl | hne
      · rfl
      rcases hc p.2 q.2 (Subtype.coe_injective.ne hne) with hpq | hqp
      · exact key hpq _ inf_le_left inf_le_right
      · exact (key hqp _ inf_le_right inf_le_left).symm
    obtain ⟨g, hg, -⟩ := hF.isSheafUniqueGluing_types _ hcompat
    have hle (p : c) : p.1.1.1 ≤ iSup fun p : c ↦ p.1.1.1 := le_iSup (fun p : c ↦ p.1.1.1) p
    refine ⟨⟨⟨_, g⟩, (p₀.2.1).trans (hle ⟨p₀, hp₀⟩),
      iSup_le fun p ↦ p.1.2.2.1, ?_⟩, fun p hp ↦ ⟨hle ⟨p, hp⟩, hg ⟨p, hp⟩⟩⟩
    have := congrArg (F.map (homOfLE p₀.2.1).op) (hg ⟨p₀, hp₀⟩)
    rw [← Functor.map_comp_apply] at this
    exact this.trans p₀.2.2.2
  obtain ⟨⟨⟨O, t⟩, hUO, hOV, ht⟩, hmax⟩ := exists_maximal_of_nonempty_chains_bounded hbound r_trans
  -- A maximal extension is defined on all of `V`.
  have hVO : V ≤ O := by
    intro x hx
    obtain ⟨W, hxW, hW⟩ := h x
    -- Extend `t` from `O ∩ (V ∩ W)` to `V ∩ W`.
    obtain ⟨u, hu⟩ := hW (U := O ⊓ (V ⊓ W)) inf_le_right inf_le_right
      (F.map (homOfLE inf_le_left).op t)
    -- Glue `t` and `u` to a section over `O ∪ (V ∩ W)`.
    let D : Bool → Opens X := fun b ↦ bif b then O else V ⊓ W
    let sf : ∀ b, F.obj (op (D b)) := fun b ↦ b.rec u t
    -- `t` and `u` agree on every open inside `O ∩ (V ∩ W)`.
    have key (Z : Opens X) (hZ : Z ≤ O ⊓ (V ⊓ W)) : F.map (homOfLE (hZ.trans inf_le_right)).op u =
        F.map (homOfLE (hZ.trans inf_le_left)).op t := by
      have := congrArg (F.map (homOfLE hZ).op) hu
      rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply] at this
    have hcompat : IsCompatible F D sf := by
      rintro (_ | _) (_ | _)
      · rfl
      · exact key _ (le_inf inf_le_right inf_le_left)
      · exact (key _ le_rfl).symm
      · rfl
    obtain ⟨g, hg, -⟩ := hF.isSheafUniqueGluing_types _ hcompat
    have hOD : O ≤ iSup D := le_iSup D true
    have hgs := congrArg (F.map (homOfLE hUO).op) (hg true)
    rw [← Functor.map_comp_apply] at hgs
    let q : E := ⟨⟨_, g⟩, hUO.trans hOD, iSup_le (Bool.forall_bool.mpr ⟨inf_le_left, hOV⟩),
      hgs.trans ht⟩
    obtain ⟨hDO, -⟩ := hmax q ⟨hOD, hg true⟩
    exact hDO (le_iSup D false ⟨hx, hxW⟩)
  exact ⟨F.map (homOfLE hVO).op t, Eq.trans (by rw [← Functor.map_comp_apply]; rfl) ht⟩

end Presheaf

namespace Sheaf

section Locality

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  [HasLimitsOfSize.{u, u} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]

/-- If every restriction map of a sheaf inside some neighbourhood of each point is surjective, then
every restriction map is surjective. -/
theorem map_surjective_of_locally_flasque (F : Sheaf C X)
    (h : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), V ≤ W →
      Function.Surjective (F.obj.map (homOfLE hUV).op))
    {U V : Opens X} (hUV : U ≤ V) : Function.Surjective (F.obj.map (homOfLE hUV).op) :=
  ((Presheaf.isSheaf_iff_isSheaf_comp' (CategoryTheory.forget C) F.obj).mp
    F.property).map_surjective_of_locally_flasque h hUV

/-- A sheaf is flasque as soon as every point has an open neighbourhood inside which all
restriction maps are surjective. -/
theorem isFlasque_of_locally_flasque (F : Sheaf C X)
    (h : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), V ≤ W →
      Function.Surjective (F.obj.map (homOfLE hUV).op)) :
    F.IsFlasque where
  epi i := ConcreteCategory.epi_of_surjective _ (F.map_surjective_of_locally_flasque h i.unop.le)

end Locality

section Restriction

variable {C : Type*} [Category.{u} C]

/-- The restriction of a flasque sheaf along an open embedding is flasque. -/
instance isFlasque_sheafPullback_obj {Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)
    (F : Sheaf C X) [F.IsFlasque] : ((hf.sheafPullback C).obj F).IsFlasque where
  epi i := Presheaf.IsFlasque.epi (F := F.obj) (hf.functor.map i.unop).op

/-- Flasqueness of a sheaf is local: a sheaf is flasque if and only if every point has an open
neighbourhood `W` such that the restriction of the sheaf to `W` is flasque. -/
theorem isFlasque_iff_locally_isFlasque {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).PreservesEpimorphisms] (F : Sheaf C X) :
    F.IsFlasque ↔
      ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ((W.isOpenEmbedding.sheafPullback C).obj F).IsFlasque := by
  refine ⟨fun _ x ↦ ⟨⊤, _root_.trivial, inferInstance⟩, fun h ↦ ?_⟩
  refine F.isFlasque_of_locally_flasque fun x ↦ ?_
  obtain ⟨W, hxW, hW⟩ := h x
  refine ⟨W, hxW, fun U V hUV hVW ↦ ?_⟩
  -- Opens of `X` contained in `W` are images of opens of the subspace `W`.
  have hU : W.isOpenEmbedding.functor.obj ((Opens.map W.inclusion').obj U) = U := by
    rw [Opens.functor_map_eq_inf, inf_eq_left.mpr (hUV.trans hVW)]
  have hV : W.isOpenEmbedding.functor.obj ((Opens.map W.inclusion').obj V) = V := by
    rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hVW]
  generalize (Opens.map W.inclusion').obj U = U' at hU
  generalize (Opens.map W.inclusion').obj V = V' at hV
  subst hU hV
  have hUV' : U' ≤ V' := by
    simpa only [Opens.map_functor_eq' _ W.isOpenEmbedding] using
      (Opens.map W.inclusion').monotone hUV
  have : Epi (F.obj.map (homOfLE hUV).op) := hW.epi (homOfLE hUV').op
  exact (CategoryTheory.epi_iff_surjective ((CategoryTheory.forget C).map _)).mp inferInstance

end Restriction

end Sheaf

end TopCat
