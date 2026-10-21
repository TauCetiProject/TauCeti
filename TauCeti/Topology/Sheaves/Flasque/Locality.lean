/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Order.Zorn

/-!
# Flasqueness is a local property

Let `F` be a sheaf on a topological space `X`, with values in a concrete category in which
sections can be glued (for instance sets, abelian groups or modules). Suppose that every point
of `X` has an open neighbourhood `W` such that every restriction map `F(V) ⟶ F(U)` with
`U ≤ V ≤ W` is surjective. Then every restriction map of `F` is surjective: flasqueness can be
checked on an open cover.

This is how flasqueness of a sheaf defined by a local construction is established: one proves
surjectivity of restrictions inside each chart, and the results here globalise it.

## Main declarations

* `TopCat.Sheaf.surjective_map_of_local_extension`: if restrictions are surjective inside the
  members of an open cover, then every restriction map is surjective;
* `TopCat.Sheaf.isFlasque_of_local_extension`: the same conclusion phrased with Mathlib's
  `TopCat.Sheaf.IsFlasque`;
* `TopCat.Sheaf.isFlasque_iff_local_extension`: when the forgetful functor preserves
  epimorphisms (as for sets, abelian groups and modules), this local condition characterises
  flasque sheaves.

## Implementation notes

Fix `U ≤ V` and a section `s` over `U`. Extensions of `s` to opens `O` with `U ≤ O ≤ V` are
preordered by extension of domains. Every chain has an upper bound, obtained by gluing the
sections of the chain over the union of their domains, so Zorn's lemma gives a maximal
extension. Its domain is all of `V`: given `x ∈ V` with a neighbourhood `W` as above, the
restriction of the maximal extension to `O ⊓ W ⊓ V` extends to `W ⊓ V`, and gluing it with the
maximal extension gives an extension to `O ⊔ (W ⊓ V)`, so `x ∈ O` by maximality.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, chapitre II, §3.1.
* G. E. Bredon, *Sheaf Theory*, chapter II, §5 (flabby sheaves).
-/

public section

universe x

open CategoryTheory Opposite TopologicalSpace TopCat.Presheaf
open scoped AlgebraicGeometry

namespace TopCat.Sheaf

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {X : TopCat.{x}} (F : TopCat.Sheaf C X)

/-- Agreement of two sections on the intersection of their domains does not depend on the order
of the intersection. -/
private lemma restrict_inf_symm {U₁ U₂ : Opens X}
    (s₁ : ToType (F.obj.obj (op U₁))) (s₂ : ToType (F.obj.obj (op U₂)))
    (h : s₁ |_ (U₁ ⊓ U₂) = s₂ |_ (U₁ ⊓ U₂)) :
    s₂ |_ (U₂ ⊓ U₁) = s₁ |_ (U₂ ⊓ U₁) := by
  have := congrArg (fun t ↦ restrictOpen t (U₂ ⊓ U₁) (inf_comm U₂ U₁).le) h
  simp only [restrict_restrict] at this
  exact this.symm

/-- An extension of a fixed section `s` over `U` to a section over an open `O` lying between `U`
and `V`. -/
private structure Extension {U V : Opens X} (s : ToType (F.obj.obj (op U))) where
  /-- The domain of the extension. -/
  dom : Opens X
  le_dom : U ≤ dom
  dom_le : dom ≤ V
  /-- The extended section. -/
  sect : ToType (F.obj.obj (op dom))
  restrict_sect : sect |_ U = s

variable {F} {U V : Opens X} {s : ToType (F.obj.obj (op U))}

/-- One extension is extended by another when the domain grows and the larger section restricts
to the smaller one. -/
private def Extension.Le (a b : Extension F (V := V) s) : Prop :=
  ∃ h : a.dom ≤ b.dom, b.sect |_ a.dom = a.sect

private lemma Extension.le_trans {a b c : Extension F (V := V) s} :
    a.Le b → b.Le c → a.Le c := by
  rintro ⟨hab, hab'⟩ ⟨hbc, hbc'⟩
  exact ⟨hab.trans hbc, by rw [← restrict_restrict hab hbc, hbc', hab']⟩

variable [Limits.HasLimitsOfSize.{x, x} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [Limits.PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]

variable (F) in
/-- Two sections which agree on the intersection of their domains glue to a section on the
union. -/
private lemma exists_restrict_eq_of_restrict_inf_eq {U₁ U₂ : Opens X}
    (s₁ : ToType (F.obj.obj (op U₁))) (s₂ : ToType (F.obj.obj (op U₂)))
    (h : s₁ |_ (U₁ ⊓ U₂) = s₂ |_ (U₁ ⊓ U₂)) :
    ∃ s : ToType (F.obj.obj (op (U₁ ⊔ U₂))), s |_ U₁ = s₁ ∧ s |_ U₂ = s₂ := by
  let U : Bool → Opens X := fun b ↦ cond b U₁ U₂
  let sf : ∀ b, ToType (F.obj.obj (op (U b)))
    | true => s₁
    | false => s₂
  have hU : ∀ b, U b ≤ U₁ ⊔ U₂ := by
    rintro (_ | _)
    exacts [le_sup_right, le_sup_left]
  have h' := restrict_inf_symm F s₁ s₂ h
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U (U₁ ⊔ U₂) (fun b ↦ homOfLE (hU b))
    (sup_le (le_iSup U true) (le_iSup U false)) sf
    -- The compatibility conditions are `h`, `h'` and two trivial ones, since `x |_ W` is by
    -- definition the image of `x` under the restriction map.
    (by rintro (_ | _) (_ | _) <;> first | rfl | assumption)
  exact ⟨s, hs true, hs false⟩

/-- Any chain of extensions is bounded above, by the gluing of its sections over the union of
their domains. -/
private lemma Extension.exists_upper_bound (hUV : U ≤ V) (c : Set (Extension F (V := V) s))
    (hc : IsChain Extension.Le c) : ∃ ub, ∀ a ∈ c, a.Le ub := by
  obtain rfl | ⟨a₀, ha₀⟩ := c.eq_empty_or_nonempty
  · exact ⟨⟨U, le_rfl, hUV, s, restrict_self s⟩, by simp⟩
  -- Two members of the chain agree on the intersection of their domains.
  have key : ∀ a b : c, a.1.Le b.1 →
      a.1.sect |_ (a.1.dom ⊓ b.1.dom) = b.1.sect |_ (a.1.dom ⊓ b.1.dom) := by
    rintro a b ⟨hab, hab'⟩
    rw [← hab', restrict_restrict]
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing (fun a : c ↦ a.1.dom) (fun a ↦ a.1.sect) <| by
    intro a b
    by_cases hab : a = b
    · subst hab
      rfl
    obtain h | h := hc a.2 b.2 (fun h ↦ hab (Subtype.ext h))
    · exact key a b h
    · exact restrict_inf_symm F _ _ (key b a h)
  have hle : ∀ a : c, a.1.dom ≤ ⨆ b : c, b.1.dom := fun a ↦ le_iSup (fun b : c ↦ b.1.dom) a
  refine ⟨⟨⨆ a : c, a.1.dom, a₀.le_dom.trans (hle ⟨a₀, ha₀⟩), iSup_le fun a ↦ a.1.dom_le, t, ?_⟩,
    fun a ha ↦ ⟨hle ⟨a, ha⟩, ht ⟨a, ha⟩⟩⟩
  exact (restrict_restrict a₀.le_dom (hle ⟨a₀, ha₀⟩) t).symm.trans
    ((congrArg (fun r ↦ restrictOpen r U a₀.le_dom) (ht ⟨a₀, ha₀⟩)).trans a₀.restrict_sect)

variable (F) in
/-- **Flasqueness is local.** If every point has an open neighbourhood `W` such that every
restriction map `F(V) ⟶ F(U)` with `U ≤ V ≤ W` is surjective, then every restriction map of `F`
is surjective. -/
theorem surjective_map_of_local_extension
    (h : ∀ p : X, ∃ W : Opens X, p ∈ W ∧ ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), V ≤ W →
      Function.Surjective (F.obj.map (homOfLE hUV).op))
    (hUV : U ≤ V) : Function.Surjective (F.obj.map (homOfLE hUV).op) := by
  intro s
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded (Extension.exists_upper_bound (s := s) hUV)
    Extension.le_trans
  -- The maximal extension is defined on all of `V`.
  have hVm : V ≤ m.dom := by
    intro p hp
    obtain ⟨W, hpW, hW⟩ := h p
    obtain ⟨t, ht⟩ := hW (inf_le_right : m.dom ⊓ (W ⊓ V) ≤ W ⊓ V) inf_le_left
      (m.sect |_ (m.dom ⊓ (W ⊓ V)))
    obtain ⟨t', ht'₁, ht'₂⟩ := exists_restrict_eq_of_restrict_inf_eq F m.sect t ht.symm
    have hmt' : m.Le ⟨m.dom ⊔ W ⊓ V, m.le_dom.trans le_sup_left,
        sup_le m.dom_le inf_le_right, t', by
          rw [← restrict_restrict m.le_dom le_sup_left, ht'₁, m.restrict_sect]⟩ :=
      ⟨le_sup_left, ht'₁⟩
    exact (hm _ hmt').1 (le_sup_right (a := m.dom) ⟨hpW, hp⟩)
  exact ⟨m.sect |_ V, (restrict_restrict hUV hVm m.sect).trans m.restrict_sect⟩

variable (F) in
/-- **Flasqueness is local.** If every point has an open neighbourhood `W` such that every
restriction map `F(V) ⟶ F(U)` with `U ≤ V ≤ W` is surjective, then `F` is flasque. -/
theorem isFlasque_of_local_extension
    (h : ∀ p : X, ∃ W : Opens X, p ∈ W ∧ ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), V ≤ W →
      Function.Surjective (F.obj.map (homOfLE hUV).op)) :
    F.IsFlasque where
  epi i := ConcreteCategory.epi_of_surjective _
    (F.surjective_map_of_local_extension h (leOfHom i.unop))

variable (F) in
/-- When the forgetful functor preserves epimorphisms, as for sets, abelian groups and modules,
a sheaf is flasque if and only if every point has an open neighbourhood `W` such that every
restriction map `F(V) ⟶ F(U)` with `U ≤ V ≤ W` is surjective. -/
theorem isFlasque_iff_local_extension [(CategoryTheory.forget C).PreservesEpimorphisms] :
    F.IsFlasque ↔ ∀ p : X, ∃ W : Opens X, p ∈ W ∧ ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), V ≤ W →
      Function.Surjective (F.obj.map (homOfLE hUV).op) := by
  refine ⟨fun _ p ↦ ⟨⊤, by simp, fun U V hUV _ ↦ ?_⟩, F.isFlasque_of_local_extension⟩
  exact (CategoryTheory.epi_iff_surjective
    ((CategoryTheory.forget C).map (F.obj.map (homOfLE hUV).op))).mp inferInstance

end TopCat.Sheaf
