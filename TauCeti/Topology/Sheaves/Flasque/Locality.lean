/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Flasqueness is a local property

A sheaf on a topological space is flasque when all of its restriction maps are surjective. This
file proves that flasqueness is a local property.

## Main declarations

* `TopCat.Sheaf.map_surjective_of_locally_flasque`: if every point has an open neighbourhood `W`
  such that all restriction maps between opens contained in `W` are surjective, then all
  restriction maps are surjective. It holds for sheaves valued in any concrete category in which
  sections glue (for instance sets, abelian groups and modules);
* `TopCat.Sheaf.isFlasque_of_locally_flasque`: the same statement, with the conclusion phrased
  by Mathlib's `TopCat.Sheaf.IsFlasque`.

Locality is proved by Zorn's lemma. Fix `U ≤ V` and a section `s` over `U`, and order the
extensions of `s` to opens between `U` and `V` by extension. A chain of extensions glues to an
extension over the union of their domains, so there is a maximal extension. If a point `x` of `V`
lay outside its domain `O`, take a neighbourhood `W` of `x` on which `F` is flasque: the
restriction of the section to `O ⊓ W ⊓ V` lifts to `W ⊓ V`, and the two glue to a strictly larger
extension. Mathlib's proof of `TopCat.Sheaf.IsFlasque.epi_of_shortExact` is a Zorn argument of
the same shape.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Section II.5.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  {X : TopCat.{u}} (F : X.Sheaf C)

/-- Composing two restriction maps of `F` gives the restriction map along the composite inclusion.
Morphisms in `Opens X` are proofs of `≤`, so the two restriction maps agree by `rfl`. -/
private lemma map_homOfLE_map_homOfLE {A B D : Opens X} (h₁ : A ≤ B) (h₂ : B ≤ D)
    (x : ToType (F.1.obj (op D))) :
    F.1.map (homOfLE h₁).op (F.1.map (homOfLE h₂).op x) = F.1.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← Functor.map_comp_apply]
  rfl

/-- An extension of a section `s` over `U` to an open set between `U` and `V`. These are the
objects ordered by the Zorn argument proving `TopCat.Sheaf.map_surjective_of_locally_flasque`. -/
private structure FlasqueExtension {U V : Opens X} (s : ToType (F.1.obj (op U))) where
  /-- The domain of the extended section. -/
  dom : Opens X
  le_dom : U ≤ dom
  dom_le : dom ≤ V
  /-- The extended section. -/
  val : ToType (F.1.obj (op dom))
  map_val : F.1.map (homOfLE le_dom).op val = s

namespace FlasqueExtension

variable {F} {U V : Opens X} {s : ToType (F.1.obj (op U))}

/-- `p.Le q` means that `q` extends `p`. -/
private def Le (p q : FlasqueExtension F (V := V) s) : Prop :=
  ∃ h : p.dom ≤ q.dom, F.1.map (homOfLE h).op q.val = p.val

private lemma Le.trans {p q r : FlasqueExtension F (V := V) s} (hpq : p.Le q) (hqr : q.Le r) :
    p.Le r := by
  obtain ⟨h₁, e₁⟩ := hpq
  obtain ⟨h₂, e₂⟩ := hqr
  exact ⟨h₁.trans h₂, by rw [← e₁, ← e₂, map_homOfLE_map_homOfLE]⟩

variable [HasLimitsOfSize.{u, u} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]

/-- A chain of extensions has an upper bound: glue the sections along the union of their
domains. -/
private lemma exists_le_of_isChain (hUV : U ≤ V) (c : Set (FlasqueExtension F (V := V) s))
    (hc : IsChain Le c) : ∃ ub, ∀ p ∈ c, p.Le ub := by
  rcases c.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨⟨U, le_rfl, hUV, s, by simp⟩, by simp⟩
  let O : c → Opens X := fun p ↦ p.1.dom
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing O (fun p ↦ p.1.val) fun p q ↦ by
    by_cases hpq : p = q
    · subst hpq; rfl
    rcases hc p.2 q.2 (fun h ↦ hpq (Subtype.ext h)) with ⟨h, e⟩ | ⟨h, e⟩ <;> dsimp only <;> rw [← e]
    exacts [map_homOfLE_map_homOfLE F _ _ _, (map_homOfLE_map_homOfLE F _ _ _).symm]
  refine ⟨⟨iSup O, p₀.le_dom.trans (le_iSup O ⟨p₀, hp₀⟩), iSup_le fun p ↦ p.1.dom_le, t, ?_⟩,
    fun p hp ↦ ⟨le_iSup O ⟨p, hp⟩, ht ⟨p, hp⟩⟩⟩
  refine Eq.trans ?_ p₀.map_val
  have h₀ := ht ⟨p₀, hp₀⟩
  dsimp only at h₀
  rw [← h₀]
  exact (map_homOfLE_map_homOfLE F _ _ _).symm

/-- An extension can be enlarged across `W ⊓ V` whenever `F` is flasque on `W`: lift the
restriction of its section to the overlap, then glue. -/
private lemma exists_le_inf_le (p : FlasqueExtension F (V := V) s) {W : Opens X}
    (hW : ∀ ⦃A B : Opens X⦄ (hAB : A ≤ B), B ≤ W →
      Function.Surjective (F.1.map (homOfLE hAB).op)) :
    ∃ q : FlasqueExtension F (V := V) s, p.Le q ∧ W ⊓ V ≤ q.dom := by
  obtain ⟨t, ht⟩ := hW (inf_le_right : p.dom ⊓ (W ⊓ V) ≤ W ⊓ V) inf_le_left
    (F.1.map (homOfLE inf_le_left : p.dom ⊓ (W ⊓ V) ⟶ p.dom).op p.val)
  have key {D : Opens X} (hA : D ≤ p.dom) (hB : D ≤ W ⊓ V) :
      F.1.map (homOfLE hA).op p.val = F.1.map (homOfLE hB).op t := by
    have := congrArg (F.1.map (homOfLE (le_inf hA hB)).op) ht
    rw [map_homOfLE_map_homOfLE, map_homOfLE_map_homOfLE] at this
    exact this.symm
  let O : Fin 2 → Opens X := ![p.dom, W ⊓ V]
  let sf : ∀ i, ToType (F.1.obj (op (O i)))
    | 0 => p.val
    | 1 => t
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing O sf fun i j ↦ by
    fin_cases i <;> fin_cases j
    exacts [rfl, key _ _, (key _ _).symm, rfl]
  refine ⟨⟨iSup O, p.le_dom.trans (le_iSup O 0),
    iSup_le (Fin.forall_fin_two.2 ⟨p.dom_le, inf_le_right⟩), g, ?_⟩, ⟨le_iSup O 0, hg 0⟩,
    le_iSup O 1⟩
  refine Eq.trans ?_ p.map_val
  have h₀ : F.1.map (homOfLE (le_iSup O 0) : p.dom ⟶ iSup O).op g = p.val := hg 0
  rw [← h₀]
  exact (map_homOfLE_map_homOfLE F _ _ _).symm

end FlasqueExtension

variable [HasLimitsOfSize.{u, u} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]

/-- **Flasque locality.** If every point of `X` has an open neighbourhood `W` such that every
restriction map `F(B) → F(A)` of `F` with `A ≤ B ≤ W` is surjective, then every restriction map
of `F` is surjective.

For `C = Type u` this is the statement for sheaves of sets. -/
theorem map_surjective_of_locally_flasque
    (hF : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃A B : Opens X⦄ (hAB : A ≤ B), B ≤ W →
      Function.Surjective (F.1.map (homOfLE hAB).op))
    {U V : Opens X} (hUV : U ≤ V) : Function.Surjective (F.1.map (homOfLE hUV).op) := by
  intro s
  -- By Zorn's lemma, `s` has a maximal extension `m` to an open between `U` and `V`.
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (FlasqueExtension.exists_le_of_isChain (F := F) (s := s) hUV) FlasqueExtension.Le.trans
  -- Maximality and the local hypothesis force the domain of `m` to contain `V`.
  have hV : V ≤ m.dom := fun x hx ↦ by
    obtain ⟨W, hxW, hW⟩ := hF x
    obtain ⟨q, hmq, hq⟩ := m.exists_le_inf_le hW
    exact (hm q hmq).1 (hq ⟨hxW, hx⟩)
  refine ⟨F.1.map (homOfLE hV).op m.val, ?_⟩
  rw [map_homOfLE_map_homOfLE]
  exact m.map_val

/-- **Flasque locality**, with the conclusion phrased by Mathlib's `TopCat.Sheaf.IsFlasque`: a
sheaf all of whose restriction maps between opens inside some neighbourhood of each point are
surjective is flasque. -/
theorem isFlasque_of_locally_flasque
    (hF : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃A B : Opens X⦄ (hAB : A ≤ B), B ≤ W →
      Function.Surjective (F.1.map (homOfLE hAB).op)) :
    F.IsFlasque where
  epi i := ConcreteCategory.epi_of_surjective _ (F.map_surjective_of_locally_flasque hF i.unop.le)

end TopCat.Sheaf
