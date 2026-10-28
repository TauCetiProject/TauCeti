/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.PartialEquiv

/-!
# Potential isomorphisms

Two structures are potentially isomorphic when some nonempty family of equivalences between
finitely generated substructures has the back-and-forth extension property. Crucially, extensions
must remain inside the chosen family. Mathlib's `Language.IsExtensionPair` instead requires every
finitely generated partial equivalence to extend; holding in both directions, together with an
initial finitely generated partial equivalence, it implies potential isomorphism
(`FirstOrder.Language.IsExtensionPair.potentialIso`).

In any language, potential isomorphism is reflexive, since an isomorphism gives one
(`FirstOrder.Language.Equiv.potentialIso`), symmetric (`TauCeti.PotentialIso.symm`), and
transitive (`TauCeti.PotentialIso.trans`), by composing members of the two families.

The definition is the finitely-generated-partial-equivalence presentation of the back-and-forth
systems used by Carol Karp, *Finite-quantifier equivalence* (1965). Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Karp/PotentialIso.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, instead uses finite tuples; the two presentations
agree for relational languages.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- Two structures are potentially isomorphic if a nonempty set of finitely generated partial
equivalences admits extensions containing every element on either side. -/
def PotentialIso (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] : Prop :=
  ∃ S : Set (L.FGEquiv M N), S.Nonempty ∧
    (∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g) ∧
    (∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g)

/-- Potential isomorphism is witnessed by a nonempty family closed under extensions on both
sides. -/
theorem potentialIso_def : PotentialIso (L := L) M N ↔
    ∃ S : Set (L.FGEquiv M N), S.Nonempty ∧
      (∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g) ∧
      (∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g) :=
  Iff.rfl

/-- An isomorphism gives a potential isomorphism by restricting it to finitely generated
substructures. -/
theorem _root_.FirstOrder.Language.Equiv.potentialIso (e : M ≃[L] N) :
    PotentialIso (L := L) M N := by
  let F : M ≃ₚ[L] N := e.toEmbedding.toPartialEquiv
  refine ⟨{f | f.1 ≤ F}, ?_, ?_, ?_⟩
  · have hbot : (⊥ : L.Substructure M) ≤ F.dom := bot_le
    exact ⟨⟨F.domRestrict hbot, Substructure.fg_bot⟩, F.domRestrict_le hbot⟩
  · intro f hf m
    let A : L.Substructure M := Substructure.closure L {m} ⊔ f.1.dom
    have hA : A ≤ F.dom := le_top
    let g : L.FGEquiv M N :=
      ⟨F.domRestrict hA, (Substructure.fg_closure_singleton m).sup f.2⟩
    refine ⟨g, F.domRestrict_le hA, ?_, ?_⟩
    · have hm : m ∈ Substructure.closure L {m} :=
        Substructure.subset_closure (Set.mem_singleton m)
      exact mem_of_le_of_mem le_sup_left hm
    · exact PartialEquiv.le_domRestrict f.1 F le_sup_right hA hf
  · intro f hf n
    let A : L.Substructure N := Substructure.closure L {n} ⊔ f.1.cod
    have hFcod : F.cod = ⊤ := by
      exact Hom.range_eq_top.mpr e.surjective
    have hA : A ≤ F.cod := hFcod.symm ▸ le_top
    have hfg : (F.codRestrict hA).dom.FG :=
      (F.codRestrict hA).dom_fg_iff_cod_fg.mpr ((Substructure.fg_closure_singleton n).sup
        (f.1.dom_fg_iff_cod_fg.mp f.2))
    let g : L.FGEquiv M N := ⟨F.codRestrict hA, hfg⟩
    refine ⟨g, F.codRestrict_le hA, ?_, ?_⟩
    · have hn : n ∈ Substructure.closure L {n} :=
        Substructure.subset_closure (Set.mem_singleton n)
      exact mem_of_le_of_mem le_sup_left hn
    · exact PartialEquiv.le_codRestrict f.1 F le_sup_right hA hf

/-- Inverting a finitely generated partial equivalence twice gives it back. -/
@[simp]
theorem _root_.FirstOrder.Language.FGEquiv.symm_symm (f : L.FGEquiv M N) : f.symm.symm = f :=
  Subtype.ext f.1.symm_symm

/-- Potential isomorphism is symmetric. -/
theorem PotentialIso.symm (h : PotentialIso (L := L) M N) :
    PotentialIso (L := L) N M := by
  obtain ⟨S, ⟨f, hf⟩, hforth, hback⟩ := h
  refine ⟨{g | g.symm ∈ S}, ⟨f.symm, ?_⟩, ?_, ?_⟩
  · rwa [Set.mem_ofPred_eq, FGEquiv.symm_symm]
  · intro g hg n
    obtain ⟨k, hk, hn, hgk⟩ := hback g.symm hg n
    refine ⟨k.symm, ?_, hn, ?_⟩
    · rwa [Set.mem_ofPred_eq, FGEquiv.symm_symm]
    · exact PartialEquiv.monotone_symm hgk
  · intro g hg m
    obtain ⟨k, hk, hm, hgk⟩ := hforth g.symm hg m
    refine ⟨k.symm, ?_, hm, ?_⟩
    · rwa [Set.mem_ofPred_eq, FGEquiv.symm_symm]
    · exact PartialEquiv.monotone_symm hgk

/-- Potential isomorphism is transitive. -/
theorem PotentialIso.trans {P : Type*} [L.Structure P] (h₁ : PotentialIso (L := L) M N)
    (h₂ : PotentialIso (L := L) N P) : PotentialIso (L := L) M P := by
  obtain ⟨S, ⟨f₀, hf₀⟩, hSf, hSb⟩ := h₁
  obtain ⟨T, ⟨g₀, hg₀⟩, hTf, hTb⟩ := h₂
  -- The composites of compatible members of `S` and `T` form the required family.
  let comp (f : L.FGEquiv M N) (g : L.FGEquiv N P) (h : f.1.cod ≤ g.1.dom) : L.FGEquiv M P :=
    ⟨g.1.comp f.1 h, by rw [PartialEquiv.dom_comp]; exact f.2⟩
  refine ⟨{k | ∃ f ∈ S, ∃ g ∈ T, ∃ h, k = comp f g h}, ?_, ?_, ?_⟩
  · obtain ⟨g, hg, h, -⟩ :=
      FGEquiv.exists_le_and_le_dom_of_fg hTf hg₀ (f₀.1.dom_fg_iff_cod_fg.1 f₀.2)
    exact ⟨_, f₀, hf₀, g, hg, h, rfl⟩
  · rintro _ ⟨f, hf, g, hg, h, rfl⟩ m
    obtain ⟨f', hf', hm, hff'⟩ := hSf f hf m
    obtain ⟨g', hg', h', hgg'⟩ :=
      FGEquiv.exists_le_and_le_dom_of_fg hTf hg (f'.1.dom_fg_iff_cod_fg.1 f'.2)
    exact ⟨_, ⟨f', hf', g', hg', h', rfl⟩, by rwa [PartialEquiv.dom_comp],
      PartialEquiv.comp_le_comp hff' hgg' h h'⟩
  · rintro _ ⟨f, hf, g, hg, h, rfl⟩ p
    -- Extend `g` to reach `p`, extend `f` to reach the preimage `y` of `p`, then extend the first
    -- extension of `g` over the codomain of the extension of `f`.
    obtain ⟨g₁, hg₁, hp, hgg₁⟩ := hTb g hg p
    let y := g₁.1.toEquiv.symm ⟨p, hp⟩
    obtain ⟨f', hf', hy, hff'⟩ := hSb f hf y
    obtain ⟨g', hg', h', hg₁g'⟩ :=
      FGEquiv.exists_le_and_le_dom_of_fg hTf hg₁ (f'.1.dom_fg_iff_cod_fg.1 f'.2)
    refine ⟨_, ⟨f', hf', g', hg', h', rfl⟩, (PartialEquiv.mem_cod_comp _ _ h').2 ⟨⟨y, hy⟩, ?_⟩,
      PartialEquiv.comp_le_comp hff' (hgg₁.trans hg₁g') h h'⟩
    -- The extension `g'` agrees with `g₁` at `y`, which `g₁` sends to `p`.
    exact (PartialEquiv.toEquiv_apply_of_le hg₁g' y.2).trans (by simp [y])

/-- Mathlib's global two-sided extension property gives a potential isomorphism when there is an
initial finitely generated partial equivalence. -/
theorem _root_.FirstOrder.Language.IsExtensionPair.potentialIso (hMN : L.IsExtensionPair M N)
    (hNM : L.IsExtensionPair N M) (hne : Nonempty (L.FGEquiv M N)) :
    PotentialIso (L := L) M N := by
  refine ⟨Set.univ, hne.elim fun f => ⟨f, Set.mem_univ f⟩, ?_, ?_⟩
  · intro f _ m
    obtain ⟨g, hm, hfg⟩ := hMN f m
    exact ⟨g, Set.mem_univ g, hm, hfg⟩
  · intro f _ n
    obtain ⟨g, hn, hfg⟩ := hNM.cod f n
    exact ⟨g, Set.mem_univ g, hn, hfg⟩

end TauCeti
