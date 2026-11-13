/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Linear
public import TauCeti.GroupTheory.GroupAlgGeom.Separated
public import TauCeti.GroupTheory.LimitGroup.Characterization

/-!
# Descending chains of residually free groups stabilise

In a sequence of epimorphisms `G 0 ↠ G 1 ↠ G 2 ↠ ⋯` of residually free groups, with `G 0` finitely
generated, all but finitely many of the epimorphisms are isomorphisms. In particular this holds
for sequences of epimorphisms of limit groups, so a proper quotient of a limit group which is a
limit group is strictly simpler, and a finitely generated residually free group is Hopfian: every
surjective endomorphism is injective.

The proof is the one of Champetier and Guirardel which avoids finite presentability. A finite
generating tuple of `G 0` marks every `G k`, and the tuples in the free group `F₂` satisfying the
relations of `G k` form a decreasing sequence of algebraic sets. Since `F₂` is equationally
Noetherian the sequence is eventually constant, and since `G k` is residually free its relations
are exactly the words vanishing on its algebraic set, so the relations are eventually constant.
Champetier and Guirardel use representations in `SL₂(ℂ)` and the Noetherianity of affine space;
the equational Noetherianity of `F₂` is that argument applied through an embedding of `F₂` in
`SL₂`. The general statement, for groups separated by an equationally Noetherian group over a
group of coefficients, is
`TauCeti.GroupAlgGeom.IsEquationallyNoetherian.exists_forall_ge_injective`.

## Main results

* `TauCeti.LimitGroup.exists_forall_ge_bijective_of_isResiduallyFree`: a sequence of epimorphisms
  of residually free groups starting from a finitely generated group consists of isomorphisms from
  some index on.
* `TauCeti.LimitGroup.exists_forall_ge_bijective_of_isLimitGroup`: the same for limit groups.
* `TauCeti.LimitGroup.IsResiduallyFree.injective_of_surjective`: finitely generated residually
  free groups are Hopfian.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), §3.3, Proposition 3.13, and §6.4, Proposition 6.8.
-/

public section

namespace TauCeti.LimitGroup

open GroupAlgGeom Monoid.Coprod

universe u

variable {G : ℕ → Type u} [∀ k, Group (G k)]

/-- **Descending chain condition for residually free groups.** In a sequence of epimorphisms
`G 0 ↠ G 1 ↠ ⋯` of residually free groups, with `G 0` finitely generated, all but finitely many
of the epimorphisms are isomorphisms. -/
theorem exists_forall_ge_bijective_of_isResiduallyFree [Group.FG (G 0)]
    (f : ∀ k, G k →* G (k + 1)) (hf : ∀ k, Function.Surjective (f k))
    (hG : ∀ k, IsResiduallyFree (G k)) : ∃ m, ∀ k, m ≤ k → Function.Bijective (f k) := by
  obtain ⟨α, _, φ, hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.1 ‹Group.FG (G 0)›
  -- A finite generating family presents `G 0` on finitely many variables, without coefficients.
  let π : GHom (inl : Unit →* GX Unit α) (1 : Unit →* G 0) := ⟨lift 1 φ, fun _ => by simp⟩
  have hπ : Function.Surjective π := fun g =>
    (hφ g).elim fun w hw => ⟨inr w, (lift_apply_inr 1 φ w).trans hw⟩
  obtain ⟨m, hm⟩ := (isEquationallyNoetherian_freeGroup (1 : Unit →* FreeGroup (Fin 2)))
    |>.exists_forall_ge_injective π hπ (fun k => ⟨f k, fun _ => by simp⟩) hf
      fun k => isResiduallyFree_iff_isSeparatedBy.1 (hG k)
  exact ⟨m, fun k hk => ⟨hm k hk, hf k⟩⟩

/-- **Descending chain condition for limit groups.** In a sequence of epimorphisms
`G 0 ↠ G 1 ↠ ⋯` of limit groups, all but finitely many of the epimorphisms are isomorphisms. -/
theorem exists_forall_ge_bijective_of_isLimitGroup (f : ∀ k, G k →* G (k + 1))
    (hf : ∀ k, Function.Surjective (f k)) (hG : ∀ k, IsLimitGroup (G k)) :
    ∃ m, ∀ k, m ≤ k → Function.Bijective (f k) :=
  have := (hG 0).fg
  exists_forall_ge_bijective_of_isResiduallyFree f hf fun k =>
    (hG k).isFullyResiduallyFree.isResiduallyFree

/-- A finitely generated residually free group is Hopfian: every surjective endomorphism is
injective. -/
theorem IsResiduallyFree.injective_of_surjective {G : Type u} [Group G] [Group.FG G]
    (h : IsResiduallyFree G) {f : G →* G} (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨m, hm⟩ := exists_forall_ge_bijective_of_isResiduallyFree (G := fun _ => G) (fun _ => f)
    (fun _ => hf) fun _ => h
  exact (hm m le_rfl).1

end TauCeti.LimitGroup
