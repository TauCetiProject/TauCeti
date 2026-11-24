/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.Characterization
import TauCeti.GroupTheory.GroupAlgGeom.Irreducible.Components
import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Finitely generated residually free groups embed in finite products of limit groups

A finitely generated residually free group `G` is a subdirect product of finitely many limit
groups: there are finitely many normal subgroups `N₁, …, Nₘ` of `G` with trivial intersection
whose quotients `G ⧸ Nᵢ` are limit groups, that is, finitely generated fully residually free
groups. Hence `G` embeds in the direct product `G ⧸ N₁ × ⋯ × G ⧸ Nₘ`. Conversely a group which
embeds in a product of residually free groups is residually free, so among finitely generated
groups the residually free ones are exactly the subgroups of finite direct products of limit
groups.

The proof is the one of Kharlampovich and Myasnikov. A finite generating family presents `G` on
finitely many variables `X`. Since `G` is residually free, its relations are exactly the words
vanishing on the algebraic set `V ⊆ F₂^X` they define, so `G` is the coordinate group of `V`. The
free group `F₂` is equationally Noetherian, so `V` is a finite union of irreducible algebraic sets
`V₁, …, Vₘ`, and the coordinate group of `V` embeds in the product of the coordinate groups of the
`Vᵢ`. The coordinate group of an irreducible algebraic set is discriminated by `F₂`, that is, fully
residually free. Kharlampovich and Myasnikov work with coefficients in a nonabelian free group
`F`. There residual freeness shows that the coefficient-free words vanishing on the algebraic set
over `F` are exactly the relations of `G`, so `G` embeds in the coordinate group over `F`. That
coordinate group is a proper quotient of `F ∗ G` unless `G` is fully residually free, although
their proof of Corollary 2 identifies the two; only the embedding is needed. Here the coefficients
are trivial, and `G` itself is the coordinate group.

The product `F₂ × F₂` shows that the factors cannot be dispensed with: it is residually free and a
product of two limit groups, but it is not fully residually free
(`TauCeti.LimitGroup.not_isFullyResiduallyFree_freeGroup_prod_freeGroup`).

## Main results

* `TauCeti.LimitGroup.IsResiduallyFree.exists_isLimitGroup_quotient_iInf_eq_bot`: a finitely
  generated residually free group has finitely many normal subgroups with trivial intersection
  whose quotients are limit groups.
* `TauCeti.LimitGroup.IsResiduallyFree.exists_injective_monoidHom_pi_isLimitGroup`: a finitely
  generated residually free group embeds in a finite direct product of limit groups.
* `TauCeti.LimitGroup.isResiduallyFree_iff_exists_injective_monoidHom_pi_isLimitGroup`: a finitely
  generated group is residually free if and only if it embeds in a finite direct product of limit
  groups.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II: Systems in
  triangular quasi-quadratic form and description of residually free groups*, J. Algebra 200
  (1998), §0, Corollary 2, and its proof.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.6 and §4, Theorem 5.
-/

public section

namespace TauCeti.LimitGroup

open GroupAlgGeom Monoid.Coprod

universe u

variable {G : Type u} [Group G]

/-- A finitely generated residually free group is a subdirect product of finitely many limit
groups: it has finitely many normal subgroups with trivial intersection whose quotients are limit
groups (Kharlampovich and Myasnikov). -/
theorem IsResiduallyFree.exists_isLimitGroup_quotient_iInf_eq_bot [Group.FG G]
    (h : IsResiduallyFree G) :
    ∃ (m : ℕ) (N : Fin m → Subgroup G) (_ : ∀ i, (N i).Normal),
      (∀ i, IsLimitGroup (G ⧸ N i)) ∧ ⨅ i, N i = ⊥ := by
  obtain ⟨α, _, φ, hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.1 ‹Group.FG G›
  -- A finite generating family presents `G` on finitely many variables, without coefficients,
  -- and residual freeness makes `G` a coordinate group over `F₂`.
  let π : GHom (inl : Unit →* GX Unit α) (1 : Unit →* G) := ⟨lift 1 φ, fun _ => by simp⟩
  have hπ : Function.Surjective π := fun g =>
    (hφ g).elim fun w hw => ⟨inr w, (lift_apply_inr 1 φ w).trans hw⟩
  obtain ⟨S, ψ, hψ⟩ :=
    (isSeparatedBy_iff_exists_coordGroup π hπ).1 (isResiduallyFree_iff_isSeparatedBy.1 h)
  -- The coordinate group embeds in the product of those of the irreducible components.
  obtain ⟨m, T, hT, hirr, -, -, hinj⟩ :=
    (isEquationallyNoetherian_freeGroup
      (1 : Unit →* FreeGroup (Fin 2))).exists_injective_coordGroup_toPi S
  let f : G →* ∀ i, CoordGroup (1 : Unit →* FreeGroup (Fin 2)) (T i) :=
    (CoordGroup.toPi 1 S T hT : CoordGroup (1 : Unit →* FreeGroup (Fin 2)) S →* _).comp
      (ψ.symmOfBijective hψ : G →* CoordGroup (1 : Unit →* FreeGroup (Fin 2)) S)
  have hf : Function.Injective f := hinj.comp (ψ.symmOfBijective_injective hψ)
  refine ⟨m, fun i => ((Pi.evalMonoidHom _ i).comp f).ker, fun i => inferInstance, fun i => ?_,
    (Subgroup.eq_bot_iff_forall _).2 fun g hg => hf (funext fun i => ?_)⟩
  · -- Each quotient embeds in the coordinate group of an irreducible algebraic set.
    exact ((isFullyResiduallyFree_of_isFreeGroup.of_isDiscriminatedBy
      (isIrreducible_V_iff_isDiscriminatedBy.1 (hirr i))).of_injective
        (QuotientGroup.kerLift_injective _)).isLimitGroup
  · simpa [MonoidHom.mem_ker] using Subgroup.mem_iInf.1 hg i

/-- A finitely generated residually free group embeds in a direct product of finitely many limit
groups (Kharlampovich and Myasnikov). -/
theorem IsResiduallyFree.exists_injective_monoidHom_pi_isLimitGroup [Group.FG G]
    (h : IsResiduallyFree G) :
    ∃ (m : ℕ) (L : Fin m → Type u) (_ : ∀ i, Group (L i)) (f : G →* ∀ i, L i),
      (∀ i, IsLimitGroup (L i)) ∧ Function.Injective f := by
  obtain ⟨m, N, _, hN, hbot⟩ := h.exists_isLimitGroup_quotient_iInf_eq_bot
  refine ⟨m, fun i => G ⧸ N i, inferInstance, MonoidHom.pi fun i => QuotientGroup.mk' (N i), hN,
    (injective_iff_map_eq_one _).2 fun g hg => ?_⟩
  rw [← Subgroup.mem_bot, ← hbot, Subgroup.mem_iInf]
  exact fun i => (QuotientGroup.eq_one_iff g).1 (congr_fun hg i)

/-- A finitely generated group is residually free if and only if it embeds in a direct product of
finitely many limit groups. -/
theorem isResiduallyFree_iff_exists_injective_monoidHom_pi_isLimitGroup [Group.FG G] :
    IsResiduallyFree G ↔
      ∃ (m : ℕ) (L : Fin m → Type u) (_ : ∀ i, Group (L i)) (f : G →* ∀ i, L i),
        (∀ i, IsLimitGroup (L i)) ∧ Function.Injective f :=
  ⟨fun h => h.exists_injective_monoidHom_pi_isLimitGroup, fun ⟨_, _, _, _, hL, hf⟩ =>
    (IsResiduallyFree.pi fun i => (hL i).isFullyResiduallyFree.isResiduallyFree).of_injective hf⟩

end TauCeti.LimitGroup
