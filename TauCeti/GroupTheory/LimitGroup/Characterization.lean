/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Linear
public import TauCeti.GroupTheory.LimitGroup.MarkedGroup
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree

/-!
# Limit groups are the finitely generated fully residually free groups

A finitely generated group is a limit group, that is, some (equivalently every) finite generating
tuple marks a limit of markings of free groups in the space `𝒢ₙ` of marked groups, if and only if
it is fully residually free. This is the equivalence of conditions (1) and (2) in Theorem 1.1 of
Champetier and Guirardel.

* If `G` is fully residually free and `S : Fin n → G`, then for each finite set `W` of words a
  homomorphism `φ_W : G →* F₂` keeping the nontrivial values `S(w)`, `w ∈ W`, nontrivial gives a
  marking `φ_W ∘ S` of a free group. As `W` grows these markings converge to the marking of `S`.
* Conversely, the free group `F₂` is equationally Noetherian (Guba's theorem), so the relators of
  any marked group `N` are, over `F₂`, consequences of finitely many of them. These finitely many
  relators define an open neighbourhood of `N` in `𝒢ₙ`, and every marking of a free group in it is
  a quotient of `N`, because every free group is fully residually `F₂`
  (`TauCeti.LimitGroup.MarkedGroup.eventually_nhdsWithin_freeMarkings_ker_le`). If the marking of a
  limit group `G` is approximated by markings of free groups, finitely many nontrivial elements of
  `G` therefore stay nontrivial under a homomorphism from `G` onto a free group.

## Main results

* `TauCeti.LimitGroup.MarkedGroup.eventually_nhdsWithin_freeMarkings_ker_le`: near a marked group,
  every marking of a free group is a quotient of it.
* `TauCeti.LimitGroup.IsFullyResiduallyFree.ofMarking_mem_closure_freeMarkings`: every finite
  tuple of a fully residually free group marks a limit of markings of free groups.
* `TauCeti.LimitGroup.IsLimitGroup.isFullyResiduallyFree`: limit groups are fully residually
  free.
* `TauCeti.LimitGroup.isLimitGroup_iff_isFullyResiduallyFree`: a group is a limit group if and
  only if it is finitely generated and fully residually free.
* `TauCeti.LimitGroup.IsLimitGroup.of_injective`: finitely generated subgroups of limit groups
  are limit groups.
* `TauCeti.LimitGroup.not_isLimitGroup_freeGroup_prod_int`: `F₂ × ℤ` is not a limit group,
  although it is finitely generated and residually free.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), Theorem 1.1, Proposition 3.1 and §5.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.2.
-/

public section

open Filter Topology

namespace TauCeti.LimitGroup

open GroupAlgGeom

namespace MarkedGroup

variable {n : ℕ}

/-- Near a marked group `N`, every marking of a free group is a quotient of `N`: its kernel
contains that of `N`. By equational Noetherianity of `F₂`, finitely many relators of `N` have,
over `F₂`, all relators of `N` as consequences; containing these finitely many relators is an open
condition, and a marking of a free group satisfying it is a quotient of `N` because free groups are
fully residually `F₂`. -/
theorem eventually_nhdsWithin_freeMarkings_ker_le (N : MarkedGroup n) :
    ∀ᶠ N' in 𝓝[freeMarkings n] N, N.ker ≤ N'.ker := by
  obtain ⟨R, hRN, hRfin, hV⟩ := (Set.exists_subset_image_finite_and
    (p := fun T => V (1 : Unit →* FreeGroup (Fin 2)) T =
      V 1 (Monoid.Coprod.inr '' (N.ker : Set (FreeGroup (Fin n)))))).1
    ((isEquationallyNoetherian_freeGroup (1 : Unit →* FreeGroup (Fin 2))).exists_finite _)
  -- Every tuple of `F₂` killing the finitely many relators `R` kills all relators of `N`.
  have hR (T : Fin n → FreeGroup (Fin 2)) (hT : ∀ r ∈ R, FreeGroup.lift T r = 1) :
      ∀ w ∈ N.ker, FreeGroup.lift T w = 1 := by
    have hTV : T ∈ V (1 : Unit →* FreeGroup (Fin 2)) (Monoid.Coprod.inr '' R) := by
      simpa [mem_V] using hT
    rw [hV] at hTV
    simpa [mem_V] using hTV
  have hnhds : ∀ᶠ N' in 𝓝 N, ∀ r ∈ R, r ∈ N'.ker :=
    hRfin.eventually_all.2 fun r hr => (isClopen_setOf_mem_ker r).isOpen.mem_nhds (hRN hr)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnhds, self_mem_nhdsWithin]
    with N' hRN' hN' w hw
  by_contra hw'
  have := mem_freeMarkings.1 hN'
  -- The quotient by `N'` is free, so the nontrivial image of `w` there survives in `F₂`.
  obtain ⟨ψ, hψ⟩ := isFullyResiduallyFree_iff_fin_two.1 isFullyResiduallyFree_of_isFreeGroup
    {(w : FreeGroup (Fin n) ⧸ N'.ker)} (by simpa [QuotientGroup.eq_one_iff] using hw')
  have hlift (x : FreeGroup (Fin n)) :
      FreeGroup.lift (fun i => ψ (FreeGroup.of i : FreeGroup (Fin n) ⧸ N'.ker)) x = ψ x := by
    rw [FreeGroup.ext_hom (FreeGroup.lift _) (ψ.comp (QuotientGroup.mk' N'.ker))
      fun i => by simp]
    simp
  refine hψ _ (Finset.mem_singleton_self _) ?_
  rw [← hlift]
  refine hR _ (fun r hr => ?_) w hw
  rw [hlift, (QuotientGroup.eq_one_iff r).2 (hRN' r hr), map_one]

end MarkedGroup

open MarkedGroup

variable {G : Type*} [Group G]

/-- Every finite tuple `S` of a fully residually free group marks a limit of markings of free
groups: the markings `φ_W ∘ S`, where `φ_W` keeps nontrivial the nontrivial values of the words
in a finite set `W`, converge to the marking of `S` as `W` grows. -/
theorem IsFullyResiduallyFree.ofMarking_mem_closure_freeMarkings (h : IsFullyResiduallyFree G)
    {n : ℕ} (S : Fin n → G) : ofMarking S ∈ closure (freeMarkings n) := by
  classical
  choose φ hφ using fun W : Finset (FreeGroup (Fin n)) =>
    isFullyResiduallyFree_iff_fin_two.1 h ((W.image (FreeGroup.lift S)).filter (· ≠ 1))
      fun _ hg => (Finset.mem_filter.1 hg).2
  refine mem_closure_of_tendsto (f := fun W => ofMarking (φ W ∘ S)) (b := atTop) ?_
    (Eventually.of_forall fun W => ofMarking_mem_freeMarkings _)
  rw [tendsto_nhds_iff]
  intro w
  filter_upwards [eventually_ge_atTop {w}] with W hW
  have hlift : FreeGroup.lift (φ W ∘ S) = (φ W).comp (FreeGroup.lift S) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  simp only [mem_ofMarking_ker, hlift, MonoidHom.comp_apply]
  by_cases hw : FreeGroup.lift S w = 1
  · simp [hw]
  · exact iff_of_false (hφ W _ (Finset.mem_filter.2
      ⟨Finset.mem_image_of_mem _ (hW (Finset.mem_singleton_self w)), hw⟩)) hw

/-- A finitely generated fully residually free group is a limit group. -/
theorem IsFullyResiduallyFree.isLimitGroup [Group.FG G] (h : IsFullyResiduallyFree G) :
    IsLimitGroup G :=
  isLimitGroup_iff.2 ⟨‹_›, fun _ => h.ofMarking_mem_closure_freeMarkings⟩

/-- Limit groups are fully residually free. Given finitely many nontrivial elements, a marking of
a free group close enough to a generating marking of the limit group is a quotient of it
(`MarkedGroup.eventually_nhdsWithin_freeMarkings_ker_le`) in which the chosen elements stay
nontrivial. -/
theorem IsLimitGroup.isFullyResiduallyFree (h : IsLimitGroup G) : IsFullyResiduallyFree G := by
  classical
  rw [isFullyResiduallyFree_iff_fin_two]
  intro s hs
  obtain ⟨n, S, hS, hmem⟩ := isLimitGroup_def.1 h
  have hsurj := FreeGroup.lift_surjective_iff_closure_range_eq_top.2 hS
  -- A word representing each element of `G`.
  let w := Function.surjInv hsurj
  have hw : Function.RightInverse w (FreeGroup.lift S) := Function.rightInverse_surjInv hsurj
  have hne : ∀ᶠ N in 𝓝 (ofMarking S), ∀ g ∈ s, w g ∉ N.ker :=
    s.eventually_all.2 fun g hg =>
      (isClopen_setOf_mem_ker (w g)).compl.isOpen.mem_nhds (by simpa [hw g] using hs g hg)
  have := mem_closure_iff_nhdsWithin_neBot.1 hmem
  obtain ⟨N, hle, hN, hF⟩ := ((ofMarking S).eventually_nhdsWithin_freeMarkings_ker_le.and
    ((eventually_nhdsWithin_of_eventually_nhds hne).and self_mem_nhdsWithin)).exists
  have := mem_freeMarkings.1 hF
  -- The quotient map from `G` onto the free group `F_n ⧸ N`.
  let π : G →* FreeGroup (Fin n) ⧸ N.ker := (FreeGroup.lift S).liftOfRightInverse w hw
    ⟨QuotientGroup.mk' N.ker, by rwa [QuotientGroup.ker_mk', ← ker_ofMarking]⟩
  have hπ (g : G) : π g = (w g : FreeGroup (Fin n) ⧸ N.ker) := by
    conv_lhs => rw [← hw g]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨ψ, hψ⟩ := isFullyResiduallyFree_iff_fin_two.1 isFullyResiduallyFree_of_isFreeGroup
    (s.image π) fun x hx => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
      rw [hπ, Ne, QuotientGroup.eq_one_iff]
      exact hN g hg
  exact ⟨ψ.comp π, fun g hg => hψ _ (Finset.mem_image_of_mem π hg)⟩

/-- **Limit groups are the finitely generated fully residually free groups** (Champetier and
Guirardel, Theorem 1.1). -/
theorem isLimitGroup_iff_isFullyResiduallyFree :
    IsLimitGroup G ↔ Group.FG G ∧ IsFullyResiduallyFree G :=
  ⟨fun h => ⟨h.fg, h.isFullyResiduallyFree⟩, fun ⟨_, h⟩ => h.isLimitGroup⟩

/-- A finitely generated group with an injective homomorphism to a limit group is a limit group.
In particular finitely generated subgroups of limit groups are limit groups. -/
theorem IsLimitGroup.of_injective {H : Type*} [Group H] [Group.FG H] (h : IsLimitGroup G)
    {f : H →* G} (hf : Function.Injective f) : IsLimitGroup H :=
  (h.isFullyResiduallyFree.of_injective hf).isLimitGroup

/-- `F₂ × ℤ` is not a limit group: it is finitely generated and residually free, but not fully
residually free. In particular limit groups are not closed under direct products. -/
theorem not_isLimitGroup_freeGroup_prod_int :
    ¬IsLimitGroup (FreeGroup (Fin 2) × Multiplicative ℤ) := fun h =>
  not_isFullyResiduallyFree_freeGroup_prod_int h.isFullyResiduallyFree

end TauCeti.LimitGroup
