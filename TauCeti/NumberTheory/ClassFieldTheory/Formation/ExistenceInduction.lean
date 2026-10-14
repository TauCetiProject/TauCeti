/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Reciprocity
import TauCeti.GroupTheory.Index.Comap

/-!
# The induction on the index in the proof of the existence theorem

Let `F` be a formation on a profinite group `G`, with level `A^W` for an open subgroup `W`, the
module of the field `E` that `W` cuts out. A subgroup `N ⊆ A^W` **contains a norm group** if it
contains the image of the norm `N_{W/W'} : A^{W'} → A^W` from some open `W' ≤ W`, the norm group of
a finite, not necessarily Galois, extension of `E`. In a class formation such a subgroup of the
ground level `A^G` is the norm subgroup of an abelian layer
(`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le`).

This file proves the induction on the index by which the global existence theorem is deduced from
its **Kummer case** (Milne, *Class Field Theory*, VII, Theorem 9.5, from Lemmas 9.3 and 9.4). Fix,
for every open subgroup `W`, a class of *admissible* subgroups of `A^W`, closed under enlargement
and under preimages by the norms `N_{W/W'}`. For the idele classes these are the open subgroups of
`C_E`. Suppose that for every prime `p` and every open `W` there is an open `W' ≤ W` such that over
`W'` every admissible subgroup of finite index containing `p · A^{W'}` contains a norm group. For
the idele classes, `W'` cuts out `E(ζ_p)`, and the hypothesis is the Kummer case. Then every
admissible subgroup of finite index of every level contains a norm group
(`Formation.exists_range_levelNorm_le_of_forall_prime`). In a class formation, every admissible
subgroup of finite index of the ground level is therefore the norm subgroup of an abelian layer
(`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_forall_prime`).

The proof is by strong induction on the index `n` of `N ⊆ A^W`, simultaneously for all `W`. If
`n > 1`, choose a prime `p ∣ n` and the open `W' ≤ W` of the hypothesis. By descent along the norm
(Milne VII, Lemma 9.4) it suffices that the preimage `N'` of `N` in `A^{W'}` contains a norm group,
and the index of `N'` is at most `n`. If it is smaller, the induction hypothesis applies. Otherwise
`p` divides the order of `A^{W'}/N'`. The preimage `N₁` of `p · (A^{W'}/N')` then contains `N'` and
`p · A^{W'}`, and it is proper, because multiplication by `p` on the finite group `A^{W'}/N'` is not
injective by Cauchy's theorem, hence not surjective. By the hypothesis `N₁` contains the norm group
of some `W₁ ≤ W'`. The preimage of `N'` in `A^{W₁}` has index at most `[N₁ : N'] < n`, so it
contains a norm group by induction, and so does `N'`.

The induction is not an existence theorem: the class-formation axioms do not imply the Kummer
hypothesis, which is an arithmetic statement about each setting.

## Main statements

* `TauCeti.ClassFieldTheory.Formation.exists_range_levelNorm_le_of_forall_prime`: from the Kummer
  case, every admissible subgroup of finite index of a level contains a norm group.
* `TauCeti.ClassFieldTheory.ClassFormation.exists_abelianLayer_normSubgroup_eq_of_forall_prime`:
  in a class formation, every admissible subgroup of finite index of the ground level is then the
  norm subgroup of an abelian layer.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §9, Lemmas 9.3 and 9.4 and Theorem 9.5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace Formation

variable (F : Formation G)

/-- **Descent along the norm.** If the preimage of `N ⊆ A^W` under the norm `N_{W/W₁}` contains
the norm group of some `W₂ ≤ W₁`, then `N` contains the norm group of `W₂`. -/
private theorem exists_range_levelNorm_le_of_comap {W W₁ : OpenSubgroup G} (h₁ : W₁ ≤ W)
    {N : AddSubgroup (F.level W)}
    (h : ∃ (W₂ : OpenSubgroup G) (h₂ : W₂ ≤ W₁),
      (F.levelNorm h₂).range ≤ N.comap (F.levelNorm h₁)) :
    ∃ (W₂ : OpenSubgroup G) (h₂ : W₂ ≤ W), (F.levelNorm h₂).range ≤ N := by
  obtain ⟨W₂, h₂, hle⟩ := h
  refine ⟨W₂, h₂.trans h₁, ?_⟩
  rw [F.levelNorm_trans h₁ h₂, AddMonoidHom.range_comp]
  exact AddSubgroup.map_le_iff_le_comap.2 hle

/-- **The induction on the index in the existence theorem** (Milne VII, Theorem 9.5). Let `P W`
be a class of *admissible* subgroups of the level `A^W`, for each open subgroup `W` (the open
subgroups of `C_E` for the idele classes), closed under enlargement and under preimages by the
norms between levels. Suppose that for every prime `p` and every open `W` there is an open
`W' ≤ W` over which every admissible subgroup of finite index containing `p · A^{W'}` contains the
norm group of an open subgroup of `W'`; for the idele classes, `W'` cuts out `E(ζ_p)` and this is
the Kummer case (Milne VII, Lemma 9.3). Then every admissible subgroup of finite index of a level
`A^W` contains the norm group `N_{W/W'}(A^{W'})` of an open subgroup `W' ≤ W`. -/
theorem exists_range_levelNorm_le_of_forall_prime
    (P : ∀ W : OpenSubgroup G, AddSubgroup (F.level W) → Prop)
    (hP_mono : ∀ {W : OpenSubgroup G} {N N' : AddSubgroup (F.level W)}, P W N → N ≤ N' → P W N')
    (hP_comap : ∀ {W W' : OpenSubgroup G} (h : W' ≤ W) {N : AddSubgroup (F.level W)},
      P W N → P W' (N.comap (F.levelNorm h)))
    (hkummer : ∀ p : ℕ, p.Prime → ∀ W : OpenSubgroup G, ∃ W' : OpenSubgroup G, W' ≤ W ∧
      ∀ N : AddSubgroup (F.level W'), P W' N → N.FiniteIndex → (∀ a : F.level W', p • a ∈ N) →
        ∃ (W'' : OpenSubgroup G) (h : W'' ≤ W'), (F.levelNorm h).range ≤ N)
    {W : OpenSubgroup G} (N : AddSubgroup (F.level W)) (hN : P W N) [N.FiniteIndex] :
    ∃ (W' : OpenSubgroup G) (h : W' ≤ W), (F.levelNorm h).range ≤ N := by
  -- Strong induction on the index, simultaneously for all levels.
  suffices key : ∀ n : ℕ, ∀ (W : OpenSubgroup G) (N : AddSubgroup (F.level W)), P W N →
      N.FiniteIndex → N.index = n →
      ∃ (W' : OpenSubgroup G) (h : W' ≤ W), (F.levelNorm h).range ≤ N from
    key _ W N hN inferInstance rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W N hN hfin hn
  -- Index one: `N` is everything, and contains the norm group of `W` itself.
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨W, le_rfl, by rw [AddSubgroup.index_eq_one.1 hn]; exact le_top⟩
  -- Otherwise choose a prime `p ∣ n` and the level `W'` of the Kummer case, and descend from it.
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨W', hW', hK⟩ := hkummer p hp W
  set N' := N.comap (F.levelNorm hW')
  have hPN' : P W' N' := hP_comap hW' hN
  refine F.exists_range_levelNorm_le_of_comap hW' ?_
  have hN'n : N'.index ≤ n := hn ▸ N.index_comap_le _
  rcases hN'n.lt_or_eq with hlt | heq
  · exact ih _ hlt W' N' hPN' inferInstance rfl
  -- The preimage `N'` still has index `n`. Let `N₁` be the preimage of `p · (A^{W'}/N')`.
  let Q := F.level W' ⧸ N'
  let N₁ : AddSubgroup (F.level W') :=
    (nsmulAddMonoidHom p : Q →+ Q).range.comap (QuotientAddGroup.mk' N')
  have hN'N₁ : N' ≤ N₁ := fun a ha ↦ ⟨0, by
    rw [map_zero, QuotientAddGroup.mk'_apply, eq_comm, QuotientAddGroup.eq_zero_iff]
    exact ha⟩
  have hpN₁ (a : F.level W') : p • a ∈ N₁ := ⟨QuotientAddGroup.mk' N' a, by simp⟩
  -- `N₁` is proper: multiplication by `p` is not surjective on `A^{W'}/N'`, of order `n`.
  have hN₁ : N₁ ≠ ⊤ := by
    intro htop
    have : Finite Q := AddSubgroup.finite_quotient_of_finiteIndex
    have : Fact p.Prime := ⟨hp⟩
    -- by Cauchy's theorem `A^{W'}/N'` has an element `x` of order `p`
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := Q) p <| by
      rw [← AddSubgroup.index_eq_card, heq]; exact hpn
    -- but multiplication by `p` on it is surjective, since `N₁ = ⊤`, hence injective
    have hsurj : Function.Surjective (fun y : Q ↦ p • y) := fun y ↦ by
      induction y using QuotientAddGroup.induction_on with
      | H a => exact (show a ∈ N₁ from htop ▸ AddSubgroup.mem_top a)
    have hx0 : x = 0 := Finite.injective_iff_surjective.2 hsurj <| by
      simp only [smul_zero, ← hx, addOrderOf_nsmul_eq_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have : N₁.FiniteIndex := AddSubgroup.finiteIndex_of_le hN'N₁
  -- By the Kummer case `N₁` contains the norm group of some `W₁ ≤ W'`, and the preimage of `N'`
  -- in `A^{W₁}` has smaller index, so it contains a norm group by induction.
  obtain ⟨W₁, h₁, hle₁⟩ := hK N₁ (hP_mono hPN' hN'N₁) inferInstance hpN₁
  refine F.exists_range_levelNorm_le_of_comap h₁ ?_
  exact ih _ (heq ▸ N'.index_comap_lt_of_range_le _ hN'N₁ hN₁ hle₁) W₁ _ (hP_comap h₁ hPN')
    inferInstance rfl

end Formation

namespace ClassFormation

variable {F : Formation G} (cf : ClassFormation F)

include cf in
/-- **Existence from the Kummer case, in a class formation** (Milne VII, Theorem 9.5). Under the
hypotheses of `Formation.exists_range_levelNorm_le_of_forall_prime`, namely a class `P` of
admissible subgroups of the levels, closed under enlargement and under preimages by norms, and the
Kummer case over a suitable open subgroup of every open subgroup for every prime, every admissible
subgroup of finite index of the ground level `A^G` is the norm subgroup of an abelian layer. -/
theorem exists_abelianLayer_normSubgroup_eq_of_forall_prime
    (P : ∀ W : OpenSubgroup G, AddSubgroup (F.level W) → Prop)
    (hP_mono : ∀ {W : OpenSubgroup G} {N N' : AddSubgroup (F.level W)}, P W N → N ≤ N' → P W N')
    (hP_comap : ∀ {W W' : OpenSubgroup G} (h : W' ≤ W) {N : AddSubgroup (F.level W)},
      P W N → P W' (N.comap (F.levelNorm h)))
    (hkummer : ∀ p : ℕ, p.Prime → ∀ W : OpenSubgroup G, ∃ W' : OpenSubgroup G, W' ≤ W ∧
      ∀ N : AddSubgroup (F.level W'), P W' N → N.FiniteIndex → (∀ a : F.level W', p • a ∈ N) →
        ∃ (W'' : OpenSubgroup G) (h : W'' ≤ W'), (F.levelNorm h).range ≤ N)
    (N : Submodule ℤ (F.level ⊤)) (hN : P ⊤ N.toAddSubgroup) [N.toAddSubgroup.FiniteIndex] :
    ∃ V : OpenNormalSubgroup G, V.IsAbelianClassFieldLayer ∧ F.normSubgroup V = N := by
  obtain ⟨W, _, hle⟩ :=
    F.exists_range_levelNorm_le_of_forall_prime P hP_mono hP_comap hkummer N.toAddSubgroup hN
  exact cf.exists_abelianLayer_normSubgroup_eq_of_range_levelNorm_le (W := W) hle

end ClassFormation

end TauCeti.ClassFieldTheory
