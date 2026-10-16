/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Basic
import TauCeti.GroupTheory.TitsSystem.Bruhat.Subword

/-!
# Double cosets of standard parabolics

For a Tits system, the double cosets of standard parabolics `P_J` and `P_K` are indexed
by the Weyl double cosets `W_J \ W / W_K`. More precisely, `P_J n P_K` is the union of
the Bruhat cells whose indices lie in `W_J w W_K`, where `n` represents `w`.
This computes relative positions of partial flags from the Weyl group.

The intermediate one-sided decompositions describe multiplication of a Bruhat cell by a
standard parabolic. All results concern abstract groups with a BN-pair, without finiteness
or algebraic-group assumptions.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 5.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), §8.3.

The proofs use the rank-one multiplication laws and the standard-parabolic Bruhat
decomposition in `TauCeti.GroupTheory.TitsSystem.Parabolic.Basic`.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

private theorem exists_mem_weylClosure_bruhatCell_mul {J : Set T.simple} {a : G}
    (ha : a ∈ T.standardParabolic J) :
    ∀ {b : G} {w : T.WeylGroup}, b ∈ T.bruhatCell w →
      ∃ v ∈ Subgroup.closure (Subtype.val '' J), a * b ∈ T.bruhatCell (v * w) := by
  have step {a b : G}
      (ha : a ∈ (T.subgroupB : Set G) ∪ ⋃ s ∈ J, T.bruhatCell (s : T.WeylGroup))
      (hb : ∀ {c : G} {w : T.WeylGroup}, c ∈ T.bruhatCell w →
        ∃ v ∈ Subgroup.closure (Subtype.val '' J), b * c ∈ T.bruhatCell (v * w)) :
      ∀ {c : G} {w : T.WeylGroup}, c ∈ T.bruhatCell w →
        ∃ v ∈ Subgroup.closure (Subtype.val '' J), (a * b) * c ∈ T.bruhatCell (v * w) := by
    intro c w hc
    obtain ⟨v, hv, hbc⟩ := hb hc
    rcases ha with ha | ha
    · refine ⟨v, hv, ?_⟩
      rw [mul_assoc, ← T.subgroupB_mul_bruhatCell]
      exact Set.mul_mem_mul ha hbc
    · obtain ⟨s, hs, has⟩ := Set.mem_iUnion₂.mp ha
      have h := T.bruhatCell_mul_subset_union_of_mem_simple s.property (v * w)
        (Set.mul_mem_mul has hbc)
      rcases h with h | h
      · exact ⟨s * v, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨s, hs, rfl⟩) hv,
          by simpa only [mul_assoc] using h⟩
      · exact ⟨v, hv, by simpa only [mul_assoc] using h⟩
  rw [T.standardParabolic_def] at ha
  induction ha using Subgroup.closure_induction_left with
  | one =>
      intro b w hb
      exact ⟨1, Subgroup.one_mem _, by simpa using hb⟩
  | mul_left a ha b _ ih => exact step ha ih
  | inv_mul_cancel a ha b _ ih =>
      intro c w hc
      refine step (a := a⁻¹) ?_ (fun {c} {w} ↦ ih) hc
      rcases ha with ha | ha
      · exact Or.inl (T.subgroupB.inv_mem ha)
      · obtain ⟨s, hs, has⟩ := Set.mem_iUnion₂.mp ha
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨s, hs, by
          simpa only [T.inv_bruhatCell, T.inv_simple s.property] using
            Set.inv_mem_inv.mpr has⟩)

/-- Left multiplication by `P_J` collects exactly the Bruhat cells in the Weyl left coset
`W_J w`. -/
theorem mem_standardParabolic_mul_bruhatCell_iff (J : Set T.simple) (w : T.WeylGroup)
    (g : G) :
    g ∈ (T.standardParabolic J : Set G) * T.bruhatCell w ↔
      ∃ v ∈ Subgroup.closure (Subtype.val '' J), g ∈ T.bruhatCell (v * w) := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact T.exists_mem_weylClosure_bruhatCell_mul ha hb
  · rintro ⟨v, hv, hg⟩
    suffices h : ∀ {g : G}, g ∈ T.bruhatCell (v * w) →
        g ∈ (T.standardParabolic J : Set G) * T.bruhatCell w from h hg
    clear hg g
    have step {s : T.simple} (hs : s ∈ J) {v : T.WeylGroup}
        (ih : ∀ {g : G}, g ∈ T.bruhatCell (v * w) →
          g ∈ (T.standardParabolic J : Set G) * T.bruhatCell w) :
        ∀ {g : G}, g ∈ T.bruhatCell ((s * v) * w) →
          g ∈ (T.standardParabolic J : Set G) * T.bruhatCell w := by
      intro g hg
      rw [mul_assoc] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        T.subset_bruhatCell_mul_of_mem_simple s.property (v * w) hg
      obtain ⟨c, hc, d, hd, rfl⟩ := ih hb
      exact ⟨a * c, (T.standardParabolic J).mul_mem
        (T.bruhatCell_subset_standardParabolic hs ha) hc, d, hd, by simp [mul_assoc]⟩
    induction hv using Subgroup.closure_induction_left with
    | one =>
        intro g hg
        exact ⟨1, (T.standardParabolic J).one_mem, g, by simpa using hg, one_mul g⟩
    | mul_left s hs v _ ih =>
        obtain ⟨s, hs, rfl⟩ := hs
        intro g hg
        exact step hs (fun {g} ↦ ih) hg
    | inv_mul_cancel s hs v _ ih =>
        obtain ⟨s, hs, rfl⟩ := hs
        rw [T.inv_simple s.property]
        intro g hg
        exact step hs (fun {g} ↦ ih) hg

/-- Right multiplication by `P_K` collects exactly the Bruhat cells in the Weyl right coset
`w W_K`. -/
theorem mem_bruhatCell_mul_standardParabolic_iff (K : Set T.simple) (w : T.WeylGroup)
    (g : G) :
    g ∈ T.bruhatCell w * (T.standardParabolic K : Set G) ↔
      ∃ v ∈ Subgroup.closure (Subtype.val '' K), g ∈ T.bruhatCell (w * v) := by
  have hinv : g ∈ T.bruhatCell w * (T.standardParabolic K : Set G) ↔
      g⁻¹ ∈ (T.standardParabolic K : Set G) * T.bruhatCell w⁻¹ := by
    simpa only [mul_inv_rev, inv_coe_set, Subgroup.coe_inv, T.inv_bruhatCell] using
      (Set.inv_mem_inv (a := g)
        (s := T.bruhatCell w * (T.standardParabolic K : Set G))).symm
  rw [hinv, T.mem_standardParabolic_mul_bruhatCell_iff]
  constructor
  · rintro ⟨v, hv, hg⟩
    refine ⟨v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
    have h := Set.inv_mem_inv.mpr hg
    simpa only [T.inv_bruhatCell, mul_inv_rev, inv_inv] using h
  · rintro ⟨v, hv, hg⟩
    refine ⟨v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
    have h := Set.inv_mem_inv.mpr hg
    simpa only [T.inv_bruhatCell, mul_inv_rev] using h

/-- A parabolic double coset is precisely the union of the Bruhat cells indexed by the
corresponding Weyl double coset. The representative may be any element of its Bruhat cell. -/
theorem mem_doubleCoset_standardParabolic_iff (J K : Set T.simple)
    {n g : G} {w : T.WeylGroup} (hn : n ∈ T.bruhatCell w) :
    g ∈ DoubleCoset.doubleCoset n (T.standardParabolic J) (T.standardParabolic K) ↔
      ∃ v ∈ DoubleCoset.doubleCoset w
        (Subgroup.closure (Subtype.val '' J)) (Subgroup.closure (Subtype.val '' K)),
        g ∈ T.bruhatCell v := by
  constructor
  · rintro hg
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    obtain ⟨u, hu, hau⟩ := (T.mem_standardParabolic_mul_bruhatCell_iff J w (a * n)).mp
      (Set.mul_mem_mul ha hn)
    obtain ⟨v, hv, hgv⟩ := (T.mem_bruhatCell_mul_standardParabolic_iff K (u * w) _).mp
      (Set.mul_mem_mul hau hb)
    exact ⟨u * w * v, DoubleCoset.mem_doubleCoset.mpr ⟨u, hu, v, hv, rfl⟩, hgv⟩
  · rintro ⟨v, hv, hgv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hv
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      (T.mem_bruhatCell_mul_standardParabolic_iff K (a * w) g).mpr ⟨b, hb, hgv⟩
    obtain ⟨z, hz, t, ht, rfl⟩ :=
      (T.mem_standardParabolic_mul_bruhatCell_iff J w x).mpr ⟨a, ha, hx⟩
    rw [T.bruhatCell_eq_doubleCoset hn] at ht
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.mp ht
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨z * c, (T.standardParabolic J).mul_mem hz (T.subgroupB_le_standardParabolic J hc),
        d * y, (T.standardParabolic K).mul_mem (T.subgroupB_le_standardParabolic K hd) hy,
        by simp [mul_assoc]⟩

/-- For elements with known Bruhat indices, parabolic double-coset membership is exactly
Weyl double-coset membership. -/
theorem mem_doubleCoset_standardParabolic_iff_of_mem_bruhatCell
    (J K : Set T.simple) {n g : G} {w v : T.WeylGroup}
    (hn : n ∈ T.bruhatCell w) (hg : g ∈ T.bruhatCell v) :
    g ∈ DoubleCoset.doubleCoset n (T.standardParabolic J) (T.standardParabolic K) ↔
      v ∈ DoubleCoset.doubleCoset w
        (Subgroup.closure (Subtype.val '' J)) (Subgroup.closure (Subtype.val '' K)) := by
  rw [T.mem_doubleCoset_standardParabolic_iff J K hn]
  exact ⟨fun ⟨u, hu, hgu⟩ ↦ T.eq_of_mem_bruhatCell_of_mem hgu hg ▸ hu,
    fun hv ↦ ⟨v, hv, hg⟩⟩

/-- Equality of standard-parabolic double cosets is equality of the corresponding Weyl
double cosets. -/
theorem doubleCosetMk_standardParabolic_eq_iff (J K : Set T.simple)
    {n g : G} {w v : T.WeylGroup}
    (hn : n ∈ T.bruhatCell w) (hg : g ∈ T.bruhatCell v) :
    DoubleCoset.mk (T.standardParabolic J) (T.standardParabolic K) g =
        DoubleCoset.mk (T.standardParabolic J) (T.standardParabolic K) n ↔
      DoubleCoset.mk (Subgroup.closure (Subtype.val '' J))
          (Subgroup.closure (Subtype.val '' K)) v =
        DoubleCoset.mk (Subgroup.closure (Subtype.val '' J))
          (Subgroup.closure (Subtype.val '' K)) w := by
  rw [doubleCosetMk_eq_mk_iff_mem, doubleCosetMk_eq_mk_iff_mem]
  exact T.mem_doubleCoset_standardParabolic_iff_of_mem_bruhatCell J K hn hg

/-- The Weyl double cosets `W_J \ W / W_K` classify standard-parabolic double cosets
`P_J \ G / P_K`. The image of a Weyl class is the class of any element of its Bruhat cell. -/
noncomputable def parabolicDoubleCosetEquiv (J K : Set T.simple) :
    DoubleCoset.Quotient (Subgroup.closure (Subtype.val '' J) : Set T.WeylGroup)
        (Subgroup.closure (Subtype.val '' K)) ≃
      DoubleCoset.Quotient (T.standardParabolic J : Set G) (T.standardParabolic K) := by
  classical
  let r (w : T.WeylGroup) := Classical.choose (T.exists_mem_bruhatCell w)
  have hr (w : T.WeylGroup) : (r w : G) ∈ T.bruhatCell w :=
    (Classical.choose_spec (T.exists_mem_bruhatCell w)).2
  let f (w : T.WeylGroup) :=
    DoubleCoset.mk (T.standardParabolic J) (T.standardParabolic K) (r w : G)
  have hf (w v : T.WeylGroup) : f w = f v ↔
      DoubleCoset.mk (Subgroup.closure (Subtype.val '' J))
          (Subgroup.closure (Subtype.val '' K)) w =
        DoubleCoset.mk (Subgroup.closure (Subtype.val '' J))
          (Subgroup.closure (Subtype.val '' K)) v :=
    T.doubleCosetMk_standardParabolic_eq_iff J K (hr v) (hr w)
  let F := Quotient.lift f (fun w v h ↦ (hf w v).mpr (Quotient.sound h))
  apply Equiv.ofBijective F
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h w =>
      induction y using Quotient.inductionOn with
      | h v => exact (hf w v).mp
  · intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨w, hw, _⟩ := T.existsUnique_mem_bruhatCell g
      exact ⟨DoubleCoset.mk _ _ w,
        (T.doubleCosetMk_standardParabolic_eq_iff J K hw (hr w)).mpr rfl⟩

/-- The parabolic double-coset equivalence sends a Weyl element to the class of any point
in its Bruhat cell. This characterization is independent of normalizer representatives. -/
theorem parabolicDoubleCosetEquiv_apply_mk (J K : Set T.simple)
    {w : T.WeylGroup} {g : G} (hg : g ∈ T.bruhatCell w) :
    T.parabolicDoubleCosetEquiv J K
        (DoubleCoset.mk (Subgroup.closure (Subtype.val '' J))
          (Subgroup.closure (Subtype.val '' K)) w) =
      DoubleCoset.mk (T.standardParabolic J) (T.standardParabolic K) g := by
  classical
  -- Evaluate the quotient lift on a representative. Cell uniqueness removes the chosen lift.
  unfold parabolicDoubleCosetEquiv
  exact (T.doubleCosetMk_standardParabolic_eq_iff J K hg
    (Classical.choose_spec (T.exists_mem_bruhatCell w)).2).mpr rfl

end TauCeti.TitsSystem
