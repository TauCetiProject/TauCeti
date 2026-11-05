/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BigPowers
public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Extensions of centralizers are discriminated by their retractions

Let `G` be a CSA group with the big powers property and let `u ≠ 1`. The retractions
`ξₖ : G(u, ℤ) →* G` of the extension of the centralizer of `u` that fix `G` and send the new letter
`t` to `u ^ k` discriminate `G(u, ℤ)` by `G`: every nonidentity element survives under `ξₖ` for all
large `k` (`TauCeti.LimitGroup.CentralizerExt.eventually_retraction_ne_one`). Consequently
`G(u, ℤ)` is discriminated by `G` over `G`, and extending the centralizer of a nonidentity element
of a fully residually free group gives a fully residually free group. These are the rank-one steps
of iterated extensions of centralizers.

Neither `u` being a proper power nor `G` being nonabelian matters here: for central `u` the
extension is `G × ℤ`, and the statement reduces to torsion-freeness.

The proof writes an element of the amalgam `G ∗_{C} (C × ℤ)`, `C = C_G(u)`, in normal form, so its
image under `ξₖ` is an alternating product `g₀ u ^ (k e₁) g₁ ⋯ u ^ (k eₘ) gₘ` with every `eᵢ ≠ 0`
and every interior `gᵢ ∉ C`. Collecting the prefixes, this is `H₁ ^ k ⋯ Hₘ ^ k * z` for conjugates
`Hᵢ` of nonzero powers of `u` with consecutive `Hᵢ` not commuting, by malnormality of `C`, and a
fixed `z`. If `P = H₁ ^ k ⋯ Hₘ ^ k` equals `z⁻¹`, then `P * Y ^ k * P⁻¹ * Z ^ k = 1` for a suitable
conjugate `Y` of `u` and `Z = z⁻¹ * Y⁻¹ * z`, contradicting the big powers property; for `m = 1`,
torsion-freeness suffices (`Group.IsBP.exists_prod_map_pow_mul_ne_one`).

## Main results

* `TauCeti.LimitGroup.CentralizerExt.eventually_retraction_ne_one`: a nonidentity element of
  `G(u, ℤ)` survives under `t ↦ u ^ k` for all large `k`.
* `TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`: `G(u, ℤ)` is discriminated by `G` over
  `G`.
* `TauCeti.LimitGroup.isFullyResiduallyFree_centralizerExt`: extensions of centralizers of
  nonidentity elements of fully residually free groups are fully residually free.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
-/

public section

open Filter Group Subgroup

namespace TauCeti.LimitGroup

variable {G : Type*} [Group G]

section Prefixes

variable (u : G)

/-- For a base point `B` and a list of pairs `(bᵢ, eᵢ)`, the conjugates `Bᵢ * u ^ eᵢ * Bᵢ⁻¹` with
`Bᵢ = B * b₀ * ⋯ * bᵢ`, over the indices with `eᵢ ≠ 0`. -/
private def conjs : G → List (G × ℤ) → List G
  | _, [] => []
  | B, p :: l =>
    if p.2 = 0 then conjs (B * p.1) l else B * p.1 * u ^ p.2 * (B * p.1)⁻¹ :: conjs (B * p.1) l

/-- Collecting prefixes: `B * ∏ (bᵢ * (u ^ eᵢ) ^ k)` is the product of the `k`-th powers of the
conjugates `conjs u B l`, followed by `B * ∏ bᵢ`. -/
private theorem mul_prod_eq (k : ℕ) : ∀ (B : G) (l : List (G × ℤ)),
    B * (l.map fun p => p.1 * (u ^ p.2) ^ k).prod =
      ((conjs u B l).map (· ^ k)).prod * (B * (l.map Prod.fst).prod)
  | B, [] => by simp [conjs]
  | B, p :: l => by
    have ih := mul_prod_eq k (B * p.1) l
    by_cases hp : p.2 = 0
    · simp only [conjs, hp, ↓reduceIte, List.map_cons, List.prod_cons, zpow_zero, one_pow, mul_one]
      rw [← mul_assoc, ih, mul_assoc]
    · simp only [conjs, hp, ↓reduceIte, List.map_cons, List.prod_cons, conj_pow]
      rw [show B * (p.1 * (u ^ p.2) ^ k * (l.map fun p => p.1 * (u ^ p.2) ^ k).prod) =
          B * p.1 * (u ^ p.2) ^ k * (B * p.1)⁻¹ *
            (B * p.1 * (l.map fun p => p.1 * (u ^ p.2) ^ k).prod) by group, ih]
      simp only [mul_assoc]

private theorem exists_eq_conj_of_mem_conjs : ∀ {B : G} {l : List (G × ℤ)},
    ∀ H ∈ conjs u B l, ∃ y : G, ∃ e : ℤ, e ≠ 0 ∧ H = y * u ^ e * y⁻¹
  | _, [] => by simp [conjs]
  | B, p :: l => by
    intro H hH
    by_cases hp : p.2 = 0
    · simp only [conjs, hp, ↓reduceIte] at hH
      exact exists_eq_conj_of_mem_conjs H hH
    · simp only [conjs, hp, ↓reduceIte, List.mem_cons] at hH
      rcases hH with rfl | hH
      · exact ⟨B * p.1, p.2, hp, rfl⟩
      · exact exists_eq_conj_of_mem_conjs H hH

private theorem conjs_eq_nil_iff : ∀ {B : G} {l : List (G × ℤ)},
    conjs u B l = [] ↔ ∀ p ∈ l, p.2 = 0
  | _, [] => by simp [conjs]
  | B, p :: l => by
    by_cases hp : p.2 = 0
    · simp [conjs, hp, conjs_eq_nil_iff]
    · simp [conjs, hp]

variable {u}

/-- For a list alternating between pairs `(b, 0)` with `b ∉ C_G(u)` and pairs `(c, e)` with
`c ∈ C_G(u)` and `e ≠ 0`, consecutive entries of `conjs u B l` do not commute, and if `l` starts
with a pair `(b, 0)` the first entry of `conjs u B l` is a conjugate of a power of `u` by `B * y`
with `y ∉ C_G(u)`. -/
private theorem isChain_conjs_aux (hG : IsCSA G) [IsMulTorsionFree G] (hu : u ≠ 1) :
    ∀ {B : G} {l : List (G × ℤ)}, (∀ p ∈ l, (p.2 = 0 ↔ p.1 ∉ centralizer {u})) →
      l.IsChain (fun p q => (p.2 = 0 ↔ q.2 ≠ 0)) →
      (conjs u B l).IsChain (fun x y => ¬Commute x y) ∧
        ∀ p ∈ l.head?, p.2 = 0 → ∀ H ∈ (conjs u B l).head?,
          ∃ y ∉ centralizer {u}, ∃ e : ℤ, e ≠ 0 ∧ H = B * y * u ^ e * (B * y)⁻¹
  | _, [], _, _ => by simp [conjs]
  | B, p :: l, hl, halt => by
    have hl' : ∀ q ∈ l, (q.2 = 0 ↔ q.1 ∉ centralizer {u}) := fun q hq =>
      hl q (List.mem_cons_of_mem _ hq)
    have halt' := (List.isChain_cons.1 halt).2
    obtain ⟨ihc, ihh⟩ := isChain_conjs_aux hG hu (B := B * p.1) hl' halt'
    by_cases hp : p.2 = 0
    · simp only [conjs, hp, ↓reduceIte]
      refine ⟨ihc, fun _ _ _ H hH => ?_⟩
      -- The next pair, if any, is `(c, e)` with `c ∈ C_G(u)` and `e ≠ 0`.
      rcases l with _ | ⟨q, l⟩
      · simp [conjs] at hH
      · have hq : q.2 ≠ 0 := ((List.isChain_cons_cons.1 halt).1).1 hp
        have hp1 : p.1 ∉ centralizer {u} := (hl p List.mem_cons_self).1 hp
        have hq1 : q.1 ∈ centralizer {u} := by
          by_contra h
          exact hq ((hl' q List.mem_cons_self).2 h)
        simp only [conjs, hq, ↓reduceIte, List.head?_cons, Option.mem_def, Option.some.injEq] at hH
        refine ⟨p.1 * q.1, fun h => hp1 ?_, q.2, hq, by rw [← hH]; group⟩
        simpa using mul_mem h (inv_mem hq1)
    · simp only [conjs, hp, ↓reduceIte]
      refine ⟨List.isChain_cons.2 ⟨fun H hH => ?_, ihc⟩, fun _ h hp' => absurd hp' (by
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h
        exact h ▸ hp)⟩
      -- The next pair is `(b, 0)` with `b ∉ C_G(u)`.
      rcases l with _ | ⟨q, l⟩
      · simp [conjs] at hH
      · have hq : q.2 = 0 := by
          have := ((List.isChain_cons_cons.1 halt).1).not.1 hp
          simpa using this
        obtain ⟨y, hy, e, he, rfl⟩ := ihh q (by simp) hq H hH
        exact hG.not_commute_conj_zpow hu hp he (by simpa [mul_assoc] using hy)

end Prefixes

namespace CentralizerExt

variable {u : G}

/-- The base part and the exponent of a letter of the amalgam `G ∗_C (C × ℤ)`, `C = C_G(u)`: a
letter `g` of `G` gives `(g, 0)` and a letter `(c, tᵉ)` of `C × ℤ` gives `(c, e)`. -/
private def letterPair : (Σ b, CentralizerExtFactor u 1 b) → G × ℤ
  | ⟨false, g⟩ => (g, 0)
  | ⟨true, p⟩ => (p.1, (p.2 0).toAdd)

private theorem retraction_of_letter (k : ℕ) (a : Σ b, CentralizerExtFactor u 1 b) :
    retraction (fun _ => (k : ℤ)) (Monoid.PushoutI.of (φ := centralizerExtMap u 1) a.1 a.2) =
      (letterPair a).1 * (u ^ (letterPair a).2) ^ k := by
  rcases a with ⟨_ | _, g⟩
  · simp only [letterPair, zpow_zero, one_pow, mul_one]
    exact (congrArg _ (DFunLike.congr_fun of_def g).symm).trans (retraction_of _ g)
  · obtain ⟨c, v⟩ := g
    have hv : v = Pi.mulSingle 0 (.ofAdd 1) ^ (v 0).toAdd := by
      ext i
      fin_cases i
      simp
    have ht : zpowersPiHom t commute_t_t v = (t 0 : CentralizerExt u 1) ^ (v 0).toAdd := by
      conv_lhs => rw [hv]
      rw [map_zpow, zpowersPiHom_mulSingle]
    rw [pushoutI_of_true, ht, map_mul, map_zpow, retraction_of, retraction_t]
    simp [letterPair, ← zpow_natCast, ← zpow_mul, mul_comm]

/-- The letters of a normal word of `G(u, ℤ)` lie outside the image of `C_G(u)` in their factor: a
letter of `G` gives a pair
`(b, 0)` with `b ∉ C_G(u)` and a letter of `C_G(u) × ℤ` a pair `(c, e)` with `c ∈ C_G(u)` and
`e ≠ 0`. -/
private theorem letterPair_snd_eq_zero_iff
    {d : Monoid.PushoutI.NormalWord.Transversal (centralizerExtMap u 1)}
    (w : Monoid.PushoutI.NormalWord d) {a : Σ b, CentralizerExtFactor u 1 b} (ha : a ∈ w.toList) :
    ((letterPair a).2 = 0 ↔ a.1 = false) ∧
      ((letterPair a).2 = 0 ↔ (letterPair a).1 ∉ centralizer {u}) := by
  -- A letter of a normal word is a nonidentity element of the transversal, hence not in `C_G(u)`.
  have hred : a.2 ∉ (centralizerExtMap u 1 a.1).range := by
    intro hmem
    apply w.ne_one a ha
    have h₁ := (d.compl a.1).equiv_snd_eq_self_of_mem_of_one_mem (one_mem _)
      (w.normalized a.1 a.2 ha)
    have h₂ := (d.compl a.1).equiv_snd_eq_one_of_mem_of_one_mem (d.one_mem a.1) hmem
    exact congrArg Subtype.val (h₁.symm.trans h₂)
  rcases a with ⟨_ | _, g⟩
  · simpa [letterPair] using hred
  · obtain ⟨c, v⟩ := g
    have hv : (v 0).toAdd ≠ 0 := by
      intro h0
      refine hred ⟨c, ?_⟩
      rw [centralizerExtMap_true, MonoidHom.inl_apply]
      refine Prod.ext rfl (funext fun i => ?_)
      fin_cases i
      simpa using (congrArg Multiplicative.ofAdd h0).symm
    simp [letterPair, hv]

/-- The image of a normal word under `t ↦ u ^ k`, with its prefixes collected. -/
private theorem retraction_prod {d : Monoid.PushoutI.NormalWord.Transversal
    (centralizerExtMap u 1)} (w : Monoid.PushoutI.NormalWord d) (k : ℕ) :
    retraction (fun _ => (k : ℤ)) w.prod =
      ((conjs u w.head (w.toList.map letterPair)).map (· ^ k)).prod *
        (w.head * ((w.toList.map letterPair).map Prod.fst).prod) := by
  rw [Monoid.PushoutI.NormalWord.prod, map_mul, ← mul_prod_eq,
    ← Monoid.PushoutI.of_apply_eq_base (centralizerExtMap u 1) false]
  congr 1
  · rw [← of_def, retraction_of, centralizerExtMap_false, Subgroup.coe_subtype]
  · simp [Monoid.CoprodI.Word.prod, map_list_prod, Function.comp_def, retraction_of_letter]

/-- **Extensions of centralizers are discriminated by their retractions.** Let `G` be a CSA group
with the big powers property and `u ≠ 1`. Every nonidentity element of `G(u, ℤ)` survives under
the retraction `t ↦ u ^ k` for all large `k`. -/
theorem eventually_retraction_ne_one (hG : IsCSA G) (hBP : IsBP G) (hu : u ≠ 1)
    {x : CentralizerExt u 1} (hx : x ≠ 1) :
    ∀ᶠ k : ℤ in atTop, retraction (fun _ => k) x ≠ 1 := by
  classical
  have := hBP.isMulTorsionFree
  obtain ⟨d⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty (centralizerExtMap u 1)
    (centralizerExtMap_injective u 1)
  -- Write `x` in normal form and record its letters as pairs `(b, e)`.
  set w := Monoid.PushoutI.NormalWord.equiv (d := d) x
  have hxw : w.prod = x := Monoid.PushoutI.NormalWord.equiv.symm_apply_apply x
  set l := w.toList.map letterPair
  have hl : ∀ p ∈ l, (p.2 = 0 ↔ p.1 ∉ centralizer {u}) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
    exact (letterPair_snd_eq_zero_iff w ha).2
  have halt : l.IsChain fun p q => (p.2 = 0 ↔ q.2 ≠ 0) := by
    rw [List.isChain_map]
    refine (List.IsChain.iff_mem.1 w.chain_ne).imp fun a b ⟨ha, hb, hab⟩ => ?_
    rw [ne_eq, (letterPair_snd_eq_zero_iff w ha).1, (letterPair_snd_eq_zero_iff w hb).1]
    obtain ⟨_ | _, _⟩ := a <;> obtain ⟨_ | _, _⟩ := b <;> simp_all
  by_cases hHs : conjs u w.head l = []
  · -- Without letters from `C_G(u) × ℤ`, the image of `x` does not depend on `k`; by
    -- alternation `x` is `c₀` or `c₀ * g` with `c₀ ∈ C_G(u)` and `g ∉ C_G(u)`.
    have hz : (w.head : G) * (l.map Prod.fst).prod ≠ 1 := by
      have hall := (conjs_eq_nil_iff u).1 hHs
      rcases hl0 : l with _ | ⟨p, _ | ⟨q, l'⟩⟩
      · simp only [List.map_nil, List.prod_nil, mul_one]
        intro h
        apply hx
        have hw : w.toList = [] := by simpa [l] using hl0
        rw [← hxw, Monoid.PushoutI.NormalWord.prod, Monoid.CoprodI.Word.prod, hw]
        simp [OneMemClass.coe_eq_one.1 h]
      · have hp := (hl p (by simp [hl0])).1 (hall p (by simp [hl0]))
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        intro h
        exact hp (by rw [eq_inv_of_mul_eq_one_right h]; exact inv_mem w.head.2)
      · rw [hl0] at halt hall
        exact absurd (hall q (by simp)) ((List.isChain_cons_cons.1 halt).1.1
          (hall p (by simp)))
    refine eventually_atTop.2 ⟨0, fun k hk => ?_⟩
    lift k to ℕ using hk
    rw [← hxw, retraction_prod, hHs, List.map_nil, List.prod_nil, one_mul]
    exact hz
  · obtain ⟨N, hN⟩ := hBP.exists_prod_map_pow_mul_ne_one hG hu hHs
      (exists_eq_conj_of_mem_conjs u) (isChain_conjs_aux hG hu hl halt).1 _
    refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
    lift k to ℕ using by omega
    rw [← hxw, retraction_prod]
    exact hN k (by omega)

/-- **Extensions of centralizers are discriminated by the base group.** For a CSA group `G` with
the big powers property and `u ≠ 1`, `G(u, ℤ)` is discriminated by `G` over `G`: finitely many
nonidentity elements survive under one retraction `t ↦ u ^ k`. -/
theorem isDiscriminatedBy (hG : IsCSA G) (hBP : IsBP G) (hu : u ≠ 1) :
    GroupAlgGeom.IsDiscriminatedBy (of : G →* CentralizerExt u 1) (MonoidHom.id G) := by
  refine (GroupAlgGeom.isDiscriminatedBy_def _ _).2 fun s hs => ?_
  obtain ⟨k, hk⟩ := ((eventually_all_finset s).2 fun x hx =>
    eventually_retraction_ne_one hG hBP hu (hs x hx)).exists
  exact ⟨⟨retraction fun _ => k, fun g => retraction_of _ g⟩, hk⟩

end CentralizerExt

/-- Extending the centralizer of a nonidentity element of a fully residually free group gives a
fully residually free group. -/
theorem isFullyResiduallyFree_centralizerExt (hG : IsFullyResiduallyFree G) {u : G}
    (hu : u ≠ 1) : IsFullyResiduallyFree (CentralizerExt u 1) := by
  classical
  refine isFullyResiduallyFree_def.2 fun s hs => ?_
  obtain ⟨φ, hφ⟩ := (GroupAlgGeom.isDiscriminatedBy_def _ _).1
    (CentralizerExt.isDiscriminatedBy hG.isCSA hG.isBP hu) s hs
  obtain ⟨ι, ψ, hψ⟩ := isFullyResiduallyFree_def.1 hG (s.image φ) (by simpa using hφ)
  exact ⟨ι, ψ.comp φ, fun x hx => hψ _ (Finset.mem_image_of_mem _ hx)⟩

end TauCeti.LimitGroup
