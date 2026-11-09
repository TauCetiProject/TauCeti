/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
public import Mathlib.Data.Matrix.Mul
import TauCeti.Data.Matrix.DotProduct

/-!
# Extensions of centralizers are discriminated by the base group

Let `G` be a CSA group with the big powers property, for instance a fully residually free group,
and let `u ≠ 1`. The retractions `G(u, ℤⁿ) →* G`, `tᵢ ↦ u ^ kᵢ`, of the extension
`G(u, ℤⁿ) = G ∗_{C_G(u)} (C_G(u) × ℤⁿ)` of the centralizer of `u` discriminate it by `G`. More
precisely, a nonidentity element of `G(u, ℤⁿ)` survives under `tᵢ ↦ u ^ (m * wᵢ)` for all large
`m`, along every direction `w ∈ ℤⁿ` off finitely many hyperplanes. Since finitely many hyperplanes
never cover `ℤⁿ`, any finite family of nonidentity elements survives under a single such
retraction. In particular `G(u, ℤⁿ)` is fully residually free whenever `G` is. The hypothesis
`u ≠ 1` cannot be dropped: for `u = 1` every retraction kills the new letters.

For `n = 1` every nonzero direction qualifies, so a nonidentity element of `G(u, ℤ)` survives
under `t ↦ u ^ k` for every large `k`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.exists_finset_forall_retraction_smul_ne_one`: a nonidentity
  element of `G(u, ℤⁿ)` survives under `tᵢ ↦ u ^ (m * wᵢ)` for all large `m`, whenever `w` avoids
  finitely many hyperplanes.
* `TauCeti.LimitGroup.CentralizerExt.exists_forall_retraction_ne_one`: a nonidentity element of
  `G(u, ℤ)` survives under the retraction `t ↦ u ^ k` for every large `k`.
* `TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`: `G(u, ℤⁿ)` is discriminated by `G` over
  `G`.
* `TauCeti.LimitGroup.isFullyResiduallyFree_centralizerExt`: an extension of the centralizer of a
  nonidentity element of a fully residually free group is fully residually free.

## Implementation notes

An element of the amalgam `G(u, ℤⁿ)` is `h * a₁ * ⋯ * aᵣ` with `h ∈ C_G(u)` and letters `aⱼ`
alternately in `G ∖ C_G(u)` and in `(C_G(u) × ℤⁿ) ∖ C_G(u)` (Mathlib's
`Monoid.PushoutI.NormalWord`). A letter `(c, v)` of the second factor, with `v ≠ 0`, maps to
`c * u ^ (m * (w ⬝ᵥ v))`. Since `c` commutes with `u`, the image of the element is an alternating
product `g * u ^ (m * e₁) * g₁ * ⋯ * u ^ (m * eₛ) * gₛ` with `eⱼ = w ⬝ᵥ vⱼ` and separators `gⱼ`
outside `C_G(u)`, except possibly the last. It is nontrivial for all large `m` by the big powers
property (`Group.IsBP.exists_forall_mul_prod_ne_one`) as soon as every `eⱼ` is nonzero. When no
letter of the second factor occurs, the element lies in `G` and is fixed by every retraction.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II*,
  J. Algebra 200 (1998), §0, Lemma 2 and Theorem 1.
-/

public section

open Group Subgroup

namespace TauCeti.LimitGroup

open GroupAlgGeom

namespace CentralizerExt

variable {G : Type*} [Group G] {u : G} {n : ℕ}

/-- The retraction `tᵢ ↦ u ^ kᵢ` sends `∏ tᵢ ^ vᵢ` to `u ^ (k ⬝ᵥ v)`. -/
private theorem retraction_zpowersPiHom (k : Fin n → ℤ) (v : Fin n → Multiplicative ℤ) :
    retraction k (zpowersPiHom t commute_t_t v : CentralizerExt u n) =
      u ^ (k ⬝ᵥ fun i => (v i).toAdd) := by
  let f : (Fin n → Multiplicative ℤ) →* G :=
    { toFun v := u ^ (k ⬝ᵥ fun i => (v i).toAdd)
      map_one' := by simp [dotProduct]
      map_mul' v v' := by simp [dotProduct, mul_add, Finset.sum_add_distrib, zpow_add] }
  have hf : (retraction (u := u) k).comp (zpowersPiHom t commute_t_t) = f := by
    refine MonoidHom.pi_ext_mint fun i => ?_
    have hi : (fun j => ((Pi.mulSingle i (.ofAdd 1) : Fin n → Multiplicative ℤ) j).toAdd) =
        Pi.single i 1 := by
      funext j
      by_cases h : j = i <;> simp [h]
    simp [f, hi]
  exact DFunLike.congr_fun hf v

/-- The retraction `tᵢ ↦ u ^ kᵢ` fixes the letters of the factor `G`. -/
private theorem retraction_pushoutI_of_false (k : Fin n → ℤ) (g : G) :
    retraction k (Monoid.PushoutI.of (φ := centralizerExtMap u n) false g) = g := by
  rw [← of_def, retraction_of]

/-- The image of a letter `(c, v)` of the factor `C_G(u) × ℤⁿ` under `tᵢ ↦ u ^ kᵢ`. -/
private theorem retraction_pushoutI_of_true (k : Fin n → ℤ)
    (p : centralizer {u} × (Fin n → Multiplicative ℤ)) :
    retraction k (Monoid.PushoutI.of (φ := centralizerExtMap u n) true p) =
      p.1 * u ^ (k ⬝ᵥ fun i => (p.2 i).toAdd) := by
  rw [pushoutI_of_true, map_mul, retraction_of, retraction_zpowersPiHom]

/-- The data fed to the big powers property by a list of letters of `G(u, ℤⁿ)`: a leading factor,
and for every letter `(c, v)` of `C_G(u) × ℤⁿ` its exponent vector `v` together with the separator
`c * g`, where `g` is the product of the letters of `G` up to the next letter of `C_G(u) × ℤⁿ`. -/
private def bpData : List (Σ b, CentralizerExtFactor u n b) → G × List ((Fin n → ℤ) × G)
  | [] => (1, [])
  | ⟨false, g⟩ :: L => ((show G from g) * (bpData L).1, (bpData L).2)
  | ⟨true, p⟩ :: L =>
    (1, ((fun i => (p.2 i).toAdd), (p.1 : G) * (bpData L).1) :: (bpData L).2)

/-- The image of a product of letters under `tᵢ ↦ u ^ kᵢ`, in terms of `bpData`. -/
private theorem prod_map_retraction_eq (k : Fin n → ℤ)
    (L : List (Σ b, CentralizerExtFactor u n b)) :
    (L.map fun l => retraction k (Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2)).prod =
      (bpData L).1 * ((bpData L).2.map fun q => u ^ (k ⬝ᵥ q.1) * q.2).prod := by
  induction L with
  | nil => simp [bpData]
  | cons l L ih =>
    obtain ⟨_ | _, g⟩ := l
    · simp only [List.map_cons, List.prod_cons, ih, bpData, retraction_pushoutI_of_false]
      exact (mul_assoc _ _ _).symm
    · -- `c * u ^ e = u ^ e * c`, because `c` commutes with `u`.
      have hc : Commute (g.1 : G) u := mem_centralizer_singleton_iff.mp g.1.2
      simp only [List.map_cons, List.prod_cons, ih, bpData, retraction_pushoutI_of_true, one_mul,
        mul_assoc, (hc.zpow_right _).eq]

/-- If `bpData` records no letter of `C_G(u) × ℤⁿ`, then every letter lies in `G`. -/
private theorem fst_eq_false_of_bpData_snd_eq_nil {L : List (Σ b, CentralizerExtFactor u n b)}
    (h : (bpData L).2 = []) : ∀ l ∈ L, l.1 = false := by
  induction L with
  | nil => simp
  | cons l L ih =>
    obtain ⟨_ | _, g⟩ := l
    · simpa [bpData, ih h] using ih h
    · simp [bpData] at h

/-- The exponent vectors recorded by `bpData` are nonzero when no letter of `C_G(u) × ℤⁿ` lies in
`C_G(u)`. -/
private theorem ne_zero_of_mem_bpData_snd {L : List (Σ b, CentralizerExtFactor u n b)}
    (hL : ∀ l ∈ L, l.2 ∉ (centralizerExtMap u n l.1).range) :
    ∀ q ∈ (bpData L).2, q.1 ≠ 0 := by
  induction L with
  | nil => simp [bpData]
  | cons l L ih =>
    have ih := ih fun l hl => hL l (List.mem_cons_of_mem _ hl)
    obtain ⟨_ | _, p⟩ := l
    · simpa [bpData] using ih
    · simp only [bpData, List.mem_cons, forall_eq_or_imp]
      refine ⟨fun h => hL _ List.mem_cons_self ⟨p.1, ?_⟩, ih⟩
      rw [centralizerExtMap_true, MonoidHom.inl_apply]
      exact Prod.ext rfl (funext fun i => (toAdd_eq_zero.1 (congrFun h i)).symm)

/-- In a reduced alternating word of `G(u, ℤⁿ)`, every separator recorded by `bpData`, except
possibly the last, lies outside `C_G(u)`. -/
private theorem isChain_bpData_snd {L : List (Σ b, CentralizerExtFactor u n b)}
    (hc : L.IsChain fun l l' => l.1 ≠ l'.1)
    (hL : ∀ l ∈ L, l.2 ∉ (centralizerExtMap u n l.1).range) :
    (bpData L).2.IsChain fun q _ => q.2 ∉ centralizer {u} := by
  induction L with
  | nil => exact .nil
  | cons l L ih =>
    have ih := ih hc.tail fun l hl => hL l (List.mem_cons_of_mem _ hl)
    obtain ⟨_ | _, p⟩ := l
    · simpa [bpData] using ih
    · -- The letter after `(c, v)`, if any, is some `a ∈ G ∖ C_G(u)`, followed by a letter of
      -- `C_G(u) × ℤⁿ` or by nothing; the new separator is `c * a`.
      refine (List.isChain_cons_iff _ _ _).2 ?_
      rcases hq : (bpData L).2 with _ | ⟨q, l'⟩
      · exact Or.inl rfl
      refine Or.inr ⟨q, l', ?_, hq ▸ ih, rfl⟩
      rcases L with _ | ⟨⟨_ | _, a⟩, L'⟩
      · simp [bpData] at hq
      · have ha : (a : G) ∉ centralizer {u} := fun h =>
          hL _ (List.mem_cons_of_mem _ List.mem_cons_self) ⟨⟨a, h⟩, by
            rw [centralizerExtMap_false]; rfl⟩
        have h1 : (bpData L').1 = 1 := by
          rcases L' with _ | ⟨⟨_ | _, b⟩, L''⟩
          · simp [bpData] at hq
          · exact absurd (List.isChain_cons_cons.1 hc.tail).1 (by simp)
          · rfl
        simp only [bpData, h1, mul_one]
        exact fun h => ha (by simpa using mul_mem (inv_mem p.1.2) h)
      · exact absurd (List.isChain_cons_cons.1 hc).1 (by simp)

/-- The normal form for the amalgam `G(u, ℤⁿ)`: every element is `h * a₁ * ⋯ * aᵣ` with `h ∈ G`
and letters `aⱼ` alternately in the two factors, none of them in `C_G(u)`. -/
private theorem exists_eq_of_mul_prod (x : CentralizerExt u n) :
    ∃ (h : G) (L : List (Σ b, CentralizerExtFactor u n b)),
      L.IsChain (fun l l' => l.1 ≠ l'.1) ∧ (∀ l ∈ L, l.2 ∉ (centralizerExtMap u n l.1).range) ∧
      x = of h * (L.map fun l => Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod := by
  classical
  obtain ⟨d⟩ := Monoid.PushoutI.NormalWord.transversal_nonempty _ (centralizerExtMap_injective u n)
  set W := Monoid.PushoutI.NormalWord.equiv (d := d) x
  refine ⟨W.head, W.toList, W.chain_ne, ?_, ?_⟩
  · -- A nonidentity letter of the transversal is not in the amalgamated subgroup.
    rintro ⟨i, g⟩ hl hg
    have h1 := (d.compl i).equiv_fst_eq_self_of_mem_of_one_mem (d.one_mem i) hg
    rw [(d.compl i).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) (W.normalized i g hl)] at h1
    exact W.ne_one _ hl (congrArg Subtype.val h1).symm
  · have hW : W.prod = x := Monoid.PushoutI.NormalWord.equiv.symm_apply_apply x
    conv_lhs => rw [← hW]
    rw [Monoid.PushoutI.NormalWord.prod, ← Monoid.PushoutI.of_apply_eq_base _ false,
      Monoid.CoprodI.Word.prod, map_list_prod, List.map_map]
    simp [Function.comp_def, of_def]

/-- A product of letters of the factor `G` lies in `G`. -/
private theorem prod_mem_range_of {L : List (Σ b, CentralizerExtFactor u n b)}
    (hL : ∀ l ∈ L, l.1 = false) :
    (L.map fun l => Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod ∈
      (of : G →* CentralizerExt u n).range := by
  refine list_prod_mem fun y hy => ?_
  obtain ⟨⟨b, a⟩, ha, rfl⟩ := List.mem_map.1 hy
  obtain rfl : b = false := hL _ ha
  exact ⟨a, by simp [of_def]⟩

/-- In a CSA group `G` with the big powers property, a nonidentity element of the extension
`G(u, ℤⁿ)` of the centralizer of `u ≠ 1` survives under the retractions `tᵢ ↦ u ^ (m * wᵢ)` for
all large `m`, for every direction `w` off finitely many hyperplanes `w ⬝ᵥ v = 0` with `v ≠ 0`. -/
theorem exists_finset_forall_retraction_smul_ne_one (hBP : IsBP G) (hG : IsCSA G) (hu : u ≠ 1)
    {x : CentralizerExt u n} (hx : x ≠ 1) :
    ∃ V : Finset (Fin n → ℤ), (∀ v ∈ V, v ≠ 0) ∧ ∀ w : Fin n → ℤ, (∀ v ∈ V, w ⬝ᵥ v ≠ 0) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → retraction ((m : ℤ) • w) x ≠ 1 := by
  classical
  obtain ⟨h, L, hc, hred, rfl⟩ := exists_eq_of_mul_prod x
  have hρ (k : Fin n → ℤ) : retraction k (of h * (L.map fun l =>
      Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod) =
      h * (bpData L).1 * ((bpData L).2.map fun q => u ^ (k ⬝ᵥ q.1) * q.2).prod := by
    rw [map_mul, retraction_of, map_list_prod, List.map_map, mul_assoc]
    exact congrArg (h * ·) (prod_map_retraction_eq k L)
  refine ⟨((bpData L).2.map Prod.fst).toFinset, by
    simpa using ne_zero_of_mem_bpData_snd hred, fun w hw => ?_⟩
  by_cases hl : (bpData L).2 = []
  · -- No letter of `C_G(u) × ℤⁿ` occurs, so `x` lies in `G` and is fixed by every retraction.
    obtain ⟨g, hg⟩ := mul_mem (⟨h, rfl⟩ : of h ∈ (of : G →* CentralizerExt u n).range)
      (prod_mem_range_of (fst_eq_false_of_bpData_snd_eq_nil hl))
    refine ⟨0, fun m _ h1 => hx ?_⟩
    rw [← hg, retraction_of] at h1
    rw [← hg, h1, map_one]
  -- Otherwise the image is an alternating product to which the big powers property applies.
  obtain ⟨N, hN⟩ := hBP.exists_forall_mul_prod_ne_one hG hu (h * (bpData L).1)
    (l := (bpData L).2.map fun q => (w ⬝ᵥ q.1, q.2)) (by simpa using hl)
    (by
      simp only [List.mem_map]
      rintro _ ⟨q, hq, rfl⟩
      exact hw q.1 (List.mem_toFinset.2 (List.mem_map_of_mem hq)))
    ((List.isChain_map _).2 ((isChain_bpData_snd hc hred).imp fun q _ h hq => absurd hq h))
  refine ⟨N, fun m hm => ?_⟩
  rw [hρ]
  simp only [smul_dotProduct, smul_eq_mul]
  simpa [Function.comp_def, mul_assoc] using hN m hm

/-- In a CSA group `G` with the big powers property, a nonidentity element of the extension
`G(u, ℤ)` of the centralizer of `u ≠ 1` survives under the retraction `t ↦ u ^ k` for every large
`k`. -/
theorem exists_forall_retraction_ne_one (hBP : IsBP G) (hG : IsCSA G) (hu : u ≠ 1)
    {x : CentralizerExt u 1} (hx : x ≠ 1) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → retraction (fun _ => (k : ℤ)) x ≠ 1 := by
  obtain ⟨V, hV, h⟩ := exists_finset_forall_retraction_smul_ne_one hBP hG hu hx
  obtain ⟨N, hN⟩ := h 1 fun v hv => by
    simpa [dotProduct, funext_iff, Fin.forall_fin_one] using hV v hv
  refine ⟨N, fun k hk => ?_⟩
  have hk1 : (k : ℤ) • (1 : Fin 1 → ℤ) = fun _ => (k : ℤ) := by
    funext
    simp
  exact hk1 ▸ hN k hk

/-- **Extensions of centralizers are discriminated by the base group.** In a CSA group `G` with
the big powers property, the extension `G(u, ℤⁿ)` of the centralizer of `u ≠ 1` is discriminated
by `G` over `G`: any finite family of nonidentity elements survives under one retraction
`tᵢ ↦ u ^ kᵢ`. -/
theorem isDiscriminatedBy (hBP : IsBP G) (hG : IsCSA G) (hu : u ≠ 1) :
    IsDiscriminatedBy (of : G →* CentralizerExt u n) (.id G) := by
  classical
  refine (isDiscriminatedBy_def _ _).2 fun s hs => ?_
  choose! V hV h using fun x (hx : x ∈ s) =>
    exists_finset_forall_retraction_smul_ne_one hBP hG hu (hs x hx)
  obtain ⟨w, hw⟩ := TauCeti.exists_forall_dotProduct_ne_zero (s.biUnion V) fun v hv => by
    obtain ⟨x, hx, hv⟩ := Finset.mem_biUnion.1 hv
    exact hV x hx v hv
  choose! N hN using fun x (hx : x ∈ s) => h x hx w fun v hv =>
    hw v (Finset.mem_biUnion.2 ⟨x, hx, hv⟩)
  exact ⟨⟨retraction (((s.sup N : ℕ) : ℤ) • w), retraction_of _⟩,
    fun x hx => hN x hx _ (Finset.le_sup hx)⟩

end CentralizerExt

/-- An extension `G(u, ℤⁿ)` of the centralizer of a nonidentity element `u` of a fully residually
free group `G` is fully residually free. -/
theorem isFullyResiduallyFree_centralizerExt {G : Type*} [Group G] (h : IsFullyResiduallyFree G)
    {u : G} (hu : u ≠ 1) {n : ℕ} : IsFullyResiduallyFree (CentralizerExt u n) :=
  h.of_isDiscriminatedBy (CentralizerExt.isDiscriminatedBy h.isBP h.isCSA hu)

end TauCeti.LimitGroup
