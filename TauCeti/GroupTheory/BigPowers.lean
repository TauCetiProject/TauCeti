/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination

/-!
# The big powers property

A group has the *big powers property* (is a *BP group*) when every finite nonempty tuple
`(u₀, …, u_k)` of nonidentity elements, in which consecutive entries do not commute, has a bound
`N` such that `u₀ ^ e₀ * ⋯ * u_k ^ e_k ≠ 1` whenever every exponent `eᵢ` is at least `N`.

The singleton tuples say that a BP group is torsion-free; for a commutative group, where every
tuple of length at least two is excluded, this is the whole condition. Free groups are BP groups
(`FreeGroup.isBP`), and the property passes from a group `H` to every group `G` whose finite
families of nonidentity elements each survive under one homomorphism `G →* H`. In particular it
passes to subgroups and to groups discriminated by a BP group, such as fully residually free
groups.

In a nonabelian CSA group with the big powers property, big powers also survive coefficients: if
`a₁, …, a_r` lie outside the centralizer of `u ≠ 1` and the `mᵢ` are nonzero, then
`a₀ * u ^ (k * m₀) * a₁ * ⋯ * u ^ (k * m_r) * a_{r+1} ≠ 1` for every large `k`. This is the input
to the discrimination of extensions of centralizers by the retractions `t ↦ u ^ k`.

## Main definitions

* `Group.IsBP`: the big powers property.

## Main results

* `Group.IsBP.of_forall_finset_exists_monoidHom`: the big powers property passes along
  homomorphisms that keep any given finite family of nonidentity elements nontrivial.
* `Group.IsBP.of_injective`, `Group.IsBP.of_isDiscriminatedBy`: subgroups of BP groups, and groups
  discriminated by a BP group, are BP groups.
* `Group.IsBP.isMulTorsionFree`: BP groups are torsion-free.
* `Group.isBP_iff_isMulTorsionFree`: a commutative group is a BP group exactly when it is
  torsion-free.
* `Group.IsBP.exists_forall_prod_map_pow_ne_one`: the big powers property for lists.
* `Group.IsBP.exists_forall_prod_map_pow_mul_ne_one`: with trivial center, the big powers bound
  survives a fixed right factor.
* `Group.IsBP.exists_forall_mul_prod_map_zpow_mul_ne_one`: big powers with coefficients in a
  nonabelian CSA group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5, Definition 1 and the paragraph following it.
* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
-/

public section

open scoped commutatorElement

namespace Group

variable (G : Type*) [Group G]

/-- A group has the *big powers property* when for every nonempty tuple `u` of nonidentity
elements whose consecutive entries do not commute there is a bound `N` such that the product
`u 0 ^ e 0 * ⋯ * u k ^ e k` is nontrivial whenever every exponent `e i` is at least `N`. -/
def IsBP : Prop :=
  ∀ ⦃k : ℕ⦄ (u : Fin (k + 1) → G), (∀ i, u i ≠ 1) →
    (∀ i : Fin k, ¬Commute (u i.castSucc) (u i.succ)) →
    ∃ N : ℕ, ∀ e : Fin (k + 1) → ℕ, (∀ i, N ≤ e i) → (List.ofFn fun i => u i ^ e i).prod ≠ 1

/-- The defining condition of the big powers property. -/
theorem isBP_iff : IsBP G ↔
    ∀ ⦃k : ℕ⦄ (u : Fin (k + 1) → G), (∀ i, u i ≠ 1) →
      (∀ i : Fin k, ¬Commute (u i.castSucc) (u i.succ)) →
      ∃ N : ℕ, ∀ e : Fin (k + 1) → ℕ, (∀ i, N ≤ e i) →
        (List.ofFn fun i => u i ^ e i).prod ≠ 1 :=
  Iff.rfl

variable {G}

namespace IsBP

/-- The big powers property passes from `H` to `G` when every finite family of nonidentity
elements of `G` survives under one homomorphism `G →* H`. -/
theorem of_forall_finset_exists_monoidHom {H : Type*} [Group H] (hH : IsBP H)
    (h : ∀ s : Finset G, (∀ g ∈ s, g ≠ 1) → ∃ φ : G →* H, ∀ g ∈ s, φ g ≠ 1) : IsBP G := by
  classical
  intro k u hu hcomm
  -- One homomorphism keeps every entry and every commutator of consecutive entries nontrivial.
  obtain ⟨φ, hφ⟩ := h (Finset.univ.image u ∪ Finset.univ.image fun i : Fin k =>
      ⁅u i.castSucc, u i.succ⁆) (by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hu i
    · rw [Ne, commutatorElement_eq_one_iff_commute]
      exact hcomm i)
  obtain ⟨N, hN⟩ := hH (fun i => φ (u i))
    (fun i => hφ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ i))))
    (fun i hi => by
      refine hφ ⁅u i.castSucc, u i.succ⁆ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hi)
  refine ⟨N, fun e he hprod => hN e he ?_⟩
  simpa [map_list_prod, List.map_ofFn, Function.comp_def] using congrArg φ hprod

/-- A group with an injective homomorphism to a BP group is a BP group. In particular subgroups
of BP groups are BP groups. -/
theorem of_injective {H : Type*} [Group H] (hH : IsBP H) {f : G →* H}
    (hf : Function.Injective f) : IsBP G :=
  hH.of_forall_finset_exists_monoidHom fun _ hs =>
    ⟨f, fun g hg => (map_ne_one_iff f hf).2 (hs g hg)⟩

/-- A group discriminated by a BP group, relative to any coefficient group, is a BP group. -/
theorem of_isDiscriminatedBy {C K H : Type*} [Group C] [Group K] [Group H] (hH : IsBP H)
    {ιK : C →* K} {ιH : C →* H} (h : TauCeti.GroupAlgGeom.IsDiscriminatedBy ιK ιH) : IsBP K :=
  hH.of_forall_finset_exists_monoidHom fun s hs =>
    let ⟨φ, hφ⟩ := (TauCeti.GroupAlgGeom.isDiscriminatedBy_def ιK ιH).1 h s hs
    ⟨φ, hφ⟩

/-- A BP group is torsion-free: the condition for a singleton tuple `(g)` says that the powers
`g ^ e` are nontrivial for all large `e`. -/
theorem isMulTorsionFree (hG : IsBP G) : IsMulTorsionFree G := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]
  intro g hg hfin
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨N, hN⟩ := hG (k := 0) (fun _ => g) (fun _ => hg) (fun i => i.elim0)
  refine hN (fun _ => n * N.succ) (fun _ => ?_) ?_
  · exact le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left _ hn)
  · simp [pow_mul, hgn]

/-- The big powers property for lists: for a nonempty list `l` of nonidentity elements whose
consecutive entries do not commute there is a bound `N` such that `g₀ ^ e₀ * ⋯ * g_k ^ e_k ≠ 1`
for every list `p` of pairs `(gᵢ, eᵢ)` with first components `l` and every `eᵢ ≥ N`. -/
theorem exists_forall_prod_map_pow_ne_one (hG : IsBP G) {l : List G} (hl : l ≠ [])
    (h1 : ∀ g ∈ l, g ≠ 1) (hc : l.IsChain fun a b => ¬Commute a b) :
    ∃ N : ℕ, ∀ p : List (G × ℕ), p.map Prod.fst = l → (∀ x ∈ p, N ≤ x.2) →
      (p.map fun x => x.1 ^ x.2).prod ≠ 1 := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨N, hN⟩ := hG (k := l.length) (fun i => (a :: l)[(i : ℕ)])
    (fun i => h1 _ (List.getElem_mem _))
    (fun i => List.isChain_iff_getElem.1 hc i (by simp))
  refine ⟨N, fun p hp hpN => ?_⟩
  have hlen : p.length = l.length + 1 := by simpa using congrArg List.length hp
  convert hN (fun i => p[(i : ℕ)].2) (fun i => hpN _ (List.getElem_mem _)) using 2
  refine List.ext_getElem (by simp [hlen]) fun n h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_ofFn]
  simp only [← hp, List.getElem_map]

/-- In a group with trivial center, some element commutes with neither of two given nonidentity
elements: their centralizers are proper subgroups, and no group is a union of two proper
subgroups. -/
private theorem exists_notMem_centralizer (hZ : Subgroup.center G = ⊥) {g h : G} (hg : g ≠ 1)
    (hh : h ≠ 1) :
    ∃ y : G, y ∉ Subgroup.centralizer {g} ∧ y ∉ Subgroup.centralizer {h} := by
  have hC : ∀ x : G, x ≠ 1 → ¬⊤ ≤ Subgroup.centralizer {x} := fun x hx htop => hx <| by
    rw [← Subgroup.mem_bot, ← hZ, ← SetLike.mem_coe, ← Set.singleton_subset_iff,
      ← Subgroup.centralizer_eq_top_iff_subset]
    exact top_le_iff.1 htop
  by_contra! hy
  exact ((SubgroupClass.subset_union (H := (⊤ : Subgroup G))).1 fun y _ =>
    or_iff_not_imp_left.2 (hy y)).elim (hC g hg) (hC h hh)

/-- Consecutive entries of `l ++ [b * y * b⁻¹] ++ (reversed inverses of l) ++ [y⁻¹]` do not
commute, provided those of `l` do not and `y` commutes neither with the first entry of `l` nor
with `b⁻¹ * g * b` for its last entry `g`. -/
private theorem isChain_append_conj_cons {l : List G} (hl : l ≠ [])
    (hc : l.IsChain fun a b => ¬Commute a b) {b y : G}
    (hy₁ : y ∉ Subgroup.centralizer {l.head hl})
    (hy₂ : y ∉ Subgroup.centralizer {b⁻¹ * l.getLast hl * b}) :
    (l ++ b * y * b⁻¹ :: ((l.map (·⁻¹)).reverse ++ [y⁻¹])).IsChain fun a b => ¬Commute a b := by
  have hconj : ∀ g : G, Commute (b * y * b⁻¹) g → y ∈ Subgroup.centralizer {b⁻¹ * g * b} :=
    fun g h => Subgroup.mem_centralizer_singleton_iff.2
      (by simpa [mul_assoc] using ((Commute.conj_iff b⁻¹).2 h).eq)
  have hlast : (l.map (·⁻¹)).reverse.head? = some (l.getLast hl)⁻¹ := by
    simp [List.getLast?_eq_some_getLast hl]
  have hfirst : (l.map (·⁻¹)).reverse.getLast? = some (l.head hl)⁻¹ := by
    simp [List.head?_eq_some_head hl]
  refine hc.append (List.isChain_cons.2 ⟨?_, ?_⟩) ?_
  · intro z hz
    rw [List.head?_append, hlast] at hz
    obtain rfl := Option.some_injective _ hz
    exact fun h => hy₂ (hconj _ (Commute.inv_right_iff.1 h))
  · refine (List.isChain_reverse.2 ((List.isChain_map _).2 (hc.imp ?_))).append
      (List.isChain_singleton _) ?_
    · exact fun a c h h' => h (Commute.inv_inv_iff.1 h'.symm)
    · intro x hx z hz
      rw [hfirst] at hx
      obtain rfl := Option.some_injective _ hx
      obtain rfl := Option.some_injective _ hz
      exact fun h => hy₁
        (Subgroup.mem_centralizer_singleton_iff.2 (Commute.inv_inv_iff.1 h).eq.symm)
  · intro x hx z hz
    rw [List.getLast?_eq_some_getLast hl] at hx
    obtain rfl := Option.some_injective _ hx
    obtain rfl := Option.some_injective _ hz
    exact fun h => hy₂ (hconj _ h.symm)

/-- In a BP group with trivial center the big powers bound survives a fixed right factor: for a
nonempty list `l` of nonidentity elements whose consecutive entries do not commute and any `b`,
there is `N` such that `g₀ ^ e₀ * ⋯ * g_k ^ e_k * b ≠ 1` for every list `p` of pairs `(gᵢ, eᵢ)`
with first components `l` and every `eᵢ ≥ N`. -/
theorem exists_forall_prod_map_pow_mul_ne_one (hG : IsBP G) (hZ : Subgroup.center G = ⊥)
    {l : List G} (hl : l ≠ []) (h1 : ∀ g ∈ l, g ≠ 1) (hc : l.IsChain fun a b => ¬Commute a b)
    (b : G) :
    ∃ N : ℕ, ∀ p : List (G × ℕ), p.map Prod.fst = l → (∀ x ∈ p, N ≤ x.2) →
      (p.map fun x => x.1 ^ x.2).prod * b ≠ 1 := by
  have hlast := h1 _ (List.getLast_mem hl)
  obtain ⟨y, hy₁, hy₂⟩ := exists_notMem_centralizer hZ (h1 _ (List.head_mem hl))
    (h := b⁻¹ * l.getLast hl * b)
    (fun h => hlast (by simpa [mul_assoc] using congrArg (fun x => b * x * b⁻¹) h))
  have hy1 : y ≠ 1 := fun h => hy₁ (h ▸ Subgroup.one_mem _)
  -- If `g₀ ^ e₀ * ⋯ * g_k ^ e_k = b⁻¹`, then conjugating `b * y ^ N * b⁻¹` by this product and
  -- multiplying by `y⁻¹ ^ N` gives `1`; but this is a big powers product for a longer list.
  obtain ⟨N, hN⟩ := hG.exists_forall_prod_map_pow_ne_one
    (l := l ++ b * y * b⁻¹ :: ((l.map (·⁻¹)).reverse ++ [y⁻¹])) (by simp)
    (by
      simp only [List.mem_append, List.mem_cons, List.mem_reverse, List.mem_map]
      rintro g (hg | rfl | ⟨g, hg, rfl⟩ | rfl | hg)
      · exact h1 g hg
      · simpa using hy1
      · simpa using h1 g hg
      · simpa using hy1
      · simp at hg)
    (isChain_append_conj_cons hl hc hy₁ hy₂)
  refine ⟨N, fun p hp hpN hb => hN (p ++ (b * y * b⁻¹, N) ::
    ((p.map fun x => (x.1⁻¹, x.2)).reverse ++ [(y⁻¹, N)])) ?_ ?_ ?_⟩
  · simp [← hp, List.map_reverse, Function.comp_def]
  · simp only [List.mem_append, List.mem_cons, List.mem_reverse, List.mem_map]
    rintro x (hx | rfl | ⟨x, hx, rfl⟩ | rfl | hx)
    · exact hpN x hx
    · exact le_rfl
    · exact hpN x hx
    · exact le_rfl
    · simp at hx
  · rw [mul_eq_one_iff_eq_inv] at hb
    have hinv := List.prod_inv_reverse (p.map fun x => x.1 ^ x.2)
    simp only [List.map_append, List.map_cons, List.map_reverse, List.map_map, List.prod_append,
      List.prod_cons] at hinv ⊢
    have hmap : p.map ((fun x => x.1 ^ x.2) ∘ fun x => (x.1⁻¹, x.2)) =
        p.map ((fun x => x⁻¹) ∘ fun x => x.1 ^ x.2) :=
      List.map_congr_left fun x _ => by simp [inv_pow]
    rw [hmap, ← hinv, hb, conj_pow]
    simp [mul_assoc]

end IsBP

/-- A trivial group is a BP group: it has no nonidentity elements. -/
theorem isBP_of_subsingleton [Subsingleton G] : IsBP G :=
  fun _ _ hu _ => ((hu 0) (Subsingleton.elim _ _)).elim

/-- A commutative group is a BP group exactly when it is torsion-free: consecutive entries always
commute, so only singleton tuples need to be checked. -/
theorem isBP_iff_isMulTorsionFree {A : Type*} [CommGroup A] : IsBP A ↔ IsMulTorsionFree A := by
  refine ⟨IsBP.isMulTorsionFree, fun _ k u hu hcomm => ⟨1, fun e he => ?_⟩⟩
  cases k with
  | zero =>
    have h := (IsMulTorsionFree.pow_right_inj (hu 0) (n := e 0) (m := 0)).not.2
      (by have := he 0; omega)
    simpa using h
  | succ k => exact (hcomm 0 (Commute.all _ _)).elim

/-! ### Big powers with coefficients in CSA groups -/

/-- The conjugates `a * u ^ m₀ * a⁻¹`, `(a * g₀) * u ^ m₁ * (a * g₀)⁻¹`, … through which the
product `a * u ^ m₀ * g₀ * u ^ m₁ * g₁ * ⋯` is written as a product of conjugates of powers of `u`.
-/
private def conjugates (u : G) : G → List (ℤ × G) → List G
  | _, [] => []
  | a, (m, g) :: l => a * u ^ m * a⁻¹ :: conjugates u (a * g) l

private theorem conjugates_ne_nil (u a : G) {l : List (ℤ × G)} (hl : l ≠ []) :
    conjugates u a l ≠ [] := by
  obtain ⟨⟨m, g⟩, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp [conjugates]

/-- Collecting the powers of `u`: `a * u ^ (k * m₀) * g₀ * ⋯ * u ^ (k * m_r) * g_r` is the product
of the `k`-th powers of the conjugates, followed by `a * g₀ * ⋯ * g_r`. -/
private theorem mul_prod_map_zpow_mul (u : G) (k : ℕ) (a : G) (l : List (ℤ × G)) :
    a * (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod =
      ((conjugates u a l).map (· ^ k)).prod * (a * (l.map Prod.snd).prod) := by
  induction l generalizing a with
  | nil => simp [conjugates]
  | cons p l ih =>
    obtain ⟨m, g⟩ := p
    simp only [List.map_cons, List.prod_cons, conjugates]
    rw [conj_pow, ← zpow_natCast, ← zpow_mul, mul_comm m]
    calc a * (u ^ ((k : ℤ) * m) * g * (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod)
        = a * u ^ ((k : ℤ) * m) * a⁻¹ *
            (a * g * (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod) := by group
      _ = _ := by rw [ih (a * g)]; group

private theorem ne_one_of_mem_conjugates [IsMulTorsionFree G] {u : G} (hu : u ≠ 1) {a : G}
    {l : List (ℤ × G)} (hm : ∀ p ∈ l, p.1 ≠ 0) {x : G} (hx : x ∈ conjugates u a l) : x ≠ 1 := by
  induction l generalizing a with
  | nil => simp [conjugates] at hx
  | cons p l ih =>
    obtain ⟨m, g⟩ := p
    simp only [conjugates, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [Ne, conj_eq_one_iff, IsMulTorsionFree.zpow_eq_one_iff_right hu]
      exact hm _ List.mem_cons_self
    · exact ih (fun p hp => hm p (List.mem_cons_of_mem _ hp)) hx

/-- In a CSA group, consecutive conjugates do not commute when the intermediate coefficients lie
outside the centralizer of `u`. -/
private theorem isChain_conjugates [IsMulTorsionFree G] (hG : IsCSA G) {u : G} (hu : u ≠ 1)
    {a : G} {l : List (ℤ × G)} (hm : ∀ p ∈ l, p.1 ≠ 0)
    (hC : ∀ p ∈ l.dropLast, p.2 ∉ Subgroup.centralizer {u}) :
    (conjugates u a l).IsChain fun x y => ¬Commute x y := by
  induction l generalizing a with
  | nil => simp [conjugates]
  | cons p l ih =>
    obtain ⟨m, g⟩ := p
    rcases l with _ | ⟨⟨m', g'⟩, l⟩
    · simp [conjugates]
    have hm' : ∀ p ∈ (m', g') :: l, p.1 ≠ 0 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    have hg : g ∉ Subgroup.centralizer {u} := hC (m, g) (by simp)
    refine List.IsChain.cons_cons ?_ (ih hm' fun p hp => hC p (by simp_all))
    -- A commutation between consecutive conjugates conjugates back to `u ^ m` commuting with
    -- `g * u ^ m' * g⁻¹`; commutative transitivity then makes `u` commute with `g * u * g⁻¹`.
    intro h
    rw [show a * g * u ^ m' * (a * g)⁻¹ = a * (g * u ^ m' * g⁻¹) * a⁻¹ by group,
      Commute.conj_iff] at h
    have hT := (isCommTransitive_iff G).1 hG.isCommTransitive
    have hum : u ^ m ≠ 1 := (IsMulTorsionFree.zpow_eq_one_iff_right hu).not.2 (hm (m, g) (by simp))
    have hgum : g * u ^ m' * g⁻¹ ≠ 1 := by
      rw [Ne, conj_eq_one_iff, IsMulTorsionFree.zpow_eq_one_iff_right hu]
      exact hm' _ List.mem_cons_self
    have h₁ : Commute u (g * u ^ m' * g⁻¹) := hT _ _ _ hum (Commute.self_zpow u m) h
    have h₂ : Commute u (g * u * g⁻¹) :=
      hT _ _ _ hgum h₁ ((Commute.conj_iff g).2 (Commute.zpow_self u m'))
    exact hg (Subgroup.mem_centralizer_singleton_iff.2
      ((isCSA_iff_isCommTransitive_and_commute_conj.1 hG).2 u g hu h₂).eq.symm)

/-- **Big powers with coefficients.** Let `G` be a nonabelian CSA group with the big
powers property and `u ≠ 1`. If `a₀, g₀, …, g_r` are elements of `G` with `g₀, …, g_{r-1}` outside
the centralizer of `u`, and `m₀, …, m_r` are nonzero integers, then
`a₀ * u ^ (k * m₀) * g₀ * ⋯ * u ^ (k * m_r) * g_r ≠ 1` for every large enough `k`. -/
theorem IsBP.exists_forall_mul_prod_map_zpow_mul_ne_one (hBP : IsBP G) (hG : IsCSA G)
    (hab : ¬IsMulCommutative G) {u : G} (hu : u ≠ 1) (a : G) {l : List (ℤ × G)} (hl : l ≠ [])
    (hm : ∀ p ∈ l, p.1 ≠ 0) (hC : ∀ p ∈ l.dropLast, p.2 ∉ Subgroup.centralizer {u}) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → a * (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod ≠ 1 := by
  have := hBP.isMulTorsionFree
  obtain ⟨N, hN⟩ := hBP.exists_forall_prod_map_pow_mul_ne_one (hG.center_eq_bot hab)
    (conjugates_ne_nil u a hl) (fun _ hx => ne_one_of_mem_conjugates hu hm hx)
    (isChain_conjugates hG hu hm hC) (a * (l.map Prod.snd).prod)
  refine ⟨N, fun k hk => ?_⟩
  rw [mul_prod_map_zpow_mul]
  simpa [List.map_map, Function.comp_def] using
    hN ((conjugates u a l).map (·, k)) (by simp [List.map_map, Function.comp_def])
      (by simpa using fun _ _ => hk)

end Group
