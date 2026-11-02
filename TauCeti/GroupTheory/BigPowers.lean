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
groups. Big powers are the input to the discrimination of extensions of centralizers by the
retractions `t ↦ u ^ k`.

## Main definitions

* `Group.IsBP`: the big powers property.

## Main results

* `Group.IsBP.of_forall_finset_exists_monoidHom`: the big powers property passes along
  homomorphisms that keep any given finite family of nonidentity elements nontrivial.
* `Group.IsBP.of_injective`, `Group.IsBP.of_isDiscriminatedBy`: subgroups of BP groups, and groups
  discriminated by a BP group, are BP groups.
* `Group.IsBP.isMulTorsionFree`: BP groups are torsion-free.
* `Group.IsBP.exists_prod_map_pow_mul_ne_one`: in a CSA group with the big powers property, a
  product of `k`-th powers of conjugates of nonzero powers of `u ≠ 1`, consecutive ones not
  commuting, stays nontrivial after multiplying by a fixed element, for all large `k`.
* `Group.isBP_iff_isMulTorsionFree`: a commutative group is a BP group exactly when it is
  torsion-free.

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

/-- The big powers property for a list with a common exponent: if `l` is a nonempty list of
nonidentity elements in which consecutive entries do not commute, then the product of the `k`-th
powers of its entries is nontrivial for all large `k`. -/
theorem exists_prod_map_pow_ne_one (hG : IsBP G) {l : List G} (hl : l ≠ [])
    (h1 : ∀ x ∈ l, x ≠ 1) (hc : l.IsChain fun x y => ¬Commute x y) :
    ∃ N : ℕ, ∀ k, N ≤ k → (l.map (· ^ k)).prod ≠ 1 := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨N, hN⟩ := hG (k := l.length) (fun i => (a :: l)[(i : ℕ)])
    (fun i => h1 _ (List.getElem_mem _))
    (fun i => List.isChain_iff_getElem.1 hc i (by simp))
  refine ⟨N, fun k hk => ?_⟩
  rw [← List.ofFn_getElem_eq_map]
  exact hN (fun _ => k) (fun _ => hk)

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

/-- Consecutive entries of `Hs ++ Y :: (Hs⁻¹ reversed ++ [Z])` do not commute, provided this
holds within `Hs`, at the junction of the last entry of `Hs` with `Y`, and at the junction of the
first entry of `Hs` with `Z`. -/
private theorem isChain_append_cons_reverse {H₁ : G} {Hs : List G} {Y Z : G}
    (hc : (H₁ :: Hs).IsChain fun x y => ¬Commute x y)
    (hY : ¬Commute ((H₁ :: Hs).getLast (List.cons_ne_nil _ _)) Y) (hZ : ¬Commute H₁ Z) :
    ((H₁ :: Hs) ++ Y :: (((H₁ :: Hs).map (·⁻¹)).reverse ++ [Z])).IsChain
      fun x y => ¬Commute x y := by
  refine List.isChain_append.2 ⟨hc, List.isChain_cons.2 ⟨?_, List.isChain_append.2
    ⟨?_, List.isChain_singleton _, ?_⟩⟩, ?_⟩
  · intro x hx
    rw [List.head?_append, List.head?_reverse, List.getLast?_map,
      List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hx
    simp only [Option.map_some, Option.some_or, Option.mem_def, Option.some.injEq] at hx
    rw [← hx, Commute.inv_right_iff]
    exact fun h => hY h.symm
  · rw [List.isChain_reverse, List.isChain_map]
    exact hc.imp fun x y h h' => h (Commute.inv_inv_iff.1 h').symm
  · intro x hx y hy
    simp only [List.getLast?_reverse, List.head?_map, List.head?_cons, Option.map_some,
      Option.mem_def, Option.some.injEq] at hx
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    rw [← hx, ← hy, Commute.inv_left_iff]
    exact hZ
  · intro x hx y hy
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), Option.mem_def,
      Option.some.injEq] at hx
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    rw [← hx, ← hy]
    exact hY

/-- In a CSA group with the big powers property, if `H₁, …, Hₘ` (`m ≥ 1`) are conjugates of
nonzero powers of `u ≠ 1`, consecutive ones not commuting, then `H₁ ^ k ⋯ Hₘ ^ k * z ≠ 1` for all
large `k`. -/
theorem exists_prod_map_pow_mul_ne_one (hBP : IsBP G) (hG : IsCSA G) {u : G} (hu : u ≠ 1)
    {Hs : List G} (hne : Hs ≠ [])
    (hconj : ∀ H ∈ Hs, ∃ y : G, ∃ e : ℤ, e ≠ 0 ∧ H = y * u ^ e * y⁻¹)
    (hc : Hs.IsChain fun x y => ¬Commute x y) (z : G) :
    ∃ N : ℕ, ∀ k, N ≤ k → (Hs.map (· ^ k)).prod * z ≠ 1 := by
  have := hBP.isMulTorsionFree
  have hconj1 : ∀ {y : G} {e : ℤ}, e ≠ 0 → y * u ^ e * y⁻¹ ≠ 1 := fun he h => he <|
    (IsMulTorsionFree.zpow_eq_one_iff_right hu).1 (by simpa using h)
  have hne1 : ∀ H ∈ Hs, H ≠ 1 := fun H hH => by
    obtain ⟨y, e, he, rfl⟩ := hconj H hH
    exact hconj1 he
  rcases Hs with _ | ⟨H₁, _ | ⟨H₂, rest⟩⟩
  · exact absurd rfl hne
  · -- A single conjugate: `H₁ ^ k = z⁻¹` holds for at most one `k`, by torsion-freeness.
    by_cases hk : ∃ k : ℕ, H₁ ^ k * z = 1
    · obtain ⟨k₀, hk₀⟩ := hk
      refine ⟨k₀ + 1, fun k hk h => ?_⟩
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
      have := (IsMulTorsionFree.pow_right_inj (hne1 H₁ (by simp))).1
        ((mul_eq_one_iff_eq_inv.1 h).trans (mul_eq_one_iff_eq_inv.1 hk₀).symm)
      omega
    · push Not at hk
      exact ⟨0, fun k _ => by simpa using hk k⟩
  · -- Several conjugates: if `P = H₁ ^ k ⋯ Hₘ ^ k` equals `z⁻¹`, then
    -- `P * Y ^ k * P⁻¹ * Z ^ k = 1` for `Y = W * u * W⁻¹` and `Z = z⁻¹ * Y⁻¹ * z`, which the big
    -- powers property excludes once `W` is chosen so that `Y` commutes with neither `Hₘ` nor
    -- `z * H₁ * z⁻¹`.
    set Hs := H₁ :: H₂ :: rest
    obtain ⟨y₁, e₁, he₁, hH₁⟩ := hconj H₁ (by simp [Hs])
    obtain ⟨y₂, e₂, -, hH₂⟩ := hconj H₂ (by simp [Hs])
    obtain ⟨ym, em, hem, hHm⟩ := hconj (Hs.getLast (by simp [Hs])) (List.getLast_mem _)
    have hg : y₁⁻¹ * y₂ ∉ Subgroup.centralizer {u} := fun h =>
      (List.isChain_cons_cons.1 hc).1
        (hH₁ ▸ hH₂ ▸ commute_conj_zpow_of_inv_mul_mem_centralizer e₁ e₂ h)
    obtain ⟨W, hW₁, hW₂⟩ := hG.exists_inv_mul_notMem_centralizer hu hg ym (z * y₁)
    set Y := W * u ^ (1 : ℤ) * W⁻¹
    set Z := z⁻¹ * W * u ^ (-1 : ℤ) * (z⁻¹ * W)⁻¹
    obtain ⟨N, hN⟩ := hBP.exists_prod_map_pow_ne_one
      (l := Hs ++ Y :: ((Hs.map (·⁻¹)).reverse ++ [Z])) (by simp)
      (by
        simp only [List.mem_append, List.mem_cons, List.mem_reverse, List.mem_map,
          List.not_mem_nil, or_false]
        rintro x (hx | rfl | ⟨H, hH, rfl⟩ | rfl)
        · exact hne1 x hx
        · exact hconj1 one_ne_zero
        · exact inv_ne_one.2 (hne1 H hH)
        · exact hconj1 (by norm_num))
      (isChain_append_cons_reverse hc
        (by rw [hHm]; exact hG.not_commute_conj_zpow hu hem one_ne_zero hW₁)
        (by
          rw [hH₁]
          exact hG.not_commute_conj_zpow hu he₁ (by norm_num) (by simpa [mul_assoc] using hW₂)))
    refine ⟨N, fun k hk h => hN k hk ?_⟩
    have hP : (Hs.map (· ^ k)).prod = z⁻¹ := eq_inv_of_mul_eq_one_left h
    have hrev : ((Hs.map (·⁻¹)).reverse.map (· ^ k)).prod = (Hs.map (· ^ k)).prod⁻¹ := by
      rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
      simp [Function.comp_def, inv_pow]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons,
      List.map_nil, List.prod_nil, mul_one, hrev, hP, inv_inv, Y, Z, conj_pow, zpow_one,
      zpow_neg_one, inv_pow]
    group

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

end Group
