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

In a CSA group with the big powers property, the property extends to alternating products
`g₀ * u ^ (k * e₁) * g₁ * ⋯ * u ^ (k * eₙ) * gₙ` of big powers of one element `u ≠ 1`, as long as
no separator `gᵢ` commuting with `u` sits between exponents of opposite signs: such a product is
nontrivial for all large `k`. This is the form in which big powers enter the normal forms of
amalgamated products and HNN extensions along centralizers.

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
* `Group.IsBP.exists_forall_mul_prod_ne_one`: in a CSA group with the big powers property,
  alternating products of big powers of `u ≠ 1` are nontrivial.

## Implementation notes

An alternating product is rewritten as a product of conjugates `aᵢ * u ^ (k * eᵢ) * aᵢ⁻¹` followed
by `a = g₀ * ⋯ * gₙ`. Factors whose conjugators lie in one coset of `C_G(u)` merge, and conjugates
by elements of different cosets do not commute by the CSA property, so the big powers property
applies when `a = 1`. A general `a` is removed by commuting the product with a further conjugate
of a big power of `u`.

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

/-- In a torsion-free group, for `H ≠ 1` and any `z`, `H ^ k * z ≠ 1` for all large `k`: the
equation `H ^ k = z⁻¹` holds for at most one `k`. -/
theorem exists_forall_pow_mul_ne_one [IsMulTorsionFree G] {H : G} (hH : H ≠ 1) (z : G) :
    ∃ N : ℕ, ∀ k, N ≤ k → H ^ k * z ≠ 1 := by
  by_cases hk : ∃ k : ℕ, H ^ k * z = 1
  · obtain ⟨k₀, hk₀⟩ := hk
    refine ⟨k₀ + 1, fun k hk h => ?_⟩
    have := (IsMulTorsionFree.pow_right_inj hH).1
      ((mul_eq_one_iff_eq_inv.1 h).trans (mul_eq_one_iff_eq_inv.1 hk₀).symm)
    omega
  · push Not at hk
    exact ⟨0, fun k _ => hk k⟩

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
  · -- A single conjugate.
    obtain ⟨N, hN⟩ := exists_forall_pow_mul_ne_one (hne1 H₁ (by simp)) z
    exact ⟨N, fun k hk ↦ by simpa using hN k hk⟩
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

/-! ### Alternating products in CSA groups -/

namespace IsBP

open Subgroup

/-- The product `∏ᵢ aᵢ * u ^ (k * eᵢ) * aᵢ⁻¹` of conjugates of powers of `u` along a list of
pairs `(aᵢ, eᵢ)`. -/
private def conjProd (u : G) (k : ℕ) (L : List (G × ℤ)) : G :=
  (L.map fun p => p.1 * u ^ ((k : ℤ) * p.2) * p.1⁻¹).prod

/-- The big powers property for products `∏ᵢ aᵢ * u ^ (k * eᵢ) * aᵢ⁻¹` in which consecutive
conjugators lie in different cosets of `C_G(u)`. -/
private theorem exists_forall_conjProd_ne_one (hBP : IsBP G) (hG : IsCSA G) {u : G} (hu : u ≠ 1)
    {L : List (G × ℤ)} (hL : L ≠ []) (he : ∀ p ∈ L, p.2 ≠ 0)
    (hc : L.IsChain fun p q => p.1⁻¹ * q.1 ∉ centralizer {u}) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → conjProd u k L ≠ 1 := by
  have := hBP.isMulTorsionFree
  obtain ⟨n, hn⟩ : ∃ n, L.length = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by simpa using hL)
  let w : G × ℤ → G := fun p => p.1 * u ^ p.2 * p.1⁻¹
  obtain ⟨N, hN⟩ := hBP (fun i : Fin (n + 1) => w (L[i.1]'(by omega)))
    (fun i => by
      simpa [w, conj_eq_one_iff, IsMulTorsionFree.zpow_eq_one_iff] using
        ⟨hu, he _ (List.getElem_mem _)⟩)
    (fun i => hG.not_commute_conj_zpow hu (he _ (List.getElem_mem _))
      (he _ (List.getElem_mem _)) (List.isChain_iff_getElem.1 hc i.1 (by omega)))
  refine ⟨N, fun k hk => ?_⟩
  have h := hN (fun _ => k) (fun _ => hk)
  have key : (List.ofFn fun i : Fin (n + 1) => w (L[i.1]'(by omega)) ^ k) =
      L.map fun p => p.1 * u ^ ((k : ℤ) * p.2) * p.1⁻¹ := by
    rw [List.ofFn_congr hn.symm]
    simp only [Fin.val_cast]
    rw [List.ofFn_getElem_eq_map (f := fun p => w p ^ k)]
    congr 1
    ext p
    simp [w, ← zpow_natCast, ← zpow_mul, mul_comm]
  rwa [key] at h

private theorem conjProd_cons (u : G) (k : ℕ) (p : G × ℤ) (L : List (G × ℤ)) :
    conjProd u k (p :: L) = p.1 * u ^ ((k : ℤ) * p.2) * p.1⁻¹ * conjProd u k L := by
  simp [conjProd]

private theorem conjProd_append (u : G) (k : ℕ) (L M : List (G × ℤ)) :
    conjProd u k (L ++ M) = conjProd u k L * conjProd u k M := by
  simp [conjProd]

private theorem conjProd_reverse_neg (u : G) (k : ℕ) (L : List (G × ℤ)) :
    conjProd u k (L.reverse.map fun p => (p.1, -p.2)) = (conjProd u k L)⁻¹ := by
  rw [conjProd, conjProd, List.prod_inv_reverse, List.map_map, List.map_reverse, List.map_map]
  congr 2
  ext p
  simp [mul_assoc, zpow_neg]

/-- Consecutive factors whose conjugators lie in the same coset of `C_G(u)` and whose exponents
have the same sign merge into one factor. -/
private theorem exists_conjProd_eq (u : G) {L : List (G × ℤ)} (he : ∀ p ∈ L, p.2 ≠ 0)
    (hc : L.IsChain fun p q => p.1⁻¹ * q.1 ∈ centralizer {u} → p.2.sign = q.2.sign) :
    ∃ L' : List (G × ℤ), (∀ p ∈ L', p.2 ≠ 0) ∧
      L'.IsChain (fun p q => p.1⁻¹ * q.1 ∉ centralizer {u}) ∧
      L'.head?.map (fun p => (p.1, p.2.sign)) = L.head?.map (fun p => (p.1, p.2.sign)) ∧
      ∀ k, conjProd u k L' = conjProd u k L := by
  induction L with
  | nil => exact ⟨[], by simp, .nil, rfl, fun _ => rfl⟩
  | cons p L ih =>
    obtain ⟨hpc, hLc⟩ := List.isChain_cons.1 hc
    obtain ⟨L', he', hc', hhead, hprod⟩ :=
      ih (fun q hq => he q (List.mem_cons_of_mem _ hq)) hLc
    have hp := he p List.mem_cons_self
    rcases L' with _ | ⟨q', R'⟩
    · exact ⟨[p], by simpa using hp, List.isChain_singleton _, rfl, fun k => by
        rw [conjProd_cons, conjProd_cons, ← hprod]⟩
    rcases L with _ | ⟨q, R⟩
    · simp at hhead
    simp only [List.head?_cons, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhead
    obtain ⟨hq₁, hq₂⟩ := hhead
    obtain ⟨hq'c, hR'c⟩ := List.isChain_cons.1 hc'
    by_cases hm : p.1⁻¹ * q.1 ∈ centralizer {u}
    · -- Merge `p` with the first factor `q'`, whose conjugator lies in `p.1 * C_G(u)`.
      have hs : p.2.sign = q'.2.sign := (hpc q rfl hm).trans hq₂.symm
      have hsum : (p.2 + q'.2).sign = p.2.sign := (Int.sign_add_eq_of_sign_eq hs).trans hs.symm
      refine ⟨(p.1, p.2 + q'.2) :: R', ?_, ?_, ?_, fun k => ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨fun h => hp ?_, fun r hr => he' r (List.mem_cons_of_mem _ hr)⟩
        rw [← Int.sign_eq_zero_iff_zero, ← hsum, h, Int.sign_zero]
      · refine List.isChain_cons.2 ⟨fun r hr hpr => hq'c r hr ?_, hR'c⟩
        -- Factor `q.1⁻¹ * r.1` through `p.1`, so that it is a product of two elements of
        -- `C_G(u)`: the inverse of `hm` and `hpr`.
        rw [hq₁, show q.1⁻¹ * r.1 = (p.1⁻¹ * q.1)⁻¹ * (p.1⁻¹ * r.1) by group]
        exact mul_mem (inv_mem hm) hpr
      · simp [hsum]
      · have hcomm : Commute (p.1⁻¹ * q.1) (u ^ ((k : ℤ) * q'.2)) :=
          Commute.zpow_right (mem_centralizer_singleton_iff.1 hm : Commute _ u) _
        -- Rewrite the conjugate by `q.1` as a conjugate by `p.1` of a conjugate by
        -- `p.1⁻¹ * q.1 ∈ C_G(u)`; the inner conjugation then cancels by `hcomm`.
        rw [conjProd_cons, conjProd_cons u k p (q :: R), ← hprod, conjProd_cons, hq₁, mul_add,
          zpow_add,
          show q.1 * u ^ ((k : ℤ) * q'.2) * q.1⁻¹ =
            p.1 * ((p.1⁻¹ * q.1) * u ^ ((k : ℤ) * q'.2) * (p.1⁻¹ * q.1)⁻¹) * p.1⁻¹ by group,
          hcomm.mul_inv_cancel]
        group
    · -- Keep `p` as a separate factor.
      refine ⟨p :: q' :: R', ?_, ?_, by simp, fun k => ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hp, he' _ List.mem_cons_self, fun r hr => he' r (List.mem_cons_of_mem _ hr)⟩
      · exact List.isChain_cons.2 ⟨fun r hr => by
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
          rwa [← hr, hq₁], hc'⟩
      · rw [conjProd_cons u k p (q' :: R'), conjProd_cons u k p (q :: R), hprod]

/-- Doubling a product along its reverse with the signs flipped: if consecutive conjugators of
`L` lie in different cosets of `C_G(u)`, and `c` is not in the coset of the last conjugator, then
in `L ++ (c, e) :: (L⁻¹ ++ [(a * c, -e)])`, where `e` is the first exponent of `L` and `L⁻¹` is the
reverse of `L` with negated exponents, only the last two factors may merge. -/
private theorem isChain_append_reverse {u : G} {L : List (G × ℤ)}
    (hc : L.IsChain fun p q => p.1⁻¹ * q.1 ∉ centralizer {u}) {p ℓ : G × ℤ}
    (hp : L.head? = some p) (hℓ : L.getLast? = some ℓ) {c : G}
    (hcℓ : ℓ.1⁻¹ * c ∉ centralizer {u}) (a : G) :
    (L ++ (c, p.2) :: ((L.reverse.map fun r => (r.1, -r.2)) ++ [(a * c, -p.2)])).IsChain
      fun r s => r.1⁻¹ * s.1 ∈ centralizer {u} → r.2.sign = s.2.sign := by
  have hweak : ∀ {r s : G × ℤ}, r.1⁻¹ * s.1 ∉ centralizer {u} →
      r.1⁻¹ * s.1 ∈ centralizer {u} → r.2.sign = s.2.sign := fun h h' => (h h').elim
  refine List.IsChain.append (hc.imp fun _ _ h => hweak h)
    (List.isChain_cons.2 ⟨fun r hr => hweak ?_, List.IsChain.append ?_
      (List.isChain_singleton _) fun r hr s hs _ => ?_⟩) fun r hr s hs => hweak ?_
  · -- `c` and the last conjugator of `L`, which heads the reversed list.
    simp only [List.head?_append, List.head?_map, List.head?_reverse, hℓ, Option.map_some,
      Option.some_or, Option.mem_def, Option.some.injEq] at hr
    -- The coset condition is symmetric: `c⁻¹ * ℓ.1` is the inverse of `ℓ.1⁻¹ * c`.
    rw [← hr, show c⁻¹ * ℓ.1 = (ℓ.1⁻¹ * c)⁻¹ by group]
    exact fun h => hcℓ (inv_mem_iff.1 h)
  · -- The reversed list inherits the coset condition, which is symmetric.
    refine List.isChain_map_of_isChain _ (fun r s h => hweak h) (List.isChain_reverse.2
      (hc.imp fun r s h hm => h ?_))
    simpa using inv_mem hm
  · -- The last two factors have exponents of the same sign `-p.2`.
    simp only [List.getLast?_map, List.getLast?_reverse, hp, Option.map_some, Option.mem_def,
      Option.some.injEq] at hr
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs
    rw [← hr, ← hs]
  · simp only [hℓ, Option.mem_def, Option.some.injEq] at hr
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs
    rwa [← hr, ← hs]

/-- A single conjugate `p.1 * u ^ (k * p.2) * p.1⁻¹` of a power of `u ≠ 1` in a torsion-free group
takes each value for at most one `k`. -/
private theorem exists_forall_conjProd_singleton_ne [IsMulTorsionFree G] {u : G} (hu : u ≠ 1)
    {p : G × ℤ} (hp : p.2 ≠ 0) (a : G) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → conjProd u k [p] ≠ a := by
  by_cases h : ∃ k₀, conjProd u k₀ [p] = a
  · obtain ⟨k₀, hk₀⟩ := h
    refine ⟨k₀ + 1, fun k hk hka => ?_⟩
    rw [← hk₀] at hka
    have h : (k : ℤ) * p.2 = k₀ * p.2 := by
      simpa [conjProd, IsMulTorsionFree.zpow_right_inj hu] using hka
    have := mul_right_cancel₀ hp h
    omega
  · push Not at h
    exact ⟨0, fun k _ => h k⟩

/-- A product `∏ᵢ aᵢ * u ^ (k * eᵢ) * aᵢ⁻¹` in which factors with conjugators in one coset of
`C_G(u)` have exponents of the same sign avoids any given element `a` for all large `k`. -/
private theorem exists_forall_conjProd_ne (hBP : IsBP G) (hG : IsCSA G) {u : G} (hu : u ≠ 1)
    {L : List (G × ℤ)} (hL : L ≠ []) (he : ∀ p ∈ L, p.2 ≠ 0)
    (hc : L.IsChain fun p q => p.1⁻¹ * q.1 ∈ centralizer {u} → p.2.sign = q.2.sign) (a : G) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → conjProd u k L ≠ a := by
  have := hBP.isMulTorsionFree
  obtain ⟨L', he', hc', hhead, hprod⟩ := exists_conjProd_eq u he hc
  simp only [← hprod]
  rcases L' with _ | ⟨p, _ | ⟨q, R⟩⟩
  · cases L
    · exact absurd rfl hL
    · simp at hhead
  · exact exists_forall_conjProd_singleton_ne hu (he' p List.mem_cons_self) a
  -- Two consecutive conjugators supply `b ∉ C_G(u)`. For a conjugate `z` of a big power of `u` by
  -- an element of `ℓ * b`, with `ℓ` the last conjugator, `∏ L = a` would make
  -- `∏ L * z * (∏ L)⁻¹ * (a * z * a⁻¹)⁻¹` trivial, a product of the same kind.
  set L' := p :: q :: R with hL'
  have hb : p.1⁻¹ * q.1 ∉ centralizer {u} := (List.isChain_cons.1 hc').1 q rfl
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, L'.getLast? = some ℓ := Option.isSome_iff_exists.1 (by simp [hL'])
  set c := ℓ.1 * (p.1⁻¹ * q.1)
  let M := L' ++ (c, p.2) :: ((L'.reverse.map fun r => (r.1, -r.2)) ++ [(a * c, -p.2)])
  have heM : ∀ r ∈ M, r.2 ≠ 0 := by
    have hp := he' p List.mem_cons_self
    simp only [M, List.mem_append, List.mem_cons, List.mem_map, List.mem_reverse,
      List.not_mem_nil, or_false]
    rintro r (hr | rfl | ⟨r', hr', rfl⟩ | rfl)
    · exact he' r hr
    · exact hp
    · exact neg_ne_zero.2 (he' r' hr')
    · exact neg_ne_zero.2 hp
  obtain ⟨M', heM', hcM', hheadM, hprodM⟩ := exists_conjProd_eq u heM
    (isChain_append_reverse hc' rfl hℓ (by simpa [c] using hb) a)
  have hM' : M' ≠ [] := by
    rintro rfl
    simp [M, hL'] at hheadM
  obtain ⟨N, hN⟩ := exists_forall_conjProd_ne_one hBP hG hu hM' heM' hcM'
  refine ⟨N, fun k hk hka => hN k hk ?_⟩
  rw [hprodM, conjProd_append, conjProd_cons u k (c, p.2), conjProd_append, conjProd_reverse_neg,
    hka]
  simp only [conjProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_neg,
    zpow_neg]
  group

/-- The conjugators `a`, `a * g₁`, `a * g₁ * g₂`, … of the factors `u ^ eᵢ` in an alternating
product `a * u ^ e₁ * g₁ * u ^ e₂ * g₂ * ⋯`. -/
private def conjugators : G → List (ℤ × G) → List (G × ℤ)
  | _, [] => []
  | a, p :: l => (a, p.1) :: conjugators (a * p.2) l

private theorem map_snd_conjugators (a : G) (l : List (ℤ × G)) :
    (conjugators a l).map Prod.snd = l.map Prod.fst := by
  induction l generalizing a with
  | nil => rfl
  | cons p l ih => simp [conjugators, ih]

private theorem head?_conjugators (a : G) (l : List (ℤ × G)) :
    (conjugators a l).head? = l.head?.map fun q => (a, q.1) := by
  cases l <;> rfl

/-- An alternating product `a * u ^ (k * e₁) * g₁ * ⋯` is a product of conjugates of powers of `u`
followed by the product `a * g₁ * ⋯` of the separators. -/
private theorem mul_prod_eq_conjProd (u : G) (k : ℕ) (a : G) (l : List (ℤ × G)) :
    a * (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod =
      conjProd u k (conjugators a l) * (a * (l.map Prod.snd).prod) := by
  induction l generalizing a with
  | nil => simp [conjugators, conjProd]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, conjugators, conjProd_cons]
    -- Split off the first conjugate `a * u ^ (k * e₁) * a⁻¹`, leaving the tail in the form
    -- `(a * g₁) * ⋯` required by the induction hypothesis for the conjugator `a * g₁`.
    rw [show a * (u ^ ((k : ℤ) * p.1) * p.2 *
        (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod) =
      a * u ^ ((k : ℤ) * p.1) * a⁻¹ * ((a * p.2) *
        (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod) by group, ih]
    simp only [mul_assoc]

private theorem isChain_conjugators {u : G} (a : G) {l : List (ℤ × G)}
    (hc : l.IsChain fun p q => p.2 ∈ centralizer {u} → p.1.sign = q.1.sign) :
    (conjugators a l).IsChain fun p q => p.1⁻¹ * q.1 ∈ centralizer {u} → p.2.sign = q.2.sign := by
  induction l generalizing a with
  | nil => exact .nil
  | cons p l ih =>
    obtain ⟨hpc, hlc⟩ := List.isChain_cons.1 hc
    refine List.isChain_cons.2 ⟨fun r hr => ?_, ih _ hlc⟩
    rw [head?_conjugators, Option.mem_def, Option.map_eq_some_iff] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    simpa using hpc q hq

/-- **Big powers for alternating products.** Let `G` be a CSA group with the big powers property
and `u ≠ 1`. In an alternating product `g * u ^ (k * e₁) * g₁ * ⋯ * u ^ (k * eₙ) * gₙ` with
`n ≥ 1` and nonzero `eᵢ`, suppose that whenever a separator `gᵢ` commutes with `u`, the exponents
`eᵢ` and `eᵢ₊₁` on either side of it have the same sign. Then the product is nontrivial for all
large `k`. -/
theorem exists_forall_mul_prod_ne_one (hBP : IsBP G) (hG : IsCSA G) {u : G} (hu : u ≠ 1)
    (g : G) {l : List (ℤ × G)} (hl : l ≠ []) (he : ∀ p ∈ l, p.1 ≠ 0)
    (hc : l.IsChain fun p q => p.2 ∈ centralizer {u} → p.1.sign = q.1.sign) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → g * (l.map fun p => u ^ ((k : ℤ) * p.1) * p.2).prod ≠ 1 := by
  have hne : conjugators g l ≠ [] := by
    rw [Ne, ← List.map_eq_nil_iff (f := Prod.snd), map_snd_conjugators, List.map_eq_nil_iff]
    exact hl
  have he' : ∀ p ∈ conjugators g l, p.2 ≠ 0 := by
    intro p hp
    have := List.mem_map_of_mem (f := Prod.snd) hp
    rw [map_snd_conjugators, List.mem_map] at this
    obtain ⟨q, hq, hpq⟩ := this
    exact hpq ▸ he q hq
  obtain ⟨N, hN⟩ := exists_forall_conjProd_ne hBP hG hu hne he' (isChain_conjugators g hc)
    (g * (l.map Prod.snd).prod)⁻¹
  refine ⟨N, fun k hk => ?_⟩
  rw [mul_prod_eq_conjProd, Ne, mul_eq_one_iff_eq_inv]
  exact hN k hk

end IsBP

end Group
