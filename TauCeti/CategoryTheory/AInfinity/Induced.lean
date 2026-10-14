/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Basic
public import TauCeti.CategoryTheory.Graded.InducedQuiver

/-!
# A-infinity categories induced along a map of objects

For an `A∞` category `𝒞` on a graded linear quiver `C` and any map `F : D → C`, the **induced**
`A∞` category `𝒞.induced F` lives on the induced quiver
`TauCeti.GradedLinearQuiver.InducedQuiver C F`: its objects are those of `D`, its morphisms
`X ⟶ Y` are the morphisms `F X ⟶ F Y` of `𝒞`, and its operation on a composable string
`X₀, …, Xₙ` is the operation of `𝒞` on the string `F X₀, …, F Xₙ`.  When `F` is not injective,
the same morphism of `𝒞` appears between several pairs of objects.

An `A∞` functor from an `A∞` category `ℬ` on `D` to `𝒞`, with object map `F`, sends a composable
string of morphisms of `ℬ` to a morphism of `𝒞` between the images of its endpoints, and its
defining equation is imposed only on composable strings.  It can therefore be stored as an `A∞`
morphism from the total algebra of `ℬ` to the total algebra of the induced category along `F`.
The total algebra of `𝒞` itself is not a valid target when `F` is not injective: a string of
morphisms which is not composable in `ℬ` can become composable after applying `F`, and the
operations of `𝒞` do not vanish on it.

The total module of the induced quiver maps to that of `C`
(`TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap`), but this map is not injective, and it
intertwines the operations only on composable strings
(`TauCeti.AInfinityCategory.totalHomMap_induced_m_of_chain`).  So the induced structure is not a
pullback of `A∞` algebras.  Instead its Stasheff identities are checked string by string: on a
composable string each Stasheff term is the corresponding term of `𝒞`, which lies in a single hom
module where the map is injective, and on any other string every term vanishes.

## Main definitions

* `TauCeti.AInfinityCategory.induced`: the `A∞` category induced along a map of objects.

## Main results

* `TauCeti.AInfinityCategory.totalHomMap_induced_m_of_chain`: on a composable string, the map of
  total modules intertwines the operations of the induced category with those of `𝒞`.
* `TauCeti.AInfinityCategory.coe_pathOperation_induced_apply`: the operation of the induced
  category on a composable string is the operation of `𝒞` on its image.
* `TauCeti.AInfinityCategory.eq_induced`: the induced category is the unique `A∞` category on the
  induced quiver with these operations.
* `TauCeti.AInfinityCategory.homDifferential_induced` and
  `TauCeti.AInfinityCategory.comp_induced`: its differential and composition are those of `𝒞`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories
  and functors.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for `A∞` functors as morphisms of bar constructions over a map of objects.
-/

public section

namespace TauCeti

universe u u' v w

open GradedLinearQuiver GradedLinearQuiver.InducedQuiver AInfinity
open _root_.MultilinearMap (evalNat evalNat_def)

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C] {D : Type u'}
  (𝒞 : AInfinityCategory R C) (F : D → C)

/-! ### Strings of morphisms indexed by the naturals -/

section Strings

variable {α : Type*}

/-- The morphisms `aᵢ ⟶ bᵢ`, for `i < n`, form a composable string in the input order of the
operations: the source of each morphism is the target of the next one. -/
private def IsChain (a b : ℕ → α) (n : ℕ) : Prop :=
  ∀ i, i + 1 < n → b (i + 1) = a i

/-- A block of a composable string is composable. -/
private theorem IsChain.block {a b : ℕ → α} {n p s : ℕ} (h : IsChain a b n) (hps : p + s ≤ n) :
    IsChain (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) s := fun j hj ↦ by
  simpa [Nat.add_assoc] using h (p + j) (by omega)

/-- Replacing a block of a composable string by a morphism from the source of its last morphism to
the target of its first leaves a composable string. -/
private theorem IsChain.replaceBlock {a b : ℕ → α} {n p s : ℕ} (h : IsChain a b n) (hs : 1 ≤ s)
    (hps : p + s ≤ n) :
    IsChain (replaceBlock a p s (a (p + s - 1))) (replaceBlock b p s (b p))
      (p + 1 + (n - p - s)) := by
  intro i hi
  rcases lt_trichotomy (i + 1) p with hlt | heq | hgt
  · rw [replaceBlock_of_lt _ _ _ _ hlt, replaceBlock_of_lt _ _ _ _ (by omega)]
    exact h i (by omega)
  · rw [← heq, replaceBlock_self, replaceBlock_of_lt _ _ _ _ (by omega)]
    exact h i (by omega)
  · rw [replaceBlock_of_gt _ _ _ _ hgt]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hgt) with rfl | hip
    · rw [replaceBlock_self]
      convert h (p + s - 1) (by omega) using 2
      omega
    · rw [replaceBlock_of_gt _ _ _ _ hip]
      convert h (i + s - 1) (by omega) using 2
      omega

/-- If a string is not composable, then for every decomposition `n = p + s + t` either the block
of length `s` at `p` is not composable, or replacing it by a single morphism leaves a string which
is not composable. -/
private theorem not_isChain_block_or_replaceBlock {a b : ℕ → α} {n p s : ℕ}
    (h : ¬ IsChain a b n) (hps : p + s ≤ n) :
    ¬ IsChain (fun j ↦ a (p + j)) (fun j ↦ b (p + j)) s ∨
      ¬ IsChain (replaceBlock a p s (a (p + s - 1))) (replaceBlock b p s (b p))
        (p + 1 + (n - p - s)) := by
  simp only [IsChain, not_forall] at h
  obtain ⟨j, hj, hne⟩ := h
  by_cases hblock : p ≤ j ∧ j + 1 < p + s
  · refine .inl fun hc ↦ hne ?_
    simpa [show p + (j - p) = j by omega, show p + (j - p + 1) = j + 1 by omega] using
      hc (j - p) (by omega)
  · refine .inr fun hc ↦ hne ?_
    rcases Nat.lt_or_ge j p with hjp | hjp
    · have e := hc j (by omega)
      rw [replaceBlock_of_lt _ _ _ _ hjp] at e
      rcases Nat.lt_or_ge (j + 1) p with hj1 | hj1
      · rwa [replaceBlock_of_lt _ _ _ _ hj1] at e
      · rwa [show j + 1 = p by omega, replaceBlock_self, ← show j + 1 = p by omega] at e
    · have e := hc (j + 1 - s) (by omega)
      rw [replaceBlock_of_gt _ _ _ _ (by omega), show j + 1 - s + 1 + s - 1 = j + 1 by omega] at e
      rcases Nat.eq_or_lt_of_le (show p ≤ j + 1 - s by omega) with hp | hp
      · rwa [← hp, replaceBlock_self, show p + s - 1 = j by omega] at e
      · rwa [replaceBlock_of_gt _ _ _ _ hp, show j + 1 - s + s - 1 = j by omega] at e

end Strings

/-- Elements of single hom modules, indexed by the naturals, are the inclusions of a family of
morphisms. -/
private theorem exists_eq_homInclusion {E : Type u'} [GradedLinearQuiver.{u', v, w} R E] {n : ℕ}
    {z : ℕ → TotalHom R E} {a b : ℕ → E}
    (hz : ∀ i < n, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) :
    ∃ g : ∀ i : Fin n, homModule (R := R) (a i) (b i),
      ∀ i : Fin n, z i = homInclusion (a i) (b i) (g i) := by
  choose g hg using fun i : Fin n ↦ hz i i.isLt
  exact ⟨g, fun i ↦ (hg i).symm⟩

/-! ### The operations of the induced category -/

/-- The pairs of objects `p i = (sᵢ, tᵢ)` of a string of morphisms `sᵢ ⟶ tᵢ` of the induced
quiver form a composable string. -/
private def IsChainFin {n : ℕ} (p : Fin n → InducedQuiver C F × InducedQuiver C F) : Prop :=
  ∀ i (h : i + 1 < n), (p ⟨i + 1, h⟩).2 = (p ⟨i, by omega⟩).1

/-- The operations of the induced category: on a composable string of morphisms of the induced
quiver, the component between its endpoints of the operation of `𝒞` on the same morphisms; on
any other string, zero. -/
private noncomputable def inducedOperation : (n : ℕ) →
    MultilinearMap R (fun _ : Fin n ↦ TotalHom R (InducedQuiver C F))
      (TotalHom R (InducedQuiver C F))
  | 0 => 0
  | n + 1 => by
    classical
    exact MultilinearMap.fromDirectSumEquiv fun p ↦
      if IsChainFin F p then
        (homInclusion (p (Fin.last n)).1 (p 0).2 ∘ₗ
          homProjection (R := R) (F (p (Fin.last n)).1.obj) (F (p 0).2.obj)).compMultilinearMap
            ((𝒞.m (n + 1)).compLinearMap fun i ↦
              homInclusion (R := R) (F (p i).1.obj) (F (p i).2.obj))
      else 0

private theorem inducedOperation_zero : 𝒞.inducedOperation F 0 = 0 := (rfl)

/-- On a composable string of morphisms `sᵢ ⟶ tᵢ`, the operation of the induced category is the
component between the endpoints of the operation of `𝒞`. -/
private theorem inducedOperation_succ_of_isChainFin {n : ℕ} (s t : Fin (n + 1) → InducedQuiver C F)
    (x : ∀ i, homModule (R := R) (s i) (t i)) (h : IsChainFin F fun i ↦ (s i, t i)) :
    𝒞.inducedOperation F (n + 1) (fun i ↦ homInclusion (s i) (t i) (x i)) =
      homInclusion (s (Fin.last n)) (t 0)
        (homProjection (R := R) (F (s (Fin.last n)).obj) (F (t 0).obj)
          (𝒞.m (n + 1) fun i ↦ homInclusion (R := R) (F (s i).obj) (F (t i).obj) (x i))) := by
  classical
  simp only [inducedOperation, homInclusion_eq_lof]
  rw [MultilinearMap.fromDirectSumEquiv_lof (p := fun i ↦ (s i, t i))]
  simp [h]

/-- On a string of morphisms `sᵢ ⟶ tᵢ` which is not composable, the operation of the induced
category vanishes. -/
private theorem inducedOperation_succ_of_not_isChainFin {n : ℕ}
    (s t : Fin (n + 1) → InducedQuiver C F) (x : ∀ i, homModule (R := R) (s i) (t i))
    (h : ¬ IsChainFin F fun i ↦ (s i, t i)) :
    𝒞.inducedOperation F (n + 1) (fun i ↦ homInclusion (s i) (t i) (x i)) = 0 := by
  classical
  simp only [inducedOperation, homInclusion_eq_lof]
  rw [MultilinearMap.fromDirectSumEquiv_lof (p := fun i ↦ (s i, t i))]
  simp [h]

variable {𝒞 F}

/-- On morphisms `aᵢ ⟶ bᵢ`, an operation of the induced category takes values in the morphisms
from the source of the last input to the target of the first. -/
private theorem evalNat_inducedOperation_mem {k : ℕ} (hk : 0 < k)
    {z : ℕ → TotalHom R (InducedQuiver C F)} {a b : ℕ → InducedQuiver C F}
    (hz : ∀ i < k, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) :
    evalNat (𝒞.inducedOperation F k) z ∈
      LinearMap.range (homInclusion (R := R) (a (k - 1)) (b 0)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  obtain ⟨g, hg⟩ := exists_eq_homInclusion hz
  rw [evalNat_def, funext hg]
  by_cases h : IsChainFin F fun i : Fin (n + 1) ↦ (a i, b i)
  · rw [𝒞.inducedOperation_succ_of_isChainFin F (fun i ↦ a i) (fun i ↦ b i) g h]
    exact LinearMap.mem_range_self _ _
  · rw [𝒞.inducedOperation_succ_of_not_isChainFin F (fun i ↦ a i) (fun i ↦ b i) g h]
    exact zero_mem _

/-- On a composable string of morphisms `aᵢ ⟶ bᵢ`, the map of total modules intertwines an
operation of the induced category with the operation of `𝒞`. -/
private theorem totalHomMap_evalNat_inducedOperation {k : ℕ} (hk : 0 < k)
    {z : ℕ → TotalHom R (InducedQuiver C F)} {a b : ℕ → InducedQuiver C F}
    (hz : ∀ i < k, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : IsChain a b k) :
    totalHomMap R F (evalNat (𝒞.inducedOperation F k) z) =
      evalNat (𝒞.m k) fun i ↦ totalHomMap R F (z i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  obtain ⟨g, hg⟩ := exists_eq_homInclusion hz
  have hg' : (fun i : Fin (n + 1) ↦ totalHomMap R F (z i)) =
      fun i : Fin (n + 1) ↦ homInclusion (R := R) (F (a i).obj) (F (b i).obj) (g i) :=
    funext fun i ↦ by rw [hg i, totalHomMap_homInclusion]
  rw [evalNat_def, evalNat_def, funext hg, hg',
    𝒞.inducedOperation_succ_of_isChainFin F (fun i ↦ a i) (fun i ↦ b i) g hab,
    totalHomMap_homInclusion]
  refine homInclusion_homProjection_of_mem_range ?_
  exact (𝒞.isPathCompatible_m (n + 1)).mem_range_homInclusion_of_chain
    (fun i ↦ F (a i).obj) (fun i ↦ F (b i).obj) g
    (fun j ↦ congrArg (fun Y ↦ F Y.obj) (hab j (by simp))) rfl (by simp)

/-- On a string of morphisms `aᵢ ⟶ bᵢ` which is not composable, an operation of the induced
category vanishes. -/
private theorem evalNat_inducedOperation_eq_zero {k : ℕ}
    {z : ℕ → TotalHom R (InducedQuiver C F)} {a b : ℕ → InducedQuiver C F}
    (hz : ∀ i < k, z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : ¬ IsChain a b k) :
    evalNat (𝒞.inducedOperation F k) z = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (fun i hi ↦ absurd hi (by omega)) hab
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  obtain ⟨g, hg⟩ := exists_eq_homInclusion hz
  rw [evalNat_def, funext hg,
    𝒞.inducedOperation_succ_of_not_isChainFin F (fun i ↦ a i) (fun i ↦ b i) g hab]

/-! ### The Stasheff identities -/

section Stasheff

variable {d : ℕ → ℤ} {x : ℕ → TotalHom R (InducedQuiver C F)} {a b : ℕ → InducedQuiver C F}
  {n p s : ℕ}

/-- The inner operation of a Stasheff term on a string of morphisms `aᵢ ⟶ bᵢ` is a morphism from
`a (p + s - 1)` to `b p`. -/
private theorem inner_mem (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hs : 1 ≤ s) (hps : p + s ≤ n) :
    evalNat (𝒞.inducedOperation F s) (fun j ↦ x (p + j)) ∈
      LinearMap.range (homInclusion (R := R) (a (p + s - 1)) (b p)) := by
  have h := evalNat_inducedOperation_mem (𝒞 := 𝒞) hs (z := fun j ↦ x (p + j))
    (a := fun j ↦ a (p + j)) (b := fun j ↦ b (p + j)) fun i hi ↦ hx (p + i) (by omega)
  rwa [show p + (s - 1) = p + s - 1 by omega, add_zero] at h

/-- Replacing a block of a string of morphisms `aᵢ ⟶ bᵢ` by a morphism from `a (p + s - 1)` to
`b p` gives a string of morphisms between the replaced objects. -/
private theorem replaceBlock_mem
    (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    {e : TotalHom R (InducedQuiver C F)}
    (he : e ∈ LinearMap.range (homInclusion (R := R) (a (p + s - 1)) (b p))) (hps : p + s ≤ n) :
    ∀ i < p + 1 + (n - p - s), replaceBlock x p s e i ∈ LinearMap.range
      (homInclusion (R := R) (replaceBlock a p s (a (p + s - 1)) i)
        (replaceBlock b p s (b p) i)) := by
  intro i hi
  rcases lt_trichotomy i p with h | rfl | h
  · rw [replaceBlock_of_lt _ _ _ _ h, replaceBlock_of_lt _ _ _ _ h, replaceBlock_of_lt _ _ _ _ h]
    exact hx i (by omega)
  · rwa [replaceBlock_self, replaceBlock_self, replaceBlock_self]
  · rw [replaceBlock_of_gt _ _ _ _ h, replaceBlock_of_gt _ _ _ _ h, replaceBlock_of_gt _ _ _ _ h]
    exact hx (i + s - 1) (by omega)

/-- A Stasheff term of the induced category on a string of morphisms `aᵢ ⟶ bᵢ` is a morphism from
`a (n - 1)` to `b 0`. -/
private theorem stasheffTerm_mem
    (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) (hs : 1 ≤ s)
    (hps : p + s ≤ n) :
    stasheffTerm (𝒞.inducedOperation F) d x p s (n - p - s) ∈
      LinearMap.range (homInclusion (R := R) (a (n - 1)) (b 0)) := by
  rw [stasheffTerm_def]
  refine Submodule.smul_mem _ _ ?_
  have h := evalNat_inducedOperation_mem (𝒞 := 𝒞) (by omega)
    (replaceBlock_mem hx (inner_mem (𝒞 := 𝒞) hx hs hps) hps)
  have ha : replaceBlock a p s (a (p + s - 1)) (p + 1 + (n - p - s) - 1) = a (n - 1) := by
    rcases Nat.eq_or_lt_of_le (show p ≤ p + 1 + (n - p - s) - 1 by omega) with he | hlt
    · rw [← he, replaceBlock_self, show p + s - 1 = n - 1 by omega]
    · rw [replaceBlock_of_gt _ _ _ _ hlt, show p + 1 + (n - p - s) - 1 + s - 1 = n - 1 by omega]
  have hb : replaceBlock b p s (b p) 0 = b 0 := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact replaceBlock_self _ _ _ _
    · exact replaceBlock_of_lt _ _ _ _ hp
  rwa [ha, hb] at h

/-- On a composable string, the map of total modules sends each Stasheff term of the induced
category to the corresponding Stasheff term of `𝒞`. -/
private theorem totalHomMap_stasheffTerm
    (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : IsChain a b n) (hs : 1 ≤ s) (hps : p + s ≤ n) :
    totalHomMap R F (stasheffTerm (𝒞.inducedOperation F) d x p s (n - p - s)) =
      stasheffTerm 𝒞.m d (fun i ↦ totalHomMap R F (x i)) p s (n - p - s) := by
  rw [stasheffTerm_def, stasheffTerm_def, map_smul,
    totalHomMap_evalNat_inducedOperation (by omega)
      (replaceBlock_mem hx (inner_mem (𝒞 := 𝒞) hx hs hps) hps) (hab.replaceBlock hs hps),
    ← totalHomMap_evalNat_inducedOperation hs (fun i hi ↦ hx (p + i) (by omega)) (hab.block hps)]
  congr 2
  exact funext fun i ↦ apply_replaceBlock _ _ _ _ _ _

/-- On a string which is not composable, every Stasheff term of the induced category vanishes. -/
private theorem stasheffTerm_eq_zero
    (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : ¬ IsChain a b n) (hs : 1 ≤ s) (hps : p + s ≤ n) :
    stasheffTerm (𝒞.inducedOperation F) d x p s (n - p - s) = 0 := by
  rcases not_isChain_block_or_replaceBlock hab hps with h | h
  · rw [stasheffTerm_def,
      evalNat_inducedOperation_eq_zero (fun i hi ↦ hx (p + i) (by omega)) h, evalNat_def,
      (MultilinearMap.map_coord_zero _ (⟨p, by omega⟩ : Fin (p + 1 + (n - p - s))) (by simp)),
      smul_zero]
  · rw [stasheffTerm_def,
      evalNat_inducedOperation_eq_zero (replaceBlock_mem hx (inner_mem (𝒞 := 𝒞) hx hs hps) hps) h,
      smul_zero]

/-- The Stasheff identities of the induced category on homogeneous morphisms `aᵢ ⟶ bᵢ`.  On a
composable string, the Stasheff sum is a morphism `a (n - 1) ⟶ b 0`, which the map of total
modules sends to the Stasheff sum of `𝒞`; on any other string every term vanishes. -/
private theorem stasheffSum_inducedOperation_of_mem (hn : 0 < n)
    (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hd : ∀ i < n, x i ∈ (totalGrading R (InducedQuiver C F)).piece (d i)) :
    stasheffSum (𝒞.inducedOperation F) d x n = 0 := by
  have hterm (p : ℕ) (hp : p ∈ Finset.range (n + 1)) (s : ℕ) (hs : s ∈ Finset.Icc 1 (n - p)) :
      1 ≤ s ∧ p + s ≤ n := by
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Icc] at hs
    omega
  by_cases hab : IsChain a b n
  · have hmem : stasheffSum (𝒞.inducedOperation F) d x n ∈
        LinearMap.range (homInclusion (R := R) (a (n - 1)) (b 0)) := by
      rw [stasheffSum_def]
      exact Submodule.sum_mem _ fun p hp ↦ Submodule.sum_mem _ fun s hs ↦
        stasheffTerm_mem (𝒞 := 𝒞) (d := d) hx (hterm p hp s hs).1 (hterm p hp s hs).2
    have hmap : totalHomMap R F (stasheffSum (𝒞.inducedOperation F) d x n) = 0 := by
      rw [stasheffSum_def, map_sum]
      simp_rw [map_sum]
      rw [← 𝒞.stasheff n hn d (fun i ↦ totalHomMap R F (x i)) fun i hi ↦ by
        rw [𝒞.grading_eq]
        exact totalHomMap_mem_totalGrading_piece (hd i hi), stasheffSum_def]
      exact Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun s hs ↦
        totalHomMap_stasheffTerm hx hab (hterm p hp s hs).1 (hterm p hp s hs).2
    obtain ⟨g, hg⟩ := hmem
    rw [← hg, totalHomMap_homInclusion] at hmap
    rw [← hg, (homInclusion_injective _ _).eq_iff.1 (hmap.trans (map_zero _).symm), map_zero]
  · rw [stasheffSum_def]
    exact Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun s hs ↦
      stasheffTerm_eq_zero (𝒞 := 𝒞) (d := d) hx hab (hterm p hp s hs).1 (hterm p hp s hs).2

end Stasheff

variable (𝒞 F)

/-- The operations of the induced category have degree `2 - n`. -/
private theorem isHomogeneous_inducedOperation (n : ℕ) (hn : 0 < n) :
    MultilinearMap.IsHomogeneous (𝒞.inducedOperation F n)
      (fun _ ↦ (totalGrading R (InducedQuiver C F)).piece)
      (totalGrading R (InducedQuiver C F)).piece (2 - n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  refine MultilinearMap.isHomogeneous_def.2 fun d y hy ↦
    multilinearMap_apply_mem_of_mem_totalGrading_piece (fun s t x hx ↦ ?_) hy
  by_cases h : IsChainFin F fun i ↦ (s i, t i)
  · rw [𝒞.inducedOperation_succ_of_isChainFin F s t x h, homInclusion_mem_totalGrading_piece_iff]
    refine homProjection_mem_piece (𝒞.m_mem_totalGrading_piece d _ fun i ↦ ?_) _ _
    exact (homInclusion_mem_totalGrading_piece_iff _ _).2 (hx i)
  · rw [𝒞.inducedOperation_succ_of_not_isChainFin F s t x h]
    exact zero_mem _

/-- The Stasheff identities of the induced category.  Through the suspended bar construction, an
arity component of `b ∘ b` is multilinear in its inputs, so it suffices to check them on
homogeneous morphisms, each in a single hom module. -/
private theorem stasheffSum_inducedOperation (n : ℕ) (hn : 0 < n) (d : ℕ → ℤ)
    (x : ℕ → TotalHom R (InducedQuiver C F))
    (hx : ∀ i < n, x i ∈ (totalGrading R (InducedQuiver C F)).piece (d i)) :
    stasheffSum (𝒞.inducedOperation F) d x n = 0 := by
  set G := totalGrading R (InducedQuiver C F)
  have hFm := isSuspension_suspensionTaylor G (𝒞.inducedOperation F)
  have hm (k : ℕ) (hk : 0 < k) (_ : k ≤ n) := 𝒞.isHomogeneous_inducedOperation F k hk
  have key : ((ReducedTensorWords.gradedCoderiv (G.shift 1) (suspensionTaylor G
      (𝒞.inducedOperation F)) 1 ∘ₗ ReducedTensorWords.gradedCoderiv (G.shift 1)
        (suspensionTaylor G (𝒞.inducedOperation F)) 1).taylorComponent ⟨n, hn⟩).compMultilinearMap
      (PiTensorProduct.tprod R) (fun i : Fin n ↦ x i) ∈ (⊥ : Submodule R _) := by
    refine multilinearMap_apply_mem_of_mem_totalGrading_piece (d := fun i ↦ d i)
      (fun s t g hg ↦ ?_) fun i ↦ hx i i.isLt
    -- Extend the string `g` of homogeneous morphisms `sᵢ ⟶ tᵢ` to inputs indexed by `ℕ`.
    let q : ℕ → InducedQuiver C F × InducedQuiver C F := fun i ↦
      if h : i < n then (s ⟨i, h⟩, t ⟨i, h⟩) else (s ⟨0, hn⟩, t ⟨0, hn⟩)
    let y : ℕ → TotalHom R (InducedQuiver C F) := fun i ↦
      if h : i < n then homInclusion (s ⟨i, h⟩) (t ⟨i, h⟩) (g ⟨i, h⟩) else 0
    have hy (i : ℕ) (hi : i < n) : y i = homInclusion (s ⟨i, hi⟩) (t ⟨i, hi⟩) (g ⟨i, hi⟩) := by
      simp only [y, hi, ↓reduceDIte]
    have hq (i : ℕ) (hi : i < n) : q i = (s ⟨i, hi⟩, t ⟨i, hi⟩) := by
      simp only [q, hi, ↓reduceDIte]
    have hyq (i : ℕ) (hi : i < n) :
        y i ∈ LinearMap.range (homInclusion (R := R) (q i).1 (q i).2) := by
      rw [hq i hi, hy i hi]
      exact LinearMap.mem_range_self _ _
    have hyd (i : ℕ) (hi : i < n) : y i ∈ G.piece (d i) := by
      rw [hy i hi, homInclusion_mem_totalGrading_piece_iff]
      exact hg ⟨i, hi⟩
    have hyg : (fun i : Fin n ↦ y i) = fun i ↦ homInclusion (s i) (t i) (g i) :=
      funext fun i ↦ hy i i.isLt
    rw [LinearMap.compMultilinearMap_apply, ← hyg,
      hFm.taylorComponent_comp_self_eq_smul_stasheffSum hm hn d y hyd,
      stasheffSum_inducedOperation_of_mem hn hyq hyd, smul_zero]
    exact zero_mem _
  rwa [Submodule.mem_bot, LinearMap.compMultilinearMap_apply,
    hFm.taylorComponent_comp_self_eq_smul_stasheffSum hm hn d x hx,
    negOnePowCast_smul_eq_zero_iff] at key

/-- The operations of the induced category are path-compatible. -/
private theorem isPathCompatible_inducedOperation (n : ℕ) (hn : 0 < n) :
    IsPathCompatible (𝒞.inducedOperation F n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  refine ⟨fun X x ↦ ?_, fun s t x i j hij hne ↦ ?_⟩
  · have h : IsChainFin F fun i : Fin (n + 1) ↦ (X i.rev.castSucc, X i.rev.succ) := fun i hi ↦
      congrArg X <| Fin.ext <| by
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_rev]
        omega
    rw [𝒞.inducedOperation_succ_of_isChainFin F _ _ x h,
      show X (Fin.last n).rev.castSucc = X 0 by simp,
      show X (Fin.rev 0).succ = X (Fin.last (n + 1)) by simp]
    exact LinearMap.mem_range_self _ _
  · refine 𝒞.inducedOperation_succ_of_not_isChainFin F s t x fun h ↦ hne ?_
    have hj : j = ⟨i + 1, by omega⟩ := Fin.ext hij
    rw [hj]
    exact h i (by omega)

/-- The total algebra of morphisms of the induced category. -/
private noncomputable def inducedAlgebra : AInfinityAlgebra R (TotalHom R (InducedQuiver C F)) :=
  AInfinityAlgebra.ofStasheff (totalGrading R (InducedQuiver C F)) (𝒞.inducedOperation F)
    (𝒞.inducedOperation_zero F) (𝒞.isHomogeneous_inducedOperation F) _
    (isSuspension_suspensionTaylor _ _) (𝒞.stasheffSum_inducedOperation F)

/-- The **`A∞` category induced** by `𝒞` along a map of objects `F : D → C`: the `A∞` category on
the induced quiver whose operation on a composable string `X₀, …, Xₙ` is the operation of `𝒞` on
`F X₀, …, F Xₙ` (`TauCeti.AInfinityCategory.coe_pathOperation_induced_apply`). -/
noncomputable def induced : AInfinityCategory R (InducedQuiver C F) where
  toAInfinityAlgebra := 𝒞.inducedAlgebra F
  grading_eq := AInfinityAlgebra.ofStasheff_grading _ _ _ _ _ _ _
  isPathCompatible_m_of_pos n hn := by
    rw [inducedAlgebra, AInfinityAlgebra.ofStasheff_m]
    exact 𝒞.isPathCompatible_inducedOperation F n hn

private theorem induced_m : (𝒞.induced F).m = 𝒞.inducedOperation F :=
  AInfinityAlgebra.ofStasheff_m _ _ _ _ _ _ _

/-- **The induced category has the operations of `𝒞` on composable strings.** On a string of
morphisms `sᵢ ⟶ tᵢ` of the induced quiver in which the source of each morphism is the target of the
next one, the map of total modules sends the operation of the induced category to the operation of
`𝒞` on the same morphisms. -/
theorem totalHomMap_induced_m_of_chain {n : ℕ} (s t : Fin n → InducedQuiver C F)
    (x : ∀ i, homModule (R := R) (s i) (t i))
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → t j = s i) :
    totalHomMap R F ((𝒞.induced F).m n fun i ↦ homInclusion (s i) (t i) (x i)) =
      𝒞.m n fun i ↦ homInclusion (R := R) (F (s i).obj) (F (t i).obj) (x i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [AInfinityAlgebra.m_zero]
  -- Index the string by the naturals, with an arbitrary extension beyond its length.
  let a : ℕ → InducedQuiver C F := fun i ↦ if h : i < n then s ⟨i, h⟩ else s ⟨0, hn⟩
  let b : ℕ → InducedQuiver C F := fun i ↦ if h : i < n then t ⟨i, h⟩ else t ⟨0, hn⟩
  let z : ℕ → TotalHom R (InducedQuiver C F) := fun i ↦
    if h : i < n then homInclusion (s ⟨i, h⟩) (t ⟨i, h⟩) (x ⟨i, h⟩) else 0
  have hz (i : ℕ) (hi : i < n) : z i = homInclusion (s ⟨i, hi⟩) (t ⟨i, hi⟩) (x ⟨i, hi⟩) := by
    simp only [z, hi, ↓reduceDIte]
  have hzab (i : ℕ) (hi : i < n) :
      z i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)) := by
    have ha : a i = s ⟨i, hi⟩ := by simp only [a, hi, ↓reduceDIte]
    have hb : b i = t ⟨i, hi⟩ := by simp only [b, hi, ↓reduceDIte]
    rw [ha, hb, hz i hi]
    exact LinearMap.mem_range_self _ _
  have hab : IsChain a b n := fun i hi ↦ by
    simp only [a, b, hi, show i < n by omega, ↓reduceDIte]
    exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  have e := totalHomMap_evalNat_inducedOperation (𝒞 := 𝒞) hn hzab hab
  have hzx : (fun i : Fin n ↦ z i) = fun i ↦ homInclusion (s i) (t i) (x i) :=
    funext fun i ↦ hz i i.isLt
  have hzF : (fun i : Fin n ↦ totalHomMap R F (z i)) =
      fun i ↦ homInclusion (R := R) (F (s i).obj) (F (t i).obj) (x i) :=
    funext fun i ↦ by rw [hz i i.isLt, totalHomMap_homInclusion]
  rwa [evalNat_def, evalNat_def, ← induced_m, hzx, hzF] at e

/-- The operation of the induced category on a composable string `X₀, …, Xₙ` is the operation of
`𝒞` on the string `F X₀, …, F Xₙ`. -/
@[simp]
theorem coe_pathOperation_induced_apply {n : ℕ} (X : Fin (n + 1) → InducedQuiver C F)
    (d : Fin n → ℤ) (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    ((𝒞.induced F).pathOperation X d x :
        homModule (R := R) (F (X 0).obj) (F (X (Fin.last n)).obj)) =
      𝒞.pathOperation (fun k ↦ F (X k).obj) d x := by
  apply homInclusion_injective (F (X 0).obj) (F (X (Fin.last n)).obj)
  rw [← totalHomMap_homInclusion, homInclusion_pathOperation,
    totalHomMap_induced_m_of_chain _ _ _ _ _ fun i j hij ↦ ?_]
  · exact (𝒞.homInclusion_pathOperation (fun k ↦ F (X k).obj) d x).symm
  · refine congrArg X (Fin.ext ?_)
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_rev]
    omega

/-- The induced category is the unique `A∞` category on the induced quiver whose operations on
composable strings the map of total modules sends to the operations of `𝒞`. -/
theorem eq_induced {𝒟 : AInfinityCategory R (InducedQuiver C F)}
    (h : ∀ (n : ℕ) (X : Fin (n + 1) → InducedQuiver C F)
      (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)),
        totalHomMap R F (𝒟.m n fun i ↦ homInclusion _ _ (x i)) =
          𝒞.m n fun i ↦
            homInclusion (R := R) (F (X i.rev.castSucc).obj) (F (X i.rev.succ).obj) (x i)) :
    𝒟 = 𝒞.induced F := by
  refine ext <| funext fun n ↦
    (𝒟.isPathCompatible_m n).ext ((𝒞.induced F).isPathCompatible_m n) fun X x ↦ ?_
  obtain ⟨f, hf⟩ := (𝒟.isPathCompatible_m n).mem_range_homInclusion X x
  obtain ⟨g, hg⟩ := ((𝒞.induced F).isPathCompatible_m n).mem_range_homInclusion X x
  have e := (h n X x).trans (totalHomMap_induced_m_of_chain 𝒞 F _ _ x fun i j hij ↦ by
    congr 1
    ext
    simp [Fin.val_rev]
    omega).symm
  rw [← hf, ← hg, totalHomMap_homInclusion, totalHomMap_homInclusion] at e
  rw [← hf, ← hg, homInclusion_injective _ _ e]

/-- The differential of the induced category is the differential of `𝒞`. -/
@[simp]
theorem homDifferential_induced (X Y : InducedQuiver C F) (f : homModule (R := R) X Y) :
    (𝒞.induced F).homDifferential X Y f = 𝒞.homDifferential (F X.obj) (F Y.obj) f := by
  apply homInclusion_injective (F X.obj) (F Y.obj)
  have e := 𝒞.totalHomMap_induced_m_of_chain F ![X] ![Y] (Fin.cases f finZeroElim)
    fun i j hij ↦ absurd j.isLt (by omega)
  have h₁ : (fun i : Fin 1 ↦ homInclusion (R := R) (![X] i) (![Y] i)
      ((Fin.cases f finZeroElim : ∀ i : Fin 1, homModule (R := R) (![X] i) (![Y] i)) i)) =
      ![homInclusion X Y f] := by
    funext i
    fin_cases i
    rfl
  have h₂ : (fun i : Fin 1 ↦ homInclusion (R := R) (F (![X] i).obj) (F (![Y] i).obj)
      ((Fin.cases f finZeroElim : ∀ i : Fin 1, homModule (R := R) (![X] i) (![Y] i)) i)) =
      ![homInclusion (R := R) (F X.obj) (F Y.obj) f] := by
    funext i
    fin_cases i
    rfl
  rw [h₁, h₂] at e
  rw [← totalHomMap_homInclusion, homInclusion_homDifferential, homInclusion_homDifferential,
    AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply, e]

/-- The composition of the induced category is the composition of `𝒞`. -/
@[simp]
theorem comp_induced (X Y Z : InducedQuiver C F) (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y) :
    (𝒞.induced F).comp X Y Z g f = 𝒞.comp (F X.obj) (F Y.obj) (F Z.obj) g f := by
  apply homInclusion_injective (F X.obj) (F Z.obj)
  have e := 𝒞.totalHomMap_induced_m_of_chain F ![Y, X] ![Z, Y]
    (Fin.cases g (Fin.cases f finZeroElim)) fun i j hij ↦ by
      fin_cases i <;> fin_cases j <;> simp_all
  have h₁ : (fun i : Fin 2 ↦ homInclusion (R := R) (![Y, X] i) (![Z, Y] i)
      ((Fin.cases g (Fin.cases f finZeroElim) :
        ∀ i : Fin 2, homModule (R := R) (![Y, X] i) (![Z, Y] i)) i)) =
      ![homInclusion Y Z g, homInclusion X Y f] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : (fun i : Fin 2 ↦ homInclusion (R := R) (F (![Y, X] i).obj) (F (![Z, Y] i).obj)
      ((Fin.cases g (Fin.cases f finZeroElim) :
        ∀ i : Fin 2, homModule (R := R) (![Y, X] i) (![Z, Y] i)) i)) =
      ![homInclusion (R := R) (F Y.obj) (F Z.obj) g,
        homInclusion (R := R) (F X.obj) (F Y.obj) f] := by
    funext i
    fin_cases i <;> rfl
  rw [h₁, h₂] at e
  rw [← totalHomMap_homInclusion, homInclusion_comp, homInclusion_comp, e]

end AInfinityCategory

end TauCeti
