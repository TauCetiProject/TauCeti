/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Instances.Real.Lemmas
public import TauCeti.AlgebraicTopology.AlexanderSpanier.CupLength
import Mathlib.Topology.UniformSpace.OfCompactT2
import TauCeti.AlgebraicTopology.AlexanderSpanier.Homotopy
import TauCeti.Dynamics.Flow.Basic
import TauCeti.Dynamics.Flow.LusternikSchnirelmann

/-!
# The cup-length bound for flows in Alexander–Spanier cohomology

Let `ϕ` be a flow of `ℝ` on a nonempty compact Hausdorff space `α`, more generally a compact
`R1Space`, and let `W : α → ℝ` be a continuous **Lyapunov function**, strictly decreasing along
every nonconstant orbit. Then `ϕ` has at least `cl + 1` rest points, where `cl` is the cup length of
the Alexander–Spanier cohomology `H*(α; Λ)` with coefficients in any algebra `Λ` over a commutative
ring (`Flow.cupLength_add_one_le_encard`). An infinite set of rest points has count `⊤`.

Unlike the bound for singular cohomology `Flow.lsCupLength_add_one_le_encard`, which uses the
Lusternik–Schnirelmann category and therefore needs a locally contractible space, this bound holds
on every compact metric space. This is the generality in which Conley and Zehnder use it, for the
maximal invariant set of an isolating block, which is in general not locally contractible.

The proof applies the abstract Lusternik–Schnirelmann bound `Flow.index_univ_le_encard` to an
index built from a nonzero product `x = a₁ ⌣ ⋯ ⌣ aₙ` of positive-degree classes: the index of a set
`A` is the least number of open sets covering `A` on each of which every factor `aⱼ` restricts to
zero.

* It is monotone, vanishes on `∅` and is subadditive, since covers can be concatenated.
* It does not increase under the time-`t` maps of the flow, which are homotopic to the identity
  and therefore act trivially on Alexander–Spanier cohomology of the compact space `α`.
* It is at most `1` on a neighbourhood of each point, since each of the finitely many factors, of
  positive degree, restricts to zero near every point
  (`TauCeti.AlexanderSpanier.exists_mem_nhds_cohomologyMap_subtypeVal_apply_eq_zero`). Only
  finitely many classes enter, which is why no local contractibility is needed.
* The index of `α` is at least `n + 1`: a cover of `α` by `n` such open sets would make
  `x = a₁ ⌣ ⋯ ⌣ aₙ` vanish on their union
  (`TauCeti.AlexanderSpanier.IsPositiveDegreeCupProduct.exists_factors`), that is, `x = 0`.

## Main results

* `Flow.cupLength_add_one_le_encard`: a flow with a Lyapunov function on a nonempty compact space
  has at least `cl + 1` rest points, for the cup length `cl` of Alexander–Spanier cohomology.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6.
-/

public section

open Set TauCeti TauCeti.AlexanderSpanier Topology

universe w u v

namespace Flow

variable {α : Type u} [TopologicalSpace α] {ϕ : Flow ℝ α} {W : α → ℝ}

variable (R : Type w) [CommRing R] (Λ : Type v) [Ring Λ] [Algebra R Λ]

/-- A family `a` of cohomology classes restricts to zero on an open cover of `A` by `k` sets. -/
private def HasVanishingCover {ι : Type*} (a : ι → Σ p, cohomology R α Λ p) (A : Set α) (k : ℕ) :
    Prop :=
  ∃ U : Fin k → Set α, (∀ i, IsOpen (U i)) ∧ A ⊆ ⋃ i, U i ∧
    ∀ i j, (cohomologyMap R Λ (ContinuousMap.subtypeVal (U i)) (a j).1).hom (a j).2 = 0

/-- The time-`t` map of the flow acts trivially on the Alexander–Spanier cohomology of the
compact space `α`: it is homotopic to the identity through the time-`u t` maps, `u ∈ [0, 1]`. -/
private lemma cohomologyMap_apply_eq_self [CompactSpace α] (t : ℝ) {p : ℕ}
    (c : cohomology R α Λ p) :
    (cohomologyMap R Λ ⟨ϕ t, ϕ.continuous_toFun t⟩ p).hom c = c := by
  have hϕ : (⟨ϕ t, ϕ.continuous_toFun t⟩ : C(α, α)).Homotopic (ContinuousMap.id α) :=
    ϕ.homotopic_of_eq_apply Topology.IsEmbedding.id continuous_id continuous_const
      continuous_const (τ₀ := fun _ ↦ t) (τ₁ := fun _ ↦ 0) (fun _ ↦ rfl)
      (fun x ↦ (map_zero_apply ϕ x).symm) fun x u _ ↦ mem_range_self _
  rw [cohomologyMap_eq_of_homotopic R Λ hϕ, cohomologyMap_id,
    CategoryTheory.ConcreteCategory.id_apply]

/-- A class which restricts to zero on `U` restricts to zero on the preimage of `U` under every
time-`t` map of the flow. -/
private lemma cohomologyMap_subtypeVal_preimage_eq_zero [CompactSpace α] (t : ℝ) {U : Set α} {p : ℕ}
    {c : cohomology R α Λ p}
    (hc : (cohomologyMap R Λ (ContinuousMap.subtypeVal U) p).hom c = 0) :
    (cohomologyMap R Λ (ContinuousMap.subtypeVal (ϕ t ⁻¹' U)) p).hom c = 0 := by
  -- Restricted to `ϕ t ⁻¹' U`, the time-`t` map lands in `U`.
  let r : C(ϕ t ⁻¹' U, U) := ⟨fun x ↦ ⟨ϕ t x, x.property⟩,
    ((ϕ.continuous_toFun t).comp continuous_subtypeVal).subtype_mk _⟩
  have hcomp : (ContinuousMap.subtypeVal U).comp r =
      (⟨ϕ t, ϕ.continuous_toFun t⟩ : C(α, α)).comp (ContinuousMap.subtypeVal (ϕ t ⁻¹' U)) :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← cohomologyMap_apply_eq_self R Λ (ϕ := ϕ) t c, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← cohomologyMap_comp, ← hcomp, cohomologyMap_comp, CategoryTheory.ConcreteCategory.comp_apply,
    hc, _root_.map_zero]

/-- The index of a set `A` for a family `a` of cohomology classes: the least size of an open cover
of `A` on whose members every class of the family restricts to zero. -/
private noncomputable def vanishingCoverIndex {ι : Type*} (a : ι → Σ p, cohomology R α Λ p)
    (A : Set α) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : HasVanishingCover R Λ a A k), (k : ℕ∞)

variable {R Λ} {ι : Type*} {a : ι → Σ p, cohomology R α Λ p}

private lemma vanishingCoverIndex_le {A : Set α} {k : ℕ} (h : HasVanishingCover R Λ a A k) :
    vanishingCoverIndex R Λ a A ≤ k :=
  iInf₂_le k h

private lemma monotone_vanishingCoverIndex : Monotone (vanishingCoverIndex R Λ a) :=
  fun _ _ hAB ↦ le_iInf₂ fun _ ⟨U, hUo, hBU, hU⟩ ↦
    vanishingCoverIndex_le ⟨U, hUo, hAB.trans hBU, hU⟩

private lemma vanishingCoverIndex_empty : vanishingCoverIndex R Λ a ∅ = 0 :=
  nonpos_iff_eq_zero.1
    (vanishingCoverIndex_le ⟨Fin.elim0, fun i ↦ i.elim0, empty_subset _, fun i ↦ i.elim0⟩)

/-- The index is subadditive: covers of `A` and `B` concatenate to a cover of `A ∪ B`. -/
private lemma vanishingCoverIndex_union_le (A B : Set α) :
    vanishingCoverIndex R Λ a (A ∪ B) ≤ vanishingCoverIndex R Λ a A + vanishingCoverIndex R Λ a B :=
  ENat.le_iInf₂_add_iInf₂ fun k₁ ⟨U, hUo, hAU, hU⟩ k₂ ⟨V, hVo, hBV, hV⟩ ↦ by
    have hUV : ∀ i j, (cohomologyMap R Λ (ContinuousMap.subtypeVal (Fin.append U V i))
        (a j).1).hom (a j).2 = 0 := fun i ↦ by
      cases i using Fin.addCases with
      | left i => rw [Fin.append_left]; exact hU i
      | right i => rw [Fin.append_right]; exact hV i
    have hsub : A ∪ B ⊆ ⋃ i, Fin.append U V i := union_subset
      (hAU.trans (iUnion_subset fun i ↦ by
        simpa using subset_iUnion (Fin.append U V) (Fin.castAdd k₂ i)))
      (hBV.trans (iUnion_subset fun i ↦ by
        simpa using subset_iUnion (Fin.append U V) (Fin.natAdd k₁ i)))
    exact (vanishingCoverIndex_le ⟨Fin.append U V,
      Fin.addCases (by simpa using hUo) (by simpa using hVo), hsub, hUV⟩).trans_eq
        (Nat.cast_add k₁ k₂)

/-- The index does not increase under the time-`t` maps of the flow. -/
private lemma vanishingCoverIndex_preimage_le [CompactSpace α] (t : ℝ) (A : Set α) :
    vanishingCoverIndex R Λ a (ϕ t ⁻¹' A) ≤ vanishingCoverIndex R Λ a A :=
  le_iInf₂ fun _ ⟨U, hUo, hAU, hU⟩ ↦ vanishingCoverIndex_le ⟨fun i ↦ ϕ t ⁻¹' U i,
    fun i ↦ (hUo i).preimage (ϕ.continuous_toFun t),
    (preimage_mono hAU).trans preimage_iUnion.subset,
    fun i j ↦ cohomologyMap_subtypeVal_preimage_eq_zero R Λ t (hU i j)⟩

/-- On a compact `R1` space, a finite family of positive-degree classes has index at most `1` on a
neighbourhood of every point, since each class restricts to zero near every point. -/
private lemma exists_mem_nhds_vanishingCoverIndex_le_one [CompactSpace α] [R1Space α] [Finite ι]
    (ha : ∀ j, (a j).1 ≠ 0) (x : α) : ∃ V ∈ 𝓝 x, vanishingCoverIndex R Λ a V ≤ 1 := by
  let : UniformSpace α := uniformSpaceOfCompactR1
  choose N hN hNa using fun j ↦
    exists_mem_nhds_cohomologyMap_subtypeVal_apply_eq_zero R Λ x (ha j) (a j).2
  obtain ⟨V, hVN, hVo, hxV⟩ := mem_nhds_iff.1 (Filter.iInter_mem.2 hN)
  refine ⟨V, hVo.mem_nhds hxV, (vanishingCoverIndex_le (k := 1) ⟨fun _ ↦ V, fun _ ↦ hVo,
    subset_iUnion (fun _ ↦ V) 0, fun _ j ↦ ?_⟩).trans_eq Nat.cast_one⟩
  exact cohomologyMap_subtypeVal_apply_eq_zero_of_subset R Λ (hVN.trans (iInter_subset N j))
    (hNa j)

/-- If a nonzero class `x` vanishes on every union `U₁ ∪ ⋯ ∪ Uₙ` of open sets on which the
positive-degree classes `a₁, …, aₙ` vanish, then the index of the whole space for the family `a` is
at least `n + 1`. -/
private lemma natCast_add_one_le_vanishingCoverIndex_univ {n d : ℕ}
    {a : Fin n → Σ p, cohomology R α Λ p} (ha : ∀ i, (a i).1 ≠ 0) {x : cohomology R α Λ d}
    (hx0 : x ≠ 0)
    (hax : ∀ U : Fin n → Set α, (∀ i, IsOpen (U i)) →
      (∀ i, (cohomologyMap R Λ (ContinuousMap.subtypeVal (U i)) (a i).1).hom (a i).2 = 0) →
        (cohomologyMap R Λ (ContinuousMap.subtypeVal (⋃ i, U i)) d).hom x = 0) :
    (n : ℕ∞) + 1 ≤ vanishingCoverIndex R Λ a univ := by
  refine le_iInf₂ fun k ⟨U, hUo, hU, hUa⟩ ↦ ?_
  by_contra! hk
  have hkn : k ≤ n := by exact_mod_cast Order.le_of_lt_add_one hk
  -- Pad the cover with empty sets to `n` members; every class vanishes on the empty set.
  let U' : Fin n → Set α := fun i ↦ if h : (i : ℕ) < k then U ⟨i, h⟩ else ∅
  have hx' := hax U' (fun i ↦ by
    by_cases h : (i : ℕ) < k
    · simpa [U', h] using hUo ⟨i, h⟩
    · simp [U', h]) fun i ↦ by
    by_cases h : (i : ℕ) < k
    · rw [show U' i = U ⟨i, h⟩ by simp [U', h]]
      exact hUa ⟨i, h⟩ i
    · rw [show U' i = ∅ by simp [U', h]]
      have := subsingleton_cohomology (R := R) (M := Λ) (Y := (∅ : Set α)) (ha i)
      exact Subsingleton.elim _ _
  have hsub : univ ⊆ ⋃ i, U' i := hU.trans (iUnion_subset fun i ↦ by
    simpa [U', i.isLt] using subset_iUnion U' (Fin.castLE hkn i))
  exact hx0 ((cohomologyMap_subtypeVal_univ_apply_eq_zero_iff R Λ).1
    (cohomologyMap_subtypeVal_apply_eq_zero_of_subset R Λ hsub hx'))

/-- **The cup-length bound for flows.** On a nonempty compact `R1` space, such as a compact metric
space, a flow with a continuous function `W` strictly decreasing along every nonconstant orbit has
at least `cl + 1` rest points, where `cl` is the cup length of the Alexander–Spanier cohomology of
the space with coefficients in the `R`-algebra `Λ`. No local contractibility is assumed. -/
theorem cupLength_add_one_le_encard [CompactSpace α] [R1Space α] [Nonempty α] (hWc : Continuous W)
    (hW : ∀ x t, 0 < t → ϕ t x ≠ x → W (ϕ t x) < W x) :
    cupLength R α Λ + 1 ≤ {x | ∀ t, ϕ t x = x}.encard := by
  -- A point where `W` attains its minimum is a rest point.
  have hrest : {x | ∀ t, ϕ t x = x}.Nonempty := by
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hWc.continuousOn
    refine ⟨x, apply_eq_self_of_forall_pos fun t ht ↦ ?_⟩
    by_contra hne
    exact (hW x t ht hne).not_ge (hx (mem_univ _))
  -- Every nonzero product of `n` positive-degree classes gives `n + 1` rest points, by the
  -- Lusternik–Schnirelmann bound for the index of its factors.
  have key (n d : ℕ) (x : cohomology R α Λ d) (hx : IsPositiveDegreeCupProduct R α Λ n x)
      (hx0 : x ≠ 0) : (n : ℕ∞) + 1 ≤ {x | ∀ t, ϕ t x = x}.encard := by
    obtain ⟨a, ha, hax⟩ := hx.exists_factors
    exact (natCast_add_one_le_vanishingCoverIndex_univ ha hx0 hax).trans
      (index_univ_le_encard hWc hW monotone_vanishingCoverIndex vanishingCoverIndex_empty
        vanishingCoverIndex_union_le (fun t _ ↦ vanishingCoverIndex_preimage_le t)
        fun x _ ↦ exists_mem_nhds_vanishingCoverIndex_le_one ha x)
  -- Assemble: if there are `m + 1` rest points, every nonzero product has length at most `m`.
  cases hN : {x | ∀ t, ϕ t x = x}.encard with
  | top => exact le_top
  | coe N =>
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := Nat.exists_eq_add_one.2 (by
      have := (Set.one_le_encard_iff_nonempty.2 hrest).trans_eq hN
      exact_mod_cast this)
    push_cast
    gcongr
    refine cupLength_le_iff.2 fun n d x hx hx0 ↦ ?_
    have := (key n d x hx hx0).trans_eq hN
    push_cast at this
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this

end Flow
