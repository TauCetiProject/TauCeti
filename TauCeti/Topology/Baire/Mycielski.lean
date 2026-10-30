/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import TauCeti.SetTheory.Descriptive.Antichain
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.MetricSpace.CantorScheme
import TauCeti.Topology.Constructions.Pi
import TauCeti.Topology.MetricSpace.Perfect
import TauCeti.Topology.MetricSpace.PiNat

/-!
# Mycielski's theorem

**Mycielski's theorem**: let `X` be a nonempty perfect completely metrizable space (for example
a nonempty perfect Polish space), and for every `n` let `R n` be a meagre set of `k n`-tuples of
points of `X`. Then there is a continuous injection `f` of Cantor space `ℕ → Bool` into `X` that
avoids every `R n` on injective tuples: whenever `a : Fin (k n) → (ℕ → Bool)` is injective, the
tuple `f ∘ a` is not in `R n`.

The binary case says that a meagre subset of `X × X` misses every pair `(f x, f y)` with `x ≠ y`.
For the graph of an equivalence relation this produces a Cantor antichain: a meagre equivalence
relation on a nonempty perfect completely metrizable space has a continuous injection of Cantor
space whose distinct points are inequivalent. This is the last step of the category proof of
Silver's theorem, where the pulled-back equivalence relation on Cantor space is shown to be meagre
by the Kuratowski–Ulam theorem.

The proof builds a scheme of nonempty open sets indexed by finite binary words, level by level.
Each set contains the closures of its two children, which are disjoint and have diameter at most
`1 / (j + 1)` at level `j + 1` (`IsOpen.exists_disjoint_closure_subset`). After splitting, the
sets of the new level are shrunk so that, for every injective tuple of distinct sets of the
level, their product lies in finitely many of the dense open sets whose intersection misses `R n`
(`TauCeti.exists_forall_univ_pi_subset`). Two distinct branches of Cantor space pass through
distinct sets from their first difference on (`PiNat.eventually_injective_res`), so the induced
map sends an injective tuple into every one of these dense open sets, hence outside `R n`.
Avoidance holds only in the limit: a dense meagre set meets every product of nonempty open sets,
so no finite stage avoids it.

## Main results

* `TauCeti.mycielski`: Mycielski's theorem.
* `TauCeti.mycielski_prod`: the binary case, for one meagre subset of `X × X`.
* `Setoid.hasCantorAntichainOn_univ_of_isMeagre`: a meagre equivalence relation has a Cantor
  antichain.

## References

* J. Mycielski, *Independent sets in topological algebras*, Fund. Math. 55 (1964), 139–147.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 19.1.
* The scheme is assembled with Mathlib's `CantorScheme.inducedMap`, as in Mathlib's proof of
  `Perfect.exists_nat_bool_injection`.
-/

public section

open Set Function Filter Topology CantorScheme
open scoped ENNReal

namespace TauCeti

section Mycielski

variable {X : Type*}

/-- One level of the Mycielski scheme. The nonempty open sets `S l` of level `j` (words `l` of
length `j`) are split into disjoint children of diameter at most `1 / (j + 1)` with closures in
their parents, and then shrunk so that the products of distinct children along injective tuples
lie in the dense open sets `D n m` with `n, m ≤ j`. -/
private theorem mycielski_step [EMetricSpace X] [PerfectSpace X] {k : ℕ → ℕ}
    {D : ∀ n, ℕ → Set (Fin (k n) → X)} (hDo : ∀ n m, IsOpen (D n m))
    (hDd : ∀ n m, Dense (D n m)) (j : ℕ) {S : List Bool → Set X}
    (hSo : ∀ l : List Bool, l.length = j → IsOpen (S l))
    (hSne : ∀ l : List Bool, l.length = j → (S l).Nonempty) :
    ∃ S' : List Bool → Set X, (∀ l : List Bool, l.length = j + 1 → IsOpen (S' l)) ∧
      (∀ l : List Bool, l.length = j + 1 → (S' l).Nonempty) ∧
      (∀ (l : List Bool) b, l.length = j → closure (S' (b :: l)) ⊆ S l) ∧
      (∀ (l : List Bool) b, l.length = j → Metric.ediam (S' (b :: l)) ≤ ((j : ℝ≥0∞) + 1)⁻¹) ∧
      (∀ l : List Bool, l.length = j → Disjoint (S' (false :: l)) (S' (true :: l))) ∧
      ∀ n ≤ j, ∀ m ≤ j, ∀ t : Fin (k n) → List Bool, Injective t →
        (∀ i, (t i).length = j + 1) → univ.pi (fun i => S' (t i)) ⊆ D n m := by
  classical
  -- split every set of level `j`
  choose! W hWo hWne hWcl hWd hWdisj using fun (l : List Bool) (hl : l.length = j) =>
    (hSo l hl).exists_disjoint_closure_subset (hSne l hl)
      (ε := ((j : ℝ≥0∞) + 1)⁻¹) (by simp)
  -- shrink the children, indexed by the finitely many words of length `j + 1`
  let I := {l : List Bool // l.length = j + 1}
  have : Finite I := (List.finite_length_eq Bool (j + 1)).to_subtype
  have hlen (l : I) : l.1.tail.length = j := by simp [l.2]
  obtain ⟨W', hW'o, hW'ne, hW'W, hW'⟩ := exists_forall_univ_pi_subset
    (V := fun l : I => W l.1.tail l.1.headI) (fun l => hWo _ (hlen l) _)
    (fun l => hWne _ (hlen l) _) (κ := fun c : Fin (j + 1) × Fin (j + 1) => Fin (k c.1))
    (U := fun c => D c.1 c.2) (fun _ => hDo _ _) (fun _ => hDd _ _)
  let S' : List Bool → Set X := fun l => if h : l.length = j + 1 then W' ⟨l, h⟩ else ∅
  have hS' (l : List Bool) (h : l.length = j + 1) : S' l = W' ⟨l, h⟩ := by simp [S', h]
  have hS'W (l : List Bool) (b : Bool) (hl : l.length = j) : S' (b :: l) ⊆ W l b := by
    rw [hS' _ (by simp [hl])]
    exact hW'W _
  refine ⟨S', fun l hl => hS' l hl ▸ hW'o _, fun l hl => hS' l hl ▸ hW'ne _,
    fun l b hl => (closure_mono (hS'W l b hl)).trans (hWcl l hl b),
    fun l b hl => (Metric.ediam_mono (hS'W l b hl)).trans (hWd l hl b),
    fun l hl => (hWdisj l hl).mono (hS'W l false hl) (hS'W l true hl),
    fun n hn m hm t ht htl => ?_⟩
  have h := hW' (⟨n, by omega⟩, ⟨m, by omega⟩) (fun i => ⟨t i, htl i⟩)
    fun i i' hii' => ht (congrArg Subtype.val hii')
  simpa [hS' _ (htl _)] using h

/-- The Mycielski scheme. In a nonempty perfect metric space, given dense open sets `D n m`, there
is a scheme of nonempty open sets indexed by binary words, each containing the closures of its
two disjoint children, with vanishing diameter, such that at every level `j` the products of
distinct sets of the level along injective tuples lie in `D n m` for `n, m < j`. -/
private theorem exists_mycielski_scheme [MetricSpace X] [PerfectSpace X] [Nonempty X]
    {k : ℕ → ℕ} {D : ∀ n, ℕ → Set (Fin (k n) → X)} (hDo : ∀ n m, IsOpen (D n m))
    (hDd : ∀ n m, Dense (D n m)) :
    ∃ A : List Bool → Set X, (∀ l, (A l).Nonempty) ∧ ClosureAntitone A ∧ VanishingDiam A ∧
      CantorScheme.Disjoint A ∧ ∀ n m j, n < j → m < j → ∀ t : Fin (k n) → List Bool,
        Injective t → (∀ i, (t i).length = j) → univ.pi (fun i => A (t i)) ⊆ D n m := by
  -- the levels of the scheme, built one after the other by `mycielski_step`
  choose! next hnexto hnextne hnextcl hnextd hnextdisj hnextD using
    fun j (S : List Bool → Set X) => mycielski_step hDo hDd j (S := S)
  let lvl : ℕ → List Bool → Set X := fun j => Nat.rec (fun _ => univ) next j
  have hlvl (j : ℕ) : lvl (j + 1) = next j (lvl j) := rfl
  have hgood (j : ℕ) : (∀ l : List Bool, l.length = j → IsOpen (lvl j l)) ∧
      ∀ l : List Bool, l.length = j → (lvl j l).Nonempty := by
    induction j with
    | zero => exact ⟨fun _ _ => isOpen_univ, fun _ _ => univ_nonempty⟩
    | succ j ih => exact ⟨hlvl j ▸ hnexto j _ ih.1 ih.2, hlvl j ▸ hnextne j _ ih.1 ih.2⟩
  -- the scheme reads each word at its own level
  let A : List Bool → Set X := fun l => lvl l.length l
  have hAcons (b : Bool) (l : List Bool) : A (b :: l) = next l.length (lvl l.length) (b :: l) :=
    rfl
  refine ⟨A, fun l => (hgood l.length).2 l rfl, fun l b => ?_, fun x => ?_, ?_,
    fun n m j hn hm t ht htl => ?_⟩
  · rw [hAcons]
    exact hnextcl _ _ (hgood _).1 (hgood _).2 l b rfl
  · -- the diameter at level `n` is at most `1 / n`
    have hle (l : List Bool) : Metric.ediam (A l) ≤ (l.length : ℝ≥0∞)⁻¹ := by
      cases l with
      | nil => simp
      | cons b l =>
        rw [hAcons, List.length_cons, Nat.cast_succ]
        exact hnextd _ _ (hgood _).1 (hgood _).2 l b rfl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ => bot_le) fun n => ?_
    simpa [PiNat.res_length] using hle (PiNat.res x n)
  · rintro l (_ | _) (_ | _) hab <;> try contradiction
    · simpa [hAcons] using hnextdisj _ _ (hgood _).1 (hgood _).2 l rfl
    · simpa [hAcons] using (hnextdisj _ _ (hgood _).1 (hgood _).2 l rfl).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : j ≠ 0)
    have h := hnextD j (lvl j) (hgood j).1 (hgood j).2 n (by omega) m (by omega) t ht htl
    simpa [A, htl, hlvl] using h

/-- **Mycielski's theorem.** Let `X` be a nonempty perfect completely metrizable space, for
example a nonempty perfect Polish space, and let `R n` be a meagre set of `k n`-tuples of points
of `X` for each `n`. There is a continuous injection `f` of Cantor space into `X` such that for
every `n` and every injective tuple `a` of `k n` points of Cantor space, `f ∘ a ∉ R n`. -/
theorem mycielski [TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace X]
    [PerfectSpace X] [Nonempty X] (k : ℕ → ℕ) (R : ∀ n, Set (Fin (k n) → X))
    (hR : ∀ n, IsMeagre (R n)) :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Injective f ∧
      ∀ n (a : Fin (k n) → ℕ → Bool), Injective a → f ∘ a ∉ R n := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  -- the complement of each `R n` contains a countable intersection of dense open sets
  have hD (n : ℕ) : ∃ D : ℕ → Set (Fin (k n) → X), (∀ m, IsOpen (D m)) ∧ (∀ m, Dense (D m)) ∧
      ⋂ m, D m ⊆ (R n)ᶜ := by
    obtain ⟨T, hTo, hTd, hTc, hT⟩ := mem_residual_iff.1 (hR n)
    obtain ⟨D, hD⟩ := (hTc.insert univ).exists_eq_range (insert_nonempty _ _)
    have hDT (m : ℕ) : D m = univ ∨ D m ∈ T := by
      rw [← mem_insert_iff, hD]
      exact mem_range_self m
    refine ⟨D, fun m => ?_, fun m => ?_, fun x hx => hT fun s hs => ?_⟩
    · rcases hDT m with h | h
      exacts [h ▸ isOpen_univ, hTo _ h]
    · rcases hDT m with h | h
      exacts [h ▸ dense_univ, hTd _ h]
    · obtain ⟨m, rfl⟩ : s ∈ range D := hD ▸ mem_insert_of_mem _ hs
      exact mem_iInter.1 hx m
  choose D hDo hDd hDR using hD
  -- the map induced by the Mycielski scheme
  obtain ⟨A, hAne, hanti, hdiam, hdisj, hAD⟩ := exists_mycielski_scheme hDo hDd
  have hdom (x : ℕ → Bool) : x ∈ (inducedMap A).1 := by
    rw [hanti.map_of_vanishingDiam hdiam hAne]
    exact mem_univ x
  let f : (ℕ → Bool) → X := fun x => (inducedMap A).2 ⟨x, hdom x⟩
  refine ⟨f, hdiam.map_continuous.comp (by fun_prop), fun x y hxy => ?_, fun n a ha hR => ?_⟩
  · simpa using hdisj.map_injective hxy
  -- at a level where the branches of `a` have separated, `f ∘ a` lies in a product of distinct
  -- sets of the scheme, hence in `D n m`
  refine hDR n (mem_iInter.2 fun m => ?_) hR
  obtain ⟨j, ⟨hj, hjn⟩, hjm⟩ :=
    (((PiNat.eventually_injective_res ha).and (eventually_gt_atTop n)).and
      (eventually_gt_atTop m)).exists
  exact hAD n m j hjn hjm _ hj (fun i => PiNat.res_length _ _) fun i _ =>
    map_mem ⟨a i, hdom (a i)⟩ j

/-- **Mycielski's theorem, binary case.** A meagre subset `M` of `X × X`, for a nonempty perfect
completely metrizable space `X`, misses every pair `(f x, f y)` with `x ≠ y` for some continuous
injection `f` of Cantor space into `X`. -/
theorem mycielski_prod [TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace X]
    [PerfectSpace X] [Nonempty X] {M : Set (X × X)} (hM : IsMeagre M) :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Injective f ∧ ∀ x y, x ≠ y → (f x, f y) ∉ M := by
  let e := Homeomorph.finTwoArrow (X := X)
  obtain ⟨f, hf, hinj, hfM⟩ := mycielski (fun _ => 2) (fun _ => e ⁻¹' M)
    fun _ => hM.preimage_of_isOpenMap e.continuous e.isOpenMap
  refine ⟨f, hf, hinj, fun x y hxy hM => hfM 0 ![x, y] ?_ (by simpa [e] using hM)⟩
  intro i i' h
  fin_cases i <;> fin_cases i' <;> simp_all [eq_comm]

end Mycielski

end TauCeti

/-- **A meagre equivalence relation has a Cantor antichain.** If the graph of an equivalence
relation `E` on a nonempty perfect completely metrizable space is meagre in `X × X`, there is a
continuous map of Cantor space into `X` whose distinct points have `E`-inequivalent images. -/
theorem Setoid.hasCantorAntichainOn_univ_of_isMeagre {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] [PerfectSpace X] [Nonempty X]
    (E : Setoid X) (hE : IsMeagre {p : X × X | E p.1 p.2}) : E.HasCantorAntichainOn univ := by
  obtain ⟨f, hf, -, hfE⟩ := TauCeti.mycielski_prod hE
  exact Setoid.hasCantorAntichainOn_iff.2 ⟨f, hf, fun _ => mem_univ _, hfE⟩
