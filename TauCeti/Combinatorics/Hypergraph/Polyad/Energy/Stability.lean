/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stability of polyad energy under polyad matchings and pair recolorings

Refining a lower skeleton cannot decrease the polyad energy of a `Colored3Graph`
(`Colored3Graph.polyadEnergy_mono_of_refines`), whereas recoloring pairs on the lower skeleton can
merge or move triples between polyads and lose energy. When the old polyads embed injectively into
the new polyads along `f : Polyad3 S → Polyad3 T`, extending the old polyad color densities along
`f` by `0` gives a polyad-measurable test family on `T`. Comparing `H.polyadEnergy T` against this
test family shows that each injective triple `x` with `ofTriple T x = f (ofTriple S x)` contributes
zero loss, while each moved triple contributes at most `3 / |V|₃`, independently of the sizes of
the top and pair palettes (`Colored3Graph.polyadEnergy_sub_le_of_injective`).

Combining refinement monotonicity on vertex cells with `Polyad3.coarsen_injective` and the moved-
triple count `Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le` bounds the energy loss when
simultaneously refining vertex cells and recoloring ordered vertex pairs up to an injective palette
map (`Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring`).

## Main results

* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_injective`: polyad energy decreases by at most
  `3 #M / |V|.descFactorial 3` when `M` injective triples fail to follow an injective map of
  polyads.
* `TauCeti.Colored3Graph.polyadEnergy_sub_le_of_pairRecoloring`: refining vertex cells and
  recoloring `|E|` ordered distinct vertex pairs (modulo an injective palette map) decreases polyad
  energy by at most `9 |E| |V| / |V|.descFactorial 3`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] [Fintype κ]
  (H : Colored3Graph κ V)

omit [DecidableEq κ] in
/-- For any nonnegative vector `p : κ → ℝ` summing to at most `1` and any coordinate `c₀`,
`2 p c₀ - ∑ c, p c ^ 2` lies in `[-1, 2]`. -/
private theorem two_mul_sub_sum_sq_bounds {p : κ → ℝ} (hp₀ : ∀ c, 0 ≤ p c)
    (hp₁ : ∑ c, p c ≤ 1) (c₀ : κ) :
    -1 ≤ 2 * p c₀ - ∑ c, p c ^ 2 ∧ 2 * p c₀ - ∑ c, p c ^ 2 ≤ 2 := by
  have hc₀_le : p c₀ ≤ 1 := (single_le_sum (fun c _ ↦ hp₀ c) (mem_univ c₀)).trans hp₁
  have hsq_nn : 0 ≤ ∑ c, p c ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsq_le : ∑ c, p c ^ 2 ≤ 1 :=
    (sum_le_sum fun c _ ↦ by
      have hc : p c ≤ 1 := (single_le_sum (fun c' _ ↦ hp₀ c') (mem_univ c)).trans hp₁
      nlinarith [hp₀ c]).trans hp₁
  exact ⟨by linarith [hp₀ c₀], by linarith⟩

/-- At any polyad `P`, the cast relative densities sum to at most `1`. -/
private theorem sum_relativeDensity_le_one {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    ∑ c, (H.relativeDensity c P : ℝ) ≤ 1 := by
  rcases P.support.eq_empty_or_nonempty with hP | hP
  · simp [H.relativeDensity_of_support_eq_empty _ hP]
  · exact (by exact_mod_cast H.sum_relativeDensity hP :
      ∑ c, (H.relativeDensity c P : ℝ) = 1).le

/-- Variational lower bound for the unnormalized polyad energy against any test family
`ψ : Polyad3 T → κ → ℝ`. -/
private theorem sum_two_mul_sub_sum_sq_le {T : PairSkeleton3 κ₂' V} (ψ : Polyad3 T → κ → ℝ) :
    ∑ x : {x : Fin 3 → V // Function.Injective x},
      (2 * ψ (Polyad3.ofTriple T x) (H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)) -
        ∑ c, ψ (Polyad3.ofTriple T x) c ^ 2) ≤
      ∑ x : {x : Fin 3 → V // Function.Injective x},
        ∑ c, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2 := by
  let col (x : {x : Fin 3 → V // Function.Injective x}) : κ :=
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
  have hcross : ∑ x, ∑ c, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) *
        ψ (Polyad3.ofTriple T x) c =
      ∑ x, ψ (Polyad3.ofTriple T x) (col x) := by
    rw [sum_comm]
    calc ∑ c, ∑ x, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) * ψ (Polyad3.ofTriple T x) c
        = ∑ c, ∑ x with col x = c, ψ (Polyad3.ofTriple T x) c :=
          sum_congr rfl fun c _ ↦
            H.sum_relativeDensity_ofTriple_mul c _ fun _ _ hxy ↦ by rw [hxy]
      _ = ∑ c, ∑ x with col x = c, ψ (Polyad3.ofTriple T x) (col x) :=
          sum_congr rfl fun c _ ↦ sum_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
      _ = ∑ x, ψ (Polyad3.ofTriple T x) (col x) :=
          sum_fiberwise univ col fun x ↦ ψ (Polyad3.ofTriple T x) (col x)
  have hsq : 0 ≤ ∑ x : {x : Fin 3 → V // Function.Injective x}, ∑ c,
      ((H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) - ψ (Polyad3.ofTriple T x) c) ^ 2 :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum] at hsq ⊢
  linarith

/-- For the true relative densities on `S`, the variational expression equals the unnormalized
polyad energy. -/
private theorem sum_two_mul_sub_sum_sq_eq (S : PairSkeleton3 κ₂ V) :
    ∑ x : {x : Fin 3 → V // Function.Injective x},
      (2 * (H.relativeDensity (H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩))
          (Polyad3.ofTriple S x) : ℝ) -
        ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2) =
      ∑ x : {x : Fin 3 → V // Function.Injective x},
        ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 := by
  let col (x : {x : Fin 3 → V // Function.Injective x}) : κ :=
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
  have hdiag : ∑ x, ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 =
      ∑ x, (H.relativeDensity (col x) (Polyad3.ofTriple S x) : ℝ) := by
    rw [sum_comm]
    calc ∑ c, ∑ x, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2
        = ∑ c, ∑ x with col x = c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) :=
          sum_congr rfl fun c _ ↦ by
            simp_rw [sq]
            exact H.sum_relativeDensity_ofTriple_mul c _ fun _ _ hxy ↦ by rw [hxy]
      _ = ∑ c, ∑ x with col x = c, (H.relativeDensity (col x) (Polyad3.ofTriple S x) : ℝ) :=
          sum_congr rfl fun c _ ↦ sum_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
      _ = ∑ x, (H.relativeDensity (col x) (Polyad3.ofTriple S x) : ℝ) :=
          sum_fiberwise univ col fun x ↦ (H.relativeDensity (col x) (Polyad3.ofTriple S x) : ℝ)
  simp only [sum_sub_distrib, ← mul_sum]
  linarith

open Classical in
/-- **Polyad energy stability under an injective polyad matching.** If `f : Polyad3 S → Polyad3 T`
is injective, passing from `S` to `T` decreases `H.polyadEnergy` by at most
`3 #M / |V|.descFactorial 3`, where `M` is the set of injective triples `x` with
`ofTriple T x ≠ f (ofTriple S x)`. The constant `3` is independent of all palette sizes. -/
theorem polyadEnergy_sub_le_of_injective {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    {f : Polyad3 S → Polyad3 T} (hf : Function.Injective f) :
    H.polyadEnergy S - H.polyadEnergy T ≤
      3 * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 := by
  let φ : Polyad3 S → κ → ℝ := fun P c ↦ H.relativeDensity c P
  let ψ : Polyad3 T → κ → ℝ := Function.extend f φ 0
  let col (x : {x : Fin 3 → V // Function.Injective x}) : κ :=
    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
  have hψ (Q : Polyad3 T) : (∀ c, 0 ≤ ψ Q c) ∧ ∑ c, ψ Q c ≤ 1 := by
    by_cases hQ : ∃ P, f P = Q
    · obtain ⟨P, rfl⟩ := hQ
      simp only [ψ, hf.extend_apply]
      exact ⟨fun c ↦ Rat.cast_nonneg.2 (H.relativeDensity_nonneg c P),
        H.sum_relativeDensity_le_one P⟩
    · simp [ψ, Function.extend_apply' _ _ _ hQ]
  set M := (univ : Finset {x : Fin 3 → V // Function.Injective x}).filter
    fun x ↦ Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)
  have hterm (x : {x : Fin 3 → V // Function.Injective x}) :
      (2 * φ (Polyad3.ofTriple S x) (col x) - ∑ c, φ (Polyad3.ofTriple S x) c ^ 2) -
        (2 * ψ (Polyad3.ofTriple T x) (col x) - ∑ c, ψ (Polyad3.ofTriple T x) c ^ 2) ≤
      if x ∈ M then 3 else 0 := by
    by_cases hx : x ∈ M
    · have hS := two_mul_sub_sum_sq_bounds
        (fun c ↦ Rat.cast_nonneg.2 (H.relativeDensity_nonneg c (Polyad3.ofTriple S x)))
        (H.sum_relativeDensity_le_one (Polyad3.ofTriple S x)) (col x)
      have hT := two_mul_sub_sum_sq_bounds (hψ (Polyad3.ofTriple T x)).1
        (hψ (Polyad3.ofTriple T x)).2 (col x)
      simp only [hx, ↓reduceIte]
      linarith
    · have heq : Polyad3.ofTriple T x = f (Polyad3.ofTriple S x) := by
        simpa [M] using hx
      simp [hx, heq, ψ, hf.extend_apply]
  rw [polyadEnergy_def, polyadEnergy_def, ← sub_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc (∑ x, ∑ c, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2) -
        ∑ x, ∑ c, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2
      ≤ (∑ x, (2 * φ (Polyad3.ofTriple S x) (col x) - ∑ c, φ (Polyad3.ofTriple S x) c ^ 2)) -
          ∑ x, (2 * ψ (Polyad3.ofTriple T x) (col x) - ∑ c, ψ (Polyad3.ofTriple T x) c ^ 2) := by
        linarith [H.sum_two_mul_sub_sum_sq_eq S, H.sum_two_mul_sub_sum_sq_le ψ]
    _ = ∑ x, ((2 * φ (Polyad3.ofTriple S x) (col x) - ∑ c, φ (Polyad3.ofTriple S x) c ^ 2) -
          (2 * ψ (Polyad3.ofTriple T x) (col x) - ∑ c, ψ (Polyad3.ofTriple T x) c ^ 2)) := by
        rw [← sum_sub_distrib]
    _ ≤ ∑ x, if x ∈ M then (3 : ℝ) else 0 := sum_le_sum fun x _ ↦ hterm x
    _ = 3 * #M := by
        rw [sum_ite, sum_const_zero, add_zero, filter_mem_eq_inter, univ_inter, sum_const,
          nsmul_eq_mul, mul_comm]

open Classical in
/-- **Polyad energy stability under vertex refinement and pair recoloring.** Let the vertex cells of
`T` refine those of `S`, and let `g : κ₂ ↪ κ₂'` embed the old pair palette into the new one. The
polyad energy of `H` decreases by at most `9 |E| |V| / |V|.descFactorial 3`, where `E` is the set of
ordered distinct vertex pairs `p` with `T.pairColors.color p ≠ g (S.pairColors.color p)`. -/
theorem polyadEnergy_sub_le_of_pairRecoloring {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}
    (hV : T.vertexPart ≤ S.vertexPart) (g : κ₂ ↪ κ₂') :
    H.polyadEnergy S - H.polyadEnergy T ≤
      (9 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V : ℕ) /
        (Fintype.card V).descFactorial 3 := by
  let S₁ : PairSkeleton3 κ₂ V := ⟨T.vertexPart, S.pairColors⟩
  have href : H.polyadEnergy S ≤ H.polyadEnergy S₁ :=
    H.polyadEnergy_mono_of_refines fun x y hxy ↦ by
      rw [← Polyad3.coarsen_ofTriple (S := S) (T := S₁) hV id (fun _ ↦ rfl) x,
        ← Polyad3.coarsen_ofTriple (S := S) (T := S₁) hV id (fun _ ↦ rfl) y, hxy]
  have hVT : S₁.vertexPart = T.vertexPart := rfl
  have hinj := Polyad3.coarsen_injective (S := T) (T := S₁) hVT g.injective
  have hmove := Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le (S := T) (T := S₁) hVT.le g
  have hrec := H.polyadEnergy_sub_le_of_injective hinj
  refine (sub_le_sub_right href _).trans (hrec.trans ?_)
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hmul : 3 * #{x | Polyad3.ofTriple T x ≠ (Polyad3.ofTriple S₁ x).coarsen hVT.le g} ≤
      9 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V :=
    calc 3 * #{x | Polyad3.ofTriple T x ≠ (Polyad3.ofTriple S₁ x).coarsen hVT.le g}
        ≤ 3 * (3 * #{p | T.pairColors.color p ≠ g (S₁.pairColors.color p)} * Fintype.card V) :=
          Nat.mul_le_mul_left 3 hmove
      _ = 9 * #{p | T.pairColors.color p ≠ g (S.pairColors.color p)} * Fintype.card V := by
          dsimp only [S₁]
          ring
  exact_mod_cast hmul

end TauCeti.Colored3Graph
