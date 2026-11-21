/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Directed
public import TauCeti.Analysis.Convex.Lifting.OuterApproximation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Finset.Order
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.BigOperators.Sum.Sup

/-!
# Finite support elimination for shared and independent height systems

Given a finite index set `ι` of separable components and families of componentwise lower bounds,
there are two canonical lifted polyhedral systems with free height variables:

* `TauCeti.sharedRows`: a single height vector `y : ι → β` simultaneously dominates every active
  support row `row j i x ≤ y j` (`i ∈ H j`) subject to the sum budget `∑ j, y j ≤ b`.
* `TauCeti.independentRows`: each anchor `a : κ` carries its own independent height vector
  `y a : ι → β` dominating `row a j x ≤ y a j` subject to its own budget `∑ j, y a j ≤ b a`.

When every support set `H j` is nonempty, projecting `sharedRows` eliminates the free heights
exactly, yielding both the sum of componentwise maxima
(`TauCeti.exists_mem_sharedRows_iff_sum_sup'_le`) and the system of all mixed-choice row sums
(`TauCeti.exists_mem_sharedRows_iff_forall_choice`).
If some component has empty support `H j₀ = ∅` and heights range over an ordered directed group,
the projection collapses to `D` (`TauCeti.exists_mem_sharedRows_iff_of_exists_empty`). By contrast,
projecting `independentRows` recovers only the same-anchor diagonal sums
(`TauCeti.exists_mem_independentRows_iff`).

For the sum outer function `y ↦ ∑ j, y j` with free height domain `E = Set.univ`, without
assuming convexity or differentiability, `TauCeti.directOA` coincides algebraically with the
projection `Prod.fst '' independentRows` (`TauCeti.directOA_sum_eq_fst_image_independentRows`),
and for a nonempty finite anchor set `TauCeti.sharedOA` coincides with `TauCeti.sharedRows`
(`TauCeti.sharedOA_sum_eq_sharedRows`). For any nonempty anchor family (finite or infinite), the
projection of `TauCeti.sharedOA` is characterized by all mixed-choice sums
(`TauCeti.mem_fst_image_sharedOA_sum_iff_forall_choice`). A concrete two-anchor squared-component
witness (`TauCeti.exists_strict_sharedOA_ssubset_directOA`) shows that both inclusions
`{x ∈ D | h (g x) ≤ b} ⊂ Prod.fst '' sharedOA ⊂ directOA` can be strict.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Math. Program. 103 (2005), 225–249, §2, Proposition 5, p. 231.
* J. Kronqvist, A. Lundell, and T. Westerlund, *Reformulations for utilizing separability when
  solving convex MINLP problems*, J. Global Optim. 71 (2018), 571–592, §3, Eqs. (4)–(7) and
  Proposition 1, p. 574.
-/

public section

open Finset Set

namespace TauCeti

section Definitions

variable {X ι I κ β : Type*} [Fintype ι] [AddCommMonoid β] [LE β]

/-- Pairs `(x, y)` with `x ∈ D`, a single free height vector `y : ι → β` dominating every active
support row `row j i x ≤ y j` for `i ∈ H j`, and total budget `∑ j, y j ≤ b`. -/
def sharedRows (D : Set X) (row : ι → I → X → β) (H : ι → Finset I) (b : β) :
    Set (X × (ι → β)) :=
  {z | z.1 ∈ D ∧ (∀ j, ∀ i ∈ H j, row j i z.1 ≤ z.2 j) ∧ ∑ j, z.2 j ≤ b}

/-- Pairs `(x, y)` with `x ∈ D` and an independent height vector `y a : ι → β` per anchor `a : κ`
dominating `row a j x ≤ y a j` with per-anchor budget `∑ j, y a j ≤ b a`. -/
def independentRows (D : Set X) (row : κ → ι → X → β) (b : κ → β) :
    Set (X × (κ → ι → β)) :=
  {z | z.1 ∈ D ∧ ∀ a, (∀ j, row a j z.1 ≤ z.2 a j) ∧ ∑ j, z.2 a j ≤ b a}

@[simp]
theorem mem_sharedRows {D : Set X} {row : ι → I → X → β} {H : ι → Finset I} {b : β}
    {z : X × (ι → β)} :
    z ∈ sharedRows D row H b ↔
      z.1 ∈ D ∧ (∀ j, ∀ i ∈ H j, row j i z.1 ≤ z.2 j) ∧ ∑ j, z.2 j ≤ b :=
  (Iff.rfl)

@[simp]
theorem mem_independentRows {D : Set X} {row : κ → ι → X → β} {b : κ → β}
    {z : X × (κ → ι → β)} :
    z ∈ independentRows D row b ↔
      z.1 ∈ D ∧ ∀ a, (∀ j, row a j z.1 ≤ z.2 a j) ∧ ∑ j, z.2 a j ≤ b a :=
  (Iff.rfl)

/-- With zero components, `sharedRows` projects to `x ∈ D ∧ 0 ≤ b`. -/
theorem exists_mem_sharedRows_of_isEmpty [IsEmpty ι] {D : Set X} {row : ι → I → X → β}
    {H : ι → Finset I} {b : β} {x : X} :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔ x ∈ D ∧ (0 : β) ≤ b := by
  simp

/-- With zero anchors, `independentRows` projects to `x ∈ D`. -/
theorem exists_mem_independentRows_of_isEmpty_anchor [IsEmpty κ] {D : Set X}
    {row : κ → ι → X → β} {b : κ → β} {x : X} :
    (∃ y, (x, y) ∈ independentRows D row b) ↔ x ∈ D := by
  simp

/-- With zero components, `independentRows` projects to `x ∈ D ∧ ∀ a, 0 ≤ b a`. -/
theorem exists_mem_independentRows_of_isEmpty [IsEmpty ι] {D : Set X}
    {row : κ → ι → X → β} {b : κ → β} {x : X} :
    (∃ y, (x, y) ∈ independentRows D row b) ↔ x ∈ D ∧ ∀ a, (0 : β) ≤ b a := by
  simp

end Definitions

section Elimination

variable {X ι I κ β : Type*} [Fintype ι]

/-- **Shared-row projection (sum of componentwise maxima).** When every support set `H j` is
nonempty, `x` lifts to a point of `sharedRows` if and only if `x ∈ D` and the sum of the
componentwise maxima over `H j` is at most `b`. -/
theorem exists_mem_sharedRows_iff_sum_sup'_le [AddCommMonoid β] [SemilatticeSup β]
    [IsOrderedAddMonoid β] {D : Set X} {row : ι → I → X → β} {H : ι → Finset I}
    (hne : ∀ j, (H j).Nonempty) {b : β} {x : X} :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔
      x ∈ D ∧ ∑ j, (H j).sup' (hne j) (fun i => row j i x) ≤ b := by
  refine ⟨fun ⟨y, hxD, hy, hsum⟩ =>
      ⟨hxD, (sum_le_sum fun j _ => sup'_le _ _ fun i hi => hy j i hi).trans hsum⟩,
    fun ⟨hxD, hsum⟩ =>
      ⟨fun j => (H j).sup' (hne j) (fun i => row j i x), hxD,
        fun j i hi => le_sup' (fun i => row j i x) hi, hsum⟩⟩

/-- **Shared-row projection (all mixed choices).** Over a linearly ordered additive commutative
monoid, when every support set `H j` is nonempty, `x` lifts to a point of `sharedRows` if and only
if `x ∈ D` and every mixed-choice sum `∑ j, row j (choice j) x` with `choice j ∈ H j` is at most
`b`. -/
theorem exists_mem_sharedRows_iff_forall_choice [AddCommMonoid β] [LinearOrder β]
    [IsOrderedAddMonoid β] {D : Set X} {row : ι → I → X → β} {H : ι → Finset I}
    (hne : ∀ j, (H j).Nonempty) {b : β} {x : X} :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔
      x ∈ D ∧ ∀ choice : ι → I, (∀ j, choice j ∈ H j) → ∑ j, row j (choice j) x ≤ b := by
  rw [exists_mem_sharedRows_iff_sum_sup'_le hne,
    sum_sup'_le_iff_forall_choice H hne (fun j i => row j i x) b]

/-- **Shared-row projection with an unconstrained component.** If some component `j₀` has empty
support `H j₀ = ∅` and heights range over a directed preordered additive commutative group, then
every `x ∈ D` lifts to `sharedRows` by absorbing the budget residual into coordinate `j₀`. -/
theorem exists_mem_sharedRows_iff_of_exists_empty [AddCommGroup β] [Preorder β]
    [IsDirectedOrder β] {D : Set X} {row : ι → I → X → β} {H : ι → Finset I} {b : β} {x : X}
    (hempty : ∃ j₀, H j₀ = ∅) :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔ x ∈ D := by
  classical
  refine ⟨fun ⟨_, hxD, _⟩ => hxD, fun hxD => ?_⟩
  obtain ⟨j₀, hj₀⟩ := hempty
  have hbound : ∀ j, ∃ u : β, ∀ i ∈ H j, row j i x ≤ u := fun j => by
    obtain ⟨u, hu⟩ := Finset.exists_le ((H j).image fun i => row j i x)
    exact ⟨u, fun i hi => hu _ (mem_image_of_mem _ hi)⟩
  choose u hu using hbound
  let y : ι → β := Function.update u j₀ (b - ∑ k ∈ univ \ {j₀}, u k)
  refine ⟨y, mem_sharedRows.2 ⟨hxD, fun j i hi => ?_, ?_⟩⟩
  · rcases eq_or_ne j j₀ with rfl | hjj
    · simp [hj₀] at hi
    · simpa [y, hjj] using hu j i hi
  · rw [Finset.sum_update_of_mem (Finset.mem_univ j₀), sub_add_cancel]

/-- **Independent-row projection.** When each anchor carries its own free height vector, eliminating
the heights yields exactly `x ∈ D` together with each same-anchor diagonal sum inequality. -/
theorem exists_mem_independentRows_iff [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    {D : Set X} {row : κ → ι → X → β} {b : κ → β} {x : X} :
    (∃ y, (x, y) ∈ independentRows D row b) ↔ x ∈ D ∧ ∀ a, ∑ j, row a j x ≤ b a :=
  ⟨fun ⟨_, hxD, ha⟩ => ⟨hxD, fun a => (sum_le_sum fun j _ => (ha a).1 j).trans (ha a).2⟩,
    fun ⟨hxD, hsum⟩ => ⟨fun a j => row a j x, hxD, fun a => ⟨fun _ => le_rfl, hsum a⟩⟩⟩

end Elimination

section SumOuterCorrespondence

/-- For the sum outer function `v ↦ ∑ j, v j` and its derivative `∑ j, proj j`, the outer row is
simply the sum `∑ j, y j`. -/
@[simp]
theorem outerRow_sum {X ι : Type*} [Fintype ι] (g : X → ι → ℝ) (a : X) (y : ι → ℝ) :
    outerRow g (fun v => ∑ j, v j) a (∑ j, ContinuousLinearMap.proj (R := ℝ) j) y = ∑ j, y j := by
  rw [outerRow_apply]
  simp [sum_apply]

variable {X ι κ : Type*} [AddCommGroup X] [TopologicalSpace X] [Module ℝ X] [Fintype ι]

/-- For the sum outer function `v ↦ ∑ j, v j`, the direct row is the sum of the component rows at
the same anchor. -/
@[simp]
theorem directRow_sum (g : X → ι → ℝ) (a : X) (Dg : X →L[ℝ] (ι → ℝ)) (x : X) :
    directRow g (fun v => ∑ j, v j) a Dg (∑ j, ContinuousLinearMap.proj (R := ℝ) j) x =
      ∑ j, componentRow g a Dg x j := by
  rw [← outerRow_componentRow, outerRow_sum]

/-- Purely algebraic identification of `directOA` for the sum outer function with the projection of
`independentRows`. No convexity or differentiability of `g` is assumed. -/
theorem directOA_sum_eq_fst_image_independentRows (D : Set X) (g : X → ι → ℝ) (a : κ → X)
    (Dg : κ → X →L[ℝ] (ι → ℝ)) (b : ℝ) :
    directOA D g (fun v => ∑ j, v j) a Dg
        (fun _ => ∑ j, ContinuousLinearMap.proj (R := ℝ) j) b =
      Prod.fst ''
        independentRows D (fun i j x => componentRow g (a i) (Dg i) x j) (fun _ => b) := by
  ext x
  simp only [mem_directOA, directRow_sum, mem_image, Prod.exists, exists_and_right,
    exists_eq_right, exists_mem_independentRows_iff]

/-- Purely algebraic identification of `sharedOA` on `E = Set.univ` for the sum outer function with
`sharedRows` over a nonempty finite anchor set. No convexity or differentiability of `g` is
assumed. -/
theorem sharedOA_sum_eq_sharedRows [Fintype κ] [Nonempty κ] (D : Set X) (g : X → ι → ℝ)
    (a : κ → X) (Dg : κ → X →L[ℝ] (ι → ℝ)) (b : ℝ) :
    sharedOA D Set.univ g (fun v => ∑ j, v j) a Dg
        (fun _ => ∑ j, ContinuousLinearMap.proj (R := ℝ) j) b =
      sharedRows D (fun j i x => componentRow g (a i) (Dg i) x j) (fun _ => Finset.univ) b := by
  ext ⟨x, y⟩
  simp only [mem_sharedOA, Set.mem_univ, true_and, outerRow_sum, mem_sharedRows, Finset.mem_univ,
    forall_const, Pi.le_def, forall_and]
  exact ⟨fun ⟨hxD, hcomp, hsum⟩ => ⟨hxD, fun j i => hcomp i j, hsum⟩,
    fun ⟨hxD, hcomp, hsum⟩ => ⟨hxD, fun i j => hcomp j i, hsum⟩⟩

/-- For the sum outer function with free heights (`E = Set.univ`) and a nonempty finite anchor set,
the projection of `sharedOA` is given by the sum of componentwise maxima of component rows. -/
theorem mem_fst_image_sharedOA_sum_iff_sum_sup'_le [Fintype κ] [Nonempty κ] {D : Set X}
    {g : X → ι → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {b : ℝ} {x : X} :
    x ∈ Prod.fst '' sharedOA D Set.univ g (fun v => ∑ j, v j) a Dg
        (fun _ => ∑ j, ContinuousLinearMap.proj (R := ℝ) j) b ↔
      x ∈ D ∧
        ∑ j, (Finset.univ : Finset κ).sup' Finset.univ_nonempty
          (fun i => componentRow g (a i) (Dg i) x j) ≤ b := by
  rw [sharedOA_sum_eq_sharedRows]
  simpa only [mem_image, Prod.exists, exists_and_right, exists_eq_right] using
    exists_mem_sharedRows_iff_sum_sup'_le (β := ℝ)
      (row := fun j i x => componentRow g (a i) (Dg i) x j)
      (fun _ : ι => Finset.univ_nonempty (α := κ)) (D := D) (b := b) (x := x)

/-- For the sum outer function with free heights (`E = Set.univ`) and any nonempty anchor family
(finite or infinite), the projection of `sharedOA` is given by all mixed-choice sums of component
rows across anchors. -/
theorem mem_fst_image_sharedOA_sum_iff_forall_choice [Nonempty κ] {D : Set X}
    {g : X → ι → ℝ} {a : κ → X} {Dg : κ → X →L[ℝ] (ι → ℝ)} {b : ℝ} {x : X} :
    x ∈ Prod.fst '' sharedOA D Set.univ g (fun v => ∑ j, v j) a Dg
        (fun _ => ∑ j, ContinuousLinearMap.proj (R := ℝ) j) b ↔
      x ∈ D ∧ ∀ choice : ι → κ, ∑ j, componentRow g (a (choice j)) (Dg (choice j)) x j ≤ b := by
  classical
  constructor
  · rintro ⟨⟨_, y⟩, hmem, rfl⟩
    obtain ⟨hxD, _, hrow⟩ := mem_sharedOA.1 hmem
    have hsum : ∑ j, y j ≤ b := by
      simpa only [outerRow_sum] using (hrow (Classical.arbitrary κ)).2
    exact ⟨hxD, fun choice => (sum_le_sum fun j _ => (hrow (choice j)).1 j).trans hsum⟩
  · rintro ⟨hxD, hall⟩
    let r : ι → κ → ℝ := fun j i => componentRow g (a i) (Dg i) x j
    let i₀ : κ := Classical.arbitrary κ
    have hbdd : ∀ j, BddAbove (range (r j)) := fun j => by
      refine ⟨b - ∑ k ∈ univ \ {j}, r k i₀, ?_⟩
      rintro _ ⟨i, rfl⟩
      have hch : ∑ k, r k (Function.update (fun _ => i₀) j i k) ≤ b :=
        hall (Function.update (fun _ => i₀) j i)
      simp_rw [Function.apply_update r] at hch
      rw [Finset.sum_update_of_mem (Finset.mem_univ j)] at hch
      linarith
    let y : ι → ℝ := fun j => ⨆ i : κ, r j i
    refine ⟨(x, y), mem_sharedOA.2 ⟨hxD, Set.mem_univ _, fun i =>
      ⟨fun j => le_ciSup (hbdd j) i, ?_⟩⟩, rfl⟩
    rw [outerRow_sum]
    exact (sum_ciSup_le_iff_forall_choice r hbdd b).2 hall

end SumOuterCorrespondence

section Separation

/-- Strict separation of the original feasible set, shared-height projection
(`Prod.fst '' sharedOA`), and direct outer approximation (`directOA`) — bridged to `sharedRows`
and `independentRows` by `sharedOA_sum_eq_sharedRows` and
`directOA_sum_eq_fst_image_independentRows`: for `g x j = x j ^ 2` and `h y = ∑ j, y j` on the
box `[-1, 1]²` with anchors `(1, 1)` and `(-1, -1)` and budget `1 / 2`, the matched
actual-derivative outer approximations satisfy
`{x ∈ D | h (g x) ≤ 1 / 2} ⊂ Prod.fst '' sharedOA ⊂ directOA`, witnessed by `(1, 1 / 4)` and
`(1, -1)`. -/
theorem exists_strict_sharedOA_ssubset_directOA :
    ∃ (D : Set (Fin 2 → ℝ)) (g : (Fin 2 → ℝ) → Fin 2 → ℝ) (h : (Fin 2 → ℝ) → ℝ)
      (a : Fin 2 → Fin 2 → ℝ) (Dg : Fin 2 → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
      (Dh : Fin 2 → (Fin 2 → ℝ) →L[ℝ] ℝ) (b : ℝ),
      (∀ i, a i ∈ D) ∧
      (∀ i, HasFDerivAt g (Dg i) (a i)) ∧
      (∀ i, HasFDerivAt h (Dh i) (g (a i))) ∧
      {x ∈ D | h (g x) ≤ b} ⊂ Prod.fst '' sharedOA D Set.univ g h a Dg Dh b ∧
      Prod.fst '' sharedOA D Set.univ g h a Dg Dh b ⊂ directOA D g h a Dg Dh b := by
  let D : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-1) 1
  let g : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x j => x j ^ 2
  let h : (Fin 2 → ℝ) → ℝ := fun y => ∑ j, y j
  let a : Fin 2 → Fin 2 → ℝ := fun i _ => if i = 0 then 1 else -1
  let Dg : Fin 2 → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    fun i => (2 * a i 0) • ContinuousLinearMap.id ℝ _
  let Dh : Fin 2 → (Fin 2 → ℝ) →L[ℝ] ℝ := fun _ => ∑ j, ContinuousLinearMap.proj (R := ℝ) j
  have ha : ∀ i, a i ∈ D := fun i _ _ => by by_cases hi : i = 0 <;> simp [a, hi]
  have hg : ∀ i, HasFDerivAt g (Dg i) (a i) := fun i => hasFDerivAt_pi'.2 fun j => by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a i j) (a i j) := by
      simpa using hasDerivAt_pow 2 (a i j)
    have hL : (ContinuousLinearMap.proj (R := ℝ) j).comp (Dg i) =
        (2 * a i j) • ContinuousLinearMap.proj (R := ℝ) j := by
      simp only [Dg, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, a]
    rw [hL]; exact hpow.comp_hasFDerivAt (a i) (hasFDerivAt_apply (𝕜 := ℝ) j (a i))
  have hh : ∀ i, HasFDerivAt h (Dh i) (g (a i)) := fun i =>
    HasFDerivAt.fun_sum fun j _ => hasFDerivAt_apply (𝕜 := ℝ) j (g (a i))
  have hhc : ConvexOn ℝ Set.univ h := by
    let s : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := ∑ j : Fin 2, LinearMap.proj (R := ℝ) j
    have hs : (s : (Fin 2 → ℝ) → ℝ) = h := by ext y; simp [s, h]
    exact hs ▸ s.convexOn convex_univ
  have hc : ∀ j, ConvexOn ℝ D (fun x => g x j) := fun j => by
    let pj : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) j
    simpa [g, pj, Function.comp_def] using ((even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap
      pj).subset (subset_univ _) (convex_pi fun _ _ => convex_Icc (-1) 1)
  have hcmp := fullspace_analytic_comparison (1 / 2)
    (fun _ _ hxy => sum_le_sum fun j _ => hxy j) hc hhc ha hg hh
  have hstrict1 : ¬ Prod.fst '' sharedOA D Set.univ g h a Dg Dh (1 / 2) ⊆
      {x ∈ D | h (g x) ≤ 1 / 2} := fun hsub => by
    have horig := (hsub ⟨(![1, 1 / 4], ![1, -1 / 2]), mem_sharedOA.2 ⟨fun j _ => by
        fin_cases j <;> norm_num, Set.mem_univ _, fun i => ⟨fun j => by
          fin_cases i <;> fin_cases j <;>
            norm_num [componentRow_apply, g, a, Dg, Matrix.vecTail, Matrix.vecHead,
              Function.comp_def],
        by simp only [h, Dh]; rw [outerRow_sum]; norm_num [Fin.sum_univ_two]⟩⟩, rfl⟩).2
    norm_num [h, g, Fin.sum_univ_two] at horig
  have hstrict2 : ¬ directOA D g h a Dg Dh (1 / 2) ⊆
      Prod.fst '' sharedOA D Set.univ g h a Dg Dh (1 / 2) := fun hsub => by
    have hmem : (![1, -1] : Fin 2 → ℝ) ∈ directOA D g h a Dg Dh (1 / 2) :=
      mem_directOA.2 ⟨fun j _ => by fin_cases j <;> norm_num, fun i => by
        simp only [h, Dh]; rw [directRow_sum]
        fin_cases i <;> norm_num [Fin.sum_univ_two, componentRow_apply, g, a, Dg,
          Matrix.vecTail, Matrix.vecHead, Function.comp_def]⟩
    have hsh := (mem_fst_image_sharedOA_sum_iff_forall_choice.1 (hsub hmem)).2 ![0, 1]
    norm_num [Fin.sum_univ_two, componentRow_apply, g, a, Dg,
      Matrix.vecTail, Matrix.vecHead, Function.comp_def] at hsh
  exact ⟨D, g, h, a, Dg, Dh, 1 / 2, ha, hg, hh,
    ssubset_iff_subset_ne.2 ⟨hcmp.1, fun heq => hstrict1 heq.symm.subset⟩,
    ssubset_iff_subset_ne.2 ⟨hcmp.2, fun heq => hstrict2 heq.symm.subset⟩⟩

end Separation

end TauCeti
