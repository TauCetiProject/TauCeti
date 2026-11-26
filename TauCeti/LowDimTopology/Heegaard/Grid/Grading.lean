/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.LowDimTopology.Heegaard.AlexanderGrading
public import TauCeti.LowDimTopology.Heegaard.Grading
public import TauCeti.LowDimTopology.Heegaard.Grid.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The grid gradings are the Heegaard Floer gradings of every domain

Let `G` be an `n × n` grid diagram, viewed as a multi-pointed genus-one Heegaard diagram
(`TauCeti.GridDiagram.heegaardRegionSystem`) with the `O`-markings as `w`-basepoints, the
`X`-markings as `z`-basepoints and every square a region of Euler characteristic `1`.
`TauCeti.LowDimTopology.Heegaard.Grid.Basic` checks that the grid gradings change across a
rectangle as the Heegaard Floer gradings of its domain. This file proves the same for **every**
domain, as in Manolescu, Ozsváth and Sarkar: for every domain `D` from (the generator of) a grid
state `x` to (the generator of) a grid state `y`,

`M_O(x) - M_O(y) = μ(D) - 2 n_O(D)`, `M_X(x) - M_X(y) = μ(D) - 2 n_X(D)` and
`A(x) - A(y) = n_X(D) - n_O(D)`

(`TauCeti.GridDiagram.maslovIndex_sub_two_mul_sum_basepoint_inl_of_isDomainBetween`,
`TauCeti.GridDiagram.maslovIndex_sub_two_mul_sum_basepoint_inr_of_isDomainBetween`,
`TauCeti.GridDiagram.sum_basepoint_inr_sub_sum_basepoint_inl_of_isDomainBetween`).

The domains from a generator to itself are what separates the general statement from the
rectangle case. Such a domain `E` has `α`-boundary a combination of whole horizontal circles, so
its multiplicity jumps by the same amount across each horizontal circle in every column, and
`E(c, r) = a(r) + b(c)` is a sum of horizontal and vertical annuli
(`TauCeti.GridDiagram.exists_eq_add_of_isDomainBetween_self`). Each annulus contains exactly one
`O`-marking and one `X`-marking, and at the generator of a grid state its point measure is `1`,
half at each of the two boundary circles. So `n_O(E) = n_X(E) = ∑ a + ∑ b` and
`μ(E) = 2 n_x(E) = 2 (∑ a + ∑ b)`: every domain from a generator to itself has vanishing gradings
(`TauCeti.GridDiagram.maslovIndex_eq_two_mul_sum_basepoint_inl_of_isDomainBetween_self`,
`TauCeti.GridDiagram.sum_basepoint_inr_eq_sum_basepoint_inl_of_isDomainBetween_self`). Since any
two grid states are joined by a sequence of rectangles (`TauCeti.GridState.rectangle_induction_on`),
a domain from `x` to `y` differs from a sum of rectangle domains by a domain from `x` to itself,
and the rectangle formulas extend to all domains.

In the language of `TauCeti.LowDimTopology.Heegaard.Grading` and
`TauCeti.LowDimTopology.Heegaard.AlexanderGrading`:

* every two generators are joined by a domain (`TauCeti.GridDiagram.exists_isDomainBetween`);
* `M_O` is a Maslov grading of the diagram pointed at the `O`-markings, and `M_X` one of the
  diagram pointed at the `X`-markings (`TauCeti.GridDiagram.isMaslovGrading_maslovO`,
  `TauCeti.GridDiagram.isMaslovGrading_maslovX`), so the hat, minus, infinity and plus
  differentials of these diagrams lower them by one, and every Maslov grading of these diagrams is
  `M_O`, respectively `M_X`, up to a constant
  (`TauCeti.GridDiagram.isMaslovGrading_withBasepoints_inl_iff`,
  `TauCeti.GridDiagram.isMaslovGrading_withBasepoints_inr_iff`);
* for a diagram with an odd number of link components, in particular a knot, the integer
  Alexander grading is an Alexander function for the `O`-markings
  (`TauCeti.OddComponentGridDiagram.isAlexanderFunction_alexanderℤ`), so it filters the hat
  complex of the diagram pointed at the `O`-markings
  (`TauCeti.HeegaardRegionSystem.IsAlexanderFunction`).

## Main results

* `TauCeti.GridDiagram.exists_eq_add_of_isDomainBetween_self`: a domain from a generator to
  itself is a sum of horizontal and vertical annuli.
* `TauCeti.GridDiagram.maslovIndex_sub_two_mul_sum_basepoint_inl_of_isDomainBetween`,
  `TauCeti.GridDiagram.maslovIndex_sub_two_mul_sum_basepoint_inr_of_isDomainBetween`,
  `TauCeti.GridDiagram.sum_basepoint_inr_sub_sum_basepoint_inl_of_isDomainBetween`: the grid
  gradings are the Heegaard Floer gradings of every domain.
* `TauCeti.GridDiagram.isMaslovGrading_maslovO`, `TauCeti.GridDiagram.isMaslovGrading_maslovX`,
  `TauCeti.OddComponentGridDiagram.isAlexanderFunction_alexanderℤ`: the grid gradings are Maslov
  gradings and an Alexander function of the multi-pointed Heegaard diagram.
* `TauCeti.GridDiagram.isMaslovGrading_withBasepoints_inl_iff`,
  `TauCeti.GridDiagram.isMaslovGrading_withBasepoints_inr_iff`: they are the only Maslov
  gradings of these diagrams, up to a constant.

## References

* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), §2,
  where the Maslov and Alexander gradings of a grid state are shown to satisfy these formulas for
  every domain.
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Grid Homology for Knots and Links*, Mathematical
  Surveys and Monographs **208**, AMS, 2015, Chapter 4, for the grid gradings.
-/

public section

namespace TauCeti

open Finset HeegaardRegionSystem

variable {n : ℕ}

namespace GridDiagram

variable [NeZero n] (G : GridDiagram n)

section SelfDomains

/-- **Domains from a generator to itself are sums of annuli.** A domain `E` from a generator of
the Heegaard diagram of a grid diagram to itself is `E(c, r) = a(r) + b(c)`: a combination of the
horizontal annuli (the rows of squares) and the vertical annuli (the columns of squares). -/
theorem exists_eq_add_of_isDomainBetween_self {g : G.heegaardRegionSystem.Generator}
    {E : Fin n × Fin n → ℤ} (hE : G.heegaardRegionSystem.IsDomainBetween g g E) :
    ∃ a b : Fin n → ℤ, ∀ c r, E (c, r) = a r + b c := by
  -- The `α`-boundary of `E` is a cycle, hence constant along each horizontal circle: the jump
  -- of `E` across the horizontal circle `r` is the same `a r` in every column.
  obtain ⟨a, ha⟩ := (G.heegaardRegionSystem.alphaArcBoundary_eq_zero_iff _).mp
    (by rw [(isDomainBetween_iff.mp hE).1, sub_self])
  -- So `E(c, r) - E(0, r)` does not change from one row to the next.
  obtain ⟨b, hb⟩ := (G.heegaardRegionSystem.betaNext.forall_comp_symm_sub_eq_zero_iff
    G.heegaardRegionSystem.betaNext_isCycleOn fun p => E p - E (0, p.2)).mp fun p => by
      have h₁ := ha p
      have h₂ := ha (0, p.2)
      simp only [alphaBoundary_apply, heegaardRegionSystem_alphaLeft,
        heegaardRegionSystem_alphaRight, heegaardRegionSystem_alpha] at h₁ h₂
      simp only [heegaardRegionSystem_betaNext_symm_apply]
      linarith
  refine ⟨fun r => E (0, r), b, fun c r => ?_⟩
  have := hb (c, r)
  simp only [heegaardRegionSystem_beta] at this
  linarith

variable {G}

omit [NeZero n] in
/-- A sum of horizontal and vertical annuli has total multiplicity `∑ a + ∑ b` on the squares of
a grid state, one in each row and each column; for instance on the `O`- or the `X`-markings. -/
private theorem sum_apply_of_eq_add {E : Fin n × Fin n → ℤ} {a b : Fin n → ℤ}
    (h : ∀ c r, E (c, r) = a r + b c) (s : GridState n) :
    ∑ c, E (c, s c) = ∑ r, a r + ∑ c, b c := by
  simp only [h, sum_add_distrib]
  rw [Equiv.sum_comp s.toPerm a]

/-- The point measure of a sum of horizontal and vertical annuli at the generator of a grid
state: each annulus has point measure `1`, half at each of its two boundary circles. -/
private theorem generatorPointMeasure_of_eq_add {E : Fin n × Fin n → ℤ} {a b : Fin n → ℤ}
    (h : ∀ c r, E (c, r) = a r + b c) (x : GridState n) :
    G.heegaardRegionSystem.generatorPointMeasure (G.gridStateEquivGenerator x) E =
      ∑ r, (a r : ℚ) + ∑ c, (b c : ℚ) := by
  rw [generatorPointMeasure_gridStateEquivGenerator]
  simp only [pointMeasure_apply, heegaardRegionSystem_alphaNext_symm_apply,
    heegaardRegionSystem_alphaLeft, heegaardRegionSystem_alphaRight, h]
  push_cast
  have ha₁ : ∑ c, (a (x c) : ℚ) = ∑ r, (a r : ℚ) := Equiv.sum_comp x.toPerm fun r => (a r : ℚ)
  have ha₂ : ∑ c, (a ((finRotate n).symm (x c)) : ℚ) = ∑ r, (a r : ℚ) :=
    Equiv.sum_comp (x.toPerm.trans (finRotate n).symm) fun r => (a r : ℚ)
  have hb : ∑ c, (b ((finRotate n).symm c) : ℚ) = ∑ c, (b c : ℚ) :=
    Equiv.sum_comp (finRotate n).symm fun c => (b c : ℚ)
  simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib, ha₁, ha₂, hb]
  ring

variable (G)

/-- **Domains from a generator to itself have vanishing Maslov grading.** A domain `E` from a
generator of the Heegaard diagram of a grid diagram to itself has Maslov index `2 n_O(E)`. -/
theorem maslovIndex_eq_two_mul_sum_basepoint_inl_of_isDomainBetween_self
    {g : G.heegaardRegionSystem.Generator} {E : Fin n × Fin n → ℤ}
    (hE : G.heegaardRegionSystem.IsDomainBetween g g E) :
    G.heegaardRegionSystem.maslovIndex 1 g g E =
      2 * ∑ c, (E (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ) := by
  obtain ⟨a, b, h⟩ := G.exists_eq_add_of_isDomainBetween_self hE
  obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective g
  have hO : ∑ c, (E (c, G.O c) : ℚ) = ∑ r, (a r : ℚ) + ∑ c, (b c : ℚ) := by
    exact_mod_cast sum_apply_of_eq_add h G.O
  rw [maslovIndex_apply, heegaardRegionSystem_eulerMeasure_const_one_eq_zero,
    AddMonoidHom.zero_apply, generatorPointMeasure_of_eq_add h]
  simp only [heegaardRegionSystem_basepoint_inl, hO]
  ring

/-- **Domains from a generator to itself have vanishing Alexander grading.** A domain `E` from a
generator of the Heegaard diagram of a grid diagram to itself has the same total multiplicity at
the `X`-markings as at the `O`-markings. -/
theorem sum_basepoint_inr_eq_sum_basepoint_inl_of_isDomainBetween_self
    {g : G.heegaardRegionSystem.Generator} {E : Fin n × Fin n → ℤ}
    (hE : G.heegaardRegionSystem.IsDomainBetween g g E) :
    ∑ c, E (G.heegaardRegionSystem.basepoint (Sum.inr c)) =
      ∑ c, E (G.heegaardRegionSystem.basepoint (Sum.inl c)) := by
  obtain ⟨a, b, h⟩ := G.exists_eq_add_of_isDomainBetween_self hE
  simp only [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr,
    sum_apply_of_eq_add h]

end SelfDomains

section AllDomains

variable {G}

/-- A quantity attached to domains which is additive under juxtaposition, vanishes on the domains
from a generator to itself and is the change of a function `f` of grid states across every
rectangle is the change of `f` across every domain. -/
private theorem eq_sub_of_isDomainBetween
    (φ : G.heegaardRegionSystem.Generator → G.heegaardRegionSystem.Generator →
      (Fin n × Fin n → ℤ) → ℚ) (f : GridState n → ℚ)
    (hadd : ∀ {g h k : G.heegaardRegionSystem.Generator} {D E : Fin n × Fin n → ℤ},
      G.heegaardRegionSystem.IsDomainBetween g h D →
        G.heegaardRegionSystem.IsDomainBetween h k E → φ g k (D + E) = φ g h D + φ h k E)
    (hself : ∀ {g : G.heegaardRegionSystem.Generator} {E : Fin n × Fin n → ℤ},
      G.heegaardRegionSystem.IsDomainBetween g g E → φ g g E = 0)
    (hrect : ∀ {x y : GridState n} (R : GridRectangleBetween x y),
      φ (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) R.toGridRectangle.domain =
        f x - f y)
    {x y : GridState n} {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    φ (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) D = f x - f y := by
  -- Fix the target `y` and move the source `x` by rectangles, starting from `x = y`.
  refine GridState.rectangle_induction_on (P := fun x => ∀ D,
      G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) D →
      φ (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) D = f x - f y)
    y (fun D hD => by rw [hself hD, sub_self]) (fun x' y' R hx' D hD => ?_) x D hD
  -- Precomposing a domain from `y'` with the rectangle from `x'` to `y'` gives one from `x'`.
  have hRD := hx' _ ((G.isDomainBetween_domain R).add hD)
  rw [hadd (G.isDomainBetween_domain R) hD, hrect R] at hRD
  linarith

/-- **The `O`-Maslov grading of every domain.** For every domain `D` from the generator of a grid
state `x` to the generator of a grid state `y`, the Heegaard Floer grading `μ(D) - 2 n_O(D)` is
the difference `M_O(x) - M_O(y)` of the `O`-Maslov gradings of grid homology. -/
theorem maslovIndex_sub_two_mul_sum_basepoint_inl_of_isDomainBetween {x y : GridState n}
    {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y) D -
        2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ) =
      G.maslovO x - G.maslovO y := by
  refine eq_sub_of_isDomainBetween (fun g h D => G.heegaardRegionSystem.maslovIndex 1 g h D -
      2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ)) G.maslovO
    (fun hD hE => ?_) (fun hE => ?_) (fun R => G.maslovIndex_domain_sub_two_mul_sum_basepoint_inl R)
    hD
  · simp only [hD.maslovIndex_add 1 hE, Pi.add_apply, Int.cast_add, sum_add_distrib]
    ring
  · rw [G.maslovIndex_eq_two_mul_sum_basepoint_inl_of_isDomainBetween_self hE, sub_self]

/-- **The `X`-Maslov grading of every domain.** For every domain `D` from the generator of a grid
state `x` to the generator of a grid state `y`, the Heegaard Floer grading `μ(D) - 2 n_X(D)` is
the difference `M_X(x) - M_X(y)` of the `X`-Maslov gradings of grid homology. -/
theorem maslovIndex_sub_two_mul_sum_basepoint_inr_of_isDomainBetween {x y : GridState n}
    {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y) D -
        2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inr c)) : ℚ) =
      G.maslovX x - G.maslovX y := by
  refine eq_sub_of_isDomainBetween (fun g h D => G.heegaardRegionSystem.maslovIndex 1 g h D -
      2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inr c)) : ℚ)) G.maslovX
    (fun hD hE => ?_) (fun hE => ?_) (fun R => G.maslovIndex_domain_sub_two_mul_sum_basepoint_inr R)
    hD
  · simp only [hD.maslovIndex_add 1 hE, Pi.add_apply, Int.cast_add, sum_add_distrib]
    ring
  · rw [G.maslovIndex_eq_two_mul_sum_basepoint_inl_of_isDomainBetween_self hE, ← Int.cast_sum,
      ← Int.cast_sum, G.sum_basepoint_inr_eq_sum_basepoint_inl_of_isDomainBetween_self hE,
      sub_self]

/-- **The Alexander grading of every domain.** For every domain `D` from the generator of a grid
state `x` to the generator of a grid state `y`, the Heegaard Floer Alexander grading
`n_X(D) - n_O(D)` is the difference `A(x) - A(y)` of the Alexander gradings of grid homology. -/
theorem sum_basepoint_inr_sub_sum_basepoint_inl_of_isDomainBetween {x y : GridState n}
    {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    ((∑ c, D (G.heegaardRegionSystem.basepoint (Sum.inr c)) -
        ∑ c, D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℤ) : ℚ) =
      G.alexander x - G.alexander y := by
  refine eq_sub_of_isDomainBetween (fun _ _ D =>
      ((∑ c, D (G.heegaardRegionSystem.basepoint (Sum.inr c)) -
        ∑ c, D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℤ) : ℚ)) G.alexander
    (fun _ _ => ?_) (fun hE => ?_)
    (fun R => G.sum_domain_basepoint_inr_sub_sum_domain_basepoint_inl R) hD
  · simp only [Pi.add_apply, sum_add_distrib]
    push_cast
    ring
  · rw [G.sum_basepoint_inr_eq_sum_basepoint_inl_of_isDomainBetween_self hE, sub_self,
      Int.cast_zero]

variable (G)

/-- **Every two generators are joined by a domain.** In the Heegaard diagram of a grid diagram,
any two generators are joined by a sum of rectangle domains. -/
theorem exists_isDomainBetween (g h : G.heegaardRegionSystem.Generator) :
    ∃ D, G.heegaardRegionSystem.IsDomainBetween g h D := by
  obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective h
  obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective g
  obtain ⟨D, hD⟩ := GridState.rectangle_induction_on
    (P := fun x => ∃ D, G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator y)
      (G.gridStateEquivGenerator x) D)
    y ⟨0, isDomainBetween_zero _⟩ (fun x' y' R ⟨D, hD⟩ => ⟨_, hD.add (G.isDomainBetween_domain R)⟩)
    x
  exact ⟨-D, hD.neg⟩

/-- **`M_O` is a Maslov grading.** The `O`-Maslov grading of grid homology is a Maslov grading of
the Heegaard diagram of a grid diagram pointed at its `O`-markings. -/
theorem isMaslovGrading_maslovO :
    (G.heegaardRegionSystem.withBasepoints fun c =>
        G.heegaardRegionSystem.basepoint (Sum.inl c)).IsMaslovGrading 1
      fun g => G.maslovO (G.gridStateEquivGenerator.symm g) where
  sub_eq {g h D} hD := by
    obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective g
    obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective h
    rw [isDomainBetween_withBasepoints] at hD
    simp only [Equiv.symm_apply_apply, maslovIndex_withBasepoints]
    exact (G.maslovIndex_sub_two_mul_sum_basepoint_inl_of_isDomainBetween hD).symm

/-- **`M_X` is a Maslov grading.** The `X`-Maslov grading of grid homology is a Maslov grading of
the Heegaard diagram of a grid diagram pointed at its `X`-markings. -/
theorem isMaslovGrading_maslovX :
    (G.heegaardRegionSystem.withBasepoints fun c =>
        G.heegaardRegionSystem.basepoint (Sum.inr c)).IsMaslovGrading 1
      fun g => G.maslovX (G.gridStateEquivGenerator.symm g) where
  sub_eq {g h D} hD := by
    obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective g
    obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective h
    rw [isDomainBetween_withBasepoints] at hD
    simp only [Equiv.symm_apply_apply, maslovIndex_withBasepoints]
    exact (G.maslovIndex_sub_two_mul_sum_basepoint_inr_of_isDomainBetween hD).symm

/-- **The Maslov gradings pointed at the `O`-markings are the shifts of `M_O`.** The Maslov
gradings of the Heegaard diagram of a grid diagram pointed at its `O`-markings are exactly the
shifts of the `O`-Maslov grading of grid homology. -/
theorem isMaslovGrading_withBasepoints_inl_iff {gr : G.heegaardRegionSystem.Generator → ℚ} :
    (G.heegaardRegionSystem.withBasepoints fun c =>
        G.heegaardRegionSystem.basepoint (Sum.inl c)).IsMaslovGrading 1 gr ↔
      ∃ q : ℚ, gr = fun g => G.maslovO (G.gridStateEquivGenerator.symm g) + q :=
  ⟨fun h => G.isMaslovGrading_maslovO.exists_eq_add h fun x y =>
      let ⟨D, hD⟩ := G.exists_isDomainBetween x y
      ⟨D, (isDomainBetween_withBasepoints _).1 hD⟩,
    fun ⟨q, hq⟩ => hq ▸ G.isMaslovGrading_maslovO.add_const q⟩

/-- **The Maslov gradings pointed at the `X`-markings are the shifts of `M_X`.** The Maslov
gradings of the Heegaard diagram of a grid diagram pointed at its `X`-markings are exactly the
shifts of the `X`-Maslov grading of grid homology. -/
theorem isMaslovGrading_withBasepoints_inr_iff {gr : G.heegaardRegionSystem.Generator → ℚ} :
    (G.heegaardRegionSystem.withBasepoints fun c =>
        G.heegaardRegionSystem.basepoint (Sum.inr c)).IsMaslovGrading 1 gr ↔
      ∃ q : ℚ, gr = fun g => G.maslovX (G.gridStateEquivGenerator.symm g) + q :=
  ⟨fun h => G.isMaslovGrading_maslovX.exists_eq_add h fun x y =>
      let ⟨D, hD⟩ := G.exists_isDomainBetween x y
      ⟨D, (isDomainBetween_withBasepoints _).1 hD⟩,
    fun ⟨q, hq⟩ => hq ▸ G.isMaslovGrading_maslovX.add_const q⟩

end AllDomains

end GridDiagram

namespace OddComponentGridDiagram

variable [NeZero n] (G : OddComponentGridDiagram n)

/-- **The Alexander grading is an Alexander function.** For a grid diagram with an odd number of
link components, in particular a knot, the integer Alexander grading is an Alexander function of
its Heegaard diagram for the `O`-markings: every domain `D` from `x` to `y` with `n_O(D) = 0` has
`A(x) - A(y) = n_X(D)`. -/
theorem isAlexanderFunction_alexanderℤ :
    G.val.heegaardRegionSystem.IsAlexanderFunction Sum.inl
      fun g => G.alexanderℤ (G.val.gridStateEquivGenerator.symm g) := by
  rw [isAlexanderFunction_iff]
  intro g h D hD hO
  obtain ⟨x, rfl⟩ := G.val.gridStateEquivGenerator.surjective g
  obtain ⟨y, rfl⟩ := G.val.gridStateEquivGenerator.surjective h
  have hA := G.val.sum_basepoint_inr_sub_sum_basepoint_inl_of_isDomainBetween hD
  rw [alexander_eq_intCast, alexander_eq_intCast, ← Int.cast_sub, Int.cast_inj] at hA
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, hO, sum_const_zero, zero_add, ← hA,
    sub_zero]

end OddComponentGridDiagram

end TauCeti
