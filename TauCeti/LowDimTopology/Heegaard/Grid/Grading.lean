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
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The grid gradings are the Heegaard Floer gradings of the grid diagram

Let `G` be an `n × n` grid diagram, viewed as a multi-pointed genus-one Heegaard diagram
(`TauCeti.GridDiagram.heegaardRegionSystem`) whose basepoints are the `O`-markings, the `w`'s, and
the `X`-markings, the `z`'s, with every square a region of Euler characteristic `1`. Grid
homology grades a grid state `x` by the combinatorial gradings `M_O(x)`, `M_X(x)` and
`A(x) = (M_O(x) - M_X(x)) / 2 - (n - 1) / 2` of `TauCeti.KnotTheory.Grid.Gradings`. Heegaard
Floer homology grades a generator by its differences along domains: for every domain `D` from `x`
to `y`,

`M_O(x) - M_O(y) = μ(D) - 2 n_O(D)`, `M_X(x) - M_X(y) = μ(D) - 2 n_X(D)`,
`A(x) - A(y) = n_X(D) - n_O(D)`.

The domains of rectangles satisfy these identities
(`TauCeti.GridDiagram.maslovIndex_domain_sub_two_mul_sum_basepoint_inl`,
`TauCeti.GridDiagram.maslovIndex_domain_sub_two_mul_sum_basepoint_inr`,
`TauCeti.GridDiagram.sum_domain_basepoint_inr_sub_sum_domain_basepoint_inl`). This file proves
them for **every** domain, so that the grid gradings are Heegaard Floer gradings of the
multi-pointed diagram.

The argument has two parts.

* **Periodic domains.** The `α`-boundary of a domain `E` from a generator `x` to itself is a
  combination of whole horizontal circles, so `E` jumps by the same amount across a horizontal
  circle in every column, and it is a sum
  `E(c, r) = f(c) + g(r)` of a function of the column and a function of the row. The sum of `E`
  over the squares of a permutation, such as the `O`- or the `X`-markings, is then
  `∑ f + ∑ g` whatever the permutation, so `n_O(E) = n_X(E)`. Every region is a square, so the
  Euler measure vanishes and `μ(E) = 2 n_x(E)`, where the point measure at `(c, r)` averages
  `f` over the columns `c - 1`, `c` and `g` over the rows `r - 1`, `r`; summed over the points
  of `x` it is again `∑ f + ∑ g`. Hence `μ(E) = 2 n_O(E) = 2 n_X(E)`.
* **Rectangles connect.** Any two grid states are joined by a sequence of rectangle moves
  (`TauCeti.GridState.rectangle_induction_on`), so any domain from `x` to `y` is the sum of the
  domains of these rectangles and of a domain from `x` to itself. Both sides of each identity
  are additive along such sums, and they agree on rectangles and on periodic domains.

In particular every two generators are joined by a domain
(`TauCeti.GridDiagram.exists_isDomainBetween`). So `M_O` is a Maslov grading
(`TauCeti.HeegaardRegionSystem.IsMaslovGrading`) of the diagram pointed at the `O`-markings alone,
and every Maslov grading of that diagram is `M_O` up to a constant; likewise for `M_X` and the
`X`-markings. For a diagram with an odd number of components, such as a knot, the integer
Alexander grading is an Alexander function (`TauCeti.HeegaardRegionSystem.IsAlexanderFunction`)
for the `O`-markings. The general theory of these gradings then applies to grids: the hat and
minus differentials of the diagram pointed at the `O`-markings lower `M_O` by one
(`TauCeti.LowDimTopology.Heegaard.Grading`), and, for an odd number of components, its hat
differential is filtered by `A`, with associated graded differential the hat differential of the
full diagram (`TauCeti.LowDimTopology.Heegaard.AlexanderGrading`), which counts the fully blocked
empty rectangles (`TauCeti.GridDiagram.hatDifferential_comp_domLCongr`).

## Main results

* `TauCeti.GridDiagram.exists_isDomainBetween`: every two generators are joined by a domain.
* `TauCeti.GridDiagram.maslovIndex_sub_two_mul_sum_basepoint_inl`,
  `TauCeti.GridDiagram.maslovIndex_sub_two_mul_sum_basepoint_inr` and
  `TauCeti.GridDiagram.sum_basepoint_inr_sub_sum_basepoint_inl`: the three identities, for every
  domain.
* `TauCeti.GridDiagram.isMaslovGrading_maslovO` and `TauCeti.GridDiagram.isMaslovGrading_maslovX`:
  `M_O` and `M_X` are Maslov gradings of the diagrams pointed at the `O`- and at the
  `X`-markings.
* `TauCeti.GridDiagram.isMaslovGrading_withBasepoints_inl_iff` and
  `TauCeti.GridDiagram.isMaslovGrading_withBasepoints_inr_iff`: they are the only ones, up to a
  constant.
* `TauCeti.OddComponentGridDiagram.isAlexanderFunction_alexanderℤ`: the integer Alexander grading
  is an Alexander function for the `O`-markings.

## References

* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), §2,
  where the Maslov and Alexander gradings of a grid diagram are identified with those of knot
  Floer homology of the multi-pointed Heegaard diagram.
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Grid Homology for Knots and Links*, Mathematical
  Surveys and Monographs **208**, AMS, 2015, Chapter 4, for the grid gradings.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, for the index formula.
-/

public section

namespace TauCeti

open Finset

variable {n : ℕ}

namespace GridDiagram

variable [NeZero n] (G : GridDiagram n)

section Periodic

variable {G} {x : GridState n} {E : Fin n × Fin n → ℤ}

/-- A domain from a generator to itself jumps by the same amount across a horizontal circle in
every column, so it is the sum of a function of the column and a function of the row. -/
private theorem exists_eq_add_of_isDomainBetween_self
    (hE : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator x) E) :
    ∃ f g : Fin n → ℤ, ∀ c r, E (c, r) = f c + g r := by
  have hα : G.heegaardRegionSystem.alphaArcBoundary
      (G.heegaardRegionSystem.alphaBoundary E) = 0 := by
    rw [(HeegaardRegionSystem.isDomainBetween_iff.1 hE).1, sub_self]
  -- The jump `E (c, r) - E (c, r - 1)` across the horizontal circle `r` does not depend on `c`.
  obtain ⟨a, ha⟩ := (G.heegaardRegionSystem.alphaArcBoundary_eq_zero_iff _).1 hα
  have ha' : ∀ c r, E (c, r) - E (c, (finRotate n).symm r) = a r := fun c r => by
    simpa using ha (c, r)
  -- So `E (c, r) - E (0, r)` is constant along each vertical circle.
  obtain ⟨f, hf⟩ := (G.heegaardRegionSystem.betaArcBoundary_eq_zero_iff
    fun q => E q - E (0, q.2)).1 <| funext fun q => by
      have h₁ := ha' q.1 q.2
      have h₂ := ha' 0 q.2
      simp only [HeegaardRegionSystem.betaArcBoundary_apply,
        heegaardRegionSystem_betaNext_symm_apply, Pi.zero_apply]
      linarith
  refine ⟨f, fun r => E (0, r), fun c r => ?_⟩
  have := hf (c, r)
  simp only [heegaardRegionSystem_beta] at this
  linarith

omit [NeZero n] in
/-- The sum of a sum of a column function and a row function over the squares of a permutation
does not depend on the permutation. -/
private theorem sum_apply_eq_of_eq_add {f g : Fin n → ℤ} (hE : ∀ c r, E (c, r) = f c + g r)
    (y : GridState n) : ∑ c, E (c, y c) = ∑ c, f c + ∑ r, g r := by
  simp only [hE, sum_add_distrib]
  rw [Equiv.sum_comp y.toPerm g]

/-- A domain from a generator to itself has the same multiplicity at the `O`- and at the
`X`-markings, and its Maslov index is twice that multiplicity. -/
private theorem maslovIndex_self_eq_two_mul_sum_and_sum_eq
    (hE : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator x) E) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator x) E =
      2 * ∑ c, (E (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ) ∧
    ∑ c, E (G.heegaardRegionSystem.basepoint (Sum.inr c)) =
      ∑ c, E (G.heegaardRegionSystem.basepoint (Sum.inl c)) := by
  obtain ⟨f, g, hfg⟩ := exists_eq_add_of_isDomainBetween_self hE
  simp only [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr]
  refine ⟨?_, by rw [sum_apply_eq_of_eq_add hfg, sum_apply_eq_of_eq_add hfg]⟩
  rw [← Int.cast_sum, sum_apply_eq_of_eq_add hfg, HeegaardRegionSystem.maslovIndex_apply,
    heegaardRegionSystem_eulerMeasure_const_one_eq_zero, AddMonoidHom.zero_apply,
    generatorPointMeasure_gridStateEquivGenerator]
  -- The point measure at `(c, r)` averages `f` over the columns `c - 1`, `c` and `g` over the
  -- rows `r - 1`, `r`; each of these four sums over the points of `x` is `∑ f` or `∑ g`.
  have hf := Equiv.sum_comp (finRotate n).symm fun c => (f c : ℚ)
  have hg := Equiv.sum_comp x.toPerm fun r => (g r : ℚ)
  have hg' := Equiv.sum_comp (x.toPerm.trans (finRotate n).symm) fun r => (g r : ℚ)
  simp only [Equiv.trans_apply] at hg'
  simp only [HeegaardRegionSystem.pointMeasure_apply, heegaardRegionSystem_alphaNext_symm_apply,
    heegaardRegionSystem_alphaLeft, heegaardRegionSystem_alphaRight, hfg, Int.cast_add,
    div_eq_mul_inv, add_mul, sum_add_distrib, ← sum_mul]
  push_cast
  rw [hf, hg, hg']
  ring

end Periodic

/-- **Every two generators of a grid diagram are joined by a domain**: the sum of the domains
of a sequence of rectangle moves from one grid state to the other. -/
theorem exists_isDomainBetween (x y : G.heegaardRegionSystem.Generator) :
    ∃ D, G.heegaardRegionSystem.IsDomainBetween x y D := by
  obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective x
  obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective y
  refine GridState.rectangle_induction_on (P := fun y => ∃ D,
    G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) x ⟨0, HeegaardRegionSystem.isDomainBetween_zero _⟩
    (fun _ _ R ⟨D, hD⟩ => ⟨D + R.toGridRectangle.domain, hD.add (G.isDomainBetween_domain R)⟩) y

/-- A function `f` of the grid states whose differences are given by a quantity `v` that is
additive along concatenated domains is determined by `v` on every domain, once its differences
are given by `v` on the domains of rectangles and `v` vanishes on the domains from a generator to
itself. -/
private theorem sub_eq_of_forall_rectangle
    (f : GridState n → ℚ)
    (v : G.heegaardRegionSystem.Generator → G.heegaardRegionSystem.Generator →
      (Fin n × Fin n → ℤ) → ℚ)
    (hadd : ∀ {x y z : G.heegaardRegionSystem.Generator} {D E : Fin n × Fin n → ℤ},
      G.heegaardRegionSystem.IsDomainBetween x y D →
        G.heegaardRegionSystem.IsDomainBetween y z E → v x z (D + E) = v x y D + v y z E)
    (hrect : ∀ {x y : GridState n} (R : GridRectangleBetween x y),
      f x - f y = v (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y)
        R.toGridRectangle.domain)
    (hself : ∀ {x : GridState n} {E : Fin n × Fin n → ℤ},
      G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator x) E →
      v (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator x) E = 0)
    {x y : GridState n} {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    f x - f y = v (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) D := by
  -- Move the source state `x` from `y` along rectangles, absorbing each rectangle into `D`.
  revert D
  refine GridState.rectangle_induction_on (P := fun x => ∀ {D : Fin n × Fin n → ℤ},
    G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D →
    f x - f y = v (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) D) y
    (fun hD => by rw [sub_self, hself hD]) (fun x x' R ih D hD => ?_) x
  have hR := G.isDomainBetween_domain R
  have h := ih (hR.add hD)
  rw [hadd hR hD, ← hrect R] at h
  linarith

/-- **The `O`-Maslov grading along every domain.** For every domain `D` from `x` to `y`, the
Heegaard Floer grading `μ(D) - 2 n_O(D)` is the difference `M_O(x) - M_O(y)` of the `O`-Maslov
gradings of grid homology. -/
theorem maslovIndex_sub_two_mul_sum_basepoint_inl {x y : GridState n} {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y) D -
        2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ) =
      G.maslovO x - G.maslovO y := by
  refine (G.sub_eq_of_forall_rectangle G.maslovO
    (fun x y D => G.heegaardRegionSystem.maslovIndex 1 x y D -
      2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℚ))
    (fun hD hE => ?_) (fun R => (G.maslovIndex_domain_sub_two_mul_sum_basepoint_inl R).symm)
    (fun hE => ?_) hD).symm
  · simp only [hD.maslovIndex_add 1 hE, Pi.add_apply, Int.cast_add, sum_add_distrib]
    ring
  · rw [(maslovIndex_self_eq_two_mul_sum_and_sum_eq hE).1, sub_self]

/-- **The `X`-Maslov grading along every domain.** For every domain `D` from `x` to `y`, the
Heegaard Floer grading `μ(D) - 2 n_X(D)` is the difference `M_X(x) - M_X(y)` of the `X`-Maslov
gradings of grid homology. -/
theorem maslovIndex_sub_two_mul_sum_basepoint_inr {x y : GridState n} {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
          (G.gridStateEquivGenerator y) D -
        2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inr c)) : ℚ) =
      G.maslovX x - G.maslovX y := by
  refine (G.sub_eq_of_forall_rectangle G.maslovX
    (fun x y D => G.heegaardRegionSystem.maslovIndex 1 x y D -
      2 * ∑ c, (D (G.heegaardRegionSystem.basepoint (Sum.inr c)) : ℚ))
    (fun hD hE => ?_) (fun R => (G.maslovIndex_domain_sub_two_mul_sum_basepoint_inr R).symm)
    (fun hE => ?_) hD).symm
  · simp only [hD.maslovIndex_add 1 hE, Pi.add_apply, Int.cast_add, sum_add_distrib]
    ring
  · obtain ⟨hμ, hXO⟩ := maslovIndex_self_eq_two_mul_sum_and_sum_eq hE
    rw [hμ, ← Int.cast_sum, ← Int.cast_sum, hXO, sub_self]

/-- **The Alexander grading along every domain.** For every domain `D` from `x` to `y`, the
Heegaard Floer Alexander grading `n_X(D) - n_O(D)` is the difference `A(x) - A(y)` of the
Alexander gradings of grid homology. -/
theorem sum_basepoint_inr_sub_sum_basepoint_inl {x y : GridState n} {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) :
    ((∑ c, D (G.heegaardRegionSystem.basepoint (Sum.inr c)) -
        ∑ c, D (G.heegaardRegionSystem.basepoint (Sum.inl c)) : ℤ) : ℚ) =
      G.alexander x - G.alexander y := by
  have hO := G.maslovIndex_sub_two_mul_sum_basepoint_inl hD
  have hX := G.maslovIndex_sub_two_mul_sum_basepoint_inr hD
  simp only [alexander_def, Int.cast_sub, Int.cast_sum] at hO hX ⊢
  linarith

/-- **The `O`-Maslov grading is a Maslov grading of the diagram pointed at the `O`-markings.** -/
theorem isMaslovGrading_maslovO :
    (G.heegaardRegionSystem.withBasepoints
      (G.heegaardRegionSystem.basepoint ∘ Sum.inl)).IsMaslovGrading 1
      fun g => G.maslovO (G.gridStateEquivGenerator.symm g) where
  sub_eq {x y D} hD := by
    obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective x
    obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective y
    simpa using (G.maslovIndex_sub_two_mul_sum_basepoint_inl
      ((HeegaardRegionSystem.isDomainBetween_withBasepoints _).1 hD)).symm

/-- **The `X`-Maslov grading is a Maslov grading of the diagram pointed at the `X`-markings.** -/
theorem isMaslovGrading_maslovX :
    (G.heegaardRegionSystem.withBasepoints
      (G.heegaardRegionSystem.basepoint ∘ Sum.inr)).IsMaslovGrading 1
      fun g => G.maslovX (G.gridStateEquivGenerator.symm g) where
  sub_eq {x y D} hD := by
    obtain ⟨x, rfl⟩ := G.gridStateEquivGenerator.surjective x
    obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective y
    simpa using (G.maslovIndex_sub_two_mul_sum_basepoint_inr
      ((HeegaardRegionSystem.isDomainBetween_withBasepoints _).1 hD)).symm

/-- The Maslov gradings of the diagram pointed at the `O`-markings are exactly the shifts of the
`O`-Maslov grading of grid homology. -/
theorem isMaslovGrading_withBasepoints_inl_iff {gr : G.heegaardRegionSystem.Generator → ℚ} :
    (G.heegaardRegionSystem.withBasepoints
        (G.heegaardRegionSystem.basepoint ∘ Sum.inl)).IsMaslovGrading 1 gr ↔
      ∃ q : ℚ, gr = fun g => G.maslovO (G.gridStateEquivGenerator.symm g) + q :=
  ⟨fun h => G.isMaslovGrading_maslovO.exists_eq_add h fun x y =>
      let ⟨D, hD⟩ := G.exists_isDomainBetween x y
      ⟨D, (G.heegaardRegionSystem.isDomainBetween_withBasepoints
        (G.heegaardRegionSystem.basepoint ∘ Sum.inl)).2 hD⟩,
    fun ⟨q, hq⟩ => hq ▸ G.isMaslovGrading_maslovO.add_const q⟩

/-- The Maslov gradings of the diagram pointed at the `X`-markings are exactly the shifts of the
`X`-Maslov grading of grid homology. -/
theorem isMaslovGrading_withBasepoints_inr_iff {gr : G.heegaardRegionSystem.Generator → ℚ} :
    (G.heegaardRegionSystem.withBasepoints
        (G.heegaardRegionSystem.basepoint ∘ Sum.inr)).IsMaslovGrading 1 gr ↔
      ∃ q : ℚ, gr = fun g => G.maslovX (G.gridStateEquivGenerator.symm g) + q :=
  ⟨fun h => G.isMaslovGrading_maslovX.exists_eq_add h fun x y =>
      let ⟨D, hD⟩ := G.exists_isDomainBetween x y
      ⟨D, (G.heegaardRegionSystem.isDomainBetween_withBasepoints
        (G.heegaardRegionSystem.basepoint ∘ Sum.inr)).2 hD⟩,
    fun ⟨q, hq⟩ => hq ▸ G.isMaslovGrading_maslovX.add_const q⟩

end GridDiagram

namespace OddComponentGridDiagram

variable [NeZero n] (G : OddComponentGridDiagram n)

/-- **The integer Alexander grading is an Alexander function for the `O`-markings.** For a grid
diagram with an odd number of components, such as a knot, every domain `D` from `x` to `y` with
multiplicity zero at the `O`-markings has `A(x) - A(y) = n_X(D)`. -/
theorem isAlexanderFunction_alexanderℤ :
    G.val.heegaardRegionSystem.IsAlexanderFunction Sum.inl
      fun g => G.alexanderℤ (G.val.gridStateEquivGenerator.symm g) := by
  refine HeegaardRegionSystem.isAlexanderFunction_iff.2 fun x y D hD hO => ?_
  obtain ⟨x, rfl⟩ := G.val.gridStateEquivGenerator.surjective x
  obtain ⟨y, rfl⟩ := G.val.gridStateEquivGenerator.surjective y
  have h := G.val.sum_basepoint_inr_sub_sum_basepoint_inl hD
  simp only [hO, Finset.sum_const_zero, sub_zero, alexander_eq_intCast] at h
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, hO, Finset.sum_const_zero, zero_add]
  exact_mod_cast h.symm

end OddComponentGridDiagram

end TauCeti
