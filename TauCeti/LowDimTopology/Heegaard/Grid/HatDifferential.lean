/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.BlockedRectangle
public import TauCeti.KnotTheory.Grid.Chain.Basic
public import TauCeti.LowDimTopology.Heegaard.Grid.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.Differential.Square.Zero
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The index-one domains of a grid diagram are its empty rectangles

Let `G` be an `n × n` grid diagram, viewed as a multi-pointed genus-one Heegaard diagram
(`TauCeti.GridDiagram.heegaardRegionSystem`), with every square a region of Euler characteristic
`1`. The domain of an empty rectangle from `x` to `y` has Maslov index one
(`TauCeti.GridDiagram.maslovIndex_domain_eq_one_iff`). This file proves the converse, following
Manolescu, Ozsváth and Sarkar: **every nonnegative domain of Maslov index one from `x` to `y` is
the domain of an empty rectangle from `x` to `y`**
(`TauCeti.GridDiagram.exists_gridRectangleBetween_isEmpty_domain_eq`). No condition at the
basepoints is needed.

The argument is a count of corners. Since every region is a square, the Euler measure vanishes
and `μ(D) = n_x(D) + n_y(D)`, a sum of point measures, each a quarter of the sum of the four
multiplicities around a grid point. At a grid point `p` the boundary condition says that the
alternating sum of these four multiplicities is `1` if `p` is a point of `y` only, `-1` if it is
a point of `x` only, and `0` otherwise. For a nonnegative domain the alternating sum is bounded
by the sum, so each of the `2k` points at which `x` and `y` differ contributes at least `1 / 4`.
Two grid states differ in no column or in at least two, so `μ(D) = 1` forces exactly two
columns `c₁` and `c₂`, the point measure `1 / 4` at the four corners `(c₁, x c₁)`, `(c₂, x c₂)`,
`(c₁, y c₁)`, `(c₂, y c₂)`, and the point measure `0` at every common point of `x` and `y`. At
the corner `(c₁, x c₁)` the multiplicity `1` lies either in the square above and to the right,
the first square of the rectangle with left side `c₁`, or in the square below and to the left, a
square of the rectangle with left side `c₂`. Let `R` be that rectangle. The difference `D - R`
is a periodic domain: its multiplicity jumps by a constant across each horizontal and each
vertical circle. The jumps vanish across the circles through the common points of `x` and `y`,
around which `D` vanishes, and across the circles through the corner `(c₁, x c₁)`; the jumps
across the circles of a grid sum to zero, so the remaining jumps vanish too. Hence `D - R` is
constant, and it vanishes at the square above and to the right of `(c₁, x c₁)`. When `x = y`
the domain is periodic and its Maslov index is even, so it is never one.

Distinct rectangles from `x` to `y` have distinct domains
(`TauCeti.GridRectangleBetween.toGridRectangle_domain_injective`). So the domains counted by the
hat differential of the multi-pointed diagram, which also avoid the basepoints, are exactly the
domains of the fully blocked rectangles
(`TauCeti.GridDiagram.hatDomains_eq_image_fullyBlockedRectangles`), the coefficients of the hat
differential are the fully blocked rectangle counts
(`TauCeti.GridDiagram.hatCoefficient_gridStateEquivGenerator`), and the hat differential is the
fully blocked grid differential under the identification of grid states with generators
(`TauCeti.GridDiagram.hatDifferential_comp_domLCongr`). In particular the hat differential of
the Heegaard diagram of a grid diagram squares to zero
(`TauCeti.GridDiagram.hatDifferential_comp_hatDifferential`).

This is the combinatorial half of the identification of the fully blocked grid complex with the
hat complex of the multi-pointed Heegaard diagram: it excludes every domain other than the empty
rectangles. That each empty rectangle carries exactly one holomorphic disk modulo translation is
analytic and is not formalized here.

## Main results

* `TauCeti.GridDiagram.exists_gridRectangleBetween_isEmpty_domain_eq`: a nonnegative domain of
  Maslov index one is the domain of an empty rectangle.
* `TauCeti.GridDiagram.mem_hatDomains_iff_exists_mem_fullyBlockedRectangles` and
  `TauCeti.GridDiagram.hatDomains_eq_image_fullyBlockedRectangles`: the domains counted by the hat
  differential are those of the fully blocked rectangles.
* `TauCeti.GridDiagram.hatCoefficient_gridStateEquivGenerator`: the coefficients of the hat
  differential are the fully blocked rectangle counts.
* `TauCeti.GridDiagram.hatDifferential_comp_domLCongr`: the hat differential is the fully blocked
  grid differential.
* `TauCeti.GridDiagram.hatDifferential_comp_hatDifferential`: it squares to zero.

## References

* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), §2,
  where the positive domains of Maslov index one in a grid diagram are shown to be the empty
  rectangles.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, for the index formula.
-/

public section

namespace TauCeti

open Finset

variable {n : ℕ}

namespace GridDiagram

variable [NeZero n] (G : GridDiagram n)

section IndexOne

variable {x y : GridState n} {D : Fin n × Fin n → ℤ}

/-- The sum of the multiplicities of `D` in the four squares around the grid point `(c, r)`: four
times its point measure there. -/
private def cornerSum (D : Fin n × Fin n → ℤ) (c r : Fin n) : ℤ :=
  D ((finRotate n).symm c, r) + D ((finRotate n).symm c, (finRotate n).symm r) + D (c, r) +
    D (c, (finRotate n).symm r)

private theorem pointMeasure_eq_cornerSum (D : Fin n × Fin n → ℤ) (c r : Fin n) :
    G.heegaardRegionSystem.pointMeasure D (c, r) = (cornerSum D c r : ℚ) / 4 := by
  simp [cornerSum]

/-- The Maslov index of a domain is a quarter of the corner sums at the points of the two states. -/
private theorem maslovIndex_eq_sum_cornerSum (x y : GridState n) (D : Fin n × Fin n → ℤ) :
    G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) D =
      ((∑ c, (cornerSum D c (x c) + cornerSum D c (y c)) : ℤ) : ℚ) / 4 := by
  rw [HeegaardRegionSystem.maslovIndex_apply, heegaardRegionSystem_eulerMeasure_const_one_eq_zero,
    AddMonoidHom.zero_apply, generatorPointMeasure_gridStateEquivGenerator,
    generatorPointMeasure_gridStateEquivGenerator]
  simp only [G.pointMeasure_eq_cornerSum]
  push_cast
  rw [sum_add_distrib, ← sum_div, ← sum_div]
  ring

/-- The corner condition of a domain at a grid point: the alternating sum of the four
multiplicities around it is `1` at a point of `y` only, `-1` at a point of `x` only, and `0`
otherwise. -/
private theorem corner_of_isDomainBetween
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (c r : Fin n) :
    D ((finRotate n).symm c, r) - D ((finRotate n).symm c, (finRotate n).symm r) - D (c, r) +
        D (c, (finRotate n).symm r) =
      (if y c = r then 1 else 0) - if x c = r then 1 else 0 := by
  have h := congrFun (HeegaardRegionSystem.isDomainBetween_iff.1 hD).1 (c, r)
  simp only [HeegaardRegionSystem.alphaArcBoundary_apply, HeegaardRegionSystem.alphaBoundary_apply,
    heegaardRegionSystem_alphaNext_symm_apply, heegaardRegionSystem_alphaLeft,
    heegaardRegionSystem_alphaRight, Pi.sub_apply, generatorChain_gridStateEquivGenerator,
    GridState.mem_pointSet] at h
  linear_combination h

omit [NeZero n] in
/-- A sum of differences along a cyclic shift vanishes. -/
private theorem sum_sub_finRotate_symm (f : Fin n → ℤ) :
    ∑ r, (f r - f ((finRotate n).symm r)) = 0 := by
  rw [sum_sub_distrib, Equiv.sum_comp (finRotate n).symm f, sub_self]

/-- A periodic domain jumps by a constant across each horizontal circle, and these constants sum
to zero. -/
private theorem exists_alphaBoundary_eq_of_periodic
    (h : G.heegaardRegionSystem.alphaArcBoundary (G.heegaardRegionSystem.alphaBoundary D) = 0) :
    ∃ a : Fin n → ℤ, (∀ c r, D (c, r) - D (c, (finRotate n).symm r) = a r) ∧ ∑ r, a r = 0 := by
  obtain ⟨a, ha⟩ := (G.heegaardRegionSystem.alphaArcBoundary_eq_zero_iff _).1 h
  have ha' : ∀ c r, D (c, r) - D (c, (finRotate n).symm r) = a r := fun c r => by
    simpa using ha (c, r)
  refine ⟨a, ha', ?_⟩
  rw [← sum_sub_finRotate_symm fun r => D (0, r)]
  exact sum_congr rfl fun r _ => (ha' 0 r).symm

/-- A periodic domain jumps by a constant across each vertical circle, and these constants sum to
zero. -/
private theorem exists_betaBoundary_eq_of_periodic
    (h : G.heegaardRegionSystem.betaArcBoundary (G.heegaardRegionSystem.betaBoundary D) = 0) :
    ∃ b : Fin n → ℤ, (∀ c r, D ((finRotate n).symm c, r) - D (c, r) = b c) ∧ ∑ c, b c = 0 := by
  obtain ⟨b, hb⟩ := (G.heegaardRegionSystem.betaArcBoundary_eq_zero_iff _).1 h
  have hb' : ∀ c r, D ((finRotate n).symm c, r) - D (c, r) = b c := fun c r => by
    simpa using hb (c, r)
  refine ⟨b, hb', ?_⟩
  rw [← neg_eq_zero, ← sum_neg_distrib, ← sum_sub_finRotate_symm fun c => D (c, 0)]
  exact sum_congr rfl fun c _ => by rw [← hb' c 0]; ring

/-- The corner sums of a periodic domain at the points of a grid state add up to a multiple of
four, so its Maslov index is even. -/
private theorem four_dvd_sum_cornerSum
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator x) D) :
    (4 : ℤ) ∣ ∑ c, cornerSum D c (x c) := by
  obtain ⟨a, ha, hsa⟩ := G.exists_alphaBoundary_eq_of_periodic (D := D)
    (by rw [(HeegaardRegionSystem.isDomainBetween_iff.1 hD).1, sub_self])
  obtain ⟨b, hb, hsb⟩ := G.exists_betaBoundary_eq_of_periodic (D := D)
    (by rw [(HeegaardRegionSystem.isDomainBetween_iff.1 hD).2, sub_self])
  have hcs : ∀ c r, cornerSum D c r = 4 * D (c, r) + 2 * b c - 2 * a r := fun c r => by
    have := ha c r
    have := hb c r
    have := hb c ((finRotate n).symm r)
    simp only [cornerSum]
    linarith
  refine ⟨∑ c, D (c, x c), ?_⟩
  simp only [hcs, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsb,
    Equiv.sum_comp x.toPerm a, hsa]
  ring

/-- A periodic domain whose jumps vanish across all horizontal circles but `r₀` and all vertical
circles but `c₀`, and which vanishes in one square, is zero. -/
private theorem eq_zero_of_periodic {E : Fin n × Fin n → ℤ}
    (hα : G.heegaardRegionSystem.alphaArcBoundary (G.heegaardRegionSystem.alphaBoundary E) = 0)
    (hβ : G.heegaardRegionSystem.betaArcBoundary (G.heegaardRegionSystem.betaBoundary E) = 0)
    {r₀ c₀ : Fin n} (hr : ∀ r, r ≠ r₀ → ∃ c, E (c, r) = E (c, (finRotate n).symm r))
    (hc : ∀ c, c ≠ c₀ → ∃ r, E ((finRotate n).symm c, r) = E (c, r)) {p : Fin n × Fin n}
    (hp : E p = 0) : E = 0 := by
  obtain ⟨a, ha, hsa⟩ := G.exists_alphaBoundary_eq_of_periodic hα
  obtain ⟨b, hb, hsb⟩ := G.exists_betaBoundary_eq_of_periodic hβ
  have ha0 : ∀ r, r ≠ r₀ → a r = 0 := fun r h => by
    obtain ⟨c, hc⟩ := hr r h
    linarith [ha c r]
  have hb0 : ∀ c, c ≠ c₀ → b c = 0 := fun c h => by
    obtain ⟨r, hr⟩ := hc c h
    linarith [hb c r]
  have ha₀ : a r₀ = 0 := by rwa [sum_eq_single r₀ (fun r _ h => ha0 r h) (by simp)] at hsa
  have hb₀ : b c₀ = 0 := by rwa [sum_eq_single c₀ (fun c _ h => hb0 c h) (by simp)] at hsb
  -- So `E` is constant along each column and along each row.
  have ha' : ∀ r, a r = 0 := fun r => by
    rcases eq_or_ne r r₀ with rfl | h
    exacts [ha₀, ha0 r h]
  have hb' : ∀ c, b c = 0 := fun c => by
    rcases eq_or_ne c c₀ with rfl | h
    exacts [hb₀, hb0 c h]
  obtain ⟨f, hf⟩ := (G.heegaardRegionSystem.betaArcBoundary_eq_zero_iff E).1 <| funext fun q => by
    have := ha q.1 q.2
    simp only [HeegaardRegionSystem.betaArcBoundary_apply,
      heegaardRegionSystem_betaNext_symm_apply, Pi.zero_apply, ha' q.2] at this ⊢
    linarith
  obtain ⟨g, hg⟩ := (G.heegaardRegionSystem.alphaArcBoundary_eq_zero_iff E).1 <| funext fun q => by
    have := hb q.1 q.2
    simp only [HeegaardRegionSystem.alphaArcBoundary_apply,
      heegaardRegionSystem_alphaNext_symm_apply, Pi.zero_apply, hb' q.1] at this ⊢
    linarith
  funext q
  have h₁ := hf q
  have h₂ := hf (q.1, p.2)
  have h₃ := hg (q.1, p.2)
  have h₄ := hg p
  simp only [heegaardRegionSystem_beta, heegaardRegionSystem_alpha] at h₁ h₂ h₃ h₄
  rw [Pi.zero_apply, h₁, ← h₂, h₃, ← h₄, hp]

omit [NeZero n] in
private theorem cornerSum_nonneg (hD₀ : 0 ≤ D) (c r : Fin n) : 0 ≤ cornerSum D c r :=
  add_nonneg (add_nonneg (add_nonneg (hD₀ _) (hD₀ _)) (hD₀ _)) (hD₀ _)

omit [NeZero n] in
/-- A nonnegative domain with corner sum zero at a grid point vanishes in the four squares around
it. -/
private theorem eq_zero_of_cornerSum_eq_zero (hD₀ : 0 ≤ D) {c r : Fin n}
    (h : cornerSum D c r = 0) :
    D ((finRotate n).symm c, r) = 0 ∧ D ((finRotate n).symm c, (finRotate n).symm r) = 0 ∧
      D (c, r) = 0 ∧ D (c, (finRotate n).symm r) = 0 := by
  have : 0 ≤ D ((finRotate n).symm c, r) := hD₀ _
  have : 0 ≤ D ((finRotate n).symm c, (finRotate n).symm r) := hD₀ _
  have : 0 ≤ D (c, r) := hD₀ _
  have : 0 ≤ D (c, (finRotate n).symm r) := hD₀ _
  simp only [cornerSum] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Across a horizontal circle other than `x c₂`, the difference of `D` and of the domain of a
rectangle with side columns `c₁` and `c₂` has a column without jump. -/
private theorem exists_sub_domain_eq_of_ne_row (hD₀ : 0 ≤ D) (R : GridRectangleBetween x y)
    {c₁ c₂ : Fin n} (hR : R.left = c₁ ∧ R.right = c₂ ∨ R.left = c₂ ∧ R.right = c₁)
    (hfix : ∀ c, c ≠ c₁ → c ≠ c₂ → cornerSum D c (x c) = 0)
    (hα : G.heegaardRegionSystem.alphaBoundary D (c₁, x c₁) =
      G.heegaardRegionSystem.alphaBoundary R.toGridRectangle.domain (c₁, x c₁))
    {r : Fin n} (hr₂ : r ≠ x c₂) :
    ∃ c, (D - R.toGridRectangle.domain) (c, r) =
      (D - R.toGridRectangle.domain) (c, (finRotate n).symm r) := by
  by_cases hr₁ : r = x c₁
  · subst hr₁
    refine ⟨c₁, ?_⟩
    simp only [HeegaardRegionSystem.alphaBoundary_apply, heegaardRegionSystem_alphaLeft,
      heegaardRegionSystem_alphaRight] at hα
    simp only [Pi.sub_apply]
    linarith
  -- Otherwise the point of `x` on the circle `r` is a common point of `x` and `y`.
  have hxr : x (x.toPerm.symm r) = r := x.toPerm.apply_symm_apply r
  have h₁ : x.toPerm.symm r ≠ c₁ := fun h => hr₁ (by rw [← hxr, h])
  have h₂ : x.toPerm.symm r ≠ c₂ := fun h => hr₂ (by rw [← hxr, h])
  refine ⟨x.toPerm.symm r, ?_⟩
  obtain ⟨-, -, hD₁, hD₂⟩ := eq_zero_of_cornerSum_eq_zero hD₀ (hfix _ h₁ h₂)
  have hb : r ≠ R.bottom ∧ r ≠ R.top := by
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
    rcases hR with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rw [hl, hr] <;> exact ⟨by assumption, by assumption⟩
  have hjump := G.alphaBoundary_domain R.toGridRectangle (x.toPerm.symm r) r
  simp only [HeegaardRegionSystem.alphaBoundary_apply, heegaardRegionSystem_alphaLeft,
    heegaardRegionSystem_alphaRight, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, ite_eq_right hb.1, ite_eq_right hb.2, sub_self,
    mul_zero] at hjump
  rw [hxr] at hD₁ hD₂
  simp only [Pi.sub_apply, hD₁, hD₂]
  linarith

/-- Across a vertical circle other than `c₂`, the difference of `D` and of the domain of a
rectangle with side columns `c₁` and `c₂` has a row without jump. -/
private theorem exists_sub_domain_eq_of_ne_column (hD₀ : 0 ≤ D) (R : GridRectangleBetween x y)
    {c₁ c₂ : Fin n} (hR : R.left = c₁ ∧ R.right = c₂ ∨ R.left = c₂ ∧ R.right = c₁)
    (hfix : ∀ c, c ≠ c₁ → c ≠ c₂ → cornerSum D c (x c) = 0)
    (hβ : G.heegaardRegionSystem.betaBoundary D (c₁, x c₁) =
      G.heegaardRegionSystem.betaBoundary R.toGridRectangle.domain (c₁, x c₁))
    {c : Fin n} (hc₂ : c ≠ c₂) :
    ∃ r, (D - R.toGridRectangle.domain) ((finRotate n).symm c, r) =
      (D - R.toGridRectangle.domain) (c, r) := by
  refine ⟨x c, ?_⟩
  by_cases hc₁ : c = c₁
  · subst hc₁
    simp only [HeegaardRegionSystem.betaBoundary_apply, heegaardRegionSystem_betaLeft,
      heegaardRegionSystem_betaRight] at hβ
    simp only [Pi.sub_apply]
    linarith
  -- Otherwise the point of `x` on the circle `c` is a common point of `x` and `y`.
  obtain ⟨hD₁, -, hD₂, -⟩ := eq_zero_of_cornerSum_eq_zero hD₀ (hfix c hc₁ hc₂)
  have hl : c ≠ R.left ∧ c ≠ R.right := by
    rcases hR with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rw [hl, hr] <;> exact ⟨by assumption, by assumption⟩
  have hjump := G.betaBoundary_domain R.toGridRectangle c (x c)
  simp only [HeegaardRegionSystem.betaBoundary_apply, heegaardRegionSystem_betaLeft,
    heegaardRegionSystem_betaRight, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, ite_eq_right hl.1, ite_eq_right hl.2, sub_self,
    mul_zero] at hjump
  simp only [Pi.sub_apply, hD₁, hD₂]
  linarith

/-- A domain from `x` to `y`, nonnegative and vanishing around every common point of `x` and `y`
off the columns `c₁` and `c₂`, is the domain of a rectangle `R` with side columns `c₁` and `c₂`
once it has the jumps and the multiplicity of `R` at the corner `(c₁, x c₁)`. -/
private theorem eq_domain_of_corner
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (hD₀ : 0 ≤ D) (R : GridRectangleBetween x y)
    {c₁ c₂ : Fin n} (hR : R.left = c₁ ∧ R.right = c₂ ∨ R.left = c₂ ∧ R.right = c₁)
    (hfix : ∀ c, c ≠ c₁ → c ≠ c₂ → cornerSum D c (x c) = 0)
    (hα : G.heegaardRegionSystem.alphaBoundary D (c₁, x c₁) =
      G.heegaardRegionSystem.alphaBoundary R.toGridRectangle.domain (c₁, x c₁))
    (hβ : G.heegaardRegionSystem.betaBoundary D (c₁, x c₁) =
      G.heegaardRegionSystem.betaBoundary R.toGridRectangle.domain (c₁, x c₁))
    (hp : D (c₁, x c₁) = R.toGridRectangle.domain (c₁, x c₁)) :
    D = R.toGridRectangle.domain := by
  have hDR := HeegaardRegionSystem.isDomainBetween_iff.1 (G.isDomainBetween_domain R)
  rw [HeegaardRegionSystem.isDomainBetween_iff] at hD
  rw [← sub_eq_zero]
  exact G.eq_zero_of_periodic (by rw [map_sub, map_sub, hD.1, hDR.1, sub_self])
    (by rw [map_sub, map_sub, hD.2, hDR.2, sub_self])
    (fun _ hr => G.exists_sub_domain_eq_of_ne_row hD₀ R hR hfix hα hr)
    (fun _ hc => G.exists_sub_domain_eq_of_ne_column hD₀ R hR hfix hβ hc)
    (p := (c₁, x c₁)) (by rw [Pi.sub_apply, hp, sub_self])

/-- At a point of `x` which is not a point of `y`, a nonnegative domain from `x` to `y` has corner
sum at least one. -/
private theorem one_le_cornerSum_source
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (hD₀ : 0 ≤ D) {c : Fin n} (hc : x c ≠ y c) :
    1 ≤ cornerSum D c (x c) := by
  have h := G.corner_of_isDomainBetween hD c (x c)
  rw [ite_eq_right (Ne.symm hc), ite_eq_left rfl] at h
  have : 0 ≤ D ((finRotate n).symm c, x c) := hD₀ _
  have : 0 ≤ D (c, (finRotate n).symm (x c)) := hD₀ _
  simp only [cornerSum]
  linarith

/-- At a point of `y` which is not a point of `x`, a nonnegative domain from `x` to `y` has corner
sum at least one. -/
private theorem one_le_cornerSum_target
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (hD₀ : 0 ≤ D) {c : Fin n} (hc : x c ≠ y c) :
    1 ≤ cornerSum D c (y c) := by
  have h := G.corner_of_isDomainBetween hD c (y c)
  rw [ite_eq_left rfl, ite_eq_right hc] at h
  have : 0 ≤ D ((finRotate n).symm c, (finRotate n).symm (y c)) := hD₀ _
  have : 0 ≤ D (c, y c) := hD₀ _
  simp only [cornerSum]
  linarith

/-- **The corner count.** If the corner sums of a nonnegative domain from `x` to `y` at the points
of `x` and `y` add up to four, and `x` and `y` differ in the distinct columns `c₁` and `c₂`, then
they agree in every other column, around which the domain vanishes, and the corner sum at
`(c₁, x c₁)` is one. -/
private theorem cornerSum_eq_of_sum_eq_four
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (hD₀ : 0 ≤ D)
    (hsum : ∑ c, (cornerSum D c (x c) + cornerSum D c (y c)) = 4) {c₁ c₂ : Fin n}
    (hc₁₂ : c₁ ≠ c₂) (hc₁ : x c₁ ≠ y c₁) (hc₂ : x c₂ ≠ y c₂) :
    cornerSum D c₁ (x c₁) = 1 ∧ ∀ c, c ≠ c₁ → c ≠ c₂ → x c = y c ∧ cornerSum D c (x c) = 0 := by
  have hsplit := add_sum_erase _ (fun c => cornerSum D c (x c) + cornerSum D c (y c))
    (mem_erase.2 ⟨hc₁₂.symm, mem_univ c₂⟩)
  rw [← add_sum_erase _ _ (mem_univ c₁), ← hsplit] at hsum
  have hrest : ∀ c ∈ (univ.erase c₁).erase c₂, 0 ≤ cornerSum D c (x c) + cornerSum D c (y c) :=
    fun c _ => add_nonneg (cornerSum_nonneg hD₀ _ _) (cornerSum_nonneg hD₀ _ _)
  have h₁ := G.one_le_cornerSum_source hD hD₀ hc₁
  have h₂ := G.one_le_cornerSum_target hD hD₀ hc₁
  have h₃ := G.one_le_cornerSum_source hD hD₀ hc₂
  have h₄ := G.one_le_cornerSum_target hD hD₀ hc₂
  have hrest₀ := sum_eq_zero_iff_of_nonneg hrest |>.1
    (by linarith [sum_nonneg hrest] : ∑ c ∈ (univ.erase c₁).erase c₂,
      (cornerSum D c (x c) + cornerSum D c (y c)) = 0)
  refine ⟨by linarith [sum_nonneg hrest], fun c h₁ h₂ => ?_⟩
  have := hrest₀ c (by simp [h₁, h₂])
  have := cornerSum_nonneg hD₀ c (x c)
  have := cornerSum_nonneg hD₀ c (y c)
  refine ⟨by_contra fun h => ?_, by linarith⟩
  linarith [G.one_le_cornerSum_source hD hD₀ h, G.one_le_cornerSum_target hD hD₀ h]

omit [NeZero n] in
/-- Two different grid states differ in two distinct columns `c₁` and `c₂` with `x c₂ = y c₁`. -/
private theorem exists_ne_of_ne (hxy : x ≠ y) :
    ∃ c₁ c₂, c₁ ≠ c₂ ∧ x c₁ ≠ y c₁ ∧ x c₂ ≠ y c₂ ∧ x c₂ = y c₁ := by
  obtain ⟨c₁, hc₁⟩ : ∃ c, x c ≠ y c := by
    by_contra h
    exact hxy (GridState.ext fun c => by_contra fun hc => h ⟨c, hc⟩)
  have hxc₂ : x (x.toPerm.symm (y c₁)) = y c₁ := x.toPerm.apply_symm_apply _
  have hc₁₂ : c₁ ≠ x.toPerm.symm (y c₁) := fun h => hc₁ (by rw [← hxc₂, ← h])
  exact ⟨c₁, _, hc₁₂, hc₁, fun h => hc₁₂ (y.toPerm.injective (hxc₂.symm.trans h)), hxc₂⟩

omit [NeZero n] in
/-- Two grid states which agree away from the columns `c₁ ≠ c₂`, with `x c₂ = y c₁`, differ by
the transposition of these two columns. -/
private theorem eq_swapColumns_of_agree {c₁ c₂ : Fin n} (hc₁ : x c₁ ≠ y c₁) (hxc₂ : x c₂ = y c₁)
    (hagree : ∀ c, c ≠ c₁ → c ≠ c₂ → x c = y c) : y = x.swapColumns c₁ c₂ := by
  -- The column of `y` occupying the row `x c₁` can only be `c₂`.
  have hyc₂ : y c₂ = x c₁ := by
    have hyd : y (y.toPerm.symm (x c₁)) = x c₁ := y.toPerm.apply_symm_apply _
    by_cases hd₁ : y.toPerm.symm (x c₁) = c₁
    · rw [hd₁] at hyd
      exact absurd hyd.symm hc₁
    by_cases hd₂ : y.toPerm.symm (x c₁) = c₂
    · rwa [hd₂] at hyd
    · exact absurd (x.toPerm.injective ((hagree _ hd₁ hd₂).trans hyd)) hd₁
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  by_cases h₁ : c = c₁
  · rw [h₁, Equiv.swap_apply_left, hxc₂]
  by_cases h₂ : c = c₂
  · rw [h₂, Equiv.swap_apply_right, hyc₂]
  · rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂, hagree c h₁ h₂]

/-- At the corner `(c₁, x c₁)` with corner sum one, the multiplicity one lies above and to the
right, and then the domain is that of the rectangle `R` with left side `c₁`, or below and to the
left, and then it is that of `R.swapSides`. -/
private theorem eq_domain_or_eq_domain_swapSides
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (hD₀ : 0 ≤ D) (R : GridRectangleBetween x y)
    (hc₁ : cornerSum D R.left (x R.left) = 1)
    (hfix : ∀ c, c ≠ R.left → c ≠ R.right → cornerSum D c (x c) = 0) :
    D = R.toGridRectangle.domain ∨ D = R.swapSides.toGridRectangle.domain := by
  have hxy : x R.left ≠ y R.left := fun h => R.left_ne_right
    (x.toPerm.injective (h.trans R.map_left))
  have hx : x R.left ≠ x R.right := fun h => R.left_ne_right (x.toPerm.injective h)
  have hcorner := G.corner_of_isDomainBetween hD R.left (x R.left)
  rw [ite_eq_right (Ne.symm hxy), ite_eq_left rfl] at hcorner
  have : 0 ≤ D ((finRotate n).symm R.left, (finRotate n).symm (x R.left)) := hD₀ _
  have : 0 ≤ D (R.left, x R.left) := hD₀ _
  have : 0 ≤ D ((finRotate n).symm R.left, x R.left) := hD₀ _
  have : 0 ≤ D (R.left, (finRotate n).symm (x R.left)) := hD₀ _
  simp only [cornerSum] at hc₁
  have hUL : D ((finRotate n).symm R.left, x R.left) = 0 := by linarith
  have hLR : D (R.left, (finRotate n).symm (x R.left)) = 0 := by linarith
  have hUL' : D (R.left - 1, x R.left) = 0 := by simpa using hUL
  have hLR' : D (R.left, x R.left - 1) = 0 := by simpa using hLR
  rcases (by omega : D (R.left, x R.left) = 1 ∨ D (R.left, x R.left) = 0) with hUR | hUR
  · refine Or.inl (G.eq_domain_of_corner hD hD₀ R (Or.inl ⟨rfl, rfl⟩) hfix ?_ ?_ ?_)
    · rw [alphaBoundary_domain]
      simp [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hUR, hLR',
        Grid.left_mem_cIco R.left_ne_right, hx]
    · rw [betaBoundary_domain]
      simp [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hUR, hUL',
        Grid.left_mem_cIco hx, R.left_ne_right]
    · simp [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hUR,
        Grid.left_mem_cIco R.left_ne_right, Grid.left_mem_cIco hx]
  · refine Or.inr (G.eq_domain_of_corner hD hD₀ R.swapSides
      (Or.inr ⟨GridRectangleBetween.swapSides_left _, GridRectangleBetween.swapSides_right _⟩)
      hfix ?_ ?_ ?_)
    · rw [alphaBoundary_domain]
      simp only [GridRectangleBetween.swapSides_toGridRectangle, Grid.right_notMem_cIco,
        ite_false, zero_mul, HeegaardRegionSystem.alphaBoundary_apply,
        heegaardRegionSystem_alphaLeft, heegaardRegionSystem_alphaRight, hUR, hLR, sub_self]
    · rw [betaBoundary_domain]
      simp only [GridRectangleBetween.swapSides_toGridRectangle, GridRectangleBetween.bottom_def,
        GridRectangleBetween.top_def, Grid.right_notMem_cIco, ite_false, zero_mul,
        HeegaardRegionSystem.betaBoundary_apply, heegaardRegionSystem_betaLeft,
        heegaardRegionSystem_betaRight, hUR, hUL, sub_self]
    · simp only [GridRectangle.domain_apply_mk, GridRectangleBetween.swapSides_toGridRectangle,
        Grid.right_notMem_cIco, ite_false, zero_mul, hUR]

/-- **Index-one domains of a grid diagram are empty rectangles.** A nonnegative domain of Maslov
index one from `x` to `y`, for Euler characteristic `1` on every square, is the domain of an
empty rectangle from `x` to `y`. No condition at the basepoints is needed. -/
theorem exists_gridRectangleBetween_isEmpty_domain_eq
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (hD₀ : 0 ≤ D)
    (hμ : G.heegaardRegionSystem.maslovIndex 1 (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D = 1) :
    ∃ R : GridRectangleBetween x y, R.IsEmpty ∧ R.toGridRectangle.domain = D := by
  -- The corner sums at the points of `x` and `y` add up to four.
  have hsum : ∑ c, (cornerSum D c (x c) + cornerSum D c (y c)) = 4 := by
    have h := G.maslovIndex_eq_sum_cornerSum x y D
    rw [hμ] at h
    exact_mod_cast (by linarith : ((∑ c, (cornerSum D c (x c) + cornerSum D c (y c)) : ℤ) : ℚ) = 4)
  -- A periodic domain has even Maslov index, so `x ≠ y`.
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨k, hk⟩ := G.four_dvd_sum_cornerSum hD
    rw [sum_add_distrib, hk] at hsum
    omega
  obtain ⟨c₁, c₂, hc₁₂, hc₁, hc₂, hxc₂⟩ := exists_ne_of_ne hxy
  obtain ⟨hcorner, hfix⟩ := G.cornerSum_eq_of_sum_eq_four hD hD₀ hsum hc₁₂ hc₁ hc₂
  let R := GridRectangleBetween.ofSwapColumns x y c₁ c₂ hc₁₂
    (eq_swapColumns_of_agree hc₁ hxc₂ fun c h₁ h₂ => (hfix c h₁ h₂).1)
  have hRl : R.left = c₁ := GridRectangleBetween.ofSwapColumns_left ..
  have hRr : R.right = c₂ := GridRectangleBetween.ofSwapColumns_right ..
  obtain ⟨S, hS⟩ : ∃ S : GridRectangleBetween x y, D = S.toGridRectangle.domain :=
    (G.eq_domain_or_eq_domain_swapSides hD hD₀ R (by rw [hRl]; exact hcorner)
      fun c h₁ h₂ => (hfix c (hRl ▸ h₁) (hRr ▸ h₂)).2).elim (fun h => ⟨_, h⟩) fun h => ⟨_, h⟩
  subst hS
  exact ⟨S, (G.maslovIndex_domain_eq_one_iff S).1 hμ, rfl⟩

/-- **The domains counted by the hat differential are those of the fully blocked rectangles.** A
domain from `x` to `y` is counted by the hat differential of the Heegaard diagram of a grid
diagram exactly when it is the domain of an empty rectangle covering no marking. -/
theorem mem_hatDomains_iff_exists_mem_fullyBlockedRectangles :
    D ∈ G.heegaardRegionSystem.hatDomains 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) ↔
      ∃ R ∈ G.fullyBlockedRectangles x y, R.toGridRectangle.domain = D := by
  constructor
  · intro hD'
    obtain ⟨hD, hz, hD₀, hμ⟩ := HeegaardRegionSystem.mem_hatDomains_iff.1 hD'
    obtain ⟨R, hR, rfl⟩ := G.exists_gridRectangleBetween_isEmpty_domain_eq hD hD₀ hμ
    refine ⟨R, (G.mem_fullyBlockedRectangles x y R).2 ⟨hR, ?_⟩, rfl⟩
    rw [GridRectangleBetween.AvoidsMarkings, GridRectangle.avoidsMarkings_iff_forall]
    intro c hc
    have hO := hz (Sum.inl c)
    have hX := hz (Sum.inr c)
    simp only [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr,
      GridRectangle.domain_apply, GridRectangle.mem_coveredSquares, hc, true_and,
      ite_eq_right_iff, one_ne_zero, imp_false] at hO hX
    exact ⟨hO, hX⟩
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hRe, hRa⟩ := (G.mem_fullyBlockedRectangles x y R).1 hR
    exact G.domain_mem_hatDomains R hRe hRa

/-- The domains counted by the hat differential of the Heegaard diagram of a grid diagram are the
domains of the fully blocked rectangles. -/
theorem hatDomains_eq_image_fullyBlockedRectangles :
    G.heegaardRegionSystem.hatDomains 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) =
      (fun R : GridRectangleBetween x y => R.toGridRectangle.domain) ''
        (G.fullyBlockedRectangles x y : Set (GridRectangleBetween x y)) := by
  ext D
  rw [mem_hatDomains_iff_exists_mem_fullyBlockedRectangles]
  simp

/-- **The hat differential of a grid diagram counts fully blocked rectangles.** The coefficient of
the hat differential of the Heegaard diagram of a grid diagram from `x` to `y` is the number,
modulo two, of empty rectangles from `x` to `y` covering no marking. -/
@[simp]
theorem hatCoefficient_gridStateEquivGenerator (x y : GridState n) :
    G.heegaardRegionSystem.hatCoefficient 1 (G.gridStateEquivGenerator x)
        (G.gridStateEquivGenerator y) =
      G.fullyBlockedRectangleCount x y := by
  rw [HeegaardRegionSystem.hatCoefficient_def, hatDomains_eq_image_fullyBlockedRectangles,
    Set.ncard_image_of_injective _ GridRectangleBetween.toGridRectangle_domain_injective,
    Set.ncard_coe_finset,
    fullyBlockedRectangleCount_def]

end IndexOne

section Differential

/-- **The hat differential of a grid diagram is the fully blocked grid differential.** Under the
identification of grid states with the generators of the Heegaard diagram of a grid diagram
(`TauCeti.GridDiagram.gridStateEquivGenerator`), the hat differential, for Euler characteristic
`1` on every square, is the fully blocked grid differential. -/
theorem hatDifferential_comp_domLCongr :
    G.heegaardRegionSystem.hatDifferential 1 ∘ₗ
        (Finsupp.domLCongr G.gridStateEquivGenerator).toLinearMap =
      (Finsupp.domLCongr G.gridStateEquivGenerator).toLinearMap ∘ₗ G.fullyBlockedDifferential := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring <| Finsupp.ext fun g => ?_
  obtain ⟨y, rfl⟩ := G.gridStateEquivGenerator.surjective g
  simp [Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply,
    hatCoefficient_gridStateEquivGenerator]

/-- **The hat differential of a grid diagram squares to zero.** For the Heegaard diagram of a grid
diagram, with Euler characteristic `1` on every square, this follows from the fully blocked grid
complex (`TauCeti.GridDiagram.fullyBlockedDifferential_comp_self_eq_zero`). -/
theorem hatDifferential_comp_hatDifferential :
    G.heegaardRegionSystem.hatDifferential 1 ∘ₗ G.heegaardRegionSystem.hatDifferential 1 = 0 := by
  set e := Finsupp.domLCongr (R := ZMod 2) (M := ZMod 2) G.gridStateEquivGenerator
  have he : ∀ c,
      G.heegaardRegionSystem.hatDifferential 1 (e c) = e (G.fullyBlockedDifferential c) :=
    fun c => LinearMap.congr_fun G.hatDifferential_comp_domLCongr c
  refine LinearMap.ext fun g => ?_
  obtain ⟨c, rfl⟩ := e.surjective g
  rw [LinearMap.comp_apply, he, he, ← LinearMap.comp_apply,
    G.fullyBlockedDifferential_comp_self_eq_zero, LinearMap.zero_apply, map_zero,
    LinearMap.zero_apply]

end Differential


end GridDiagram

end TauCeti
