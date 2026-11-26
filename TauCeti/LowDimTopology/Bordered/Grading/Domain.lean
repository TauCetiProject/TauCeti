/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Defs
public import TauCeti.LowDimTopology.Bordered.Domain
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The grading of domains in bordered Heegaard diagrams

The bordered invariants of Lipshitz, Ozsváth and Thurston are graded by the nonabelian group
`G'(4k)` of the strands algebra (`TauCeti.StrandGradingGroup`), through a grading of domains. For
a domain `B` connecting the generator `x` to the generator `y` of a bordered Heegaard diagram,

  `g'(B) = (-e(B) - n_x(B) - n_y(B), ∂^∂ B)`,

where `e(B)` is the Euler measure of `B`, `n_x(B)` and `n_y(B)` are its point measures at the two
generators, and `∂^∂ B` is the part of its boundary along `∂Σ`, recorded by its border class
(`TauCeti.BorderedHeegaardRegionSystem.borderClass`). This file defines these quantities for the
incidence data `TauCeti.BorderedHeegaardRegionSystem` and proves that `g'` is multiplicative under
juxtaposition of domains, `g'(B₁ * B₂) = g'(B₁) g'(B₂)`
(`TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.domainGrading_add`). This is the input for
the grading sets of the type `A` module and the type `D` structure of the diagram: the images of
the periodic domains at a generator `x₀` form a subgroup `P(x₀)`
(`TauCeti.BorderedHeegaardRegionSystem.periodicGradings`), and the grading of a generator `x` is
the coset `P(x₀) g'(B)` for any domain `B` from `x₀` to `x` with basepoint multiplicity zero,
which does not depend on the choice of `B`
(`TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.rightRel_domainGrading`).

The point measure `n_p(B)` at an intersection point `p` is the average multiplicity of `B` at the
four corners at `p`, as for closed diagrams (`TauCeti.HeegaardRegionSystem.pointMeasure`). The
regions along the boundary have further corners, where the `α`-arcs meet `∂Σ` at a right angle:
each end `i` of an arc is a corner of the regions beside the two intervals of `∂Σ` at `i`. With
every corner contributing one quarter, the Euler measure of a region `R` with `k` corners is
`χ(R) - k / 4`, the Euler characteristics `χ(R)` being an explicit argument as they are not
determined by the incidence data.

Multiplicativity rests on a bordered form of the reciprocity of point measures. For two domains
`D` and `E`, pairing `∂(∂D ∩ α)` with the point measures of `E` and `∂(∂E ∩ β)` with the point
measures of `D` no longer gives opposite values: summation by parts along an `α`-arc leaves a
contribution at its two ends, and in total the two pairings add up to `∑ᵢ (∂^∂ D)(i) m_E(i)`, where
`m_E(i)` is the multiplicity of `E` at the boundary point `i`, the average of its multiplicities
at the two adjacent intervals. When `E` has basepoint multiplicity `n_z(E)`, this multiplicity is
`n_z(E) + m(∂^∂ E, i)` (`TauCeti.StrandGradingGroup.pointMultiplicity`), and since `∂^∂ D` has
total sum zero the boundary contribution is the linking `L(∂^∂ D, ∂^∂ E)` of
`TauCeti.StrandGradingGroup.linking`. For `D` from `x` to `y` and `E` from `y` to `w` this gives

  `n_x(E) + n_w(D) = n_y(D) + n_y(E) - L(∂^∂ D, ∂^∂ E)`,

which is exactly the correction term `L` in the product of `G'(4k)`.

## Main definitions

* `TauCeti.BorderedHeegaardRegionSystem.pointMeasure`: the point measure `n_p(D)`.
* `TauCeti.BorderedHeegaardRegionSystem.generatorPointMeasure`: the point measure `n_x(D)` of a
  generator.
* `TauCeti.BorderedHeegaardRegionSystem.borderPointMultiplicity`: the multiplicity of a domain at
  a point of the boundary.
* `TauCeti.BorderedHeegaardRegionSystem.cornerCount`: the number of corners of a region, at the
  intersection points and at the ends of the arcs.
* `TauCeti.BorderedHeegaardRegionSystem.eulerMeasure`: the Euler measure `e(D)`.
* `TauCeti.BorderedHeegaardRegionSystem.domainGrading`: the grading
  `g'(D) = (-e(D) - n_x(D) - n_y(D), ∂^∂ D)`.
* `TauCeti.BorderedHeegaardRegionSystem.periodicGrading`,
  `TauCeti.BorderedHeegaardRegionSystem.periodicGradings`: the grading of periodic domains at a
  generator, as a homomorphism, and its image `P(x)`.

## Main results

* `TauCeti.BorderedHeegaardRegionSystem.borderPointMultiplicity_eq_add_pointMultiplicity`: the
  multiplicity at a boundary point is the basepoint multiplicity plus the multiplicity of the
  border class.
* `TauCeti.BorderedHeegaardRegionSystem.eulerMeasure_eq_sub_sum_pointMeasure`: the Euler measure
  is `∑ χ(R) D(R) - ∑ₚ n_p(D) - ∑ᵢ m_D(i) / 2`.
* `sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure`: the bordered
  reciprocity of point measures, and its form
  `sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_linking`
  with the linking of the border classes.
* `IsDomainBetween.generatorPointMeasure_add_generatorPointMeasure`, in the namespace
  `TauCeti.BorderedHeegaardRegionSystem`: `n_x(E) + n_w(D) = n_y(D) + n_y(E) - L(∂^∂ D, ∂^∂ E)`.
* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.domainGrading_add`: the grading is
  multiplicative under juxtaposition, and
  `TauCeti.BorderedHeegaardRegionSystem.domainGrading_neg`: reversing a domain inverts its grading.
* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.periodicGradings_eq`: a domain `D` from
  `x` to `y` conjugates `P(x)` into `P(y)`, `P(y) = g'(D)⁻¹ P(x) g'(D)`.
* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.rightRel_domainGrading`: two domains from
  `x₀` to `x` with the same basepoint multiplicity have gradings in the same coset of `P(x₀)`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), Chapter 10:
  the grading `g'` of domains, its multiplicativity, and the grading sets of the bordered
  invariants as cosets of the gradings of periodic domains.
* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Topol. **4** (2011),
  [arXiv:math/0609673](https://arxiv.org/abs/math/0609673), for the combinatorial proof of the
  reciprocity of point measures in closed diagrams.
-/

public section

open Finset

open scoped Pointwise

namespace TauCeti

namespace BorderedHeegaardRegionSystem

universe u v w r

variable {g n : ℕ} {Arc : Type u} {AlphaCircle : Type v} {Point : Type w} {Region : Type r}
  (H : BorderedHeegaardRegionSystem g n Arc AlphaCircle Point Region)

/-! ### Point measures -/

section PointMeasure

/-- The four regions with a corner at the intersection point `p`, with repetition: the regions
to the left and to the right of the `α`-segment ending at `p`, then those of the `α`-segment
starting at `p`. -/
def cornerRegion (p : Point) : Fin 4 → Region :=
  ![H.alphaLeft (H.alphaNext.symm (.inl p)), H.alphaRight (H.alphaNext.symm (.inl p)),
    H.alphaLeft (.inl p), H.alphaRight (.inl p)]

/-- The two regions with a corner at the end `i` of an `α`-arc on the boundary: the regions
beside the intervals of `∂Σ` below and above `i`. -/
def borderCornerRegion (i : Fin n) : Fin 2 → Region :=
  ![H.borderRegion i.castSucc, H.borderRegion i.succ]

/-- The point measure `n_p(D)`: the average multiplicity of the domain `D` at the four corners
at the intersection point `p`. -/
def pointMeasure : (Region → ℤ) →+ Point → ℚ where
  toFun D p := (∑ i, (D (H.cornerRegion p i) : ℚ)) / 4
  map_zero' := by ext; simp
  map_add' D E := by ext; simp [sum_add_distrib, add_div]

theorem pointMeasure_apply_eq_sum (D : Region → ℤ) (p : Point) :
    H.pointMeasure D p = (∑ i, (D (H.cornerRegion p i) : ℚ)) / 4 :=
  (rfl)

@[simp]
theorem pointMeasure_apply (D : Region → ℤ) (p : Point) :
    H.pointMeasure D p =
      ((D (H.alphaLeft (H.alphaNext.symm (.inl p))) : ℚ) +
        D (H.alphaRight (H.alphaNext.symm (.inl p))) + D (H.alphaLeft (.inl p)) +
          D (H.alphaRight (.inl p))) / 4 := by
  simp [pointMeasure_apply_eq_sum, cornerRegion, Fin.sum_univ_four]

/-- The four corners at a crossing are also the regions on the two sides of the `β`-segment
ending there and of the `β`-segment starting there, so the point measure can be read off along
`β`. -/
theorem pointMeasure_apply_beta (D : Region → ℤ) (p : Point) :
    H.pointMeasure D p =
      ((D (H.betaLeft (H.betaNext.symm p)) : ℚ) + D (H.betaRight (H.betaNext.symm p)) +
        D (H.betaLeft p) + D (H.betaRight p)) / 4 := by
  rw [pointMeasure_apply]
  congr 1
  norm_cast
  linear_combination (H.crossingCompatible p).corner_sum_eq D

/-- The point measure `n_x(D) = ∑ᵢ n_{xᵢ}(D)` of a domain `D` at a generator `x`. -/
def generatorPointMeasure (x : H.Generator) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ j, H.pointMeasure D (x.point j)
  map_zero' := by simp
  map_add' D E := by simp only [map_add, Pi.add_apply, sum_add_distrib]

@[simp]
theorem generatorPointMeasure_apply (x : H.Generator) (D : Region → ℤ) :
    H.generatorPointMeasure x D = ∑ j, H.pointMeasure D (x.point j) :=
  (rfl)

/-- The point measure of a generator is the pairing of its `0`-chain with the point measures. -/
theorem generatorPointMeasure_eq_sum_generatorChain [Fintype Point] (x : H.Generator)
    (D : Region → ℤ) :
    H.generatorPointMeasure x D = ∑ q, (H.generatorChain x q : ℚ) * H.pointMeasure D q :=
  (H.sum_generatorChain_mul x (H.pointMeasure D)).symm

/-- The multiplicity `m_D(i)` of a domain at the point `i` of the boundary: the average of its
multiplicities at the two intervals of `∂Σ` on either side of `i`. -/
def borderPointMultiplicity : (Region → ℤ) →+ Fin n → ℚ where
  toFun D i := ((D (H.borderRegion i.castSucc) : ℚ) + D (H.borderRegion i.succ)) / 2
  map_zero' := by ext; simp
  map_add' D E := by ext; simp only [Pi.add_apply, Int.cast_add]; ring

@[simp]
theorem borderPointMultiplicity_apply (D : Region → ℤ) (i : Fin n) :
    H.borderPointMultiplicity D i =
      ((D (H.borderRegion i.castSucc) : ℚ) + D (H.borderRegion i.succ)) / 2 :=
  (rfl)

/-- **The multiplicity at a boundary point and the border class.** The multiplicity of a domain
at the boundary point `i` is its basepoint multiplicity plus the multiplicity `m(∂^∂ D, i)` of the
class of `∂^∂ D` at `i`. -/
theorem borderPointMultiplicity_eq_add_pointMultiplicity (D : Region → ℤ) (i : Fin n) :
    H.borderPointMultiplicity D i =
      D (H.borderRegion 0) + StrandGradingGroup.pointMultiplicity i (H.borderClass D) := by
  have h₁ := H.apply_borderRegion_castSucc D i
  have h₂ : D (H.borderRegion i.succ) = D (H.borderRegion i.castSucc) - H.borderClass D i := by
    rw [borderClass_apply]
    ring
  rw [borderPointMultiplicity_apply, StrandGradingGroup.pointMultiplicity_apply, h₂, h₁]
  push_cast
  ring

end PointMeasure

/-! ### Reciprocity of point measures -/

section Reciprocity

/-- The corner sum of `E` at a node of the `α`-curves, divided by four: the point measure at an
intersection point, and at the boundary node of an arc the corners at its two ends. -/
private def nodeMeasure (E : Region → ℤ) (v : Point ⊕ Arc) : ℚ :=
  ((E (H.alphaLeft (H.alphaNext.symm v)) + E (H.alphaRight (H.alphaNext.symm v)) +
    (E (H.alphaLeft v) + E (H.alphaRight v)) : ℤ) : ℚ) / 4

/-- At the boundary node of an arc, the boundary term of summation by parts along the arc is the
multiplicity-weighted border class at its two ends. -/
private theorem boundary_term_eq (D E : Region → ℤ) (a : Arc) :
    (((D (H.alphaLeft (H.alphaNext.symm (.inr a))) - D (H.alphaRight (H.alphaNext.symm (.inr a))) +
          (D (H.alphaLeft (.inr a)) - D (H.alphaRight (.inr a)))) *
        (E (H.alphaLeft (.inr a)) + E (H.alphaRight (.inr a)) -
          (E (H.alphaLeft (H.alphaNext.symm (.inr a))) +
            E (H.alphaRight (H.alphaNext.symm (.inr a))))) : ℤ) : ℚ) / 4 -
        (H.alphaArcBoundary (H.alphaBoundary D) (.inr a) : ℚ) * H.nodeMeasure E (.inr a) =
      (H.borderClass D (H.arcEnd (.inl a)) : ℚ) * H.borderPointMultiplicity E (H.arcEnd (.inl a)) +
        (H.borderClass D (H.arcEnd (.inr a)) : ℚ) *
          H.borderPointMultiplicity E (H.arcEnd (.inr a)) := by
  simp only [nodeMeasure, alphaArcBoundary_apply, alphaBoundary_apply, borderClass_apply,
    borderPointMultiplicity_apply, H.alphaLeft_inr, H.alphaRight_inr, H.alphaLeft_symm_inr,
    H.alphaRight_symm_inr]
  push_cast
  ring

variable [Fintype Point]

/-- **Reciprocity of point measures in a bordered diagram.** For any two domains `D` and `E`,
pairing `∂(∂D ∩ α)` with the point measures of `E` and `∂(∂E ∩ β)` with those of `D` adds up to
the border class of `D` paired with the multiplicities of `E` at the boundary points. In a closed
diagram the two pairings cancel; here summation by parts along each `α`-arc leaves a contribution
at its two ends. -/
theorem sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure
    (D E : Region → ℤ) :
    ∑ q, (H.alphaArcBoundary (H.alphaBoundary D) (.inl q) : ℚ) * H.pointMeasure E q +
      ∑ q, (H.betaArcBoundary (H.betaBoundary E) q : ℚ) * H.pointMeasure D q =
      ∑ i, (H.borderClass D i : ℚ) * H.borderPointMultiplicity E i := by
  have : Finite Arc := .of_injective _ (H.arcEnd.injective.comp Sum.inl_injective)
  have := Fintype.ofFinite Arc
  -- Summation by parts along the `α`-curves, including the boundary nodes, and along the
  -- `β`-circles.
  have hα := HeegaardRegionSystem.sum_mul_cornerSum_div_four H.alphaNext H.alphaLeft
    H.alphaRight D E (H.alphaArcBoundary (H.alphaBoundary D)) (H.nodeMeasure E)
    (fun v => by simp only [alphaArcBoundary_apply, alphaBoundary_apply]) fun v => rfl
  have hβ := HeegaardRegionSystem.sum_mul_cornerSum_div_four H.betaNext H.betaLeft
    H.betaRight E D (H.betaArcBoundary (H.betaBoundary E)) (H.pointMeasure D)
    (fun q => by simp only [betaArcBoundary_apply, betaBoundary_apply])
    (fun q => by rw [pointMeasure_apply_beta]; push_cast; ring)
  have hnode (q : Point) : H.nodeMeasure E (.inl q) = H.pointMeasure E q := by
    rw [nodeMeasure, pointMeasure_apply]
    push_cast
    ring
  simp only [Fintype.sum_sum_type, Int.cast_add, hnode] at hα
  -- The cross terms at the intersection points cancel.
  have hcross := congrArg (Int.cast : ℤ → ℚ)
    (sum_eq_zero fun q (_ : q ∈ univ) => (H.crossingCompatible q).cross_add_cross_eq_zero D E)
  rw [sum_add_distrib, Int.cast_add, Int.cast_zero] at hcross
  -- The boundary terms at the ends of the arcs give the border class paired with the
  -- multiplicities at the boundary points.
  have hbd := sum_congr rfl fun a (_ : a ∈ univ) => H.boundary_term_eq D E a
  rw [sum_sub_distrib, ← sum_div, ← Int.cast_sum, sum_add_distrib] at hbd
  have hends (f : Fin n → ℚ) :
      ∑ a, f (H.arcEnd (.inl a)) + ∑ a, f (H.arcEnd (.inr a)) = ∑ i, f i := by
    rw [← H.arcEnd.sum_comp, Fintype.sum_sum_type]
  rw [hends fun i => (H.borderClass D i : ℚ) * H.borderPointMultiplicity E i] at hbd
  linear_combination hα + hβ + hcross / 4 + hbd

/-- **Reciprocity of point measures and the linking form.** For any two domains `D` and `E`,
pairing `∂(∂D ∩ α)` with the point measures of `E` and `∂(∂E ∩ β)` with those of `D` adds up to
the linking `L(∂^∂ D, ∂^∂ E)` of their border classes. -/
theorem sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_linking
    (D E : Region → ℤ) :
    ∑ q, (H.alphaArcBoundary (H.alphaBoundary D) (.inl q) : ℚ) * H.pointMeasure E q +
      ∑ q, (H.betaArcBoundary (H.betaBoundary E) q : ℚ) * H.pointMeasure D q =
      StrandGradingGroup.linking (H.borderClass D) (H.borderClass E) := by
  have hsum : ∑ i, (H.borderClass D i : ℚ) = 0 := by exact_mod_cast H.sum_borderClass D
  rw [sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure,
    StrandGradingGroup.linking_apply]
  simp only [borderPointMultiplicity_eq_add_pointMultiplicity, mul_add, sum_add_distrib,
    ← sum_mul, hsum, zero_mul, zero_add]

variable {H} {x y w : H.Generator} {D E : Region → ℤ}

omit [Fintype Point] in
/-- **The point measures of juxtaposable domains.** When `D` connects `x` to `y` and `E`
connects `y` to `w`, `n_x(E) + n_w(D) = n_y(D) + n_y(E) - L(∂^∂ D, ∂^∂ E)`. In a closed diagram
the linking term is absent. -/
theorem IsDomainBetween.generatorPointMeasure_add_generatorPointMeasure [Finite Point]
    (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween y w E) :
    H.generatorPointMeasure x E + H.generatorPointMeasure w D =
      H.generatorPointMeasure y D + H.generatorPointMeasure y E -
        StrandGradingGroup.linking (H.borderClass D) (H.borderClass E) := by
  have := Fintype.ofFinite Point
  -- `∂(∂D ∩ α) = y - x` at the intersection points and `∂(∂E ∩ β) = y - w`, so the two pairings
  -- are `n_y(E) - n_x(E)` and `n_y(D) - n_w(D)`.
  have h :=
    H.sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_linking D E
  simp only [isDomainBetween_iff.mp hD |>.1, (isDomainBetween_iff.mp hE).2, Pi.sub_apply,
    Int.cast_sub, sub_mul, sum_sub_distrib, ← generatorPointMeasure_eq_sum_generatorChain] at h
  linarith

end Reciprocity

/-! ### The Euler measure -/

section EulerMeasure

variable [Fintype Point] [DecidableEq Region]

/-- The number of corners of the region `r`: the corners at the intersection points, counted
with multiplicity over the four corners at each point, and the corners at the ends of the arcs on
the boundary, two at each end. -/
def cornerCount (r : Region) : ℕ :=
  #{c : Point × Fin 4 | H.cornerRegion c.1 c.2 = r} +
    #{c : Fin n × Fin 2 | H.borderCornerRegion c.1 c.2 = r}

theorem cornerCount_eq_card (r : Region) :
    H.cornerCount r = #{c : Point × Fin 4 | H.cornerRegion c.1 c.2 = r} +
      #{c : Fin n × Fin 2 | H.borderCornerRegion c.1 c.2 = r} :=
  (rfl)

variable [Fintype Region]

/-- The Euler measure `e(D) = ∑ D(R) (χ(R) - k(R) / 4)` of a domain, where `χ(R)` is the Euler
characteristic of the region `R`, supplied as `χ`, and `k(R)` is its number of corners, at the
intersection points and at the ends of the arcs. -/
def eulerMeasure (χ : Region → ℤ) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ r, (D r : ℚ) * (χ r - H.cornerCount r / 4)
  map_zero' := by simp
  map_add' D E := by simp [add_mul, sum_add_distrib]

@[simp]
theorem eulerMeasure_apply (χ : Region → ℤ) (D : Region → ℤ) :
    H.eulerMeasure χ D = ∑ r, (D r : ℚ) * (χ r - H.cornerCount r / 4) :=
  (rfl)

/-- Each corner contributes a quarter of the multiplicity at its region to the point measure at
its vertex, so the Euler measure is `∑ χ(R) D(R) - ∑ₚ n_p(D) - ∑ᵢ m_D(i) / 2`, the two corners at
the boundary point `i` contributing `m_D(i) / 2`. -/
theorem eulerMeasure_eq_sub_sum_pointMeasure (χ : Region → ℤ) (D : Region → ℤ) :
    H.eulerMeasure χ D = ∑ r, (χ r : ℚ) * D r - ∑ p, H.pointMeasure D p -
      (∑ i, H.borderPointMultiplicity D i) / 2 := by
  have hcorner : ∑ r, (D r : ℚ) * #{c : Point × Fin 4 | H.cornerRegion c.1 c.2 = r} =
      ∑ p, 4 * H.pointMeasure D p := by
    simp_rw [card_filter, Nat.cast_sum, mul_sum]
    rw [sum_comm, Fintype.sum_prod_type]
    refine sum_congr rfl fun p _ => ?_
    rw [pointMeasure_apply_eq_sum, mul_div_cancel₀ _ four_ne_zero]
    simp [Nat.cast_ite]
  have hborder : ∑ r, (D r : ℚ) * #{c : Fin n × Fin 2 | H.borderCornerRegion c.1 c.2 = r} =
      ∑ i, 2 * H.borderPointMultiplicity D i := by
    simp_rw [card_filter, Nat.cast_sum, mul_sum]
    rw [sum_comm, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [borderPointMultiplicity_apply, mul_div_cancel₀ _ two_ne_zero]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, ite_true, Fin.sum_univ_two]
    simp [borderCornerRegion]
  have h (r : Region) : (D r : ℚ) * (χ r - H.cornerCount r / 4) =
      χ r * D r - D r * #{c : Point × Fin 4 | H.cornerRegion c.1 c.2 = r} / 4 -
        D r * #{c : Fin n × Fin 2 | H.borderCornerRegion c.1 c.2 = r} / 4 := by
    rw [cornerCount_eq_card]
    push_cast
    ring
  rw [eulerMeasure_apply, sum_congr rfl fun r _ => h r, sum_sub_distrib, sum_sub_distrib,
    ← sum_div, ← sum_div, hcorner, hborder, ← mul_sum, ← mul_sum]
  ring

end EulerMeasure

/-! ### The grading of domains -/

section Grading

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

/-- The grading `g'(D) = (-e(D) - n_x(D) - n_y(D), ∂^∂ D)` of a domain `D` from the generator
`x` to the generator `y` in the grading group of the strands algebra, for the Euler
characteristics `χ` of the regions. -/
def domainGrading (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    StrandGradingGroup (Fin n) :=
  .mk (-(H.eulerMeasure χ D + H.generatorPointMeasure x D + H.generatorPointMeasure y D))
    (H.borderClass D)

@[simp]
theorem domainGrading_maslov (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    (H.domainGrading χ x y D).maslov =
      -(H.eulerMeasure χ D + H.generatorPointMeasure x D + H.generatorPointMeasure y D) :=
  StrandGradingGroup.mk_maslov _ _

@[simp]
theorem domainGrading_boundary (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    (H.domainGrading χ x y D).boundary = H.borderClass D :=
  StrandGradingGroup.mk_boundary _ _

/-- The zero domain has grading `1`. -/
@[simp]
theorem domainGrading_zero (χ : Region → ℤ) (x : H.Generator) : H.domainGrading χ x x 0 = 1 := by
  ext <;> simp

/-- Reversing a domain inverts its grading: the border class has total sum zero, so the linking
term of the inverse vanishes. -/
theorem domainGrading_neg (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    H.domainGrading χ y x (-D) = (H.domainGrading χ x y D)⁻¹ := by
  have hsum : ∑ i, (H.borderClass D i : ℚ) = 0 := by exact_mod_cast H.sum_borderClass D
  ext
  · simp only [domainGrading_maslov, map_neg, StrandGradingGroup.inv_maslov,
      domainGrading_boundary, StrandGradingGroup.linking_self, hsum]
    ring
  · simp only [domainGrading_boundary, StrandGradingGroup.inv_boundary, map_neg]

variable {H} {x y w : H.Generator} {D E : Region → ℤ}

/-- **The grading of domains is multiplicative.** If `D` connects `x` to `y` and `E` connects
`y` to `w`, then `g'(D + E) = g'(D) g'(E)` in the grading group of the strands algebra. -/
theorem IsDomainBetween.domainGrading_add (χ : Region → ℤ) (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y w E) :
    H.domainGrading χ x w (D + E) = H.domainGrading χ x y D * H.domainGrading χ y w E := by
  have := hD.generatorPointMeasure_add_generatorPointMeasure hE
  ext
  · simp only [domainGrading_maslov, map_add, StrandGradingGroup.mul_maslov,
      domainGrading_boundary]
    linarith
  · simp only [domainGrading_boundary, StrandGradingGroup.mul_boundary, map_add]

variable (H) in
/-- The grading of the periodic domains at a generator `x`, as a homomorphism to the grading
group: periodic domains connect `x` to itself, so their gradings multiply. -/
def periodicGrading (χ : Region → ℤ) (x : H.Generator) :
    Multiplicative H.periodicDomains →* StrandGradingGroup (Fin n) where
  toFun P := H.domainGrading χ x x (P.toAdd : Region → ℤ)
  map_one' := by simp
  map_mul' P Q := by
    simp only [toAdd_mul, AddSubgroup.coe_add]
    exact (isDomainBetween_self_iff.mpr P.toAdd.property).1.domainGrading_add χ
      (isDomainBetween_self_iff.mpr Q.toAdd.property).1

@[simp]
theorem periodicGrading_apply (χ : Region → ℤ) (x : H.Generator)
    (P : Multiplicative H.periodicDomains) :
    H.periodicGrading χ x P = H.domainGrading χ x x (P.toAdd : Region → ℤ) :=
  (rfl)

variable (H) in
/-- The subgroup `P(x)` of the grading group formed by the gradings of the periodic domains at
the generator `x`. -/
def periodicGradings (χ : Region → ℤ) (x : H.Generator) : Subgroup (StrandGradingGroup (Fin n)) :=
  (H.periodicGrading χ x).range

theorem mem_periodicGradings_iff {χ : Region → ℤ} {x : H.Generator}
    {a : StrandGradingGroup (Fin n)} :
    a ∈ H.periodicGradings χ x ↔ ∃ P ∈ H.periodicDomains, H.domainGrading χ x x P = a := by
  simp only [periodicGradings, MonoidHom.mem_range, periodicGrading_apply]
  exact ⟨fun ⟨P, hP⟩ => ⟨_, P.toAdd.property, hP⟩, fun ⟨P, hP, h⟩ => ⟨.ofAdd ⟨P, hP⟩, h⟩⟩

/-- **Changing the generator conjugates the periodic gradings.** For a domain `D` from `x` to
`y`, the grading of a periodic domain at `y` is that at `x` conjugated by `g'(D)`, so
`P(y) = g'(D)⁻¹ P(x) g'(D)`. -/
theorem IsDomainBetween.periodicGradings_eq (χ : Region → ℤ) (hD : H.IsDomainBetween x y D) :
    H.periodicGradings χ y = MulAut.conj (H.domainGrading χ x y D)⁻¹ • H.periodicGradings χ x := by
  -- A periodic domain `P` at `y` is the juxtaposition `-D + P + D` through `x`.
  have hconj {P : Region → ℤ} (hP : P ∈ H.periodicDomains) :
      H.domainGrading χ y y P =
        (H.domainGrading χ x y D)⁻¹ * H.domainGrading χ x x P * H.domainGrading χ x y D := by
    rw [← domainGrading_neg, ← hD.neg.domainGrading_add χ (isDomainBetween_self_iff.mpr hP).1,
      ← (hD.neg.add (isDomainBetween_self_iff.mpr hP).1).domainGrading_add χ hD,
      neg_add_cancel_comm]
  ext a
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
    MulAut.conj_apply, mem_periodicGradings_iff, mem_periodicGradings_iff]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, by rw [hconj hP]; group⟩
  · rintro ⟨P, hP, h⟩
    exact ⟨P, hP, by rw [hconj hP, h]; group⟩

/-- **The relative grading is well defined.** Two domains from `x₀` to `x` with the same
basepoint multiplicity have gradings in the same right coset of the periodic gradings `P(x₀)`, so
the coset `P(x₀) g'(D)` does not depend on the domain `D` from `x₀` to `x`. -/
theorem IsDomainBetween.rightRel_domainGrading (χ : Region → ℤ) {D' : Region → ℤ}
    (hD : H.IsDomainBetween x y D) (hD' : H.IsDomainBetween x y D')
    (h₀ : D' (H.borderRegion 0) = D (H.borderRegion 0)) :
    QuotientGroup.rightRel (H.periodicGradings χ x) (H.domainGrading χ x y D)
      (H.domainGrading χ x y D') := by
  have hP := hD.sub_mem_periodicDomains_iff.mpr ⟨hD', h₀⟩
  rw [QuotientGroup.rightRel_apply, mem_periodicGradings_iff]
  refine ⟨D' - D, hP, ?_⟩
  rw [eq_mul_inv_iff_mul_eq, ← ((isDomainBetween_self_iff.mpr hP).1.domainGrading_add χ hD),
    sub_add_cancel]

end Grading

end BorderedHeegaardRegionSystem

end TauCeti
