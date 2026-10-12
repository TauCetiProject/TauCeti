/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import TauCeti.LowDimTopology.Heegaard.Domain
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The combinatorial Maslov index of a domain

Lipshitz's index formula computes the expected dimension of the moduli space of holomorphic
disks in a Whitney class `φ` from its domain `D` alone:
`μ(φ) = e(D) + n_x(D) + n_y(D)`. This file defines the right-hand side for the abstract region
incidence data `TauCeti.HeegaardRegionSystem` and proves that it is additive under juxtaposition
of domains, a property needed for a relative grading once independence of the choice of domain is
established.

Every intersection point `p` is a corner of four regions (with repetition): the regions on the
two sides of the `α`-arc ending at `p` and of the `α`-arc starting at `p`. The *point measure*
`n_p(D)` is the average of the multiplicities of `D` at these four corners, and for a generator
`x = {x₁, …, xₙ}` one puts `n_x(D) = ∑ n_{xᵢ}(D)`. With the standard combinatorial convention
that every corner contributes one quarter, the *Euler measure* of a region `R` with `k` corners
is `χ(R) - k / 4`; it is extended linearly to domains. The Euler characteristics `χ(R)` of the
regions are not determined by the incidence data, so they are an explicit argument.

The key combinatorial fact is that for a domain `D` from `x` to `y` and a domain `E` from `y` to
`w`, `n_x(E) + n_w(D) = n_y(D) + n_y(E)`. Both sides differ by a corner-averaged intersection
number of `∂D ∩ α` with `∂E ∩ β`, computed once along the `α`-curves and once along the
`β`-curves, and the two computations agree up to sign at every crossing.

## Main definitions

* `TauCeti.HeegaardRegionSystem.cornerRegion`: the four regions with a corner at a point.
* `TauCeti.HeegaardRegionSystem.pointMeasure`: the point measure `n_p(D)`.
* `TauCeti.HeegaardRegionSystem.generatorPointMeasure`: the point measure `n_x(D)` of a
  generator.
* `TauCeti.HeegaardRegionSystem.cornerCount`: the number of corners of a region.
* `TauCeti.HeegaardRegionSystem.eulerMeasure`: the Euler measure `e(D)`.
* `TauCeti.HeegaardRegionSystem.maslovIndex`: the combinatorial Maslov index
  `e(D) + n_x(D) + n_y(D)`.

## Main results

* `TauCeti.HeegaardRegionSystem.pointMeasure_apply_beta`: the point measure is also the average
  over the corners on the two sides of the `β`-arcs.
* `TauCeti.HeegaardRegionSystem.eulerMeasure_eq_sub_sum_pointMeasure`: the Euler measure is
  `∑ χ(R) D(R) - ∑ₚ n_p(D)`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.generatorPointMeasure_add_generatorPointMeasure`:
  `n_x(E) + n_w(D) = n_y(D) + n_y(E)` for `D` from `x` to `y` and `E` from `y` to `w`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.maslovIndex_add`: the Maslov index is additive
  under juxtaposition.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.maslovIndex_self_eq`: a domain whose boundary is
  a sum of whole curves has the same Maslov index at any two generators joined by a domain.

## References

* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, where the index formula
  and its additivity are proved; see also the erratum
  [arXiv:1301.4919](https://arxiv.org/abs/1301.4919).
* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Topol. **4** (2011),
  [arXiv:math/0609673](https://arxiv.org/abs/math/0609673), for the combinatorial proof of the
  additivity of point measures.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Finset

section PointMeasure

/-- The four regions with a corner at the intersection point `p`, with repetition: the regions
to the left and to the right of the `α`-arc ending at `p`, then those of the `α`-arc starting at
`p`. -/
def cornerRegion (p : Point) : Fin 4 → Region :=
  ![H.alphaLeft (H.alphaNext.symm p), H.alphaRight (H.alphaNext.symm p), H.alphaLeft p,
    H.alphaRight p]

theorem cornerRegion_eq (p : Point) :
    H.cornerRegion p = ![H.alphaLeft (H.alphaNext.symm p), H.alphaRight (H.alphaNext.symm p),
      H.alphaLeft p, H.alphaRight p] :=
  (rfl)

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
      ((D (H.alphaLeft (H.alphaNext.symm p)) : ℚ) + D (H.alphaRight (H.alphaNext.symm p)) +
        D (H.alphaLeft p) + D (H.alphaRight p)) / 4 := by
  simp [pointMeasure_apply_eq_sum, cornerRegion, Fin.sum_univ_four]

/-- The four corners at a crossing are also the regions on the two sides of the `β`-arc ending
there and of the `β`-arc starting there, so the point measure can be read off along `β`. -/
theorem pointMeasure_apply_beta (D : Region → ℤ) (p : Point) :
    H.pointMeasure D p =
      ((D (H.betaLeft (H.betaNext.symm p)) : ℚ) + D (H.betaRight (H.betaNext.symm p)) +
        D (H.betaLeft p) + D (H.betaRight p)) / 4 := by
  rw [pointMeasure_apply]
  rcases H.crossingCompatible p with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;>
    · rw [h₁, h₂, h₃, h₄]
      ring

/-- The point measure `n_x(D) = ∑ᵢ n_{xᵢ}(D)` of a domain `D` at a generator `x`. -/
def generatorPointMeasure (x : H.Generator) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ i, H.pointMeasure D (H.point x i)
  map_zero' := by simp
  map_add' D E := by simp only [map_add, Pi.add_apply, sum_add_distrib]

@[simp]
theorem generatorPointMeasure_apply (x : H.Generator) (D : Region → ℤ) :
    H.generatorPointMeasure x D = ∑ i, H.pointMeasure D (H.point x i) :=
  (rfl)

/-- The point measure of a generator is the pairing of its `0`-chain with the point
measures. -/
theorem generatorPointMeasure_eq_sum_generatorChain [Fintype Point] (x : H.Generator)
    (D : Region → ℤ) :
    H.generatorPointMeasure x D = ∑ q, (H.generatorChain x q : ℚ) * H.pointMeasure D q := by
  simp_rw [← zsmul_eq_mul]
  exact (H.sum_generatorChain_smul x (H.pointMeasure D)).symm

end PointMeasure

section Additivity

variable {H}

/-- At every crossing, the jump across `β` of the average of `E` along `α`, weighted by the
`α`-boundary of `D`, cancels the jump across `α` of the average of `D` along `β`, weighted by the
`β`-boundary of `E`: both are the local intersection number of the two boundaries, with opposite
signs. -/
private theorem crossing_cancel (D E : Region → ℤ) (q : Point) :
    ((H.alphaBoundary D (H.alphaNext.symm q) : ℚ) + H.alphaBoundary D q) *
        (((E (H.alphaLeft q) : ℚ) + E (H.alphaRight q)) -
          ((E (H.alphaLeft (H.alphaNext.symm q)) : ℚ) + E (H.alphaRight (H.alphaNext.symm q)))) +
      ((H.betaBoundary E (H.betaNext.symm q) : ℚ) + H.betaBoundary E q) *
        (((D (H.betaLeft q) : ℚ) + D (H.betaRight q)) -
          ((D (H.betaLeft (H.betaNext.symm q)) : ℚ) + D (H.betaRight (H.betaNext.symm q)))) =
      0 := by
  simp only [alphaBoundary_apply, betaBoundary_apply, Int.cast_sub]
  rcases H.crossingCompatible q with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;>
    · rw [h₁, h₂, h₃, h₄]
      ring

/-- Pairing `∂(∂D ∩ α)` with the sums of `E` over the corners along `α` cancels pairing
`∂(∂E ∩ β)` with the sums of `D` over the corners along `β`. Summation by parts along the curves
turns the two pairings into sums over the crossings of the two terms of `crossing_cancel`. -/
private theorem sum_arcBoundary_mul_add_sum_arcBoundary_mul [Fintype Point]
    (D E : Region → ℤ) :
    ∑ q, (H.alphaArcBoundary (H.alphaBoundary D) q : ℚ) *
        ((E (H.alphaLeft (H.alphaNext.symm q)) : ℚ) + E (H.alphaRight (H.alphaNext.symm q)) +
          E (H.alphaLeft q) + E (H.alphaRight q)) +
      ∑ q, (H.betaArcBoundary (H.betaBoundary E) q : ℚ) *
        ((D (H.betaLeft (H.betaNext.symm q)) : ℚ) + D (H.betaRight (H.betaNext.symm q)) +
          D (H.betaLeft q) + D (H.betaRight q)) = 0 := by
  -- Reindexing along the curves by the predecessor maps.
  have hα := Equiv.sum_comp H.alphaNext.symm fun q =>
    (H.alphaBoundary D q : ℚ) * (E (H.alphaLeft q) + E (H.alphaRight q))
  have hβ := Equiv.sum_comp H.betaNext.symm fun q =>
    (H.betaBoundary E q : ℚ) * (D (H.betaLeft q) + D (H.betaRight q))
  rw [← sum_add_distrib]
  calc _ = ∑ q, (2 * ((H.alphaBoundary D (H.alphaNext.symm q) : ℚ) *
          (E (H.alphaLeft (H.alphaNext.symm q)) + E (H.alphaRight (H.alphaNext.symm q))) -
            (H.alphaBoundary D q : ℚ) * (E (H.alphaLeft q) + E (H.alphaRight q))) +
        2 * ((H.betaBoundary E (H.betaNext.symm q) : ℚ) *
          (D (H.betaLeft (H.betaNext.symm q)) + D (H.betaRight (H.betaNext.symm q))) -
            (H.betaBoundary E q : ℚ) * (D (H.betaLeft q) + D (H.betaRight q)))) :=
        sum_congr rfl fun q _ => by
          simp only [alphaArcBoundary_apply, betaArcBoundary_apply, Int.cast_sub]
          linear_combination crossing_cancel D E q
    _ = 0 := by simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, hα, hβ, sub_self,
          mul_zero, add_zero]

variable {x y w : H.Generator} {D E : Region → ℤ}

/-- The point measures of two juxtaposable domains satisfy `n_x(E) + n_w(D) = n_y(D) + n_y(E)`
when `D` connects `x` to `y` and `E` connects `y` to `w`. -/
theorem IsDomainBetween.generatorPointMeasure_add_generatorPointMeasure
    (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween y w E) :
    H.generatorPointMeasure x E + H.generatorPointMeasure w D =
      H.generatorPointMeasure y D + H.generatorPointMeasure y E := by
  let _ : Fintype Point := H.pointFintype
  -- Along `α`: `n_y(E) - n_x(E)` pairs `∂(∂D ∩ α) = y - x` with the point measures of `E`.
  have hα : H.generatorPointMeasure y E - H.generatorPointMeasure x E =
      (∑ q, (H.alphaArcBoundary (H.alphaBoundary D) q : ℚ) *
        ((E (H.alphaLeft (H.alphaNext.symm q)) : ℚ) + E (H.alphaRight (H.alphaNext.symm q)) +
          E (H.alphaLeft q) + E (H.alphaRight q))) / 4 := by
    rw [generatorPointMeasure_eq_sum_generatorChain, generatorPointMeasure_eq_sum_generatorChain,
      ← sum_sub_distrib, (isDomainBetween_iff.mp hD).1, sum_div]
    refine sum_congr rfl fun q _ => ?_
    simp only [Pi.sub_apply, Int.cast_sub, pointMeasure_apply]
    ring
  -- Along `β`: `n_y(D) - n_w(D)` pairs `∂(∂E ∩ β) = y - w` with the point measures of `D`.
  have hβ : H.generatorPointMeasure y D - H.generatorPointMeasure w D =
      (∑ q, (H.betaArcBoundary (H.betaBoundary E) q : ℚ) *
        ((D (H.betaLeft (H.betaNext.symm q)) : ℚ) + D (H.betaRight (H.betaNext.symm q)) +
          D (H.betaLeft q) + D (H.betaRight q))) / 4 := by
    rw [generatorPointMeasure_eq_sum_generatorChain, generatorPointMeasure_eq_sum_generatorChain,
      ← sum_sub_distrib, (isDomainBetween_iff.mp hE).2, sum_div]
    refine sum_congr rfl fun q _ => ?_
    simp only [Pi.sub_apply, Int.cast_sub, pointMeasure_apply_beta]
    ring
  linarith [sum_arcBoundary_mul_add_sum_arcBoundary_mul (H := H) D E]

/-- A domain whose boundary is a sum of whole curves has the same point measure at any two
generators joined by a domain. -/
theorem IsDomainBetween.generatorPointMeasure_eq {P : Region → ℤ} (hD : H.IsDomainBetween x y D)
    (hP : H.IsDomainBetween y y P) :
    H.generatorPointMeasure x P = H.generatorPointMeasure y P := by
  have := hD.generatorPointMeasure_add_generatorPointMeasure hP
  linarith

end Additivity

section EulerMeasure

variable [Fintype Point] [DecidableEq Region]

/-- The number of corners of the region `r`, counted with multiplicity over the four corners at
every intersection point. -/
def cornerCount (r : Region) : ℕ :=
  #{c : Point × Fin 4 | H.cornerRegion c.1 c.2 = r}

theorem cornerCount_eq_card (r : Region) :
    H.cornerCount r = #{c : Point × Fin 4 | H.cornerRegion c.1 c.2 = r} :=
  (rfl)

variable [Fintype Region]

/-- The Euler measure `e(D) = ∑ D(R) (χ(R) - k(R) / 4)` of a domain, where `χ(R)` is the Euler
characteristic of the region `R`, supplied as `χ`, and `k(R)` is its number of corners. -/
def eulerMeasure (χ : Region → ℤ) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ r, (D r : ℚ) * (χ r - H.cornerCount r / 4)
  map_zero' := by simp
  map_add' D E := by simp [add_mul, sum_add_distrib]

@[simp]
theorem eulerMeasure_apply (χ : Region → ℤ) (D : Region → ℤ) :
    H.eulerMeasure χ D = ∑ r, (D r : ℚ) * (χ r - H.cornerCount r / 4) :=
  (rfl)

/-- The Euler measure of a single region `R` is `χ(R) - k(R) / 4`. -/
theorem eulerMeasure_single (χ : Region → ℤ) (r : Region) :
    H.eulerMeasure χ (Pi.single r 1) = χ r - H.cornerCount r / 4 := by
  simp [Pi.single_apply]

/-- Each corner contributes a quarter of the multiplicity at its region to the point measure at
its vertex, so the Euler measure is `∑ χ(R) D(R) - ∑ₚ n_p(D)`. -/
theorem eulerMeasure_eq_sub_sum_pointMeasure (χ : Region → ℤ) (D : Region → ℤ) :
    H.eulerMeasure χ D = ∑ r, (χ r : ℚ) * D r - ∑ p, H.pointMeasure D p := by
  have hcorner : ∑ r, (D r : ℚ) * H.cornerCount r =
      ∑ c : Point × Fin 4, (D (H.cornerRegion c.1 c.2) : ℚ) := by
    rw [← sum_fiberwise univ (fun c : Point × Fin 4 => H.cornerRegion c.1 c.2)]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_congr rfl fun c hc => by rw [(mem_filter.mp hc).2], sum_const, nsmul_eq_mul,
      cornerCount_eq_card, mul_comm]
  simp only [eulerMeasure_apply, pointMeasure_apply_eq_sum, mul_sub, sum_sub_distrib]
  rw [← sum_div, ← Fintype.sum_prod_type', ← hcorner, sum_div]
  congr 1
  · exact sum_congr rfl fun r _ => mul_comm _ _
  · exact sum_congr rfl fun r _ => by ring

/-- The combinatorial Maslov index `μ(D) = e(D) + n_x(D) + n_y(D)` of a domain `D` from the
generator `x` to the generator `y`, for the Euler characteristics `χ` of the regions. -/
def maslovIndex (χ : Region → ℤ) (x y : H.Generator) : (Region → ℤ) →+ ℚ :=
  H.eulerMeasure χ + H.generatorPointMeasure x + H.generatorPointMeasure y

@[simp]
theorem maslovIndex_apply (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    H.maslovIndex χ x y D =
      H.eulerMeasure χ D + H.generatorPointMeasure x D + H.generatorPointMeasure y D :=
  (rfl)

/-- Reversing a domain negates its Maslov index. -/
theorem maslovIndex_neg (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    H.maslovIndex χ y x (-D) = -H.maslovIndex χ x y D := by
  simp only [maslovIndex_apply, map_neg]
  ring

variable {H} {x y w : H.Generator} {D E : Region → ℤ}

/-- The Maslov index is additive under juxtaposition of domains: if `D` connects `x` to `y` and
`E` connects `y` to `w`, then `μ(D + E) = μ(D) + μ(E)`. -/
theorem IsDomainBetween.maslovIndex_add (χ : Region → ℤ) (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y w E) :
    H.maslovIndex χ x w (D + E) = H.maslovIndex χ x y D + H.maslovIndex χ y w E := by
  have := hD.generatorPointMeasure_add_generatorPointMeasure hE
  simp only [maslovIndex_apply, map_add]
  linarith

/-- A domain whose boundary is a sum of whole curves has the same Maslov index at any two
generators joined by a domain. -/
theorem IsDomainBetween.maslovIndex_self_eq (χ : Region → ℤ) {P : Region → ℤ}
    (hD : H.IsDomainBetween x y D) (hP : H.IsDomainBetween y y P) :
    H.maslovIndex χ x x P = H.maslovIndex χ y y P := by
  simp [hD.generatorPointMeasure_eq hP]

end EulerMeasure

end HeegaardRegionSystem

end TauCeti
