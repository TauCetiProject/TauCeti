/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.InformationTheory.Hamming
public import TauCeti.LowDimTopology.Heegaard.Domain
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# The combinatorial Maslov index of a domain

Lipshitz's index formula computes the expected dimension of the moduli space of holomorphic
disks in a Whitney class `φ` from its domain `D` alone:
`μ(φ) = e(D) + n_x(D) + n_y(D)`. This file defines the right-hand side for the abstract region
incidence data `TauCeti.HeegaardRegionSystem` and proves that it is additive under juxtaposition
of domains. In a singly pointed diagram satisfying the Euler normalization, this additivity,
the Maslov index two of the whole surface, and vanishing Maslov index on periodic domains make
the relative grading `μ(D) - 2 n_z(D)` independent of the choice of domain
(`TauCeti.LowDimTopology.Heegaard.RelativeGrading`).

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

For a nonnegative domain `D` from `x` to `y`, the points of `x` and of `y` on each of the `m`
`α`-curves where they differ are corners of `D`, so each has point measure at least `1 / 4`, and
`μ(D) ≥ e(D) + m / 2`. When this estimate is an equality, `D` has point measure exactly `1 / 4`
at these `2 m` points and point measure zero at the common points of `x` and `y`. Point measure
`1 / 4` at the point of `x` (or of `y`) on such a curve says that `D` is a convex corner there:
multiplicity one in a single quadrant, on one of the two sides allowed by the corner condition,
and zero in the three others. Point measure zero says that `D` vanishes on all four corners. In
a nice diagram these are the local shapes of the empty bigons and rectangles counted by the hat
differential (`TauCeti.LowDimTopology.Heegaard.Nice`).

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
* `sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_zero`:
  pairing `∂(∂D ∩ α)` with the point measures of `E` cancels pairing `∂(∂E ∩ β)` with those of `D`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.generatorPointMeasure_add_generatorPointMeasure`:
  `n_x(E) + n_w(D) = n_y(D) + n_y(E)` for `D` from `x` to `y` and `E` from `y` to `w`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.maslovIndex_add`: the Maslov index is additive
  under juxtaposition.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.maslovIndex_self_eq`: a domain whose boundary is
  a sum of whole curves has the same Maslov index at any two generators joined by a domain.
* `TauCeti.HeegaardRegionSystem.maslovIndex_one`: the Maslov index of the whole surface is
  `∑ χ(R) - #(α ∩ β) + 2n`, so it is two for a closed surface of genus `n`
  (`TauCeti.HeegaardRegionSystem.maslovIndex_one_eq_two`).
* `TauCeti.HeegaardRegionSystem.maslovIndex_mem_zmultiples_inv_four`: every Maslov index is an
  integer multiple of `1 / 4`, since every corner contributes a quarter.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.eulerMeasure_add_half_hammingDist_le_maslovIndex`:
  a nonnegative domain from `x` to `y` has a corner at the points of `x` and of `y` on every
  `α`-curve where they differ, so its Maslov index is at least its Euler measure plus half the
  number of such curves.
* `TauCeti.HeegaardRegionSystem.pointMeasure_eq_zero_iff`: a nonnegative domain has point measure
  zero at `p` exactly when it vanishes at the four corners at `p`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_left_eq_inv_four_iff` and
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_right_eq_inv_four_iff`: a
  moved point has point measure `1 / 4` exactly when the domain is a convex corner there.
* `IsDomainBetween.pointMeasure_point_left_eq_inv_four_of_maslovIndex_le`,
  `IsDomainBetween.pointMeasure_point_right_eq_inv_four_of_maslovIndex_le`
  and `TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_eq_zero_of_maslovIndex_le`:
  the equality case of the index estimate.

## References

* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, where the index formula
  and its additivity are proved; see also the erratum
  [arXiv:1301.4919](https://arxiv.org/abs/1301.4919).
* S. Sarkar, *Maslov index formulas for Whitney n-gons*, J. Topol. **4** (2011),
  [arXiv:math/0609673](https://arxiv.org/abs/math/0609673), for the combinatorial proof of the
  additivity of point measures.
* S. Sarkar and J. Wang, *An algorithm for computing some Heegaard Floer homologies*, Ann. of
  Math. **171** (2010), [arXiv:math/0607777](https://arxiv.org/abs/math/0607777), §3, for the
  index estimate `μ(D) ≥ e(D) + m / 2` and its equality case.
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
  congr 1
  norm_cast
  linear_combination (H.crossingCompatible p).corner_sum_eq D

/-- Every point measure is an integer multiple of `1 / 4`. -/
theorem pointMeasure_apply_mem_zmultiples_inv_four (D : Region → ℤ) (p : Point) :
    H.pointMeasure D p ∈ AddSubgroup.zmultiples (4⁻¹ : ℚ) :=
  AddSubgroup.mem_zmultiples_iff.mpr ⟨∑ i, D (H.cornerRegion p i), by
    rw [pointMeasure_apply_eq_sum, zsmul_eq_mul, div_eq_mul_inv, Int.cast_sum]⟩

/-- The point measure `n_x(D) = ∑ᵢ n_{xᵢ}(D)` of a domain `D` at a generator `x`. -/
def generatorPointMeasure (x : H.Generator) : (Region → ℤ) →+ ℚ where
  toFun D := ∑ i, H.pointMeasure D (H.point x i)
  map_zero' := by simp
  map_add' D E := by simp only [map_add, Pi.add_apply, sum_add_distrib]

@[simp]
theorem generatorPointMeasure_apply (x : H.Generator) (D : Region → ℤ) :
    H.generatorPointMeasure x D = ∑ i, H.pointMeasure D (H.point x i) :=
  (rfl)

/-- The whole surface has multiplicity one at all four corners of every point. -/
@[simp]
theorem pointMeasure_one : H.pointMeasure 1 = 1 := by
  ext p
  simp only [pointMeasure_apply, Pi.one_apply, Int.cast_one]
  norm_num

/-- The point measure of the whole surface at a generator is the number of its points. -/
theorem generatorPointMeasure_one (x : H.Generator) : H.generatorPointMeasure x 1 = n := by
  simp only [generatorPointMeasure_apply, pointMeasure_one, Pi.one_apply, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The point measure of a generator is the pairing of its `0`-chain with the point
measures. -/
theorem generatorPointMeasure_eq_sum_generatorChain [Fintype Point] (x : H.Generator)
    (D : Region → ℤ) :
    H.generatorPointMeasure x D = ∑ q, (H.generatorChain x q : ℚ) * H.pointMeasure D q := by
  exact (H.sum_generatorChain_mul x (H.pointMeasure D)).symm

end PointMeasure

section Additivity

variable {H}

/-- At every crossing, the local intersection number of `∂D ∩ α` with `∂E ∩ β` cancels that of
`∂E ∩ β` with `∂D ∩ α`, by `IsCrossingCompatible.cross_add_cross_eq_zero`, so their sums over the
crossings cancel too. -/
private theorem sum_cross_add_sum_cross_eq_zero [Fintype Point] (D E : Region → ℤ) :
    ∑ q, (D (H.alphaLeft (H.alphaNext.symm q)) - D (H.alphaRight (H.alphaNext.symm q)) +
          (D (H.alphaLeft q) - D (H.alphaRight q))) *
        (E (H.alphaLeft q) + E (H.alphaRight q) -
          (E (H.alphaLeft (H.alphaNext.symm q)) + E (H.alphaRight (H.alphaNext.symm q)))) +
      ∑ q, (E (H.betaLeft (H.betaNext.symm q)) - E (H.betaRight (H.betaNext.symm q)) +
          (E (H.betaLeft q) - E (H.betaRight q))) *
        (D (H.betaLeft q) + D (H.betaRight q) -
          (D (H.betaLeft (H.betaNext.symm q)) + D (H.betaRight (H.betaNext.symm q)))) = 0 := by
  rw [← sum_add_distrib]
  exact sum_eq_zero fun q _ => (H.crossingCompatible q).cross_add_cross_eq_zero D E

variable (H) in
/-- Reciprocity of point measures: for any two domains `D` and `E`, pairing `∂(∂D ∩ α)` with the
point measures of `E` and `∂(∂E ∩ β)` with those of `D` gives opposite values. Both pairings are a
corner-averaged intersection number of `∂D ∩ α` with `∂E ∩ β`, computed once along the `α`-curves
and once along the `β`-curves. -/
theorem sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_zero
    [Fintype Point] (D E : Region → ℤ) :
    ∑ q, (H.alphaArcBoundary (H.alphaBoundary D) q : ℚ) * H.pointMeasure E q +
      ∑ q, (H.betaArcBoundary (H.betaBoundary E) q : ℚ) * H.pointMeasure D q = 0 := by
  rw [sum_mul_cornerSum_div_four H.alphaNext H.alphaLeft H.alphaRight D E _ _
      (fun q => by simp only [alphaArcBoundary_apply, alphaBoundary_apply])
      (fun q => by rw [pointMeasure_apply]; push_cast; ring),
    sum_mul_cornerSum_div_four H.betaNext H.betaLeft H.betaRight E D _ _
      (fun q => by simp only [betaArcBoundary_apply, betaBoundary_apply])
      (fun q => by rw [pointMeasure_apply_beta]; push_cast; ring),
    ← add_div, ← Int.cast_add, sum_cross_add_sum_cross_eq_zero, Int.cast_zero, zero_div]

variable {x y w : H.Generator} {D E : Region → ℤ}

/-- The point measures of two juxtaposable domains satisfy `n_x(E) + n_w(D) = n_y(D) + n_y(E)`
when `D` connects `x` to `y` and `E` connects `y` to `w`. -/
theorem IsDomainBetween.generatorPointMeasure_add_generatorPointMeasure
    (hD : H.IsDomainBetween x y D) (hE : H.IsDomainBetween y w E) :
    H.generatorPointMeasure x E + H.generatorPointMeasure w D =
      H.generatorPointMeasure y D + H.generatorPointMeasure y E := by
  let _ : Fintype Point := H.pointFintype
  -- `∂(∂D ∩ α) = y - x` and `∂(∂E ∩ β) = y - w`, so the pairings are `n_y(E) - n_x(E)` and
  -- `n_y(D) - n_w(D)`.
  have h :=
    H.sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_zero D E
  rw [(isDomainBetween_iff.mp hD).1, (isDomainBetween_iff.mp hE).2] at h
  simp only [Pi.sub_apply, Int.cast_sub, sub_mul, sum_sub_distrib,
    ← generatorPointMeasure_eq_sum_generatorChain] at h
  linarith

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
    simp_rw [cornerCount_eq_card, mul_comm (D _ : ℚ), ← nsmul_eq_mul]
    exact sum_card_filter_nsmul_eq_sum_comp (fun _ _ => mem_univ _) _
  simp only [eulerMeasure_apply, pointMeasure_apply_eq_sum, mul_sub, sum_sub_distrib]
  rw [← sum_div, ← Fintype.sum_prod_type', ← hcorner, sum_div]
  congr 1
  · exact sum_congr rfl fun r _ => mul_comm _ _
  · exact sum_congr rfl fun r _ => by ring

/-- The Euler measure of the whole surface is `∑ χ(R) - #(α ∩ β)`, the Euler characteristic of
the surface assembled from the regions, the arcs and the intersection points. -/
theorem eulerMeasure_one (χ : Region → ℤ) :
    H.eulerMeasure χ 1 = ∑ r, (χ r : ℚ) - Fintype.card Point := by
  simp only [eulerMeasure_eq_sub_sum_pointMeasure, pointMeasure_one, Pi.one_apply, Int.cast_one,
    mul_one, sum_const, card_univ, nsmul_eq_mul]

/-- The combinatorial Maslov index `μ(D) = e(D) + n_x(D) + n_y(D)` of a domain `D` from the
generator `x` to the generator `y`, for the Euler characteristics `χ` of the regions. -/
def maslovIndex (χ : Region → ℤ) (x y : H.Generator) : (Region → ℤ) →+ ℚ :=
  H.eulerMeasure χ + H.generatorPointMeasure x + H.generatorPointMeasure y

@[simp]
theorem maslovIndex_apply (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    H.maslovIndex χ x y D =
      H.eulerMeasure χ D + H.generatorPointMeasure x D + H.generatorPointMeasure y D :=
  (rfl)

/-- The Maslov index of the whole surface is `∑ χ(R) - #(α ∩ β) + 2n`, at any two generators. -/
theorem maslovIndex_one (χ : Region → ℤ) (x y : H.Generator) :
    H.maslovIndex χ x y 1 = ∑ r, (χ r : ℚ) - Fintype.card Point + 2 * n := by
  rw [maslovIndex_apply, eulerMeasure_one, generatorPointMeasure_one, generatorPointMeasure_one]
  ring

/-- The Maslov index does not involve the basepoints. -/
@[simp]
theorem maslovIndex_withBasepoints {B : Type*} (b : B → Region) (χ : Region → ℤ)
    (x y : H.Generator) : (H.withBasepoints b).maslovIndex χ x y = H.maslovIndex χ x y :=
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

/-- If every periodic domain has Maslov index zero at `x`, then the same holds at every generator
`y` joined to `x` by a domain. -/
theorem IsDomainBetween.forall_mem_periodicDomains_maslovIndex_eq_zero (χ : Region → ℤ)
    (hD : H.IsDomainBetween x y D) (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) :
    ∀ P ∈ H.periodicDomains, H.maslovIndex χ y y P = 0 := fun P hPmem => by
  rw [← hD.maslovIndex_self_eq χ (isDomainBetween_self_iff.mpr hPmem).1, hP P hPmem]

/-- When the region Euler characteristics `χ` are those of a closed surface of genus `n`, that is
`∑ χ(R) - #(α ∩ β) = 2 - 2n`, the whole surface has Maslov index two. -/
theorem maslovIndex_one_eq_two {χ : Region → ℤ}
    (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) (x y : H.Generator) :
    H.maslovIndex χ x y 1 = 2 := by
  have hχ' : ∑ r, (χ r : ℚ) - Fintype.card Point = 2 - 2 * n := by exact_mod_cast hχ
  rw [maslovIndex_one]
  linarith

variable (H) in
/-- Every Euler measure is an integer multiple of `1 / 4`. -/
theorem eulerMeasure_mem_zmultiples_inv_four (χ : Region → ℤ) (D : Region → ℤ) :
    H.eulerMeasure χ D ∈ AddSubgroup.zmultiples (4⁻¹ : ℚ) :=
  AddSubgroup.mem_zmultiples_iff.mpr ⟨∑ r, D r * (4 * χ r - H.cornerCount r), by
    rw [eulerMeasure_apply, zsmul_eq_mul]
    push_cast
    rw [sum_mul]
    exact sum_congr rfl fun r _ => by ring⟩

variable (H) in
/-- Every combinatorial Maslov index is an integer multiple of `1 / 4`. -/
theorem maslovIndex_mem_zmultiples_inv_four (χ : Region → ℤ) (x y : H.Generator)
    (D : Region → ℤ) : H.maslovIndex χ x y D ∈ AddSubgroup.zmultiples (4⁻¹ : ℚ) := by
  rw [maslovIndex_apply, generatorPointMeasure_apply, generatorPointMeasure_apply]
  exact add_mem (add_mem (H.eulerMeasure_mem_zmultiples_inv_four χ D)
    (sum_mem fun i _ => H.pointMeasure_apply_mem_zmultiples_inv_four D _))
    (sum_mem fun i _ => H.pointMeasure_apply_mem_zmultiples_inv_four D _)

end EulerMeasure

section NonnegDomain

variable {H} {x y : H.Generator} {D : Region → ℤ}

variable (H) in
/-- At an intersection point, the boundary of the `α`-part of a nonnegative domain is bounded by
the sum of the multiplicities at the four corners there, that is, by four times the point
measure. -/
theorem abs_alphaArcBoundary_alphaBoundary_le_four_mul_pointMeasure (hD : 0 ≤ D) (p : Point) :
    |(H.alphaArcBoundary (H.alphaBoundary D) p : ℚ)| ≤ 4 * H.pointMeasure D p := by
  have h₁ : (0 : ℚ) ≤ D (H.alphaLeft (H.alphaNext.symm p)) := by exact_mod_cast hD _
  have h₂ : (0 : ℚ) ≤ D (H.alphaRight (H.alphaNext.symm p)) := by exact_mod_cast hD _
  have h₃ : (0 : ℚ) ≤ D (H.alphaLeft p) := by exact_mod_cast hD _
  have h₄ : (0 : ℚ) ≤ D (H.alphaRight p) := by exact_mod_cast hD _
  simp only [alphaArcBoundary_apply, alphaBoundary_apply, pointMeasure_apply, Int.cast_sub]
  rw [abs_le]
  constructor <;> linarith

variable (H) in
/-- The point measure of a nonnegative domain is nonnegative. -/
theorem pointMeasure_nonneg (hD : 0 ≤ D) (p : Point) : 0 ≤ H.pointMeasure D p := by
  have := H.abs_alphaArcBoundary_alphaBoundary_le_four_mul_pointMeasure hD p
  linarith [abs_nonneg (H.alphaArcBoundary (H.alphaBoundary D) p : ℚ)]

variable (H) in
/-- The point measure of a nonnegative domain at a generator is nonnegative. -/
theorem generatorPointMeasure_nonneg (hD : 0 ≤ D) (x : H.Generator) :
    0 ≤ H.generatorPointMeasure x D := by
  rw [generatorPointMeasure_apply]
  exact sum_nonneg fun i _ => H.pointMeasure_nonneg hD _

variable (H) in
/-- A nonnegative domain has point measure zero at `p` exactly when it has multiplicity zero at
the four corners at `p`. -/
theorem pointMeasure_eq_zero_iff (hD : 0 ≤ D) (p : Point) :
    H.pointMeasure D p = 0 ↔ ∀ k, D (H.cornerRegion p k) = 0 := by
  have h := sum_eq_zero_iff_of_nonneg (s := univ) (f := fun k => (D (H.cornerRegion p k) : ℚ))
    fun k _ => by exact_mod_cast hD _
  rw [pointMeasure_apply_eq_sum, div_eq_zero_iff, or_iff_left (by norm_num), h]
  simp

/-- For a nonnegative domain `D` from `x` to `y`, the point of `x` on an `α`-curve where `x` and
`y` differ has point measure at least `1 / 4`. -/
theorem IsDomainBetween.inv_four_le_pointMeasure_point_left (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D) {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    4⁻¹ ≤ H.pointMeasure D (H.point x i) := by
  have := H.abs_alphaArcBoundary_alphaBoundary_le_four_mul_pointMeasure hD0 (H.point x i)
  rw [hD.alphaArcBoundary_alphaBoundary_point_left hi, Int.cast_neg, Int.cast_one, abs_neg,
    abs_one] at this
  linarith

/-- For a nonnegative domain `D` from `x` to `y`, the point of `y` on an `α`-curve where `x` and
`y` differ has point measure at least `1 / 4`. -/
theorem IsDomainBetween.inv_four_le_pointMeasure_point_right (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D) {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    4⁻¹ ≤ H.pointMeasure D (H.point y i) := by
  have := H.abs_alphaArcBoundary_alphaBoundary_le_four_mul_pointMeasure hD0 (H.point y i)
  rw [hD.alphaArcBoundary_alphaBoundary_point_right hi, Int.cast_one, abs_one] at this
  linarith

/-- The arithmetic of a convex corner: if four corners of a nonnegative domain `D` at `p`, listed
as `a`, `b`, `c`, `d`, satisfy `D a - D b - D c + D d = -1`, then `D` has point measure `1 / 4` at
`p` exactly when it vanishes at `a` and `d` and has total multiplicity one at `b` and `c`. -/
private theorem pointMeasure_eq_inv_four_iff_of_corners (hD0 : 0 ≤ D) {p : Point}
    {a b c d : Region} (hp : H.pointMeasure D p = ((D a : ℚ) + D b + D c + D d) / 4)
    (hb : D a - D b - D c + D d = -1) :
    H.pointMeasure D p = 4⁻¹ ↔ D a = 0 ∧ D d = 0 ∧ D b + D c = 1 := by
  have h₁ := hD0 a
  have h₂ := hD0 b
  have h₃ := hD0 c
  have h₄ := hD0 d
  simp only [Pi.zero_apply] at h₁ h₂ h₃ h₄
  rw [hp, div_eq_iff (by norm_num), inv_mul_cancel₀ (by norm_num)]
  norm_cast
  omega

/-- **Convex corners at `x`.** Let `D` be a nonnegative domain from `x` to `y` and `p` the point
of `x` on an `α`-curve where `x` and `y` differ. Then `D` has the minimal point measure `1 / 4`
at `p` exactly when it has multiplicity one in a single quadrant at `p`, which is either the
region to the right of the `α`-arc ending at `p` or the region to the left of the `α`-arc
starting at `p`, and multiplicity zero in the three other quadrants. -/
theorem IsDomainBetween.pointMeasure_point_left_eq_inv_four_iff (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D) {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    H.pointMeasure D (H.point x i) = 4⁻¹ ↔
      D (H.alphaLeft (H.alphaNext.symm (H.point x i))) = 0 ∧
        D (H.alphaRight (H.point x i)) = 0 ∧
          D (H.alphaRight (H.alphaNext.symm (H.point x i))) + D (H.alphaLeft (H.point x i)) =
            1 := by
  have h := hD.alphaArcBoundary_alphaBoundary_point_left hi
  simp only [alphaArcBoundary_apply, alphaBoundary_apply] at h
  exact pointMeasure_eq_inv_four_iff_of_corners hD0 (by rw [pointMeasure_apply])
    (by omega)

/-- **Convex corners at `y`.** Let `D` be a nonnegative domain from `x` to `y` and `q` the point
of `y` on an `α`-curve where `x` and `y` differ. Then `D` has the minimal point measure `1 / 4`
at `q` exactly when it has multiplicity one in a single quadrant at `q`, which is either the
region to the left of the `α`-arc ending at `q` or the region to the right of the `α`-arc
starting at `q`, and multiplicity zero in the three other quadrants. -/
theorem IsDomainBetween.pointMeasure_point_right_eq_inv_four_iff (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D) {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    H.pointMeasure D (H.point y i) = 4⁻¹ ↔
      D (H.alphaRight (H.alphaNext.symm (H.point y i))) = 0 ∧
        D (H.alphaLeft (H.point y i)) = 0 ∧
          D (H.alphaLeft (H.alphaNext.symm (H.point y i))) + D (H.alphaRight (H.point y i)) =
            1 := by
  have h := hD.alphaArcBoundary_alphaBoundary_point_right hi
  simp only [alphaArcBoundary_apply, alphaBoundary_apply] at h
  exact pointMeasure_eq_inv_four_iff_of_corners hD0 (by rw [pointMeasure_apply]; ring)
    (by omega)

variable [DecidableEq Point]

/-- If a nonnegative domain `D` has point measure at least `1 / 4` at the point of `w` on every
`α`-curve where `x` and `y` differ, then each such curve contributes at least `1 / 4` to
`n_w(D)`. -/
private theorem hammingDist_le_four_mul_generatorPointMeasure_of_inv_four_le (hD0 : 0 ≤ D)
    (w : H.Generator)
    (hw : ∀ i, H.point x i ≠ H.point y i → 4⁻¹ ≤ H.pointMeasure D (H.point w i)) :
    (hammingDist (H.point x) (H.point y) : ℚ) ≤ 4 * H.generatorPointMeasure w D := by
  rw [hammingDist, generatorPointMeasure_apply, mul_sum, card_filter, Nat.cast_sum]
  refine sum_le_sum fun i _ => ?_
  split_ifs with hi
  · push_cast
    linarith [hw i hi]
  · simpa using H.pointMeasure_nonneg hD0 (H.point w i)

/-- For a nonnegative domain `D` from `x` to `y`, every `α`-curve on which `x` and `y` differ
contributes at least `1 / 4` to `n_x(D)`. -/
theorem IsDomainBetween.hammingDist_le_four_mul_generatorPointMeasure_left
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) :
    (hammingDist (H.point x) (H.point y) : ℚ) ≤ 4 * H.generatorPointMeasure x D :=
  hammingDist_le_four_mul_generatorPointMeasure_of_inv_four_le hD0 x fun _ hi =>
    hD.inv_four_le_pointMeasure_point_left hD0 hi

/-- For a nonnegative domain `D` from `x` to `y`, every `α`-curve on which `x` and `y` differ
contributes at least `1 / 4` to `n_y(D)`. -/
theorem IsDomainBetween.hammingDist_le_four_mul_generatorPointMeasure_right
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) :
    (hammingDist (H.point x) (H.point y) : ℚ) ≤ 4 * H.generatorPointMeasure y D :=
  hammingDist_le_four_mul_generatorPointMeasure_of_inv_four_le hD0 y fun _ hi =>
    hD.inv_four_le_pointMeasure_point_right hD0 hi

/-- The excess `n_{xᵢ}(D) + n_{yᵢ}(D) - 1 / 2` of the point measures on an `α`-curve where `x`
and `y` differ over the two corners forced there, and `n_{xᵢ}(D) + n_{yᵢ}(D)` on a curve where
they agree, is nonnegative. -/
private theorem IsDomainBetween.excess_nonneg (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D)
    (i : Fin n) :
    0 ≤ H.pointMeasure D (H.point x i) + H.pointMeasure D (H.point y i) -
      if H.point x i = H.point y i then 0 else 2⁻¹ := by
  split_ifs with hi
  · linarith [H.pointMeasure_nonneg hD0 (H.point x i), H.pointMeasure_nonneg hD0 (H.point y i)]
  · linarith [hD.inv_four_le_pointMeasure_point_left hD0 hi,
      hD.inv_four_le_pointMeasure_point_right hD0 hi]

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

/-- The Maslov index of a nonnegative domain from `x` to `y` is at least its Euler measure plus
half the number of `α`-curves on which `x` and `y` differ. -/
theorem IsDomainBetween.eulerMeasure_add_half_hammingDist_le_maslovIndex (χ : Region → ℤ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) :
    H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2 ≤ H.maslovIndex χ x y D := by
  have hx := hD.hammingDist_le_four_mul_generatorPointMeasure_left hD0
  have hy := hD.hammingDist_le_four_mul_generatorPointMeasure_right hD0
  rw [maslovIndex_apply]
  linarith

/-! ### The equality case of the index estimate -/

/-- The excesses of the point measures add up to the gap
`μ(D) - e(D) - m / 2` in the index estimate. -/
private theorem sum_excess_eq (χ : Region → ℤ) :
    ∑ i, (H.pointMeasure D (H.point x i) + H.pointMeasure D (H.point y i) -
        if H.point x i = H.point y i then 0 else 2⁻¹) =
      H.maslovIndex χ x y D - H.eulerMeasure χ D -
        hammingDist (H.point x) (H.point y) / 2 := by
  simp only [sum_sub_distrib, sum_add_distrib, sum_ite, sum_const_zero, sum_const,
    nsmul_eq_mul, maslovIndex_apply, generatorPointMeasure_apply, hammingDist]
  ring

/-- When the index estimate is an equality, every excess of the point measures vanishes. -/
private theorem IsDomainBetween.excess_eq_zero (χ : Region → ℤ) (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D)
    (hμ : H.maslovIndex χ x y D ≤ H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2)
    (i : Fin n) :
    H.pointMeasure D (H.point x i) + H.pointMeasure D (H.point y i) =
      if H.point x i = H.point y i then 0 else 2⁻¹ := by
  have hsum := sum_excess_eq (H := H) (x := x) (y := y) (D := D) χ
  have h0 := (sum_eq_zero_iff_of_nonneg fun i _ => hD.excess_nonneg hD0 i).mp
    (le_antisymm (by linarith) (sum_nonneg fun i _ => hD.excess_nonneg hD0 i)) i (mem_univ i)
  linarith

/-- **The equality case of the index estimate, at `x`.** If the Maslov index of a nonnegative
domain `D` from `x` to `y` is at most `e(D) + m / 2`, where `m` is the number of `α`-curves on
which `x` and `y` differ, then `D` has point measure exactly `1 / 4` at the point of `x` on each
such curve: it is a convex corner there
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_left_eq_inv_four_iff`). -/
theorem IsDomainBetween.pointMeasure_point_left_eq_inv_four_of_maslovIndex_le (χ : Region → ℤ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D)
    (hμ : H.maslovIndex χ x y D ≤ H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2)
    {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    H.pointMeasure D (H.point x i) = 4⁻¹ := by
  have h := hD.excess_eq_zero χ hD0 hμ i
  simp only [hi, ↓reduceIte] at h
  linarith [hD.inv_four_le_pointMeasure_point_left hD0 hi,
    hD.inv_four_le_pointMeasure_point_right hD0 hi]

/-- **The equality case of the index estimate, at `y`.** If the Maslov index of a nonnegative
domain `D` from `x` to `y` is at most `e(D) + m / 2`, where `m` is the number of `α`-curves on
which `x` and `y` differ, then `D` has point measure exactly `1 / 4` at the point of `y` on each
such curve: it is a convex corner there
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_right_eq_inv_four_iff`). -/
theorem IsDomainBetween.pointMeasure_point_right_eq_inv_four_of_maslovIndex_le (χ : Region → ℤ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D)
    (hμ : H.maslovIndex χ x y D ≤ H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2)
    {i : Fin n} (hi : H.point x i ≠ H.point y i) :
    H.pointMeasure D (H.point y i) = 4⁻¹ := by
  have h := hD.excess_eq_zero χ hD0 hμ i
  simp only [hi, ↓reduceIte] at h
  linarith [hD.inv_four_le_pointMeasure_point_left hD0 hi,
    hD.inv_four_le_pointMeasure_point_right hD0 hi]

/-- **The equality case of the index estimate, at the fixed points.** If the Maslov index of a
nonnegative domain `D` from `x` to `y` is at most `e(D) + m / 2`, where `m` is the number of
`α`-curves on which `x` and `y` differ, then `D` has point measure zero, so multiplicity zero at
all four corners (`TauCeti.HeegaardRegionSystem.pointMeasure_eq_zero_iff`), at the common point
of `x` and `y` on every other `α`-curve: no such point lies in the closure of the support
of `D`. -/
theorem IsDomainBetween.pointMeasure_point_eq_zero_of_maslovIndex_le (χ : Region → ℤ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D)
    (hμ : H.maslovIndex χ x y D ≤ H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2)
    {i : Fin n} (hi : H.point x i = H.point y i) :
    H.pointMeasure D (H.point x i) = 0 := by
  have h := hD.excess_eq_zero χ hD0 hμ i
  rw [← hi] at h
  simp only [↓reduceIte] at h
  linarith

end NonnegDomain

end HeegaardRegionSystem

end TauCeti
