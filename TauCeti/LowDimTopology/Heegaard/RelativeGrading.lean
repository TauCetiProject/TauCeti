/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.MaslovIndex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The relative Maslov grading of generators

Let `(Σ, α, β, z)` be a pointed Heegaard diagram with `n` attaching curves of each kind and a
single basepoint `z`. The Heegaard Floer chain group `CF̂` is relatively graded: for generators
`x`, `y` joined by a domain `D`, the *relative Maslov grading* is

`gr(x, y) = μ(D) - 2 n_z(D)`,

where `μ` is the combinatorial Maslov index `TauCeti.HeegaardRegionSystem.maslovIndex` and
`n_z(D)` is the multiplicity of `D` at the basepoint. The hat differential counts holomorphic
disks of Maslov index one avoiding the basepoint, so it lowers `gr` by one.

Two domains from `x` to `y` differ by a domain from `x` to `x`. With a single basepoint, such a
domain is a periodic domain plus a multiple of the whole surface `Σ`, the domain `1`. The whole
surface has `n_z(Σ) = 1` and, when the Euler characteristics `χ` of the regions are those of the
regions of a closed surface of genus `n`, Maslov index `μ(Σ) = 2`. So it does not change `gr`,
while a periodic domain `P` changes it by `μ(P)`. Hence `gr` is well defined as soon as every
periodic domain has Maslov index zero at `x`. On a geometric diagram `μ(P)` is the evaluation of
the first Chern class of the spin^c structure of `x` on the homology class of `P`, so this holds
for the generators of a torsion spin^c structure, and in particular when `b₁(Y) = 0`, when the
only periodic domain is zero. Without it `gr` genuinely depends on the domain: for the
genus-one diagram of `S¹ × S²` with its basepoint in a bigon, the two bigons from `p₀` to `p₁`
give the values `-1` and `1`
(`TauCeti.HeegaardRegionSystem.maslovIndex_sub_two_mul_circleTimesSphere_one`).

The Euler characteristics are not determined by the incidence data, so they are an explicit
argument `χ`, normalized by `∑ χ(R) - #(α ∩ β) = 2 - 2n`. The left side is the Euler
characteristic of the surface assembled from the regions, the `2 #(α ∩ β)` arcs and the
intersection points, so this says that the surface has genus `n`, as for a pointed Heegaard
diagram.

## Main definitions

* `TauCeti.HeegaardRegionSystem.relativeGrading`: the relative grading `gr(x, y)`, computed from
  a chosen domain from `x` to `y`, or `0` when there is none.

## Main results

* `TauCeti.HeegaardRegionSystem.IsDomainBetween.maslovIndex_self_eq_two_mul`: a domain from `x`
  to `x` has Maslov index `2 n_z`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.maslovIndex_sub_two_mul_eq`: `μ(D) - 2 n_z(D)` is
  the same for all domains `D` from `x` to `y`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_eq`: the relative grading is
  `μ(D) - 2 n_z(D)` for every domain `D` from `x` to `y`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_add`:
  `gr(x, y) + gr(y, w) = gr(x, w)`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_swap`: `gr(y, x) = -gr(x, y)`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206): the relative grading
  `gr(x, y) = μ(φ) - 2 n_z(φ)`, the class of the whole surface with Maslov index two and basepoint
  multiplicity one, and the evaluation of the first Chern class as the Maslov index of a periodic
  domain.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, for the index formula
  `μ(D) = e(D) + n_x(D) + n_y(D)`.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

open scoped Classical in
variable (H) in
/-- The relative Maslov grading `gr(x, y) = μ(D) - 2 n_z(D)` of two generators, for a chosen
domain `D` from `x` to `y`, or `0` when no domain joins them. When the periodic domains have
Maslov index zero, the value does not depend on the choice of `D`
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_eq`). -/
noncomputable def relativeGrading (χ : Region → ℤ) (z : Basepoint) (x y : H.Generator) : ℚ :=
  if h : ∃ D, H.IsDomainBetween x y D then
    H.maslovIndex χ x y h.choose - 2 * h.choose (H.basepoint z)
  else 0

variable [Subsingleton Basepoint] {χ : Region → ℤ} (z : Basepoint)
  (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ)) {x y w : H.Generator}
  {D D' E : Region → ℤ}

include hχ

/-- In a singly pointed diagram of a closed surface of genus `n` all of whose periodic domains
have Maslov index zero at `x`, a domain `E` from `x` to `x` has Maslov index `2 n_z(E)`: it is a
periodic domain plus `n_z(E)` copies of the whole surface. -/
theorem IsDomainBetween.maslovIndex_self_eq_two_mul
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E = 2 * E (H.basepoint z) := by
  have hper := hP _ ((isDomainBetween_self_iff_sub_smul_one_mem_periodicDomains z).mp hE)
  rw [map_sub, map_zsmul, maslovIndex_one_eq_two hχ, zsmul_eq_mul, sub_eq_zero] at hper
  rw [hper]
  ring

/-- In a singly pointed diagram of a closed surface of genus `n` all of whose periodic domains
have Maslov index zero at `x`, the quantity `μ(D) - 2 n_z(D)` is the same for all domains `D`
from `x` to `y`. -/
theorem IsDomainBetween.maslovIndex_sub_two_mul_eq
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D)
    (hD' : H.IsDomainBetween x y D') :
    H.maslovIndex χ x y D - 2 * D (H.basepoint z) =
      H.maslovIndex χ x y D' - 2 * D' (H.basepoint z) := by
  -- `D' - D` runs from `x` to `x`, so its Maslov index is twice its basepoint multiplicity.
  have hE := (hD'.add hD.neg).maslovIndex_self_eq_two_mul z hχ hP
  rw [hD'.maslovIndex_add χ hD.neg, maslovIndex_neg] at hE
  push_cast [Pi.add_apply, Pi.neg_apply] at hE
  linarith

omit hχ [Subsingleton Basepoint] in
/-- When no domain joins `x` to `y`, the relative grading is `0`. -/
theorem relativeGrading_of_forall_not_isDomainBetween
    (h : ∀ D, ¬H.IsDomainBetween x y D) : H.relativeGrading χ z x y = 0 := by
  rw [relativeGrading, dite_eq_right (not_exists.mpr h)]

/-- The relative grading is `μ(D) - 2 n_z(D)` for every domain `D` from `x` to `y`, when the
periodic domains have Maslov index zero at `x`. -/
theorem IsDomainBetween.relativeGrading_eq
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D) :
    H.relativeGrading χ z x y = H.maslovIndex χ x y D - 2 * D (H.basepoint z) := by
  have h : ∃ D, H.IsDomainBetween x y D := ⟨D, hD⟩
  rw [relativeGrading, dite_eq_left h]
  exact h.choose_spec.maslovIndex_sub_two_mul_eq z hχ hP hD

/-- A generator has relative grading zero with itself. -/
theorem relativeGrading_self (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) :
    H.relativeGrading χ z x x = 0 := by
  simp [(isDomainBetween_zero x).relativeGrading_eq z hχ hP]

/-- The relative grading is additive: `gr(x, y) + gr(y, w) = gr(x, w)` for generators joined by
domains, when the periodic domains have Maslov index zero at `x`. -/
theorem IsDomainBetween.relativeGrading_add
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y w E) :
    H.relativeGrading χ z x y + H.relativeGrading χ z y w = H.relativeGrading χ z x w := by
  rw [hD.relativeGrading_eq z hχ hP,
    hE.relativeGrading_eq z hχ (hD.forall_mem_periodicDomains_maslovIndex_eq_zero χ hP),
    (hD.add hE).relativeGrading_eq z hχ hP, hD.maslovIndex_add χ hE, Pi.add_apply, Int.cast_add]
  ring

/-- The relative grading is antisymmetric: `gr(y, x) = -gr(x, y)` for generators joined by a
domain, when the periodic domains have Maslov index zero at `x`. -/
theorem IsDomainBetween.relativeGrading_swap
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D) :
    H.relativeGrading χ z y x = -H.relativeGrading χ z x y := by
  rw [hD.relativeGrading_eq z hχ hP,
    hD.neg.relativeGrading_eq z hχ (hD.forall_mem_periodicDomains_maslovIndex_eq_zero χ hP),
    maslovIndex_neg, Pi.neg_apply, Int.cast_neg]
  ring

end HeegaardRegionSystem

end TauCeti
