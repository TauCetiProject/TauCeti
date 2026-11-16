/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.RelativeGrading
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# The relative Maslov grading of a multipointed Heegaard diagram

A *balanced* multipointed Heegaard diagram `(Σ, α, β, z₁, …, z_b)` of a closed `3`-manifold has
`n = g + b - 1` attaching curves of each kind on a surface of genus `g`, and each component of
`Σ - α` (and of `Σ - β`) contains exactly one basepoint: compressing `Σ` along the `α`-curves
gives `b` spheres, one around each basepoint. For generators `x`, `y` joined by a domain `D`, the
*relative Maslov grading* is

`gr(x, y) = μ(D) - 2 ∑ᵢ n_{zᵢ}(D)`,

where `μ` is the combinatorial Maslov index `TauCeti.HeegaardRegionSystem.maslovIndex`. With a
single basepoint this is the formula of `TauCeti.HeegaardRegionSystem.relativeGrading`, which is
well defined under the Euler normalization of the whole surface. This file develops the
multipointed grading on the incidence data `TauCeti.HeegaardRegionSystem`.

The singly pointed argument shows that two domains from `x` to `y` differ by a periodic domain
plus a multiple of the whole surface, whose Maslov index two cancels its basepoint multiplicity
one. With `b` basepoints the whole surface has Maslov index `2b` and multiplicity one at every
basepoint, but it no longer accounts for every domain from `x` to `x`. Its role is taken by the
components of `Σ - α`. Two regions lie in the same component
(`TauCeti.HeegaardRegionSystem.SameAlphaComponent`) when they are joined by a chain of regions,
consecutive ones on the two sides of a `β`-arc. The domain `A(r₀)` of the component of a region
`r₀` (`TauCeti.HeegaardRegionSystem.alphaComponentDomain`) has no `β`-boundary, and its
`α`-boundary is a combination of whole `α`-curves, since the regions on one side of an `α`-curve
all lie in the same component. So `A(r₀)` is a domain from every generator to itself
(`TauCeti.HeegaardRegionSystem.isDomainBetween_alphaComponentDomain`). Its Maslov index is

`μ(A(r₀)) = χ(C) + k(C)`

(`TauCeti.HeegaardRegionSystem.maslovIndex_alphaComponentDomain_eq`), where `χ(C)` is the Euler
characteristic of the closure `C` of the component, assembled from its regions and its `β`-arcs
(`TauCeti.HeegaardRegionSystem.alphaComponentEuler`; the arcs and points on its boundary cancel),
and `k(C)` is the number of its boundary circles, an `α`-curve counting twice when the component
lies on both of its sides (`TauCeti.HeegaardRegionSystem.alphaComponentBoundaryCount`). The Euler
measure of `A(r₀)` is `χ(C)`, and the point measure of `A(r₀)` at every generator is `k(C) / 2`,
since each point of a generator on a boundary circle of `C` sees two of its four corners in `C`.
When `C` is a sphere with holes, `χ(C) = 2 - k(C)`, so `μ(A(r₀)) = 2`
(`TauCeti.HeegaardRegionSystem.maslovIndex_alphaComponentDomain`). This normalization is the
counterpart of the Euler characteristics `χ` of the regions being those of a closed surface of
genus `n` in the singly pointed case: the Euler characteristics are not determined by the
incidence data, so they are an explicit argument.

When distinct basepoints lie in distinct components, a domain `E` connects a generator to itself
exactly when `E - ∑ᵢ n_{zᵢ}(E) A(zᵢ)` is periodic
(`TauCeti.HeegaardRegionSystem.isDomainBetween_self_iff_sub_sum_smul_mem_periodicDomains`). If
moreover the components of the basepoints are spheres with holes, then `μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` is
a periodic Maslov index at `x`, and the class of `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` modulo the periodic Maslov
indices `TauCeti.HeegaardRegionSystem.periodicMaslovIndices` does not depend on the domain `D`
from `x` to `y`. The value `TauCeti.HeegaardRegionSystem.multipointedRelativeGrading` computed
from a chosen domain is therefore a representative of this class, additive and antisymmetric
modulo the subgroup; when the periodic domains have Maslov index zero at `x`, these hold in `ℚ`.
When every region also lies in the component of a basepoint, the whole surface is the sum of the
`A(zᵢ)` and has Maslov index `2b` (`TauCeti.HeegaardRegionSystem.maslovIndex_one_eq_two_mul_card`):
`2` for one basepoint and `4` for two.

## Main definitions

* `TauCeti.HeegaardRegionSystem.SameAlphaComponent`: two regions lie in the same component of
  `Σ - α`.
* `TauCeti.HeegaardRegionSystem.alphaComponentDomain`: the domain of the component of `Σ - α`
  containing a region.
* `TauCeti.HeegaardRegionSystem.alphaComponentEuler`: the Euler characteristic of the closure of
  that component.
* `TauCeti.HeegaardRegionSystem.alphaComponentBoundaryCount`: its number of boundary circles.
* `TauCeti.HeegaardRegionSystem.multipointedRelativeGrading`: the relative grading
  `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)`, computed from a chosen domain `D` from `x` to `y`, or `0` when there is
  none.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_alphaComponentDomain`: the domain of a component
  of `Σ - α` connects every generator to itself.
* `TauCeti.HeegaardRegionSystem.maslovIndex_alphaComponentDomain_eq`: its Maslov index is
  `χ(C) + k(C)`, and `TauCeti.HeegaardRegionSystem.maslovIndex_alphaComponentDomain`: it is two
  when `C` is a sphere with holes.
* `TauCeti.HeegaardRegionSystem.isDomainBetween_self_iff_sub_sum_smul_mem_periodicDomains`: a
  domain from `x` to `x` is a periodic domain plus `∑ᵢ n_{zᵢ}(E) A(zᵢ)`.
* `TauCeti.HeegaardRegionSystem.maslovIndex_one_eq_two_mul_card`: in a balanced diagram the
  whole surface has Maslov index `2b`.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_multipointedRelativeGrading_eq`: modulo the
  periodic Maslov indices at `x`, the relative grading is `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for every
  domain `D` from `x` to `y`, and
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.multipointedRelativeGrading_eq` is the
  `ℚ`-valued statement.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_multipointedRelativeGrading_add`,
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_multipointedRelativeGrading_swap` and their
  `ℚ`-valued versions: additivity and antisymmetry.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks, link invariants and the multi-variable Alexander
  polynomial*, Algebr. Geom. Topol. **8** (2008),
  [arXiv:math/0512286](https://arxiv.org/abs/math/0512286), §3 (multipointed Heegaard diagrams
  and their relative Maslov grading).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830), §2
  (balanced multipointed diagrams, with `g + b - 1` curves of each kind).
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, for the index formula
  `μ(D) = e(D) + n_x(D) + n_y(D)`.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Finset

section AlphaComponent

/-- Two regions lie in the same component of `Σ - α`: they are joined by a chain of regions,
consecutive ones on the two sides of a `β`-arc. -/
def SameAlphaComponent (r r' : Region) : Prop :=
  Relation.EqvGen (fun a b => ∃ p, H.betaLeft p = a ∧ H.betaRight p = b) r r'

variable {H}

@[refl]
theorem SameAlphaComponent.refl (r : Region) : H.SameAlphaComponent r r :=
  Relation.EqvGen.refl r

@[symm]
theorem SameAlphaComponent.symm {r r' : Region} (h : H.SameAlphaComponent r r') :
    H.SameAlphaComponent r' r :=
  Relation.EqvGen.symm r r' h

@[trans]
theorem SameAlphaComponent.trans {r r' r'' : Region} (h : H.SameAlphaComponent r r')
    (h' : H.SameAlphaComponent r' r'') : H.SameAlphaComponent r r'' :=
  Relation.EqvGen.trans r r' r'' h h'

variable (H)

/-- The two sides of a `β`-arc lie in the same component of `Σ - α`. -/
theorem sameAlphaComponent_betaLeft_betaRight (p : Point) :
    H.SameAlphaComponent (H.betaLeft p) (H.betaRight p) :=
  Relation.EqvGen.rel _ _ ⟨p, rfl, rfl⟩

/-- The regions to the left of consecutive `α`-arcs lie in the same component of `Σ - α`: they
are the two sides of the `β`-arc through the point separating them. -/
theorem sameAlphaComponent_alphaLeft_alphaNext_symm (q : Point) :
    H.SameAlphaComponent (H.alphaLeft q) (H.alphaLeft (H.alphaNext.symm q)) := by
  rcases H.crossingCompatible q with ⟨h₁, -, h₃, -⟩ | ⟨h₁, -, h₃, -⟩
  · rw [h₁, h₃]
    exact (H.sameAlphaComponent_betaLeft_betaRight q).symm
  · rw [h₁, h₃]
    exact H.sameAlphaComponent_betaLeft_betaRight _

/-- The regions to the right of consecutive `α`-arcs lie in the same component of `Σ - α`. -/
theorem sameAlphaComponent_alphaRight_alphaNext_symm (q : Point) :
    H.SameAlphaComponent (H.alphaRight q) (H.alphaRight (H.alphaNext.symm q)) := by
  rcases H.crossingCompatible q with ⟨-, h₂, -, h₄⟩ | ⟨-, h₂, -, h₄⟩
  · rw [h₂, h₄]
    exact (H.sameAlphaComponent_betaLeft_betaRight _).symm
  · rw [h₂, h₄]
    exact H.sameAlphaComponent_betaLeft_betaRight q

/-- The domain `A(r₀)` of the component of `Σ - α` containing the region `r₀`: multiplicity one
on the regions of that component and zero elsewhere. -/
noncomputable def alphaComponentDomain (r₀ : Region) : Region → ℤ :=
  {r | H.SameAlphaComponent r r₀}.indicator 1

variable {H} {r r' r₀ r₁ : Region}

theorem alphaComponentDomain_of_sameAlphaComponent (h : H.SameAlphaComponent r r₀) :
    H.alphaComponentDomain r₀ r = 1 :=
  Set.indicator_of_mem (s := {r | H.SameAlphaComponent r r₀}) h _

theorem alphaComponentDomain_of_not_sameAlphaComponent (h : ¬H.SameAlphaComponent r r₀) :
    H.alphaComponentDomain r₀ r = 0 :=
  Set.indicator_of_notMem (s := {r | H.SameAlphaComponent r r₀}) h _

@[simp]
theorem alphaComponentDomain_self (r₀ : Region) : H.alphaComponentDomain r₀ r₀ = 1 :=
  alphaComponentDomain_of_sameAlphaComponent (.refl r₀)

/-- The domain of a component takes the same value at two regions of a common component. -/
theorem alphaComponentDomain_eq_of_sameAlphaComponent (h : H.SameAlphaComponent r r') :
    H.alphaComponentDomain r₀ r = H.alphaComponentDomain r₀ r' := by
  by_cases hr : H.SameAlphaComponent r r₀
  · rw [alphaComponentDomain_of_sameAlphaComponent hr,
      alphaComponentDomain_of_sameAlphaComponent (h.symm.trans hr)]
  · rw [alphaComponentDomain_of_not_sameAlphaComponent hr,
      alphaComponentDomain_of_not_sameAlphaComponent fun hr' => hr (h.trans hr')]

/-- Regions of a common component have the same component domain. -/
theorem alphaComponentDomain_congr (h : H.SameAlphaComponent r₀ r₁) :
    H.alphaComponentDomain r₀ = H.alphaComponentDomain r₁ := by
  ext r
  by_cases hr : H.SameAlphaComponent r r₀
  · rw [alphaComponentDomain_of_sameAlphaComponent hr,
      alphaComponentDomain_of_sameAlphaComponent (hr.trans h)]
  · rw [alphaComponentDomain_of_not_sameAlphaComponent hr,
      alphaComponentDomain_of_not_sameAlphaComponent fun hr' => hr (hr'.trans h.symm)]

variable (H)

/-- The domain of a component of `Σ - α` has no `β`-boundary. -/
@[simp]
theorem betaBoundary_alphaComponentDomain (r₀ : Region) :
    H.betaBoundary (H.alphaComponentDomain r₀) = 0 := by
  ext p
  rw [betaBoundary_apply, alphaComponentDomain_eq_of_sameAlphaComponent
    (H.sameAlphaComponent_betaLeft_betaRight p), sub_self, Pi.zero_apply]

/-- The `α`-boundary of the domain of a component of `Σ - α` is a combination of whole
`α`-curves. -/
@[simp]
theorem alphaArcBoundary_alphaBoundary_alphaComponentDomain (r₀ : Region) :
    H.alphaArcBoundary (H.alphaBoundary (H.alphaComponentDomain r₀)) = 0 := by
  ext q
  rw [alphaArcBoundary_apply, alphaBoundary_apply, alphaBoundary_apply,
    alphaComponentDomain_eq_of_sameAlphaComponent (H.sameAlphaComponent_alphaLeft_alphaNext_symm q),
    alphaComponentDomain_eq_of_sameAlphaComponent
      (H.sameAlphaComponent_alphaRight_alphaNext_symm q), sub_self, Pi.zero_apply]

/-- **The domain of a component of `Σ - α` connects every generator to itself.** -/
theorem isDomainBetween_alphaComponentDomain (x : H.Generator) (r₀ : Region) :
    H.IsDomainBetween x x (H.alphaComponentDomain r₀) :=
  isDomainBetween_self_iff_arcBoundary_eq_zero.mpr ⟨by simp, by simp⟩

/-- The domain of a component of `Σ - α` takes the same value to the left of any two arcs of a
common `α`-curve. -/
theorem alphaComponentDomain_alphaLeft_eq {p q : Point} (h : H.alpha p = H.alpha q)
    (r₀ : Region) :
    H.alphaComponentDomain r₀ (H.alphaLeft p) = H.alphaComponentDomain r₀ (H.alphaLeft q) := by
  obtain ⟨a, ha⟩ := (H.alphaNext.forall_comp_symm_sub_eq_zero_iff H.alphaNext_isCycleOn
    fun p => H.alphaComponentDomain r₀ (H.alphaLeft p)).mp fun q => by
      rw [alphaComponentDomain_eq_of_sameAlphaComponent
        (H.sameAlphaComponent_alphaLeft_alphaNext_symm q).symm, sub_self]
  rw [ha, ha, h]

/-- The domain of a component of `Σ - α` takes the same value to the right of any two arcs of a
common `α`-curve. -/
theorem alphaComponentDomain_alphaRight_eq {p q : Point} (h : H.alpha p = H.alpha q)
    (r₀ : Region) :
    H.alphaComponentDomain r₀ (H.alphaRight p) = H.alphaComponentDomain r₀ (H.alphaRight q) := by
  obtain ⟨a, ha⟩ := (H.alphaNext.forall_comp_symm_sub_eq_zero_iff H.alphaNext_isCycleOn
    fun p => H.alphaComponentDomain r₀ (H.alphaRight p)).mp fun q => by
      rw [alphaComponentDomain_eq_of_sameAlphaComponent
        (H.sameAlphaComponent_alphaRight_alphaNext_symm q).symm, sub_self]
  rw [ha, ha, h]

/-- At every intersection point, the point measure of the domain of a component of `Σ - α` is
half the number of sides of the `α`-curve through it that lie in the component. -/
theorem pointMeasure_alphaComponentDomain (r₀ : Region) (p : Point) :
    H.pointMeasure (H.alphaComponentDomain r₀) p =
      ((H.alphaComponentDomain r₀ (H.alphaLeft p) : ℚ) +
        H.alphaComponentDomain r₀ (H.alphaRight p)) / 2 := by
  rw [pointMeasure_apply,
    ← alphaComponentDomain_eq_of_sameAlphaComponent
      (H.sameAlphaComponent_alphaLeft_alphaNext_symm p),
    ← alphaComponentDomain_eq_of_sameAlphaComponent
      (H.sameAlphaComponent_alphaRight_alphaNext_symm p)]
  ring

/-- Read along `β`, the point measure of the domain of a component of `Σ - α` is half the number
of the two `β`-arcs at the point that lie in the component. -/
theorem pointMeasure_alphaComponentDomain_beta (r₀ : Region) (p : Point) :
    H.pointMeasure (H.alphaComponentDomain r₀) p =
      ((H.alphaComponentDomain r₀ (H.betaLeft (H.betaNext.symm p)) : ℚ) +
        H.alphaComponentDomain r₀ (H.betaLeft p)) / 2 := by
  rw [pointMeasure_apply_beta,
    ← alphaComponentDomain_eq_of_sameAlphaComponent
      (H.sameAlphaComponent_betaLeft_betaRight (H.betaNext.symm p)),
    ← alphaComponentDomain_eq_of_sameAlphaComponent (H.sameAlphaComponent_betaLeft_betaRight p)]
  ring

variable [Fintype Point]

/-- The total point measure of the domain of a component of `Σ - α` is the number of `β`-arcs
in the component. -/
theorem sum_pointMeasure_alphaComponentDomain (r₀ : Region) :
    ∑ p, H.pointMeasure (H.alphaComponentDomain r₀) p =
      ∑ p, (H.alphaComponentDomain r₀ (H.betaLeft p) : ℚ) := by
  simp_rw [pointMeasure_alphaComponentDomain_beta, ← sum_div, sum_add_distrib,
    Equiv.sum_comp H.betaNext.symm fun p => (H.alphaComponentDomain r₀ (H.betaLeft p) : ℚ)]
  ring

/-- The number of boundary circles of the closure of the component of `Σ - α` containing `r₀`:
the number of `α`-curves with an arc having the component on its left, plus the number with an
arc having it on its right. An `α`-curve along which the component lies on both sides counts
twice. This counts the boundary circles when every `α`-curve meets the `β`-curves, as it does in
a diagram with a generator. -/
noncomputable def alphaComponentBoundaryCount (r₀ : Region) : ℕ :=
  open scoped Classical in
  #{i | ∃ p, H.alpha p = i ∧ H.SameAlphaComponent (H.alphaLeft p) r₀} +
    #{i | ∃ p, H.alpha p = i ∧ H.SameAlphaComponent (H.alphaRight p) r₀}

/-- The point measure of the domain of a component of `Σ - α` at every generator is half the
number of boundary circles of the component: the point of the generator on a boundary circle sees
two of its four corners in the component. -/
theorem generatorPointMeasure_alphaComponentDomain (x : H.Generator) (r₀ : Region) :
    H.generatorPointMeasure x (H.alphaComponentDomain r₀) =
      (H.alphaComponentBoundaryCount r₀ : ℚ) / 2 := by
  have hxi (i : Fin n) : H.alpha (H.point x i) = i := by simp
  -- On the curve `αᵢ`, a side of the point `xᵢ` lies in the component exactly when the same side
  -- of some point of `αᵢ` does, since `A(r₀)` is constant along each side of `αᵢ`.
  have hside (side : Point → Region) (hc : ∀ p q, H.alpha p = H.alpha q →
      H.alphaComponentDomain r₀ (side p) = H.alphaComponentDomain r₀ (side q)) (i : Fin n) :
      H.alphaComponentDomain r₀ (side (H.point x i)) =
        {i | ∃ p, H.alpha p = i ∧ H.SameAlphaComponent (side p) r₀}.indicator 1 i := by
    by_cases h : ∃ p, H.alpha p = i ∧ H.SameAlphaComponent (side p) r₀
    · obtain ⟨p, hp, hpr⟩ := h
      rw [Set.indicator_of_mem (s := {i | ∃ p, H.alpha p = i ∧ H.SameAlphaComponent (side p) r₀})
        ⟨p, hp, hpr⟩, hc _ p (by rw [hp, hxi]), alphaComponentDomain_of_sameAlphaComponent hpr,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem h, alphaComponentDomain_of_not_sameAlphaComponent fun hx =>
        h ⟨H.point x i, hxi i, hx⟩]
  classical
  simp only [alphaComponentBoundaryCount, Nat.cast_add, natCast_card_filter,
    generatorPointMeasure_apply, pointMeasure_alphaComponentDomain,
    hside _ fun _ _ h => H.alphaComponentDomain_alphaLeft_eq h r₀,
    hside _ fun _ _ h => H.alphaComponentDomain_alphaRight_eq h r₀, Set.indicator_apply,
    Set.mem_ofPred_eq, Pi.one_apply, ← sum_div, sum_add_distrib]
  push_cast
  -- The two sides differ only in the decidability instances of their conditions.
  congr

variable [Fintype Region]

/-- The Euler characteristic `χ(C)` of the closure `C` of the component of `Σ - α` containing
`r₀`, for the Euler characteristics `χ` of the regions: the sum of `χ` over the regions of the
component minus the number of `β`-arcs in it. The arcs and points on the boundary of `C`, which
lies on the `α`-curves, are equal in number and cancel. -/
noncomputable def alphaComponentEuler (χ : Region → ℤ) (r₀ : Region) : ℤ :=
  ∑ r, χ r * H.alphaComponentDomain r₀ r - ∑ p, H.alphaComponentDomain r₀ (H.betaLeft p)

theorem alphaComponentEuler_def (χ : Region → ℤ) (r₀ : Region) :
    H.alphaComponentEuler χ r₀ =
      ∑ r, χ r * H.alphaComponentDomain r₀ r - ∑ p, H.alphaComponentDomain r₀ (H.betaLeft p) :=
  (rfl)

variable [DecidableEq Region]

/-- The Euler measure of the domain of a component of `Σ - α` is the Euler characteristic of the
closure of the component. -/
theorem eulerMeasure_alphaComponentDomain (χ : Region → ℤ) (r₀ : Region) :
    H.eulerMeasure χ (H.alphaComponentDomain r₀) = H.alphaComponentEuler χ r₀ := by
  rw [eulerMeasure_eq_sub_sum_pointMeasure, sum_pointMeasure_alphaComponentDomain,
    alphaComponentEuler_def]
  push_cast
  rfl

/-- **The Maslov index of a component of `Σ - α`.** At any two generators, the domain of the
component of `Σ - α` containing `r₀` has Maslov index `χ(C) + k(C)`, the Euler characteristic of
the closure `C` of the component plus its number of boundary circles. -/
theorem maslovIndex_alphaComponentDomain_eq (χ : Region → ℤ) (x y : H.Generator) (r₀ : Region) :
    H.maslovIndex χ x y (H.alphaComponentDomain r₀) =
      H.alphaComponentEuler χ r₀ + H.alphaComponentBoundaryCount r₀ := by
  rw [maslovIndex_apply, eulerMeasure_alphaComponentDomain,
    generatorPointMeasure_alphaComponentDomain, generatorPointMeasure_alphaComponentDomain]
  ring

/-- **A sphere-with-holes component of `Σ - α` has Maslov index two.** When the closure of the
component of `Σ - α` containing `r₀` is a sphere with holes, `χ(C) = 2 - k(C)`, its domain has
Maslov index two at any two generators. -/
theorem maslovIndex_alphaComponentDomain {χ : Region → ℤ} {r₀ : Region}
    (hχ : H.alphaComponentEuler χ r₀ = 2 - H.alphaComponentBoundaryCount r₀) (x y : H.Generator) :
    H.maslovIndex χ x y (H.alphaComponentDomain r₀) = 2 := by
  rw [maslovIndex_alphaComponentDomain_eq, hχ]
  push_cast
  ring

end AlphaComponent

section Balanced

variable {H} [Fintype Basepoint]

/-- When distinct basepoints lie in distinct components of `Σ - α`, the domains of the components
of the basepoints, weighted by the multiplicities of a domain `E` at the basepoints, have the
multiplicities of `E` at the basepoints. -/
theorem sum_smul_alphaComponentDomain_basepoint_apply_basepoint
    (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
    (E : Region → ℤ) (z' : Basepoint) :
    (∑ z, E (H.basepoint z) • H.alphaComponentDomain (H.basepoint z)) (H.basepoint z') =
      E (H.basepoint z') := by
  simp only [Finset.sum_apply]
  rw [sum_eq_single z' (fun z _ hzz' => by
      rw [Pi.smul_apply,
        alphaComponentDomain_of_not_sameAlphaComponent fun h => hzz' (hz _ _ h).symm, smul_zero])
    (fun h => absurd (mem_univ z') h), Pi.smul_apply, alphaComponentDomain_self, smul_eq_mul,
    mul_one]

/-- **Domains from a generator to itself in a multipointed diagram.** When distinct basepoints lie
in distinct components of `Σ - α`, a domain `E` connects a generator to itself exactly when
`E - ∑ᵢ n_{zᵢ}(E) A(zᵢ)` is periodic, where `A(zᵢ)` is the domain of the component of the
basepoint `zᵢ`. With a single basepoint whose component is everything this is
`TauCeti.HeegaardRegionSystem.isDomainBetween_self_iff_sub_smul_one_mem_periodicDomains`. -/
theorem isDomainBetween_self_iff_sub_sum_smul_mem_periodicDomains
    (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
    {x : H.Generator} {E : Region → ℤ} :
    H.IsDomainBetween x x E ↔
      E - ∑ z, E (H.basepoint z) • H.alphaComponentDomain (H.basepoint z) ∈ H.periodicDomains := by
  simp only [mem_periodicDomains_iff, isDomainBetween_self_iff_arcBoundary_eq_zero, map_sub,
    map_sum, map_zsmul, alphaArcBoundary_alphaBoundary_alphaComponentDomain,
    betaBoundary_alphaComponentDomain, smul_zero, sum_const_zero, sub_zero, Pi.sub_apply,
    sum_smul_alphaComponentDomain_basepoint_apply_basepoint hz, sub_self, implies_true, true_and]

/-- **The whole surface of a balanced diagram.** When every region lies in the component of
`Σ - α` of exactly one basepoint, the whole surface is the sum of the domains of the components of
the basepoints. -/
theorem sum_alphaComponentDomain_basepoint
    (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
    (hcover : ∀ r, ∃ z, H.SameAlphaComponent r (H.basepoint z)) :
    ∑ z, H.alphaComponentDomain (H.basepoint z) = 1 := by
  ext r
  obtain ⟨z₀, hz₀⟩ := hcover r
  simp only [Finset.sum_apply]
  rw [sum_eq_single z₀ (fun z _ hzz₀ => alphaComponentDomain_of_not_sameAlphaComponent
      fun h => hzz₀ (hz _ _ (h.symm.trans hz₀))) (fun h => absurd (mem_univ z₀) h),
    alphaComponentDomain_of_sameAlphaComponent hz₀, Pi.one_apply]

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- **The whole surface of a balanced diagram has Maslov index `2b`.** When every region lies in
the component of `Σ - α` of exactly one of the `b` basepoints and these components are spheres
with holes, the whole surface, which has multiplicity one at every basepoint, has Maslov index
`2b` at any two generators. -/
theorem maslovIndex_one_eq_two_mul_card
    (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
    (hcover : ∀ r, ∃ z, H.SameAlphaComponent r (H.basepoint z))
    (hχ : ∀ z, H.alphaComponentEuler χ (H.basepoint z) =
      2 - H.alphaComponentBoundaryCount (H.basepoint z)) (x y : H.Generator) :
    H.maslovIndex χ x y 1 = 2 * Fintype.card Basepoint := by
  rw [← sum_alphaComponentDomain_basepoint hz hcover, map_sum,
    sum_congr rfl fun z _ => H.maslovIndex_alphaComponentDomain (hχ z) x y, sum_const, card_univ,
    nsmul_eq_mul, mul_comm]

open scoped Classical in
variable (H) in
/-- The relative Maslov grading `gr(x, y) = μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` of two generators of a
multipointed diagram, for a chosen domain `D` from `x` to `y`, or `0` when no domain joins them.
When distinct basepoints lie in distinct components of `Σ - α` and these components are spheres
with holes, its class modulo the periodic Maslov indices at `x` does not depend on the choice of
`D` (`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_multipointedRelativeGrading_eq`), and when
the periodic domains have Maslov index zero at the source generator neither does the value itself
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.multipointedRelativeGrading_eq`). -/
noncomputable def multipointedRelativeGrading (χ : Region → ℤ) (x y : H.Generator) : ℚ :=
  if h : ∃ D, H.IsDomainBetween x y D then
    H.maslovIndex χ x y h.choose - 2 * ∑ z, (h.choose (H.basepoint z) : ℚ)
  else 0

/-- When no domain joins `x` to `y`, the multipointed relative grading is `0`. -/
theorem multipointedRelativeGrading_of_forall_not_isDomainBetween {x y : H.Generator}
    (h : ∀ D, ¬H.IsDomainBetween x y D) : H.multipointedRelativeGrading χ x y = 0 := by
  rw [multipointedRelativeGrading, dite_eq_right (not_exists.mpr h)]

variable (hz : ∀ z z', H.SameAlphaComponent (H.basepoint z) (H.basepoint z') → z = z')
  (hχ : ∀ z, H.alphaComponentEuler χ (H.basepoint z) =
    2 - H.alphaComponentBoundaryCount (H.basepoint z))
  {x y w : H.Generator} {D D' E : Region → ℤ}

include hz hχ

/-- In a multipointed diagram whose basepoints lie in distinct sphere-with-holes components of
`Σ - α`, a domain `E` from `x` to `x` has `μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` among the periodic Maslov
indices at `x`: it is a periodic domain plus `n_{zᵢ}(E)` copies of the domain of the component of
each basepoint `zᵢ`, which has Maslov index two. -/
theorem IsDomainBetween.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices
    (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x := by
  have h := maslovIndex_mem_periodicMaslovIndices (χ := χ) (x := x)
    ((isDomainBetween_self_iff_sub_sum_smul_mem_periodicDomains hz).mp hE)
  rw [map_sub, map_sum] at h
  simp only [AddMonoidHom.map_zsmul] at h
  simp only [H.maslovIndex_alphaComponentDomain (hχ _), zsmul_eq_mul] at h
  convert h using 2
  rw [mul_sum]
  exact sum_congr rfl fun z _ => mul_comm _ _

/-- In a multipointed diagram whose basepoints lie in distinct sphere-with-holes components of
`Σ - α` and all of whose periodic domains have Maslov index zero at `x`, a domain `E` from `x` to
`x` has Maslov index `2 ∑ᵢ n_{zᵢ}(E)`. -/
theorem IsDomainBetween.maslovIndex_self_eq_two_mul_sum
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ) := by
  have h := hE.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices hz hχ
  rwa [periodicMaslovIndices_eq_bot_iff.mpr hP, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- In a multipointed diagram whose basepoints lie in distinct sphere-with-holes components of
`Σ - α`, the quantities `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for domains `D` from `x` to `y` differ by periodic
Maslov indices at `x`. -/
theorem IsDomainBetween.maslovIndex_sub_two_mul_sum_sub_mem_periodicMaslovIndices
    (hD : H.IsDomainBetween x y D) (hD' : H.IsDomainBetween x y D') :
    H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ) -
        (H.maslovIndex χ x y D' - 2 * ∑ z, (D' (H.basepoint z) : ℚ)) ∈
      H.periodicMaslovIndices χ x := by
  -- `D - D'` runs from `x` to `x`, and both sides of its index count split along `y`.
  have h := (hD.add hD'.neg).maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices hz hχ
  rw [hD.maslovIndex_add χ hD'.neg, maslovIndex_neg] at h
  convert h using 1
  simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg, sum_add_distrib,
    sum_neg_distrib]
  ring

/-- In a multipointed diagram whose basepoints lie in distinct sphere-with-holes components of
`Σ - α` and all of whose periodic domains have Maslov index zero at `x`, the quantity
`μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` is the same for all domains `D` from `x` to `y`. -/
theorem IsDomainBetween.maslovIndex_sub_two_mul_sum_eq
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D)
    (hD' : H.IsDomainBetween x y D') :
    H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ) =
      H.maslovIndex χ x y D' - 2 * ∑ z, (D' (H.basepoint z) : ℚ) := by
  have h := hD.maslovIndex_sub_two_mul_sum_sub_mem_periodicMaslovIndices hz hχ hD'
  rwa [periodicMaslovIndices_eq_bot_iff.mpr hP, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- Modulo the periodic Maslov indices at `x`, the multipointed relative grading is
`μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for every domain `D` from `x` to `y`. -/
theorem IsDomainBetween.coe_multipointedRelativeGrading_eq (hD : H.IsDomainBetween x y D) :
    (H.multipointedRelativeGrading χ x y : ℚ ⧸ H.periodicMaslovIndices χ x) =
      ((H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ) : ℚ) :
        ℚ ⧸ H.periodicMaslovIndices χ x) := by
  have h : ∃ D, H.IsDomainBetween x y D := ⟨D, hD⟩
  rw [QuotientAddGroup.eq_iff_sub_mem, multipointedRelativeGrading, dite_eq_left h]
  exact h.choose_spec.maslovIndex_sub_two_mul_sum_sub_mem_periodicMaslovIndices hz hχ hD

/-- The multipointed relative grading is `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for every domain `D` from `x` to
`y`, when the periodic domains have Maslov index zero at `x`. -/
theorem IsDomainBetween.multipointedRelativeGrading_eq
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D) :
    H.multipointedRelativeGrading χ x y =
      H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ) := by
  have h := QuotientAddGroup.eq_iff_sub_mem.mp (hD.coe_multipointedRelativeGrading_eq hz hχ)
  rwa [periodicMaslovIndices_eq_bot_iff.mpr hP, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- A generator has multipointed relative grading zero with itself, modulo the periodic Maslov
indices. -/
theorem coe_multipointedRelativeGrading_self :
    (H.multipointedRelativeGrading χ x x : ℚ ⧸ H.periodicMaslovIndices χ x) = 0 := by
  simp [(isDomainBetween_zero x).coe_multipointedRelativeGrading_eq hz hχ]

/-- The multipointed relative grading is additive modulo the periodic Maslov indices:
`gr(x, y) + gr(y, w) = gr(x, w)` for generators joined by domains. -/
theorem IsDomainBetween.coe_multipointedRelativeGrading_add (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y w E) :
    ((H.multipointedRelativeGrading χ x y + H.multipointedRelativeGrading χ y w : ℚ) :
        ℚ ⧸ H.periodicMaslovIndices χ x) = H.multipointedRelativeGrading χ x w := by
  have hxy := QuotientAddGroup.eq_iff_sub_mem.mp (hD.coe_multipointedRelativeGrading_eq hz hχ)
  have hyw := QuotientAddGroup.eq_iff_sub_mem.mp (hE.coe_multipointedRelativeGrading_eq hz hχ)
  have hxw := QuotientAddGroup.eq_iff_sub_mem.mp
    ((hD.add hE).coe_multipointedRelativeGrading_eq hz hχ)
  rw [← hD.periodicMaslovIndices_eq] at hyw
  rw [QuotientAddGroup.eq_iff_sub_mem]
  convert sub_mem (add_mem hxy hyw) hxw using 1
  simp only [hD.maslovIndex_add χ hE, Pi.add_apply, Int.cast_add, sum_add_distrib]
  ring

/-- The multipointed relative grading is antisymmetric modulo the periodic Maslov indices:
`gr(y, x) = -gr(x, y)` for generators joined by a domain. -/
theorem IsDomainBetween.coe_multipointedRelativeGrading_swap (hD : H.IsDomainBetween x y D) :
    (H.multipointedRelativeGrading χ y x : ℚ ⧸ H.periodicMaslovIndices χ x) =
      -(H.multipointedRelativeGrading χ x y : ℚ ⧸ H.periodicMaslovIndices χ x) := by
  have hxy := QuotientAddGroup.eq_iff_sub_mem.mp (hD.coe_multipointedRelativeGrading_eq hz hχ)
  have hyx := QuotientAddGroup.eq_iff_sub_mem.mp (hD.neg.coe_multipointedRelativeGrading_eq hz hχ)
  rw [← hD.periodicMaslovIndices_eq] at hyx
  rw [← QuotientAddGroup.mk_neg, QuotientAddGroup.eq_iff_sub_mem]
  convert add_mem hyx hxy using 1
  simp only [maslovIndex_neg, Pi.neg_apply, Int.cast_neg, sum_neg_distrib]
  ring

/-- A generator has multipointed relative grading zero with itself. -/
theorem multipointedRelativeGrading_self
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) :
    H.multipointedRelativeGrading χ x x = 0 := by
  simp [(isDomainBetween_zero x).multipointedRelativeGrading_eq hz hχ hP]

/-- The multipointed relative grading is additive: `gr(x, y) + gr(y, w) = gr(x, w)` for
generators joined by domains, when the periodic domains have Maslov index zero at `x`. -/
theorem IsDomainBetween.multipointedRelativeGrading_add
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y w E) :
    H.multipointedRelativeGrading χ x y + H.multipointedRelativeGrading χ y w =
      H.multipointedRelativeGrading χ x w := by
  rw [hD.multipointedRelativeGrading_eq hz hχ hP,
    hE.multipointedRelativeGrading_eq hz hχ
      (hD.forall_mem_periodicDomains_maslovIndex_eq_zero χ hP),
    (hD.add hE).multipointedRelativeGrading_eq hz hχ hP, hD.maslovIndex_add χ hE]
  simp only [Pi.add_apply, Int.cast_add, sum_add_distrib]
  ring

/-- The multipointed relative grading is antisymmetric: `gr(y, x) = -gr(x, y)` for generators
joined by a domain, when the periodic domains have Maslov index zero at `x`. -/
theorem IsDomainBetween.multipointedRelativeGrading_swap
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D) :
    H.multipointedRelativeGrading χ y x = -H.multipointedRelativeGrading χ x y := by
  rw [hD.multipointedRelativeGrading_eq hz hχ hP,
    hD.neg.multipointedRelativeGrading_eq hz hχ
      (hD.forall_mem_periodicDomains_maslovIndex_eq_zero χ hP), maslovIndex_neg]
  simp only [Pi.neg_apply, Int.cast_neg, sum_neg_distrib]
  ring

end Balanced

end HeegaardRegionSystem

end TauCeti
