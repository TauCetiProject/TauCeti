/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.LowDimTopology.Heegaard.HatDifferential
public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility
import TauCeti.Algebra.BigOperators.Pi

/-!
# Adding a basepoint to a Heegaard diagram

A multipointed Heegaard diagram with `b` basepoints can be enlarged to one with `b + 1`
basepoints by a local move: inside a region `R₀`, draw a small `α`-circle and a small `β`-circle
meeting in two points `p` and `q`, and put the new basepoint in the lens enclosed by both
circles. The circles cut out of `R₀` an open disc, which they divide into three new regions, the
`α`-crescent `C_α` inside the `α`-circle only, the `β`-crescent `C_β` inside the `β`-circle only
and the lens `L`; what remains of `R₀` is `R₀` with an open disc removed, whose Euler
characteristic is one less. The hat complex of the new diagram is the hat complex of the old one
tensored with the two-dimensional space `W` on `p` and `q` with zero differential, when `R₀`
contains a basepoint.
This is the chain-level form of the comparison of Ozsváth, Stipsicz and Szabó, by which each
additional basepoint tensors the hat homology with a two-dimensional factor. The two
crescents are the bigons from `p` to `q`; they cancel modulo two, and give the two generators of
`W` relative Maslov grading one apart.

This file performs the move on the incidence data `TauCeti.HeegaardRegionSystem`
(`TauCeti.HeegaardRegionSystem.addBasepoint`). The intersection points become `Point ⊕ Fin 2`,
with `p = Sum.inr 0` and `q = Sum.inr 1`; the regions become `Region ⊕ Fin 3`, the region label
`Sum.inl R₀` now standing for `R₀` with the disc removed and `Sum.inr 0`, `Sum.inr 1`,
`Sum.inr 2` for `C_α`, `C_β` and `L`; the new circles are the last `α`- and `β`-curves; and the
basepoints become `Basepoint ⊕ Unit`. The region Euler characteristics are changed accordingly
(`TauCeti.HeegaardRegionSystem.addBasepointEuler`). A generator of the new diagram is a
generator `x` of the old one together with one of the two new points
(`TauCeti.HeegaardRegionSystem.addBasepointGeneratorEquiv`).

The two circles are oriented as boundaries of the discs they bound. A domain `D` of the new
diagram then connects `(x, i)` to `(y, j)` exactly when its restriction to the old regions
connects `x` to `y` and `D(C_α) + D(C_β) - D(R₀) - D(L) = j - i`
(`TauCeti.HeegaardRegionSystem.isDomainBetween_addBasepoint_iff`), and its Maslov index is
`μ(D|_old) + D(C_α) + D(C_β) + D(L) - D(R₀)`
(`TauCeti.HeegaardRegionSystem.maslovIndex_addBasepoint`). When `R₀` contains a basepoint, the
domains counted by the hat differential vanish on `R₀` and `L`, and the first condition forces
the crescents to vanish when `i = j`, and to be one crescent when `i = 0` and `j = 1`, the
restriction then having Maslov index zero. So between generators with the same new point the
counted domains are those of the old diagram, while from `p` to `q` they come in pairs, one for
each crescent, and cancel modulo two.

The periodic data change by exactly one class. A domain of the new diagram is periodic exactly when
its restriction to the old regions is periodic, it vanishes on the lens, which contains the new
basepoint, and `D(C_α) + D(C_β) = D(R₀)`
(`TauCeti.HeegaardRegionSystem.mem_periodicDomains_addBasepoint_iff`). So the periodic domains of
the new diagram are those of the old one together with the multiples of `C_α - C_β`, the class of
the sphere bounding the ball around the new basepoint
(`TauCeti.HeegaardRegionSystem.addBasepointPeriodicDomainsEquiv`). A periodic domain has the
Maslov index of its restriction, so the periodic Maslov indices are unchanged, and since a
nonzero multiple of `C_α - C_β` has coefficients of both signs, weak admissibility, weak
admissibility at a generator and strong admissibility are each preserved and reflected. In a
domain from `(x, i)` to itself the crescents and the remainder of `R₀` cancel in the index
formula, while the lens contributes `2 n_L` to the Maslov index and `n_L` at the new basepoint.
So the normalization under which the relative grading `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` is well defined
passes to the new diagram, and its relative grading is
`gr((x, i), (y, j)) = gr(x, y) + j - i` modulo the periodic Maslov indices
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeGrading_addBasepoint`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.addBasepoint`: the diagram with a basepoint added in a region.
* `TauCeti.HeegaardRegionSystem.addBasepointEuler`: its region Euler characteristics.
* `TauCeti.HeegaardRegionSystem.addBasepointGenerator`: the generator `(x, i)`.
* `TauCeti.HeegaardRegionSystem.addBasepointGeneratorEquiv`: the generators of the new diagram
  are the pairs of an old generator and a new point.
* `TauCeti.HeegaardRegionSystem.addBasepointChainEquiv`: the resulting identification of hat
  chain groups `CF̂_{b+1} ≅ CF̂_b ⊗ W`.
* `TauCeti.HeegaardRegionSystem.addBasepointPeriodicDomainsEquiv`: the periodic domains of the new
  diagram are those of the old one times `ℤ`, the multiples of `C_α - C_β`.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_addBasepoint_iff` and
  `TauCeti.HeegaardRegionSystem.maslovIndex_addBasepoint`: domains and their Maslov indices in
  the new diagram.
* `TauCeti.HeegaardRegionSystem.hatCoefficient_addBasepoint`: the hat coefficient from `(x, i)`
  to `(y, j)` is that from `x` to `y` when `i = j` and zero otherwise.
* `TauCeti.HeegaardRegionSystem.hatDifferential_comp_addBasepointChainEquiv`: the hat
  differential of the new diagram is `∂ ⊗ 1` on `CF̂_b ⊗ W`.
* `TauCeti.HeegaardRegionSystem.single_mem_hatDomains_addBasepoint`: each crescent is a counted
  domain from `(x, 0)` to `(x, 1)`, of Maslov index one and avoiding all basepoints.
* `TauCeti.HeegaardRegionSystem.mem_periodicDomains_addBasepoint_iff` and
  `TauCeti.HeegaardRegionSystem.periodicMaslovIndices_addBasepoint`: the periodic domains of the
  new diagram and their Maslov indices.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_addBasepoint_iff`,
  `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_addBasepoint_iff` and
  `TauCeti.HeegaardRegionSystem.stronglyAdmissible_addBasepoint_iff`: adding a basepoint preserves
  and reflects each kind of admissibility.
* `TauCeti.HeegaardRegionSystem.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_addBasepoint`:
  the normalization of the relative grading passes to the new diagram.
* `TauCeti.HeegaardRegionSystem.IsDomainBetween.coe_relativeGrading_addBasepoint`,
  `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_addBasepoint` and
  `TauCeti.HeegaardRegionSystem.relativeGrading_addBasepoint_self`: the relative grading of
  `(x, i)` and `(y, j)` is `gr(x, y) + j - i`.

## References

* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830)
  (multipointed nice diagrams, whose hat homology is that of a singly pointed diagram tensored
  with one two-dimensional factor for each additional basepoint).
* P. Ozsváth and Z. Szabó, *Holomorphic disks, link invariants and the multi-variable Alexander
  polynomial*, Algebr. Geom. Topol. **8** (2008),
  [arXiv:math/0512286](https://arxiv.org/abs/math/0512286), §3 (periodic domains, admissibility
  and the relative Maslov grading of multipointed Heegaard diagrams).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Function
open scoped TensorProduct

section Construction

/-- The diagram obtained by adding a basepoint in the region `r₀`. Inside `r₀` a new `α`-circle
and a new `β`-circle, the last curves, meet in the two new points `Sum.inr 0` and `Sum.inr 1`.
They bound the three new regions `Sum.inr 0`, `Sum.inr 1` and `Sum.inr 2`, the `α`-crescent
inside the `α`-circle only, the `β`-crescent inside the `β`-circle only and the lens inside both,
and the new basepoint lies in the lens. Both circles are oriented as the boundaries of the discs
they bound, so each new arc has the region it bounds on its left. The region label `Sum.inl r₀`
now denotes `r₀` with the disc enclosed by the circles removed. -/
def addBasepoint (r₀ : Region) :
    HeegaardRegionSystem (n + 1) (Point ⊕ Fin 2) (Region ⊕ Fin 3) (Basepoint ⊕ Unit) where
  pointFintype := letI := H.pointFintype; inferInstance
  alpha := Sum.elim (fun p => (H.alpha p).castSucc) fun _ => Fin.last n
  beta := Sum.elim (fun p => (H.beta p).castSucc) fun _ => Fin.last n
  alphaNext := Equiv.Perm.sumCongr H.alphaNext (Equiv.swap 0 1)
  alphaNext_isCycleOn := Equiv.Perm.isCycleOn_sumCongr_fiber H.alphaNext_isCycleOn
    (by simpa using isCycleOn_swap_fiber (by decide) (fun _ : Fin 2 => (0 : Fin 1)) 0)
  betaNext := Equiv.Perm.sumCongr H.betaNext (Equiv.swap 0 1)
  betaNext_isCycleOn := Equiv.Perm.isCycleOn_sumCongr_fiber H.betaNext_isCycleOn
    (by simpa using isCycleOn_swap_fiber (by decide) (fun _ : Fin 2 => (0 : Fin 1)) 0)
  alphaLeft := Sum.elim (Sum.inl ∘ H.alphaLeft) ![Sum.inr 0, Sum.inr 2]
  alphaRight := Sum.elim (Sum.inl ∘ H.alphaRight) ![Sum.inl r₀, Sum.inr 1]
  betaLeft := Sum.elim (Sum.inl ∘ H.betaLeft) ![Sum.inr 2, Sum.inr 1]
  betaRight := Sum.elim (Sum.inl ∘ H.betaRight) ![Sum.inr 0, Sum.inl r₀]
  regionNonempty := ⟨Sum.inr 0⟩
  crossingCompatible := by
    rintro (p | k) <;> rw [isCrossingCompatible_iff]
    · rcases isCrossingCompatible_iff.1 (H.crossingCompatible p) with h | h
      · left
        simpa using h
      · right
        simpa using h
    · fin_cases k
      · left
        simp
      · right
        simp
  regionCovered := by
    rintro (r | k)
    · rcases H.regionCovered r with ⟨p, hp⟩ | ⟨-, hR⟩
      · exact Or.inl ⟨Sum.inl p, by simpa using hp⟩
      · exact Or.inl ⟨Sum.inr 0, by simp [Subsingleton.elim r r₀]⟩
    · refine Or.inl ?_
      fin_cases k
      · exact ⟨Sum.inr 0, by simp⟩
      · exact ⟨Sum.inr 1, by simp⟩
      · exact ⟨Sum.inr 1, by simp⟩
  basepoint := Sum.elim (Sum.inl ∘ H.basepoint) fun _ => Sum.inr 2

variable (r₀ : Region)

/-- The old points keep their `α`-curves. -/
@[simp]
theorem addBasepoint_alpha_inl (p : Point) :
    (H.addBasepoint r₀).alpha (Sum.inl p) = (H.alpha p).castSucc :=
  (rfl)

/-- The new points lie on the new last `α`-curve. -/
@[simp]
theorem addBasepoint_alpha_inr (k : Fin 2) :
    (H.addBasepoint r₀).alpha (Sum.inr k) = Fin.last n :=
  (rfl)

/-- The old points keep their `β`-curves. -/
@[simp]
theorem addBasepoint_beta_inl (p : Point) :
    (H.addBasepoint r₀).beta (Sum.inl p) = (H.beta p).castSucc :=
  (rfl)

/-- The new points lie on the new last `β`-curve. -/
@[simp]
theorem addBasepoint_beta_inr (k : Fin 2) :
    (H.addBasepoint r₀).beta (Sum.inr k) = Fin.last n :=
  (rfl)

/-- The successor along the `α`-curves: the old one on the old points, and the exchange of
the two new points on the new curve. -/
@[simp]
theorem addBasepoint_alphaNext :
    (H.addBasepoint r₀).alphaNext = Equiv.Perm.sumCongr H.alphaNext (Equiv.swap 0 1) :=
  (rfl)

/-- The successor along the `β`-curves: the old one on the old points, and the exchange of
the two new points on the new curve. -/
@[simp]
theorem addBasepoint_betaNext :
    (H.addBasepoint r₀).betaNext = Equiv.Perm.sumCongr H.betaNext (Equiv.swap 0 1) :=
  (rfl)

/-- The regions to the left of the `α`-arcs: the `α`-crescent and the lens for the two new
arcs. -/
@[simp]
theorem addBasepoint_alphaLeft :
    (H.addBasepoint r₀).alphaLeft = Sum.elim (Sum.inl ∘ H.alphaLeft) ![Sum.inr 0, Sum.inr 2] :=
  (rfl)

/-- The regions to the right of the `α`-arcs: the remainder of `r₀` and the `β`-crescent for
the two new arcs. -/
@[simp]
theorem addBasepoint_alphaRight :
    (H.addBasepoint r₀).alphaRight =
      Sum.elim (Sum.inl ∘ H.alphaRight) ![Sum.inl r₀, Sum.inr 1] :=
  (rfl)

/-- The regions to the left of the `β`-arcs: the lens and the `β`-crescent for the two new
arcs. -/
@[simp]
theorem addBasepoint_betaLeft :
    (H.addBasepoint r₀).betaLeft = Sum.elim (Sum.inl ∘ H.betaLeft) ![Sum.inr 2, Sum.inr 1] :=
  (rfl)

/-- The regions to the right of the `β`-arcs: the `α`-crescent and the remainder of `r₀` for
the two new arcs. -/
@[simp]
theorem addBasepoint_betaRight :
    (H.addBasepoint r₀).betaRight =
      Sum.elim (Sum.inl ∘ H.betaRight) ![Sum.inr 0, Sum.inl r₀] :=
  (rfl)

/-- The old basepoints keep their regions, and the new basepoint lies in the lens. -/
@[simp]
theorem addBasepoint_basepoint :
    (H.addBasepoint r₀).basepoint = Sum.elim (Sum.inl ∘ H.basepoint) fun _ => Sum.inr 2 :=
  (rfl)

end Construction

section Generator

variable (r₀ : Region)

/-- The intersection points of the generator `x` together with the new point `k`, indexed by
the `α`-curves of the diagram with an added basepoint. -/
def addBasepointPoint (x : H.Generator) (k : Fin 2) : Fin (n + 1) → Point ⊕ Fin 2 :=
  Fin.lastCases (Sum.inr k) fun i => Sum.inl (H.point x i)

/-- On an old `α`-curve, `(x, k)` has the point of `x`. -/
@[simp]
theorem addBasepointPoint_castSucc (x : H.Generator) (k : Fin 2) (i : Fin n) :
    H.addBasepointPoint x k i.castSucc = Sum.inl (H.point x i) := by
  simp [addBasepointPoint]

/-- On the new `α`-curve, `(x, k)` has the new point `k`. -/
@[simp]
theorem addBasepointPoint_last (x : H.Generator) (k : Fin 2) :
    H.addBasepointPoint x k (Fin.last n) = Sum.inr k := by
  simp [addBasepointPoint]

private theorem alpha_addBasepointPoint (x : H.Generator) (k : Fin 2) (i : Fin (n + 1)) :
    (H.addBasepoint r₀).alpha (H.addBasepointPoint x k i) = i := by
  induction i using Fin.lastCases <;> simp

private theorem bijective_beta_addBasepointPoint (x : H.Generator) (k : Fin 2) :
    Bijective ((H.addBasepoint r₀).beta ∘ H.addBasepointPoint x k) := by
  refine Finite.injective_iff_bijective.mp fun a b hab => ?_
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp_all [Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

/-- The generator of the diagram with an added basepoint formed by a generator `x` of the
original diagram and the new point `k`. -/
noncomputable def addBasepointGenerator (x : H.Generator) (k : Fin 2) :
    (H.addBasepoint r₀).Generator :=
  (H.addBasepoint r₀).generatorOfPointChoice (H.addBasepointPoint x k)
    (H.alpha_addBasepointPoint r₀ x k) (H.bijective_beta_addBasepointPoint r₀ x k)

/-- The intersection point of `(x, k)` on the `α`-curve `i`. -/
@[simp]
theorem addBasepointGenerator_val (x : H.Generator) (k : Fin 2) (i : Fin (n + 1)) :
    ((H.addBasepointGenerator r₀ x k).2 i : Point ⊕ Fin 2) = H.addBasepointPoint x k i := by
  simp [addBasepointGenerator]

/-- Distinct pairs of an old generator and a new point give distinct generators. -/
theorem addBasepointGenerator_injective :
    Injective fun c : H.Generator × Fin 2 => H.addBasepointGenerator r₀ c.1 c.2 := by
  rintro ⟨x, k⟩ ⟨y, m⟩ h
  have h' (i : Fin (n + 1)) := congrArg (fun g : (H.addBasepoint r₀).Generator =>
    (g.2 i : Point ⊕ Fin 2)) h
  refine Prod.ext (H.point_injective (funext fun i => ?_)) ?_
  · simpa using h' i.castSucc
  · simpa using h' (Fin.last n)

/-- The generators `(x, k)` and `(y, m)` agree exactly when `x = y` and `k = m`. -/
@[simp]
theorem addBasepointGenerator_inj {x y : H.Generator} {k m : Fin 2} :
    H.addBasepointGenerator r₀ x k = H.addBasepointGenerator r₀ y m ↔ x = y ∧ k = m :=
  ((H.addBasepointGenerator_injective r₀).eq_iff (a := (x, k)) (b := (y, m))).trans Prod.ext_iff

/-- A point on an old `α`-curve of the diagram with an added basepoint is an old point. -/
private theorem exists_eq_inl_of_addBasepoint_alpha {p : Point ⊕ Fin 2} {i : Fin n}
    (hp : (H.addBasepoint r₀).alpha p = i.castSucc) : ∃ q, p = Sum.inl q ∧ H.alpha q = i := by
  rcases p with q | k
  · exact ⟨q, rfl, by simpa using hp⟩
  · exact absurd (by simpa using hp.symm) (Fin.castSucc_ne_last i)

/-- Every generator of the diagram with an added basepoint is an old generator together with a
new point: its point on the new `α`-curve is a new point, and its other points are old ones. -/
theorem addBasepointGenerator_surjective :
    Surjective fun c : H.Generator × Fin 2 => H.addBasepointGenerator r₀ c.1 c.2 := by
  intro g
  have hold (i : Fin n) : ∃ q, (g.2 i.castSucc : Point ⊕ Fin 2) = Sum.inl q ∧
      H.alpha q = i :=
    H.exists_eq_inl_of_addBasepoint_alpha r₀ (by simp)
  choose q hq hqα using hold
  obtain ⟨k, hk⟩ : ∃ k, (g.2 (Fin.last n) : Point ⊕ Fin 2) = Sum.inr k := by
    have := HeegaardIntersectionSystem.alpha_coe _ g (Fin.last n)
    rcases h : (g.2 (Fin.last n) : Point ⊕ Fin 2) with q' | k
    · simp [h, Fin.castSucc_ne_last] at this
    · exact ⟨k, rfl⟩
  have hβ : Bijective (H.beta ∘ q) := by
    refine Finite.injective_iff_bijective.mp fun a b hab => ?_
    have hg := (HeegaardIntersectionSystem.betaEquiv _ g).injective
    refine Fin.castSucc_injective n (hg ?_)
    simp only [HeegaardIntersectionSystem.betaEquiv_apply, HeegaardIntersectionSystem.point_apply,
      hq, addBasepoint_beta_inl]
    simpa using hab
  refine ⟨⟨H.generatorOfPointChoice q hqα hβ, k⟩, (H.addBasepoint r₀).point_injective ?_⟩
  funext i
  induction i using Fin.lastCases <;> simp [hq, hk]

/-- The generators of the diagram with an added basepoint are the pairs of a generator of the
original diagram and one of the two new intersection points. -/
noncomputable def addBasepointGeneratorEquiv :
    H.Generator × Fin 2 ≃ (H.addBasepoint r₀).Generator :=
  Equiv.ofBijective _ ⟨H.addBasepointGenerator_injective r₀, H.addBasepointGenerator_surjective r₀⟩

/-- The equivalence sends `(x, k)` to the generator `(x, k)`. -/
@[simp]
theorem addBasepointGeneratorEquiv_apply (c : H.Generator × Fin 2) :
    H.addBasepointGeneratorEquiv r₀ c = H.addBasepointGenerator r₀ c.1 c.2 :=
  (rfl)

/-- The inverse equivalence reads off the old generator and the new point. -/
@[simp]
theorem addBasepointGeneratorEquiv_symm_apply (x : H.Generator) (k : Fin 2) :
    (H.addBasepointGeneratorEquiv r₀).symm (H.addBasepointGenerator r₀ x k) = (x, k) :=
  (H.addBasepointGeneratorEquiv r₀).symm_apply_eq.mpr rfl

end Generator

section Domain

variable (r₀ : Region)

/-- The `0`-chain of the generator `(x, k)` restricted to the old intersection points is that of
`x`. -/
@[simp]
theorem generatorChain_addBasepointGenerator_inl (x : H.Generator) (k : Fin 2) (q : Point) :
    (H.addBasepoint r₀).generatorChain (H.addBasepointGenerator r₀ x k) (Sum.inl q) =
      H.generatorChain x q := by
  classical
  simp [HeegaardIntersectionSystem.generatorChain_apply]

/-- The `0`-chain of the generator `(x, k)` at the new intersection points is the indicator of
`k`. -/
@[simp]
theorem generatorChain_addBasepointGenerator_inr (x : H.Generator) (k m : Fin 2) :
    (H.addBasepoint r₀).generatorChain (H.addBasepointGenerator r₀ x k) (Sum.inr m) =
      if k = m then 1 else 0 := by
  classical
  simp [HeegaardIntersectionSystem.generatorChain_apply]

variable {x y : H.Generator} {i j : Fin 2}

/-- A domain of the diagram with an added basepoint connects `(x, i)` to `(y, j)` exactly when
its restriction to the old regions connects `x` to `y` and the multiplicities of the two
crescents, of the remainder of `r₀` and of the lens satisfy
`D(C_α) + D(C_β) - D(r₀) - D(L) = j - i`. -/
theorem isDomainBetween_addBasepoint_iff {D : Region ⊕ Fin 3 → ℤ} :
    (H.addBasepoint r₀).IsDomainBetween (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) D ↔
      H.IsDomainBetween x y (D ∘ Sum.inl) ∧
        D (Sum.inr 0) + D (Sum.inr 1) - D (Sum.inl r₀) - D (Sum.inr 2) = (j : ℤ) - i := by
  simp only [isDomainBetween_iff, funext_iff, Sum.forall, Fin.forall_fin_two, Pi.sub_apply,
    alphaArcBoundary_apply, betaArcBoundary_apply, alphaBoundary_apply, betaBoundary_apply,
    addBasepoint_alphaNext, addBasepoint_betaNext, addBasepoint_alphaLeft,
    addBasepoint_alphaRight, addBasepoint_betaLeft, addBasepoint_betaRight,
    generatorChain_addBasepointGenerator_inl, generatorChain_addBasepointGenerator_inr,
    Equiv.Perm.sumCongr_symm, Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- On the new arcs the boundary conditions read off the indicators of the new points.
  have hind : ∀ k : Fin 2,
      (if k = 1 then (1 : ℤ) else 0) = k ∧ (if k = 0 then (1 : ℤ) else 0) = 1 - k := by
    decide
  obtain ⟨hi₁, hi₀⟩ := hind i
  obtain ⟨hj₁, hj₀⟩ := hind j
  constructor
  · rintro ⟨⟨hα, -, h₂⟩, hβ, -, -⟩
    exact ⟨⟨hα, hβ⟩, by omega⟩
  · rintro ⟨⟨hα, hβ⟩, hs⟩
    exact ⟨⟨hα, by omega, by omega⟩, hβ, by omega, by omega⟩

end Domain

section MaslovIndex

variable (r₀ : Region)

/-- The point measure of a domain at an old intersection point is that of its restriction to
the old regions. -/
theorem pointMeasure_addBasepoint_inl (D : Region ⊕ Fin 3 → ℤ) (p : Point) :
    (H.addBasepoint r₀).pointMeasure D (Sum.inl p) = H.pointMeasure (D ∘ Sum.inl) p := by
  simp

/-- At both new intersection points, the four corners are the two crescents, the lens and the
remainder of `r₀`. -/
theorem pointMeasure_addBasepoint_inr (D : Region ⊕ Fin 3 → ℤ) (k : Fin 2) :
    (H.addBasepoint r₀).pointMeasure D (Sum.inr k) =
      ((D (Sum.inr 0) : ℚ) + D (Sum.inr 1) + D (Sum.inr 2) + D (Sum.inl r₀)) / 4 := by
  fin_cases k <;> simp <;> ring

/-- The point measure of a domain at the generator `(x, k)` is that of its restriction to the
old regions at `x` plus its point measure at the new point `k`. -/
theorem generatorPointMeasure_addBasepointGenerator (x : H.Generator) (k : Fin 2)
    (D : Region ⊕ Fin 3 → ℤ) :
    (H.addBasepoint r₀).generatorPointMeasure (H.addBasepointGenerator r₀ x k) D =
      H.generatorPointMeasure x (D ∘ Sum.inl) +
        ((D (Sum.inr 0) : ℚ) + D (Sum.inr 1) + D (Sum.inr 2) + D (Sum.inl r₀)) / 4 := by
  simp only [generatorPointMeasure_apply, HeegaardIntersectionSystem.point_apply,
    Fin.sum_univ_castSucc, addBasepointGenerator_val, addBasepointPoint_castSucc,
    addBasepointPoint_last, pointMeasure_addBasepoint_inl, pointMeasure_addBasepoint_inr]

section Euler

variable [DecidableEq Region]

/-- The region Euler characteristics after adding a basepoint in `r₀`: the region `r₀` loses an
open disc, so its Euler characteristic drops by one, and the two crescents and the lens are
discs. -/
def addBasepointEuler (χ : Region → ℤ) (r₀ : Region) : Region ⊕ Fin 3 → ℤ :=
  Sum.elim (χ - Pi.single r₀ 1) 1

/-- The Euler characteristic of an old region, one less for `r₀`. -/
@[simp]
theorem addBasepointEuler_inl (χ : Region → ℤ) (r₀ r : Region) :
    addBasepointEuler χ r₀ (Sum.inl r) = χ r - (Pi.single r₀ 1 : Region → ℤ) r :=
  (rfl)

/-- The new regions are discs. -/
@[simp]
theorem addBasepointEuler_inr (χ : Region → ℤ) (r₀ : Region) (k : Fin 3) :
    addBasepointEuler χ r₀ (Sum.inr k) = 1 :=
  (rfl)

variable [Fintype Point] [Fintype Region]

/-- The Maslov index of a domain of the diagram with an added basepoint is
`μ(D|_old) + D(C_α) + D(C_β) + D(L) - D(r₀)`, where `D|_old` is its restriction to the old
regions. -/
theorem maslovIndex_addBasepoint (χ : Region → ℤ) (x y : H.Generator) (i j : Fin 2)
    (D : Region ⊕ Fin 3 → ℤ) :
    (H.addBasepoint r₀).maslovIndex (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) D =
      H.maslovIndex χ x y (D ∘ Sum.inl) + D (Sum.inr 0) + D (Sum.inr 1) + D (Sum.inr 2) -
        D (Sum.inl r₀) := by
  simp only [maslovIndex_apply, eulerMeasure_eq_sub_sum_pointMeasure,
    generatorPointMeasure_addBasepointGenerator, Fintype.sum_sum_type, addBasepointEuler_inl,
    addBasepointEuler_inr, pointMeasure_addBasepoint_inl, pointMeasure_addBasepoint_inr,
    Fin.sum_univ_three, Fin.sum_univ_two, Function.comp_apply,
    Fintype.sum_intCast_sub_pi_single_mul]
  push_cast
  ring

end Euler

end MaslovIndex

section Hat

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region) {χ : Region → ℤ}

/-- The conditions for a domain of the diagram with an added basepoint in a region containing a
basepoint to be counted by the hat differential, read on the old regions and the three new ones.
-/
private theorem mem_hatDomains_addBasepoint_iff (hr₀ : r₀ ∈ Set.range H.basepoint)
    {x y : H.Generator} {i j : Fin 2} {D : Region ⊕ Fin 3 → ℤ} :
    D ∈ (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) ↔
      H.IsDomainBetween x y (D ∘ Sum.inl) ∧ (∀ z, D (Sum.inl (H.basepoint z)) = 0) ∧
        0 ≤ D ∘ Sum.inl ∧ 0 ≤ D (Sum.inr 0) ∧ 0 ≤ D (Sum.inr 1) ∧ D (Sum.inr 2) = 0 ∧
          D (Sum.inr 0) + D (Sum.inr 1) = (j : ℤ) - i ∧
            H.maslovIndex χ x y (D ∘ Sum.inl) + D (Sum.inr 0) + D (Sum.inr 1) = 1 := by
  obtain ⟨z₀, rfl⟩ := hr₀
  simp only [mem_hatDomains_iff, isDomainBetween_addBasepoint_iff, maslovIndex_addBasepoint,
    Sum.forall, addBasepoint_basepoint, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    Pi.le_def, Pi.zero_apply, Fin.forall_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    IsEmpty.forall_iff, and_true]
  constructor
  · rintro ⟨⟨hD, hs⟩, ⟨hz, h2⟩, ⟨hD0, h0, h1, -⟩, hμ⟩
    have hz₀ := hz z₀
    have h2 := h2 ()
    refine ⟨hD, hz, hD0, h0, h1, h2, by omega, ?_⟩
    rw [h2, hz₀] at hμ
    simpa using hμ
  · rintro ⟨hD, hz, hD0, h0, h1, h2, hs, hμ⟩
    have hz₀ := hz z₀
    refine ⟨⟨hD, by omega⟩, ⟨hz, fun _ => h2⟩, ⟨hD0, h0, h1, h2.ge⟩, ?_⟩
    rw [h2, hz₀]
    simpa using hμ

/-- Between generators with the same new point, the domains counted by the hat differential of
the diagram with an added basepoint in a region containing a basepoint are those of the original
diagram, extended by zero on the new regions. -/
theorem hatDomains_addBasepoint_self (hr₀ : r₀ ∈ Set.range H.basepoint) (x y : H.Generator)
    (i : Fin 2) :
    (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y i) =
      (fun D : Region → ℤ => (Sum.elim D 0 : Region ⊕ Fin 3 → ℤ)) '' H.hatDomains χ x y := by
  ext D
  rw [H.mem_hatDomains_addBasepoint_iff r₀ hr₀]
  constructor
  · rintro ⟨hD, hz, hD0, h0, h1, h2, hs, hμ⟩
    have h0' : D (Sum.inr 0) = 0 := by omega
    have h1' : D (Sum.inr 1) = 0 := by omega
    refine ⟨D ∘ Sum.inl, mem_hatDomains_iff.mpr ⟨hD, hz, hD0, by simpa [h0', h1'] using hμ⟩, ?_⟩
    funext r
    rcases r with r | k
    · rfl
    · fin_cases k <;> simp [h0', h1', h2]
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨hE, hz, hE0, hμ⟩ := mem_hatDomains_iff.mp hE
    exact ⟨by simpa using hE, by simpa using hz, by simpa using hE0, by simp, by simp, by simp,
      by simp, by simpa using hμ⟩

/-- From the new point `p` to the new point `q`, a domain counted by the hat differential of the
diagram with an added basepoint in a region containing a basepoint is a nonnegative domain of
Maslov index zero of the original diagram avoiding the basepoints, together with one of the two
crescents. -/
theorem hatDomains_addBasepoint_zero_one (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) :
    (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
        (H.addBasepointGenerator r₀ y 1) =
      (fun c : (Region → ℤ) × Fin 2 => Sum.elim c.1 (Pi.single c.2.castSucc 1)) ''
        ({E | H.IsDomainBetween x y E ∧ (∀ z, E (H.basepoint z) = 0) ∧ 0 ≤ E ∧
          H.maslovIndex χ x y E = 0} ×ˢ Set.univ) := by
  ext D
  rw [H.mem_hatDomains_addBasepoint_iff r₀ hr₀]
  constructor
  · rintro ⟨hD, hz, hD0, h0, h1, h2, hs, hμ⟩
    simp only [Fin.isValue, Fin.val_one, Fin.val_zero, Nat.cast_one, Nat.cast_zero,
      sub_zero] at hs
    obtain ⟨k, hk0, hk1⟩ : ∃ k : Fin 2, D (Sum.inr 0) = (Pi.single k 1 : Fin 2 → ℤ) 0 ∧
        D (Sum.inr 1) = (Pi.single k 1 : Fin 2 → ℤ) 1 := by
      rcases (by omega : D (Sum.inr 0) = 1 ∧ D (Sum.inr 1) = 0 ∨
          D (Sum.inr 0) = 0 ∧ D (Sum.inr 1) = 1) with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    refine ⟨⟨D ∘ Sum.inl, k⟩, ⟨⟨hD, hz, hD0, ?_⟩, Set.mem_univ _⟩, ?_⟩
    · have : (D (Sum.inr 0) : ℚ) + D (Sum.inr 1) = 1 := by exact_mod_cast hs
      linarith
    · funext r
      rcases r with r | m
      · rfl
      · fin_cases m <;> fin_cases k <;> simp_all
  · rintro ⟨⟨E, k⟩, ⟨⟨hE, hz, hE0, hμ⟩, -⟩, rfl⟩
    fin_cases k <;>
      exact ⟨by simpa using hE, by simpa using hz, by simpa using hE0, by simp, by simp, by simp,
        by simp, by simp [hμ]⟩

/-- No domain counted by the hat differential of the diagram with an added basepoint in a region
containing a basepoint runs from the new point `q` to the new point `p`. -/
theorem hatDomains_addBasepoint_one_zero (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) :
    (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x 1)
        (H.addBasepointGenerator r₀ y 0) = ∅ := by
  ext D
  simp only [H.mem_hatDomains_addBasepoint_iff r₀ hr₀, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, -, h0, h1, -, hs, -⟩
  simp at hs
  omega

/-- The coefficient of the hat differential of the diagram with an added basepoint in a region
containing a basepoint, from `(x, i)` to `(y, j)`, is that of the original diagram from `x` to
`y` when `i = j`, and zero otherwise: from `p` to `q` the counted domains come in pairs, one for
each crescent. -/
theorem hatCoefficient_addBasepoint (hr₀ : r₀ ∈ Set.range H.basepoint) (x y : H.Generator)
    (i j : Fin 2) :
    (H.addBasepoint r₀).hatCoefficient (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) = if i = j then H.hatCoefficient χ x y else 0 := by
  have hinj : Injective fun D : Region → ℤ => (Sum.elim D 0 : Region ⊕ Fin 3 → ℤ) :=
    fun D E h => funext fun r => congrFun h (Sum.inl r)
  have hinj' : Injective fun c : (Region → ℤ) × Fin 2 =>
      (Sum.elim c.1 (Pi.single c.2.castSucc 1) : Region ⊕ Fin 3 → ℤ) := by
    rintro ⟨D, k⟩ ⟨E, m⟩ h
    refine Prod.ext (funext fun r => congrFun h (Sum.inl r)) ?_
    simpa [Pi.single_apply, eq_comm] using congrFun h (Sum.inr k.castSucc)
  by_cases hij : i = j
  · subst hij
    simp [hatCoefficient_def, hatDomains_addBasepoint_self _ _ hr₀,
      Set.ncard_image_of_injective _ hinj]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 := by omega
  · -- From `p` to `q` each old counted domain gives two, one per crescent, and `2 = 0` mod two.
    simp [hatCoefficient_def, hatDomains_addBasepoint_zero_one _ _ hr₀,
      Set.ncard_image_of_injective _ hinj', Set.ncard_prod, CharTwo.two_eq_zero]
  · simp [hatCoefficient_def, hatDomains_addBasepoint_one_zero _ _ hr₀]

/-- Each crescent is a domain counted by the hat differential of the diagram with an added
basepoint from `(x, p)` to `(x, q)`: it has Maslov index one and avoids all basepoints, so `p`
and `q` lie one apart in relative Maslov grading. -/
theorem single_mem_hatDomains_addBasepoint (x : H.Generator) (k : Fin 2) :
    Pi.single (Sum.inr k.castSucc) 1 ∈
      (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x 0)
        (H.addBasepointGenerator r₀ x 1) := by
  have hinl : (Pi.single (Sum.inr k.castSucc) 1 : Region ⊕ Fin 3 → ℤ) ∘ Sum.inl = 0 :=
    funext fun r => by simp
  rw [mem_hatDomains_iff, isDomainBetween_addBasepoint_iff, maslovIndex_addBasepoint, hinl]
  refine ⟨⟨isDomainBetween_zero x, ?_⟩, fun z => ?_, fun r => ?_, ?_⟩
  · fin_cases k <;> simp
  · rcases z with z | z <;> fin_cases k <;> simp
  · rcases r with r | m
    · simp
    · fin_cases k <;> fin_cases m <;> simp
  · fin_cases k <;> simp

end Hat

section Differential

variable (r₀ : Region)

/-- The identification `CF̂_b ⊗ W ≅ CF̂_{b+1}` of the hat chain group of the original diagram
tensored with the two-dimensional space `W` on the new points with the hat chain group of the
diagram with an added basepoint, sending `x ⊗ k` to the generator `(x, k)`. -/
noncomputable def addBasepointChainEquiv :
    (H.Generator →₀ ZMod 2) ⊗[ZMod 2] (Fin 2 →₀ ZMod 2) ≃ₗ[ZMod 2]
      ((H.addBasepoint r₀).Generator →₀ ZMod 2) :=
  finsuppTensorFinsupp' (ZMod 2) H.Generator (Fin 2) ≪≫ₗ
    Finsupp.domLCongr (H.addBasepointGeneratorEquiv r₀)

/-- The coefficient of `(x, k)` in the image of a tensor is its `(x, k)` coefficient. -/
@[simp]
theorem addBasepointChainEquiv_apply (t : (H.Generator →₀ ZMod 2) ⊗[ZMod 2] (Fin 2 →₀ ZMod 2))
    (x : H.Generator) (k : Fin 2) :
    H.addBasepointChainEquiv r₀ t (H.addBasepointGenerator r₀ x k) =
      finsuppTensorFinsupp' (ZMod 2) H.Generator (Fin 2) t (x, k) := by
  simp [addBasepointChainEquiv, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]

/-- The identification sends `x ⊗ k` to the generator `(x, k)`. -/
@[simp]
theorem addBasepointChainEquiv_single_tmul_single (x : H.Generator) (k : Fin 2) (a b : ZMod 2) :
    H.addBasepointChainEquiv r₀ (Finsupp.single x a ⊗ₜ Finsupp.single k b) =
      Finsupp.single (H.addBasepointGenerator r₀ x k) (a * b) := by
  simp [addBasepointChainEquiv, finsuppTensorFinsupp'_single_tmul_single]

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- The hat differential of the diagram with an added basepoint in a region containing a
basepoint is `∂ ⊗ 1` on `CF̂_b ⊗ W`, where `∂` is the hat differential of the original diagram
and `W` carries the zero differential: under `TauCeti.HeegaardRegionSystem.addBasepointChainEquiv`
the hat complex of the new diagram is the tensor product of the old one with `W`. -/
theorem hatDifferential_comp_addBasepointChainEquiv (hr₀ : r₀ ∈ Set.range H.basepoint) :
    (H.addBasepoint r₀).hatDifferential (addBasepointEuler χ r₀) ∘ₗ
        (H.addBasepointChainEquiv r₀).toLinearMap =
      (H.addBasepointChainEquiv r₀).toLinearMap ∘ₗ
        TensorProduct.map (H.hatDifferential χ) LinearMap.id := by
  ext x k g
  obtain ⟨⟨y, m⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective g
  simp [hatCoefficient_addBasepoint _ _ hr₀, finsuppTensorFinsupp'_apply_apply,
    Finsupp.single_apply]

end Differential

section PeriodicDomain

variable (r₀ : Region)

/-- A domain of the diagram with an added basepoint in `r₀` is periodic exactly when its
restriction to the old regions is periodic, it vanishes on the lens, which contains the new
basepoint, and the multiplicities of the two crescents add up to that of the remainder of `r₀`. -/
theorem mem_periodicDomains_addBasepoint_iff {P : Region ⊕ Fin 3 → ℤ} :
    P ∈ (H.addBasepoint r₀).periodicDomains ↔
      P ∘ Sum.inl ∈ H.periodicDomains ∧ P (Sum.inr 2) = 0 ∧
        P (Sum.inr 0) + P (Sum.inr 1) = P (Sum.inl r₀) := by
  simp only [mem_periodicDomains_iff, funext_iff, Sum.forall, Fin.forall_fin_two, Pi.zero_apply,
    alphaArcBoundary_apply, betaArcBoundary_apply, alphaBoundary_apply, betaBoundary_apply,
    addBasepoint_alphaNext, addBasepoint_betaNext, addBasepoint_alphaLeft,
    addBasepoint_alphaRight, addBasepoint_betaLeft, addBasepoint_betaRight,
    addBasepoint_basepoint, Equiv.Perm.sumCongr_symm, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Equiv.symm_swap,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨hz, hL⟩, ⟨hα, -, hα₁⟩, hβ, -, -⟩
    exact ⟨⟨hz, hα, hβ⟩, hL (), by linarith [hL ()]⟩
  · rintro ⟨⟨hz, hα, hβ⟩, hL, hs⟩
    exact ⟨⟨hz, fun _ => hL⟩, ⟨hα, by omega, by omega⟩, hβ, by omega, by omega⟩

/-- **The periodic domains after adding a basepoint.** The periodic domains of the diagram with
an added basepoint in `r₀` are those of the original diagram together with the multiples of the
difference `C_α - C_β` of the two crescents. The pair `(Q, a)` goes to the extension of `Q` with
multiplicities `a` on `C_α`, `Q(r₀) - a` on `C_β` and `0` on the lens, and a periodic domain goes
to its restriction to the old regions and its multiplicity on `C_α`. Geometrically, `C_α - C_β`
is the class of the sphere bounding the ball around the new basepoint. -/
def addBasepointPeriodicDomainsEquiv :
    H.periodicDomains × ℤ ≃+ (H.addBasepoint r₀).periodicDomains where
  toFun c := ⟨Sum.elim (c.1 : Region → ℤ) ![c.2, (c.1 : Region → ℤ) r₀ - c.2, 0],
    (H.mem_periodicDomains_addBasepoint_iff r₀).mpr ⟨c.1.property, rfl, by simp⟩⟩
  invFun P := (⟨(P : Region ⊕ Fin 3 → ℤ) ∘ Sum.inl,
    ((H.mem_periodicDomains_addBasepoint_iff r₀).mp P.property).1⟩,
    (P : Region ⊕ Fin 3 → ℤ) (Sum.inr 0))
  left_inv c := by
    ext
    · rfl
    · simp
  right_inv P := by
    obtain ⟨-, h2, hs⟩ := (H.mem_periodicDomains_addBasepoint_iff r₀).mp P.property
    ext (r | k)
    · rfl
    · fin_cases k <;> simp [h2, ← hs]
  map_add' c d := by
    ext (r | k)
    · rfl
    · fin_cases k <;> simp [sub_add_sub_comm]

/-- The periodic domain attached to `(Q, a)` is `Q` extended by `a` on the `α`-crescent,
`Q(r₀) - a` on the `β`-crescent and `0` on the lens. -/
@[simp]
theorem coe_addBasepointPeriodicDomainsEquiv_apply (c : H.periodicDomains × ℤ) :
    (H.addBasepointPeriodicDomainsEquiv r₀ c : Region ⊕ Fin 3 → ℤ) =
      Sum.elim (c.1 : Region → ℤ) ![c.2, (c.1 : Region → ℤ) r₀ - c.2, 0] :=
  (rfl)

/-- When `r₀` contains a basepoint, the periodic domain attached to `(Q, 0)` is `Q` extended by
zero over the new regions: `Q` vanishes on `r₀`. -/
theorem coe_addBasepointPeriodicDomainsEquiv_mk_zero (hr₀ : r₀ ∈ Set.range H.basepoint)
    (Q : H.periodicDomains) :
    (H.addBasepointPeriodicDomainsEquiv r₀ (Q, 0) : Region ⊕ Fin 3 → ℤ) =
      Sum.elim (Q : Region → ℤ) 0 := by
  obtain ⟨z₀, rfl⟩ := hr₀
  have hQ : (Q : Region → ℤ) (H.basepoint z₀) = 0 :=
    (mem_periodicDomains_iff.mp Q.property).1 z₀
  funext s
  rcases s with s | k
  · simp
  · fin_cases k <;> simp [hQ]

/-- The old periodic domain attached to a periodic domain of the diagram with an added basepoint
is its restriction to the old regions. -/
@[simp]
theorem coe_addBasepointPeriodicDomainsEquiv_symm_apply_fst
    (P : (H.addBasepoint r₀).periodicDomains) :
    (((H.addBasepointPeriodicDomainsEquiv r₀).symm P).1 : Region → ℤ) =
      (P : Region ⊕ Fin 3 → ℤ) ∘ Sum.inl :=
  (rfl)

/-- The multiple of `C_α - C_β` attached to a periodic domain of the diagram with an added
basepoint is its multiplicity on the `α`-crescent. -/
@[simp]
theorem addBasepointPeriodicDomainsEquiv_symm_apply_snd
    (P : (H.addBasepoint r₀).periodicDomains) :
    ((H.addBasepointPeriodicDomainsEquiv r₀).symm P).2 = (P : Region ⊕ Fin 3 → ℤ) (Sum.inr 0) :=
  (rfl)

/-- A periodic domain `Q` of the original diagram extends to the periodic
domain of the diagram with an added basepoint with multiplicity `Q(r₀)` on the `α`-crescent and
`0` on the `β`-crescent and the lens. -/
private theorem sum_elim_mem_periodicDomains_addBasepoint {Q : Region → ℤ}
    (hQ : Q ∈ H.periodicDomains) :
    (Sum.elim Q ![Q r₀, 0, 0] : Region ⊕ Fin 3 → ℤ) ∈ (H.addBasepoint r₀).periodicDomains :=
  (H.mem_periodicDomains_addBasepoint_iff r₀).mpr ⟨hQ, rfl, by simp⟩

private theorem nonneg_sum_elim_addBasepoint {Q : Region → ℤ} (hQ₀ : 0 ≤ Q) :
    0 ≤ (Sum.elim Q ![Q r₀, 0, 0] : Region ⊕ Fin 3 → ℤ) := by
  rintro (r | k)
  · exact hQ₀ r
  · fin_cases k
    exacts [hQ₀ r₀, le_rfl, le_rfl]

/-- A nonnegative periodic domain of the diagram with an added basepoint vanishes when its
restriction to the old regions does: the two crescents are then nonnegative with sum zero. -/
private theorem eq_zero_of_mem_periodicDomains_addBasepoint {P : Region ⊕ Fin 3 → ℤ}
    (hP : P ∈ (H.addBasepoint r₀).periodicDomains) (hP₀ : 0 ≤ P) (hQ : P ∘ Sum.inl = 0) :
    P = 0 := by
  obtain ⟨-, h2, hs⟩ := (H.mem_periodicDomains_addBasepoint_iff r₀).mp hP
  have hr₀ : P (Sum.inl r₀) = 0 := congrFun hQ r₀
  have h0 := hP₀ (Sum.inr 0)
  have h1 := hP₀ (Sum.inr 1)
  funext r
  rcases r with r | k
  · exact congrFun hQ r
  · fin_cases k <;> simp at h0 h1 ⊢ <;> omega

/-- Adding a basepoint preserves and reflects weak admissibility: the new periodic domains
`a (C_α - C_β)` have coefficients of both signs when `a ≠ 0`. -/
@[simp]
theorem weaklyAdmissible_addBasepoint_iff :
    (H.addBasepoint r₀).WeaklyAdmissible ↔ H.WeaklyAdmissible := by
  rw [weaklyAdmissible_iff, weaklyAdmissible_iff]
  constructor
  · intro h Q hQ hQ₀
    have := h _ (H.sum_elim_mem_periodicDomains_addBasepoint r₀ hQ)
      (nonneg_sum_elim_addBasepoint r₀ hQ₀)
    exact funext fun r => congrFun this (Sum.inl r)
  · intro h P hP hP₀
    exact H.eq_zero_of_mem_periodicDomains_addBasepoint r₀ hP hP₀
      (h _ ((H.mem_periodicDomains_addBasepoint_iff r₀).mp hP).1 fun r => hP₀ (Sum.inl r))

end PeriodicDomain

section PeriodicMaslovIndex

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region) (χ : Region → ℤ)

/-- A periodic domain of the diagram with an added basepoint has, at every generator `(x, i)`, the
Maslov index of its restriction to the old regions at `x`: the crescents and the remainder of
`r₀` cancel in the index formula, and the lens has multiplicity zero. In particular `C_α - C_β` has
Maslov index zero. -/
theorem maslovIndex_addBasepoint_of_mem_periodicDomains (x : H.Generator) (i : Fin 2)
    {P : Region ⊕ Fin 3 → ℤ} (hP : P ∈ (H.addBasepoint r₀).periodicDomains) :
    (H.addBasepoint r₀).maslovIndex (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ x i) P = H.maslovIndex χ x x (P ∘ Sum.inl) := by
  obtain ⟨-, h2, hs⟩ := (H.mem_periodicDomains_addBasepoint_iff r₀).mp hP
  have hs' : (P (Sum.inr 0) : ℚ) + P (Sum.inr 1) = P (Sum.inl r₀) := by exact_mod_cast hs
  rw [maslovIndex_addBasepoint, h2]
  push_cast
  linarith

/-- Adding a basepoint does not change the periodic Maslov indices at a generator. -/
@[simp]
theorem periodicMaslovIndices_addBasepoint (x : H.Generator) (i : Fin 2) :
    (H.addBasepoint r₀).periodicMaslovIndices (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) = H.periodicMaslovIndices χ x := by
  ext q
  simp only [mem_periodicMaslovIndices_iff]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P ∘ Sum.inl, ((H.mem_periodicDomains_addBasepoint_iff r₀).mp hP).1,
      (H.maslovIndex_addBasepoint_of_mem_periodicDomains r₀ χ x i hP).symm⟩
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨_, H.sum_elim_mem_periodicDomains_addBasepoint r₀ hQ, ?_⟩
    rw [H.maslovIndex_addBasepoint_of_mem_periodicDomains r₀ χ x i
      (H.sum_elim_mem_periodicDomains_addBasepoint r₀ hQ), Sum.elim_comp_inl]

/-- Adding a basepoint preserves and reflects weak admissibility at a generator, the condition
of weak admissibility for the spin^c structure of that generator. -/
@[simp]
theorem weaklyAdmissibleAt_addBasepoint_iff (x : H.Generator) (i : Fin 2) :
    (H.addBasepoint r₀).WeaklyAdmissibleAt (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) ↔ H.WeaklyAdmissibleAt χ x := by
  rw [weaklyAdmissibleAt_iff, weaklyAdmissibleAt_iff]
  constructor
  · intro h Q hQ hμ hQ₀
    have hP := H.sum_elim_mem_periodicDomains_addBasepoint r₀ hQ
    have := h _ hP (by rw [H.maslovIndex_addBasepoint_of_mem_periodicDomains r₀ χ x i hP]; exact hμ)
      (nonneg_sum_elim_addBasepoint r₀ hQ₀)
    exact funext fun r => congrFun this (Sum.inl r)
  · intro h P hP hμ hP₀
    rw [H.maslovIndex_addBasepoint_of_mem_periodicDomains r₀ χ x i hP] at hμ
    exact H.eq_zero_of_mem_periodicDomains_addBasepoint r₀ hP hP₀
      (h _ ((H.mem_periodicDomains_addBasepoint_iff r₀).mp hP).1 hμ fun r => hP₀ (Sum.inl r))

/-- Adding a basepoint preserves and reflects strong admissibility at a generator. -/
@[simp]
theorem stronglyAdmissible_addBasepoint_iff (x : H.Generator) (i : Fin 2) :
    (H.addBasepoint r₀).StronglyAdmissible (addBasepointEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) ↔ H.StronglyAdmissible χ x := by
  rw [stronglyAdmissible_iff, stronglyAdmissible_iff]
  constructor
  · intro h Q hQ hQ0 hμ
    have hP := H.sum_elim_mem_periodicDomains_addBasepoint r₀ hQ
    have hμP := H.maslovIndex_addBasepoint_of_mem_periodicDomains r₀ χ x i hP
    rw [Sum.elim_comp_inl] at hμP
    obtain ⟨r | k, hr⟩ := h _ hP (fun h0 => hQ0 (funext fun r => congrFun h0 (Sum.inl r)))
      (by rw [hμP]; exact hμ)
    · exact ⟨r, by rwa [hμP] at hr⟩
    · rw [hμP] at hr
      -- Only the `α`-crescent can carry a coefficient above half the nonnegative index.
      generalize H.maslovIndex χ x x Q = μ at hμ hr ⊢
      fin_cases k
      · exact ⟨r₀, hr⟩
      all_goals simp at hr; linarith
  · intro h P hP hP0 hμ
    rw [H.maslovIndex_addBasepoint_of_mem_periodicDomains r₀ χ x i hP] at hμ ⊢
    by_cases hQ : P ∘ Sum.inl = 0
    · -- A new periodic domain `a (C_α - C_β)` with `a ≠ 0` has a positive coefficient, which is
      -- more than half its index zero: otherwise `-P` would be a nonnegative periodic domain
      -- vanishing on the old regions, hence zero.
      rw [hQ, map_zero, zero_div]
      by_contra! hle
      refine hP0 (neg_eq_zero.mp (H.eq_zero_of_mem_periodicDomains_addBasepoint r₀ (neg_mem hP)
        (fun r => ?_) (by rw [Pi.neg_comp, hQ, neg_zero])))
      simpa using hle r
    · obtain ⟨r, hr⟩ := h _ ((H.mem_periodicDomains_addBasepoint_iff r₀).mp hP).1 hQ hμ
      exact ⟨Sum.inl r, hr⟩

end PeriodicMaslovIndex

section RelativeGrading

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint] (r₀ : Region)
  {χ : Region → ℤ}

/-- **The grading normalization survives adding a basepoint.** Suppose every domain `E` from a
generator of the original diagram to itself has `μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` among the periodic Maslov
indices, the normalization under which its relative grading is well defined. Then so does every
such domain of the diagram with an added basepoint. -/
theorem maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_addBasepoint
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x) :
    ∀ (x : (H.addBasepoint r₀).Generator) (E : Region ⊕ Fin 3 → ℤ),
      (H.addBasepoint r₀).IsDomainBetween x x E →
        (H.addBasepoint r₀).maslovIndex (addBasepointEuler χ r₀) x x E -
            2 * ∑ z, (E ((H.addBasepoint r₀).basepoint z) : ℚ) ∈
          (H.addBasepoint r₀).periodicMaslovIndices (addBasepointEuler χ r₀) x := by
  intro x' E hE
  obtain ⟨⟨x, i⟩, rfl⟩ := (H.addBasepointGeneratorEquiv r₀).surjective x'
  rw [addBasepointGeneratorEquiv_apply] at hE ⊢
  obtain ⟨hE, hs⟩ := (H.isDomainBetween_addBasepoint_iff r₀).mp hE
  have hs' : (E (Sum.inr 0) : ℚ) + E (Sum.inr 1) - E (Sum.inl r₀) - E (Sum.inr 2) = 0 := by
    exact_mod_cast hs.trans (sub_self _)
  rw [periodicMaslovIndices_addBasepoint, maslovIndex_addBasepoint]
  -- The crescents and the remainder of `r₀` cancel, and the lens contributes `2 n_L` to the
  -- Maslov index and `n_L` to the multiplicity at the new basepoint.
  convert hself x _ hE using 1
  simp only [addBasepoint_basepoint, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, Finset.univ_unique, Finset.sum_singleton]
  linarith

variable {H}
variable (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
  H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)

include hself

/-- **The relative grading after adding a basepoint**, modulo the periodic Maslov indices: when the
original diagram satisfies the relative-grading normalization `hself` (`μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` is a
periodic Maslov index for every domain `E` from a generator to itself) and a domain joins `x` to
`y`, the generators `(x, i)` and `(y, j)` of the diagram with an added basepoint have relative
grading `gr(x, y) + j - i`. -/
theorem IsDomainBetween.coe_relativeGrading_addBasepoint {x y : H.Generator} {D : Region → ℤ}
    (hD : H.IsDomainBetween x y D) (i j : Fin 2) :
    ((H.addBasepoint r₀).relativeGrading (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) : ℚ ⧸ H.periodicMaslovIndices χ x) =
      ((H.relativeGrading χ x y + (j - i : ℚ) : ℚ) : ℚ ⧸ H.periodicMaslovIndices χ x) := by
  -- Extend `D` by `D(r₀) + j - i` on the `α`-crescent and by zero on the other new regions.
  have hD' : (H.addBasepoint r₀).IsDomainBetween (H.addBasepointGenerator r₀ x i)
      (H.addBasepointGenerator r₀ y j) (Sum.elim D ![D r₀ + (j - i), 0, 0]) :=
    (H.isDomainBetween_addBasepoint_iff r₀).mpr ⟨hD, by simp⟩
  have h' := hD'.coe_relativeGrading_eq
    (H.maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_addBasepoint r₀ hself)
  rw [periodicMaslovIndices_addBasepoint] at h'
  rw [h', QuotientAddGroup.mk_add, hD.coe_relativeGrading_eq hself, ← QuotientAddGroup.mk_add]
  congr 1
  rw [maslovIndex_addBasepoint]
  simp only [addBasepoint_basepoint, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, Finset.univ_unique, Finset.sum_singleton, Sum.elim_comp_inl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  push_cast
  ring

/-- **The relative grading after adding a basepoint**: when the original diagram satisfies the
relative-grading normalization `hself` (`μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` is a periodic Maslov index for
every domain `E` from a generator to itself), its periodic domains have Maslov index zero at `x`
and a domain joins `x` to `y`, the generators `(x, i)` and
`(y, j)` of the diagram with an added basepoint have relative grading `gr(x, y) + j - i`. -/
theorem IsDomainBetween.relativeGrading_addBasepoint {x y : H.Generator} {D : Region → ℤ}
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (hD : H.IsDomainBetween x y D)
    (i j : Fin 2) :
    (H.addBasepoint r₀).relativeGrading (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) = H.relativeGrading χ x y + (j - i : ℚ) := by
  have h := QuotientAddGroup.eq_iff_sub_mem.mp (hD.coe_relativeGrading_addBasepoint r₀ hself i j)
  rwa [periodicMaslovIndices_eq_bot_iff.mpr hP, AddSubgroup.mem_bot, sub_eq_zero] at h

/-- The two generators `(x, i)` and `(x, j)` of the diagram with an added basepoint have relative
grading `j - i` when the original diagram satisfies the relative-grading normalization `hself`
(`μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` is a periodic Maslov index for every domain `E` from a generator to
itself) and its periodic domains have Maslov index zero at `x`. -/
theorem relativeGrading_addBasepoint_self {x : H.Generator}
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (i j : Fin 2) :
    (H.addBasepoint r₀).relativeGrading (addBasepointEuler χ r₀) (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ x j) = (j - i : ℚ) := by
  rw [(isDomainBetween_zero x).relativeGrading_addBasepoint r₀ hself hP,
    relativeGrading_self hself hP, zero_add]

end RelativeGrading

end HeegaardRegionSystem

end TauCeti
