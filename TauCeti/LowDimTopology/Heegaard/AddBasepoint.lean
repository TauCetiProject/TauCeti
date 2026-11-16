/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.LowDimTopology.Heegaard.HatDifferential

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

## Main definitions

* `TauCeti.HeegaardRegionSystem.addBasepoint`: the diagram with a basepoint added in a region.
* `TauCeti.HeegaardRegionSystem.addBasepointEuler`: its region Euler characteristics.
* `TauCeti.HeegaardRegionSystem.addBasepointGenerator`: the generator `(x, i)`.
* `TauCeti.HeegaardRegionSystem.addBasepointGeneratorEquiv`: the generators of the new diagram
  are the pairs of an old generator and a new point.
* `TauCeti.HeegaardRegionSystem.addBasepointChainEquiv`: the resulting identification of hat
  chain groups `CF̂_{b+1} ≅ CF̂_b ⊗ W`.

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

## References

* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830)
  (multipointed nice diagrams, whose hat homology is that of a singly pointed diagram tensored
  with one two-dimensional factor for each additional basepoint).
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
  alphaNext_isCycleOn := Equiv.Perm.isCycleOn_sumCongr_swap_fiber H.alphaNext_isCycleOn
  betaNext := Equiv.Perm.sumCongr H.betaNext (Equiv.swap 0 1)
  betaNext_isCycleOn := Equiv.Perm.isCycleOn_sumCongr_swap_fiber H.betaNext_isCycleOn
  alphaLeft := Sum.elim (Sum.inl ∘ H.alphaLeft) ![Sum.inr 0, Sum.inr 2]
  alphaRight := Sum.elim (Sum.inl ∘ H.alphaRight) ![Sum.inl r₀, Sum.inr 1]
  betaLeft := Sum.elim (Sum.inl ∘ H.betaLeft) ![Sum.inr 2, Sum.inr 1]
  betaRight := Sum.elim (Sum.inl ∘ H.betaRight) ![Sum.inr 0, Sum.inl r₀]
  regionNonempty := ⟨Sum.inr 0⟩
  crossingCompatible := by
    rintro (p | k)
    · rcases H.crossingCompatible p with h | h
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
    Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Equiv.symm_swap]
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Nat.cast_zero, Nat.cast_one] <;> constructor
  all_goals first
    | rintro ⟨⟨hα, -, h₂⟩, hβ, -, -⟩
      exact ⟨⟨hα, hβ⟩, by simp at h₂; omega⟩
    | rintro ⟨⟨hα, hβ⟩, hs⟩
      refine ⟨⟨hα, ?_, ?_⟩, hβ, ?_, ?_⟩ <;> simp <;> omega

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
  have hχ : ∑ r, (((χ r - (Pi.single r₀ 1 : Region → ℤ) r : ℤ) : ℚ)) * D (Sum.inl r) =
      ∑ r, (χ r : ℚ) * D (Sum.inl r) - D (Sum.inl r₀) := by
    simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  simp only [maslovIndex_apply, eulerMeasure_eq_sub_sum_pointMeasure,
    generatorPointMeasure_addBasepointGenerator, Fintype.sum_sum_type, addBasepointEuler_inl,
    addBasepointEuler_inr, pointMeasure_addBasepoint_inl, pointMeasure_addBasepoint_inr,
    Fin.sum_univ_three, Fin.sum_univ_two, Function.comp_apply, hχ]
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

end HeegaardRegionSystem

end TauCeti
