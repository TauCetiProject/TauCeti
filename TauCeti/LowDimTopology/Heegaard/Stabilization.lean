/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.LowDimTopology.Heegaard.HatDifferential
public import TauCeti.LowDimTopology.Heegaard.Nice
public import TauCeti.LowDimTopology.Heegaard.RelativeGrading
public import TauCeti.LowDimTopology.Heegaard.StrongAdmissibility

/-!
# Stabilizing a Heegaard diagram

The genus of a pointed Heegaard diagram `(Σ, α, β, z)` can be raised by one by a *stabilization*:
take the connected sum of `Σ` with a torus `T²` at a point of a region `R₀` away from the
basepoints, and add to `α` and `β` a pair of curves `α'` and `β'` on the torus meeting
transversally in a single point `x₀`. The complement of `α' ∪ β'` in `T²` is an open square, so the
connected sum merges it into `R₀`: the stabilized diagram has the same regions, with `R₀` replaced
by its connected sum with a disc, whose Euler characteristic is one less, and which acquires the
four corners of the square, all at `x₀`. The generators of the stabilized diagram are the
generators of the original one together with `x₀`, and Ozsváth and Szabó show that stabilization
induces an isomorphism of the hat complexes. This file performs the move on the incidence data
`TauCeti.HeegaardRegionSystem` and proves the combinatorial content of that isomorphism: domains,
their Maslov indices and the domains counted by the hat differential are unchanged.

The move is `TauCeti.HeegaardRegionSystem.stabilize r₀`. The intersection points become
`Point ⊕ Unit`, with `x₀ = Sum.inr ()`; the new curves are the last `α`- and `β`-curves, each made
of the single arc from `x₀` back to itself, with the region `r₀` on both of its sides; the regions
and the basepoints are unchanged. The region Euler characteristics drop by one at `r₀`
(`TauCeti.HeegaardRegionSystem.stabilizeEuler`), and `r₀` gains four corners
(`TauCeti.HeegaardRegionSystem.cornerCount_stabilize`), so the closed-surface normalization
`∑ χ(R) - #(α ∩ β) = 2 - 2n` passes from genus `n` to genus `n + 1`
(`TauCeti.HeegaardRegionSystem.sum_stabilizeEuler_sub_card`).

A generator `x` gives the generator `x ∪ {x₀}` of the stabilized diagram, and every generator
arises in this way exactly once (`TauCeti.HeegaardRegionSystem.stabilizeGeneratorEquiv`), since
`x₀` is the only point on the new curves. Each new arc has the same region on both sides, so it
contributes nothing to the boundary of a domain, and the point `x₀` lies in both generators: a
domain connects `x ∪ {x₀}` to `y ∪ {x₀}` exactly when it connects `x` to `y`
(`TauCeti.HeegaardRegionSystem.isDomainBetween_stabilize_iff`), and the periodic domains are the
same (`TauCeti.HeegaardRegionSystem.periodicDomains_stabilize`). In Lipshitz's formula
`μ(D) = e(D) + n_x(D) + n_y(D)` the Euler measure loses `2 D(r₀)`, one for the lost Euler
characteristic and one for the four new quarter corners, while each point measure gains the
multiplicity `D(r₀)` of the four corners at `x₀`, so the Maslov index is unchanged
(`TauCeti.HeegaardRegionSystem.maslovIndex_stabilize`). Consequently weak and strong
admissibility, the relative grading and the domains counted by the hat differential are those of
the original diagram, and under the identification of the hat chain groups by
`TauCeti.HeegaardRegionSystem.stabilizeChainEquiv` the hat differentials agree
(`TauCeti.HeegaardRegionSystem.hatDifferential_comp_stabilizeChainEquiv`). None of this needs the
region `r₀` to avoid the basepoints. When `r₀` contains a basepoint, as it does in the usual
stabilization next to the basepoint, the stabilized diagram is nice exactly when the original one
is (`TauCeti.HeegaardRegionSystem.isNice_stabilize_iff`), since `r₀` is the only region that
changes.

## Main definitions

* `TauCeti.HeegaardRegionSystem.stabilize`: the stabilization of a diagram in a region.
* `TauCeti.HeegaardRegionSystem.stabilizeEuler`: its region Euler characteristics.
* `TauCeti.HeegaardRegionSystem.stabilizeGenerator`: the generator `x ∪ {x₀}`.
* `TauCeti.HeegaardRegionSystem.stabilizeGeneratorEquiv`: the generators of the stabilized
  diagram are those of the original one.
* `TauCeti.HeegaardRegionSystem.stabilizeChainEquiv`: the resulting identification of hat chain
  groups.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_stabilize_iff` and
  `TauCeti.HeegaardRegionSystem.periodicDomains_stabilize`: domains and periodic domains are
  unchanged.
* `TauCeti.HeegaardRegionSystem.maslovIndex_stabilize`: so are Maslov indices.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_stabilize_iff`,
  `TauCeti.HeegaardRegionSystem.weaklyAdmissibleAt_stabilize_iff` and
  `TauCeti.HeegaardRegionSystem.stronglyAdmissible_stabilize_iff`: so are the admissibility
  conditions.
* `TauCeti.HeegaardRegionSystem.relativeGrading_stabilize`: so is the relative grading.
* `TauCeti.HeegaardRegionSystem.hatDomains_stabilize` and
  `TauCeti.HeegaardRegionSystem.hatDifferential_comp_stabilizeChainEquiv`: so are the domains
  counted by the hat differential, and the hat differential itself.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §10 (stabilization invariance,
  Theorem 10.2).
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4, for the index formula.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Function

section Construction

/-- The stabilization of a diagram in the region `r₀`: the connected sum with a torus carrying a
new `α`-curve and a new `β`-curve, the last curves, meeting in the single new point `Sum.inr ()`.
Each new curve is one arc from the new point back to itself, and the region on both of its sides
is `r₀`, which now stands for the connected sum of `r₀` with the square cut out of the torus by the
new curves. The regions and the basepoints are those of the original diagram. -/
def stabilize (r₀ : Region) :
    HeegaardRegionSystem (n + 1) (Point ⊕ Unit) Region Basepoint where
  pointFintype := letI := H.pointFintype; inferInstance
  alpha := Sum.elim (fun p => (H.alpha p).castSucc) fun _ => Fin.last n
  beta := Sum.elim (fun p => (H.beta p).castSucc) fun _ => Fin.last n
  alphaNext := Equiv.Perm.sumCongr H.alphaNext 1
  alphaNext_isCycleOn := Equiv.Perm.isCycleOn_sumCongr_fiber H.alphaNext_isCycleOn
    (Equiv.Perm.isCycleOn_of_subsingleton _ _)
  betaNext := Equiv.Perm.sumCongr H.betaNext 1
  betaNext_isCycleOn := Equiv.Perm.isCycleOn_sumCongr_fiber H.betaNext_isCycleOn
    (Equiv.Perm.isCycleOn_of_subsingleton _ _)
  alphaLeft := Sum.elim H.alphaLeft fun _ => r₀
  alphaRight := Sum.elim H.alphaRight fun _ => r₀
  betaLeft := Sum.elim H.betaLeft fun _ => r₀
  betaRight := Sum.elim H.betaRight fun _ => r₀
  regionNonempty := H.regionNonempty
  crossingCompatible := by
    rintro (p | -)
    · simpa [isCrossingCompatible_iff] using H.crossingCompatible p
    · simp [isCrossingCompatible_iff]
  regionCovered r := by
    rcases H.regionCovered r with ⟨p, hp⟩ | ⟨-, hR⟩
    · exact Or.inl ⟨Sum.inl p, by simpa using hp⟩
    · exact Or.inl ⟨Sum.inr (), by simp [Subsingleton.elim r r₀]⟩
  basepoint := H.basepoint

variable (r₀ : Region)

/-- The old points keep their `α`-curves. -/
@[simp]
theorem stabilize_alpha_inl (p : Point) :
    (H.stabilize r₀).alpha (Sum.inl p) = (H.alpha p).castSucc :=
  (rfl)

/-- The new point lies on the new last `α`-curve. -/
@[simp]
theorem stabilize_alpha_inr (u : Unit) : (H.stabilize r₀).alpha (Sum.inr u) = Fin.last n :=
  (rfl)

/-- The old points keep their `β`-curves. -/
@[simp]
theorem stabilize_beta_inl (p : Point) :
    (H.stabilize r₀).beta (Sum.inl p) = (H.beta p).castSucc :=
  (rfl)

/-- The new point lies on the new last `β`-curve. -/
@[simp]
theorem stabilize_beta_inr (u : Unit) : (H.stabilize r₀).beta (Sum.inr u) = Fin.last n :=
  (rfl)

/-- The successor along the `α`-curves: the old one on the old points, and the new point is its
own successor on the new curve. -/
@[simp]
theorem stabilize_alphaNext :
    (H.stabilize r₀).alphaNext = Equiv.Perm.sumCongr H.alphaNext 1 :=
  (rfl)

/-- The successor along the `β`-curves: the old one on the old points, and the new point is its
own successor on the new curve. -/
@[simp]
theorem stabilize_betaNext :
    (H.stabilize r₀).betaNext = Equiv.Perm.sumCongr H.betaNext 1 :=
  (rfl)

/-- The regions to the left of the `α`-arcs: `r₀` for the new arc. -/
@[simp]
theorem stabilize_alphaLeft : (H.stabilize r₀).alphaLeft = Sum.elim H.alphaLeft fun _ => r₀ :=
  (rfl)

/-- The regions to the right of the `α`-arcs: `r₀` for the new arc. -/
@[simp]
theorem stabilize_alphaRight :
    (H.stabilize r₀).alphaRight = Sum.elim H.alphaRight fun _ => r₀ :=
  (rfl)

/-- The regions to the left of the `β`-arcs: `r₀` for the new arc. -/
@[simp]
theorem stabilize_betaLeft : (H.stabilize r₀).betaLeft = Sum.elim H.betaLeft fun _ => r₀ :=
  (rfl)

/-- The regions to the right of the `β`-arcs: `r₀` for the new arc. -/
@[simp]
theorem stabilize_betaRight : (H.stabilize r₀).betaRight = Sum.elim H.betaRight fun _ => r₀ :=
  (rfl)

/-- The basepoints keep their regions. -/
@[simp]
theorem stabilize_basepoint : (H.stabilize r₀).basepoint = H.basepoint :=
  (rfl)

end Construction

section Generator

variable (r₀ : Region)

/-- The intersection points of the generator `x` together with the new point, indexed by the
`α`-curves of the stabilized diagram. -/
def stabilizePoint (x : H.Generator) : Fin (n + 1) → Point ⊕ Unit :=
  Fin.lastCases (Sum.inr ()) fun i => Sum.inl (H.point x i)

/-- On an old `α`-curve, `x ∪ {x₀}` has the point of `x`. -/
@[simp]
theorem stabilizePoint_castSucc (x : H.Generator) (i : Fin n) :
    H.stabilizePoint x i.castSucc = Sum.inl (H.point x i) := by
  simp [stabilizePoint]

/-- On the new `α`-curve, `x ∪ {x₀}` has the new point. -/
@[simp]
theorem stabilizePoint_last (x : H.Generator) : H.stabilizePoint x (Fin.last n) = Sum.inr () := by
  simp [stabilizePoint]

private theorem alpha_stabilizePoint (x : H.Generator) (i : Fin (n + 1)) :
    (H.stabilize r₀).alpha (H.stabilizePoint x i) = i := by
  induction i using Fin.lastCases <;> simp

private theorem bijective_beta_stabilizePoint (x : H.Generator) :
    Bijective ((H.stabilize r₀).beta ∘ H.stabilizePoint x) := by
  refine Finite.injective_iff_bijective.mp fun a b hab => ?_
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp_all [Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

/-- The generator `x ∪ {x₀}` of the stabilized diagram formed by a generator `x` of the original
diagram and the new point. -/
noncomputable def stabilizeGenerator (x : H.Generator) : (H.stabilize r₀).Generator :=
  (H.stabilize r₀).generatorOfPointChoice (H.stabilizePoint x) (H.alpha_stabilizePoint r₀ x)
    (H.bijective_beta_stabilizePoint r₀ x)

/-- The intersection point of `x ∪ {x₀}` on the `α`-curve `i`. -/
@[simp]
theorem stabilizeGenerator_val (x : H.Generator) (i : Fin (n + 1)) :
    ((H.stabilizeGenerator r₀ x).2 i : Point ⊕ Unit) = H.stabilizePoint x i := by
  simp [stabilizeGenerator]

/-- Distinct generators give distinct generators of the stabilized diagram. -/
theorem stabilizeGenerator_injective : Injective (H.stabilizeGenerator r₀) := by
  intro x y h
  refine H.point_injective (funext fun i => ?_)
  simpa using congrArg (fun g : (H.stabilize r₀).Generator => (g.2 i.castSucc : Point ⊕ Unit)) h

/-- A point on an old `α`-curve of the stabilized diagram is an old point. -/
private theorem exists_eq_inl_of_stabilize_alpha {p : Point ⊕ Unit} {i : Fin n}
    (hp : (H.stabilize r₀).alpha p = i.castSucc) : ∃ q, p = Sum.inl q ∧ H.alpha q = i := by
  rcases p with q | u
  · exact ⟨q, rfl, by simpa using hp⟩
  · exact absurd (by simpa using hp.symm) (Fin.castSucc_ne_last i)

/-- Every generator of the stabilized diagram is `x ∪ {x₀}` for a generator `x` of the original
diagram: its point on the new `α`-curve is the new point, and its other points are old ones. -/
theorem stabilizeGenerator_surjective : Surjective (H.stabilizeGenerator r₀) := by
  intro g
  have hold (i : Fin n) : ∃ q, (g.2 i.castSucc : Point ⊕ Unit) = Sum.inl q ∧ H.alpha q = i :=
    H.exists_eq_inl_of_stabilize_alpha r₀ (by simp)
  choose q hq hqα using hold
  have hlast : (g.2 (Fin.last n) : Point ⊕ Unit) = Sum.inr () := by
    have := HeegaardIntersectionSystem.alpha_coe _ g (Fin.last n)
    rcases h : (g.2 (Fin.last n) : Point ⊕ Unit) with q' | u
    · simp [h, Fin.castSucc_ne_last] at this
    · rfl
  have hβ : Bijective (H.beta ∘ q) := by
    refine Finite.injective_iff_bijective.mp fun a b hab => ?_
    have hg := (HeegaardIntersectionSystem.betaEquiv _ g).injective
    refine Fin.castSucc_injective n (hg ?_)
    simp only [HeegaardIntersectionSystem.betaEquiv_apply, HeegaardIntersectionSystem.point_apply,
      hq, stabilize_beta_inl]
    simpa using hab
  refine ⟨H.generatorOfPointChoice q hqα hβ, (H.stabilize r₀).point_injective ?_⟩
  funext i
  induction i using Fin.lastCases <;> simp [hq, hlast]

/-- The generators of the stabilized diagram are those of the original diagram, each together with
the new intersection point. -/
noncomputable def stabilizeGeneratorEquiv : H.Generator ≃ (H.stabilize r₀).Generator :=
  Equiv.ofBijective _ ⟨H.stabilizeGenerator_injective r₀, H.stabilizeGenerator_surjective r₀⟩

/-- The equivalence sends `x` to `x ∪ {x₀}`. -/
@[simp]
theorem stabilizeGeneratorEquiv_apply (x : H.Generator) :
    H.stabilizeGeneratorEquiv r₀ x = H.stabilizeGenerator r₀ x :=
  (rfl)

/-- The inverse equivalence forgets the new point. -/
@[simp]
theorem stabilizeGeneratorEquiv_symm_apply (x : H.Generator) :
    (H.stabilizeGeneratorEquiv r₀).symm (H.stabilizeGenerator r₀ x) = x :=
  (H.stabilizeGeneratorEquiv r₀).symm_apply_eq.mpr rfl

end Generator

section Domain

variable (r₀ : Region)

/-- The `0`-chain of `x ∪ {x₀}` at the old intersection points is that of `x`. -/
@[simp]
theorem generatorChain_stabilizeGenerator_inl (x : H.Generator) (q : Point) :
    (H.stabilize r₀).generatorChain (H.stabilizeGenerator r₀ x) (Sum.inl q) =
      H.generatorChain x q := by
  classical
  simp [HeegaardIntersectionSystem.generatorChain_apply]

/-- The `0`-chain of `x ∪ {x₀}` is `1` at the new intersection point. -/
@[simp]
theorem generatorChain_stabilizeGenerator_inr (x : H.Generator) (u : Unit) :
    (H.stabilize r₀).generatorChain (H.stabilizeGenerator r₀ x) (Sum.inr u) = 1 := by
  classical
  simp [HeegaardIntersectionSystem.generatorChain_apply]

/-- The `α`-part of the boundary of a domain in the stabilized diagram is that in the original
diagram on the old arcs, and vanishes on the new arc, which has `r₀` on both sides. -/
@[simp]
theorem alphaBoundary_stabilize (D : Region → ℤ) :
    (H.stabilize r₀).alphaBoundary D = Sum.elim (H.alphaBoundary D) 0 := by
  ext (p | u) <;> simp

/-- The `β`-part of the boundary of a domain in the stabilized diagram is that in the original
diagram on the old arcs, and vanishes on the new arc, which has `r₀` on both sides. -/
@[simp]
theorem betaBoundary_stabilize (D : Region → ℤ) :
    (H.stabilize r₀).betaBoundary D = Sum.elim (H.betaBoundary D) 0 := by
  ext (p | u) <;> simp

/-- The boundary of a `1`-chain on the `α`-arcs of the stabilized diagram supported on the old
arcs. -/
@[simp]
theorem alphaArcBoundary_stabilize_sumElim (c : Point → ℤ) :
    (H.stabilize r₀).alphaArcBoundary (Sum.elim c 0) = Sum.elim (H.alphaArcBoundary c) 0 := by
  ext (p | u) <;> simp

/-- The boundary of a `1`-chain on the `β`-arcs of the stabilized diagram supported on the old
arcs. -/
@[simp]
theorem betaArcBoundary_stabilize_sumElim (c : Point → ℤ) :
    (H.stabilize r₀).betaArcBoundary (Sum.elim c 0) = Sum.elim (H.betaArcBoundary c) 0 := by
  ext (p | u) <;> simp

variable {r₀} {x y : H.Generator}

/-- A domain connects `x ∪ {x₀}` to `y ∪ {x₀}` in the stabilized diagram exactly when it connects
`x` to `y` in the original diagram. -/
theorem isDomainBetween_stabilize_iff {D : Region → ℤ} :
    (H.stabilize r₀).IsDomainBetween (H.stabilizeGenerator r₀ x) (H.stabilizeGenerator r₀ y) D ↔
      H.IsDomainBetween x y D := by
  simp only [isDomainBetween_iff, alphaBoundary_stabilize, betaBoundary_stabilize,
    alphaArcBoundary_stabilize_sumElim, betaArcBoundary_stabilize_sumElim, funext_iff, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, Pi.zero_apply,
    generatorChain_stabilizeGenerator_inl, generatorChain_stabilizeGenerator_inr, sub_self,
    forall_const, and_true]

variable (r₀) in
/-- The stabilized diagram has the same periodic domains as the original diagram. -/
@[simp]
theorem periodicDomains_stabilize : (H.stabilize r₀).periodicDomains = H.periodicDomains := by
  ext P
  simp only [mem_periodicDomains_iff, stabilize_basepoint, alphaBoundary_stabilize,
    betaBoundary_stabilize, alphaArcBoundary_stabilize_sumElim, betaArcBoundary_stabilize_sumElim,
    funext_iff, Sum.forall, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, forall_const, and_true]

variable (r₀) in
/-- The stabilized diagram is weakly admissible exactly when the original diagram is. -/
@[simp]
theorem weaklyAdmissible_stabilize_iff :
    (H.stabilize r₀).WeaklyAdmissible ↔ H.WeaklyAdmissible := by
  simp only [weaklyAdmissible_iff, periodicDomains_stabilize]

end Domain

section MaslovIndex

variable (r₀ : Region)

/-- The point measure of a domain at an old intersection point is unchanged. -/
theorem pointMeasure_stabilize_inl (D : Region → ℤ) (p : Point) :
    (H.stabilize r₀).pointMeasure D (Sum.inl p) = H.pointMeasure D p := by
  simp

/-- All four corners at the new intersection point lie in `r₀`, so the point measure there is the
multiplicity at `r₀`. -/
theorem pointMeasure_stabilize_inr (D : Region → ℤ) (u : Unit) :
    (H.stabilize r₀).pointMeasure D (Sum.inr u) = D r₀ := by
  simp only [pointMeasure_apply, stabilize_alphaNext, Equiv.Perm.sumCongr_symm,
    Equiv.Perm.sumCongr_apply, Sum.map_inr, stabilize_alphaLeft, stabilize_alphaRight,
    Sum.elim_inr]
  ring

/-- The point measure of a domain at `x ∪ {x₀}` is its point measure at `x` plus its
multiplicity at `r₀`. -/
theorem generatorPointMeasure_stabilizeGenerator (x : H.Generator) (D : Region → ℤ) :
    (H.stabilize r₀).generatorPointMeasure (H.stabilizeGenerator r₀ x) D =
      H.generatorPointMeasure x D + D r₀ := by
  simp only [generatorPointMeasure_apply, HeegaardIntersectionSystem.point_apply,
    Fin.sum_univ_castSucc, stabilizeGenerator_val, stabilizePoint_castSucc, stabilizePoint_last,
    pointMeasure_stabilize_inl, pointMeasure_stabilize_inr]

section Euler

variable [DecidableEq Region]

/-- The region Euler characteristics after stabilizing in `r₀`: the connected sum of `r₀` with
the open square cut out of the torus has Euler characteristic one less than `r₀`, and the other
regions are unchanged. -/
def stabilizeEuler (χ : Region → ℤ) (r₀ : Region) : Region → ℤ :=
  χ - Pi.single r₀ 1

/-- The Euler characteristic of a region after stabilizing, one less for `r₀`. -/
@[simp]
theorem stabilizeEuler_apply (χ : Region → ℤ) (r₀ r : Region) :
    stabilizeEuler χ r₀ r = χ r - (Pi.single r₀ 1 : Region → ℤ) r :=
  (rfl)

section Corner

variable [Fintype Point]

/-- The region `r₀` gains the four corners at the new intersection point; the other regions keep
their corners. -/
theorem cornerCount_stabilize (r : Region) :
    (H.stabilize r₀).cornerCount r = H.cornerCount r + if r₀ = r then 4 else 0 := by
  simp only [cornerCount_eq_card, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_unique]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
    fin_cases i <;> simp [cornerRegion_eq]
  · rw [Fin.sum_univ_four]
    by_cases h : r₀ = r <;> simp [cornerRegion_eq, h]

/-- When `r₀` contains a basepoint, the stabilized diagram is nice exactly when the original one
is: the regions without basepoints keep their Euler characteristics and corners. -/
theorem isNice_stabilize_iff {χ : Region → ℤ} (hr₀ : r₀ ∈ Set.range H.basepoint) :
    (H.stabilize r₀).IsNice (stabilizeEuler χ r₀) ↔ H.IsNice χ := by
  obtain ⟨z₀, rfl⟩ := hr₀
  simp only [isNice_iff, stabilize_basepoint]
  refine forall_congr' fun r => forall_congr' fun hr => ?_
  have hne : H.basepoint z₀ ≠ r := hr z₀
  simp [cornerCount_stabilize, hne]

end Corner

variable [Fintype Point] [Fintype Region]

/-- The closed-surface normalization `∑ χ(R) - #(α ∩ β)` drops by two under stabilization, from
the value `2 - 2n` for a surface of genus `n` to the value `2 - 2(n + 1)`. -/
theorem sum_stabilizeEuler_sub_card (χ : Region → ℤ) :
    ∑ r, stabilizeEuler χ r₀ r - Fintype.card (Point ⊕ Unit) =
      ∑ r, χ r - Fintype.card Point - 2 := by
  simp only [stabilizeEuler_apply, Finset.sum_sub_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true, Fintype.card_sum, Fintype.card_unit]
  push_cast
  ring

/-- The Maslov index of a domain from `x ∪ {x₀}` to `y ∪ {x₀}` in the stabilized diagram is its
Maslov index from `x` to `y` in the original diagram: the Euler measure loses `2 D(r₀)`, and the
point measures at the two generators each gain `D(r₀)`. -/
theorem maslovIndex_stabilize (χ : Region → ℤ) (x y : H.Generator) (D : Region → ℤ) :
    (H.stabilize r₀).maslovIndex (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x)
        (H.stabilizeGenerator r₀ y) D = H.maslovIndex χ x y D := by
  have hχ : ∑ r, (((χ r - (Pi.single r₀ 1 : Region → ℤ) r : ℤ) : ℚ)) * D r =
      ∑ r, (χ r : ℚ) * D r - D r₀ := by
    simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  simp only [maslovIndex_apply, eulerMeasure_eq_sub_sum_pointMeasure,
    generatorPointMeasure_stabilizeGenerator, Fintype.sum_sum_type, stabilizeEuler_apply,
    pointMeasure_stabilize_inl, pointMeasure_stabilize_inr, Fintype.sum_unique, hχ]
  ring

variable {χ : Region → ℤ} {x : H.Generator}

/-- The stabilized diagram is weakly admissible at `x ∪ {x₀}` exactly when the original diagram
is weakly admissible at `x`. -/
@[simp]
theorem weaklyAdmissibleAt_stabilize_iff :
    (H.stabilize r₀).WeaklyAdmissibleAt (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x) ↔
      H.WeaklyAdmissibleAt χ x := by
  simp only [weaklyAdmissibleAt_def, periodicDomains_stabilize, maslovIndex_stabilize]

/-- The stabilized diagram is strongly admissible at `x ∪ {x₀}` exactly when the original diagram
is strongly admissible at `x`. -/
@[simp]
theorem stronglyAdmissible_stabilize_iff :
    (H.stabilize r₀).StronglyAdmissible (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x) ↔
      H.StronglyAdmissible χ x := by
  simp only [stronglyAdmissible_iff, periodicDomains_stabilize, maslovIndex_stabilize]

/-- The periodic Maslov indices at `x ∪ {x₀}` are those at `x`. -/
@[simp]
theorem periodicMaslovIndices_stabilize :
    (H.stabilize r₀).periodicMaslovIndices (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x) =
      H.periodicMaslovIndices χ x := by
  ext q
  simp only [mem_periodicMaslovIndices_iff, periodicDomains_stabilize, maslovIndex_stabilize]

/-- Under the normalization of `TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_eq`,
the relative grading of `x ∪ {x₀}` and `y ∪ {x₀}` in the stabilized diagram is that of `x` and `y`
in the original diagram. -/
theorem relativeGrading_stabilize [Fintype Basepoint]
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0) (y : H.Generator) :
    (H.stabilize r₀).relativeGrading (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x)
        (H.stabilizeGenerator r₀ y) = H.relativeGrading χ x y := by
  have hself' (x' : (H.stabilize r₀).Generator) (E : Region → ℤ)
      (hE : (H.stabilize r₀).IsDomainBetween x' x' E) :
      (H.stabilize r₀).maslovIndex (stabilizeEuler χ r₀) x' x' E -
          2 * ∑ z, (E ((H.stabilize r₀).basepoint z) : ℚ) ∈
        (H.stabilize r₀).periodicMaslovIndices (stabilizeEuler χ r₀) x' := by
    obtain ⟨x₁, rfl⟩ := H.stabilizeGenerator_surjective r₀ x'
    simpa only [periodicMaslovIndices_stabilize, maslovIndex_stabilize, stabilize_basepoint] using
      hself x₁ E (H.isDomainBetween_stabilize_iff.mp hE)
  by_cases h : ∃ D, H.IsDomainBetween x y D
  · obtain ⟨D, hD⟩ := h
    have hD' : (H.stabilize r₀).IsDomainBetween (H.stabilizeGenerator r₀ x)
        (H.stabilizeGenerator r₀ y) D := H.isDomainBetween_stabilize_iff.mpr hD
    rw [hD.relativeGrading_eq hself hP, hD'.relativeGrading_eq hself'
      (by simpa only [periodicDomains_stabilize, maslovIndex_stabilize] using hP),
      maslovIndex_stabilize, stabilize_basepoint]
  · simp only [not_exists] at h
    rw [relativeGrading_of_forall_not_isDomainBetween h,
      relativeGrading_of_forall_not_isDomainBetween fun D hD =>
        h D (H.isDomainBetween_stabilize_iff.mp hD)]

end Euler

end MaslovIndex

section Hat

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region) {χ : Region → ℤ}

/-- The domains counted by the hat differential of the stabilized diagram from `x ∪ {x₀}` to
`y ∪ {x₀}` are those of the original diagram from `x` to `y`. -/
@[simp]
theorem hatDomains_stabilize (x y : H.Generator) :
    (H.stabilize r₀).hatDomains (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x)
        (H.stabilizeGenerator r₀ y) = H.hatDomains χ x y := by
  ext D
  simp only [mem_hatDomains_iff, isDomainBetween_stabilize_iff, stabilize_basepoint,
    maslovIndex_stabilize]

/-- The coefficients of the hat differential of the stabilized diagram are those of the original
diagram. -/
@[simp]
theorem hatCoefficient_stabilize (x y : H.Generator) :
    (H.stabilize r₀).hatCoefficient (stabilizeEuler χ r₀) (H.stabilizeGenerator r₀ x)
        (H.stabilizeGenerator r₀ y) = H.hatCoefficient χ x y := by
  rw [hatCoefficient_def, hatCoefficient_def, hatDomains_stabilize]

end Hat

section Differential

variable (r₀ : Region)

/-- The identification of the hat chain group of the original diagram with that of the stabilized
diagram, sending a generator `x` to `x ∪ {x₀}`. -/
noncomputable def stabilizeChainEquiv :
    (H.Generator →₀ ZMod 2) ≃ₗ[ZMod 2] ((H.stabilize r₀).Generator →₀ ZMod 2) :=
  Finsupp.domLCongr (H.stabilizeGeneratorEquiv r₀)

/-- The identification sends the generator `x` to the generator `x ∪ {x₀}`. -/
@[simp]
theorem stabilizeChainEquiv_single (x : H.Generator) (a : ZMod 2) :
    H.stabilizeChainEquiv r₀ (Finsupp.single x a) =
      Finsupp.single (H.stabilizeGenerator r₀ x) a := by
  simp [stabilizeChainEquiv]

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}

/-- Stabilization does not change the hat complex: under
`TauCeti.HeegaardRegionSystem.stabilizeChainEquiv` the hat differential of the stabilized diagram
is that of the original diagram. -/
theorem hatDifferential_comp_stabilizeChainEquiv :
    (H.stabilize r₀).hatDifferential (stabilizeEuler χ r₀) ∘ₗ
        (H.stabilizeChainEquiv r₀).toLinearMap =
      (H.stabilizeChainEquiv r₀).toLinearMap ∘ₗ H.hatDifferential χ := by
  ext x g
  obtain ⟨y, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g
  simp [stabilizeChainEquiv, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]

end Differential

end HeegaardRegionSystem

end TauCeti
