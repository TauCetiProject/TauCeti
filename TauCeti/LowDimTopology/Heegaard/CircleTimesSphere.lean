/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Domain
import Mathlib.Tactic.FinCases

/-!
# The genus-one Heegaard diagram of `S¹ × S²`

On the torus `ℝ² / ℤ²` let `α` be the circle `y = 0` and let `β` be the circle
`y = ε sin (2π x)` for a small `ε > 0`, both oriented by increasing `x`. Two isotopic
attaching circles on a torus give `S¹ × S²`; the perturbation makes them meet transversally in
the two points `p₀ = (0, 0)` and `p₁ = (1/2, 0)`. The complement of `α ∪ β` has three regions:
the bigon `B₁` between `α` and `β` over `0 < x < 1/2`, where `β` lies above `α`; the bigon `B₂`
over `1/2 < x < 1`, where `β` lies below `α`; and the annulus `A` making up the rest of the torus.

In `TauCeti.HeegaardRegionSystem.circleTimesSphere r` the points `p₀`, `p₁` are `0, 1 : Fin 2`,
the regions `A`, `B₁`, `B₂` are `0, 1, 2 : Fin 3`, and the single basepoint lies in the region
`r`. Both bigons are domains from the generator `p₀` to the generator `p₁`, so their difference
`B₁ - B₂`, whose boundary is `α - β`, is a periodic domain whenever the basepoint lies in `A`.

This is a basic example of a diagram with a nonzero periodic domain, on which weak admissibility
depends on the placement of the basepoint. With the basepoint in the annulus, the periodic
domains are the multiples of `B₁ - B₂`, and the diagram is weakly admissible. With the basepoint
in a bigon, say `B₁`, the periodic domain `A + 2 B₂` has no negative coefficient, so the diagram
is not weakly admissible.

## Main definitions

* `TauCeti.HeegaardRegionSystem.circleTimesSphere`: the diagram, with its basepoint in a given
  region.
* `TauCeti.HeegaardRegionSystem.circleTimesSphereGenerator`: its two generators.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_circleTimesSphere_single_one` and
  `TauCeti.HeegaardRegionSystem.isDomainBetween_circleTimesSphere_single_two`: both bigons are
  domains from `p₀` to `p₁`.
* `TauCeti.HeegaardRegionSystem.periodicDomains_circleTimesSphere_zero`: with the basepoint in
  the annulus, the periodic domains are the multiples of `B₁ - B₂`.
* `TauCeti.HeegaardRegionSystem.weaklyAdmissible_circleTimesSphere_zero`: that diagram is weakly
  admissible.
* `TauCeti.HeegaardRegionSystem.not_weaklyAdmissible_circleTimesSphere_one`: with the basepoint
  in a bigon, the diagram is not weakly admissible.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.2, where admissibility is
  introduced.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

/-- The two intersection points form one cycle of the transposition exchanging them. -/
private theorem isCycleOn_swap_setOf (f : Fin 2 → Fin 1) (i : Fin 1) :
    (Equiv.swap (0 : Fin 2) 1).IsCycleOn {p | f p = i} := by
  convert Equiv.Perm.isCycleOn_swap (a := (0 : Fin 2)) (b := 1) (by decide) using 1
  ext p
  fin_cases p <;> simp [Subsingleton.elim (f _) i]

/-- The genus-one Heegaard diagram of `S¹ × S²` whose two attaching circles meet in two points,
with its basepoint in the region `r`. The regions `0`, `1`, `2` are the annulus and the two
bigons. -/
def circleTimesSphere (r : Fin 3) : HeegaardRegionSystem 1 (Fin 2) (Fin 3) Unit where
  pointFintype := inferInstance
  alpha _ := 0
  beta _ := 0
  alphaNext := Equiv.swap 0 1
  alphaNext_isCycleOn := isCycleOn_swap_setOf _
  betaNext := Equiv.swap 0 1
  betaNext_isCycleOn := isCycleOn_swap_setOf _
  alphaLeft := ![1, 0]
  alphaRight := ![0, 2]
  betaLeft := ![0, 2]
  betaRight := ![1, 0]
  regionNonempty := inferInstance
  crossingCompatible := by
    intro p
    fin_cases p
    · left
      simp
    · right
      simp
  regionCovered := by
    intro s
    left
    fin_cases s <;> simp [Fin.exists_fin_two]
  basepoint _ := r

/-- The generator of `circleTimesSphere r` at the intersection point `a`. -/
def circleTimesSphereGenerator (r : Fin 3) (a : Fin 2) : (circleTimesSphere r).Generator :=
  (circleTimesSphere r).generatorOf 1 (fun _ => a) (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)

private theorem generatorChain_circleTimesSphereGenerator (r : Fin 3) (a q : Fin 2) :
    (circleTimesSphere r).generatorChain (circleTimesSphereGenerator r a) q =
      if a = q then 1 else 0 := by
  rw [HeegaardIntersectionSystem.generatorChain_apply]
  simp [circleTimesSphereGenerator]

/-- The value of the `α`-boundary cycle condition of `circleTimesSphere` on the two points. -/
private theorem alphaArcBoundary_alphaBoundary_circleTimesSphere (r : Fin 3) (D : Fin 3 → ℤ)
    (q : Fin 2) :
    (circleTimesSphere r).alphaArcBoundary ((circleTimesSphere r).alphaBoundary D) q =
      ![(D 0 - D 2) - (D 1 - D 0), (D 1 - D 0) - (D 0 - D 2)] q := by
  fin_cases q <;> simp [circleTimesSphere]

/-- The value of the `β`-boundary cycle condition of `circleTimesSphere` on the two points. -/
private theorem betaArcBoundary_betaBoundary_circleTimesSphere (r : Fin 3) (D : Fin 3 → ℤ)
    (q : Fin 2) :
    (circleTimesSphere r).betaArcBoundary ((circleTimesSphere r).betaBoundary D) q =
      ![(D 2 - D 0) - (D 0 - D 1), (D 0 - D 1) - (D 2 - D 0)] q := by
  fin_cases q <;> simp [circleTimesSphere]

/-- A domain of `circleTimesSphere r` is periodic exactly when it vanishes at the basepoint and
its multiplicities satisfy `D B₁ + D B₂ = 2 D A`. -/
private theorem mem_periodicDomains_circleTimesSphere_iff (r : Fin 3) (D : Fin 3 → ℤ) :
    D ∈ (circleTimesSphere r).periodicDomains ↔ D r = 0 ∧ D 1 + D 2 = 2 * D 0 := by
  simp only [mem_periodicDomains_iff, funext_iff, alphaArcBoundary_alphaBoundary_circleTimesSphere,
    betaArcBoundary_betaBoundary_circleTimesSphere, Fin.forall_fin_two]
  simp only [circleTimesSphere, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    forall_const]
  omega

/-- The bigon `B₁` is a domain from the generator `p₀` to the generator `p₁`. -/
theorem isDomainBetween_circleTimesSphere_single_one (r : Fin 3) :
    (circleTimesSphere r).IsDomainBetween (circleTimesSphereGenerator r 0)
      (circleTimesSphereGenerator r 1) (Pi.single 1 1) := by
  refine isDomainBetween_iff.mpr ⟨funext fun q => ?_, funext fun q => ?_⟩ <;>
    simp only [alphaArcBoundary_alphaBoundary_circleTimesSphere,
      betaArcBoundary_betaBoundary_circleTimesSphere, Pi.sub_apply,
      generatorChain_circleTimesSphereGenerator] <;>
    fin_cases q <;> simp

/-- The bigon `B₂` is a domain from the generator `p₀` to the generator `p₁`. -/
theorem isDomainBetween_circleTimesSphere_single_two (r : Fin 3) :
    (circleTimesSphere r).IsDomainBetween (circleTimesSphereGenerator r 0)
      (circleTimesSphereGenerator r 1) (Pi.single 2 1) := by
  refine isDomainBetween_iff.mpr ⟨funext fun q => ?_, funext fun q => ?_⟩ <;>
    simp only [alphaArcBoundary_alphaBoundary_circleTimesSphere,
      betaArcBoundary_betaBoundary_circleTimesSphere, Pi.sub_apply,
      generatorChain_circleTimesSphereGenerator] <;>
    fin_cases q <;> simp

/-- With the basepoint in the annulus, the periodic domains of the genus-one diagram of
`S¹ × S²` are the multiples of the difference `B₁ - B₂` of the two bigons. -/
theorem periodicDomains_circleTimesSphere_zero :
    (circleTimesSphere 0).periodicDomains =
      AddSubgroup.zmultiples (Pi.single 1 1 - Pi.single 2 1) := by
  ext D
  rw [mem_periodicDomains_circleTimesSphere_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨h0, h12⟩
    refine ⟨D 1, funext fun i => ?_⟩
    fin_cases i <;> simp <;> omega
  · rintro ⟨k, rfl⟩
    simp

/-- With the basepoint in the annulus, the genus-one diagram of `S¹ × S²` is weakly
admissible. -/
theorem weaklyAdmissible_circleTimesSphere_zero : (circleTimesSphere 0).WeaklyAdmissible := by
  rw [weaklyAdmissible_iff]
  intro D hD hnonneg
  rw [mem_periodicDomains_circleTimesSphere_iff] at hD
  have h1 := hnonneg 1
  have h2 := hnonneg 2
  simp only [Pi.zero_apply] at h1 h2
  funext i
  fin_cases i <;> simp <;> omega

/-- With the basepoint in a bigon, the genus-one diagram of `S¹ × S²` is not weakly admissible:
the periodic domain `A + 2 B₂` has no negative coefficient. -/
theorem not_weaklyAdmissible_circleTimesSphere_one : ¬ (circleTimesSphere 1).WeaklyAdmissible := by
  rw [weaklyAdmissible_iff]
  intro h
  have hP : ![1, 0, 2] ∈ (circleTimesSphere 1).periodicDomains := by
    rw [mem_periodicDomains_circleTimesSphere_iff]
    simp
  have hnonneg : (0 : Fin 3 → ℤ) ≤ ![1, 0, 2] := by
    intro i
    fin_cases i <;> simp
  simpa using congrFun (h _ hP hnonneg) 0

end HeegaardRegionSystem

end TauCeti
