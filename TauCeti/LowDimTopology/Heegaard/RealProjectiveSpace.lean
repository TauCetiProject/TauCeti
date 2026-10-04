/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.CurveHomology
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases

/-!
# The genus-one Heegaard diagram of `ℝP³`

On the torus `ℝ² / ℤ²` let `α` be the circle `y = 0`, oriented by increasing `x`, and let `β` be
the line `t ↦ (t, 2t)` of slope `2`, oriented by increasing `t`. Attaching circles of homology
classes `(1, 0)` and `(1, 2)` give the lens space `L(2, 1) = ℝP³`. They meet transversally in the
two points `p₀ = (0, 0)` and `p₁ = (1/2, 0)`, and the complement of `α ∪ β` consists of the two
parallelograms `R₀ = {y/2 < x < 1/2 + y/2}` and `R₁ = {1/2 + y/2 < x < 1 + y/2}`.

In `TauCeti.HeegaardRegionSystem.realProjectiveSpace r` the points `p₀`, `p₁` are `0, 1 : Fin 2`,
the regions `R₀`, `R₁` are `0, 1 : Fin 2`, and the single basepoint lies in the region `r`. Each
point is a generator. The `α`-part of the boundary of any domain `D` has boundary
`2 (D R₁ - D R₀) (p₀ - p₁)`, which is never `p₁ - p₀`; so no domain connects `p₀` to `p₁`, and
`ε(p₀, p₁) ≠ 0`. On the other hand twice the connecting chain differs from the boundary of `R₀`
by `α + β`, so `ε(p₀, p₁)` has order two. This matches `H₁(ℝP³) = ℤ/2`: the two generators lie in
the two different spin^c structures of `ℝP³`, as needed for `HF̂(ℝP³) = 𝔽₂²` with one generator
in each spin^c structure.

## Main definitions

* `TauCeti.HeegaardRegionSystem.realProjectiveSpace`: the diagram, with its basepoint in a given
  region.
* `TauCeti.HeegaardRegionSystem.realProjectiveSpaceGenerator`: its two generators.

## Main results

* `TauCeti.HeegaardRegionSystem.not_isDomainBetween_realProjectiveSpace`: no domain connects the
  two generators.
* `TauCeti.HeegaardRegionSystem.epsilon_realProjectiveSpace_ne_zero`: `ε(p₀, p₁) ≠ 0`.
* `TauCeti.HeegaardRegionSystem.addOrderOf_epsilon_realProjectiveSpace`: `ε(p₀, p₁)` has order
  two.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4 for `ε(x, y)`; the genus-one
  diagrams of lens spaces are those of their §3.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

/-- The genus-one Heegaard diagram of `ℝP³` whose two attaching circles meet in two points, with
its basepoint in the region `r`. -/
def realProjectiveSpace (r : Fin 2) : HeegaardRegionSystem 1 (Fin 2) (Fin 2) Unit where
  pointFintype := inferInstance
  alpha _ := 0
  beta _ := 0
  alphaNext := Equiv.swap 0 1
  alphaNext_isCycleOn := isCycleOn_swap_fin_two_fiber _
  betaNext := Equiv.swap 0 1
  betaNext_isCycleOn := isCycleOn_swap_fin_two_fiber _
  alphaLeft := ![0, 1]
  alphaRight := ![1, 0]
  betaLeft := ![1, 0]
  betaRight := ![0, 1]
  regionNonempty := inferInstance
  crossingCompatible := by
    intro p
    left
    fin_cases p <;> simp
  regionCovered := by
    intro s
    left
    fin_cases s <;> simp [Fin.exists_fin_two]
  basepoint _ := r

/-- The generator of `realProjectiveSpace r` at the intersection point `a`. -/
def realProjectiveSpaceGenerator (r : Fin 2) (a : Fin 2) : (realProjectiveSpace r).Generator :=
  (realProjectiveSpace r).generatorOf 1 (fun _ => a) (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)

/-- The generator chain is supported at its chosen intersection point. -/
theorem generatorChain_realProjectiveSpaceGenerator (r a q : Fin 2) :
    (realProjectiveSpace r).generatorChain (realProjectiveSpaceGenerator r a) q =
      if a = q then 1 else 0 := by
  rw [HeegaardIntersectionSystem.generatorChain_apply]
  simp [realProjectiveSpaceGenerator]

/-- No domain connects the generator `p₀` to the generator `p₁`: the `α`-part of the boundary of
a domain has boundary divisible by two. -/
theorem not_isDomainBetween_realProjectiveSpace (r : Fin 2) (D : Fin 2 → ℤ) :
    ¬ (realProjectiveSpace r).IsDomainBetween (realProjectiveSpaceGenerator r 0)
      (realProjectiveSpaceGenerator r 1) D := by
  intro hD
  have h := congrFun (isDomainBetween_iff.mp hD).1 0
  simp only [alphaArcBoundary_apply, alphaBoundary_apply, Pi.sub_apply,
    generatorChain_realProjectiveSpaceGenerator] at h
  simp [realProjectiveSpace] at h
  omega

/-- The class `ε(p₀, p₁)` of the two generators of the diagram of `ℝP³` is nonzero, so they lie
in different spin^c structures. -/
theorem epsilon_realProjectiveSpace_ne_zero (r : Fin 2) :
    (realProjectiveSpace r).epsilon (realProjectiveSpaceGenerator r 0)
      (realProjectiveSpaceGenerator r 1) ≠ 0 := by
  rw [Ne, epsilon_eq_zero_iff, not_exists]
  exact not_isDomainBetween_realProjectiveSpace r

/-- The `1`-chain made of the `α`-arc from `p₀` to `p₁` and the `β`-arc from `p₁` to `p₀`
connects the two generators. -/
private theorem isConnectingChain_realProjectiveSpace (r : Fin 2) :
    (realProjectiveSpace r).IsConnectingChain (realProjectiveSpaceGenerator r 0)
      (realProjectiveSpaceGenerator r 1) (Pi.single 0 1, Pi.single 1 1) := by
  refine isConnectingChain_iff.mpr ⟨funext fun q => ?_, funext fun q => ?_⟩ <;>
    simp only [alphaArcBoundary_apply, betaArcBoundary_apply, Pi.sub_apply,
      generatorChain_realProjectiveSpaceGenerator] <;>
    fin_cases q <;> simp [realProjectiveSpace]

/-- Twice `ε(p₀, p₁)` vanishes: twice the connecting chain is the boundary of `R₀` plus
`α + β`. -/
theorem two_nsmul_epsilon_realProjectiveSpace (r : Fin 2) :
    2 • (realProjectiveSpace r).epsilon (realProjectiveSpaceGenerator r 0)
      (realProjectiveSpaceGenerator r 1) = 0 := by
  rw [(isConnectingChain_realProjectiveSpace r).epsilon_eq, ← map_nsmul,
    CurveHomology.mk_eq_zero_iff, AddSubgroup.coe_nsmul, mem_arcRelations_iff]
  refine ⟨Pi.single 0 1, mem_curveCycles_iff_exists.mpr ⟨⟨fun _ => 1, fun p => ?_⟩,
    fun _ => 1, fun p => ?_⟩⟩ <;>
    fin_cases p <;> simp [realProjectiveSpace]

/-- The class `ε(p₀, p₁)` has order two, as an element of `H₁(ℝP³) = ℤ/2` should. -/
theorem addOrderOf_epsilon_realProjectiveSpace (r : Fin 2) :
    addOrderOf ((realProjectiveSpace r).epsilon (realProjectiveSpaceGenerator r 0)
      (realProjectiveSpaceGenerator r 1)) = 2 :=
  addOrderOf_eq_prime (two_nsmul_epsilon_realProjectiveSpace r)
    (epsilon_realProjectiveSpace_ne_zero r)

end HeegaardRegionSystem

end TauCeti
