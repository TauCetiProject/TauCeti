/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.MayerVietoris
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Product
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The Euler characteristic of a space with finitely many points removed

Let `X` be a Hausdorff space charted on a `d`-dimensional real normed space `E`, for instance a
topological `d`-manifold without boundary, and let `S ⊆ X` be finite. If `X` and `X \ S` have
finite CW type, then

```text
χ(X \ S) = χ(X) - (-1)ᵈ · #S.
```

For a surface, removing `k` points lowers the Euler characteristic by `k`. This is the count by
which a branched covering of compact surfaces is compared with the unbranched covering obtained by
deleting the branch values and their preimages, as in the topological proof of the
Riemann--Hurwitz formula.

The proof covers `X` by the open sets `X \ S` and a union `V` of pairwise disjoint coordinate
balls centred at the points of `S` (`Set.Finite.exists_isOpenEmbedding_prod_ball`). In
coordinates, `V` is `S × B` for a ball `B ⊆ E`, so
`χ(V) = #S`. The intersection is `S × (B \ {0})`, and a punctured ball retracts onto a sphere
(`StarConvex.sphereHomotopyEquiv`), so `χ(V \ S) = #S · (1 - (-1)ᵈ)`. Additivity of the Euler
characteristic along the open cover (`TauCeti.eulerChar_add_eulerChar_inter_of_union_eq_univ`)
then gives the formula. The model space is first replaced by a Euclidean space of the same
dimension in the universe of `X`, so that `E` and `X` may live in different universes.

## Main results

* `TauCeti.eulerChar_compl_of_finite`: `χ(X \ S) = χ(X) - (-1)ᵈ · #S`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44 and the Mayer--Vietoris sequences.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §17 (the Riemann--Hurwitz formula).
-/

public section

noncomputable section

open Metric Module Set Topology
open scoped ContinuousMap

universe v w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {S : Set X}

/-- The case of `eulerChar_compl_of_finite` where the model space lives in the universe of `X`. -/
private theorem eulerChar_compl_of_finite_aux {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E X] (hS : S.Finite) [FiniteCWType X]
    [FiniteCWType ↥Sᶜ] : eulerChar ↥Sᶜ = eulerChar X - (-1) ^ finrank ℝ E * S.ncard := by
  have := hS.to_subtype
  obtain ⟨F, hF, hzero⟩ := hS.exists_isOpenEmbedding_prod_ball (E := E) two_pos
  have h0 : (0 : E) ∈ ball 0 2 := mem_ball_self two_pos
  have hP : IsOpen (ball (0 : E) 2 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  -- The restriction of `F` to the punctured balls `S × (ball 0 2 \ {0})`.
  let G := F ∘ Prod.map id (inclusion (sdiff_subset (t := {(0 : E)})))
  have hG : IsOpenEmbedding G := hF.comp (IsOpenEmbedding.id.prodMap
    (isOpen_ball.isOpenEmbedding_subtypeVal.of_comp _ hP.isOpenEmbedding_subtypeVal))
  -- The punctured coordinate balls are exactly the coordinate balls minus `S`.
  have hrange : range G = Sᶜ ∩ range F := by
    ext x
    constructor
    · rintro ⟨⟨s, z, hzB, hz0⟩, rfl⟩
      refine ⟨fun hx ↦ hz0 ?_, ⟨s, z, hzB⟩, rfl⟩
      have := hF.injective ((hzero ⟨_, hx⟩).trans rfl)
      simpa using (congrArg (fun p ↦ (p.2 : E)) this).symm
    · rintro ⟨hxS, ⟨s, z, hzB⟩, rfl⟩
      refine ⟨⟨s, z, hzB, fun hz0 ↦ hxS ?_⟩, rfl⟩
      obtain rfl : z = 0 := hz0
      exact hzero s ▸ s.2
  have hcover : Sᶜ ∪ range F = univ :=
    eq_univ_of_forall fun x ↦ (em (x ∈ S)).elim (fun hx ↦ .inr ⟨_, hzero ⟨x, hx⟩⟩) .inl
  have := (convex_ball (0 : E) 2).contractibleSpace ⟨0, h0⟩
  -- The punctured ball retracts onto the unit sphere.
  let ePS : S × ↥(ball (0 : E) 2 \ {0}) ≃ₕ S × sphere (0 : E) 1 :=
    (ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (((convex_ball (0 : E) 2).starConvex h0).sphereHomotopyEquiv one_pos
        (sphere_subset_ball one_lt_two)).symm
  have := ePS.finiteCWType
  let eV := hF.isEmbedding.toHomeomorph
  let eI := hG.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have := eV.symm.finiteCWType
  have := eI.symm.finiteCWType
  have key := eulerChar_add_eulerChar_inter_of_union_eq_univ hS.isClosed.isOpen_compl
    hF.isOpen_range hcover
  rw [← eV.eulerChar_eq, ← eI.eulerChar_eq, ePS.eulerChar_eq, eulerChar_prod, eulerChar_prod,
    eulerChar_sphere_eq_one_sub, eulerChar_of_contractibleSpace (X := ball (0 : E) 2),
    eulerChar_of_discreteTopology (X := S), Nat.card_coe_set_eq] at key
  linear_combination -key

/-- **The Euler characteristic of the complement of finitely many points.** Let `X` be a
Hausdorff space charted on a finite-dimensional real normed space `E`, and `S ⊆ X` a finite set.
If `X` and `X \ S` have finite CW type, then `χ(X \ S) = χ(X) - (-1) ^ dim E · #S`. -/
theorem eulerChar_compl_of_finite {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E X] (hS : S.Finite) [FiniteCWType X]
    [FiniteCWType ↥Sᶜ] : eulerChar ↥Sᶜ = eulerChar X - (-1) ^ finrank ℝ E * S.ncard := by
  -- Recharts `X` on a Euclidean space of the same dimension in the universe of `X`.
  let E' := EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ E)))
  have hE' : finrank ℝ E' = finrank ℝ E := by simp [E']
  let _ : ChartedSpace E' E := (ContinuousLinearEquiv.ofFinrankEq hE').toHomeomorph.chartedSpace
  let _ : ChartedSpace E' X := .comp E' E X
  rw [eulerChar_compl_of_finite_aux (E := E') hS, hE']

end TauCeti
