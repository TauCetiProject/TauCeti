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
balls centred at the points of `S`. In coordinates, `V` is `S × B` for a ball `B ⊆ E`, so
`χ(V) = #S`. The intersection is `S × (B \ {0})`, and a punctured ball retracts onto a sphere
(`StarConvex.sphereHomotopyEquiv`), so `χ(V \ S) = #S · (1 - (-1)ᵈ)`. Additivity of the Euler
characteristic along the open cover (`TauCeti.eulerChar_add_eulerChar_inter_of_union_eq_univ`)
then gives the formula.

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

universe w

namespace TauCeti

variable {E X : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [ChartedSpace E X] {S : Set X}

/-- **Disjoint coordinate balls about finitely many points.** For a finite set `S`, there is an
open embedding of `S × ball 0 2` into `X` sending `(s, 0)` to `s`: on each slice it is a chart
inverse precomposed with a rescaling, and distinct slices land in disjoint open sets. -/
private theorem exists_isOpenEmbedding_prod_ball (hS : S.Finite) :
    ∃ F : S × ball (0 : E) 2 → X, IsOpenEmbedding F ∧
      ∀ s, F (s, ⟨0, mem_ball_self two_pos⟩) = s := by
  have := hS.to_subtype
  obtain ⟨W, hW, hWd⟩ := hS.t2_separation
  -- In the chart at `s`, a ball of radius `ε s` about `s` lies in the target and maps into `W s`.
  have hε (s : S) : ∃ ε > 0, ball (chartAt E (s : X) s) ε ⊆
      (chartAt E (s : X)).target ∩ (chartAt E (s : X)).symm ⁻¹' W s :=
    isOpen_iff.1 ((chartAt E (s : X)).isOpen_inter_preimage_symm (hW s).2) _
      ⟨(chartAt E (s : X)).map_source (mem_chart_source E _), by
        simpa [(chartAt E (s : X)).left_inv (mem_chart_source E _)] using (hW s).1⟩
  choose ε hε₀ hεW using hε
  -- The rescaling `z ↦ c s + (ε s / 2) • z` sends `ball 0 2` into `ball (c s) (ε s)`.
  have hball (s : S) {z : E} (hz : z ∈ ball (0 : E) 2) :
      chartAt E (s : X) s + (ε s / 2) • z ∈ ball (chartAt E (s : X) s) (ε s) := by
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_of_nonneg (by linarith [hε₀ s])]
    nlinarith [hε₀ s]
  let g (s : S) (z : E) : X := (chartAt E (s : X)).symm (chartAt E (s : X) s + (ε s / 2) • z)
  refine ⟨fun p ↦ g p.1 p.2, .of_continuous_injective_isOpenMap
    (continuous_prod_of_discrete_left.2 fun s ↦ ((chartAt E (s : X)).continuousOn_symm.comp
      (by fun_prop) fun z hz ↦ (hεW s (hball s hz)).1).comp_continuous continuous_subtype_val
        fun z ↦ z.2) (fun p q h ↦ ?_) (isOpenMap_prod_of_discrete_left.2 fun s U hU ↦ ?_),
    fun s ↦ by simp [g, (chartAt E (s : X)).left_inv (mem_chart_source E _)]⟩
  · -- The common value lies in `W p.1 ∩ W q.1`, so `p.1 = q.1`; charts are injective.
    obtain ⟨⟨s, hsS⟩, z, hz⟩ := p
    obtain ⟨⟨s', hs'S⟩, z', hz'⟩ := q
    have h₁ : g ⟨s, hsS⟩ z ∈ W s := (hεW ⟨s, hsS⟩ (hball ⟨s, hsS⟩ hz)).2
    have h₂ : g ⟨s', hs'S⟩ z' ∈ W s' := (hεW ⟨s', hs'S⟩ (hball _ hz')).2
    simp only at h
    obtain rfl : s = s' := hWd.elim hsS hs'S <| not_disjoint_iff.2 ⟨_, h₁, h ▸ h₂⟩
    have := (chartAt E s).symm.injOn (hεW ⟨s, hsS⟩ (hball _ hz)).1
      (hεW ⟨s, hsS⟩ (hball _ hz')).1 h
    simpa using smul_right_injective E (by linarith [hε₀ ⟨s, hsS⟩]) (add_left_cancel this)
  · -- On a slice the map is a chart inverse after an affine homeomorphism of `E`.
    rw [← image_image (g s), ← image_image (chartAt E (s : X)).symm]
    exact (chartAt E (s : X)).isOpen_image_symm_of_subset_target
      (((isOpenMap_add_left _).comp (isOpenMap_smul₀ (by linarith [hε₀ s])))
        _ (isOpen_ball.isOpenMap_subtype_val U hU))
      (by rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩; exact (hεW s (hball s z.2)).1)

variable [FiniteDimensional ℝ E]

/-- **The Euler characteristic of the complement of finitely many points.** Let `X` be a
Hausdorff space charted on a finite-dimensional real normed space `E`, and `S ⊆ X` a finite set.
If `X` and `X \ S` have finite CW type, then `χ(X \ S) = χ(X) - (-1) ^ dim E · #S`. -/
theorem eulerChar_compl_of_finite (hS : S.Finite) [FiniteCWType X] [FiniteCWType ↥Sᶜ] :
    eulerChar ↥Sᶜ = eulerChar X - (-1) ^ finrank ℝ E * S.ncard := by
  have := hS.to_subtype
  obtain ⟨F, hF, hzero⟩ := exists_isOpenEmbedding_prod_ball (E := E) hS
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

end TauCeti
