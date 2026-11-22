/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Covering
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.GenusCapDuality
public import TauCeti.Topology.Covering.Degree
public import TauCeti.Topology.Covering.IsFiniteCover
public import TauCeti.Topology.Covering.Proper

/-!
# Genus relation for connected finite surface covers under cap duality

If the rational middle-degree cap map is injective on the base connected oriented surface,
its Euler characteristic is even. Cover multiplicativity transfers evenness to the covering
surface, so both satisfy the genus identity. This gives
`genus(T) - 1 = degree * (genus(S) - 1)`.
-/

public noncomputable section

open AlgebraicTopology CategoryTheory Module MonoidalCategory

namespace TauCeti

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {T S : Type} [TopologicalSpace T] [T2Space T] [ChartedSpace E T]
  [ConnectedSpace T]
  [TopologicalSpace S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
  [ChartedSpace F S] [FiniteCWType S]
  {q : T → S}

/-- For a connected finite cover of closed oriented surfaces with base of finite CW type,
middle-degree cap injectivity on the base implies the usual genus relation. -/
theorem IsFiniteCover.genus_sub_one_eq_mul_of_injective_cap (hq : IsFiniteCover q)
    (oT : HomologicalOrientation T E 2) (oS : HomologicalOrientation S F 2)
    (hnT : finrank ℝ E = 2) (hnS : finrank ℝ F = 2)
    (μS : ((singularHomologyFunctor (ModuleCat ℚ) 2).obj (𝟙_ (ModuleCat ℚ))).obj
      (TopCat.of S))
    (hinjS : Function.Injective
      ((TopCat.of S).singularCapLinearMap ℚ (by decide : 1 + 1 = 2) μS)) (y : S) :
    letI := hq.isCoveringMap.compactSpace hq.finite_fiber
    letI := hq.isCoveringMap.finiteCWType hq.finite_fiber
    (RiemannSurface.genus T : ℤ) - 1 =
      Nat.card (q ⁻¹' {y}) * ((RiemannSurface.genus S : ℤ) - 1) := by
  let : CompactSpace T := hq.isCoveringMap.compactSpace hq.finite_fiber
  let : FiniteCWType T := hq.isCoveringMap.finiteCWType hq.finite_fiber
  have hχS := oS.eulerChar_eq_two_sub_two_mul_genus_of_injective_cap hnS μS hinjS
  have hχ : eulerChar T = (Nat.card (q ⁻¹' {y}) : ℤ) * eulerChar S :=
    eulerChar_eq_mul_of_isCoveringMap hq.isCoveringMap hq.finite_fiber
      (fun x ↦ by
        simpa only [IsCoveringMap.degree_apply] using
          hq.isCoveringMap.degree.apply_eq_of_preconnectedSpace x y)
  have hχT := RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff.mpr
    ⟨oT.eulerChar_le_two hnT, by
      rw [hχ]
      exact (RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff.mp hχS).2.mul_left _⟩
  rw [hχT, hχS] at hχ
  nlinarith

end TauCeti
