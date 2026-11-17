/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.QuotientRange
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth quotient coordinates over manifold parameters

A family of split injections parametrized by a manifold admits a fixed closed complement
near each parameter. If the family is `C^n` on an open domain, its quotient-coordinate
operators are `C^n` on a single smaller open domain, including when `n = ∞`.

These operators give fixed model fibres for normal-bundle charts: the quotient of the
ambient model space by the range of a coordinate differential is identified with the
complement by `ContinuousLinearMap.quotientRangeEquiv`. Regularity is checked on ambient
representatives, before assigning a smooth structure to the total quotient bundle.

The neighbourhood theorem uses regularity on an open domain, rather than regularity
only at its centre. This distinction matters at smooth order: smoothness at one point
does not in general give one neighbourhood on which the family is smooth.

The same coordinates give smooth local frames of annihilators: if the family consists of
injections of `𝕜ᵏ` into a space of dimension `k + r`, the coordinates of the quotient coordinate
operators in a basis of the complement are `r` covectors depending `C^n` on the parameter, linearly
independent and annihilating the range at every point
(`ContMDiffOn.exists_contMDiffOn_linearIndependent_comp_eq_zero`). This adapts the chart
construction of conormal frames (`chartConormalFrame` in
`TauCeti/Geometry/Manifold/VectorBundle/Cotangent/Conormal/Subbundle.lean`).

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

/- Formal sources: the quotient-coordinate calculus in `TauCeti.Analysis.Calculus.QuotientRange`
and the fixed-complement theorem `ContinuousAt.exists_isInvertible_coprod_subtypeL`. -/

public section

open Set Filter Topology
open scoped Manifold ContDiff

variable {𝕜 X E F G H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 X H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {A : M → E →L[𝕜] F} {x : M} {s : Set M} {n : ℕ∞ω}

/-- Quotient coordinates inherit the regularity of a manifold-parametrized family,
within a set, wherever the fixed complement is valid. -/
theorem ContMDiffWithinAt.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] F) n A s x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜] G) n
      (fun y => (A y).quotientRangeCoordinate B) s x :=
  (contDiffAt_id.quotientRangeCoordinate B h).contMDiffAt.comp_contMDiffWithinAt x hA

/-- Quotient-coordinate operators are `C^n` at a parameter where the fixed complement
is valid and the operator family is `C^n`. -/
theorem ContMDiffAt.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) n A x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n (fun y => (A y).quotientRangeCoordinate B) x :=
  (hA.contMDiffWithinAt.quotientRangeCoordinate B h).contMDiffAt univ_mem

/-- A fixed complement gives `C^n` quotient-coordinate operators throughout any
domain on which it is valid and the operator family is `C^n`. -/
theorem ContMDiffOn.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] F) n A s) (B : G →L[𝕜] F)
    (h : ∀ y ∈ s, ((A y).coprod B).IsInvertible) :
    ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n (fun y => (A y).quotientRangeCoordinate B) s :=
  fun y hy => (hA y hy).quotientRangeCoordinate B (h y hy)

/-- A `C^n` operator family on an open manifold domain, split injective at one point,
admits a fixed closed complementary fibre and `C^n` quotient coordinates on one open
neighbourhood of that point. Smooth and analytic orders are included.

The complement is valid at every point of the neighbourhood, so
`ContinuousLinearMap.quotientRangeEquiv` identifies every moving quotient with this
same model fibre. Completeness is required only of the ambient model. -/
theorem ContMDiffOn.exists_contMDiffOn_quotientRangeCoordinate [CompleteSpace F]
    (hA : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] F) n A s) (hs : IsOpen s) (hx : x ∈ s)
    (h : (A x).HasLeftInverse) :
    ∃ Q : Submodule 𝕜 F, IsClosed (Q : Set F) ∧
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧
        (∀ y ∈ U, ((A y).coprod Q.subtypeL).IsInvertible) ∧
        ContMDiffOn I 𝓘(𝕜, F →L[𝕜] Q) n
          (fun y => (A y).quotientRangeCoordinate Q.subtypeL) U := by
  obtain ⟨Q, hQ, V, hV, hxV, hInv⟩ :=
    (hA.continuousOn.continuousAt (hs.mem_nhds hx)).exists_isInvertible_coprod_subtypeL h
  have : CompleteSpace (E × Q) :=
    ContinuousLinearMap.completeSpace_of_isInvertible (hInv x hxV)
  refine ⟨Q, hQ, V ∩ s, hV.inter hs, ⟨hxV, hx⟩, inter_subset_right,
    (fun y hy => hInv y hy.1), ?_⟩
  exact (hA.mono inter_subset_right).quotientRangeCoordinate Q.subtypeL
    (fun y hy => hInv y hy.1)

/-- **Smooth local frames of annihilators.** Let `A y : 𝕜ᵏ →L[𝕜] F` be a family of operators,
depending `C^n` on `y` in an open set `s`, into a space of dimension `k + r`, and injective at a
point `x` of `s`. Near `x` there are `r` covectors `c j y`, depending `C^n` on `y`, which at every
point are linearly independent and annihilate the range of `A y`. They are the coordinates of the
quotient coordinate operators of `A y` for a fixed complement of the range of `A x`. -/
theorem ContMDiffOn.exists_contMDiffOn_linearIndependent_comp_eq_zero [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F] {k r : ℕ} {A : M → (Fin k → 𝕜) →L[𝕜] F}
    (hA : ContMDiffOn I 𝓘(𝕜, (Fin k → 𝕜) →L[𝕜] F) n A s) (hs : IsOpen s) (hx : x ∈ s)
    (hinj : Function.Injective (A x)) (hk : k + r = Module.finrank 𝕜 F) :
    ∃ U ⊆ s, IsOpen U ∧ x ∈ U ∧ ∃ c : Fin r → M → F →L[𝕜] 𝕜,
      (∀ j, ContMDiffOn I 𝓘(𝕜, F →L[𝕜] 𝕜) n (c j) U) ∧
      ∀ y ∈ U, LinearIndependent 𝕜 (c · y) ∧ ∀ j, c j y ∘L A y = 0 := by
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  -- In finite dimensions every linear left inverse of `A x` is continuous.
  obtain ⟨p, hp⟩ := (A x).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨Q, -, U, hU, hxU, hUs, hInv, hq⟩ := hA.exists_contMDiffOn_quotientRangeCoordinate hs hx
    ⟨LinearMap.toContinuousLinearMap p, fun v ↦ LinearMap.congr_fun hp v⟩
  -- The complement `Q` has dimension `r`; identify it with `𝕜ʳ`.
  obtain ⟨e₀, -⟩ := hInv x hxU
  have hQ : Module.finrank 𝕜 Q = Module.finrank 𝕜 (Fin r → 𝕜) := by
    have he₀ := e₀.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, Module.finrank_fin_fun] at he₀
    rw [Module.finrank_fin_fun]
    omega
  let eQ : Q ≃L[𝕜] (Fin r → 𝕜) := ContinuousLinearEquiv.ofFinrankEq hQ
  let c : Fin r → M → F →L[𝕜] 𝕜 := fun j y ↦
    ContinuousLinearMap.proj j ∘L (eQ : Q →L[𝕜] Fin r → 𝕜) ∘L
      (A y).quotientRangeCoordinate Q.subtypeL
  refine ⟨U, hUs, hU, hxU, c, fun j ↦ contMDiffOn_const.clm_comp (contMDiffOn_const.clm_comp hq),
    fun y hy ↦ ⟨Fintype.linearIndependent_iff.mpr fun μ hμ i ↦ ?_, fun j ↦ ?_⟩⟩
  · -- Evaluate on the complement vector with coordinates `Pi.single i 1`.
    have h := (A y).quotientRangeCoordinate_apply_right (hInv y hy) (eQ.symm (Pi.single i 1))
    rw [Submodule.subtypeL_apply] at h
    simpa [c, h, Pi.single_apply] using
      DFunLike.congr_fun hμ (Q.subtypeL (eQ.symm (Pi.single i 1)))
  · ext v
    simp [c]
