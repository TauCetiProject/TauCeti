/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Summation
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
import Mathlib.Topology.Algebra.SeparationQuotient.Section
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Pietsch's lifting identity for Kolmogorov numbers

Over a complete nontrivially normed field `𝕜`, scalar `ℓ¹` spaces have the metric lifting property
for finite-rank approximation: every bounded operator `S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F` into a
seminormed space has equal approximation and Kolmogorov numbers,
`S.singularValue n = S.kolmogorovNumber n`
(`ContinuousLinearMap.singularValue_lpOne_eq_kolmogorovNumber`). Neither completeness nor
Hausdorffness of `F` is required, and `ι` and `F` may live in arbitrary universes.

Combining this equality on scalar `ℓ¹` with quotient invariance of Kolmogorov numbers
(`ContinuousLinearMap.kolmogorovNumber_comp_of_isQuotient`) expresses the Kolmogorov numbers
of an arbitrary operator `T : E →L[𝕜] F` as approximation numbers after precomposition with a
summation surjection (**Pietsch's lifting identity**):
* for any operator `Q : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E` over a complete nontrivially normed field
  `𝕜` whose underlying bounded additive homomorphism is a normed quotient map,
  `(T ∘L Q).singularValue n = T.kolmogorovNumber n`
  (`ContinuousLinearMap.singularValue_comp_lpOne_of_isQuotient`);
* in particular, for a complete normed domain `E` over a complete densely normed field `𝕜`,
  `(T ∘L TauCeti.unitBallSummation 𝕜 E).singularValue n = T.kolmogorovNumber n`
  (`ContinuousLinearMap.singularValue_comp_unitBallSummation`).

## Main results

* `ContinuousLinearMap.singularValue_lpOne_eq_kolmogorovNumber`: `aₙ(S) = dₙ(S)` for operators
  out of `lp (fun _ : ι ↦ 𝕜) 1` over complete scalar fields.
* `ContinuousLinearMap.singularValue_comp_lpOne_of_isQuotient`: `aₙ(T ∘ Q) = dₙ(T)` for every
  normed quotient map `Q` from scalar `ℓ¹`.
* `ContinuousLinearMap.singularValue_comp_unitBallSummation`: Pietsch's lifting identity.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4, Theorem 4.3.
* A. Pietsch, *Operator Ideals*, North-Holland (1980), §11.5.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.4.
-/

public section

open scoped ENNReal NNReal

namespace ContinuousLinearMap

section LpOneLifting

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a complete scalar field, uniform approximation of the unit coordinate images of
`S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F` within `C ≥ 0` by vectors in a finite-dimensional subspace
`V ≤ F` yields a bounded operator `L` with range in `V` and `‖S - L‖ ≤ C`. -/
private theorem exists_range_le_norm_sub_le_of_lpOne [DecidableEq ι]
    (S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) (V : Submodule 𝕜 F) [FiniteDimensional 𝕜 V]
    {C : ℝ} (hC : 0 ≤ C) {v : ι → V} (hv : ∀ i : ι, ‖S (lp.single 1 i 1) - (v i : F)‖ ≤ C) :
    ∃ L : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F, L.range ≤ V ∧ ‖S - L‖ ≤ C := by
  -- Sum the coordinate approximants in `SeparationQuotient V` (complete by finite
  -- dimensionality) and lift back to `V` via `SeparationQuotient.outCLM`.
  have : CompleteSpace (SeparationQuotient V) :=
    FiniteDimensional.completeSpace 𝕜 (SeparationQuotient V)
  let u : ι → SeparationQuotient V := fun i ↦ SeparationQuotient.mk (v i)
  have hu : BddAbove (Set.range fun i ↦ ‖u i‖) := by
    refine ⟨‖S‖ + C, mem_upperBounds.mpr <| Set.forall_mem_range.mpr fun i ↦ ?_⟩
    rw [SeparationQuotient.norm_mk, ← Submodule.norm_coe]
    calc ‖(v i : F)‖
        = ‖S (lp.single 1 i 1) - (S (lp.single 1 i 1) - (v i : F))‖ := by abel_nf
      _ ≤ ‖S (lp.single 1 i 1)‖ + ‖S (lp.single 1 i 1) - (v i : F)‖ := norm_sub_le _ _
      _ ≤ ‖S‖ + C := add_le_add (S.norm_apply_lp_single_le i) (hv i)
  set L : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F :=
    V.subtypeL ∘L SeparationQuotient.outCLM 𝕜 V ∘L TauCeti.lpOneSummation 𝕜 u hu with hL
  have hL_range : L.range ≤ V := by
    rintro _ ⟨α, rfl⟩
    rw [hL]
    exact Subtype.prop _
  have hL_single (i : ι) :
      L (lp.single 1 i 1) = (SeparationQuotient.outCLM 𝕜 V (u i) : F) := by
    simp [hL]
  refine ⟨L, hL_range, (S - L).opNorm_lpOne_le hC fun i ↦ ?_⟩
  have hout : ‖(v i : F) - L (lp.single 1 i 1)‖ = 0 := by
    rw [hL_single, ← Submodule.coe_sub, Submodule.norm_coe, ← SeparationQuotient.norm_mk]
    simp [u]
  rw [sub_apply]
  calc ‖S (lp.single 1 i 1) - L (lp.single 1 i 1)‖
      ≤ ‖S (lp.single 1 i 1) - (v i : F)‖ + ‖(v i : F) - L (lp.single 1 i 1)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C + 0 := add_le_add (hv i) hout.le
    _ = C := add_zero C

/-- **Lifting property of scalar `ℓ¹`.** Over a complete nontrivially normed field, the
approximation numbers and Kolmogorov numbers coincide for every bounded operator out of
`lp (fun _ : ι ↦ 𝕜) 1` into a seminormed space. -/
theorem singularValue_lpOne_eq_kolmogorovNumber (S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) (n : ℕ) :
    S.singularValue n = S.kolmogorovNumber n := by
  classical
  refine le_antisymm ?_ (S.kolmogorovNumber_le_singularValue n)
  refine le_kolmogorovNumber_iff.mpr fun V hV ↦
    NNReal.coe_le_coe.mp <| le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have hex (i : ι) : ∃ v : V, ‖S (lp.single 1 i 1) - v.val‖ ≤ ‖V.mkQL ∘L S‖ + ε / 2 := by
    obtain ⟨m, hm, hmlt⟩ :=
      Submodule.Quotient.norm_mk_lt (V.mkQL (S (lp.single 1 i 1))) (half_pos hε)
    refine ⟨⟨S (lp.single 1 i 1) - m, (Submodule.Quotient.eq V).mp hm.symm⟩, ?_⟩
    rw [sub_sub_cancel]
    exact hmlt.le.trans (add_le_add_left ((V.mkQL ∘L S).norm_apply_lp_single_le i) _)
  choose v hv using hex
  obtain ⟨L, hLrange, hnorm⟩ :=
    exists_range_le_norm_sub_le_of_lpOne S V (by positivity) hv
  have hle : (S.singularValue n : ℝ) ≤ ‖S - L‖ := by
    exact_mod_cast S.singularValue_le_nnnorm_sub ((Submodule.rank_mono hLrange).trans hV)
  calc (S.singularValue n : ℝ) ≤ ‖V.mkQL ∘L S‖ + ε / 2 := hle.trans hnorm
    _ < (‖V.mkQL ∘L S‖₊ : ℝ) + ε := by
      rw [coe_nnNorm]
      linarith

/-- Precomposing `T : E →L[𝕜] F` with any continuous linear operator out of scalar `ℓ¹` whose
underlying bounded additive homomorphism is a normed quotient map turns the Kolmogorov numbers of
`T` into approximation numbers, over any complete nontrivially normed field. -/
theorem singularValue_comp_lpOne_of_isQuotient {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (T : E →L[𝕜] F)
    {Q : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E} (hQ : Q.toNormedAddGroupHom.IsQuotient) (n : ℕ) :
    (T ∘L Q).singularValue n = T.kolmogorovNumber n :=
  ((T ∘L Q).singularValue_lpOne_eq_kolmogorovNumber n).trans
    (T.kolmogorovNumber_comp_of_isQuotient hQ n)

end LpOneLifting

section UnitBallLifting

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch's lifting identity.** Over a complete densely normed field and for a complete normed
domain `E`, the approximation numbers of `T ∘L TauCeti.unitBallSummation 𝕜 E` equal the Kolmogorov
numbers of `T`. -/
@[simp]
theorem singularValue_comp_unitBallSummation (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitBallSummation 𝕜 E).singularValue n = T.kolmogorovNumber n :=
  T.singularValue_comp_lpOne_of_isQuotient
    (TauCeti.isQuotient_toNormedAddGroupHom_unitBallSummation 𝕜 E) n

end UnitBallLifting

end ContinuousLinearMap
