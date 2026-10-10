/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The Hilbert--Schmidt energy of a bounded operator

For a bounded operator `T : E →L[𝕜] F` between Hilbert spaces and a Hilbert basis `b` of
the domain, the **Hilbert--Schmidt energy** is the extended real number

```
T.hilbertSchmidtEnergy b = ∑' i, ‖T (b i)‖ₑ ^ 2.
```

It is the square of the Hilbert--Schmidt norm, and `T` is a Hilbert--Schmidt operator
exactly when the energy is finite.

## Why `ℝ≥0∞`

Taking values in `ℝ≥0∞` rather than `ℝ` is what makes this development
hypothesis-free.  Every sum converges in `ℝ≥0∞`, so the energy is defined for *every*
bounded operator with no summability side condition, and — this is the point — the
Fubini exchange `ENNReal.tsum_comm` used in `hilbertSchmidtEnergy_adjoint` needs no
integrability hypothesis either.  The same convention is used for the gauge of
`TauCeti.OperatorIdealFamily`, whose Hilbert--Schmidt instance this file is groundwork
for.

## Main results

* `HilbertBasis.tsum_enorm_inner_sq`: **Parseval** in `ℝ≥0∞`, `∑' i, ‖⟪b i, v⟫‖ₑ ^ 2 = ‖v‖ₑ ^ 2`;
* `ContinuousLinearMap.hilbertSchmidtEnergy_adjoint`: the **adjoint swap**, the energy of
  `T` in a basis of `E` equals the energy of `T⋆` in a basis of `F`.  Note that no
  self-adjointness, and indeed no relation at all between `E` and `F`, is assumed;
* `ContinuousLinearMap.hilbertSchmidtEnergy_indep`: consequently the energy does not depend
  on the chosen basis, so it is an invariant of `T` alone;
* `ContinuousLinearMap.enorm_apply_sq_le_hilbertSchmidtEnergy_mul`: the energy dominates the
  operator norm, `‖T x‖ₑ ^ 2 ≤ (T.hilbertSchmidtEnergy b) * ‖x‖ₑ ^ 2`;
* `ContinuousLinearMap.hilbertSchmidtEnergy_comp_left_le` and
  `ContinuousLinearMap.hilbertSchmidtEnergy_comp_right_le`: the **ideal property**, the
  energy is contracted by composition with bounded operators on either side.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: the two Parseval lemmas follow the shape of the `ℂ`-only versions in
  `vendor/Spectra` (`Spectra.QuantumMechanics.Channels.{hasSum_norm_inner_sq,
  tsum_enorm_inner_sq}`), which are themselves short consequences of Mathlib's
  `HilbertBasis.hasSum_inner_mul_inner`; they are restated here for a general `RCLike`
  scalar field.  The swap lemma is *not* a transcription: Spectra's
  `tsum_enorm_apply_sq_comm` is stated for a self-adjoint endomorphism, while the
  rectangular statement proved here needs no such hypothesis.  Everything downstream of the
  swap is new.
-/

open scoped ENNReal InnerProductSpace

public section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable {ι κ : Type*}

namespace HilbertBasis

/-- **Parseval's identity**, real form: the squared moduli of the coordinates of `v` in a
Hilbert basis sum to `‖v‖ ^ 2`. -/
theorem hasSum_norm_inner_sq (b : HilbertBasis ι 𝕜 E) (v : E) :
    HasSum (fun i => ‖⟪b i, v⟫_𝕜‖ ^ 2) (‖v‖ ^ 2) := by
  have key : (fun i => ‖⟪b i, v⟫_𝕜‖ ^ 2) = fun i => RCLike.re (⟪v, b i⟫_𝕜 * ⟪b i, v⟫_𝕜) := by
    funext i
    rw [← inner_conj_symm v (b i), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hsum : (‖v‖ ^ 2 : ℝ) = RCLike.re ⟪v, v⟫_𝕜 := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [key, hsum]
  simpa only [RCLike.reCLM_apply] using
    (b.hasSum_inner_mul_inner v v).mapL (RCLike.reCLM (K := 𝕜))

/-- **Parseval's identity** in `ℝ≥0∞`.  Unlike the real form this is an unconditional
equation between extended reals, which is what lets it be substituted under a `tsum`
without a summability hypothesis. -/
theorem tsum_enorm_inner_sq (b : HilbertBasis ι 𝕜 E) (v : E) :
    ∑' i, ‖⟪b i, v⟫_𝕜‖ₑ ^ 2 = ‖v‖ₑ ^ 2 := by
  have hnn : HasSum (fun i => ‖⟪b i, v⟫_𝕜‖₊ ^ 2) (‖v‖₊ ^ 2) := by
    rw [← NNReal.hasSum_coe]
    push_cast
    exact b.hasSum_norm_inner_sq v
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow]
  rw [← ENNReal.coe_tsum hnn.summable, hnn.tsum_eq]

end HilbertBasis

namespace ContinuousLinearMap

/-- The **Hilbert--Schmidt energy** of `T` measured in the Hilbert basis `b` of the domain:
the sum of the squared norms of the columns of `T`.  It is the square of the
Hilbert--Schmidt norm, and by `hilbertSchmidtEnergy_indep` it does not in fact depend on
`b`. -/
@[expose]
noncomputable def hilbertSchmidtEnergy (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

/-- Rewrite form of the Hilbert--Schmidt energy as the sum of squared column norms. -/
theorem hilbertSchmidtEnergy_def (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b = ∑' i, ‖T (b i)‖ₑ ^ 2 := (rfl)
/-- The energy is the supremum of its finite partial sums. -/
theorem hilbertSchmidtEnergy_eq_iSup_sum (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b = ⨆ s : Finset ι, ∑ i ∈ s, ‖T (b i)‖ₑ ^ 2 :=
  ENNReal.tsum_eq_iSup_sum

/-- The zero operator has zero energy. -/
@[simp] theorem hilbertSchmidtEnergy_zero (b : HilbertBasis ι 𝕜 E) :
    (0 : E →L[𝕜] F).hilbertSchmidtEnergy b = 0 := by
  simp [hilbertSchmidtEnergy]

/-- Energy is unchanged by negation. -/
@[simp] theorem hilbertSchmidtEnergy_neg (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (-T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  simp [hilbertSchmidtEnergy]

/-- The energy is quadratically homogeneous: scaling the operator by `c` scales the energy by
`‖c‖²`, not `‖c‖`. -/
theorem hilbertSchmidtEnergy_smul (c : 𝕜) (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (c • T).hilbertSchmidtEnergy b = ‖c‖ₑ ^ 2 * T.hilbertSchmidtEnergy b := by
  simp only [hilbertSchmidtEnergy, smul_apply, enorm_smul, mul_pow]
  exact ENNReal.tsum_mul_left

/-- Expanding each column of `T` in a Hilbert basis of the codomain turns the energy into a
double sum of squared matrix entries. -/
theorem hilbertSchmidtEnergy_eq_tsum_tsum (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    T.hilbertSchmidtEnergy b = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := by
  simp_rw [hilbertSchmidtEnergy, c.tsum_enorm_inner_sq]

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- **The adjoint swap.**  Summing the squared norms of the columns of `T` gives the same
extended real as summing the squared norms of the columns of `T⋆`, in any pair of Hilbert
bases of the two spaces.

This is the whole content of the Hilbert--Schmidt theory at this level: transposing the
matrix of `T` is exactly the Fubini exchange, which in `ℝ≥0∞` is unconditional. -/
theorem hilbertSchmidtEnergy_adjoint (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    T.hilbertSchmidtEnergy b = T.adjoint.hilbertSchmidtEnergy c := by
  have hentry : ∀ i j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ = ‖⟪b i, T.adjoint (c j)⟫_𝕜‖ₑ := by
    intro i j
    rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm (b i) (T.adjoint (c j)),
      enorm_eq_nnnorm, enorm_eq_nnnorm, RCLike.nnnorm_conj]
  calc T.hilbertSchmidtEnergy b
      = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := T.hilbertSchmidtEnergy_eq_tsum_tsum b c
    _ = ∑' j, ∑' i, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ‖⟪b i, T.adjoint (c j)⟫_𝕜‖ₑ ^ 2 :=
        tsum_congr fun j => tsum_congr fun i => by rw [hentry i j]
    _ = T.adjoint.hilbertSchmidtEnergy c :=
        (T.adjoint.hilbertSchmidtEnergy_eq_tsum_tsum c b).symm

/-- **The energy is a basis-independent invariant of the operator.**

Note the two bases are allowed to be indexed by different types, so this covers the
comparison of a countable with an uncountable indexing. -/
theorem hilbertSchmidtEnergy_indep (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis κ 𝕜 E) :
    T.hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b' := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [T.hilbertSchmidtEnergy_adjoint b c, ← T.hilbertSchmidtEnergy_adjoint b' c]

/-- The energy dominates the operator norm: every value `T x` is bounded by the square root
of the energy times `‖x‖`.  In particular an operator of finite energy is bounded, which is
the qualitative half of the containment of the Hilbert--Schmidt ideal in the bounded
operators. -/
theorem enorm_apply_sq_le_hilbertSchmidtEnergy_mul (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (x : E) :
    ‖T x‖ₑ ^ 2 ≤ T.hilbertSchmidtEnergy b * ‖x‖ₑ ^ 2 := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
  have hcs : ∀ j, ‖⟪c j, T x⟫_𝕜‖ₑ ^ 2 ≤ ‖T.adjoint (c j)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
    intro j
    rw [← ContinuousLinearMap.adjoint_inner_left, ← mul_pow]
    gcongr
    simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using
      nnnorm_inner_le_nnnorm (𝕜 := 𝕜) (T.adjoint (c j)) x
  calc ‖T x‖ₑ ^ 2 = ∑' j, ‖⟪c j, T x⟫_𝕜‖ₑ ^ 2 := (c.tsum_enorm_inner_sq (T x)).symm
    _ ≤ ∑' j, ‖T.adjoint (c j)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := ENNReal.tsum_le_tsum hcs
    _ = T.adjoint.hilbertSchmidtEnergy c * ‖x‖ₑ ^ 2 := ENNReal.tsum_mul_right
    _ = T.hilbertSchmidtEnergy b * ‖x‖ₑ ^ 2 := by rw [← T.hilbertSchmidtEnergy_adjoint b c]

/-- Taking adjoints preserves the extended operator norm.  Mathlib has this for the real
norm (`ContinuousLinearMap.adjoint` is a `LinearIsometryEquiv`) but not for `‖·‖ₑ`. -/
theorem enorm_adjoint (T : E →L[𝕜] F) : ‖T.adjoint‖ₑ = ‖T‖ₑ := by
  simp only [enorm_eq_nnnorm]
  norm_cast
  rw [← NNReal.coe_inj]
  simp

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- **Left ideal property.**  Postcomposing with a bounded operator contracts the energy by
at most the square of its norm. -/
theorem hilbertSchmidtEnergy_comp_left_le (A : F →L[𝕜] G) (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    (A ∘L T).hilbertSchmidtEnergy b ≤ ‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy b := by
  calc (A ∘L T).hilbertSchmidtEnergy b = ∑' i, ‖A (T (b i))‖ₑ ^ 2 := (rfl)
    _ ≤ ∑' i, ‖A‖ₑ ^ 2 * ‖T (b i)‖ₑ ^ 2 :=
        ENNReal.tsum_le_tsum fun i => by rw [← mul_pow]; gcongr; exact A.le_opENorm _
    _ = ‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy b := ENNReal.tsum_mul_left

/-- **Right ideal property.**  Precomposing with a bounded operator contracts the energy by
at most the square of its norm. -/
theorem hilbertSchmidtEnergy_comp_right_le (T : F →L[𝕜] G) (B : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    (T ∘L B).hilbertSchmidtEnergy b ≤ ‖B‖ₑ ^ 2 * T.hilbertSchmidtEnergy c := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis 𝕜 G
  rw [(T ∘L B).hilbertSchmidtEnergy_adjoint b d, T.hilbertSchmidtEnergy_adjoint c d,
    ContinuousLinearMap.adjoint_comp]
  refine (B.adjoint.hilbertSchmidtEnergy_comp_left_le T.adjoint d).trans ?_
  gcongr
  exact (B.enorm_adjoint).le

end ContinuousLinearMap
