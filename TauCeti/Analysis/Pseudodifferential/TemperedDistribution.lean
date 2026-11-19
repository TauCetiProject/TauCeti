/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Transpose
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.FiniteOrder
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Pseudodifferential operators on tempered distributions

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose estimates hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Its quantization `Op(a)` is a continuous operator on Schwartz space
(`TauCeti.Symbol.quantizeUniformCLM`), and so is its transpose `Op(a)ᵗ` for the bilinear pairing
`⟨φ, u⟩ = ∫ φ u`: `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` for all Schwartz functions `u` and `φ`
(`TauCeti.Symbol.transposeUniformCLM`, `TauCeti.Symbol.integral_mul_quantizeUniformCLM`). The
transpose is obtained from the formal adjoint `Op_R(ā)`
(`TauCeti.Symbol.integral_inner_quantizeUniformCLM`) by conjugating its input and output, and it
is the only operator with this property (`TauCeti.Symbol.eq_transposeUniformCLM`).

Duality then extends `Op(a)` to tempered distributions with values in any topological vector
space `F`: `Op(a) T = T ∘ Op(a)ᵗ` (`TauCeti.Symbol.quantizeTempered`), a continuous operator on
`𝓢'(ℝⁿ, F)` for the topology of pointwise convergence. On the tempered distribution of a Schwartz
function `u` it gives the tempered distribution of `Op(a) u`
(`TauCeti.Symbol.quantizeTempered_toTemperedDistributionCLM`), and every Sobolev realization
`H^s → H^r` of `Op(a)`, such as `TauCeti.Symbol.quantizeSobolev` for a symbol with compact spatial
support, is the restriction of this one operator to `H^s`
(`TauCeti.Symbol.toDistr_eq_quantizeTempered`, `TauCeti.Symbol.toDistr_quantizeSobolev`).
Pseudodifferential operators thus act on arbitrary tempered distributions, as needed for
distributional regularity and for wave front sets, compatibly with all their Sobolev mappings.

The rules of the calculus on Schwartz space carry over to distributions, since an identity between
transposes is detected by testing against Schwartz functions:

* a constant symbol `T` acts as multiplication by `T 1`, so the symbol `1` is the identity
  (`TauCeti.Symbol.quantizeTempered_const`);
* `∂_j (Op(a) T) = Op(a) (∂_j T) + Op(∂_{x_j} a) T`
  (`TauCeti.Symbol.lineDerivOp_quantizeTempered`), with distributional derivatives;
* `Op(a) (∂_v T) = i Op(a ⟪ξ, v⟫) T` (`TauCeti.Symbol.quantizeTempered_lineDerivOp`);
* `x_j Op(a) T = Op(a) (x_j T) + i Op(∂_{ξ_j} a) T` (`TauCeti.Symbol.smulLeftCLM_quantizeTempered`);
* for `b` with compact spatial support, `Op(a # b) = Op(a) ∘ Op(b)` on tempered distributions
  (`TauCeti.Symbol.quantizeTempered_sharp`), from the same identity on Schwartz space
  (`TauCeti.Symbol.quantizeUniformCLM_sharp`).

In particular, for a symbol of order `m` with compact spatial support, `Op(a)` maps tempered
distributions of Sobolev order `s` to tempered distributions of Sobolev order `s - m`
(`TauCeti.Symbol.memSobolev_quantizeTempered`).

## Smoothing operators

A smoothing symbol `r` with compact spatial support maps every tempered distribution `T`, of
arbitrary order and growth, into every Sobolev space `H^t`
(`TauCeti.Symbol.IsSmoothing.memSobolev_quantizeTempered`), so `Op(r) T` is a smooth function
(`TauCeti.Symbol.IsSmoothing.exists_contDiff_quantizeTempered_apply_eq_integral`). This is what
makes the smoothing remainder `Op(r) T` of a parametrix identity `Op(q) Op(p) = 1 + Op(r)`
harmless for distributional regularity. The proof writes `T = (1 + ‖y‖ ^ 2) ^ K S` with `S` of
finite Sobolev order (`TemperedDistribution.exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow`)
and moves each coordinate factor through `Op(r)` with the commutator rule above:
`y_j Op(r) U` equals `(ψ y_j) Op(r) U` for a cutoff `ψ` equal to `1` on the spatial support of
`r` (`TauCeti.Symbol.smulLeftCLM_quantizeTempered_of_eq_one`), and multiplication by the
Schwartz function `ψ y_j` preserves every `H^t`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3
  (operators of order `-∞` are smoothing).
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap BesselPotentialSpace RealInnerProductSpace LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-! ### Quantization of tempered distributions -/

section Tempered

variable (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- **Pseudodifferential operators on tempered distributions.** For a scalar symbol `a` whose
estimates are uniform in the position, the quantization `Op(a)` acts on tempered distributions with
values in `F` by duality, `Op(a) T = T ∘ Op(a)ᵗ` (`TauCeti.Symbol.transposeUniformCLM`), a
continuous operator on `𝓢'(ℝⁿ, F)`. It extends the quantization of Schwartz functions
(`TauCeti.Symbol.quantizeTempered_toTemperedDistributionCLM`) and of Sobolev spaces
(`TauCeti.Symbol.toDistr_eq_quantizeTempered`). -/
def quantizeTempered (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) :
    𝓢'(CoordinateSpace n, F) →L[ℂ] 𝓢'(CoordinateSpace n, F) :=
  PointwiseConvergenceCLM.precomp F (transposeUniformCLM a ha)

variable {F}

/-- `(Op(a) T) φ = T (Op(a)ᵗ φ)`. -/
@[simp]
theorem quantizeTempered_apply_apply (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (T : 𝓢'(CoordinateSpace n, F)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTempered F a ha T φ = T (transposeUniformCLM a ha φ) :=
  (rfl)

/-- On the tempered distribution of a Schwartz function `u`, `Op(a)` gives the tempered
distribution of `Op(a) u`. -/
@[simp]
theorem quantizeTempered_toTemperedDistributionCLM (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTempered ℂ a ha (SchwartzMap.toTemperedDistributionCLM _ ℂ volume u) =
      SchwartzMap.toTemperedDistributionCLM _ ℂ volume (quantizeUniformCLM a ha u) := by
  ext φ
  simp only [quantizeTempered_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    smul_eq_mul]
  exact (integral_mul_quantizeUniformCLM a ha u φ).symm

/-- `Op(a)` on tempered distributions is additive in the symbol. -/
theorem quantizeTempered_add {a b : Symbol n ℂ ℂ m} (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeTempered F (a + b) (ha.add hb) = quantizeTempered F a ha + quantizeTempered F b hb := by
  ext T φ
  simp [transposeUniformCLM_add ha hb]

/-- `Op(a)` on tempered distributions is homogeneous in the symbol. -/
theorem quantizeTempered_smul {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (c : ℂ) :
    quantizeTempered F (c • a) (ha.smul c) = c • quantizeTempered F a ha := by
  ext T φ
  simp [transposeUniformCLM_smul ha c]

/-- `Op(a)` on tempered distributions does not depend on the order at which `a` is considered. -/
theorem quantizeTempered_inclusion {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) (h : m ≤ m') :
    quantizeTempered F (inclusion h a) (ha.inclusion h) = quantizeTempered F a ha := by
  ext T φ
  simp [transposeUniformCLM_inclusion ha h]

/-- `Op(a)` on tempered distributions depends only on the coefficient of `a`. -/
theorem quantizeTempered_congr {a : Symbol n ℂ ℂ m} {b : Symbol n ℂ ℂ m'} (ha : a.IsUniform)
    (hb : b.IsUniform) (h : a.coefficient = b.coefficient) :
    quantizeTempered F a ha = quantizeTempered F b hb := by
  ext T φ
  simp [transposeUniformCLM_congr ha hb h]

/-- A constant symbol `T` acts on tempered distributions as multiplication by `T 1`; in particular
the symbol `1` acts as the identity. -/
theorem quantizeTempered_const (T : ℂ →L[ℂ] ℂ) :
    quantizeTempered F (n := n) (const T) (isUniform_const T) =
      T 1 • ContinuousLinearMap.id ℂ _ := by
  ext S φ
  simp [transposeUniformCLM_const]

/-- **Commutator with a derivative.** `∂_j (Op(a) T) = Op(a) (∂_j T) + Op(∂_{x_j} a) T` for
every tempered distribution `T`. -/
theorem lineDerivOp_quantizeTempered (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) (j : Fin n)
    (T : 𝓢'(CoordinateSpace n, F)) :
    ∂_{EuclideanSpace.single j (1 : ℝ)} (quantizeTempered F a ha T) =
      quantizeTempered F a ha (∂_{EuclideanSpace.single j (1 : ℝ)} T) +
        quantizeTempered F (spatialDeriv j a) (ha.spatialDeriv j) T := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, quantizeTempered_apply_apply, map_neg,
    transposeUniformCLM_lineDerivOp, neg_sub, map_sub, add_apply]
  abel

/-- **Composition with a derivative on the right.** `Op(a) (∂_v T) = i Op(a ⟪ξ, v⟫) T` for every
tempered distribution `T`. -/
theorem quantizeTempered_lineDerivOp (a : Symbol n ℂ ℂ m) (ha : a.IsUniform)
    (v : CoordinateSpace n) (T : 𝓢'(CoordinateSpace n, F)) :
    quantizeTempered F a ha (∂_{v} T) =
      I • quantizeTempered F (a.comp (ofInner v)) (ha.comp (isUniform_ofInner v)) T := by
  ext φ
  simp [transposeUniformCLM_comp_ofInner ha, smul_smul]

/-- **Commutator with a coordinate function.** `x_j Op(a) T = Op(a) (x_j T) + i Op(∂_{ξ_j} a) T`
for every tempered distribution `T`. -/
theorem smulLeftCLM_quantizeTempered (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) (j : Fin n)
    (T : 𝓢'(CoordinateSpace n, F)) :
    TemperedDistribution.smulLeftCLM F (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ))
        (quantizeTempered F a ha T) =
      quantizeTempered F a ha
          (TemperedDistribution.smulLeftCLM F (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) T) +
        I • quantizeTempered F (frequencyDeriv j a) (ha.frequencyDeriv j) T := by
  ext φ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, quantizeTempered_apply_apply,
    transposeUniformCLM_smulLeftCLM, map_add, map_smul, add_apply, smul_apply]

/-- **Composition of quantizations on tempered distributions.** For a symbol `b` with compact
spatial support, `Op(a # b) = Op(a) ∘ Op(b)` on `𝓢'(ℝⁿ, F)`. -/
theorem quantizeTempered_sharp {a : Symbol n ℂ ℂ m'} {b : Symbol n ℂ ℂ m} (ha : a.IsUniform)
    (hb : b.HasCompactSpatialSupport) :
    quantizeTempered F (a.sharp b hb) (ha.sharp hb) =
      quantizeTempered F a ha ∘L quantizeTempered F b hb.isUniform := by
  ext T φ
  simp only [quantizeTempered_apply_apply, transposeUniformCLM_sharp ha hb,
    ContinuousLinearMap.comp_apply]

end Tempered

/-! ### Comparison with the Sobolev mappings -/

section Sobolev

/-- **Sobolev realizations are restrictions of the tempered one.** Any bounded operator
`T : H^s(ℝⁿ) → H^r(ℝⁿ)` that agrees with `Op(a)` on Schwartz functions is the restriction of
`Op(a) : 𝓢'(ℝⁿ, ℂ) → 𝓢'(ℝⁿ, ℂ)` to `H^s`: `T f = Op(a) f` as tempered distributions. This
applies to `TauCeti.Symbol.quantizeSobolev` (`TauCeti.Symbol.toDistr_quantizeSobolev`) and to the
Sobolev mappings of uniform symbols. -/
theorem toDistr_eq_quantizeTempered {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) {s r : ℝ}
    {T : H^{s}(CoordinateSpace n) →L[ℂ] H^{r}(CoordinateSpace n)}
    (hT : ∀ u φ : 𝓢(CoordinateSpace n, ℂ),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue a.coefficient u x)
    (f : H^{s}(CoordinateSpace n)) :
    (T f).toDistr = quantizeTempered ℂ a ha f.toDistr := by
  have key : BesselPotentialSpace.toDistrCLM _ ℂ r 2 ∘L T =
      quantizeTempered ℂ a ha ∘L BesselPotentialSpace.toDistrCLM _ ℂ s 2 := by
    refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
    ext φ
    simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistrCLM_apply, hT,
      quantizeTempered_apply_apply, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      SchwartzMap.coe_apply, smul_eq_mul, ← integral_mul_quantizeUniformCLM,
      quantizeUniformCLM_apply]
  simpa using congr($key f)

/-- For a symbol with compact spatial support, `Op(a) : H^s → H^{s - m}`
(`TauCeti.Symbol.quantizeSobolev`) is the restriction of `Op(a)` on tempered distributions. -/
theorem toDistr_quantizeSobolev {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport) (s : ℝ)
    (f : H^{s}(CoordinateSpace n)) :
    (a.quantizeSobolev ha s f).toDistr = quantizeTempered ℂ a ha.isUniform f.toDistr :=
  toDistr_eq_quantizeTempered ha.isUniform
    (toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply ha s) f

/-- **Sobolev mapping on tempered distributions.** For a symbol `a` of order `m` with compact
spatial support, `Op(a)` maps every tempered distribution of Sobolev order `s` to one of Sobolev
order `s - m`. -/
theorem memSobolev_quantizeTempered {a : Symbol n ℂ ℂ m} (ha : a.HasCompactSpatialSupport)
    {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)} (hT : T.MemSobolev s 2) :
    (quantizeTempered ℂ a ha.isUniform T).MemSobolev (s - m) 2 := by
  rw [← hT.toBesselPotentialSpace_toDistr, ← toDistr_quantizeSobolev ha s]
  exact BesselPotentialSpace.memSobolev_toDistr _

end Sobolev

/-! ### Smoothing operators on tempered distributions -/

section Smoothing

variable {r : Symbol n ℂ ℂ m}

/-- A smoothing symbol with compact spatial support maps every tempered distribution of some Sobolev
order `s` into every Sobolev space `H^t`. -/
private theorem IsSmoothing.memSobolev_quantizeTempered_of_memSobolev (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) {s : ℝ} {T : 𝓢'(CoordinateSpace n, ℂ)}
    (hT : T.MemSobolev s 2) (t : ℝ) : (quantizeTempered ℂ r hr.isUniform T).MemSobolev t 2 := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 hsm (s - t)
  have hbK := hr.of_coefficient_eq hb
  rw [quantizeTempered_congr hr.isUniform hbK.isUniform hb.symm]
  simpa using memSobolev_quantizeTempered hbK hT

/-- **Spatial cutoffs.** If `ψ = 1` at every position at which the symbol `r` does not vanish
identically, then `ψ Op(r) T = Op(r) T` for every tempered distribution `T`. -/
theorem smulLeftCLM_quantizeTempered_of_eq_one (hr : r.IsUniform)
    {ψ : 𝓢(CoordinateSpace n, ℂ)} (hψ : ∀ x ξ, r.coefficient (x, ξ) ≠ 0 → ψ x = 1)
    (T : 𝓢'(CoordinateSpace n, ℂ)) :
    TemperedDistribution.smulLeftCLM ℂ (ψ : CoordinateSpace n → ℂ) (quantizeTempered ℂ r hr T) =
      quantizeTempered ℂ r hr T := by
  -- `ψ Op(r) u = Op(r) u` pointwise, so `Op(r)ᵗ (ψ φ) = Op(r)ᵗ φ`.
  have hpt (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
      ψ x * quantizeUniformCLM r hr u x = quantizeUniformCLM r hr u x := by
    by_cases hx : ∀ ξ, r.coefficient (x, ξ) = 0
    · rw [quantizeUniformCLM_apply, quantizeSchwartzValue_congr_left (b := 0) hx u,
        quantizeSchwartzValue_zero_left, mul_zero]
    · obtain ⟨ξ, hξ⟩ := not_forall.1 hx
      rw [hψ x ξ hξ, one_mul]
  have key : transposeUniformCLM r hr ∘L SchwartzMap.smulLeftCLM ℂ (ψ : CoordinateSpace n → ℂ) =
      transposeUniformCLM r hr := by
    refine eq_transposeUniformCLM fun u φ ↦ ?_
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply, ← integral_mul_quantizeUniformCLM]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth, smul_eq_mul]
    rw [mul_comm (ψ x), mul_assoc, hpt]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, quantizeTempered_apply_apply,
    quantizeTempered_apply_apply, ← ContinuousLinearMap.comp_apply, key]

/-- The tempered distributions `U` such that `Op(r) U` lies in every Sobolev space `H^t` for every
smoothing symbol `r` with compact spatial support. -/
private def SmoothedBy (U : 𝓢'(CoordinateSpace n, ℂ)) : Prop :=
  ∀ (m : ℝ) (r : Symbol n ℂ ℂ m), r.IsSmoothing → ∀ (hr : r.HasCompactSpatialSupport) (t : ℝ),
    (quantizeTempered ℂ r hr.isUniform U).MemSobolev t 2

private theorem smoothedBy_of_memSobolev {U : 𝓢'(CoordinateSpace n, ℂ)} {s : ℝ}
    (hU : U.MemSobolev s 2) : SmoothedBy U :=
  fun _ _ hsm hr t ↦ hsm.memSobolev_quantizeTempered_of_memSobolev hr hU t

private theorem SmoothedBy.add {U V : 𝓢'(CoordinateSpace n, ℂ)} (hU : SmoothedBy U)
    (hV : SmoothedBy V) : SmoothedBy (U + V) := fun m r hsm hr t ↦ by
  rw [map_add]
  exact (hU m r hsm hr t).add (hV m r hsm hr t)

/-- Multiplying by a coordinate keeps the class: `Op(r) (y_j U) = y_j Op(r) U - i Op(∂_{ξ_j} r) U`,
and `y_j Op(r) U = (y_j ψ) Op(r) U` for a cutoff `ψ` equal to `1` on the spatial support of `r`. -/
private theorem SmoothedBy.smulLeftCLM_coord {U : 𝓢'(CoordinateSpace n, ℂ)} (hU : SmoothedBy U)
    (j : Fin n) :
    SmoothedBy (TemperedDistribution.smulLeftCLM ℂ
      (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) U) := fun m r hsm hr t ↦ by
  have hcoord : (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)).HasTemperateGrowth :=
    (ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth
  rw [eq_sub_of_add_eq (smulLeftCLM_quantizeTempered r hr.isUniform j U).symm]
  refine TemperedDistribution.MemSobolev.sub ?_
    ((hU _ _ (hsm.frequencyDeriv j) (hr.frequencyDeriv j) t).smul I)
  obtain ⟨K, hK, hKr⟩ := hasCompactSpatialSupport_iff.1 hr
  obtain ⟨ψ, -, -, hψ⟩ := hK.exists_schwartzMap_cutoff isOpen_univ (Set.subset_univ K)
  have hψ1 (x : CoordinateSpace n) (ξ : CoordinateSpace n) (hx : r.coefficient (x, ξ) ≠ 0) :
      ψ x = 1 := by
    by_contra hψx
    exact hx (hKr x (fun hxK ↦ hψx (hψ.self_of_nhdsSet x hxK)) ξ)
  rw [← smulLeftCLM_quantizeTempered_of_eq_one hr.isUniform hψ1,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth hcoord]
  have hχ : (ψ : CoordinateSpace n → ℂ) * (fun y ↦ ((y j : ℝ) : ℂ)) =
      ⇑(SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) ψ) := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hcoord, Pi.mul_apply, smul_eq_mul, mul_comm]
  rw [hχ]
  exact (hU m r hsm hr t).smulLeftCLM _

/-- Multiplying by `1 + ‖y‖ ^ 2 = 1 + ∑ⱼ y_j ^ 2` keeps the class. -/
private theorem SmoothedBy.smulLeftCLM_one_add_norm_sq {U : 𝓢'(CoordinateSpace n, ℂ)}
    (hU : SmoothedBy U) :
    SmoothedBy (TemperedDistribution.smulLeftCLM ℂ
      (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) U) := by
  set c : Fin n → CoordinateSpace n → ℂ := fun j y ↦ ((y j : ℝ) : ℂ)
  have hc (j : Fin n) : (c j).HasTemperateGrowth :=
    (ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth
  have hp : (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hid : TemperedDistribution.smulLeftCLM ℂ
      (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) U =
        U + ∑ j, TemperedDistribution.smulLeftCLM ℂ (c j)
          (TemperedDistribution.smulLeftCLM ℂ (c j) U) := by
    have hφ (φ : 𝓢(CoordinateSpace n, ℂ)) :
        SchwartzMap.smulLeftCLM ℂ (fun y : CoordinateSpace n ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) φ =
          φ + ∑ j, SchwartzMap.smulLeftCLM ℂ (c j) (SchwartzMap.smulLeftCLM ℂ (c j) φ) := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply hp]
      simp only [add_apply, sum_apply, SchwartzMap.smulLeftCLM_apply_apply (hc _), c, smul_eq_mul,
        EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
      push_cast
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    ext φ
    rw [TemperedDistribution.smulLeftCLM_apply_apply, hφ, map_add, map_sum]
    simp [TemperedDistribution.smulLeftCLM_apply_apply]
  rw [hid]
  refine hU.add ?_
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact smoothedBy_of_memSobolev (s := 0) (TemperedDistribution.memSobolev_fun_zero _ _ 0 2)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact SmoothedBy.add ((hU.smulLeftCLM_coord j).smulLeftCLM_coord j) ih

/-- **Smoothing operators on tempered distributions.** A smoothing symbol `r` with compact spatial
support maps every tempered distribution `T`, of any order and growth, into every Sobolev space
`H^t`. -/
theorem IsSmoothing.memSobolev_quantizeTempered (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) (T : 𝓢'(CoordinateSpace n, ℂ)) (t : ℝ) :
    (quantizeTempered ℂ r hr.isUniform T).MemSobolev t 2 := by
  obtain ⟨K, s, S, hS, rfl⟩ :=
    TemperedDistribution.exists_memSobolev_eq_smulLeftCLM_one_add_norm_sq_pow T
  set p : CoordinateSpace n → ℂ := fun y ↦ ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)
  have hp : p.HasTemperateGrowth := by fun_prop
  -- Each factor `1 + ‖y‖ ^ 2` keeps the class.
  have hpow (k : ℕ) (U : 𝓢'(CoordinateSpace n, ℂ)) (hU : SmoothedBy U) :
      SmoothedBy (TemperedDistribution.smulLeftCLM ℂ (p ^ k) U) := by
    induction k generalizing U with
    | zero =>
      rw [show p ^ 0 = fun _ ↦ (1 : ℂ) from funext fun _ ↦ by simp,
        TemperedDistribution.smulLeftCLM_const, one_smul]
      exact hU
    | succ k ih =>
      rw [pow_succ, ← TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (hp.pow k) hp]
      exact (ih U hU).smulLeftCLM_one_add_norm_sq
  have hpK : p ^ K = fun y : CoordinateSpace n ↦ (((1 + ‖y‖ ^ 2) ^ K : ℝ) : ℂ) :=
    funext fun y ↦ by simp [p]
  exact hpK ▸ hpow K S (smoothedBy_of_memSobolev hS) m r hsm hr t

open scoped ContDiff in
/-- **Smoothing operators produce smooth functions.** For a smoothing symbol `r` with compact
spatial support and every tempered distribution `T`, the tempered distribution `Op(r) T` is a
smooth function `g`. -/
theorem IsSmoothing.exists_contDiff_quantizeTempered_apply_eq_integral (hsm : r.IsSmoothing)
    (hr : r.HasCompactSpatialSupport) (T : 𝓢'(CoordinateSpace n, ℂ)) :
    ∃ g : CoordinateSpace n → ℂ, ContDiff ℝ ∞ g ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), quantizeTempered ℂ r hr.isUniform T φ = ∫ x, φ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev
    (hsm.memSobolev_quantizeTempered hr T)

end Smoothing

end Symbol

end TauCeti
