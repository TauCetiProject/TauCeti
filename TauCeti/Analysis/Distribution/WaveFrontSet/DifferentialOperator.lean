/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import TauCeti.Analysis.Distribution.WaveFrontSet.EllipticRegularity
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
import TauCeti.Algebra.BigOperators.Pi
import TauCeti.Analysis.Distribution.LineDeriv
import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Basic

/-!
# Differential operators on `C^∞(E)` and wave front sets

Let `E` be a finite-dimensional real inner product space and `D` a differential operator of order
at most `m` on the smooth functions on `E`, in Grothendieck's sense of iterated commutators with
multiplication operators (`TauCeti.differentialOperators`). For a distribution `S` on an open set
`Ω ⊆ E`, the functional `φ ↦ S (D φ)` on test functions on `Ω` is again a distribution, and it is
microlocally smooth wherever `S` is
(`Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`).
In coordinates `D = ∑_{|α| ≤ m} c_α ∂^α` (`Module.Basis.eq_coordinateOperator_coordinateCoeff`), so
`φ ↦ S (D φ)` is built from `S` by multiplications by the smooth coefficients `c_α` and
differentiations, neither of which enlarges wave front sets.

Conversely, `S` is as regular as `φ ↦ S (D φ)` at the covectors where `D` is elliptic. If the
principal symbol `σ(D)(x, ⟪ξ, ·⟫)` (`TauCeti.smoothPrincipalSymbol`, defined by iterated
commutators) does not vanish and `φ ↦ S (D φ)` is microlocally smooth at `(x, ξ)`, then so is `S`
(`Distribution.IsMicrolocallySmoothAt.of_mem_differentialOperators`), and
`WF(S) ⊆ WF(φ ↦ S (D φ)) ∪ Char(D)`
(`Distribution.waveFrontSet_subset_waveFrontSet_union_of_mem_differentialOperators`). The
functional `φ ↦ S (D φ)` is `Dᵗ S` for the formal transpose `Dᵗ` of `D`, which is again a
differential operator of order at most `m`
(`LinearMap.exists_isFormalTranspose_of_mem_differentialOperators`) with principal symbol
`(-1) ^ m σ(D)` (`LinearMap.IsFormalTranspose.smoothPrincipalSymbol_eq`). Writing
`Dᵗ = ∑_{|α| ≤ m} d_α ∂^α` in coordinates, the formal transpose of this expression is
`φ ↦ ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (d_α φ)` (`LinearMap.isFormalTranspose_coordinateOperator`), which
is `D` by uniqueness of formal transposes. So `φ ↦ S (D φ)` is the distribution
`∑_{|α| ≤ m} d_α ∂^α S`, with principal symbol `(-1) ^ m σ(D)`
(`Distribution.exists_eq_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_mem_differentialOperators`),
to which microlocal elliptic regularity for operators with smooth coefficients applies
(`Distribution.IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`).

## Main results

* `Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`:
  a differential operator on `C^∞(E)` acts on distributions by transposition without enlarging
  their wave front sets.
* `Distribution.exists_eq_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_mem_differentialOperators`:
  this action in coordinates, as an operator `∑ i, g i ∂^(v i)` with smooth coefficients whose
  principal symbol is `(-1) ^ m σ(D)`.
* `Distribution.IsMicrolocallySmoothAt.of_mem_differentialOperators`,
  `Distribution.waveFrontSet_subset_waveFrontSet_union_of_mem_differentialOperators`: microlocal
  elliptic regularity for this action.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (differential operators with smooth coefficients do not enlarge wave front
  sets) and Theorem 8.3.1 (microlocal elliptic regularity).
-/

public section

noncomputable section

open Set Function TopologicalSpace LineDeriv
open scoped ContDiff Manifold Distributions Topology RealInnerProductSpace

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-- The operator `D` on `C^∞(E)` does not enlarge supports and acts on the distributions on `Ω`
by transposition without enlarging their wave front sets: every `S` has a transpose `R` with
`R φ = S (D φ)` for every test function `φ`, microlocally smooth wherever `S` is. -/
private def HasMicrolocalTranspose (Ω : Opens E)
    (D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : Prop :=
  (∀ f, tsupport (D f) ⊆ tsupport f) ∧
    ∀ S : 𝓓'(Ω, ℂ), ∃ R : 𝓓'(Ω, ℂ),
      (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ) ∧
        ∀ x ξ, S.IsMicrolocallySmoothAt x ξ → R.IsMicrolocallySmoothAt x ξ

namespace HasMicrolocalTranspose

private theorem id : HasMicrolocalTranspose Ω LinearMap.id :=
  ⟨fun _ ↦ subset_rfl, fun S ↦ ⟨S, fun φ ψ f hf hψ ↦ by
    rw [show ψ = φ from TestFunction.ext fun x ↦ by simp [hψ, ← hf]], fun _ _ h ↦ h⟩⟩

private theorem zero : HasMicrolocalTranspose Ω 0 :=
  ⟨fun _ ↦ by simp, fun S ↦ ⟨(0 : ℂ) • S, fun φ ψ f _ hψ ↦ by
    rw [show ψ = 0 from TestFunction.ext fun x ↦ by simp [hψ]]; simp,
    fun _ _ hS ↦ hS.smul 0⟩⟩

private theorem comp {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h₁ : HasMicrolocalTranspose Ω D₁) (h₂ : HasMicrolocalTranspose Ω D₂) :
    HasMicrolocalTranspose Ω (D₁ ∘ₗ D₂) := by
  refine ⟨fun f ↦ (h₁.1 _).trans (h₂.1 f), fun S ↦ ?_⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := h₁.2 S
  obtain ⟨R, hR, hR'⟩ := h₂.2 R₁
  refine ⟨R, fun φ ψ f hf hψ ↦ ?_, fun x ξ hS ↦ hR' x ξ (hR₁' x ξ hS)⟩
  -- The intermediate test function `D₂ φ`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₂ f).contMDiff) (hf ▸ h₂.1 f)
  rw [hR φ χ f hf hχ, hR₁ χ ψ (D₂ f) hχ.symm hψ]

variable [FiniteDimensional ℝ E]

private theorem add {D₁ D₂ : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h₁ : HasMicrolocalTranspose Ω D₁) (h₂ : HasMicrolocalTranspose Ω D₂) :
    HasMicrolocalTranspose Ω (D₁ + D₂) := by
  refine ⟨fun f ↦ (tsupport_add _ _).trans (union_subset (h₁.1 f) (h₂.1 f)), fun S ↦ ?_⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := h₁.2 S
  obtain ⟨R₂, hR₂, hR₂'⟩ := h₂.2 S
  refine ⟨R₁ + R₂, fun φ ψ f hf hψ ↦ ?_, fun x ξ hS ↦ (hR₁' x ξ hS).add (hR₂' x ξ hS)⟩
  obtain ⟨ψ₁, hψ₁⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₁ f).contMDiff) (hf ▸ h₁.1 f)
  obtain ⟨ψ₂, hψ₂⟩ := TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D₂ f).contMDiff) (hf ▸ h₂.1 f)
  have hψ' : ψ = ψ₁ + ψ₂ := TestFunction.ext fun x ↦ by simp [hψ, hψ₁, hψ₂]
  simp [hR₁ φ ψ₁ f hf hψ₁, hR₂ φ ψ₂ f hf hψ₂, hψ']

private theorem sum {ι : Type*} (s : Finset ι)
    {D : ι → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯}
    (h : ∀ i ∈ s, HasMicrolocalTranspose Ω (D i)) :
    HasMicrolocalTranspose Ω (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add (h i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private theorem mulLeft (c : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    HasMicrolocalTranspose Ω (LinearMap.mulLeft ℝ c) := by
  have hc : ContDiff ℝ ∞ c := contMDiff_iff_contDiff.1 c.contMDiff
  refine ⟨fun f ↦ tsupport_mul_subset_right, fun S ↦
    ⟨smulLeftCLM hc S, fun φ ψ f hf hψ ↦ ?_, fun _ _ hS ↦ hS.smulLeftCLM hc⟩⟩
  rw [smulLeftCLM_apply, show TestFunction.smulLeftCLM hc φ = ψ from
    TestFunction.ext fun x ↦ by simp [hψ, ← hf]]

private theorem lineDerivation (v : E) :
    HasMicrolocalTranspose Ω (TauCeti.lineDerivation ℝ v : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] _) := by
  refine ⟨fun f ↦ TauCeti.tsupport_lineDerivation_apply_subset v f, fun S ↦
    ⟨∂_{v} ((-1 : ℂ) • S), fun φ ψ f hf hψ ↦ ?_, fun _ _ hS ↦ (hS.smul (-1)).lineDerivOp v⟩⟩
  rw [lineDerivOp_apply_apply, show ψ = ∂_{v} φ from TestFunction.ext fun x ↦ by
    rw [hψ, TestFunction.lineDerivOp_apply_eq_fderiv, ← hf]
    exact TauCeti.lineDerivation_apply_apply v f x]
  simp

private theorem multiIndexDeriv {ι : Type*} [Fintype ι] (v : ι → E) (α : ι → ℕ) :
    HasMicrolocalTranspose Ω (TauCeti.multiIndexDeriv (fun i ↦ TauCeti.lineDerivation ℝ (v i))
      (fun i j ↦ TauCeti.commute_lineDerivation (v i) (v j)) α) := by
  classical
  induction α using TauCeti.multiIndex_induction_add_single with
  | zero => simpa [Module.End.one_eq_id] using id
  | add_single α i ih =>
    rw [TauCeti.multiIndexDeriv_add_single, Module.End.mul_eq_comp]
    exact ih.comp (lineDerivation (v i))

private theorem coordinateOperator {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (m : ℕ)
    (c : (ι → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    HasMicrolocalTranspose Ω (TauCeti.coordinateOperator
      (fun i ↦ TauCeti.lineDerivation ℝ (v i))
      (fun i j ↦ TauCeti.commute_lineDerivation (v i) (v j)) m c) := by
  rw [TauCeti.coordinateOperator_eq_sum_mulLeft]
  exact sum _ fun k _ ↦ sum _ fun α _ ↦ (mulLeft (c α)).comp (multiIndexDeriv v α)

end HasMicrolocalTranspose

variable [FiniteDimensional ℝ E]

/-- **Differential operators act on distributions without enlarging wave front sets.** Let `D` be
a differential operator of order at most `m` on the smooth functions on `E`, in Grothendieck's
sense of iterated commutators with multiplication operators. For every distribution `S` on an open
set `Ω`, the functional `φ ↦ S (D φ)` on test functions on `Ω` is a distribution `R`, and `R` is
microlocally smooth at every point and direction at which `S` is. -/
theorem exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    (S : 𝓓'(Ω, ℂ)) :
    ∃ R : 𝓓'(Ω, ℂ), (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f →
      R φ = S ψ) ∧ ∀ x ξ, S.IsMicrolocallySmoothAt x ξ → R.IsMicrolocallySmoothAt x ξ := by
  classical
  have hD' := (Module.finBasis ℝ E).eq_coordinateOperator_coordinateCoeff hD
  exact (hD' ▸ HasMicrolocalTranspose.coordinateOperator _ m _).2 S

/-! ### Microlocal elliptic regularity -/

/-- The multi-indices `α : Fin n → ℕ` of order `|α| ≤ m`, each tagged with its order. -/
private def multiIndicesLE (n m : ℕ) : Finset (Σ _ : ℕ, Fin n → ℕ) :=
  (Finset.range (m + 1)).sigma fun k ↦ Finset.piAntidiag Finset.univ k

omit [FiniteDimensional ℝ E] in
/-- The transpose of a distribution `S` by the operator `φ ↦ ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (d_α φ)`,
for smooth coefficients `d_α` and derivatives `∂^α` along directions `b`, is the distribution
`∑_{|α| ≤ m} d_α ∂^α S`: the derivatives of `S` are taken along the reversed word of directions of
each multi-index, which gives the same distribution as the derivatives commute. -/
private theorem exists_apply_eq_sum_smulLeftCLM_iteratedLineDerivOp {n : ℕ} (b : Fin n → E)
    (m : ℕ) (d : (Fin n → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (S : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℝ))
    {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : ⇑f = φ) :
    ∃ ψ : 𝓓(Ω, ℝ), ⇑ψ = (∑ k ∈ Finset.range (m + 1), ∑ α ∈ Finset.piAntidiag Finset.univ k,
        (-1 : ℝ) ^ k • (TauCeti.multiIndexDeriv (fun i ↦ TauCeti.lineDerivation ℝ (b i))
          (fun i j ↦ TauCeti.commute_lineDerivation (b i) (b j)) α ∘ₗ
            LinearMap.mulLeft ℝ (d α))) f ∧
      S ψ = (∑ i ∈ multiIndicesLE n m,
        (1 : ℂ) • smulLeftCLM (contMDiff_iff_contDiff.1 (d i.2).contMDiff)
          (∂^{b ∘ TauCeti.multiIndexWord i.2 ∘ Fin.rev} S)) φ := by
  refine ⟨∑ i ∈ multiIndicesLE n m, (-1 : ℝ) ^ (∑ j, i.2 j) • ∂^{b ∘ TauCeti.multiIndexWord i.2}
      (TestFunction.smulLeftCLM (contMDiff_iff_contDiff.1 (d i.2).contMDiff) φ), ?_, ?_⟩
  · ext y
    simp only [multiIndicesLE, Finset.sum_sigma, _root_.sum_apply, LinearMap.coe_sum,
      Finset.sum_apply, ContMDiffMap.coe_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun α hα ↦ ?_
    rw [← (Finset.mem_piAntidiag.1 hα).1]
    -- Both sides are `(-1) ^ |α|` times `D^{|α|} (d_α φ) (y)` evaluated on the word of `α`; the
    -- product `d_α φ` appears as `•` on one side and `*` on the other, and `smul_eq_mul` with
    -- `Pi.mul_def` brings both to the same pointwise product.
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      ContMDiffMap.coe_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      TestFunction.iteratedLineDerivOp_apply_eq_iteratedFDeriv,
      TauCeti.multiIndexDeriv_apply_eq_iteratedFDeriv_multiIndexWord,
      TestFunction.coe_smulLeftCLM, ContMDiffMap.coe_mul, hf, Pi.mul_def]
  · simp only [map_sum, map_smul, _root_.sum_apply, one_smul, smulLeftCLM_apply,
      iteratedLineDerivOp_apply_apply, Function.comp_assoc, Fin.rev_involutive.comp_self,
      Function.comp_id]

omit [FiniteDimensional ℝ E] in
/-- The principal symbol of order `m` of `∑_{|α| ≤ m} d_α ∂^α`, with derivatives along the
reversed words of the multi-indices in the directions of a basis `b`, is
`ξ ↦ ∑_{|α| = m} d_α(x) ∏ᵢ ⟪ξ, bᵢ⟫ ^ αᵢ`. -/
private theorem principalSymbol_multiIndexWord {n : ℕ} (b : Fin n → E) (m : ℕ)
    (d : (Fin n → ℕ) → C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (x ξ : E) :
    TauCeti.principalSymbol (multiIndicesLE n m) (fun i y ↦ 1 * (d i.2 y : ℂ))
        (fun i ↦ b ∘ TauCeti.multiIndexWord i.2 ∘ Fin.rev) m x ξ =
      ((∑ α ∈ Finset.piAntidiag Finset.univ m, d α x * ∏ i, ⟪ξ, b i⟫ ^ α i : ℝ) : ℂ) := by
  rw [TauCeti.principalSymbol_def, TauCeti.constCoeffPrincipalSymbol_def, multiIndicesLE,
    Finset.sum_filter, Finset.sum_sigma, Finset.sum_eq_single m]
  · push_cast
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    simp only [(Finset.mem_piAntidiag.1 hα).1, ↓reduceIte, one_mul]
    congr 1
    rw [Fintype.prod_equiv Fin.revPerm _ (fun l ↦ ((⟪ξ, b (TauCeti.multiIndexWord α l)⟫ : ℝ) : ℂ))
      fun l ↦ by simp [real_inner_comm]]
    exact TauCeti.prod_multiIndexWord α fun i ↦ ((⟪ξ, b i⟫ : ℝ) : ℂ)
  · intro k _ hk
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    simp [(Finset.mem_piAntidiag.1 hα).1, hk]
  · exact fun h ↦ absurd (Finset.mem_range.2 (Nat.lt_succ_self m)) h

/-- **A differential operator acting on distributions, in coordinates.** Let `D` be a differential
operator of order at most `m` on the smooth functions on `E`, in Grothendieck's sense. There is an
expression `∑ i ∈ t, g i ∂^(v i)`, with smooth real coefficients `g i` and words of directions
`v i` of lengths `k i ≤ m`, such that for every distribution `S` on an open set `Ω`, the transpose
`R : φ ↦ S (D φ)` is the distribution `∑ i ∈ t, g i ∂^(v i) S`, and the principal symbol of order
`m` of this expression is `(-1) ^ m` times that of `D`. This turns statements about operators
`∑ i ∈ t, c i g i ∂^(v i)` into statements about the transposes of differential operators. -/
theorem exists_eq_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m) :
    ∃ (ι : Type) (t : Finset ι) (k : ι → ℕ) (v : ∀ i, Fin (k i) → E) (g : ι → E → ℝ)
      (hg : ∀ i, ContDiff ℝ ∞ (g i)), (∀ i ∈ t, k i ≤ m) ∧
      (∀ x ξ : E, TauCeti.principalSymbol t (fun i y ↦ 1 * (g i y : ℂ)) v m x ξ =
        (((-1) ^ m * TauCeti.smoothPrincipalSymbol 𝓘(ℝ, E) (x := x)
          BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ (innerSL ℝ ξ : E →L[ℝ] ℝ) : ℝ) : ℂ)) ∧
      ∀ (Ω : Opens E) (S R : 𝓓'(Ω, ℂ)),
        (∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ) →
        R = ∑ i ∈ t, (1 : ℂ) • smulLeftCLM (hg i) (∂^{v i} S) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  -- The formal transpose `D'` of `D` for a Haar measure, in coordinates `∑_{|α| ≤ m} d_α ∂^α`.
  obtain ⟨D', hD', hT⟩ := LinearMap.exists_isFormalTranspose_of_mem_differentialOperators hD
  let μ : MeasureTheory.Measure E := MeasureTheory.Measure.addHaar
  let b := Module.finBasis ℝ E
  let d := TauCeti.coordinateCoeff b.smoothCoord D'
  have hG := LinearMap.isFormalTranspose_coordinateOperator (μ := μ) b m d
  rw [← b.eq_coordinateOperator_coordinateCoeff hD'] at hG
  -- By uniqueness of formal transposes, `D φ = ∑_{|α| ≤ m} (-1) ^ |α| ∂^α (d_α φ)`.
  have hDG := (hT μ).symm.unique hG
  refine ⟨_, multiIndicesLE _ m, fun i ↦ ∑ j, i.2 j,
    fun i ↦ b ∘ TauCeti.multiIndexWord i.2 ∘ Fin.rev, fun i ↦ d i.2,
    fun i ↦ contMDiff_iff_contDiff.1 (d i.2).contMDiff, fun i hi ↦ ?_,
    fun x ξ ↦ ?_, fun Ω S R hR ↦ ?_⟩
  · have hi' : i.1 ≤ m ∧ ∑ j, i.2 j = i.1 := by simpa [multiIndicesLE, Nat.lt_succ_iff] using hi
    exact hi'.2.le.trans hi'.1
  · -- The principal symbol of `∑_{|α| ≤ m} d_α ∂^α` is `σ(D') = (-1) ^ m σ(D)`.
    have h₁ :=
      b.smoothPrincipalSymbol_eq_sum_coordinateCoeff ⟨D', hD'⟩ x (innerSL ℝ ξ : E →L[ℝ] ℝ)
    have h₂ := LinearMap.IsFormalTranspose.smoothPrincipalSymbol_eq (D := ⟨D, hD⟩)
      (D' := ⟨D', hD'⟩) (hT μ) (x := x) (innerSL ℝ ξ : E →L[ℝ] ℝ)
    rw [principalSymbol_multiIndexWord]
    exact congrArg _ (h₁.symm.trans h₂)
  · ext φ
    obtain ⟨ψ, hψ, hSψ⟩ := exists_apply_eq_sum_smulLeftCLM_iteratedLineDerivOp b m d S φ
      (f := ⟨φ, contMDiff_iff_contDiff.2 φ.contDiff⟩) rfl
    rw [hR φ ψ _ rfl (hDG ▸ hψ), hSψ]

/-- **Microlocal elliptic regularity for differential operators on `C^∞(E)`** (Hörmander I,
Theorem 8.3.1). Let `D` be a differential operator of order at most `m` on the smooth functions on
`E`, in Grothendieck's sense, and let `ξ` be noncharacteristic for `D` at `x`: its principal symbol
`σ(D)(x, ⟪ξ, ·⟫)` does not vanish. If `R` is the transpose `φ ↦ S (D φ)` of a distribution `S` on
`Ω`, and `R` is microlocally smooth at `(x, ξ)`, then so is `S`. -/
theorem IsMicrolocallySmoothAt.of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    {S R : 𝓓'(Ω, ℂ)}
    (hR : ∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ)
    {x ξ : E} (hξ : TauCeti.smoothPrincipalSymbol 𝓘(ℝ, E) (x := x)
      BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ (innerSL ℝ ξ : E →L[ℝ] ℝ) ≠ 0)
    (h : R.IsMicrolocallySmoothAt x ξ) : S.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨_, t, _, _, _, hg, hk, hσ, hRS⟩ :=
    exists_eq_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_mem_differentialOperators hD
  refine IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk
    (hRS Ω S R hR ▸ h) ?_
  rw [hσ]
  exact Complex.ofReal_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hξ)

/-- **Microlocal elliptic regularity for differential operators on `C^∞(E)`**: if `R` is the
transpose `φ ↦ S (D φ)` of a distribution `S` on `Ω` by a differential operator `D` of order at
most `m`, then `WF(S) ⊆ WF(R) ∪ Char(D)`, where `Char(D)` is the set of `(x, ξ)` at which the
principal symbol `σ(D)(x, ⟪ξ, ·⟫)` vanishes. -/
theorem waveFrontSet_subset_waveFrontSet_union_of_mem_differentialOperators
    {D : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯} {m : ℕ}
    (hD : D ∈ TauCeti.differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m)
    {S R : 𝓓'(Ω, ℂ)}
    (hR : ∀ (φ ψ : 𝓓(Ω, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ → ⇑ψ = D f → R φ = S ψ) :
    S.waveFrontSet ⊆ R.waveFrontSet ∪ {p | TauCeti.smoothPrincipalSymbol 𝓘(ℝ, E) (x := p.1)
      BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ (innerSL ℝ p.2 : E →L[ℝ] ℝ) = 0} := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hS⟩ := mem_waveFrontSet_iff.1 hp
  refine or_iff_not_imp_right.2 fun hσ ↦ mem_waveFrontSet_iff.2 ⟨hx, hξ, fun h ↦ hS ?_⟩
  exact IsMicrolocallySmoothAt.of_mem_differentialOperators hD hR hσ h

end Distribution
