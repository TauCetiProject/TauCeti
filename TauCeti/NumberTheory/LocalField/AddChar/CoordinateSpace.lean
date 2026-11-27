/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.TraceForm
public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
public import TauCeti.NumberTheory.LocalField.AddChar.SelfDualMeasure
import TauCeti.LinearAlgebra.Matrix.Dual
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.Order.Filter.Pi
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Instances.Matrix

/-!
# Self-dual product measures for the dot product and the trace form

For a nonarchimedean local field `K` and a nontrivial continuous additive character `ψ`, take
the product of the one-dimensional measure `ψ.selfDualMeasure` over the coordinates of a vector
or the entries of a matrix. Fourier transform for this explicit measure squares to reflection
on locally constant compactly supported functions, both for the dot product and for the trace
pairing `(X, Y) ↦ trace (X * Y)`. Mathlib’s `VectorFourier.fourierIntegral` uses the negative
kernel. Applying the inversion theorems to `ψ⁻¹` gives the positive kernel with the same
measure by `AddChar.inv_apply` and `AddChar.selfDualMeasure_inv`.

Writing `q` for the residue cardinality and `ν` for the conductor exponent, the integral vectors
have volume `q^(-nν/2)` and the integral square matrices have volume `q^(-n²ν/2)`. These are the
normalizations of the test functions in the equal-rank Rankin–Selberg and Godement–Jacquet
integrals. The same product volume calculation applies to rectangular matrices.
-/

public section

open MeasureTheory Measure Filter Topology ValuativeRel TauCeti Function Set LocallyConstant
open scoped ENNReal

namespace AddChar

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

section Volume

variable {M : Type*} [Monoid M] (ψ : AddChar K M)

/-- The product of the scalar self-dual measures gives the integral vectors in `Kⁿ`
volume `q^(-nν/2)`. -/
@[simp]
theorem pi_selfDualMeasure_integerBox (ι : Type*) [Fintype ι] :
    (Measure.pi fun _ : ι ↦ ψ.selfDualMeasure) (integerBox K ι) =
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ (-(Fintype.card ι : ℝ) * ψ.conductorExponent / 2) := by
  rw [integerBox_def, Measure.pi_pi]
  simp only [selfDualMeasure_integer, Finset.prod_const, Finset.card_univ, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  congr 1
  ring

/-- With the product measure on the entries, the integral `r × s` matrices have volume
`q^(-rsν/2)`. In particular the exponent for square matrices involves the square of their size. -/
@[simp]
theorem map_pi_selfDualMeasure_matrix_integer (r s : Type*) [Fintype r] [Fintype s] :
    let μ := Measure.pi fun _ : r ↦ Measure.pi fun _ : s ↦ ψ.selfDualMeasure
    μ.map (Matrix.ofMeasurableEquiv r s K) (𝒪[K] : Set K).matrix =
      (Nat.card 𝓀[K] : ℝ≥0∞) ^
        (-(Fintype.card r : ℝ) * Fintype.card s * ψ.conductorExponent / 2) := by
  let : MeasureSpace K := { volume := ψ.selfDualMeasure }
  have : (volume : Measure K).IsAddHaarMeasure := ψ.isAddHaarMeasure_selfDualMeasure
  have h𝒪 : volume (𝒪[K] : Set K) = _ := ψ.selfDualMeasure_integer
  have hμ : (Measure.pi fun _ : r ↦ Measure.pi fun _ : s ↦ ψ.selfDualMeasure).map
      (Matrix.ofMeasurableEquiv r s K) = volume :=
    (Matrix.volume_preserving_ofMeasurableEquiv r s K).map_eq
  dsimp only
  rw [hμ, Set.volume_matrix, h𝒪, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

end Volume

variable {ψ : AddChar K Circle} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- In both coordinate models the conductor takes the box of level `m` to the box of level
`-ν-m`, and the box volume is the scalar volume raised to the number of entries. -/
private theorem inversion_of_coordinate_boxes
    {V : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddLeftInvariant]
    (B : LinearMap.BilinForm K V) (hB : LinearMap.flip B = B)
    (hcont : Continuous fun p : V × V ↦ B p.1 p.2) (hψ : Continuous ψ)
    (U : ℤ → AddSubgroup V) (hbasis : (𝓝 0).HasBasis (fun _ : ℤ ↦ True) (fun m ↦ (U m : Set V)))
    (hdual : ∀ m, (U m).characterAnnihilator ψ B = U (-ψ.conductorExponent - m))
    (d : ℕ) (hvol : ∀ m, μ (U m) =
      ψ.selfDualMeasure {x | valuation K x ≤ uniformizer K ^ m} ^ d)
    (f : compactlySupported ℂ V E) (x : V) :
    VectorFourier.fourierIntegral ψ μ B
      (VectorFourier.fourierIntegral ψ μ B ⇑(f : LocallyConstant V E)) x =
        (f : LocallyConstant V E) (-x) := by
  have hf := (f : LocallyConstant V E).isLocallyConstant
  have hfc := mem_compactlySupported.mp f.property
  obtain ⟨m, -, hm⟩ := hbasis.mem_iff.mp
    ((isOpen_addRightTranslationStabilizer_of_hasCompactSupport hf hfc).mem_nhds
      (zero_mem (addRightTranslationStabilizer (f : LocallyConstant V E))))
  have hopen (k : ℤ) : IsOpen (U k : Set V) :=
    (U k).isOpen_of_mem_nhds (hbasis.mem_of_mem (i := k) trivial)
  have : IsLocallyFiniteMeasure μ := by
    apply isLocallyFiniteMeasure_of_vaddInvariant V (hopen 0) ⟨0, (U 0).zero_mem⟩
    rw [hvol]
    exact ENNReal.pow_ne_top (isCompact_leAddSubgroup K _).measure_ne_top
  have hprod : μ.real (U m) * μ.real (U (-ψ.conductorExponent - m)) = 1 := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_mul, hvol, hvol, ← mul_pow,
      selfDualMeasure_mul_selfDualMeasure, one_pow, ENNReal.toReal_one]
  simpa only [hB, LocallyConstant.toFun_eq_coe] using
    VectorFourier.fourierIntegral_fourierIntegral_of_periodic ψ μ B μ hψ hcont
      (hopen m).measurableSet (hdual m ▸ (hopen _).measurableSet)
      (by rw [hB, hdual, hdual, sub_sub_cancel])
      (hdual m ▸ hprod) (hf.continuous.integrable_of_hasCompactSupport hfc)
      (fun u hu ↦ mem_addRightTranslationStabilizer.mp (hm hu)) x

/-- Fourier inversion for the dot product on `Kⁿ` with the product of the scalar self-dual
measures. -/
theorem fourierIntegral_fourierIntegral_dotProductBilin {ι : Type*} [Fintype ι]
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (f : compactlySupported ℂ (ι → K) E) (x : ι → K) :
    let μ := Measure.pi fun _ : ι ↦ ψ.selfDualMeasure
    VectorFourier.fourierIntegral ψ μ (dotProductBilin K K)
      (VectorFourier.fourierIntegral ψ μ (dotProductBilin K K) ⇑(f : LocallyConstant (ι → K) E)) x =
        (f : LocallyConstant (ι → K) E) (-x) := by
  let U (m : ℤ) := (valuation K).leAddSubgroup (uniformizer K ^ m)
  refine inversion_of_coordinate_boxes _ _ (LinearMap.BilinForm.isSymm_iff_flip.mp
    isSymm_dotProductBilin) (continuous_fst.dotProduct continuous_snd) hψ
    (fun m ↦ AddSubgroup.pi univ fun _ ↦ U m) ?_ ?_ (Fintype.card ι) ?_ f x
  · rw [nhds_pi]
    exact (hasBasis_nhds_zero_valuation_le_uniformizer_zpow K).pi_self_of_finite
  · intro m
    ext y
    simpa [AddSubgroup.mem_characterAnnihilator, AddSubgroup.mem_pi, U] using
      forall_dotProduct_eq_one_iff_forall_valuation_le (setOf_eq_one_mem_nhds_zero hψ) h1 m y
  · intro m
    simp [AddSubgroup.coe_pi, Measure.pi_pi, U, Valuation.coe_leAddSubgroup]

/-- Fourier inversion on square matrices for the trace pairing and the product of the scalar
self-dual measures on their entries. -/
theorem fourierIntegral_fourierIntegral_traceBilinForm {ι : Type*} [Fintype ι]
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (f : compactlySupported ℂ (Matrix ι ι K) E)
    (X : Matrix ι ι K) :
    let μ := (Measure.pi fun _ : ι ↦ Measure.pi fun _ : ι ↦ ψ.selfDualMeasure).map
      (Matrix.ofMeasurableEquiv ι ι K)
    VectorFourier.fourierIntegral ψ μ (traceBilinForm K ι)
      (VectorFourier.fourierIntegral ψ μ (traceBilinForm K ι)
        ⇑(f : LocallyConstant (Matrix ι ι K) E)) X = (f : LocallyConstant _ E) (-X) := by
  let : MeasureSpace K := { volume := ψ.selfDualMeasure }
  have : (volume : Measure K).IsAddHaarMeasure := ψ.isAddHaarMeasure_selfDualMeasure
  let U (m : ℤ) := (valuation K).leAddSubgroup (uniformizer K ^ m)
  refine inversion_of_coordinate_boxes volume _ (traceBilinForm_flip K ι)
    (by simpa only [traceBilinForm_apply] using
      ((continuous_fst.matrix_mul continuous_snd).matrix_trace :
        Continuous fun p : Matrix ι ι K × Matrix ι ι K ↦ (p.1 * p.2).trace)) hψ
    (fun m ↦ (U m).matrix) ?_ ?_ (Fintype.card ι * Fintype.card ι) ?_ f X
  · have he : ⇑(Matrix.ofHomeomorph : (ι → ι → K) ≃ₜ Matrix ι ι K).symm = Matrix.of.symm :=
      funext Matrix.ofHomeomorph_symm_apply
    rw [Matrix.ofHomeomorph.symm.nhds_eq_comap, he]
    simp only [nhds_pi, Matrix.of_symm_apply, Matrix.zero_apply,
      AddSubgroup.coe_matrix, Set.matrix_eq_pi, Valuation.coe_leAddSubgroup, U]
    exact (((hasBasis_nhds_zero_valuation_le_uniformizer_zpow K).pi_self_of_finite
      (ι := ι)).pi_self_of_finite (ι := ι)).comap _
  · intro m
    ext Y
    rw [AddSubgroup.mem_characterAnnihilator]
    simpa only [← SetLike.mem_coe, AddSubgroup.coe_matrix, Set.mem_matrix,
      Valuation.coe_leAddSubgroup, Set.mem_ofPred_eq, traceBilinForm_apply, U] using
      forall_trace_mul_eq_one_iff_forall_valuation_le (setOf_eq_one_mem_nhds_zero hψ) h1 m Y
  · intro m
    rw [AddSubgroup.coe_matrix, Set.volume_matrix, Valuation.coe_leAddSubgroup]
    rfl

end AddChar
