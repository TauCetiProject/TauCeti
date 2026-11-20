/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Basic
public import TauCeti.Analysis.Normed.Operator.Splitting.Family
import TauCeti.Analysis.Calculus.ContDiff.Matrix
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearEquiv.Basic
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Kernel charts of Fredholm determinant lines

The determinant lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of a continuous family of Fredholm
operators `T x : E →L[𝕜] F` form a line bundle over the parameter space, although kernel and
cokernel jump. This file constructs its local trivializations and proves that they are
compatible: their transition functions are nowhere zero and have the regularity of the family. As
functions of the operator they are analytic. The bundle itself is
assembled from these charts in `TauCeti.Analysis.Fredholm.DeterminantLine.Bundle`.

A *kernel chart* is a finite stabilization `D₂ : Λ →L[𝕜] F`, with `Λ` finite-dimensional,
together with a kernel coordinate `q : E × Λ →L[𝕜] G`, with `G` finite-dimensional, for which the
pair `((T.coprod D₂).prod q)` is invertible. Then `T.coprod D₂` is onto and `q` identifies its
kernel with `G`, so the normalized stabilization isomorphism
`ContinuousLinearMap.detLineStabilizationEquiv` followed by `q` identifies the determinant line of
`T` with the fixed line `det G ⊗ (det Λ)^*` (`ContinuousLinearMap.detLineChartEquiv`).
Invertibility of the pair is an open condition on `T`, and
`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates` supplies such a chart near
every Fredholm operator, so the kernel charts of a family cover the parameter space.

Over operators at which two kernel charts are both defined, the transition from one to the other
is an isomorphism between two fixed lines, so it is multiplication by a scalar relative to its
value at any base operator `A₀`. The main theorem,
`ContinuousLinearMap.exists_contDiffAt_detLineChartEquiv_symm_eq_smul`, says that this scalar is an
analytic nowhere-vanishing function of the operator. Along a family `T x` of operators it is
therefore continuous when the family is continuous
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`) and `C^n` when the
family is `C^n` (`ContinuousLinearMap.exists_contDiffOn_detLineChartEquiv_symm_eq_smul`). Two
charts are compared through their sum `D₂.coprod D₃`
(`ContinuousLinearMap.IsInvertible.prod_coprod_coprod`), and the essential case is that of nested
stabilizers, `D₂ = D₂' ∘ ι`
(`ContinuousLinearMap.exists_contDiffAt_detLineChartEquiv_symm_eq_smul_of_comp`). There the
transition is the change of stabilizer `ContinuousLinearMap.detLineCoprodMapEquiv`,
which is constant on exterior products of suitable bases. These bases are a fixed basis of `G`
transported by the kernel section of `q`, followed by kernel vectors of the larger stabilization
lifting a fixed basis of `Λ' ⧸ range ι`, obtained from the right inverse normalized by `q`. Both
are analytic functions of the operator, since the inverse of an invertible operator is, and the
transition coefficient is the inverse of the determinant of their `q'`-coordinates, up to a
constant.

Kernel charts are natural with respect to commuting squares of stabilized operators
(`ContinuousLinearMap.detLineChartEquiv_detLineCongr`); in particular a kernel chart of `S`, for
`S ∘ e₁ = e₂ ∘ T`, reads the transport of the determinant line of `T` as the conjugate kernel chart
of `T` reads it (`ContinuousLinearMap.detLineChartEquiv_detLineCongr_of_comp_eq`). More generally,
operators with isomorphic kernels and cokernels, compared by a map of their stabilized kernels
compatible with the exact sequences and the kernel coordinates, have charts that read
corresponding elements of their determinant lines in the same way
(`ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker`), and a chart of the first operator is
valid as soon as the corresponding chart of the second is
(`ContinuousLinearMap.isInvertible_prod_coprod_of_kerCokerEquiv`). This compares, for instance, a
differential operator with a finite-dimensional endomorphism having the same kernel and cokernel.
Changing the
kernel coordinate `q` of a chart to `q₁` multiplies it by the determinant of `q₁ ∘ kerSection q`
(`ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul`), and changing the stabilizer `D₂` to
`D₂ + (D₁.coprod D₂) ∘ L`, with `L` valued in the kernel of `q`, multiplies it by the determinant
of `1 + snd ∘ L` (`ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul_of_coprod_apply_eq_sub`).
Over `ℝ`, when the stabilizer and the coordinate move continuously with a parameter, both
determinants are close to `1`, so the chart with moving data is a positive multiple of the chart
with the data frozen (`ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul`).

## Main definitions

* `ContinuousLinearMap.detLineChartEquiv`: the kernel chart `det T ≃ det G ⊗ (det Λ)^*` of the
  determinant line of `T` given by a stabilization `D₂` and kernel coordinate `q`.

## Main results

* `ContinuousLinearMap.exists_contDiffAt_detLineChartEquiv_symm_eq_smul_of_comp`: transitions
  between the kernel charts of nested stabilizers are analytic and nowhere zero, as functions of
  the operator.
* `ContinuousLinearMap.exists_contDiffAt_detLineChartEquiv_symm_eq_smul`: the same for any two
  kernel charts.
* `ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul_of_comp`,
  `ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`: along a continuous family
  of operators, the transitions are continuous and nowhere zero.
* `ContinuousLinearMap.exists_contDiffOn_detLineChartEquiv_symm_eq_smul`: along a family of
  operators which is `C^n` on a subset of a normed space, the transitions are `C^n` there.
* `ContinuousLinearMap.detLineChartEquiv_detLineCongr`,
  `ContinuousLinearMap.detLineChartEquiv_detLineCongr_of_comp_eq`: naturality of kernel charts.
* `ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker`,
  `ContinuousLinearMap.isInvertible_prod_coprod_of_kerCokerEquiv`: kernel charts of operators with
  isomorphic exact sequences of stabilization.
* `ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul_of_coprod_comp_eq`: kernel charts of
  the same operator related by automorphisms of `E × Λ` and of `G` differ by a ratio of
  determinants.
* `ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul`,
  `ContinuousLinearMap.detLineChartEquiv_apply_eq_det_smul_of_coprod_apply_eq_sub`: changing the
  kernel coordinate or the stabilizer of a kernel chart multiplies it by a determinant.
* `ContinuousLinearMap.IsFredholm.exists_isOpen_kernelChart`: a Fredholm operator has a kernel
  chart valid on an open neighbourhood.
* `ContinuousLinearMap.detLineChartEquiv_eq_detLineEquivOfBijective_smul`: the kernel chart of an
  invertible operator with zero stabilization and coordinate spaces
  (`ContinuousLinearMap.IsInvertible.prod_coprod_of_subsingleton`) reads the identification of its
  determinant line with the scalars as one fixed identification.
* `ContinuousLinearMap.eventually_detLineChartEquiv_symm_eq_smul`: over `ℝ`, the transition between
  two kernel charts valid at an operator is, nearby, a positive multiple of its value there.
* `ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul`: over `ℝ`, a kernel chart with
  continuously moving data is, nearby, a positive multiple of the chart with the data frozen.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

section Chart

variable {𝕜 E Λ F G : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G]
  {T : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G}

omit [FiniteDimensional 𝕜 Λ] in
/-- A kernel coordinate of a finite stabilization with finite-dimensional model makes the kernel
of the original operator finite-dimensional. -/
theorem finiteDimensional_ker_of_isInvertible_prod_coprod
    (h : ((T.coprod D₂).prod q).IsInvertible) : FiniteDimensional 𝕜 T.ker :=
  have := finite_ker_of_isInvertible_prod h
  FiniteDimensional.of_injective (kerCoprodHom T D₂ : T.ker →ₗ[𝕜] (T.coprod D₂).ker)
    (kerCoprodHom_injective T D₂)

variable (T D₂ q) in
/-- **A kernel chart of the determinant line.** If the stabilization `T.coprod D₂` paired with the
coordinate `q : E × Λ →L[𝕜] G` is invertible, then `T.coprod D₂` is onto and `q` identifies its
kernel with `G`. The normalized stabilization isomorphism
`ContinuousLinearMap.detLineStabilizationEquiv` followed by `q` then identifies the determinant
line of `T` with `det G ⊗ (det Λ)^*`. Its inverse on pure tensors is
`ContinuousLinearMap.detLineChartEquiv_symm_tmul`. -/
noncomputable def detLineChartEquiv (h : ((T.coprod D₂).prod q).IsInvertible) :
    (T : E →ₗ[𝕜] F).detLine ≃ₗ[𝕜]
      TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) :=
  have := finiteDimensional_ker_of_isInvertible_prod_coprod h
  (detLineStabilizationEquiv T D₂ (surjective_of_isInvertible_prod h)).symm ≪≫ₗ
    LinearEquiv.rTensor _ (kerEquivOfProd _ q h).toLinearEquiv.symm.detLineCongr

/-- The inverse of a kernel chart sends `g ⊗ φ` to the normalized stabilization isomorphism of the
image of `g` in the determinant line of the stabilized kernel, tensored with `φ`. -/
theorem detLineChartEquiv_symm_tmul [FiniteDimensional 𝕜 T.ker]
    (h : ((T.coprod D₂).prod q).IsInvertible)
    (g : TauCeti.detLine 𝕜 G) (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    (detLineChartEquiv T D₂ q h).symm (g ⊗ₜ φ) =
      detLineStabilizationEquiv T D₂ (surjective_of_isInvertible_prod h)
        ((kerEquivOfProd _ q h).toLinearEquiv.detLineCongr g ⊗ₜ φ) := by
  simp [detLineChartEquiv, LinearEquiv.detLineCongr_symm]

/-- A kernel chart undoes the normalized stabilization isomorphism, up to reading the stabilized
kernel in the coordinate `q`. -/
theorem detLineChartEquiv_detLineStabilizationEquiv [FiniteDimensional 𝕜 T.ker]
    (h : ((T.coprod D₂).prod q).IsInvertible)
    (z : TauCeti.detLine 𝕜 (T.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    detLineChartEquiv T D₂ q h
        (detLineStabilizationEquiv T D₂ (surjective_of_isInvertible_prod h) z) =
      LinearEquiv.rTensor _ (kerEquivOfProd _ q h).toLinearEquiv.symm.detLineCongr z := by
  simp [detLineChartEquiv]

section Subsingleton

variable [Subsingleton Λ] [Subsingleton G]

/-- **The invertibility trivialization in a zero kernel chart.** For a bijective `T` and a kernel
chart whose stabilization and coordinate spaces `Λ` and `G` are zero, the chart reads an element
`z` of the determinant line as its value under `LinearMap.detLineEquivOfBijective` times the
generator `1 ⊗ 1` of `det G ⊗ (det Λ)^*`, the empty exterior product tensored with the functional
taking the value `1` on it. The generator does not depend on `T`, so the identifications of the
determinant lines of invertible operators with the scalars form a continuous orientation. -/
theorem detLineChartEquiv_eq_detLineEquivOfBijective_smul
    (h : ((T.coprod D₂).prod q).IsInvertible) (hT : Function.Bijective T)
    (z : (T : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv T D₂ q h z = LinearMap.detLineEquivOfBijective hT z •
      (exteriorPower.ιMulti 𝕜 _ 0 ⊗ₜ (TauCeti.detLineEquivOfFinrankEqZero
        (finrank_zero_of_subsingleton (M := Λ))).toLinearMap :
          TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) := by
  have := finiteDimensional_ker_of_isInvertible_prod_coprod h
  have hΛ : finrank 𝕜 Λ = 0 := finrank_zero_of_subsingleton
  have hker : finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) = 0 :=
    LinearMap.finrank_ker_eq_zero_of_injective hT.1
  have hcoker : finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) = 0 :=
    LinearMap.finrank_quotient_range_eq_zero_of_surjective hT.2
  have hB : finrank 𝕜 (LinearMap.ker ((T.coprod D₂ : E × Λ →L[𝕜] F) : E × Λ →ₗ[𝕜] F)) = 0 :=
    (kerEquivOfProd _ q h).toLinearEquiv.finrank_eq.symm.trans finrank_zero_of_subsingleton
  have hsign : (-1 : 𝕜) ^ (finrank 𝕜 (F ⧸ (T : E →ₗ[𝕜] F).range) * finrank 𝕜 Λ) = 1 := by
    simp [hΛ]
  -- All the spaces of the exact sequence `0 → ker T → ker (T.coprod D₂) → Λ → coker T → 0` are
  -- zero, so the inverse chart sends the generator to the element `1` under invertibility.
  have hone : (detLineChartEquiv T D₂ q h).symm (exteriorPower.ιMulti 𝕜 _ 0 ⊗ₜ
      (TauCeti.detLineEquivOfFinrankEqZero hΛ).toLinearMap) =
        (LinearMap.detLineEquivOfBijective hT).symm 1 := by
    simp only [detLineChartEquiv_symm_tmul, detLineStabilizationEquiv_apply, hsign, one_smul,
      detLineCoprodEquiv_def, LinearEquiv.detLineCongr_ιMulti]
    rw [TauCeti.detLineFourTermEquiv_ιMulti_tmul_of_finrank_eq_zero _ _ _ _ hker hB hΛ hcoker 0,
      LinearMap.detLineEquivOfBijective_symm_one_eq_ιMulti_tmul]
  rw [← LinearEquiv.eq_symm_apply, map_smul, hone]
  apply (LinearMap.detLineEquivOfBijective hT).injective
  simp

end Subsingleton

section Nested

variable {Λ' G' : Type*} [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ']
  [AddCommGroup G'] [Module 𝕜 G'] [TopologicalSpace G'] [FiniteDimensional 𝕜 Λ']
  [FiniteDimensional 𝕜 G'] {D₂' : Λ' →L[𝕜] F} {q' : E × Λ' →L[𝕜] G'} {ι : Λ →ₗ[𝕜] Λ'}

/-- The transition between the kernel charts of two nested stabilizers, on the element of the
larger chart obtained from `g ∈ det G` and `w ∈ det (Λ' ⧸ range ι)`. -/
private theorem detLineChartEquiv_symm_tmul_nested [FiniteDimensional 𝕜 (T.coprod D₂).ker]
    (hι : ∀ l, D₂' (ι l) = D₂ l) (hι' : Function.Injective ι)
    (h : ((T.coprod D₂).prod q).IsInvertible) (h' : ((T.coprod D₂').prod q').IsInvertible)
    (g : TauCeti.detLine 𝕜 G) (w : TauCeti.detLine 𝕜 (Λ' ⧸ LinearMap.range ι))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ')) :
    detLineChartEquiv T D₂ q h ((detLineChartEquiv T D₂' q' h').symm
        ((kerEquivOfProd _ q' h').toLinearEquiv.symm.detLineCongr
          (TauCeti.detLineShortExactEquiv (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
            (surjective_mkQ_comp_parameterProj hι (surjective_of_isInvertible_prod h))
            ((kerEquivOfProd _ q h).toLinearEquiv.detLineCongr g ⊗ₜ w)) ⊗ₜ φ)) =
      g ⊗ₜ (φ ∘ₗ (TauCeti.detLineShortExactEquiv hι' (LinearMap.exact_map_mkQ_range ι)
        (Submodule.mkQ_surjective _)).toLinearMap ∘ₗ (TensorProduct.mk 𝕜 _ _).flip w) := by
  have := finiteDimensional_ker_of_isInvertible_prod_coprod h
  have hs := surjective_of_isInvertible_prod h
  rw [detLineChartEquiv_symm_tmul, ← LinearEquiv.detLineCongr_symm, LinearEquiv.apply_symm_apply,
    ← detLineStabilizationEquiv_detLineCoprodMapEquiv hι hι' hs,
    detLineChartEquiv_detLineStabilizationEquiv,
    detLineCoprodMapEquiv_detLineShortExactEquiv_tmul, LinearEquiv.rTensor_tmul,
    ← LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_apply]

omit [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 G'] in
/-- The element of `det G'` in `private theorem detLineChartEquiv_symm_tmul_nested`, for `g` the
exterior product of a family `b` and `w` that of the classes of a family `v` of kernel vectors of
the larger stabilization, is the exterior product of the `q'`-coordinates of the vectors of `b`
carried to the larger kernel, followed by those of `v`. -/
private theorem coe_detLineCongr_detLineShortExactEquiv_nested
    [FiniteDimensional 𝕜 (T.coprod D₂).ker]
    (hι : ∀ l, D₂' (ι l) = D₂ l) (hι' : Function.Injective ι)
    (h : ((T.coprod D₂).prod q).IsInvertible) (h' : ((T.coprod D₂').prod q').IsInvertible)
    (b : Fin (finrank 𝕜 G) → G)
    (v : Fin (finrank 𝕜 (Λ' ⧸ LinearMap.range ι)) → (T.coprod D₂').ker) :
    ((kerEquivOfProd _ q' h').toLinearEquiv.symm.detLineCongr
        (TauCeti.detLineShortExactEquiv (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
          (surjective_mkQ_comp_parameterProj hι (surjective_of_isInvertible_prod h))
          ((kerEquivOfProd _ q h).toLinearEquiv.detLineCongr (exteriorPower.ιMulti 𝕜 _ b) ⊗ₜ
            exteriorPower.ιMulti 𝕜 _ (((LinearMap.range ι).mkQ ∘ₗ
              (parameterProj T D₂' : (T.coprod D₂').ker →ₗ[𝕜] Λ')) ∘ v))) :
        ExteriorAlgebra 𝕜 G') =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (fun i ↦ q' (((T.coprod D₂).kerSection q (b i)).1, ι ((T.coprod D₂).kerSection q (b i)).2))
        (fun j ↦ q' (v j))) := by
  rw [LinearEquiv.coe_detLineCongr, TauCeti.coe_detLineShortExactEquiv_tmul_eq_map_mul]
  simp only [LinearEquiv.coe_detLineCongr, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  refine funext fun i ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp

omit [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 Λ']
  [FiniteDimensional 𝕜 G'] in
/-- From the right inverse of `T.coprod D₂` normalized by `q`, a kernel vector of the larger
stabilization `T.coprod D₂'` whose parameter is `l'` modulo the range of `ι`. -/
private theorem mem_ker_coprod_kerSection (hι : ∀ l, D₂' (ι l) = D₂ l)
    (h : ((T.coprod D₂).prod q).IsInvertible) (l' : Λ') :
    ((q.kerSection (T.coprod D₂) (-D₂' l')).1, l' + ι (q.kerSection (T.coprod D₂) (-D₂' l')).2) ∈
      (T.coprod D₂').ker := by
  have := apply_kerSection_right (isInvertible_prod_comm.mp h) (-D₂' l')
  simp only [coprod_apply, LinearMap.mem_ker, coe_coe, map_add, hι] at this ⊢
  rw [← add_assoc, add_right_comm, this, neg_add_cancel]

variable (T D₂ q D₂' q' ι) in
/-- The `q'`-coordinates of the vectors of `b` carried by the kernel section of `q` to the kernel
of the larger stabilization, followed by those of the kernel vectors of the larger stabilization
lifting `lift` (`private theorem mem_ker_coprod_kerSection`). -/
private noncomputable def kerCoordAppend {k m : ℕ} (b : Fin k → G) (lift : Fin m → Λ') :
    Fin (k + m) → G' :=
  Fin.append
    (fun i ↦ q' (((T.coprod D₂).kerSection q (b i)).1, ι ((T.coprod D₂).kerSection q (b i)).2))
    (fun j ↦ q' ((q.kerSection (T.coprod D₂) (-D₂' (lift j))).1,
      lift j + ι (q.kerSection (T.coprod D₂) (-D₂' (lift j))).2))

omit [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 Λ'] in
/-- Nested kernel charts have model dimensions differing by that of `Λ' ⧸ range ι`. -/
private theorem finrank_eq_finrank_add_finrank_quotient (hι : ∀ l, D₂' (ι l) = D₂ l)
    (hι' : Function.Injective ι) (h : ((T.coprod D₂).prod q).IsInvertible)
    (h' : ((T.coprod D₂').prod q').IsInvertible) :
    finrank 𝕜 G' = finrank 𝕜 G + finrank 𝕜 (Λ' ⧸ LinearMap.range ι) := by
  have := finite_ker_of_isInvertible_prod h
  have := finite_ker_of_isInvertible_prod h'
  rw [(kerEquivOfProd _ q' h').toLinearEquiv.finrank_eq,
    (exact_kerCoprodMap hι).finrank_eq_add (kerCoprodMap_injective hι hι')
      (surjective_mkQ_comp_parameterProj hι (surjective_of_isInvertible_prod h)),
    ← (kerEquivOfProd _ q h).toLinearEquiv.finrank_eq]

omit [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 G'] in
/-- The element of `det G'` in `private theorem detLineChartEquiv_symm_tmul_nested` built from
exterior products of bases is nonzero. -/
private theorem detLineCongr_detLineShortExactEquiv_ne_zero
    [FiniteDimensional 𝕜 (T.coprod D₂).ker] (hι : ∀ l, D₂' (ι l) = D₂ l)
    (hι' : Function.Injective ι) (h : ((T.coprod D₂).prod q).IsInvertible)
    (h' : ((T.coprod D₂').prod q').IsInvertible) (b : Module.Basis (Fin (finrank 𝕜 G)) 𝕜 G)
    (c : Module.Basis (Fin (finrank 𝕜 (Λ' ⧸ LinearMap.range ι))) 𝕜 (Λ' ⧸ LinearMap.range ι)) :
    (kerEquivOfProd _ q' h').toLinearEquiv.symm.detLineCongr
      (TauCeti.detLineShortExactEquiv (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
        (surjective_mkQ_comp_parameterProj hι (surjective_of_isInvertible_prod h))
        ((kerEquivOfProd _ q h).toLinearEquiv.detLineCongr (exteriorPower.ιMulti 𝕜 _ b) ⊗ₜ
          exteriorPower.ιMulti 𝕜 _ c)) ≠ 0 := by
  have ha := (LinearEquiv.map_ne_zero_iff (kerEquivOfProd _ q h).toLinearEquiv.detLineCongr).2
    ((exteriorPower.ιMulti_ne_zero_iff _).2 b.linearIndependent)
  have hc := (exteriorPower.ιMulti_ne_zero_iff _).2 c.linearIndependent
  exact (LinearEquiv.map_ne_zero_iff _).2
    ((LinearEquiv.map_ne_zero_iff _).2 (TauCeti.tmul_ne_zero ha hc))

end Nested

end Chart

section ChartCongr

variable {𝕜 E Λ F G E' Λ' F' G' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ'] [AddCommGroup F'] [Module 𝕜 F']
  [TopologicalSpace F'] [ContinuousAdd F'] [AddCommGroup G'] [Module 𝕜 G'] [TopologicalSpace G']
  [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 Λ'] [FiniteDimensional 𝕜 G']
  {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {D₁' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'}
  {q : E × Λ →L[𝕜] G} {q' : E' × Λ' →L[𝕜] G'}
  {e₁ : E ≃ₗ[𝕜] E'} {e₂ : F ≃ₗ[𝕜] F'} {eΛ : Λ ≃ₗ[𝕜] Λ'} {Ψ : (E × Λ) ≃ₗ[𝕜] (E' × Λ')}

/-- **Kernel charts of operators with isomorphic exact sequences.** Let `eK` and `eC` identify
the kernels and the cokernels of `D₁` and `D₁'`, and let `Φ : E × Λ → E' × Λ'` carry the kernel of
the stabilization `D₁.coprod D₂` into that of `D₁'.coprod D₂'`, restricting to `eK` on
`ker D₁ × 0`, acting on the stabilizing component by `eΛ` and matching the kernel coordinates
along `eG : G ≃ G'`, `q' ∘ Φ = eG ∘ q`, on the stabilized kernel. If moreover `eC` sends the class
of `D₂ l` to that of `D₂' (eΛ l)`, then the two kernel charts intertwine
`LinearMap.detLineCongrKerCoker eK eC` with the isomorphism
`det G ⊗ (det Λ)^* ≃ det G' ⊗ (det Λ')^*` induced by `eG` and `eΛ`.

The operators need not be related by isomorphisms of their sources and targets, as in
`ContinuousLinearMap.detLineChartEquiv_detLineCongr`: for instance `D₁` may be a differential
operator and `D₁'` an endomorphism of a finite-dimensional space with the same kernel and
cokernel. -/
theorem detLineChartEquiv_detLineCongrKerCoker {eK : D₁.ker ≃ₗ[𝕜] D₁'.ker}
    {eC : (F ⧸ D₁.range) ≃ₗ[𝕜] (F' ⧸ D₁'.range)} {Φ : E × Λ →ₗ[𝕜] E' × Λ'}
    (hΦ : ∀ y, D₁.coprod D₂ y = 0 → D₁'.coprod D₂' (Φ y) = 0)
    (hK : ∀ u : D₁.ker, Φ ((u : E), 0) = ((eK u : E'), 0))
    (hΛ : ∀ y, D₁.coprod D₂ y = 0 → (Φ y).2 = eΛ y.2)
    (hC : ∀ l, eC (D₁.range.mkQ (D₂ l)) = D₁'.range.mkQ (D₂' (eΛ l))) (eG : G ≃ₗ[𝕜] G')
    (hq : ∀ y, D₁.coprod D₂ y = 0 → q' (Φ y) = eG (q y))
    (h : ((D₁.coprod D₂).prod q).IsInvertible) (h' : ((D₁'.coprod D₂').prod q').IsInvertible)
    (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁' D₂' q' h' (LinearMap.detLineCongrKerCoker eK eC y) =
      TensorProduct.congr eG.detLineCongr eΛ.detLineCongr.symm.dualMap
        (detLineChartEquiv D₁ D₂ q h y) := by
  have := finiteDimensional_ker_of_isInvertible_prod_coprod h
  have := finiteDimensional_ker_of_isInvertible_prod_coprod h'
  have hs := surjective_of_isInvertible_prod h
  have hs' := surjective_of_isInvertible_prod h'
  -- The stabilized kernels are identified through their coordinate spaces and `eG`; on them this
  -- identification is `Φ`.
  set eS : (D₁.coprod D₂).ker ≃ₗ[𝕜] (D₁'.coprod D₂').ker :=
    (kerEquivOfProd _ q h).toLinearEquiv.symm.trans
      (eG.trans (kerEquivOfProd _ q' h').toLinearEquiv) with heS_def
  have heS (z : (D₁.coprod D₂).ker) : (eS z : E' × Λ') = Φ z := by
    simp only [heS_def, LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      kerEquivOfProd_symm_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      coe_kerEquivOfProd_apply]
    rw [← hq z z.property, kerSection_apply_of_mem_ker h' (hΦ z z.property)]
  obtain ⟨t, rfl⟩ := (detLineStabilizationEquiv D₁ D₂ hs).surjective y
  rw [← detLineStabilizationEquiv_congrKerCoker eK eS eC (fun u ↦ Subtype.ext ?_) (fun z ↦ ?_)
      (fun l ↦ ?_) hs hs' t,
    detLineChartEquiv_detLineStabilizationEquiv, detLineChartEquiv_detLineStabilizationEquiv]
  · induction t using TensorProduct.inductionOn with
    | tmul a φ =>
      rw [TensorProduct.congr_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul,
        TensorProduct.congr_tmul]
      congr 1
      rw [← LinearEquiv.trans_apply, ← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans,
        ← LinearEquiv.detLineCongr_trans]
      refine congrArg (fun e ↦ LinearEquiv.detLineCongr e a) (LinearEquiv.ext fun k ↦ ?_)
      simp [heS_def]
    | add a b ha hb => rw [LinearEquiv.map_add, LinearEquiv.map_add, ha, hb, LinearEquiv.map_add,
        LinearEquiv.map_add]
  · rw [heS, kerCoprodHom_apply, kerCoprodHom_apply]
    exact hK u
  · simp [parameterProj_apply, heS, hΛ z z.property]
  · simp only [parameterToCoker_apply]
    exact (hC l).symm

/-- **Naturality of kernel charts.** In the setting of
`ContinuousLinearMap.detLineStabilizationEquiv_congr`, let `(D₂, q)` and `(D₂', q')` be kernel
charts of `D₁` and `D₁'`, and let `eG : G ≃ G'` match the kernel coordinates along `Ψ` on the
stabilized kernel. Then the two charts intertwine the transport of determinant lines along the
square formed by `e₁` and `e₂` with the isomorphism `det G ⊗ (det Λ)^* ≃ det G' ⊗ (det Λ')^*`
induced by `eG` and `eΛ`. -/
theorem detLineChartEquiv_detLineCongr
    (hΨ : (D₁'.coprod D₂' : E' × Λ' →ₗ[𝕜] F') ∘ₗ Ψ.toLinearMap =
      e₂.toLinearMap ∘ₗ (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))
    (hΨ₁ : ∀ x, Ψ (x, 0) = (e₁ x, 0)) (hΨ₂ : ∀ y, (Ψ y).2 = eΛ y.2) (eG : G ≃ₗ[𝕜] G')
    (hq : ∀ y ∈ (D₁.coprod D₂).ker, q' (Ψ y) = eG (q y))
    (hinv : ((D₁.coprod D₂).prod q).IsInvertible)
    (hinv' : ((D₁'.coprod D₂').prod q').IsInvertible) (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁' D₂' q' hinv'
        ((D₁ : E →ₗ[𝕜] F).detLineCongr e₁ e₂ (comp_eq_of_coprod_comp_eq hΨ hΨ₁) y) =
      TensorProduct.congr eG.detLineCongr eΛ.detLineCongr.symm.dualMap
        (detLineChartEquiv D₁ D₂ q hinv y) := by
  rw [LinearMap.detLineCongr_eq_detLineCongrKerCoker]
  refine detLineChartEquiv_detLineCongrKerCoker (Φ := Ψ.toLinearMap)
    (fun z hz ↦ (LinearMap.congr_fun hΨ z).trans (by
      rw [LinearMap.comp_apply, coe_coe, hz, map_zero])) (fun u ↦ by simp [hΨ₁])
    (fun z _ ↦ hΨ₂ z) (quotientEquiv_mkQ_of_coprod_comp_eq hΨ hΨ₂ _) eG hq hinv hinv' y

/-- **Changing the data of a kernel chart.** Let `(D₂, q)` and `(D₃, q₁)` be kernel charts of the
same operator `D₁`, related by an automorphism `Ψ₁` of `E × Λ` which fixes `E × 0`, acts on the
stabilizing space by `eΛ₁` and intertwines `D₁.coprod D₂` with `D₁.coprod D₃`, and by an
automorphism `eG` of `G` matching the kernel coordinates along `Ψ₁`. Then the two charts differ by
`det eG * (det eΛ₁)⁻¹`. -/
theorem detLineChartEquiv_apply_eq_det_smul_of_coprod_comp_eq {D₃ : Λ →L[𝕜] F}
    {q₁ : E × Λ →L[𝕜] G} {eΛ₁ : Λ ≃ₗ[𝕜] Λ} {Ψ₁ : (E × Λ) ≃ₗ[𝕜] (E × Λ)}
    (hΨ : (D₁.coprod D₃ : E × Λ →ₗ[𝕜] F) ∘ₗ Ψ₁.toLinearMap = (D₁.coprod D₂ : E × Λ →ₗ[𝕜] F))
    (hΨ₁ : ∀ x, Ψ₁ (x, 0) = (x, 0)) (hΨ₂ : ∀ y, (Ψ₁ y).2 = eΛ₁ y.2) (eG : G ≃ₗ[𝕜] G)
    (hq : ∀ y ∈ (D₁.coprod D₂).ker, q₁ (Ψ₁ y) = eG (q y))
    (h : ((D₁.coprod D₂).prod q).IsInvertible) (h₁ : ((D₁.coprod D₃).prod q₁).IsInvertible)
    (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁ D₃ q₁ h₁ y =
      (LinearMap.det (eG : G →ₗ[𝕜] G) * (LinearMap.det (eΛ₁ : Λ →ₗ[𝕜] Λ))⁻¹) •
        detLineChartEquiv D₁ D₂ q h y := by
  have := detLineChartEquiv_detLineCongr (e₁ := LinearEquiv.refl 𝕜 E)
    (e₂ := LinearEquiv.refl 𝕜 F) hΨ hΨ₁ hΨ₂ eG hq h h₁ y
  simpa only [LinearMap.detLineCongr_refl, LinearEquiv.refl_apply,
    LinearEquiv.tensorProductCongr_detLineCongr_apply_eq_det_smul, Units.smul_def, Units.val_mul,
    Units.val_inv_eq_inv_val, LinearEquiv.coe_det] using this

/-- **Changing the kernel coordinate.** Two kernel charts of `D₁` with the same stabilizer `D₂`
differ by the determinant of the change of coordinate `q₁ ∘ kerSection q` of `G`. -/
theorem detLineChartEquiv_apply_eq_det_smul (h : ((D₁.coprod D₂).prod q).IsInvertible)
    {q₁ : E × Λ →L[𝕜] G} (h₁ : ((D₁.coprod D₂).prod q₁).IsInvertible)
    (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁ D₂ q₁ h₁ y =
      (q₁ ∘L (D₁.coprod D₂).kerSection q).det • detLineChartEquiv D₁ D₂ q h y := by
  set eG : G ≃ₗ[𝕜] G := ((D₁.coprod D₂).kerEquivOfProd q h).toLinearEquiv.trans
    ((D₁.coprod D₂).kerEquivOfProd q₁ h₁).toLinearEquiv.symm with heG
  have hdet : LinearMap.det (eG : G →ₗ[𝕜] G) = (q₁ ∘L (D₁.coprod D₂).kerSection q).det := by
    congr 1
    exact LinearMap.ext fun g ↦ by simp [heG]
  rw [detLineChartEquiv_apply_eq_det_smul_of_coprod_comp_eq (eΛ₁ := LinearEquiv.refl 𝕜 Λ)
    (Ψ₁ := LinearEquiv.refl 𝕜 (E × Λ)) (LinearMap.ext fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) eG
    (fun z hz ↦ by simp [heG, kerSection_apply_of_mem_ker h hz]) h h₁ y, hdet,
    LinearEquiv.refl_toLinearMap, LinearMap.det_id, inv_one, mul_one]

variable [ContinuousAdd Λ] in
/-- **Changing the stabilizer.** Let `D₂' = D₂ + (D₁.coprod D₂) ∘ L` for a map `L : Λ → E × Λ`
with values in the kernel of the coordinate `q`. Then the kernel charts `(D₂', q)` and `(D₂, q)` of
`D₁` differ by the determinant of the induced change `1 + snd ∘ L` of the stabilizing space. -/
theorem detLineChartEquiv_apply_eq_det_smul_of_coprod_apply_eq_sub {D₂' : Λ →L[𝕜] F}
    {L : Λ →L[𝕜] E × Λ} (hL : ∀ l, D₁.coprod D₂ (L l) = D₂' l - D₂ l) (hqL : ∀ l, q (L l) = 0)
    (h : ((D₁.coprod D₂).prod q).IsInvertible) (h' : ((D₁.coprod D₂').prod q).IsInvertible)
    (y : (D₁ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv D₁ D₂' q h' y =
      (ContinuousLinearMap.id 𝕜 Λ + snd 𝕜 E Λ ∘L L).det • detLineChartEquiv D₁ D₂ q h y := by
  set Φ := ContinuousLinearMap.id 𝕜 Λ + snd 𝕜 E Λ ∘L L with hΦ_def
  -- `Ψ (u, l) = (u, l) + L l` carries the kernel of `(D₁.coprod D₂', q)` into that of
  -- `(D₁.coprod D₂, q)`, so `Φ` is injective.
  have hΨL (z : E × Λ) : (D₁.coprod D₂ (z + L z.2), q (z + L z.2)) =
      (D₁.coprod D₂' z, q z) := by
    refine Prod.ext ?_ ?_
    · simp only [map_add, hL, coprod_apply]
      abel
    · simp [hqL]
  have hΦ : LinearMap.det (Φ : Λ →ₗ[𝕜] Λ) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
    intro l hl
    have hl' : l + (L l).2 = 0 := by simpa [hΦ_def] using hl
    have hz : ((D₁.coprod D₂').prod q) (-(L l).1, l) = 0 := by
      have h0 : (-(L l).1, l) + L (-(L l).1, l).2 = 0 := Prod.ext (neg_add_cancel _) hl'
      rw [prod_apply, ← hΨL, h0, map_zero, map_zero, Prod.mk_zero_zero]
    obtain ⟨e, he⟩ := h'
    rw [← he, ContinuousLinearEquiv.coe_coe, e.map_eq_zero_iff] at hz
    exact congrArg Prod.snd hz
  set eΛ : Λ ≃ₗ[𝕜] Λ := (Φ : Λ →ₗ[𝕜] Λ).equivOfDetNeZero hΦ with heΛ
  set Ψ : (E × Λ) ≃ₗ[𝕜] (E × Λ) := (LinearEquiv.prodComm 𝕜 E Λ).trans
    ((eΛ.skewProd (LinearEquiv.refl 𝕜 E) (fst 𝕜 E Λ ∘L L : Λ →L[𝕜] E)).trans
      (LinearEquiv.prodComm 𝕜 Λ E)) with hΨ_def
  have hΨ (z : E × Λ) : Ψ z = z + L z.2 := by
    ext <;> simp [hΨ_def, heΛ, hΦ_def]
  have hdet : LinearMap.det (eΛ : Λ →ₗ[𝕜] Λ) = Φ.det := by simp [heΛ]
  rw [detLineChartEquiv_apply_eq_det_smul_of_coprod_comp_eq (q₁ := q) (eΛ₁ := eΛ)
    (Ψ₁ := Ψ) (LinearMap.ext fun z ↦ by simpa [hΨ] using congrArg Prod.fst (hΨL z))
    (fun u ↦ by simp [hΨ]) (fun z ↦ by simp [hΨ, heΛ, hΦ_def]) (LinearEquiv.refl 𝕜 G)
    (fun z _ ↦ by simp [hΨ, hqL]) h' h y, hdet, LinearEquiv.refl_toLinearMap, LinearMap.det_id,
    one_mul, smul_inv_smul₀ (hdet ▸ hΦ)]

end ChartCongr

section Conjugate

variable {𝕜 E Λ F G E' F' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] [AddCommGroup F']
  [Module 𝕜 F'] [TopologicalSpace F'] [ContinuousAdd F'] [FiniteDimensional 𝕜 Λ]
  [FiniteDimensional 𝕜 G] {T : E →L[𝕜] F} {S : E' →L[𝕜] F'} {e₁ : E ≃L[𝕜] E'} {e₂ : F ≃L[𝕜] F'}
  {D₂ : Λ →L[𝕜] F'} {q : E' × Λ →L[𝕜] G}

omit [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G] in
/-- A kernel chart `(D₂, q)` of `S`, for `S ∘ e₁ = e₂ ∘ T`, is valid when the kernel chart
`(e₂⁻¹ ∘ D₂, q ∘ (e₁ × 1))` of `T` is. -/
theorem isInvertible_prod_coprod_of_comp_eq
    (h : (S : E' →ₗ[𝕜] F') ∘ₗ e₁.toLinearEquiv.toLinearMap =
      e₂.toLinearEquiv.toLinearMap ∘ₗ (T : E →ₗ[𝕜] F))
    (hT : ((T.coprod ((e₂.symm : F' →L[𝕜] F) ∘L D₂)).prod
      (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ))).IsInvertible) :
    ((S.coprod D₂).prod q).IsInvertible := by
  have hS (u : E') : S u = e₂ (T (e₁.symm u)) := by
    simpa using LinearMap.congr_fun h (e₁.symm u)
  have : (S.coprod D₂).prod q =
      ((e₂.prodCongr (ContinuousLinearEquiv.refl 𝕜 G) : F × G →L[𝕜] F' × G) ∘L
        (T.coprod ((e₂.symm : F' →L[𝕜] F) ∘L D₂)).prod
          (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ))) ∘L
      ((e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 Λ)).symm : E' × Λ →L[𝕜] E × Λ) := by
    ext z <;> simp [hS]
  rw [this, isInvertible_comp_equiv, isInvertible_equiv_comp]
  exact hT

/-- **Conjugate kernel charts.** For `S ∘ e₁ = e₂ ∘ T`, the kernel chart `(D₂, q)` of `S` reads
the transport of `y ∈ det T` along the square as the kernel chart `(e₂⁻¹ ∘ D₂, q ∘ (e₁ × 1))` of
`T` reads `y`. -/
theorem detLineChartEquiv_detLineCongr_of_comp_eq
    (h : (S : E' →ₗ[𝕜] F') ∘ₗ e₁.toLinearEquiv.toLinearMap =
      e₂.toLinearEquiv.toLinearMap ∘ₗ (T : E →ₗ[𝕜] F))
    (hT : ((T.coprod ((e₂.symm : F' →L[𝕜] F) ∘L D₂)).prod
      (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ))).IsInvertible)
    (y : (T : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv S D₂ q (isInvertible_prod_coprod_of_comp_eq h hT)
        ((T : E →ₗ[𝕜] F).detLineCongr e₁.toLinearEquiv e₂.toLinearEquiv h y) =
      detLineChartEquiv T ((e₂.symm : F' →L[𝕜] F) ∘L D₂)
        (q ∘L ((e₁ : E →L[𝕜] E') ∘L fst 𝕜 E Λ).prod (snd 𝕜 E Λ)) hT y := by
  have hS (u : E) : S (e₁ u) = e₂ (T u) := by simpa using LinearMap.congr_fun h u
  have := detLineChartEquiv_detLineCongr (e₁ := e₁.toLinearEquiv) (e₂ := e₂.toLinearEquiv)
    (Ψ := e₁.toLinearEquiv.prodCongr (LinearEquiv.refl 𝕜 Λ)) (eΛ := LinearEquiv.refl 𝕜 Λ)
    (LinearMap.ext fun z ↦ by simp [hS])
    (fun _ ↦ rfl) (fun _ ↦ rfl) (LinearEquiv.refl 𝕜 G) (fun z _ ↦ by simp) hT
    (isInvertible_prod_coprod_of_comp_eq h hT) y
  rw [LinearEquiv.tensorProductCongr_detLineCongr_apply_eq_det_smul] at this
  simpa using this

end Conjugate

section Comparison

/-! ### Kernel charts of operators with isomorphic exact sequences -/

variable {𝕜 E Λ F E' Λ' F' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup E'] [Module 𝕜 E']
  [TopologicalSpace E'] [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ'] [AddCommGroup F']
  [Module 𝕜 F'] [TopologicalSpace F'] [ContinuousAdd F'] {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F}
  {D₁' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'} {eK : D₁.ker ≃ₗ[𝕜] D₁'.ker}
  {eC : (F ⧸ D₁.range) ≃ₗ[𝕜] (F' ⧸ D₁'.range)} {eΛ : Λ ≃ₗ[𝕜] Λ'} {Φ : E × Λ →ₗ[𝕜] E' × Λ'}

/-- **The five lemma for stabilized kernels.** In the situation of
`ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker`, `Φ` maps the kernel of
`D₁.coprod D₂` onto that of `D₁'.coprod D₂'`. -/
private theorem exists_coprod_eq_zero_and_eq
    (hΦ : ∀ y, D₁.coprod D₂ y = 0 → D₁'.coprod D₂' (Φ y) = 0)
    (hK : ∀ u : D₁.ker, Φ ((u : E), 0) = ((eK u : E'), 0))
    (hΛ : ∀ y, D₁.coprod D₂ y = 0 → (Φ y).2 = eΛ y.2)
    (hC : ∀ l, eC (D₁.range.mkQ (D₂ l)) = D₁'.range.mkQ (D₂' (eΛ l))) (y' : E' × Λ')
    (hy' : D₁'.coprod D₂' y' = 0) : ∃ y, D₁.coprod D₂ y = 0 ∧ Φ y = y' := by
  obtain ⟨u', l'⟩ := y'
  obtain ⟨l, rfl⟩ := eΛ.surjective l'
  have hy'' : D₁' u' + D₂' (eΛ l) = 0 := by simpa using hy'
  -- The class of `D₂ l` vanishes, since that of `D₂' (eΛ l)` does.
  have hmk : D₁.range.mkQ (D₂ l) = 0 := by
    refine eC.injective ?_
    rw [hC, map_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨-u', ?_⟩
    rw [coe_coe, map_neg, neg_eq_iff_add_eq_zero]
    exact hy''
  obtain ⟨u₀, hu₀⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmk
  rw [coe_coe] at hu₀
  have hy₀ : D₁.coprod D₂ (-u₀, l) = 0 := by simp [hu₀]
  -- The difference `(u', eΛ l) - Φ (-u₀, l)` lies in `ker D₁' × 0`, so it is the image of
  -- `ker D₁ × 0`.
  have h2 : (Φ (-u₀, l)).2 = eΛ l := hΛ _ hy₀
  have hd : D₁' (u' - (Φ (-u₀, l)).1) = 0 := by
    have h1 := hΦ _ hy₀
    rw [← Prod.mk.eta (p := Φ (-u₀, l)), h2] at h1
    simp only [coprod_apply] at h1
    rw [map_sub, sub_eq_zero]
    exact add_right_cancel (hy''.trans h1.symm)
  obtain ⟨u, hu⟩ := eK.surjective ⟨_, hd⟩
  refine ⟨(-u₀ + u, l), by simp [hu₀], ?_⟩
  have : ((-u₀ + (u : E), l) : E × Λ) = (-u₀, l) + ((u : E), 0) := by simp
  rw [this, map_add, hK u, hu]
  ext <;> simp [h2]

end Comparison

section ComparisonInvertible

variable {𝕜 E Λ F G E' Λ' F' G' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] [AddCommGroup Λ'] [Module 𝕜 Λ']
  [TopologicalSpace Λ'] [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [ContinuousAdd F']
  [AddCommGroup G'] [Module 𝕜 G'] [TopologicalSpace G']
  {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G}
  {D₁' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'} {q' : E' × Λ' →L[𝕜] G'}
  {eK : D₁.ker ≃ₗ[𝕜] D₁'.ker} {eC : (F ⧸ D₁.range) ≃ₗ[𝕜] (F' ⧸ D₁'.range)} {eΛ : Λ ≃ₗ[𝕜] Λ'}
  {Φ : E × Λ →ₗ[𝕜] E' × Λ'}

/-- **Kernel charts transfer along isomorphic exact sequences.** In the situation of
`ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker`, with `D₁` an operator between Banach
spaces, the pair `(D₂, q)` is a kernel chart of `D₁` as soon as `(D₂', q')` is a kernel chart of
`D₁'`. -/
theorem isInvertible_prod_coprod_of_kerCokerEquiv
    (hΦ : ∀ y, D₁.coprod D₂ y = 0 → D₁'.coprod D₂' (Φ y) = 0)
    (hK : ∀ u : D₁.ker, Φ ((u : E), 0) = ((eK u : E'), 0))
    (hΛ : ∀ y, D₁.coprod D₂ y = 0 → (Φ y).2 = eΛ y.2)
    (hC : ∀ l, eC (D₁.range.mkQ (D₂ l)) = D₁'.range.mkQ (D₂' (eΛ l))) (eG : G ≃ₗ[𝕜] G')
    (hq : ∀ y, D₁.coprod D₂ y = 0 → q' (Φ y) = eG (q y))
    (h' : ((D₁'.coprod D₂').prod q').IsInvertible) : ((D₁.coprod D₂).prod q).IsInvertible := by
  have : CompleteSpace Λ := FiniteDimensional.completeSpace 𝕜 Λ
  have : CompleteSpace G := FiniteDimensional.completeSpace 𝕜 G
  -- `D₁.coprod D₂` is onto: every class in the cokernel of `D₁` is the class of some `D₂ l`.
  have hsurj : Function.Surjective (D₁.coprod D₂) := by
    refine (parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).1 fun c ↦ ?_
    obtain ⟨l', hl⟩ := (parameterToCoker_surjective_iff_coprod_surjective D₁' D₂').2
      (surjective_of_isInvertible_prod h') (eC c)
    obtain ⟨l, rfl⟩ := eΛ.surjective l'
    refine ⟨l, eC.injective ?_⟩
    rw [parameterToCoker_apply, hC, ← parameterToCoker_apply, hl]
  have hker := exists_coprod_eq_zero_and_eq (eK := eK) hΦ hK hΛ hC
  refine isInvertible_iff_bijective.2 ⟨(injective_iff_map_eq_zero _).2 fun y hy ↦ ?_,
    fun ⟨f, g⟩ ↦ ?_⟩
  · obtain ⟨u, l⟩ := y
    have hy₁ : D₁.coprod D₂ (u, l) = 0 := congrArg Prod.fst hy
    have hq0 : q (u, l) = 0 := congrArg Prod.snd hy
    -- `Φ (u, l)` lies in the stabilized kernel of `D₁'` with vanishing coordinate, so it is zero.
    have hΦ0 : Φ (u, l) = 0 := h'.injective (by
      simp only [map_zero]
      exact Prod.ext (hΦ _ hy₁) ((hq _ hy₁).trans (by simp [hq0])))
    have hl : l = 0 := by simpa [hΦ0] using (hΛ _ hy₁).symm
    subst hl
    have hu : D₁ u = 0 := by simpa using hy₁
    have := hK ⟨u, hu⟩
    rw [hΦ0, eq_comm, Prod.mk_eq_zero, ZeroMemClass.coe_eq_zero,
      LinearEquiv.map_eq_zero_iff] at this
    simpa using congrArg Subtype.val this.1
  · obtain ⟨y₀, hy₀⟩ := hsurj f
    set y' := (D₁'.coprod D₂').kerSection q' (eG (g - q y₀))
    obtain ⟨k, hk, hky⟩ := hker y' (apply_kerSection _)
    have hqk : q k = g - q y₀ := eG.injective (by rw [← hq k hk, hky, apply_kerSection_right h'])
    refine ⟨y₀ + k, Prod.ext ?_ ?_⟩
    · rw [prod_apply, map_add, hy₀, hk, add_zero]
    · simp [hqk]

end ComparisonInvertible

section Regularity

open scoped ContDiff

variable {𝕜 E Λ Λ' F G G' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
  [NormedAddCommGroup Λ'] [NormedSpace 𝕜 Λ'] [FiniteDimensional 𝕜 Λ']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] [FiniteDimensional 𝕜 G']
  {D₂ : Λ →L[𝕜] F} {D₂' : Λ' →L[𝕜] F} {q : E × Λ →L[𝕜] G} {q' : E × Λ' →L[𝕜] G'}
  {ι : Λ →ₗ[𝕜] Λ'}

omit [FiniteDimensional 𝕜 Λ'] [FiniteDimensional 𝕜 G] in
/-- The determinant, against a fixed basis of `G'`, of the `q'`-coordinates of the kernel vectors
of the larger stabilization used to compare two nested kernel charts is an analytic function of the
operator at every operator where the smaller chart is valid. -/
private theorem contDiffAt_det_kerCoordAppend {A : E →L[𝕜] F}
    (h : ((A.coprod D₂).prod q).IsInvertible) {k m : ℕ}
    (bB : Module.Basis (Fin (k + m)) 𝕜 G') (b : Fin k → G) (lift : Fin m → Λ') :
    ContDiffAt 𝕜 ω (fun A ↦ bB.det (kerCoordAppend A D₂ q D₂' q' ι b lift)) A := by
  have : CompleteSpace Λ := FiniteDimensional.completeSpace 𝕜 Λ
  have hA : ContDiffAt 𝕜 ω (fun A : E →L[𝕜] F ↦ A.coprod D₂) A :=
    contDiffAt_id.continuousLinearMapCoprod contDiffAt_const
  have hks : ContDiffAt 𝕜 ω (fun A : E →L[𝕜] F ↦ (A.coprod D₂).kerSection q) A :=
    hA.kerSection contDiffAt_const h
  have hrc : ContDiffAt 𝕜 ω (fun A : E →L[𝕜] F ↦ q.kerSection (A.coprod D₂)) A :=
    contDiffAt_const.kerSection hA (isInvertible_prod_comm.mp h)
  -- `q' (x.1, ι x.2 + l)` is an affine function of `x`.
  have hq (l : Λ') : ContDiff 𝕜 ω fun x : E × Λ ↦ q' (x.1, l + ι x.2) := by
    have hι : ContDiff 𝕜 ω fun x : E × Λ ↦ ι x.2 := by
      simpa only [LinearMap.coe_toContinuousLinearMap', Function.comp_def] using
        (LinearMap.toContinuousLinearMap ι).contDiff.comp contDiff_snd
    exact q'.contDiff.comp (contDiff_fst.prodMk (contDiff_const.add hι))
  have hfam : ContDiffAt 𝕜 ω (fun A ↦ kerCoordAppend A D₂ q D₂' q' ι b lift) A := by
    refine contDiffAt_pi.2 fun i ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
    · simpa only [kerCoordAppend, Fin.append_left, zero_add, Function.comp_def] using
        (hq 0).contDiffAt.comp A (hks.clm_apply (contDiffAt_const (c := b i)))
    · simpa only [kerCoordAppend, Fin.append_right, Function.comp_def] using
        (hq (lift j)).contDiffAt.comp A (hrc.clm_apply (contDiffAt_const (c := -D₂' (lift j))))
  simp only [Module.Basis.det_apply]
  refine ContDiffAt.matrix_det fun i j ↦ ?_
  simpa only [Module.Basis.toMatrix_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, Function.comp_def] using
    (LinearMap.toContinuousLinearMap (bB.coord i)).contDiff.contDiffAt.comp A
      (contDiffAt_pi.1 hfam j)

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/-- For nested kernel charts both valid at `A`, an element `y` of `det G'`, read off as the
determinant against a fixed basis `bB` of the `q'`-coordinates of kernel vectors of the larger
stabilization, on which the transition from the larger chart to the smaller one takes a value
independent of `A`. Here `lift` lifts a fixed basis of `Λ' ⧸ range ι` to `Λ'`. -/
private theorem exists_detLineChartEquiv_symm_tmul_nested
    (hι : ∀ l, D₂' (ι l) = D₂ l) (hι' : Function.Injective ι) {A : E →L[𝕜] F}
    (h : ((A.coprod D₂).prod q).IsInvertible) (h' : ((A.coprod D₂').prod q').IsInvertible)
    (bB : Module.Basis (Fin (finrank 𝕜 G + finrank 𝕜 (Λ' ⧸ LinearMap.range ι))) 𝕜 G')
    (lift : Fin (finrank 𝕜 (Λ' ⧸ LinearMap.range ι)) → Λ')
    (hlift : ∀ j, (LinearMap.range ι).mkQ (lift j) = Module.finBasis 𝕜 _ j) :
    ∃ y : TauCeti.detLine 𝕜 G', y ≠ 0 ∧
      (y : ExteriorAlgebra 𝕜 G') =
        bB.det (kerCoordAppend A D₂ q D₂' q' ι (Module.finBasis 𝕜 G) lift) •
          ExteriorAlgebra.ιMulti 𝕜 _ bB ∧
      ∀ φ, detLineChartEquiv A D₂ q h ((detLineChartEquiv A D₂' q' h').symm (y ⊗ₜ φ)) =
        exteriorPower.ιMulti 𝕜 _ (Module.finBasis 𝕜 G) ⊗ₜ
          (φ ∘ₗ (TauCeti.detLineShortExactEquiv hι' (LinearMap.exact_map_mkQ_range ι)
            (Submodule.mkQ_surjective _)).toLinearMap ∘ₗ
              (TensorProduct.mk 𝕜 _ _).flip (exteriorPower.ιMulti 𝕜 _ (Module.finBasis 𝕜 _))) := by
  have := finite_ker_of_isInvertible_prod h
  set bG := Module.finBasis 𝕜 G
  set bW := Module.finBasis 𝕜 (Λ' ⧸ LinearMap.range ι)
  -- Kernel vectors of the larger stabilization lifting `lift`.
  let wv (j : Fin (finrank 𝕜 (Λ' ⧸ LinearMap.range ι))) : (A.coprod D₂').ker :=
    ⟨_, mem_ker_coprod_kerSection hι h (lift j)⟩
  have hgv : ((LinearMap.range ι).mkQ ∘ₗ
      (parameterProj A D₂' : (A.coprod D₂').ker →ₗ[𝕜] Λ')) ∘ wv = bW := by
    funext j
    have hι0 : (LinearMap.range ι).mkQ (ι (q.kerSection (A.coprod D₂) (-D₂' (lift j))).2) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self ι _)
    simp only [LinearMap.coe_comp, Function.comp_apply, coe_coe, parameterProj_apply, wv]
    rw [map_add, hι0, add_zero]
    exact hlift j
  refine ⟨(kerEquivOfProd _ q' h').toLinearEquiv.symm.detLineCongr
    (TauCeti.detLineShortExactEquiv (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
      (surjective_mkQ_comp_parameterProj hι (surjective_of_isInvertible_prod h))
      ((kerEquivOfProd _ q h).toLinearEquiv.detLineCongr (exteriorPower.ιMulti 𝕜 _ bG) ⊗ₜ
        exteriorPower.ιMulti 𝕜 _ bW)),
    detLineCongr_detLineShortExactEquiv_ne_zero hι hι' h h' bG bW, ?_, fun φ ↦
      detLineChartEquiv_symm_tmul_nested hι hι' h h' _ _ φ⟩
  have hy := coe_detLineCongr_detLineShortExactEquiv_nested hι hι' h h' bG wv
  rw [hgv] at hy
  rw [hy, ← exteriorPower.ιMulti_apply_coe, bB.exteriorPower_ιMulti_eq_det_smul,
    Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
  simp only [kerCoordAppend, wv]

/-- **Transitions between nested kernel charts are analytic.** Let `(D₂, q)` and `(D₂', q')` be
kernel charts of the operator `A₀`, with the stabilizer `D₂ = D₂' ∘ ι` obtained from `D₂'` along an
injective `ι : Λ → Λ'`. Then there is a function `c` of the operator such that, at every operator
`A` where both charts are valid, `c` is analytic (`C^ω`) and nonzero at `A`, and the transition
from the
second chart to the first at `A` is `c A` times the transition at `A₀`. -/
theorem exists_contDiffAt_detLineChartEquiv_symm_eq_smul_of_comp
    (hι : ∀ l, D₂' (ι l) = D₂ l) (hι' : Function.Injective ι) {A₀ : E →L[𝕜] F}
    (h₀ : ((A₀.coprod D₂).prod q).IsInvertible) (h₀' : ((A₀.coprod D₂').prod q').IsInvertible) :
    ∃ c : (E →L[𝕜] F) → 𝕜, ∀ A (h : ((A.coprod D₂).prod q).IsInvertible)
      (h' : ((A.coprod D₂').prod q').IsInvertible), ContDiffAt 𝕜 ω c A ∧ c A ≠ 0 ∧ ∀ v,
        detLineChartEquiv A D₂ q h ((detLineChartEquiv A D₂' q' h').symm v) =
          c A • detLineChartEquiv A₀ D₂ q h₀ ((detLineChartEquiv A₀ D₂' q' h₀').symm v) := by
  set W := Λ' ⧸ LinearMap.range ι
  -- Fixed data: lifts of a basis of `W` to `Λ'`, and a basis of `G'`.
  let lift : Fin (finrank 𝕜 W) → Λ' := fun j ↦
    Function.surjInv (Submodule.mkQ_surjective (LinearMap.range ι)) (Module.finBasis 𝕜 W j)
  have hlift (j) : (LinearMap.range ι).mkQ (lift j) = Module.finBasis 𝕜 W j :=
    Function.surjInv_eq (Submodule.mkQ_surjective _) _
  let bB : Module.Basis (Fin (finrank 𝕜 G + finrank 𝕜 W)) 𝕜 G' := Module.finBasisOfFinrankEq 𝕜 G'
    (finrank_eq_finrank_add_finrank_quotient hι hι' h₀ h₀')
  -- The transition is `c₀ A₀ / c₀ A` times its value at `A₀`.
  set c₀ : (E →L[𝕜] F) → 𝕜 := fun A ↦
    bB.det (kerCoordAppend A D₂ q D₂' q' ι (Module.finBasis 𝕜 G) lift)
  obtain ⟨y₀, hy₀, hyc₀, hM₀⟩ :=
    exists_detLineChartEquiv_symm_tmul_nested hι hι' h₀ h₀' bB lift hlift
  have hc0 {A : E →L[𝕜] F} {y : TauCeti.detLine 𝕜 G'} (hy : y ≠ 0)
      (hyc : (y : ExteriorAlgebra 𝕜 G') = c₀ A • ExteriorAlgebra.ιMulti 𝕜 _ bB) : c₀ A ≠ 0 :=
    fun hc ↦ hy (Subtype.ext (by rw [hyc, hc, zero_smul, ZeroMemClass.coe_zero]))
  refine ⟨fun A ↦ c₀ A₀ / c₀ A, fun A h h' ↦ ?_⟩
  obtain ⟨y, hy, hyc, hM⟩ := exists_detLineChartEquiv_symm_tmul_nested hι hι' h h' bB lift hlift
  refine ⟨contDiffAt_const.div (contDiffAt_det_kerCoordAppend h bB _ lift) (hc0 hy hyc),
    div_ne_zero (hc0 hy₀ hyc₀) (hc0 hy hyc), fun v ↦ ?_⟩
  -- The transition is constant on `y ⊗ φ`, and `det G'` is spanned by `y₀`.
  let e (A : E →L[𝕜] F) (h : ((A.coprod D₂).prod q).IsInvertible)
      (h' : ((A.coprod D₂').prod q').IsInvertible) :=
    (detLineChartEquiv A D₂' q' h').symm ≪≫ₗ detLineChartEquiv A D₂ q h
  have key : (e A h h').toLinearMap = (c₀ A₀ / c₀ A) • (e A₀ h₀ h₀').toLinearMap :=
    TauCeti.eq_smul_of_tmul_eq_tmul (N := Dual 𝕜 (TauCeti.detLine 𝕜 Λ'))
      (P := TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) (y := y)
      (TauCeti.finrank_detLine 𝕜 G') hy₀
      (Subtype.ext (by
        rw [Submodule.coe_smul, hyc, hyc₀, smul_smul, div_mul_cancel₀ _ (hc0 hy hyc)]))
      fun n ↦ (hM n).trans (hM₀ n).symm
  simpa [e] using LinearMap.congr_fun key v

variable {Λ₃ G₃ : Type*} [NormedAddCommGroup Λ₃] [NormedSpace 𝕜 Λ₃] [FiniteDimensional 𝕜 Λ₃]
  [NormedAddCommGroup G₃] [NormedSpace 𝕜 G₃] [FiniteDimensional 𝕜 G₃]
  {D₃ : Λ₃ →L[𝕜] F} {q₃ : E × Λ₃ →L[𝕜] G₃}

/-- **Transitions between kernel charts are analytic.** Let `(D₂, q)` and `(D₃, q₃)` be kernel
charts of the operator `A₀`. Then there is a function `c` of the operator such that, at every
operator `A` where both charts are valid, `c` is analytic (`C^ω`) and nonzero at `A`, and the
transition from the second chart to the first at `A` is `c A` times the transition at `A₀`. These
are the transition functions of the determinant line bundle, as functions of the operator; along a
family of operators they have the regularity of the family
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`,
`ContinuousLinearMap.exists_contDiffOn_detLineChartEquiv_symm_eq_smul`). -/
theorem exists_contDiffAt_detLineChartEquiv_symm_eq_smul {A₀ : E →L[𝕜] F}
    (h₀ : ((A₀.coprod D₂).prod q).IsInvertible) (h₀₃ : ((A₀.coprod D₃).prod q₃).IsInvertible) :
    ∃ c : (E →L[𝕜] F) → 𝕜, ∀ A (h : ((A.coprod D₂).prod q).IsInvertible)
      (h₃ : ((A.coprod D₃).prod q₃).IsInvertible), ContDiffAt 𝕜 ω c A ∧ c A ≠ 0 ∧ ∀ v,
        detLineChartEquiv A D₂ q h ((detLineChartEquiv A D₃ q₃ h₃).symm v) =
          c A • detLineChartEquiv A₀ D₂ q h₀ ((detLineChartEquiv A₀ D₃ q₃ h₀₃).symm v) := by
  -- Both charts are compared with the chart of the sum `D₂.coprod D₃` of the stabilizers.
  let q'' : E × Λ × Λ₃ →L[𝕜] G × Λ₃ := (q.prodMap (ContinuousLinearMap.id 𝕜 Λ₃)) ∘L
    (ContinuousLinearEquiv.prodAssoc 𝕜 E Λ Λ₃).symm.toContinuousLinearMap
  obtain ⟨c₁, hc₁⟩ := exists_contDiffAt_detLineChartEquiv_symm_eq_smul_of_comp
    (ι := LinearMap.inl 𝕜 Λ Λ₃) (D₂' := D₂.coprod D₃) (q' := q'') (fun _ ↦ by simp)
    LinearMap.inl_injective h₀ (h₀.prod_coprod_coprod D₃)
  obtain ⟨c₂, hc₂⟩ := exists_contDiffAt_detLineChartEquiv_symm_eq_smul_of_comp
    (ι := LinearMap.inr 𝕜 Λ Λ₃) (D₂' := D₂.coprod D₃) (q' := q'') (fun _ ↦ by simp)
    LinearMap.inr_injective h₀₃ (h₀.prod_coprod_coprod D₃)
  refine ⟨fun A ↦ c₁ A / c₂ A, fun A h h₃ ↦ ?_⟩
  have h'' : (((A.coprod (D₂.coprod D₃)).prod q'')).IsInvertible := h.prod_coprod_coprod D₃
  obtain ⟨hd₁, hn₁, he₁⟩ := hc₁ A h h''
  obtain ⟨hd₂, hn₂, he₂⟩ := hc₂ A h₃ h''
  refine ⟨hd₁.div hd₂ hn₂, div_ne_zero hn₁ hn₂, fun v ↦ ?_⟩
  let M₁ (A : E →L[𝕜] F) (h : ((A.coprod D₂).prod q).IsInvertible) :=
    (detLineChartEquiv A (D₂.coprod D₃) q'' (h.prod_coprod_coprod D₃)).symm ≪≫ₗ
      detLineChartEquiv A D₂ q h
  let M₂ (A : E →L[𝕜] F) (h : ((A.coprod D₂).prod q).IsInvertible)
      (h₃ : ((A.coprod D₃).prod q₃).IsInvertible) :=
    (detLineChartEquiv A (D₂.coprod D₃) q'' (h.prod_coprod_coprod D₃)).symm ≪≫ₗ
      detLineChartEquiv A D₃ q₃ h₃
  have := LinearEquiv.apply_symm_eq_div_smul (M₁ A h) (M₁ A₀ h₀) (M₂ A h h₃) (M₂ A₀ h₀ h₀₃) he₁ he₂
    hn₂ v
  simpa only [M₁, M₂, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using this

section Family

variable {X : Type*} [TopologicalSpace X] {T : X → E →L[𝕜] F}

/-- **Transitions between nested kernel charts are continuous.** Let `T` be a continuous family
of operators, and `(D₂, q)` and `(D₂', q')` kernel charts of `T x` at every parameter `x`, with the
stabilizer `D₂ = D₂' ∘ ι` obtained from `D₂'` along an injective `ι : Λ → Λ'`. Then, relative to
its value at any base point `x₀`, the transition from the second chart to the first is
multiplication by a continuous nowhere-vanishing function. -/
theorem exists_continuous_detLineChartEquiv_symm_eq_smul_of_comp (hT : Continuous T)
    (hι : ∀ l, D₂' (ι l) = D₂ l) (hι' : Function.Injective ι)
    (h : ∀ x, (((T x).coprod D₂).prod q).IsInvertible)
    (h' : ∀ x, (((T x).coprod D₂').prod q').IsInvertible) (x₀ : X) :
    ∃ c : X → 𝕜, Continuous c ∧ (∀ x, c x ≠ 0) ∧ ∀ x v,
      detLineChartEquiv (T x) D₂ q (h x) ((detLineChartEquiv (T x) D₂' q' (h' x)).symm v) =
        c x • detLineChartEquiv (T x₀) D₂ q (h x₀)
          ((detLineChartEquiv (T x₀) D₂' q' (h' x₀)).symm v) := by
  obtain ⟨c, hc⟩ := exists_contDiffAt_detLineChartEquiv_symm_eq_smul_of_comp hι hι' (h x₀) (h' x₀)
  exact ⟨fun x ↦ c (T x), continuous_iff_continuousAt.2 fun x ↦
    (hc _ (h x) (h' x)).1.continuousAt.comp hT.continuousAt, fun x ↦ (hc _ (h x) (h' x)).2.1,
    fun x ↦ (hc _ (h x) (h' x)).2.2⟩

/-- **Transitions between kernel charts are continuous.** Let `T` be a continuous family of
operators, and `(D₂, q)` and `(D₃, q₃)` kernel charts of `T x` at every parameter `x`. Then,
relative to its value at any base point `x₀`, the transition from the second chart to the first
is multiplication by a continuous nowhere-vanishing function. These are the transition functions of
the determinant line bundle of the family; to compare charts defined only on part of the parameter
space, apply this to the subtype on which both are defined. -/
theorem exists_continuous_detLineChartEquiv_symm_eq_smul (hT : Continuous T)
    (h : ∀ x, (((T x).coprod D₂).prod q).IsInvertible)
    (h₃ : ∀ x, (((T x).coprod D₃).prod q₃).IsInvertible) (x₀ : X) :
    ∃ c : X → 𝕜, Continuous c ∧ (∀ x, c x ≠ 0) ∧ ∀ x v,
      detLineChartEquiv (T x) D₂ q (h x) ((detLineChartEquiv (T x) D₃ q₃ (h₃ x)).symm v) =
        c x • detLineChartEquiv (T x₀) D₂ q (h x₀)
          ((detLineChartEquiv (T x₀) D₃ q₃ (h₃ x₀)).symm v) := by
  obtain ⟨c, hc⟩ := exists_contDiffAt_detLineChartEquiv_symm_eq_smul (h x₀) (h₃ x₀)
  exact ⟨fun x ↦ c (T x), continuous_iff_continuousAt.2 fun x ↦
    (hc _ (h x) (h₃ x)).1.continuousAt.comp hT.continuousAt, fun x ↦ (hc _ (h x) (h₃ x)).2.1,
    fun x ↦ (hc _ (h x) (h₃ x)).2.2⟩

end Family

/-- **Transitions between kernel charts have the regularity of the family.** Let `T` be a family of
operators which is `C^n` on a set `s` of a normed space, and `(D₂, q)` and `(D₃, q₃)` kernel charts
of `T x` at every `x ∈ s`. Then, relative to its value at any base point `x₀ ∈ s`, the transition
from the second chart to the first is multiplication by a function which is `C^n` on `s` and
nowhere zero there. -/
theorem exists_contDiffOn_detLineChartEquiv_symm_eq_smul {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {T : X → E →L[𝕜] F} {s : Set X} {n : ℕ∞ω} (hT : ContDiffOn 𝕜 n T s)
    (h : ∀ x ∈ s, (((T x).coprod D₂).prod q).IsInvertible)
    (h₃ : ∀ x ∈ s, (((T x).coprod D₃).prod q₃).IsInvertible) {x₀ : X} (hx₀ : x₀ ∈ s) :
    ∃ c : X → 𝕜, ContDiffOn 𝕜 n c s ∧ (∀ x ∈ s, c x ≠ 0) ∧ ∀ x (hx : x ∈ s) v,
      detLineChartEquiv (T x) D₂ q (h x hx) ((detLineChartEquiv (T x) D₃ q₃ (h₃ x hx)).symm v) =
        c x • detLineChartEquiv (T x₀) D₂ q (h x₀ hx₀)
          ((detLineChartEquiv (T x₀) D₃ q₃ (h₃ x₀ hx₀)).symm v) := by
  obtain ⟨c, hc⟩ := exists_contDiffAt_detLineChartEquiv_symm_eq_smul (h x₀ hx₀) (h₃ x₀ hx₀)
  exact ⟨fun x ↦ c (T x), fun x hx ↦
    ((hc _ (h x hx) (h₃ x hx)).1.of_le le_top).comp_contDiffWithinAt x (hT x hx),
    fun x hx ↦ (hc _ (h x hx) (h₃ x hx)).2.1, fun x hx ↦ (hc _ (h x hx) (h₃ x hx)).2.2⟩

variable [CompleteSpace F] in
/-- **Kernel charts near a Fredholm operator.** A Fredholm operator `A₀` has a kernel chart, with
stabilizer a finite-dimensional subspace `S` of the target and kernel coordinate `q`, which is
valid at every operator of an open neighbourhood of `A₀`. -/
theorem IsFredholm.exists_isOpen_kernelChart {A₀ : E →L[𝕜] F} (hF : IsFredholm A₀) :
    ∃ (S : Submodule 𝕜 F) (_ : FiniteDimensional 𝕜 S) (G : Submodule 𝕜 (E × S))
      (_ : FiniteDimensional 𝕜 G) (q : E × S →L[𝕜] G) (U : Set (E →L[𝕜] F)), IsOpen U ∧ A₀ ∈ U ∧
      ∀ A ∈ U, ((A.coprod S.subtypeL).prod q).IsInvertible := by
  obtain ⟨S, -, -, hS, q, U, hU, hxU, hinv⟩ :=
    IsFredholm.exists_stabilization_kernel_coordinates (T := fun A : E →L[𝕜] F ↦ A) hF
      continuousAt_id (D := ⊤) (by simp)
  have : FiniteDimensional 𝕜 (A₀.coprod S.subtypeL).ker :=
    (hF.coprod_of_finiteDimensional S.subtypeL).finite_ker
  exact ⟨S, hS, _, inferInstance, q, U, hU, hxU, hinv⟩

end Regularity

section Real

open Filter Topology

variable {E F Λ G Λ' G' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup Λ'] [NormedSpace ℝ Λ'] [FiniteDimensional ℝ Λ']
  [NormedAddCommGroup G'] [NormedSpace ℝ G'] [FiniteDimensional ℝ G']
  {D₂ : Λ →L[ℝ] F} {q : E × Λ →L[ℝ] G} {D₂' : Λ' →L[ℝ] F} {q' : E × Λ' →L[ℝ] G'}

/-- **Real kernel-chart transitions keep their sign nearby.** The transition between two real
kernel charts, both valid at the operator `A₀`, is at every operator `A` near `A₀` a positive
multiple of the same transition at `A₀`: its coefficient relative to the transition at `A₀` is
continuous in `A` and equal to `1` at `A₀`. -/
theorem eventually_detLineChartEquiv_symm_eq_smul {A₀ : E →L[ℝ] F}
    (h₀ : ((A₀.coprod D₂).prod q).IsInvertible) (h₀' : ((A₀.coprod D₂').prod q').IsInvertible) :
    ∀ᶠ A in 𝓝 A₀, ∃ (h : ((A.coprod D₂).prod q).IsInvertible)
      (h' : ((A.coprod D₂').prod q').IsInvertible) (c : ℝ), 0 < c ∧
      ∀ u, detLineChartEquiv A D₂ q h ((detLineChartEquiv A D₂' q' h').symm u) =
        c • detLineChartEquiv A₀ D₂ q h₀ ((detLineChartEquiv A₀ D₂' q' h₀').symm u) := by
  obtain ⟨U, hU, hxU, hUinv⟩ := exists_isOpen_isInvertible_prod (q := q)
    (continuous_id.continuousLinearMapCoprod (continuous_const (y := D₂))).continuousAt h₀
  obtain ⟨U', hU', hxU', hUinv'⟩ := exists_isOpen_isInvertible_prod (q := q')
    (continuous_id.continuousLinearMapCoprod (continuous_const (y := D₂'))).continuousAt h₀'
  set V := U ∩ U'
  have hV : IsOpen V := hU.inter hU'
  have hxV : A₀ ∈ V := ⟨hxU, hxU'⟩
  -- The transition on the open set `V` where both charts are valid, relative to its value at `A₀`.
  obtain ⟨c, hc, -, hcu⟩ := exists_continuous_detLineChartEquiv_symm_eq_smul
    (T := fun A : V ↦ (A : E →L[ℝ] F)) continuous_subtypeVal (fun A ↦ hUinv A A.property.1)
    (fun A ↦ hUinv' A A.property.2) ⟨A₀, hxV⟩
  -- At `A₀` the transition agrees with itself, so its relative coefficient `c` is `1` there.
  have hc1 : c ⟨A₀, hxV⟩ = 1 := by
    have : Nontrivial (TauCeti.detLine ℝ G' ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ Λ')) :=
      Module.nontrivial_of_finrank_eq_succ (n := 0) (by
        rw [Module.finrank_tensorProduct (R := ℝ) (S := ℝ), Subspace.dual_finrank_eq,
          TauCeti.finrank_detLine ℝ G', TauCeti.finrank_detLine ℝ Λ'])
    obtain ⟨u, hu⟩ := exists_ne (0 : TauCeti.detLine ℝ G' ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ Λ'))
    set B := detLineChartEquiv A₀ D₂ q h₀ ((detLineChartEquiv A₀ D₂' q' h₀').symm u)
    have hB : B ≠ 0 :=
      (LinearEquiv.map_ne_zero_iff _).2 ((LinearEquiv.map_ne_zero_iff _).2 hu)
    have h : B = c ⟨A₀, hxV⟩ • B := hcu ⟨A₀, hxV⟩ u
    exact ((smul_left_inj (R := ℝ)
      (M := TauCeti.detLine ℝ G ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ Λ)) hB).1
      ((one_smul ℝ B).trans h)).symm
  have hpos : ∀ᶠ A : V in 𝓝 ⟨A₀, hxV⟩, 0 < c A :=
    hc.continuousAt.eventually (lt_mem_nhds (by rw [hc1]; exact one_pos))
  have hpos' : ∀ᶠ A in 𝓝 A₀, ∀ hA : A ∈ V, 0 < c ⟨A, hA⟩ := by
    have := (eventually_nhds_subtype_iff V ⟨A₀, hxV⟩ (fun A ↦ ∀ hA : A ∈ V, 0 < c ⟨A, hA⟩)).1
      (hpos.mono fun A hA _ ↦ hA)
    rwa [hV.nhdsWithin_eq hxV] at this
  filter_upwards [hpos', hV.mem_nhds hxV] with A hcA hAV
  exact ⟨hUinv A hAV.1, hUinv' A hAV.2, c ⟨A, hAV⟩, hcA hAV, hcu ⟨A, hAV⟩⟩

end Real

section Moving

open Filter Topology

variable {E F Λ G X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace X]
  {T : X → E →L[ℝ] F} {D₂ : X → Λ →L[ℝ] F} {q : X → E × Λ →L[ℝ] G} {s : Set X} {x₀ : X}

/-- **Kernel charts with moving data.** Let `T` be a family of operators and `(D₂ x, q x)` a
kernel chart whose stabilizer and coordinate depend on the parameter, all continuous within `s`
at `x₀`. Near `x₀` the chart with the moving data reads the determinant line of `T x` as a
positive multiple of the chart with the data frozen at `x₀`. -/
theorem eventually_detLineChartEquiv_eq_smul (hT : ContinuousWithinAt T s x₀)
    (hD₂ : ContinuousWithinAt D₂ s x₀) (hq : ContinuousWithinAt q s x₀)
    (h₀ : (((T x₀).coprod (D₂ x₀)).prod (q x₀)).IsInvertible) :
    ∀ᶠ x in 𝓝[s] x₀, ∃ (h : (((T x).coprod (D₂ x)).prod (q x)).IsInvertible)
      (h' : (((T x).coprod (D₂ x₀)).prod (q x₀)).IsInvertible) (c : ℝ), 0 < c ∧
      ∀ y, detLineChartEquiv (T x) (D₂ x) (q x) h y =
        c • detLineChartEquiv (T x) (D₂ x₀) (q x₀) h' y := by
  have : CompleteSpace Λ := FiniteDimensional.completeSpace ℝ Λ
  have hA : ContinuousWithinAt (fun x ↦ (T x).coprod (D₂ x)) s x₀ :=
    hT.continuousLinearMapCoprod hD₂
  have hA₀ : ContinuousWithinAt (fun x ↦ (T x).coprod (D₂ x₀)) s x₀ :=
    hT.continuousLinearMapCoprod continuousWithinAt_const
  have hprod {B : X → E × Λ →L[ℝ] F} {r : X → E × Λ →L[ℝ] G} (hB : ContinuousWithinAt B s x₀)
      (hr : ContinuousWithinAt r s x₀) (hBr : ((B x₀).prod (r x₀)).IsInvertible) :
      ∀ᶠ x in 𝓝[s] x₀, ((B x).prod (r x)).IsInvertible :=
    ((prodL ℝ).continuous.continuousAt.comp_continuousWithinAt (hB.prodMk hr)).tendsto.eventually
      hBr.eventually_nhds
  -- The three pairs of the comparison are invertible near `x₀`.
  have ev₀ := hprod hA₀ continuousWithinAt_const h₀
  have ev₁ := hprod hA continuousWithinAt_const h₀
  have ev₂ := hprod hA hq h₀
  -- Moving the stabilizer from `D₂ x₀` to `D₂ x` is the cutoff change `D₂ x = D₂ x₀ + A₀ ∘ L x`,
  -- where `L x` is normalized by `q x₀`; it acts on the stabilizer by `Φ x = 1 + snd ∘ L x`.
  set L : X → Λ →L[ℝ] E × Λ :=
    fun x ↦ (q x₀).kerSection ((T x).coprod (D₂ x₀)) ∘L (D₂ x - D₂ x₀) with hL_def
  set Φ : X → Λ →L[ℝ] Λ := fun x ↦ ContinuousLinearMap.id ℝ Λ + snd ℝ E Λ ∘L L x with hΦ_def
  have hL : ContinuousWithinAt L s x₀ :=
    ((contDiffAt_kerSection (n := 0)
      (isInvertible_prod_comm.mp h₀)).continuousAt.comp_continuousWithinAt
        (f := fun x ↦ (q x₀, (T x).coprod (D₂ x₀))) (continuousWithinAt_const.prodMk hA₀)).clm_comp
      (hD₂.sub continuousWithinAt_const)
  have hΦ : ContinuousWithinAt (fun x ↦ (Φ x).det) s x₀ :=
    continuous_det.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_const.add (continuousWithinAt_const.clm_comp hL))
  have hΦ₀ : (Φ x₀).det = 1 := by
    simp [hΦ_def, hL_def, ContinuousLinearMap.det, LinearMap.det_id]
  -- Moving the coordinate from `q x₀` to `q x` acts on `G` by `K x = q x ∘ kerSection`.
  set K : X → G →L[ℝ] G := fun x ↦ q x ∘L ((T x).coprod (D₂ x)).kerSection (q x₀)
  have hK : ContinuousWithinAt (fun x ↦ (K x).det) s x₀ :=
    continuous_det.continuousAt.comp_continuousWithinAt (hq.clm_comp
      ((contDiffAt_kerSection (n := 0) h₀).continuousAt.comp_continuousWithinAt
        (f := fun x ↦ ((T x).coprod (D₂ x), q x₀)) (hA.prodMk continuousWithinAt_const)))
  have hK₀ : (K x₀).det = 1 := by
    have : K x₀ = ContinuousLinearMap.id ℝ G :=
      ContinuousLinearMap.ext fun g ↦ apply_kerSection_right h₀ g
    rw [this, ContinuousLinearMap.det, coe_id, LinearMap.det_id]
  have evΦ := hΦ.tendsto.eventually (lt_mem_nhds (hΦ₀ ▸ one_pos : (0 : ℝ) < (Φ x₀).det))
  have evK := hK.tendsto.eventually (lt_mem_nhds (hK₀ ▸ one_pos : (0 : ℝ) < (K x₀).det))
  filter_upwards [ev₀, ev₁, ev₂, evΦ, evK] with x h0x h1x h2x hΦx hKx
  refine ⟨h2x, h0x, (K x).det * (Φ x).det, mul_pos hKx hΦx, fun y ↦ ?_⟩
  rw [detLineChartEquiv_apply_eq_det_smul h1x h2x,
    detLineChartEquiv_apply_eq_det_smul_of_coprod_apply_eq_sub (L := L x)
      (fun l ↦ apply_kerSection_right (isInvertible_prod_comm.mp h0x) _)
      (fun l ↦ apply_kerSection _) h0x h1x, smul_smul]

end Moving

end ContinuousLinearMap
