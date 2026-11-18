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
* `ContinuousLinearMap.IsFredholm.exists_isOpen_kernelChart`: a Fredholm operator has a kernel
  chart valid on an open neighbourhood.
* `ContinuousLinearMap.eventually_detLineChartEquiv_symm_eq_smul`: over `ℝ`, the transition between
  two kernel charts valid at an operator is, nearby, a positive multiple of its value there.

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
    (T := fun A : V ↦ (A : E →L[ℝ] F)) continuous_subtype_val (fun A ↦ hUinv A A.2.1)
    (fun A ↦ hUinv' A A.2.2) ⟨A₀, hxV⟩
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

end ContinuousLinearMap
