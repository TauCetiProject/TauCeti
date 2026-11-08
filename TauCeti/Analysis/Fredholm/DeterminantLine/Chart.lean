/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Basic
public import TauCeti.Analysis.Normed.Operator.Splitting.Family
import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearEquiv.Basic

/-!
# Kernel charts of Fredholm determinant lines

The determinant lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of a continuous family of Fredholm
operators `T x : E →L[𝕜] F` form a line bundle over the parameter space, although kernel and
cokernel jump. This file constructs its local trivializations and proves that they are
compatible: their transition functions are continuous and nowhere zero. Assembling the bundle
itself from these charts, and the orientation transport it supports, are not done here.

A *kernel chart* is a finite stabilization `D₂ : Λ →L[𝕜] F`, with `Λ` finite-dimensional,
together with a kernel coordinate `q : E × Λ →L[𝕜] G`, with `G` finite-dimensional, for which the
pair `((T.coprod D₂).prod q)` is invertible. Then `T.coprod D₂` is onto and `q` identifies its
kernel with `G`, so the normalized stabilization isomorphism
`ContinuousLinearMap.detLineStabilizationEquiv` followed by `q` identifies the determinant line of
`T` with the fixed line `det G ⊗ (det Λ)^*` (`ContinuousLinearMap.detLineChartEquiv`).
Invertibility of the pair is an open condition on `T`, and
`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates` supplies such a chart near
every Fredholm operator, so the kernel charts of a family cover the parameter space.

Over parameters where two kernel charts are both defined, the transition from one to the other is
an isomorphism between two fixed lines, so it is multiplication by a scalar relative to its value
at any base point `x₀`. The main theorem,
`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`, says that this scalar is a
continuous nowhere-vanishing function of the parameter. Two charts are compared through their sum
`D₂.coprod D₃` (`ContinuousLinearMap.IsInvertible.prod_coprod_coprod`), and the essential case
is that of nested stabilizers, `D₂ = D₂' ∘ ι`
(`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul_of_comp`). There the
transition is the change of stabilizer `ContinuousLinearMap.detLineCoprodMapEquiv`, which is
constant on exterior products of suitable bases. These bases are a fixed basis of `G`
transported by the kernel section of `q`, followed by kernel vectors of the larger stabilization
lifting a fixed basis of `Λ' ⧸ range ι`, obtained from the right inverse normalized by `q`. Both
depend continuously on the operator, and the transition coefficient is the inverse of the
determinant of their `q'`-coordinates, up to a constant.

## Main definitions

* `ContinuousLinearMap.detLineChartEquiv`: the kernel chart `det T ≃ det G ⊗ (det Λ)^*` of the
  determinant line of `T` given by a stabilization `D₂` and kernel coordinate `q`.

## Main results

* `ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul_of_comp`: transitions
  between the kernel charts of nested stabilizers are continuous and nowhere zero.
* `ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`: the same for any two
  kernel charts.

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
  rw [LinearEquiv.coe_detLineCongr, TauCeti.coe_detLineShortExactEquiv_tmul_eq_map_mul,
    LinearEquiv.coe_detLineCongr, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
    map_mul, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
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
  -- Two nonzero vectors of lines have nonzero tensor product.
  have htm := ((FiniteDimensional.basisSingleton Unit (TauCeti.finrank_detLine 𝕜 _) _
    ha).tensorProduct
    (FiniteDimensional.basisSingleton Unit (TauCeti.finrank_detLine 𝕜 _) _ hc)).ne_zero ((), ())
  rw [Module.Basis.tensorProduct_apply, FiniteDimensional.basisSingleton_apply,
    FiniteDimensional.basisSingleton_apply] at htm
  exact (LinearEquiv.map_ne_zero_iff _).2 ((LinearEquiv.map_ne_zero_iff _).2 htm)

end Nested

end Chart

section Continuity

variable {𝕜 E Λ Λ' F G G' X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
  [NormedAddCommGroup Λ'] [NormedSpace 𝕜 Λ'] [FiniteDimensional 𝕜 Λ']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] [FiniteDimensional 𝕜 G']
  [TopologicalSpace X] {T : X → E →L[𝕜] F}
  {D₂ : Λ →L[𝕜] F} {D₂' : Λ' →L[𝕜] F} {q : E × Λ →L[𝕜] G} {q' : E × Λ' →L[𝕜] G'}
  {ι : Λ →ₗ[𝕜] Λ'}

omit [FiniteDimensional 𝕜 Λ'] [FiniteDimensional 𝕜 G] in
/-- The determinant, against a fixed basis of `G'`, of the `q'`-coordinates of the kernel vectors
of the larger stabilization used to compare two nested kernel charts depends continuously on the
operator. -/
private theorem continuous_det_append_kerSection (hT : Continuous T)
    (h : ∀ x, (((T x).coprod D₂).prod q).IsInvertible) {k m : ℕ}
    (bB : Module.Basis (Fin (k + m)) 𝕜 G') (b : Fin k → G) (lift : Fin m → Λ') :
    Continuous fun x ↦ bB.det (kerCoordAppend (T x) D₂ q D₂' q' ι b lift) := by
  have : CompleteSpace Λ := FiniteDimensional.complete 𝕜 Λ
  have hA : Continuous fun x ↦ (T x).coprod D₂ := hT.continuousLinearMapCoprod continuous_const
  have hιc : Continuous ι := ι.continuous_of_finiteDimensional
  have hks : Continuous fun x ↦ ((T x).coprod D₂).kerSection q := continuous_kerSection hA h
  have hrc : Continuous fun x ↦ q.kerSection ((T x).coprod D₂) :=
    continuous_const.kerSection hA fun x ↦ isInvertible_prod_comm.mp (h x)
  have hfam : Continuous fun x ↦ kerCoordAppend (T x) D₂ q D₂' q' ι b lift := by
    refine continuous_pi fun i ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
    · simp only [kerCoordAppend, Fin.append_left]
      have := hks.clm_apply (continuous_const (y := b i))
      fun_prop
    · simp only [kerCoordAppend, Fin.append_right]
      have := hrc.clm_apply (continuous_const (y := -D₂' (lift j)))
      fun_prop
  simp only [Module.Basis.det_apply]
  refine Continuous.matrix_det (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_)
  simpa only [Module.Basis.toMatrix_apply, Function.comp_def, Module.Basis.coord_apply] using
    (bB.coord i).continuous_of_finiteDimensional.comp ((continuous_apply j).comp hfam)

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
  set W := Λ' ⧸ LinearMap.range ι
  have hfd (x) : FiniteDimensional 𝕜 ((T x).coprod D₂).ker := finite_ker_of_isInvertible_prod (h x)
  -- Fixed data: bases of `G` and `W`, lifts of the latter to `Λ'`, and a basis of `G'`.
  let bG := Module.finBasis 𝕜 G
  let bW := Module.finBasis 𝕜 W
  let lift : Fin (finrank 𝕜 W) → Λ' := fun j ↦
    Function.surjInv (Submodule.mkQ_surjective (LinearMap.range ι)) (bW j)
  let bB : Module.Basis (Fin (finrank 𝕜 G + finrank 𝕜 W)) 𝕜 G' := Module.finBasisOfFinrankEq 𝕜 G'
    (finrank_eq_finrank_add_finrank_quotient hι hι' (h x₀) (h' x₀))
  -- Kernel vectors of the larger stabilization lifting `lift`, continuous in `x`.
  let wv (x : X) (j : Fin (finrank 𝕜 W)) : ((T x).coprod D₂').ker :=
    ⟨_, mem_ker_coprod_kerSection hι (h x) (lift j)⟩
  have hgv (x) : ((LinearMap.range ι).mkQ ∘ₗ
      (parameterProj (T x) D₂' : ((T x).coprod D₂').ker →ₗ[𝕜] Λ')) ∘ wv x = bW := by
    funext j
    have hι0 : (LinearMap.range ι).mkQ
        (ι (q.kerSection ((T x).coprod D₂) (-D₂' (lift j))).2) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self ι _)
    simp only [LinearMap.coe_comp, Function.comp_apply, coe_coe, parameterProj_apply, wv]
    rw [map_add, hι0, add_zero]
    exact Function.surjInv_eq (Submodule.mkQ_surjective _) _
  -- The elements `y x` of `det G'`, on which the transition is constant, are the multiples
  -- `c₀ x` of a fixed generator, with `c₀` continuous.
  let y (x : X) : TauCeti.detLine 𝕜 G' :=
    have := hfd x
    (kerEquivOfProd _ q' (h' x)).toLinearEquiv.symm.detLineCongr
      (TauCeti.detLineShortExactEquiv (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
        (surjective_mkQ_comp_parameterProj hι (surjective_of_isInvertible_prod (h x)))
        ((kerEquivOfProd _ q (h x)).toLinearEquiv.detLineCongr (exteriorPower.ιMulti 𝕜 _ bG) ⊗ₜ
          exteriorPower.ιMulti 𝕜 _ bW))
  have hc := continuous_det_append_kerSection (q' := q') (ι := ι) (D₂' := D₂') hT h bB bG lift
  set c₀ : X → 𝕜 := fun x ↦ bB.det (kerCoordAppend (T x) D₂ q D₂' q' ι bG lift)
  have hyc (x) : (y x : ExteriorAlgebra 𝕜 G') = c₀ x • ExteriorAlgebra.ιMulti 𝕜 _ bB := by
    have := hfd x
    have hy := coe_detLineCongr_detLineShortExactEquiv_nested hι hι' (h x) (h' x) bG (wv x)
    rw [hgv x] at hy
    rw [hy, ← exteriorPower.ιMulti_apply_coe, bB.exteriorPower_ιMulti_eq_det_smul,
      Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
    simp only [c₀, kerCoordAppend, wv, W]
  have hy0 (x) : y x ≠ 0 :=
    have := hfd x
    detLineCongr_detLineShortExactEquiv_ne_zero hι hι' (h x) (h' x) bG bW
  -- The transition from the larger chart to the smaller one.
  let e (x : X) := (detLineChartEquiv (T x) D₂' q' (h' x)).symm ≪≫ₗ
    detLineChartEquiv (T x) D₂ q (h x)
  have hM (x) (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ')) :
      (e x).toLinearMap (y x ⊗ₜ φ) =
      exteriorPower.ιMulti 𝕜 _ bG ⊗ₜ (φ ∘ₗ (TauCeti.detLineShortExactEquiv hι'
        (LinearMap.exact_map_mkQ_range ι) (Submodule.mkQ_surjective _)).toLinearMap ∘ₗ
          (TensorProduct.mk 𝕜 _ _).flip (exteriorPower.ιMulti 𝕜 _ bW)) :=
    have := hfd x
    detLineChartEquiv_symm_tmul_nested hι hι' (h x) (h' x) (exteriorPower.ιMulti 𝕜 _ bG)
      (exteriorPower.ιMulti 𝕜 _ bW) φ
  clear_value y c₀
  have hc0 (x) : c₀ x ≠ 0 := fun hc ↦
    hy0 x (Subtype.ext (by rw [hyc, hc, zero_smul, ZeroMemClass.coe_zero]))
  refine ⟨fun x ↦ c₀ x₀ / c₀ x, continuous_const.div hc hc0,
    fun x ↦ div_ne_zero (hc0 x₀) (hc0 x), fun x v ↦ ?_⟩
  -- The transition is constant on `y x ⊗ φ`, and `det G'` is spanned by `y x₀`.
  have key : (e x).toLinearMap = (c₀ x₀ / c₀ x) • (e x₀).toLinearMap :=
    TauCeti.eq_smul_of_tmul_eq_tmul (N := Dual 𝕜 (TauCeti.detLine 𝕜 Λ'))
      (P := TauCeti.detLine 𝕜 G ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) (y := y x)
      (TauCeti.finrank_detLine 𝕜 G') (hy0 x₀)
      (Subtype.ext (by rw [Submodule.coe_smul, hyc, hyc, smul_smul, div_mul_cancel₀ _ (hc0 x)]))
      fun n ↦ (hM x n).trans (hM x₀ n).symm
  simpa [e] using LinearMap.congr_fun key v

variable {Λ₃ G₃ : Type*} [NormedAddCommGroup Λ₃] [NormedSpace 𝕜 Λ₃] [FiniteDimensional 𝕜 Λ₃]
  [NormedAddCommGroup G₃] [NormedSpace 𝕜 G₃] [FiniteDimensional 𝕜 G₃]
  {D₃ : Λ₃ →L[𝕜] F} {q₃ : E × Λ₃ →L[𝕜] G₃}

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
  let q'' : E × Λ × Λ₃ →L[𝕜] G × Λ₃ := (q.prodMap (ContinuousLinearMap.id 𝕜 Λ₃)) ∘L
    (ContinuousLinearEquiv.prodAssoc 𝕜 E Λ Λ₃).symm.toContinuousLinearMap
  have h'' (x) : (((T x).coprod (D₂.coprod D₃)).prod q'').IsInvertible :=
    (h x).prod_coprod_coprod D₃
  obtain ⟨c₁, hc₁, hc₁0, h₁⟩ := exists_continuous_detLineChartEquiv_symm_eq_smul_of_comp hT
    (ι := LinearMap.inl 𝕜 Λ Λ₃) (fun _ ↦ by simp) LinearMap.inl_injective h h'' x₀
  obtain ⟨c₂, hc₂, hc₂0, h₂⟩ := exists_continuous_detLineChartEquiv_symm_eq_smul_of_comp hT
    (ι := LinearMap.inr 𝕜 Λ Λ₃) (fun _ ↦ by simp) LinearMap.inr_injective h₃ h'' x₀
  refine ⟨fun x ↦ c₁ x / c₂ x, hc₁.div hc₂ hc₂0, fun x ↦ div_ne_zero (hc₁0 x) (hc₂0 x),
    fun x v ↦ ?_⟩
  let M₁ (x : X) := (detLineChartEquiv (T x) (D₂.coprod D₃) q'' (h'' x)).symm ≪≫ₗ
    detLineChartEquiv (T x) D₂ q (h x)
  let M₂ (x : X) := (detLineChartEquiv (T x) (D₂.coprod D₃) q'' (h'' x)).symm ≪≫ₗ
    detLineChartEquiv (T x) D₃ q₃ (h₃ x)
  have := LinearEquiv.apply_symm_eq_div_smul (M₁ x) (M₁ x₀) (M₂ x) (M₂ x₀) (h₁ x) (h₂ x) (hc₂0 x) v
  simpa only [M₁, M₂, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using this

end Continuity

end ContinuousLinearMap
