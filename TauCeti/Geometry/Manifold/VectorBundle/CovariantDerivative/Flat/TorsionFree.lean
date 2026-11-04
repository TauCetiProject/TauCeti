/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Flat.Basic
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField

/-!
# Integrating dual coframes of torsion-free local parallel frames

Let `∇` be a covariant derivative on the tangent bundle of a finite-dimensional Hausdorff smooth
real manifold `M`, and let `{s i}` be a smooth local `∇`-parallel frame on an open neighbourhood
`W` of `x₀` on which `∇` has vanishing torsion (`∀ y ∈ W, ∇.torsion y = 0`). Given any family of
vectors `v : ι → F` in a Banach space `F`, the unique smooth `F`-valued `1`-form `ω` taking the
constant value `v i` on `s i` near `x₀` is closed near `x₀`: on frame vectors, the invariant
exterior-derivative formula (`TauCeti.mextDeriv_apply_one`) gives

`dω(sᵢ, sⱼ) = sᵢ(ω(sⱼ)) - sⱼ(ω(sᵢ)) - ω([sᵢ, sⱼ])`
`= 0 - 0 - ω(∇_{sᵢ} sⱼ - ∇_{sⱼ} sᵢ - T(sᵢ, sⱼ)) = 0`.

Applying the manifold Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`) produces a globally smooth
map `f : M → F` vanishing at `x₀` whose differential satisfies `df_y (s i y) = v i` for every `y` in
a neighbourhood of `x₀`. Boundary and corner points are permitted here; boundarylessness is only
needed earlier when constructing `{s i}` via Frobenius integrability, or later when inverting `df`
via the manifold inverse function theorem.

## Main results

* `CovariantDerivative.exists_contMDiff_mfderiv_parallel_frame_eq`: around `x₀`, any smooth local
  parallel frame of a torsion-free connection integrates to a smooth `F`-valued map vanishing at
  `x₀` whose differential sends the frame vectors to prescribed vectors in `F`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Theorem 7.10.
* M. Spivak, *A Comprehensive Introduction to Differential Geometry*, Vol. II, 3rd ed., Publish or
  Perish (1999), Chapter 4D.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Module Set Topology VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*}

/-- **Integrating the dual coframe of a torsion-free local parallel frame.** Let `{s i}` be a smooth
local frame of `TangentSpace I` on an open neighbourhood `W` of `x₀` such that `cov (s i) y = 0` and
`cov.torsion y = 0` for all `y ∈ W`. Then for any `v : ι → F` into a complete normed real vector
space `F`, there exists a globally smooth map `f : M → F` with `f x₀ = 0` whose differential sends
`s i y` to `v i` for all `y` in a neighbourhood of `x₀`. -/
theorem exists_contMDiff_mfderiv_parallel_frame_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {s : ι → Π x : M, TangentSpace I x} {W : Set M} (hW : IsOpen W) {x₀ : M} (hx₀W : x₀ ∈ W)
    (hs : IsLocalFrameOn I E ∞ s W) (hpar : ∀ y ∈ W, ∀ i, cov (s i) y = 0)
    (htors : ∀ y ∈ W, cov.torsion y = 0) (v : ι → F) :
    ∃ U ∈ 𝓝 x₀, ∃ f : M → F, CMDiff ∞ f ∧ f x₀ = 0 ∧
      ∀ y ∈ U, ∀ i, mfderiv I 𝓘(ℝ, F) f y (s i y) = v i := by
  classical
  let _ : Fintype ι := hs.fintypeOfFiniteDimensional hx₀W
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let eT := trivializationAt E (TangentSpace I) x₀
  have hx₀T : x₀ ∈ eT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  let bE : Basis ι ℝ E := (hs.toBasisAt hx₀W).map (eT.linearEquivAt ℝ x₀ hx₀T)
  -- Express `{s i y}` in `eT` as a continuous linear operator `S y : E →L[ℝ] E` equal to `id` at
  -- `x₀`, hence invertible on an open neighbourhood `W₀ ⊆ W ∩ eT.baseSet` of `x₀`.
  let S : M → E →L[ℝ] E := fun y ↦
    ∑ i, (bE.coord i).toContinuousLinearMap.smulRight (eT ⟨y, s i y⟩).2
  have hS_smooth : CMDiff[W ∩ eT.baseSet] ∞ S := by
    refine contMDiffOn_finsetSum fun i _ ↦ ?_
    refine (ContinuousLinearMap.smulRightL ℝ E E
      (bE.coord i).toContinuousLinearMap).contDiff.contMDiff.comp_contMDiffOn ?_
    exact ((eT.contMDiffOn_iff fun y (hy : y ∈ W ∩ eT.baseSet) ↦ eT.mem_source.mpr hy.2).1
      ((hs.contMDiffOn i).mono inter_subset_left)).2
  have hS₀ : S x₀ = ContinuousLinearMap.id ℝ E := by
    refine ContinuousLinearMap.coe_injective (bE.ext fun j ↦ ?_)
    have heval : (eT ⟨x₀, s j x₀⟩).2 = bE j := by
      simp [bE, Bundle.Trivialization.linearEquivAt_apply]
    simp [S, Basis.coord_apply, Finsupp.single_apply, heval]
  have hS_inv : ∀ᶠ y in 𝓝 x₀, (S y).IsInvertible := by
    have hid : (ContinuousLinearMap.id ℝ E).IsInvertible :=
      ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
    have hcont : ContinuousAt S x₀ :=
      hS_smooth.continuousOn.continuousAt ((hW.inter eT.open_baseSet).mem_nhds ⟨hx₀W, hx₀T⟩)
    exact hcont.eventually (hS₀.symm ▸ hid.eventually_nhds)
  obtain ⟨W₀, hW₀_sub, hW₀_open, hx₀W₀⟩ := mem_nhds_iff.mp
    (Filter.inter_mem ((hW.inter eT.open_baseSet).mem_nhds ⟨hx₀W, hx₀T⟩) hS_inv)
  -- Build the local linear map `L y : E →L[ℝ] F` sending `(eT ⟨y, s i y⟩).2` to `v i` on `W₀`.
  let T₀ : E →L[ℝ] F := ∑ i, (bE.coord i).toContinuousLinearMap.smulRight (v i)
  let L : M → E →L[ℝ] F := fun y ↦ T₀.comp (S y).inverse
  have hL_smooth : CMDiff[W₀] ∞ L := by
    intro y hy
    have hinv_at : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (S y) :=
      (hW₀_sub hy).2.contDiffAt_map_inverse
    have hS_at : CMDiffAt ∞ S y :=
      (hS_smooth.mono fun z hz ↦ (hW₀_sub hz).1).contMDiffAt (hW₀_open.mem_nhds hy)
    have hinv_m : CMDiffAt ∞ (fun z ↦ (S z).inverse) y := hinv_at.contMDiffAt.comp y hS_at
    exact (((ContinuousLinearMap.compL ℝ E E F T₀).contDiff.contDiffAt).contMDiffAt.comp y
      hinv_m).contMDiffWithinAt
  -- Read `L` back through `eT` as a smooth local section `α₀` of `Hom(TM, M × F)` on `W₀`.
  let α₀ : Π y : M, TangentSpace I y →L[ℝ] Bundle.Trivial M F y := fun y ↦
    (L y).comp (eT.continuousLinearMapAt ℝ y)
  have hα₀_apply {y : M} (hy : y ∈ W₀) (i : ι) : (α₀ y (s i y) : F) = v i := by
    obtain ⟨⟨-, hyT⟩, hyInv⟩ := hW₀_sub hy
    have hSi : S y (bE i) = (eT ⟨y, s i y⟩).2 := by
      simp [S, Basis.coord_apply, Finsupp.single_apply]
    have hinvi : (S y).inverse ((eT ⟨y, s i y⟩).2) = bE i := by
      rw [← hSi]
      exact DFunLike.congr_fun hyInv.inverse_comp_self (bE i)
    -- `Bundle.Trivial M F y` is definitionally `F`, so unfold `α₀ y` before rewriting in `eT`.
    change T₀ ((S y).inverse (eT.continuousLinearMapAt ℝ y (s i y))) = v i
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ eT hyT, hinvi]
    simp [T₀, Basis.coord_apply, Finsupp.single_apply]
  have hα₀_smooth : CMDiff[W₀] ∞ (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] Bundle.Trivial M F y) y (α₀ y)) := by
    let eF := trivializationAt F (Bundle.Trivial M F) x₀
    let eh := eT.continuousLinearMap (RingHom.id ℝ) eF
    refine (eh.contMDiffOn_iff fun y (hy : y ∈ W₀) ↦ ?_).2 ⟨contMDiffOn_id, ?_⟩
    · exact eh.mem_source.mpr ⟨(hW₀_sub hy).1.2, mem_univ y⟩
    · refine hL_smooth.congr fun y hy ↦ ?_
      have hyT : y ∈ eT.baseSet := (hW₀_sub hy).1.2
      ext w
      simp [eh, α₀, eF, Bundle.Trivialization.continuousLinearMap_apply,
        eT.continuousLinearMapAt_symmL hyT]
  -- Cut both `α₀` and `{s i}` off by a smooth bump function supported in `W₀`.
  obtain ⟨χ, -, hχW₀⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp (hW₀_open.mem_nhds hx₀W₀)
  let α : Π y : M, TangentSpace I y →L[ℝ] F := fun y ↦ χ y • α₀ y
  have hα_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y : M ↦ TangentSpace I y →L[ℝ] F) y (α y)) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hW₀_open hχW₀ hα₀_smooth
  let s' : ι → Π y : M, TangentSpace I y := fun i y ↦ χ y • s i y
  have hs'_smooth (i : ι) : CMDiff ∞ (T% (s' i)) :=
    χ.contMDiff.contMDiffOn.smul_section_of_tsupport hW₀_open hχW₀
      ((hs.contMDiffOn i).mono fun y hy ↦ (hW₀_sub hy).1.1)
  let η : TauCeti.RoughForm I M F 1 := fun y ↦
    ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) F (0 : Fin 1) (α y)
  have hη : TauCeti.IsSmoothForm I ∞ η :=
    TauCeti.isSmoothForm_ofSubsingleton_iff.mpr hα_smooth
  -- On `W_one := W₀ ∩ interior {y | χ y = 1}`, `η` is closed because `s'` is parallel and
  -- `cov` is torsion-free there.
  let W_one : Set M := W₀ ∩ interior {y | χ y = 1}
  have hW_one : IsOpen W_one := hW₀_open.inter isOpen_interior
  have hx₀W_one : x₀ ∈ W_one := ⟨hx₀W₀, mem_interior_iff_mem_nhds.mpr χ.eventuallyEq_one⟩
  have hclosed : ∀ᶠ y in 𝓝 x₀, TauCeti.mextDeriv η y = 0 := by
    filter_upwards [hW_one.mem_nhds hx₀W_one] with y ⟨hyW₀, hyχ⟩
    have hyW : y ∈ W := (hW₀_sub hyW₀).1.1
    have hframe_zero (i j : ι) : TauCeti.mextDeriv η y ![s i y, s j y] = 0 := by
      have hs'_eq (k : ι) : ∀ᶠ z in 𝓝 y, s' k z = s k z := by
        filter_upwards [isOpen_interior.mem_nhds hyχ] with z hz
        have hχz : χ z = 1 := interior_subset hz
        simp [s', hχz]
      have hη_const (k : ι) : (fun z ↦ η z ![s' k z]) =ᶠ[𝓝 y] fun _ ↦ v k := by
        filter_upwards [hW_one.mem_nhds ⟨hyW₀, hyχ⟩] with z ⟨hzW₀, hzχ⟩
        have hχz : χ z = 1 := interior_subset hzχ
        simp [η, α, s', hχz, hα₀_apply hzW₀ k]
      have hcov_zero (k : ι) : cov (s' k) y = 0 := by
        rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
          ((hs'_smooth k).mdifferentiable (by simp) y)
          ((hs.contMDiffAt hW hyW k).mdifferentiableAt (by simp)) univ_mem (hs'_eq k)]
        exact hpar y hyW k
      have hbr : mlieBracket I (s' i) (s' j) y = 0 := by
        have ht := cov.torsion_apply
          ((hs'_smooth i).mdifferentiable (by simp) y)
          ((hs'_smooth j).mdifferentiable (by simp) y)
        rw [htors y hyW, zero_apply, zero_apply, hcov_zero j, hcov_zero i,
          zero_apply, zero_apply, sub_zero, zero_sub] at ht
        exact neg_eq_zero.mp ht.symm
      have hχy : χ y = 1 := interior_subset hyχ
      have hs'iy : s' i y = s i y := by simp [s', hχy]
      have hs'jy : s' j y = s j y := by simp [s', hχy]
      rw [← hs'iy, ← hs'jy, TauCeti.mextDeriv_apply_one
        (hη.contMDiff.mdifferentiableAt (by simp))
        ((hs'_smooth i).mdifferentiable (by simp) y)
        ((hs'_smooth j).mdifferentiable (by simp) y)]
      have hd1 : mvfderiv I (fun z ↦ η z ![s' j z]) y = 0 :=
        (hη_const j).mvfderiv_eq.trans (mvfderiv_const (I := I) (c := v j))
      have hd2 : mvfderiv I (fun z ↦ η z ![s' i z]) y = 0 :=
        (hη_const i).mvfderiv_eq.trans (mvfderiv_const (I := I) (c := v i))
      rw [hd1, hd2, hbr]
      simp [η]
    -- Expand any two tangent vectors at `y` in the basis `{s i y}` to conclude `mextDeriv η y = 0`.
    let b_y : Basis ι ℝ (TangentSpace I y) := hs.toBasisAt hyW
    ext u
    have hu : u = ![u 0, u 1] := by
      funext k
      fin_cases k <;> rfl
    rw [hu, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
      ← b_y.sum_repr (u 0), ← b_y.sum_repr (u 1), ← ContinuousAlternatingMap.coe_toAlternatingMap]
    have h0 : ![∑ i, b_y.repr (u 0) i • b_y i, ∑ j, b_y.repr (u 1) j • b_y j] =
        Function.update ![0, ∑ j, b_y.repr (u 1) j • b_y j] 0
          (∑ i, b_y.repr (u 0) i • b_y i) := by
      ext k
      fin_cases k <;> rfl
    rw [h0, AlternatingMap.map_update_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [AlternatingMap.map_update_smul]
    have h1 : Function.update ![0, ∑ j, b_y.repr (u 1) j • b_y j] 0 (b_y i) =
        Function.update ![b_y i, 0] 1 (∑ j, b_y.repr (u 1) j • b_y j) := by
      ext k
      fin_cases k <;> rfl
    rw [h1, AlternatingMap.map_update_sum]
    suffices ∑ j, (TauCeti.mextDeriv η y).toAlternatingMap
        (Function.update ![b_y i, 0] 1 (b_y.repr (u 1) j • b_y j)) = 0 by
      rw [this, smul_zero]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [AlternatingMap.map_update_smul]
    have hpair : Function.update ![b_y i, 0] 1 (b_y j) = ![s i y, s j y] := by
      ext k
      fin_cases k <;> simp [b_y]
    rw [hpair, ContinuousAlternatingMap.coe_toAlternatingMap, hframe_zero i j, smul_zero]
  -- Integrate the closed `1`-form `η` near `x₀` by the manifold Poincaré lemma.
  obtain ⟨U_p, hU_p, ψ, hψ, hdψ⟩ :=
    TauCeti.exists_mextDeriv_eq_nhds (r := (⊤ : ℕ∞)) le_top hη hclosed
  let g : M → F := fun y ↦ ψ y 0
  have hg_smooth : CMDiff ∞ g := by
    have h1 : TauCeti.IsSmoothForm I ∞ (TauCeti.RoughForm.ofFunction I g) := by
      rwa [← ψ.eq_ofFunction]
    exact TauCeti.isSmoothForm_ofFunction_iff.mp h1
  let f : M → F := fun y ↦ g y - g x₀
  have hf_smooth : CMDiff ∞ f := hg_smooth.sub contMDiff_const
  let U : Set M := W_one ∩ interior U_p
  have hU_mem : U ∈ 𝓝 x₀ :=
    Filter.inter_mem (hW_one.mem_nhds hx₀W_one) (interior_mem_nhds.mpr hU_p)
  refine ⟨U, hU_mem, f, hf_smooth, sub_self _, fun y ⟨⟨hyW₀, hyχ⟩, hyU_p⟩ i ↦ ?_⟩
  have hdf : TauCeti.mextDeriv (TauCeti.RoughForm.ofFunction I f) y = η y := by
    rw [TauCeti.mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (c := -g x₀) (hg_smooth.mdifferentiable (by simp) y)
      (Eventually.of_forall fun z ↦ sub_eq_add_neg (g z) (g x₀)),
      ← ψ.eq_ofFunction]
    exact hdψ y (interior_subset hyU_p)
  have hχy : χ y = 1 := interior_subset hyχ
  rw [← TauCeti.mextDeriv_ofFunction_apply, hdf]
  simp only [η, α, hχy, one_smul, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero]
  exact hα₀_apply hyW₀ i

end CovariantDerivative

end
