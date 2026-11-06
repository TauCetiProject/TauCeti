/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.ODE.EnergyEstimate.Sobolev
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The cokernel of the trajectory operator

Let `A` be an essentially bounded family of operators on a real inner product space `E`, and let

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

be its trajectory operator (`TauCeti.WeakDerivStep.trajectoryOperator`, for an `L∞` class of `A`).
This file identifies the orthogonal complement of the range of `D_A` with the kernel of the formal
adjoint `-d/ds + A†`, where `A†` is the pointwise adjoint of `A`.

A path `v` orthogonal to the range pairs to zero with `D_A (φ • e)` for every test function `φ` and
every vector `e`. This says that `v` has weak derivative `A† v`, so `v` lies in `W^{1,2}(ℝ, E)` and
solves the formal adjoint equation `-v' + A† v = 0`: it is in the kernel of `D_{-A†}`. This
inclusion needs neither finite dimensionality of `E` nor any further hypothesis on `A`, and is
stated in that generality, for any essentially bounded `B` with `B = A†` almost everywhere
(`TauCeti.WeakDerivStep.exists_ae_eq_adjoint` provides one). Conversely, when `E` is finite
dimensional, density of test functions in `W^{1,2}(ℝ, E)` shows that every element of the kernel of
`D_{-A†}` is orthogonal to the range of `D_A`.

When the range of `D_A` is closed, its cokernel is the orthogonal complement of the range, so the
index of `D_A` is `dim ker D_A - dim ker D_{-A†}`. For symmetric `A` it reads
`dim ker D_A - dim ker D_{-A}`. The file `TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov` uses this
to prove that `D_A` is Fredholm when the limits of `A` at `±∞` are hyperbolic.

## Main declarations

* `TauCeti.WeakDerivStep.hasWeakLineDerivOn_of_mem_orthogonal_range_trajectoryOperator`: a path
  orthogonal to the range of `D_A` has weak derivative `A† v`.
* `TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_le_map_ker`: such a path is the value
  of an element of the kernel of `D_{-A†}`.
* `TauCeti.WeakDerivStep.map_ker_le_orthogonal_range_trajectoryOperator` and
  `TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_eq_map_ker`: the values of the kernel
  of `D_{-A†}` are exactly the orthogonal complement of the range of `D_A`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_of_isClosed_range`: whenever the range of `D_A`
  is closed, its index is `dim ker D_A - dim ker D_{-A†}`.
* `TauCeti.WeakDerivStep.exists_ae_eq_adjoint`: the pointwise adjoint of an essentially bounded
  family has an `L∞` class.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (the cokernel of a first-order operator through its formal adjoint).
* M. Schwarz, *Morse Homology*, Chapter 2 (the Fredholm property of linearized trajectory
  operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace Distributions

namespace TauCeti.WeakDerivStep

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Pairing `v` with `D_A (φ • e)` for a test function `φ` and a vector `e` gives the pairing of
`e` with `∫ φ' v + ∫ φ B v`, when `B` is almost everywhere the adjoint of `A`. Both directions of
the identification of the cokernel of `D_A` with the kernel of `D_{-B}` are read off from it. -/
private theorem inner_trajectoryOperator_smulRightW1pL
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      BL s = ContinuousLinearMap.adjoint (AL s))
    (v : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) (e : E)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ⟪trajectoryOperator (p := 2) AL (smulRightW1pL e (W1p.ofTestFunctionₗ volume ⊤ 2 φ)), v⟫_ℝ =
      ⟪e, (∫ s, lineDeriv ℝ (φ : ℝ → ℝ) s 1 • v s) + ∫ s, (φ : ℝ → ℝ) s • BL s (v s)⟫_ℝ := by
  have hi1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Lp.locallyIntegrableOn v (by norm_num)) φ 1
  have hi2 := integrable_smul_of_locallyIntegrableOn (w := fun s ↦ BL s (v s))
    ((Lp.locallyIntegrableOn _ (by norm_num)).congr
      ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder (r := 2) BL v)) φ
  have hψ : ContDiff ℝ 1 fun s ↦ (φ : ℝ → ℝ) s • e :=
    (φ.contDiff.of_le (by exact_mod_cast le_top)).smul contDiff_const
  have hDu := trajectoryOperator_apply_ae_eq_deriv_add AL _
    (prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (p := 2) e φ)
    ((hψ.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
    fun s _ ↦ hψ.differentiable one_ne_zero s
  have hvol (g : ℝ → ℝ) : ∫ s, g s = ∫ s, g s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ) := by
    simp
  rw [inner_add_right, ← integral_inner hi1, ← integral_inner hi2,
    ← integral_add (hi1.const_inner e) (hi2.const_inner e), L2.inner_def, hvol]
  refine integral_congr_ae ?_
  filter_upwards [hDu, hadj] with s hs hadjs
  have hφd : DifferentiableAt ℝ (φ : ℝ → ℝ) s := φ.contDiff.differentiable (by simp) s
  rw [hs, deriv_smul_const hφd, lineDeriv_one, hadjs]
  simp only [map_smul, inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    ContinuousLinearMap.adjoint_inner_right]

/-- An element `z` of `W^{1,2}(ℝ, E)` lies in the kernel of `D_{-B}` exactly when its value `v`
has weak derivative `B v`. -/
private theorem trajectoryOperator_neg_eq_zero_iff
    (BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (z : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectoryOperator (-BL) z = 0 ↔ HasWeakLineDerivOn volume ⊤
      (prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) z
        : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      (fun s ↦ BL s
        (prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) z s))
      1 := by
  rw [trajectoryOperator_eq_iff_hasWeakLineDerivOn]
  refine ⟨fun h ↦ h.congr_ae_deriv ?_, fun h ↦ h.congr_ae_deriv ?_⟩ <;>
  · filter_upwards [Lp.coeFn_zero E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      Lp.coeFn_neg BL] with s h0 hneg
    rw [h0, hneg]
    simp

/-- **A path orthogonal to the range solves the adjoint equation weakly.** Let `B` be almost
everywhere the pointwise adjoint of the coefficient of the trajectory operator `D_A u = u' + A u`.
Then every `v ∈ L²(ℝ, E)` orthogonal to the range of `D_A` has weak derivative `B v`: it is a weak
solution of the formal adjoint equation `-v' + B v = 0`. -/
theorem hasWeakLineDerivOn_of_mem_orthogonal_range_trajectoryOperator
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      BL s = ContinuousLinearMap.adjoint (AL s))
    {v : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hv : v ∈ (trajectoryOperator (p := 2) AL).rangeᗮ) :
    HasWeakLineDerivOn volume ⊤ v (fun s ↦ BL s (v s)) 1 := by
  refine hasWeakLineDerivOn_iff_testFunction.mpr ⟨inferInstance,
    Lp.locallyIntegrableOn v (by norm_num), (Lp.locallyIntegrableOn _ (by norm_num)).congr
      ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder (r := 2) BL v), fun φ ↦ ?_⟩
  -- The pairing of `∫ φ' v + ∫ φ B v` with every vector vanishes, so this vector is zero.
  have hpair (e : E) := (inner_trajectoryOperator_smulRightW1pL hadj v e φ).symm.trans
    ((Submodule.mem_orthogonal _ _).mp hv _ (LinearMap.mem_range_self _ _))
  exact eq_neg_of_add_eq_zero_left (inner_self_eq_zero.mp (hpair _))

/-- **Paths orthogonal to the range lie in the kernel of the formal adjoint.** Let `B` be almost
everywhere the pointwise adjoint of the coefficient of `D_A u = u' + A u`. Every `v ∈ L²(ℝ, E)`
orthogonal to the range of `D_A` is the value of an element of `W^{1,2}(ℝ, E)` in the kernel of
`D_{-B}`; that is, `v` solves `v' - B v = 0` in `W^{1,2}`. -/
theorem orthogonal_range_trajectoryOperator_le_map_ker
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      BL s = ContinuousLinearMap.adjoint (AL s)) :
    (trajectoryOperator (p := 2) AL).rangeᗮ ≤
      (trajectoryOperator (p := 2) (-BL)).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) := by
  intro v hv
  have h := hasWeakLineDerivOn_of_mem_orthogonal_range_trajectoryOperator hadj hv
  obtain ⟨z, hzv, hz⟩ := exists_prev_eq_and_trajectoryOperator_eq_of_hasWeakLineDerivOn (F := E)
    (-BL) (f := 0) <| h.congr_ae_deriv <| by
      filter_upwards [Lp.coeFn_zero E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
        Lp.coeFn_neg BL] with s h0 hneg
      rw [h0, hneg]
      simp
  exact ⟨z, hz, by simpa using hzv⟩

/-- **The kernel of the formal adjoint is orthogonal to the range.** Let `B` be almost everywhere
the pointwise adjoint of the coefficient of `D_A u = u' + A u`, and let `E` be finite dimensional.
The value of every solution of `v' - B v = 0` in `W^{1,2}(ℝ, E)` is orthogonal to the range of
`D_A`. -/
theorem map_ker_le_orthogonal_range_trajectoryOperator [FiniteDimensional ℝ E]
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      BL s = ContinuousLinearMap.adjoint (AL s)) :
    (trajectoryOperator (p := 2) (-BL)).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) ≤
      (trajectoryOperator (p := 2) AL).rangeᗮ := by
  rintro _ ⟨z, hz, rfl⟩
  set v := prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) z
  -- The value `v` of `z` has weak derivative `B v`.
  have h : HasWeakLineDerivOn volume ⊤ v (fun s ↦ BL s (v s)) 1 :=
    (trajectoryOperator_neg_eq_zero_iff BL z).mp hz
  -- The paths `u` with `⟪v, D_A u⟫ = 0` form a closed subspace containing the test fields.
  let K := ((innerSL ℝ v).comp (trajectoryOperator (p := 2) AL)).ker
  have hK := ((innerSL ℝ v).comp (trajectoryOperator (p := 2) AL)).isClosed_ker
  have mem_K (u) : u ∈ K ↔ ⟪v, trajectoryOperator (p := 2) AL u⟫_ℝ = 0 := by simp [K]
  have htest (e : E) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
      smulRightW1pL e (W1p.ofTestFunctionₗ volume ⊤ 2 φ) ∈ K := by
    rw [mem_K, real_inner_comm, inner_trajectoryOperator_smulRightW1pL hadj,
      h.integral_lineDeriv_smul_eq_neg_integral_smul, neg_add_cancel, inner_zero_right]
  -- By density of test functions, `K` contains every coordinate field, hence every path.
  have hcoord (e : E) (w : W1p volume ⊤ 2) : smulRightW1pL e w ∈ K :=
    (W1p.denseRange_ofTestFunctionₗ_top (by norm_num)).induction_on w
      (hK.preimage (smulRightW1pL e).continuous) (htest e)
  rw [Submodule.mem_orthogonal']
  rintro _ ⟨u, rfl⟩
  have hu : u ∈ K := by
    rw [← sum_smulRightW1pL_toW1pL (Module.finBasis ℝ E) u]
    exact K.sum_mem fun i _ ↦ hcoord _ _
  simpa [v, prevL_apply] using (mem_K u).mp hu

/-- **The orthogonal complement of the range of `D_A` is the kernel of its formal adjoint.** Let
`B` be almost everywhere the pointwise adjoint of the coefficient of `D_A u = u' + A u`, and let
`E` be finite dimensional. The orthogonal complement of the range of `D_A` in `L²(ℝ, E)` consists
exactly of the values of the solutions of `v' - B v = 0` in `W^{1,2}(ℝ, E)`, the kernel of
`D_{-B}`. -/
theorem orthogonal_range_trajectoryOperator_eq_map_ker [FiniteDimensional ℝ E]
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      BL s = ContinuousLinearMap.adjoint (AL s)) :
    (trajectoryOperator (p := 2) AL).rangeᗮ =
      (trajectoryOperator (p := 2) (-BL)).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) :=
  (orthogonal_range_trajectoryOperator_le_map_ker hadj).antisymm
    (map_ker_le_orthogonal_range_trajectoryOperator hadj)

/-- **The index of a trajectory operator with closed range.** Let `B` be almost everywhere the
pointwise adjoint of the coefficient of `D_A u = u' + A u`, let `E` be finite dimensional and let
the range of `D_A` be closed. Then the index of `D_A` is `dim ker D_A - dim ker D_{-B}`: its
cokernel is the kernel of the formal adjoint `-d/ds + B`, whose solutions are those of
`v' - B v = 0`. -/
theorem index_trajectoryOperator_of_isClosed_range [FiniteDimensional ℝ E]
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      BL s = ContinuousLinearMap.adjoint (AL s))
    (hclosed : IsClosed ((trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker : ℤ) -
        Module.finrank ℝ (trajectoryOperator (p := 2) (-BL)).ker := by
  have := hclosed.completeSpace_coe
  -- The value map `W^{1,2}(ℝ, E) → L²(ℝ, E)` is injective.
  have hinj : Function.Injective
      (prevL (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :=
    fun u w h ↦ ext (by simpa using h)
  -- The cokernel is the orthogonal complement of the range, which is the image of the kernel of
  -- `D_{-B}` under the injective value map.
  have hcoker : Module.finrank ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ⧸
      (trajectoryOperator (p := 2) AL).range) =
        Module.finrank ℝ (trajectoryOperator (p := 2) (-BL)).ker :=
    (((trajectoryOperator (p := 2) AL).range.quotientEquivOrthogonal.toLinearEquiv.trans
      (LinearEquiv.ofEq _ _ (orthogonal_range_trajectoryOperator_eq_map_ker hadj))).trans
      (Submodule.equivMapOfInjective _ hinj _).symm).finrank_eq
  rw [ContinuousLinearMap.index_eq_finrank_sub, hcoker]

variable {A : ℝ → E →L[ℝ] E}

/-- **An `L∞` class of the pointwise adjoint.** If `AL` is an `L∞` class of `A`, then the pointwise
adjoints `s ↦ A(s)†` also have an `L∞` class. It is the coefficient of the formal adjoint
`-d/ds + A†` of the trajectory operator `d/ds + A`. -/
theorem exists_ae_eq_adjoint (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ∃ BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ ContinuousLinearMap.adjoint (A s) := by
  set adj := (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ⋆[ℝ] (E →L[ℝ] E))
  set L : (E →L[ℝ] E) →SL[starRingEnd ℝ] (E →L[ℝ] E) :=
    adj.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨L.compLp AL, ?_⟩
  filter_upwards [L.coeFn_compLp AL, hAL] with s hs hAs
  simp [hs, hAs, L, adj]

/-- An `L∞` class of the pointwise adjoint of `A` is almost everywhere the pointwise adjoint of an
`L∞` class of `A`. This is the hypothesis on the coefficient of the formal adjoint in
`TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_eq_map_ker`. -/
theorem ae_eq_adjoint_of_ae_eq
    {AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ContinuousLinearMap.adjoint (A s)) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), BL s = ContinuousLinearMap.adjoint (AL s) := by
  filter_upwards [hAL, hBL] with s hs hBs
  rw [hBs, hs]

end Orthogonal

end TauCeti.WeakDerivStep
