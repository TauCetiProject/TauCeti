/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.ShapeOperator
import TauCeti.Analysis.InnerProductSpace.PointSpectrum.Transport
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Morse index and focal points of squared distance via the shape operator

Let `i : V → E` be a `C²` immersion from a finite-dimensional real normed space into a real inner
product space, and let `a : E`. At a critical point `x` of the squared-distance function
`ρ_a(y) = ‖i y - a‖²`, the displacement `i x - a` is normal to the tangent space `(Di(x)).range`,
and the Hessian of `ρ_a` at `x` is `2 g((1 - S_{a - i x}) v, w)` for the induced metric
`g(v, w) = ⟪Di(x) v, Di(x) w⟫`
(`TauCeti.fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_shapeOperator`).

Transporting the shape operator `S_{a - i x}` along the linear isomorphism `Di(x)` onto its image
yields a symmetric operator on a finite-dimensional inner product space. Diagonalizing it in an
orthonormal eigenbasis proves Milnor's focal-point formula (*Morse Theory*, Lemma 6.5):

* `x` is a nondegenerate critical point of `ρ_a` exactly when `i x - a` is normal and `1` is not an
  eigenvalue of `S_{a - i x}`, that is, `a` is not a focal point of `i` at `x`;
* the Morse index of `ρ_a` at any critical point `x` (degenerate or not) is the dimension of the
  point-spectral subspace of `S_{a - i x}` for `(1, ∞)`, equivalently the sum of the focal
  multiplicities along the open segment `{i x + t • (a - i x) | t ∈ (0, 1)}`.

For a holomorphic immersion into a complex inner product space (equipped with `re ⟪·, ·⟫`), the
paired principal curvatures and symmetric focal multiplicities of
`TauCeti.Analysis.InnerProductSpace.ShapeOperator` imply that `i x - ν` and `i x + ν` have equal
squared-distance Morse indices along every normal vector `ν`.

## Main results

* `TauCeti.isNondegenerateCriticalPoint_norm_sq_sub_comp_iff` and
  `TauCeti.isNondegenerateCriticalPoint_norm_sq_sub_add_smul_comp_iff`: nondegeneracy of squared
  distance in terms of the eigenvalues of the shape operator.
* `TauCeti.morseIndex_norm_sq_sub_comp`: the Morse index of `y ↦ ‖i y - a‖²` at a critical point is
  the dimension of `(shapeOperator i x (a - i x)).pointSpectralSubspace (Set.Ioi 1)`.
* `TauCeti.morseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker`: Milnor's focal-point index formula
  along the open segment from `i x` to `a`.
* `ContDiffAt.isNondegenerateCriticalPoint_norm_sq_sub_sub_comp_iff` and
  `ContDiffAt.morseIndex_norm_sq_sub_sub_comp`: symmetry of nondegeneracy and of the Morse index
  under reflection `i x + ν ↔ i x - ν` in the normal space of a holomorphic immersion.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §6, Lemma 6.5, and §7.
-/

public section

open Complex Function Module Module.End Set
open scoped Finset RealInnerProductSpace

namespace TauCeti

section Real

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {i : V → E} {x : V} {a : E}

/-- **Nondegeneracy of squared distance via the shape operator.** Along a `C²` immersion `i`, `x`
is a nondegenerate critical point of `y ↦ ‖i y - a‖²` if and only if `i x - a` is normal and `1` is
not an eigenvalue of `S_{a - i x}` (that is, `a` is not a focal point of `i` at `x`). -/
theorem isNondegenerateCriticalPoint_norm_sq_sub_comp_iff (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) :
    IsNondegenerateCriticalPoint (fun y ↦ ‖i y - a‖ ^ 2) x ↔
      i x - a ∈ (fderiv ℝ i x).rangeᗮ ∧ ¬(shapeOperator i x (a - i x)).HasEigenvalue 1 := by
  have hf : ContDiffAt ℝ 2 (fun y ↦ ‖i y - a‖ ^ 2) x :=
    ContDiffAt.norm_sq ℝ (hi.sub contDiffAt_const)
  have hcrit := fderiv_norm_sq_sub_comp_eq_zero_iff (a := a) (hi.differentiableAt (by norm_num))
  refine ⟨fun hnd ↦ ?_, fun ⟨ha, hev⟩ ↦ ⟨hf, hcrit.mpr ha, ?_⟩⟩
  · have ha : i x - a ∈ (fderiv ℝ i x).rangeᗮ := hcrit.mp hnd.fderiv_eq_zero
    refine ⟨ha, ?_⟩
    rw [Module.End.hasEigenvalue_iff, ← ker_fderiv_fderiv_norm_sq_sub_comp hi h ha, not_not,
      LinearMap.ker_eq_bot]
    exact hnd.isInvertible.injective
  · refine ContinuousLinearMap.isInvertible_of_injective ?_
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot,
      ker_fderiv_fderiv_norm_sq_sub_comp hi h ha]
    rwa [Module.End.hasEigenvalue_iff, not_not] at hev

/-- Along a normal ray `t ↦ i x + t • ν` (`t ≠ 0`), `x` is a nondegenerate critical point of
squared distance from `i x + t • ν` if and only if `t⁻¹` is not an eigenvalue of `S_ν`. -/
theorem isNondegenerateCriticalPoint_norm_sq_sub_add_smul_comp_iff (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) {ν : E} (hν : ν ∈ (fderiv ℝ i x).rangeᗮ) {t : ℝ} (ht : t ≠ 0) :
    IsNondegenerateCriticalPoint (fun y ↦ ‖i y - (i x + t • ν)‖ ^ 2) x ↔
      ¬(shapeOperator i x ν).HasEigenvalue t⁻¹ := by
  have ha : i x - (i x + t • ν) ∈ (fderiv ℝ i x).rangeᗮ := by
    simpa using Submodule.smul_mem _ (-t) hν
  rw [isNondegenerateCriticalPoint_norm_sq_sub_comp_iff hi h, and_iff_right ha,
    add_sub_cancel_left, Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff,
    shapeOperator_smul, eigenspace, eigenspace, genEigenspace_smul _ ht, mul_one]

/-- Squared distance from `i x` itself has a nondegenerate critical point at `x` along any `C²`
immersion. -/
theorem isNondegenerateCriticalPoint_norm_sq_sub_self_comp (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) :
    IsNondegenerateCriticalPoint (fun y ↦ ‖i y - i x‖ ^ 2) x := by
  rw [isNondegenerateCriticalPoint_norm_sq_sub_comp_iff hi h]
  simp [Module.End.hasEigenvalue_iff, eigenspace_def, Module.End.one_eq_id]

/-- Conjugating `shapeOperator i x ν` along `Di(x)` onto `(Di(x)).range` produces a symmetric
endomorphism when `i` is `C²` at `x` with injective derivative. -/
private theorem isSymmetric_conj_shapeOperator (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) (ν : E) :
    ((LinearEquiv.ofInjective (fderiv ℝ i x : V →ₗ[ℝ] E) h).conj
      (shapeOperator i x ν)).IsSymmetric := by
  let eR := LinearEquiv.ofInjective (fderiv ℝ i x : V →ₗ[ℝ] E) h
  have coe_eR (v : V) : (eR v : E) = fderiv ℝ i x v := by simp [eR]
  intro u w
  have hu : (u : E) = fderiv ℝ i x (eR.symm u) := by
    conv_lhs => rw [← eR.apply_symm_apply u]
    exact coe_eR (eR.symm u)
  have hw : (w : E) = fderiv ℝ i x (eR.symm w) := by
    conv_lhs => rw [← eR.apply_symm_apply w]
    exact coe_eR (eR.symm w)
  rw [Submodule.coe_inner, Submodule.coe_inner, LinearEquiv.conj_apply_apply,
    LinearEquiv.conj_apply_apply, coe_eR, coe_eR, hu, hw]
  exact hi.inner_fderiv_shapeOperator_apply_comm ν (eR.symm u) (eR.symm w)

/-- **Spectral formula for the Morse index of squared distance.** At any critical point `x` of
`y ↦ ‖i y - a‖²` along a `C²` immersion `i` (degenerate or not), the Morse index equals the
dimension of the point-spectral subspace of `S_{a - i x}` for eigenvalues strictly greater than
`1`. -/
theorem morseIndex_norm_sq_sub_comp (hi : ContDiffAt ℝ 2 i x) (h : Injective (fderiv ℝ i x))
    (ha : i x - a ∈ (fderiv ℝ i x).rangeᗮ) :
    morseIndex (fun y ↦ ‖i y - a‖ ^ 2) x =
      finrank ℝ ((shapeOperator i x (a - i x)).pointSpectralSubspace (Ioi 1)) := by
  let R : Submodule ℝ E := LinearMap.range (fderiv ℝ i x : V →ₗ[ℝ] E)
  let eR : V ≃ₗ[ℝ] R := LinearEquiv.ofInjective (fderiv ℝ i x : V →ₗ[ℝ] E) h
  have coe_eR (v : V) : (eR v : E) = fderiv ℝ i x v := by simp [R, eR]
  have : FiniteDimensional ℝ R := Module.Finite.equiv eR
  let S : Module.End ℝ V := shapeOperator i x (a - i x)
  let T : Module.End ℝ R := eR.conj S
  have hT : T.IsSymmetric := isSymmetric_conj_shapeOperator hi h (a - i x)
  have hn : finrank ℝ R = finrank ℝ V := eR.finrank_eq.symm
  let b := hT.eigenvectorBasis hn
  let b₀ : Module.Basis (Fin (finrank ℝ V)) ℝ V := b.toBasis.map eR.symm
  let f : V → ℝ := fun y ↦ ‖i y - a‖ ^ 2
  have hf : ContDiffAt ℝ 2 f x := ContDiffAt.norm_sq ℝ (hi.sub contDiffAt_const)
  have hval (j k : Fin (finrank ℝ V)) :
      fderiv ℝ (fderiv ℝ f) x (b₀ j) (b₀ k) =
        2 * (1 - hT.eigenvalues hn j) * ⟪b j, b k⟫ := by
    have hev : T (b j) = (hT.eigenvalues hn j) • b j := hT.apply_eigenvectorBasis hn j
    have hbj : fderiv ℝ i x (b₀ j) = (b j : E) := by rw [← coe_eR]; simp [b₀]
    have hbk : fderiv ℝ i x (b₀ k) = (b k : E) := by rw [← coe_eR]; simp [b₀]
    have hSbj : fderiv ℝ i x (S (b₀ j)) = hT.eigenvalues hn j • (b j : E) := by
      have h₁ : (T (b j) : E) = fderiv ℝ i x (S (b₀ j)) := by
        simp only [T, LinearEquiv.conj_apply_apply, b₀, Module.Basis.map_apply,
          OrthonormalBasis.coe_toBasis, coe_eR]
      rw [← h₁, hev, Submodule.coe_smul]
    rw [fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_shapeOperator hi h ha, map_sub, hbj, hSbj,
      hbk, inner_sub_left, real_inner_smul_left, ← R.coe_inner]
    ring
  have horth : (QuadraticMap.associated (R := ℝ) (hessianQuadraticForm f x)).IsOrthoᵢ b₀ := by
    rw [LinearMap.isOrthoᵢ_def]
    intro j k hjk
    rw [associated_hessianQuadraticForm hf, ContinuousLinearMap.toBilinForm_apply, hval,
      orthonormal_iff_ite.mp b.orthonormal j k]
    simp [hjk]
  have hequiv : QuadraticMap.Equivalent (hessianQuadraticForm f x)
      (QuadraticMap.weightedSumSquares ℝ fun i ↦ hessianQuadraticForm f x (b₀ i)) :=
    ⟨QuadraticForm.isometryEquivWeightedSumSquares (hessianQuadraticForm f x) b₀ horth⟩
  have hdiag : (fun i ↦ hessianQuadraticForm f x (b₀ i)) =
      fun j ↦ 2 * (1 - hT.eigenvalues hn j) := by
    funext j
    rw [hessianQuadraticForm_apply, hval, orthonormal_iff_ite.mp b.orthonormal j j]
    simp
  rw [hdiag] at hequiv
  have hset : {j | 2 * (1 - hT.eigenvalues hn j) < 0} =
      {j | hT.eigenvalues hn j ∈ Ioi 1} := by
    ext j
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor <;> intro hj <;> linarith
  rw [morseIndex_def, QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv, hset,
    ← hT.finrank_pointSpectralSubspace hn (Ioi 1), ← map_pointSpectralSubspace_conj eR S (Ioi 1),
    eR.finrank_map_eq]

/-- **Milnor's focal-point formula for the Morse index of squared distance** (*Morse Theory*,
Lemma 6.5). At any critical point `x` of `y ↦ ‖i y - a‖²` along a `C²` immersion `i`, the Morse
index equals the sum over `t ∈ (0, 1)` of the focal multiplicities of `i x + t • (a - i x)` at `x`
(only finitely many `t` have nonzero focal multiplicity). -/
theorem morseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) (ha : i x - a ∈ (fderiv ℝ i x).rangeᗮ) :
    morseIndex (fun y ↦ ‖i y - a‖ ^ 2) x =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1, finrank ℝ
        (LinearMap.ker (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - (i x + t • (a - i x))‖ ^ 2) x :
          V →ₗ[ℝ] V →L[ℝ] ℝ)) := by
  classical
  let R : Submodule ℝ E := LinearMap.range (fderiv ℝ i x : V →ₗ[ℝ] E)
  let eR : V ≃ₗ[ℝ] R := LinearEquiv.ofInjective (fderiv ℝ i x : V →ₗ[ℝ] E) h
  have : FiniteDimensional ℝ R := Module.Finite.equiv eR
  let S : Module.End ℝ V := shapeOperator i x (a - i x)
  let T : Module.End ℝ R := eR.conj S
  have hT : T.IsSymmetric := isSymmetric_conj_shapeOperator hi h (a - i x)
  have hν : a - i x ∈ (fderiv ℝ i x).rangeᗮ := by simpa using Submodule.neg_mem _ ha
  have hbij : BijOn Inv.inv (Ioo (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    ⟨fun t ht ↦ (one_lt_inv₀ ht.1).mpr ht.2, inv_injective.injOn, fun μ hμ ↦
      ⟨μ⁻¹, ⟨inv_pos.mpr (zero_lt_one.trans hμ), inv_lt_one_of_one_lt₀ hμ⟩, inv_inv μ⟩⟩
  have hbij_sum := finsum_mem_eq_of_bijOn Inv.inv hbij
    (f := fun t ↦ finrank ℝ (LinearMap.ker
      (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - (i x + t • (a - i x))‖ ^ 2) x : V →ₗ[ℝ] V →L[ℝ] ℝ)))
    (g := fun μ ↦ finrank ℝ (eigenspace S μ))
    fun t ht ↦ by rw [ker_fderiv_fderiv_norm_sq_sub_add_smul_comp hi h hν ht.1.ne']
  have heig (μ : ℝ) : finrank ℝ (eigenspace S μ) = #{j | hT.eigenvalues rfl j = μ} := by
    have hmap : (eigenspace S μ).map eR.toLinearMap = eigenspace T μ := by
      rw [eigenspace_eq_comap_of_intertwine (e := eR) (f := S) (g := T) (fun v ↦ by simp [T]) μ,
        Submodule.map_comap_eq_self (by simp)]
    rw [← eR.finrank_map_eq, hmap, ← hT.card_filter_eigenvalues_eq rfl]
    simp
  let s : Finset ℝ := (Finset.univ.image (hT.eigenvalues rfl)).filter (· ∈ Ioi (1 : ℝ))
  have hsum : (∑ᶠ μ ∈ Ioi (1 : ℝ), finrank ℝ (eigenspace S μ)) =
      ∑ μ ∈ s, finrank ℝ (eigenspace S μ) := by
    refine finsum_mem_eq_sum_of_subset _ (fun μ ⟨hμ1, hμ0⟩ ↦ ?_)
      (fun μ hμ ↦ (Finset.mem_filter.mp hμ).2)
    rw [Function.mem_support, heig, Finset.card_ne_zero, Finset.filter_nonempty_iff] at hμ0
    obtain ⟨j, -, rfl⟩ := hμ0
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), hμ1⟩
  have hcard : ∑ μ ∈ s, finrank ℝ (eigenspace S μ) =
      {j | hT.eigenvalues rfl j ∈ Ioi (1 : ℝ)}.ncard := by
    simp_rw [heig]
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [s]
  rw [morseIndex_norm_sq_sub_comp hi h ha, ← eR.finrank_map_eq,
    map_pointSpectralSubspace_conj eR S (Ioi 1), hT.finrank_pointSpectralSubspace rfl (Ioi 1),
    ← hcard, ← hsum, ← hbij_sum]

/-- At the base point `a = i x`, the squared-distance function `y ↦ ‖i y - i x‖²` has Morse index
`0` for any `C²` map `i` (no immersion hypothesis is needed). -/
@[simp]
theorem morseIndex_norm_sq_sub_self_comp (hi : ContDiffAt ℝ 2 i x) :
    morseIndex (fun y ↦ ‖i y - i x‖ ^ 2) x = 0 := by
  rw [morseIndex_def, ← QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero]
  intro v
  rw [hessianQuadraticForm_apply, fderiv_fderiv_norm_sq_sub_comp_apply hi]
  simp only [sub_self, inner_zero_left, add_zero, real_inner_self_eq_norm_sq]
  positivity

end Real

section Complex

/-! ### Holomorphic immersions -/

attribute [local instance] InnerProductSpace.complexToReal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {i : V → E} {x : V}

/-- **Symmetric nondegeneracy across the tangent space.** For a `C²` holomorphic immersion `i` and
any vector `ν : E`, `x` is a nondegenerate critical point of squared distance from `i x - ν` if and
only if it is a nondegenerate critical point of squared distance from `i x + ν`. -/
theorem _root_.ContDiffAt.isNondegenerateCriticalPoint_norm_sq_sub_sub_comp_iff
    (hi : ContDiffAt ℂ 2 i x) (h : Injective (fderiv ℂ i x)) (ν : E) :
    IsNondegenerateCriticalPoint (fun y ↦ ‖i y - (i x - ν)‖ ^ 2) x ↔
      IsNondegenerateCriticalPoint (fun y ↦ ‖i y - (i x + ν)‖ ^ 2) x := by
  have hiR : ContDiffAt ℝ 2 i x := hi.restrict_scalars ℝ
  have hR := ((hi.differentiableAt (by norm_num)).injective_fderiv_restrictScalars_iff ℝ).2 h
  rw [isNondegenerateCriticalPoint_norm_sq_sub_comp_iff hiR hR,
    isNondegenerateCriticalPoint_norm_sq_sub_comp_iff hiR hR,
    sub_sub_cancel, sub_sub_cancel_left, add_sub_cancel_left, sub_add_cancel_left,
    Submodule.neg_mem_iff, shapeOperator_neg, Module.End.hasEigenvalue_iff,
    Module.End.hasEigenvalue_iff, eigenspace, eigenspace, genEigenspace_neg,
    ← Module.End.hasEigenvalue_iff, ← Module.End.hasEigenvalue_iff,
    hi.hasEigenvalue_shapeOperator_neg_iff]

/-- **Symmetric Morse indices along normal lines.** For a `C²` holomorphic immersion `i` and a
normal vector `ν`, the squared-distance functions from `i x - ν` and from `i x + ν` have the same
Morse index at `x`: every focal point `i x + t • ν` (`0 < t < 1`) is paired with `i x - t • ν` of
equal multiplicity. -/
theorem _root_.ContDiffAt.morseIndex_norm_sq_sub_sub_comp (hi : ContDiffAt ℂ 2 i x)
    (h : Injective (fderiv ℂ i x)) {ν : E} (hν : ν ∈ (fderiv ℝ i x).rangeᗮ) :
    morseIndex (fun y ↦ ‖i y - (i x - ν)‖ ^ 2) x =
      morseIndex (fun y ↦ ‖i y - (i x + ν)‖ ^ 2) x := by
  have hiR : ContDiffAt ℝ 2 i x := hi.restrict_scalars ℝ
  have hR := ((hi.differentiableAt (by norm_num)).injective_fderiv_restrictScalars_iff ℝ).2 h
  have ha₁ : i x - (i x - ν) ∈ (fderiv ℝ i x).rangeᗮ := by rwa [sub_sub_cancel]
  have ha₂ : i x - (i x + ν) ∈ (fderiv ℝ i x).rangeᗮ := by
    rw [sub_add_cancel_left]
    exact Submodule.neg_mem _ hν
  rw [morseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker hiR hR ha₁,
    morseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker hiR hR ha₂]
  refine finsum_mem_congr rfl fun t _ ↦ ?_
  have hsub₁ : i x + t • (i x - ν - i x) = i x - t • ν := by
    rw [sub_sub_cancel_left, smul_neg, sub_eq_add_neg]
  have hsub₂ : i x + t • (i x + ν - i x) = i x + t • ν := by
    rw [add_sub_cancel_left]
  rw [hsub₁, hsub₂]
  exact hi.finrank_ker_fderiv_fderiv_norm_sq_sub_sub_comp h (Submodule.smul_mem _ t hν)

end Complex

end TauCeti
