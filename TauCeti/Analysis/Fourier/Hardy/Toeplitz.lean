/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Fourier.Hardy.Basic
public import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# Toeplitz operators on boundary Hardy space

For an essentially bounded symbol `a` on `UnitAddCircle`, the Toeplitz operator `T_a` is the
compression `P M_a |H²` of the multiplication operator `M_a` on circle `L²` to the boundary Hardy
space `H²`, where `P` is the orthogonal projection onto `H²`. This file bundles the symbol map
`a ↦ T_a` as a bounded complex-linear map `TauCeti.toeplitz` and proves its basic properties:

* `TauCeti.inner_hardyBasis_toeplitz_hardyBasis`: in the Hardy basis `e₀, e₁, …` the matrix
  entry `(i, j)` of `T_a` is the Fourier coefficient `â(i - j)`;
* `TauCeti.adjoint_toeplitz`: the adjoint of `T_a` is the Toeplitz operator of the complex
  conjugate symbol;
* `TauCeti.toeplitz_const`: a constant symbol acts by scalar multiplication;
* `TauCeti.norm_toeplitz`: the operator norm of `T_a` is exactly `‖a‖∞`, so the symbol map is an
  isometry (`TauCeti.isometry_toeplitz`) and in particular injective
  (`TauCeti.toeplitz_injective`).

The inequality `‖T_a‖ ≤ ‖a‖∞` is immediate from the compression. For the reverse inequality,
multiplication by a Fourier monomial `e_N` is unitary on circle `L²` and commutes with `M_a`, and
for `N` large it moves any two trigonometric polynomials `f, g` into `H²`. Hence
`|⟪f, a g⟫| = |⟪e_N f, T_a (e_N g)⟫| ≤ ‖T_a‖ ‖f‖ ‖g‖`, which extends by density to all of `L²`
and gives `‖M_a‖ ≤ ‖T_a‖`; the operator norm of `M_a` is `‖a‖∞`.

The conventions are those of Conway, *A Course in Functional Analysis*, second edition, and of
E. Park, *Toeplitz operators*: normalized Haar measure, the modes `exp (2πint)` and inner products
conjugate linear in the first variable.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Compressing multiplication by `a` to Hardy space does not increase the operator norm. -/
private theorem norm_compress_multiplicationOperator_le
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖hardySubmodule.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
      hardySubmodule.subtypeL‖ ≤ ‖a‖ := by
  calc _ ≤ ‖hardySubmodule.orthogonalProjectionOnto‖ *
        (‖Lp.multiplicationOperator (E := ℂ) a‖ * ‖hardySubmodule.subtypeL‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        · exact hardySubmodule.orthogonalProjectionOnto_norm_le
        · exact Lp.norm_multiplicationOperator_le a
        · exact Submodule.norm_subtypeL_le _
    _ = ‖a‖ := by ring

/-- The Toeplitz operator map, sending an essentially bounded symbol `a` on the unit circle to the
compression `T_a = P M_a |H²` of multiplication by `a` to boundary Hardy space. -/
def toeplitz :
    Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)) →L[ℂ] HardySpace →L[ℂ] HardySpace :=
  LinearMap.mkContinuous
    { toFun a := hardySubmodule.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
        hardySubmodule.subtypeL
      map_add' a b := by
        simp only [Lp.multiplicationOperator_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c a := by
        simp only [Lp.multiplicationOperator_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    1 fun a ↦ (one_mul ‖a‖).symm ▸ norm_compress_multiplicationOperator_le a

/-- The Toeplitz operator of `a` compresses the multiplication operator of `a` to Hardy space. -/
theorem toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    toeplitz a = hardySubmodule.orthogonalProjectionOnto ∘L
      Lp.multiplicationOperator a ∘L hardySubmodule.subtypeL :=
  (rfl)

/-- The ambient value of `T_a f` is the Hardy projection of the product `a f`. -/
theorem coe_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (f : HardySpace) :
    (toeplitz a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      hardySubmodule.starProjection (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) := by
  rw [toeplitz_apply, Submodule.starProjection_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Lp.multiplicationOperator_apply]

/-- Compressing to Hardy space does not change inner products against Hardy functions. -/
theorem inner_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f g : HardySpace) :
    ⟪f, toeplitz a g⟫_ℂ =
      ⟪(f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))),
        a • (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))⟫_ℂ := by
  rw [toeplitz_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.subtypeL_apply,
    Lp.multiplicationOperator_apply]

/-- The Hardy coordinates of `T_a f` are the nonnegative Fourier coefficients of `a f`. -/
@[simp]
theorem hardyBasis_repr_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f : HardySpace) (i : ℕ) :
    hardyBasis.repr (toeplitz a f) i =
      fourierCoeff (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) (i : ℤ) := by
  rw [HilbertBasis.repr_apply_apply, inner_toeplitz_apply, coe_hardyBasis,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

/-- **Matrix formula.** In the Hardy basis `e₀, e₁, …`, the `(i, j)` entry of the Toeplitz
operator `T_a` is the Fourier coefficient `â(i - j)`. -/
theorem inner_hardyBasis_toeplitz_hardyBasis (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (i j : ℕ) :
    ⟪hardyBasis i, toeplitz a (hardyBasis j)⟫_ℂ = fourierCoeff a ((i : ℤ) - j) := by
  rw [← HilbertBasis.repr_apply_apply, hardyBasis_repr_toeplitz_apply, coe_hardyBasis,
    fourierCoeff_smul_fourierBasis]

/-- The adjoint of the Toeplitz operator `T_a` is the Toeplitz operator of the complex conjugate
symbol. -/
@[simp]
theorem adjoint_toeplitz (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ContinuousLinearMap.adjoint (toeplitz a) = toeplitz (star a) := by
  rw [toeplitz_apply, toeplitz_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, Lp.adjoint_multiplicationOperator,
    ContinuousLinearMap.comp_assoc]

/-- A constant symbol acts on Hardy space by scalar multiplication. -/
@[simp]
theorem toeplitz_const (c : ℂ) :
    toeplitz (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) c) =
      c • ContinuousLinearMap.id ℂ HardySpace := by
  ext f : 2
  rw [coe_toeplitz_apply, ← Lp.multiplicationOperator_apply, Lp.multiplicationOperator_const]
  simp [Submodule.starProjection_eq_self_iff.mpr (hardySubmodule.smul_mem c f.property)]

/-- The operator norm of the Toeplitz operator `T_a` is at most the `L∞` norm of its symbol. -/
theorem norm_toeplitz_le (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖toeplitz a‖ ≤ ‖a‖ :=
  norm_compress_multiplicationOperator_le a

/-- Multiplying a trigonometric polynomial by a sufficiently high Fourier mode lands in Hardy
space. -/
private theorem eventually_fourierLp_smul_mem_hardySubmodule
    {g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hg : g ∈ Submodule.span ℂ (Set.range (fourierBasis (T := 1)))) :
    ∀ᶠ N : ℤ in Filter.atTop,
      (fourierLp (T := 1) ∞ N • g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) ∈
        hardySubmodule := by
  simp only [← Lp.multiplicationOperator_apply]
  induction hg using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨m, rfl⟩ := hx
    filter_upwards [Filter.eventually_ge_atTop (-m)] with N hN
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ N + m)
    rw [Lp.multiplicationOperator_apply, fourierLp_smul_fourierBasis, hk]
    exact fourierBasis_mem_hardySubmodule k
  | zero => exact Filter.Eventually.of_forall fun N ↦ by simp
  | add _ _ _ _ hx hy =>
    filter_upwards [hx, hy] with N hx hy
    rw [map_add]
    exact add_mem hx hy
  | smul c _ _ hx =>
    filter_upwards [hx] with N hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/-- On trigonometric polynomials, the matrix coefficients of multiplication by `a` are bounded by
the norm of `T_a`: multiplying by a high Fourier mode is unitary, commutes with multiplication by
`a`, and moves both vectors into Hardy space, where `M_a` is compressed to `T_a`. -/
private theorem norm_inner_smul_le_of_mem_span (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    {f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hf : f ∈ Submodule.span ℂ (Set.range (fourierBasis (T := 1))))
    (hg : g ∈ Submodule.span ℂ (Set.range (fourierBasis (T := 1)))) :
    ‖⟪f, a • g⟫_ℂ‖ ≤ ‖toeplitz a‖ * ‖f‖ * ‖g‖ := by
  obtain ⟨N, hfN, hgN⟩ := ((eventually_fourierLp_smul_mem_hardySubmodule hf).and
    (eventually_fourierLp_smul_mem_hardySubmodule hg)).exists
  have hu := ae_norm_fourierLp_eq_one (T := 1) ∞ N
  have hcomm := congrArg (· g)
    (Lp.commute_multiplicationOperator (E := ℂ) (fourierLp (T := 1) ∞ N) a).eq
  simp only [mul_apply_eq_comp, Lp.multiplicationOperator_apply] at hcomm
  have hinner : ⟪f, a • g⟫_ℂ = ⟪(⟨_, hfN⟩ : HardySpace), toeplitz a ⟨_, hgN⟩⟫_ℂ := by
    rw [inner_toeplitz_apply, Submodule.coe_mk, Submodule.coe_mk, ← hcomm]
    simp only [← Lp.multiplicationOperator_apply]
    rw [Lp.inner_multiplicationOperator_apply_apply_of_ae_norm_eq_one hu]
  have hnorm (h : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      ‖(fourierLp (T := 1) ∞ N • h : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ = ‖h‖ := by
    rw [← Lp.multiplicationOperator_apply,
      Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one hu]
  calc ‖⟪f, a • g⟫_ℂ‖ ≤ ‖(⟨_, hfN⟩ : HardySpace)‖ * (‖toeplitz a‖ * ‖(⟨_, hgN⟩ : HardySpace)‖) := by
        rw [hinner]
        exact (norm_inner_le_norm _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ = ‖toeplitz a‖ * ‖f‖ * ‖g‖ := by
        rw [← Submodule.norm_coe, ← Submodule.norm_coe, Submodule.coe_mk, Submodule.coe_mk,
          hnorm, hnorm]
        ring

/-- Multiplication by `a` on circle `L²` changes norms by at most the norm of `T_a`. -/
private theorem norm_smul_le_norm_toeplitz_mul (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    ‖(a • f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ ≤ ‖toeplitz a‖ * ‖f‖ := by
  have hD : Dense (Submodule.span ℂ (Set.range (fourierBasis (T := 1))) :
      Set (Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 (fourierBasis (T := 1)).dense_span
  -- The bound on matrix coefficients is a closed condition, so it extends from trigonometric
  -- polynomials to all pairs of `L²` functions.
  have hbound : ∀ p : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) ×
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)),
      ‖⟪p.1, Lp.multiplicationOperator a p.2⟫_ℂ‖ ≤ ‖toeplitz a‖ * ‖p.1‖ * ‖p.2‖ := by
    refine (hD.prod hD).induction (fun p hp ↦ ?_) (isClosed_le (by fun_prop) (by fun_prop))
    rw [Lp.multiplicationOperator_apply]
    exact norm_inner_smul_le_of_mem_span a hp.1 hp.2
  -- Testing against `a f` itself bounds its norm.
  have h := hbound (Lp.multiplicationOperator a f, f)
  rw [inner_self_eq_norm_sq_to_K, Lp.multiplicationOperator_apply] at h
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at h
  rcases (norm_nonneg (a • f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · refine le_of_mul_le_mul_left ?_ hpos
    calc _ = ‖(a • f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ ^ 2 := (sq _).symm
      _ ≤ _ := h
      _ = _ := by ring

/-- **Symbol norm.** The operator norm of the Toeplitz operator `T_a` is the `L∞` norm of its
symbol. -/
@[simp]
theorem norm_toeplitz (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖toeplitz a‖ = ‖a‖ := by
  refine le_antisymm (norm_toeplitz_le a) ?_
  rw [← Lp.norm_multiplicationOperator (E := ℂ) a]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (toeplitz a)) fun f ↦ by
    rw [Lp.multiplicationOperator_apply]
    exact norm_smul_le_norm_toeplitz_mul a f

/-- The Toeplitz symbol map `a ↦ T_a` is an isometry. -/
theorem isometry_toeplitz : Isometry toeplitz :=
  AddMonoidHomClass.isometry_of_norm toeplitz norm_toeplitz

/-- A symbol is determined by its Toeplitz operator. -/
theorem toeplitz_injective : Function.Injective toeplitz :=
  isometry_toeplitz.injective

end TauCeti
