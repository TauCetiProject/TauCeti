/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.Prod
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity

/-!
# Tensor products of distributions

Let `Ω ⊆ E` and `O ⊆ D` be open subsets of real normed spaces, with `E` finite-dimensional, and
let `V ⊆ Ω ×ˢ O` be open. For a distribution `T` on `O` and a test function `φ` on `V`, the
**partial pairing** of `T` with `φ` is the function

`x ↦ T (φ (x, ·))`

obtained by pairing `T` with the slices `y ↦ φ (x, y)` of `φ` (`TestFunction.sliceRight`). It is a
test function on `Ω`: it is smooth, with derivatives
`∂_v (x ↦ T (φ (x, ·))) = x ↦ T (∂_{(v, 0)} φ (x, ·))`, and it is supported in the first
projection of the support of `φ`. The partial pairing is continuous for the LF topologies
(`Distribution.partialPairing`).

For complex-valued distributions `S` on `Ω` and `T` on `O`, the **tensor product** `S ⊗ T` is the
distribution on `V`

`(S ⊗ T) φ = S (x ↦ T (φ (x, ·)))`,

where `S` is applied to the complex test function `x ↦ T (φ (x, ·))` through its complex-linear
extension `Distribution.complexPairing` (`Distribution.tensorProduct`). On a tensor product of
real test functions it is the product of the pairings,

`(S ⊗ T) ((x, y) ↦ φ x ψ y) = S φ * T ψ`,

and when `D` is also finite-dimensional and `V = Ω ×ˢ O` it is the only distribution with this
property, because such tensor products span a dense subspace of the test functions on `Ω ×ˢ O`
(`TestFunction.ext_prodSMulCLM`). The tensor product is bilinear and satisfies the Leibniz rule
`∂_{(v, w)} (S ⊗ T) = ∂_{v} S ⊗ T + S ⊗ ∂_{w} T`; when `D` is also finite-dimensional it is
supported in the product of the supports. The tensor product of the point masses at `a` and `b`
is the point mass at `(a, b)`.

## Main declarations

* `Distribution.partialPairing`: the continuous linear map `φ ↦ (x ↦ T (φ (x, ·)))`.
* `Distribution.lineDerivOp_partialPairing`: its derivatives,
  `∂_v (x ↦ T (φ (x, ·))) = x ↦ T (∂_{(v, 0)} φ (x, ·))`.
* `Distribution.tsupport_partialPairing_subset`: its support.
* `Distribution.partialPairing_lineDerivOp_zero_prod`: derivatives in the second variable move to
  the distribution.
* `Distribution.tensorProduct`: the tensor product `S ⊗ T` of complex-valued distributions.
* `Distribution.tensorProduct_prodSMulCLM`: `(S ⊗ T) (φ ⊗ ψ) = S φ * T ψ`, and
  `Distribution.complexPairing_tensorProduct_prodSMulCLM` for complex test functions `φ`.
* `Distribution.complexPairing_tensorProduct_eq_mul`: the same for complex test functions `φ` and
  `ψ`.
* `Distribution.tensorProduct_eq`: uniqueness of the tensor product.
* `Distribution.lineDerivOp_tensorProduct`: `∂_{(v, w)} (S ⊗ T) = ∂_{v} S ⊗ T + S ⊗ ∂_{w} T`.
* `Distribution.tensorProduct_delta`: `δ_a ⊗ δ_b = δ_(a, b)`.
* `Distribution.dsupport_tensorProduct_subset`: `supp (S ⊗ T) ⊆ supp S ×ˢ supp T`.

## Implementation notes

Smoothness of `x ↦ T (φ (x, ·))` rests on the finite order of `T` on each compact set
(`Distribution.exists_norm_apply_le`): the first-order Taylor remainder
`y ↦ φ (x + h, y) - φ (x, y) - Dφ(x, y) (h, 0)` is supported in a fixed compact set and all of its
derivatives in `y` are `o(‖h‖)` uniformly
(`HasCompactSupport.exists_norm_iteratedFDeriv_prod_right_sub_sub_le`), so its image under `T` is
`o(‖h‖)` as well (`Distribution.isLittleO_apply_of_norm_iteratedFDeriv_le`). Iterating the
derivative formula bounds the `i`-th derivative of the partial pairing by the derivatives of `φ` of
order at most `N + i`, where `N` is the order of `T` on the second projection of a compact set
containing the support of `φ`; this is the continuity estimate.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §5.1 and
  Theorem 5.1.1 (existence and uniqueness of the tensor product of distributions).
* C. Brouder, N. V. Dang and F. Hélein, *Continuity of the fundamental operations on
  distributions having a specified wave front set (with a counter example by Semyon Alesker)*,
  Studia Math. 232 (2016), arXiv:1409.7662v2, §4 (tensor products of distributions).
-/

public section

noncomputable section

open Set Filter Topology TopologicalSpace TestFunction LineDeriv Metric Complex
open scoped Distributions ContDiff

namespace Distribution

variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {O : Opens D} {V : Opens (E × D)}

/-! ### The partial pairing -/

section PartialPairing

/-- The function `x ↦ T (φ (x, ·))`. -/
private def pairingFun (T : 𝓓'(O, F)) (hO : MapsTo Prod.snd (V : Set (E × D)) O)
    (φ : 𝓓(V, ℝ)) (x : E) : F :=
  T (sliceRight hO φ x)

private theorem pairingFun_add (T : 𝓓'(O, F)) (hO : MapsTo Prod.snd (V : Set (E × D)) O)
    (φ ψ : 𝓓(V, ℝ)) (x : E) :
    pairingFun T hO (φ + ψ) x = pairingFun T hO φ x + pairingFun T hO ψ x := by
  simp [pairingFun]

private theorem pairingFun_smul (T : 𝓓'(O, F)) (hO : MapsTo Prod.snd (V : Set (E × D)) O)
    (c : ℝ) (φ : 𝓓(V, ℝ)) (x : E) : pairingFun T hO (c • φ) x = c • pairingFun T hO φ x := by
  simp [pairingFun]

/-- The partial pairing vanishes off the first projection of the support of `φ`. -/
private theorem tsupport_pairingFun_subset (T : 𝓓'(O, F))
    (hO : MapsTo Prod.snd (V : Set (E × D)) O) (φ : 𝓓(V, ℝ)) :
    tsupport (pairingFun T hO φ) ⊆ Prod.fst '' tsupport φ := by
  refine closure_minimal (fun x hx ↦ ?_) (φ.hasCompactSupport.image continuous_fst).isClosed
  by_contra h
  exact hx (by simp [pairingFun, sliceRight_eq_zero h])

/-- The first-order Taylor remainder in the first variable of the slices of `φ` is supported in
the second projection of the support of `φ`. -/
private theorem tsupport_sliceRight_taylor_subset (hO : MapsTo Prod.snd (V : Set (E × D)) O)
    (φ : 𝓓(V, ℝ)) (x h : E) :
    tsupport (sliceRight hO φ (x + h) - sliceRight hO φ x -
      sliceRight hO (∂_{((h, 0) : E × D)} φ) x) ⊆ Prod.snd '' tsupport φ := by
  refine closure_minimal (fun y hy ↦ ?_) (φ.hasCompactSupport.image continuous_snd).isClosed
  by_contra hyK
  have hn (x' : E) : (x', y) ∉ tsupport φ := fun h' ↦ hyK ⟨(x', y), h', rfl⟩
  apply hy
  simp only [sub_apply, sliceRight_apply, TestFunction.lineDerivOp_apply_eq_fderiv]
  rw [image_eq_zero_of_notMem_tsupport (hn _), image_eq_zero_of_notMem_tsupport (hn _),
    Function.notMem_support.1 fun h' ↦ hn x (support_fderiv_subset ℝ h')]
  simp

variable [FiniteDimensional ℝ E]

/-- The partial pairing is differentiable at every point, with derivative in the direction `v`
given by the partial pairing with `∂_{(v, 0)} φ`. -/
private theorem exists_hasFDerivAt_pairingFun (T : 𝓓'(O, F))
    (hO : MapsTo Prod.snd (V : Set (E × D)) O) (φ : 𝓓(V, ℝ)) (x : E) :
    ∃ L : E →L[ℝ] F, HasFDerivAt (pairingFun T hO φ) L x ∧
      ∀ v, L v = pairingFun T hO (∂_{((v, 0) : E × D)} φ) x := by
  let L : E →L[ℝ] F := LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ pairingFun T hO (∂_{((v, 0) : E × D)} φ) x
      map_add' := fun v w ↦ by
        rw [show ((v + w, 0) : E × D) = (v, 0) + (w, 0) by simp, lineDerivOp_left_add,
          pairingFun_add]
      map_smul' := fun c v ↦ by
        rw [show ((c • v, 0) : E × D) = c • (v, 0) by simp, lineDerivOp_left_smul,
          pairingFun_smul, RingHom.id_apply] }
  refine ⟨L, ?_, fun v ↦ rfl⟩
  -- The second projection `K` of the support of `φ`, on which `T` has finite order `N`.
  let K : Compacts D := ⟨Prod.snd '' tsupport φ, φ.hasCompactSupport.image continuous_snd⟩
  have hKO : (K : Set D) ⊆ O := image_subset_iff.2 fun p hp ↦ hO (φ.tsupport_subset hp)
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le hKO
  -- The Taylor remainder of the slices, as test functions on `O` supported in `K`.
  let R (h : E) : 𝓓(O, ℝ) :=
    sliceRight hO φ (x + h) - sliceRight hO φ x - sliceRight hO (∂_{((h, 0) : E × D)} φ) x
  have hR (h : E) :
      (R h : D → ℝ) = fun y ↦ φ (x + h, y) - φ (x, y) - fderiv ℝ φ (x, y) (h, 0) := by
    ext y
    simp only [R, sub_apply, sliceRight_apply, TestFunction.lineDerivOp_apply_eq_fderiv]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (isLittleO_apply_of_norm_iteratedFDeriv_le hC hT
    (.of_forall fun h ↦ tsupport_sliceRight_taylor_subset hO φ x h) fun i _ ε hε ↦ ?_).congr_left
    fun h ↦ by simp [pairingFun, L]
  obtain ⟨r, hr, hrem⟩ := φ.hasCompactSupport.exists_norm_iteratedFDeriv_prod_right_sub_sub_le
    φ.contDiff (i := i) (by exact_mod_cast le_top) x hε
  exact eventually_nhds_iff_ball.2 ⟨r, hr, fun h hh ↦ by
    rw [hR]
    exact hrem h (mem_ball_zero_iff.1 hh)⟩

private theorem differentiable_pairingFun (T : 𝓓'(O, F))
    (hO : MapsTo Prod.snd (V : Set (E × D)) O) (φ : 𝓓(V, ℝ)) :
    Differentiable ℝ (pairingFun T hO φ) := fun x ↦
  let ⟨_, hL, _⟩ := exists_hasFDerivAt_pairingFun T hO φ x
  hL.differentiableAt

private theorem fderiv_pairingFun_apply (T : 𝓓'(O, F))
    (hO : MapsTo Prod.snd (V : Set (E × D)) O) (φ : 𝓓(V, ℝ)) (x v : E) :
    fderiv ℝ (pairingFun T hO φ) x v = pairingFun T hO (∂_{((v, 0) : E × D)} φ) x := by
  obtain ⟨L, hL, hLv⟩ := exists_hasFDerivAt_pairingFun T hO φ x
  rw [hL.fderiv, hLv]

private theorem contDiff_pairingFun (T : 𝓓'(O, F)) (hO : MapsTo Prod.snd (V : Set (E × D)) O)
    (φ : 𝓓(V, ℝ)) : ContDiff ℝ ∞ (pairingFun T hO φ) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing φ with
  | zero => exact contDiff_zero.2 (differentiable_pairingFun T hO φ).continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨differentiable_pairingFun T hO φ, by simp, contDiff_clm_apply_iff.2 fun v ↦ ?_⟩
    simpa only [fderiv_pairingFun_apply] using ih (∂_{((v, 0) : E × D)} φ)

/-- **Finite-order estimate for the partial pairing.** For a compact `K ⊆ V` there are an order
`N` and a constant `C` such that the `i`-th derivative of `x ↦ T (φ (x, ·))` is bounded by `C * M`
for every test function `φ` supported in `K` whose derivatives of order at most `N + i` are
bounded by `M`. -/
private theorem exists_norm_iteratedFDeriv_pairingFun_le (T : 𝓓'(O, F))
    (hO : MapsTo Prod.snd (V : Set (E × D)) O) {K : Compacts (E × D)}
    (hK : (K : Set (E × D)) ⊆ V) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (i : ℕ) (φ : 𝓓(V, ℝ)), tsupport φ ⊆ K → ∀ M, 0 ≤ M →
      (∀ j ≤ N + i, ∀ p, ‖iteratedFDeriv ℝ j φ p‖ ≤ M) →
        ∀ x, ‖iteratedFDeriv ℝ i (pairingFun T hO φ) x‖ ≤ C * M := by
  let K₂ : Compacts D := K.map Prod.snd continuous_snd
  have hK₂ : (K₂ : Set D) ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact hO (hK hp)
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le hK₂
  refine ⟨N, C, hC, fun i ↦ ?_⟩
  induction i with
  | zero =>
    intro φ hφ M hM hφM x
    rw [norm_iteratedFDeriv_zero]
    refine hT _ ((tsupport_sliceRight_subset_image_snd φ x).trans (image_mono hφ)) M hM
      fun j hj y ↦ ?_
    exact (norm_iteratedFDeriv_sliceRight_le φ j x y).trans (hφM j (by omega) _)
  | succ i ih =>
    intro φ hφ M hM hφM x
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
    -- The last direction `w` of `m` is moved into the test function: the derivative of the
    -- partial pairing with `φ` in the direction `w` is the partial pairing with `∂_{(w, 0)} φ`.
    set w := m (Fin.last i)
    have hfun : (fun x ↦ fderiv ℝ (pairingFun T hO φ) x w) =
        pairingFun T hO (∂_{((w, 0) : E × D)} φ) :=
      funext fun x ↦ fderiv_pairingFun_apply T hO φ x w
    have hd : ContDiff ℝ ∞ (fderiv ℝ (pairingFun T hO φ)) :=
      (contDiff_pairingFun T hO φ).fderiv_right (by simp)
    have happ := (ContinuousLinearMap.apply ℝ F w).iteratedFDeriv_comp_left hd.contDiffAt
      (i := i) (x := x) (mod_cast le_top)
    have key : iteratedFDeriv ℝ i (fun y ↦ fderiv ℝ (pairingFun T hO φ) y) x (Fin.init m) w =
        iteratedFDeriv ℝ i (pairingFun T hO (∂_{((w, 0) : E × D)} φ)) x (Fin.init m) := by
      simpa [Function.comp_def, hfun] using (congrArg (· (Fin.init m)) happ).symm
    rw [iteratedFDeriv_succ_apply_right, key]
    -- The derivatives of `∂_{(w, 0)} φ` of order at most `N + i` are bounded by `M * ‖w‖`.
    have hbd := ih (∂_{((w, 0) : E × D)} φ) ((tsupport_lineDerivOp_subset φ _).trans hφ)
      (M * ‖w‖) (by positivity) (fun j hj p ↦ ?_) x
    · calc ‖iteratedFDeriv ℝ i (pairingFun T hO (∂_{((w, 0) : E × D)} φ)) x (Fin.init m)‖
          ≤ ‖iteratedFDeriv ℝ i (pairingFun T hO (∂_{((w, 0) : E × D)} φ)) x‖ *
              ∏ j, ‖Fin.init m j‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ C * (M * ‖w‖) * ∏ j, ‖Fin.init m j‖ := by gcongr
        _ = C * M * ∏ j, ‖m j‖ := by
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.init, w]
          ring
    · rw [show ((∂_{((w, 0) : E × D)} φ : 𝓓(V, ℝ)) : E × D → ℝ) =
          fun p ↦ fderiv ℝ φ p (w, 0) from funext (lineDerivOp_apply_eq_fderiv φ _)]
      refine (ContDiff.norm_iteratedFDeriv_fderiv_apply_le φ.contDiff (by simp) _ p).trans ?_
      rw [show ‖((w, 0) : E × D)‖ = ‖w‖ by simp]
      exact mul_le_mul_of_nonneg_right (hφM (j + 1) (by omega) p) (norm_nonneg _)

/-- The partial pairing on test functions supported in a fixed compact set `K`, as a continuous
linear map into the test functions supported in the first projection of `K`. -/
private def pairingSupportedInCLM (T : 𝓓'(O, F))
    (hV : (V : Set (E × D)) ⊆ (Ω : Set E) ×ˢ (O : Set D)) (K : Compacts (E × D))
    (hK : (K : Set (E × D)) ⊆ V) :
    𝓓_{K}(E × D, ℝ) →L[ℝ] 𝓓_{K.map Prod.fst continuous_fst}(E, F) :=
  letI hO : MapsTo Prod.snd (V : Set (E × D)) O := mapsTo_snd_prod.mono_left hV
  letI P : 𝓓_{K}(E × D, ℝ) →ₗ[ℝ] 𝓓_{K.map Prod.fst continuous_fst}(E, F) :=
    { toFun f := ⟨pairingFun T hO (ofSupportedInCLM ℝ hK f),
        contDiff_pairingFun T hO _,
        fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx
          (image_mono (f.tsupport_subset) (tsupport_pairingFun_subset T hO _ h))⟩
      map_add' f g := ContDiffMapSupportedIn.ext fun x ↦ by
        simp only [map_add]
        exact pairingFun_add T hO _ _ x
      map_smul' c f := ContDiffMapSupportedIn.ext fun x ↦ by
        simp only [map_smul]
        exact pairingFun_smul T hO c _ x }
  { toLinearMap := P
    cont := by
      obtain ⟨N, C, hC, hbound⟩ := exists_norm_iteratedFDeriv_pairingFun_le T hO hK
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨Finset.range (N + i + 1), C, fun f ↦ ((P f).seminorm_le_iff ℝ
        (mul_nonneg hC (apply_nonneg _ _)) i).2 fun _ x _ ↦ ?_⟩
      exact hbound i _ f.tsupport_subset _ (apply_nonneg _ _) (fun j hj p ↦
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
          (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (by omega)))) x }

/-- The **partial pairing** of a distribution `T` on `O` with test functions on `V ⊆ Ω ×ˢ O`: the
continuous linear map sending a test function `φ` on `V` to the test function
`x ↦ T (φ (x, ·))` on `Ω`. -/
def partialPairing (T : 𝓓'(O, F)) (hV : (V : Set (E × D)) ⊆ (Ω : Set E) ×ˢ (O : Set D)) :
    𝓓(V, ℝ) →L[ℝ] 𝓓(Ω, F) :=
  letI hO : MapsTo Prod.snd (V : Set (E × D)) O := mapsTo_snd_prod.mono_left hV
  TestFunction.limitCLM ℝ
    (fun φ ↦ ⟨pairingFun T hO φ, contDiff_pairingFun T hO φ,
      (φ.hasCompactSupport.image continuous_fst).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_pairingFun_subset T hO φ),
      (tsupport_pairingFun_subset T hO φ).trans
        (image_subset_iff.2 fun _ hp ↦ (hV (φ.tsupport_subset hp)).1)⟩)
    (fun K hK ↦ ofSupportedInCLM ℝ (by
        rintro _ ⟨p, hp, rfl⟩
        exact (hV (hK hp)).1) ∘L
      pairingSupportedInCLM T hV K hK)
    (fun _ _ _ ↦ rfl)

variable (T : 𝓓'(O, F)) {hV : (V : Set (E × D)) ⊆ (Ω : Set E) ×ˢ (O : Set D)}

/-- The partial pairing of `T` with `φ` is `x ↦ T (φ (x, ·))`. -/
@[simp]
theorem partialPairing_apply (φ : 𝓓(V, ℝ)) (x : E) :
    T.partialPairing hV φ x =
      T (sliceRight (mapsTo_snd_prod.mono_left hV) φ x) :=
  (rfl)

/-- **Derivatives of the partial pairing.** The derivative of `x ↦ T (φ (x, ·))` in the direction
`v` is `x ↦ T (∂_{(v, 0)} φ (x, ·))`. -/
theorem lineDerivOp_partialPairing (φ : 𝓓(V, ℝ)) (v : E) :
    ∂_{v} (T.partialPairing hV φ) = T.partialPairing hV (∂_{((v, 0) : E × D)} φ) := by
  ext x
  rw [TestFunction.lineDerivOp_apply_eq_fderiv]
  exact fderiv_pairingFun_apply T _ φ x v

/-- The partial pairing of `T` with `φ` is supported in the first projection of the support of
`φ`. -/
theorem tsupport_partialPairing_subset (φ : 𝓓(V, ℝ)) :
    tsupport (T.partialPairing hV φ) ⊆ Prod.fst '' tsupport φ :=
  tsupport_pairingFun_subset T _ φ

/-- The partial pairing of `T` with a tensor product `(x, y) ↦ ψ y φ x` is `x ↦ φ x • T ψ`. -/
theorem partialPairing_prodSMulCLM_apply (ψ : 𝓓(O, ℝ))
    (hV' : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (φ : 𝓓(Ω, ℝ)) (x : E) :
    T.partialPairing hV (prodSMulCLM ψ hV' φ) x = φ x • T ψ := by
  rw [partialPairing_apply, sliceRight_prodSMulCLM, map_smul]

/-- The partial pairing of `T` with a derivative of `φ` in the second variable is minus the partial
pairing of `∂_{w} T` with `φ`. -/
theorem partialPairing_lineDerivOp_zero_prod (φ : 𝓓(V, ℝ)) (w : D) :
    T.partialPairing hV (∂_{((0, w) : E × D)} φ) = -(∂_{w} T).partialPairing hV φ := by
  ext x
  simp [sliceRight_lineDerivOp_zero_prod]

/-- The partial pairing is additive in the distribution. -/
@[simp]
theorem partialPairing_add (T' : 𝓓'(O, F)) :
    (T + T').partialPairing hV = T.partialPairing hV + T'.partialPairing hV := by
  ext φ x
  simp

/-- The partial pairing is homogeneous in the distribution. -/
@[simp]
theorem partialPairing_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (φ : 𝓓(V, ℝ)) :
    (c • T).partialPairing hV φ = c • T.partialPairing hV φ := by
  ext x
  simp

end PartialPairing

/-! ### The tensor product -/

section TensorProduct

variable [FiniteDimensional ℝ E] (S : 𝓓'(Ω, ℂ)) (T : 𝓓'(O, ℂ))
  (hV : (V : Set (E × D)) ⊆ (Ω : Set E) ×ˢ (O : Set D))

/-- The **tensor product** `S ⊗ T` of complex-valued distributions `S` on `Ω` and `T` on `O`, as a
distribution on an open set `V ⊆ Ω ×ˢ O`: `(S ⊗ T) φ = S (x ↦ T (φ (x, ·)))`, where `S` acts on
the complex test function `x ↦ T (φ (x, ·))` through its complex-linear extension. -/
def tensorProduct : 𝓓'(V, ℂ) :=
  (S.complexPairing.restrictScalars ℝ).comp (T.partialPairing hV)

theorem tensorProduct_apply (φ : 𝓓(V, ℝ)) :
    S.tensorProduct T hV φ = S.complexPairing (T.partialPairing hV φ) :=
  (rfl)

/-- The partial pairing of `T` with a tensor product of real test functions is `T ψ` times `φ`,
viewed as a complex test function. -/
private theorem partialPairing_prodSMulCLM (ψ : 𝓓(O, ℝ))
    (hV' : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (φ : 𝓓(Ω, ℝ)) :
    T.partialPairing hV (prodSMulCLM ψ hV' φ) = T ψ • postcompCLM (𝕜 := ℝ) ofRealCLM φ := by
  ext x
  rw [partialPairing_prodSMulCLM_apply]
  simp [mul_comm]

/-- **The tensor product on tensor products of test functions.**
`(S ⊗ T) ((x, y) ↦ φ x ψ y) = S φ * T ψ`. -/
@[simp]
theorem tensorProduct_prodSMulCLM (ψ : 𝓓(O, ℝ)) (hV' : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    (φ : 𝓓(Ω, ℝ)) : S.tensorProduct T hV (prodSMulCLM ψ hV' φ) = S φ * T ψ := by
  rw [tensorProduct_apply, partialPairing_prodSMulCLM, map_smul,
    complexPairing_postcompCLM_ofRealCLM, smul_eq_mul, mul_comm]

/-- The tensor product on a complex test function `φ` on `Ω` tensored with a real test function
`ψ` on `O`: `(S ⊗ T) ((x, y) ↦ φ x ψ y) = S φ * T ψ`, with `S` and `S ⊗ T` acting on complex test
functions through their complex-linear extensions. -/
theorem complexPairing_tensorProduct_prodSMulCLM (ψ : 𝓓(O, ℝ))
    (hV' : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (φ : 𝓓(Ω, ℂ)) :
    (S.tensorProduct T hV).complexPairing (prodSMulCLM ψ hV' φ) = S.complexPairing φ * T ψ := by
  -- Real and imaginary parts commute with tensoring by the real test function `ψ`.
  have hpart (L : ℂ →L[ℝ] ℝ) : postcompCLM (𝕜 := ℝ) L (prodSMulCLM ψ hV' φ) =
      prodSMulCLM ψ hV' (postcompCLM (𝕜 := ℝ) L φ) := by
    ext p
    simp only [postcompCLM_apply, prodSMulCLM_apply, Function.comp_apply, map_smul]
  rw [complexPairing_apply, complexPairing_apply, hpart, hpart, tensorProduct_prodSMulCLM,
    tensorProduct_prodSMulCLM]
  ring

/-- The tensor product on a tensor product of complex test functions: if `χ (x, y) = φ x * ψ y`,
then `(S ⊗ T) χ = S φ * T ψ`, with all three distributions acting on complex test functions
through their complex-linear extensions. -/
theorem complexPairing_tensorProduct_eq_mul (hV' : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    {φ : 𝓓(Ω, ℂ)} {ψ : 𝓓(O, ℂ)} {χ : 𝓓(V, ℂ)} (hχ : ∀ p, χ p = φ p.1 * ψ p.2) :
    (S.tensorProduct T hV).complexPairing χ = S.complexPairing φ * T.complexPairing ψ := by
  -- Split `ψ` into its real and imaginary parts, which are real test functions.
  have h : χ = prodSMulCLM (postcompCLM (𝕜 := ℝ) reCLM ψ) hV' φ +
      I • prodSMulCLM (postcompCLM (𝕜 := ℝ) imCLM ψ) hV' φ := by
    ext p
    rw [hχ]
    simp only [add_apply, prodSMulCLM_apply, postcompCLM_apply, Function.comp_apply, reCLM_apply,
      real_smul, smul_apply, imCLM_apply, smul_eq_mul]
    conv_lhs => rw [← re_add_im (ψ p.2)]
    ring
  rw [h, map_add, map_smul, complexPairing_tensorProduct_prodSMulCLM,
    complexPairing_tensorProduct_prodSMulCLM, complexPairing_apply T ψ, smul_eq_mul]
  ring

/-- **Uniqueness of the tensor product.** When `V = Ω ×ˢ O`, the tensor product `S ⊗ T` is the
only distribution on `V` taking the value `S φ * T ψ` on every tensor product
`(x, y) ↦ φ x ψ y` of real test functions. -/
theorem tensorProduct_eq [FiniteDimensional ℝ D]
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) {U : 𝓓'(V, ℂ)}
    (h : ∀ (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)), U (prodSMulCLM ψ hV.symm.subset φ) = S φ * T ψ) :
    S.tensorProduct T hV.subset = U :=
  ext_prodSMulCLM hV fun ψ φ ↦ by rw [tensorProduct_prodSMulCLM, h]

@[simp]
theorem add_tensorProduct (S' : 𝓓'(Ω, ℂ)) :
    (S + S').tensorProduct T hV = S.tensorProduct T hV + S'.tensorProduct T hV := by
  ext φ
  simp [tensorProduct_apply]

@[simp]
theorem tensorProduct_add (T' : 𝓓'(O, ℂ)) :
    S.tensorProduct (T + T') hV = S.tensorProduct T hV + S.tensorProduct T' hV := by
  ext φ
  simp [tensorProduct_apply]

@[simp]
theorem smul_tensorProduct (c : ℂ) :
    (c • S).tensorProduct T hV = c • S.tensorProduct T hV := by
  ext φ
  simp [tensorProduct_apply]

@[simp]
theorem tensorProduct_smul (c : ℂ) :
    S.tensorProduct (c • T) hV = c • S.tensorProduct T hV := by
  ext φ
  simp [tensorProduct_apply]

/-- **Derivatives of the tensor product.**
`∂_{(v, w)} (S ⊗ T) = (∂_{v} S) ⊗ T + S ⊗ (∂_{w} T)`. -/
theorem lineDerivOp_tensorProduct (v : E) (w : D) :
    ∂_{(v, w)} (S.tensorProduct T hV) =
      (∂_{v} S).tensorProduct T hV + S.tensorProduct (∂_{w} T) hV := by
  ext φ
  rw [lineDerivOp_apply_apply, show ((v, w) : E × D) = (v, 0) + (0, w) by simp,
    lineDerivOp_left_add, add_apply, tensorProduct_apply, tensorProduct_apply,
    tensorProduct_apply]
  simp only [map_neg, map_add, ← lineDerivOp_partialPairing, partialPairing_lineDerivOp_zero_prod,
    complexPairing_lineDerivOp]
  abel

/-- The tensor product of two complex point masses is the point mass at the pair:
`δ_a ⊗ δ_b = δ_(a, b)`. -/
@[simp]
theorem tensorProduct_delta (a : E) (b : D) :
    (mapCLM ofRealCLM (delta a : 𝓓'(Ω, ℝ))).tensorProduct
        (mapCLM ofRealCLM (delta b : 𝓓'(O, ℝ))) hV =
      mapCLM ofRealCLM (delta (a, b) : 𝓓'(V, ℝ)) := by
  ext φ
  simp [tensorProduct_apply]

/-- **Support of the tensor product.** `supp (S ⊗ T) ⊆ supp S ×ˢ supp T`. -/
theorem dsupport_tensorProduct_subset [FiniteDimensional ℝ D] :
    dsupport (S.tensorProduct T hV) ⊆ dsupport S ×ˢ dsupport T := by
  refine sInter_subset_of_mem ⟨fun φ hφ ↦ ?_, isClosed_dsupport.prod isClosed_dsupport⟩
  -- `B` is the first projection of the part of the support of `φ` lying over `supp T`. Off `B`
  -- every slice of `φ` is supported off `supp T`, and `B` does not meet `supp S`.
  set B := Prod.fst '' (tsupport φ ∩ Prod.snd ⁻¹' dsupport T)
  have hB : IsClosed B := ((φ.hasCompactSupport.isCompact.inter_right
    (isClosed_dsupport.preimage continuous_snd)).image continuous_fst).isClosed
  have hzero (x : E) (hx : x ∉ B) : T.partialPairing hV φ x = 0 := by
    rw [partialPairing_apply]
    exact map_eq_zero_of_disjoint_dsupport T (disjoint_left.2 fun y hy hyT ↦
      hx ⟨(x, y), ⟨tsupport_sliceRight_subset φ x hy, hyT⟩, rfl⟩)
  have hSB : dsupport S ⊆ Bᶜ := by
    rintro x hxS ⟨p, ⟨hp, hpT⟩, rfl⟩
    exact hφ hp ⟨hxS, hpT⟩
  rw [tensorProduct_apply, complexPairing_eq_of_eventuallyEq S (ψ := 0)
    (eventually_of_mem (hB.isOpen_compl.mem_nhdsSet.2 hSB) fun x hx ↦ by simp [hzero x hx]),
    map_zero]

end TensorProduct

end Distribution
