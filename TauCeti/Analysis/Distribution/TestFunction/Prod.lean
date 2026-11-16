/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Topology.Algebra.Support

/-!
# Tensor products and slices of test functions

Let `Ω ⊆ E` and `O ⊆ D` be open subsets of real normed spaces and let `ψ` be a real test function
on `O`. For a test function `φ` on `Ω`, the function `(x, t) ↦ ψ t • φ x` is a test function on
`Ω × O`, supported in `tsupport φ ×ˢ tsupport ψ`. For fixed `ψ` this tensor product is continuous
for the LF topologies (`TestFunction.prodSMulCLM`), with values in the test functions on any open
set containing `Ω ×ˢ O`.

Tensoring with a fixed profile in an extra variable turns tests on `Ω` into tests on a product
without enlarging their support in the first factor. Composed with a pullback along a map of the
form `(x, t) ↦ (Φ (x, t), t)`, it cuts off the pullback of a test form along a map `Φ` that is
proper only on bounded slabs `Ω × [c, d]`.

Conversely, a test function `φ` on an open set `V ⊆ E × D` has slices `y ↦ φ (x, y)`, which are
test functions on every open set `O ⊆ D` containing the second projection of `V`
(`TestFunction.sliceRight`). Pairing the slices with a distribution on `O` is the first step of
the tensor product of distributions.

For complex smooth functions `φ` supported in a compact set `K₁ ⊆ E` and `ψ` supported in a
compact set `K₂ ⊆ D`, the tensor product `(x, y) ↦ φ x * ψ y` is a smooth function supported in
`K₁ ×ˢ K₂` (`ContDiffMapSupportedIn.tensor`), bilinear in `φ` and `ψ`. Likewise, for complex test
functions `φ` on `Ω` and `ψ` on `O` it is a test function on any open set containing `Ω ×ˢ O`
(`TestFunction.tensor`). These are the tensor products of test functions against which Schwartz
kernels are tested. On an open subset `W` of the `L^p` product `WithLp p (E × D)`, test functions
`φ` on `Ω` and `ψ` on `O` supported close enough to a point of `W` have the product test function
`(x, y) ↦ φ x * ψ y` on `W` (`TestFunction.exists_nhds_prod_cutoff`).

## Main declarations

* `TestFunction.prodSMulCLM`: the continuous linear map `φ ↦ ((x, t) ↦ ψ t • φ x)`.
* `TestFunction.prodSMulCLM_apply`: its values.
* `TestFunction.tsupport_prodSMulCLM_subset`: its support lies in `tsupport φ ×ˢ tsupport ψ`.
* `TestFunction.sliceRight`: the slice `y ↦ φ (x, y)` of a test function on a product, with its
  support `TestFunction.tsupport_sliceRight_subset`, derivative bound
  `TestFunction.norm_iteratedFDeriv_sliceRight_le` and derivatives
  `TestFunction.sliceRight_lineDerivOp_zero_prod`.
* `TestFunction.tensor`: the tensor product `(x, y) ↦ φ x * ψ y` of complex test functions on
  `Ω` and `O`, with `TestFunction.tensor_apply`, its support `TestFunction.tsupport_tensor_subset`
  and its bilinearity.
* `TestFunction.exists_nhds_prod_cutoff`: products of test functions supported near a point
  of an open subset of `WithLp p (E × D)` are test functions on it.
* `ContDiffMapSupportedIn.tensor`: the tensor product `(x, y) ↦ φ x * ψ y` of complex smooth
  functions `φ`, `ψ` supported in compact sets `K₁`, `K₂`, supported in `K₁ ×ˢ K₂`, with
  `ContDiffMapSupportedIn.tensor_apply` and its bilinearity.
-/

public section

noncomputable section

open Set TopologicalSpace TauCeti LineDeriv WithLp
open scoped Distributions ENNReal Topology

namespace TestFunction

variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {O : Opens D} {V : Opens (E × D)}

/-- The tensor product with `ψ` of tests supported in a compact `K`, which is supported in
`K ×ˢ tsupport ψ`. -/
private def prodSMulSupportedInCLM (ψ : 𝓓(O, ℝ)) (K : Compacts E) :
    𝓓_{K}(E, F) →L[ℝ]
      𝓓_{⟨(K : Set E) ×ˢ tsupport ψ, K.isCompact.prod ψ.hasCompactSupport⟩}(E × D, F) :=
  letI P : 𝓓_{K}(E, F) →ₗ[ℝ]
      𝓓_{⟨(K : Set E) ×ˢ tsupport ψ, K.isCompact.prod ψ.hasCompactSupport⟩}(E × D, F) :=
    { toFun φ := ⟨fun p ↦ ψ p.2 • φ p.1,
        (ψ.contDiff.comp contDiff_snd).smul (φ.contDiff.comp contDiff_fst),
        fun p hp ↦ Function.notMem_support.1 fun h ↦ hp <|
          prod_mono φ.support_subset (subset_tsupport _) (support_snd_smul_fst_subset _ _ h)⟩
      map_add' φ η := ContDiffMapSupportedIn.ext fun p ↦ smul_add (ψ p.2) (φ p.1) (η p.1)
      map_smul' c φ := ContDiffMapSupportedIn.ext fun p ↦ smul_comm (ψ p.2) c (φ p.1) }
  { toLinearMap := P
    cont := by
      -- Leibniz: the `i`-th derivative is controlled by the first `i` derivatives of `φ`, with
      -- constants given by bounds for the derivatives of `ψ`.
      choose M hM using fun j : ℕ ↦
        (ψ.contDiff.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).norm
          |>.bddAbove_range_of_hasCompactSupport (ψ.hasCompactSupport.iteratedFDeriv j).norm
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨Finset.range (i + 1), ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * |M j|,
        fun φ ↦ ((P φ).seminorm_le_iff ℝ (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)
          (apply_nonneg _ _)) i).2 fun _ p _ ↦ ?_⟩
      refine (norm_iteratedFDeriv_smul_le (ψ.contDiff.comp contDiff_snd)
        (φ.contDiff.comp contDiff_fst) p (mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hj : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hψj : ‖iteratedFDeriv ℝ j (ψ ∘ Prod.snd) p‖ ≤ |M j| :=
        (norm_iteratedFDeriv_comp_snd_le p).trans
          ((hM j ⟨p.2, rfl⟩).trans (le_abs_self _))
      have hφj : ‖iteratedFDeriv ℝ (i - j) (φ ∘ Prod.fst) p‖ ≤
          (Finset.range (i + 1)).sup (ContDiffMapSupportedIn.seminorm ℝ E F ⊤ K) φ :=
        (norm_iteratedFDeriv_comp_fst_le p).trans
          ((ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
            (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (by omega))))
      calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun p : E × D ↦ ψ p.2) p‖ *
            ‖iteratedFDeriv ℝ (i - j) (fun p : E × D ↦ φ p.1) p‖
          ≤ (i.choose j : ℝ) * |M j| *
              (Finset.range (i + 1)).sup (ContDiffMapSupportedIn.seminorm ℝ E F ⊤ K) φ := by
            gcongr
            exacts [hψj, hφj] }

/-- The **tensor product with a fixed test function** `ψ` on `O ⊆ D`: the continuous linear map
sending a test function `φ` on `Ω` to the test function `(x, t) ↦ ψ t • φ x` on any open
`V ⊇ Ω ×ˢ O`. -/
def prodSMulCLM (ψ : 𝓓(O, ℝ)) (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) :
    𝓓(Ω, F) →L[ℝ] 𝓓(V, F) :=
  letI T (φ : 𝓓(Ω, F)) : 𝓓(V, F) :=
    ⟨fun p ↦ ψ p.2 • φ p.1, (ψ.contDiff.comp contDiff_snd).smul (φ.contDiff.comp contDiff_fst),
      (φ.hasCompactSupport.prod ψ.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_snd_smul_fst_subset _ _),
      (tsupport_snd_smul_fst_subset _ _).trans
        ((prod_mono φ.tsupport_subset ψ.tsupport_subset).trans hV)⟩
  TestFunction.limitCLM ℝ T
    (fun K hK ↦ ofSupportedInCLM ℝ ((prod_mono hK ψ.tsupport_subset).trans hV) ∘L
      prodSMulSupportedInCLM ψ K)
    (fun _ _ _ ↦ rfl)

variable {ψ : 𝓓(O, ℝ)} {hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V}

/-- The tensor product of `φ` with `ψ` is `(x, t) ↦ ψ t • φ x`. -/
@[simp]
theorem prodSMulCLM_apply (φ : 𝓓(Ω, F)) (p : E × D) :
    prodSMulCLM ψ hV φ p = ψ p.2 • φ p.1 :=
  (rfl)

/-- The tensor product of `φ` with `ψ` is supported in `tsupport φ ×ˢ tsupport ψ`. -/
theorem tsupport_prodSMulCLM_subset (φ : 𝓓(Ω, F)) :
    tsupport (prodSMulCLM ψ hV φ) ⊆ tsupport φ ×ˢ tsupport ψ :=
  tsupport_snd_smul_fst_subset _ _

/-! ### Slices -/

variable {hO : MapsTo Prod.snd (V : Set (E × D)) O}

variable (hO) in
/-- The **slice** `y ↦ φ (x, y)` of a test function `φ` on `V ⊆ E × D` at a point `x : E`, as a
test function on an open set `O ⊆ D` containing the second projection of `V`. -/
def sliceRight (φ : 𝓓(V, F)) (x : E) : 𝓓(O, F) :=
  ⟨fun y ↦ φ (x, y), φ.contDiff.comp (contDiff_const.prodMk contDiff_id),
    (φ.hasCompactSupport.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) φ (by fun_prop)).trans
        fun y hy ↦ ⟨(x, y), hy, rfl⟩),
    (tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) φ (by fun_prop)).trans
      fun y hy ↦ hO (φ.tsupport_subset hy)⟩

/-- The slice of `φ` at `x` is `y ↦ φ (x, y)`. -/
@[simp]
theorem sliceRight_apply (φ : 𝓓(V, F)) (x : E) (y : D) : sliceRight hO φ x y = φ (x, y) :=
  (rfl)

/-- The slice of `φ` at `x` is supported in the slice `{y | (x, y) ∈ tsupport φ}` of the support
of `φ`. -/
theorem tsupport_sliceRight_subset (φ : 𝓓(V, F)) (x : E) :
    tsupport (sliceRight hO φ x) ⊆ Prod.mk x ⁻¹' tsupport φ :=
  tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) φ (by fun_prop)

/-- Every slice of `φ` is supported in the second projection of the support of `φ`. -/
theorem tsupport_sliceRight_subset_image_snd (φ : 𝓓(V, F)) (x : E) :
    tsupport (sliceRight hO φ x) ⊆ Prod.snd '' tsupport φ :=
  (tsupport_sliceRight_subset φ x).trans fun y hy ↦ ⟨(x, y), hy, rfl⟩

/-- The slice of `φ` at a point outside the first projection of its support vanishes. -/
theorem sliceRight_eq_zero {φ : 𝓓(V, F)} {x : E} (hx : x ∉ Prod.fst '' tsupport φ) :
    sliceRight hO φ x = 0 := by
  ext y
  rw [sliceRight_apply, image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨(x, y), h, rfl⟩, zero_apply]

@[simp]
theorem sliceRight_add (φ ψ : 𝓓(V, F)) (x : E) :
    sliceRight hO (φ + ψ) x = sliceRight hO φ x + sliceRight hO ψ x :=
  (rfl)

@[simp]
theorem sliceRight_sub (φ ψ : 𝓓(V, F)) (x : E) :
    sliceRight hO (φ - ψ) x = sliceRight hO φ x - sliceRight hO ψ x :=
  (rfl)

@[simp]
theorem sliceRight_smul (c : ℝ) (φ : 𝓓(V, F)) (x : E) :
    sliceRight hO (c • φ) x = c • sliceRight hO φ x :=
  (rfl)

/-- The derivatives of a slice are bounded by those of the test function:
`‖Dⁱ (y ↦ φ (x, y)) y‖ ≤ ‖Dⁱ φ (x, y)‖`. -/
theorem norm_iteratedFDeriv_sliceRight_le (φ : 𝓓(V, F)) (i : ℕ) (x : E) (y : D) :
    ‖iteratedFDeriv ℝ i (sliceRight hO φ x) y‖ ≤ ‖iteratedFDeriv ℝ i φ (x, y)‖ :=
  φ.contDiff.contDiffAt.norm_iteratedFDeriv_prod_right_le i (mod_cast le_top)

/-- Differentiating in the second variable commutes with taking slices:
`∂_{(0, w)} φ (x, ·) = ∂_{w} (φ (x, ·))`. -/
theorem sliceRight_lineDerivOp_zero_prod (φ : 𝓓(V, F)) (w : D) (x : E) :
    sliceRight hO (∂_{((0, w) : E × D)} φ) x = ∂_{w} (sliceRight hO φ x) := by
  ext y
  have hφ := (φ.contDiff.differentiable (by simp) (x, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
  rw [Function.comp_def, ← funext (sliceRight_apply (hO := hO) φ x)] at hφ
  rw [sliceRight_apply, lineDerivOp_apply_eq_fderiv, lineDerivOp_apply_eq_fderiv, hφ.fderiv]
  simp

/-- The slice of a tensor product of real test functions is a multiple of the second factor:
`(y ↦ ψ y φ x) = φ x • ψ`. -/
theorem sliceRight_prodSMulCLM (ψ : 𝓓(O, ℝ)) (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    (φ : 𝓓(Ω, ℝ)) (x : E) : sliceRight hO (prodSMulCLM ψ hV φ) x = φ x • ψ := by
  ext y
  simp [mul_comm]

/-- Around a point `z` of an open set `W ⊆ WithLp p (E × D)` there are neighbourhoods `B₁` of
`z.fst` and `B₂` of `z.snd` such that test functions `φ` on `Ω` supported in `B₁` and `ψ` on `O`
supported in `B₂` have a product test function `χ (x, y) = φ x * ψ y` on `W`, supported in the
product of their supports. -/
theorem exists_nhds_prod_cutoff {p : ℝ≥0∞} [Fact (1 ≤ p)] {W : Opens (WithLp p (E × D))}
    {z : WithLp p (E × D)} (hz : z ∈ W) :
    ∃ B₁ ∈ 𝓝 z.fst, ∃ B₂ ∈ 𝓝 z.snd, ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)), tsupport φ ⊆ B₁ →
      tsupport ψ ⊆ B₂ → ∃ χ : 𝓓(W, ℂ), (∀ q, χ q = φ q.fst * ψ q.snd) ∧
        tsupport χ ⊆ ofLp ⁻¹' (tsupport φ ×ˢ tsupport ψ) := by
  -- A box `B₁ × B₂` around `z` whose copy in `WithLp p (E × D)` lies in `W`.
  have hW : toLp p ⁻¹' (W : Set (WithLp p (E × D))) ∈ 𝓝 (ofLp z) :=
    (W.isOpen.preimage (prod_continuous_toLp p E D)).mem_nhds (by simpa using hz)
  obtain ⟨B₁, hB₁, B₂, hB₂, hB⟩ := mem_nhds_prod_iff.1 hW
  refine ⟨B₁, hB₁, B₂, hB₂, fun φ ψ hφ hψ ↦ ?_⟩
  -- The product is supported in the compact set `ofLp ⁻¹' (tsupport φ ×ˢ tsupport ψ)`.
  set K : Set (WithLp p (E × D)) := ofLp ⁻¹' (tsupport φ ×ˢ tsupport ψ)
  have hK : IsCompact K :=
    (prodContinuousLinearEquiv p ℝ E D).toHomeomorph.isCompact_preimage.2
      (φ.hasCompactSupport.isCompact.prod ψ.hasCompactSupport.isCompact)
  have hsupp : tsupport (fun q : WithLp p (E × D) ↦ φ q.fst * ψ q.snd) ⊆ K := fun q hq ↦
    ⟨tsupport_comp_subset_preimage φ (continuous_fst.comp (prod_continuous_ofLp p E D))
        (tsupport_mul_subset_left hq),
      tsupport_comp_subset_preimage ψ (continuous_snd.comp (prod_continuous_ofLp p E D))
        (tsupport_mul_subset_right hq)⟩
  have hKW : K ⊆ W := fun q ⟨hq₁, hq₂⟩ ↦ by
    simpa using hB ⟨hφ hq₁, hψ hq₂⟩
  exact ⟨⟨fun q ↦ φ q.fst * ψ q.snd,
    (φ.contDiff.comp (fstL p ℝ E D).contDiff).mul (ψ.contDiff.comp (sndL p ℝ E D).contDiff),
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hKW⟩, fun _ ↦ (rfl), hsupp⟩

section Tensor

variable {n : ℕ∞}

/-- The tensor product `(x, y) ↦ φ x * ψ y` of complex test functions `φ` on `Ω` and `ψ` on `O`,
a test function on every open set `V` containing `Ω ×ˢ O`. -/
def tensor (φ : 𝓓^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) :
    𝓓^{n}(V, ℂ) :=
  have h : tsupport (fun p : E × D ↦ φ p.1 * ψ p.2) ⊆ tsupport φ ×ˢ tsupport ψ := by
    simpa only [smul_eq_mul, mul_comm] using tsupport_snd_smul_fst_subset (ψ : D → ℂ) (φ : E → ℂ)
  ⟨fun p ↦ φ p.1 * ψ p.2, (φ.contDiff.comp contDiff_fst).mul (ψ.contDiff.comp contDiff_snd),
    (φ.hasCompactSupport.prod ψ.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _) h,
    h.trans ((prod_mono φ.tsupport_subset ψ.tsupport_subset).trans hV)⟩

variable (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)

@[simp]
theorem tensor_apply (φ : 𝓓^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) (p : E × D) :
    φ.tensor ψ hV p = φ p.1 * ψ p.2 :=
  (rfl)

/-- The tensor product `φ ⊗ ψ` is supported in `tsupport φ ×ˢ tsupport ψ`. -/
theorem tsupport_tensor_subset (φ : 𝓓^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) :
    tsupport (φ.tensor ψ hV) ⊆ tsupport φ ×ˢ tsupport ψ := by
  simpa only [smul_eq_mul, mul_comm (ψ _), ← tensor_apply hV] using
    tsupport_snd_smul_fst_subset (ψ : D → ℂ) (φ : E → ℂ)

theorem tensor_add_left (φ φ' : 𝓓^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) :
    (φ + φ').tensor ψ hV = φ.tensor ψ hV + φ'.tensor ψ hV := by
  ext p
  simp [add_mul]

theorem tensor_add_right (φ : 𝓓^{n}(Ω, ℂ)) (ψ ψ' : 𝓓^{n}(O, ℂ)) :
    φ.tensor (ψ + ψ') hV = φ.tensor ψ hV + φ.tensor ψ' hV := by
  ext p
  simp [mul_add]

theorem tensor_smul_left (c : ℂ) (φ : 𝓓^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) :
    (c • φ).tensor ψ hV = c • φ.tensor ψ hV := by
  ext p
  simp [mul_assoc]

theorem tensor_smul_right (c : ℂ) (φ : 𝓓^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(O, ℂ)) :
    φ.tensor (c • ψ) hV = c • φ.tensor ψ hV := by
  ext p
  simp [mul_left_comm]

end Tensor

end TestFunction

namespace ContDiffMapSupportedIn

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {K₁ : Compacts E} {K₂ : Compacts D}

/-- The tensor product `(x, y) ↦ φ x * ψ y` of smooth functions `φ` supported in `K₁` and `ψ`
supported in `K₂`, a smooth function supported in `K₁ ×ˢ K₂`. -/
def tensor (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) : 𝓓_{K₁ ×ˢ K₂}(E × D, ℂ) :=
  .of_support_subset ((φ.contDiff.comp contDiff_fst).mul (ψ.contDiff.comp contDiff_snd))
    fun _ hp ↦ ⟨φ.support_subset (left_ne_zero_of_mul hp),
      ψ.support_subset (right_ne_zero_of_mul hp)⟩

@[simp]
theorem tensor_apply (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) (p : E × D) :
    φ.tensor ψ p = φ p.1 * ψ p.2 :=
  (rfl)

theorem tensor_add_left (φ φ' : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) :
    (φ + φ').tensor ψ = φ.tensor ψ + φ'.tensor ψ := by
  ext p
  simp [add_mul]

theorem tensor_add_right (φ : 𝓓_{K₁}(E, ℂ)) (ψ ψ' : 𝓓_{K₂}(D, ℂ)) :
    φ.tensor (ψ + ψ') = φ.tensor ψ + φ.tensor ψ' := by
  ext p
  simp [mul_add]

theorem tensor_smul_left (c : ℂ) (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) :
    (c • φ).tensor ψ = c • φ.tensor ψ := by
  ext p
  simp [mul_assoc]

theorem tensor_smul_right (c : ℂ) (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) :
    φ.tensor (c • ψ) = c • φ.tensor ψ := by
  ext p
  simp [mul_left_comm]

end ContDiffMapSupportedIn
