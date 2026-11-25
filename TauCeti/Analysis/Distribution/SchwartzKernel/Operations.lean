/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LinearEquiv
public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.SchwartzKernel.Basic
public import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity

/-!
# Operations on Schwartz kernels

A distribution `K` on an open set `V ⊇ Ω × O` is the Schwartz kernel of the operator
`A_K = Distribution.kernelOperator hV K : 𝓓(O) → 𝓓'(Ω)`, `⟨A_K ψ, φ⟩ = K (φ ⊗ ψ)`. This file
translates the basic operations on operators into operations on their kernels, and reads the
support of the operator off the support of its kernel.

* **Transpose.** The kernel `Kᵗ (y, x) = K (x, y)` with swapped variables, the transport of `K`
  along the swap `D × E ≃ E × D`, is the kernel of the transposed operator:
  `⟨A_{Kᵗ} φ, ψ⟩ = ⟨A_K ψ, φ⟩`. The transposed operator is the one used to extend an operator
  to distributions.
* **Restriction.** Restricting the kernel to a smaller product `Ω' × O'` gives the operator
  that extends inputs by zero and restricts outputs to `Ω'`.
* **Multiplication.** Multiplying the kernel by `f (x)` multiplies the outputs by `f`, and
  multiplying it by `g (y)` multiplies the inputs by `g`.
* **Support.** The output `A_K ψ` is supported in the projection to `E` of
  `supp K ∩ (E × supp ψ)`. In particular, when this set is compact, as it is for a properly
  supported kernel, `A_K` maps tests to compactly supported distributions. Conversely the kernel
  vanishes on an open rectangle `s × t` exactly when `⟨A_K ψ, φ⟩ = 0` for all tests `φ`
  supported in `s` and `ψ` supported in `t`. So the outputs of `A_K` are supported in a closed set
  `C` exactly when `K` vanishes on `(E \ C) × D`, and `A_K` ignores the inputs on an open set `t`
  exactly when `K` vanishes on `E × t`.
* **Integral kernels.** A kernel given by a locally integrable function `k` on `V`, for the product
  `μ × ν` of measures on `E` and `D`, is the kernel of the integral operator
  `ψ ↦ (x ↦ ∫ ψ y • k (x, y) dν(y))`. For instance the constant kernel `1` on `ℝ × ℝ` sends every
  test function of integral one to the constant function `1`: a smooth kernel need not preserve
  compact supports.

## Main declarations

* `Distribution.kernelOperator_transportCLM_prodComm`: the kernel with swapped variables is the
  kernel of the transposed operator.
* `Distribution.kernelOperator_restrictCLM`: restriction of kernels.
* `Distribution.kernelOperator_smulLeftCLM_fst`, `Distribution.kernelOperator_smulLeftCLM_snd`:
  multiplication of kernels by smooth functions of either variable.
* `Distribution.dsupport_kernelOperator_subset`: the support of an output, and
  `Distribution.isCompact_dsupport_kernelOperator` its compactness.
* `Distribution.isVanishingOn_prod_iff_kernelOperator`: the kernel vanishes on an open rectangle
  `s × t` exactly when the operator does, with the special cases
  `Distribution.isVanishingOn_prod_univ_iff_kernelOperator` (output support) and
  `Distribution.isVanishingOn_univ_prod_iff_kernelOperator_eq_zero` (inputs that are ignored),
  and `Distribution.dsupport_kernelOperator_subset_iff` for the output support in a closed set.
* `Distribution.kernelOperator_ofFun`: function kernels give integral operators, whose outputs are
  locally integrable by `Distribution.locallyIntegrableOn_integral_smul`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §5.2 (the Schwartz kernel theorem, the transposed kernel and the supports of
  kernels).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions

namespace Distribution

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {Ω : Opens E} {O : Opens D} {V : Opens (E × D)}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-! ### Transpose, restriction and multiplication -/

/-- **The transposed kernel.** Swapping the variables of a Schwartz kernel, `Kᵗ (y, x) = K (x, y)`,
gives the kernel of the transposed operator: `⟨A_{Kᵗ} φ, ψ⟩ = ⟨A_K ψ, φ⟩`. Here `Kᵗ` is the
transport of `K` along the swap `D × E ≃ E × D`, a distribution on any open set `W ⊆ D × E` that
the swap maps into `V`. -/
theorem kernelOperator_transportCLM_prodComm {W : Opens (D × E)}
    (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (hW : (O : Set D) ×ˢ (Ω : Set E) ⊆ W)
    (hWV : MapsTo (ContinuousLinearEquiv.prodComm ℝ D E) W V) (K : 𝓓'(V, F)) (φ : 𝓓(Ω, ℝ))
    (ψ : 𝓓(O, ℝ)) :
    kernelOperator hW (transportCLM (ContinuousLinearEquiv.prodComm ℝ D E) hWV K) φ ψ =
      kernelOperator hV K ψ φ := by
  rw [kernelOperator_apply, kernelOperator_apply, transportCLM_apply]
  congr 1
  ext p
  simp [prodSMulCLM_apply, mul_comm]

/-- **Restriction of a Schwartz kernel.** Restricting the kernel to an open set `V' ⊆ V` containing
`Ω' × O'`, where `Ω' ⊆ Ω` and `O' ⊆ O`, gives the operator `𝓓(O') → 𝓓'(Ω')` that extends inputs by
zero and restricts outputs to `Ω'`. -/
theorem kernelOperator_restrictCLM {Ω' : Opens E} {O' : Opens D} {V' : Opens (E × D)}
    (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (hV' : (Ω' : Set E) ×ˢ (O' : Set D) ⊆ V')
    (hΩ : Ω' ≤ Ω) (hO : O' ≤ O) (hVV' : V' ≤ V) (K : 𝓓'(V, F)) (ψ : 𝓓(O', ℝ)) :
    kernelOperator hV' (restrictCLM K) ψ = restrictCLM (kernelOperator hV K (monoCLM ℝ ψ)) := by
  ext φ
  rw [kernelOperator_apply, restrictCLM_apply, restrictCLM_apply, kernelOperator_apply]
  congr 1
  ext p
  simp [prodSMulCLM_apply, hΩ, hO, hVV']

/-- Multiplying a Schwartz kernel by a smooth function `f (x)` of the output variable multiplies the
outputs of its operator by `f`. -/
@[simp]
theorem kernelOperator_smulLeftCLM_fst {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F)) (ψ : 𝓓(O, ℝ)) :
    kernelOperator hV (smulLeftCLM (hf.comp contDiff_fst) K) ψ =
      smulLeftCLM hf (kernelOperator hV K ψ) := by
  ext φ
  rw [kernelOperator_apply, smulLeftCLM_apply, smulLeftCLM_apply, kernelOperator_apply]
  congr 1
  ext p
  simp [prodSMulCLM_apply, mul_left_comm]

/-- Multiplying a Schwartz kernel by a smooth function `g (y)` of the input variable multiplies the
inputs of its operator by `g`. -/
@[simp]
theorem kernelOperator_smulLeftCLM_snd {g : D → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F)) (ψ : 𝓓(O, ℝ)) :
    kernelOperator hV (smulLeftCLM (hg.comp contDiff_snd) K) ψ =
      kernelOperator hV K (TestFunction.smulLeftCLM hg ψ) := by
  ext φ
  rw [kernelOperator_apply, smulLeftCLM_apply, kernelOperator_apply]
  congr 1
  ext p
  simp [prodSMulCLM_apply, mul_assoc]

/-! ### Supports -/

section Support

/-- **The support of an output.** The distribution `A_K ψ` is supported in the set of points `x`
such that `(x, y)` lies in the support of the kernel for some `y` in the support of `ψ`. -/
theorem dsupport_kernelOperator_subset (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F))
    (ψ : 𝓓(O, ℝ)) :
    dsupport (kernelOperator hV K ψ) ⊆ Prod.fst '' (dsupport K ∩ univ ×ˢ tsupport ψ) := by
  intro x hx
  by_contra hxK
  -- By the tube lemma, `K` vanishes on a product `u × v` of neighbourhoods of `x` and `supp ψ`.
  have hsub : ({x} : Set E) ×ˢ tsupport ψ ⊆ (dsupport K)ᶜ := by
    rintro ⟨x', y⟩ ⟨rfl, hy⟩ hK
    exact hxK ⟨(x', y), ⟨hK, mem_univ _, hy⟩, rfl⟩
  obtain ⟨u, v, hu, -, hxu, hψv, huv⟩ := generalized_tube_lemma isCompact_singleton
    ψ.hasCompactSupport isClosed_dsupport.isOpen_compl hsub
  refine (notMem_dsupport_iff (f := kernelOperator hV K ψ) x).2
    ⟨u, fun φ hφ ↦ ?_, hu, hxu rfl⟩ hx
  rw [kernelOperator_apply]
  exact map_eq_zero_of_disjoint_dsupport K <| subset_compl_iff_disjoint_right.1 <|
    (tsupport_prodSMulCLM_subset φ).trans <| (prod_mono hφ hψv).trans huv

/-- **Compactly supported outputs.** If the part of the support of the kernel lying over the support
of `ψ` is compact, as it is for a properly supported kernel, then `A_K ψ` has compact support. -/
theorem isCompact_dsupport_kernelOperator (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, F))
    (ψ : 𝓓(O, ℝ)) (hK : IsCompact (dsupport K ∩ univ ×ˢ tsupport ψ)) :
    IsCompact (dsupport (kernelOperator hV K ψ)) :=
  (hK.image continuous_fst).of_isClosed_subset isClosed_dsupport
    (dsupport_kernelOperator_subset hV K ψ)

variable [T2Space F]

/-- **Vanishing of a Schwartz kernel on an open rectangle.** For open sets `s ⊆ E` and `t ⊆ D`,
the kernel `K` on `Ω × O` vanishes on `s × t` exactly when `⟨A_K ψ, φ⟩ = 0` for all test
functions `φ` supported in `s` and `ψ` supported in `t`. -/
theorem isVanishingOn_prod_iff_kernelOperator (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    {s : Set E} {t : Set D} (hs : IsOpen s) (ht : IsOpen t) (K : 𝓓'(V, F)) :
    IsVanishingOn K (s ×ˢ t) ↔
      ∀ ψ : 𝓓(O, ℝ), tsupport ψ ⊆ t → IsVanishingOn (kernelOperator hV.symm.subset K ψ) s := by
  refine ⟨fun h ψ hψ φ hφ ↦ by
    rw [kernelOperator_apply]
    exact h _ ((tsupport_prodSMulCLM_subset φ).trans (prod_mono hφ hψ)), fun h χ hχ ↦ ?_⟩
  -- Restrict `K` to the rectangle `V' = (Ω ∩ s) × (O ∩ t)`, where it vanishes on tensor products.
  let Ω' : Opens E := Ω ⊓ ⟨s, hs⟩
  let O' : Opens D := O ⊓ ⟨t, ht⟩
  let V' : Opens (E × D) := ⟨(Ω' : Set E) ×ˢ (O' : Set D), Ω'.isOpen.prod O'.isOpen⟩
  have hVV' : V' ≤ V := by
    rw [← SetLike.coe_subset_coe, hV]
    exact prod_mono inter_subset_left inter_subset_left
  have hK' : (restrictCLM K : 𝓓'(V', F)) = 0 := ext_prodSMulCLM (Ω := Ω') (O := O') rfl
    fun ψ φ ↦ by
      rw [zero_apply, ← kernelOperator_apply,
        kernelOperator_restrictCLM hV.symm.subset _ inf_le_left inf_le_left hVV',
        restrictCLM_apply]
      have hψ : ⇑(monoCLM ℝ ψ : 𝓓(O, ℝ)) = ψ := by ext; simp [O']
      have hφ : ⇑(monoCLM ℝ φ : 𝓓(Ω, ℝ)) = φ := by ext; simp [Ω']
      exact h _ (hψ ▸ ψ.tsupport_subset.trans inter_subset_right) _
        (hφ ▸ φ.tsupport_subset.trans inter_subset_right)
  -- The test `χ` is supported in `V'`, so it is the extension by zero of a test on `V'`.
  have hχV' : tsupport χ ⊆ V' := fun p hp ↦ by
    have hpV : p ∈ (Ω : Set E) ×ˢ (O : Set D) := hV ▸ χ.tsupport_subset hp
    exact ⟨⟨hpV.1, (hχ hp).1⟩, hpV.2, (hχ hp).2⟩
  obtain ⟨χ', rfl⟩ := exists_monoCLM_eq_of_tsupport_subset hVV' hχV'
  rw [← restrictCLM_apply, hK', zero_apply]

/-- **Output support.** For an open set `s ⊆ E`, the kernel `K` on `Ω × O` vanishes on `s × D`
exactly when every output `A_K ψ` vanishes on `s`. -/
theorem isVanishingOn_prod_univ_iff_kernelOperator
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) {s : Set E} (hs : IsOpen s)
    (K : 𝓓'(V, F)) :
    IsVanishingOn K (s ×ˢ univ) ↔
      ∀ ψ : 𝓓(O, ℝ), IsVanishingOn (kernelOperator hV.symm.subset K ψ) s := by
  simp [isVanishingOn_prod_iff_kernelOperator hV hs isOpen_univ]

/-- **Ignored inputs.** For an open set `t ⊆ D`, the kernel `K` on `Ω × O` vanishes on `E × t`
exactly when `A_K ψ = 0` for every test function `ψ` supported in `t`. -/
theorem isVanishingOn_univ_prod_iff_kernelOperator_eq_zero
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) {t : Set D} (ht : IsOpen t)
    (K : 𝓓'(V, F)) :
    IsVanishingOn K (univ ×ˢ t) ↔
      ∀ ψ : 𝓓(O, ℝ), tsupport ψ ⊆ t → kernelOperator hV.symm.subset K ψ = 0 := by
  rw [isVanishingOn_prod_iff_kernelOperator hV isOpen_univ ht]
  refine forall₂_congr fun ψ _ ↦ ⟨fun h ↦ ?_, fun h φ _ ↦ by rw [h, zero_apply]⟩
  ext φ
  exact h φ (subset_univ _)

/-- **Output support in a closed set.** For a closed set `C ⊆ E`, every output `A_K ψ` of the kernel
`K` on `Ω × O` is supported in `C` exactly when `K` vanishes on `(E \ C) × D`. -/
theorem dsupport_kernelOperator_subset_iff (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    {C : Set E} (hC : IsClosed C) (K : 𝓓'(V, F)) :
    (∀ ψ : 𝓓(O, ℝ), dsupport (kernelOperator hV.symm.subset K ψ) ⊆ C) ↔
      IsVanishingOn K (Cᶜ ×ˢ univ) := by
  rw [isVanishingOn_prod_univ_iff_kernelOperator hV hC.isOpen_compl]
  exact forall_congr' fun ψ ↦ by
    rw [isVanishingOn_iff_disjoint_dsupport _ hC.isOpen_compl, disjoint_compl_left_iff_subset]

end Support

/-! ### Integral kernels -/

section IntegralKernel

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace D] [BorelSpace D] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E} {ν : Measure D} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
/-- The output `x ↦ ∫ ψ y • k (x, y) dν(y)` of an integral kernel `k` locally integrable on `V` is
locally integrable on `Ω`. -/
theorem locallyIntegrableOn_integral_smul (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    {k : E × D → G} (hk : LocallyIntegrableOn k V (μ.prod ν)) (ψ : 𝓓(O, ℝ)) :
    LocallyIntegrableOn (fun x ↦ ∫ y, ψ y • k (x, y) ∂ν) Ω μ := by
  refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun L hLΩ hL ↦ ?_
  -- Multiply by a test function `θ` equal to one on `L`; `θ ⊗ ψ` is a test function on `V`.
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hL hLΩ
  refine (((prodSMulCLM ψ hV θ).integrable_smul hk).integral_prod_left.integrableOn).congr_fun
    (fun x hx ↦ ?_) hL.measurableSet
  simp [prodSMulCLM_apply, hθ.self_of_nhdsSet x hx]

/-- **Integral kernels.** A Schwartz kernel given by a function `k`, locally integrable on `V`, is
the kernel of the integral operator `ψ ↦ (x ↦ ∫ ψ y • k (x, y) dν(y))`. -/
@[simp]
theorem kernelOperator_ofFun (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) {k : E × D → G}
    (hk : LocallyIntegrableOn k V (μ.prod ν)) (ψ : 𝓓(O, ℝ)) :
    kernelOperator hV (ofFun V k (μ.prod ν) ⊤) ψ =
      ofFun Ω (fun x ↦ ∫ y, ψ y • k (x, y) ∂ν) μ ⊤ := by
  ext φ
  rw [kernelOperator_apply, ofFun_apply hk, ofFun_apply (locallyIntegrableOn_integral_smul hV hk ψ),
    integral_prod _ ((prodSMulCLM ψ hV φ).integrable_smul hk)]
  congr 1
  ext x
  simp only [prodSMulCLM_apply, smul_eq_mul, ← integral_smul, mul_smul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ smul_comm _ _ _)

end IntegralKernel

end Distribution
