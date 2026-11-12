/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.TestFunction.Prod
public import TauCeti.Analysis.Fourier.Torus.Periodization
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Distribution.Gluing
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Complexify
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity
import TauCeti.Analysis.Normed.Operator.ContinuousLinearEquiv

/-!
# The Schwartz kernel theorem

This file proves the Schwartz kernel theorem on open subsets of `ℝ^a × ℝ^b`: a continuous bilinear
map `B` on real test functions on open sets `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` has a unique distributional
kernel, a distribution `T` on `Ω ×ˢ O` with `T (φ ⊗ ψ) = B φ ψ`
(`LinearMap.existsUnique_schwartzKernel_distribution`). Kernels are how linear operators between
spaces of functions on manifolds are described, for instance the pseudodifferential operators,
whose kernels are smooth away from the diagonal. The first part of the file constructs the kernel
on products of small compact sets; the second part glues these local kernels.

## Kernels on small compact sets

Let `K₁' ⊆ ℝ^a` and `K₂' ⊆ ℝ^b` be compact sets that meet none of their translates by nonzero
integer vectors (for instance sets of diameter less than one,
`UnitAddTorus.eq_zero_of_add_mem_of_diam_lt_one`), and let `B` be a bilinear map on
`𝓓_{K₁'}(ℝ^a, ℂ) × 𝓓_{K₂'}(ℝ^b, ℂ)` with values in a complex Banach space, continuous in the
sense that `‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for one of the `C^k` seminorms `N_k`. For compact sets
`K₁`, `K₂` in the interiors of `K₁'`, `K₂'`, this file constructs the kernel of `B` on
`K₁ × K₂`: a continuous linear map `T` on `𝓓_{K₁ × K₂}(ℝ^a × ℝ^b, ℂ)` with
`T (φ ⊗ ψ) = B φ ψ` for `φ` supported in `K₁` and `ψ` supported in `K₂`, where
`(φ ⊗ ψ)(x, y) = φ x * ψ y` is `ContDiffMapSupportedIn.tensor`. Every continuous linear map on
`𝓓_{K₁' × K₂'}` representing `B` on tensor products restricts to `T`
(`LinearMap.exists_schwartzKernel_supportedIn`), so `T` is determined by `B` whenever such a
kernel on `K₁' × K₂'` exists.

The proof transfers the Schwartz kernel theorem on the torus
(`LinearMap.existsUnique_schwartzKernel`) to these compact sets. Fix cutoffs `χᵢ` supported in
`Kᵢ'` and equal to one on `Kᵢ`. The bilinear map `(f, g) ↦ B (χ₁ f) (χ₂ g)` on smooth functions
on the tori `(ℝ / ℤ)^a` and `(ℝ / ℤ)^b` is continuous for the `C^k` norms, so it has a kernel
`K` on the product torus, and `T Φ` is `K` applied to the periodization of `Φ`
(`UnitAddTorus.periodize`). The cutoffs come from
`ContDiffMapSupportedIn.exists_eqOn_one_of_subset_interior`, and the Leibniz bound
`ContDiffMapSupportedIn.seminorm_bilinLeftCLM_mul_le` controls the `C^k` seminorms of the cut-off
functions. Since `Kᵢ'` meets none of its integer translates, the
periodization of `φ` cut off by `χ₁` is `φ` again, and periodization takes tensor products to
tensor products; this gives `T (φ ⊗ ψ) = B φ ψ`. For the comparison, a map `T'` as above
induces `h ↦ T' ((χ₁ ⊗ χ₂) h)` on the product torus, which represents the same bilinear map on
the torus, hence is `K` by uniqueness there.

## Kernels on open sets

Let `B` be a bilinear map on `𝓓(Ω, ℝ) × 𝓓(O, ℝ)` with values in a complex Banach space, bounded
on functions supported in compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` by a product of `C^k` seminorms;
this is the form continuity takes on each pair `𝓓_{K₁} × 𝓓_{K₂}`. Cover `Ω` and `O` by open balls
`ball c r` with `r < 1/4` whose closed balls of radius `2 r` lie in `Ω`, respectively `O`. On a box
`ball c r ×ˢ ball c' r'` the kernel on compact sets, applied to the complex-bilinear extension
`(φ, ψ) ↦ B (Re φ) (Re ψ) - B (Im φ) (Im ψ) + i (B (Re φ) (Im ψ) + B (Im φ) (Re ψ))` of `B`
restricted to the closed balls of radius `2 r` and `2 r'` (`LinearMap.complexifySupportedIn`), gives
a distribution on the box which agrees with `B` on tensor products. Two of these local kernels agree
on the intersection of their boxes, which is again a box, because tensor products of test functions
span a dense subspace (`TestFunction.ext_prodSMulCLM`). They therefore glue to a distribution on
`Ω ×ˢ O` (`Distribution.existsUnique_gluing`). It agrees with `B` on tensor products of test
functions supported in balls of the cover, and hence on all tensor products, because an additive
map on test functions which vanishes locally vanishes
(`AddMonoidHom.eq_zero_of_locally_vanishing`). Uniqueness is again the density of tensor products.

## Main results

* `LinearMap.exists_schwartzKernel_supportedIn`: existence of the kernel on `K₁ × K₂` and its
  agreement with every kernel on `K₁' × K₂'`.
* `LinearMap.existsUnique_schwartzKernel_distribution`: **the Schwartz kernel theorem**, existence
  and uniqueness of the distributional kernel on `Ω ×ˢ O` of a bilinear map on test functions on
  open sets `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 and its proof (the Schwartz kernel theorem, proved by Fourier
  series on a cube) and Theorem 2.2.4 (gluing of distributions).
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

namespace TauCeti.UnitAddTorus

open ContDiffMapSupportedIn _root_.UnitAddTorus

/-! ### Cutting off smooth functions on the torus -/

section Cutoff

variable {d : Type*} [Fintype d] {K : Compacts (d → ℝ)}

/-- The lift of a smooth function on the torus, multiplied by a cutoff `χ` supported in `K`. -/
private def cutoffLift (χ : 𝓓_{K}(d → ℝ, ℂ)) : smoothFunctions d →ₗ[ℂ] 𝓓_{K}(d → ℝ, ℂ) where
  toFun f := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (mem_smoothFunctions.1 f.2) χ
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, FunLike.coe_smul]
    ring

private theorem cutoffLift_apply (χ : 𝓓_{K}(d → ℝ, ℂ)) (f : smoothFunctions d) (x : d → ℝ) :
    cutoffLift χ f x = χ x * (f : UnitAddTorus d → ℂ) (fun i ↦ (x i : UnitAddCircle)) :=
  (rfl)

/-- The `C^k` seminorm of `χ f` is bounded by `2 ^ k N_k(χ) M` for `DerivBound k M f`. -/
private theorem supSeminorm_cutoffLift_le (χ : 𝓓_{K}(d → ℝ, ℂ)) {f : smoothFunctions d}
    {k : ℕ} {M : ℝ} (hf : DerivBound k M (f : UnitAddTorus d → ℂ)) :
    ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k (cutoffLift χ f) ≤
      2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * M := by
  have hM0 := hf.nonneg
  refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦ ?_
  exact seminorm_bilinLeftCLM_mul_le χ (mem_smoothFunctions.1 f.2)
    (fun j hj x ↦ hf.norm_iteratedFDeriv_le hj x) (Finset.mem_Iic.1 hi)

/-- On a set meeting none of its nonzero integer translates, a cutoff equal to one on the
support of `φ` recovers `φ` from its periodization. -/
private theorem cutoffLift_periodize {K' : Compacts (d → ℝ)}
    (hK : ∀ x ∈ K, ∀ ℓ : d → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ K → ℓ = 0) (χ : 𝓓_{K}(d → ℝ, ℂ))
    (hKK' : K' ≤ K) (hχ : EqOn χ 1 K') (φ : 𝓓_{K'}(d → ℝ, ℂ)) :
    cutoffLift χ ⟨periodize φ, periodize_mem_smoothFunctions φ.contDiff φ.hasCompactSupport⟩ =
      monoCLM ℂ φ := by
  ext x
  rw [cutoffLift_apply, monoCLM_apply, ite_eq_left ⟨le_rfl, hKK'⟩, Submodule.coe_mk]
  by_cases hx : x ∈ K
  · rw [periodize_coe_of_mem hK (φ.support_subset.trans hKK') hx]
    by_cases hφ : φ x = 0
    · rw [hφ, mul_zero]
    · rw [hχ (φ.support_subset hφ), Pi.one_apply, one_mul]
  · rw [χ.zero_on_compl hx, φ.zero_on_compl fun h ↦ hx (hKK' h), Pi.zero_apply, zero_mul]

end Cutoff

/-! ### The product of two tori -/

section Prod

variable {a b : Type*}

/-- The identification of `ℝ^(a ⊕ b)` with `ℝ^a × ℝ^b`. -/
private abbrev splitEquiv (a b : Type*) :
    (a ⊕ b → ℝ) ≃L[ℝ] (a → ℝ) × (b → ℝ) :=
  ContinuousLinearEquiv.sumPiEquivProdPi ℝ a b fun _ ↦ ℝ

/-- The integer translates of the preimage of a product of sets meeting none of their nonzero
integer translates. -/
private theorem eq_zero_of_mem_preimage_splitEquiv {S₁ : Set (a → ℝ)} {S₂ : Set (b → ℝ)}
    (hS₁ : ∀ x ∈ S₁, ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ S₁ → ℓ = 0)
    (hS₂ : ∀ y ∈ S₂, ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ S₂ → ℓ = 0) :
    ∀ x ∈ splitEquiv a b ⁻¹' (S₁ ×ˢ S₂), ∀ ℓ : a ⊕ b → ℤ,
      x + (fun i ↦ (ℓ i : ℝ)) ∈ splitEquiv a b ⁻¹' (S₁ ×ˢ S₂) → ℓ = 0 := by
  intro x hx ℓ hxℓ
  have h₁ := hS₁ _ hx.1 (fun i ↦ ℓ (.inl i)) hxℓ.1
  have h₂ := hS₂ _ hx.2 (fun i ↦ ℓ (.inr i)) hxℓ.2
  ext i
  cases i with
  | inl i => exact congrFun h₁ i
  | inr i => exact congrFun h₂ i

variable [Fintype a] [Fintype b]

variable {L : Compacts ((a → ℝ) × (b → ℝ))}

/-- The periodization to the product torus `UnitAddTorus (a ⊕ b)` of a smooth function on
`ℝ^a × ℝ^b` supported in a compact set. -/
private def periodizeProd : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ) →ₗ[ℂ] smoothFunctions (a ⊕ b) where
  toFun Φ := ⟨periodize (Φ ∘ splitEquiv a b),
    periodize_mem_smoothFunctions (Φ.contDiff.comp (splitEquiv a b).contDiff)
      (Φ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph)⟩
  map_add' Φ Ψ := Subtype.ext (periodize_add
    (Φ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph)
    (Ψ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph))
  map_smul' c Φ := Subtype.ext (periodize_smul c (Φ ∘ splitEquiv a b))

private theorem coe_periodizeProd (Φ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    (periodizeProd Φ : UnitAddTorus (a ⊕ b) → ℂ) = periodize (Φ ∘ splitEquiv a b) :=
  (rfl)

private theorem periodizeProd_tensor {K₁ : Compacts (a → ℝ)} {K₂ : Compacts (b → ℝ)}
    (φ : 𝓓_{K₁}(a → ℝ, ℂ)) (ψ : 𝓓_{K₂}(b → ℝ, ℂ)) :
    periodizeProd (φ.tensor ψ) =
      ⟨tensor (periodize φ) (periodize ψ), tensor_mem_smoothFunctions
        (periodize_mem_smoothFunctions φ.contDiff φ.hasCompactSupport)
        (periodize_mem_smoothFunctions ψ.contDiff ψ.hasCompactSupport)⟩ :=
  Subtype.ext ((congrArg periodize (funext fun x ↦ φ.tensor_apply ψ (splitEquiv a b x))).trans
    (periodize_tensor φ.hasCompactSupport ψ.hasCompactSupport))

/-- If `L` lies in a product of sets meeting none of their nonzero integer translates, the
`C^N` norms of the periodization of `Φ` are bounded by the `C^N` seminorm of `Φ`. -/
private theorem derivBound_periodizeProd {S₁ : Set (a → ℝ)} {S₂ : Set (b → ℝ)}
    (hS₁ : ∀ x ∈ S₁, ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ S₁ → ℓ = 0)
    (hS₂ : ∀ y ∈ S₂, ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ S₂ → ℓ = 0)
    (hL : (L : Set ((a → ℝ) × (b → ℝ))) ⊆ S₁ ×ˢ S₂) (Φ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) (N : ℕ) :
    DerivBound N (ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ L N Φ)
      (periodizeProd Φ : UnitAddTorus (a ⊕ b) → ℂ) := by
  refine derivBound_periodize (eq_zero_of_mem_preimage_splitEquiv hS₁ hS₂)
    (Φ.contDiff.comp (splitEquiv a b).contDiff)
    (Φ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph) ?_ fun j hj x ↦ ?_
  · exact (tsupport_comp_subset_preimage _ (splitEquiv a b).continuous).trans
      (preimage_mono (Φ.tsupport_subset.trans hL))
  · have h := ((splitEquiv a b : (a ⊕ b → ℝ) →L[ℝ] (a → ℝ) × (b → ℝ))
      |>.norm_iteratedFDeriv_comp_right_le Φ.contDiff x (i := j) (mod_cast le_top)).trans
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
          (ContinuousLinearEquiv.opNorm_sumPiEquivProdPi_le (𝕜 := ℝ))))
    rw [ContinuousLinearEquiv.coe_coe] at h
    refine h.trans ?_
    exact (norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hj))

/-- The lift of a smooth function on the product torus to `ℝ^a × ℝ^b`, multiplied by a cutoff
`χ` supported in `L`. -/
private def cutoffLiftProd (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    smoothFunctions (a ⊕ b) →ₗ[ℂ] 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ) where
  toFun h := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    ((mem_smoothFunctions.1 h.2).comp (splitEquiv a b).symm.contDiff) χ
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', SetLike.val_smul,
      Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      FunLike.coe_smul]
    ring

private theorem cutoffLiftProd_apply (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ))
    (h : smoothFunctions (a ⊕ b)) (p : (a → ℝ) × (b → ℝ)) :
    cutoffLiftProd χ h p =
      χ p * (h : UnitAddTorus (a ⊕ b) → ℂ) (fun i ↦ ((splitEquiv a b).symm p i : UnitAddCircle)) :=
  (rfl)

private theorem supSeminorm_cutoffLiftProd_le (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ))
    {h : smoothFunctions (a ⊕ b)} {k : ℕ} {M : ℝ}
    (hh : DerivBound k M (h : UnitAddTorus (a ⊕ b) → ℂ)) {i : ℕ} (hi : i ≤ k) :
    N[ℂ]_{L, i} (cutoffLiftProd χ h) ≤
      2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ L k χ * M :=
  seminorm_bilinLeftCLM_mul_le χ ((mem_smoothFunctions.1 h.2).comp (splitEquiv a b).symm.contDiff)
    (fun j hj x ↦ by
      have h' := (((splitEquiv a b).symm : (a → ℝ) × (b → ℝ) →L[ℝ] (a ⊕ b → ℝ))
        |>.norm_iteratedFDeriv_comp_right_le (mem_smoothFunctions.1 h.2) x (i := j)
          (mod_cast le_top)).trans (mul_le_of_le_one_right
          (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
            (ContinuousLinearEquiv.opNorm_sumPiEquivProdPi_symm_le (𝕜 := ℝ))))
      rw [ContinuousLinearEquiv.coe_coe] at h'
      exact h'.trans (hh.norm_iteratedFDeriv_le hj _)) hi

private theorem cutoffLiftProd_tensor {K₁ : Compacts (a → ℝ)} {K₂ : Compacts (b → ℝ)}
    (χ₁ : 𝓓_{K₁}(a → ℝ, ℂ)) (χ₂ : 𝓓_{K₂}(b → ℝ, ℂ)) (f : smoothFunctions a)
    (g : smoothFunctions b) :
    cutoffLiftProd (χ₁.tensor χ₂)
        ⟨tensor (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ),
          tensor_mem_smoothFunctions f.2 g.2⟩ =
      (cutoffLift χ₁ f).tensor (cutoffLift χ₂ g) := by
  ext p
  simp only [cutoffLiftProd_apply, ContDiffMapSupportedIn.tensor_apply, cutoffLift_apply,
    _root_.UnitAddTorus.tensor_apply, ContinuousLinearEquiv.sumPiEquivProdPi_symm_apply]
  ring

/-- If `L` lies in a product of sets meeting none of their nonzero integer translates and a
cutoff supported in that product is one on `L`, the cutoff recovers `Φ` from its periodization. -/
private theorem cutoffLiftProd_periodizeProd {K₁ : Compacts (a → ℝ)} {K₂ : Compacts (b → ℝ)}
    (hK₁ : ∀ x ∈ K₁, ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ K₁ → ℓ = 0)
    (hK₂ : ∀ y ∈ K₂, ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ K₂ → ℓ = 0)
    (χ : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ)) (hLK : L ≤ K₁ ×ˢ K₂) (hχ : EqOn χ 1 L)
    (Φ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    cutoffLiftProd χ (periodizeProd Φ) = monoCLM ℂ Φ := by
  ext p
  rw [cutoffLiftProd_apply, coe_periodizeProd, monoCLM_apply, ite_eq_left ⟨le_rfl, hLK⟩]
  by_cases hp : p ∈ (K₁ ×ˢ K₂ : Compacts ((a → ℝ) × (b → ℝ)))
  · have hx : (splitEquiv a b).symm p ∈ splitEquiv a b ⁻¹' ((K₁ : Set (a → ℝ)) ×ˢ K₂) := by
      rwa [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    rw [periodize_coe_of_mem (f := Φ ∘ splitEquiv a b)
      (eq_zero_of_mem_preimage_splitEquiv hK₁ hK₂) (fun x hx ↦ hLK (Φ.support_subset hx)) hx,
      Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    by_cases hΦ : Φ p = 0
    · rw [hΦ, mul_zero]
    · rw [hχ (Φ.support_subset hΦ), Pi.one_apply, one_mul]
  · rw [χ.zero_on_compl hp, Φ.zero_on_compl fun h ↦ hp (hLK h), Pi.zero_apply, zero_mul]

end Prod

end TauCeti.UnitAddTorus

/-! ### The kernel theorem -/

namespace LinearMap

open ContDiffMapSupportedIn TauCeti.UnitAddTorus _root_.UnitAddTorus

variable {a b : Type*} [Fintype a] [Fintype b]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {K₁ K₁' : Compacts (a → ℝ)} {K₂ K₂' : Compacts (b → ℝ)}

omit [CompleteSpace F] in
/-- A bilinear map bounded by a product of `C^k` seminorms induces, through cutoffs, a bilinear
map on smooth functions on two tori which is continuous for the `C^k` norms. -/
private theorem exists_bound_compl₁₂_cutoffLift
    (B : 𝓓_{K₁'}(a → ℝ, ℂ) →ₗ[ℂ] 𝓓_{K₂'}(b → ℝ, ℂ) →ₗ[ℂ] F)
    (hB : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖B φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k ψ)
    (χ₁ : 𝓓_{K₁'}(a → ℝ, ℂ)) (χ₂ : 𝓓_{K₂'}(b → ℝ, ℂ)) :
    ∃ (C : ℝ) (N : ℕ), ∀ (f : smoothFunctions a) (g : smoothFunctions b) (M₁ M₂ : ℝ),
      DerivBound N M₁ (f : UnitAddTorus a → ℂ) → DerivBound N M₂ (g : UnitAddTorus b → ℂ) →
        ‖B.compl₁₂ (cutoffLift χ₁) (cutoffLift χ₂) f g‖ ≤ C * M₁ * M₂ := by
  obtain ⟨C, k, hCk⟩ := hB
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 * (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k χ₁) *
    (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k χ₂), k,
    fun f g M₁ M₂ hf hg ↦ ?_⟩
  have h₁ := supSeminorm_cutoffLift_le χ₁ hf
  have h₂ := supSeminorm_cutoffLift_le χ₂ hg
  rw [LinearMap.compl₁₂_apply]
  calc _ ≤ max C 0 * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k (cutoffLift χ₁ f) *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k (cutoffLift χ₂ g) :=
        (hCk _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (apply_nonneg _ _)) (apply_nonneg _ _))
    _ ≤ max C 0 * (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k χ₁ * M₁) *
        (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k χ₂ * M₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC0) h₂ (apply_nonneg _ _)
          (mul_nonneg hC0 (mul_nonneg (mul_nonneg (by positivity) (apply_nonneg _ _))
            hf.nonneg))
    _ = _ := by ring

omit [CompleteSpace F] in
/-- A continuous linear map on `𝓓_L(ℝ^a × ℝ^b, ℂ)`, composed with a cutoff lift from the product
torus, is continuous for one of the `C^N` norms on the torus. -/
private theorem exists_bound_comp_cutoffLiftProd {L : Compacts ((a → ℝ) × (b → ℝ))}
    (T' : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F) (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    ∃ (C : ℝ) (N : ℕ), ∀ (h : smoothFunctions (a ⊕ b)) M,
      DerivBound N M (h : UnitAddTorus (a ⊕ b) → ℂ) →
        ‖(T'.toLinearMap ∘ₗ cutoffLiftProd χ) h‖ ≤ C * M := by
  obtain ⟨s, C, -, hs⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ ⊤ L)
    ((normSeminorm ℂ F).comp T'.toLinearMap) (continuous_norm.comp T'.continuous)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ s, i ≤ N :=
    ⟨s.sup fun i ↦ i, fun i hi ↦ Finset.le_sup (f := fun i ↦ i) hi⟩
  refine ⟨C * (2 ^ N * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ L N χ), N,
    fun h M hM ↦ ?_⟩
  have hM0 := hM.nonneg
  refine (hs (cutoffLiftProd χ h)).trans ?_
  rw [smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc]
  gcongr
  exact Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦
    supSeminorm_cutoffLiftProd_le _ hM (hN i hi)

/-- **The Schwartz kernel theorem for test functions supported in compact sets.** Let `K₁'` and
`K₂'` be compact sets meeting none of their translates by nonzero integer vectors, and let `B` be
a bilinear map on `𝓓_{K₁'}(ℝ^a, ℂ) × 𝓓_{K₂'}(ℝ^b, ℂ)` bounded by a product of `C^k` seminorms.
For compact sets `K₁`, `K₂` in the interiors of `K₁'`, `K₂'` there is a continuous linear map `T`
on `𝓓_{K₁ × K₂}(ℝ^a × ℝ^b, ℂ)` with `T (φ ⊗ ψ) = B φ ψ`, and every continuous linear map `T'` on
`𝓓_{K₁' × K₂'}(ℝ^a × ℝ^b, ℂ)` with `T' (φ ⊗ ψ) = B φ ψ` restricts to `T`. -/
theorem exists_schwartzKernel_supportedIn
    (B : 𝓓_{K₁'}(a → ℝ, ℂ) →ₗ[ℂ] 𝓓_{K₂'}(b → ℝ, ℂ) →ₗ[ℂ] F)
    (hB : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖B φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k ψ)
    (hK₁' : ∀ x ∈ K₁', ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ K₁' → ℓ = 0)
    (hK₂' : ∀ y ∈ K₂', ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ K₂' → ℓ = 0)
    (hK₁ : (K₁ : Set (a → ℝ)) ⊆ interior K₁') (hK₂ : (K₂ : Set (b → ℝ)) ⊆ interior K₂') :
    ∃ T : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F,
      (∀ φ ψ, T (φ.tensor ψ) = B (monoCLM ℂ φ) (monoCLM ℂ ψ)) ∧
      ∀ T' : 𝓓_{K₁' ×ˢ K₂'}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F,
        (∀ φ ψ, T' (φ.tensor ψ) = B φ ψ) → ∀ Φ, T' (monoCLM ℂ Φ) = T Φ := by
  obtain ⟨χ₁, hχ₁⟩ := exists_eqOn_one_of_subset_interior hK₁
  obtain ⟨χ₂, hχ₂⟩ := exists_eqOn_one_of_subset_interior hK₂
  have hKK₁ : K₁ ≤ K₁' := hK₁.trans interior_subset
  have hKK₂ : K₂ ≤ K₂' := hK₂.trans interior_subset
  have hKK : K₁ ×ˢ K₂ ≤ K₁' ×ˢ K₂' := prod_mono hKK₁ hKK₂
  -- The bilinear map on the tori and its continuity for the `C^k` norms.
  set B' := B.compl₁₂ (cutoffLift χ₁) (cutoffLift χ₂)
  have hB' := exists_bound_compl₁₂_cutoffLift B hB χ₁ χ₂
  obtain ⟨C', N', hC'N'⟩ := exists_norm_schwartzKernel_le B' hB'
  -- The kernel on `K₁ × K₂`: the torus kernel applied to the periodization.
  have hbound (Φ : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ)) :
      ‖schwartzKernel B' hB' (periodizeProd Φ)‖ ≤
        max C' 0 * (Finset.Iic N').sup (fun i ↦ N[ℂ]_{K₁ ×ˢ K₂, i}) Φ := by
    have hΦ := derivBound_periodizeProd hK₁' hK₂' hKK Φ N'
    have hΦ0 := hΦ.nonneg
    refine (hC'N' _ _ hΦ).trans ?_
    gcongr
    · exact le_max_left _ _
    · exact le_rfl
  let T : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F :=
    ContDiffMapSupportedIn.mkCLMtoNormedSpace ℂ (fun Φ ↦ schwartzKernel B' hB' (periodizeProd Φ))
      (fun Φ Ψ ↦ by simp only [map_add]) (fun c Φ ↦ by simp only [map_smul])
      ⟨Finset.Iic N', max C' 0, le_max_right _ _, hbound⟩
  -- `mkCLMtoNormedSpace` has no evaluation lemma; it evaluates by definition.
  have hT (Φ : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ)) :
      T Φ = schwartzKernel B' hB' (periodizeProd Φ) :=
    rfl
  refine ⟨T, fun φ ψ ↦ ?_, fun T' hT' Φ ↦ ?_⟩
  · rw [hT, periodizeProd_tensor]
    refine (schwartzKernel_tensor B' hB'
      ⟨periodize φ, periodize_mem_smoothFunctions φ.contDiff φ.hasCompactSupport⟩
      ⟨periodize ψ, periodize_mem_smoothFunctions ψ.contDiff ψ.hasCompactSupport⟩).trans ?_
    rw [LinearMap.compl₁₂_apply, cutoffLift_periodize hK₁' χ₁ hKK₁ hχ₁ φ,
      cutoffLift_periodize hK₂' χ₂ hKK₂ hχ₂ ψ]
  · -- `T'` induces a kernel of `B'` on the product torus, which is the torus kernel of `B'` by
    -- uniqueness there.
    have hUK : T'.toLinearMap ∘ₗ cutoffLiftProd (χ₁.tensor χ₂) = schwartzKernel B' hB' :=
      eq_schwartzKernel B' hB' (exists_bound_comp_cutoffLiftProd T' _) fun f g ↦ by
        rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, cutoffLiftProd_tensor, hT',
          LinearMap.compl₁₂_apply]
    have hχ : EqOn (χ₁.tensor χ₂) 1 (K₁ ×ˢ K₂ : Compacts ((a → ℝ) × (b → ℝ))) := fun p hp ↦ by
      rw [ContDiffMapSupportedIn.tensor_apply, hχ₁ hp.1, hχ₂ hp.2, Pi.one_apply, Pi.one_apply,
        Pi.one_apply, mul_one]
    rw [hT, ← hUK, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      cutoffLiftProd_periodizeProd hK₁' hK₂' (χ₁.tensor χ₂) hKK hχ Φ]

end LinearMap

/-! ### The kernel theorem on open sets -/

namespace LinearMap

open Complex ContDiffMapSupportedIn TestFunction Metric

section SmallBall

variable {d : Type*} [Fintype d] {Ω : Opens (d → ℝ)}

/-- Centres `c` and radii `r` of the balls covering an open set `Ω` on which the kernel theorem for
compact sets applies: `r < 1/4` and the closed ball of radius `2 r` lies in `Ω`, so that this
closed ball meets none of its nonzero integer translates. -/
private def SmallBall (Ω : Opens (d → ℝ)) : Type _ :=
  {p : (d → ℝ) × ℝ // 0 < p.2 ∧ p.2 < 1 / 4 ∧ closedBall p.1 (2 * p.2) ⊆ Ω}

namespace SmallBall

/-- The closed ball of radius `r`. -/
private def inner (i : SmallBall Ω) : Compacts (d → ℝ) :=
  ⟨closedBall i.1.1 i.1.2, isCompact_closedBall _ _⟩

/-- The closed ball of radius `2 r`. -/
private def outer (i : SmallBall Ω) : Compacts (d → ℝ) :=
  ⟨closedBall i.1.1 (2 * i.1.2), isCompact_closedBall _ _⟩

/-- The open ball of radius `r`. -/
private def ball (i : SmallBall Ω) : Opens (d → ℝ) := ⟨Metric.ball i.1.1 i.1.2, isOpen_ball⟩

private theorem ball_subset_inner (i : SmallBall Ω) : (i.ball : Set (d → ℝ)) ⊆ i.inner :=
  ball_subset_closedBall

private theorem inner_subset_interior_outer (i : SmallBall Ω) :
    (i.inner : Set (d → ℝ)) ⊆ interior i.outer :=
  (closedBall_subset_ball (by linarith [i.2.1])).trans ball_subset_interior_closedBall

private theorem inner_subset_outer (i : SmallBall Ω) : (i.inner : Set (d → ℝ)) ⊆ i.outer :=
  i.inner_subset_interior_outer.trans interior_subset

private theorem outer_subset (i : SmallBall Ω) : (i.outer : Set (d → ℝ)) ⊆ Ω := i.2.2.2

private theorem ball_le (i : SmallBall Ω) : i.ball ≤ Ω :=
  i.ball_subset_inner.trans (i.inner_subset_outer.trans i.outer_subset)

private theorem eq_zero_of_add_mem_outer (i : SmallBall Ω) {x : d → ℝ} (hx : x ∈ i.outer)
    {ℓ : d → ℤ} (hxℓ : x + (fun k ↦ (ℓ k : ℝ)) ∈ i.outer) : ℓ = 0 :=
  UnitAddTorus.eq_zero_of_add_mem_of_diam_lt_one isBounded_closedBall
    ((diam_closedBall (by linarith [i.2.1])).trans_lt (by linarith [i.2.2.1])) hx hxℓ

private theorem exists_mem_ball {x : d → ℝ} (hx : x ∈ Ω) : ∃ i : SmallBall Ω, x ∈ i.ball := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hr : 0 < min (ε / 4) (1 / 8) := by positivity
  refine ⟨⟨(x, min (ε / 4) (1 / 8)), hr, by linarith [min_le_right (ε / 4) (1 / 8)],
    (closedBall_subset_ball ?_).trans hεΩ⟩, mem_ball_self hr⟩
  linarith [min_le_left (ε / 4) (1 / 8)]

end SmallBall

end SmallBall

section Kernel

variable {a b : Type*} [Fintype a] [Fintype b]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {Ω : Opens (a → ℝ)} {O : Opens (b → ℝ)} (B : 𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(O, ℝ) →ₗ[ℝ] F)

/-- `B` on real functions supported in the outer closed balls of `i` and `j`. -/
private def restrictOuter (i : SmallBall Ω) (j : SmallBall O) :
    𝓓_{i.outer}(a → ℝ, ℝ) →ₗ[ℝ] 𝓓_{j.outer}(b → ℝ, ℝ) →ₗ[ℝ] F :=
  B.compl₁₂ (ofSupportedInCLM ℝ i.outer_subset).toLinearMap
    (ofSupportedInCLM ℝ j.outer_subset).toLinearMap

/-- The open box `ball i ×ˢ ball j`. -/
private def box (i : SmallBall Ω) (j : SmallBall O) : Opens ((a → ℝ) × (b → ℝ)) :=
  ⟨i.ball ×ˢ j.ball, i.ball.isOpen.prod j.ball.isOpen⟩

private theorem coe_box (i : SmallBall Ω) (j : SmallBall O) :
    (box i j : Set ((a → ℝ) × (b → ℝ))) = (i.ball : Set (a → ℝ)) ×ˢ (j.ball : Set (b → ℝ)) :=
  (rfl)

private theorem box_subset (i : SmallBall Ω) (j : SmallBall O) :
    (box i j : Set ((a → ℝ) × (b → ℝ))) ⊆ (i.inner ×ˢ j.inner : Compacts _) :=
  prod_mono i.ball_subset_inner j.ball_subset_inner

variable {B}

/-- The kernel of `B` on a box: a distribution on `ball i ×ˢ ball j` which takes the value
`B φ ψ` on every test function `(x, y) ↦ ψ y • φ x` with `φ` supported in `ball i` and `ψ` in
`ball j`. It is the restriction to real test functions of the kernel on compact sets
`exists_schwartzKernel_supportedIn` of the complex-bilinear extension of `B`. -/
private theorem exists_kernel_box
    (hB : ∀ (K₁ : Compacts (a → ℝ)) (K₂ : Compacts (b → ℝ)) (hK₁ : (K₁ : Set (a → ℝ)) ⊆ Ω)
      (hK₂ : (K₂ : Set (b → ℝ)) ⊆ O), ∃ (C : ℝ) (k : ℕ),
        ∀ (φ : 𝓓_{K₁}(a → ℝ, ℝ)) (ψ : 𝓓_{K₂}(b → ℝ, ℝ)),
          ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
            C * ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₁ k φ *
              ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₂ k ψ)
    (i : SmallBall Ω) (j : SmallBall O) :
    ∃ S : 𝓓(box i j, ℝ) →L[ℝ] F, ∀ {Ω' : Opens (a → ℝ)} {O' : Opens (b → ℝ)},
      Ω' ≤ i.ball → O' ≤ j.ball → ∀ (φ : 𝓓(Ω', ℝ)) (ψ : 𝓓(O', ℝ)) (f : 𝓓(box i j, ℝ)),
        (⇑f = fun p ↦ ψ p.2 • φ p.1) → S f = B (monoCLM ℝ φ) (monoCLM ℝ ψ) := by
  obtain ⟨C, k, hCk⟩ := hB i.outer j.outer i.outer_subset j.outer_subset
  have hbound : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖complexifySupportedIn (restrictOuter B i j) φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ i.outer k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ j.outer k ψ :=
    ⟨4 * max C 0, k, norm_complexifySupportedIn_le (le_max_right _ _) fun φ ψ ↦ (hCk φ ψ).trans
      (by gcongr; exact le_max_left _ _)⟩
  obtain ⟨T, hT, -⟩ := exists_schwartzKernel_supportedIn _ hbound
    (fun _ hx _ ↦ i.eq_zero_of_add_mem_outer hx) (fun _ hy _ ↦ j.eq_zero_of_add_mem_outer hy)
    i.inner_subset_interior_outer j.inner_subset_interior_outer
  refine ⟨T.restrictScalars ℝ ∘L ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM ∘L
    toSupportedInCLM (box_subset i j), fun {Ω' O'} hΩ' hO' φ ψ f hf ↦ ?_⟩
  have hφ : (Ω' : Set (a → ℝ)) ⊆ i.inner :=
    (SetLike.coe_subset_coe.2 hΩ').trans i.ball_subset_inner
  have hψ : (O' : Set (b → ℝ)) ⊆ j.inner :=
    (SetLike.coe_subset_coe.2 hO').trans j.ball_subset_inner
  -- Read on the compact boxes, `f` is the tensor product of `φ` and `ψ`.
  have htensor : ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM
      (toSupportedInCLM (box_subset i j) f) =
      (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM hφ φ)).tensor
        (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM hψ ψ)) := by
    ext p
    simp [hf, mul_comm]
  have hmono₁ : (ContDiffMapSupportedIn.monoCLM ℂ
      (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM hφ φ)) :
        𝓓_{i.outer}(a → ℝ, ℂ)) =
      postcompLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM (hφ.trans i.inner_subset_outer) φ) := by
    ext x
    simp [SetLike.coe_subset_coe.1 i.inner_subset_outer]
  have hmono₂ : (ContDiffMapSupportedIn.monoCLM ℂ
      (ContDiffMapSupportedIn.postcompCLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM hψ ψ)) :
        𝓓_{j.outer}(b → ℝ, ℂ)) =
      postcompLM (𝕜 := ℝ) ofRealCLM (toSupportedInCLM (hψ.trans j.inner_subset_outer) ψ) := by
    ext x
    simp [SetLike.coe_subset_coe.1 j.inner_subset_outer]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', htensor, hT, hmono₁, hmono₂,
    complexifySupportedIn_postcompLM_ofRealCLM, restrictOuter, compl₁₂_apply,
    ContinuousLinearMap.coe_coe, coe_ofSupportedInCLM, ofSupportedIn_toSupportedInCLM]

/-- The boxes `ball i ×ˢ ball j` cover `Ω ×ˢ O`. -/
private theorem iSup_box {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ⨆ ij : SmallBall Ω × SmallBall O, box ij.1 ij.2 = V := by
  refine le_antisymm (iSup_le fun ij z hz ↦ ?_) fun z hz ↦ ?_
  · rw [← SetLike.mem_coe, hV]
    exact ⟨ij.1.ball_le hz.1, ij.2.ball_le hz.2⟩
  · rw [← SetLike.mem_coe, hV] at hz
    obtain ⟨i, hi⟩ := SmallBall.exists_mem_ball hz.1
    obtain ⟨j, hj⟩ := SmallBall.exists_mem_ball hz.2
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩

omit [CompleteSpace F] in
/-- A continuous linear map on test functions on `Ω ×ˢ O` which agrees with `B` on the tensor
products of test functions supported in balls of the covers agrees with `B` on all tensor
products: localize first in `φ` and then in `ψ`. -/
private theorem prodSMulCLM_eq_of_forall_tsupport_subset_ball {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ)))
    {S : 𝓓(V, ℝ) →L[ℝ] F}
    (hS : ∀ (i : SmallBall Ω) (j : SmallBall O) (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)),
      tsupport φ ⊆ i.ball → tsupport ψ ⊆ j.ball → S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ)
    (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ)) : S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
  have hloc (ψ : 𝓓(O, ℝ)) (hψ : ∃ j : SmallBall O, tsupport ψ ⊆ j.ball) (φ : 𝓓(Ω, ℝ)) :
      S (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
    obtain ⟨j, hj⟩ := hψ
    let Φ : 𝓓(Ω, ℝ) →+ F :=
      { toFun φ := S (prodSMulCLM ψ hV.symm.subset φ) - B φ ψ
        map_zero' := by simp
        map_add' φ₁ φ₂ := by simp only [map_add, LinearMap.add_apply]; abel }
    have hΦ : Φ = 0 := AddMonoidHom.eq_zero_of_locally_vanishing Φ fun x hx ↦ by
      obtain ⟨i, hi⟩ := SmallBall.exists_mem_ball hx
      exact ⟨i.ball, i.ball.isOpen, hi, fun φ hφ ↦ sub_eq_zero.2 (hS i j φ ψ hφ hj)⟩
    exact sub_eq_zero.1 (DFunLike.congr_fun hΦ φ)
  have hadd (ψ₁ ψ₂ : 𝓓(O, ℝ)) : prodSMulCLM (ψ₁ + ψ₂) hV.symm.subset φ =
      prodSMulCLM ψ₁ hV.symm.subset φ + prodSMulCLM ψ₂ hV.symm.subset φ := by
    ext z
    simp [add_mul]
  let Ψ : 𝓓(O, ℝ) →+ F :=
    { toFun ψ := S (prodSMulCLM ψ hV.symm.subset φ) - B φ ψ
      map_zero' := by
        rw [map_zero, sub_zero, ← map_zero S]
        congr 1
        ext z
        simp
      map_add' ψ₁ ψ₂ := by
        simp only [hadd, map_add]
        abel }
  have hΨ : Ψ = 0 := AddMonoidHom.eq_zero_of_locally_vanishing Ψ fun y hy ↦ by
    obtain ⟨j, hj⟩ := SmallBall.exists_mem_ball hy
    exact ⟨j.ball, j.ball.isOpen, hj, fun ψ hψ ↦ sub_eq_zero.2 (hloc ψ ⟨j, hψ⟩ φ)⟩
  exact sub_eq_zero.1 (DFunLike.congr_fun hΨ ψ)

/-- **The Schwartz kernel theorem.** Let `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` be open sets and let `B` be a
bilinear map on the real test functions on `Ω` and on `O`, with values in a complex Banach space
`F`, which is continuous in the sense that on functions supported in compact sets `K₁ ⊆ Ω` and
`K₂ ⊆ O` it is bounded by a product of `C^k` seminorms. Then there is a unique distribution `T`
on `V = Ω ×ˢ O`, the kernel of `B`, with `T (φ ⊗ ψ) = B φ ψ` on the tensor products
`(φ ⊗ ψ)(x, y) = ψ y • φ x` (`TestFunction.prodSMulCLM`). -/
theorem existsUnique_schwartzKernel_distribution
    (hB : ∀ (K₁ : Compacts (a → ℝ)) (K₂ : Compacts (b → ℝ)) (hK₁ : (K₁ : Set (a → ℝ)) ⊆ Ω)
      (hK₂ : (K₂ : Set (b → ℝ)) ⊆ O), ∃ (C : ℝ) (k : ℕ),
        ∀ (φ : 𝓓_{K₁}(a → ℝ, ℝ)) (ψ : 𝓓_{K₂}(b → ℝ, ℝ)),
          ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
            C * ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₁ k φ *
              ContDiffMapSupportedIn.supSeminorm ℝ _ ℝ ⊤ K₂ k ψ)
    {V : Opens ((a → ℝ) × (b → ℝ))}
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ∃! T : 𝓓'(V, F), ∀ φ ψ, T (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
  classical
  choose S hS using exists_kernel_box hB
  have hcover := iSup_box (Ω := Ω) (O := O) hV
  have hboxV (i : SmallBall Ω) (j : SmallBall O) : box i j ≤ V := by
    rw [← hcover]
    exact le_iSup (fun ij : SmallBall Ω × SmallBall O ↦ box ij.1 ij.2) (i, j)
  -- The kernels on two boxes agree on their intersection, a box on which they agree on tensor
  -- products, which span a dense subspace.
  have hcompat (ij kl : SmallBall Ω × SmallBall O)
      (f : 𝓓(box ij.1 ij.2 ⊓ box kl.1 kl.2, ℝ)) :
      S ij.1 ij.2 (monoCLM ℝ f) = S kl.1 kl.2 (monoCLM ℝ f) := by
    have hW : ((box ij.1 ij.2 ⊓ box kl.1 kl.2 : Opens _) : Set ((a → ℝ) × (b → ℝ))) =
        ((ij.1.ball ⊓ kl.1.ball : Opens _) : Set (a → ℝ)) ×ˢ
          ((ij.2.ball ⊓ kl.2.ball : Opens _) : Set (b → ℝ)) := by
      rw [Opens.coe_inf, coe_box, coe_box, Opens.coe_inf, Opens.coe_inf, prod_inter_prod]
    have := ext_prodSMulCLM (T₁ := S ij.1 ij.2 ∘L monoCLM ℝ) (T₂ := S kl.1 kl.2 ∘L monoCLM ℝ) hW
      fun ψ φ ↦ by
        simp only [ContinuousLinearMap.comp_apply]
        rw [hS _ _ inf_le_left inf_le_left φ ψ _ (by ext p; simp),
          hS _ _ inf_le_right inf_le_right φ ψ _ (by ext p; simp)]
    exact congr($this f)
  obtain ⟨S', hS', -⟩ := Distribution.existsUnique_gluing (V := F) (n := ⊤) (F := ℝ)
    (U := fun ij : SmallBall Ω × SmallBall O ↦ box ij.1 ij.2) (T := fun ij ↦ S ij.1 ij.2)
    hcover hcompat
  -- The glued distribution is a kernel of `B` on tensor products supported in a box.
  have hbox (i : SmallBall Ω) (j : SmallBall O) (φ : 𝓓(Ω, ℝ)) (ψ : 𝓓(O, ℝ))
      (hφ : tsupport φ ⊆ i.ball) (hψ : tsupport ψ ⊆ j.ball) :
      S' (prodSMulCLM ψ hV.symm.subset φ) = B φ ψ := by
    let φ' : 𝓓(i.ball, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    let ψ' : 𝓓(j.ball, ℝ) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
    have hsub : (i.ball : Set (a → ℝ)) ×ˢ (j.ball : Set (b → ℝ)) ⊆ box i j := subset_rfl
    have hφ' : monoCLM ℝ φ' = φ := TestFunction.ext fun x ↦ by simp [φ', i.ball_le]
    have hψ' : monoCLM ℝ ψ' = ψ := TestFunction.ext fun x ↦ by simp [ψ', j.ball_le]
    have hmono : monoCLM ℝ (prodSMulCLM ψ' hsub φ') = prodSMulCLM ψ hV.symm.subset φ :=
      TestFunction.ext fun z ↦ by
        simp only [TestFunction.monoCLM_apply, hboxV i j, le_rfl, and_self, ite_true,
          prodSMulCLM_apply, φ', ψ', TestFunction.coe_mk]
    rw [← hmono, ← ContinuousLinearMap.comp_apply, hS' (i, j),
      hS i j le_rfl le_rfl φ' ψ' _ (by ext p; simp), hφ', hψ']
  have htensor := prodSMulCLM_eq_of_forall_tsupport_subset_ball hV hbox
  refine ⟨ContinuousLinearMap.toUniformConvergenceCLM _ F _ S', fun φ ψ ↦ ?_, fun T hT ↦ ?_⟩
  · simpa using htensor φ ψ
  · refine ext_prodSMulCLM hV fun ψ φ ↦ ?_
    simpa [hT] using (htensor φ ψ).symm

end Kernel

end LinearMap
