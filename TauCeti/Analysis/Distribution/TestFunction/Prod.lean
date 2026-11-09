/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Topology.Algebra.Support

/-!
# Tensor products of test functions with a fixed test function

Let `Ω ⊆ E` and `O ⊆ D` be open subsets of real normed spaces and let `ψ` be a real test function
on `O`. For a test function `φ` on `Ω`, the function `(x, t) ↦ ψ t • φ x` is a test function on
`Ω × O`, supported in `tsupport φ ×ˢ tsupport ψ`. For fixed `ψ` this tensor product is continuous
for the LF topologies (`TestFunction.prodSMulCLM`), with values in the test functions on any open
set containing `Ω ×ˢ O`.

Tensoring with a fixed profile in an extra variable turns tests on `Ω` into tests on a product
without enlarging their support in the first factor. Composed with a pullback along a map of the
form `(x, t) ↦ (Φ (x, t), t)`, it cuts off the pullback of a test form along a map `Φ` that is
proper only on bounded slabs `Ω × [c, d]`.

## Main declarations

* `TestFunction.prodSMulCLM`: the continuous linear map `φ ↦ ((x, t) ↦ ψ t • φ x)`.
* `TestFunction.prodSMulCLM_apply`: its values.
* `TestFunction.tsupport_prodSMulCLM_subset`: its support lies in `tsupport φ ×ˢ tsupport ψ`.
-/

public section

noncomputable section

open Set TopologicalSpace TauCeti
open scoped Distributions

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
      have hle (m : ℕ) : (m : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := mod_cast le_top
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
        (norm_iteratedFDeriv_comp_snd_le ψ.contDiff p (hle j)).trans
          ((hM j ⟨p.2, rfl⟩).trans (le_abs_self _))
      have hφj : ‖iteratedFDeriv ℝ (i - j) (φ ∘ Prod.fst) p‖ ≤
          (Finset.range (i + 1)).sup (ContDiffMapSupportedIn.seminorm ℝ E F ⊤ K) φ :=
        (norm_iteratedFDeriv_comp_fst_le φ.contDiff p (hle (i - j))).trans
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

end TestFunction
