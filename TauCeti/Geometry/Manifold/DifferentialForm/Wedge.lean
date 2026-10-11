/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge

/-!
# Wedge products of bundle-valued rough differential forms

The paired wedge combines two rough forms with values in topological vector-bundle fibres by
a continuous bilinear pairing on each fibre. Its formula is the signed permutation sum divided
by the two factorials. This construction uses no norm or trivialization on the tangent fibres.
Pullback carries both the forms and their pairing to the source manifold.

The normalization follows Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 14.
The algebraic alternatization follows the paired-wedge construction of Yury Kudryashov's
`DeRhamCohomology` project and Mathlib's `MultilinearMap.alternatization`.
-/

public section

noncomputable section

open TensorProduct
open scoped Manifold

namespace TauCeti

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  {k l : ℕ}

private def pairingLinear (x : M) (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x) :
    V₁ x ⊗[ℝ] V₂ x →ₗ[ℝ] V₃ x :=
  TensorProduct.lift ((ContinuousLinearMap.coeLM ℝ).comp (μ x).toLinearMap)

private def unalternated (x : M)
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    MultilinearMap ℝ (fun _ : Fin (k + l) => TangentSpace I x) (V₃ x) :=
  (pairingLinear x μ).compMultilinearMap <|
    (MultilinearMap.domCoprod (φ x).toAlternatingMap.toMultilinearMap
      (ψ x).toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv

private theorem unalternated_apply (x : M)
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l)
    (v : Fin (k + l) → TangentSpace I x) :
    unalternated x μ φ ψ v =
      μ x (φ x (fun i ↦ v (Fin.castAdd l i)))
        (ψ x (fun j ↦ v (Fin.natAdd k j))) := by
  simp [unalternated, pairingLinear]

private def unalternatedContinuous (x : M)
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ x p.1 p.2))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) => TangentSpace I x) (V₃ x) :=
  { toMultilinearMap := unalternated x μ φ ψ
    cont := by
      have hfun : (unalternated x μ φ ψ).toFun =
        (fun v ↦ μ x (φ x (fun i ↦ v (Fin.castAdd l i)))
          (ψ x (fun j ↦ v (Fin.natAdd k j)))) :=
        funext (unalternated_apply x μ φ ψ)
      rw [hfun]
      fun_prop }

/-- The paired wedge of rough bundle-valued forms, normalized so that one-forms multiply
by the usual two-term alternating product. -/
def bundleWedgeWith (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ x p.1 p.2))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    RoughBundleForm I M V₃ (k + l) :=
  fun x ↦ (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
    (unalternatedContinuous x μ hμ φ ψ).alternatization

/-- The fibrewise paired wedge is the signed permutation sum. -/
theorem bundleWedgeWith_apply (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ x p.1 p.2))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    bundleWedgeWith μ hμ φ ψ x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ x (φ x (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simp only [bundleWedgeWith, ContinuousAlternatingMap.smul_apply,
    ContinuousMultilinearMap.alternatization_apply_apply]
  rfl

/-- On two one-forms, the fibrewise wedge is the usual alternating product. -/
theorem bundleWedgeWith_apply_one_one
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ x p.1 p.2))
    (φ : RoughBundleForm I M V₁ 1) (ψ : RoughBundleForm I M V₂ 1)
    (x : M) (v w : TangentSpace I x) :
    bundleWedgeWith μ hμ φ ψ x ![v, w] =
      μ x (φ x ![v]) (ψ x ![w]) - μ x (φ x ![w]) (ψ x ![v]) := by
  rw [bundleWedgeWith_apply]
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_fin_two_eq_one_or_swap e
  rw [hperm, Finset.sum_insert (by decide), Finset.sum_singleton,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [Fin.fin_one_eq_zero, Matrix.cons_fin_one, sub_eq_add_neg]

/-- Pullback of a paired wedge pulls back its fibrewise pairing as well as both forms. -/
theorem bundleMpullback_wedgeWith (f : M' → M)
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ x p.1 p.2))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleMpullback I' I f (bundleWedgeWith μ hμ φ ψ) =
      bundleWedgeWith (I := I') (fun y ↦ μ (f y)) (fun y ↦ hμ (f y))
        (bundleMpullback I' I f φ) (bundleMpullback I' I f ψ) := by
  ext x v
  simp [bundleWedgeWith_apply, bundleMpullback_apply]

/-- Within-set pullback likewise commutes with the paired wedge without regularity
assumptions. -/
theorem bundleMpullbackWithin_wedgeWith (f : M' → M) (s : Set M')
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ x p.1 p.2))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleMpullbackWithin I' I f s (bundleWedgeWith μ hμ φ ψ) =
      bundleWedgeWith (I := I') (fun y ↦ μ (f y)) (fun y ↦ hμ (f y))
        (bundleMpullbackWithin I' I f s φ) (bundleMpullbackWithin I' I f s ψ) := by
  ext x v
  simp [bundleWedgeWith_apply, bundleMpullbackWithin_apply]

end TauCeti

namespace TauCeti

variable {E H M E' H' M' F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ}

namespace RoughForm

/-- The paired wedge of fixed-coefficient rough forms. It is the trivial-value-bundle
specialization of `bundleWedgeWith`. -/
def wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) : RoughForm I M F₃ (k + l) :=
  bundleWedgeWith (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ ψ

/-- Evaluation of the fixed-coefficient paired wedge. -/
theorem wedgeWith_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    φ.wedgeWith μ ψ x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ (φ x (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ x (fun j ↦ v (σ (Fin.natAdd k j)))) :=
  bundleWedgeWith_apply _ _ φ ψ x v

/-- Pullback preserves the paired wedge of fixed-coefficient rough forms. -/
theorem bundleMpullback_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : M' → M) (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    bundleMpullback I' I f (φ.wedgeWith μ ψ) =
      wedgeWith μ (bundleMpullback I' I f φ : RoughForm I' M' F₁ k)
        (bundleMpullback I' I f ψ : RoughForm I' M' F₂ l) := by
  simpa only [wedgeWith] using
    (TauCeti.bundleMpullback_wedgeWith f (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ ψ)

/-- The real wedge of rough forms uses multiplication as its fibrewise pairing. -/
def wedge (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    RoughForm I M ℝ (k + l) :=
  φ.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) ψ

/-- The wedge of real-valued one-forms has the determinant normalization. -/
@[simp]
theorem wedge_apply_one_one (φ : RoughForm I M ℝ 1) (ψ : RoughForm I M ℝ 1)
    (x : M) (v w : TangentSpace I x) :
    φ.wedge ψ x ![v, w] =
      φ x ![v] * ψ x ![w] - φ x ![w] * ψ x ![v] := by
  simpa only [wedge, wedgeWith, ContinuousLinearMap.mul_apply'] using
    (bundleWedgeWith_apply_one_one (μ := fun _ ↦ ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (ContinuousLinearMap.mul ℝ ℝ).continuous₂) φ ψ x v w)

end RoughForm

end TauCeti
