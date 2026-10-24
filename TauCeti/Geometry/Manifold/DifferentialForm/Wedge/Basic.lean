/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic

/-!
# Wedge products of bundle-valued rough differential forms

The paired wedge combines two rough forms with values in topological vector-bundle fibres by
a continuous bilinear pairing on each fibre. Its formula is the signed permutation sum divided
by the two factorials. This construction uses no norm or trivialization on the tangent fibres.
Pullback carries both the forms and their pairing to the source manifold. The output fibres
need only continuity of multiplication by each fixed scalar. A pairing that turns multiplication
by one scalar into multiplication by another, such as a complex-bilinear pairing or a Hermitian
metric, makes the wedge semilinear in the same way.

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
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousConstSMul ℝ (V₃ x)]
  {k l : ℕ}

/-- The paired wedge of rough bundle-valued forms, normalized so that one-forms multiply
by the usual two-term alternating product. -/
def bundleWedgeWith (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    RoughBundleForm I M V₃ (k + l) :=
  fun x ↦ ContinuousAlternatingMap.pairedWedge (μ x) (hμ x) (φ x) (ψ x)

/-- At each point, the bundle wedge is the paired wedge of the two fibre values. -/
@[simp]
theorem bundleWedgeWith_apply' (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) (x : M) :
    bundleWedgeWith μ hμ φ ψ x =
      ContinuousAlternatingMap.pairedWedge (μ x) (hμ x) (φ x) (ψ x) := (rfl)

/-- The fibrewise paired wedge is the signed permutation sum. -/
theorem bundleWedgeWith_apply (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    bundleWedgeWith μ hμ φ ψ x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ x (φ x (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simpa only [bundleWedgeWith] using
    (ContinuousAlternatingMap.pairedWedge_apply (μ x) (hμ x) (φ x) (ψ x) v)

/-- On two one-forms, the fibrewise wedge is the usual alternating product. -/
theorem bundleWedgeWith_apply_one_one
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ 1) (ψ : RoughBundleForm I M V₂ 1)
    (x : M) (v w : TangentSpace I x) :
    bundleWedgeWith μ hμ φ ψ x ![v, w] =
      μ x (φ x ![v]) (ψ x ![w]) - μ x (φ x ![w]) (ψ x ![v]) := by
  simpa only [bundleWedgeWith] using
    (ContinuousAlternatingMap.pairedWedge_apply_one_one (μ := μ x) (hμ x) (φ x) (ψ x) v w)

/-- Swapping the factors of a fibrewise paired wedge flips the pairing and contributes the graded
sign. This applies to arbitrary value bundles, with no norm on the tangent fibres or values. -/
theorem bundleWedgeWith_flip
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousConstSMul ℝ (V₂ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    bundleWedgeWith μ hμ φ ψ x v =
      (-1 : ℝ) ^ (k * l) •
        bundleWedgeWith
          (fun y ↦ ContinuousLinearMap.pairingFlip (μ y) (hμ y))
          (fun y ↦ ContinuousLinearMap.pairingFlip_continuous (μ y) (hμ y))
          ψ φ x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  simpa only [bundleWedgeWith] using
    ContinuousAlternatingMap.pairedWedge_flip (μ x) (hμ x) (φ x) (ψ x) v

/-- The fibrewise paired wedge is additive in its first form. -/
@[simp]
theorem bundleWedgeWith_add_left [∀ x, ContinuousAdd (V₁ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ φ' : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ (φ + φ') ψ =
      bundleWedgeWith μ hμ φ ψ + bundleWedgeWith μ hμ φ' ψ := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_add_left (μ x) (hμ x) (φ x) (φ' x) (ψ x)

/-- The fibrewise paired wedge is additive in its second form. -/
@[simp]
theorem bundleWedgeWith_add_right [∀ x, ContinuousAdd (V₂ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ ψ' : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ φ (ψ + ψ') =
      bundleWedgeWith μ hμ φ ψ + bundleWedgeWith μ hμ φ ψ' := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_add_right (μ x) (hμ x) (φ x) (ψ x) (ψ' x)

/-- The fibrewise paired wedge respects scalar multiplication in its first form. -/
@[simp]
theorem bundleWedgeWith_smul_left [∀ x, ContinuousConstSMul ℝ (V₁ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (c : ℝ) (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ (c • φ) ψ = c • bundleWedgeWith μ hμ φ ψ := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_smul_left (μ x) (hμ x) c (φ x) (ψ x)

/-- The fibrewise paired wedge respects scalar multiplication in its second form. -/
@[simp]
theorem bundleWedgeWith_smul_right [∀ x, ContinuousConstSMul ℝ (V₂ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (c : ℝ) (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ φ (c • ψ) = c • bundleWedgeWith μ hμ φ ψ := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_smul_right (μ x) (hμ x) c (φ x) (ψ x)

/-- If each fibrewise pairing turns multiplication by `c` in its first argument into
multiplication by `d`, then so does the fibrewise paired wedge in its first form. This covers
complex-bilinear pairings, and pairings that are conjugate-linear in the first argument, such as
Hermitian metrics. -/
theorem bundleWedgeWith_smul_left_of_map_smul {S S' : Type*} [Monoid S]
    [∀ x, DistribMulAction S (V₁ x)] [∀ x, ContinuousConstSMul S (V₁ x)]
    [∀ x, SMulCommClass ℝ S (V₁ x)] [Monoid S'] [∀ x, DistribMulAction S' (V₃ x)]
    [∀ x, ContinuousConstSMul S' (V₃ x)] [∀ x, SMulCommClass ℝ S' (V₃ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b)) {c : S} {d : S'}
    (hcd : ∀ x a b, μ x (c • a) b = d • μ x a b)
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ (c • φ) ψ = d • bundleWedgeWith μ hμ φ ψ := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_smul_left_of_map_smul (μ x) (hμ x) (hcd x)
    (φ x) (ψ x)

/-- If each fibrewise pairing turns multiplication by `c` in its second argument into
multiplication by `d`, then so does the fibrewise paired wedge in its second form. -/
theorem bundleWedgeWith_smul_right_of_map_smul {S S' : Type*} [Monoid S]
    [∀ x, DistribMulAction S (V₂ x)] [∀ x, ContinuousConstSMul S (V₂ x)]
    [∀ x, SMulCommClass ℝ S (V₂ x)] [Monoid S'] [∀ x, DistribMulAction S' (V₃ x)]
    [∀ x, ContinuousConstSMul S' (V₃ x)] [∀ x, SMulCommClass ℝ S' (V₃ x)]
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b)) {c : S} {d : S'}
    (hcd : ∀ x a b, μ x a (c • b) = d • μ x a b)
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ φ (c • ψ) = d • bundleWedgeWith μ hμ φ ψ := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_smul_right_of_map_smul (μ x) (hμ x) (hcd x)
    (φ x) (ψ x)

/-- The fibrewise paired wedge vanishes when its first form is zero. -/
@[simp]
theorem bundleWedgeWith_zero_left (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (ψ : RoughBundleForm I M V₂ l) :
    bundleWedgeWith μ hμ (0 : RoughBundleForm I M V₁ k) ψ = 0 := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_zero_left (μ x) (hμ x) (ψ x)

/-- The fibrewise paired wedge vanishes when its second form is zero. -/
@[simp]
theorem bundleWedgeWith_zero_right (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) :
    bundleWedgeWith μ hμ φ (0 : RoughBundleForm I M V₂ l) = 0 := by
  funext x
  exact ContinuousAlternatingMap.pairedWedge_zero_right (μ x) (hμ x) (φ x)

/-- Pullback of a paired wedge pulls back its fibrewise pairing as well as both forms. -/
theorem bundleMpullback_wedgeWith (f : M' → M)
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleMpullback I' I f (bundleWedgeWith μ hμ φ ψ) =
      bundleWedgeWith (I := I') (fun y ↦ μ (f y)) (fun y ↦ hμ (f y))
        (bundleMpullback I' I f φ) (bundleMpullback I' I f ψ) := by
  ext x v
  simp [bundleWedgeWith_apply, bundleMpullback_apply, -bundleWedgeWith_apply']

/-- Within-set pullback likewise commutes with the paired wedge without regularity
assumptions. -/
theorem bundleMpullbackWithin_wedgeWith (f : M' → M) (s : Set M')
    (μ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x)
    (hμ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ x a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) :
    bundleMpullbackWithin I' I f s (bundleWedgeWith μ hμ φ ψ) =
      bundleWedgeWith (I := I') (fun y ↦ μ (f y)) (fun y ↦ hμ (f y))
        (bundleMpullbackWithin I' I f s φ) (bundleMpullbackWithin I' I f s ψ) := by
  ext x v
  simp [bundleWedgeWith_apply, bundleMpullbackWithin_apply, -bundleWedgeWith_apply']

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

/-- A fixed-coefficient wedge evaluates through the pointwise paired wedge. -/
theorem wedgeWith_apply' (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) (x : M) :
    φ.wedgeWith μ ψ x = ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ (φ x) (ψ x) :=
  by simp only [wedgeWith, bundleWedgeWith]

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

/-- Pairing a rough form with a degree-zero form pairs its value with the function value. -/
@[simp]
theorem wedgeWith_apply_zero_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ 0)
    (x : M) (v : Fin k → TangentSpace I x) :
    φ.wedgeWith μ ψ x v = μ (φ x v) (ψ x 0) := by
  rw [wedgeWith_apply']
  exact ContinuousAlternatingMap.pairedWedge_apply_zero_right μ μ.continuous₂ _ _ v

/-- Evaluation of the paired rough-form wedge on two one-forms. -/
theorem wedgeWith_apply_one_one (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ 1) (ψ : RoughForm I M F₂ 1) (x : M)
    (v w : TangentSpace I x) :
    φ.wedgeWith μ ψ x ![v, w] = μ (φ x ![v]) (ψ x ![w]) - μ (φ x ![w]) (ψ x ![v]) := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_apply_one_one (μ := fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ ψ x v w)

/-- The paired rough-form wedge is additive in its first form. -/
@[simp]
theorem wedgeWith_add_left (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ φ' : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    (φ + φ').wedgeWith μ ψ = φ.wedgeWith μ ψ + φ'.wedgeWith μ ψ := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_add_left (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ φ' ψ)

/-- The paired rough-form wedge is additive in its second form. -/
@[simp]
theorem wedgeWith_add_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ ψ' : RoughForm I M F₂ l) :
    φ.wedgeWith μ (ψ + ψ') = φ.wedgeWith μ ψ + φ.wedgeWith μ ψ' := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_add_right (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ ψ ψ')

/-- The paired rough-form wedge respects scalar multiplication in its first form. -/
@[simp]
theorem wedgeWith_smul_left (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (c : ℝ)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    (c • φ).wedgeWith μ ψ = c • φ.wedgeWith μ ψ := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_smul_left (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) c φ ψ)

/-- The paired rough-form wedge respects scalar multiplication in its second form. -/
@[simp]
theorem wedgeWith_smul_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (c : ℝ)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    φ.wedgeWith μ (c • ψ) = c • φ.wedgeWith μ ψ := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_smul_right (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) c φ ψ)

/-- If the pairing turns multiplication by `c` in its first argument into multiplication by `d`,
then so does the paired rough-form wedge in its first form. For a complex-bilinear pairing of
complex coefficient spaces this is complex-linearity in the first form. -/
theorem wedgeWith_smul_left_of_map_smul {S S' : Type*} [Monoid S] [DistribMulAction S F₁]
    [ContinuousConstSMul S F₁] [SMulCommClass ℝ S F₁] [Monoid S'] [DistribMulAction S' F₃]
    [ContinuousConstSMul S' F₃] [SMulCommClass ℝ S' F₃] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {c : S} {d : S'} (hcd : ∀ a b, μ (c • a) b = d • μ a b)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    (c • φ).wedgeWith μ ψ = d • φ.wedgeWith μ ψ := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_smul_left_of_map_smul (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) (fun _ ↦ hcd) φ ψ)

/-- If the pairing turns multiplication by `c` in its second argument into multiplication by
`d`, then so does the paired rough-form wedge in its second form. For a complex-bilinear pairing
of complex coefficient spaces this is complex-linearity in the second form. -/
theorem wedgeWith_smul_right_of_map_smul {S S' : Type*} [Monoid S] [DistribMulAction S F₂]
    [ContinuousConstSMul S F₂] [SMulCommClass ℝ S F₂] [Monoid S'] [DistribMulAction S' F₃]
    [ContinuousConstSMul S' F₃] [SMulCommClass ℝ S' F₃] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {c : S} {d : S'} (hcd : ∀ a b, μ a (c • b) = d • μ a b)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    φ.wedgeWith μ (c • ψ) = d • φ.wedgeWith μ ψ := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_smul_right_of_map_smul (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) (fun _ ↦ hcd) φ ψ)

/-- The paired rough-form wedge vanishes when its first form is zero. -/
@[simp]
theorem wedgeWith_zero_left (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (ψ : RoughForm I M F₂ l) :
    (0 : RoughForm I M F₁ k).wedgeWith μ ψ = 0 := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_zero_left (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) ψ)

/-- The paired rough-form wedge vanishes when its second form is zero. -/
@[simp]
theorem wedgeWith_zero_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) :
    φ.wedgeWith μ (0 : RoughForm I M F₂ l) = 0 := by
  simpa only [wedgeWith] using
    (bundleWedgeWith_zero_right (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ)

/-- The paired rough-form wedge is supported in the support of its first form. -/
theorem tsupport_wedgeWith_subset_left (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    _root_.tsupport (α := E [⋀^Fin (k + l)]→L[ℝ] F₃) (φ.wedgeWith μ ψ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F₁) φ := by
  refine closure_mono fun x hx hφ ↦ hx ?_
  rw [wedgeWith_apply']
  exact (congrArg (ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ · (ψ x)) hφ).trans
    (ContinuousAlternatingMap.pairedWedge_zero_left μ μ.continuous₂ (ψ x))

/-- The paired rough-form wedge is supported in the support of its second form. -/
theorem tsupport_wedgeWith_subset_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    _root_.tsupport (α := E [⋀^Fin (k + l)]→L[ℝ] F₃) (φ.wedgeWith μ ψ) ⊆
      _root_.tsupport (α := E [⋀^Fin l]→L[ℝ] F₂) ψ := by
  refine closure_mono fun x hx hψ ↦ hx ?_
  rw [wedgeWith_apply']
  exact (congrArg (ContinuousAlternatingMap.pairedWedge μ μ.continuous₂ (φ x)) hψ).trans
    (ContinuousAlternatingMap.pairedWedge_zero_right μ μ.continuous₂ (φ x))

/-- Swapping the factors of a paired rough-form wedge flips the pairing and contributes the
graded sign. The argument reindexing is the canonical cast between the two degree sums. -/
theorem wedgeWith_flip (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) (x : M)
    (v : Fin (k + l) → TangentSpace I x) :
    φ.wedgeWith μ ψ x v =
      (-1 : ℝ) ^ (k * l) •
        ψ.wedgeWith μ.flip φ x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  have hμ : Continuous (Function.uncurry fun a b ↦ μ a b) := μ.continuous₂
  have hpair : ContinuousLinearMap.pairingFlip μ hμ = μ.flip := by
    ext a b
    rw [ContinuousLinearMap.pairingFlip_apply, ContinuousLinearMap.flip_apply]
  simpa only [wedgeWith, bundleWedgeWith, hpair, Function.uncurry_apply_pair] using
    bundleWedgeWith_flip (μ := fun _ ↦ μ) (hμ := fun _ ↦ hμ) φ ψ x v

/-- A symmetric fibrewise pairing gives the graded-commutativity identity for rough forms. -/
theorem wedgeWith_comm (μ : F₁ →L[ℝ] F₁ →L[ℝ] F₃)
    (hμ : ∀ a b, μ a b = μ b a) (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₁ l) (x : M)
    (v : Fin (k + l) → TangentSpace I x) :
    φ.wedgeWith μ ψ x v =
      (-1 : ℝ) ^ (k * l) • ψ.wedgeWith μ φ x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  have hflip : μ.flip = μ := by
    ext a b
    exact hμ b a
  rw [wedgeWith_flip, hflip]

/-- The real wedge of rough forms uses multiplication as its fibrewise pairing. -/
def wedge (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    RoughForm I M ℝ (k + l) :=
  φ.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) ψ

/-- The real-valued wedge specializes the paired wedge to multiplication. -/
theorem wedge_def (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    φ.wedge ψ = φ.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) ψ := (rfl)

/-- Evaluation of the real-valued rough-form wedge in every degree. -/
theorem wedge_apply (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    φ.wedge ψ x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ x (fun i ↦ v (σ (Fin.castAdd l i))) *
            ψ x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simpa [wedge, ContinuousLinearMap.mul_apply'] using
    (wedgeWith_apply (ContinuousLinearMap.mul ℝ ℝ) φ ψ x v)

/-- The wedge of real-valued one-forms has the determinant normalization. -/
@[simp]
theorem wedge_apply_one_one (φ : RoughForm I M ℝ 1) (ψ : RoughForm I M ℝ 1)
    (x : M) (v w : TangentSpace I x) :
    φ.wedge ψ x ![v, w] =
      φ x ![v] * ψ x ![w] - φ x ![w] * ψ x ![v] := by
  simpa only [wedge, wedgeWith, ContinuousLinearMap.mul_apply'] using
    (bundleWedgeWith_apply_one_one (μ := fun _ ↦ ContinuousLinearMap.mul ℝ ℝ)
      (fun _ ↦ (ContinuousLinearMap.mul ℝ ℝ).continuous₂) φ ψ x v w)

/-- The real wedge is additive in its first form. -/
@[simp]
theorem wedge_add_left (φ φ' : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    (φ + φ').wedge ψ = φ.wedge ψ + φ'.wedge ψ := by
  exact wedgeWith_add_left (ContinuousLinearMap.mul ℝ ℝ) φ φ' ψ

/-- The real wedge is additive in its second form. -/
@[simp]
theorem wedge_add_right (φ : RoughForm I M ℝ k) (ψ ψ' : RoughForm I M ℝ l) :
    φ.wedge (ψ + ψ') = φ.wedge ψ + φ.wedge ψ' := by
  exact wedgeWith_add_right (ContinuousLinearMap.mul ℝ ℝ) φ ψ ψ'

/-- The real wedge respects scalar multiplication in its first form. -/
@[simp]
theorem wedge_smul_left (c : ℝ) (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    (c • φ).wedge ψ = c • φ.wedge ψ := by
  exact wedgeWith_smul_left (ContinuousLinearMap.mul ℝ ℝ) c φ ψ

/-- The real wedge respects scalar multiplication in its second form. -/
@[simp]
theorem wedge_smul_right (c : ℝ) (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    φ.wedge (c • ψ) = c • φ.wedge ψ := by
  exact wedgeWith_smul_right (ContinuousLinearMap.mul ℝ ℝ) c φ ψ

/-- The real wedge vanishes when its first form is zero. -/
@[simp]
theorem wedge_zero_left (ψ : RoughForm I M ℝ l) :
    (0 : RoughForm I M ℝ k).wedge ψ = 0 :=
  wedgeWith_zero_left (ContinuousLinearMap.mul ℝ ℝ) ψ

/-- The real wedge vanishes when its second form is zero. -/
@[simp]
theorem wedge_zero_right (φ : RoughForm I M ℝ k) :
    φ.wedge (0 : RoughForm I M ℝ l) = 0 :=
  wedgeWith_zero_right (ContinuousLinearMap.mul ℝ ℝ) φ

/-- Real-valued rough forms commute with the usual graded sign. -/
theorem wedge_comm (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) (x : M)
    (v : Fin (k + l) → TangentSpace I x) :
    φ.wedge ψ x v = (-1 : ℝ) ^ (k * l) • ψ.wedge φ x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  simpa only [wedge] using wedgeWith_comm (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b ↦ mul_comm a b) φ ψ x v

end RoughForm

/-- On a trivial value bundle, the bundle wedge is the fixed-coefficient rough-form wedge. -/
theorem bundleWedgeWith_trivial {F₁ F₂ F₃ : Type*}
    [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    bundleWedgeWith (fun _ ↦ μ) (fun _ ↦ μ.continuous₂) φ ψ =
      RoughForm.wedgeWith μ φ ψ := by
  simp only [RoughForm.wedgeWith]

/-- Within-set pullback preserves the paired wedge of fixed-coefficient rough forms. -/
theorem bundleMpullbackWithin_roughFormWedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : M' → M) (s : Set M') (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    bundleMpullbackWithin I' I f s (RoughForm.wedgeWith μ φ ψ) =
      RoughForm.wedgeWith μ (bundleMpullbackWithin I' I f s φ : RoughForm I' M' F₁ k)
        (bundleMpullbackWithin I' I f s ψ : RoughForm I' M' F₂ l) := by
  simpa only [RoughForm.wedgeWith] using
    (TauCeti.bundleMpullbackWithin_wedgeWith f s (fun _ ↦ μ)
      (fun _ ↦ μ.continuous₂) φ ψ)

/-- Within-set pullback preserves the real-valued rough-form wedge. -/
theorem bundleMpullbackWithin_roughFormWedge (f : M' → M) (s : Set M')
    (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    bundleMpullbackWithin I' I f s (RoughForm.wedge φ ψ) =
      RoughForm.wedge (bundleMpullbackWithin I' I f s φ : RoughForm I' M' ℝ k)
        (bundleMpullbackWithin I' I f s ψ : RoughForm I' M' ℝ l) := by
  simpa [RoughForm.wedge] using
    (bundleMpullbackWithin_roughFormWedgeWith (ContinuousLinearMap.mul ℝ ℝ) f s φ ψ)

/-- Pullback preserves the paired wedge of fixed-coefficient rough forms. -/
theorem mpullback_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : M' → M) (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    mpullback I' I f (RoughForm.wedgeWith μ φ ψ) =
      RoughForm.wedgeWith μ (mpullback I' I f φ : RoughForm I' M' F₁ k)
        (mpullback I' I f ψ : RoughForm I' M' F₂ l) := by
  rw [← mpullbackWithin_univ (I := I') (I' := I) f (RoughForm.wedgeWith μ φ ψ),
    ← mpullbackWithin_univ (I := I') (I' := I) f φ,
    ← mpullbackWithin_univ (I := I') (I' := I) f ψ]
  ext x v
  have hφ : mpullbackWithin I' I f Set.univ φ x = bundleMpullbackWithin I' I f Set.univ φ x := by
    ext w
    simp only [mpullbackWithin_apply, bundleMpullbackWithin_apply]
  have hψ : mpullbackWithin I' I f Set.univ ψ x = bundleMpullbackWithin I' I f Set.univ ψ x := by
    ext w
    simp only [mpullbackWithin_apply, bundleMpullbackWithin_apply]
  rw [RoughForm.wedgeWith_apply', hφ, hψ]
  simpa only [RoughForm.wedgeWith_apply', mpullbackWithin_apply,
    bundleMpullbackWithin_apply] using
    congrArg (fun h ↦ h x v)
      (bundleMpullbackWithin_roughFormWedgeWith (I := I) (I' := I') μ f Set.univ φ ψ)

/-- Pullback preserves the real-valued rough-form wedge. -/
theorem mpullback_wedge (f : M' → M)
    (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) :
    mpullback I' I f (RoughForm.wedge φ ψ) =
      RoughForm.wedge (mpullback I' I f φ : RoughForm I' M' ℝ k)
        (mpullback I' I f ψ : RoughForm I' M' ℝ l) := by
  simpa only [RoughForm.wedge] using
    mpullback_wedgeWith (I := I) (I' := I') (ContinuousLinearMap.mul ℝ ℝ) f φ ψ

end TauCeti
