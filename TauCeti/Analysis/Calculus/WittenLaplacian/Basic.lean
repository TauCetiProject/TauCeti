/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Coordinates
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Witten Laplacian on Euclidean space and its frame formula

A differential form on `ℝ^ι` (for a finite linearly ordered type `ι`) is written in the
coordinates of the exterior basis `dx^s = dx^{i₁} ∧ ⋯ ∧ dx^{iₖ}`, `s = {i₁ < ⋯ < iₖ}`, as a
function `φ : (ι → ℝ) → Finset ι → ℝ`. On these forms exterior multiplication by `dx^i` and
contraction with the coordinate vector field `∂ᵢ` are the coordinate operators
`εᵢ = (Pi.basisFun ℝ ι).exteriorCreation i` and `ιᵢ = (Pi.basisFun ℝ ι).exteriorContraction i`.
The exterior derivative is `d = ∑ᵢ εᵢ ∂ᵢ`, and for the Euclidean metric its formal adjoint is
`d^* = -∑ᵢ ιᵢ ∂ᵢ`: `ιᵢ` is the transpose of `εᵢ`
(`Module.Basis.sum_exteriorCreation_apply_mul`) and `-∂ᵢ` is the formal adjoint of `∂ᵢ`.

For a function `f` and a real parameter `t`, Witten's deformation `d_t = e^{-tf} d e^{tf}` of the
exterior derivative is `d_t = d + t df ∧ = ∑ᵢ εᵢ (∂ᵢ + t ∂ᵢf)`
(`TauCeti.euclideanWittenDiff`), and its formal adjoint is
`d_t^* = d^* + t ι_{∇f} = ∑ᵢ ιᵢ (-∂ᵢ + t ∂ᵢf)` (`TauCeti.euclideanWittenCodiff`), since
multiplication by `t ∂ᵢf` is symmetric: the pointwise pairings `⟨d_t φ, ψ⟩` and `⟨φ, d_t^* ψ⟩`
differ by a divergence
(`TauCeti.sum_euclideanWittenDiff_mul_sub_sum_mul_euclideanWittenCodiff`). The
**Witten Laplacian** is `Δ_t = d_t d_t^* + d_t^* d_t` (`TauCeti.euclideanWittenLaplacian`).

The main result is Witten's formula for `Δ_t` in the orthonormal frame `∂ᵢ`
(`TauCeti.euclideanWittenLaplacian_apply`): for a function `f` and a form `φ` that are `C²` at
the point,

`Δ_t φ = Δ φ + t² |df|² φ + t ∑_{i,j} Hess f(∂ᵢ, ∂ⱼ) ⁅εᵢ, ιⱼ⁆ φ`,

where `Δ = -∑ᵢ ∂ᵢ²` is the Hodge Laplacian, acting coefficientwise, and `⁅εᵢ, ιⱼ⁆ = εᵢ ιⱼ - ιⱼ εᵢ`.
The zeroth-order term `t² |df|²` is a potential that, at each point where `df ≠ 0`, grows like
`t²` as `t → ∞`, while at each point the Hessian term is an endomorphism of the finite-dimensional
fiber `Finset ι → ℝ`, of size linear in `t`. Under suitable global hypotheses, for instance
finitely many critical points, all nondegenerate, `|df|` bounded below outside a compact set and
the Hessian of `f` bounded, this is the mechanism by which the low-lying spectrum of `Δ_t`
concentrates near the critical points; no spectral statement is proved here. The proof expands
`d_t d_t^*` and `d_t^* d_t` and uses the canonical anticommutation relation `εᵢ ιⱼ + ιⱼ εᵢ = δᵢⱼ`
(`Module.Basis.exteriorCreation_mul_exteriorContraction_add`), together with the symmetry of
second derivatives of `C²` maps.

## Main definitions

* `TauCeti.euclideanWittenDiff`: the deformed exterior derivative `d_t = d + t df ∧`.
* `TauCeti.euclideanWittenCodiff`: its formal adjoint `d_t^* = d^* + t ι_{∇f}`.
* `TauCeti.euclideanWittenLaplacian`: the Witten Laplacian `d_t d_t^* + d_t^* d_t`.

## Main results

* `TauCeti.sum_euclideanWittenDiff_mul_sub_sum_mul_euclideanWittenCodiff`: the Lagrange identity
  exhibiting `d_t^*` as the formal adjoint of `d_t`.
* `TauCeti.euclideanWittenLaplacian_apply`: Witten's frame formula for the Witten Laplacian.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340, §2.
-/

public section

noncomputable section

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The Witten differential** `d_t = d + t df ∧` on differential forms on `ℝ^ι`, written in the
coordinates of the exterior basis: `d_t φ = ∑ᵢ εᵢ (∂ᵢ φ + t ∂ᵢ f · φ)`, with `εᵢ` exterior
multiplication by `dx^i`. -/
def euclideanWittenDiff (f : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → Finset ι → ℝ) :
    (ι → ℝ) → Finset ι → ℝ :=
  fun x ↦ ∑ i, (Pi.basisFun ℝ ι).exteriorCreation i
    (fderiv ℝ φ x (Pi.single i 1) + (t * fderiv ℝ f x (Pi.single i 1)) • φ x)

/-- **The Witten codifferential** `d_t^* = d^* + t ι_{∇f}`, the formal adjoint of the Witten
differential for the Euclidean metric, written in the coordinates of the exterior basis:
`d_t^* φ = ∑ᵢ ιᵢ (-∂ᵢ φ + t ∂ᵢ f · φ)`, with `ιᵢ` contraction with `∂ᵢ`. -/
def euclideanWittenCodiff (f : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → Finset ι → ℝ) :
    (ι → ℝ) → Finset ι → ℝ :=
  fun x ↦ ∑ i, (Pi.basisFun ℝ ι).exteriorContraction i
    (-fderiv ℝ φ x (Pi.single i 1) + (t * fderiv ℝ f x (Pi.single i 1)) • φ x)

/-- **The Witten Laplacian** `Δ_t = d_t d_t^* + d_t^* d_t` on differential forms on `ℝ^ι`. -/
def euclideanWittenLaplacian (f : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → Finset ι → ℝ) :
    (ι → ℝ) → Finset ι → ℝ :=
  euclideanWittenDiff f t (euclideanWittenCodiff f t φ) +
    euclideanWittenCodiff f t (euclideanWittenDiff f t φ)

theorem euclideanWittenDiff_apply (f : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → Finset ι → ℝ)
    (x : ι → ℝ) :
    euclideanWittenDiff f t φ x = ∑ i, (Pi.basisFun ℝ ι).exteriorCreation i
      (fderiv ℝ φ x (Pi.single i 1) + (t * fderiv ℝ f x (Pi.single i 1)) • φ x) :=
  (rfl)

theorem euclideanWittenCodiff_apply (f : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → Finset ι → ℝ)
    (x : ι → ℝ) :
    euclideanWittenCodiff f t φ x = ∑ i, (Pi.basisFun ℝ ι).exteriorContraction i
      (-fderiv ℝ φ x (Pi.single i 1) + (t * fderiv ℝ f x (Pi.single i 1)) • φ x) :=
  (rfl)

theorem euclideanWittenLaplacian_def (f : (ι → ℝ) → ℝ) (t : ℝ) (φ : (ι → ℝ) → Finset ι → ℝ) :
    euclideanWittenLaplacian f t φ =
      euclideanWittenDiff f t (euclideanWittenCodiff f t φ) +
        euclideanWittenCodiff f t (euclideanWittenDiff f t φ) :=
  (rfl)

/-- **The Lagrange identity: `d_t^*` is the formal adjoint of `d_t`.** For forms `φ`, `ψ`
differentiable at `x`, the pointwise pairings `⟨d_t φ, ψ⟩` and `⟨φ, d_t^* ψ⟩` differ by the
divergence `∑ᵢ ∂ᵢ ⟨φ, ιᵢ ψ⟩`, whose integral vanishes for compactly supported forms. -/
theorem sum_euclideanWittenDiff_mul_sub_sum_mul_euclideanWittenCodiff (f : (ι → ℝ) → ℝ) (t : ℝ)
    {φ ψ : (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ} (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    ∑ s, euclideanWittenDiff f t φ x s * ψ x s - ∑ s, φ x s * euclideanWittenCodiff f t ψ x s =
      ∑ i, fderiv ℝ (fun y ↦ ∑ s, φ y s * (Pi.basisFun ℝ ι).exteriorContraction i (ψ y) s) x
        (Pi.single i 1) := by
  set ε := (Pi.basisFun ℝ ι).exteriorCreation
  set κ := (Pi.basisFun ℝ ι).exteriorContraction
  -- The derivative of the pairing `⟨φ, ιᵢ ψ⟩`, by the product rule.
  have hpair : ∀ i, fderiv ℝ (fun y ↦ ∑ s, φ y s * κ i (ψ y) s) x (Pi.single i 1) =
      ∑ s, (fderiv ℝ φ x (Pi.single i 1) s * κ i (ψ x) s +
        φ x s * κ i (fderiv ℝ ψ x (Pi.single i 1)) s) := by
    intro i
    have hφs : ∀ s, HasFDerivAt (fun y ↦ φ y s)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s).comp
          (fderiv ℝ φ x)) x := fun s ↦
      (hasFDerivAt_apply (𝕜 := ℝ) s (φ x)).comp x hφ.hasFDerivAt
    have hψs : ∀ s, HasFDerivAt (fun y ↦ κ i (ψ y) s)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s).comp
          ((LinearMap.toContinuousLinearMap (κ i)).comp (fderiv ℝ ψ x))) x := fun s ↦ by
      have := (hasFDerivAt_apply (𝕜 := ℝ) s (LinearMap.toContinuousLinearMap (κ i) (ψ x))).comp x
        ((LinearMap.toContinuousLinearMap (κ i)).hasFDerivAt.comp x hψ.hasFDerivAt)
      simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap'] using this
    have h : HasFDerivAt (fun y ↦ ∑ s, φ y s * κ i (ψ y) s)
        (∑ s, (φ x s • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s).comp
          ((LinearMap.toContinuousLinearMap (κ i)).comp (fderiv ℝ ψ x)) +
          κ i (ψ x) s • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s).comp
            (fderiv ℝ φ x))) x :=
      HasFDerivAt.fun_sum fun s _ ↦ (hφs s).mul (hψs s)
    rw [h.fderiv]
    simp [add_comm, mul_comm]
  have e₁ : ∑ s, euclideanWittenDiff f t φ x s * ψ x s = ∑ i, ∑ s, ε i
      (fderiv ℝ φ x (Pi.single i 1) + (t * fderiv ℝ f x (Pi.single i 1)) • φ x) s * ψ x s := by
    simp only [euclideanWittenDiff_apply, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have e₂ : ∑ s, φ x s * euclideanWittenCodiff f t ψ x s = ∑ i, ∑ s, φ x s * κ i
      (-fderiv ℝ ψ x (Pi.single i 1) + (t * fderiv ℝ f x (Pi.single i 1)) • ψ x) s := by
    simp only [euclideanWittenCodiff_apply, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [e₁, e₂, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(Pi.basisFun ℝ ι).sum_exteriorCreation_apply_mul, ← Finset.sum_sub_distrib, hpair]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [map_add, map_neg, map_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

section FrameFormula

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [LinearOrder ι] in
/-- The derivative of one summand `c ∂ᵥ φ + t ∂ᵥ f · φ` of a Witten operator, by the product
rule. -/
private theorem hasFDerivAt_wittenSummand {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → F} {x : ι → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ x) (t c : ℝ) (v : ι → ℝ) :
    HasFDerivAt (fun y ↦ c • fderiv ℝ φ y v + (t * fderiv ℝ f y v) • φ y)
      (c • (ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ φ) x) +
        ((t * fderiv ℝ f x v) • fderiv ℝ φ x +
          (t • (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x)).smulRight
            (φ x))) x := by
  have hφ' : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₁ : HasFDerivAt (fun y ↦ fderiv ℝ φ y v)
      ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ φ) x)) x :=
    (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hφ'.hasFDerivAt
  have h₂ : HasFDerivAt (fun y ↦ t * fderiv ℝ f y v)
      (t • (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hf'.hasFDerivAt).const_mul t
  exact (h₁.const_smul c).add (h₂.smul (hφ.differentiableAt (by norm_num)).hasFDerivAt)

omit [LinearOrder ι] in
/-- The derivative of one summand of a Witten operator, evaluated on a vector. -/
private theorem fderiv_wittenSummand_apply {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → F} {x : ι → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ x) (t c : ℝ) (v w : ι → ℝ) :
    fderiv ℝ (fun y ↦ c • fderiv ℝ φ y v + (t * fderiv ℝ f y v) • φ y) x w =
      c • fderiv ℝ (fderiv ℝ φ) x w v + (t * fderiv ℝ (fderiv ℝ f) x w v) • φ x +
        (t * fderiv ℝ f x v) • fderiv ℝ φ x w := by
  rw [(hasFDerivAt_wittenSummand hf hφ t c v).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  abel

/-- The derivative of a sum `∑ᵢ Lᵢ (c ∂ᵢ φ + t ∂ᵢ f · φ)` of summands of a Witten operator, for
fixed linear maps `Lᵢ` of the coefficient space. -/
private theorem fderiv_sum_wittenSummand_apply {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ x) (t c : ℝ)
    (L : ι → Module.End ℝ (Finset ι → ℝ)) (w : ι → ℝ) :
    fderiv ℝ (fun y ↦ ∑ i, L i (c • fderiv ℝ φ y (Pi.single i 1) +
        (t * fderiv ℝ f y (Pi.single i 1)) • φ y)) x w =
      ∑ i, L i (c • fderiv ℝ (fderiv ℝ φ) x w (Pi.single i 1) +
        (t * fderiv ℝ (fderiv ℝ f) x w (Pi.single i 1)) • φ x +
          (t * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ φ x w) := by
  have h : ∀ i, HasFDerivAt (fun y ↦ LinearMap.toContinuousLinearMap (L i)
      (c • fderiv ℝ φ y (Pi.single i 1) + (t * fderiv ℝ f y (Pi.single i 1)) • φ y))
      ((LinearMap.toContinuousLinearMap (L i)).comp
        (fderiv ℝ (fun y ↦ c • fderiv ℝ φ y (Pi.single i 1) +
          (t * fderiv ℝ f y (Pi.single i 1)) • φ y) x)) x := fun i ↦
    (LinearMap.toContinuousLinearMap (L i)).hasFDerivAt.comp x
      (hasFDerivAt_wittenSummand hf hφ t c (Pi.single i 1)).differentiableAt.hasFDerivAt
  simp only [LinearMap.coe_toContinuousLinearMap'] at h
  rw [(HasFDerivAt.fun_sum fun i _ ↦ h i).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', fderiv_wittenSummand_apply hf hφ]

/-- **Witten's frame formula.** For a function `f` and a form `φ` on `ℝ^ι` that are `C²` at `x`,
the Witten Laplacian at `x` is

`Δ_t φ = -∑ᵢ ∂ᵢ² φ + t² |df|² φ + t ∑_{i,j} Hess f(∂ᵢ, ∂ⱼ) ⁅εᵢ, ιⱼ⁆ φ`,

with `⁅εᵢ, ιⱼ⁆ = εᵢ ιⱼ - ιⱼ εᵢ` the commutator of exterior multiplication by `dx^i` and contraction
with `∂ⱼ`. -/
theorem euclideanWittenLaplacian_apply {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}
    {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ x) (t : ℝ) :
    euclideanWittenLaplacian f t φ x =
      ∑ i, (-fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) +
          (t ^ 2 * fderiv ℝ f x (Pi.single i 1) ^ 2) • φ x) +
        t • ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
          ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
            (φ x) := by
  set ε := (Pi.basisFun ℝ ι).exteriorCreation
  set κ := (Pi.basisFun ℝ ι).exteriorContraction
  -- Abbreviations for the first and second derivatives at `x`.
  set D : ι → Finset ι → ℝ := fun i ↦ fderiv ℝ φ x (Pi.single i 1)
  set S : ι → ι → Finset ι → ℝ := fun i j ↦ fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single j 1)
  set g : ι → ℝ := fun i ↦ fderiv ℝ f x (Pi.single i 1)
  set H : ι → ι → ℝ := fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)
  have hS : ∀ i j, S i j = S j i := fun i j ↦ (hφ.isSymmSndFDerivAt (by simp)) _ _
  have hH : ∀ i j, H i j = H j i := fun i j ↦ (hf.isSymmSndFDerivAt (by simp)) _ _
  -- The two halves of the Laplacian as double sums of creation-contraction products.
  set Z : ι → ι → Finset ι → ℝ := fun i j ↦
    -S i j + (t * g j) • D i - (t * g i) • D j + (t ^ 2 * g i * g j) • φ x
  set W : ι → ι → Finset ι → ℝ := fun i j ↦ (t * H i j) • φ x
  have hcod : euclideanWittenCodiff f t φ = fun y ↦ ∑ i, κ i ((-1 : ℝ) •
      fderiv ℝ φ y (Pi.single i 1) + (t * fderiv ℝ f y (Pi.single i 1)) • φ y) := by
    funext y
    simp only [euclideanWittenCodiff_apply, neg_one_smul, κ]
  have hdiff : euclideanWittenDiff f t φ = fun y ↦ ∑ i, ε i ((1 : ℝ) •
      fderiv ℝ φ y (Pi.single i 1) + (t * fderiv ℝ f y (Pi.single i 1)) • φ y) := by
    funext y
    simp only [euclideanWittenDiff_apply, one_smul, ε]
  have h₁ : euclideanWittenDiff f t (euclideanWittenCodiff f t φ) x =
      ∑ i, ∑ j, ε i (κ j (Z i j + W i j)) := by
    rw [euclideanWittenDiff_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hcod, fderiv_sum_wittenSummand_apply hf hφ t (-1) κ (Pi.single i 1), ← hcod,
      euclideanWittenCodiff_apply, Finset.smul_sum, ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [ε, κ, Z, W, D, S, g, H, map_add, map_sub, map_smul, map_neg]
    module
  have h₂ : euclideanWittenCodiff f t (euclideanWittenDiff f t φ) x =
      ∑ i, ∑ j, κ j (ε i (Z i j - W i j)) := by
    rw [euclideanWittenCodiff_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hdiff, fderiv_sum_wittenSummand_apply hf hφ t 1 ε (Pi.single j 1), ← hdiff,
      euclideanWittenDiff_apply, Finset.smul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hS' := hS j i
    have hH' := hH j i
    simp only [S, H] at hS' hH'
    simp only [ε, κ, Z, W, D, S, g, H, hS', hH', map_add, map_sub, map_smul, map_neg]
    module
  rw [euclideanWittenLaplacian_def, Pi.add_apply, h₁, h₂,
    sum_creation_contraction_of_anticommutator ε κ
      (Pi.basisFun ℝ ι).exteriorCreation_mul_exteriorContraction_add,
    Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Z]
    module
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [W, H, map_smul, smul_smul]

end FrameFormula

end TauCeti
