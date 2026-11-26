/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening.Direction
public import TauCeti.Analysis.PDE.Regularity.Boundary.GradientLp
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.EuclideanMatrix
import TauCeti.Analysis.Calculus.GraphFlattening.Volume
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables

/-!
# The `W^{1,p}` estimate up to a differentiable graph

Let `ν` be a unit vector of `ℝ^{n+1}` and let `γ : ℝ^{n+1} → ℝ` be differentiable, invariant under
translation along `ν`, with `‖Dγ‖ ≤ K`. Then `Ω = {x | γ x < ⟪x, ν⟫}` is the region above the graph
of a differentiable Lipschitz function over the hyperplane `ν^⊥`, a `C¹` graph when `Dγ` is
continuous. Let `u ∈ H¹(ℝ^{n+1})` vanish off `Ω` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`,

that is `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩` for every `v ∈ H¹₀(Ω)`, with `G ∈ L²(Ω) ∩ Lᵖ(Ω)`. This file
proves the `W^{1,p}` estimate up to the curved boundary,

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(Ω)}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ` and vanishes off a set `s` on which the
coefficients are close to a constant elliptic matrix `A` and `Dγ` is close to a constant
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_graph`). The constant `C` and the
tolerance `δ` depend only on `n`, `p`, the ellipticity constants `λ, Λ` of `A` and the bound `K`.
For coefficients continuous up to the boundary at a point `x₀` of the graph, `s` can be a small ball
centred at `x₀` and `A = a(x₀)`: this is the estimate for solutions supported near a boundary
point, the local piece that a partition of unity can assemble into a global `W^{1,p}` estimate
on a domain with `C¹` boundary. Only the oscillation of `Dγ` on `s` enters, not a modulus of
continuity of `Dγ`, so no Hölder or Dini condition on the boundary is needed. It is the curved
counterpart of the flat-boundary estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero`.

## The argument

The shear `Φ = TauCeti.shearAlong γ ν`, `Φ y = y + γ y ν`, maps the half-space
`H = {0 < ⟪y, ν⟫}` onto `Ω`, with inverse the shear `Ψ` by `-γ`. Its derivative is a transvection,
of Jacobian determinant one (`TauCeti.det_fderiv_shearAlong`), so `Φ` preserves volume
(`TauCeti.measurePreserving_shearAlong`), and `DΨ(Φ y)` is the inverse of `DΦ(y)`, of norm at most
`1 + K`. The flattened function `v = u ∘ Φ` vanishes off `H`, and solves
`-∂ᵢ(a'ⁱʲ ∂ⱼv) = -div G'` weakly in `H`
(`TauCeti.PDE.energyFormH1_compL_eq_setIntegral_add_setIntegral_inner`), with
`a'(y) = DΨ(Φ y) a(Φ y) DΨ(Φ y)ᵀ` and `G'(y) = DΨ(Φ y) G(Φ y)`. Where `∇v` does not vanish, `a'`
is close to the constant matrix `A' = DΨ(x₀) A DΨ(x₀)ᵀ`, which is uniformly elliptic with constants
depending on `λ, Λ, K`, so the flat estimate bounds `‖∇v‖_{Lᵖ}` by `‖G'‖_{Lᵖ(H)}`. Since `Φ`
preserves volume and `DΦ`, `DΨ` are bounded by `1 + K`, the norms of `∇u` and `∇v`, and of `G` and
`G'`, agree up to factors `1 + K`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (flattening the boundary) and Section 9.5 (the `W^{2,p}` estimate near the boundary,
  by flattening and freezing the coefficients).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics 96, American Mathematical Society, 2008 (`Lᵖ` estimates for divergence-form
  equations near the boundary).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### The flattening shear -/

section Shear

variable {γ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν : EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}

/-- The shear by a function with derivative bounded by `K` has derivative bounded by `1 + K`. -/
private theorem norm_fderiv_shearAlong_le (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) (y : E) : ‖fderiv ℝ (shearAlong γ ν) y‖ ≤ 1 + K := by
  rw [fderiv_shearAlong (hγ y)]
  exact_mod_cast norm_id_add_smulRight_le hν.le (hK y)

/-- The inverse shear `shearAlong (-γ) ν` has derivative bounded by `1 + K`. -/
private theorem norm_fderiv_shearAlong_neg_le (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) (y : E) : ‖fderiv ℝ (shearAlong (-γ) ν) y‖ ≤ 1 + K :=
  norm_fderiv_shearAlong_le hν hγ.neg (fun x => by rw [fderiv_neg, norm_neg]; exact hK x) y

/-- The shear `shearAlong γ ν` and its inverse have Jacobian determinant one, so its Jacobian is
at least one in absolute value. -/
private theorem one_le_abs_det_fderiv_shearAlong (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    1 ≤ |(fderiv ℝ (shearAlong γ ν) y).det| ∧ 1 ≤ |(fderiv ℝ (shearAlong (-γ) ν) y).det| := by
  rw [det_fderiv_shearAlong hγν (hγ y),
    det_fderiv_shearAlong (fun x t => by simp only [Pi.neg_apply, hγν]) (hγ.neg y), abs_one]
  exact ⟨le_rfl, le_rfl⟩

/-- The derivative of the inverse shear at `Φ y` is a left inverse of the derivative of the shear
`Φ = shearAlong γ ν` at `y`. -/
private theorem fderiv_shearAlong_neg_comp_fderiv (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y) ∘L fderiv ℝ (shearAlong γ ν) y =
      ContinuousLinearMap.id ℝ E :=
  fderiv_comp_fderiv_eq_id_of_eqOn_comp_id uniqueDiffWithinAt_univ
    (hasFDerivAt_shearAlong (hγ y)).differentiableAt
    (hasFDerivAt_shearAlong (hγ.neg _)).differentiableAt
    (fun z _ => shearAlong_neg_shearAlong hγν z) (mem_univ y)

/-- The derivative of the shear `Φ = shearAlong γ ν` at `y` is a left inverse of the derivative of
the inverse shear at `Φ y`. -/
private theorem fderiv_comp_fderiv_shearAlong_neg (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (y : E) :
    fderiv ℝ (shearAlong γ ν) y ∘L fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y) =
      ContinuousLinearMap.id ℝ E := by
  have h := fderiv_comp_fderiv_eq_id_of_eqOn_comp_id uniqueDiffWithinAt_univ
    (hasFDerivAt_shearAlong (hγ.neg (shearAlong γ ν y))).differentiableAt
    (hasFDerivAt_shearAlong (hγ (shearAlong (-γ) ν (shearAlong γ ν y)))).differentiableAt
    (fun z _ => shearAlong_shearAlong_neg hγν z) (mem_univ _)
  rwa [shearAlong_neg_shearAlong hγν] at h

/-- The shear `Φ = shearAlong γ ν` carries `H = {0 < ⟪y, ν⟫}` onto `Ω = {γ x < ⟪x, ν⟫}`. -/
private theorem preimage_shearAlong_eq (hν : ‖ν‖ = 1) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    {Ω H : Set E} (hΩ : ∀ x, x ∈ Ω ↔ γ x < ⟪x, ν⟫_ℝ) (hH : ∀ y, y ∈ H ↔ (0 : ℝ) < ⟪y, ν⟫_ℝ) :
    shearAlong γ ν ⁻¹' Ω = H := by
  ext y
  rw [mem_preimage, hΩ, hH, ← sub_pos, real_inner_shearAlong_sub hν hγν]

/-- The principal coefficient transformed by the shear `Φ = shearAlong γ ν` is measurable on the
half-space `H = Φ⁻¹(Ω)` when the coefficient is measurable on `Ω`. -/
private theorem aestronglyMeasurable_pullbackPrincipal_shearAlong (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {Ω H : Opens E}
    (hmp : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω))
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict Ω)) :
    AEStronglyMeasurable (pullbackPrincipal (shearAlong γ ν) a) (volume.restrict H) := by
  have hΦd := differentiable_shearAlong (ν := ν) hγ
  have hΨd := differentiable_shearAlong (ν := ν) hγ.neg
  set S : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun y =>
    (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y))
  have hS : AEStronglyMeasurable S (volume.restrict H) :=
    Matrix.continuous_toEuclideanCLM_symm.comp_aestronglyMeasurable ((measurable_fderiv ℝ _).comp
      hΦd.continuous.measurable).aestronglyMeasurable
  -- Since `|det DΦ| = 1`, the transformed coefficient is `S (a ∘ Φ) Sᵀ`.
  refine ((hS.mul (ha.comp_measurePreserving hmp)).mul
    ((Continuous.matrix_transpose continuous_id).comp_aestronglyMeasurable hS)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  -- The inverse Jacobian matrix of `Φ` at `y` is the Jacobian matrix of `Ψ` at `Φ y`.
  have hinv : ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ (shearAlong γ ν) y))⁻¹ = S y := by
    simp only [S]
    rw [← toEuclideanCLM_inv_fderiv_of_invOn (U := ⊤) (V := ⊤) hΦd.differentiableOn
      (mapsTo_univ _ _) hΨd.differentiableOn (fun x _ => shearAlong_shearAlong_neg hγν x)
      (fun x _ => shearAlong_neg_shearAlong hγν x) (mem_univ y), StarAlgEquiv.symm_apply_apply]
  simp only [pullbackPrincipal_apply, det_fderiv_shearAlong hγν (hγ y), abs_one, one_smul, hinv,
    Function.comp_apply, Pi.mul_apply, id_eq]

/-- **The flattened constant coefficient is elliptic.** For a constant matrix `A`, uniformly
elliptic with constants `λ, Λ`, and a shear `Φ = shearAlong γ ν` by a function with derivative
bounded by `K`, the constant matrix `A' = DΦ(z)⁻¹ A DΦ(z)⁻ᵀ` is uniformly elliptic with constants
`λ / (1 + K)²` and `(1 + K)^(n + 1) (1 + K)² Λ`. -/
private theorem uniformlyEllipticOn_pullbackPrincipal_shearAlong_const (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hA : UniformlyEllipticOn univ (fun _ : E => A) lam Lam) (z : E) :
    UniformlyEllipticOn univ (fun _ : E => pullbackPrincipal (shearAlong γ ν) (fun _ => A) z)
      (1 * lam / (1 + K) ^ 2) ((1 + K) ^ Fintype.card (Fin (n + 1)) * (1 + K) ^ 2 * Lam) := by
  have h := hA.pullbackPrincipal (Φ := shearAlong γ ν) (L' := 1 + K) (s := {z}) (mapsTo_univ _ _)
    (singleton_nonempty z) (fun y _ => norm_fderiv_shearAlong_le hν hγ hK y)
    (fun y _ w => ?_) one_pos (fun y _ => by rw [det_fderiv_shearAlong hγν (hγ y), abs_one])
  · obtain ⟨h1, h2, h3⟩ := uniformlyEllipticOn_iff.1 h
    exact uniformlyEllipticOn_iff.2 ⟨h1, h2, fun _ _ => h3 (mem_singleton z)⟩
  · -- `w = DΨ(Φ y) (DΦ(y) w)` with `‖DΨ‖ ≤ 1 + K`.
    calc ‖w‖ = ‖fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y)
          (fderiv ℝ (shearAlong γ ν) y w)‖ := by
          rw [← ContinuousLinearMap.comp_apply, fderiv_shearAlong_neg_comp_fderiv hγ hγν,
            ContinuousLinearMap.id_apply]
      _ ≤ (1 + K) * ‖fderiv ℝ (shearAlong γ ν) y w‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (norm_fderiv_shearAlong_neg_le hν hγ hK _) (norm_nonneg _))

/-- **The flattened coefficient is close to the flattened constant.** Let `Φ = shearAlong γ ν`
and `Ψ = shearAlong (-γ) ν`. If at the point `Φ y` the coefficient `a` is within `δ` of the
constant `A`, whose bilinear form has norm at most `M`, and `Dγ` is within `δ` of `Dγ(x₀)`, then
the transformed coefficient `a'(y)` is within `δ ((1 + K)² + 2 M (1 + K))` of the constant
`A' = DΨ(x₀) A DΨ(x₀)ᵀ`. -/
private theorem norm_matrixBilinearForm_pullbackPrincipal_sub_le (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {M δ : ℝ} {x₀ y : E}
    (hA : ‖matrixBilinearForm A‖ ≤ M)
    (ha : ‖matrixBilinearForm (a (shearAlong γ ν y)) - matrixBilinearForm A‖ ≤ δ)
    (hγx₀ : ‖fderiv ℝ γ (shearAlong γ ν y) - fderiv ℝ γ x₀‖ ≤ δ) :
    ‖matrixBilinearForm (pullbackPrincipal (shearAlong γ ν) a y) -
        matrixBilinearForm (pullbackPrincipal (shearAlong γ ν) (fun _ => A)
          (shearAlong (-γ) ν x₀))‖ ≤ δ * ((1 + K) ^ 2 + 2 * M * (1 + K)) := by
  set T := fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y)
  set T₀ := fderiv ℝ (shearAlong (-γ) ν) x₀
  have hT₀ : fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν (shearAlong (-γ) ν x₀)) = T₀ := by
    rw [shearAlong_shearAlong_neg hγν]
  rw [matrixBilinearForm_pullbackPrincipal_eq_bilinearComp a
      (fderiv_shearAlong_neg_comp_fderiv hγ hγν y),
    matrixBilinearForm_pullbackPrincipal_eq_bilinearComp (fun _ => A)
      (fderiv_shearAlong_neg_comp_fderiv hγ hγν (shearAlong (-γ) ν x₀)), hT₀,
    det_fderiv_shearAlong hγν (hγ _), det_fderiv_shearAlong hγν (hγ _), abs_one, one_smul,
    one_smul]
  -- `T - T₀ = (Dγ(x₀) - Dγ(Φ y)) ν`, of norm at most `δ`.
  have hdiff : T - T₀ = (fderiv ℝ γ x₀ - fderiv ℝ γ (shearAlong γ ν y)).smulRight ν := by
    ext w
    simp [T, T₀, fderiv_shearAlong (hγ.neg _), fderiv_neg, sub_smul]
    abel
  have hTT : ‖T.adjoint - T₀.adjoint‖ ≤ δ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map, hdiff, ContinuousLinearMap.norm_smulRight_apply,
      hν, mul_one, norm_sub_rev]
    exact hγx₀
  have hT : ‖T.adjoint‖ ≤ 1 + K := by
    rw [LinearIsometryEquiv.norm_map]
    exact norm_fderiv_shearAlong_neg_le hν hγ hK _
  have hT₀' : ‖T₀.adjoint‖ ≤ 1 + K := by
    rw [LinearIsometryEquiv.norm_map]
    exact norm_fderiv_shearAlong_neg_le hν hγ hK _
  have hδ : 0 ≤ δ :=
    (norm_nonneg (matrixBilinearForm (a (shearAlong γ ν y)) - matrixBilinearForm A)).trans ha
  have hM : 0 ≤ M := (norm_nonneg (matrixBilinearForm A)).trans hA
  -- Split the difference into three terms, each bounded by
  -- `ContinuousLinearMap.norm_bilinearComp_le`.
  set B := matrixBilinearForm (a (shearAlong γ ν y))
  set B₀ := matrixBilinearForm A
  have hsplit : B.bilinearComp T.adjoint T.adjoint - B₀.bilinearComp T₀.adjoint T₀.adjoint =
      (B - B₀).bilinearComp T.adjoint T.adjoint +
        B₀.bilinearComp (T.adjoint - T₀.adjoint) T.adjoint +
        B₀.bilinearComp T₀.adjoint (T.adjoint - T₀.adjoint) := by
    ext ξ η
    simp [map_sub]
  rw [hsplit]
  refine le_trans (@norm_add₃_le (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _) (le_trans
    (add_le_add_three (ContinuousLinearMap.norm_bilinearComp_le _ _ _)
      (ContinuousLinearMap.norm_bilinearComp_le _ _ _)
      (ContinuousLinearMap.norm_bilinearComp_le _ _ _)) ?_)
  calc _ ≤ δ * (1 + K) * (1 + K) + M * δ * (1 + K) + M * (1 + K) * δ := by
        gcongr
    _ = δ * ((1 + K) ^ 2 + 2 * M * (1 + K)) := by ring

/-- **The flattened function.** Precomposition with the shear `Φ = shearAlong γ ν` maps
`u ∈ H¹(ℝ^{n+1})` to some `v ∈ H¹(ℝ^{n+1})` with value `u ∘ Φ` and gradient `DΦ* (∇u ∘ Φ)`. -/
private theorem exists_value_and_gradient_compL_shearAlong (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) (u : W1p volume (⊤ : Opens E) 2) :
    ∃ v : W1p volume (⊤ : Opens E) 2,
      (∀ᵐ y, W1p.value v y = W1p.value u (shearAlong γ ν y)) ∧
      ∀ᵐ y, W1p.gradient v y =
        (fderiv ℝ (shearAlong γ ν) y).adjoint (W1p.gradient u (shearAlong γ ν y)) := by
  have hmaps : MapsTo (shearAlong γ ν) ((⊤ : Opens E) : Set E) ((⊤ : Opens E) : Set E) :=
    fun _ _ => trivial
  have hinj : InjOn (shearAlong γ ν) ((⊤ : Opens E) : Set E) :=
    (Function.LeftInverse.injective (g := shearAlong (-γ) ν)
      (shearAlong_neg_shearAlong hγν)).injOn
  have hΦL (y : E) (_ : y ∈ ((⊤ : Opens E) : Set E)) := norm_fderiv_shearAlong_le hν hγ hK y
  have hdet (y : E) (_ : y ∈ ((⊤ : Opens E) : Set E)) :=
    (one_le_abs_det_fderiv_shearAlong hγ hγν y).1
  refine ⟨W1p.compL (shearAlong γ ν) ENNReal.ofNat_ne_top
      (differentiable_shearAlong hγ).differentiableOn hinj hmaps hΦL one_pos hdet u, ?_, ?_⟩
  · filter_upwards [(ae_restrict_iff' (⊤ : Opens E).isOpen.measurableSet).1
      (W1p.value_compL_ae _ ENNReal.ofNat_ne_top (differentiable_shearAlong hγ).differentiableOn
        hinj hmaps hΦL one_pos hdet u)] with y hy
    exact hy trivial
  · filter_upwards [(ae_restrict_iff' (⊤ : Opens E).isOpen.measurableSet).1
      (W1p.gradient_compL_ae _ ENNReal.ofNat_ne_top (differentiable_shearAlong hγ).differentiableOn
        hinj hmaps hΦL one_pos hdet u)] with y hy
    exact hy trivial

/-- **The flattened equation.** If `u ∈ H¹(ℝ^{n+1})` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in
`Ω = Φ(H)`, for the shear `Φ = shearAlong γ ν`, then a function `v` with value `u ∘ Φ` solves
`-∂ᵢ(a'ⁱʲ ∂ⱼv) = -div G'` weakly in `H`, with the transformed coefficient `a'` and datum `G'`. -/
private theorem energyFormH1_pullbackPrincipal_shearAlong_eq (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω H : Opens E} (hpre : shearAlong γ ν ⁻¹' (Ω : Set E) = H)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {G : E → E} {u v : W1p volume (⊤ : Opens E) 2}
    (hv : ∀ᵐ y, W1p.value v y = W1p.value u (shearAlong γ ν y))
    (hu : ∀ w : W1p0 volume Ω 2,
      energyFormH1 a 0 0 (W1p.restrictL (le_top : Ω ≤ ⊤) u) (w : W1p volume Ω 2) =
        ∫ x in Ω, ⟪G x, W1p.gradient (w : W1p volume Ω 2) x⟫_ℝ)
    (w : W1p0 volume H 2) :
    energyFormH1 (pullbackPrincipal (shearAlong γ ν) a) 0 0 (W1p.restrictL (le_top : H ≤ ⊤) v)
        (w : W1p volume H 2) =
      ∫ y in H, ⟪pullbackDrift (shearAlong γ ν) G y, W1p.gradient (w : W1p volume H 2) y⟫_ℝ := by
  have hmaps : MapsTo (shearAlong γ ν) H Ω := fun y hy => by
    rw [← mem_preimage, hpre]
    exact hy
  have hΨmaps : MapsTo (shearAlong (-γ) ν) Ω H := fun x hx => by
    rw [← hpre, mem_preimage, shearAlong_shearAlong_neg hγν]
    exact hx
  have hinj : InjOn (shearAlong γ ν) H :=
    (Function.LeftInverse.injective (g := shearAlong (-γ) ν)
      (shearAlong_neg_shearAlong hγν)).injOn
  have hΦL (y : E) (_ : y ∈ (H : Set E)) := norm_fderiv_shearAlong_le hν hγ hK y
  have hdet (y : E) (_ : y ∈ (H : Set E)) := (one_le_abs_det_fderiv_shearAlong hγ hγν y).1
  have hmpH : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω) := by
    have h := (measurePreserving_shearAlong volume hγ hγν).restrict_preimage
      Ω.isOpen.measurableSet
    rwa [hpre] at h
  -- The weak equation of `u` in the form of the change of variables theorem, with `f = 0`.
  have hu' : ∀ w : W1p0 volume Ω 2,
      energyFormH1 a 0 0 (W1p.restrictL (le_top : Ω ≤ ⊤) u) (w : W1p volume Ω 2) =
        ∫ y in Ω, (0 : E → ℝ) y * W1p.value (w : W1p volume Ω 2) y ∂volume +
          ∫ y in Ω, ⟪G y, W1p.gradient (w : W1p volume Ω 2) y⟫_ℝ ∂volume := fun w => by
    simpa using hu w
  -- On `H` the restriction of `v` is `u ∘ Φ`, the change of variables of `u` on `Ω`.
  have hvw : W1p.restrictL (le_top : H ≤ ⊤) v = W1p.compL (shearAlong γ ν) ENNReal.ofNat_ne_top
      (differentiable_shearAlong hγ).differentiableOn hinj hmaps hΦL one_pos hdet
      (W1p.restrictL (le_top : Ω ≤ ⊤) u) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_restrictL_ae (le_top : H ≤ ⊤) v, ae_restrict_of_ae hv,
      W1p.value_compL_ae (shearAlong γ ν) ENNReal.ofNat_ne_top
        (differentiable_shearAlong hγ).differentiableOn hinj hmaps hΦL one_pos hdet
        (W1p.restrictL (le_top : Ω ≤ ⊤) u),
      hmpH.quasiMeasurePreserving.ae (W1p.value_restrictL_ae (le_top : Ω ≤ ⊤) u)]
      with y h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  simpa [hvw] using energyFormH1_compL_eq_setIntegral_add_setIntegral_inner (mu := volume)
    (differentiable_shearAlong hγ).differentiableOn hinj hmaps hΦL one_pos hdet
    (differentiable_shearAlong hγ.neg).differentiableOn hΨmaps
    (fun y _ => norm_fderiv_shearAlong_neg_le hν hγ hK y) one_pos
    (fun y _ => (one_le_abs_det_fderiv_shearAlong hγ hγν y).2)
    (fun y _ => shearAlong_neg_shearAlong hγν y) (fun x _ => shearAlong_shearAlong_neg hγν x) hu' w

/-- **Gradients under the shear.** If `∇v = DΦ* (∇u ∘ Φ)` for the shear `Φ = shearAlong γ ν`,
then `‖∇u ∘ Φ‖ ≤ (1 + K) ‖∇v‖` pointwise, since `DΨ(Φ ·)* ∘ DΦ* = id` for the inverse shear `Ψ`. -/
private theorem norm_gradient_comp_shearAlong_le (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {g h : E → E} {y : E}
    (hy : h y = (fderiv ℝ (shearAlong γ ν) y).adjoint (g (shearAlong γ ν y))) :
    ‖g (shearAlong γ ν y)‖ ≤ (1 + K) * ‖h y‖ := by
  calc ‖g (shearAlong γ ν y)‖ =
        ‖(fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y)).adjoint
          ((fderiv ℝ (shearAlong γ ν) y).adjoint (g (shearAlong γ ν y)))‖ := by
        rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
          fderiv_comp_fderiv_shearAlong_neg hγ hγν, ContinuousLinearMap.adjoint_id,
          ContinuousLinearMap.id_apply]
    _ ≤ (1 + K) * ‖h y‖ := by
        rw [hy]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [LinearIsometryEquiv.norm_map]
        gcongr
        exact norm_fderiv_shearAlong_neg_le hν hγ hK _

/-- **Divergence data under the shear.** For the shear `Φ = shearAlong γ ν` carrying `H` onto `Ω`,
the transformed datum `G' = DΨ(Φ ·) (G ∘ Φ)` lies in `L^q(H)` when `G ∈ L^q(Ω)`, with
`‖G'‖_{L^q(H)} ≤ (1 + K) ‖G‖_{L^q(Ω)}`. -/
private theorem memLp_pullbackDrift_shearAlong_and_eLpNorm_le (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω H : Opens E} (hpre : shearAlong γ ν ⁻¹' (Ω : Set E) = H)
    {G : E → E} {q : ℝ≥0∞} (hG : MemLp G q (volume.restrict Ω)) :
    MemLp (pullbackDrift (shearAlong γ ν) G) q (volume.restrict H) ∧
      eLpNorm (pullbackDrift (shearAlong γ ν) G) q (volume.restrict H) ≤
        ENNReal.ofReal (1 + K) * eLpNorm G q (volume.restrict Ω) := by
  have hmaps : MapsTo (shearAlong γ ν) H Ω := fun y hy => by
    rw [← mem_preimage, hpre]
    exact hy
  have hmpH : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω) := by
    have h := (measurePreserving_shearAlong volume hγ hγν).restrict_preimage
      Ω.isOpen.measurableSet
    rwa [hpre] at h
  have hG' := memLp_pullbackDrift (differentiable_shearAlong hγ).differentiableOn hmaps
    (fun y _ => norm_fderiv_shearAlong_le hν hγ hK y) one_pos
    (fun y _ => (one_le_abs_det_fderiv_shearAlong hγ hγν y).1)
    (differentiable_shearAlong hγ.neg).differentiableOn
    (fun y _ => norm_fderiv_shearAlong_neg_le hν hγ hK y)
    (fun y _ => shearAlong_neg_shearAlong hγν y) (fun x _ => shearAlong_shearAlong_neg hγν x) hG
  refine ⟨hG', ?_⟩
  rw [← eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hmpH]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hG'.aestronglyMeasurable ?_ q
  -- `G'(y) = |det DΦ(y)| DΨ(Φ y) G(Φ y)` with `|det DΦ| = 1` and `‖DΨ‖ ≤ 1 + K`.
  filter_upwards [ae_restrict_mem H.isOpen.measurableSet] with y hy
  rw [pullbackDrift_eq_of_invOn (differentiable_shearAlong hγ).differentiableOn hmaps
    (differentiable_shearAlong hγ.neg).differentiableOn
    (fun x _ => shearAlong_shearAlong_neg hγν x) (fun y _ => shearAlong_neg_shearAlong hγν y) G hy,
    det_fderiv_shearAlong hγν (hγ y), abs_one, one_smul, Function.comp_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_shearAlong_neg_le hν hγ hK _) (norm_nonneg _))

end Shear

/-! ### The estimate -/

/-- **The `W^{1,p}` estimate up to a differentiable graph, near an elliptic matrix.** Let
`2 < p < ∞`, `0 < λ ≤ Λ` and `K ≥ 0`. There are constants `C` and `δ > 0`, depending only on `n`,
`p`, `λ`, `Λ` and `K`, with the following property. Let `ν` be a unit vector, let `γ` be
differentiable, invariant under translation along `ν`, with `‖Dγ‖ ≤ K`, and let
`Ω = {x | γ x < ⟪x, ν⟫}` be the region above its graph. Let `A` be a constant matrix, uniformly
elliptic with constants `λ, Λ` and not necessarily symmetric, and let `s` be a measurable set on
which `Dγ` is within `δ` of `Dγ(x₀)` and on whose part in `Ω` the bilinear form of `a`, measurable
on `Ω`, is within `δ` of that of `A`, in operator norm. Let `u ∈ H¹(ℝ^{n+1})` vanish off `Ω`, let
`∇u` vanish off `s`, and let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`, that is
`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩` for every `v ∈ H¹₀(Ω)`, with `G ∈ L²(Ω) ∩ Lᵖ(Ω)`. If `∇u` lies in
`Lᵖ`, then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(Ω)}`.

No continuity of `a` or of `Dγ`, and no bound on `a` off `s`, are assumed. For `γ = 0` the region
`Ω` is a half-space and this is the flat estimate
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero`. -/
theorem exists_eLpNorm_gradient_le_of_norm_sub_le_of_graph {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {Ω : Opens E} {ν : E} {γ : E → ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {s : Set E} {x₀ : E},
        ‖ν‖ = 1 → Differentiable ℝ γ → (∀ x (t : ℝ), γ (x + t • ν) = γ x) →
        (∀ x, ‖fderiv ℝ γ x‖ ≤ K) → (∀ x, x ∈ Ω ↔ γ x < ⟪x, ν⟫_ℝ) → MeasurableSet s →
        AEStronglyMeasurable a (volume.restrict Ω) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x ∈ s, ‖fderiv ℝ γ x - fderiv ℝ γ x₀‖ ≤ δ) →
        (∀ x ∈ s, x ∈ Ω → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ Ω → W1p.value u x = 0) → (∀ᵐ x, x ∉ s → W1p.gradient u x = 0) →
          (∀ v : W1p0 volume Ω 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : Ω ≤ ⊤) u) (v : W1p volume Ω 2) =
              ∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) →
          MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict Ω) → MemLp G p (volume.restrict Ω) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict Ω) := by
  obtain ⟨C₀, δ₀, hδ₀, hflat⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero
    (n := n) hp hp_top (1 * lam / (1 + K) ^ 2)
    ((1 + K) ^ Fintype.card (Fin (n + 1)) * (1 + K) ^ 2 * Lam)
  set D : ℝ := (1 + K) ^ 2 + 2 * |Lam| * (1 + K)
  have hD : 0 < D := by positivity
  refine ⟨(1 + K) ^ 2 * C₀, δ₀ / D, div_pos hδ₀ hD, ?_⟩
  intro Ω ν γ a A s x₀ hν hγd hγν hK hΩ hs ha hA hγs has u G hu0 hus hu hgp hG2 hGp
  -- The half-space `H = {0 < ⟪y, ν⟫}`, carried onto `Ω` by the shear `Φ = shearAlong γ ν`.
  let H : Opens E :=
    ⟨{y | 0 < ⟪y, ν⟫_ℝ}, isOpen_lt continuous_const (continuous_id.inner continuous_const)⟩
  have hpre : shearAlong γ ν ⁻¹' (Ω : Set E) = H :=
    preimage_shearAlong_eq hν hγν hΩ fun _ => Iff.rfl
  have hmp : MeasurePreserving (shearAlong γ ν) volume volume :=
    measurePreserving_shearAlong volume hγd hγν
  have hmpH : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω) := by
    have h := hmp.restrict_preimage Ω.isOpen.measurableSet
    rwa [hpre] at h
  -- The flattened function `v = u ∘ Φ` and the hypotheses of the flat estimate for it.
  obtain ⟨v, hv_val, hv_grad⟩ := exists_value_and_gradient_compL_shearAlong hν hγd hγν hK u
  have hv0 : ∀ᵐ y, y ∉ H → W1p.value v y = 0 := by
    filter_upwards [hv_val, hmp.quasiMeasurePreserving.ae hu0] with y h1 h2 hy
    rw [h1]
    exact h2 fun h => hy (by rw [← SetLike.mem_coe, ← hpre]; exact h)
  have hvs : ∀ᵐ y, y ∉ shearAlong γ ν ⁻¹' s → W1p.gradient v y = 0 := by
    filter_upwards [hv_grad, hmp.quasiMeasurePreserving.ae hus] with y h1 h2 hy
    rw [h1, h2 hy, map_zero]
  have hvp : MemLp (W1p.gradient v : E → E) p volume := by
    refine (hgp.comp_measurePreserving hmp).of_le_mul (c := 1 + K)
      (by simpa using Lp.aestronglyMeasurable (W1p.gradient v)) ?_
    filter_upwards [hv_grad] with y h
    rw [h, Function.comp_apply]
    refine ((fderiv ℝ (shearAlong γ ν) y).adjoint.le_opNorm _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    gcongr
    exact norm_fderiv_shearAlong_le hν hγd hK y
  obtain ⟨hG'2, -⟩ := memLp_pullbackDrift_shearAlong_and_eLpNorm_le hν hγd hγν hK hpre hG2
  obtain ⟨hG'p, hG'⟩ := memLp_pullbackDrift_shearAlong_and_eLpNorm_le hν hγd hγν hK hpre hGp
  -- The flat estimate, with the constant matrix `A' = DΨ(x₀) A DΨ(x₀)ᵀ`.
  have hflat' := hflat (H := H) (ν := ν) (c₀ := 0) (a := pullbackPrincipal (shearAlong γ ν) a)
    (A := pullbackPrincipal (shearAlong γ ν) (fun _ => A) (shearAlong (-γ) ν x₀))
    (s := shearAlong γ ν ⁻¹' s) (fun h => by simp [h] at hν) (fun _ => Iff.rfl)
    (hs.preimage (differentiable_shearAlong hγd).continuous.measurable)
    (aestronglyMeasurable_pullbackPrincipal_shearAlong hγd hγν hmpH ha)
    (uniformlyEllipticOn_pullbackPrincipal_shearAlong_const hν hγd hγν hK hA _)
    (fun y hys hyH => (norm_matrixBilinearForm_pullbackPrincipal_sub_le hν hγd hγν hK
      ((hA.opNorm_matrixBilinearForm_le (mem_univ x₀)).trans (le_abs_self Lam))
      (has _ hys (by rw [← SetLike.mem_coe, ← hpre] at hyH; exact hyH)) (hγs _ hys)).trans
      (div_mul_cancel₀ δ₀ hD.ne').le)
    v (pullbackDrift (shearAlong γ ν) G) hv0 hvs
    (energyFormH1_pullbackPrincipal_shearAlong_eq hν hγd hγν hK hpre hv_val hu) hvp hG'2 hG'p
  -- Back to `Ω`: the norms of `∇u` and `G` are those of `∇v` and `G'` up to factors `1 + K`.
  have hK1 : ENNReal.ofReal (1 + K) = ((1 + K : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_add, NNReal.coe_one]
  calc eLpNorm (W1p.gradient u : E → E) p volume =
        eLpNorm ((W1p.gradient u : E → E) ∘ shearAlong γ ν) p volume :=
        (eLpNorm_comp_measurePreserving hgp.aestronglyMeasurable hmp).symm
    _ ≤ ENNReal.ofReal (1 + K) * eLpNorm (W1p.gradient v : E → E) p volume :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hgp.aestronglyMeasurable.comp_measurePreserving hmp)
          (hv_grad.mono fun y hy => norm_gradient_comp_shearAlong_le hν hγd hγν hK hy) p
    _ ≤ ENNReal.ofReal (1 + K) * (C₀ * (ENNReal.ofReal (1 + K) *
          eLpNorm G p (volume.restrict Ω))) := by
        gcongr
        exact hflat'.trans (mul_le_mul_right hG' _)
    _ = ((1 + K) ^ 2 * C₀ : ℝ≥0) * eLpNorm G p (volume.restrict Ω) := by
        rw [hK1]
        push_cast
        ring

end PDE

end TauCeti
