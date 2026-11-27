/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening.Direction
public import TauCeti.Analysis.PDE.Regularity.Boundary.GradientLp
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

that is `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩` for every `v ∈ H¹₀(Ω)`, with `G ∈ Lᵖ(Ω)`. This file
proves the `W^{1,p}` estimate up to the curved boundary,

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(Ω)}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ` and vanishes off a set `s` on which the
coefficients are close to a constant elliptic matrix `A` and `Dγ` is close to a constant
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_graph`). The constant `C` and the
tolerance `δ` depend only on `n`, `p`, the ellipticity constants `λ, Λ` of `A` and the bound `K`.
For `Dγ` continuous at a point `x₀` of the graph (for instance a `C¹` graph) and coefficients
continuous up to the boundary at `x₀`, `s` can be a small ball centred at `x₀` and `A = a(x₀)`:
this is the estimate for solutions supported near a boundary point, the local piece that a
partition of unity can assemble into a global `W^{1,p}` estimate on a domain with `C¹` boundary.
Only the oscillation of `Dγ` on `s` enters, not a modulus of continuity of `Dγ`, so beyond this
continuity no Hölder or Dini condition on the boundary is needed. It is the curved
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
  simp only [pullbackPrincipal_apply, abs_det_fderiv_shearAlong hγ hγν y, one_smul, hinv,
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
    (singleton_nonempty z) (fun y _ => norm_fderiv_shearAlong_le hν.le (hγ y) (hK y))
    (fun y _ w => ?_) one_pos (fun y _ => (abs_det_fderiv_shearAlong hγ hγν y).ge)
  · obtain ⟨h1, h2, h3⟩ := uniformlyEllipticOn_iff.1 h
    exact uniformlyEllipticOn_iff.2 ⟨h1, h2, fun _ _ => h3 (mem_singleton z)⟩
  · -- `w = DΨ(Φ y) (DΦ(y) w)` with `‖DΨ‖ ≤ 1 + K`.
    calc ‖w‖ = ‖fderiv ℝ (shearAlong (-γ) ν) (shearAlong γ ν y)
          (fderiv ℝ (shearAlong γ ν) y w)‖ := by
          rw [← ContinuousLinearMap.comp_apply, fderiv_shearAlong_neg_comp_fderiv hγν (hγ _) (hγ _),
            ContinuousLinearMap.id_apply]
      _ ≤ (1 + K) * ‖fderiv ℝ (shearAlong γ ν) y w‖ :=
          ContinuousLinearMap.le_of_opNorm_le _
            (norm_fderiv_shearAlong_neg_le hν.le (hγ _) (hK _)) _

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
      (fderiv_shearAlong_neg_comp_fderiv hγν (hγ y) (hγ _)),
    matrixBilinearForm_pullbackPrincipal_eq_bilinearComp (fun _ => A)
      (fderiv_shearAlong_neg_comp_fderiv hγν (hγ (shearAlong (-γ) ν x₀)) (hγ _)), hT₀,
    abs_det_fderiv_shearAlong hγ hγν, abs_det_fderiv_shearAlong hγ hγν, one_smul, one_smul]
  -- `T - T₀ = (Dγ(x₀) - Dγ(Φ y)) ν`, of norm at most `δ`.
  have hdiff : T - T₀ = (fderiv ℝ γ x₀ - fderiv ℝ γ (shearAlong γ ν y)).smulRight ν := by
    ext w
    simp only [T, T₀, fderiv_shearAlong (hγ.neg _), fderiv_neg, add_sub_add_left_eq_sub, sub_apply,
      ContinuousLinearMap.smulRight_apply, neg_apply, neg_smul, sub_neg_eq_add, PiLp.add_apply,
      PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, sub_smul, PiLp.sub_apply]
    abel
  have hTT : ‖T.adjoint - T₀.adjoint‖ ≤ δ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map, hdiff, ContinuousLinearMap.norm_smulRight_apply,
      hν, mul_one, norm_sub_rev]
    exact hγx₀
  have hT (z : E) : ‖(fderiv ℝ (shearAlong (-γ) ν) z).adjoint‖ ≤ 1 + K :=
    (LinearIsometryEquiv.norm_map _ _).trans_le (norm_fderiv_shearAlong_neg_le hν.le (hγ _) (hK _))
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
        gcongr <;> exact hT _
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
  have hinj : InjOn (shearAlong γ ν) ((⊤ : Opens E) : Set E) := (injective_shearAlong hγν).injOn
  have hΦL (y : E) (_ : y ∈ ((⊤ : Opens E) : Set E)) :=
    norm_fderiv_shearAlong_le hν.le (hγ y) (hK y)
  have hdet (y : E) (_ : y ∈ ((⊤ : Opens E) : Set E)) :=
    (abs_det_fderiv_shearAlong hγ hγν y).ge
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
    (hmpH : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω))
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {G : E → E} {u v : W1p volume (⊤ : Opens E) 2}
    (hv : ∀ᵐ y, W1p.value v y = W1p.value u (shearAlong γ ν y))
    (hu : ∀ w : W1p0 volume Ω 2,
      energyFormH1 a 0 0 (W1p.restrictL (le_top : Ω ≤ ⊤) u) (w : W1p volume Ω 2) =
        ∫ x in Ω, ⟪G x, W1p.gradient (w : W1p volume Ω 2) x⟫_ℝ)
    (w : W1p0 volume H 2) :
    energyFormH1 (pullbackPrincipal (shearAlong γ ν) a) 0 0 (W1p.restrictL (le_top : H ≤ ⊤) v)
        (w : W1p volume H 2) =
      ∫ y in H, ⟪pullbackDrift (shearAlong γ ν) G y, W1p.gradient (w : W1p volume H 2) y⟫_ℝ := by
  have hmaps : MapsTo (shearAlong γ ν) H Ω := hpre ▸ mapsTo_preimage _ _
  have hΨmaps : MapsTo (shearAlong (-γ) ν) Ω H := fun x hx => by
    rw [← hpre, mem_preimage, shearAlong_shearAlong_neg hγν]
    exact hx
  have hinj : InjOn (shearAlong γ ν) H := (injective_shearAlong hγν).injOn
  have hΦL (y : E) (_ : y ∈ (H : Set E)) := norm_fderiv_shearAlong_le hν.le (hγ y) (hK y)
  have hdet (y : E) (_ : y ∈ (H : Set E)) := (abs_det_fderiv_shearAlong hγ hγν y).ge
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
    (fun y _ => norm_fderiv_shearAlong_neg_le hν.le (hγ y) (hK y)) one_pos
    (fun y _ => (abs_det_fderiv_shearAlong hγ.neg (neg_apply_add_smul_eq hγν) y).ge)
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
          fderiv_comp_fderiv_shearAlong_neg hγν (hγ _) (hγ _), ContinuousLinearMap.adjoint_id,
          ContinuousLinearMap.id_apply]
    _ ≤ (1 + K) * ‖h y‖ := by
        rw [hy]
        exact ContinuousLinearMap.le_of_opNorm_le _ ((LinearIsometryEquiv.norm_map _ _).trans_le
          (norm_fderiv_shearAlong_neg_le hν.le (hγ _) (hK _))) _

/-- **Gradients in `Lᵖ` under the shear.** If `h = DΦ* (g ∘ Φ)` for the shear `Φ = shearAlong γ ν`
and `g ∈ Lᵖ`, then `h ∈ Lᵖ` and `‖g‖_{Lᵖ} ≤ (1 + K) ‖h‖_{Lᵖ}`, since `Φ` preserves volume. -/
private theorem memLp_and_eLpNorm_le_of_eq_adjoint_shearAlong (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {g h : E → E} {p : ℝ≥0∞} (hh : AEStronglyMeasurable h volume)
    (hgh : ∀ᵐ y, h y = (fderiv ℝ (shearAlong γ ν) y).adjoint (g (shearAlong γ ν y)))
    (hg : MemLp g p volume) :
    MemLp h p volume ∧ eLpNorm g p volume ≤ ENNReal.ofReal (1 + K) * eLpNorm h p volume := by
  have hmp := measurePreserving_shearAlong volume hγ hγν
  refine ⟨(hg.comp_measurePreserving hmp).of_le_mul (c := 1 + K) hh ?_, ?_⟩
  · filter_upwards [hgh] with y hy
    rw [hy, Function.comp_apply]
    exact ContinuousLinearMap.le_of_opNorm_le _ ((LinearIsometryEquiv.norm_map _ _).trans_le
      (norm_fderiv_shearAlong_le hν.le (hγ y) (hK y))) _
  · rw [← eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hmp]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hg.aestronglyMeasurable.comp_measurePreserving hmp)
      (hgh.mono fun y hy => norm_gradient_comp_shearAlong_le hν hγ hγν hK hy) p

/-- **Divergence data under the shear.** For the shear `Φ = shearAlong γ ν` carrying `H` onto `Ω`,
the transformed datum `G' = DΨ(Φ ·) (G ∘ Φ)` lies in `L^q(H)` when `G ∈ L^q(Ω)`, with
`‖G'‖_{L^q(H)} ≤ (1 + K) ‖G‖_{L^q(Ω)}`. -/
private theorem memLp_pullbackDrift_shearAlong_and_eLpNorm_le (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω H : Opens E} (hpre : shearAlong γ ν ⁻¹' (Ω : Set E) = H)
    (hmpH : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω))
    {G : E → E} {q : ℝ≥0∞} (hG : MemLp G q (volume.restrict Ω)) :
    MemLp (pullbackDrift (shearAlong γ ν) G) q (volume.restrict H) ∧
      eLpNorm (pullbackDrift (shearAlong γ ν) G) q (volume.restrict H) ≤
        ENNReal.ofReal (1 + K) * eLpNorm G q (volume.restrict Ω) := by
  have hmaps : MapsTo (shearAlong γ ν) H Ω := hpre ▸ mapsTo_preimage _ _
  have hG' := memLp_pullbackDrift (differentiable_shearAlong hγ).differentiableOn hmaps
    (fun y _ => norm_fderiv_shearAlong_le hν.le (hγ y) (hK y)) one_pos
    (fun y _ => (abs_det_fderiv_shearAlong hγ hγν y).ge)
    (differentiable_shearAlong hγ.neg).differentiableOn
    (fun y _ => norm_fderiv_shearAlong_neg_le hν.le (hγ y) (hK y))
    (fun y _ => shearAlong_neg_shearAlong hγν y) (fun x _ => shearAlong_shearAlong_neg hγν x) hG
  refine ⟨hG', ?_⟩
  rw [← eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hmpH]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hG'.aestronglyMeasurable ?_ q
  -- `G'(y) = |det DΦ(y)| DΨ(Φ y) G(Φ y)` with `|det DΦ| = 1` and `‖DΨ‖ ≤ 1 + K`.
  filter_upwards [ae_restrict_mem H.isOpen.measurableSet] with y hy
  rw [pullbackDrift_eq_of_invOn (differentiable_shearAlong hγ).differentiableOn hmaps
    (differentiable_shearAlong hγ.neg).differentiableOn
    (fun x _ => shearAlong_shearAlong_neg hγν x) (fun y _ => shearAlong_neg_shearAlong hγν y) G hy,
    abs_det_fderiv_shearAlong hγ hγν y, one_smul, Function.comp_apply]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_fderiv_shearAlong_neg_le hν.le (hγ _) (hK _)) _

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
`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩` for every `v ∈ H¹₀(Ω)`, with `G ∈ Lᵖ(Ω)`. If `∇u` lies in `Lᵖ`,
then

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
          MemLp (W1p.gradient u : E → E) p volume → MemLp G p (volume.restrict Ω) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict Ω) := by
  obtain ⟨C₀, δ₀, hδ₀, hflat⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero
    (n := n) hp hp_top (1 * lam / (1 + K) ^ 2)
    ((1 + K) ^ Fintype.card (Fin (n + 1)) * (1 + K) ^ 2 * Lam)
  set D : ℝ := (1 + K) ^ 2 + 2 * |Lam| * (1 + K)
  have hD : 0 < D := by positivity
  refine ⟨(1 + K) ^ 2 * C₀, δ₀ / D, div_pos hδ₀ hD, ?_⟩
  intro Ω ν γ a A s x₀ hν hγd hγν hK hΩ hs ha hA hγs has u G hu0 hus hu hgp hGp
  -- The half-space `H = {0 < ⟪y, ν⟫}`, carried onto `Ω` by the shear `Φ = shearAlong γ ν`.
  let H : Opens E := ⟨{y | 0 < ⟪y, ν⟫_ℝ}, isOpen_lt continuous_const (by fun_prop)⟩
  have hΩ' : (Ω : Set E) = {x | γ x < ⟪x, ν⟫_ℝ} := Set.ext hΩ
  have hpre : shearAlong γ ν ⁻¹' (Ω : Set E) = H := hΩ' ▸ preimage_shearAlong_setOf_lt_inner hν hγν
  have hmp := measurePreserving_shearAlong (ν := ν) volume hγd hγν
  have hmpH : MeasurePreserving (shearAlong γ ν) (volume.restrict H) (volume.restrict Ω) :=
    hΩ' ▸ measurePreserving_shearAlong_restrict volume hν hγd hγν
  -- The flattened function `v = u ∘ Φ` and the hypotheses of the flat estimate for it.
  obtain ⟨v, hv_val, hv_grad⟩ := exists_value_and_gradient_compL_shearAlong hν hγd hγν hK u
  have hv0 : ∀ᵐ y, y ∉ H → W1p.value v y = 0 := by
    filter_upwards [hv_val, hmp.quasiMeasurePreserving.ae hu0] with y h1 h2 hy
    exact h1.trans (h2 fun h => hy (by rw [← SetLike.mem_coe, ← hpre]; exact h))
  have hvs : ∀ᵐ y, y ∉ shearAlong γ ν ⁻¹' s → W1p.gradient v y = 0 := by
    filter_upwards [hv_grad, hmp.quasiMeasurePreserving.ae hus] with y h1 h2 hy
    rw [h1, h2 hy, map_zero]
  obtain ⟨hvp, hgv⟩ := memLp_and_eLpNorm_le_of_eq_adjoint_shearAlong hν hγd hγν hK
    (by simpa using Lp.aestronglyMeasurable (W1p.gradient v)) hv_grad hgp
  obtain ⟨hG'p, hG'⟩ := memLp_pullbackDrift_shearAlong_and_eLpNorm_le hν hγd hγν hK hpre hmpH hGp
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
    (energyFormH1_pullbackPrincipal_shearAlong_eq hν hγd hγν hK hpre hmpH hv_val hu) hvp hG'p
  -- Back to `Ω`: the norms of `∇u` and `G` are those of `∇v` and `G'` up to factors `1 + K`.
  calc eLpNorm (W1p.gradient u : E → E) p volume ≤
        ENNReal.ofReal (1 + K) * eLpNorm (W1p.gradient v : E → E) p volume := hgv
    _ ≤ ENNReal.ofReal (1 + K) * (C₀ * (ENNReal.ofReal (1 + K) *
          eLpNorm G p (volume.restrict Ω))) :=
        mul_le_mul_right (hflat'.trans (mul_le_mul_right hG' _)) _
    _ = ((1 + K) ^ 2 * C₀ : ℝ≥0) * eLpNorm G p (volume.restrict Ω) := by
        rw [ENNReal.ofReal_add zero_le_one K.coe_nonneg, ENNReal.ofReal_one,
          ENNReal.ofReal_coe_nnreal]
        push_cast
        ring

end PDE

end TauCeti
