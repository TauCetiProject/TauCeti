/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening.Direction
public import TauCeti.Analysis.PDE.Regularity.Boundary.GradientLp
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.EuclideanMatrix
import TauCeti.Analysis.Calculus.GraphFlattening.Volume
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Sobolev.W1p.Localization

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

The same holds for local solutions near a curved boundary portion
(`TauCeti.PDE.exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le_of_graph`): if an
open set `Ω` agrees with the region above the graph inside a ball `B(x₀, ρ)` centred on the graph,
and `u ∈ H¹(Ω)` solves the equation in `Ω` and vanishes on `∂Ω ∩ B(x₀, ρ)`, then

`‖∇u‖_{Lᵖ(Ω ∩ B(x₀, θρ))} ≤`
`  C (‖G‖_{Lᵖ(Ω ∩ B(x₀, ρ))} + |B(x₀, ρ)|^(1/p - 1/2) ‖∇u‖_{L²(Ω ∩ B(x₀, ρ))})`,

with `C`, `θ` and the tolerance `δ` depending only on `n`, `p`, `λ, Λ` and `K`. Nothing is assumed
about `Ω` or `a` away from `B(x₀, ρ)`. This is the estimate at a boundary point that a covering of
`∂Ω` assembles into a global `W^{1,p}` estimate on a domain with `C¹` boundary.

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

For the local estimate the shear carries `Ω ∩ B(x₀, ρ)` to an open set `U'` that agrees with `H`
inside the ball of radius `2R`, `R = ρ / (4 (1 + K))`, about the point `Ψ x₀` of the hyperplane,
since `Φ` and `Ψ` are `(1 + K)`-Lipschitz. The restriction of `u` to `Ω ∩ B(x₀, ρ)` solves the
equation tested against `H¹₀`, so the flattened function `v = u ∘ Φ` solves the transformed
equation in `U'`, and it vanishes on the flat boundary portion: for a cutoff `ψ` equal to one on
`B(x₀, ρ / 2)`, `ψ u ∈ H¹₀(Ω)` restricts to `H¹₀(Ω ∩ B(x₀, ρ))` and is carried to `H¹₀(U')`. The
local estimate near a flat boundary portion
`TauCeti.PDE.exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le` then applies to `v`
on the ball of radius `R`, and the norms are carried back by the shear.

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
  {F F' : Type*} [NormedAddCommGroup F] [NormedAddCommGroup F']

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

/-- **The flattened function.** For the shear `Φ = shearAlong γ ν` and open sets `U` and
`U' = Φ⁻¹(U)`, precomposition with `Φ` maps `u ∈ H¹(U)` to some `v ∈ H¹(U')` with value `u ∘ Φ`
and gradient `DΦ* (∇u ∘ Φ)`. It lies in `H¹₀(U')` when `u ∈ H¹₀(U)`, and if `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `U`, then `v` solves `-∂ᵢ(a'ⁱʲ ∂ⱼv) = -div G'` weakly in `U'`,
with the transformed coefficient `a'` and datum `G'`. -/
private theorem exists_compL_shearAlong (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {U U' : Opens E}
    (hU' : (U' : Set E) = shearAlong γ ν ⁻¹' U) (u : W1p volume U 2) :
    ∃ v : W1p volume U' 2,
      (∀ᵐ y ∂volume.restrict U', W1p.value v y = W1p.value u (shearAlong γ ν y)) ∧
      (∀ᵐ y ∂volume.restrict U', W1p.gradient v y =
        (fderiv ℝ (shearAlong γ ν) y).adjoint (W1p.gradient u (shearAlong γ ν y))) ∧
      (u ∈ w1p0Submodule volume U 2 → v ∈ w1p0Submodule volume U' 2) ∧
      ∀ (a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (G : E → E),
        (∀ w : W1p0 volume U 2, energyFormH1 a 0 0 u (w : W1p volume U 2) =
          ∫ x in U, ⟪G x, W1p.gradient (w : W1p volume U 2) x⟫_ℝ) →
        ∀ w : W1p0 volume U' 2, energyFormH1 (pullbackPrincipal (shearAlong γ ν) a) 0 0 v
          (w : W1p volume U' 2) = ∫ y in U',
            ⟪pullbackDrift (shearAlong γ ν) G y, W1p.gradient (w : W1p volume U' 2) y⟫_ℝ := by
  have hΦd := differentiable_shearAlong (ν := ν) hγ
  have hmaps : MapsTo (shearAlong γ ν) U' U := fun y hy => by
    rw [hU'] at hy
    exact hy
  have hΨmaps : MapsTo (shearAlong (-γ) ν) U U' := fun x hx => by
    rw [hU', mem_preimage, shearAlong_shearAlong_neg hγν]
    exact hx
  have hinj : InjOn (shearAlong γ ν) U' := (injective_shearAlong hγν).injOn
  have hΦL (y : E) (_ : y ∈ (U' : Set E)) := norm_fderiv_shearAlong_le hν.le (hγ y) (hK y)
  have hdet (y : E) (_ : y ∈ (U' : Set E)) := (abs_det_fderiv_shearAlong hγ hγν y).ge
  refine ⟨W1p.compL (shearAlong γ ν) ENNReal.ofNat_ne_top hΦd.differentiableOn hinj hmaps hΦL
      one_pos hdet u,
    W1p.value_compL_ae _ _ _ hinj hmaps hΦL one_pos hdet u,
    W1p.gradient_compL_ae _ _ _ hinj hmaps hΦL one_pos hdet u,
    fun hu => W1p.compL_mem_w1p0Submodule_of_leftInvOn _ _ _ hinj hmaps hΦL one_pos hdet
      (differentiable_shearAlong hγ.neg).continuous.continuousOn hΨmaps
      (fun y _ => shearAlong_neg_shearAlong hγν y) hu, fun a G hu w => ?_⟩
  -- The weak equation of `u` in the form of the change of variables theorem, with `f = 0`.
  have hu' : ∀ w : W1p0 volume U 2,
      energyFormH1 a 0 0 u (w : W1p volume U 2) =
        ∫ y in U, (0 : E → ℝ) y * W1p.value (w : W1p volume U 2) y ∂volume +
          ∫ y in U, ⟪G y, W1p.gradient (w : W1p volume U 2) y⟫_ℝ ∂volume := fun w => by
    simpa using hu w
  simpa using energyFormH1_compL_eq_setIntegral_add_setIntegral_inner (mu := volume)
    hΦd.differentiableOn hinj hmaps hΦL one_pos hdet
    (differentiable_shearAlong hγ.neg).differentiableOn hΨmaps
    (fun y _ => norm_fderiv_shearAlong_neg_le hν.le (hγ y) (hK y)) one_pos
    (fun y _ => (abs_det_fderiv_shearAlong hγ.neg (neg_apply_add_smul_eq hγν) y).ge)
    (fun y _ => shearAlong_neg_shearAlong hγν y) (fun x _ => shearAlong_shearAlong_neg hγν x) hu' w

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
  obtain ⟨v', hv', -, -, hv'eq⟩ :=
    exists_compL_shearAlong hν hγ hγν hK hpre.symm (W1p.restrictL (le_top : Ω ≤ ⊤) u)
  -- On `H` the restriction of `v` is `u ∘ Φ`, the flattening of `u` on `Ω`.
  have hvw : W1p.restrictL (le_top : H ≤ ⊤) v = v' := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_restrictL_ae (le_top : H ≤ ⊤) v, ae_restrict_of_ae hv, hv',
      hmpH.quasiMeasurePreserving.ae (W1p.value_restrictL_ae (le_top : Ω ≤ ⊤) u)]
      with y h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  rw [hvw]
  exact hv'eq a G hu w

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

/-- The adjoint of the derivative of the shear `Φ = shearAlong γ ν` by a function with
`‖Dγ‖ ≤ K` increases norms by at most the factor `1 + K`. -/
private theorem norm_adjoint_fderiv_shearAlong_apply_le (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) (y w : E) :
    ‖(fderiv ℝ (shearAlong γ ν) y).adjoint w‖ ≤ (1 + K) * ‖w‖ :=
  ContinuousLinearMap.le_of_opNorm_le _ ((LinearIsometryEquiv.norm_map _ _).trans_le
    (norm_fderiv_shearAlong_le hν.le (hγ y) (hK y))) _

/-- **Norms through the shear, from the curved side.** If `‖f (Φ y)‖ ≤ c ‖g y‖` almost everywhere
on a set `t` containing `Φ⁻¹(S)`, for the shear `Φ = shearAlong γ ν`, then
`‖f‖_{L^q(S)} ≤ c ‖g‖_{L^q(t)}`, since `Φ` preserves volume. -/
private theorem eLpNorm_restrict_le_of_ae_norm_comp_shearAlong_le (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {f : E → F} {g : E → F'} {S t : Set E}
    (hS : MeasurableSet S) (hSt : shearAlong γ ν ⁻¹' S ⊆ t)
    (hf : AEStronglyMeasurable f (volume.restrict S)) {c : ℝ}
    (hfg : ∀ᵐ y ∂volume.restrict t, ‖f (shearAlong γ ν y)‖ ≤ c * ‖g y‖) (q : ℝ≥0∞) :
    eLpNorm f q (volume.restrict S) ≤ ENNReal.ofReal c * eLpNorm g q (volume.restrict t) := by
  have hmp := (measurePreserving_shearAlong volume hγ hγν).restrict_preimage hS
  rw [← eLpNorm_comp_measurePreserving hf hmp]
  exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hf.comp_measurePreserving hmp)
    (ae_restrict_of_ae_restrict_of_subset hSt hfg) q).trans
      (mul_le_mul_right (eLpNorm_mono_measure _ (Measure.restrict_mono hSt le_rfl)) _)

/-- **Norms through the shear, from the flat side.** If `‖g y‖ ≤ c ‖f (Φ y)‖` almost everywhere
on a set `t` contained in `Φ⁻¹(S)`, for the shear `Φ = shearAlong γ ν`, and `f ∈ L^q(S)`, then
`g ∈ L^q(t)` and `‖g‖_{L^q(t)} ≤ c ‖f‖_{L^q(S)}`, since `Φ` preserves volume. -/
private theorem memLp_and_eLpNorm_restrict_le_of_ae_norm_le_comp_shearAlong
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {f : E → F} {g : E → F'}
    {S t : Set E} (hS : MeasurableSet S) (htS : t ⊆ shearAlong γ ν ⁻¹' S) {q : ℝ≥0∞}
    (hf : MemLp f q (volume.restrict S)) (hg : AEStronglyMeasurable g (volume.restrict t)) {c : ℝ}
    (hgf : ∀ᵐ y ∂volume.restrict t, ‖g y‖ ≤ c * ‖f (shearAlong γ ν y)‖) :
    MemLp g q (volume.restrict t) ∧
      eLpNorm g q (volume.restrict t) ≤ ENNReal.ofReal c * eLpNorm f q (volume.restrict S) := by
  have hmp := measurePreserving_shearAlong volume hγ hγν
  exact ⟨((hf.comp_measurePreserving (hmp.restrict_preimage hS)).mono_measure
      (Measure.restrict_mono htS le_rfl)).of_le_mul hg hgf,
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hg hgf q).trans
      (mul_le_mul_right (hmp.eLpNorm_comp_restrict_le_of_mapsTo hS htS f q) _)⟩

/-- **Gradients in `Lᵖ` under the shear.** If `h = DΦ* (g ∘ Φ)` for the shear `Φ = shearAlong γ ν`
and `g ∈ Lᵖ`, then `h ∈ Lᵖ` and `‖g‖_{Lᵖ} ≤ (1 + K) ‖h‖_{Lᵖ}`, since `Φ` preserves volume. -/
private theorem memLp_and_eLpNorm_le_of_eq_adjoint_shearAlong (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {g h : E → E} {p : ℝ≥0∞} (hh : AEStronglyMeasurable h volume)
    (hgh : ∀ᵐ y, h y = (fderiv ℝ (shearAlong γ ν) y).adjoint (g (shearAlong γ ν y)))
    (hg : MemLp g p volume) :
    MemLp h p volume ∧ eLpNorm g p volume ≤ ENNReal.ofReal (1 + K) * eLpNorm h p volume := by
  have h₁ := memLp_and_eLpNorm_restrict_le_of_ae_norm_le_comp_shearAlong hγ hγν
    MeasurableSet.univ (subset_univ _) (hg.restrict univ) (hh.restrict (s := univ))
    (ae_restrict_of_ae (hgh.mono fun y hy => by
      rw [hy]
      exact norm_adjoint_fderiv_shearAlong_apply_le hν hγ hK y _))
  have h₂ := eLpNorm_restrict_le_of_ae_norm_comp_shearAlong_le hγ hγν MeasurableSet.univ
    (subset_univ _) (hg.aestronglyMeasurable.restrict (s := univ))
    (ae_restrict_of_ae (hgh.mono fun y hy => norm_gradient_comp_shearAlong_le hν hγ hγν hK hy)) p
  rw [Measure.restrict_univ] at h₁ h₂
  exact ⟨h₁.1, h₂⟩

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
  obtain ⟨v, hv_val, hv_grad, -, -⟩ :=
    exists_compL_shearAlong (U := ⊤) (U' := ⊤) hν hγd hγν hK (by simp) u
  simp only [Opens.coe_top, Measure.restrict_univ] at hv_val hv_grad
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

/-! ### The local estimate near a curved boundary portion -/

section Local

open Metric InnerProductSpace
open scoped Distributions Gradient

variable {γ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν : EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}

/-- **The flattened local solution.** Let `U ⊆ Ω` be open, `U' = Φ⁻¹(U)` for the shear
`Φ = shearAlong γ ν`, and let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`, tested
against test functions, with `a` bounded on `U` and `G ∈ L²(U)`. Then some `v ∈ H¹(U')` has value
`u ∘ Φ`, gradient `DΦ* (∇u ∘ Φ)`, and solves `-∂ᵢ(a'ⁱʲ ∂ⱼv) = -div G'` weakly in `U'` with the
transformed coefficient `a'` and datum `G'`. -/
private theorem exists_value_gradient_and_energyFormH1_eq_of_shearAlong (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω U U' : Opens E} (hUΩ : U ≤ Ω)
    (hU' : (U' : Set E) = shearAlong γ ν ⁻¹' U) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {M : ℝ} (hM : 0 ≤ M) (ha : AEStronglyMeasurable a (volume.restrict U))
    (hbd : ∀ x ∈ (U : Set E), ‖matrixBilinearForm (a x)‖ ≤ M) {u : W1p volume Ω 2} {G : E → E}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ)
    (hG : MemLp G 2 (volume.restrict U)) :
    ∃ v : W1p volume U' 2,
      (∀ᵐ y ∂volume.restrict U', W1p.value v y = W1p.value u (shearAlong γ ν y)) ∧
      (∀ᵐ y ∂volume.restrict U', W1p.gradient v y =
        (fderiv ℝ (shearAlong γ ν) y).adjoint (W1p.gradient u (shearAlong γ ν y))) ∧
      ∀ φ : 𝓓(U', ℝ), energyFormH1 (pullbackPrincipal (shearAlong γ ν) a) 0 0 v
        (W1p.ofTestFunctionₗ volume U' 2 φ) =
          ∫ y in U', ⟪pullbackDrift (shearAlong γ ν) G y, ∇ (φ : E → ℝ) y⟫_ℝ := by
  have hmp : MeasurePreserving (shearAlong γ ν) (volume.restrict U') (volume.restrict U) :=
    hU' ▸ (measurePreserving_shearAlong volume hγ hγν).restrict_preimage U.isOpen.measurableSet
  -- The restriction of `u` to `U` solves the equation tested against `H¹₀(U)`.
  have hU : ∀ w : W1p0 volume U 2, energyFormH1 a 0 0 (W1p.restrictL hUΩ u) (w : W1p volume U 2) =
      ∫ y in U, ⟪G y, W1p.gradient (w : W1p volume U 2) y⟫_ℝ := fun w => by
    rw [forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner hUΩ
      (memLp_energyIntegrand_zero_zero_of_norm_le hM ha hbd) (f := 0) (fun φ => by simp [hu φ])
      hG MemLp.zero w]
    simp [inner_neg_left, integral_neg]
  obtain ⟨v, hv_val, hv_grad, -, hv_eq⟩ :=
    exists_compL_shearAlong hν hγ hγν hK hU' (W1p.restrictL hUΩ u)
  refine ⟨v, ?_, ?_, fun φ => ?_⟩
  · filter_upwards [hv_val, hmp.quasiMeasurePreserving.ae (W1p.value_restrictL_ae hUΩ u)]
      with y h1 h2
    rw [h1, h2]
  · filter_upwards [hv_grad, hmp.quasiMeasurePreserving.ae (W1p.gradient_restrictL_ae hUΩ u)]
      with y h1 h2
    rw [h1, h2]
  · have h := hv_eq a G hU
      ⟨W1p.ofTestFunctionₗ volume U' 2 φ, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
    simp only [W1p.gradient_ofTestFunctionₗ] at h
    rw [h]
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with y hy
    rw [hy]

/-- **Zero boundary values through the shear.** If `χ u ∈ H¹₀(Ω)` for every smooth `χ` compactly
supported in `B(x₀, ρ)`, and `v` has value `u ∘ Φ` on `U' = Φ⁻¹(Ω ∩ B(x₀, ρ))` for the shear
`Φ = shearAlong γ ν`, then `χ v ∈ H¹₀(U')` for every smooth `χ` compactly supported in the ball of
radius `r` about `Ψ x₀`, for the inverse shear `Ψ = shearAlong (-γ) ν` and `(1 + K) r ≤ ρ / 2`. -/
private theorem exists_w1p0_value_ae_eq_mul_of_shearAlong (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω U' : Opens E} {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hU' : (U' : Set E) = shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ)) {u : W1p volume Ω 2}
    (hu0 : ∀ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ ball x₀ ρ → ∃ w : W1p0 volume Ω 2,
        W1p.value (w : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => χ x * W1p.value u x)
    {v : W1p volume U' 2}
    (hv : ∀ᵐ y ∂volume.restrict U', W1p.value v y = W1p.value u (shearAlong γ ν y))
    {r : ℝ} (hr : (1 + K) * r ≤ ρ / 2) {χ : E → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ ball (shearAlong (-γ) ν x₀) r) :
    ∃ w : W1p0 volume U' 2,
      W1p.value (w : W1p volume U' 2) =ᵐ[volume.restrict U'] fun y => χ y * W1p.value v y := by
  set U : Opens E := Ω ⊓ ⟨ball x₀ ρ, isOpen_ball⟩
  -- `ψ u ∈ H¹₀(Ω)` for a cutoff `ψ` equal to one on `closedBall x₀ (ρ / 2)`, and it restricts to
  -- an element of `H¹₀(U)`, since it vanishes off the compact `tsupport ψ ⊆ B(x₀, ρ)`.
  -- `«E»` names the lemma's type argument, since `E` is a local notation token in this file.
  obtain ⟨c, -, hcut⟩ := exists_forall_contDiff_cutoff_ball («E» := E)
  obtain ⟨ψ, hψ, hψc, -, hψ1, hψs, -⟩ := hcut x₀ (half_pos hρ).le (half_lt_self hρ)
  obtain ⟨w₁, hw₁⟩ := hu0 ψ hψ hψc hψs
  have hw₂ : W1p.restrictL (inf_le_left : U ≤ Ω) (w₁ : W1p volume Ω 2) ∈
      w1p0Submodule volume U 2 :=
    W1p.restrictL_mem_w1p0Submodule_of_isCompact (V := ⟨ball x₀ ρ, isOpen_ball⟩) hψc hψs
      w₁.property (by
        filter_upwards [hw₁] with x hx hxK
        rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul])
  -- Its composition with `Φ` lies in `H¹₀(U')`, and so does the product with `χ`.
  obtain ⟨w₃, hw₃, -, hw₃0, -⟩ := exists_compL_shearAlong hν hγ hγν hK hU'
    (W1p.restrictL (inf_le_left : U ≤ Ω) (w₁ : W1p volume Ω 2))
  obtain ⟨w, hw⟩ := W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hχ hχc (hw₃0 hw₂)
  refine ⟨w, ?_⟩
  -- On `tsupport χ`, `ψ ∘ Φ = 1`, so `χ (ψ u) ∘ Φ = χ (u ∘ Φ)`.
  have hmp : MeasurePreserving (shearAlong γ ν) (volume.restrict U') (volume.restrict U) :=
    hU' ▸ (measurePreserving_shearAlong volume hγ hγν).restrict_preimage U.isOpen.measurableSet
  filter_upwards [hw, hw₃,
    hmp.quasiMeasurePreserving.ae
      (W1p.value_restrictL_ae (inf_le_left : U ≤ Ω) (w₁ : W1p volume Ω 2)),
    hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr inf_le_left) hw₁), hv]
    with y h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  by_cases hy : y ∈ tsupport χ
  · have h := dist_shearAlong_lt hν.le
      (lipschitzWith_of_nnNorm_fderiv_le hγ fun x => by exact_mod_cast hK x) (hχs hy)
    rw [shearAlong_shearAlong_neg hγν] at h
    rw [hψ1 (ball_subset_closedBall (h.trans_le hr)), Pi.one_apply, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]

/-- **Inside a small ball, the flattened region is the half-space.** If `Ω` agrees inside
`B(x₀, ρ)` with the region above the graph of `γ`, and `(1 + K) r ≤ ρ`, then inside the ball of
radius `r` about `Ψ x₀`, for the inverse shear `Ψ = shearAlong (-γ) ν`, the preimage of
`Ω ∩ B(x₀, ρ)` under the shear `Φ = shearAlong γ ν` is the half-space `{0 < ⟪y, ν⟫}`. -/
private theorem preimage_inter_ball_inter_ball_eq (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω : Opens E}
    {x₀ : E} {ρ r : ℝ} (hΩ : ∀ x ∈ ball x₀ ρ, x ∈ Ω ↔ γ x < ⟪x, ν⟫_ℝ) (hr : (1 + K) * r ≤ ρ) :
    shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ) ∩ ball (shearAlong (-γ) ν x₀) r =
      {y | 0 < ⟪y, ν⟫_ℝ} ∩ ball (shearAlong (-γ) ν x₀) r := by
  refine Set.ext fun y => and_congr_left fun hy => ?_
  have hb : shearAlong γ ν y ∈ ball x₀ ρ := by
    have h := dist_shearAlong_lt hν.le
      (lipschitzWith_of_nnNorm_fderiv_le hγ fun x => by exact_mod_cast hK x) hy
    rw [shearAlong_shearAlong_neg hγν] at h
    exact h.trans_le hr
  rw [mem_preimage, mem_inter_iff, and_iff_left hb, SetLike.mem_coe, hΩ _ hb, mem_ofPred_eq,
    ← sub_pos, real_inner_shearAlong_sub hν hγν]

/-- **The flattened image of a smaller ball.** For `r ≤ ρ` and `(1 + K) r ≤ s`, the preimage of
`Ω ∩ B(x₀, r)` under the shear `Φ = shearAlong γ ν` lies in the preimage of `Ω ∩ B(x₀, ρ)` and in
the ball of radius `s` about `Ψ x₀`, for the inverse shear `Ψ = shearAlong (-γ) ν`. -/
private theorem preimage_inter_ball_subset (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω : Opens E}
    {x₀ : E} {ρ r s : ℝ} (hr : r ≤ ρ) (hrs : (1 + K) * r ≤ s) :
    shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ r) ⊆
      shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ) ∩ ball (shearAlong (-γ) ν x₀) s :=
  fun y ⟨hyΩ, hyb⟩ => by
    refine ⟨⟨hyΩ, ball_subset_ball hr hyb⟩, ?_⟩
    have h := dist_shearAlong_lt hν.le (lipschitzWith_of_nnNorm_fderiv_le hγ.neg fun x => by
      rw [fderiv_neg, nnNorm_neg]; exact_mod_cast hK x) hyb
    rw [shearAlong_neg_shearAlong hγν] at h
    exact h.trans_le hrs

/-- **Gradients back through the shear.** If `v ∈ H¹(U')` has gradient `DΦ* (∇u ∘ Φ)` on
`U' = Φ⁻¹(Ω ∩ B(x₀, ρ))`, for the shear `Φ = shearAlong γ ν`, then for `r ≤ ρ` and
`(1 + K) r ≤ s`, `‖∇u‖_{Lᵖ(Ω ∩ B(x₀, r))} ≤ (1 + K) ‖∇v‖_{Lᵖ(U' ∩ B(Ψ x₀, s))}`, for the inverse
shear `Ψ = shearAlong (-γ) ν`. -/
private theorem eLpNorm_gradient_inter_ball_le_of_shearAlong (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x)
    (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω U' : Opens E} {x₀ : E} {ρ r s : ℝ}
    (hU' : (U' : Set E) = shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ)) (hr : r ≤ ρ)
    (hrs : (1 + K) * r ≤ s) {u : W1p volume Ω 2} {v : W1p volume U' 2}
    (hv : ∀ᵐ y ∂volume.restrict U', W1p.gradient v y =
      (fderiv ℝ (shearAlong γ ν) y).adjoint (W1p.gradient u (shearAlong γ ν y))) (q : ℝ≥0∞) :
    eLpNorm (W1p.gradient u) q (volume.restrict ((Ω : Set E) ∩ ball x₀ r)) ≤
      ENNReal.ofReal (1 + K) *
        eLpNorm (W1p.gradient v) q
          (volume.restrict ((U' : Set E) ∩ ball (shearAlong (-γ) ν x₀) s)) :=
  eLpNorm_restrict_le_of_ae_norm_comp_shearAlong_le hγ hγν
    (Ω.isOpen.measurableSet.inter measurableSet_ball)
    (hU' ▸ preimage_inter_ball_subset hν hγ hγν hK hr hrs)
    ((Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl))
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (hv.mono fun _ hy => norm_gradient_comp_shearAlong_le hν hγ hγν hK hy)) q

/-- **The flattened local data.** Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`,
tested against test functions, with `a` bounded on `S = Ω ∩ B(x₀, ρ)` and `u`, `∇u`, `G` in
`Lᵖ(S)`, `p ≥ 2`. For the shear `Φ = shearAlong γ ν` and `t ⊆ U' = Φ⁻¹(S)`, the flattened solution
`v ∈ H¹(U')` of `exists_value_gradient_and_energyFormH1_eq_of_shearAlong` has `v`, `∇v` and the
transformed datum `G'` in `Lᵖ(t)`, and the transformed coefficient `a'` is measurable on `t`, with
`‖G'‖_{Lᵖ(t)} ≤ (1 + K) ‖G‖_{Lᵖ(S)}` and
`‖∇v‖_{L²(t)} ≤ (1 + K) ‖∇u‖_{L²(S)}`. -/
private theorem exists_flattened_of_shearAlong (hν : ‖ν‖ = 1) (hγ : Differentiable ℝ γ)
    (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) (hK : ∀ x, ‖fderiv ℝ γ x‖ ≤ K) {Ω U' : Opens E}
    {x₀ : E} {ρ : ℝ} (hU' : (U' : Set E) = shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ))
    {t : Set E} (ht : t ⊆ U') {p : ℝ≥0∞} (hp : 2 ≤ p)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : AEStronglyMeasurable a (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)))
    (hbd : ∀ x ∈ (Ω : Set E) ∩ ball x₀ ρ, ‖matrixBilinearForm (a x)‖ ≤ M) {u : W1p volume Ω 2}
    {G : E → E} (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ)
    (hvp : MemLp (W1p.value u) p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)))
    (hgp : MemLp (W1p.gradient u) p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)))
    (hGp : MemLp G p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ))) :
    ∃ v : W1p volume U' 2,
      (∀ᵐ y ∂volume.restrict U', W1p.value v y = W1p.value u (shearAlong γ ν y)) ∧
      (∀ᵐ y ∂volume.restrict U', W1p.gradient v y =
        (fderiv ℝ (shearAlong γ ν) y).adjoint (W1p.gradient u (shearAlong γ ν y))) ∧
      (∀ φ : 𝓓(U', ℝ), energyFormH1 (pullbackPrincipal (shearAlong γ ν) a) 0 0 v
        (W1p.ofTestFunctionₗ volume U' 2 φ) =
          ∫ y in U', ⟪pullbackDrift (shearAlong γ ν) G y, ∇ (φ : E → ℝ) y⟫_ℝ) ∧
      AEStronglyMeasurable (pullbackPrincipal (shearAlong γ ν) a) (volume.restrict t) ∧
      MemLp (W1p.value v) p (volume.restrict t) ∧ MemLp (W1p.gradient v) p (volume.restrict t) ∧
      MemLp (pullbackDrift (shearAlong γ ν) G) p (volume.restrict t) ∧
      eLpNorm (pullbackDrift (shearAlong γ ν) G) p (volume.restrict t) ≤
        ENNReal.ofReal (1 + K) * eLpNorm G p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) ∧
      eLpNorm (W1p.gradient v) 2 (volume.restrict t) ≤ ENNReal.ofReal (1 + K) *
        eLpNorm (W1p.gradient u) 2 (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) := by
  set U : Opens E := Ω ⊓ ⟨ball x₀ ρ, isOpen_ball⟩
  have hfin : IsFiniteMeasure (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) :=
    isFiniteMeasure_restrict.2 ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  obtain ⟨v, hv_val, hv_grad, hv_eq⟩ := exists_value_gradient_and_energyFormH1_eq_of_shearAlong hν
    hγ hγν hK (inf_le_left : U ≤ Ω) hU' hM ha hbd hu (hGp.mono_exponent hp)
  have hmp : MeasurePreserving (shearAlong γ ν) (volume.restrict U') (volume.restrict U) :=
    hU' ▸ (measurePreserving_shearAlong volume hγ hγν).restrict_preimage U.isOpen.measurableSet
  have hS : MeasurableSet ((Ω : Set E) ∩ ball x₀ ρ) := U.isOpen.measurableSet
  have hmono : volume.restrict t ≤ volume.restrict U' := Measure.restrict_mono ht le_rfl
  have htS : t ⊆ shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ) := hU' ▸ ht
  -- `‖∇v‖ ≤ (1 + K) ‖∇u ∘ Φ‖`, since `‖DΦ‖ ≤ 1 + K`.
  have hgrad_le : ∀ᵐ y ∂volume.restrict t, ‖W1p.gradient v y‖ ≤
      (1 + K) * ‖W1p.gradient u (shearAlong γ ν y)‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ht hv_grad] with y hy
    rw [hy]
    exact norm_adjoint_fderiv_shearAlong_apply_le hν hγ hK y _
  have hgv := memLp_and_eLpNorm_restrict_le_of_ae_norm_le_comp_shearAlong hγ hγν hS htS
    ((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    ((Lp.aestronglyMeasurable (W1p.gradient v)).mono_measure hmono) hgrad_le
  obtain ⟨hG'p, hG'⟩ := memLp_pullbackDrift_shearAlong_and_eLpNorm_le hν hγ hγν hK
    (Ω := U) (H := U') hU'.symm hmp hGp
  exact ⟨v, hv_val, hv_grad, hv_eq,
    (aestronglyMeasurable_pullbackPrincipal_shearAlong hγ hγν hmp ha).mono_measure hmono,
    (memLp_and_eLpNorm_restrict_le_of_ae_norm_le_comp_shearAlong hγ hγν hS htS hvp
      ((Lp.aestronglyMeasurable (W1p.value v)).mono_measure hmono)
      (ae_restrict_of_ae_restrict_of_subset ht (hv_val.mono fun y hy => by rw [hy, one_mul]))).1,
    (memLp_and_eLpNorm_restrict_le_of_ae_norm_le_comp_shearAlong hγ hγν hS htS hgp
      ((Lp.aestronglyMeasurable (W1p.gradient v)).mono_measure hmono) hgrad_le).1,
    hG'p.mono_measure hmono, (eLpNorm_mono_measure _ hmono).trans hG', hgv.2⟩

/-- The radii of the local estimate near a curved boundary portion: for `R = ρ / (4 (1 + K))` and
`θ = min θ₀ 1 / (4 (1 + K)²)`, the shear by a function with `‖Dγ‖ ≤ K` maps `B(Ψ x₀, 2R)` into
`B(x₀, ρ / 2)`, and its inverse maps `B(x₀, θρ) ⊆ B(x₀, ρ)` into `B(Ψ x₀, θ₀R)`. -/
private theorem radii_of_shearAlong (K : ℝ≥0) (θ₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (1 + (K : ℝ)) * (2 * (ρ / (4 * (1 + K)))) = ρ / 2 ∧
      min θ₀ 1 / (4 * (1 + K) ^ 2) * ρ ≤ ρ ∧
      (1 + K) * (min θ₀ 1 / (4 * (1 + K) ^ 2) * ρ) ≤ θ₀ * (ρ / (4 * (1 + K))) := by
  refine ⟨by field_simp; ring, mul_le_of_le_one_left hρ.le (div_le_one_of_le₀
    ((min_le_right _ _).trans (by nlinarith [K.coe_nonneg])) (by positivity)), ?_⟩
  calc (1 + K) * (min θ₀ 1 / (4 * (1 + K) ^ 2) * ρ) = min θ₀ 1 * (ρ / (4 * (1 + K))) := by
        field_simp
    _ ≤ θ₀ * (ρ / (4 * (1 + K))) := by
        gcongr
        exact min_le_left _ _

/-- The arithmetic combining the flat estimate with the changes of norms under the shear. -/
private theorem le_mul_add_mul_of_le {X Y g g' W V w w' L C₀ c : ℝ≥0∞} (hc : 1 ≤ c)
    (hX : X ≤ L * Y) (hY : Y ≤ C₀ * (g' + W * w')) (hg : g' ≤ L * g) (hW : W ≤ c * V)
    (hw : w' ≤ L * w) : X ≤ L ^ 2 * C₀ * c * (g + V * w) := by
  calc X ≤ L * (C₀ * (c * (L * g) + c * V * (L * w))) := by
        refine hX.trans (mul_le_mul_right (hY.trans (mul_le_mul_right ?_ _)) _)
        gcongr
        exact hg.trans (le_mul_of_one_le_left zero_le hc)
    _ = L ^ 2 * C₀ * c * (g + V * w) := by ring

/-- **The local `W^{1,p}` estimate near a curved boundary portion.** Let `2 < p < ∞`,
`0 < λ ≤ Λ` and `K ≥ 0`. There are constants `C`, `δ > 0` and `θ > 0`, depending only on `n`, `p`,
`λ`, `Λ` and `K`, with the following property. Let `ν` be a unit vector, let `γ` be
differentiable, invariant under translation along `ν`, with `‖Dγ‖ ≤ K`, and let `x₀` lie on its
graph, `γ x₀ = ⟪x₀, ν⟫`. Let `Ω` be open and agree inside `B(x₀, ρ)` with the region
`{γ x < ⟪x, ν⟫}` above the graph, so that inside `B(x₀, ρ)` the boundary of `Ω` is the graph of
`γ`, and let `Dγ` be within `δ` of `Dγ(x₀)` on `B(x₀, ρ)`. Let `A` be a constant matrix, uniformly
elliptic with constants `λ, Λ` and not necessarily symmetric, and let `a` be measurable on
`Ω ∩ B(x₀, ρ)` with bilinear form within `δ` of that of `A`, in operator norm, there. Let
`u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`, tested against test functions, and
vanish on the curved boundary portion: `χ u ∈ H¹₀(Ω)` for every smooth `χ` compactly supported in
`B(x₀, ρ)`. If `u`, `∇u` and `G` lie in `Lᵖ(Ω ∩ B(x₀, ρ))`, then

`‖∇u‖_{Lᵖ(Ω ∩ B(x₀, θρ))} ≤`
`  C (‖G‖_{Lᵖ(Ω ∩ B(x₀, ρ))} + |B(x₀, ρ)|^(1/p - 1/2) ‖∇u‖_{L²(Ω ∩ B(x₀, ρ))})`.

Nothing is assumed about the rest of `∂Ω`, nor about `a` away from `Ω ∩ B(x₀, ρ)`. For a `C¹`
graph and coefficients continuous up to the boundary at `x₀`, `A` can be `a(x₀)` and `ρ` small.
This is the curved counterpart of the estimate near a flat boundary portion
`TauCeti.PDE.exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le`, and the local
counterpart of the estimate up to a graph
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_graph`. -/
theorem exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le_of_graph {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧
      ∀ {Ω : Opens E} {ν x₀ : E} {γ : E → ℝ} {ρ : ℝ}
        {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ‖ν‖ = 1 → Differentiable ℝ γ → (∀ x (t : ℝ), γ (x + t • ν) = γ x) →
        (∀ x, ‖fderiv ℝ γ x‖ ≤ K) → γ x₀ = ⟪x₀, ν⟫_ℝ → 0 < ρ →
        (∀ x ∈ ball x₀ ρ, x ∈ Ω ↔ γ x < ⟪x, ν⟫_ℝ) →
        AEStronglyMeasurable a (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ γ x - fderiv ℝ γ x₀‖ ≤ δ) →
        (∀ x ∈ ball x₀ ρ, x ∈ Ω → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume Ω 2) (G : E → E),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
          (∀ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            tsupport χ ⊆ ball x₀ ρ → ∃ v : W1p0 volume Ω 2,
              W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω]
                fun x => χ x * W1p.value u x) →
          MemLp (W1p.value u) p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) →
          MemLp (W1p.gradient u) p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) →
          MemLp G p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) →
          eLpNorm (W1p.gradient u) p (volume.restrict ((Ω : Set E) ∩ ball x₀ (θ * ρ))) ≤
            C * (eLpNorm G p (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ)) +
              volume (ball x₀ ρ) ^ (p.toReal⁻¹ - 2⁻¹) *
                eLpNorm (W1p.gradient u) 2 (volume.restrict ((Ω : Set E) ∩ ball x₀ ρ))) := by
  obtain ⟨C₀, δ₀, θ₀, hδ₀, hθ₀, hflat⟩ :=
    exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le
    (n := n) hp hp_top (1 * lam / (1 + K) ^ 2)
    ((1 + K) ^ Fintype.card (Fin (n + 1)) * (1 + K) ^ 2 * Lam)
  set D : ℝ := (1 + K) ^ 2 + 2 * |Lam| * (1 + K)
  have hD : 0 < D := by positivity
  refine ⟨(1 + K) ^ 2 * C₀ * (4 * (1 + K)) ^ (n + 1), δ₀ / D, min θ₀ 1 / (4 * (1 + K) ^ 2),
    div_pos hδ₀ hD, by positivity, ?_⟩
  intro Ω ν x₀ γ ρ a A hν hγd hγν hK hx₀ hρ hΩ ha hA hγs has u G hu hu0 hvp hgp hGp
  -- The flat side: `y₀ = Ψ x₀` on the hyperplane `{⟪y, ν⟫ = 0}`, the radius `R = ρ / (4 (1 + K))`,
  -- and `U' = Φ⁻¹(Ω ∩ B(x₀, ρ))`, which is the half-space `H` inside `B(y₀, 2R)`.
  set y₀ := shearAlong (-γ) ν x₀
  set c₄ : ℝ≥0 := 4 * (1 + K)
  set R : ℝ := ρ / c₄
  have hc₄ : (c₄ : ℝ) = 4 * (1 + K) := by simp [c₄]
  have hR : 0 < R := by positivity
  obtain ⟨h2R, hθ1, hθρ⟩ := radii_of_shearAlong K θ₀ hρ
  rw [← hc₄] at h2R hθρ
  set U' : Opens E := ⟨shearAlong γ ν ⁻¹' ((Ω : Set E) ∩ ball x₀ ρ),
    (Ω.isOpen.inter isOpen_ball).preimage (differentiable_shearAlong hγd).continuous⟩
  let H : Opens E := ⟨{y | 0 < ⟪y, ν⟫_ℝ}, isOpen_lt continuous_const (by fun_prop)⟩
  have hU'H : (U' : Set E) ∩ ball y₀ (2 * R) = (H : Set E) ∩ ball y₀ (2 * R) :=
    preimage_inter_ball_inter_ball_eq hν hγd hγν hK hΩ (by linarith)
  -- The flattened solution `v`, with value `u ∘ Φ` and gradient `DΦ* (∇u ∘ Φ)` on `U'`.
  obtain ⟨v, hv_val, hv_grad, hv_eq, ha', hvp', hgp', hG'p, hG', hgv₂⟩ :=
    exists_flattened_of_shearAlong hν hγd hγν hK (U' := U') rfl (t := (U' : Set E) ∩ ball y₀ R)
    inter_subset_left hp.le (by linarith [hA.upper_nonneg, div_pos hδ₀ hD]) ha
    (fun x hx => hA.opNorm_matrixBilinearForm_le_add (mem_univ 0) (has x hx.2 hx.1)) hu hvp hgp hGp
  -- The flat estimate on `B(y₀, R)`, with the constant matrix `A' = DΨ(x₀) A DΨ(x₀)ᵀ`.
  have hmain := hflat (Ω := U') (H := H) (y₀ := y₀) (R := R)
    (A := pullbackPrincipal (shearAlong γ ν) (fun _ => A) (shearAlong (-γ) ν x₀))
    (fun h => by simp [h] at hν) (fun _ => Iff.rfl) (by simp [y₀, real_inner_shearAlong hν, hx₀])
    hR hU'H ha' (uniformlyEllipticOn_pullbackPrincipal_shearAlong_const hν hγd hγν hK hA _)
    (fun y hy hyH => by
      have hy' : y ∈ (U' : Set E) ∩ ball y₀ (2 * R) := by
        rw [hU'H]
        exact ⟨hyH, ball_subset_ball (by linarith) hy⟩
      exact (norm_matrixBilinearForm_pullbackPrincipal_sub_le hν hγd hγν hK
        ((hA.opNorm_matrixBilinearForm_le (mem_univ x₀)).trans (le_abs_self Lam))
        (has _ hy'.1.2 hy'.1.1) (hγs _ hy'.1.2)).trans (div_mul_cancel₀ δ₀ hD.ne').le)
    v (pullbackDrift (shearAlong γ ν) G) hv_eq
    (fun χ hχ hχc hχs => exists_w1p0_value_ae_eq_mul_of_shearAlong hν hγd hγν hK hρ rfl hu0 hv_val
      h2R.le hχ hχc hχs)
    hvp' hgp' hG'p
  -- Back to `Ω`, on `B(x₀, θρ)` with `(1 + K) θρ ≤ θ₀R`.
  have hX := eLpNorm_gradient_inter_ball_le_of_shearAlong hν hγd hγν hK (U' := U') rfl hθ1 hθρ
    hv_grad p
  -- The volume factor of `B(y₀, R)` and the arithmetic.
  have hc₄1 : 1 ≤ c₄ := one_le_mul_of_one_le_of_one_le (by norm_num) le_self_add
  have hW := Measure.addHaar_ball_div_rpow_le volume x₀ y₀ hρ (κ := c₄) (by exact_mod_cast hc₄1)
    (e := p.toReal⁻¹ - 2⁻¹) (by linarith [inv_nonneg.2 (ENNReal.toReal_nonneg (a := p))])
  rw [finrank_euclideanSpace_fin, ENNReal.ofReal_coe_nnreal] at hW
  refine (le_mul_add_mul_of_le (one_le_pow₀ (by exact_mod_cast hc₄1)) hX hmain hG' hW
    hgv₂).trans_eq ?_
  simp [c₄, ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]

end Local

end PDE

end TauCeti
