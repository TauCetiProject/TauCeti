/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Calculus.DifferentialForm.Codifferential
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The exterior derivative, the codifferential and the Hodge Laplacian in an orthonormal frame

Let `V` be an oriented finite-dimensional real inner product space with an orthonormal basis
`(eᵢ)`. For a differential form `ω : V → V [⋀^Fin k]→L[ℝ] ℝ` write `∂ᵢω` for its derivative in
the direction `eᵢ`. This file computes the exterior derivative `extDeriv`, the codifferential
`δ = ± ⋆ d ⋆` of `Orientation.codifferential` and the Hodge Laplacian `δ d + d δ` in this frame:

* `dω = ∑ᵢ eⁱ ∧ ∂ᵢω` (`TauCeti.alternatingFormEquiv_symm_extDeriv`), stated on the elements of
  the exterior powers representing the forms, where wedging with a vector is
  `TauCeti.ExteriorAlgebra.wedgeLeft`. It specializes the frame formula for alternation,
  `TauCeti.alternatingFormEquiv_symm_alternatizeUncurryFin`;
* `δω = -∑ᵢ ι_{eᵢ} ∂ᵢω` (`Orientation.codifferential_eq_neg_sum_curryLeft`), where the interior
  product `ι_u α` is `α.curryLeft u`. Although the codifferential is built from the Hodge star of
  the orientation, it is a first-order operator in contractions alone;
* `δ d ω + d δ ω = -Δω` for forms of class `C²`
  (`Orientation.codifferential_extDeriv_add_extDeriv_codifferential_eq_neg_laplacian`), where
  `Δ = ∑ᵢ ∂ᵢ²` is Mathlib's Laplacian of maps from an inner product space, acting on the form as a
  vector-valued function. In degree zero only `δ d` occurs
  (`Orientation.codifferential_extDeriv_eq_neg_laplacian_zero`) and in the top degree only `d δ`
  (`Orientation.extDeriv_codifferential_eq_neg_laplacian_of_eq_finrank`); these two need only a
  differentiable derivative, not symmetry of second derivatives.

So the Hodge Laplacian of Euclidean space is the nonnegative Laplacian `-∑ᵢ ∂ᵢ²` acting on the
coefficients of a form. The proof expands `δ d + d δ` with the first two formulas and uses the
anticommutation relation `ι_{eⱼ} (eⁱ ∧ α) + eⁱ ∧ ι_{eⱼ} α = ⟪eⱼ, eᵢ⟫ α` of the interior product
and exterior multiplication `TauCeti.wedgeCovector` (`TauCeti.curryLeftFlipL_wedgeCovector_add`),
together with the symmetry of second derivatives.

These are the flat, chart-level frame formulas for the undeformed operators. They have the same
shape as the coordinate operators `∑ᵢ εᵢ ∂ᵢ`, `-∑ᵢ ιᵢ ∂ᵢ` and `-∑ᵢ ∂ᵢ²` of the Witten complex in
`TauCeti.euclideanWittenLaplacian_apply`, which act on coefficient families rather than on forms;
the identification of the two is not proved here.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
-/

public section

noncomputable section

open Module exteriorPower Laplacian
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι]

namespace TauCeti

/-- **The exterior derivative in an orthonormal frame**: `dω = ∑ᵢ eⁱ ∧ ∂ᵢω`, read on the elements
of the exterior powers representing the forms. -/
theorem alternatingFormEquiv_symm_extDeriv (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    (alternatingFormEquiv V (k + 1)).symm (extDeriv ω x) =
      ∑ i, ExteriorAlgebra.wedgeLeft (b i) k
        ((alternatingFormEquiv V k).symm (fderiv ℝ ω x (b i))) :=
  alternatingFormEquiv_symm_alternatizeUncurryFin b (fderiv ℝ ω x)

end TauCeti

namespace Orientation

open TauCeti

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n)) {k l : ℕ}

/-- **The codifferential in an orthonormal frame**: `δω = -∑ᵢ ι_{eᵢ} ∂ᵢω`, where the interior
product `ι_u α` is `α.curryLeft u`. -/
theorem codifferential_eq_neg_sum_curryLeft (b : OrthonormalBasis ι ℝ V)
    (hkl : k + 1 + l = finrank ℝ V) (ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (x : V) :
    o.codifferential hkl ω x = -∑ i, (fderiv ℝ ω x (b i)).curryLeft (b i) := by
  have hlk : l + 1 + k = finrank ℝ V := by omega
  have hn : finrank ℝ V = n := Fact.out
  -- The derivative of `⋆ω` is the star of the derivative of `ω`.
  have hstar : fderiv ℝ (fun y ↦ o.formHodgeStar hkl (ω y)) x =
      ((o.formHodgeStar hkl).toContinuousLinearEquiv : _ →L[ℝ] _).comp (fderiv ℝ ω x) :=
    (o.formHodgeStar hkl).toContinuousLinearEquiv.comp_fderiv
  -- Each `⋆ (eᵢ ∧ ⋆ aᵢ)` is the contraction `ι_{eᵢ} aᵢ` up to the sign `(-1) ^ (n k)`.
  have hι (i : ι) : o.hodgeStar hlk (ExteriorAlgebra.wedgeLeft (b i) l
      (o.hodgeStar hkl ((alternatingFormEquiv V (k + 1)).symm (fderiv ℝ ω x (b i))))) =
      (-1 : ℝ) ^ (n * k) • (alternatingFormEquiv V k).symm
        ((fderiv ℝ ω x (b i)).curryLeft (b i)) := by
    set a := (alternatingFormEquiv V (k + 1)).symm (fderiv ℝ ω x (b i))
    have ha : fderiv ℝ ω x (b i) = alternatingFormEquiv V (k + 1) a := by simp [a]
    rw [ha, ← alternatingFormEquiv_koszulDifferential, LinearEquiv.symm_apply_apply,
      o.koszulDifferential_eq_smul_hodgeStar_wedgeLeft_hodgeStar (b i) hkl hlk, smul_smul, hn,
      ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]
  have hsign : (-1 : ℝ) ^ (n * (k + 2) + 1) * (-1) ^ (n * k) = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨n * (k + 1), by ring⟩
  rw [codifferential_apply o hkl hlk,
    ← LinearEquiv.apply_symm_apply (alternatingFormEquiv V (l + 1)) (extDeriv _ x),
    alternatingFormEquiv_symm_extDeriv b, hstar, formHodgeStar_alternatingFormEquiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv',
    alternatingFormEquiv_symm_formHodgeStar, map_sum, hι, map_smul, LinearEquiv.apply_symm_apply,
    ← Finset.smul_sum, smul_smul, hsign]
  module

/-! ### The Hodge Laplacian -/

section HodgeLaplacian

open ContinuousAlternatingMap (curryLeftFlipL curryLeftFlipL_apply_apply)

/-- The exterior derivative in an orthonormal frame, as a sum of exterior multiplications. -/
private theorem extDeriv_eq_sum_wedgeCovector (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    extDeriv ω x = ∑ i, wedgeCovector (b i) k (fderiv ℝ ω x (b i)) := by
  rw [← LinearEquiv.apply_symm_apply (alternatingFormEquiv V (k + 1)) (extDeriv ω x),
    alternatingFormEquiv_symm_extDeriv b, map_sum]
  simp only [wedgeCovector_apply]

/-- The derivative of `y ↦ ∑ᵢ Lᵢ (∂ᵢ ω y)` for fixed linear maps `Lᵢ`, when the derivative of
`ω` is differentiable. -/
private theorem fderiv_sum_comp_fderiv_apply {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : ι → F →L[ℝ] G) (b : ι → E) {ω : E → F} {x : E}
    (hω : DifferentiableAt ℝ (fderiv ℝ ω) x) (w : E) :
    fderiv ℝ (fun y ↦ ∑ i, L i (fderiv ℝ ω y (b i))) x w =
      ∑ i, L i (fderiv ℝ (fderiv ℝ ω) x w (b i)) := by
  have h (i : ι) : HasFDerivAt (fun y ↦ L i (fderiv ℝ ω y (b i)))
      ((L i).comp ((ContinuousLinearMap.apply ℝ F (b i)).comp (fderiv ℝ (fderiv ℝ ω) x))) x :=
    (L i).hasFDerivAt.comp x
      ((ContinuousLinearMap.apply ℝ F (b i)).hasFDerivAt.comp x hω.hasFDerivAt)
  rw [(HasFDerivAt.fun_sum fun i _ ↦ h i).fderiv]
  simp

variable {x : V}

/-- `δ d ω` in an orthonormal frame: `δ d ω = -∑ⱼ ∑ᵢ ι_{eⱼ} (eⁱ ∧ ∂ⱼ∂ᵢω)`. -/
private theorem codifferential_extDeriv_eq_neg_sum (b : OrthonormalBasis ι ℝ V)
    (hkl : k + 1 + l = finrank ℝ V) {ω : V → V [⋀^Fin k]→L[ℝ] ℝ}
    (hω : DifferentiableAt ℝ (fderiv ℝ ω) x) :
    o.codifferential hkl (extDeriv ω) x = -∑ j, ∑ i, curryLeftFlipL (n := k) (b j)
      (wedgeCovector (b i) k (fderiv ℝ (fderiv ℝ ω) x (b j) (b i))) := by
  rw [o.codifferential_eq_neg_sum_curryLeft b, funext (extDeriv_eq_sum_wedgeCovector b ω)]
  simp only [fderiv_sum_comp_fderiv_apply (fun i ↦ wedgeCovector (b i) k) b hω,
    ← curryLeftFlipL_apply_apply, map_sum]

/-- `d δ ω` in an orthonormal frame: `d δ ω = -∑ᵢ ∑ⱼ eⁱ ∧ ι_{eⱼ} ∂ᵢ∂ⱼω`. -/
private theorem extDeriv_codifferential_eq_neg_sum (b : OrthonormalBasis ι ℝ V)
    (hkl : k + 1 + l = finrank ℝ V) {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ}
    (hω : DifferentiableAt ℝ (fderiv ℝ ω) x) :
    extDeriv (o.codifferential hkl ω) x = -∑ i, ∑ j, wedgeCovector (b i) k
      (curryLeftFlipL (n := k) (b j) (fderiv ℝ (fderiv ℝ ω) x (b i) (b j))) := by
  have hδ : o.codifferential hkl ω =
      fun y ↦ ∑ i, (-curryLeftFlipL (n := k) (b i)) (fderiv ℝ ω y (b i)) := by
    funext y
    simp [o.codifferential_eq_neg_sum_curryLeft b, curryLeftFlipL_apply_apply]
  rw [extDeriv_eq_sum_wedgeCovector b, hδ]
  simp only [fderiv_sum_comp_fderiv_apply (fun j ↦ -curryLeftFlipL (n := k) (b j)) b hω]
  simp only [neg_apply, map_neg, map_sum, Finset.sum_neg_distrib]

/-- **The Hodge Laplacian of Euclidean space**: for a `(k + 1)`-form `ω` of class `C²` at `x`,
in an intermediate degree `0 < k + 1 < n`, `δ d ω + d δ ω = -Δω` at `x`, where `Δ = ∑ᵢ ∂ᵢ²` is the
Laplacian of `ω` as a vector-valued function. -/
theorem codifferential_extDeriv_add_extDeriv_codifferential_eq_neg_laplacian {l' : ℕ}
    (hkl : k + 1 + l = finrank ℝ V) (hkl' : k + 1 + 1 + l' = finrank ℝ V)
    {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : ContDiffAt ℝ 2 ω x) :
    o.codifferential hkl' (extDeriv ω) x + extDeriv (o.codifferential hkl ω) x = -Δ ω x := by
  set b := stdOrthonormalBasis ℝ V
  have hω' : DifferentiableAt ℝ (fderiv ℝ ω) x :=
    (hω.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hS : ∀ v w, fderiv ℝ (fderiv ℝ ω) x v w = fderiv ℝ (fderiv ℝ ω) x w v :=
    hω.isSymmSndFDerivAt (by simp)
  rw [o.codifferential_extDeriv_eq_neg_sum b hkl' hω',
    o.extDeriv_codifferential_eq_neg_sum b hkl hω', laplacian_eq_sum_fderiv_fderiv b,
    Finset.sum_comm, ← neg_add, ← Finset.sum_add_distrib]
  -- By symmetry of second derivatives and the anticommutation relation, the `i`-th summand is
  -- `∑ⱼ ⟪eⱼ, eᵢ⟫ ∂ᵢ∂ⱼω = ∂ᵢ²ω`.
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ ↦ by
    rw [hS (b j) (b i), curryLeftFlipL_wedgeCovector_add]]
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- **The Laplacian of Euclidean space on functions**: for a `0`-form `ω` whose derivative is
differentiable at `x`, `δ d ω = -Δω` at `x`. -/
theorem codifferential_extDeriv_eq_neg_laplacian_zero (hkl : 0 + 1 + l = finrank ℝ V)
    {ω : V → V [⋀^Fin 0]→L[ℝ] ℝ} (hω : DifferentiableAt ℝ (fderiv ℝ ω) x) :
    o.codifferential hkl (extDeriv ω) x = -Δ ω x := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.codifferential_extDeriv_eq_neg_sum b hkl hω, laplacian_eq_sum_fderiv_fderiv b]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun i _ ↦ curryLeftFlipL_wedgeCovector_zero (b j) (b i) _]
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- **The Hodge Laplacian of Euclidean space in the top degree**: for a form `ω` of degree
`k + 1 = n` whose derivative is differentiable at `x`, `d δ ω = -Δω` at `x`. -/
theorem extDeriv_codifferential_eq_neg_laplacian_of_eq_finrank (hkl : k + 1 + 0 = finrank ℝ V)
    {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : DifferentiableAt ℝ (fderiv ℝ ω) x) :
    extDeriv (o.codifferential hkl ω) x = -Δ ω x := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.extDeriv_codifferential_eq_neg_sum b hkl hω, laplacian_eq_sum_fderiv_fderiv b]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_congr rfl fun j _ ↦ wedgeCovector_curryLeftFlipL_of_eq_finrank (b j) (b i) hkl _]
  simp [orthonormal_iff_ite.mp b.orthonormal]

end HodgeLaplacian

end Orientation
