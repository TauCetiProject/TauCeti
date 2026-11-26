/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Calculus.DifferentialForm.Codifferential
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction

/-!
# The exterior derivative, the codifferential and the Hodge Laplacian in an orthonormal frame

Let `V` be an oriented finite-dimensional real inner product space with an orthonormal basis
`(eᵢ)`. For a differential form `ω : V → V [⋀^Fin k]→L[ℝ] ℝ` write `∂ᵢω` for its derivative in
the direction `eᵢ`. This file computes the exterior derivative `extDeriv`, the codifferential
`δ = ± ⋆ d ⋆` of `Orientation.codifferential` and the Hodge Laplacian `δ d + d δ` in this frame:

* `dω = ∑ᵢ eⁱ ∧ ∂ᵢω` (`TauCeti.alternatingFormEquiv_symm_extDeriv`), stated on the elements of
  the exterior powers representing the forms, where wedging with a vector is
  `TauCeti.ExteriorAlgebra.wedgeLeft`;
* `δω = -∑ᵢ ι_{eᵢ} ∂ᵢω` (`Orientation.codifferential_eq_neg_sum_curryLeft`), where the interior
  product `ι_u α` is `α.curryLeft u`. Although the codifferential is built from the Hodge star of
  the orientation, it is a first-order operator in contractions alone;
* `δ d ω + d δ ω = -Δω` for forms of class `C²`
  (`Orientation.codifferential_extDeriv_add_extDeriv_codifferential_eq_neg_laplacian`), where
  `Δ = ∑ᵢ ∂ᵢ²` is Mathlib's Laplacian of maps from an inner product space, acting on the form as a
  vector-valued function. In degree zero only `δ d` occurs
  (`Orientation.codifferential_extDeriv_eq_neg_laplacian`) and in the top degree only `d δ`
  (`Orientation.extDeriv_codifferential_eq_neg_laplacian`).

So the Hodge Laplacian of Euclidean space is the nonnegative Laplacian `-∑ᵢ ∂ᵢ²` acting on the
coefficients of a form. The proof expands `δ d + d δ` with the first two formulas and uses the
anticommutation relation `ι_{eⱼ} (eⁱ ∧ α) + eⁱ ∧ ι_{eⱼ} α = ⟪eⱼ, eᵢ⟫ α` of the Koszul complex
(`TauCeti.wedgeLeft_comp_koszulDifferential_add`), together with the symmetry of second
derivatives.

These are the flat, chart-level frame formulas behind the Bochner–Weitzenböck formula and behind
Witten's computation of the deformed Laplacian in an orthonormal frame, whose coordinate version is
`TauCeti.euclideanWittenLaplacian_apply`: they identify the operators built from the Hodge star
with the coordinate operators `∑ᵢ εᵢ ∂ᵢ`, `-∑ᵢ ιᵢ ∂ᵢ` and `-∑ᵢ ∂ᵢ²`.

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

/-- **Alternation in an orthonormal frame**: the alternation `f ↦ ∑ⱼ (-1)ʲ f(vⱼ)(v̂ⱼ)` of a
linear map `f` from `V` to `k`-forms is `∑ᵢ eⁱ ∧ f(eᵢ)`, read on the elements of the exterior
powers representing the forms. -/
theorem alternatingFormEquiv_symm_alternatizeUncurryFin (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (f : V →L[ℝ] V [⋀^Fin k]→L[ℝ] ℝ) :
    (alternatingFormEquiv V (k + 1)).symm (ContinuousAlternatingMap.alternatizeUncurryFin f) =
      ∑ i, ExteriorAlgebra.wedgeLeft (b i) k ((alternatingFormEquiv V k).symm (f (b i))) := by
  rw [LinearEquiv.symm_apply_eq]
  ext v
  -- Each summand pairs `eᵢ ∧ aᵢ` with `v₀ ∧ ⋯ ∧ vₖ`, which contracts `⟪eᵢ, ·⟫` into one `vⱼ`.
  have h (i : ι) : alternatingFormEquiv V (k + 1)
      (ExteriorAlgebra.wedgeLeft (b i) k ((alternatingFormEquiv V k).symm (f (b i)))) v =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * (⟪b i, v j⟫ * f (b i) (j.removeNth v)) := by
    rw [alternatingFormEquiv_apply, inner_wedgeLeft_eq_inner_koszulDifferential,
      koszulDifferential_ιMulti, inner_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_right, ← alternatingFormEquiv_apply, LinearEquiv.apply_symm_apply,
      innerₗ_apply_apply]
    ring
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, map_sum,
    ContinuousAlternatingMap.sum_apply, Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- Summing over the frame reassembles `vⱼ = ∑ᵢ ⟪eᵢ, vⱼ⟫ eᵢ`.
  conv_lhs => rw [← b.sum_repr' (v j)]
  simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Finset.mul_sum]

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
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  have hsign : (-1 : ℝ) ^ (n * (k + 2) + 1) * (-1) ^ (n * k) = -1 := by
    rw [← pow_add, show n * (k + 2) + 1 + n * k = 2 * (n * k + n) + 1 by ring, pow_succ, pow_mul,
      neg_one_sq, one_pow, one_mul]
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

/-- Exterior multiplication `α ↦ ⟪u, ·⟫ ∧ α` of forms, through the exterior powers. -/
private def wedgeCovector (u : V) (k : ℕ) :
    (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((alternatingFormEquiv V (k + 1)).toLinearMap ∘ₗ
    ExteriorAlgebra.wedgeLeft u k ∘ₗ (alternatingFormEquiv V k).symm.toLinearMap)

private theorem wedgeCovector_apply (u : V) (k : ℕ) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeCovector u k α = alternatingFormEquiv V (k + 1)
      (ExteriorAlgebra.wedgeLeft u k ((alternatingFormEquiv V k).symm α)) :=
  (rfl)

/-- The interior product of the form of `x` is the form of the contraction of `x`. -/
private theorem curryLeftFlipL_alternatingFormEquiv (u : V) (k : ℕ) (x : ⋀[ℝ]^(k + 1) V) :
    curryLeftFlipL (n := k) u (alternatingFormEquiv V (k + 1) x) =
      alternatingFormEquiv V k (koszulDifferential (innerₗ V u) k x) := by
  rw [curryLeftFlipL_apply_apply, alternatingFormEquiv_koszulDifferential]

/-- **The anticommutation relation** `ι_u (⟪w, ·⟫ ∧ α) + ⟪w, ·⟫ ∧ ι_u α = ⟪u, w⟫ α` on forms of
positive degree. -/
private theorem curryLeftFlipL_wedgeCovector_add (u w : V) (k : ℕ) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    curryLeftFlipL (n := k + 1) u (wedgeCovector w (k + 1) α) +
      wedgeCovector w k (curryLeftFlipL (n := k) u α) = ⟪u, w⟫ • α := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V (k + 1)).surjective α
  have h := LinearMap.congr_fun (wedgeLeft_comp_koszulDifferential_add (innerₗ V u) w k) a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    innerₗ_apply_apply] at h
  rw [wedgeCovector_apply, LinearEquiv.symm_apply_apply, curryLeftFlipL_alternatingFormEquiv,
    curryLeftFlipL_alternatingFormEquiv, wedgeCovector_apply, LinearEquiv.symm_apply_apply,
    ← map_add, ← map_smul]
  exact congrArg _ ((add_comm _ _).trans h)

/-- The anticommutation relation on functions: `ι_u (⟪w, ·⟫ ∧ α) = ⟪u, w⟫ α` for `0`-forms. -/
private theorem curryLeftFlipL_wedgeCovector_zero (u w : V) (α : V [⋀^Fin 0]→L[ℝ] ℝ) :
    curryLeftFlipL (n := 0) u (wedgeCovector w 0 α) = ⟪u, w⟫ • α := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V 0).surjective α
  have h := LinearMap.congr_fun (koszulDifferential_comp_wedgeLeft_zero (innerₗ V u) w) a
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    innerₗ_apply_apply] at h
  rw [wedgeCovector_apply, LinearEquiv.symm_apply_apply, curryLeftFlipL_alternatingFormEquiv, h,
    map_smul]

/-- The anticommutation relation on top-degree forms: `⟪w, ·⟫ ∧ ι_u α = ⟪u, w⟫ α`, since there
are no nonzero forms of degree above the dimension. -/
private theorem wedgeCovector_curryLeftFlipL_of_eq_finrank (u w : V) {k : ℕ}
    (hk : k + 1 = finrank ℝ V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    wedgeCovector w k (curryLeftFlipL (n := k) u α) = ⟪u, w⟫ • α := by
  have h0 : wedgeCovector w (k + 1) α = 0 := by
    ext v
    refine (wedgeCovector w (k + 1) α).toAlternatingMap.map_linearDependent v fun hv ↦ ?_
    have := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  rw [← curryLeftFlipL_wedgeCovector_add, h0, map_zero, zero_add]

/-- The exterior derivative in an orthonormal frame, as a sum of exterior multiplications. -/
private theorem extDeriv_eq_sum_wedgeCovector (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    extDeriv ω x = ∑ i, wedgeCovector (b i) k (fderiv ℝ ω x (b i)) := by
  rw [← LinearEquiv.apply_symm_apply (alternatingFormEquiv V (k + 1)) (extDeriv ω x),
    alternatingFormEquiv_symm_extDeriv b, map_sum]
  rfl

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

/-- The Laplacian in an orthonormal frame, through the second derivative. -/
private theorem laplacian_eq_sum (b : OrthonormalBasis ι ℝ V) {k : ℕ}
    (ω : V → V [⋀^Fin k]→L[ℝ] ℝ) (x : V) :
    Δ ω x = ∑ i, fderiv ℝ (fderiv ℝ ω) x (b i) (b i) := by
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ω b,
    iteratedFDeriv_two_apply]

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
    o.extDeriv_codifferential_eq_neg_sum b hkl hω', laplacian_eq_sum b, Finset.sum_comm, ← neg_add,
    ← Finset.sum_add_distrib]
  -- By symmetry of second derivatives and the anticommutation relation, the `i`-th summand is
  -- `∑ⱼ ⟪eⱼ, eᵢ⟫ ∂ᵢ∂ⱼω = ∂ᵢ²ω`.
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ ↦ by
    rw [hS (b j) (b i), curryLeftFlipL_wedgeCovector_add]]
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- **The Laplacian of Euclidean space on functions**: for a `0`-form `ω` of class `C²` at `x`,
`δ d ω = -Δω` at `x`. -/
theorem codifferential_extDeriv_eq_neg_laplacian (hkl : 0 + 1 + l = finrank ℝ V)
    {ω : V → V [⋀^Fin 0]→L[ℝ] ℝ} (hω : ContDiffAt ℝ 2 ω x) :
    o.codifferential hkl (extDeriv ω) x = -Δ ω x := by
  set b := stdOrthonormalBasis ℝ V
  have hω' : DifferentiableAt ℝ (fderiv ℝ ω) x :=
    (hω.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [o.codifferential_extDeriv_eq_neg_sum b hkl hω', laplacian_eq_sum b]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun i _ ↦ curryLeftFlipL_wedgeCovector_zero (b j) (b i) _]
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- **The Hodge Laplacian of Euclidean space in the top degree**: for a form `ω` of degree
`k + 1 = n` of class `C²` at `x`, `d δ ω = -Δω` at `x`. -/
theorem extDeriv_codifferential_eq_neg_laplacian (hkl : k + 1 + 0 = finrank ℝ V)
    {ω : V → V [⋀^Fin (k + 1)]→L[ℝ] ℝ} (hω : ContDiffAt ℝ 2 ω x) :
    extDeriv (o.codifferential hkl ω) x = -Δ ω x := by
  set b := stdOrthonormalBasis ℝ V
  have hω' : DifferentiableAt ℝ (fderiv ℝ ω) x :=
    (hω.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [o.extDeriv_codifferential_eq_neg_sum b hkl hω', laplacian_eq_sum b]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_congr rfl fun j _ ↦ wedgeCovector_curryLeftFlipL_of_eq_finrank (b j) (b i) hkl _]
  simp [orthonormal_iff_ite.mp b.orthonormal]

end HodgeLaplacian

end Orientation
