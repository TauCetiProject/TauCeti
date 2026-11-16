/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Comp
public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Complex orientations and the determinant line of a composition

For complex-linear maps `f : M → N` and `g : N → P` with finite-dimensional kernels and
cokernels, the real determinant lines of `f`, `g` and `g ∘ f` carry complex orientations
(`LinearMap.IsComplexPositiveDetLine`), and the composition law
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) identifies the first with the tensor
product of the other two. This file shows that the composition law respects these orientations:
it sends a complex positive element of `det (g ∘ f)` to the tensor product of complex positive
elements of `det f` and `det g`
(`LinearMap.IsComplexPositiveDetLine.exists_detLineCompEquiv_eq_tmul`). No sign corrections
enter, because complex vector spaces have even real dimension.

The composition law is the six-term isomorphism `TauCeti.detLineSixTermEquiv` of the exact
sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`, whose terms
are formed from the underlying real-linear maps. The general statement is therefore about
six-term exact sequences of real vector spaces isomorphic to the real restriction of an exact
sequence of complex vector spaces and complex-linear maps
(`TauCeti.exists_detLineSixTermEquiv_congr_eq_tmul`), the six-term counterpart of
`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr`. For the composition, the
isomorphisms are those between the real and complex kernels and cokernels
(`LinearMap.kerRestrictScalarsEquiv`, `LinearMap.cokerRestrictScalarsEquiv`).

Orientations of determinant lines of complex-linear Fredholm operators are oriented this way
when an operator is composed with another complex-linear operator. For instance, a complex-linear
operator `D` cut down by complex-linear incidence conditions `ev` is the composite of
`D.prod ev` with the projection onto the target of `D`, so the complex orientations of
`det (D.prod ev)` and of the determinant line of the projection give that of `det D`.

## Main results

* `TauCeti.exists_detLineSixTermEquiv_congr_eq_tmul`: six-term exact sequences of complex vector
  spaces respect complex orientations.
* `LinearMap.IsComplexPositiveDetLine.exists_detLineCompEquiv_eq_tmul`: the composition law of
  determinant lines respects complex orientations.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences, and
  the canonical orientation of the determinant line of a complex-linear Fredholm operator).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable {E F E' F' : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F'] [Module ℝ F']

/-- Transported along real isomorphisms `e : E ≃ E'` and `e' : F ≃ F'` intertwining a
complex-linear `f` with a real-linear `g`, the range of `g` has real dimension twice the complex
dimension of the range of `f`. -/
private theorem finrank_range_eq_two_mul {f : E →ₗ[ℂ] F} {g : E' →ₗ[ℝ] F'} (e : E ≃ₗ[ℝ] E')
    (e' : F ≃ₗ[ℝ] F') (h : g ∘ₗ e.toLinearMap = e'.toLinearMap ∘ₗ f.restrictScalars ℝ) :
    finrank ℝ (LinearMap.range g) = 2 * finrank ℂ (LinearMap.range f) := by
  have hr : LinearMap.range g = (LinearMap.range (f.restrictScalars ℝ)).map e'.toLinearMap := by
    rw [← LinearMap.range_comp, ← h, LinearMap.range_comp_of_range_eq_top _ e.range]
  rw [hr, LinearEquiv.finrank_map_eq, LinearMap.range_restrictScalars]
  exact finrank_real_eq_two_mul_finrank_complex (V := (LinearMap.range f).restrictScalars ℝ)

/-- A real vector space isomorphic to a complex vector space with a complex basis of size `k` has
real dimension `2 k`. -/
private theorem finrank_eq_two_mul_of_basis (e : E ≃ₗ[ℝ] E') {k : ℕ} (c : Basis (Fin k) ℂ E) :
    finrank ℝ E' = 2 * k := by
  rw [← e.finrank_eq, finrank_real_eq_two_mul_finrank_complex, finrank_eq_card_basis c,
    Fintype.card_fin]

/-- The exterior product of the image under `g` of `e ∘ u`, followed by `e' ∘ v`, is carried by
`e'⁻¹` to a complex positive element when `(f ∘ u, v)` is a complex basis, for real isomorphisms
`e` and `e'` intertwining the complex-linear `f` with the real-linear `g`. This is a complex
positive element of the determinant line of the middle term of an exact sequence, transported
from a complex sequence to an isomorphic real one. -/
private theorem isComplexPositive_detLineCongr_symm_ιMulti_append {m n a b : ℕ}
    {f : E →ₗ[ℂ] F} {g : E' →ₗ[ℝ] F'} (e : E ≃ₗ[ℝ] E') (e' : F ≃ₗ[ℝ] F')
    (h : g ∘ₗ e.toLinearMap = e'.toLinearMap ∘ₗ f.restrictScalars ℝ) {u : Fin m → E}
    {v : Fin n → F} (bF : Basis (Fin (m + n)) ℂ F) (hbF : ⇑bF = Fin.append (f ∘ u) v)
    (ha : a = 2 * m) (hb : b = 2 * n) (hab : finrank ℝ F' = a + b) :
    IsComplexPositive (e'.symm.detLineCongr (exteriorPower.ιMulti ℝ _
      (Fin.append (g ∘ e ∘ complexToRealFamily u ∘ Fin.cast ha)
        (e' ∘ complexToRealFamily v ∘ Fin.cast hb) ∘ Fin.cast hab))) := by
  have hp (z : E) : g (e z) = e' (f z) := LinearMap.congr_fun h z
  refine isComplexPositive_of_coe_eq_smul_ιMulti_append f bF hbF ha hb one_pos ?_
  rw [one_smul, LinearEquiv.coe_detLineCongr, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_comp_cast, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [hp]

/-- The exterior product of `e ∘ u` is carried by `e⁻¹` to a complex positive element when the
complex-linear image `f ∘ u` is a complex basis, for real isomorphisms `e` and `e'` intertwining
`f` with `g`. This is the case of `isComplexPositive_detLineCongr_symm_ιMulti_append` with an
empty first family, written without it. -/
private theorem isComplexPositive_detLineCongr_symm_ιMulti_comp {n : ℕ} {f : E →ₗ[ℂ] F}
    {g : E' →ₗ[ℝ] F'} (e : E ≃ₗ[ℝ] E') (e' : F ≃ₗ[ℝ] F')
    (h : g ∘ₗ e.toLinearMap = e'.toLinearMap ∘ₗ f.restrictScalars ℝ) {u : Fin n → E}
    (b : Basis (Fin n) ℂ F) (hu : f ∘ u = b) (hn : finrank ℝ F' = 2 * n) :
    IsComplexPositive (e'.symm.detLineCongr (exteriorPower.ιMulti ℝ _
      (g ∘ e ∘ complexToRealFamily u ∘ Fin.cast hn))) := by
  have hp (z : E) : g (e z) = e' (f z) := LinearMap.congr_fun h z
  have hF : finrank ℝ F = 2 * n := e'.finrank_eq.trans hn
  convert isComplexPositive_ιMulti_comp_complexToRealFamily f b hu hF using 1
  rw [LinearEquiv.detLineCongr_ιMulti]
  congr 1
  funext i
  simp [hp]

section SixTerm

variable {A₁ A₂ A₃ A₄ A₅ A₆ : Type*}
  [AddCommGroup A₁] [Module ℂ A₁] [Module ℝ A₁] [IsScalarTower ℝ ℂ A₁]
  [AddCommGroup A₂] [Module ℂ A₂] [Module ℝ A₂] [IsScalarTower ℝ ℂ A₂]
  [AddCommGroup A₃] [Module ℂ A₃] [Module ℝ A₃] [IsScalarTower ℝ ℂ A₃]
  [AddCommGroup A₄] [Module ℂ A₄] [Module ℝ A₄] [IsScalarTower ℝ ℂ A₄]
  [AddCommGroup A₅] [Module ℂ A₅] [Module ℝ A₅] [IsScalarTower ℝ ℂ A₅]
  [AddCommGroup A₆] [Module ℂ A₆] [Module ℝ A₆] [IsScalarTower ℝ ℂ A₆]
  {f₁ : A₁ →ₗ[ℂ] A₂} {f₂ : A₂ →ₗ[ℂ] A₃} {f₃ : A₃ →ₗ[ℂ] A₄} {f₄ : A₄ →ₗ[ℂ] A₅}
  {f₅ : A₅ →ₗ[ℂ] A₆}
  {B₁ B₂ B₃ B₄ B₅ B₆ : Type*} [AddCommGroup B₁] [Module ℝ B₁] [AddCommGroup B₂] [Module ℝ B₂]
  [AddCommGroup B₃] [Module ℝ B₃] [AddCommGroup B₄] [Module ℝ B₄] [AddCommGroup B₅]
  [Module ℝ B₅] [AddCommGroup B₆] [Module ℝ B₆]
  [FiniteDimensional ℝ B₁] [FiniteDimensional ℝ B₃] [FiniteDimensional ℝ B₅]
  {g₁ : B₁ →ₗ[ℝ] B₂} {g₂ : B₂ →ₗ[ℝ] B₃} {g₃ : B₃ →ₗ[ℝ] B₄} {g₄ : B₄ →ₗ[ℝ] B₅}
  {g₅ : B₅ →ₗ[ℝ] B₆}

/-- **Six-term exact sequences isomorphic to complex ones respect complex orientations.** Let
`0 → B₁ → B₂ → B₃ → B₄ → B₅ → B₆ → 0` be an exact sequence of real vector spaces, isomorphic
through real isomorphisms `eᵢ : Aᵢ ≃ Bᵢ` to the real restriction of an exact sequence
`0 → A₁ → ⋯ → A₆ → 0` of complex vector spaces and complex-linear maps. Then the identification
`det B₂ ⊗ (det B₅)^* ≃ (det B₁ ⊗ (det B₄)^*) ⊗ (det B₃ ⊗ (det B₆)^*)`
(`TauCeti.detLineSixTermEquiv`) sends the transport of a complex positive element of
`det A₂ ⊗ (det A₅)^*` to the tensor product of the transports of complex positive elements of
`det A₁ ⊗ (det A₄)^*` and of `det A₃ ⊗ (det A₆)^*`. With all `eᵢ` the identity, this says that
`TauCeti.detLineSixTermEquiv` respects complex orientations for exact sequences of complex vector
spaces. -/
theorem exists_detLineSixTermEquiv_congr_eq_tmul (hg₁ : Function.Injective g₁)
    (hg₁₂ : Function.Exact g₁ g₂) (hg₂₃ : Function.Exact g₂ g₃) (hg₃₄ : Function.Exact g₃ g₄)
    (hg₄₅ : Function.Exact g₄ g₅) (hg₅ : Function.Surjective g₅) (e₁ : A₁ ≃ₗ[ℝ] B₁)
    (e₂ : A₂ ≃ₗ[ℝ] B₂) (e₃ : A₃ ≃ₗ[ℝ] B₃) (e₄ : A₄ ≃ₗ[ℝ] B₄) (e₅ : A₅ ≃ₗ[ℝ] B₅)
    (e₆ : A₆ ≃ₗ[ℝ] B₆) (he₁ : g₁ ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f₁.restrictScalars ℝ)
    (he₂ : g₂ ∘ₗ e₂.toLinearMap = e₃.toLinearMap ∘ₗ f₂.restrictScalars ℝ)
    (he₃ : g₃ ∘ₗ e₃.toLinearMap = e₄.toLinearMap ∘ₗ f₃.restrictScalars ℝ)
    (he₄ : g₄ ∘ₗ e₄.toLinearMap = e₅.toLinearMap ∘ₗ f₄.restrictScalars ℝ)
    (he₅ : g₅ ∘ₗ e₅.toLinearMap = e₆.toLinearMap ∘ₗ f₅.restrictScalars ℝ)
    {t : detLine ℝ A₂ ⊗[ℝ] Dual ℝ (detLine ℝ A₅)} (ht : IsComplexPositiveTMulDual t) :
    ∃ s₁ s₂, IsComplexPositiveTMulDual s₁ ∧ IsComplexPositiveTMulDual s₂ ∧
      detLineSixTermEquiv hg₁ hg₁₂ hg₂₃ hg₃₄ hg₄₅ hg₅
          (TensorProduct.congr e₂.detLineCongr e₅.detLineCongr.symm.dualMap t) =
        TensorProduct.congr e₁.detLineCongr e₄.detLineCongr.symm.dualMap s₁ ⊗ₜ
          TensorProduct.congr e₃.detLineCongr e₆.detLineCongr.symm.dualMap s₂ := by
  -- Exactness and finite dimensionality of the complex sequence, transported from the real one.
  have h₁₂ : Function.Exact f₁ f₂ := (Function.Exact.iff_of_ladder_linearEquiv he₁ he₂).1 hg₁₂
  have h₂₃ : Function.Exact f₂ f₃ := (Function.Exact.iff_of_ladder_linearEquiv he₂ he₃).1 hg₂₃
  have h₃₄ : Function.Exact f₃ f₄ := (Function.Exact.iff_of_ladder_linearEquiv he₃ he₄).1 hg₃₄
  have h₄₅ : Function.Exact f₄ f₅ := (Function.Exact.iff_of_ladder_linearEquiv he₄ he₅).1 hg₄₅
  have hp₁ (a : A₁) : g₁ (e₁ a) = e₂ (f₁ a) := LinearMap.congr_fun he₁ a
  have hp₅ (a : A₅) : g₅ (e₅ a) = e₆ (f₅ a) := LinearMap.congr_fun he₅ a
  have hf₁ : Function.Injective f₁ := fun a b hab ↦ e₁.injective (hg₁ (by rw [hp₁, hp₁, hab]))
  have hf₅ : Function.Surjective f₅ := fun c ↦ by
    obtain ⟨b, hb⟩ := hg₅ (e₆ c)
    exact ⟨e₅.symm b, e₆.injective (by rw [← hp₅, LinearEquiv.apply_symm_apply, hb])⟩
  have : FiniteDimensional ℝ A₁ := Module.Finite.equiv e₁.symm
  have : FiniteDimensional ℝ A₃ := Module.Finite.equiv e₃.symm
  have : FiniteDimensional ℝ A₅ := Module.Finite.equiv e₅.symm
  have : FiniteDimensional ℂ A₁ := Module.Finite.of_restrictScalars_finite ℝ ℂ A₁
  have : FiniteDimensional ℂ A₃ := Module.Finite.of_restrictScalars_finite ℝ ℂ A₃
  have : FiniteDimensional ℂ A₅ := Module.Finite.of_restrictScalars_finite ℝ ℂ A₅
  have : FiniteDimensional ℂ A₂ := finiteDimensional_of_exact h₁₂
  have : FiniteDimensional ℂ A₄ := finiteDimensional_of_exact h₃₄
  have : FiniteDimensional ℂ A₆ := Module.Finite.of_surjective f₅ hf₅
  -- Complex bases of `A₁`, of the ranges of `f₂`, `f₃`, `f₄` and of `A₆`, lifts `v`, `w`, `x`,
  -- `y` of the last four, and the complex bases of `A₂`, …, `A₅` they give.
  set b₁ := finBasis ℂ A₁
  set b₆ := finBasis ℂ A₆
  obtain ⟨v, c₂, hv, hc₂⟩ := Basis.exists_coe_eq_append_lift hf₁ h₁₂.rangeRestrict
    f₂.surjective_rangeRestrict b₁ (finBasis ℂ (LinearMap.range f₂))
  obtain ⟨w, c₃, hw, hc₃⟩ := Basis.exists_coe_eq_append_lift
    (LinearMap.range f₂).injective_subtype h₂₃.range_subtype.rangeRestrict
    f₃.surjective_rangeRestrict (finBasis ℂ (LinearMap.range f₂)) (finBasis ℂ (LinearMap.range f₃))
  obtain ⟨x, c₄, hx, hc₄⟩ := Basis.exists_coe_eq_append_lift
    (LinearMap.range f₃).injective_subtype h₃₄.range_subtype.rangeRestrict
    f₄.surjective_rangeRestrict (finBasis ℂ (LinearMap.range f₃)) (finBasis ℂ (LinearMap.range f₄))
  obtain ⟨y, c₅, hy, hc₅⟩ := Basis.exists_coe_eq_append_lift
    (LinearMap.range f₄).injective_subtype h₄₅.range_subtype hf₅
    (finBasis ℂ (LinearMap.range f₄)) b₆
  rw [← hv, ← Function.comp_assoc, ← LinearMap.coe_comp,
    LinearMap.subtype_comp_rangeRestrict] at hc₃
  rw [← hw, ← Function.comp_assoc, ← LinearMap.coe_comp,
    LinearMap.subtype_comp_rangeRestrict] at hc₄
  rw [← hx, ← Function.comp_assoc, ← LinearMap.coe_comp,
    LinearMap.subtype_comp_rangeRestrict] at hc₅
  -- Real dimensions of the terms of the real sequence and of the ranges of its maps.
  have hB₁ : finrank ℝ B₁ = 2 * finrank ℂ A₁ :=
    e₁.finrank_eq.symm.trans finrank_real_eq_two_mul_finrank_complex
  have hB₆ : finrank ℝ B₆ = 2 * finrank ℂ A₆ :=
    e₆.finrank_eq.symm.trans finrank_real_eq_two_mul_finrank_complex
  have hR₂ := finrank_range_eq_two_mul e₂ e₃ he₂
  have hR₃ := finrank_range_eq_two_mul e₃ e₄ he₃
  have hR₄ := finrank_range_eq_two_mul e₄ e₅ he₄
  have hB₂ := finrank_eq_two_mul_of_basis e₂ c₂
  have hB₃ := finrank_eq_two_mul_of_basis e₃ c₃
  have hB₄ := finrank_eq_two_mul_of_basis e₄ c₄
  have hB₅ := finrank_eq_two_mul_of_basis e₅ c₅
  -- The real families and exterior products entering `TauCeti.detLineSixTermEquiv_tmul`.
  set u' := e₁ ∘ complexToRealFamily b₁ ∘ Fin.cast hB₁
  set v' := e₂ ∘ complexToRealFamily v ∘ Fin.cast hR₂
  set w' := e₃ ∘ complexToRealFamily w ∘ Fin.cast hR₃
  set x' := e₄ ∘ complexToRealFamily x ∘ Fin.cast hR₄
  set y' := e₅ ∘ complexToRealFamily y ∘ Fin.cast hB₆
  set β : detLine ℝ B₂ := exteriorPower.ιMulti ℝ _ (Fin.append (g₁ ∘ u') v' ∘ Fin.cast (by omega))
  set γ : detLine ℝ B₃ := exteriorPower.ιMulti ℝ _ (Fin.append (g₂ ∘ v') w' ∘ Fin.cast (by omega))
  set δ : detLine ℝ B₄ := exteriorPower.ιMulti ℝ _ (Fin.append (g₃ ∘ w') x' ∘ Fin.cast (by omega))
  set ε : detLine ℝ B₅ := exteriorPower.ιMulti ℝ _ (Fin.append (g₄ ∘ x') y' ∘ Fin.cast (by omega))
  -- Their transports to the complex sequence are complex positive.
  have hβ := isComplexPositive_detLineCongr_symm_ιMulti_append e₁ e₂ he₁ c₂ hc₂ hB₁ hR₂
    (by omega)
  have hγ := isComplexPositive_detLineCongr_symm_ιMulti_append e₂ e₃ he₂ c₃ hc₃ hR₂ hR₃
    (by omega)
  have hδ := isComplexPositive_detLineCongr_symm_ιMulti_append e₃ e₄ he₃ c₄ hc₄ hR₃ hR₄
    (by omega)
  have hε := isComplexPositive_detLineCongr_symm_ιMulti_append e₄ e₅ he₄ c₅ hc₅ hR₄ hB₆
    (by omega)
  have hα := isComplexPositive_detLineCongr_symm_ιMulti_comp e₁ e₁ (f := LinearMap.id)
    (g := LinearMap.id) rfl b₁ rfl hB₁
  have hζ := isComplexPositive_detLineCongr_symm_ιMulti_comp e₅ e₆ he₅ b₆ hy hB₆
  -- Functionals normalized at `δ` and at the exterior product of `g₅ ∘ y'`.
  obtain ⟨ψ, hψ⟩ := Projective.exists_dual_eq_one ℝ hδ.ne_zero
  obtain ⟨χ, hχ⟩ := Projective.exists_dual_eq_one ℝ hζ.ne_zero
  -- Compute the image of `t`, a positive multiple of `e₂⁻¹ β ⊗ φ` for a complex positive `φ`.
  obtain ⟨φ, hφ⟩ := exists_isComplexPositiveDual (E := A₅)
  obtain ⟨c, hc, rfl⟩ := (hβ.isComplexPositiveTMulDual_tmul hφ).exists_pos_smul_eq ht
  refine ⟨(c * φ (e₅.symm.detLineCongr ε)) • (e₁.symm.detLineCongr
      (exteriorPower.ιMulti ℝ _ u') ⊗ₜ ψ), e₃.symm.detLineCongr γ ⊗ₜ χ,
    (hα.smul (mul_pos hc (hε.isComplexPositiveDual_iff.1 hφ))).isComplexPositiveTMulDual_tmul
      (hδ.isComplexPositiveDual_of_apply_eq_one hψ),
    hγ.isComplexPositiveTMulDual_tmul (hζ.isComplexPositiveDual_of_apply_eq_one hχ), ?_⟩
  have hβ' : (β : ExteriorAlgebra ℝ B₂) = ExteriorAlgebra.ιMulti ℝ _ (Fin.append (g₁ ∘ u') v') := by
    simp [β]
  have hγ' : (γ : ExteriorAlgebra ℝ B₃) = ExteriorAlgebra.ιMulti ℝ _ (Fin.append (g₂ ∘ v') w') := by
    simp [γ]
  have hδ' : (δ : ExteriorAlgebra ℝ B₄) = ExteriorAlgebra.ιMulti ℝ _ (Fin.append (g₃ ∘ w') x') := by
    simp [δ]
  have hε' : (ε : ExteriorAlgebra ℝ B₅) = ExteriorAlgebra.ιMulti ℝ _ (Fin.append (g₄ ∘ x') y') := by
    simp [ε]
  have hψ' : e₄.detLineCongr.symm.dualMap ψ δ = 1 := by
    rwa [LinearEquiv.dualMap_apply, LinearEquiv.detLineCongr_symm]
  have hχ' : e₆.detLineCongr.symm.dualMap χ (exteriorPower.ιMulti ℝ _ (g₅ ∘ y')) = 1 := by
    rwa [LinearEquiv.dualMap_apply, LinearEquiv.detLineCongr_symm]
  rw [map_smul, map_smul, TensorProduct.congr_tmul, ← LinearEquiv.detLineCongr_symm e₂,
    LinearEquiv.apply_symm_apply,
    detLineSixTermEquiv_tmul hg₁ hg₁₂ hg₂₃ hg₃₄ hg₄₅ hg₅ u' v' w' x' y' hβ' hγ' hδ' hε' _ hψ' hχ',
    ← LinearEquiv.detLineCongr_symm e₁, ← LinearEquiv.detLineCongr_symm e₃,
    ← LinearEquiv.detLineCongr_symm e₅]
  simp only [TensorProduct.congr_tmul, map_smul, LinearEquiv.apply_symm_apply,
    LinearEquiv.dualMap_apply, TensorProduct.smul_tmul', smul_smul]

end SixTerm

end TauCeti

namespace LinearMap

open TauCeti

variable {M N P : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  [AddCommGroup P] [Module ℂ P] [Module ℝ P] [IsScalarTower ℝ ℂ P]

/-- The inverse of `LinearMap.detLineRestrictScalarsEquiv` is the transport along the
identifications of the complex kernel and cokernel with the real ones. -/
private theorem detLineRestrictScalarsEquiv_symm_eq_congr (f : M →ₗ[ℂ] N) :
    f.detLineRestrictScalarsEquiv.symm = TensorProduct.congr
      (f.kerRestrictScalarsEquiv ℝ).detLineCongr
      (f.cokerRestrictScalarsEquiv ℝ).symm.detLineCongr.symm.dualMap := by
  refine LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun x φ ↦ ?_)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, detLineRestrictScalarsEquiv_symm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.detLineCongr_symm, LinearEquiv.symm_symm]
  exact congrArg _ (LinearMap.ext fun _ ↦ (LinearEquiv.dualMap_apply _ _ _).symm)

variable (f : M →ₗ[ℂ] N) (g : N →ₗ[ℂ] P)

/-! ### The kernel–cokernel sequences of a complex composite and of its real restriction

The maps of the real sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) →
coker g → 0` of the restricted maps commute with the identifications of real and complex kernels
and cokernels. They act on representatives, but the kernel and cokernel of the restriction of
`g ∘ f` agree with those of the composite of the restrictions only up to definitional unfolding,
which defeats rewriting, so each square is checked by an explicit chain of equations. -/

/-- The inclusion of kernels commutes with the identifications of real and complex kernels. -/
private theorem inclusion_comp_kerRestrictScalarsEquiv :
    Submodule.inclusion (ker_le_ker_comp (f.restrictScalars ℝ) (g.restrictScalars ℝ)) ∘ₗ
    (f.kerRestrictScalarsEquiv ℝ).toLinearMap =
      ((g ∘ₗ f).kerRestrictScalarsEquiv ℝ).toLinearMap ∘ₗ
      (Submodule.inclusion (ker_le_ker_comp f g)).restrictScalars ℝ :=
  LinearMap.ext fun x ↦ Subtype.ext ((coe_kerRestrictScalarsEquiv_apply ℝ f x).trans
    (coe_kerRestrictScalarsEquiv_apply ℝ (g ∘ₗ f)
      (Submodule.inclusion (ker_le_ker_comp f g) x)).symm)

/-- The map `ker (g ∘ f) → ker g` commutes with the identifications of real and complex
kernels. -/
private theorem kerCompToKer_comp_kerRestrictScalarsEquiv :
    (f.restrictScalars ℝ).kerCompToKer (g.restrictScalars ℝ) ∘ₗ
    ((g ∘ₗ f).kerRestrictScalarsEquiv ℝ).toLinearMap =
      (g.kerRestrictScalarsEquiv ℝ).toLinearMap ∘ₗ (f.kerCompToKer g).restrictScalars ℝ :=
  LinearMap.ext fun x ↦ Subtype.ext ((coe_kerCompToKer_apply _ _ _).trans
    ((congrArg f (coe_kerRestrictScalarsEquiv_apply ℝ (g ∘ₗ f) x)).trans
      ((coe_kerCompToKer_apply f g x).symm.trans
        (coe_kerRestrictScalarsEquiv_apply ℝ g (f.kerCompToKer g x)).symm)))

/-- The map `ker g → coker f` commutes with the identifications of real and complex kernels and
cokernels. -/
private theorem kerToCoker_comp_kerRestrictScalarsEquiv :
    (f.restrictScalars ℝ).kerToCoker (g.restrictScalars ℝ) ∘ₗ
    (g.kerRestrictScalarsEquiv ℝ).toLinearMap =
      (f.cokerRestrictScalarsEquiv ℝ).symm.toLinearMap ∘ₗ (f.kerToCoker g).restrictScalars ℝ :=
  LinearMap.ext fun x ↦ (kerToCoker_apply _ _ _).trans
    ((congrArg Submodule.Quotient.mk (coe_kerRestrictScalarsEquiv_apply ℝ g x)).trans
      ((cokerRestrictScalarsEquiv_symm_mk ℝ f _).symm.trans
        (congrArg _ (kerToCoker_apply f g x)).symm))

/-- The map `coker f → coker (g ∘ f)` commutes with the identifications of real and complex
cokernels. -/
private theorem cokerToCokerComp_comp_cokerRestrictScalarsEquiv_symm :
    (f.restrictScalars ℝ).cokerToCokerComp (g.restrictScalars ℝ) ∘ₗ
    (f.cokerRestrictScalarsEquiv ℝ).symm.toLinearMap =
      ((g ∘ₗ f).cokerRestrictScalarsEquiv ℝ).symm.toLinearMap ∘ₗ
      (f.cokerToCokerComp g).restrictScalars ℝ :=
  LinearMap.ext fun q ↦ Submodule.Quotient.induction_on _ q fun y ↦
    (congrArg _ (cokerRestrictScalarsEquiv_symm_mk ℝ f y)).trans
      ((cokerToCokerComp_mk _ _ y).trans
        ((cokerRestrictScalarsEquiv_symm_mk ℝ (g ∘ₗ f) (g y)).symm.trans
          (congrArg _ (cokerToCokerComp_mk f g y)).symm))

/-- The quotient map `coker (g ∘ f) → coker g` commutes with the identifications of real and
complex cokernels. -/
private theorem factor_comp_cokerRestrictScalarsEquiv_symm :
    Submodule.factor (range_comp_le_range (f.restrictScalars ℝ) (g.restrictScalars ℝ)) ∘ₗ
    ((g ∘ₗ f).cokerRestrictScalarsEquiv ℝ).symm.toLinearMap =
      (g.cokerRestrictScalarsEquiv ℝ).symm.toLinearMap ∘ₗ
      (Submodule.factor (range_comp_le_range f g)).restrictScalars ℝ :=
  LinearMap.ext fun q ↦ Submodule.Quotient.induction_on _ q fun y ↦
    (congrArg _ (cokerRestrictScalarsEquiv_symm_mk ℝ (g ∘ₗ f) y)).trans
      ((Submodule.factor_mk
        (range_comp_le_range (f.restrictScalars ℝ) (g.restrictScalars ℝ)) y).trans
        ((cokerRestrictScalarsEquiv_symm_mk ℝ g y).symm.trans
          (congrArg _ (Submodule.factor_mk (range_comp_le_range f g) y)).symm))

variable {f g} [FiniteDimensional ℝ (ker (f.restrictScalars ℝ))]
  [FiniteDimensional ℝ (ker (g.restrictScalars ℝ))]
  [FiniteDimensional ℝ (N ⧸ range (f.restrictScalars ℝ))]
  [FiniteDimensional ℝ (P ⧸ range (g.restrictScalars ℝ))]

/-- **The composition law of determinant lines respects complex orientations.** For complex-linear
maps `f` and `g` with finite-dimensional kernels and cokernels, the isomorphism
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) sends a complex positive element of
`det (g ∘ f)` to `x ⊗ y` for complex positive elements `x` of `det f` and `y` of `det g`. -/
theorem IsComplexPositiveDetLine.exists_detLineCompEquiv_eq_tmul
    {z : ((g ∘ₗ f).restrictScalars ℝ).detLine} (hz : (g ∘ₗ f).IsComplexPositiveDetLine z) :
    ∃ x y, f.IsComplexPositiveDetLine x ∧ g.IsComplexPositiveDetLine y ∧
      (f.restrictScalars ℝ).detLineCompEquiv (g.restrictScalars ℝ) z = x ⊗ₜ y := by
  have : FiniteDimensional ℝ (P ⧸ range (g.restrictScalars ℝ ∘ₗ f.restrictScalars ℝ)) :=
    Module.Finite.quotient_range_comp (f.restrictScalars ℝ) (g.restrictScalars ℝ)
  -- The kernel–cokernel sequence of the real composite is isomorphic to that of the complex
  -- composite, through the identifications of the real and complex kernels and cokernels.
  obtain ⟨s₁, s₂, hs₁, hs₂, h⟩ := exists_detLineSixTermEquiv_congr_eq_tmul
    (Submodule.inclusion_injective _)
    ((f.restrictScalars ℝ).exact_inclusion_kerCompToKer (g.restrictScalars ℝ))
    ((f.restrictScalars ℝ).exact_kerCompToKer_kerToCoker (g.restrictScalars ℝ))
    ((f.restrictScalars ℝ).exact_kerToCoker_cokerToCokerComp (g.restrictScalars ℝ))
    ((f.restrictScalars ℝ).exact_cokerToCokerComp_factor (g.restrictScalars ℝ))
    (Submodule.factor_surjective _) _ _ _ _ _ _ (inclusion_comp_kerRestrictScalarsEquiv f g)
    (kerCompToKer_comp_kerRestrictScalarsEquiv f g) (kerToCoker_comp_kerRestrictScalarsEquiv f g)
    (cokerToCokerComp_comp_cokerRestrictScalarsEquiv_symm f g)
    (factor_comp_cokerRestrictScalarsEquiv_symm f g)
    (isComplexPositiveDetLine_iff.1 hz)
  have hz' : TensorProduct.congr ((g ∘ₗ f).kerRestrictScalarsEquiv ℝ).detLineCongr
      ((g ∘ₗ f).cokerRestrictScalarsEquiv ℝ).symm.detLineCongr.symm.dualMap
        ((g ∘ₗ f).detLineRestrictScalarsEquiv z) = z :=
    (LinearEquiv.congr_fun (detLineRestrictScalarsEquiv_symm_eq_congr (g ∘ₗ f)) _).symm.trans
      (LinearEquiv.symm_apply_apply _ z)
  refine ⟨f.detLineRestrictScalarsEquiv.symm s₁, g.detLineRestrictScalarsEquiv.symm s₂,
    by rwa [isComplexPositiveDetLine_iff, LinearEquiv.apply_symm_apply],
    by rwa [isComplexPositiveDetLine_iff, LinearEquiv.apply_symm_apply], ?_⟩
  -- `(g ∘ₗ f).restrictScalars ℝ` is `g.restrictScalars ℝ ∘ₗ f.restrictScalars ℝ` by definition
  -- (`LinearMap.restrictScalars_comp` is `rfl`), but not syntactically, so the two determinant
  -- lines are matched by `Eq.trans`, which checks definitional equality, rather than by rewriting.
  rw [detLineCompEquiv_def]
  exact ((congrArg _ hz').symm.trans h).trans (congrArg₂ (· ⊗ₜ ·)
    (LinearEquiv.congr_fun (detLineRestrictScalarsEquiv_symm_eq_congr f) s₁).symm
    (LinearEquiv.congr_fun (detLineRestrictScalarsEquiv_symm_eq_congr g) s₂).symm)

end LinearMap
