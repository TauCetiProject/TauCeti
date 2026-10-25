/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hochschild.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation

/-!
# Gauge transformations of `A∞` structures

An `A∞` structure on a graded module `A` is a degree-one square-zero coderivation `b` of the
reduced bar construction `Tᶜ(sA)`.  Conjugating it by a degree-zero coalgebra automorphism `F` of
`Tᶜ(sA)` gives another one, `F⁻¹ ∘ b ∘ F`, and `F` becomes an `A∞` isomorphism from the new
structure to the old.  More generally, an isomorphism of reduced bar constructions
`e : Tᶜ(sA) ≃ Tᶜ(sB)` pulls an `A∞` structure on `B` back to one on `A`
(`TauCeti.AInfinityAlgebra.comapBarEquiv`).

A **gauge transformation** uses the coalgebra automorphism whose Taylor components are those of
the identity perturbed by a degree-zero suspended Hochschild cochain `φ` without unary component
(`TauCeti.AInfinityAlgebra.gauge`).  If `φ` vanishes on the words of length at most `e`, the new
Taylor map `m'` differs from the old one `m` on the words of length at most `2 e + 1` only through
the Hochschild differential `δφ = [m, φ]`:

```text
m' = m + δφ - φ{δφ}   on words of length at most 2 e + 1,
m' = m + δφ           on words of length at most 2 e.
```

For a minimal `A∞` algebra the correction `φ{δφ}` vanishes, `m'` agrees with `m` on the words of
length at most `e + 1`, and `m' = m + δφ` on the words of length at most `2 e + 1`.  This is the
inductive step of Kadeishvili's obstruction theory: if the operations `m₃, …, mₙ₋₁` of a minimal
`A∞` algebra vanish and `mₙ` is a Hochschild coboundary `-δφ` for a cochain `φ` of arity `n - 1`,
then the gauge transformation by `φ` keeps `m₃, …, mₙ₋₁` zero and kills `mₙ`, and it is
`A∞` isomorphic to the original algebra through a morphism whose linear part is the identity.

## Main definitions

* `TauCeti.AInfinityAlgebra.comapBarEquiv`: the `A∞` structure pulled back along a degree-zero
  isomorphism of reduced bar constructions, and `TauCeti.AInfinityAlgebra.comapBarEquivHom` the
  resulting `A∞` isomorphism.
* `TauCeti.AInfinityAlgebra.gauge`: the gauge transformation of an `A∞` structure by a degree-zero
  cochain without unary component, and `TauCeti.AInfinityAlgebra.gaugeHom` the `A∞` isomorphism
  to the original structure, with linear part the identity.

## Main results

* `TauCeti.AInfinityAlgebra.isIso_comapBarEquivHom` and `TauCeti.AInfinityAlgebra.isIso_gaugeHom`:
  both morphisms are `A∞` isomorphisms.
* `TauCeti.AInfinityHom.taylor_eq_taylor_comp_coalgHom_sub_brace`: the morphism equation of an
  `A∞` morphism with Taylor map `letter + ψ`, in the form `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}`.
* `TauCeti.AInfinityAlgebra.taylor_gauge`: the recursive formula `m' = m ∘ F - φ{m'}`.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_apply_eq_zero_of_mem_filtration`: the
  Hochschild differential of a cochain vanishing on the words of length at most `e` vanishes on
  them; for a minimal algebra it vanishes on the words of length at most `e + 1`
  (`IsMinimal.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one`).
* `TauCeti.AInfinityAlgebra.taylor_gauge_apply_of_mem_filtration_two_mul` and
  `TauCeti.AInfinityAlgebra.taylor_gauge_apply_of_mem_filtration_two_mul_add_one`: the new Taylor
  map on short words.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_gauge_apply_of_mem_filtration`,
  `TauCeti.AInfinityAlgebra.IsMinimal.m_gauge_of_le` and
  `TauCeti.AInfinityAlgebra.IsMinimal.isMinimal_gauge`: for a minimal algebra, the gauge
  transformation adds `δφ` on the words of length at most `2 e + 1`, keeps the operations of
  arity at most `e + 1`, and is minimal.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for braces and the Hochschild differential.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
-/

public section

universe uR uA uB

namespace TauCeti

namespace AInfinityHom

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 ℋ : AInfinityAlgebra R A}

/-- **The morphism equation in gauge form.**  Let `f : 𝒜 ⟶ ℋ` be an `A∞` morphism between
structures with the same grading, with Taylor map `letter + ψ`.  Then the Taylor map of `𝒜`
satisfies `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}`, for `F` the coalgebra map with Taylor components
`letter + ψ`. -/
theorem taylor_eq_taylor_comp_coalgHom_sub_brace (f : AInfinityHom 𝒜 ℋ)
    (hG : 𝒜.grading = ℋ.grading) {ψ : ReducedTensorWords R A →ₗ[R] A}
    (hf : f.taylor = letter R A + ψ) :
    𝒜.taylor = ℋ.taylor ∘ₗ coalgHom R (letter R A + ψ) -
      brace (ℋ.grading.shift 1) ψ 𝒜.taylor 1 := by
  have h := f.taylor_comp_barMap
  rw [f.barMap_eq_coalgHom, hf, LinearMap.add_comp, AInfinityAlgebra.letter_comp_barDifferential,
    AInfinityAlgebra.barDifferential_def, hG] at h
  rw [h, brace_def, add_sub_cancel_right]

end AInfinityHom

namespace AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-! ### Pulling back along an isomorphism of bar constructions -/

section ComapBarEquiv

variable (ℬ : AInfinityAlgebra R B) (G : InternalGrading R A)
  (e : ReducedTensorWords R A ≃ₗ[R] ReducedTensorWords R B)
  (he : IsCoalgHom R e.toLinearMap)
  (he₀ : LinearMap.IsHomogeneous e.toLinearMap (gradedPiece (G.shift 1))
    (gradedPiece (ℬ.grading.shift 1)) 0)

include he he₀

/-- The conjugate `e⁻¹ ∘ b ∘ e` of the bar differential `b` of `ℬ` is a graded coderivation. -/
private theorem isGradedCoderivation_symm_comp_barDifferential_comp :
    IsGradedCoderivation (G.shift 1) 1
      (e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap) := by
  have h := he.linearEquiv_symm.comp_isGradedCoderivationAlong
    (ℬ.isGradedCoderivation_barDifferential.comp_isCoalgHom he he₀)
  rwa [LinearEquiv.symm_comp, isGradedCoderivationAlong_id_id_iff] at h

/-- The letter component of the conjugate `e⁻¹ ∘ b ∘ e` has degree one. -/
private theorem isHomogeneous_letter_comp_symm_comp_barDifferential_comp :
    LinearMap.IsHomogeneous
      (letter R A ∘ₗ e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap)
      (gradedPiece (G.shift 1)) (G.shift 1).piece 1 := by
  simpa using (isHomogeneous_letter (G.shift 1)).comp
    ((he.isHomogeneous_linearEquiv_symm he₀).comp (ℬ.isHomogeneous_barDifferential.comp he₀))

/-- The conjugate `e⁻¹ ∘ b ∘ e` is the coderivation generated by its letter component. -/
private theorem gradedCoderiv_letter_comp_symm_comp_barDifferential_comp :
    gradedCoderiv (G.shift 1)
        (letter R A ∘ₗ e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap) 1 =
      e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap :=
  (isGradedCoderivation_gradedCoderiv _ _ 1).eq_of_letter_comp_eq
    (isGradedCoderivation_symm_comp_barDifferential_comp ℬ G e he he₀)
    (letter_comp_gradedCoderiv _ _ _)

/-- The `A∞` structure on `A` pulled back from `ℬ` along a degree-zero isomorphism
`e : Tᶜ(sA) ≃ Tᶜ(sB)` of reduced bar constructions: its bar differential is `e⁻¹ ∘ b ∘ e`, for the
bar differential `b` of `ℬ`. -/
noncomputable def comapBarEquiv : AInfinityAlgebra R A :=
  ofTaylor G (letter R A ∘ₗ e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap)
    (isHomogeneous_letter_comp_symm_comp_barDifferential_comp ℬ G e he he₀) <| by
      rw [gradedCoderiv_letter_comp_symm_comp_barDifferential_comp ℬ G e he he₀]
      refine LinearMap.ext fun z ↦ ?_
      have h := LinearMap.congr_fun ℬ.barDifferential_sq (e z)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        LinearMap.zero_apply] at h ⊢
      rw [h, map_zero]

@[simp]
theorem comapBarEquiv_grading : (ℬ.comapBarEquiv G e he he₀).grading = G := by
  rw [comapBarEquiv, ofTaylor_grading]

@[simp]
theorem taylor_comapBarEquiv :
    (ℬ.comapBarEquiv G e he he₀).taylor =
      letter R A ∘ₗ e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap := by
  rw [comapBarEquiv, ofTaylor_taylor]

/-- The bar differential of the pulled-back structure is the conjugate `e⁻¹ ∘ b ∘ e`. -/
@[simp]
theorem barDifferential_comapBarEquiv :
    (ℬ.comapBarEquiv G e he he₀).barDifferential =
      e.symm.toLinearMap ∘ₗ ℬ.barDifferential ∘ₗ e.toLinearMap := by
  rw [barDifferential_def, comapBarEquiv_grading, taylor_comapBarEquiv,
    gradedCoderiv_letter_comp_symm_comp_barDifferential_comp ℬ G e he he₀]

/-- The isomorphism of bar constructions along which an `A∞` structure is pulled back, as an
`A∞` morphism from the pulled-back structure. -/
noncomputable def comapBarEquivHom : AInfinityHom (ℬ.comapBarEquiv G e he he₀) ℬ where
  barMap := e.toLinearMap
  isCoalgHom_barMap := he
  isHomogeneous_barMap := by
    rw [comapBarEquiv_grading]
    exact he₀
  barDifferential_comp_barMap := by
    rw [barDifferential_comapBarEquiv]
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

@[simp]
theorem barMap_comapBarEquivHom :
    (ℬ.comapBarEquivHom G e he he₀).barMap = e.toLinearMap := (rfl)

/-- The pulled-back structure is `A∞` isomorphic to the original one. -/
theorem isIso_comapBarEquivHom : (ℬ.comapBarEquivHom G e he he₀).IsIso := by
  refine AInfinityHom.isIso_of_linearPart_bijective _ ?_
  have h : (ℬ.comapBarEquivHom G e he he₀).linearPart =
      letter R B ∘ₗ e.toLinearMap ∘ₗ ofLetter R A := by
    refine LinearMap.ext fun a ↦ ?_
    rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_def, barMap_comapBarEquivHom,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h]
  exact he.letter_comp_comp_ofLetter_bijective

end ComapBarEquiv

/-! ### Gauge transformations -/

section Gauge

variable (𝒜 : AInfinityAlgebra R A) (φ : ReducedTensorWords R A →ₗ[R] A)
  (hφ : LinearMap.IsHomogeneous φ (gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 0)
  (hφ₁ : φ ∘ₗ ofLetter R A = 0)

include hφ₁ in
/-- The coalgebra automorphism with Taylor components `letter + φ` is bijective: its arity-one
component is the identity. -/
private theorem bijective_coalgHom_letter_add :
    Function.Bijective (coalgHom R (letter R A + φ)) := by
  refine (isCoalgHom_coalgHom _).bijective_of_letter_comp_comp_ofLetter_bijective ?_
  have h : letter R A ∘ₗ coalgHom R (letter R A + φ) ∘ₗ ofLetter R A = LinearMap.id := by
    refine LinearMap.ext fun a ↦ ?_
    have ha := LinearMap.congr_fun hφ₁ a
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at ha
    rw [LinearMap.comp_apply, LinearMap.comp_apply, coalgHom_ofLetter, letter_ofLetter,
      LinearMap.add_apply, letter_ofLetter, ha, add_zero, LinearMap.id_apply]
  rw [h]
  exact Function.bijective_id

/-- The coalgebra automorphism with Taylor components `letter + φ`, as a linear equivalence. -/
private noncomputable def gaugeBarEquiv : ReducedTensorWords R A ≃ₗ[R] ReducedTensorWords R A :=
  LinearEquiv.ofBijective _ (bijective_coalgHom_letter_add φ hφ₁)

private theorem coe_gaugeBarEquiv :
    (gaugeBarEquiv φ hφ₁).toLinearMap = coalgHom R (letter R A + φ) :=
  LinearMap.ext fun _ ↦ LinearEquiv.ofBijective_apply _ _

/-- The **gauge transformation** of `𝒜` by a degree-zero suspended cochain `φ` without unary
component: the `A∞` structure pulled back along the coalgebra automorphism `F` of `Tᶜ(sA)` with
Taylor components `letter + φ`, whose bar differential is `F⁻¹ ∘ b ∘ F`. -/
noncomputable def gauge : AInfinityAlgebra R A :=
  𝒜.comapBarEquiv 𝒜.grading (gaugeBarEquiv φ hφ₁)
    (by rw [coe_gaugeBarEquiv]; exact isCoalgHom_coalgHom _)
    (by rw [coe_gaugeBarEquiv]; exact isHomogeneous_coalgHom ((isHomogeneous_letter _).add hφ))

@[simp]
theorem gauge_grading : (𝒜.gauge φ hφ hφ₁).grading = 𝒜.grading := by
  rw [gauge, comapBarEquiv_grading]

/-- The coalgebra automorphism defining a gauge transformation, as an `A∞` morphism from the
gauge-transformed structure to the original one. -/
noncomputable def gaugeHom : AInfinityHom (𝒜.gauge φ hφ hφ₁) 𝒜 :=
  𝒜.comapBarEquivHom _ _ _ _

@[simp]
theorem barMap_gaugeHom :
    (𝒜.gaugeHom φ hφ hφ₁).barMap = coalgHom R (letter R A + φ) := by
  rw [gaugeHom, barMap_comapBarEquivHom, coe_gaugeBarEquiv]

/-- The Taylor components of the gauge morphism are `letter + φ`. -/
@[simp]
theorem taylor_gaugeHom : (𝒜.gaugeHom φ hφ hφ₁).taylor = letter R A + φ := by
  rw [AInfinityHom.taylor_def, barMap_gaugeHom, letter_comp_coalgHom]

/-- The linear part of the gauge morphism is the identity. -/
@[simp]
theorem linearPart_gaugeHom : (𝒜.gaugeHom φ hφ hφ₁).linearPart = LinearMap.id := by
  refine LinearMap.ext fun a ↦ ?_
  have ha := LinearMap.congr_fun hφ₁ a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at ha
  rw [AInfinityHom.linearPart_apply, taylor_gaugeHom, LinearMap.add_apply, letter_ofLetter, ha,
    add_zero, LinearMap.id_apply]

/-- **A gauge transformation is `A∞` isomorphic to the original structure.** -/
theorem isIso_gaugeHom : (𝒜.gaugeHom φ hφ hφ₁).IsIso :=
  𝒜.isIso_comapBarEquivHom _ _ _ _

/-- The Taylor map `m'` of a gauge transformation satisfies `m' = m ∘ F - φ{m'}`, for `m` the
Taylor map of `𝒜` and `F` the coalgebra automorphism with Taylor components `letter + φ`. -/
theorem taylor_gauge :
    (𝒜.gauge φ hφ hφ₁).taylor =
      𝒜.taylor ∘ₗ coalgHom R (letter R A + φ) -
        brace (𝒜.grading.shift 1) φ (𝒜.gauge φ hφ hφ₁).taylor 1 :=
  (𝒜.gaugeHom φ hφ hφ₁).taylor_eq_taylor_comp_coalgHom_sub_brace (gauge_grading 𝒜 φ hφ hφ₁)
    (taylor_gaugeHom 𝒜 φ hφ hφ₁)

/-! ### The gauge transformation on short words -/

variable {𝒜 φ}

/-- The Hochschild differential of a cochain vanishing on the words of length at most `e` vanishes
on them. -/
theorem hochschildDifferential_apply_eq_zero_of_mem_filtration (q : ℤ) {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A e) : 𝒜.hochschildDifferential q φ z = 0 := by
  rw [hochschildDifferential_eq_brace_sub, LinearMap.sub_apply, LinearMap.smul_apply,
    brace_apply_eq_zero_of_mem_filtration _ _ (apply_eq_zero_of_mem_filtration_zero R A _) hφe
      (by rwa [zero_add]),
    brace_apply_eq_zero_of_mem_filtration _ _ hφe (apply_eq_zero_of_mem_filtration_zero R A _)
      (by rwa [add_zero]), smul_zero, sub_zero]

/-- On the words of length at most `2 e + 1`, the difference `h = m' - m` of the Taylor maps
satisfies `h = δφ - φ{h}`. -/
private theorem taylor_gauge_sub_apply {e : ℕ} (hφe : ∀ z ∈ filtration R A e, φ z = 0)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (2 * e + 1)) :
    (𝒜.gauge φ hφ hφ₁).taylor z - 𝒜.taylor z =
      𝒜.hochschildDifferential 0 φ z -
        brace (𝒜.grading.shift 1) φ ((𝒜.gauge φ hφ hφ₁).taylor - 𝒜.taylor) 1 z := by
  conv_lhs => rw [taylor_gauge]
  rw [hochschildDifferential_zero_apply]
  have hb : brace (𝒜.grading.shift 1) φ (𝒜.gauge φ hφ hφ₁).taylor 1 =
      brace (𝒜.grading.shift 1) φ 𝒜.taylor 1 +
        brace (𝒜.grading.shift 1) φ ((𝒜.gauge φ hφ hφ₁).taylor - 𝒜.taylor) 1 := by
    rw [← brace_add_right, add_sub_cancel]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hb, LinearMap.add_apply,
    coalgHom_letter_add_apply_of_mem_filtration hφe hz, map_add]
  abel

/-- The Taylor maps of a gauge transformation and of the original structure agree on the words of
length at most `e`, when `φ` vanishes on them. -/
private theorem taylor_gauge_apply_of_mem_filtration_self {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A e) : (𝒜.gauge φ hφ hφ₁).taylor z = 𝒜.taylor z := by
  have h := taylor_gauge_sub_apply hφ hφ₁ hφe (filtration_monotone R A (by omega) hz)
  rw [hochschildDifferential_apply_eq_zero_of_mem_filtration 0 hφe hz,
    brace_apply_eq_zero_of_mem_filtration _ _ hφe (apply_eq_zero_of_mem_filtration_zero R A _)
      (by rwa [add_zero]), sub_zero, sub_eq_zero] at h
  exact h

/-- **The gauge transformation on words of length at most `2 e`.**  If `φ` vanishes on the words
of length at most `e`, the gauge transformation adds the Hochschild differential `δφ = [m, φ]` to
the Taylor map on the words of length at most `2 e`. -/
theorem taylor_gauge_apply_of_mem_filtration_two_mul {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (2 * e)) :
    (𝒜.gauge φ hφ hφ₁).taylor z = 𝒜.taylor z + 𝒜.hochschildDifferential 0 φ z := by
  have h := taylor_gauge_sub_apply hφ hφ₁ hφe (filtration_monotone R A (by omega) hz)
  rw [brace_apply_eq_zero_of_mem_filtration _ _ hφe (k := e) (j := e)
      (fun w hw ↦ by
        rw [LinearMap.sub_apply, taylor_gauge_apply_of_mem_filtration_self hφ hφ₁ hφe hw,
          sub_self])
      (by rwa [← two_mul]), sub_zero, sub_eq_iff_eq_add'] at h
  exact h

/-- The gauge transformation on words of length at most `2 e + 1`, for `e ≥ 1`. -/
private theorem taylor_gauge_apply_of_mem_filtration_two_mul_add_one_of_one_le {e : ℕ}
    (he : 1 ≤ e)
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (2 * e + 1)) :
    (𝒜.gauge φ hφ hφ₁).taylor z =
      𝒜.taylor z + 𝒜.hochschildDifferential 0 φ z -
        brace (𝒜.grading.shift 1) φ (𝒜.hochschildDifferential 0 φ) 1 z := by
  have h := taylor_gauge_sub_apply hφ hφ₁ hφe hz
  -- On the words of length at most `2 e`, `m' - m` is `δφ`, so `φ{m' - m} = φ{δφ}` on `z`.
  have hb : brace (𝒜.grading.shift 1) φ ((𝒜.gauge φ hφ hφ₁).taylor - 𝒜.taylor) 1 z =
      brace (𝒜.grading.shift 1) φ (𝒜.hochschildDifferential 0 φ) 1 z := by
    have hsplit : (𝒜.gauge φ hφ hφ₁).taylor - 𝒜.taylor = 𝒜.hochschildDifferential 0 φ +
        ((𝒜.gauge φ hφ hφ₁).taylor - 𝒜.taylor - 𝒜.hochschildDifferential 0 φ) := by
      abel
    rw [hsplit, brace_add_right, LinearMap.add_apply,
      brace_apply_eq_zero_of_mem_filtration _ _ hφe (k := e) (j := 2 * e)
        (g := (𝒜.gauge φ hφ hφ₁).taylor - 𝒜.taylor - 𝒜.hochschildDifferential 0 φ)
        (fun w hw ↦ by
          rw [LinearMap.sub_apply, LinearMap.sub_apply,
            taylor_gauge_apply_of_mem_filtration_two_mul hφ hφ₁ hφe hw, add_sub_cancel_left,
            sub_self])
        (filtration_monotone R A (by omega) hz), add_zero]
  rw [hb, sub_eq_iff_eq_add'] at h
  rw [h]
  abel

/-- **The gauge transformation on words of length at most `2 e + 1`.**  If `φ` vanishes on the
words of length at most `e`, the gauge transformation changes the Taylor map `m` to
`m + δφ - φ{δφ}` on the words of length at most `2 e + 1`, where `δφ = [m, φ]` is the Hochschild
differential. -/
theorem taylor_gauge_apply_of_mem_filtration_two_mul_add_one {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (2 * e + 1)) :
    (𝒜.gauge φ hφ hφ₁).taylor z =
      𝒜.taylor z + 𝒜.hochschildDifferential 0 φ z -
        brace (𝒜.grading.shift 1) φ (𝒜.hochschildDifferential 0 φ) 1 z := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · -- Since `φ` vanishes on single letters, the case `e = 1` applies.
    exact taylor_gauge_apply_of_mem_filtration_two_mul_add_one_of_one_le hφ hφ₁ le_rfl
      (apply_eq_zero_of_mem_filtration_one R A hφ₁)
      (filtration_monotone R A (by omega) hz)
  · exact taylor_gauge_apply_of_mem_filtration_two_mul_add_one_of_one_le hφ hφ₁ he hφe hz

/-! ### Gauge transformations of minimal algebras -/

/-- The Taylor map of a minimal `A∞` algebra vanishes on single letters. -/
theorem IsMinimal.taylor_apply_eq_zero_of_mem_filtration_one (h𝒜 : 𝒜.IsMinimal) :
    ∀ z ∈ filtration R A 1, 𝒜.taylor z = 0 :=
  apply_eq_zero_of_mem_filtration_one R A (𝒜.taylor_comp_ofLetter.trans ((isMinimal_def 𝒜).1 h𝒜))

/-- For a minimal `A∞` algebra, the Hochschild differential of a cochain vanishing on the words of
length at most `e` vanishes on the words of length at most `e + 1`. -/
theorem IsMinimal.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one
    (h𝒜 : 𝒜.IsMinimal) (q : ℤ) {e : ℕ} (hφe : ∀ z ∈ filtration R A e, φ z = 0)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (e + 1)) :
    𝒜.hochschildDifferential q φ z = 0 := by
  rw [hochschildDifferential_eq_brace_sub, LinearMap.sub_apply, LinearMap.smul_apply,
    brace_apply_eq_zero_of_mem_filtration _ _
      h𝒜.taylor_apply_eq_zero_of_mem_filtration_one hφe (by rwa [add_comm]),
    brace_apply_eq_zero_of_mem_filtration _ _ hφe
      h𝒜.taylor_apply_eq_zero_of_mem_filtration_one hz, smul_zero, sub_zero]

/-- **The gauge transformation of a minimal algebra.**  If `𝒜` is minimal and `φ` vanishes on the
words of length at most `e`, the gauge transformation adds the Hochschild differential
`δφ = [m, φ]` to the Taylor map on the words of length at most `2 e + 1`. -/
theorem IsMinimal.taylor_gauge_apply_of_mem_filtration (h𝒜 : 𝒜.IsMinimal) {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (2 * e + 1)) :
    (𝒜.gauge φ hφ hφ₁).taylor z = 𝒜.taylor z + 𝒜.hochschildDifferential 0 φ z := by
  rw [taylor_gauge_apply_of_mem_filtration_two_mul_add_one hφ hφ₁ hφe hz,
    brace_apply_eq_zero_of_mem_filtration _ _ hφe (k := e) (j := e + 1)
      (fun w hw ↦ h𝒜.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one 0 hφe hw)
      (by rwa [← add_assoc, ← two_mul]), sub_zero]

/-- For a minimal `A∞` algebra, a gauge transformation by a cochain vanishing on the words of length
at most `e` does not change the Taylor map on the words of length at most `e + 1`. -/
theorem IsMinimal.taylor_gauge_apply_of_mem_filtration_add_one (h𝒜 : 𝒜.IsMinimal) {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (e + 1)) : (𝒜.gauge φ hφ hφ₁).taylor z = 𝒜.taylor z := by
  rw [h𝒜.taylor_gauge_apply_of_mem_filtration hφ hφ₁ hφe (filtration_monotone R A (by omega) hz),
    h𝒜.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one 0 hφe hz, add_zero]

/-- For a minimal `A∞` algebra, a gauge transformation by a cochain vanishing on the words of length
at most `e` does not change the operations of arity at most `e + 1`. -/
theorem IsMinimal.m_gauge_of_le (h𝒜 : 𝒜.IsMinimal) {e : ℕ}
    (hφe : ∀ z ∈ filtration R A e, φ z = 0) {n : ℕ} (hn : n ≤ e + 1) :
    (𝒜.gauge φ hφ hφ₁).m n = 𝒜.m n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [m_zero, m_zero]
  refine MultilinearMap.ext fun x ↦ ?_
  have h := h𝒜.taylor_gauge_apply_of_mem_filtration_add_one hφ hφ₁ hφe
    (of_mem_filtration R A (k := ⟨n, hn0⟩) hn
      (PiTensorProduct.tprod R fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))
  rw [taylor_of_tprod, taylor_of_tprod, gauge_grading] at h
  simpa only [InternalGrading.koszulTwist_koszulTwist] using h

/-- **A gauge transformation of a minimal `A∞` algebra is minimal.** -/
theorem IsMinimal.isMinimal_gauge (h𝒜 : 𝒜.IsMinimal) : (𝒜.gauge φ hφ hφ₁).IsMinimal := by
  rw [isMinimal_iff_m_one_eq_zero]
  intro x
  rw [h𝒜.m_gauge_of_le hφ hφ₁ (e := 0) (apply_eq_zero_of_mem_filtration_zero R A φ) le_rfl,
    h𝒜.m_one]

end Gauge

end AInfinityAlgebra

end TauCeti
