/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import TauCeti.NumberTheory.MulChar.Lemmas

/-!
# The conjugate form `f_ρ(τ) = conj (f (-conj τ))`

The conjugate of a modular form `f` is `f_ρ(τ) = conj (f (-conj τ))`. It is holomorphic, and if
`f = ∑ aₙ qⁿ` then `f_ρ = ∑ conj (aₙ) qⁿ`. Mathlib's slash action of `GL(2, ℝ)` builds complex
conjugation into the action of a matrix of negative determinant, so `f_ρ = f ∣[k] J` for the
reflection `J = !![-1, 0; 0, 1]` (`UpperHalfPlane.J`), and Mathlib's `ModularForm.translate` makes
`f_ρ` a modular form for `J⁻¹ 𝒢 J`. Conjugation by `J` changes the signs of the off-diagonal
entries, so it preserves `Γ₀(N)` and `Γ₁(N)`.

On `Γ₁(N)` the conjugate form carries the nebentypus `χ` to its complex conjugate `χ⁻¹`, since
the diamond eigenvalues are roots of unity, and it intertwines the Hecke operators `Tₙ`: their
coefficient formula has real coefficients apart from the values of `χ`. So the conjugate of a Hecke
eigenform of nebentypus `χ` is a Hecke eigenform of nebentypus `χ⁻¹` with the complex-conjugate
eigenvalues. This is the form that the Fricke involution relates a newform to: for a newform `f`
of level `N`, `f ∣ W_N` is a multiple of `f_ρ` (Miyake, Theorem 4.6.15), the multiple being the
Atkin–Li pseudo-eigenvalue.

## Main definitions

* `ModularForm.conj`, `CuspForm.conj`: the conjugate form `f_ρ`, with the
  antilinear maps `ModularForm.conjₗ` and `CuspForm.conjₗ`.
* `CuspForm.conjCharSpace`: the conjugate form as an antilinear equivalence
  `S_k(N, χ) ≃ S_k(N, χ⁻¹)`.

## Main results

* `TauCeti.qExpansion_slash_J`: slashing a modular form by `J` conjugates its `q`-expansion
  coefficients; `ModularForm.qExpansion_conj` and `CuspForm.qExpansion_conj`
  are its forms for `f_ρ`.
* `ModularForm.conj_conj`: `f ↦ f_ρ` is an involution.
* `CuspForm.conj_levelRaise`: `f ↦ f_ρ` commutes with the level-raising operators `V_d`.
* `TauCeti.Gamma0_map_le_conjAct_inv_J`, `TauCeti.Gamma1_map_le_conjAct_inv_J`: conjugation by
  `J` preserves `Γ₀(N)` and `Γ₁(N)`.
* `ModularForm.conj_mem_modFormCharSpace`, `CuspForm.conj_mem_cuspFormCharSpace`:
  `f ∈ M_k(N, χ)` gives `f_ρ ∈ M_k(N, χ⁻¹)`, and likewise for cusp forms.
* `CuspForm.heckeRingHomCuspCharSpace_conjCharSpace`: `Tₙ (f_ρ) = (Tₙ f)_ρ` on
  `S_k(N, χ)`, and `CuspForm.heckeRingHomCuspCharSpace_conjCharSpace_eq_smul`: the
  conjugate of a `Tₙ`-eigenform is a `Tₙ`-eigenform with the conjugate eigenvalue.

## References

* [T. Miyake, *Modular forms*][miyake1989], §4.6, where the conjugate form is written `f_ρ`.
* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  `W`-operators*, Invent. Math. **48** (1978), 221–243.
-/

public noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped ModularForm MatrixGroups Pointwise

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

namespace TauCeti

namespace UpperHalfPlane

/-- The matrix `J = !![-1, 0; 0, 1]` is its own inverse. -/
@[simp]
lemma J_inv : (J : GL (Fin 2) ℝ)⁻¹ = J :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, J_sq])

/-- Slashing by `J` conjugates the value at the reflected point `J • τ = -conj τ`, in every
weight. -/
lemma slash_J_apply (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) : (f ∣[k] J) τ = starRingEnd ℂ (f (J • τ)) := by
  simp [ModularForm.slash_apply]

/-- The `q`-parameter at the reflected point `J • τ = -conj τ` is the conjugate of the
`q`-parameter at `τ`. -/
lemma conj_qParam_J_smul (h : ℝ) (τ : ℍ) :
    starRingEnd ℂ (Function.Periodic.qParam h (J • τ : ℍ)) = Function.Periodic.qParam h τ := by
  simp only [Function.Periodic.qParam, coe_J_smul, ← Complex.exp_conj, map_div₀, map_mul,
    map_neg, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring_nf

end UpperHalfPlane

open UpperHalfPlane

/-- Membership in `J⁻¹ 𝒢 J`, spelled out as a conjugation condition. -/
lemma mem_conjAct_inv_J_iff {g : GL (Fin 2) ℝ} :
    g ∈ ConjAct.toConjAct J⁻¹ • 𝒢 ↔ J * g * J ∈ 𝒢 := by
  rw [map_inv, 𝒢.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul, J_inv]

/-- A subgroup contained in its conjugate `J⁻¹ 𝒢 J` by the involution `J` is equal to it. -/
lemma conjAct_inv_J_smul_eq_of_le (hJ : 𝒢 ≤ ConjAct.toConjAct J⁻¹ • 𝒢) :
    ConjAct.toConjAct J⁻¹ • 𝒢 = 𝒢 := by
  refine le_antisymm (fun g hg ↦ ?_) hJ
  have h := hJ (mem_conjAct_inv_J_iff.mp hg)
  rw [mem_conjAct_inv_J_iff] at h
  have hJJ : (J : GL (Fin 2) ℝ) * J = 1 := by rw [← sq, J_sq]
  have hg : J * (J * g * J) * J = (J * J) * g * (J * J) := by group
  rwa [hg, hJJ, one_mul, mul_one] at h

/-- A strict period of `𝒢` is a strict period of `J⁻¹ 𝒢 J`: conjugating `!![1, h; 0, 1]` by `J`
gives its inverse `!![1, -h; 0, 1]`. -/
lemma mem_strictPeriods_conjAct_inv_J {h : ℝ} (hΓ : h ∈ 𝒢.strictPeriods) :
    h ∈ (ConjAct.toConjAct J⁻¹ • 𝒢).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, mem_conjAct_inv_J_iff]
  convert 𝒢.inv_mem (Subgroup.mem_strictPeriods_iff.mp hΓ) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Slashing by `J` conjugates the `q`-expansion coefficients.** For a modular form `f` of
weight `k` on `𝒢` and a strict period `h` of `𝒢`, the `q`-expansion of
`f ∣[k] J = conj ∘ f ∘ (τ ↦ -conj τ)` is that of `f` with every coefficient conjugated. -/
theorem qExpansion_slash_J {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒢 k] (f : F)
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) :
    qExpansion h (⇑f ∣[k] J) = PowerSeries.map (starRingEnd ℂ) (qExpansion h f) := by
  have : Fact (IsCusp OnePoint.infty 𝒢) := ⟨𝒢.isCusp_of_mem_strictPeriods hh hΓ⟩
  ext m
  rw [PowerSeries.coeff_map, ← _root_.ModularForm.coe_translate f J]
  refine (ModularFormClass.qExpansion_coeff_unique hh (mem_strictPeriods_conjAct_inv_J hΓ)
    (c := fun m ↦ starRingEnd ℂ ((qExpansion h f).coeff m)) (fun τ ↦ ?_) m).symm
  rw [_root_.ModularForm.coe_translate, slash_J_apply]
  simpa [conj_qParam_J_smul] using
    (Complex.hasSum_conj'.mpr (_root_.ModularForm.hasSum_qExpansion (f := f) hh hΓ (J • τ)))

/-! ### The congruence subgroups -/

end TauCeti

namespace Matrix.SpecialLinearGroup

/-- The `J`-conjugate `!![a, -b; -c, d]` of `!![a, b; c, d] ∈ SL(2, ℤ)`. -/
def conjJ (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    linarith [Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ]⟩

@[simp]
lemma coe_conjJ (γ : SL(2, ℤ)) :
    ((conjJ γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1] := by
  rw [conjJ]

/-- Conjugation by `J` realizes `conjJ`. -/
lemma J_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J * mapGL ℝ γ * UpperHalfPlane.J = mapGL ℝ (conjJ γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

end Matrix.SpecialLinearGroup

namespace TauCeti

open UpperHalfPlane

section Congruence

lemma conjJ_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : conjJ γ ∈ Gamma0 N := by
  simpa [Gamma0_mem] using hγ

lemma conjJ_mem_Gamma1 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) : conjJ γ ∈ Gamma1 N := by
  simpa [Gamma1_mem] using hγ

/-- `conjJ` leaves the lower-right entry, hence the diamond label, alone. -/
lemma Gamma0Map_conjJ {N : ℕ} (γ : ↥(Gamma0 N)) :
    (Gamma0Map N).toHomUnits ⟨conjJ γ, conjJ_mem_Gamma0 γ.2⟩ = (Gamma0Map N).toHomUnits γ := by
  ext
  simp [Gamma0Map_apply]

/-- Conjugation by `J` preserves `Γ₀(N)`, so the conjugate of a form on `Γ₀(N)` is again a
form on `Γ₀(N)`. -/
theorem Gamma0_map_le_conjAct_inv_J (N : ℕ) :
    ((Gamma0 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct J⁻¹ • (Gamma0 N).map (mapGL ℝ) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_conjAct_inv_J_iff, J_mul_mapGL_mul_J]
  exact ⟨_, conjJ_mem_Gamma0 hγ, rfl⟩

/-- Conjugation by `J` preserves `Γ₁(N)`, so the conjugate of a form on `Γ₁(N)` is again a
form on `Γ₁(N)`. -/
theorem Gamma1_map_le_conjAct_inv_J (N : ℕ) :
    ((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct J⁻¹ • (Gamma1 N).map (mapGL ℝ) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_conjAct_inv_J_iff, J_mul_mapGL_mul_J]
  exact ⟨_, conjJ_mem_Gamma1 hγ, rfl⟩

end Congruence

/-! ### Nebentypus -/

section Nebentypus

variable {N : ℕ} {χ : (ZMod N)ˣ →* ℂˣ}

private lemma slash_conj_eq {f : ℍ → ℂ}
    (hf : ∀ g : ↥(Gamma0 N), f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f) (g : ↥(Gamma0 N)) :
    (f ∣[k] J) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ⁻¹ ((Gamma0Map N).toHomUnits g)) : ℂ) • (f ∣[k] J) := by
  have hJg : J * mapGL ℝ (g : SL(2, ℤ)) = mapGL ℝ (conjJ g) * J := by
    rw [← J_mul_mapGL_mul_J, mul_assoc, ← sq, J_sq, mul_one]
  rw [← SlashAction.slash_mul, hJg, SlashAction.slash_mul,
    hf ⟨conjJ g, conjJ_mem_Gamma0 g.2⟩, ModularForm.smul_slash, Gamma0Map_conjJ, sigma_J]
  congr 1
  rw [Complex.conjCAE_apply, ← MulChar.ofUnitHom_coe, ← MulChar.ofUnitHom_coe,
    MulChar.ofUnitHom_inv_eq_star, MulChar.star_apply, RCLike.star_def]

end Nebentypus

end TauCeti

open TauCeti TauCeti.UpperHalfPlane

namespace ModularForm

/-- **The conjugate form** `f_ρ(τ) = conj (f (-conj τ))` of a modular form `f` for `𝒢`, as a
modular form for any `𝒢'` conjugated into `𝒢` by `J = !![-1, 0; 0, 1]`. It is the slash of `f`
by the determinant `-1` matrix `J`, so its `q`-expansion has the complex-conjugate
coefficients (`ModularForm.qExpansion_conj`). -/
def conj (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : ModularForm 𝒢 k) : ModularForm 𝒢' k :=
  _root_.ModularForm.ofLe hJ (_root_.ModularForm.translate f J)

lemma coe_conj (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    ⇑(conj hJ f) = ⇑f ∣[k] J := by
  rw [conj, _root_.ModularForm.coe_ofLe, _root_.ModularForm.coe_translate]

@[simp]
lemma conj_apply (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : ModularForm 𝒢 k) (τ : ℍ) :
    conj hJ f τ = starRingEnd ℂ (f (J • τ)) := by
  rw [coe_conj, slash_J_apply]

/-- The conjugate form is an involution. -/
@[simp]
lemma conj_conj (hJ : 𝒢 ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    conj hJ (conj hJ f) = f := by
  ext τ
  simp [smul_smul, ← sq]

lemma conj_injective (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) :
    Function.Injective (conj (k := k) hJ) := by
  intro f g hfg
  ext τ
  simpa [smul_smul, ← sq] using congrArg (starRingEnd ℂ) (DFunLike.congr_fun hfg (J • τ))

@[simp]
lemma conj_zero (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) : conj hJ (0 : ModularForm 𝒢 k) = 0 := by
  ext τ
  simp

@[simp]
lemma conj_add (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f g : ModularForm 𝒢 k) :
    conj hJ (f + g) = conj hJ f + conj hJ g := by
  ext τ
  simp

@[simp]
lemma conj_smul [𝒢.HasDetOne] [𝒢'.HasDetOne] (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (c : ℂ)
    (f : ModularForm 𝒢 k) : conj hJ (c • f) = starRingEnd ℂ c • conj hJ f := by
  ext τ
  simp

/-- The conjugate form, as a `ℂ`-antilinear map. -/
def conjₗ [𝒢.HasDetOne] [𝒢'.HasDetOne] (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) :
    ModularForm 𝒢 k →ₗ⋆[ℂ] ModularForm 𝒢' k where
  toFun := conj hJ
  map_add' := conj_add hJ
  map_smul' := conj_smul hJ

@[simp]
lemma conjₗ_apply [𝒢.HasDetOne] [𝒢'.HasDetOne] (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢)
    (f : ModularForm 𝒢 k) : conjₗ hJ f = conj hJ f :=
  (rfl)

/-- **The `q`-expansion of the conjugate form has the conjugate coefficients**:
`a_n(f_ρ) = conj (a_n(f))`. -/
theorem qExpansion_conj {h : ℝ} (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods)
    (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    qExpansion h (conj hJ f) = PowerSeries.map (starRingEnd ℂ) (qExpansion h f) := by
  rw [coe_conj, qExpansion_slash_J f hh hΓ]

section Nebentypus

variable {N : ℕ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The conjugate of a form of nebentypus `χ` has nebentypus `χ⁻¹`**: `f_ρ ∈ M_k(N, χ⁻¹)`. -/
theorem conj_mem_modFormCharSpace
    {f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    ModularForm.conj (Gamma1_map_le_conjAct_inv_J N) f ∈ modFormCharSpace k χ⁻¹ := by
  rw [mem_modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [ModularForm.coe_conj]
  exact slash_conj_eq hf g

end Nebentypus

end ModularForm

namespace CuspForm

/-- **The conjugate cusp form** `f_ρ(τ) = conj (f (-conj τ))`, the cusp-form counterpart of
`ModularForm.conj`. -/
def conj (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : CuspForm 𝒢 k) : CuspForm 𝒢' k :=
  _root_.CuspForm.ofLe hJ (_root_.CuspForm.translate f J)

lemma coe_conj (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    ⇑(conj hJ f) = ⇑f ∣[k] J := by
  rw [conj, _root_.CuspForm.coe_ofLe, _root_.CuspForm.coe_translate]

@[simp]
lemma conj_apply (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : CuspForm 𝒢 k) (τ : ℍ) :
    conj hJ f τ = starRingEnd ℂ (f (J • τ)) := by
  rw [coe_conj, slash_J_apply]

/-- The conjugate cusp form is the conjugate of the underlying modular form. -/
@[simp]
lemma coe_conj_toModularForm (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    (conj hJ f : ModularForm 𝒢' k) = ModularForm.conj hJ (f : ModularForm 𝒢 k) := by
  ext τ
  simp

/-- The conjugate cusp form is an involution. -/
@[simp]
lemma conj_conj (hJ : 𝒢 ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    conj hJ (conj hJ f) = f := by
  ext τ
  simp [smul_smul, ← sq]

lemma conj_injective (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) :
    Function.Injective (conj (k := k) hJ) := by
  intro f g hfg
  ext τ
  simpa [smul_smul, ← sq] using congrArg (starRingEnd ℂ) (DFunLike.congr_fun hfg (J • τ))

@[simp]
lemma conj_zero (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) : conj hJ (0 : CuspForm 𝒢 k) = 0 := by
  ext τ
  simp

@[simp]
lemma conj_add (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f g : CuspForm 𝒢 k) :
    conj hJ (f + g) = conj hJ f + conj hJ g := by
  ext τ
  simp

@[simp]
lemma conj_smul [𝒢.HasDetOne] [𝒢'.HasDetOne] (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (c : ℂ)
    (f : CuspForm 𝒢 k) : conj hJ (c • f) = starRingEnd ℂ c • conj hJ f := by
  ext τ
  simp

/-- The conjugate cusp form, as a `ℂ`-antilinear map. -/
def conjₗ [𝒢.HasDetOne] [𝒢'.HasDetOne] (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) :
    CuspForm 𝒢 k →ₗ⋆[ℂ] CuspForm 𝒢' k where
  toFun := conj hJ
  map_add' := conj_add hJ
  map_smul' := conj_smul hJ

@[simp]
lemma conjₗ_apply [𝒢.HasDetOne] [𝒢'.HasDetOne] (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢)
    (f : CuspForm 𝒢 k) : conjₗ hJ f = conj hJ f :=
  (rfl)

/-- **The `q`-expansion of the conjugate cusp form has the conjugate coefficients**. -/
theorem qExpansion_conj {h : ℝ} (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods)
    (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    qExpansion h (conj hJ f) = PowerSeries.map (starRingEnd ℂ) (qExpansion h f) := by
  rw [coe_conj, qExpansion_slash_J f hh hΓ]

/-- **Conjugation commutes with the level-raising operators**: `(V_d f)_ρ = V_d (f_ρ)`, since
the reflection `τ ↦ -conj τ` commutes with `τ ↦ d τ`. -/
theorem conj_levelRaise {𝒢₁ 𝒢₁' : Subgroup (GL (Fin 2) ℝ)} [𝒢'.HasDetOne] [𝒢₁'.HasDetOne]
    {d : ℕ} [NeZero d] (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢)
    (hJ : 𝒢₁' ≤ ConjAct.toConjAct J⁻¹ • 𝒢') (hJ' : 𝒢₁ ≤ ConjAct.toConjAct J⁻¹ • 𝒢)
    (h' : 𝒢₁' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢₁) (f : CuspForm 𝒢 k) :
    conj hJ (TauCeti.CuspForm.levelRaise d h f) =
      TauCeti.CuspForm.levelRaise d h' (conj hJ' f) := by
  ext τ
  have hτ : J • scaleGL d • τ = scaleGL d • J • τ :=
    UpperHalfPlane.ext <| by simp only [coe_J_smul, coe_scaleGL_smul, map_mul, map_natCast]; ring
  simp [hτ]

/-! ### Nebentypus and Hecke operators -/

section Nebentypus

variable {N : ℕ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The conjugate of a cusp form of nebentypus `χ` has nebentypus `χ⁻¹`**:
`f_ρ ∈ S_k(N, χ⁻¹)`. -/
theorem conj_mem_cuspFormCharSpace
    {f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f ∈ cuspFormCharSpace k χ⁻¹ := by
  rw [mem_cuspFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [CuspForm.coe_conj]
  exact slash_conj_eq hf g

variable (k χ) in
/-- The conjugate cusp form as an antilinear equivalence `S_k(N, χ) ≃ S_k(N, χ⁻¹)`. Its inverse is
again `f ↦ f_ρ`, now on `S_k(N, χ⁻¹)`. -/
def conjCharSpace : cuspFormCharSpace k χ ≃ₗ⋆[ℂ] cuspFormCharSpace k χ⁻¹ where
  toFun f := ⟨CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f, conj_mem_cuspFormCharSpace f.2⟩
  map_add' f g := by ext1; simp
  map_smul' c f := by ext1; simp
  invFun f := ⟨CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) f, by
    simpa using conj_mem_cuspFormCharSpace f.2⟩
  left_inv f := by ext1; simp
  right_inv f := by ext1; simp

@[simp]
lemma coe_conjCharSpace_apply (f : cuspFormCharSpace k χ) :
    (CuspForm.conjCharSpace k χ f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) (f : _root_.CuspForm _ k) :=
  (rfl)

@[simp]
lemma coe_conjCharSpace_symm_apply (f : cuspFormCharSpace k χ⁻¹) :
    ((CuspForm.conjCharSpace k χ).symm f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) (f : _root_.CuspForm _ k) :=
  (rfl)

/-- Conjugating twice, first on `S_k(N, χ)` and then on `S_k(N, χ⁻¹)`, gives back the original
form. -/
lemma coe_conjCharSpace_conjCharSpace (f : cuspFormCharSpace k χ) :
    (CuspForm.conjCharSpace k χ⁻¹ (CuspForm.conjCharSpace k χ f) :
      _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f := by
  simp

open HeckeRing.GL2 in
/-- **The conjugate form intertwines the Hecke operators**: for `f ∈ S_k(N, χ)` and `n ≠ 0`,
`T_n (f_ρ) = (T_n f)_ρ`, where on the left `T_n` acts on `S_k(N, χ⁻¹)`. Since the conjugation is
antilinear, the conjugate of a `T_n`-eigenform with eigenvalue `λ` is a `T_n`-eigenform with
eigenvalue `conj λ`. -/
theorem heckeRingHomCuspCharSpace_conjCharSpace [NeZero N] {n : ℕ} (hn : n ≠ 0)
    (f : cuspFormCharSpace k χ) :
    heckeRingHomCuspCharSpace k χ⁻¹ (heckeTCompositeGamma0 N n) (CuspForm.conjCharSpace k χ f) =
      CuspForm.conjCharSpace k χ (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) f) := by
  have h1 := one_mem_strictPeriods_Gamma1_map N
  refine Subtype.ext <| _root_.CuspForm.qExpansion_injective one_pos h1 ?_
  ext m
  simp only [CuspForm.coe_conjCharSpace_apply, CuspForm.qExpansion_conj one_pos h1,
    PowerSeries.coeff_map, qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 hn,
    map_sum, map_mul, map_zpow₀, map_natCast, MulChar.ofUnitHom_inv_eq_star, MulChar.star_apply,
    RCLike.star_def]

open HeckeRing.GL2 in
/-- **The conjugate of a Hecke eigenform is an eigenform with the conjugate eigenvalue**: if
`Tₙ f = λ f` on `S_k(N, χ)`, then `Tₙ f_ρ = conj λ • f_ρ` on `S_k(N, χ⁻¹)`. -/
theorem heckeRingHomCuspCharSpace_conjCharSpace_eq_smul [NeZero N] {n : ℕ}
    (hn : n ≠ 0)
    {f : cuspFormCharSpace k χ} {c : ℂ}
    (hf : heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) f = c • f) :
    heckeRingHomCuspCharSpace k χ⁻¹ (heckeTCompositeGamma0 N n) (CuspForm.conjCharSpace k χ f) =
      starRingEnd ℂ c • CuspForm.conjCharSpace k χ f := by
  rw [heckeRingHomCuspCharSpace_conjCharSpace hn, hf, map_smulₛₗ]

end Nebentypus

end CuspForm
