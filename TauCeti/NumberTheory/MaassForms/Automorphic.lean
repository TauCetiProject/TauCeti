/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Conjugate
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.Fricke.CharacterSpace
public import TauCeti.NumberTheory.ModularForms.Parity

/-!
# Weight-zero automorphy with nebentypus

A Maass form of level `N` and nebentypus `χ` is, before any analytic condition, a function
`f : ℍ → ℂ` with

  `f (γ • z) = χ (d_γ) * f z` for every `γ ∈ Γ₀(N)`,

where `d_γ` is the lower-right entry of `γ`, read modulo `N`, and `χ` is a Dirichlet character
modulo `N` (zero on non-units, so `χ (p) = 0` for `p ∣ N` wherever a formula needs it). This is the
weight-`0` case of the nebentypus relation of holomorphic modular forms: at weight `0` the slash
by an element of `SL(2, ℤ)` has no automorphy factor, so the relation is plain composition. This
file names the relation `IsAutomorphic N χ`, as membership in Tau Ceti's plain-function character
space `TauCeti.functionCharSpace 0 χ` at the unit homomorphism `MulChar.equivToUnitHom χ`, and
proves its algebraic properties. Nothing analytic is assumed: no smoothness, no growth, no
integrability.

The properties are the stability of the relation under the symmetries that later act on Maass
forms, together with the parity constraint:

* **The parity lemma.** `-I ∈ Γ₀(N)` acts trivially on `ℍ` but has lower-right entry `-1`, so an
  automorphic `f` satisfies `f = χ(-1) f`. A nonzero automorphic function therefore forces `χ` to
  be even, and for odd `χ` the only automorphic function is `0`. This is the weight-`0` case of
  `TauCeti.char_neg_one_of_mem_functionCharSpace`.
* **The reflection** `(ι f)(z) = f(-conj z)`, through `UpperHalfPlane.J`. Conjugation by
  `J = diag(-1, 1)` preserves `Γ₀(N)` and the lower-right entry, so `ι` preserves the relation
  with the same `χ`. (Mathlib's slash by `J` also conjugates the values, `f ∣[k] J = conj ∘ ι f`,
  which is why `ι` is composition with `J` here and not the slash.)
* **The Fricke involution** `z ↦ -1 / (N z)`, through `TauCeti.frickeGL`. It normalizes `Γ₀(N)`
  and inverts the diamond label, so composition with it carries `χ` to `χ⁻¹`, the complex
  conjugate character (`MulChar.star_apply'`).
* **Dilation** `z ↦ d z`, through `TauCeti.scaleGL`. For `d * M ∣ N` it carries an automorphic
  function of level `M` and nebentypus `χ'` to one of level `N` and nebentypus
  `DirichletCharacter.changeLevel χ'`.

The last two are composition, not the weight-`0` slash: Mathlib's slash by a matrix of
determinant `D > 0` carries the factor `D⁻¹` at weight `0`, which plays no role for a relation
that is linear in `f`. The general-weight transports on `functionCharSpace` are
`TauCeti.slash_frickeGL_mem_functionCharSpace` and
`TauCeti.slash_scaleGL_mem_functionCharSpace_of_dvd`.

## Main definitions

* `TauCeti.MaassForms.IsAutomorphic N χ f`: weight-`0` automorphy for `Γ₀(N)` with nebentypus `χ`.
* `TauCeti.MaassForms.reflection f`: the reflected function `z ↦ f (-conj z)`.

## Main results

* `TauCeti.MaassForms.isAutomorphic_iff`: the relation entrywise,
  `f (γ • z) = χ (γ 1 1) * f z` for `γ ∈ Γ₀(N)`.
* `TauCeti.MaassForms.IsAutomorphic.apply_smul_smul_of_mul_eq`: transport of the relation through
  a conjugation `g γ = γ' g` in `GL(2, ℝ)` with `γ' ∈ Γ₀(N)`.
* `TauCeti.MaassForms.isAutomorphic_one_iff`, `TauCeti.MaassForms.isAutomorphic_const`: at
  trivial character the relation is `Γ₀(N)`-invariance, and constants are automorphic.
* `TauCeti.MaassForms.isAutomorphic_const_iff`: a nonzero constant is automorphic exactly for the
  trivial character.
* `TauCeti.MaassForms.IsAutomorphic.apply_intCast_vadd`: automorphic functions have period `1`.
* `TauCeti.MaassForms.IsAutomorphic.even`, `TauCeti.MaassForms.IsAutomorphic.eq_zero_of_odd`: the
  parity lemma.
* `TauCeti.MaassForms.isAutomorphic_reflection_iff`: `ι` preserves the relation.
* `TauCeti.MaassForms.IsAutomorphic.comp_frickeGL_smul`,
  `TauCeti.MaassForms.isAutomorphic_comp_frickeGL_smul_iff`: the Fricke involution exchanges `χ`
  and `χ⁻¹`.
* `TauCeti.MaassForms.IsAutomorphic.comp_scaleGL_smul`: dilation raises the level, and its case
  `d = 1`, `TauCeti.MaassForms.IsAutomorphic.changeLevel`.

## References

* H. Iwaniec, *Topics in Classical Automorphic Forms*, Graduate Studies in Mathematics **17**,
  AMS, 1997, Chapter 2 (automorphic functions with a multiplier system on `Γ₀(N)`).
* A. R. Booker, M. Lee and A. Strömbergsson, *Twist-minimal trace formulas and the Selberg
  eigenvalue conjecture*, J. London Math. Soc. **102** (2020), arXiv:1803.06016, §1.1 (Maass
  forms of level `N` with character, the reflection and the dilation `f(d ·)`).
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ModularGroup

open scoped MatrixGroups ModularForm

namespace TauCeti.MaassForms

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f g : ℍ → ℂ}

/-! ### The automorphy relation -/

/-- **Weight-zero automorphy with nebentypus.** `IsAutomorphic N χ f` says that
`f (γ • z) = χ (d_γ) * f z` for every `γ ∈ Γ₀(N)`, where `d_γ` is the lower-right entry of `γ`
modulo `N` (`isAutomorphic_iff`). It is membership in the plain-function character space
`functionCharSpace 0` at the unit homomorphism of `χ`, so no analytic condition is imposed. -/
def IsAutomorphic (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  f ∈ functionCharSpace 0 (MulChar.equivToUnitHom χ)

/-- `IsAutomorphic` is membership in the weight-`0` character space, by definition. -/
theorem isAutomorphic_iff_mem_functionCharSpace :
    IsAutomorphic N χ f ↔ f ∈ functionCharSpace 0 (MulChar.equivToUnitHom χ) :=
  Iff.rfl

/-- **The automorphy relation, entrywise**: `f` is automorphic for `Γ₀(N)` with nebentypus `χ`
exactly when `f (γ • z) = χ (γ 1 1) * f z` for every `γ ∈ Γ₀(N)` and every `z ∈ ℍ`. -/
theorem isAutomorphic_iff :
    IsAutomorphic N χ f ↔
      ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ z : ℍ, f (γ • z) = χ (γ 1 1) * f z := by
  -- at weight `0` the slash by `γ ∈ SL(2, ℤ)` is composition with `γ`, with no automorphy factor
  have hslash (γ : SL(2, ℤ)) (z : ℍ) : (f ∣[(0 : ℤ)] mapGL ℝ γ) z = f (γ • z) := by
    have h := ModularForm.SL_slash_apply (f := f) (k := 0) γ z
    rwa [neg_zero, zpow_zero, mul_one] at h
  -- the unit homomorphism of `χ` at the diamond label of `γ` is `χ` at its lower-right entry
  have hχ (γ : ↥(Gamma0 N)) : ((MulChar.equivToUnitHom χ ((Gamma0Map N).toHomUnits γ) : ℂˣ) : ℂ) =
      χ ((γ : SL(2, ℤ)) 1 1) := by
    simp [Gamma0Map_apply]
  refine (mem_functionCharSpace_iff _ _ _).trans ⟨fun h γ hγ z ↦ ?_, fun h γ ↦ funext fun z ↦ ?_⟩
  · have := congr_fun (h ⟨γ, hγ⟩) z
    rwa [hslash, Pi.smul_apply, smul_eq_mul, hχ] at this
  · rw [hslash, Pi.smul_apply, smul_eq_mul, hχ]
    exact h γ γ.property z

/-- **The automorphy relation at one matrix**: for `γ ∈ Γ₀(N)`, `f (γ • z) = χ (γ 1 1) * f z`. -/
theorem IsAutomorphic.apply_smul (hf : IsAutomorphic N χ f) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (z : ℍ) : f (γ • z) = χ (γ 1 1) * f z :=
  isAutomorphic_iff.mp hf γ hγ z

/-- **Transport of the automorphy relation through a conjugation**: if `g γ = γ' g` in
`GL(2, ℝ)` with `γ' ∈ Γ₀(N)`, then `f (g • γ • z) = χ (γ' 1 1) * f (g • z)`. -/
theorem IsAutomorphic.apply_smul_smul_of_mul_eq (hf : IsAutomorphic N χ f)
    {g : GL (Fin 2) ℝ} {γ γ' : SL(2, ℤ)} (hg : g * mapGL ℝ γ = mapGL ℝ γ' * g)
    (hγ' : γ' ∈ Gamma0 N) (z : ℍ) :
    f (g • γ • z) = χ (γ' 1 1) * f (g • z) := by
  rw [← mapGL_smul (R := ℤ) γ, ← mul_smul, hg, mul_smul, mapGL_smul, hf.apply_smul hγ']

/-- The zero function is automorphic for every level and nebentypus. -/
theorem isAutomorphic_zero : IsAutomorphic N χ 0 :=
  Submodule.zero_mem _

/-- Automorphic functions with the same level and nebentypus are closed under addition. -/
theorem IsAutomorphic.add (hf : IsAutomorphic N χ f) (hg : IsAutomorphic N χ g) :
    IsAutomorphic N χ (f + g) :=
  Submodule.add_mem _ hf hg

/-- Automorphic functions are closed under complex scalars. -/
theorem IsAutomorphic.const_smul (hf : IsAutomorphic N χ f) (c : ℂ) :
    IsAutomorphic N χ (c • f) :=
  Submodule.smul_mem _ c hf

/-- Automorphic functions have period `1`: the translation `T ^ n` lies in `Γ₀(N)` with
lower-right entry `1`. -/
theorem IsAutomorphic.apply_intCast_vadd (hf : IsAutomorphic N χ f) (n : ℤ) (z : ℍ) :
    f ((n : ℝ) +ᵥ z) = f z := by
  rw [← modular_T_zpow_smul, hf.apply_smul (Gamma1_le_Gamma0 N (T_zpow_mem_Gamma1 N n)),
    coe_T_zpow]
  simp

/-! ### Trivial character -/

/-- **Trivial character.** With trivial nebentypus, automorphy is invariance under `Γ₀(N)`. -/
theorem isAutomorphic_one_iff :
    IsAutomorphic N 1 f ↔ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ z : ℍ, f (γ • z) = f z := by
  refine isAutomorphic_iff.trans (forall₂_congr fun γ hγ ↦ forall_congr' fun z ↦ ?_)
  rw [MulChar.one_apply (isUnit_intCast_apply_one_one_of_mem_Gamma0 hγ), one_mul]

/-- Constants are automorphic with trivial nebentypus. -/
theorem isAutomorphic_const (c : ℂ) : IsAutomorphic N 1 (fun _ ↦ c) :=
  isAutomorphic_one_iff.mpr fun _ _ _ ↦ rfl

/-- **Automorphic constants.** A constant function is automorphic for `Γ₀(N)` with nebentypus
`χ` exactly when it is zero or `χ` is trivial: every unit modulo `N` is the lower-right entry of
a matrix in `Γ₀(N)`, so a nonzero constant forces `χ` to be `1` on every unit. -/
theorem isAutomorphic_const_iff (c : ℂ) :
    IsAutomorphic N χ (fun _ ↦ c) ↔ c = 0 ∨ χ = 1 := by
  refine ⟨fun h ↦ or_iff_not_imp_left.mpr fun hc ↦ MulChar.ext fun u ↦ ?_, ?_⟩
  · obtain ⟨γ, rfl⟩ := Gamma0Map_toHomUnits_surjective u
    have hγ := h.apply_smul γ.property UpperHalfPlane.I
    rw [MulChar.one_apply_coe, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    exact (mul_eq_right₀ hc).mp hγ.symm
  · rintro (rfl | rfl)
    · exact isAutomorphic_iff.mpr fun _ _ _ ↦ (mul_zero _).symm
    · exact isAutomorphic_const c

/-! ### The parity lemma -/

/-- On an automorphic function, `χ (-1)` acts trivially: `-I ∈ Γ₀(N)` fixes every point of `ℍ`
and has lower-right entry `-1`. -/
theorem IsAutomorphic.char_neg_one_smul (hf : IsAutomorphic N χ f) : χ (-1) • f = f := by
  simpa using char_neg_one_smul_of_mem_functionCharSpace hf

/-- **The parity lemma.** A nonzero automorphic function forces the nebentypus to be even. -/
theorem IsAutomorphic.even (hf : IsAutomorphic N χ f) (hf0 : f ≠ 0) : χ.Even := by
  simpa [DirichletCharacter.Even] using char_neg_one_of_mem_functionCharSpace hf hf0

/-- **The parity lemma.** For an odd nebentypus the only automorphic function is `0`. -/
theorem IsAutomorphic.eq_zero_of_odd (hf : IsAutomorphic N χ f) (hχ : χ.Odd) : f = 0 :=
  not_not.mp fun hf0 ↦ DirichletCharacter.Even.not_odd χ (hf.even hf0) hχ

/-! ### The reflection `z ↦ -conj z` -/

/-- **The reflection** `(ι f)(z) = f (-conj z)`, composition with the orientation-reversing
involution `UpperHalfPlane.J`. It is plain composition, without the complex conjugation of values
that Mathlib's slash by `J` carries. -/
noncomputable def reflection {α : Type*} (f : ℍ → α) : ℍ → α :=
  fun z ↦ f (J • z)

@[simp]
theorem reflection_apply {α : Type*} (f : ℍ → α) (z : ℍ) : reflection f z = f (J • z) :=
  (rfl)

/-- The reflection is an involution. -/
@[simp]
theorem reflection_reflection {α : Type*} (f : ℍ → α) : reflection (reflection f) = f := by
  funext z
  rw [reflection_apply, reflection_apply, J_smul_J_smul]

/-- The reflection is an involution, in the form `Function.Involutive` consumes. -/
theorem reflection_involutive {α : Type*} : Function.Involutive (reflection (α := α)) :=
  reflection_reflection

/-- **The reflection preserves automorphy**, with the same nebentypus: conjugation by
`J = diag(-1, 1)` preserves `Γ₀(N)` and the lower-right entry (`conjJ`). -/
theorem IsAutomorphic.reflection (hf : IsAutomorphic N χ f) :
    IsAutomorphic N χ (reflection f) := by
  refine isAutomorphic_iff.mpr fun γ hγ z ↦ ?_
  rw [reflection_apply, reflection_apply,
    hf.apply_smul_smul_of_mul_eq (J_mul_mapGL γ) (conjJ_mem_Gamma0 hγ)]
  simp

/-- A function is automorphic exactly when its reflection is. -/
@[simp]
theorem isAutomorphic_reflection_iff : IsAutomorphic N χ (reflection f) ↔ IsAutomorphic N χ f :=
  ⟨fun h ↦ reflection_reflection f ▸ h.reflection, IsAutomorphic.reflection⟩

/-! ### The Fricke involution -/

/-- **The Fricke involution conjugates the nebentypus**: if `f` is automorphic for `Γ₀(N)` with
nebentypus `χ`, then `z ↦ f (-1 / (N z))` is automorphic with nebentypus `χ⁻¹`, the complex
conjugate character. -/
theorem IsAutomorphic.comp_frickeGL_smul [NeZero N] (hf : IsAutomorphic N χ f) :
    IsAutomorphic N χ⁻¹ (fun z ↦ f (frickeGL ℝ N • z)) := by
  have hχ : MulChar.equivToUnitHom χ⁻¹ = (MulChar.equivToUnitHom χ)⁻¹ := by
    simpa using map_inv MulChar.mulEquivToUnitHom χ
  -- at weight `0` the slash by `W` is composition with `W` divided by `det W = N`
  have hW : (fun z ↦ f (frickeGL ℝ N • z)) = (N : ℂ) • (f ∣[(0 : ℤ)] frickeGL ℝ N) := by
    funext z
    rw [Pi.smul_apply, ModularForm.slash_apply_of_det_pos 0 val_det_frickeGL_pos,
      val_det_frickeGL, smul_eq_mul]
    simp [mul_left_comm (N : ℂ), NeZero.ne N]
  rw [isAutomorphic_iff_mem_functionCharSpace, hχ, hW]
  exact Submodule.smul_mem _ _ (slash_frickeGL_mem_functionCharSpace hf)

/-- **The Fricke involution exchanges `χ` and `χ⁻¹`**: `z ↦ f (-1 / (N z))` is automorphic with
nebentypus `χ⁻¹` exactly when `f` is automorphic with nebentypus `χ`. -/
theorem isAutomorphic_comp_frickeGL_smul_iff [NeZero N] :
    IsAutomorphic N χ⁻¹ (fun z ↦ f (frickeGL ℝ N • z)) ↔ IsAutomorphic N χ f := by
  refine ⟨fun h ↦ ?_, IsAutomorphic.comp_frickeGL_smul⟩
  simpa only [inv_inv, frickeGL_smul_frickeGL_smul] using h.comp_frickeGL_smul

/-! ### Dilation -/

/-- **Dilation raises the level.** If `f` is automorphic for `Γ₀(M)` with nebentypus `χ`, and
`d * M ∣ N`, then `z ↦ f (d z)` is automorphic for `Γ₀(N)` with nebentypus `χ` changed to level
`N`. -/
theorem IsAutomorphic.comp_scaleGL_smul {M d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ M}
    (hdvd : d * M ∣ N) (hf : IsAutomorphic M χ f) :
    IsAutomorphic N (DirichletCharacter.changeLevel ((Dvd.intro_left d rfl).trans hdvd) χ)
      (fun z ↦ f (scaleGL d • z)) := by
  rw [isAutomorphic_iff_mem_functionCharSpace, ← smul_slash_scaleGL_eq,
    ← MulChar.toUnitHom_eq, DirichletCharacter.changeLevel_toUnitHom, MulChar.toUnitHom_eq]
  exact Submodule.smul_mem _ _ (slash_scaleGL_mem_functionCharSpace_of_dvd hdvd hf)

/-- **Level raising**: an automorphic function for `Γ₀(M)` with nebentypus `χ` is automorphic for
`Γ₀(N)` with nebentypus `χ` changed to level `N`, for every multiple `N` of `M`. -/
theorem IsAutomorphic.changeLevel {M : ℕ} {χ : DirichletCharacter ℂ M}
    (hf : IsAutomorphic M χ f) (h : M ∣ N) :
    IsAutomorphic N (DirichletCharacter.changeLevel h χ) f := by
  simpa only [scaleGL_one, one_smul] using
    IsAutomorphic.comp_scaleGL_smul (d := 1) (by simpa using h) hf

end TauCeti.MaassForms
