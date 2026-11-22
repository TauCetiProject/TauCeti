/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Conjugate
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.Fricke.Operator

/-!
# Weight-zero automorphy with a nebentypus character

A function `f : ℍ → ℂ` is *automorphic for `Γ₀(N)` with character `χ`* when
`f(γ z) = χ(d_γ) f(z)` for every `γ ∈ Γ₀(N)`, where `d_γ` is the lower-right entry of `γ` and
`χ` is a Dirichlet character modulo `N`. This is the transformation law of a Maass form of
weight `0` with nebentypus `χ`, imposed on an arbitrary function: no smoothness, growth or
eigenfunction condition is part of it.

The predicate `IsAutomorphic N χ f` is membership in Tau Ceti's `functionCharSpace` at weight `0`,
with `χ` read as a unit homomorphism through `MulChar.equivToUnitHom`; this is the nebentypus law
that `mem_modFormCharSpace_iff_nebentypus` characterizes on modular forms, so on the underlying
function of a weight-`0` modular form of level `Γ₁(N)` the two notions agree by
`coe_mem_functionCharSpace_iff`. At weight `0` the slash by a determinant-one matrix carries no
automorphy factor, and `isAutomorphic_iff` restates the predicate as the pointwise law above.

The file proves the closure properties that the later theory of Maass forms relies on:

* the **parity lemma** (`IsAutomorphic.even_of_ne_zero`, `IsAutomorphic.eq_zero_of_odd`): `-I`
  lies in `Γ₀(N)` and acts trivially on `ℍ`, so `f = χ(-1) f`, and a nonzero automorphic function
  forces `χ` to be even;
* invariance under integral translations (`IsAutomorphic.apply_intCast_vadd`), since
  `T ∈ Γ₀(N)` has lower-right entry `1`;
* the constant functions (`isAutomorphic_const_iff`): a nonzero constant is automorphic exactly
  for the trivial character, because every residue unit is the lower-right entry of some
  element of `Γ₀(N)`;
* the **reflection** `z ↦ -conj z`, the action of `UpperHalfPlane.J`, which preserves the character
  (`isAutomorphic_comp_J_smul_iff`), because conjugation by `J` preserves `Γ₀(N)` and the
  lower-right entry;
* the **Fricke involution** `z ↦ -1/(Nz)`, the action of `frickeGL ℝ N`, which replaces `χ` by
  `χ⁻¹` (`isAutomorphic_comp_frickeGL_smul_iff`), because conjugation by the Fricke matrix
  exchanges the two diagonal entries, which are mutually inverse modulo `N`;
* the **dilation** `z ↦ d z`, the action of `scaleGL d`, which carries the character `χ` modulo
  `M` to its lift modulo `N` whenever `d * M ∣ N` (`IsAutomorphic.comp_scaleGL_smul`), and its
  case `d = 1`, raising the level (`IsAutomorphic.changeLevel`).

The Fricke and reflection operators act by plain composition with the Möbius action; Mathlib's
weight-`0` slash would instead multiply by `|det|⁻¹` and, for `J`, conjugate the values.

## References

* A. R. Booker, M. Lee and A. Strömbergsson, *Twist-minimal trace formulas and the Selberg
  eigenvalue conjecture*, J. London Math. Soc. (2) 102 (2020); arXiv:1803.06016, §1.1.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.1 (the parity remark
  following the definition of `M_k(N, χ)`).
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti.MaassForms

/-- A function `f : ℍ → ℂ` is **automorphic for `Γ₀(N)` with character `χ`** when
`f(γ z) = χ(d_γ) f(z)` for every `γ ∈ Γ₀(N)`, with `d_γ` the lower-right entry of `γ`
(`isAutomorphic_iff`). It is the weight-`0` member of Tau Ceti's nebentypus function spaces
`functionCharSpace`, with `χ` read as a homomorphism on residue units. -/
public def IsAutomorphic (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  f ∈ functionCharSpace 0 (MulChar.equivToUnitHom χ)

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}

/-- `IsAutomorphic` is membership in the weight-`0` nebentypus function space. -/
public theorem isAutomorphic_iff_mem_functionCharSpace :
    IsAutomorphic N χ f ↔ f ∈ functionCharSpace 0 (MulChar.equivToUnitHom χ) :=
  Iff.rfl

/-- **The automorphy law**: `f` is automorphic for `Γ₀(N)` with character `χ` exactly when
`f(γ z) = χ(d) f(z)` for every `γ = !![a, b; c, d] ∈ Γ₀(N)` and every `z ∈ ℍ`. -/
public theorem isAutomorphic_iff :
    IsAutomorphic N χ f ↔
      ∀ γ ∈ Gamma0 N, ∀ z : ℍ, f (γ • z) = χ ((γ 1 1 : ℤ) : ZMod N) * f z := by
  rw [isAutomorphic_iff_mem_functionCharSpace, mem_functionCharSpace_iff]
  -- at weight `0` the slash by a determinant-one matrix is composition with its action
  have hslash (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] mapGL ℝ γ = fun z ↦ f (γ • z) := by
    ext z
    rw [ModularForm.slash_apply, σ_mapGL_real_eq_refl, ContinuousAlgEquiv.refl_apply,
      Matrix.SpecialLinearGroup.mapGL_smul]
    simp
  simp only [hslash, funext_iff, Pi.smul_apply, smul_eq_mul, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, Gamma0Map_apply, Subtype.forall]

/-- The automorphy law of an automorphic function at one matrix `γ = !![a, b; c, d] ∈ Γ₀(N)`:
`f(γ z) = χ(d) f(z)`. -/
public theorem IsAutomorphic.apply_smul (hf : IsAutomorphic N χ f) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (z : ℍ) : f (γ • z) = χ ((γ 1 1 : ℤ) : ZMod N) * f z :=
  isAutomorphic_iff.mp hf γ hγ z

/-- The zero function is automorphic for every character. -/
@[simp]
public theorem isAutomorphic_zero : IsAutomorphic N χ 0 :=
  (functionCharSpace 0 _).zero_mem

/-- Automorphic functions with a common character are closed under addition. -/
public theorem IsAutomorphic.add {g : ℍ → ℂ} (hf : IsAutomorphic N χ f)
    (hg : IsAutomorphic N χ g) : IsAutomorphic N χ (f + g) :=
  (functionCharSpace 0 _).add_mem hf hg

/-- Automorphic functions with a common character are closed under complex scalars. -/
public theorem IsAutomorphic.const_smul (c : ℂ) (hf : IsAutomorphic N χ f) :
    IsAutomorphic N χ (c • f) :=
  (functionCharSpace 0 _).smul_mem c hf

/-- **The automorphy law for the trivial character** is plain invariance under `Γ₀(N)`. -/
public theorem isAutomorphic_one_iff :
    IsAutomorphic N 1 f ↔ ∀ γ ∈ Gamma0 N, ∀ z : ℍ, f (γ • z) = f z := by
  refine isAutomorphic_iff.trans (forall₂_congr fun γ hγ ↦ forall_congr' fun z ↦ ?_)
  rw [MulChar.one_apply (IsUnit.of_mul_eq_one_right _
    (intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγ)), one_mul]

/-! ### The parity lemma -/

/-- An automorphic function is fixed by the scalar `χ(-1)`, since `-I ∈ Γ₀(N)` acts trivially
on `ℍ` and has lower-right entry `-1`. -/
public theorem IsAutomorphic.char_neg_one_mul_apply (hf : IsAutomorphic N χ f) (z : ℍ) :
    χ (-1) * f z = f z := by
  have h := hf.apply_smul neg_one_mem_Gamma0 z
  rw [ModularGroup.SL_neg_smul, one_smul] at h
  simpa using h.symm

/-- **The parity lemma**: a nonzero automorphic function for `Γ₀(N)` with character `χ` forces
`χ` to be even, `χ(-1) = 1`. -/
public theorem IsAutomorphic.even_of_ne_zero (hf : IsAutomorphic N χ f) (h : f ≠ 0) :
    χ.Even := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp h
  exact mul_right_cancel₀ hz ((hf.char_neg_one_mul_apply z).trans (one_mul _).symm)

/-- **The parity lemma, as an emptiness criterion**: for an odd character `χ` the only
automorphic function for `Γ₀(N)` with character `χ` is `0`. -/
public theorem IsAutomorphic.eq_zero_of_odd (hf : IsAutomorphic N χ f) (hχ : χ.Odd) : f = 0 :=
  by_contra fun h ↦ DirichletCharacter.Odd.not_even χ hχ (hf.even_of_ne_zero h)

/-! ### Translations and constants -/

/-- An automorphic function is invariant under every integral translation `z ↦ z + n`: the
translation `T ^ n` lies in `Γ₀(N)` with lower-right entry `1`. -/
public theorem IsAutomorphic.apply_intCast_vadd (hf : IsAutomorphic N χ f) (n : ℤ) (z : ℍ) :
    f ((n : ℝ) +ᵥ z) = f z := by
  have hT : ModularGroup.T ^ n ∈ Gamma0 N := by simp [Gamma0_mem, ModularGroup.coe_T_zpow]
  have h := hf.apply_smul hT z
  rw [modular_T_zpow_smul, ModularGroup.coe_T_zpow] at h
  simpa using h

/-- **Automorphic constants.** A constant function is automorphic for `Γ₀(N)` with character
`χ` exactly when it is zero or `χ` is trivial: every unit modulo `N` is the lower-right entry of
a matrix in `Γ₀(N)`, so a nonzero constant forces `χ` to be `1` on every unit. -/
public theorem isAutomorphic_const_iff (c : ℂ) :
    IsAutomorphic N χ (fun _ ↦ c) ↔ c = 0 ∨ χ = 1 := by
  refine ⟨fun h ↦ or_iff_not_imp_left.mpr fun hc ↦ MulChar.ext fun u ↦ ?_, ?_⟩
  · obtain ⟨γ, rfl⟩ := Gamma0Map_toHomUnits_surjective u
    have hγ := h.apply_smul γ.property UpperHalfPlane.I
    rw [MulChar.one_apply_coe, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    exact (mul_eq_right₀ hc).mp hγ.symm
  · rintro (rfl | rfl)
    · exact isAutomorphic_iff.mpr fun _ _ _ ↦ (mul_zero _).symm
    · exact isAutomorphic_one_iff.mpr fun _ _ _ ↦ rfl

/-! ### The reflection `z ↦ -conj z` -/

/-- **The reflection preserves automorphy**: if `f` is automorphic for `Γ₀(N)` with character
`χ`, so is `z ↦ f(-conj z)`, the composition with the action of `J = diag(-1, 1)`. -/
public theorem IsAutomorphic.comp_J_smul (hf : IsAutomorphic N χ f) :
    IsAutomorphic N χ (fun z ↦ f (J • z)) := by
  refine isAutomorphic_iff.mpr fun γ hγ z ↦ ?_
  rw [← Matrix.SpecialLinearGroup.mapGL_smul (R := ℤ) γ,
    ← mul_smul, J_mul_mapGL, mul_smul, Matrix.SpecialLinearGroup.mapGL_smul,
    hf.apply_smul (conjJ_mem_Gamma0 hγ)]
  simp

/-- **Automorphy is invariant under the reflection** `z ↦ -conj z`: the reflection preserves the
character, and it is an involution. -/
public theorem isAutomorphic_comp_J_smul_iff :
    IsAutomorphic N χ (fun z ↦ f (J • z)) ↔ IsAutomorphic N χ f :=
  ⟨fun h ↦ by simpa only [J_smul_J_smul] using h.comp_J_smul, IsAutomorphic.comp_J_smul⟩

/-! ### The Fricke involution `z ↦ -1/(Nz)` -/

section Fricke

variable [NeZero N]

/-- **The Fricke involution conjugates the character**: if `f` is automorphic for `Γ₀(N)` with
character `χ`, then `z ↦ f(-1/(Nz))`, the composition with the action of the Fricke matrix
`W = !![0, -1; N, 0]`, is automorphic with character `χ⁻¹`. -/
public theorem IsAutomorphic.comp_frickeGL_smul (hf : IsAutomorphic N χ f) :
    IsAutomorphic N χ⁻¹ (fun z ↦ f (frickeGL ℝ N • z)) := by
  refine isAutomorphic_iff.mpr fun γ hγ z ↦ ?_
  rw [← Matrix.SpecialLinearGroup.mapGL_smul (R := ℤ) γ,
    ← mul_smul, frickeGL_mul_mapGL ℝ ⟨γ, hγ⟩, mul_smul, Matrix.SpecialLinearGroup.mapGL_smul,
    hf.apply_smul (frickeConjSL_mem_Gamma0 ⟨γ, hγ⟩)]
  congr 1
  -- the conjugate has lower-right entry `a`, the inverse of `d` modulo `N`
  have h : χ ((γ 0 0 : ℤ) : ZMod N) * χ ((γ 1 1 : ℤ) : ZMod N) = 1 := by
    rw [← map_mul, intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγ, map_one]
  simpa [MulChar.inv_apply_eq_inv'] using eq_inv_of_mul_eq_one_left h

/-- **The Fricke involution exchanges `χ` and `χ⁻¹`**: `z ↦ f(-1/(Nz))` is automorphic for
`Γ₀(N)` with character `χ⁻¹` exactly when `f` is automorphic with character `χ`. -/
public theorem isAutomorphic_comp_frickeGL_smul_iff :
    IsAutomorphic N χ⁻¹ (fun z ↦ f (frickeGL ℝ N • z)) ↔ IsAutomorphic N χ f := by
  refine ⟨fun h ↦ ?_, IsAutomorphic.comp_frickeGL_smul⟩
  simpa only [inv_inv, frickeGL_smul_frickeGL_smul] using h.comp_frickeGL_smul

end Fricke

/-! ### Dilations and level raising -/

/-- **Dilation raises the level**: if `f` is automorphic for `Γ₀(M)` with character `χ` and
`d * M ∣ N`, then `z ↦ f(d z)`, the composition with the action of `diag(d, 1)`, is automorphic
for `Γ₀(N)` with the lift of `χ` to modulus `N`. -/
public theorem IsAutomorphic.comp_scaleGL_smul {M d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ M}
    (hf : IsAutomorphic M χ f) (h : d * M ∣ N) :
    IsAutomorphic N (DirichletCharacter.changeLevel ((Dvd.intro_left d rfl).trans h) χ)
      (fun z ↦ f (scaleGL d • z)) := by
  refine isAutomorphic_iff.mpr fun γ hγ z ↦ ?_
  obtain ⟨c, hc, hm, -⟩ := exists_conjScale_mem_Gamma0_of_dvd d M N h ⟨γ, hγ⟩
  have hconj : scaleGL d * mapGL ℝ γ = mapGL ℝ (conjScale d γ c hc) * scaleGL d :=
    mul_inv_eq_iff_eq_mul.mp (mapGL_conjScale γ c hc)
  rw [← Matrix.SpecialLinearGroup.mapGL_smul (R := ℤ) γ,
    ← mul_smul, hconj, mul_smul, Matrix.SpecialLinearGroup.mapGL_smul, hf.apply_smul hm,
    conjScale_apply_one_one]
  congr 1
  -- the lower-right entry is a unit modulo `N`, whose reduction modulo `M` is read by `χ`
  have hu := IsUnit.of_mul_eq_one_right _
    (intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγ)
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu.unit_spec,
    ZMod.cast_intCast ((Dvd.intro_left d rfl).trans h)]

/-- **Level raising**: an automorphic function for `Γ₀(M)` with character `χ` is automorphic
for `Γ₀(N)` with the lift of `χ`, for every multiple `N` of `M`. -/
public theorem IsAutomorphic.changeLevel {M : ℕ} {χ : DirichletCharacter ℂ M}
    (hf : IsAutomorphic M χ f) (h : M ∣ N) :
    IsAutomorphic N (DirichletCharacter.changeLevel h χ) f := by
  simpa only [scaleGL_one, one_smul] using hf.comp_scaleGL_smul (d := 1) (by simpa using h)

end TauCeti.MaassForms
