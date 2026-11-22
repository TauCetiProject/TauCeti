/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Primitive

/-!
# Primitive ray class characters of `ℚ` and primitive Dirichlet characters

Bundled primitive ray class characters `TauCeti.LFunctions.PrimitiveRayClassCharacter ℚ` are in
canonical bijection (`TauCeti.LFunctions.PrimitiveRayClassCharacter.ratEquiv`) with primitive
complex Dirichlet characters `(N : ℕ+) × {χ : DirichletCharacter ℂ N // χ.IsPrimitive}`. Even
primitive characters correspond to finite moduli `(N)` without the real place, and odd primitive
characters correspond to `(N)·∞`.

## Main definitions

* `TauCeti.LFunctions.PrimitiveRayClassCharacter.toDirichletCharacter`: the primitive Dirichlet
  character attached to a bundled primitive ray class character of `ℚ`.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.ofDirichletCharacter`: the bundled primitive ray
  class character of `ℚ` underlying any complex Dirichlet character.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.ratEquiv`: equivalence between
  `PrimitiveRayClassCharacter ℚ` and `(N : ℕ+) × {χ : DirichletCharacter ℂ N // χ.IsPrimitive}`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
-/

public section
noncomputable section

open DirichletCharacter NumberField
open scoped NumberField

namespace TauCeti.LFunctions.PrimitiveRayClassCharacter

open GlobalNumberFields

/-- **The primitive Dirichlet character attached to a bundled primitive ray class character of
`ℚ`**, of level `Ideal.absNorm ψ.conductor.finitePart`. -/
def toDirichletCharacter (ψ : PrimitiveRayClassCharacter ℚ) :
    DirichletCharacter ℂ (Ideal.absNorm ψ.conductor.finitePart) :=
  ψ.character.toDirichletCharacter

theorem toDirichletCharacter_def (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.toDirichletCharacter = ψ.character.toDirichletCharacter := (rfl)

/-- The Dirichlet character of a primitive ray class character of `ℚ` is primitive. -/
theorem isPrimitive_toDirichletCharacter (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.toDirichletCharacter.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, toDirichletCharacter_def,
    RayClassCharacter.conductor_toDirichletCharacter, ψ.conductor_character]

@[simp]
theorem toDirichletCharacter_eq_one_iff (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.toDirichletCharacter = 1 ↔ ψ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_one _⟩
  have hchar : ψ.character = 1 :=
    (RayClassCharacter.toDirichletCharacter_eq_one_iff ψ.character).mp h
  rw [← of_character ψ, hchar, of_one]

/-- Along `Ideal.absNorm (of η).conductor.finitePart = η.toDirichletCharacter.conductor`,
`(of η).toDirichletCharacter` is `η.toDirichletCharacter.primitiveCharacter`. -/
theorem changeLevel_toDirichletCharacter_of {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) :
    changeLevel (dvd_of_eq (by rw [conductor_of, RayClassCharacter.conductor_toDirichletCharacter]))
      (of η).toDirichletCharacter = η.toDirichletCharacter.primitiveCharacter := by
  apply changeLevel_injective η.toDirichletCharacter.conductor_dvd_level
  rw [← changeLevel_trans, changeLevel_primitiveCharacter, toDirichletCharacter_def,
    ← RayClassCharacter.toDirichletCharacter_induced (conductor_of_dvd η), induced_character_of]

@[simp]
theorem toDirichletCharacter_of_intCast {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (m : ℤ) :
    (of η).toDirichletCharacter m = η.toDirichletCharacter.primitiveCharacter m := by
  have heq : Ideal.absNorm (of η).conductor.finitePart = η.toDirichletCharacter.conductor := by
    rw [conductor_of, RayClassCharacter.conductor_toDirichletCharacter]
  refine apply_intCast_eq_of_forall_isCoprime heq (fun a ha ↦ ?_) m
  have ha' : IsCoprime a η.toDirichletCharacter.conductor := heq ▸ ha
  rw [← changeLevel_toDirichletCharacter_of η, changeLevel_eq_cast_of_dvd' _ _ ha']

@[simp]
theorem toDirichletCharacter_of_natCast {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (m : ℕ) :
    (of η).toDirichletCharacter m = η.toDirichletCharacter.primitiveCharacter m := by
  simpa only [Int.cast_natCast] using toDirichletCharacter_of_intCast η (m : ℤ)

/-- **The bundled primitive ray class character of `ℚ` underlying a complex Dirichlet character.**
This applies to imprimitive characters as well as primitive ones: it extracts the ray class
conductor (`(f)` if `χ` is even, `(f)·∞` if `χ` is odd, where `f = χ.conductor`) together with its
primitive ray class character. -/
def ofDirichletCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    PrimitiveRayClassCharacter ℚ :=
  of ((ratDirichletEquiv N (NeZero.ne N)).symm χ)

theorem ofDirichletCharacter_def {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ofDirichletCharacter χ = of ((ratDirichletEquiv N (NeZero.ne N)).symm χ) := (rfl)

@[simp]
theorem absNorm_conductor_ofDirichletCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Ideal.absNorm (ofDirichletCharacter χ).conductor.finitePart = χ.conductor := by
  rw [ofDirichletCharacter_def, conductor_of, RayClassCharacter.absNorm_conductor_finitePart,
    MulEquiv.apply_symm_apply]

/-- For an even Dirichlet character `χ`, the conductor of `ofDirichletCharacter χ` is the finite
modulus `(χ.conductor)` without the real place. -/
theorem conductor_ofDirichletCharacter_of_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.Even) :
    (ofDirichletCharacter χ).conductor = ratFiniteModulus χ.conductor (conductor_ne_zero χ) := by
  let η := (ratDirichletEquiv N (NeZero.ne N)).symm χ
  have hη : changeLevel (dvd_of_eq (absNorm_ratModulus_finitePart N (NeZero.ne N)))
      η.toDirichletCharacter = χ := by
    rw [RayClassCharacter.changeLevel_toDirichletCharacter_ratModulus, MulEquiv.apply_symm_apply]
  have hcond : η.toDirichletCharacter.conductor = χ.conductor := by
    simpa only [conductor_changeLevel] using congrArg DirichletCharacter.conductor hη
  have heven : η.toDirichletCharacter.Even := by
    rwa [← even_changeLevel_iff (dvd_of_eq (absNorm_ratModulus_finitePart N (NeZero.ne N))), hη]
  simpa only [ofDirichletCharacter_def, conductor_of, hcond] using
    RayClassCharacter.conductor_eq_ratFiniteModulus_of_even η heven

/-- For an odd Dirichlet character `χ`, the conductor of `ofDirichletCharacter χ` is the modulus
`(χ.conductor)·∞` including the real place. -/
theorem conductor_ofDirichletCharacter_of_not_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : ¬ χ.Even) :
    (ofDirichletCharacter χ).conductor = ratModulus χ.conductor (conductor_ne_zero χ) := by
  let η := (ratDirichletEquiv N (NeZero.ne N)).symm χ
  have hη : changeLevel (dvd_of_eq (absNorm_ratModulus_finitePart N (NeZero.ne N)))
      η.toDirichletCharacter = χ := by
    rw [RayClassCharacter.changeLevel_toDirichletCharacter_ratModulus, MulEquiv.apply_symm_apply]
  have hcond : η.toDirichletCharacter.conductor = χ.conductor := by
    simpa only [conductor_changeLevel] using congrArg DirichletCharacter.conductor hη
  have hodd : ¬ η.toDirichletCharacter.Even := by
    rwa [← even_changeLevel_iff (dvd_of_eq (absNorm_ratModulus_finitePart N (NeZero.ne N))), hη]
  simpa only [ofDirichletCharacter_def, conductor_of, hcond] using
    RayClassCharacter.conductor_eq_ratModulus_of_not_even η hodd

@[simp]
theorem ofDirichletCharacter_toDirichletCharacter {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) :
    ofDirichletCharacter η.toDirichletCharacter = of η := by
  rw [ofDirichletCharacter_def, RayClassCharacter.toDirichletCharacter_def,
    MulEquiv.symm_apply_apply, of_induced]

@[simp]
theorem ofDirichletCharacter_primitive_toDirichletCharacter (ψ : PrimitiveRayClassCharacter ℚ) :
    ofDirichletCharacter ψ.toDirichletCharacter = ψ := by
  rw [toDirichletCharacter_def, ofDirichletCharacter_toDirichletCharacter, of_character]

@[simp]
theorem ofDirichletCharacter_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) :
    ofDirichletCharacter (changeLevel hMN χ) = ofDirichletCharacter χ := by
  have hmod : ratModulus M (NeZero.ne M) ∣ ratModulus N (NeZero.ne N) :=
    ratModulus_dvd_ratModulus_iff.mpr hMN
  have hsymm : (ratDirichletEquiv N (NeZero.ne N)).symm (changeLevel hMN χ) =
      ((ratDirichletEquiv M (NeZero.ne M)).symm χ).induced hmod := by
    apply (ratDirichletEquiv N (NeZero.ne N)).injective
    rw [MulEquiv.apply_symm_apply, ratDirichletEquiv_induced, MulEquiv.apply_symm_apply]
  rw [ofDirichletCharacter_def, hsymm, of_induced, ← ofDirichletCharacter_def]

@[simp]
theorem toDirichletCharacter_inv (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ⁻¹.toDirichletCharacter = ψ.toDirichletCharacter⁻¹ :=
  map_inv RayClassCharacter.toDirichletCharacter ψ.character

@[simp]
theorem ofDirichletCharacter_primitiveCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ofDirichletCharacter χ.primitiveCharacter = ofDirichletCharacter χ := by
  rw [← ofDirichletCharacter_changeLevel χ.conductor_dvd_level χ.primitiveCharacter,
    changeLevel_primitiveCharacter]

@[simp]
theorem ofDirichletCharacter_one (N : ℕ) [NeZero N] :
    ofDirichletCharacter (1 : DirichletCharacter ℂ N) = 1 := by
  rw [ofDirichletCharacter_def, map_one, of_one]

@[simp]
theorem ofDirichletCharacter_eq_one_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ofDirichletCharacter χ = 1 ↔ χ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ofDirichletCharacter_one N⟩
  have hc : χ.conductor = 1 := by
    have := congrArg (fun ψ : PrimitiveRayClassCharacter ℚ ↦ Ideal.absNorm ψ.conductor.finitePart) h
    simpa [absNorm_conductor_ofDirichletCharacter] using this
  exact eq_one_iff_conductor_eq_one.mpr hc

@[simp]
theorem ofDirichletCharacter_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ofDirichletCharacter χ⁻¹ = (ofDirichletCharacter χ)⁻¹ := by
  rw [ofDirichletCharacter_def, map_inv, of_inv, ← ofDirichletCharacter_def]

/-- Along `Ideal.absNorm (ofDirichletCharacter χ).conductor.finitePart = χ.conductor`,
`(ofDirichletCharacter χ).toDirichletCharacter` is `χ.primitiveCharacter`. -/
theorem changeLevel_toDirichletCharacter_ofDirichletCharacter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    changeLevel (dvd_of_eq (absNorm_conductor_ofDirichletCharacter χ))
      (ofDirichletCharacter χ).toDirichletCharacter = χ.primitiveCharacter := by
  apply changeLevel_injective χ.conductor_dvd_level
  rw [← changeLevel_trans, changeLevel_primitiveCharacter]
  let η₀ := (ratDirichletEquiv N (NeZero.ne N)).symm χ
  have hdvd : Ideal.absNorm (ofDirichletCharacter χ).conductor.finitePart ∣
      Ideal.absNorm (ratModulus N (NeZero.ne N)).finitePart :=
    map_dvd Ideal.absNorm (Modulus.dvd_iff.mp (conductor_of_dvd η₀)).1
  have h1 : changeLevel hdvd (ofDirichletCharacter χ).toDirichletCharacter =
      η₀.toDirichletCharacter :=
    (RayClassCharacter.toDirichletCharacter_induced (conductor_of_dvd η₀)
      (of η₀).character).symm.trans
      (congrArg RayClassCharacter.toDirichletCharacter (induced_character_of η₀))
  rw [changeLevel_trans _ hdvd (dvd_of_eq (absNorm_ratModulus_finitePart N (NeZero.ne N))), h1,
    RayClassCharacter.changeLevel_toDirichletCharacter_ratModulus, MulEquiv.apply_symm_apply]

/-- When `χ` is primitive of level `N`, `(ofDirichletCharacter χ).toDirichletCharacter` agrees with
`χ` along `Ideal.absNorm (ofDirichletCharacter χ).conductor.finitePart = N`. -/
theorem changeLevel_toDirichletCharacter_ofDirichletCharacter_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    changeLevel (dvd_of_eq ((absNorm_conductor_ofDirichletCharacter χ).trans
        ((isPrimitive_def χ).mp hχ)))
      (ofDirichletCharacter χ).toDirichletCharacter = χ := by
  rw [changeLevel_trans _
      (dvd_of_eq (absNorm_conductor_ofDirichletCharacter χ))
      (dvd_of_eq ((isPrimitive_def χ).mp hχ)),
    changeLevel_toDirichletCharacter_ofDirichletCharacter, changeLevel_primitiveCharacter]

@[simp]
theorem toDirichletCharacter_ofDirichletCharacter_intCast {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (m : ℤ) :
    (ofDirichletCharacter χ).toDirichletCharacter m = χ.primitiveCharacter m := by
  have h := primitiveCharacter_changeLevel_apply
    (dvd_of_eq (absNorm_ratModulus_finitePart N (NeZero.ne N)))
    ((ratDirichletEquiv N (NeZero.ne N)).symm χ).toDirichletCharacter m
  rw [RayClassCharacter.changeLevel_toDirichletCharacter_ratModulus,
    MulEquiv.apply_symm_apply] at h
  rw [ofDirichletCharacter_def, toDirichletCharacter_of_intCast, ← h]

@[simp]
theorem toDirichletCharacter_ofDirichletCharacter_natCast {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (m : ℕ) :
    (ofDirichletCharacter χ).toDirichletCharacter m = χ.primitiveCharacter m := by
  simpa only [Int.cast_natCast] using toDirichletCharacter_ofDirichletCharacter_intCast χ (m : ℤ)

theorem toDirichletCharacter_ofDirichletCharacter_intCast_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (m : ℤ) :
    (ofDirichletCharacter χ).toDirichletCharacter m = χ m := by
  rw [toDirichletCharacter_ofDirichletCharacter_intCast]
  exact apply_intCast_eq_of_forall_isCoprime ((isPrimitive_def χ).mp hχ)
    (fun _ ha ↦ primitiveCharacter_apply_of_isCoprime χ ((isPrimitive_def χ).mp hχ ▸ ha)) m

theorem toDirichletCharacter_ofDirichletCharacter_natCast_of_isPrimitive {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (m : ℕ) :
    (ofDirichletCharacter χ).toDirichletCharacter m = χ m := by
  simpa only [Int.cast_natCast] using
    toDirichletCharacter_ofDirichletCharacter_intCast_of_isPrimitive hχ (m : ℤ)

/-- **Equivalence between bundled primitive ray class characters of `ℚ` and primitive complex
Dirichlet characters bundled with their positive integer conductor.** Even primitive Dirichlet
characters correspond to finite moduli `(N)` without the real place; odd primitive Dirichlet
characters correspond to moduli `(N)·∞` including the real place. -/
def ratEquiv :
    PrimitiveRayClassCharacter ℚ ≃ (N : ℕ+) × {χ : DirichletCharacter ℂ N // χ.IsPrimitive} where
  toFun ψ :=
    ⟨⟨Ideal.absNorm ψ.conductor.finitePart, Nat.pos_of_ne_zero (NeZero.ne _)⟩,
      ⟨ψ.toDirichletCharacter, ψ.isPrimitive_toDirichletCharacter⟩⟩
  invFun p := ofDirichletCharacter p.snd.val
  left_inv ψ := ofDirichletCharacter_primitive_toDirichletCharacter ψ
  right_inv := by
    rintro ⟨N, ⟨χ, hχ⟩⟩
    have hlevel : Ideal.absNorm (ofDirichletCharacter χ).conductor.finitePart = N :=
      (absNorm_conductor_ofDirichletCharacter χ).trans ((isPrimitive_def χ).mp hχ)
    suffices ∀ (M : ℕ+) (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) (hM : M = N),
        changeLevel (dvd_of_eq (congrArg PNat.val hM)) ψ = χ →
        (⟨M, ⟨ψ, hψ⟩⟩ : (K : ℕ+) × {η : DirichletCharacter ℂ K // η.IsPrimitive}) =
          ⟨N, ⟨χ, hχ⟩⟩ from
      this _ _ _ (PNat.eq hlevel)
        (changeLevel_toDirichletCharacter_ofDirichletCharacter_of_isPrimitive hχ)
    rintro M ψ hψ rfl h
    simpa only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and, changeLevel_self] using h

theorem ratEquiv_apply (ψ : PrimitiveRayClassCharacter ℚ) :
    ratEquiv ψ =
      ⟨⟨Ideal.absNorm ψ.conductor.finitePart, Nat.pos_of_ne_zero (NeZero.ne _)⟩,
        ⟨ψ.toDirichletCharacter, ψ.isPrimitive_toDirichletCharacter⟩⟩ := (rfl)

@[simp]
theorem ratEquiv_fst_coe (ψ : PrimitiveRayClassCharacter ℚ) :
    ((ratEquiv ψ).fst : ℕ) = Ideal.absNorm ψ.conductor.finitePart := (rfl)

@[simp]
theorem ratEquiv_snd_intCast (ψ : PrimitiveRayClassCharacter ℚ) (m : ℤ) :
    (ratEquiv ψ).snd.val m = ψ.toDirichletCharacter m := (rfl)

@[simp]
theorem ratEquiv_snd_natCast (ψ : PrimitiveRayClassCharacter ℚ) (m : ℕ) :
    (ratEquiv ψ).snd.val m = ψ.toDirichletCharacter m := (rfl)

@[simp]
theorem ratEquiv_symm_apply (p : (N : ℕ+) × {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    ratEquiv.symm p = ofDirichletCharacter p.snd.val := (rfl)

@[simp]
theorem ratEquiv_one : ratEquiv 1 = ⟨1, ⟨1, isPrimitive_one_level_one⟩⟩ := by
  apply ratEquiv.symm.injective
  rw [Equiv.symm_apply_apply, ratEquiv_symm_apply, ofDirichletCharacter_one]

@[simp]
theorem ratEquiv_inv (ψ : PrimitiveRayClassCharacter ℚ) :
    ratEquiv ψ⁻¹ = ⟨(ratEquiv ψ).fst, ⟨(ratEquiv ψ).snd.val⁻¹, (ratEquiv ψ).snd.property.inv⟩⟩ := by
  apply ratEquiv.symm.injective
  rw [Equiv.symm_apply_apply, ratEquiv_symm_apply, ofDirichletCharacter_inv,
    ← ratEquiv_symm_apply, Equiv.symm_apply_apply]

end TauCeti.LFunctions.PrimitiveRayClassCharacter
