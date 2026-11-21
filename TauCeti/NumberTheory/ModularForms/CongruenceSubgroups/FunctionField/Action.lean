/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Generators

/-!
# The fractional-linear action on arithmetic modular functions

Fricke generation shows that fractional-linear substitutions preserve `F_N`, the field of
functions whose Laurent coefficients at infinity lie in `ℚ(ζ_N)`. We restrict the complex
action to this field and compute its action on generators and its kernel. The action is
faithful exactly when `N ∣ 2`, including the levels where the two scalar signs coincide.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient
open TauCeti.RiemannSurface
open scoped Matrix MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- If `K` contains the `N`-th roots of unity and a function has Laurent coefficients at
infinity in `K`, its fractional-linear substitutions also have coefficients there in `K`. -/
theorem unop_modularFunctionActionZMod_mem_coeffSubfield {K : Subfield ℂ}
    (hK : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ K) (g : SL(2, ZMod N))
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ coeffSubfield (cuspDatumInftyGamma N) K) :
    unop (modularFunctionActionZMod N g) F ∈ coeffSubfield (cuspDatumInftyGamma N) K := by
  let B := coeffIntermediateField (cuspDatumInftyGamma N) K
  let σ := (unop (modularFunctionActionZMod N g)).restrictScalars K
  have hle : B ≤ B.comap σ.toAlgHom := by
    conv_lhs =>
      unfold B
      rw [← adjoin_insert_image_frickeMeromorphicFunction_eq_coeffIntermediateField hK]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro F (rfl | ⟨a, _, rfl⟩)
    · simp only [SetLike.mem_coe, IntermediateField.mem_comap, σ, AlgEquiv.coe_toAlgHom,
        AlgEquiv.restrictScalars_apply, unop_modularFunctionActionZMod_compactifiedQuotientComap]
      simpa only [B, coe_modularFunctionJ, SetLike.mem_coe] using (modularFunctionJ N K).property
    · simp only [SetLike.mem_coe, IntermediateField.mem_comap, σ, AlgEquiv.coe_toAlgHom,
        AlgEquiv.restrictScalars_apply, unop_modularFunctionActionZMod_frickeMeromorphicFunction]
      exact mem_coeffIntermediateField.mpr ((mem_coeffSubfield _).mpr
        (laurentQExpansion_frickeMeromorphicFunction_coeff_mem hK _))
  exact mem_coeffIntermediateField.mp (hle (mem_coeffIntermediateField.mpr hF))

/-- If `K` contains the `N`-th roots of unity, a substituted function has Laurent coefficients
at infinity in `K` if and only if the original function does. -/
@[simp]
theorem unop_modularFunctionActionZMod_mem_coeffSubfield_iff {K : Subfield ℂ}
    (hK : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ K) (g : SL(2, ZMod N))
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    unop (modularFunctionActionZMod N g) F ∈ coeffSubfield (cuspDatumInftyGamma N) K ↔
      F ∈ coeffSubfield (cuspDatumInftyGamma N) K := by
  refine ⟨fun hF ↦ ?_, unop_modularFunctionActionZMod_mem_coeffSubfield hK g⟩
  have h := unop_modularFunctionActionZMod_mem_coeffSubfield hK g⁻¹ hF
  simpa only [map_inv, unop_inv, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply] using h

/-- The finite modular action preserves the arithmetic modular function field. -/
@[simp]
theorem unop_modularFunctionActionZMod_mem_modularFunctionField_iff (g : SL(2, ZMod N))
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    unop (modularFunctionActionZMod N g) F ∈ modularFunctionField N ↔
      F ∈ modularFunctionField N := by
  rw [modularFunctionField_def]
  exact unop_modularFunctionActionZMod_mem_coeffSubfield_iff
    (fun _ hζ ↦ Subfield.subset_closure hζ) g

private theorem coe_modularFunctionFieldActionZMod_restrict_apply (g : SL(2, ZMod N))
    (F : modularFunctionField N) :
    (((unop (modularFunctionActionZMod N g)).toRingEquiv.restrict
      (modularFunctionField N) (modularFunctionField N)
      (fun _ ↦ (unop_modularFunctionActionZMod_mem_modularFunctionField_iff g).symm) F) :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
        unop (modularFunctionActionZMod N g) F :=
  RingHom.coe_restrict_apply _ (modularFunctionField N) (modularFunctionField N)
    (fun _ hF ↦ (unop_modularFunctionActionZMod_mem_modularFunctionField_iff g).mpr hF) F

variable (N) in
/-- The fractional-linear right action of `SL(2, ℤ/Nℤ)` on the arithmetic modular function
field `F_N`, obtained by restricting its action on the complex function field. -/
def modularFunctionFieldActionZMod :
    SL(2, ZMod N) →* (modularFunctionField N ≃+* modularFunctionField N)ᵐᵒᵖ where
  toFun g := op ((unop (modularFunctionActionZMod N g)).toRingEquiv.restrict
    (modularFunctionField N) (modularFunctionField N)
    (fun _ ↦ (unop_modularFunctionActionZMod_mem_modularFunctionField_iff g).symm))
  map_one' := by
    apply unop_injective
    apply RingEquiv.ext
    intro F
    apply Subtype.ext
    simp only [unop_op, unop_one, RingAut.one_apply]
    rw [coe_modularFunctionFieldActionZMod_restrict_apply, map_one, unop_one,
      AlgEquiv.one_apply]
  map_mul' g h := by
    apply unop_injective
    apply RingEquiv.ext
    intro F
    apply Subtype.ext
    simp only [unop_op, unop_mul, RingAut.mul_apply]
    rw [coe_modularFunctionFieldActionZMod_restrict_apply]
    simp only [coe_modularFunctionFieldActionZMod_restrict_apply, map_mul, unop_mul,
      AlgEquiv.mul_apply]

/-- The arithmetic modular action agrees with the complex action on underlying functions. -/
@[simp]
theorem coe_unop_modularFunctionFieldActionZMod_apply (g : SL(2, ZMod N))
    (F : modularFunctionField N) :
    (unop (modularFunctionFieldActionZMod N g) F :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
        unop (modularFunctionActionZMod N g) F :=
  coe_modularFunctionFieldActionZMod_restrict_apply g F

/-- The arithmetic modular action fixes every cyclotomic constant. -/
@[simp]
theorem unop_modularFunctionFieldActionZMod_const (g : SL(2, ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    unop (modularFunctionFieldActionZMod N g)
        ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.property⟩ =
      ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.property⟩ := by
  apply Subtype.ext
  rw [coe_unop_modularFunctionFieldActionZMod_apply, AlgEquiv.commutes]

/-- The arithmetic modular action fixes the modular invariant `j`. -/
@[simp]
theorem unop_modularFunctionFieldActionZMod_jMeromorphicFunction (g : SL(2, ZMod N)) :
    unop (modularFunctionFieldActionZMod N g)
        ⟨Subgroup.compactifiedQuotientComap
          (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction,
            compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩ =
      ⟨Subgroup.compactifiedQuotientComap
        (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction,
          compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩ := by
  apply Subtype.ext
  rw [coe_unop_modularFunctionFieldActionZMod_apply,
    unop_modularFunctionActionZMod_compactifiedQuotientComap]

/-- On arithmetic Fricke functions, substitution by `g` sends `f_a` to `f_{a g}`. -/
@[simp]
theorem unop_modularFunctionFieldActionZMod_frickeMeromorphicFunction (g : SL(2, ZMod N))
    (a : Fin 2 → ZMod N) :
    unop (modularFunctionFieldActionZMod N g)
        ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ =
      ⟨frickeMeromorphicFunction (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))),
        frickeMeromorphicFunction_mem_modularFunctionField _⟩ := by
  apply Subtype.ext
  rw [coe_unop_modularFunctionFieldActionZMod_apply,
    unop_modularFunctionActionZMod_frickeMeromorphicFunction]

/-- Opposite scalar signs induce the same arithmetic modular substitution. -/
@[simp]
theorem modularFunctionFieldActionZMod_neg (g : SL(2, ZMod N)) :
    modularFunctionFieldActionZMod N (-g) = modularFunctionFieldActionZMod N g := by
  apply unop_injective
  apply RingEquiv.ext
  intro F
  apply Subtype.ext
  simp

/-- The kernel of the arithmetic modular action consists exactly of the two scalar signs.
This statement also applies when the two signs coincide. -/
@[simp]
theorem modularFunctionFieldActionZMod_eq_one_iff (g : SL(2, ZMod N)) :
    modularFunctionFieldActionZMod N g = 1 ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    refine (forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff g).mp ?_
    intro a _
    have h := congrArg (fun e : (modularFunctionField N ≃+* modularFunctionField N)ᵐᵒᵖ ↦
      (unop e (⟨frickeMeromorphicFunction a,
        frickeMeromorphicFunction_mem_modularFunctionField a⟩ : modularFunctionField N) :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)) hg
    simpa only [coe_unop_modularFunctionFieldActionZMod_apply, unop_one,
      RingAut.one_apply] using h
  · rintro (rfl | rfl)
    · exact map_one _
    · exact (modularFunctionFieldActionZMod_neg (N := N) 1).trans (map_one _)

/-- The arithmetic modular action is faithful exactly at the positive levels dividing two. -/
theorem modularFunctionFieldActionZMod_injective_iff :
    Function.Injective (modularFunctionFieldActionZMod N) ↔ N ∣ 2 := by
  have hsign : (-1 : SL(2, ZMod N)) = 1 ↔ N ∣ 2 := by
    constructor
    · intro h
      have hentry := congrArg (fun g : SL(2, ZMod N) ↦ g 0 0) h
      have hz : (-1 : ZMod N) = 1 := by simpa using hentry
      exact (Nat.dvd_prime Nat.prime_two).mpr (ZMod.neg_one_eq_one_iff.mp hz)
    · intro h
      have hz : (-1 : ZMod N) = 1 :=
        ZMod.neg_one_eq_one_iff.mpr ((Nat.dvd_prime Nat.prime_two).mp h)
      ext i j
      by_cases hij : i = j <;> simp [hij, hz]
  rw [← hsign, injective_iff_map_eq_one]
  constructor
  · intro h
    exact h (-1) ((modularFunctionFieldActionZMod_eq_one_iff _).mpr (Or.inr rfl))
  · intro h g hg
    rcases (modularFunctionFieldActionZMod_eq_one_iff g).mp hg with hg | hg
    · exact hg
    · exact hg.trans h

/-- At level two the arithmetic modular action is faithful, since the two signs coincide. -/
theorem modularFunctionFieldActionZMod_two_injective :
    Function.Injective (modularFunctionFieldActionZMod 2) :=
  modularFunctionFieldActionZMod_injective_iff.mpr (dvd_refl 2)

end TauCeti
