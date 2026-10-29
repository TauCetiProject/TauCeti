/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
public import TauCeti.NumberTheory.NumberField.Units.Signature.Surjective

/-!
# The narrow class group and the signatures of units

Let `K` be a number field. Every sign pattern at the real places is the signature of an element of
`Kˣ` (`NumberField.fieldUnitSignature_surjective`), but the units of `𝓞 K` may realize fewer
sign patterns. This file shows that the gap is detected by the narrow class group: the forgetful
map `Cl⁺(K) → Cl(K)` is injective exactly when the integer-unit signature
`NumberField.unitSignature` is surjective.

## Main results

* `TauCeti.NumberField.NarrowClassGroup.toClassGroup_injective_iff_unitSignature_surjective`:
  the narrow and ordinary class groups agree exactly when the units of `𝓞 K` realize every sign
  pattern at the real places.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open NumberField NumberField.NarrowClassGroup

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The narrow and ordinary class groups agree exactly when the units realize every sign
pattern.** The forgetful map `Cl⁺(K) → Cl(K)` is injective if and only if the signature map on the
units of `𝓞 K` is surjective. So a field whose units miss a sign pattern at the real places has a
narrow class group strictly larger than its class group. -/
theorem toClassGroup_injective_iff_unitSignature_surjective :
    Function.Injective (toClassGroup (K := K)) ↔ Function.Surjective (unitSignature (K := K)) := by
  -- By exactness of `Kˣ → Cl⁺(K) → Cl(K) → 1`, injectivity says every principal narrow class
  -- `[(x)]⁺` is trivial, that is, some unit `w` makes `w x` totally positive. Since every sign
  -- pattern is the signature of some `x`, this holds exactly when every sign pattern is the
  -- signature of a unit.
  -- Scaling `x` by a unit `w` gives a totally positive element exactly when the signature of `w`
  -- cancels that of `x`.
  have key (w : (𝓞 K)ˣ) (x : Kˣ) :
      IsTotallyPositive (w • (x : K)) ↔ unitSignature w * fieldUnitSignature x = 1 := by
    rw [unitSignature_eq_fieldUnitSignature, ← map_mul, fieldUnitSignature_eq_one_iff]
    simp [Units.smul_def, Algebra.smul_def]
  rw [← MonoidHom.ker_eq_bot_iff, toClassGroup_ker, Subgroup.eq_bot_iff_forall]
  simp only [MonoidHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h s
    obtain ⟨x, hx⟩ := fieldUnitSignature_surjective (K := K) s⁻¹
    obtain ⟨w, hw⟩ := mkPrincipal_eq_one_iff.mp (h x)
    rw [key, hx] at hw
    exact ⟨w, mul_inv_eq_one.mp hw⟩
  · intro h x
    obtain ⟨w, hw⟩ := h (fieldUnitSignature x)⁻¹
    refine mkPrincipal_eq_one_iff.mpr ⟨w, (key w x).mpr ?_⟩
    rw [hw]
    exact inv_mul_cancel (fieldUnitSignature x)

end TauCeti.NumberField.NarrowClassGroup
