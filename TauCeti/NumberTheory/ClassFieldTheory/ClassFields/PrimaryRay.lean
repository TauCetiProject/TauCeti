/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Abelian.PrimarySubfield
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField

/-!
# Primary layers of ray class fields

For prime `p`, `primaryRayClassField` gives Rubin's fields `K(q)` and `K(1)` at a prime
and the trivial modulus (*Euler Systems*, Chapter IV, §1). The maximality criterion
`le_primaryRayClassField_iff` and inclusions `primaryRayClassField_mono` use
`IsAbelianGalois.primarySubfield`. The degree formula `finrank_primaryRayClassField` uses
`finrank_rayClassField`.
-/

public section

open scoped Nat
open NumberField IntermediateField TauCeti.GlobalNumberFields

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- The primary subfield of the ray class field of `𝔪`, viewed in `SeparableClosure K`.
For prime `p`, it is the maximal subextension of `p`-power degree. -/
noncomputable def primaryRayClassField (𝔪 : Modulus K) (p : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  lift (IsAbelianGalois.primarySubfield K (rayClassField 𝔪) p)

/-- The primary ray class field is the lift of the primary subfield of the full ray class field. -/
theorem primaryRayClassField_def (𝔪 : Modulus K) (p : ℕ) :
    primaryRayClassField 𝔪 p =
      lift (IsAbelianGalois.primarySubfield K (rayClassField 𝔪) p) := (rfl)

/-- The primary ray class field is contained in the full ray class field. -/
@[simp] theorem primaryRayClassField_le_rayClassField (𝔪 : Modulus K) (p : ℕ) :
    primaryRayClassField 𝔪 p ≤ rayClassField 𝔪 :=
  (primaryRayClassField_def 𝔪 p).symm ▸ lift_le _

/-- The primary ray class field is finite over the base. -/
instance finiteDimensional_primaryRayClassField (𝔪 : Modulus K) (p : ℕ) :
    FiniteDimensional K (primaryRayClassField 𝔪 p) :=
  let f := inclusion (primaryRayClassField_le_rayClassField 𝔪 p)
  FiniteDimensional.of_injective f.toLinearMap f.injective

/-- The primary ray class field is abelian Galois over the base. -/
instance isAbelianGalois_primaryRayClassField (𝔪 : Modulus K) (p : ℕ) :
    IsAbelianGalois K (primaryRayClassField 𝔪 p) :=
  IsAbelianGalois.of_algHom (inclusion (primaryRayClassField_le_rayClassField 𝔪 p))

-- Not a simp lemma: the right side introduces an existential degree condition.
/-- For prime `p`, this is the largest ray subextension of `p`-power degree. -/
theorem le_primaryRayClassField_iff {𝔪 : Modulus K} {p : ℕ} (hp : p.Prime)
    {E : IntermediateField K (SeparableClosure K)} :
    E ≤ primaryRayClassField 𝔪 p ↔ E ≤ rayClassField 𝔪 ∧ ∃ n : ℕ, Module.finrank K E = p ^ n := by
  have criterion (hE : E ≤ rayClassField 𝔪) :
      E ≤ primaryRayClassField 𝔪 p ↔ ∃ n : ℕ, Module.finrank K E = p ^ n := by
    have hdeg := (restrictAlgEquiv hE).toLinearEquiv.finrank_eq
    calc
      E ≤ primaryRayClassField 𝔪 p ↔
          lift (restrict hE) ≤ primaryRayClassField 𝔪 p := by rw [lift_restrict]
      _ ↔ restrict hE ≤ IsAbelianGalois.primarySubfield K (rayClassField 𝔪) p := by
        rw [primaryRayClassField_def]
        exact IntermediateField.map_le_map_iff (rayClassField 𝔪).val
      _ ↔ ∃ n : ℕ, Module.finrank K E = p ^ n := by
        rw [IsAbelianGalois.le_primarySubfield_iff hp, ← hdeg]
  refine ⟨fun h ↦ ?_, fun ⟨hE, hdeg⟩ ↦ (criterion hE).mpr hdeg⟩
  have hE := h.trans (primaryRayClassField_le_rayClassField 𝔪 p)
  exact ⟨hE, (criterion hE).mp h⟩

/-- Divisibility of moduli gives inclusion of their primary ray class fields. -/
theorem primaryRayClassField_mono {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) (p : ℕ) :
    primaryRayClassField 𝔪 p ≤ primaryRayClassField 𝔫 p := by
  by_cases hp : p.Prime
  · have h𝔪 := (le_primaryRayClassField_iff hp (𝔪 := 𝔪)).mp le_rfl
    exact (le_primaryRayClassField_iff hp).mpr ⟨h𝔪.1.trans (rayClassField_mono h), h𝔪.2⟩
  · simp only [primaryRayClassField_def, IsAbelianGalois.primarySubfield_eq_bot_of_ordProj_eq_one
      (Nat.ordProj_of_not_prime _ _ hp), lift_bot, le_refl]

/-- The primary ray class field has degree the `p`-part of the ray class number. -/
theorem finrank_primaryRayClassField (𝔪 : Modulus K) (p : ℕ) :
    Module.finrank K (primaryRayClassField 𝔪 p) = ordProj[p] (Nat.card (RayClassGroup 𝔪)) := by
  have he := (liftAlgEquiv (IsAbelianGalois.primarySubfield K (rayClassField 𝔪) p)).toLinearEquiv
  rw [primaryRayClassField_def, ← he.finrank_eq, IsAbelianGalois.finrank_primarySubfield p,
    finrank_rayClassField]

end TauCeti.ClassFieldTheory
