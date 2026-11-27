/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Idempotented.Basic

/-!
# Checks: submodules of nondegenerate modules over a non-idempotented ring

A submodule of a nondegenerate module over an idempotented algebra is nondegenerate
(`TauCeti.IsNondegenerate.of_injective`). The idempotents are needed: the non-unital ring
`H = 2ℤ` is not idempotented, it acts nondegenerately on `ℤ[1/2]` (`2ℤ · ℤ[1/2] = ℤ[1/2]`), but its
submodule `ℤ` has `2ℤ · ℤ = 2ℤ ≠ ℤ`. Here `H` acts on both through the inclusion `2ℤ → ℤ`,
extended to the unitization `ℤ ⊕ 2ℤ`.
-/

public section

open TauCeti

namespace TauCeti.Examples.Idempotented.TwoZ

/-- The non-unital ring `2ℤ`. -/
abbrev H : Type := (Ideal.span {(2 : ℤ)} : Ideal ℤ)

/-- The action of the unitization `ℤ ⊕ 2ℤ` on `ℤ` through the inclusion `2ℤ → ℤ`. -/
noncomputable abbrev φ : Unitization ℤ H →ₐ[ℤ] ℤ :=
  Unitization.lift (NonUnitalSubalgebraClass.subtype (R := ℤ) (Ideal.span {(2 : ℤ)}))

/-- `ℤ[1/2]`. -/
abbrev M : Type := Localization.Away (2 : ℤ)

/-- `ℤ[1/2]` as a module over `ℤ ⊕ 2ℤ`, through `φ`. -/
noncomputable abbrev moduleM : Module (Unitization ℤ H) M :=
  Module.compHom M ((algebraMap ℤ M).comp φ.toRingHom)

/-- `ℤ` as a module over `ℤ ⊕ 2ℤ`, through `φ`. -/
noncomputable abbrev moduleInt : Module (Unitization ℤ H) ℤ :=
  Module.compHom ℤ φ.toRingHom

attribute [local instance] moduleM moduleInt

/-- `ℤ ⊕ 2ℤ` acts on `ℤ[1/2]` by multiplication through `φ`. -/
theorem smul_M_def (r : Unitization ℤ H) (m : M) : r • m = algebraMap ℤ M (φ r) * m := rfl

/-- `ℤ ⊕ 2ℤ` acts on `ℤ` by multiplication through `φ`. -/
theorem smul_int_def (r : Unitization ℤ H) (n : ℤ) : r • n = φ r * n := rfl

/-- `φ` is the inclusion on `2ℤ`. -/
theorem φ_inr (h : H) : φ (h : Unitization ℤ H) = (h : ℤ) := by
  simp [φ]

/-- **`2ℤ` is not idempotented**: an idempotent `e` of `2ℤ` with `e * 2 = 2` would be `1`. -/
theorem not_isIdempotented : ¬IsIdempotented H := by
  intro h
  obtain ⟨e, -, hs⟩ := h.exists_isIdempotentElem {⟨2, Ideal.mem_span_singleton_self 2⟩}
  have h2 : (e : ℤ) * 2 = 2 := congrArg Subtype.val (hs _ (Finset.mem_singleton_self _)).1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 e.property
  omega

/-- **`2ℤ · ℤ[1/2] = ℤ[1/2]`**: every `m` is `2 • (m / 2)`. -/
theorem isNondegenerate_M : IsNondegenerate ℤ H M := by
  rw [isNondegenerate_iff_nondegeneratePart_eq_top, eq_top_iff]
  intro m _
  have : ((⟨2, Ideal.mem_span_singleton_self 2⟩ : H) : Unitization ℤ H) •
      (IsLocalization.Away.invSelf (2 : ℤ) * m) = m := by
    rw [smul_M_def, φ_inr, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  rw [← this]
  exact inr_smul_mem_nondegeneratePart _ _

/-- The inclusion `ℤ → ℤ[1/2]`, linear over `ℤ ⊕ 2ℤ`. -/
noncomputable def incl : ℤ →ₗ[Unitization ℤ H] M where
  toFun := algebraMap ℤ M
  map_add' := map_add _
  map_smul' r n := by
    rw [smul_int_def, smul_M_def, map_mul, RingHom.id_apply]

/-- The inclusion `ℤ → ℤ[1/2]` is injective. -/
theorem incl_injective : Function.Injective incl :=
  IsLocalization.injective (M := Submonoid.powers (2 : ℤ)) M
    (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)

/-- **`2ℤ · ℤ = 2ℤ ≠ ℤ`**: the submodule `ℤ` of `ℤ[1/2]` is not nondegenerate. -/
theorem not_isNondegenerate_int : ¬IsNondegenerate ℤ H ℤ := by
  intro hnd
  let N : Submodule (Unitization ℤ H) ℤ :=
    { carrier := {m | (2 : ℤ) ∣ m}
      add_mem' := fun ha hb => dvd_add ha hb
      zero_mem' := dvd_zero 2
      smul_mem' := fun r m hm => by
        rw [smul_int_def]
        exact dvd_mul_of_dvd_right hm (φ r) }
  have hle : nondegeneratePart ℤ H ℤ ≤ N := nondegeneratePart_le_iff.2 fun h m => by
    rw [smul_int_def, φ_inr]
    exact dvd_mul_of_dvd_left (Ideal.mem_span_singleton.1 h.property) m
  have h1 : (1 : ℤ) ∈ N := hle (by rw [isNondegenerate_iff_nondegeneratePart_eq_top.1 hnd]; trivial)
  exact (by decide : ¬(2 : ℤ) ∣ 1) h1

-- Without idempotents, a submodule of a nondegenerate module need not be nondegenerate.
example : ¬IsIdempotented H ∧ IsNondegenerate ℤ H M ∧ Function.Injective incl ∧
    ¬IsNondegenerate ℤ H ℤ :=
  ⟨not_isIdempotented, isNondegenerate_M, incl_injective, not_isNondegenerate_int⟩

end TauCeti.Examples.Idempotented.TwoZ
