/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.Ideal.Maps
import TauCeti.Algebra.Group.Hom.Lift
import TauCeti.RingTheory.Ideal.Span

/-!
# Reducing an additive character modulo a principal ideal

Let `O` be a subring of a commutative ring `F`, `ϖ` a unit of `F` lying in `O`, and
`π : O →+* R` a surjection with kernel `ϖ O`, such as the reduction `O → O / ϖ O` of the integers
of a non-archimedean local field modulo a uniformiser. An additive character `ψ` of `F` with
conductor `O`, that is, trivial on `t O` exactly when `t ∈ O`, induces the additive character
`π x ↦ ψ (ϖ⁻¹ x)` of `R`, and this character is primitive.

* `TauCeti.exists_isPrimitive_addChar_apply_eq`: the reduced additive character exists and is
  primitive.
-/

public section

namespace TauCeti

variable {F R : Type*} [CommRing F] [CommRing R] {O : Subring F} {ϖ : Fˣ} {π : O →+* R}

/-- **The reduced additive character.** Let `ψ` be an additive character of `F` with conductor
`O`, that is, trivial on `t O` exactly when `t ∈ O`. Then `π x ↦ ψ (ϖ⁻¹ x)` is a well-defined
primitive additive character of `R = O / ϖ O`. -/
theorem exists_isPrimitive_addChar_apply_eq {M : Type*} [CommMonoid M] (hϖ : (ϖ : F) ∈ O)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {⟨ϖ, hϖ⟩})
    {ψ : AddChar F M} (hψ : ∀ t : F, (∀ x ∈ O, ψ (t * x) = 1) ↔ t ∈ O) :
    ∃ φ : AddChar R M, φ.IsPrimitive ∧ ∀ x : O, φ (π x) = ψ (((ϖ⁻¹ : Fˣ) : F) * x) := by
  have hzero := map_eq_zero_iff_inv_mul_mem hϖ hker
  -- `x ↦ ψ (ϖ⁻¹ x)` on `O` is trivial on the kernel of `π`, so it factors through `π`
  let ψO := (ψ.mulShift ((ϖ⁻¹ : Fˣ) : F)).compAddMonoidHom O.subtype.toAddMonoidHom
  have hle : π.toAddMonoidHom.ker ≤ (AddChar.toAddMonoidHomEquiv ψO).ker := fun x hx ↦ by
    simpa [ψO] using (hψ 1).mpr O.one_mem _ ((hzero x).mp hx)
  obtain ⟨φ', hφ', -⟩ := (AddMonoidHom.existsUnique_comp_eq_iff_ker_le
    (AddChar.toAddMonoidHomEquiv ψO) π.toAddMonoidHom hπ).2 hle
  let φ : AddChar R M := AddChar.toAddMonoidHomEquiv.symm φ'
  have hs (x : O) : φ (π x) = ψ (((ϖ⁻¹ : Fˣ) : F) * x) := by
    simpa [φ, ψO] using congr_arg Additive.toMul (DFunLike.congr_fun hφ' x)
  refine ⟨φ, fun a ha h ↦ ?_, hs⟩
  obtain ⟨x, rfl⟩ := hπ a
  -- `ϖ⁻¹ x ∉ O`, so `ψ (ϖ⁻¹ x y) ≠ 1` for some `y ∈ O`
  obtain ⟨y, hy, hne⟩ : ∃ y ∈ O, ψ (((ϖ⁻¹ : Fˣ) : F) * x * y) ≠ 1 := by
    by_contra! h'
    exact ha ((hzero x).mpr ((hψ _).mp h'))
  apply hne
  have h2 := DFunLike.congr_fun h (π ⟨y, hy⟩)
  rw [AddChar.mulShift_apply, one_apply, ← map_mul] at h2
  rw [← h2]
  refine Eq.trans ?_ (hs (x * ⟨y, hy⟩)).symm
  simp [mul_assoc]

end TauCeti
