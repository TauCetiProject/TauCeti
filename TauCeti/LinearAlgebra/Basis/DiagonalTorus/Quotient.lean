/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Torus points annihilating a character sublattice

For a sublattice `Q` of the character lattice `ℤ^κ`, the torus points on which every character
in `Q` is one form a subgroup. This subgroup is naturally the group of characters of `ℤ^κ / Q`
with values in the units of the coefficient ring. In particular, taking `Q` to be the root
lattice gives the torus part of the centre of a Chevalley group.

The equivalence `torusAnnihilatorEquiv` sends a quotient character to its values on the standard
basis classes. Its inverse retains the evaluation equation on arbitrary quotient classes.
No divisibility of the units, saturation of `Q`, or field hypothesis is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(d).
* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
-/

public section

namespace TauCeti

variable {κ ι R : Type*} [Fintype κ] [CommRing R]

/-- The points of a split torus annihilating a sublattice of its character lattice. -/
def torusAnnihilator (Q : Submodule ℤ (κ → ℤ)) : Subgroup (κ → Rˣ) where
  carrier := {s | ∀ μ ∈ Q, torusCharacter s μ = 1}
  one_mem' := by simp
  mul_mem' hs ht μ hμ := by rw [torusCharacter_mul, hs μ hμ, ht μ hμ, mul_one]
  inv_mem' {s} hs μ hμ := by
    have h := torusCharacter_mul s s⁻¹ μ
    simpa [hs μ hμ] using h.symm

/-- Membership means that every character of the sublattice evaluates to one. -/
@[simp]
theorem mem_torusAnnihilator (Q : Submodule ℤ (κ → ℤ)) (s : κ → Rˣ) :
    s ∈ torusAnnihilator Q ↔ ∀ μ ∈ Q, torusCharacter s μ = 1 :=
  Iff.rfl

/-- It suffices to annihilate the generators of a character sublattice. -/
theorem mem_torusAnnihilator_span_iff (α : ι → κ → ℤ) (s : κ → Rˣ) :
    s ∈ torusAnnihilator (Submodule.span ℤ (Set.range α)) ↔
      ∀ i, torusCharacter s (α i) = 1 := by
  constructor
  · intro hs i
    exact hs _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hs μ hμ
    induction hμ using Submodule.span_induction with
    | mem μ hμ => obtain ⟨i, rfl⟩ := hμ; exact hs i
    | zero => simp
    | add μ ν hμ hν ihμ ihν => rw [torusCharacter_add, ihμ, ihν, mul_one]
    | smul z μ hμ ih => rw [torusCharacter_zsmul, ih, one_zpow]

omit [Fintype κ] in
/-- A unit-valued character of a quotient character lattice determines a torus point by its
values on the standard basis classes. -/
def quotientCharTorusPoint [DecidableEq κ] (Q : Submodule ℤ (κ → ℤ)) :
    AddChar ((κ → ℤ) ⧸ Q) Rˣ →* (κ → Rˣ) where
  toFun χ i := χ (Q.mkQ (Pi.single i 1))
  map_one' := by ext; simp
  map_mul' χ ψ := by ext; simp

omit [Fintype κ] in
/-- The coordinates of the torus point associated to a quotient character. -/
@[simp]
theorem quotientCharTorusPoint_apply [DecidableEq κ] (Q : Submodule ℤ (κ → ℤ))
    (χ : AddChar ((κ → ℤ) ⧸ Q) Rˣ) (i : κ) :
    quotientCharTorusPoint Q χ i = χ (Q.mkQ (Pi.single i 1)) :=
  (rfl)

/-- Evaluating a lattice character at the associated torus point is evaluation of its quotient
class by the quotient character. -/
@[simp]
theorem torusCharacter_quotientCharTorusPoint [DecidableEq κ]
    (Q : Submodule ℤ (κ → ℤ)) (χ : AddChar ((κ → ℤ) ⧸ Q) Rˣ) (μ : κ → ℤ) :
    torusCharacter (quotientCharTorusPoint Q χ) μ = χ (Q.mkQ μ) := by
  have hμ : Q.mkQ μ = ∑ i, μ i • Q.mkQ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' μ]
    simp only [map_sum, map_smul]
  have h := congrArg Additive.toMul (congrArg χ.toAddMonoidHom hμ)
  simpa [map_sum, map_zsmul, toMul_sum, toMul_zsmul, torusCharacter_def] using h.symm

omit [Fintype κ] in
/-- A quotient character is determined by its associated torus point. -/
theorem quotientCharTorusPoint_injective [Finite κ] [DecidableEq κ]
    (Q : Submodule ℤ (κ → ℤ)) :
    Function.Injective (quotientCharTorusPoint (R := R) Q) := by
  let := Fintype.ofFinite κ
  intro χ ψ h
  apply AddChar.ext
  intro μ
  induction μ using Submodule.Quotient.induction_on with
  | _ μ =>
    simpa only [torusCharacter_quotientCharTorusPoint, Submodule.mkQ_apply] using
      congrArg (fun s => torusCharacter s μ) h

/-- The image of quotient characters consists exactly of the points annihilating the sublattice.
This is the universal property of the quotient lattice, read in torus coordinates. -/
theorem range_quotientCharTorusPoint [DecidableEq κ] (Q : Submodule ℤ (κ → ℤ)) :
    (quotientCharTorusPoint (R := R) Q).range = torusAnnihilator Q := by
  ext s
  constructor
  · rintro ⟨χ, rfl⟩ μ hμ
    rw [torusCharacter_quotientCharTorusPoint,
      (LinearMap.mem_ker.mp (Q.ker_mkQ.symm ▸ hμ)), χ.map_zero_eq_one]
  · intro hs
    let f : (κ → ℤ) →ₗ[ℤ] Additive Rˣ :=
      ({ toFun := fun μ => Additive.ofMul (torusCharacter s μ)
         map_zero' := by simp
         map_add' := fun μ ν => by simp [torusCharacter_add] } :
          (κ → ℤ) →+ Additive Rˣ).toIntLinearMap
    have hf : Q ≤ f.ker := by
      intro μ hμ
      rw [LinearMap.mem_ker]
      exact congrArg Additive.ofMul (hs μ hμ)
    refine ⟨AddChar.toAddMonoidHomEquiv.symm (Q.liftQ f hf).toAddMonoidHom, ?_⟩
    ext i
    simp [f]

/-- The unit-valued characters of a quotient character lattice are naturally its annihilator
in the split torus. -/
noncomputable def torusAnnihilatorEquiv [DecidableEq κ] (Q : Submodule ℤ (κ → ℤ)) :
    AddChar ((κ → ℤ) ⧸ Q) Rˣ ≃* torusAnnihilator (R := R) Q :=
  (MonoidHom.ofInjective (quotientCharTorusPoint_injective Q)).trans
    (MulEquiv.subgroupCongr (range_quotientCharTorusPoint Q))

/-- The equivalence has the same coordinates as the underlying torus-point map. -/
@[simp]
theorem coe_torusAnnihilatorEquiv [DecidableEq κ] (Q : Submodule ℤ (κ → ℤ))
    (χ : AddChar ((κ → ℤ) ⧸ Q) Rˣ) :
    (torusAnnihilatorEquiv Q χ : κ → Rˣ) = quotientCharTorusPoint Q χ := by
  simp [torusAnnihilatorEquiv, MonoidHom.ofInjective_apply]

/-- The inverse equivalence evaluates a quotient class by the original torus character. -/
@[simp]
theorem torusAnnihilatorEquiv_symm_apply_mk [DecidableEq κ] (Q : Submodule ℤ (κ → ℤ))
    (s : torusAnnihilator (R := R) Q) (μ : κ → ℤ) :
    (torusAnnihilatorEquiv Q).symm s (Submodule.Quotient.mk μ) = torusCharacter s.val μ := by
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint,
    ← coe_torusAnnihilatorEquiv, MulEquiv.apply_symm_apply]

end TauCeti
