/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.FiniteIndex

/-!
# Induction in free left-coset coordinates

For a finite-index subgroup `S ≤ G`, identify the coinvariant carrier of `Ind_S^G A`
with `G ⧸ S →₀ A`. The coordinate at `g⁻¹S` is the right-coset coordinate at `Sg`;
the representatives are therefore the inverses of those used by
`TauCeti.Rep.indSubtypeEquivPi`. This convention matters because Mathlib's induced
action sends `⟦h ⊗ a⟧` to `⟦h g⁻¹ ⊗ a⟧`.

The action formula expresses the usual permutation of left cosets with a correction
by the subgroup action. The generator and inverse-single formulas identify the
actual coinvariant vectors, and the naturality formula makes the coordinates usable
for induced intertwiners. No finiteness assumption on the coefficient module or on
the group is needed.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.1.
* Mathlib's finite-index comparison `Rep.indCoindIso` and Tau Ceti's
  right-coset model `TauCeti.Rep.indSubtypeEquivPi` supply the underlying maps.
-/

public section

open CategoryTheory

universe u v w

namespace Rep

open TauCeti.Rep

variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable {S : Subgroup G} [S.FiniteIndex]

/-- The free left-coset model of induction, using inversion to turn the existing
right-coset coordinates into left-coset coordinates. -/
noncomputable def indLeftCosetCoinvariantEquiv (A : Rep.{max w u} k S) :
    Rep.ind S.subtype A ≃ₗ[k] (G ⧸ S →₀ A) :=
  (indSubtypeEquivPi A).trans
    ((LinearEquiv.funCongrLeft k A
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm).trans
        (Finsupp.linearEquivFunOnFinite k A (G ⧸ S)).symm)

-- This comparison is not a simp rule: computations should stay in the left-coset model.
/-- The coordinate at a left coset is the existing right-coset coordinate at its inverse. -/
theorem indLeftCosetCoinvariantEquiv_apply (A : Rep.{max w u} k S)
    (x : Rep.ind S.subtype A) (q : G ⧸ S) :
    indLeftCosetCoinvariantEquiv A x q =
      indSubtypeEquivPi A x
        ((QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm q) :=
  (rfl)

/-- The induced action permutes left cosets by `g⁻¹` and applies the corresponding
subgroup correction to each value. -/
theorem indLeftCosetCoinvariantEquiv_ρ_apply (A : Rep.{max w u} k S) (g : G)
    (x : Rep.ind S.subtype A) (q : G ⧸ S) :
    indLeftCosetCoinvariantEquiv A ((Rep.ind S.subtype A).ρ g x) q =
      A.ρ (rightCosetFactor (S := S)
        (((QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm q).out * g))
        (indLeftCosetCoinvariantEquiv A x (g⁻¹ • q)) := by
  rw [indLeftCosetCoinvariantEquiv_apply, indSubtypeEquivPi_ρ_apply,
    indLeftCosetCoinvariantEquiv_apply]
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel S
  have hq : q = (((e.symm q).out⁻¹ : G) : G ⧸ S) := by
    rw [← QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk, Quotient.out_eq',
      e.apply_symm_apply]
  have hcos : e (Quotient.mk'' ((e.symm q).out * g)) = g⁻¹ • q := by
    conv_rhs => rw [hq]
    rw [QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk, MulAction.Quotient.smul_coe,
      smul_eq_mul, mul_inv_rev]
  congr 2
  apply congrArg (indSubtypeEquivPi A x)
  simpa using congrArg e.symm hcos

/-- Induced intertwiners act on the values of the free left-coset model. -/
theorem indLeftCosetCoinvariantEquiv_indMap {A B : Rep.{max w u} k S} (f : A ⟶ B)
    (x : Rep.ind S.subtype A) (q : G ⧸ S) :
    indLeftCosetCoinvariantEquiv B ((Rep.indMap S.subtype f).hom x) q =
      f.hom (indLeftCosetCoinvariantEquiv A x q) := by
  rw [indLeftCosetCoinvariantEquiv_apply, indLeftCosetCoinvariantEquiv_apply,
    Rep.indSubtypeEquivPi_indMap]

-- Normalize the induced carrier and generator so simp can match them in importing modules.
/-- An arbitrary coinvariant generator becomes a single vector at `g⁻¹S`; its value is corrected
by the inverse of the right-coset factor of `g`. -/
@[simp]
theorem indLeftCosetCoinvariantEquiv_mk (A : Rep.{max w u} k S) (g : G) (a : A) :
    (dsimp% only [Representation.IndV.mk, LinearMap.comp_apply, TensorProduct.mk_apply]
      (indLeftCosetCoinvariantEquiv A (Representation.IndV.mk S.subtype A.ρ g a))) =
      Finsupp.single (QuotientGroup.quotientRightRelEquivQuotientLeftRel S
        (Quotient.mk'' g)) (A.ρ (rightCosetFactor (S := S) g)⁻¹ a) := by
  classical
  ext p
  obtain ⟨p, rfl⟩ := (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).surjective p
  rw [indLeftCosetCoinvariantEquiv_apply, Equiv.symm_apply_apply]
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  have hmodel : indSubtypeEquivPi A (Representation.IndV.mk S.subtype A.ρ g a) p =
      indToCoindAux A g a p.out := by
    rw [indSubtypeEquivPi_apply]
    -- Pass to the underlying linear map to use Mathlib's comparison-map equation.
    change (((indCoindIso.{w, u, v} A).hom.hom.toLinearMap
      (Representation.IndV.mk S.subtype A.ρ g a))).1 p.out = _
    rw [indCoindIso_hom_hom_toLinearMap]
    exact congrFun (TauCeti.indToCoind_mk g a) p.out
  dsimp only [Representation.IndV.mk, LinearMap.comp_apply, TensorProduct.mk_apply] at hmodel
  rw [hmodel]
  by_cases hp : p = Quotient.mk'' g
  · subst p
    rw [eq_inv_mul_of_mul_eq (rightCosetFactor_mul_out g), ← Subgroup.coe_inv,
      indToCoindAux_mul_snd, indToCoindAux_self]
    simp
  · have hrel : ¬(QuotientGroup.rightRel S).r p.out g := by
      intro h
      exact hp (by simpa using Quotient.sound h)
    rw [indToCoindAux_of_not_rel _ _ _ hrel]
    simp [hp]

-- Normalize the induced carrier in the statement so simp can match it after reducing `Rep.ind`.
/-- The inverse left-coset model sends a single vector to its chosen coinvariant generator. -/
@[simp]
theorem indLeftCosetCoinvariantEquiv_symm_single (A : Rep.{max w u} k S)
    (q : G ⧸ S) (a : A) :
    (dsimp% only ((indLeftCosetCoinvariantEquiv A).symm (Finsupp.single q a))) =
      Representation.IndV.mk S.subtype A.ρ
        ((QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm q).out a := by
  apply (indLeftCosetCoinvariantEquiv A).injective
  rw [LinearEquiv.apply_symm_apply]
  simp [Representation.IndV.mk]

end Rep
