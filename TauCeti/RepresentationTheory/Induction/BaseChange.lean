/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Scalar extension of finite-index induction

Scalar extension commutes with induction from a finite-index subgroup, over commutative rings.
The comparison matches the two finite coset models coordinatewise. Its evaluation and naturality
formulas allow it to be used in computations and to descend to Grothendieck groups.

The construction uses `TauCeti.Rep.indSubtypeEquivPi` and Mathlib's `TensorProduct.piRight`.
No flatness or finite generation of the representation is required.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.
-/

open TensorProduct

public section

namespace Rep

universe u v w t

variable {R : Type u} {A : Type v} {G : Type w} [CommRing R] [CommRing A] [Algebra R A] [Group G]
  {S : Subgroup G} [S.FiniteIndex]

private noncomputable def indBaseChangeLinearEquiv (V : Rep.{max t u} R S) :
    A ⊗[R] Rep.ind S.subtype V ≃ₗ[A]
      Rep.ind S.subtype (Rep.of (V.ρ.baseChange A)) := by
  classical
  letI : Finite (Quotient (QuotientGroup.rightRel S)) :=
    .of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _
  exact ((TauCeti.Rep.indSubtypeEquivPi V).baseChange R A _ _).trans
    ((piRight R A A (fun _ : Quotient (QuotientGroup.rightRel S) ↦ V)).trans
      (TauCeti.Rep.indSubtypeEquivPi (Rep.of (V.ρ.baseChange A))).symm)

private theorem indBaseChangeLinearEquiv_tmul (V : Rep.{max t u} R S) (a : A)
    (x : Rep.ind S.subtype V) (q : Quotient (QuotientGroup.rightRel S)) :
    TauCeti.Rep.indSubtypeEquivPi (Rep.of (V.ρ.baseChange A))
        (indBaseChangeLinearEquiv V (a ⊗ₜ[R] x)) q =
      a ⊗ₜ[R] TauCeti.Rep.indSubtypeEquivPi V x q := by
  classical
  simp [indBaseChangeLinearEquiv]

/-- Extending scalars commutes with induction from a finite-index subgroup. The comparison
identifies the scalar extensions of the coordinates in the right-coset model of induction. -/
noncomputable def indBaseChangeEquiv (V : Rep.{max t u} R S) :
    ((Rep.ind S.subtype V).ρ.baseChange A).Equiv
      (Rep.ind S.subtype (Rep.of (V.ρ.baseChange A))).ρ :=
  Representation.Equiv.mk (indBaseChangeLinearEquiv V) fun g ↦ by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    | tmul a x =>
      apply (TauCeti.Rep.indSubtypeEquivPi (Rep.of (V.ρ.baseChange A))).injective
      funext q
      simp only [Representation.baseChange_apply, LinearMap.baseChange_tmul,
        indBaseChangeLinearEquiv_tmul (A := A) V]
      rw [TauCeti.Rep.indSubtypeEquivPi_ρ_apply, TauCeti.Rep.indSubtypeEquivPi_ρ_apply,
        indBaseChangeLinearEquiv_tmul (A := A) V]
      simp

/-- In coset coordinates, the induction comparison sends `a ⊗ x` to the function
whose coordinate at `q` is `a ⊗ x(q)`. -/
@[simp↓]
theorem indBaseChangeEquiv_tmul (V : Rep.{max t u} R S) (a : A)
    (x : Rep.ind S.subtype V) (q : Quotient (QuotientGroup.rightRel S)) :
    TauCeti.Rep.indSubtypeEquivPi (Rep.of (V.ρ.baseChange A))
        (indBaseChangeEquiv V (a ⊗ₜ[R] x)) q =
      a ⊗ₜ[R] TauCeti.Rep.indSubtypeEquivPi V x q :=
  indBaseChangeLinearEquiv_tmul V a x q

/-- On the generators of induction, the comparison moves scalar extension inside the
induced generator, retaining its group coordinate. -/
@[simp↓]
theorem indBaseChangeEquiv_tmul_mk (V : Rep.{max t u} R S) (a : A) (g : G) (x : V) :
    indBaseChangeEquiv V (a ⊗ₜ[R] Representation.IndV.mk S.subtype V.ρ g x) =
      Representation.IndV.mk S.subtype (V.ρ.baseChange A) g (a ⊗ₜ[R] x) := by
  classical
  let : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  apply (TauCeti.Rep.indSubtypeEquivPi (Rep.of (V.ρ.baseChange A))).injective
  funext q
  rw [indBaseChangeEquiv_tmul, TauCeti.Rep.indSubtypeEquivPi_apply,
    TauCeti.Rep.indSubtypeEquivPi_apply]
  simp only [← Representation.IntertwiningMap.toLinearMap_apply,
    Rep.indCoindIso_hom_hom_toLinearMap]
  simp only [Rep.indToCoind, Representation.IndV.mk, LinearMap.comp_apply,
    Representation.Coinvariants.lift_mk]
  simp [Rep.indToCoindAux]
  split <;> simp

/-- The inverse comparison moves a scalar-extended induced generator outside induction. -/
@[simp↓]
theorem indBaseChangeEquiv_symm_mk_tmul (V : Rep.{max t u} R S) (a : A) (g : G) (x : V) :
    (indBaseChangeEquiv (A := A) V).symm
        (Representation.IndV.mk S.subtype (V.ρ.baseChange A) g (a ⊗ₜ[R] x)) =
      a ⊗ₜ[R] Representation.IndV.mk S.subtype V.ρ g x := by
  have h := congrArg (indBaseChangeEquiv (A := A) V).symm
    (indBaseChangeEquiv_tmul_mk V a g x).symm
  simpa only [Representation.Equiv.symm_apply_apply] using h

/-- The comparison commutes with an induced morphism and its scalar extension. -/
theorem indBaseChangeEquiv_naturality {V W : Rep.{max t u} R S} (f : V ⟶ W)
    (z : A ⊗[R] Rep.ind S.subtype V) :
    indBaseChangeEquiv W ((Rep.indMap S.subtype f).hom.baseChange A z) =
      (Rep.indMap S.subtype (Rep.ofHom (f.hom.baseChange A))).hom (indBaseChangeEquiv V z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul a x =>
    apply (TauCeti.Rep.indSubtypeEquivPi (Rep.of (W.ρ.baseChange A))).injective
    funext q
    rw [Representation.IntertwiningMap.baseChange_tmul, indBaseChangeEquiv_tmul,
      Rep.indSubtypeEquivPi_indMap, Rep.indSubtypeEquivPi_indMap, indBaseChangeEquiv_tmul]
    simp

end Rep
