/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialResolution.Basic

/-!
# Varying-base maps on iterated polynomial algebras

A commutative square of ring maps induces maps on the augmented polynomial stages
`B`, `R[B]`, `R[R[B]]`, and so on, by mapping coefficients and renaming variables.
These maps preserve the counit faces and comultiplication degeneracies, including
the augmentation, and respect identities and composition.

The stages and operators are iterates of `CommAlgCat.polynomialComonad`, not a separate
choice of polynomial presentations. This supplies varying-base compatibility before
assembling the stages into an augmented simplicial algebra. No resolution or acyclicity
assertion is made here.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM), the standard polynomial resolution.
-/

public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace TauCeti.PolynomialResolution

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {B : CommAlgCat.{u} R} {C : CommAlgCat.{u} S} {D : CommAlgCat.{u} T}

/-- Map all stages by a base-ring map and a map of the original algebras.
Compatibility with the scalar maps is needed only for compatibility with the faces. -/
def map (f : R →+* S) (g : B →+* C) :
    (n : ℕ) → stage R B n →+* stage S C n
  | 0 => g
  | n + 1 => (MvPolynomial.map f).comp (rename (map f g n)).toRingHom

@[simp] theorem map_stage_zero (f : R →+* S) (g : B →+* C) : map f g 0 = g := (rfl)

/-- At a successor stage, map coefficients and rename the polynomial variables. -/
@[simp] theorem map_stage_succ (f : R →+* S) (g : B →+* C) (n : ℕ) :
    map f g (n + 1) = (MvPolynomial.map f).comp (rename (map f g n)).toRingHom := (rfl)

/-- Identity squares induce identity maps in every degree. -/
@[simp] theorem map_id (n : ℕ) :
    map (RingHom.id R) (RingHom.id B) n = RingHom.id _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply RingHom.ext
    intro p
    simp [map_stage_succ, ih, MvPolynomial.map_id]

/-- Composition of ring squares is preserved in every degree. -/
@[simp] theorem map_comp (f : R →+* S) (g : B →+* C)
    (f' : S →+* T) (g' : C →+* D) (n : ℕ) :
    map (f'.comp f) (g'.comp g) n = (map f' g' n).comp (map f g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply RingHom.ext
    intro p
    simp [map_stage_succ, ih, map_rename, map_map, Function.comp_def]

/-- A commutative ring square remains commutative on all polynomial stages. -/
theorem map_algebraMap (f : R →+* S) (g : B →+* C)
    (h : g.comp (algebraMap R B) = (algebraMap S C).comp f) (n : ℕ) (r : R) :
    map f g n (algebraMap R (stage R B n) r) =
      algebraMap S (stage S C n) (f r) := by
  cases n with
  | zero => exact DFunLike.congr_fun h r
  | succ n => simp

/-- Lift a commuting square of stage maps through one polynomial layer. -/
private theorem map_succ_comp_rename (f : R →+* S) (g : B →+* C) (k m : ℕ)
    (φ : stage R B k →+* stage R B m) (ψ : stage S C k →+* stage S C m)
    (h : (map f g m).comp φ = ψ.comp (map f g k)) :
    (map f g (m + 1)).comp (rename φ).toRingHom =
      (rename ψ).toRingHom.comp (map f g (k + 1)) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [map_stage_succ]
  · intro x
    simpa using congrArg (X (R := S)) (DFunLike.congr_fun h x)

/-- Varying-base stage maps commute with every counit face, including augmentation. -/
theorem map_face (f : R →+* S) (g : B →+* C)
    (h : g.comp (algebraMap R B) = (algebraMap S C).comp f)
    (n : ℕ) (i : Fin (n + 1)) :
    (map f g n).comp (face B n i).hom.toRingHom =
      (face C n i).hom.toRingHom.comp (map f g (n + 1)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    apply MvPolynomial.ringHom_ext
    · intro x
      simpa using DFunLike.congr_fun h x
    · intro x
      simp
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply MvPolynomial.ringHom_ext <;> intro x <;> simp
    · simpa using map_succ_comp_rename f g (n + 1) n
        (face B n j).hom.toRingHom (face C n j).hom.toRingHom (ih j)

/-- Varying-base stage maps commute with every comultiplication degeneracy. -/
theorem map_degeneracy (f : R →+* S) (g : B →+* C) (n : ℕ) (i : Fin (n + 1)) :
    (map f g (n + 2)).comp (degeneracy B n i).hom.toRingHom =
      (degeneracy C n i).hom.toRingHom.comp (map f g (n + 1)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply MvPolynomial.ringHom_ext <;> intro x <;> simp
    · simpa using map_succ_comp_rename f g (n + 1) (n + 2)
        (degeneracy B n j).hom.toRingHom (degeneracy C n j).hom.toRingHom (ih j)

end TauCeti.PolynomialResolution
