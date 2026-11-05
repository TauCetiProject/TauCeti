/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialPresentation

/-!
# Varying-base maps on iterated polynomial algebras

The augmented polynomial stages are `B`, `R[B]`, `R[R[B]]`, and so on. A commutative
square of ring maps induces maps on all these stages, by mapping coefficients and
renaming variables. These maps preserve the counit faces and comultiplication degeneracies,
including the augmentation, and respect identities and composition.

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

namespace CommAlgCat.PolynomialResolution

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The augmented polynomial stages, with the original algebra in stage zero.
The body is exposed so callers can use each successor stage as a polynomial ring. -/
abbrev stage (R : Type u) [CommRing R] (B : CommAlgCat.{u} R) : ℕ → CommAlgCat.{u} R
  | 0 => B
  | n + 1 => CommAlgCat.of R (MvPolynomial (stage R B n) R)

theorem stage_zero (B : CommAlgCat.{u} R) : stage R B 0 = B := rfl

theorem stage_succ (B : CommAlgCat.{u} R) (n : ℕ) :
    stage R B (n + 1) = CommAlgCat.of R (MvPolynomial (stage R B n) R) := rfl

variable {B : CommAlgCat.{u} R} {C : CommAlgCat.{u} S} {D : CommAlgCat.{u} T}

/-- Map all stages by a base-ring map and a map of the original algebras.
Compatibility with the scalar maps is needed only for compatibility with the faces. -/
def map (f : R →+* S) (g : B →+* C) :
    (n : ℕ) → stage R B n →+* stage S C n
  | 0 => g
  | n + 1 => eval₂Hom (MvPolynomial.C.comp f) (fun b => X (map f g n b))

@[simp] theorem map_zero (f : R →+* S) (g : B →+* C) : map f g 0 = g := (rfl)

/-- At a successor stage, map coefficients and rename the polynomial variables. -/
@[simp] theorem map_succ (f : R →+* S) (g : B →+* C) (n : ℕ) :
    map f g (n + 1) = eval₂Hom (MvPolynomial.C.comp f) (fun b => X (map f g n b)) := (rfl)

/-- Identity squares induce identity maps in every degree. -/
@[simp] theorem map_id (n : ℕ) :
    map (RingHom.id R) (RingHom.id B) n = RingHom.id _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply MvPolynomial.ringHom_ext <;> intro x <;>
      simp [map, eval₂Hom_C, eval₂Hom_X', ih]

/-- Composition of ring squares is preserved in every degree. -/
@[simp] theorem map_comp (f : R →+* S) (g : B →+* C)
    (f' : S →+* T) (g' : C →+* D) (n : ℕ) :
    map (f'.comp f) (g'.comp g) n = (map f' g' n).comp (map f g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply MvPolynomial.ringHom_ext <;> intro x <;>
      simp [map, eval₂Hom_C, eval₂Hom_X', ih]

/-- A commutative ring square remains commutative on all polynomial stages. -/
theorem map_algebraMap (f : R →+* S) (g : B →+* C)
    (h : g.comp (algebraMap R B) = (algebraMap S C).comp f) (n : ℕ) (r : R) :
    map f g n (algebraMap R (stage R B n) r) =
      algebraMap S (stage S C n) (f r) := by
  cases n with
  | zero => exact DFunLike.congr_fun h r
  | succ n => simp

/-- Counit faces, indexed from the outermost polynomial algebra.
For `n = 0` this is the augmentation `R[B] → B`. -/
def face (B : CommAlgCat.{u} R) :
    (n : ℕ) → Fin (n + 1) → (stage R B (n + 1) ⟶ stage R B n)
  | 0, _ => CommAlgCat.ofHom (aeval id)
  | n + 1, i => Fin.cases
      (CommAlgCat.ofHom (aeval id))
      (fun j => CommAlgCat.ofHom (rename (face B n j).hom)) i

theorem face_zero (B : CommAlgCat.{u} R) (n : ℕ) :
    face B n 0 = (CommAlgCat.polynomialComonad R).ε.app (stage R B n) := by
  cases n <;> apply CommAlgCat.hom_ext <;>
    exact (CommAlgCat.polynomialComonad_ε_app_hom R _).symm

theorem face_succ (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    face B (n + 1) i.succ = (CommAlgCat.polynomialComonad R).map (face B n i) := (rfl)

@[simp] theorem face_zero_hom (B : CommAlgCat.{u} R) (n : ℕ) :
    (face B n 0).hom = aeval (id : stage R B n → stage R B n) := by
  cases n <;> rfl

@[simp] theorem face_succ_hom (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    (face B (n + 1) i.succ).hom = rename (face B n i).hom := (rfl)

/-- Comultiplication degeneracies, indexed from the outermost polynomial algebra. -/
def degeneracy (B : CommAlgCat.{u} R) :
    (n : ℕ) → Fin (n + 1) → (stage R B (n + 1) ⟶ stage R B (n + 2))
  | 0, _ => CommAlgCat.ofHom (rename (X (R := R)))
  | n + 1, i => Fin.cases
      (CommAlgCat.ofHom (rename (X (R := R))))
      (fun j => CommAlgCat.ofHom (rename (degeneracy B n j).hom)) i

theorem degeneracy_zero (B : CommAlgCat.{u} R) (n : ℕ) :
    degeneracy B n 0 = (CommAlgCat.polynomialComonad R).δ.app (stage R B n) := by
  cases n <;> apply CommAlgCat.hom_ext <;>
    exact (CommAlgCat.polynomialComonad_δ_app_hom R _).symm

theorem degeneracy_succ (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    degeneracy B (n + 1) i.succ =
      (CommAlgCat.polynomialComonad R).map (degeneracy B n i) := (rfl)

@[simp] theorem degeneracy_zero_hom (B : CommAlgCat.{u} R) (n : ℕ) :
    (degeneracy B n 0).hom = rename (X (R := R) : stage R B n → _) := by
  cases n <;> rfl

@[simp] theorem degeneracy_succ_hom (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    (degeneracy B (n + 1) i.succ).hom = rename (degeneracy B n i).hom := (rfl)

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
      simpa [map, face, eval₂Hom_C] using DFunLike.congr_fun h x
    · intro x
      simp [map, face, eval₂Hom_X']
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply MvPolynomial.ringHom_ext <;> intro x <;>
        simp [map, face, eval₂Hom_C, eval₂Hom_X']
    · apply MvPolynomial.ringHom_ext
      · intro x
        simp [map, face, eval₂Hom_C]
      · intro x
        simpa only [map, face, Fin.cases_succ, CommAlgCat.hom_ofHom,
          RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          rename_X, eval₂Hom_X'] using
          congrArg (X (R := S)) (DFunLike.congr_fun (ih j) x)

/-- Varying-base stage maps commute with every comultiplication degeneracy. -/
theorem map_degeneracy (f : R →+* S) (g : B →+* C) (n : ℕ) (i : Fin (n + 1)) :
    (map f g (n + 2)).comp (degeneracy B n i).hom.toRingHom =
      (degeneracy C n i).hom.toRingHom.comp (map f g (n + 1)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    apply MvPolynomial.ringHom_ext <;> intro x <;>
      simp [map, degeneracy, eval₂Hom_C, eval₂Hom_X']
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply MvPolynomial.ringHom_ext <;> intro x <;>
        simp [map, degeneracy, eval₂Hom_C, eval₂Hom_X']
    · apply MvPolynomial.ringHom_ext
      · intro x
        simp [map, degeneracy, eval₂Hom_C]
      · intro x
        simpa only [map, degeneracy, Fin.cases_succ, CommAlgCat.hom_ofHom,
          RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          rename_X, eval₂Hom_X'] using
          congrArg (X (R := S)) (DFunLike.congr_fun (ih j) x)

end CommAlgCat.PolynomialResolution
