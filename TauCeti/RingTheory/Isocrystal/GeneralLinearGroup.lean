/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Isocrystal
public import TauCeti.GroupTheory.TwistedConjugacy.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Semilinear
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Witt isocrystals and twisted conjugacy in the general linear group

Over the Witt fraction field of a perfect field of characteristic `p`, specifying an
invertible matrix `b` specifies an isocrystal on the standard coordinate space with
Frobenius `x ↦ b σ(x)`. Every finite-dimensional isocrystal has such a presentation, and
its isomorphism class determines exactly one twisted conjugacy class of matrices. This
allows invariants of the isocrystal to be computed on matrix representatives.

## References

* R. E. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), p. 202.
-/

public section

open scoped Isocrystal
open WittVector
open Matrix.GeneralLinearGroup

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
variable {n : ℕ}

/-- The isocrystal on the standard coordinate space with Frobenius `x ↦ b σ(x)`,
where `σ` is the arithmetic Frobenius of the Witt fraction field. -/
noncomputable abbrev wittGLIsocrystal (b : Matrix.GeneralLinearGroup (Fin n) K(p, k)) :
    Isocrystal p k (Fin n → K(p, k)) where
  frob := semilinearEquiv (Fin n) (FractionRing.frobenius p k) b

/-- The Frobenius of the matrix presentation is the associated semilinear equivalence. -/
theorem wittGLIsocrystal_frobenius_eq_semilinearEquiv
    (b : Matrix.GeneralLinearGroup (Fin n) K(p, k)) :
    letI := wittGLIsocrystal p k b
    Φ(p, k) = semilinearEquiv (Fin n) (FractionRing.frobenius p k) b := (rfl)

@[simp]
theorem wittGLIsocrystal_frobenius_apply (b : Matrix.GeneralLinearGroup (Fin n) K(p, k))
    (x : Fin n → K(p, k)) :
    letI := wittGLIsocrystal p k b
    Φ(p, k) x =
      Matrix.mulVec (↑b : Matrix (Fin n) (Fin n) K(p, k)) (FractionRing.frobenius p k ∘ x) := by
  rw [wittGLIsocrystal_frobenius_eq_semilinearEquiv]
  exact semilinearEquiv_apply _ b x

-- The two isocrystal instances on the same coordinate space must be supplied separately.
local notation "withWittGLIsocrystals(" op ", " p ", " k ", " b ", " c ")" =>
  @op p _ k _ _ _ _ _ (wittGLIsocrystal p k b) _ _ (wittGLIsocrystal p k c)

/-- Isomorphisms between the isocrystals of `b` and `c` are precisely the linear equivalences
whose matrices twisted-conjugate `b` to `c`. -/
noncomputable def wittGLConjugatorEquiv (b c : Matrix.GeneralLinearGroup (Fin n) K(p, k)) :
    {g : Matrix.GeneralLinearGroup (Fin n) K(p, k) //
      c = g * b * (mapEquiv (Fin n) (FractionRing.frobenius p k) g)⁻¹} ≃
    withWittGLIsocrystals(IsocrystalEquiv, p, k, b, c) where
  toFun g := withWittGLIsocrystals(IsocrystalEquiv.mk, p, k, b, c) (matrixLinearEquiv g.val) (by
    simp only [wittGLIsocrystal_frobenius_eq_semilinearEquiv]
    exact (intertwines_semilinearEquiv_iff _ b c g.val).mpr g.property)
  invFun f := by
    let e := withWittGLIsocrystals(IsocrystalEquiv.toLinearEquiv, p, k, b, c) f
    let g := matrixLinearEquiv.symm e
    refine ⟨g, (intertwines_semilinearEquiv_iff _ b c g).mp ?_⟩
    have hf : ∀ x, (letI := wittGLIsocrystal p k c; Φ(p, k) (e x)) =
        e (letI := wittGLIsocrystal p k b; Φ(p, k) x) :=
      withWittGLIsocrystals(IsocrystalEquiv.frob_equivariant, p, k, b, c) f
    rw [show matrixLinearEquiv g = e from matrixLinearEquiv.apply_symm_apply e]
    simp only [wittGLIsocrystal_frobenius_eq_semilinearEquiv] at hf
    exact hf
  left_inv g := Subtype.ext (matrixLinearEquiv.symm_apply_apply g.val)
  right_inv := by
    rintro ⟨f, hf⟩
    exact (withWittGLIsocrystals(IsocrystalEquiv.mk.injEq, p, k, b, c) _ _ _ _).mpr
      (matrixLinearEquiv.apply_symm_apply f)

@[simp]
theorem wittGLConjugatorEquiv_apply_toLinearEquiv
    (b c : Matrix.GeneralLinearGroup (Fin n) K(p, k))
    (g : {g : Matrix.GeneralLinearGroup (Fin n) K(p, k) //
      c = g * b * (mapEquiv (Fin n) (FractionRing.frobenius p k) g)⁻¹}) :
    withWittGLIsocrystals(IsocrystalEquiv.toLinearEquiv, p, k, b, c)
      (wittGLConjugatorEquiv p k b c g) = matrixLinearEquiv g.val := (rfl)

@[simp]
theorem wittGLConjugatorEquiv_symm_apply_val
    (b c : Matrix.GeneralLinearGroup (Fin n) K(p, k))
    (f : withWittGLIsocrystals(IsocrystalEquiv, p, k, b, c)) :
    ((wittGLConjugatorEquiv p k b c).symm f).val =
      matrixLinearEquiv.symm (withWittGLIsocrystals(IsocrystalEquiv.toLinearEquiv, p, k, b, c) f) :=
  (rfl)

/-- Two matrix presentations give isomorphic Witt isocrystals precisely when the matrices
represent the same twisted conjugacy class. -/
theorem nonempty_wittGLIsocrystalEquiv_iff
    (b c : Matrix.GeneralLinearGroup (Fin n) K(p, k)) :
    Nonempty (withWittGLIsocrystals(IsocrystalEquiv, p, k, b, c)) ↔
    TwistedConj.Classes.mk (mapEquiv (Fin n) (FractionRing.frobenius p k)).toMonoidHom b =
    TwistedConj.Classes.mk (mapEquiv (Fin n) (FractionRing.frobenius p k)).toMonoidHom c := by
  constructor
  · rintro ⟨f⟩
    let g := (wittGLConjugatorEquiv p k b c).symm f
    exact TwistedConj.Classes.mk_eq_mk_iff.mpr ⟨g.val, g.property⟩
  · intro h
    obtain ⟨g, hg⟩ := TwistedConj.Classes.mk_eq_mk_iff.mp h
    exact ⟨wittGLConjugatorEquiv p k b c ⟨g, hg⟩⟩

/-- Transport an isocrystal to a matrix using any linear coordinates. -/
theorem exists_wittGLIsocrystalEquiv_of_linearEquiv {V : Type*} [AddCommGroup V] [Isocrystal p k V]
    (e : (Fin n → K(p, k)) ≃ₗ[K(p, k)] V) :
    ∃ b : Matrix.GeneralLinearGroup (Fin n) K(p, k),
      letI := wittGLIsocrystal p k b
      ∃ f : (Fin n → K(p, k)) ≃ᶠⁱ[p, k] V, f.toLinearEquiv = e := by
  let φ := (e.trans (Isocrystal.frobenius p k (V := V))).trans e.symm
  obtain ⟨b, hb⟩ := (semilinearEquiv (Fin n) (FractionRing.frobenius p k)).surjective φ
  refine ⟨b, ?_⟩
  let := wittGLIsocrystal p k b
  refine ⟨⟨e, ?_⟩, rfl⟩
  intro x
  rw [wittGLIsocrystal_frobenius_eq_semilinearEquiv, hb]
  -- Applying the transported Frobenius `φ` sends `x` to `e.symm (Φ(p, k) (e x))`.
  exact (e.apply_symm_apply _).symm

/-- Every finite-dimensional Witt isocrystal admits a matrix presentation, whose class
is characterized by the isocrystals isomorphic to the given one. -/
theorem wittGL_isocrystal_classes (V : Type*) [AddCommGroup V] [Isocrystal p k V]
    [FiniteDimensional K(p, k) V] (hdim : Module.finrank K(p, k) V = n) :
    ∃ b : Matrix.GeneralLinearGroup (Fin n) K(p, k),
      ∀ c : Matrix.GeneralLinearGroup (Fin n) K(p, k),
        letI := wittGLIsocrystal p k c
        Nonempty ((Fin n → K(p, k)) ≃ᶠⁱ[p, k] V) ↔
        TwistedConj.Classes.mk (mapEquiv (Fin n) (FractionRing.frobenius p k)).toMonoidHom b =
        TwistedConj.Classes.mk (mapEquiv (Fin n) (FractionRing.frobenius p k)).toMonoidHom c := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (R := K(p, k)) (M := Fin n → K(p, k)) (M' := V) (by simp [hdim])
  obtain ⟨b, ⟨f, hf⟩, -⟩ := exists_wittGLIsocrystalEquiv_of_linearEquiv p k e
  refine ⟨b, fun c => ?_⟩
  let := wittGLIsocrystal p k c
  rw [eq_comm, ← nonempty_wittGLIsocrystalEquiv_iff]
  constructor
  · rintro ⟨⟨g, hg⟩⟩
    refine ⟨withWittGLIsocrystals(IsocrystalEquiv.mk, p, k, c, b) (g.trans f.symm) (fun x => ?_)⟩
    apply f.injective
    simp only [LinearEquiv.trans_apply, ← hf, f.apply_symm_apply, hg]
  · rintro ⟨⟨g, hg⟩⟩
    exact ⟨⟨g.trans f, fun x => by simp only [LinearEquiv.trans_apply, hf, hg]⟩⟩

end TauCeti
