/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import TauCeti.Algebra.Module.StablyFree.Semilocal

/-!
# Transitivity on unimodular frames over semilocal rings

A unimodular `k`-frame of `Rⁿ` is an `n × k` matrix `A` with a left inverse `B * A = 1`: its
columns form a basis of a free direct summand of `Rⁿ`. The general linear group `GL n R` acts on
the `n × k` matrices by left multiplication, and this action preserves frames, `B * g⁻¹` being a
left inverse of `g • A`. The standard frame `(1 : Matrix n n R).submatrix id f` of an injective
`f : k → n` is the frame of the standard basis vectors `e_(f a)`; its stabiliser is computed in
`TauCeti.stabilizer_submatrix_one` and, for the first `r` standard basis vectors of `Rⁿ`, it is the
affine group `A_{n-r,r}(R)` of `TauCeti.stabilizerCastLEEquivAffineGroup`.

Over a commutative semilocal ring, one with finitely many maximal ideals, `GL n R` acts
transitively on the `k`-frames of `Rⁿ` for every `k`: every frame is the first `k` columns of an
invertible matrix, that is, it completes to a basis of `Rⁿ`. If `B * A = 1`, then `Rⁿ` is the direct
sum of the image of `A`, free of rank `k`, and the kernel of `B`; this kernel is therefore finitely
generated and stably free, hence free of rank `n - k` over a semilocal ring
(`Module.free_of_isStablyFree_of_finite_maximalSpectrum`). Two frames `A` and `A'` have isomorphic
complements, and the isomorphism of `Rⁿ` sending `A` to `A'` and one complement onto the other is
the required matrix.

Without the semilocal hypothesis transitivity fails: over `ℝ[x, y, z] ⧸ (x² + y² + z² - 1)` the
unimodular vector `(x, y, z)` is the frame of no basis of `R³`, the tangent bundle of the sphere
being stably free and not free.

## Main results

* `TauCeti.exists_smul_eq_of_mul_eq_one`: over a semilocal ring, any two `k`-frames of `Rⁿ` lie in
  the same orbit of `GL n R`.
* `TauCeti.orbit_submatrix_one`: over a semilocal ring, the orbit of the standard frame of an
  injective `f : k → n` consists of exactly the `n × k` matrices with a left inverse.

## References

* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. 60 (1980), 269–295,
  2.4 (unimodular sequences).
* Yu. P. Nesterenko, A. A. Suslin, *Homology of the full linear group over a local ring, and
  Milnor's K-theory*, Izv. Akad. Nauk SSSR Ser. Mat. 53 (1989), §1.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] {n k : Type*} [Fintype n] [DecidableEq n] [DecidableEq k]

section Complement

variable [Fintype k]

/-- A frame `A` with left inverse `B` splits `Rⁿ` as `Rᵏ × ker B`, by `(x, m) ↦ A x + m`, with
inverse `v ↦ (B v, v - A B v)`. -/
private def frameComplEquiv {A : Matrix n k R} {B : Matrix k n R} (h : B * A = 1) :
    ((k → R) × LinearMap.ker B.mulVecLin) ≃ₗ[R] (n → R) :=
  LinearEquiv.ofLinearMap (A.mulVecLin.coprod (LinearMap.ker B.mulVecLin).subtype)
    (B.mulVecLin.prod <| (LinearMap.id - A.mulVecLin ∘ₗ B.mulVecLin).codRestrict _ fun v ↦ by
      simp [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc, h])
    (by ext v; simp)
    (LinearMap.ext fun ⟨x, m⟩ ↦ by
      have hm : B *ᵥ (m : n → R) = 0 := m.property
      simp [Prod.ext_iff, mulVec_add, mulVec_mulVec, h, hm, Subtype.ext_iff])

private theorem frameComplEquiv_apply {A : Matrix n k R} {B : Matrix k n R} (h : B * A = 1)
    (x : k → R) (m : LinearMap.ker B.mulVecLin) : frameComplEquiv h (x, m) = A *ᵥ x + m :=
  (rfl)

private theorem frameComplEquiv_symm_mulVec {A : Matrix n k R} {B : Matrix k n R} (h : B * A = 1)
    (x : k → R) : (frameComplEquiv h).symm (A *ᵥ x) = (x, 0) := by
  rw [LinearEquiv.symm_apply_eq, frameComplEquiv_apply, Submodule.coe_zero, add_zero]

omit [DecidableEq n] in
/-- Over a semilocal ring, the kernel of a left inverse `B` of a frame `A` is free, of rank
`card n - card k`. -/
private theorem nonempty_basis_ker [Finite (MaximalSpectrum R)] [Nontrivial R]
    {A : Matrix n k R} {B : Matrix k n R} (h : B * A = 1) :
    Nonempty (Module.Basis (Fin (Fintype.card n - Fintype.card k)) R
      (LinearMap.ker B.mulVecLin)) := by
  classical
  let e := frameComplEquiv h
  have : Module.Finite R (LinearMap.ker B.mulVecLin) :=
    Module.Finite.of_surjective ((LinearMap.snd R (k → R) _).comp e.symm.toLinearMap)
      ((LinearMap.snd_surjective (R := R) (M := k → R)).comp e.symm.surjective)
  have : Module.Free R ((k → R) × LinearMap.ker B.mulVecLin) := .of_equiv e.symm
  have : Module.IsStablyFree R (LinearMap.ker B.mulVecLin) := .of_free_prod' R _ (k → R)
  have := Module.free_of_isStablyFree_of_finite_maximalSpectrum R (LinearMap.ker B.mulVecLin)
  have he := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    at he
  exact ⟨Module.finBasisOfFinrankEq R _ (by omega)⟩

end Complement

variable [Finite k]

/-- Over a commutative semilocal ring `R`, `GL n R` acts transitively on the unimodular `k`-frames
of `Rⁿ`: if the `n × k` matrices `A` and `A'` have left inverses, then `g • A = A'` for some
invertible `g`. -/
theorem exists_smul_eq_of_mul_eq_one [Finite (MaximalSpectrum R)] {A A' : Matrix n k R}
    {B B' : Matrix k n R} (h : B * A = 1) (h' : B' * A' = 1) : ∃ g : GL n R, g • A = A' := by
  cases subsingleton_or_nontrivial R
  · exact ⟨1, Subsingleton.elim _ _⟩
  have := Fintype.ofFinite k
  let e := frameComplEquiv h
  let e' := frameComplEquiv h'
  obtain ⟨b⟩ := nonempty_basis_ker h
  obtain ⟨b'⟩ := nonempty_basis_ker h'
  -- the automorphism `A x + m ↦ A' x + φ m` of `Rⁿ`, for an isomorphism `φ` of the complements
  let L := e.symm ≪≫ₗ (LinearEquiv.refl R (k → R)).prodCongr (b.equiv b' (Equiv.refl _)) ≪≫ₗ e'
  let g : GL n R := GeneralLinearGroup.toLin.symm (.ofLinearEquiv L)
  have hg (v : n → R) : (g : Matrix n n R) *ᵥ v = L v := by
    rw [← mulVecLin_apply, ← GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply]
    simp
  refine ⟨g, toLin'.injective (LinearMap.ext fun x ↦ ?_)⟩
  rw [GeneralLinearGroup.smul_def, toLin'_apply, toLin'_apply, ← mulVec_mulVec, hg]
  simp [L, e, e', frameComplEquiv_symm_mulVec, frameComplEquiv_apply]

/-- Over a commutative semilocal ring, the orbit under `GL n R` of a unimodular `k`-frame of `Rⁿ`
is the set of all unimodular `k`-frames, the `n × k` matrices with a left inverse. -/
theorem orbit_eq_setOf_exists_mul_eq_one [Finite (MaximalSpectrum R)] {A : Matrix n k R}
    {B : Matrix k n R} (h : B * A = 1) :
    MulAction.orbit (GL n R) A = {A' | ∃ B' : Matrix k n R, B' * A' = (1 : Matrix k k R)} := by
  ext A'
  refine ⟨?_, fun ⟨_, h'⟩ ↦ exists_smul_eq_of_mul_eq_one h h'⟩
  rintro ⟨g, rfl⟩
  refine ⟨B * ((g⁻¹ : GL n R) : Matrix n n R), ?_⟩
  dsimp only
  rw [GeneralLinearGroup.smul_def, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix n n R),
    ← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one, Matrix.one_mul, h]

/-- Over a commutative semilocal ring, the orbit under `GL n R` of the standard frame
`(e_(f a))_a` of an injective `f : k → n` is the set of all unimodular `k`-frames of `Rⁿ`, the
`n × k` matrices with a left inverse: every unimodular frame completes to a basis of `Rⁿ`. -/
theorem orbit_submatrix_one [Finite (MaximalSpectrum R)] {f : k → n}
    (hf : Function.Injective f) :
    MulAction.orbit (GL n R) ((1 : Matrix n n R).submatrix id f) =
      {A | ∃ B : Matrix k n R, B * A = (1 : Matrix k k R)} :=
  orbit_eq_setOf_exists_mul_eq_one (B := (1 : Matrix n n R).submatrix f id) <| by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, submatrix_one _ hf]

end TauCeti
