/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Conjugate
public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism

/-!
# The conjugate-linear Chevalley involution of a Serre presentation

Over a commutative ring `R` with an involution `star` (complex conjugation for `R = ℂ`), the Lie
algebra `Matrix.ToLieAlgebra R CM` presented by Serre's relations carries a *conjugate-linear*
involution `τ` with `τ Hᵢ = -Hᵢ`, `τ Eᵢ = -Fᵢ`, `τ Fᵢ = -Eᵢ`, preserving brackets and satisfying
`τ (c • x) = star c • τ x`. For a complex semisimple Lie algebra this is the conjugation whose
fixed points form the compact real form (Knapp, Section VI.1;
Helgason, Chapter III, Section 6).

It is constructed through the universal property of the presentation, applied to the *conjugate*
Lie algebra `TauCeti.ConjLieAlgebra` of `Matrix.ToLieAlgebra R CM`: the same Lie ring, with `c`
acting as `star c`. Serre's relations have integer coefficients, so the signed exchange
`Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ` of the generators is still a Serre system there, and the
`R`-linear homomorphism it induces into the conjugate algebra is a conjugate-linear map of
`Matrix.ToLieAlgebra R CM` to itself.

Unlike `TauCeti.serreChevalleyInvolution`, which is `R`-linear, `τ` conjugates the scalars. For
`R = ℂ` this is what makes `(x, y) ↦ -B(x, τ y)` Hermitian, and the fixed set of `τ` a real form
rather than a complex subalgebra. When `star` is trivial, as for `ℤ`, `ℚ` or `ℝ`, `τ` is the
Chevalley involution (`TauCeti.serreCompactInvolution_eq_serreChevalleyInvolution`).

## Main definitions

* `TauCeti.serreCompactInvolution`: the conjugate-linear involution `τ` of
  `Matrix.ToLieAlgebra R CM`.

## Main results

* `TauCeti.IsSerreSystem.toConj`: a Serre system is a Serre system in the conjugate Lie algebra.
* `TauCeti.serreCompactInvolution_serreH` and its companions: the values on the generators.
* `TauCeti.serreCompactInvolution_lie`: `τ` preserves brackets.
* `TauCeti.serreCompactInvolution_serreCompactInvolution`: `τ ∘ τ = id`.
* `TauCeti.eq_serreCompactInvolution`: `τ` is the unique bracket-preserving conjugate-linear map
  with these values on the generators.
* `TauCeti.serreCompactInvolution_eq_serreChevalleyInvolution`: for a trivial star, `τ` is the
  Chevalley involution.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Section VI.1.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Academic Press, 1978,
  Chapter III, Section 6.
-/

public section

namespace TauCeti

variable {B : Type*} (R : Type*) [CommRing R] [StarRing R] (CM : Matrix B B ℤ)

open ConjLieAlgebra

variable {R CM} in
/-- A Serre system in `L` is a Serre system in the conjugate Lie algebra: Serre's relations have
integer coefficients, so they pass through the `ℤ`-linear identification
`TauCeti.ConjLieAlgebra.toConj`. -/
theorem IsSerreSystem.toConj {L : Type*} [LieRing L] [LieAlgebra R L] {H E F : B → L}
    (h : IsSerreSystem R CM H E F) :
    IsSerreSystem R CM (toConj ∘ H) (toConj ∘ E) (toConj ∘ F) :=
  ((h.changeScalars (S := ℤ)).map ConjLieAlgebra.toConj.toLieHom).changeScalars

variable [DecidableEq B]

variable {R} in
/-- The homomorphism into the conjugate algebra inducing `TauCeti.serreCompactInvolution`. -/
private noncomputable def serreCompactHom :
    Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ ConjLieAlgebra (Matrix.ToLieAlgebra R CM) :=
  serreLift (isSerreSystem_serre R CM).neg_swap.toConj

/-- The **conjugate-linear Chevalley involution** `τ` of `Matrix.ToLieAlgebra R CM`: the
bracket-preserving map with `τ (c • x) = star c • τ x` and `Hᵢ ↦ -Hᵢ`, `Eᵢ ↦ -Fᵢ`, `Fᵢ ↦ -Eᵢ`.
For `R = ℂ` and a Cartan matrix `CM`, its fixed points are the compact real form. -/
noncomputable def serreCompactInvolution :
    Matrix.ToLieAlgebra R CM →ₛₗ[starRingEnd R] Matrix.ToLieAlgebra R CM :=
  semilinearOfLieHom (serreCompactHom CM)

variable {R CM}

private theorem serreCompactInvolution_apply (x : Matrix.ToLieAlgebra R CM) :
    serreCompactInvolution R CM x = toConj.symm (serreCompactHom CM x) :=
  rfl

variable (R CM) in
/-- `τ` sends `Hᵢ` to `-Hᵢ`. -/
@[simp]
theorem serreCompactInvolution_serreH (i : B) :
    serreCompactInvolution R CM (serreH R CM i) = -serreH R CM i := by
  rw [serreCompactInvolution_apply, serreCompactHom, serreLift_serreH, Function.comp_apply,
    LieEquiv.symm_apply_apply]

variable (R CM) in
/-- `τ` sends `Eᵢ` to `-Fᵢ`. -/
@[simp]
theorem serreCompactInvolution_serreE (i : B) :
    serreCompactInvolution R CM (serreE R CM i) = -serreF R CM i := by
  rw [serreCompactInvolution_apply, serreCompactHom, serreLift_serreE, Function.comp_apply,
    LieEquiv.symm_apply_apply]

variable (R CM) in
/-- `τ` sends `Fᵢ` to `-Eᵢ`. -/
@[simp]
theorem serreCompactInvolution_serreF (i : B) :
    serreCompactInvolution R CM (serreF R CM i) = -serreE R CM i := by
  rw [serreCompactInvolution_apply, serreCompactHom, serreLift_serreF, Function.comp_apply,
    LieEquiv.symm_apply_apply]

/-- `τ` preserves brackets. -/
@[simp]
theorem serreCompactInvolution_lie (x y : Matrix.ToLieAlgebra R CM) :
    serreCompactInvolution R CM ⁅x, y⁆ =
      ⁅serreCompactInvolution R CM x, serreCompactInvolution R CM y⁆ :=
  semilinearOfLieHom_lie (serreCompactHom CM) x y

/-- `τ` is the unique bracket-preserving conjugate-linear map of `Matrix.ToLieAlgebra R CM` sending
`Eᵢ` to `-Fᵢ` and `Fᵢ` to `-Eᵢ`; its value `-Hᵢ` on `Hᵢ = ⁅Eᵢ, Fᵢ⁆` is then forced. -/
theorem eq_serreCompactInvolution
    {f : Matrix.ToLieAlgebra R CM →ₛₗ[starRingEnd R] Matrix.ToLieAlgebra R CM}
    (hf : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆)
    (hE : ∀ i, f (serreE R CM i) = -serreF R CM i)
    (hF : ∀ i, f (serreF R CM i) = -serreE R CM i) :
    f = serreCompactInvolution R CM := by
  have h : lieHomOfSemilinear f hf = serreCompactHom CM :=
    eq_serreLift (fun i => by rw [lieHomOfSemilinear_apply, hE, Function.comp_apply])
      fun i => by rw [lieHomOfSemilinear_apply, hF, Function.comp_apply]
  rw [serreCompactInvolution, ← h, semilinearOfLieHom_lieHomOfSemilinear]

/-- Applying `τ` twice returns the original element. -/
@[simp]
theorem serreCompactInvolution_serreCompactInvolution (x : Matrix.ToLieAlgebra R CM) :
    serreCompactInvolution R CM (serreCompactInvolution R CM x) = x := by
  let g : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM :=
    { toFun y := serreCompactInvolution R CM (serreCompactInvolution R CM y)
      map_add' y z := by simp only [map_add]
      map_smul' c y := by simp only [map_smulₛₗ, starRingEnd_self_apply, RingHom.id_apply]
      map_lie' := by simp only [serreCompactInvolution_lie, implies_true] }
  have h : g = LieHom.id := serre_hom_ext (fun i => by simp [g]) fun i => by simp [g]
  exact DFunLike.congr_fun h x

variable (R CM) in
/-- `τ` is an involution. -/
theorem serreCompactInvolution_involutive :
    Function.Involutive (serreCompactInvolution R CM) :=
  serreCompactInvolution_serreCompactInvolution

/-- For a trivial star, as on `ℤ`, `ℚ` or `ℝ`, `τ` is the Chevalley involution. -/
theorem serreCompactInvolution_eq_serreChevalleyInvolution [TrivialStar R]
    (x : Matrix.ToLieAlgebra R CM) :
    serreCompactInvolution R CM x = serreChevalleyInvolution R CM x := by
  let g : Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM :=
    { toFun := serreCompactInvolution R CM
      map_add' := map_add _
      map_smul' c y := by simp only [map_smulₛₗ, starRingEnd_apply, star_trivial,
        RingHom.id_apply]
      map_lie' := serreCompactInvolution_lie _ _ }
  have h : g = (serreChevalleyInvolution R CM :
      Matrix.ToLieAlgebra R CM →ₗ⁅R⁆ Matrix.ToLieAlgebra R CM) :=
    eq_serreChevalleyInvolution R CM (fun i => by simp [g]) fun i => by simp [g]
  exact DFunLike.congr_fun h x

end TauCeti
