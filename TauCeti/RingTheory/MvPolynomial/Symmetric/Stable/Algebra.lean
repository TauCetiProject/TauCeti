/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Basic

/-!
# The graded algebra of symmetric functions

The symmetric functions of degree `n` over a commutative semiring `R`, the compatible families
`TauCeti.stableSymmetricSubmodule R n`, are multiplied componentwise: setting a variable to zero is
a ring homomorphism, so the product of two compatible families is compatible, and the product of
symmetric polynomials of degrees `n` and `m` has degree `n + m`. This file packages that
multiplication as a graded commutative `R`-algebra structure on the direct sum of the degree-`n`
pieces, the **ring of symmetric functions** `Λ_R`.

Reading off the members of the families in `d` variables is an algebra homomorphism to the
polynomial ring. These specializations detect equality, and recover each homogeneous component.

## Main definitions

* `TauCeti.stableSymmetricOne R`, `TauCeti.stableSymmetricMul R n m`: the unit, and the degreewise
  multiplication `Λⁿ →ₗ[R] Λᵐ →ₗ[R] Λⁿ⁺ᵐ`.
* `TauCeti.SymmetricFunction R`: the ring of symmetric functions, the direct sum over `n` of the
  symmetric functions of degree `n`. It is a commutative `R`-algebra, and a commutative ring when
  `R` is one.
* `TauCeti.SymmetricFunction.specialization R d`: the algebra homomorphism from `Λ_R` to polynomials
  in `Fin d`, which sets all but `d` of the variables to zero.

## Main results

* `TauCeti.SymmetricFunction.ext_specialization`: a symmetric function is determined by its
  specializations to all finite alphabets.
* `TauCeti.SymmetricFunction.aeval_snoc_zero_specialization`: the specializations are compatible.
* `TauCeti.SymmetricFunction.homogeneousComponent_specialization`: the component of degree `n` of a
  specialization is the specialization of the component of degree `n`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: the graded ring `Λ = ⨁ₙ Λⁿ` and its homomorphisms onto the rings of symmetric
  polynomials in finitely many variables.
-/

public section

namespace TauCeti

open MvPolynomial DirectSum

section CommSemiring

variable {R : Type*} [CommSemiring R] {n m : ℕ}

variable (R) in
/-- The unit of the symmetric functions: the family of constant polynomials `1`. -/
noncomputable def stableSymmetricOne : stableSymmetricSubmodule R 0 :=
  ⟨fun _ => ⟨1, mem_symmetricHomogeneousSubmodule.mpr ⟨IsSymmetric.one, isHomogeneous_one _ _⟩⟩,
    mem_stableSymmetricSubmodule.mpr fun _ => map_one _⟩

/-- The unit of the symmetric functions, read in `d` variables, is the constant polynomial `1`. -/
@[simp]
theorem coe_stableSymmetricProj_stableSymmetricOne (d : ℕ) :
    (stableSymmetricProj R 0 d (stableSymmetricOne R) : MvPolynomial (Fin d) R) = 1 := by
  rw [stableSymmetricOne, stableSymmetricProj_mk]

/-- The componentwise product of two compatible families. -/
private noncomputable def stableSymmetricMulAux (f : stableSymmetricSubmodule R n)
    (g : stableSymmetricSubmodule R m) : stableSymmetricSubmodule R (n + m) :=
  ⟨fun d => ⟨stableSymmetricProj R n d f * stableSymmetricProj R m d g,
      mem_symmetricHomogeneousSubmodule.mpr
        ⟨(mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).1.mul
            (mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).1,
          (mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).2.mul
            (mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).2⟩⟩,
    mem_stableSymmetricSubmodule.mpr fun d => by
      simp only [map_mul, aeval_snoc_zero_stableSymmetricProj]⟩

private theorem coe_stableSymmetricProj_stableSymmetricMulAux (d : ℕ)
    (f : stableSymmetricSubmodule R n) (g : stableSymmetricSubmodule R m) :
    (stableSymmetricProj R (n + m) d (stableSymmetricMulAux f g) : MvPolynomial (Fin d) R) =
      stableSymmetricProj R n d f * stableSymmetricProj R m d g := by
  rw [stableSymmetricMulAux, stableSymmetricProj_mk]

variable (R n m) in
/-- **The multiplication of symmetric functions in degrees `n` and `m`**: the componentwise product
of compatible families. -/
noncomputable def stableSymmetricMul :
    stableSymmetricSubmodule R n →ₗ[R] stableSymmetricSubmodule R m →ₗ[R]
      stableSymmetricSubmodule R (n + m) :=
  LinearMap.mk₂ R stableSymmetricMulAux
    (fun _ _ _ => stableSymmetricSubmodule_ext fun _ => Subtype.ext <| by
      simp [coe_stableSymmetricProj_stableSymmetricMulAux, add_mul])
    (fun _ _ _ => stableSymmetricSubmodule_ext fun _ => Subtype.ext <| by
      simp [coe_stableSymmetricProj_stableSymmetricMulAux])
    (fun _ _ _ => stableSymmetricSubmodule_ext fun _ => Subtype.ext <| by
      simp [coe_stableSymmetricProj_stableSymmetricMulAux, mul_add])
    (fun _ _ _ => stableSymmetricSubmodule_ext fun _ => Subtype.ext <| by
      simp [coe_stableSymmetricProj_stableSymmetricMulAux])

/-- **The product of symmetric functions is computed in each finite alphabet.** -/
@[simp]
theorem coe_stableSymmetricProj_stableSymmetricMul (d : ℕ) (f : stableSymmetricSubmodule R n)
    (g : stableSymmetricSubmodule R m) :
    (stableSymmetricProj R (n + m) d (stableSymmetricMul R n m f g) : MvPolynomial (Fin d) R) =
      stableSymmetricProj R n d f * stableSymmetricProj R m d g :=
  coe_stableSymmetricProj_stableSymmetricMulAux d f g

noncomputable instance : GradedMonoid.GOne fun n => stableSymmetricSubmodule R n where
  one := stableSymmetricOne R

noncomputable instance : GradedMonoid.GMul fun n => stableSymmetricSubmodule R n where
  mul f g := stableSymmetricMul R _ _ f g

/-- The graded unit of the symmetric functions is `TauCeti.stableSymmetricOne`. -/
@[simp]
theorem gOne_one_stableSymmetricSubmodule :
    GradedMonoid.GOne.one (A := fun n => stableSymmetricSubmodule R n) = stableSymmetricOne R :=
  (rfl)

/-- The graded product of the symmetric functions is `TauCeti.stableSymmetricMul`. -/
@[simp]
theorem gMul_mul_stableSymmetricSubmodule (f : stableSymmetricSubmodule R n)
    (g : stableSymmetricSubmodule R m) :
    GradedMonoid.GMul.mul (A := fun n => stableSymmetricSubmodule R n) f g =
      stableSymmetricMul R n m f g :=
  (rfl)

/-- Two graded elements of the symmetric functions are equal when their degrees agree and they
agree in each finite alphabet. The members in `d` variables are compared as polynomials, so that
the two degrees need not be definitionally equal. -/
private theorem gradedMonoid_mk_eq_mk {f : stableSymmetricSubmodule R n}
    {g : stableSymmetricSubmodule R m} (hnm : n = m)
    (h : ∀ d, (stableSymmetricProj R n d f : MvPolynomial (Fin d) R) =
      stableSymmetricProj R m d g) :
    GradedMonoid.mk (A := fun n => stableSymmetricSubmodule R n) n f = GradedMonoid.mk m g := by
  subst hnm
  exact congrArg _ (stableSymmetricSubmodule_ext fun d => Subtype.ext (h d))

noncomputable instance : GradedMonoid.GCommMonoid fun n => stableSymmetricSubmodule R n where
  one_mul := fun ⟨n, f⟩ => by
    exact gradedMonoid_mk_eq_mk (f := stableSymmetricMul R 0 n (stableSymmetricOne R) f) (g := f)
      (zero_add n) fun d => by simp
  mul_one := fun ⟨n, f⟩ => by
    exact gradedMonoid_mk_eq_mk (f := stableSymmetricMul R n 0 f (stableSymmetricOne R)) (g := f)
      (add_zero n) fun d => by simp only [coe_stableSymmetricProj_stableSymmetricMul,
        coe_stableSymmetricProj_stableSymmetricOne, mul_one]
  mul_assoc := fun ⟨n, f⟩ ⟨m, g⟩ ⟨k, h⟩ => by
    exact gradedMonoid_mk_eq_mk
      (f := stableSymmetricMul R (n + m) k (stableSymmetricMul R n m f g) h)
      (g := stableSymmetricMul R n (m + k) f (stableSymmetricMul R m k g h))
      (add_assoc n m k) fun d => by simp [mul_assoc]
  mul_comm := fun ⟨n, f⟩ ⟨m, g⟩ => by
    exact gradedMonoid_mk_eq_mk (f := stableSymmetricMul R n m f g)
      (g := stableSymmetricMul R m n g f) (add_comm n m) fun d => by simp [mul_comm]

noncomputable instance : DirectSum.GCommSemiring fun n => stableSymmetricSubmodule R n where
  mul_zero _ := map_zero _
  zero_mul g := LinearMap.map_zero₂ _ g
  mul_add _ g h := map_add _ g h
  add_mul f g h := LinearMap.map_add₂ (stableSymmetricMul R _ _) f g h
  natCast k := k • stableSymmetricOne R
  natCast_zero := zero_smul _ _
  natCast_succ k := succ_nsmul _ k

noncomputable instance : DirectSum.GAlgebra R fun n => stableSymmetricSubmodule R n where
  toFun := (LinearMap.toSpanSingleton R _ (stableSymmetricOne R)).toAddMonoidHom
  map_one := by exact one_smul R (stableSymmetricOne R)
  map_mul r s := by
    exact gradedMonoid_mk_eq_mk (f := (r * s) • stableSymmetricOne R)
      (g := stableSymmetricMul R 0 0 (r • stableSymmetricOne R) (s • stableSymmetricOne R))
      (add_zero 0).symm fun d => by
        simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul,
          coe_stableSymmetricProj_stableSymmetricMul, coe_stableSymmetricProj_stableSymmetricOne,
          mul_one, mul_smul]
        rw [smul_comm]
  commutes r := fun ⟨n, f⟩ => by
    exact gradedMonoid_mk_eq_mk (f := stableSymmetricMul R 0 n (r • stableSymmetricOne R) f)
      (g := stableSymmetricMul R n 0 f (r • stableSymmetricOne R)) (add_comm 0 n) fun d => by
        simp only [coe_stableSymmetricProj_stableSymmetricMul, mul_comm]
  smul_def r := fun ⟨n, f⟩ => by
    exact gradedMonoid_mk_eq_mk (f := r • f)
      (g := stableSymmetricMul R 0 n (r • stableSymmetricOne R) f) (zero_add n).symm fun d => by
        simp

variable (R)

/-- **The ring of symmetric functions** `Λ_R` over a commutative semiring `R`: the direct sum over
`n` of the symmetric functions of degree `n`, with the componentwise product of compatible
families. -/
abbrev SymmetricFunction : Type _ :=
  ⨁ n, stableSymmetricSubmodule R n

namespace SymmetricFunction

/-- The member in `d` variables of a symmetric function of degree `n`, as a polynomial. -/
private noncomputable def specializationAux (d n : ℕ) :
    stableSymmetricSubmodule R n →ₗ[R] MvPolynomial (Fin d) R :=
  (symmetricHomogeneousSubmodule (Fin d) R n).subtype ∘ₗ stableSymmetricProj R n d

private theorem specializationAux_apply (d n : ℕ) (f : stableSymmetricSubmodule R n) :
    specializationAux R d n f = stableSymmetricProj R n d f :=
  (rfl)

private theorem specializationAux_gOne (d : ℕ) :
    specializationAux R d 0
      (GradedMonoid.GOne.one (A := fun n => stableSymmetricSubmodule R n)) = 1 := by
  simp [specializationAux_apply]

private theorem specializationAux_gMul (d : ℕ) {i j : ℕ} (f : stableSymmetricSubmodule R i)
    (g : stableSymmetricSubmodule R j) :
    specializationAux R d (i + j)
        (GradedMonoid.GMul.mul (A := fun n => stableSymmetricSubmodule R n) f g) =
      specializationAux R d i f * specializationAux R d j g := by
  simp [specializationAux_apply]

/-- **The specialization of symmetric functions to the alphabet `Fin d`**: the algebra homomorphism
sending a symmetric function of degree `n` to its member in `d` variables. -/
noncomputable def specialization (d : ℕ) : SymmetricFunction R →ₐ[R] MvPolynomial (Fin d) R :=
  DirectSum.toAlgebra R _ (specializationAux R d) (specializationAux_gOne R d)
    (specializationAux_gMul R d)

variable {R}

/-- A symmetric function of degree `n` specializes to its member in `d` variables. -/
@[simp]
theorem specialization_of (d : ℕ) (f : stableSymmetricSubmodule R n) :
    specialization R d (DirectSum.of _ n f) = stableSymmetricProj R n d f := by
  rw [specialization, DirectSum.toAlgebra_apply]
  exact (DirectSum.toSemiring_of (fun i => (specializationAux R d i).toAddMonoidHom) _ _ n f).trans
    (specializationAux_apply R d n f)

/-- **The specializations are compatible**: setting the last of `d + 1` variables to zero turns the
specialization to `d + 1` variables into the specialization to `d` variables.

Not a `simp` lemma, for the reason recorded at `TauCeti.aeval_snoc_zero_stableSymmetricProj`. -/
theorem aeval_snoc_zero_specialization (d : ℕ) (x : SymmetricFunction R) :
    aeval (Fin.snoc (X : Fin d → MvPolynomial (Fin d) R) 0) (specialization R (d + 1) x) =
      specialization R d x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n f => rw [specialization_of, specialization_of, aeval_snoc_zero_stableSymmetricProj]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The homogeneous component of degree `n` of a specialization** is the specialization of the
component of degree `n`. -/
theorem homogeneousComponent_specialization (n d : ℕ) (x : SymmetricFunction R) :
    homogeneousComponent n (specialization R d x) = stableSymmetricProj R n d (x n) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m f =>
    rw [specialization_of, homogeneousComponent_of_mem
      (mem_symmetricHomogeneousSubmodule.mp (Subtype.prop _)).2]
    obtain rfl | hmn := eq_or_ne n m
    · simp
    · simp [hmn, DirectSum.of_eq_of_ne _ _ _ hmn]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, DirectSum.add_apply, map_add, Submodule.coe_add]

/-- **A symmetric function is determined by its specializations to all finite alphabets.** -/
theorem ext_specialization {x y : SymmetricFunction R}
    (h : ∀ d, specialization R d x = specialization R d y) : x = y := by
  refine DirectSum.ext fun n => stableSymmetricSubmodule_ext fun d => Subtype.ext ?_
  have := congrArg (homogeneousComponent n) (h d)
  rwa [homogeneousComponent_specialization, homogeneousComponent_specialization] at this

/-- The unit of the symmetric functions of degree zero is the unit of the ring of symmetric
functions. -/
@[simp]
theorem of_stableSymmetricOne :
    DirectSum.of _ 0 (stableSymmetricOne R) = (1 : SymmetricFunction R) :=
  ext_specialization fun d => by simp

end SymmetricFunction

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

noncomputable instance : DirectSum.GCommRing fun n => stableSymmetricSubmodule R n where
  intCast k := k • stableSymmetricOne R
  intCast_ofNat k := natCast_zsmul (stableSymmetricOne R) k
  intCast_negSucc_ofNat k := negSucc_zsmul (stableSymmetricOne R) k

/-- The ring structure on the symmetric functions over a commutative ring. It is stated by hand
because `DirectSum.commRing` asks the `AddCommMonoid` on each degree to come from an `AddCommGroup`,
which instance search cannot unify with the `AddCommMonoid` of a submodule. -/
noncomputable instance : CommRing (SymmetricFunction R) :=
  DirectSum.commRing fun n => stableSymmetricSubmodule R n

end CommRing

end TauCeti
