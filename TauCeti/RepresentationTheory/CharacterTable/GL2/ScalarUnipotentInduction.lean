/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.indClassFun` is the object the four values below are computed for.
public import TauCeti.RepresentationTheory.Induction.ClassFunction
-- `FDRep.ofLinearCharacter` and `TauCeti.indFDRep` are the bodies of the constructions below.
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
-- `TauCeti.GL2ScalarUnipotent` and `TauCeti.jordanGL` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- `TauCeti.diagGL` occurs in the statements below: the contributing cosets are those of the
-- diagonal matrices `diag (c, 1)`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `TauCeti.GL2NonSplitTorusHom` occurs in the elliptic statement below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- `AddChar` occurs in the public construction.
public import Mathlib.Algebra.Group.AddChar
-- Non-public: `TauCeti.smul_quotientGroup_mk_eq_self_iff` is used only inside a proof.
import TauCeti.GroupTheory.QuotientGroup.Basic
-- Non-public: the sum of a nontrivial additive character over the nonzero field elements is used
-- in the Jordan computation.
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality

/-!
# Induction from the scalar--unipotent subgroup of `GL₂(𝔽_q)`

Let `F` be a finite field with `q` elements and let `Z U = TauCeti.GL2ScalarUnipotent F` be the
product of the centre of `GL₂(F)` with the unipotent radical of the Borel subgroup: the matrices
`!![x, y; 0, x]`, a copy of `Fˣ × (F, +)`.  This file computes the induced class function
`TauCeti.indClassFun (GL2ScalarUnipotent F) f` on the four families of conjugacy classes of
`GL₂(F)`: at a central scalar `a` it is `[GL₂(F) : Z U] = q² - 1` copies of `f(a)`, it vanishes on
the split semisimple and the elliptic families, and at a non-semisimple element with repeated
eigenvalue `a` it is the sum of `f` over the `q - 1` Jordan blocks `!![a, c; 0, a]` with `c ≠ 0`.

It then specialises those four values to the inducing datum that the character table needs.  A
multiplicative character `μ : Fˣ → ℂˣ` and an additive character `ψ : F → ℂ` define the linear
character

`(a, t) ↦ μ(a) ψ(t)`

under the isomorphism `Fˣ × (F, +) ≃ Z U`; this file constructs that character, the line it acts
on, and the representation the line induces to `GL₂(F)`, and reads its degree and its four
character values off the class-function computation:

* `(q² - 1) μ(a)` on the scalar matrix `a I`;
* `0` on split regular semisimple and on elliptic elements;
* `-μ(a)` on a nontrivial Jordan block with eigenvalue `a`, once `ψ` is nontrivial.

Together with `TauCeti.GL2NonSplitTorus.indClassFun_gl2NonSplitTorusHom` this supplies the two
induced class functions whose difference is the cuspidal (discrete series) character of
`GL₂(𝔽_q)`.  The Gelfand-Graev summand here is the one that carries the degree, since
`[GL₂(F) : Z U] - [GL₂(F) : Eˣ] = (q² - 1) - q (q - 1) = q - 1`.

## The geometry behind the four values

Everything follows from which conjugates of an element land in `Z U`, and an element of `Z U`
differs from a scalar by a square-zero matrix: subtracting its repeated diagonal entry leaves a
nilpotent.  That condition is invariant under conjugation, and it is exactly what an element with
two distinct eigenvalues -- split or elliptic -- fails.

* A **scalar** matrix is central, so every conjugate of it lies in `Z U`, and the sum has one
  equal summand for each of the `[GL₂(F) : Z U]` cosets.
* A **split semisimple** element `diag (a, b)` with `a ≠ b` fails the square-zero condition,
  because `(a - u)² = (b - u)² = 0` would force `a = u = b`; an **elliptic** element, the matrix
  of multiplication by `x` outside `F` in a quadratic extension `E/F`, fails it because `E` is a
  field, so `(x - u)² = 0` would force `x = u ∈ F`.  No conjugate of either meets `Z U`.
* A **non-semisimple** element `!![a, b; 0, a]` with `b ≠ 0` is conjugated into `Z U` by exactly
  the upper triangular matrices, and those form the `q - 1` cosets of `Z U` represented by the
  diagonal matrices `diag (c, 1)`, `c : Fˣ`.  Conjugating by `diag (c, 1)` rescales the
  off-diagonal entry to `c⁻¹ b`, so the `q - 1` summands run over all the Jordan blocks with the
  same diagonal entry.

Neither the square-zero argument nor the coset count needs separability or a case split on the
characteristic, unlike the trace-and-determinant route, which in characteristic two only sees the
trace.

## Main definitions

* `TauCeti.GL2ScalarUnipotent.linearChar`: the character `(a, t) ↦ μ(a) ψ(t)` of `Z U`.
* `TauCeti.GL2ScalarUnipotentRep`: its one-dimensional complex representation.
* `TauCeti.GL2ScalarUnipotentInduction`: the representation induced from `Z U` to `GL₂(F)`.

## Main results

* `TauCeti.GL2ScalarUnipotent.indClassFun_eq_zero_of_forall_sq_ne_zero`: the induced class
  function vanishes at an element that differs from no scalar by a square-zero matrix.
* `TauCeti.GL2ScalarUnipotent.mem_classFunction`: every function on the abelian subgroup `Z U` is
  a class function, so the summands depend only on the coset of their representative.
* `TauCeti.GL2ScalarUnipotent.indClassFun_scalar`,
  `TauCeti.GL2ScalarUnipotent.indClassFun_diagGL`,
  `TauCeti.GL2ScalarUnipotent.indClassFun_gl2NonSplitTorusHom` and
  `TauCeti.GL2ScalarUnipotent.indClassFun_jordanGL`: **the four values**, on the central, split
  semisimple, elliptic and non-semisimple normal forms.
* `TauCeti.finrank_GL2ScalarUnipotentInduction`: the induced representation has dimension
  `q² - 1`.
* `TauCeti.character_GL2ScalarUnipotentInduction_scalar`,
  `TauCeti.character_GL2ScalarUnipotentInduction_diagGL`,
  `TauCeti.character_GL2ScalarUnipotentInduction_gl2NonSplitTorusHom` and
  `TauCeti.character_GL2ScalarUnipotentInduction_jordanGL`: its four character values.

That the four normal forms exhaust the conjugacy classes is
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses`; as in
`TauCeti/RepresentationTheory/CharacterTable/GL2/PrincipalSeries/CharacterValues.lean`, the values
below are stated at the normal forms themselves rather than assembled into a single case
distinction.  None of the class-function values is a `simp` lemma: they evaluate a class function
at a normal form, and neither side is a normal form for `simp`.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

universe u

namespace GL2ScalarUnipotent

variable {F : Type u} [Field F]

/-! ### Which conjugates land in `Z U` -/

/-- **An element of `Z U` differs from a scalar by a square-zero matrix**: subtracting its
repeated diagonal entry leaves the nilpotent `!![0, y; 0, 0]`. -/
private theorem exists_sq_sub_algebraMap_eq_zero {z : GL (Fin 2) F}
    (hz : z ∈ GL2ScalarUnipotent F) : ∃ u : Fˣ, ((z : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F)) ^ 2 = 0 := by
  obtain ⟨u, y, rfl⟩ := mem_gl2ScalarUnipotent_iff.mp hz
  refine ⟨u, ?_⟩
  have hshift : ((jordanGL u y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F) = !![0, y; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_matrix_apply]
  rw [hshift, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The square-zero condition is conjugation invariant**: if some conjugate of `g` lies in
`Z U`, then `g` itself differs from a scalar by a square-zero matrix. -/
private theorem exists_sq_sub_algebraMap_eq_zero_of_conj_mem {g x : GL (Fin 2) F}
    (hx : x⁻¹ * g * x ∈ GL2ScalarUnipotent F) :
    ∃ u : Fˣ, ((g : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F)) ^ 2 = 0 := by
  obtain ⟨u, hu⟩ := exists_sq_sub_algebraMap_eq_zero hx
  refine ⟨u, ?_⟩
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  set Y : Matrix (Fin 2) (Fin 2) F := ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hY
  set A : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) -
    algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F) with hA
  have hXY : X * Y = 1 := by rw [hX, hY, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYX : Y * X = 1 := by rw [hX, hY, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : Y * algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F) * X =
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F) := by
    rw [mul_assoc, Algebra.commutes (u : F) X, ← mul_assoc, hYX, one_mul]
  have hsplit : ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F) = Y * A * X := by
    rw [hA, mul_sub, sub_mul, hcomm, Units.val_mul, Units.val_mul]
  rw [hsplit, pow_two] at hu
  have hu' : Y * (A * A) * X = 0 := by
    have hmid : Y * A * X * (Y * A * X) = Y * (A * A) * X :=
      calc Y * A * X * (Y * A * X) = Y * A * (X * Y) * (A * X) := by simp only [mul_assoc]
        _ = Y * (A * A) * X := by rw [hXY, mul_one]; simp only [mul_assoc]
    rwa [hmid] at hu
  calc A ^ 2 = X * Y * (A * A) * (X * Y) := by rw [hXY, one_mul, mul_one, pow_two]
    _ = X * (Y * (A * A) * X) * Y := by simp only [mul_assoc]
    _ = X * 0 * Y := by rw [hu']
    _ = 0 := by rw [mul_zero, zero_mul]

/-- **A matrix conjugating a Jordan block into `Z U` is upper triangular.**  Comparing the lower
rows of `!![a, b; 0, a] · x` and of `x · !![u, y; 0, u]` gives `r (a - u) = 0` for the lower-left
entry `r` of `x`; when `a = u` the upper-left entries give `b r = 0` instead, and `b ≠ 0` settles
both cases. -/
private theorem mem_gl2Borel_of_conj_mem (a : Fˣ) {b : F} (hb : b ≠ 0) {x : GL (Fin 2) F}
    (hx : x⁻¹ * jordanGL a b * x ∈ GL2ScalarUnipotent F) : x ∈ GL2Borel F := by
  obtain ⟨u, y, hxy⟩ := mem_gl2ScalarUnipotent_iff.mp hx
  have hmul : (jordanGL a b : GL (Fin 2) F) * x = x * jordanGL u y := by
    rw [← hxy]; group
  have hEq : ((jordanGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (x : Matrix (Fin 2) (Fin 2) F) = (x : Matrix (Fin 2) (Fin 2) F) *
        ((jordanGL u y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    congrArg Units.val hmul
  have h10 : (a : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (u : F) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ hEq 1 0
  have h00 : (a : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0 +
      b * (x : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (u : F) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ hEq 0 0
  refine GL2Borel.mem_iff.mpr ?_
  by_cases hau : (a : F) = (u : F)
  · have hbr : b * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [hau] at h00; linear_combination h00
    exact (mul_eq_zero.mp hbr).resolve_left hb
  · have hr : (x : Matrix (Fin 2) (Fin 2) F) 1 0 * ((a : F) - (u : F)) = 0 := by
      linear_combination h10
    exact (mul_eq_zero.mp hr).resolve_right (sub_ne_zero.mpr hau)

/-! ### The cosets of `Z U` inside the Borel subgroup -/

/-- **An upper triangular matrix lies in the coset of a diagonal matrix `diag (c, 1)`**: writing
it as `!![p, q; 0, s]`, the factor `diag (p s⁻¹, 1)` clears the ratio of the diagonal entries. -/
private theorem exists_quotient_mk_eq_diagGL {x : GL (Fin 2) F} (hx : x ∈ GL2Borel F) :
    ∃ c : Fˣ, (QuotientGroup.mk x : GL (Fin 2) F ⧸ GL2ScalarUnipotent F) =
      QuotientGroup.mk (diagGL ![c, 1]) := by
  obtain ⟨p, s, q, rfl⟩ := GL2Borel.mem_iff_exists_mk.mp hx
  refine ⟨p * s⁻¹, ?_⟩
  have hsplit : (GL2Borel.mk p s q : GL (Fin 2) F) =
      diagGL ![p * s⁻¹, 1] * jordanGL s (q * (s : F) * ((p⁻¹ : Fˣ) : F)) := by
    have hp : (p : F) ≠ 0 := p.ne_zero
    have hs : (s : F) ≠ 0 := s.ne_zero
    refine Units.ext ?_
    rw [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]
    all_goals field_simp
  rw [eq_comm, QuotientGroup.eq, hsplit, inv_mul_cancel_left]
  exact jordanGL_mem_gl2ScalarUnipotent _ _

/-- **The cosets `diag (c, 1) · Z U` are pairwise distinct**: the two diagonal entries of an
element of `Z U` agree, so `diag (c, 1)⁻¹ diag (d, 1)` lies in `Z U` only for `c = d`.  Together
with `TauCeti.GL2ScalarUnipotent.exists_quotient_mk_eq_diagGL` this enumerates the `q - 1` cosets
of `Z U` inside the Borel subgroup. -/
private theorem quotient_mk_diagGL_injective :
    Function.Injective fun c : Fˣ =>
      (QuotientGroup.mk (diagGL ![c, 1]) : GL (Fin 2) F ⧸ GL2ScalarUnipotent F) := by
  intro c d hcd
  rw [QuotientGroup.eq] at hcd
  obtain ⟨v, w, hvw⟩ := mem_gl2ScalarUnipotent_iff.mp hcd
  have hval : ((diagGL ![d, 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((diagGL ![c, 1] * jordanGL v w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    congrArg Units.val (by rw [← hvw, mul_inv_cancel_left])
  have h00 : (d : F) = (c : F) * (v : F) := by
    simpa [Matrix.mul_apply, Matrix.diagonal] using congrFun₂ hval 0 0
  have h11 : (1 : F) = (v : F) := by
    simpa [Matrix.mul_apply, Matrix.diagonal] using congrFun₂ hval 1 1
  exact (Units.ext (by rw [h00, ← h11, mul_one])).symm

/-- Conjugating a Jordan block by `diag (c, 1)` rescales its off-diagonal entry by `c⁻¹`. -/
private theorem inv_diagGL_mul_jordanGL_mul_diagGL (a : Fˣ) (b : F) (c : Fˣ) :
    (diagGL ![c, 1])⁻¹ * jordanGL a b * diagGL ![c, 1] = jordanGL a (((c⁻¹ : Fˣ) : F) * b) := by
  have hprod : (jordanGL a b : GL (Fin 2) F) * diagGL ![c, 1] =
      diagGL ![c, 1] * jordanGL a (((c⁻¹ : Fˣ) : F) * b) := by
    have hc : (c : F) ≠ 0 := c.ne_zero
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]
    all_goals field_simp
  rw [mul_assoc, hprod, inv_mul_cancel_left]

/-! ### The central, split semisimple and elliptic values -/

section Finite

variable {k : Type*} [AddCommMonoid k] [Finite F]

/-- **The induced class function vanishes where the square-zero condition fails**: an element with
a conjugate in `Z U` differs from a scalar by a square-zero matrix, so no coset contributes. -/
theorem indClassFun_eq_zero_of_forall_sq_ne_zero (f : GL2ScalarUnipotent F → k)
    {g : GL (Fin 2) F} (hg : ∀ u : Fˣ, ((g : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (u : F)) ^ 2 ≠ 0) :
    indClassFun (GL2ScalarUnipotent F) f g = 0 := by
  classical
  rw [indClassFun_apply]
  refine Finset.sum_eq_zero fun t _ => dite_eq_right fun hmem => ?_
  obtain ⟨u, hu⟩ := exists_sq_sub_algebraMap_eq_zero_of_conj_mem hmem
  exact absurd hu (hg u)

/-- **The induced class function at a central element**: a scalar matrix is central, so every
conjugate of it is itself and lies in `Z U`, and each of the `[GL₂(F) : Z U]` cosets contributes
the same value.  Over a field with `q` elements the index is `q² - 1`, by
`TauCeti.index_gl2ScalarUnipotent`. -/
theorem indClassFun_scalar (f : GL2ScalarUnipotent F → k) (a : Fˣ) :
    indClassFun (GL2ScalarUnipotent F) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      (GL2ScalarUnipotent F).index •
        f ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, scalar_mem a⟩ := by
  classical
  have hconj : ∀ x : GL (Fin 2) F,
      x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * x =
        Matrix.GeneralLinearGroup.scalar (Fin 2) a := fun x => by
    rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute a x, ← mul_assoc, inv_mul_cancel,
      one_mul]
  let _ : Fintype (GL (Fin 2) F ⧸ GL2ScalarUnipotent F) := Fintype.ofFinite _
  rw [indClassFun_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.sum_eq_card_nsmul fun t _ => by rw [hconj, dite_eq_left (scalar_mem a)]

/-- **The induced class function vanishes on the split semisimple classes**: if `diag (a, b)`
differed from a scalar `u` by a square-zero matrix then `(a - u)² = (b - u)² = 0`, so
`a = u = b`. -/
theorem indClassFun_diagGL (f : GL2ScalarUnipotent F → k) {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    indClassFun (GL2ScalarUnipotent F) f (diagGL t) = 0 := by
  refine indClassFun_eq_zero_of_forall_sq_ne_zero f fun u hu => ht ?_
  have hentry : ∀ i : Fin 2, ((t i : F) - (u : F)) ^ 2 = 0 := fun i => by
    have hii := congrFun₂ hu i i
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply,
      Matrix.one_apply, Fin.ext_iff] using hii
  exact Units.ext (by
    rw [sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (hentry 0)),
      sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (hentry 1))])

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **The induced class function vanishes on the elliptic classes**: `E` is a field, so
`(x - u)² = 0` would force `x` to be the scalar `u`, which lies in `F`. -/
theorem indClassFun_gl2NonSplitTorusHom (f : GL2ScalarUnipotent F → k) {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    indClassFun (GL2ScalarUnipotent F) f (GL2NonSplitTorusHom F E hE x) = 0 := by
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  refine indClassFun_eq_zero_of_forall_sq_ne_zero f fun u hu => hx ⟨(u : F), ?_⟩
  -- the square-zero matrix is the matrix of `(x - u)²`, and `leftMulMatrix` is injective
  have hpow : ((x : E) - algebraMap F E (u : F)) ^ 2 = 0 :=
    Algebra.leftMulMatrix_injective (nonSplitTorusBasis F E hE) (by
      rw [map_pow, map_sub, (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes,
        ← GL2NonSplitTorus.coe_gl2NonSplitTorusHom hE, hu, map_zero])
  exact (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hpow)).symm

end Elliptic

end Finite

/-! ### The non-semisimple value -/

/-- **Conjugation inside `Z U` is trivial**, because the subgroup is abelian.  It is what makes a
summand of the induced class function depend only on the coset of its representative, by
`TauCeti.indTerm_eq_of_mk_eq_of_conj`. -/
private theorem conj_eq_self (s y : GL2ScalarUnipotent F) : s * y * s⁻¹ = y := by
  rw [mul_comm' s y, mul_assoc, mul_inv_cancel, mul_one]

section Semiring

variable {k : Type*} [Semiring k]

/-- Every function on the abelian subgroup `Z U` is a class function, so the summands of the
induced class function depend only on the coset of their representative.  It is the hypothesis of
`TauCeti.ClassFunction.ind` and of `TauCeti.indClassFun_mem_classFunction` for `Z U`. -/
theorem mem_classFunction (f : GL2ScalarUnipotent F → k) :
    f ∈ ClassFunction k (GL2ScalarUnipotent F) :=
  ClassFunction.mem_iff.mpr fun g h => congrArg f (conj_eq_self h g)

end Semiring

section Fintype

variable {k : Type*} [AddCommMonoid k] [Fintype F] [DecidableEq F]

/-- **The induced class function at a non-semisimple element.**  A Jordan block `!![a, b; 0, a]`
with `b ≠ 0` is conjugated into `Z U` exactly by the upper triangular matrices, which form the
`q - 1` cosets represented by the diagonal matrices `diag (c, 1)`; conjugating by `diag (c, 1)`
sends the block to `!![a, c⁻¹ b; 0, a]`, so the summands run over all the Jordan blocks with
diagonal entry `a` and nonzero off-diagonal entry.  In particular the value does not depend on
`b`. -/
theorem indClassFun_jordanGL (f : GL2ScalarUnipotent F → k) (a : Fˣ) {b : F} (hb : b ≠ 0) :
    indClassFun (GL2ScalarUnipotent F) f (jordanGL a b) =
      ∑ c : Fˣ, f ⟨jordanGL a (c : F), jordanGL_mem_gl2ScalarUnipotent a (c : F)⟩ := by
  classical
  -- the cosets that contribute are exactly those of the `diag (c, 1)`
  have hT : ∀ t : GL (Fin 2) F ⧸ GL2ScalarUnipotent F, jordanGL a b • t = t →
      t ∈ (Finset.univ.image fun c : Fˣ =>
        (QuotientGroup.mk (diagGL ![c, 1]) : GL (Fin 2) F ⧸ GL2ScalarUnipotent F)) := by
    intro t htfix
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨c, hc⟩ := exists_quotient_mk_eq_diagGL (mem_gl2Borel_of_conj_mem a hb
      ((smul_quotientGroup_mk_eq_self_iff _ _ _).mp htfix))
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hc.symm⟩
  -- and each of them contributes the value of `f` at a rescaled Jordan block
  have hterm : ∀ c : Fˣ,
      indTerm f (jordanGL a b) (Quotient.out
          (QuotientGroup.mk (diagGL ![c, 1]) : GL (Fin 2) F ⧸ GL2ScalarUnipotent F)) =
        f ⟨jordanGL a (((c⁻¹ : Fˣ) : F) * b),
          jordanGL_mem_gl2ScalarUnipotent a (((c⁻¹ : Fˣ) : F) * b)⟩ := fun c => by
    rw [indTerm_eq_of_mk_eq_of_conj (fun y s => congrArg f (conj_eq_self s y)) _ _
        (diagGL ![c, 1]) (QuotientGroup.out_eq' _),
      indTerm_apply, dite_eq_left ((inv_diagGL_mul_jordanGL_mul_diagGL a b c) ▸
        jordanGL_mem_gl2ScalarUnipotent a (((c⁻¹ : Fˣ) : F) * b))]
    exact congrArg f (Subtype.ext (inv_diagGL_mul_jordanGL_mul_diagGL a b c))
  rw [indClassFun_eq_sum_of_smul_eq_self_mem _ _ _ hT,
    Finset.sum_image fun c _ d _ h => quotient_mk_diagGL_injective h,
    Finset.sum_congr rfl fun c _ => hterm c]
  exact Fintype.sum_equiv ((Equiv.inv Fˣ).trans (Equiv.mulRight (Units.mk0 b hb))) _ _
    fun c => congrArg f (Subtype.ext (by simp))

end Fintype

/-! ### The scalar--unipotent linear character -/

section LinearCharacter

/-- **The scalar--unipotent linear character** attached to a multiplicative character `μ` and
an additive character `ψ`.  In the coordinates `Fˣ × (F,+) ≃ Z U` it is
`(a,t) ↦ μ(a)ψ(t)`. -/
noncomputable def linearChar (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    GL2ScalarUnipotent F →* ℂˣ :=
  (μ.coprod ψ.toMonoidHom.toHomUnits).comp (mulEquiv F).symm.toMonoidHom

/-- Evaluation of the scalar--unipotent character in product coordinates. -/
@[simp]
theorem linearChar_mulEquiv (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ)
    (a : Fˣ) (t : Multiplicative F) :
    linearChar μ ψ (mulEquiv F (a, t)) = μ a * ψ.toMonoidHom.toHomUnits t := by
  simp [linearChar]

/-- The complex value of the scalar--unipotent character on a Jordan block. -/
@[simp]
theorem coe_linearChar_jordanGL (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) (a : Fˣ) (b : F) :
    ((linearChar μ ψ ⟨jordanGL a b, jordanGL_mem_gl2ScalarUnipotent a b⟩ : ℂˣ) : ℂ) =
      (μ a : ℂ) * ψ ((a⁻¹ : Fˣ) * b) := by
  let t : Multiplicative F := Multiplicative.ofAdd ((a⁻¹ : Fˣ) * b)
  have h : (mulEquiv F (a, t) : GL (Fin 2) F) = jordanGL a b := by
    simp [t]
  have hs : mulEquiv F (a, t) =
      ⟨jordanGL a b, jordanGL_mem_gl2ScalarUnipotent a b⟩ := Subtype.ext h
  rw [← hs, linearChar_mulEquiv, Units.val_mul, MonoidHom.coe_toHomUnits]
  rfl

end LinearCharacter

end GL2ScalarUnipotent

section Representations

variable (F : Type u) [Field F]

/-- The one-dimensional representation of `Z U` carrying
`TauCeti.GL2ScalarUnipotent.linearChar μ ψ`. -/
noncomputable def GL2ScalarUnipotentRep (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    FDRep ℂ (GL2ScalarUnipotent F) :=
  FDRep.ofLinearCharacter (GL2ScalarUnipotent.linearChar μ ψ)

/-- The scalar--unipotent representation is one-dimensional. -/
@[simp]
theorem finrank_GL2ScalarUnipotentRep (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    Module.finrank ℂ (GL2ScalarUnipotentRep F μ ψ) = 1 := by
  rw [GL2ScalarUnipotentRep, FDRep.finrank_ofLinearCharacter]

/-- The character of the scalar--unipotent line is its defining linear character. -/
@[simp]
theorem character_GL2ScalarUnipotentRep (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ)
    (g : GL2ScalarUnipotent F) :
    (GL2ScalarUnipotentRep F μ ψ).character g =
      (GL2ScalarUnipotent.linearChar μ ψ g : ℂ) :=
  FDRep.char_ofLinearCharacter _ g

variable [Fintype F]

/-- **The scalar--unipotent induction for `GL₂(F)` with central character `μ`**: induce the
character `(a,t) ↦ μ(a)ψ(t)` from `Z U` to `GL₂(F)`. -/
noncomputable def GL2ScalarUnipotentInduction (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    FDRep ℂ (GL (Fin 2) F) :=
  indFDRep (GL2ScalarUnipotentRep F μ ψ)

/-- The scalar--unipotent induction has dimension `q² - 1`, the index of `Z U`. -/
@[simp]
theorem finrank_GL2ScalarUnipotentInduction (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    Module.finrank ℂ (GL2ScalarUnipotentInduction F μ ψ) = Fintype.card F ^ 2 - 1 := by
  rw [GL2ScalarUnipotentInduction, GL2ScalarUnipotentRep,
    finrank_indFDRep_ofLinearCharacter, index_gl2ScalarUnipotent]

end Representations

/-! ### The four character values -/

section CharacterValues

variable {F : Type u} [Field F] [Fintype F]
variable (μ : Fˣ →* ℂˣ) (ψ : AddChar F ℂ)

private theorem character_GL2ScalarUnipotentInduction_eq_indClassFun (g : GL (Fin 2) F) :
    (GL2ScalarUnipotentInduction F μ ψ).character g =
      indClassFun (GL2ScalarUnipotent F) (GL2ScalarUnipotentRep F μ ψ).character g := by
  rw [GL2ScalarUnipotentInduction, ← indClassFun_ofFDRep_character]

/-- **The scalar--unipotent induced character at a scalar matrix** is `(q² - 1) μ(a)`: every coset
contributes the value of the inducing character at the unchanged scalar. -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_scalar (a : Fˣ) :
    (GL2ScalarUnipotentInduction F μ ψ).character
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      (Fintype.card F ^ 2 - 1 : ℂ) * (μ a : ℂ) := by
  have hvalue : (GL2ScalarUnipotentRep F μ ψ).character
      ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, GL2ScalarUnipotent.scalar_mem a⟩ =
        (μ a : ℂ) := by
    rw [character_GL2ScalarUnipotentRep]
    have hsub :
        (⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, GL2ScalarUnipotent.scalar_mem a⟩ :
            GL2ScalarUnipotent F) =
          ⟨jordanGL a 0, jordanGL_mem_gl2ScalarUnipotent _ _⟩ :=
      Subtype.ext (jordanGL_zero a).symm
    rw [hsub, GL2ScalarUnipotent.coe_linearChar_jordanGL]
    simp
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun,
    GL2ScalarUnipotent.indClassFun_scalar _ a, hvalue, index_gl2ScalarUnipotent, nsmul_eq_mul]
  have hle : 1 ≤ Fintype.card F ^ 2 :=
    Nat.one_le_pow 2 (Fintype.card F) Fintype.card_pos
  rw [Nat.cast_sub hle]
  push_cast
  rfl

/-- **The scalar--unipotent induced character vanishes on split regular semisimple elements.** -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_diagGL {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    (GL2ScalarUnipotentInduction F μ ψ).character (diagGL t) = 0 := by
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun]
  exact GL2ScalarUnipotent.indClassFun_diagGL _ ht

section Elliptic

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **The scalar--unipotent induced character vanishes on elliptic elements.** -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_gl2NonSplitTorusHom {z : Eˣ}
    (hz : (z : E) ∉ Set.range (algebraMap F E)) :
    (GL2ScalarUnipotentInduction F μ ψ).character (GL2NonSplitTorusHom F E hE z) = 0 := by
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun]
  exact GL2ScalarUnipotent.indClassFun_gl2NonSplitTorusHom hE _ hz

end Elliptic

/-- **The scalar--unipotent induced character at a nontrivial Jordan block** is `-μ(a)`: the
`q - 1` summands of `TauCeti.GL2ScalarUnipotent.indClassFun_jordanGL` are `μ(a)` times the values
of `ψ` on `Fˣ`, and those sum to `-1`.  So the induced character has degree `q² - 1` but absolute
value `1` on the unipotent classes. -/
@[simp]
theorem character_GL2ScalarUnipotentInduction_jordanGL
    (hψ : ψ ≠ 1) (a : Fˣ) {b : F} (hb : b ≠ 0) :
    (GL2ScalarUnipotentInduction F μ ψ).character (jordanGL a b) = -(μ a : ℂ) := by
  classical
  have hterm : ∀ c : Fˣ, (GL2ScalarUnipotentRep F μ ψ).character
      ⟨jordanGL a (c : F), jordanGL_mem_gl2ScalarUnipotent a (c : F)⟩ =
        (μ a : ℂ) * ψ (((a⁻¹ : Fˣ) : F) * (c : F)) := fun c => by
    rw [character_GL2ScalarUnipotentRep, GL2ScalarUnipotent.coe_linearChar_jordanGL]
  rw [character_GL2ScalarUnipotentInduction_eq_indClassFun,
    GL2ScalarUnipotent.indClassFun_jordanGL _ a hb,
    Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum,
    AddChar.sum_units_mul_eq_neg_one ψ hψ a⁻¹, mul_neg_one]

end CharacterValues

end TauCeti
