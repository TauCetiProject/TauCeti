/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.indClassFun` is the object computed here.
public import TauCeti.RepresentationTheory.Induction.ClassFunction
-- `TauCeti.GL2ScalarUnipotent` and `TauCeti.jordanGL` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- `TauCeti.diagGL` occurs in the statements below: the contributing cosets are those of the
-- diagonal matrices `diag (c, 1)`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `TauCeti.GL2NonSplitTorusHom` occurs in the elliptic statement below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- `AddChar` occurs in the statement of the Gelfand-Graev value.
public import Mathlib.Algebra.Group.AddChar
-- Non-public: `TauCeti.smul_quotientGroup_mk_eq_self_iff` is used only inside a proof.
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# The class function of `GL₂(𝔽_q)` induced from the scalar–unipotent subgroup

Let `F` be a finite field with `q` elements and let `Z U = TauCeti.GL2ScalarUnipotent F` be the
product of the centre of `GL₂(F)` with the unipotent radical of the Borel subgroup: the matrices
`!![x, y; 0, x]`, a copy of `Fˣ × (F, +)`.  This file computes the induced class function
`TauCeti.indClassFun (GL2ScalarUnipotent F) f` on the four families of conjugacy classes of
`GL₂(F)`: at a central scalar `a` it is `[GL₂(F) : Z U] = q² - 1` copies of `f(a)`, it vanishes on
the split semisimple and the elliptic families, and at a non-semisimple element with repeated
eigenvalue `a` it is the sum of `f` over the `q - 1` Jordan blocks `!![a, c; 0, a]` with `c ≠ 0`.

Applied to a product character `μ ⊗ ψ` of `Z U` with `ψ` a nontrivial additive character of `F`,
the last sum collapses to `-μ(a)`, because the values of `ψ` on `Fˣ` sum to `-1`
(`TauCeti.GL2ScalarUnipotent.indClassFun_jordanGL_of_eq_mul`).  That is the Gelfand-Graev induced
character of `GL₂(𝔽_q)`, one of the two induced characters whose difference is the cuspidal
(discrete series) character attached to a character of `Eˣ` in general position; the other is
induced from the non-split torus `Eˣ` of a quadratic extension.  The degree of the difference is
the difference of the two inducing indices,
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
* `TauCeti.GL2ScalarUnipotent.indClassFun_jordanGL_of_eq_mul`: the non-semisimple value `-μ(a)`
  for a product character `μ ⊗ ψ` with `ψ` nontrivial.

That the four normal forms exhaust the conjugacy classes is
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses`; as in
`TauCeti/RepresentationTheory/CharacterTable/GL2/PrincipalSeries/CharacterValues.lean`, the values
below are stated at the normal forms themselves rather than assembled into a single case
distinction.  None of them is a `simp` lemma: they evaluate a class function at a normal form, and
neither side is a normal form for `simp`.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The cuspidal (discrete series) representations".
-/

public section

open Matrix

namespace TauCeti

namespace GL2ScalarUnipotent

variable {F : Type*} [Field F]

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

/-- The two diagonal entries of an element of `Z U` agree. -/
private theorem apply_zero_zero_eq_apply_one_one {z : GL (Fin 2) F}
    (hz : z ∈ GL2ScalarUnipotent F) :
    (z : Matrix (Fin 2) (Fin 2) F) 0 0 = (z : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  obtain ⟨v, w, rfl⟩ := mem_gl2ScalarUnipotent_iff.mp hz
  simp

/-- **The cosets `diag (c, 1) · Z U` are pairwise distinct**, so together with the previous lemma
they enumerate the `q - 1` cosets of `Z U` inside the Borel subgroup. -/
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
`TauCeti.GL2ScalarUnipotent.index_eq`. -/
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

section Semiring

variable {k : Type*} [Semiring k]

/-- Every function on the abelian subgroup `Z U` is a class function, so the summands of the
induced class function depend only on the coset of their representative. -/
theorem mem_classFunction (f : GL2ScalarUnipotent F → k) :
    f ∈ ClassFunction k (GL2ScalarUnipotent F) := by
  refine ClassFunction.mem_iff.mpr fun g h => ?_
  rw [mul_comm' h g, mul_assoc, mul_inv_cancel, mul_one]

section Fintype

variable [Fintype F] [DecidableEq F]

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
    rw [indTerm_eq_of_mk_eq (mem_classFunction f) _ _ (diagGL ![c, 1]) (QuotientGroup.out_eq' _),
      indTerm_apply, dite_eq_left ((inv_diagGL_mul_jordanGL_mul_diagGL a b c) ▸
        jordanGL_mem_gl2ScalarUnipotent a (((c⁻¹ : Fˣ) : F) * b))]
    exact congrArg f (Subtype.ext (inv_diagGL_mul_jordanGL_mul_diagGL a b c))
  rw [indClassFun_eq_sum_of_smul_eq_self_mem _ _ _ hT,
    Finset.sum_image fun c _ d _ h => quotient_mk_diagGL_injective h,
    Finset.sum_congr rfl fun c _ => hterm c]
  exact Fintype.sum_equiv ((Equiv.inv Fˣ).trans (Equiv.mulRight (Units.mk0 b hb))) _ _
    fun c => congrArg f (Subtype.ext (by simp))

/-- **The values of a nontrivial additive character on the units of a finite field sum to
`-1`**: they are the values on all of `F`, which sum to `0`, minus the value `1` at `0`. -/
private theorem sum_units_addChar {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {ψ : AddChar F R} (hψ : ψ ≠ 0) : ∑ c : Fˣ, ψ (c : F) = -1 := by
  have hunits : ∑ t ∈ (Finset.univ : Finset F).erase 0, ψ t = ∑ c : Fˣ, ψ (c : F) := by
    rw [Finset.sum_subtype ((Finset.univ : Finset F).erase 0) (p := fun x => x ≠ 0)
      (fun x => by simp) (fun t => ψ t)]
    exact (Fintype.sum_equiv unitsEquivNeZero _ _ fun c => rfl).symm
  have hsplit : ψ 0 + ∑ t ∈ (Finset.univ : Finset F).erase 0, ψ t = ∑ t : F, ψ t :=
    Finset.add_sum_erase _ _ (Finset.mem_univ 0)
  rw [hunits, AddChar.map_zero_eq_one, AddChar.sum_eq_zero_iff_ne_zero.mpr hψ] at hsplit
  linear_combination hsplit

end Fintype

/-- **The induced class function of a product character at a non-semisimple element.**  If `f`
reads the two coordinates of `Z U ≅ Fˣ × (F, +)` as `f (!![u, u t; 0, u]) = μ u * ψ t`, with `ψ` a
nontrivial additive character, then the `q - 1` summands of
`TauCeti.GL2ScalarUnipotent.indClassFun_jordanGL` are `μ a` times the values of `ψ` on `Fˣ`, and
those sum to `-1`.  So the value is `-μ a`, of size `1` rather than of size `q - 1`.

Together with `TauCeti.GL2ScalarUnipotent.indClassFun_scalar` and the two vanishing statements
this is the Gelfand-Graev induced character of `GL₂(𝔽_q)`, of degree `q² - 1`. -/
theorem indClassFun_jordanGL_of_eq_mul [Finite F] {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R]
    (f : GL2ScalarUnipotent F → R) (μ : Fˣ → R) {ψ : AddChar F R} (hψ : ψ ≠ 0)
    (hf : ∀ (u : Fˣ) (t : F),
      f ⟨jordanGL u ((u : F) * t), jordanGL_mem_gl2ScalarUnipotent u ((u : F) * t)⟩ = μ u * ψ t)
    (a : Fˣ) {b : F} (hb : b ≠ 0) :
    indClassFun (GL2ScalarUnipotent F) f (jordanGL a b) = -μ a := by
  classical
  let _ := Fintype.ofFinite F
  have hval : ∀ c : Fˣ,
      f ⟨jordanGL a (c : F), jordanGL_mem_gl2ScalarUnipotent a (c : F)⟩ =
        μ a * ψ (((a⁻¹ : Fˣ) : F) * (c : F)) := fun c => by
    rw [← hf a (((a⁻¹ : Fˣ) : F) * (c : F))]
    exact congrArg f (Subtype.ext (congrArg (jordanGL a)
      (by rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul])))
  have hshift : ∑ c : Fˣ, ψ (((a⁻¹ : Fˣ) : F) * (c : F)) = ∑ c : Fˣ, ψ (c : F) :=
    Fintype.sum_equiv (Equiv.mulLeft a⁻¹) _ _ fun c => congrArg ψ (Units.val_mul a⁻¹ c).symm
  rw [indClassFun_jordanGL f a hb, Finset.sum_congr rfl fun c _ => hval c, ← Finset.mul_sum,
    hshift, sum_units_addChar hψ, mul_neg_one]


end Semiring

end GL2ScalarUnipotent

end TauCeti
