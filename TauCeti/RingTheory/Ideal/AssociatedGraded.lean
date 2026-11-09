/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Ideal.Maps
public import TauCeti.RingTheory.Ideal.Operations

/-!
# The associated graded ring of an ideal

For an ideal `I` of a commutative ring `R`, this file constructs the associated graded ring
`gr_I R = ⨁ n, I ^ n ⧸ I ^ (n + 1)` on its native direct-sum carrier. The product of the class of
`x ∈ I ^ m` in degree `m` and the class of `y ∈ I ^ n` in degree `n` is the class of `x * y` in
degree `m + n`. For a maximal ideal this is the ring of the tangent cone; for the maximal ideal of
a regular local ring it is a polynomial ring over the residue field, which is the standard route to
the multiplicativity of the order function.

## Main definitions

* `Ideal.GradedPiece I n`: the degree-`n` piece `I ^ n ⧸ I ^ (n + 1)`.
* `Ideal.AssociatedGraded I`: the direct sum `⨁ n, I ^ n ⧸ I ^ (n + 1)`, a commutative
  `R`-algebra and an `R ⧸ I`-algebra.
* `Ideal.AssociatedGraded.mk I n`: the `R`-linear map sending `x ∈ I ^ n` to its class in
  degree `n`.
* `Ideal.gradedPieceZeroEquiv I`: the degree-zero piece is `R ⧸ I`.
* `Ideal.AssociatedGraded.map f h`: the ring homomorphism `gr_I R →+* gr_J S` induced by a ring
  homomorphism `f : R →+* S` with `I ≤ J.comap f`.

## Main results

* `Ideal.AssociatedGraded.mk_eq_zero_iff`: the class of `x ∈ I ^ n` in degree `n` vanishes exactly
  when `x ∈ I ^ (n + 1)`.
* `Ideal.AssociatedGraded.mk_mul_mk`: the product rule `[x]_m * [y]_n = [x * y]_(m + n)`.
* `Ideal.AssociatedGraded.ker_algebraMap`: the kernel of `R → gr_I R` is `I`, so
  `R ⧸ I → gr_I R` is injective (`Ideal.AssociatedGraded.algebraMap_quotient_injective`).
* `Ideal.AssociatedGraded.map_id` and `Ideal.AssociatedGraded.map_comp`: functoriality.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
* H. Matsumura, *Commutative Ring Theory*, §14.
* The Stacks project, Lemma 00NO.

## Implementation notes

The graded multiplication, unit and scalar structures follow the pattern of
`TauCeti.Algebra.wordFiltration.AssociatedGraded`. The instance `gradedGSemiring` is stated
explicitly because `DirectSum.GRing.toGSemiring` supplies the pointwise `AddCommMonoid` through
`AddCommGroup.toAddCommMonoid`, which does not match the one instance search finds directly for the
quotient pieces.
-/

public section

open scoped DirectSum

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The degree-`n` piece `I ^ n ⧸ I ^ (n + 1)` of the associated graded ring of `I`. -/
abbrev GradedPiece (n : ℕ) : Type u :=
  ↥(I ^ n) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1))

/-- The associated graded ring `⨁ n, I ^ n ⧸ I ^ (n + 1)` of an ideal `I`. -/
abbrev AssociatedGraded : Type u :=
  ⨁ n : ℕ, I.GradedPiece n

variable {I}

/-- The class of `x ∈ I ^ n` in the degree-`n` piece vanishes exactly when `x ∈ I ^ (n + 1)`. -/
theorem gradedPiece_mk_eq_zero_iff {n : ℕ} (x : ↥(I ^ n)) :
    (Submodule.Quotient.mk x : I.GradedPiece n) = 0 ↔ (x : R) ∈ I ^ (n + 1) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

private noncomputable def filteredMul (I : Ideal R) (i j : ℕ) :
    ↥(I ^ i) →ₗ[R] ↥(I ^ j) →ₗ[R] ↥(I ^ (i + j)) :=
  LinearMap.mk₂ R (fun x y => ⟨(x : R) * y, mul_mem_pow_add x.2 y.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

private noncomputable def gradedPreMul (I : Ideal R) (i j : ℕ) :
    ↥(I ^ i) →ₗ[R] ↥(I ^ j) →ₗ[R] I.GradedPiece (i + j) :=
  (filteredMul I i j).compr₂ (Submodule.mkQ _)

private theorem gradedPreMul_apply (i j : ℕ) (x : ↥(I ^ i)) (y : ↥(I ^ j)) :
    gradedPreMul I i j x y =
      Submodule.Quotient.mk (⟨(x : R) * y, mul_mem_pow_add x.2 y.2⟩ : ↥(I ^ (i + j))) :=
  rfl

private theorem gradedPreMul_ker_left (i j : ℕ) :
    Submodule.comap (I ^ i).subtype (I ^ (i + 1)) ≤ (gradedPreMul I i j).ker := by
  intro x hx
  rw [Submodule.mem_comap, Submodule.subtype_apply] at hx
  rw [LinearMap.mem_ker]
  ext y
  rw [gradedPreMul_apply, LinearMap.zero_apply, gradedPiece_mk_eq_zero_iff]
  have h := mul_mem_pow_add hx y.2
  rwa [Nat.add_right_comm] at h

private theorem gradedPreMul_ker_right (i j : ℕ) :
    Submodule.comap (I ^ j).subtype (I ^ (j + 1)) ≤ (gradedPreMul I i j).flip.ker := by
  intro y hy
  rw [Submodule.mem_comap, Submodule.subtype_apply] at hy
  rw [LinearMap.mem_ker]
  ext x
  rw [LinearMap.flip_apply, gradedPreMul_apply, LinearMap.zero_apply,
    gradedPiece_mk_eq_zero_iff]
  exact mul_mem_pow_add (i := i) (j := j + 1) x.2 hy

variable (I) in
/-- The multiplication `I ^ i ⧸ I ^ (i + 1) × I ^ j ⧸ I ^ (j + 1) → I ^ (i + j) ⧸ I ^ (i + j + 1)`
of two homogeneous pieces, induced by multiplication in `R`. -/
noncomputable def gradedMul (i j : ℕ) :
    I.GradedPiece i →ₗ[R] I.GradedPiece j →ₗ[R] I.GradedPiece (i + j) :=
  (gradedPreMul I i j).liftQ₂ _ _ (gradedPreMul_ker_left i j) (gradedPreMul_ker_right i j)

/-- On representatives, the homogeneous product is induced by multiplication in `R`. -/
@[simp]
theorem gradedMul_mk (i j : ℕ) (x : ↥(I ^ i)) (y : ↥(I ^ j)) :
    gradedMul I i j (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨(x : R) * y, mul_mem_pow_add x.2 y.2⟩ : ↥(I ^ (i + j))) := by
  rw [gradedMul, LinearMap.liftQ₂_mk, gradedPreMul_apply]

private theorem gradedPiece_cast_mk {i j : ℕ} (h : i = j) (x : ↥(I ^ i)) :
    cast (congrArg I.GradedPiece h) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (⟨(x : R), h ▸ x.2⟩ : ↥(I ^ j)) := by
  subst j
  rfl

private theorem gradedMul_mk_eq_cast {i j k : ℕ} (h : i + j = k) (x : ↥(I ^ i))
    (y : ↥(I ^ j)) (z : ↥(I ^ k)) (hz : (x : R) * y = z) :
    cast (congrArg I.GradedPiece h)
        (gradedMul I i j (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) =
      Submodule.Quotient.mk z := by
  rw [gradedMul_mk, gradedPiece_cast_mk h]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hz)

private theorem gradedMul_mk_eq_cast_rev {i j k : ℕ} (h : k = i + j) (x : ↥(I ^ i))
    (y : ↥(I ^ j)) (z : ↥(I ^ k)) (hz : (x : R) * y = z) :
    gradedMul I i j (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      cast (congrArg I.GradedPiece h) (Submodule.Quotient.mk z) := by
  subst k
  exact gradedMul_mk_eq_cast rfl x y z hz

private theorem gradedMul_assoc (i j k : ℕ) (x : I.GradedPiece i) (y : I.GradedPiece j)
    (z : I.GradedPiece k) :
    cast (congrArg I.GradedPiece (Nat.add_assoc i j k))
        (gradedMul I (i + j) k (gradedMul I i j x y) z) =
      gradedMul I i (j + k) x (gradedMul I j k y z) := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  induction z using Submodule.Quotient.induction_on with | _ z =>
  rw [gradedMul_mk, gradedMul_mk j k y z]
  conv_rhs => rw [gradedMul_mk]
  exact gradedMul_mk_eq_cast (Nat.add_assoc i j k) _ z _ (mul_assoc (x : R) y z)

private theorem gradedMul_comm (i j : ℕ) (x : I.GradedPiece i) (y : I.GradedPiece j) :
    cast (congrArg I.GradedPiece (Nat.add_comm i j)) (gradedMul I i j x y) =
      gradedMul I j i y x := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  conv_rhs => rw [gradedMul_mk]
  exact gradedMul_mk_eq_cast (Nat.add_comm i j) x y _ (mul_comm (x : R) y)

variable (I) in
/-- The degree-zero unit: the class of `1 ∈ I ^ 0`. -/
noncomputable def gradedOne : I.GradedPiece 0 :=
  Submodule.Quotient.mk ⟨1, I.mem_pow_zero 1⟩

variable (I) in
/-- The degree-zero class of an element of `R`. -/
noncomputable def gradedAlgebraMap₀ : R →ₗ[R] I.GradedPiece 0 :=
  (Submodule.mkQ _).comp (LinearMap.codRestrict (I ^ 0) LinearMap.id I.mem_pow_zero)

/-- The degree-zero class of `r` is the class of `r ∈ I ^ 0`. -/
theorem gradedAlgebraMap₀_apply (r : R) :
    gradedAlgebraMap₀ I r = Submodule.Quotient.mk (⟨r, I.mem_pow_zero r⟩ : ↥(I ^ 0)) :=
  (rfl)

/-- The degree-zero class of `1` is the degree-zero unit. -/
@[simp]
theorem gradedAlgebraMap₀_one : gradedAlgebraMap₀ I 1 = gradedOne I :=
  (rfl)

private theorem gradedOne_mul (k : ℕ) (x : I.GradedPiece k) :
    gradedMul I 0 k (gradedOne I) x = cast (congrArg I.GradedPiece (Nat.zero_add k).symm) x := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  exact gradedMul_mk_eq_cast_rev (Nat.zero_add k).symm _ x x (one_mul (x : R))

private theorem gradedMul_one (k : ℕ) (x : I.GradedPiece k) :
    gradedMul I k 0 x (gradedOne I) = cast (congrArg I.GradedPiece (Nat.add_zero k).symm) x := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  exact gradedMul_mk_eq_cast_rev (Nat.add_zero k).symm x _ x (mul_one (x : R))

private theorem gradedAlgebraMap₀_mul (r : R) (k : ℕ) (x : I.GradedPiece k) :
    cast (congrArg I.GradedPiece (Nat.zero_add k)) (gradedMul I 0 k (gradedAlgebraMap₀ I r) x) =
      r • x := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  rw [gradedAlgebraMap₀_apply, ← Submodule.Quotient.mk_smul]
  exact gradedMul_mk_eq_cast (Nat.zero_add k) _ x _ (smul_eq_mul r (x : R)).symm

private theorem gradedMul_gradedAlgebraMap₀ (r s : R) :
    gradedMul I 0 0 (gradedAlgebraMap₀ I r) (gradedAlgebraMap₀ I s) =
      gradedAlgebraMap₀ I (r * s) := by
  rw [gradedAlgebraMap₀_apply, gradedAlgebraMap₀_apply, gradedMul_mk]
  rfl

/-- The degree-zero unit supplies the `GOne` structure on the pieces. -/
noncomputable instance gradedGOne : GradedMonoid.GOne I.GradedPiece where
  one := gradedOne I

/-- The graded unit is `gradedOne`. -/
@[simp]
theorem gradedGOne_one : (GradedMonoid.GOne.one : I.GradedPiece 0) = gradedOne I :=
  rfl

/-- Homogeneous multiplication supplies the `GMul` structure on the pieces. -/
noncomputable instance gradedGMul : GradedMonoid.GMul I.GradedPiece where
  mul {i j} x y := gradedMul I i j x y

/-- The graded multiplication is `gradedMul`. -/
@[simp]
theorem gradedGMul_mul {i j : ℕ} (x : I.GradedPiece i) (y : I.GradedPiece j) :
    GradedMonoid.GMul.mul x y = gradedMul I i j x y :=
  rfl

/-- The homogeneous unit and multiplication form a commutative graded monoid. -/
noncomputable instance gradedGCommMonoid : GradedMonoid.GCommMonoid I.GradedPiece :=
  { gradedGMul, gradedGOne with
    one_mul := fun ⟨k, x⟩ => by
      apply Sigma.ext (Nat.zero_add k)
      apply heq_of_cast_eq (congrArg I.GradedPiece (Nat.zero_add k))
      -- Expose the `GOne` and `GMul` fields as the named homogeneous operations.
      change cast _ (gradedMul I 0 k (gradedOne I) x) = x
      rw [gradedOne_mul, cast_cast, cast_eq]
    mul_one := fun ⟨k, x⟩ => by
      apply Sigma.ext (Nat.add_zero k)
      apply heq_of_cast_eq (congrArg I.GradedPiece (Nat.add_zero k))
      -- Expose the `GOne` and `GMul` fields as the named homogeneous operations.
      change cast _ (gradedMul I k 0 x (gradedOne I)) = x
      rw [gradedMul_one, cast_cast, cast_eq]
    mul_assoc := fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ => by
      apply Sigma.ext (Nat.add_assoc i j k)
      apply heq_of_cast_eq (congrArg I.GradedPiece (Nat.add_assoc i j k))
      exact gradedMul_assoc i j k x y z
    mul_comm := fun ⟨i, x⟩ ⟨j, y⟩ => by
      apply Sigma.ext (Nat.add_comm i j)
      apply heq_of_cast_eq (congrArg I.GradedPiece (Nat.add_comm i j))
      exact gradedMul_comm i j x y }

/-- Bilinearity of the homogeneous product makes the pieces a commutative direct-sum graded
ring. -/
noncomputable instance gradedGCommRing : DirectSum.GCommRing I.GradedPiece :=
  { gradedGCommMonoid with
    mul_zero := fun x => (gradedMul I _ _ x).map_zero
    zero_mul := fun x => LinearMap.map_zero₂ (gradedMul I _ _) x
    mul_add := fun x y z => (gradedMul I _ _ x).map_add y z
    add_mul := fun x y z => LinearMap.map_add₂ (gradedMul I _ _) x y z
    natCast := fun n => gradedAlgebraMap₀ I n
    natCast_zero := by
      rw [Nat.cast_zero]
      exact map_zero (gradedAlgebraMap₀ I)
    natCast_succ := fun n => by
      -- The cast field is the degree-zero class of the scalar cast.
      change gradedAlgebraMap₀ I ((n + 1 : ℕ) : R) = gradedAlgebraMap₀ I (n : R) + gradedOne I
      rw [Nat.cast_succ, map_add, gradedAlgebraMap₀_one]
    intCast := fun z => gradedAlgebraMap₀ I z
    intCast_ofNat := fun n => by
      -- The cast field is the degree-zero class of the scalar cast.
      change gradedAlgebraMap₀ I ((n : ℤ) : R) = gradedAlgebraMap₀ I (n : R)
      rw [Int.cast_natCast]
    intCast_negSucc_ofNat := fun n => by
      -- The cast field is the degree-zero class of the scalar cast.
      change gradedAlgebraMap₀ I ((Int.negSucc n : ℤ) : R) =
        -gradedAlgebraMap₀ I ((n + 1 : ℕ) : R)
      rw [Int.cast_negSucc, map_neg] }

/-- The graded-ring structure supplies the graded-semiring structure used by the direct sum. -/
noncomputable instance gradedGSemiring : DirectSum.GSemiring I.GradedPiece :=
  @DirectSum.GRing.toGSemiring ℕ I.GradedPiece _ _ gradedGCommRing.toGRing

/-- Degree-zero classes of scalars make the pieces a graded `R`-algebra. -/
noncomputable instance gradedGAlgebra : DirectSum.GAlgebra R I.GradedPiece where
  toFun := (gradedAlgebraMap₀ I).toAddMonoidHom
  map_one := gradedAlgebraMap₀_one
  map_mul r s := by
    apply Sigma.ext (Nat.zero_add 0).symm
    apply heq_of_cast_eq (congrArg I.GradedPiece (Nat.zero_add 0).symm)
    -- The scalar product is a degree-zero homogeneous product after this reindexing.
    change cast _ (gradedAlgebraMap₀ I (r * s)) =
      gradedMul I 0 0 (gradedAlgebraMap₀ I r) (gradedAlgebraMap₀ I s)
    rw [gradedMul_gradedAlgebraMap₀, cast_eq]
  commutes r x := mul_comm _ _
  smul_def r := fun ⟨k, x⟩ => by
    apply Sigma.ext (Nat.zero_add k).symm
    apply heq_of_cast_eq (congrArg I.GradedPiece (Nat.zero_add k).symm)
    -- The sigma-level scalar law is the degree-`k` homogeneous scalar equation.
    change cast _ (r • x) = gradedMul I 0 k (gradedAlgebraMap₀ I r) x
    rw [← gradedAlgebraMap₀_mul r k x, cast_cast, cast_eq]

/-- The graded scalar map is `gradedAlgebraMap₀`. -/
@[simp]
theorem gradedGAlgebra_toFun (r : R) :
    (DirectSum.GAlgebra.toFun r : I.GradedPiece 0) = gradedAlgebraMap₀ I r :=
  rfl

namespace AssociatedGraded

variable (I) in
/-- The class in degree `n` of an element of `I ^ n`. -/
noncomputable def mk (n : ℕ) : ↥(I ^ n) →ₗ[R] I.AssociatedGraded :=
  DirectSum.lof R ℕ I.GradedPiece n ∘ₗ Submodule.mkQ _

/-- The class in degree `n` is the summand inclusion of the quotient class. -/
theorem mk_apply (n : ℕ) (x : ↥(I ^ n)) :
    mk I n x = DirectSum.of I.GradedPiece n (Submodule.Quotient.mk x) :=
  (rfl)

/-- The class of `x ∈ I ^ n` in degree `n` vanishes exactly when `x ∈ I ^ (n + 1)`. -/
@[simp]
theorem mk_eq_zero_iff {n : ℕ} (x : ↥(I ^ n)) : mk I n x = 0 ↔ (x : R) ∈ I ^ (n + 1) := by
  rw [mk_apply, map_eq_zero_iff _ (DirectSum.of_injective n), gradedPiece_mk_eq_zero_iff]

/-- Two elements of `I ^ n` have the same class in degree `n` exactly when they agree modulo
`I ^ (n + 1)`. -/
theorem mk_eq_mk_iff {n : ℕ} (x y : ↥(I ^ n)) :
    mk I n x = mk I n y ↔ (x : R) - y ∈ I ^ (n + 1) := by
  rw [← Submodule.coe_sub, ← mk_eq_zero_iff, map_sub, sub_eq_zero]

/-- The class of an element does not depend on how its degree is written. -/
theorem mk_congr {m n : ℕ} (h : m = n) (x : ↥(I ^ m)) :
    mk I m x = mk I n ⟨(x : R), h ▸ x.2⟩ := by
  subst n
  rfl

/-- **Product rule.** The product of the classes of `x ∈ I ^ m` and `y ∈ I ^ n` is the class of
`x * y` in degree `m + n`. -/
@[simp]
theorem mk_mul_mk {m n : ℕ} (x : ↥(I ^ m)) (y : ↥(I ^ n)) :
    mk I m x * mk I n y = mk I (m + n) ⟨(x : R) * y, mul_mem_pow_add x.2 y.2⟩ := by
  rw [mk_apply, mk_apply, DirectSum.of_mul_of, gradedGMul_mul, gradedMul_mk, mk_apply]

/-- The class of `r ∈ I ^ 0 = R` in degree zero is the image of `r` under the algebra map. -/
@[simp]
theorem mk_zero (r : ↥(I ^ 0)) : mk I 0 r = algebraMap R I.AssociatedGraded r := by
  rw [mk_apply, DirectSum.algebraMap_apply, gradedGAlgebra_toFun, gradedAlgebraMap₀_apply]

/-- The class of `1` in degree zero is the unit. -/
theorem mk_zero_one : mk I 0 ⟨1, I.mem_pow_zero 1⟩ = 1 := by
  rw [mk_zero, map_one]

/-- The `k`-th power of the class of `x ∈ I ^ n` is the class of `x ^ k` in degree `k * n`. -/
theorem mk_pow {n : ℕ} (x : ↥(I ^ n)) (k : ℕ) :
    mk I n x ^ k =
      mk I (k * n) ⟨(x : R) ^ k, by rw [mul_comm, pow_mul]; exact pow_mem_pow x.2 k⟩ := by
  induction k with
  | zero =>
    rw [pow_zero, mk_congr (Nat.zero_mul n), ← mk_zero_one]
    exact congrArg (mk I 0) (Subtype.ext (pow_zero (x : R)).symm)
  | succ k ih =>
    rw [pow_succ, ih, mk_mul_mk, mk_congr (Nat.succ_mul k n).symm]
    simp only [pow_succ]

/-- An element of `R` maps to zero in the associated graded ring exactly when it lies in `I`. -/
@[simp]
theorem algebraMap_eq_zero_iff (r : R) : algebraMap R I.AssociatedGraded r = 0 ↔ r ∈ I := by
  rw [← mk_zero ⟨r, I.mem_pow_zero r⟩, mk_eq_zero_iff, zero_add, pow_one]

/-- The kernel of `R → gr_I R` is `I`. -/
theorem ker_algebraMap : RingHom.ker (algebraMap R I.AssociatedGraded) = I := by
  ext r
  rw [RingHom.mem_ker, algebraMap_eq_zero_iff]

/-- The associated graded ring of `I` is an `R ⧸ I`-algebra through its degree-zero part. -/
noncomputable instance instAlgebraQuotient : Algebra (R ⧸ I) I.AssociatedGraded :=
  (Ideal.Quotient.lift I (algebraMap R I.AssociatedGraded) fun r hr =>
    (algebraMap_eq_zero_iff r).mpr hr).toAlgebra' fun _ x => mul_comm _ x

/-- The algebra map from `R ⧸ I` sends the class of `r` to the image of `r`. -/
@[simp]
theorem algebraMap_quotient_mk (r : R) :
    algebraMap (R ⧸ I) I.AssociatedGraded (Ideal.Quotient.mk I r) =
      algebraMap R I.AssociatedGraded r :=
  (rfl)

/-- The `R`-algebra structure of `gr_I R` factors through `R ⧸ I`. -/
instance : IsScalarTower R (R ⧸ I) I.AssociatedGraded :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := R ⧸ I) (A := I.AssociatedGraded) fun r =>
    (algebraMap_quotient_mk r).symm

/-- The degree-zero part of `gr_I R` is a copy of `R ⧸ I`. -/
theorem algebraMap_quotient_injective :
    Function.Injective (algebraMap (R ⧸ I) I.AssociatedGraded) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [algebraMap_quotient_mk, algebraMap_eq_zero_iff] at hq
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

end AssociatedGraded

private noncomputable def powZeroEquiv (I : Ideal R) : ↥(I ^ 0) ≃ₗ[R] R :=
  (LinearEquiv.ofEq _ _ ((pow_zero I).trans one_eq_top)).trans Submodule.topEquiv

private theorem map_subtype_comap_pow_one :
    (Submodule.comap (I ^ 0).subtype (I ^ 1)).map
        (powZeroEquiv I : ↥(I ^ 0) →ₗ[R] R) = I := by
  have h : (powZeroEquiv I : ↥(I ^ 0) →ₗ[R] R) = (I ^ 0).subtype :=
    LinearMap.ext fun _ => rfl
  rw [h, Submodule.map_comap_subtype, pow_zero, one_eq_top, pow_one]
  exact top_inf_eq I

variable (I) in
/-- The degree-zero piece `I ^ 0 ⧸ I ^ 1` of the associated graded ring is `R ⧸ I`. -/
noncomputable def gradedPieceZeroEquiv : I.GradedPiece 0 ≃ₗ[R] R ⧸ I :=
  Submodule.Quotient.equiv _ I (powZeroEquiv I) map_subtype_comap_pow_one

/-- `gradedPieceZeroEquiv` sends the class of `x ∈ I ^ 0` to the class of `x` in `R ⧸ I`. -/
@[simp]
theorem gradedPieceZeroEquiv_mk (x : ↥(I ^ 0)) :
    gradedPieceZeroEquiv I (Submodule.Quotient.mk x) = Ideal.Quotient.mk I x :=
  (rfl)

/-- Under `gradedPieceZeroEquiv`, the degree-zero summand of `gr_I R` is the image of the
algebra map from `R ⧸ I`. -/
theorem AssociatedGraded.of_gradedPieceZeroEquiv_symm (q : R ⧸ I) :
    DirectSum.of I.GradedPiece 0 ((gradedPieceZeroEquiv I).symm q) =
      algebraMap (R ⧸ I) I.AssociatedGraded q := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h : (gradedPieceZeroEquiv I).symm (Ideal.Quotient.mk I r) =
      Submodule.Quotient.mk ⟨r, I.mem_pow_zero r⟩ :=
    (LinearEquiv.symm_apply_eq _).mpr
      (gradedPieceZeroEquiv_mk (I := I) ⟨r, I.mem_pow_zero r⟩).symm
  rw [h, ← mk_apply, mk_zero, algebraMap_quotient_mk]

section map

variable {S : Type v} [CommRing S] {J : Ideal S}

private noncomputable def gradedPieceMap (f : R →+* S) (h : I ≤ J.comap f) (n : ℕ) :
    I.GradedPiece n →ₛₗ[f] J.GradedPiece n :=
  Submodule.mapQ _ _
    ((f.toSemilinearMap.domRestrict (I ^ n)).codRestrict (J ^ n) fun x =>
      map_mem_pow_of_le_comap f h x.2)
    fun x hx => by
      rw [Submodule.mem_comap, Submodule.subtype_apply] at hx
      exact map_mem_pow_of_le_comap f h hx

private theorem gradedPieceMap_mk (f : R →+* S) (h : I ≤ J.comap f) {n : ℕ} (x : ↥(I ^ n)) :
    gradedPieceMap f h n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (⟨f x, map_mem_pow_of_le_comap f h x.2⟩ : ↥(J ^ n)) :=
  rfl

namespace AssociatedGraded

/-- The ring homomorphism `gr_I R →+* gr_J S` induced by a ring homomorphism `f : R →+* S`
with `I ≤ J.comap f`: it sends the class of `x ∈ I ^ n` to the class of `f x ∈ J ^ n`. -/
noncomputable def map (f : R →+* S) (h : I ≤ J.comap f) :
    I.AssociatedGraded →+* J.AssociatedGraded :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of J.GradedPiece n).comp (gradedPieceMap f h n).toAddMonoidHom)
    (by
      -- The unit is the class of `1`, which `f` preserves.
      change DirectSum.of J.GradedPiece 0 (gradedPieceMap f h 0 (gradedOne I)) = 1
      rw [gradedOne, gradedPieceMap_mk, ← mk_apply, ← mk_zero_one]
      exact congrArg (mk J 0) (Subtype.ext (map_one f)))
    (fun {i j} x y => by
      induction x using Submodule.Quotient.induction_on with | _ x =>
      induction y using Submodule.Quotient.induction_on with | _ y =>
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, gradedGMul_mul,
        gradedMul_mk, gradedPieceMap_mk, ← mk_apply, mk_mul_mk, map_mul])

/-- `AssociatedGraded.map` sends the class of `x ∈ I ^ n` to the class of `f x ∈ J ^ n`. -/
@[simp]
theorem map_mk (f : R →+* S) (h : I ≤ J.comap f) {n : ℕ} (x : ↥(I ^ n)) :
    map f h (mk I n x) = mk J n ⟨f x, map_mem_pow_of_le_comap f h x.2⟩ := by
  rw [map, mk_apply, DirectSum.toSemiring_of, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, gradedPieceMap_mk, mk_apply]

/-- `AssociatedGraded.map` is compatible with the algebra maps from `R` and `S`. -/
@[simp]
theorem map_algebraMap (f : R →+* S) (h : I ≤ J.comap f) (r : R) :
    map f h (algebraMap R I.AssociatedGraded r) = algebraMap S J.AssociatedGraded (f r) := by
  rw [← mk_zero ⟨r, I.mem_pow_zero r⟩, map_mk, mk_zero]

/-- Two ring homomorphisms out of `gr_I R` agree once they agree on every homogeneous class. -/
theorem ringHom_ext {T : Type w} [Semiring T] {φ ψ : I.AssociatedGraded →+* T}
    (h : ∀ n (x : ↥(I ^ n)), φ (mk I n x) = ψ (mk I n x)) : φ = ψ :=
  DirectSum.ringHom_ext fun n x => by
    induction x using Submodule.Quotient.induction_on with | _ x =>
    exact h n x

/-- The identity of `R` induces the identity of `gr_I R`. -/
@[simp]
theorem map_id (h : I ≤ I.comap (RingHom.id R)) : map (RingHom.id R) h = RingHom.id _ :=
  ringHom_ext fun n x => by simp

/-- The map induced by a composite is the composite of the induced maps. -/
theorem map_comp {T : Type w} [CommRing T] {K : Ideal T} (g : S →+* T) (f : R →+* S)
    (hJK : J ≤ K.comap g) (hIJ : I ≤ J.comap f) (hIK : I ≤ K.comap (g.comp f)) :
    (map g hJK).comp (map f hIJ) = map (g.comp f) hIK :=
  ringHom_ext fun n x => by simp

end AssociatedGraded

end map

end Ideal
