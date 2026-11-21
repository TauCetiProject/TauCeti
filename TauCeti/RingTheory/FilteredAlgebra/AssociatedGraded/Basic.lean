/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.RingTheory.FilteredAlgebra.Basic

/-!
# The associated graded ring of a decreasing ideal filtration

Let `F` be a decreasing multiplicative filtration `A = F⁰ ⊇ F¹ ⊇ ⋯` of a possibly noncommutative
ring `A` by two-sided ideals (`TauCeti.AlgFiltration`). Its associated graded ring is
`gr A = ⨁ n, Fⁿ / Fⁿ⁺¹`, with multiplication of homogeneous classes induced by multiplication in
`A`: the product of the classes of `x ∈ Fᵐ` and `y ∈ Fⁿ` is the class of `x * y ∈ Fᵐ⁺ⁿ`. This is
well defined because `Fᵐ⁺¹ * Fⁿ` and `Fᵐ * Fⁿ⁺¹` lie in `Fᵐ⁺ⁿ⁺¹`.

The associated graded ring is the tool for transferring ring-theoretic properties from a graded
ring, where they are often computable, to a complete filtered ring: Iwasawa algebras of uniform
pro-`p` groups and power series rings have polynomial associated graded rings. The transfer of
the domain property is in `TauCeti.RingTheory.FilteredAlgebra.AssociatedGraded.Domain`, and that of
the noetherian property in `TauCeti.RingTheory.FilteredAlgebra.AssociatedGraded.Noetherian`.

## Main definitions

* `TauCeti.AlgFiltration.GradedPiece F n`: the additive group `Fⁿ / Fⁿ⁺¹`.
* `TauCeti.AlgFiltration.gradedMul F m n`: the biadditive product
  `Fᵐ / Fᵐ⁺¹ → Fⁿ / Fⁿ⁺¹ → Fᵐ⁺ⁿ / Fᵐ⁺ⁿ⁺¹`.
* `TauCeti.AlgFiltration.gradedZeroMk F`: the class map `A → F⁰ / F¹`, which supplies the unit
  and the numeral casts.
* `TauCeti.AlgFiltration.AssociatedGraded F`: the direct sum `⨁ n, Fⁿ / Fⁿ⁺¹`, with its ring
  structure `TauCeti.AlgFiltration.instRingAssociatedGraded`.

## Main results

* `TauCeti.AlgFiltration.gradedPiece_mk_eq_zero_iff`: the class of `x ∈ Fⁿ` vanishes exactly
  when `x ∈ Fⁿ⁺¹`.
* `TauCeti.AlgFiltration.gradedMul_mk_mk`: homogeneous products are computed on representatives.
* `TauCeti.AlgFiltration.of_mk_mul_of_mk`, `TauCeti.AlgFiltration.of_mk_eq_zero_iff`: the same
  statements for homogeneous elements of `gr A`.

## Implementation notes

The graded-ring packaging (the transport lemmas along equalities of degrees and the
`DirectSum.GRing` instance) follows the associated graded algebra of a word filtration in
`TauCeti.Algebra.WordFiltration.AssociatedGraded`. Here the pieces are quotients of additive groups
and the product is biadditive, so `gr A` is a ring and no coefficient algebra is fixed.

## References

* P. Schneider and J. Teitelbaum, *Algebras of `p`-adic distributions and admissible
  representations*, Invent. Math. 153 (2003), §1.
* J.-E. Björk, *Filtered Noetherian rings*, in *Noetherian rings and their applications*, Math.
  Surveys Monogr. 24 (1987).
-/

public section

open scoped DirectSum

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] (F : AlgFiltration A)

/-- The `n`-th graded piece `Fⁿ / Fⁿ⁺¹` of a decreasing ideal filtration, as an additive group. -/
abbrev GradedPiece (n : ℕ) : Type _ :=
  F.ideal n ⧸ (F.ideal (n + 1)).toAddSubgroup.comap (F.ideal n).subtype.toAddMonoidHom

variable {F}

/-- Membership in the subgroup of `Fⁿ` defining `Fⁿ / Fⁿ⁺¹` is membership in `Fⁿ⁺¹`. -/
private theorem mem_comap_iff {n : ℕ} (x : F.ideal n) :
    x ∈ (F.ideal (n + 1)).toAddSubgroup.comap (F.ideal n).subtype.toAddMonoidHom ↔
      (x : A) ∈ F.ideal (n + 1) := by
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe,
    Submodule.coe_subtype]

/-- The class of `x ∈ Fⁿ` in `Fⁿ / Fⁿ⁺¹` vanishes exactly when `x ∈ Fⁿ⁺¹`. -/
theorem gradedPiece_mk_eq_zero_iff {n : ℕ} (x : F.ideal n) :
    (x : F.GradedPiece n) = 0 ↔ (x : A) ∈ F.ideal (n + 1) := by
  rw [QuotientAddGroup.eq_zero_iff, mem_comap_iff]

/-- Two elements of `Fⁿ` have the same class in `Fⁿ / Fⁿ⁺¹` exactly when their difference lies
in `Fⁿ⁺¹`. -/
theorem gradedPiece_mk_eq_mk_iff {n : ℕ} (x y : F.ideal n) :
    (x : F.GradedPiece n) = y ↔ (x : A) - y ∈ F.ideal (n + 1) := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, gradedPiece_mk_eq_zero_iff, Submodule.coe_sub]

/-- Transporting a class along an equality of degrees keeps its representative. -/
theorem gradedPiece_cast_mk {i j : ℕ} (h : i = j) (x : A) (hi : x ∈ F.ideal i)
    (hj : x ∈ F.ideal j) :
    cast (congrArg F.GradedPiece h) (⟨x, hi⟩ : F.ideal i) =
      ((⟨x, hj⟩ : F.ideal j) : F.GradedPiece j) := by
  subst h
  rfl

/-- The class in `Fᵐ⁺ⁿ / Fᵐ⁺ⁿ⁺¹` of the product of a fixed `x ∈ Fᵐ` with `y ∈ Fⁿ`. -/
private def mulMk {m : ℕ} (n : ℕ) (x : F.ideal m) :
    F.ideal n →+ F.GradedPiece (m + n) :=
  (QuotientAddGroup.mk' _).comp
    { toFun y := ⟨x * y, F.mul_mem x.property y.property⟩
      map_zero' := Subtype.ext (mul_zero (x : A))
      map_add' y z := Subtype.ext (mul_add (x : A) y z) }

private theorem mulMk_apply {m n : ℕ} (x : F.ideal m)
    (y : F.ideal n) :
    mulMk n x y = ((⟨x * y, F.mul_mem x.property y.property⟩ : F.ideal (m + n)) :
      F.GradedPiece (m + n)) :=
  rfl

/-- Left multiplication of classes by a fixed `x ∈ Fᵐ`, descended to `Fⁿ / Fⁿ⁺¹`. -/
private def mulLeft {m : ℕ} (n : ℕ) (x : F.ideal m) :
    F.GradedPiece n →+ F.GradedPiece (m + n) :=
  QuotientAddGroup.lift _ (mulMk n x) fun y hy => by
    rw [mem_comap_iff] at hy
    rw [AddMonoidHom.mem_ker, mulMk_apply, gradedPiece_mk_eq_zero_iff]
    exact F.mul_mem (a := m) (b := n + 1) x.property hy

private theorem mulLeft_mk {m n : ℕ} (x : F.ideal m)
    (y : F.ideal n) :
    mulLeft n x y = ((⟨x * y, F.mul_mem x.property y.property⟩ : F.ideal (m + n)) :
      F.GradedPiece (m + n)) :=
  rfl

/-- `mulLeft` as an additive function of the left factor. -/
private def mulLeftHom (m n : ℕ) :
    F.ideal m →+ F.GradedPiece n →+ F.GradedPiece (m + n) where
  toFun x := mulLeft n x
  map_zero' := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun y => ?_)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, QuotientAddGroup.mk'_apply,
      mulLeft_mk, AddMonoidHom.zero_apply, gradedPiece_mk_eq_zero_iff, ZeroMemClass.coe_zero,
      zero_mul, zero_mem]
  map_add' x x' := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun y => ?_)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, QuotientAddGroup.mk'_apply,
      mulLeft_mk, AddMonoidHom.add_apply, ← QuotientAddGroup.mk_add]
    exact congrArg _ (Subtype.ext (add_mul (x : A) x' y))

variable (F) in
/-- The product `Fᵐ / Fᵐ⁺¹ → Fⁿ / Fⁿ⁺¹ → Fᵐ⁺ⁿ / Fᵐ⁺ⁿ⁺¹` of homogeneous classes, induced by
multiplication in `A`. -/
def gradedMul (m n : ℕ) : F.GradedPiece m →+ F.GradedPiece n →+ F.GradedPiece (m + n) :=
  QuotientAddGroup.lift _ (mulLeftHom m n) fun x hx => by
    rw [mem_comap_iff] at hx
    refine (AddMonoidHom.mem_ker).2
      (QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun y => ?_))
    simp only [mulLeftHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
      Function.comp_apply, QuotientAddGroup.mk'_apply, mulLeft_mk, AddMonoidHom.zero_apply,
      gradedPiece_mk_eq_zero_iff]
    simpa only [Nat.add_right_comm m 1 n] using F.mul_mem hx y.property

/-- The product of the classes of `x ∈ Fᵐ` and `y ∈ Fⁿ` is the class of `x * y ∈ Fᵐ⁺ⁿ`. -/
@[simp]
theorem gradedMul_mk_mk {m n : ℕ} (x : F.ideal m)
    (y : F.ideal n) :
    F.gradedMul m n x y = ((⟨x * y, F.mul_mem x.property y.property⟩ : F.ideal (m + n)) :
      F.GradedPiece (m + n)) :=
  (rfl)

/-- Homogeneous products of classes are computed on representatives, up to a transport of
degrees. -/
private theorem cast_gradedMul_mk_mk {i j k : ℕ} (h : i + j = k) (x : A) (hx : x ∈ F.ideal i)
    (y : A) (hy : y ∈ F.ideal j) (z : A) (hz : z ∈ F.ideal k) (hxyz : x * y = z) :
    cast (congrArg F.GradedPiece h)
        (F.gradedMul i j (⟨x, hx⟩ : F.ideal i)
          (⟨y, hy⟩ : F.ideal j)) =
      ((⟨z, hz⟩ : F.ideal k) : F.GradedPiece k) := by
  rw [gradedMul_mk_mk, gradedPiece_cast_mk h (x * y) (F.mul_mem hx hy) (hxyz ▸ hz)]
  exact congrArg _ (Subtype.ext hxyz)

variable (F) in
/-- The class in `F⁰ / F¹` of an element of `A = F⁰`. -/
def gradedZeroMk : A →+ F.GradedPiece 0 :=
  (QuotientAddGroup.mk' _).comp
    { toFun x := ⟨x, by simp⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- `gradedZeroMk` is the class of its argument. -/
@[simp]
theorem gradedZeroMk_apply (x : A) :
    F.gradedZeroMk x =
      ((⟨x, by simp⟩ : F.ideal 0) : F.GradedPiece 0) :=
  (rfl)

/-- The class of `1` is a left unit for the homogeneous product. -/
theorem gradedZeroMk_one_gradedMul {n : ℕ} (y : F.GradedPiece n) :
    cast (congrArg F.GradedPiece (Nat.zero_add n)) (F.gradedMul 0 n (F.gradedZeroMk 1) y) = y := by
  induction y using QuotientAddGroup.induction_on with
  | H y => exact cast_gradedMul_mk_mk (Nat.zero_add n) _ _ _ _ _ y.property (one_mul _)

/-- The class of `1` is a right unit for the homogeneous product. -/
theorem gradedMul_gradedZeroMk_one {n : ℕ} (x : F.GradedPiece n) :
    cast (congrArg F.GradedPiece (Nat.add_zero n)) (F.gradedMul n 0 x (F.gradedZeroMk 1)) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H x => exact cast_gradedMul_mk_mk (Nat.add_zero n) _ _ _ _ _ x.property (mul_one _)

/-- The homogeneous product is associative, up to a transport of degrees. -/
theorem gradedMul_assoc {i j k : ℕ} (x : F.GradedPiece i) (y : F.GradedPiece j)
    (z : F.GradedPiece k) :
    cast (congrArg F.GradedPiece (Nat.add_assoc i j k))
        (F.gradedMul (i + j) k (F.gradedMul i j x y) z) =
      F.gradedMul i (j + k) x (F.gradedMul j k y z) := by
  induction x using QuotientAddGroup.induction_on with | H x =>
  induction y using QuotientAddGroup.induction_on with | H y =>
  induction z using QuotientAddGroup.induction_on with | H z =>
  rw [gradedMul_mk_mk, gradedMul_mk_mk, gradedMul_mk_mk, gradedMul_mk_mk]
  exact cast_gradedMul_mk_mk (Nat.add_assoc i j k) _ _ _ _ _ _ (mul_assoc (x : A) y z)

instance : GradedMonoid.GOne F.GradedPiece where
  one := F.gradedZeroMk 1

instance : GradedMonoid.GMul F.GradedPiece where
  mul x y := F.gradedMul _ _ x y

/-- The graded unit is the class of `1`. -/
theorem gOne_def : (GradedMonoid.GOne.one : F.GradedPiece 0) = F.gradedZeroMk 1 :=
  (rfl)

/-- The graded product is `gradedMul`. -/
theorem gMul_def {m n : ℕ} (x : F.GradedPiece m) (y : F.GradedPiece n) :
    GradedMonoid.GMul.mul x y = F.gradedMul m n x y :=
  (rfl)

instance : GradedMonoid.GMonoid F.GradedPiece where
  one_mul := fun ⟨n, y⟩ =>
    Sigma.ext (Nat.zero_add n)
      (heq_of_cast_eq (congrArg F.GradedPiece (Nat.zero_add n))
        (gradedZeroMk_one_gradedMul y))
  mul_one := fun ⟨n, x⟩ =>
    Sigma.ext (Nat.add_zero n)
      (heq_of_cast_eq (congrArg F.GradedPiece (Nat.add_zero n))
        (gradedMul_gradedZeroMk_one x))
  mul_assoc := fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ =>
    Sigma.ext (Nat.add_assoc i j k)
      (heq_of_cast_eq (congrArg F.GradedPiece (Nat.add_assoc i j k))
        (gradedMul_assoc x y z))

instance : DirectSum.GRing F.GradedPiece where
  mul_zero x := (F.gradedMul _ _ x).map_zero
  zero_mul y := DFunLike.congr_fun (F.gradedMul _ _).map_zero y
  mul_add x y z := (F.gradedMul _ _ x).map_add y z
  add_mul x y z := DFunLike.congr_fun ((F.gradedMul _ _).map_add x y) z
  natCast n := F.gradedZeroMk n
  natCast_zero := by rw [Nat.cast_zero, map_zero]
  natCast_succ n := by rw [Nat.cast_succ, map_add, gOne_def]
  intCast z := F.gradedZeroMk z
  intCast_ofNat n := by rw [Int.cast_natCast]
  intCast_negSucc_ofNat n := by rw [Int.cast_negSucc, map_neg]

variable (F) in
/-- The associated graded ring `gr A = ⨁ n, Fⁿ / Fⁿ⁺¹` of a decreasing ideal filtration. -/
abbrev AssociatedGraded : Type _ :=
  ⨁ n, F.GradedPiece n

/-- The ring structure on the associated graded ring. -/
instance instRingAssociatedGraded : Ring F.AssociatedGraded :=
  DirectSum.ring F.GradedPiece

/-- In the associated graded ring, the product of the homogeneous classes of `x ∈ Fᵐ` and
`y ∈ Fⁿ` is the homogeneous class of `x * y ∈ Fᵐ⁺ⁿ`. -/
@[simp]
theorem of_mk_mul_of_mk {m n : ℕ} (x : F.ideal m)
    (y : F.ideal n) :
    DirectSum.of F.GradedPiece m x * DirectSum.of F.GradedPiece n y =
      DirectSum.of F.GradedPiece (m + n)
        ((⟨x * y, F.mul_mem x.property y.property⟩ : F.ideal (m + n)) : F.GradedPiece (m + n)) :=
  DirectSum.of_mul_of _ _

/-- The homogeneous class of `x ∈ Fⁿ` in the associated graded ring vanishes exactly when
`x ∈ Fⁿ⁺¹`. -/
@[simp]
theorem of_mk_eq_zero_iff {n : ℕ} (x : F.ideal n) :
    DirectSum.of F.GradedPiece n (x : F.GradedPiece n) = 0 ↔ (x : A) ∈ F.ideal (n + 1) := by
  rw [map_eq_zero_iff _ (DirectSum.of_injective n), gradedPiece_mk_eq_zero_iff]

/-- Homogeneous classes of the same element in equal degrees agree in the associated graded
ring. -/
theorem of_mk_eq_of_mk {i j : ℕ} (h : i = j) (x : A) (hi : x ∈ F.ideal i) (hj : x ∈ F.ideal j) :
    DirectSum.of F.GradedPiece i ((⟨x, hi⟩ : F.ideal i) : F.GradedPiece i) =
      DirectSum.of F.GradedPiece j ((⟨x, hj⟩ : F.ideal j) : F.GradedPiece j) := by
  subst h
  rfl

/-- The unit of the associated graded ring is the degree-zero class of `1`. -/
theorem one_eq_of_gradedZeroMk : (1 : F.AssociatedGraded) =
    DirectSum.of F.GradedPiece 0 (F.gradedZeroMk 1) :=
  (rfl)

end TauCeti.AlgFiltration
