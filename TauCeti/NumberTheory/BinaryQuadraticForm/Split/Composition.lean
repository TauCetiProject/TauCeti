/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Classes
public import TauCeti.NumberTheory.QuadraticOrder.Split.Lattice
public import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Group.TransferInstance

/-!
# Composition of split proper classes

Primitive forms of nonzero square discriminant `s²` have triangular proper representatives
`sxy + cy²`. Their coefficients `c` classify the proper classes by the units of `ZMod s`.
Multiplication of these residues defines composition, and agrees with multiplication of
the explicit modules over the actual congruence product order. The canonical forgetful map
embeds these classes into the existing proper-class quotient of all integral forms.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (proper-equivalence conventions).
-/

public section
noncomputable section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

open QuadraticOrder

/-- The existing proper-orbit quotient of primitive square-discriminant forms. -/
abbrev SplitProperClass (s : ℕ) :=
  MulAction.orbitRel.Quotient SL(2, ℤ) (primitiveForms ((s : ℤ) ^ 2))

/-- Forget the primitive square-discriminant restriction on a proper class. -/
def splitProperClassToProperClass (s : ℕ) :
    SplitProperClass s →
      MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ) :=
  Quotient.map' (fun f : primitiveForms ((s : ℤ) ^ 2) ↦ f.val) fun f g h ↦ by
    exact SubMulAction.mem_orbit_subMul_iff.mp h

/-- Forgetting the restriction preserves the underlying representative. -/
@[simp] theorem splitProperClassToProperClass_mk (s : ℕ)
    (f : primitiveForms ((s : ℤ) ^ 2)) :
    splitProperClassToProperClass s (Quotient.mk _ f) = Quotient.mk'' f.val := by
  rfl

/-- Forgetting the restriction does not identify distinct split proper classes. -/
theorem splitProperClassToProperClass_injective (s : ℕ) :
    Function.Injective (splitProperClassToProperClass s) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro f g h
  rw [splitProperClassToProperClass_mk, splitProperClassToProperClass_mk] at h
  apply Quotient.sound
  exact SubMulAction.mem_orbit_subMul_iff.mpr (Quotient.exact h)

/-- The proper class of the triangular representative with coefficient `c`. -/
def splitProperClassMk (s : ℕ) (c : ℤ) (hc : IsCoprime (s : ℤ) c) : SplitProperClass s :=
  Quotient.mk _ ⟨splitTriangularForm s c,
    (mem_primitiveForms _ _).mpr
      ⟨discrim_splitTriangularForm s c, (isPrimitive_splitTriangularForm s c).mpr hc⟩⟩

/-- The triangular class forgets to the existing raw proper class of its form. -/
@[simp] theorem splitProperClassToProperClass_splitProperClassMk (s : ℕ) (c : ℤ)
    (hc : IsCoprime (s : ℤ) c) :
    splitProperClassToProperClass s (splitProperClassMk s c hc) =
      Quotient.mk'' (splitTriangularForm s c) := by
  rfl

/-- Triangular representatives give the same proper class exactly when their coefficients
have the same residue modulo the nonzero square root. -/
@[simp] theorem splitProperClassMk_eq_iff (s : ℕ) [NeZero s] (c d : ℤ)
    (hc : IsCoprime (s : ℤ) c) (hd : IsCoprime (s : ℤ) d) :
    splitProperClassMk s c hc = splitProperClassMk s d hd ↔ (c : ZMod s) = d := by
  rw [splitProperClassMk, splitProperClassMk, Quotient.eq,
    SubMulAction.orbitRel_of_subMul]
  -- The subaction orbit lemma leaves subtype coercions at both endpoints; their values
  -- are definitionally the original triangular forms.
  change MulAction.orbitRel SL(2, ℤ) (BinaryQuadraticForm ℤ)
    (splitTriangularForm s c) (splitTriangularForm s d) ↔ (c : ZMod s) = d
  rw [← Quotient.eq, properClass_splitTriangularForm_eq_iff _ _ _
    (Nat.cast_ne_zero.mpr (NeZero.ne s)), ZMod.intCast_eq_intCast_iff_dvd_sub, dvd_sub_comm]

/-- A unit residue gives the proper class of its triangular form. -/
def splitUnitToProperClass (s : ℕ) (u : (ZMod s)ˣ) : SplitProperClass s :=
  splitProperClassMk s (u : ZMod s).val (ZMod.val_coe_unit_coprime u).isCoprime.symm

/-- Distinct unit residues give distinct proper classes. -/
theorem splitUnitToProperClass_injective (s : ℕ) [NeZero s] :
    Function.Injective (splitUnitToProperClass s) := by
  intro u v h
  apply Units.ext
  have hcast := (splitProperClassMk_eq_iff s _ _ _ _).mp h
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hcast

/-- Every primitive split proper class has a triangular representative from a unit residue. -/
theorem splitUnitToProperClass_surjective (s : ℕ) [NeZero s] :
    Function.Surjective (splitUnitToProperClass s) := by
  intro q
  induction q using Quotient.inductionOn with
  | h f =>
    have hf := (mem_primitiveForms _ f.val).mp f.property
    obtain ⟨γ, c, hγ, hc⟩ := exists_smul_eq_splitTriangularForm f.val s hf.1 hf.2
    have hrep : (Quotient.mk _ f : SplitProperClass s) = splitProperClassMk s c hc := by
      have htype : γ • f = ⟨splitTriangularForm s c,
          (mem_primitiveForms _ _).mpr
            ⟨discrim_splitTriangularForm s c, (isPrimitive_splitTriangularForm s c).mpr hc⟩⟩ :=
        Subtype.ext hγ
      rw [splitProperClassMk, ← htype]
      exact MulAction.orbitRel.Quotient.quotient_smul_eq.symm
    refine ⟨ZMod.unitOfIsCoprime c hc.symm, ?_⟩
    rw [hrep]
    apply (splitProperClassMk_eq_iff s _ _ _ _).mpr
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.coe_unitOfIsCoprime]

private def splitClassEquivUnits (s : ℕ) [NeZero s] : SplitProperClass s ≃ (ZMod s)ˣ :=
  (Equiv.ofBijective (splitUnitToProperClass s)
    ⟨splitUnitToProperClass_injective s, splitUnitToProperClass_surjective s⟩).symm

/-- Composition of primitive split proper classes is multiplication of their unit residues. -/
@[no_expose] instance instCommGroupSplitProperClass (s : ℕ) [NeZero s] :
    CommGroup (SplitProperClass s) :=
  (splitClassEquivUnits s).commGroup

/-- Split proper classes, with their elementary composition, are the units modulo the
square root. -/
def splitProperClassEquivUnits (s : ℕ) [NeZero s] : SplitProperClass s ≃* (ZMod s)ˣ :=
  (splitClassEquivUnits s).mulEquiv

/-- The inverse classifier takes a unit residue to the proper class of its triangular form. -/
@[simp] theorem splitProperClassEquivUnits_symm_apply (s : ℕ) [NeZero s]
    (u : (ZMod s)ˣ) :
    (splitProperClassEquivUnits s).symm u = splitUnitToProperClass s u := by
  rfl

/-- The class of `sxy + cy²` corresponds to the residue of `c`. -/
@[simp] theorem splitProperClassEquivUnits_mk (s : ℕ) [NeZero s] (c : ℤ)
    (hc : IsCoprime (s : ℤ) c) :
    splitProperClassEquivUnits s (splitProperClassMk s c hc) =
      ZMod.unitOfIsCoprime c hc.symm := by
  have hrep : splitUnitToProperClass s (ZMod.unitOfIsCoprime c hc.symm) =
      splitProperClassMk s c hc := by
    apply (splitProperClassMk_eq_iff s _ _ _ _).mpr
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.coe_unitOfIsCoprime]
  simpa only [splitProperClassEquivUnits_symm_apply, hrep] using
    (splitProperClassEquivUnits s).apply_symm_apply (ZMod.unitOfIsCoprime c hc.symm)

/-- Composition multiplies the two triangular coefficients. -/
@[simp] theorem splitProperClassMk_mul (s : ℕ) [NeZero s] (c d : ℤ)
    (hc : IsCoprime (s : ℤ) c) (hd : IsCoprime (s : ℤ) d) :
    splitProperClassMk s c hc * splitProperClassMk s d hd =
      splitProperClassMk s (c * d) (hc.mul_right hd) := by
  apply (splitProperClassEquivUnits s).injective
  simp only [map_mul, splitProperClassEquivUnits_mk]
  apply Units.ext
  simp only [Units.val_mul, ZMod.coe_unitOfIsCoprime, Int.cast_mul]

/-- The triangular representative with coefficient one is the principal split class. -/
@[simp] theorem splitProperClassMk_one (s : ℕ) [NeZero s] :
    splitProperClassMk s 1 isCoprime_one_right = 1 := by
  apply (splitProperClassEquivUnits s).injective
  rw [splitProperClassEquivUnits_mk, map_one]
  apply Units.ext
  simp

private theorem splitModule_eq_of_cast_eq (s : ℕ) (c d : ℤ)
    (h : (c : ZMod s) = d) : splitModule s c = splitModule s d :=
  (splitModule_eq_iff_dvd_sub s c d).mpr
    ((ZMod.intCast_eq_intCast_iff_dvd_sub d c s).mp h.symm)

/-- A split proper class gives its explicit module over the actual product order;
composition is multiplication of these modules. -/
def splitProperClassModule (s : ℕ) [NeZero s] :
    SplitProperClass s →* Submodule (QuadraticOrder.productSubalgebra s) (ℤ × ℤ) where
  toFun q := splitModule s (splitProperClassEquivUnits s q : ZMod s).val
  map_one' := by
    rw [map_one, Units.val_one]
    calc
      splitModule s (1 : ZMod s).val = splitModule s 1 := by
        apply splitModule_eq_of_cast_eq
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one]
      _ = 1 := splitModule_one s
  map_mul' p q := by
    have hc := (ZMod.val_coe_unit_coprime (splitProperClassEquivUnits s p)).isCoprime.symm
    rw [map_mul, splitModule_mul _ _ _
      (hc.of_isCoprime_of_dvd_right (Int.gcd_dvd_left _ _))]
    apply splitModule_eq_of_cast_eq
    simp only [Int.cast_natCast, Int.cast_mul, ZMod.natCast_zmod_val, Units.val_mul]

/-- The actual module of a triangular representative has its defining congruence coefficient. -/
@[simp] theorem splitProperClassModule_mk (s : ℕ) [NeZero s] (c : ℤ)
    (hc : IsCoprime (s : ℤ) c) :
    splitProperClassModule s (splitProperClassMk s c hc) = splitModule s c := by
  -- Applying the monoid homomorphism unfolds its defining congruence module.
  change splitModule s (splitProperClassEquivUnits s (splitProperClassMk s c hc) : ZMod s).val = _
  rw [splitProperClassEquivUnits_mk]
  apply splitModule_eq_of_cast_eq
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.coe_unitOfIsCoprime]

/-- The explicit congruence modules distinguish every split proper class. -/
theorem splitProperClassModule_injective (s : ℕ) [NeZero s] :
    Function.Injective (splitProperClassModule s) := by
  intro p q h
  apply (splitProperClassEquivUnits s).injective
  apply Units.ext
  -- Equality of the homomorphism values is definitionally equality of their modules.
  change splitModule s (splitProperClassEquivUnits s p : ZMod s).val =
    splitModule s (splitProperClassEquivUnits s q : ZMod s).val at h
  have hdiv := (splitModule_eq_iff_dvd_sub _ _ _).mp h
  have hcast := (ZMod.intCast_eq_intCast_iff_dvd_sub
    ((splitProperClassEquivUnits s q : ZMod s).val : ℤ)
    ((splitProperClassEquivUnits s p : ZMod s).val : ℤ) s).mpr hdiv
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hcast.symm

/-- At discriminant one there is only the principal split proper class. -/
instance instSubsingletonSplitProperClassOne : Subsingleton (SplitProperClass 1) :=
  (splitProperClassEquivUnits 1).injective.subsingleton

end TauCeti.BinaryQuadraticForm
