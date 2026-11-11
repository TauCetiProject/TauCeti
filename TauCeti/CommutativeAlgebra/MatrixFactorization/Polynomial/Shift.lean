/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Polynomial.Cokernel
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Shift

/-!
# Parity shift of polynomial matrix factorizations

For `i ≤ n`, the parity shift of the factorization with maps `X ^ i` and `X ^ (n - i)`
is isomorphic to the factorization indexed by `n - i`. The comparison has components `1`
and `-1`; it removes the signs introduced by parity shift, in every characteristic.
Consequently the shift by one of this object in `HMF(R[X], X ^ n)` is represented by the
complementary factorization, and its reduced cokernel is the cyclic module `A/(x ^ (n - i))`,
where `A = R[X]/(X ^ n)`.

These calculations identify the objects in the parity-shift/syzygy comparison: the alternating
free resolution of `A/(x ^ i)` has the complementary cyclic module as its first syzygy.
They require only a commutative coefficient ring, not a field or a regularity hypothesis.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Polynomial

variable (R : Type u) [CommRing R] {i n : ℕ}

/-- Identity comparison reindexing the complementary rank-one factorization. -/
private def powerXOfLEReindexIso (hi : i ≤ n) :
    rankOne (X ^ (n - i) : R[X]) (X ^ i)
      (by rw [← pow_add, Nat.sub_add_cancel hi]) ≅ powerXOfLE R (Nat.sub_le n i) :=
  ObjectProperty.isoMk (P := isProjective R[X] (X ^ n))
    (CurvedDuplex.isoMk (Iso.refl _) (Iso.refl _)
      -- Normalize the indexed carriers and their instances before simplifying the squares.
      (by dsimp +instances only [powerXOfLE, rankOne, ofCurvedDuplex]; simp)
      (by dsimp +instances only [powerXOfLE, rankOne, ofCurvedDuplex]
          simp [Nat.sub_sub_self hi]))

/-- Parity shift exchanges the exponents `i` and `n - i` of the polynomial factorization. -/
def parityShiftPowerXOfLEIso (hi : i ≤ n) :
    parityShift.obj (powerXOfLE R hi) ≅ powerXOfLE R (Nat.sub_le n i) :=
  parityShiftRankOneIso (X ^ i : R[X]) (X ^ (n - i))
      (by rw [← pow_add, Nat.add_sub_cancel' hi]) ≪≫
    powerXOfLEReindexIso R hi

-- The component proofs use the rank-one comparison lemmas; constructor reduction below
-- computes only the identity comparison that reindexes the complementary exponent.
/-- The even component of the comparison is the identity. -/
@[simp]
theorem parityShiftPowerXOfLEIso_hom_f₀ (hi : i ≤ n) :
    (parityShiftPowerXOfLEIso R hi).hom.hom.f₀ = 𝟙 (FGModuleCat.of R[X] R[X]) := by
  simp [parityShiftPowerXOfLEIso, powerXOfLEReindexIso, powerXOfLE,
    CurvedDuplex.isoMk, CurvedDuplex.homMk]

/-- The odd component of the comparison is minus the identity. -/
@[simp]
theorem parityShiftPowerXOfLEIso_hom_f₁ (hi : i ≤ n) :
    (parityShiftPowerXOfLEIso R hi).hom.hom.f₁ = -𝟙 (FGModuleCat.of R[X] R[X]) := by
  simp [parityShiftPowerXOfLEIso, powerXOfLEReindexIso, powerXOfLE,
    CurvedDuplex.isoMk, CurvedDuplex.homMk]

/-- The inverse comparison is the identity in even parity. -/
@[simp]
theorem parityShiftPowerXOfLEIso_inv_f₀ (hi : i ≤ n) :
    (parityShiftPowerXOfLEIso R hi).inv.hom.f₀ = 𝟙 (FGModuleCat.of R[X] R[X]) := by
  simp [parityShiftPowerXOfLEIso, powerXOfLEReindexIso, powerXOfLE,
    CurvedDuplex.isoMk, CurvedDuplex.homMk]

/-- The inverse comparison is minus the identity in odd parity. -/
@[simp]
theorem parityShiftPowerXOfLEIso_inv_f₁ (hi : i ≤ n) :
    (parityShiftPowerXOfLEIso R hi).inv.hom.f₁ = -𝟙 (FGModuleCat.of R[X] R[X]) := by
  simp [parityShiftPowerXOfLEIso, powerXOfLEReindexIso, powerXOfLE,
    CurvedDuplex.isoMk, CurvedDuplex.homMk]

/-- In the triangulated homotopy category, the shift by one of the polynomial factorization
indexed by `i` is the factorization indexed by `n - i`. -/
def shiftPowerXOfLEIso (hi : i ≤ n) :
    ((nullHomotopic (S := R[X]) (w := X ^ n)).quotientFunctor.obj
      (powerXOfLE R hi))⟦(1 : ℤ)⟧ ≅
        (nullHomotopic (S := R[X]) (w := X ^ n)).quotientFunctor.obj
          (powerXOfLE R (Nat.sub_le n i)) :=
  shiftRankOneIso (X ^ i : R[X]) (X ^ (n - i))
      (by rw [← pow_add, Nat.add_sub_cancel' hi]) ≪≫
    (nullHomotopic (S := R[X]) (w := X ^ n)).quotientFunctor.mapIso
      (powerXOfLEReindexIso R hi)

/-- The forward polynomial shift comparison is induced by the parity-shift comparison. -/
@[simp]
theorem shiftPowerXOfLEIso_hom (hi : i ≤ n) :
    (shiftPowerXOfLEIso R hi).hom =
      (HomotopyCategory.parityShiftCompQuotientFunctorIso R[X] (X ^ n)).inv.app
          (powerXOfLE R hi) ≫
        (nullHomotopic (S := R[X]) (w := X ^ n)).quotientFunctor.map
          (parityShiftPowerXOfLEIso R hi).hom := by
  dsimp only [shiftPowerXOfLEIso, parityShiftPowerXOfLEIso, Iso.trans, Functor.mapIso]
  rw [shiftRankOneIso_hom, Functor.map_comp]
  -- Term-level associativity lets elaboration align the shifted indexed carriers.
  exact Category.assoc _ _ _

/-- The inverse polynomial shift comparison is induced by the inverse parity-shift comparison. -/
@[simp]
theorem shiftPowerXOfLEIso_inv (hi : i ≤ n) :
    (shiftPowerXOfLEIso R hi).inv =
      (nullHomotopic (S := R[X]) (w := X ^ n)).quotientFunctor.map
          (parityShiftPowerXOfLEIso R hi).inv ≫
        (HomotopyCategory.parityShiftCompQuotientFunctorIso R[X] (X ^ n)).hom.app
          (powerXOfLE R hi) := by
  dsimp only [shiftPowerXOfLEIso, parityShiftPowerXOfLEIso, Iso.trans, Functor.mapIso]
  rw [shiftRankOneIso_inv, Functor.map_comp]
  -- Term-level associativity lets elaboration align the shifted indexed carriers.
  exact (Category.assoc _ _ _).symm

/-- Reduction modulo `X ^ n` of the shifted factorization has cyclic right-module cokernel
`A/(x ^ (n - i))`, viewed as a left module through the commutativity isomorphism. -/
def parityShiftPowerXOfLECokernelIso (hi : i ≤ n) :
    ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X])) ⋙ cokernelFunctor).obj
      (parityShift.obj (powerXOfLE R hi))).obj ≅
        (ModuleCat.restrictScalars
          (RingEquiv.toOpposite (AdjoinRoot (X ^ n : R[X]))).toRingHom).obj
          (FGModuleCat.cyclicModule (AdjoinRoot.root (X ^ n : R[X]) ^ (n - i))).obj :=
  (forget₂ (FGModuleCat (AdjoinRoot (X ^ n : R[X])))
      (ModuleCat (AdjoinRoot (X ^ n : R[X])))).mapIso
    ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X])) ⋙ cokernelFunctor).mapIso
      (parityShiftPowerXOfLEIso R hi)) ≪≫
    powerXOfLECokernelIso R (Nat.sub_le n i)

/-- On an odd-component representative, the shifted cyclic-cokernel comparison sends the
scalar-extension counit image to its negative class. The minus sign comes from the odd
component of `parityShiftPowerXOfLEIso`. -/
theorem cokernelπ_comp_parityShiftPowerXOfLECokernelIso_hom_apply (hi : i ≤ n)
    (a : ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj
      (parityShift.obj (powerXOfLE R hi))).obj.X₁.obj) :
    (parityShiftPowerXOfLECokernelIso R hi).hom
      (cokernelπ ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj
        (parityShift.obj (powerXOfLE R hi))) a) =
      -Submodule.Quotient.mk (MulOpposite.op (Functor.OplaxMonoidal.η
        (ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X]))) a)) := by
  have hf :
      ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).map
        (parityShiftPowerXOfLEIso R hi).hom).hom.f₁.hom = -𝟙 _ := by
    rw [baseChangeFunctor_map_f₁, parityShiftPowerXOfLEIso_hom_f₁]
    -- Explicit composition lets elaboration align the two indexed module carriers.
    exact (Functor.map_neg
      (forget₂ (FGModuleCat R[X]) (ModuleCat R[X]) ⋙
        ModuleCat.extendScalars (AdjoinRoot.mk (X ^ n : R[X])))).trans
      (congrArg Neg.neg (CategoryTheory.Functor.map_id _ _))
  have ha :
      ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).map
        (parityShiftPowerXOfLEIso R hi).hom).hom.f₁.hom.hom a = -a :=
    congrArg (fun f ↦ f.hom a) hf
  have hnat := cokernelπ_naturality_apply
    ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).map
      (parityShiftPowerXOfLEIso R hi).hom) a
  let e := powerXOfLECokernelIso R (Nat.sub_le n i)
  let π := cokernelπ ((baseChangeFunctor (AdjoinRoot.mk (X ^ n : R[X]))).obj
    (powerXOfLE R (Nat.sub_le n i)))
  refine (congrArg e.hom hnat).trans ?_
  rw [ha]
  -- Instantiate linear-map formulas explicitly: the shifted and complementary odd modules
  -- agree definitionally, but their indexed carriers prevent generic `map_neg` rewrites.
  calc
    _ = e.hom (-(π a)) := congrArg e.hom (π.hom.map_neg a)
    _ = -(e.hom (π a)) := e.hom.hom.map_neg _
    _ = _ := congrArg Neg.neg
      (cokernelπ_comp_powerXOfLECokernelIso_hom_apply R (Nat.sub_le n i) a)

end TauCeti.MatrixFactorization
