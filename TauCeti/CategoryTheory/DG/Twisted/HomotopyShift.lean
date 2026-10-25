/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Twisted.Shift
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# The shift on the homotopy category of twisted objects

Let `C` be a differential graded category and let `H⁰` be the homotopy category of the twisted
objects `(⊕ᵢ Xᵢ[rᵢ], δ)` of the additive closure of the shift closure of `C`.  The DG shift
functors `TauCeti.DGTwistedObject.shiftFunctor n`, which send `(⊕ᵢ Xᵢ[rᵢ], δ)` to
`(⊕ᵢ Xᵢ[rᵢ + n], δ)`, induce functors on `H⁰`.  This file makes them a shift `HasShift H⁰ ℤ` in
the sense of Mathlib, the structure that Mathlib's triangles `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` and
pretriangulated categories are formulated with.

The shifts do not compose strictly: `P⟦a⟧⟦b⟧` has summands `Xᵢ[rᵢ + a + b]` and `P⟦a + b⟧` has
summands `Xᵢ[rᵢ + (a + b)]`.  They are identified by closed degree-zero isomorphisms built from
the comparison morphisms `σ : P ⟶ P⟦n⟧` of degree `-n` and `σ⁻¹ : P⟦n⟧ ⟶ P` of degree `n`
(`TauCeti.DGTwistedObject.toShift` and `TauCeti.DGTwistedObject.fromShift`):
`TauCeti.DGTwistedObject.shiftAddHom P a b` is the composite
`P⟦a + b⟧ ⟶ P ⟶ P⟦b⟧ ⟶ P⟦a⟧⟦b⟧` whose last map is the shift by `b` of `P ⟶ P⟦a⟧`, and
`P⟦0⟧ ⟶ P` is the comparison morphism itself.  Composing directly through `P ⟶ P⟦a⟧ ⟶ P⟦a⟧⟦b⟧`
instead gives `(-1)^(a * b)` times `shiftAddHom P a b`
(`TauCeti.DGTwistedObject.shiftAddHom_eq_units_smul`), by the Koszul-sign naturality of the
comparison morphisms.  This second description makes the associativity and unit coherences of
the shift a cancellation of comparison morphisms, the signs `(-1)^((a + b) * c + a * b)` and
`(-1)^(a * (b + c) + b * c)` agreeing.

## Main definitions

* `TauCeti.DGTwistedObject.shiftAddHom` and `TauCeti.DGTwistedObject.shiftAddInv`: the mutually
  inverse closed degree-zero morphisms `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` and `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧`.
* `TauCeti.DGTwistedObject.homotopyCategoryShiftMkCore`: the shift functors on `H⁰` and their
  compatibility isomorphisms.
* `TauCeti.DGTwistedObject.hasShiftHomotopyCategory`: the shift `HasShift H⁰ ℤ`.

## Main results

* `TauCeti.DGTwistedObject.dgComp_shiftAddHom_shiftAddInv` and
  `TauCeti.DGTwistedObject.dgComp_shiftAddInv_shiftAddHom`: the two comparisons are inverse.
* `TauCeti.DGTwistedObject.dgMap_dgComp_shiftAddHom`: `shiftAddHom` is natural.
* `TauCeti.DGTwistedObject.shiftFunctor_map_homOf`,
  `TauCeti.DGTwistedObject.shiftFunctorZero_hom_app_of` and
  `TauCeti.DGTwistedObject.shiftFunctorAdd_hom_app_of`: the shift of `H⁰` and its isomorphisms
  are induced by the DG shift and the comparison morphisms.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

namespace DGTwistedObject

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Degree bookkeeping

The coherences below compare composites of comparison morphisms whose degrees are integer
expressions such as `-a + -b` and `a + -(a + b)`, which agree only propositionally.  The following
rewriting rules bring such composites to a normal form: a degree transport `castDeg` of a
right-associated composite whose intermediate degrees are the sums of the degrees of the factors.
Two composites of the same factors then agree up to the outer degree transport.  The rules are
applied with `simp -proj`, which keeps the shifted objects `(shiftFunctor R n).obj P` folded so that
the comparison lemmas about `TauCeti.DGTwistedObject.toShift` and
`TauCeti.DGTwistedObject.fromShift` keep matching. -/

section calculus

variable {P Q W X Y Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}

private theorem dgComp_eq_castDeg {p q n : ℤ} (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (h : p + q = n) : dgComp R f g h = castDeg R h (dgComp R f g rfl) := by
  subst h
  rw [castDeg_self]

private theorem dgComp_assoc' {p q r pq n : ℤ} (f : DGHom R p W X) (g : DGHom R q X Y)
    (k : DGHom R r Y Z) (hpq : p + q = pq) (h : pq + r = n) :
    dgComp R (dgComp R f g hpq) k h =
      castDeg R (by omega) (dgComp R f (dgComp R g k rfl) rfl) := by
  subst hpq h
  rw [dgComp_assoc R f g k rfl rfl rfl, dgComp_eq_castDeg (n := p + q + r)]

private theorem castDeg_dgComp' {p p' q n : ℤ} (hp : p = p') (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p' + q = n) :
    dgComp R (castDeg R hp f) g h = castDeg R (by omega) (dgComp R f g rfl) :=
  castDeg_dgComp R hp _ f g h

private theorem dgComp_castDeg' {p q q' n : ℤ} (hq : q = q') (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q' = n) :
    dgComp R f (castDeg R hq g) h = castDeg R (by omega) (dgComp R f g rfl) :=
  dgComp_castDeg R hq _ f g h

private theorem dgId_dgComp' {q n : ℤ} (g : DGHom R q X Y) (h : 0 + q = n) :
    dgComp R (dgId R X) g h = castDeg R (by omega) g := by
  have := castDeg_dgId_dgComp R (rfl : (0 : ℤ) = 0) g h
  rwa [castDeg_self] at this

private theorem dgComp_fromShift_toShift' (n : ℤ) {m : ℤ} (h : n + -n = m) :
    dgComp R (fromShift P n) (toShift P n) h = castDeg R (by omega) (dgId R _) := by
  obtain rfl : m = 0 := by omega
  rw [dgComp_fromShift_toShift, castDeg_self]

private theorem dgComp_toShift_fromShift_assoc' (n : ℤ) {q m m' : ℤ} (x : DGHom R q P Z)
    (h : n + q = m) (h' : -n + m = m') :
    dgComp R (toShift P n) (dgComp R (fromShift P n) x h) h' = castDeg R (by omega) x := by
  subst h h'
  rw [← dgComp_assoc R _ _ x (neg_add_cancel n) rfl (by omega), dgComp_toShift_fromShift,
    dgId_dgComp']

private theorem dgComp_fromShift_toShift_assoc' (n : ℤ) {q m m' : ℤ}
    (x : DGHom R q ((shiftFunctor R n).obj P) Z) (h : -n + q = m) (h' : n + m = m') :
    dgComp R (fromShift P n) (dgComp R (toShift P n) x h) h' = castDeg R (by omega) x := by
  subst h h'
  rw [← dgComp_assoc R _ _ x (add_neg_cancel n) rfl (by omega), dgComp_fromShift_toShift,
    dgId_dgComp']

private theorem toShift_dgComp_dgMap (n : ℤ) (f : DGHom R 0 P Q) {m : ℤ} (h : -n + 0 = m) :
    dgComp R (toShift P n) ((shiftFunctor R n).dgMap 0 f) h =
      castDeg R (by omega) (dgComp R f (toShift Q n) rfl) := by
  subst h
  rw [dgComp_toShift n f rfl, mul_zero, Int.negOnePow_zero, one_smul,
    dgComp_eq_castDeg (n := 0 + -n), castDeg_castDeg, castDeg_self]

private theorem toShift_dgComp_dgMap_assoc (n : ℤ) (f : DGHom R 0 P Q) {q m m' : ℤ}
    (x : DGHom R q ((shiftFunctor R n).obj Q) Z) (h : 0 + q = m) (h' : -n + m = m') :
    dgComp R (toShift P n) (dgComp R ((shiftFunctor R n).dgMap 0 f) x h) h' =
      castDeg R (by omega) (dgComp R f (dgComp R (toShift Q n) x rfl) rfl) := by
  subst h h'
  rw [← dgComp_assoc R _ _ x rfl rfl (by omega), toShift_dgComp_dgMap, castDeg_dgComp',
    dgComp_assoc', castDeg_castDeg]

private theorem dgMap_dgComp_fromShift_assoc (n : ℤ) (f : DGHom R 0 P Q) {q m m' : ℤ}
    (x : DGHom R q Q Z) (h : n + q = m) (h' : 0 + m = m') :
    dgComp R ((shiftFunctor R n).dgMap 0 f) (dgComp R (fromShift Q n) x h) h' =
      castDeg R (by omega) (dgComp R (fromShift P n) (dgComp R f x rfl) rfl) := by
  subst h h'
  rw [← dgComp_assoc R _ _ x rfl rfl (by omega), dgComp_fromShift n f rfl, mul_zero,
    Int.negOnePow_zero, one_smul, dgComp_assoc']

end calculus

/-! ### The comparison of iterated shifts -/

section comparison

variable (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))

/-- The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧`, a closed degree-zero isomorphism: the comparison
morphisms `P⟦a + b⟧ ⟶ P ⟶ P⟦b⟧` followed by the shift by `b` of the comparison morphism
`P ⟶ P⟦a⟧`. -/
noncomputable def shiftAddHom (a b : ℤ) :
    DGHom R 0 ((shiftFunctor R (a + b)).obj P)
      ((shiftFunctor R b).obj ((shiftFunctor R a).obj P)) :=
  dgComp R (fromShift P (a + b))
    (dgComp R (toShift P b) ((shiftFunctor R b).dgMap (-a) (toShift P a)) (add_comm _ _))
    (by omega)

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧`, inverse to `TauCeti.DGTwistedObject.shiftAddHom`: the
shift by `b` of the comparison morphism `P⟦a⟧ ⟶ P` followed by the comparison morphisms
`P⟦b⟧ ⟶ P ⟶ P⟦a + b⟧`. -/
noncomputable def shiftAddInv (a b : ℤ) :
    DGHom R 0 ((shiftFunctor R b).obj ((shiftFunctor R a).obj P))
      ((shiftFunctor R (a + b)).obj P) :=
  dgComp R ((shiftFunctor R b).dgMap a (fromShift P a))
    (dgComp R (fromShift P b) (toShift P (a + b)) rfl) (by omega)

/-- The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` is `P⟦a + b⟧ ⟶ P ⟶ P⟦b⟧` followed by the shift of
`P ⟶ P⟦a⟧`. -/
theorem shiftAddHom_def (a b : ℤ) :
    shiftAddHom P a b = dgComp R (fromShift P (a + b))
      (dgComp R (toShift P b) ((shiftFunctor R b).dgMap (-a) (toShift P a)) (add_comm _ _))
      (by omega) :=
  (rfl)

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` is the shift of `P⟦a⟧ ⟶ P` followed by
`P⟦b⟧ ⟶ P ⟶ P⟦a + b⟧`. -/
theorem shiftAddInv_def (a b : ℤ) :
    shiftAddInv P a b = dgComp R ((shiftFunctor R b).dgMap a (fromShift P a))
      (dgComp R (fromShift P b) (toShift P (a + b)) rfl) (by omega) :=
  (rfl)

/-- Through `P ⟶ P⟦a⟧ ⟶ P⟦a⟧⟦b⟧` instead, the comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` acquires the
Koszul sign `(-1)^(a * b)`. -/
theorem shiftAddHom_eq_units_smul (a b : ℤ) :
    shiftAddHom P a b = (a * b).negOnePow • dgComp R (fromShift P (a + b))
      (dgComp R (toShift P a) (toShift ((shiftFunctor R a).obj P) b) rfl) (by omega) := by
  rw [shiftAddHom_def, dgComp_toShift b (toShift P a) rfl, dgComp_units_smul, smul_smul, mul_neg,
    Int.negOnePow_neg, mul_comm b a, Int.units_mul_self, one_smul]

/-- Through `P⟦a⟧⟦b⟧ ⟶ P⟦a⟧ ⟶ P` instead, the comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` acquires the
Koszul sign `(-1)^(a * b)`. -/
theorem shiftAddInv_eq_units_smul (a b : ℤ) :
    shiftAddInv P a b = (a * b).negOnePow • dgComp R (fromShift ((shiftFunctor R a).obj P) b)
      (dgComp R (fromShift P a) (toShift P (a + b)) rfl) (by omega) := by
  rw [shiftAddInv_def, ← dgComp_assoc R _ _ _ rfl rfl (by omega), dgComp_fromShift b _ rfl,
    units_smul_dgComp, dgComp_assoc R _ _ _ _ rfl (by omega), mul_comm b a]

/-- The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` is closed. -/
@[simp↓]
theorem dgDifferential_shiftAddHom (a b : ℤ) : dgDifferential R 0 (shiftAddHom P a b) = 0 := by
  rw [shiftAddHom_eq_units_smul, map_zsmul_unit, dgDifferential_dgComp, dgDifferential_dgComp,
    dgDifferential_fromShift, dgDifferential_toShift, dgDifferential_toShift, zero_dgComp,
    zero_dgComp, dgComp_zero, smul_zero, add_zero, dgComp_zero, smul_zero, add_zero, smul_zero]

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` is closed. -/
@[simp↓]
theorem dgDifferential_shiftAddInv (a b : ℤ) : dgDifferential R 0 (shiftAddInv P a b) = 0 := by
  rw [shiftAddInv_eq_units_smul, map_zsmul_unit, dgDifferential_dgComp, dgDifferential_dgComp,
    dgDifferential_fromShift, dgDifferential_fromShift, dgDifferential_toShift, zero_dgComp,
    zero_dgComp, dgComp_zero, smul_zero, add_zero, dgComp_zero, smul_zero, add_zero, smul_zero]

/-- The comparisons `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftAddHom_shiftAddInv (a b : ℤ) :
    dgComp R (shiftAddHom P a b) (shiftAddInv P a b) (add_zero 0) = dgId R _ := by
  simp -proj only [shiftAddHom_eq_units_smul, shiftAddInv_eq_units_smul, units_smul_dgComp,
    dgComp_units_smul, smul_smul, Int.units_mul_self, one_smul, dgComp_assoc',
    dgComp_toShift_fromShift_assoc', dgComp_castDeg', castDeg_castDeg,
    dgComp_fromShift_toShift', castDeg_self]

/-- The comparisons `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftAddInv_shiftAddHom (a b : ℤ) :
    dgComp R (shiftAddInv P a b) (shiftAddHom P a b) (add_zero 0) = dgId R _ := by
  simp -proj only [shiftAddHom_eq_units_smul, shiftAddInv_eq_units_smul, units_smul_dgComp,
    dgComp_units_smul, smul_smul, Int.units_mul_self, one_smul, dgComp_assoc',
    dgComp_toShift_fromShift_assoc', dgComp_fromShift_toShift_assoc', dgComp_castDeg',
    castDeg_castDeg, dgComp_fromShift_toShift', castDeg_self]

variable {P} in
/-- **The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` is natural** in degree-zero morphisms `f : P ⟶ Q`. -/
theorem dgMap_dgComp_shiftAddHom {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (a b : ℤ) (f : DGHom R 0 P Q) :
    dgComp R ((shiftFunctor R (a + b)).dgMap 0 f) (shiftAddHom Q a b) (add_zero 0) =
      dgComp R (shiftAddHom P a b)
        ((shiftFunctor R b).dgMap 0 ((shiftFunctor R a).dgMap 0 f)) (add_zero 0) := by
  simp -proj only [shiftAddHom_eq_units_smul, units_smul_dgComp, dgComp_units_smul,
    dgComp_assoc', dgMap_dgComp_fromShift_assoc, castDeg_castDeg, dgComp_castDeg',
    toShift_dgComp_dgMap_assoc, toShift_dgComp_dgMap]

/-- The associativity coherence of the comparisons, at the level of DG morphisms. -/
private theorem shiftAddHom_assoc (a b c : ℤ) :
    dgComp R (shiftAddHom P (a + b) c) ((shiftFunctor R c).dgMap 0 (shiftAddHom P a b))
        (add_zero 0) =
      dgComp R (dgComp R (fromShift P (a + b + c)) (toShift P (a + (b + c))) (by omega))
        (dgComp R (shiftAddHom P a (b + c)) (shiftAddHom ((shiftFunctor R a).obj P) b c)
          (add_zero 0)) (add_zero 0) := by
  rw [shiftAddHom_eq_units_smul P (a + b) c]
  simp -proj only [units_smul_dgComp, dgComp_assoc', toShift_dgComp_dgMap, dgComp_castDeg',
    castDeg_castDeg]
  simp -proj only [shiftAddHom_eq_units_smul, units_smul_dgComp, dgComp_units_smul, smul_smul,
    dgComp_assoc', dgComp_toShift_fromShift_assoc', dgComp_castDeg', castDeg_castDeg,
    map_zsmul_unit]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 1
  ring

/-- The left unit coherence of the comparisons, at the level of DG morphisms. -/
private theorem shiftAddHom_zero_add (n : ℤ) :
    shiftAddHom P 0 n =
      dgComp R (dgComp R (fromShift P (0 + n)) (toShift P n) (by omega))
        ((shiftFunctor R n).dgMap 0 (toShift P 0)) (add_zero 0) := by
  simp -proj only [shiftAddHom_eq_units_smul, dgComp_assoc', toShift_dgComp_dgMap,
    dgComp_castDeg', castDeg_castDeg, zero_mul, Int.negOnePow_zero, one_smul]
  exact dgComp_eq_castDeg _ _ _

/-- The right unit coherence of the comparisons, at the level of DG morphisms. -/
private theorem shiftAddHom_add_zero (n : ℤ) :
    shiftAddHom P n 0 =
      dgComp R (dgComp R (fromShift P (n + 0)) (toShift P n) (by omega))
        (toShift ((shiftFunctor R n).obj P) 0) (add_zero 0) := by
  simp -proj only [shiftAddHom_eq_units_smul, dgComp_assoc', mul_zero, Int.negOnePow_zero,
    one_smul]
  exact dgComp_eq_castDeg _ _ _

end comparison

/-! ### The shift on the homotopy category -/

section homotopy

open DGHomotopyCategory

variable (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))

private theorem dgDifferential_dgComp_fromShift_toShift (a b : ℤ) (h : a + -b = 0) :
    dgDifferential R 0 (dgComp R (fromShift P a) (toShift P b) h) = 0 := by
  rw [dgDifferential_dgComp, dgDifferential_fromShift, dgDifferential_toShift, zero_dgComp,
    dgComp_zero, smul_zero, add_zero]

private theorem homOf_fromShift_comp_homOf_toShift_zero :
    homOf R (fromShift P 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0)) ≫
        homOf R (toShift P 0) ((mem_dgCycles R).mpr (dgDifferential_toShift P 0)) =
      𝟙 _ := by
  rw [homOf_comp, ← homOf_dgId]
  congr 1
  exact (dgCompZero_def R _ _).trans (dgComp_fromShift_toShift P 0)

private theorem homOf_toShift_comp_homOf_fromShift_zero :
    homOf R (toShift P 0) ((mem_dgCycles R).mpr (dgDifferential_toShift P 0)) ≫
        homOf R (fromShift P 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0)) =
      𝟙 _ := by
  rw [homOf_comp, ← homOf_dgId]
  congr 1
  exact (dgCompZero_def R _ _).trans (dgComp_toShift_fromShift P 0)

private theorem homOf_shiftAddHom_comp_homOf_shiftAddInv (a b : ℤ) :
    homOf R (shiftAddHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b)) ≫
        homOf R (shiftAddInv P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv P a b)) =
      𝟙 _ := by
  rw [homOf_comp, ← homOf_dgId]
  congr 1
  exact (dgCompZero_def R _ _).trans (dgComp_shiftAddHom_shiftAddInv P a b)

private theorem homOf_shiftAddInv_comp_homOf_shiftAddHom (a b : ℤ) :
    homOf R (shiftAddInv P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv P a b)) ≫
        homOf R (shiftAddHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b)) =
      𝟙 _ := by
  rw [homOf_comp, ← homOf_dgId]
  congr 1
  exact (dgCompZero_def R _ _).trans (dgComp_shiftAddInv_shiftAddHom P a b)

variable {P} in
/-- An identity `P⟦a⟧ = P⟦b⟧` in the homotopy category, for `a = b`, is represented by the
comparison morphisms `P⟦a⟧ ⟶ P ⟶ P⟦b⟧`. -/
private theorem eqToHom_mapDGHomotopyCategory_shiftFunctor {a b : ℤ} (h : a = b)
    (h' : (shiftFunctor R a).mapDGHomotopyCategory.obj (DGHomotopyCategory.of R P) =
      (shiftFunctor R b).mapDGHomotopyCategory.obj (DGHomotopyCategory.of R P)) :
    eqToHom h' = homOf R (dgComp R (fromShift P a) (toShift P b) (by omega))
      ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P a b _)) := by
  subst h
  rw [eqToHom_refl]
  refine (homOf_dgId R _).symm.trans ?_
  congr 1
  exact (dgComp_fromShift_toShift P a).symm

variable {P} in
private theorem homOf_fromShift_zero_naturality
    {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (f : DGHom R 0 P Q) (hf : f ∈ dgCycles R P Q) :
    homOf R ((shiftFunctor R 0).dgMap 0 f) ((shiftFunctor R 0).dgMap_mem_dgCycles hf) ≫
        homOf R (fromShift Q 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift Q 0)) =
      homOf R (fromShift P 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0)) ≫
        homOf R f hf := by
  rw [homOf_comp, homOf_comp]
  congr 1
  rw [dgCompZero_def, dgCompZero_def, dgComp_fromShift 0 f, mul_zero, Int.negOnePow_zero,
    one_smul]

variable {P} in
private theorem homOf_shiftAddHom_naturality
    {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (a b : ℤ) (f : DGHom R 0 P Q) (hf : f ∈ dgCycles R P Q) :
    homOf R ((shiftFunctor R (a + b)).dgMap 0 f)
          ((shiftFunctor R (a + b)).dgMap_mem_dgCycles hf) ≫
        homOf R (shiftAddHom Q a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom Q a b)) =
      homOf R (shiftAddHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b)) ≫
        homOf R ((shiftFunctor R b).dgMap 0 ((shiftFunctor R a).dgMap 0 f))
          ((shiftFunctor R b).dgMap_mem_dgCycles ((shiftFunctor R a).dgMap_mem_dgCycles hf)) := by
  rw [homOf_comp, homOf_comp]
  congr 1
  rw [dgCompZero_def, dgCompZero_def]
  exact dgMap_dgComp_shiftAddHom a b f

private theorem homOf_shiftAddHom_assoc (a b c : ℤ) :
    homOf R (shiftAddHom P (a + b) c)
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P (a + b) c)) ≫
        homOf R ((shiftFunctor R c).dgMap 0 (shiftAddHom P a b))
          ((shiftFunctor R c).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b))) =
      homOf R (dgComp R (fromShift P (a + b + c)) (toShift P (a + (b + c))) (by omega))
          ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
        homOf R (shiftAddHom P a (b + c))
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a (b + c))) ≫
          homOf R (shiftAddHom ((shiftFunctor R a).obj P) b c)
            ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom _ b c)) := by
  rw [homOf_comp, homOf_comp, homOf_comp]
  congr 1
  rw [dgCompZero_def, dgCompZero_def, dgCompZero_def]
  exact shiftAddHom_assoc P a b c

private theorem homOf_shiftAddHom_zero_add (n : ℤ) :
    homOf R (shiftAddHom P 0 n) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P 0 n)) =
      homOf R (dgComp R (fromShift P (0 + n)) (toShift P n) (by omega))
          ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
        homOf R ((shiftFunctor R n).dgMap 0 (toShift P 0))
          ((shiftFunctor R n).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_toShift P 0))) := by
  rw [homOf_comp]
  congr 1
  rw [dgCompZero_def]
  exact shiftAddHom_zero_add P n

private theorem homOf_shiftAddHom_add_zero (n : ℤ) :
    homOf R (shiftAddHom P n 0) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P n 0)) =
      homOf R (dgComp R (fromShift P (n + 0)) (toShift P n) (by omega))
          ((mem_dgCycles R).mpr (dgDifferential_dgComp_fromShift_toShift P _ _ _)) ≫
        homOf R (toShift ((shiftFunctor R n).obj P) 0)
          ((mem_dgCycles R).mpr (dgDifferential_toShift _ 0)) := by
  rw [homOf_comp]
  congr 1
  rw [dgCompZero_def]
  exact shiftAddHom_add_zero P n

variable (R C) in
/-- The shift of the homotopy category of twisted objects: the shift by `n` is induced by the DG
shift functor `TauCeti.DGTwistedObject.shiftFunctor n`, and the isomorphisms `P⟦0⟧ ≅ P` and
`P⟦a + b⟧ ≅ P⟦a⟧⟦b⟧` are the classes of the comparison morphism `P⟦0⟧ ⟶ P` and of
`TauCeti.DGTwistedObject.shiftAddHom`. -/
@[expose]
noncomputable def homotopyCategoryShiftMkCore :
    ShiftMkCore
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ where
  F n := (shiftFunctor R n).mapDGHomotopyCategory
  -- The private inverse laws are only accessible from tactic blocks in this exposed definition.
  zero := NatIso.ofComponents (fun X ↦
      { hom := homOf R (fromShift (underlying R X) 0)
          ((mem_dgCycles R).mpr (dgDifferential_fromShift _ 0))
        inv := homOf R (toShift (underlying R X) 0)
          ((mem_dgCycles R).mpr (dgDifferential_toShift _ 0))
        hom_inv_id := by exact homOf_fromShift_comp_homOf_toShift_zero _
        inv_hom_id := by exact homOf_toShift_comp_homOf_fromShift_zero _ }) fun {X Y} f ↦ by
    obtain ⟨P, rfl⟩ : ∃ P, of R P = X := ⟨_, of_underlying R X⟩
    obtain ⟨Q, rfl⟩ : ∃ Q, of R Q = Y := ⟨_, of_underlying R Y⟩
    obtain ⟨f, hf, rfl⟩ := exists_homOf_eq R f
    exact (congrArg (· ≫ _) (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf)).trans
      (homOf_fromShift_zero_naturality f hf)
  add a b := NatIso.ofComponents (fun X ↦
      { hom := homOf R (shiftAddHom (underlying R X) a b)
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom _ a b))
        inv := homOf R (shiftAddInv (underlying R X) a b)
          ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv _ a b))
        hom_inv_id := by exact homOf_shiftAddHom_comp_homOf_shiftAddInv _ a b
        inv_hom_id := by exact homOf_shiftAddInv_comp_homOf_shiftAddHom _ a b }) fun {X Y} f ↦ by
    obtain ⟨P, rfl⟩ : ∃ P, of R P = X := ⟨_, of_underlying R X⟩
    obtain ⟨Q, rfl⟩ : ∃ Q, of R Q = Y := ⟨_, of_underlying R Y⟩
    obtain ⟨f, hf, rfl⟩ := exists_homOf_eq R f
    refine (congrArg (· ≫ _) (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf)).trans
      ((homOf_shiftAddHom_naturality a b f hf).trans ?_)
    exact congrArg (_ ≫ ·) ((EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ _ _).symm.trans
      (congrArg _ (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf).symm))
  assoc_hom_app m₁ m₂ m₃ X := by
    obtain ⟨P, rfl⟩ : ∃ P, of R P = X := ⟨_, of_underlying R X⟩
    refine (congrArg (_ ≫ ·) (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ _ _)).trans
      ((homOf_shiftAddHom_assoc P m₁ m₂ m₃).trans ?_)
    exact congrArg (· ≫ _)
      (eqToHom_mapDGHomotopyCategory_shiftFunctor (add_assoc m₁ m₂ m₃) _).symm
  zero_add_hom_app n X := by
    obtain ⟨P, rfl⟩ : ∃ P, of R P = X := ⟨_, of_underlying R X⟩
    refine (homOf_shiftAddHom_zero_add P n).trans ?_
    exact congrArg₂ (· ≫ ·)
      (eqToHom_mapDGHomotopyCategory_shiftFunctor (zero_add n) _).symm
      (EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ _ _).symm
  add_zero_hom_app n X := by
    obtain ⟨P, rfl⟩ : ∃ P, of R P = X := ⟨_, of_underlying R X⟩
    exact (homOf_shiftAddHom_add_zero P n).trans (congrArg (· ≫ _)
      (eqToHom_mapDGHomotopyCategory_shiftFunctor (add_zero n) _).symm)

/-- **The homotopy category of twisted objects has a shift by `ℤ`**, induced by the DG shift
functors `TauCeti.DGTwistedObject.shiftFunctor`. -/
noncomputable instance hasShiftHomotopyCategory :
    HasShift (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ :=
  hasShiftMk _ _ (homotopyCategoryShiftMkCore R C)

variable (R C) in
/-- The shift by `n` of the homotopy category of twisted objects is the functor induced by the DG
shift functor `TauCeti.DGTwistedObject.shiftFunctor n`. -/
theorem shiftFunctor_eq_mapDGHomotopyCategory (n : ℤ) :
    CategoryTheory.shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n =
      (shiftFunctor R n).mapDGHomotopyCategory :=
  (rfl)

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))
        n).Additive :=
  inferInstanceAs (shiftFunctor R n).mapDGHomotopyCategory.Additive

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).Linear
        R :=
  inferInstanceAs ((shiftFunctor R n).mapDGHomotopyCategory.Linear R)

/-- The shift of a twisted object in the homotopy category is its DG shift. -/
@[simp]
theorem shiftFunctor_obj_of (n : ℤ) :
    (CategoryTheory.shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).obj
        (DGHomotopyCategory.of R P) =
      DGHomotopyCategory.of R ((shiftFunctor R n).obj P) :=
  (rfl)

variable {P} in
/-- The shift of the class of a closed degree-zero morphism is the class of its DG shift. -/
@[simp]
theorem shiftFunctor_map_homOf {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (n : ℤ) (f : DGHom R 0 P Q) (hf : f ∈ dgCycles R P Q) :
    (CategoryTheory.shiftFunctor
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) n).map
        (homOf R f hf) =
      homOf R ((shiftFunctor R n).dgMap 0 f) ((shiftFunctor R n).dgMap_mem_dgCycles hf) :=
  EnrichedFunctor.mapDGHomotopyCategory_map_homOf _ f hf

/-- The isomorphism `P⟦0⟧ ≅ P` of the shift is the class of the comparison morphism. -/
@[simp]
theorem shiftFunctorZero_hom_app_of :
    (shiftFunctorZero
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ).hom.app
        (DGHomotopyCategory.of R P) =
      homOf R (fromShift P 0) ((mem_dgCycles R).mpr (dgDifferential_fromShift P 0)) := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The inverse isomorphism `P ≅ P⟦0⟧` of the shift is the class of the comparison morphism. -/
@[simp]
theorem shiftFunctorZero_inv_app_of :
    (shiftFunctorZero
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) ℤ).inv.app
        (DGHomotopyCategory.of R P) =
      homOf R (toShift P 0) ((mem_dgCycles R).mpr (dgDifferential_toShift P 0)) := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The isomorphism `P⟦a + b⟧ ≅ P⟦a⟧⟦b⟧` of the shift is the class of
`TauCeti.DGTwistedObject.shiftAddHom`. -/
@[simp]
theorem shiftFunctorAdd_hom_app_of (a b : ℤ) :
    (shiftFunctorAdd
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a
          b).hom.app (DGHomotopyCategory.of R P) =
      homOf R (shiftAddHom P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddHom P a b)) := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

/-- The isomorphism `P⟦a⟧⟦b⟧ ≅ P⟦a + b⟧` of the shift is the class of
`TauCeti.DGTwistedObject.shiftAddInv`. -/
@[simp]
theorem shiftFunctorAdd_inv_app_of (a b : ℤ) :
    (shiftFunctorAdd
        (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) a
          b).inv.app (DGHomotopyCategory.of R P) =
      homOf R (shiftAddInv P a b) ((mem_dgCycles R).mpr (dgDifferential_shiftAddInv P a b)) := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

end homotopy

end DGTwistedObject

end TauCeti
