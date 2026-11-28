/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.Algebra.Algebra.Units.Basic
public import TauCeti.Algebra.BigOperators.Group.OrderedProduct
public import TauCeti.Algebra.QuantumTorus.Basic
public import TauCeti.Data.Finsupp.Single
public import TauCeti.LinearAlgebra.Matrix.FinsuppBilinForm
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Ring

/-!
# Normalized ordered monomials and the universal coordinate lift for quantum tori

For a linearly ordered index type `I`, an `R`-algebra `B` with scalar unit `u : Rˣ`, a matrix
`Λ : Matrix I I ℤ`, and a coordinate family `U : I → Bˣ`, `TauCeti.orderedMonomial u Λ U a`
normalizes the ordered coordinate product `TauCeti.orderedCoordProd U a` by the strict
upper-triangular twist `u ^ (-Λ.strictUpper.finsuppBilinForm a a)`.

When `Λ.finsuppBilinForm` is alternating and `U : I → Bˣ` satisfies the `(u, 2 • Λ)`
quasi-commutation relations, `orderedMonomial u Λ U` satisfies the `(u, Λ)` multiplication law
independently of the chosen linear order on `I`, yielding the universal coordinate lift
`QuantumTorus.liftCoordinates` without requiring an order on `I`.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §4.
-/

public section

namespace TauCeti

section Algebra

variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- The normalized ordered-product monomial `u ^ (-∑_{i < j} a_i Λ_{ij} a_j) * ∏_i U_i^{a_i}`. -/
noncomputable def orderedMonomial [_ord : LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B) (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) * orderedCoordProd U a

theorem orderedMonomial_def [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (a : I →₀ ℤ) :
    orderedMonomial u Λ U a =
      Units.map (algebraMap R B) (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) *
        orderedCoordProd U a :=
  (rfl)

@[simp]
theorem orderedMonomial_zero [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ) :
    orderedMonomial u Λ U 0 = 1 := by
  simp [orderedMonomial]

@[simp]
theorem orderedMonomial_single_one [_ord : LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (i : I) : orderedMonomial u Λ U (Finsupp.single i 1) = U i := by
  rw [orderedMonomial, orderedCoordProd_eq_sort_prod U _ Finsupp.support_single_subset,
    Matrix.finsuppBilinForm_single_single]
  simp

section QuasiComm

variable {u : Rˣ} {Λ : Matrix I I ℤ} (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
  (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i))

include hU in
private theorem zpow_mul_zpow_of_quasiComm (i j : I) (m n : ℤ) :
    U i ^ m * U j ^ n =
      Units.map (algebraMap R B) (u ^ (2 * (m * Λ i j * n))) * (U j ^ n * U i ^ m) := by
  rw [Units.zpow_mul_zpow_of_map_algebraMap_mul (hU i j) m n, ← zpow_mul]
  congr 3
  ring

include hΛ hU in
private theorem prod_zpow_mul_zpow_of_lt [LinearOrder I] (tl : List I) {i : I}
    (htl : tl.Pairwise (· < ·)) (hi : ∀ j ∈ tl, i < j) (a : I →₀ ℤ) (ha : ∀ j ∈ a.support, j ∈ tl)
    (n : ℤ) :
    ((tl.map fun j ↦ U j ^ a j).prod) * U i ^ n =
      Units.map (algebraMap R B)
        (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a)) *
        (U i ^ n * (tl.map fun j ↦ U j ^ a j).prod) := by
  induction tl generalizing a with
  | nil => simp [Finsupp.eq_zero_of_support_mem_nil ha]
  | cons j rest ih =>
    rw [List.pairwise_cons] at htl
    set a' := a.erase j
    have ha' : ∀ k ∈ a'.support, k ∈ rest := fun _ hk ↦ Finsupp.mem_of_mem_support_erase ha hk
    have hj_notMem : j ∉ rest := fun h ↦ (htl.1 j h).false
    have hmap := (a.list_map_erase_of_notMem hj_notMem fun k m ↦ U k ^ m).symm
    have hup : -2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a =
        -2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a' +
          2 * (a j * Λ j i * n) := by
      conv_lhs => rw [← Finsupp.single_add_erase j a]
      simp only [map_add, Matrix.finsuppBilinForm_single_single, Matrix.strictUpper_apply,
        hi j List.mem_cons_self, ↓reduceIte,
        ← Matrix.neg_apply_eq_of_isAlt_finsuppBilinForm hΛ i j]
      ring
    calc
      (List.map (fun k ↦ U k ^ a k) (j :: rest)).prod * U i ^ n
        = U j ^ a j * (Units.map (algebraMap R B)
            (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a')) *
            (U i ^ n * (rest.map fun k ↦ U k ^ a' k).prod)) := by
          rw [List.map_cons, List.prod_cons, hmap, mul_assoc,
            ih htl.2 (fun k hk ↦ hi k (List.mem_cons_of_mem j hk)) a' ha']
      _ = Units.map (algebraMap R B)
            (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a')) *
            ((U j ^ a j * U i ^ n) * (rest.map fun k ↦ U k ^ a' k).prod) := by
          rw [Units.mul_map_algebraMap_mul, mul_assoc]
      _ = Units.map (algebraMap R B)
            (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a)) *
            (U i ^ n * (List.map (fun k ↦ U k ^ a k) (j :: rest)).prod) := by
          rw [zpow_mul_zpow_of_quasiComm hU j i (a j) n, mul_assoc _ (U i ^ n * U j ^ a j),
            Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, ← hup, mul_assoc (U i ^ n),
            List.map_cons, List.prod_cons, hmap]

include hΛ hU in
private theorem prod_zpow_mul_prod_zpow [LinearOrder I] (l : List I) (hl : l.Pairwise (· < ·))
    (p q : I →₀ ℤ) (hp : ∀ j ∈ p.support, j ∈ l) (hq : ∀ j ∈ q.support, j ∈ l) :
    ((l.map fun i ↦ U i ^ p i).prod) * ((l.map fun i ↦ U i ^ q i).prod) =
      Units.map (algebraMap R B) (u ^ (-2 * Λ.strictUpper.finsuppBilinForm q p)) *
        ((l.map fun i ↦ U i ^ (p + q) i).prod) := by
  induction l generalizing p q with
  | nil => simp [Finsupp.eq_zero_of_support_mem_nil hp, Finsupp.eq_zero_of_support_mem_nil hq]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    set p' := p.erase i
    set q' := q.erase i
    have hp' : ∀ j ∈ p'.support, j ∈ tl := fun _ hj ↦ Finsupp.mem_of_mem_support_erase hp hj
    have hq' : ∀ j ∈ q'.support, j ∈ tl := fun _ hj ↦ Finsupp.mem_of_mem_support_erase hq hj
    have hi_notMem : i ∉ tl := fun h ↦ (hl.1 i h).false
    have hmapp := (p.list_map_erase_of_notMem hi_notMem fun j m ↦ U j ^ m).symm
    have hmapq := (q.list_map_erase_of_notMem hi_notMem fun j m ↦ U j ^ m).symm
    have hmappq := ((p + q).list_map_erase_of_notMem hi_notMem fun j m ↦ U j ^ m).symm
    have hq0 := Λ.finsuppBilinForm_strictUpper_single_right_eq_zero (x := q.erase i) (p i)
      fun j hj ↦ (hl.1 j (hq' j hj)).le
    have hup : -2 * Λ.strictUpper.finsuppBilinForm q p =
        -2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p' +
          (-2 * Λ.strictUpper.finsuppBilinForm q' p') := by
      dsimp only [p', q']
      conv_lhs => rw [← Finsupp.single_add_erase i p, ← Finsupp.single_add_erase i q]
      simp only [map_add, LinearMap.add_apply, Matrix.finsuppBilinForm_single_single, hq0,
        Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]
      ring
    calc
      (List.map (fun j ↦ U j ^ p j) (i :: tl)).prod *
          (List.map (fun j ↦ U j ^ q j) (i :: tl)).prod
        = U i ^ p i * (((tl.map fun j ↦ U j ^ p' j).prod * U i ^ q i) *
            (tl.map fun j ↦ U j ^ q' j).prod) := by
          rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, hmapp, hmapq,
            mul_assoc (U i ^ p i), ← mul_assoc _ (U i ^ q i)]
      _ = Units.map (algebraMap R B)
            (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p')) *
            (U i ^ (p + q) i * ((tl.map fun j ↦ U j ^ p' j).prod *
              (tl.map fun j ↦ U j ^ q' j).prod)) := by
          rw [prod_zpow_mul_zpow_of_lt hΛ hU tl hl.2 hl.1 p' hp' (q i),
            mul_assoc _ (U i ^ q i * _), Units.mul_map_algebraMap_mul,
            mul_assoc (U i ^ q i), ← mul_assoc (U i ^ p i) (U i ^ q i), ← zpow_add,
            ← Finsupp.add_apply]
      _ = Units.map (algebraMap R B) (u ^ (-2 * Λ.strictUpper.finsuppBilinForm q p)) *
            (List.map (fun j ↦ U j ^ (p + q) j) (i :: tl)).prod := by
          rw [ih hl.2 p' q' hp' hq', Units.mul_map_algebraMap_mul,
            Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, ← hup, List.map_cons,
            List.prod_cons, hmappq, Finsupp.erase_add]

include hΛ hU in
/-- For alternating `Λ` and `(u, 2 • Λ)`-quasi-commuting coordinates `U`, normalized ordered
products satisfy the `(u, Λ)`-twisted multiplication law. -/
theorem orderedMonomial_mul [LinearOrder I] (a b : I →₀ ℤ) :
    orderedMonomial u Λ U a * orderedMonomial u Λ U b =
      Units.map (algebraMap R B) (u ^ Λ.finsuppBilinForm a b) *
        orderedMonomial u Λ U (a + b) := by
  let s := a.support ∪ b.support
  have hprod := prod_zpow_mul_prod_zpow hΛ hU (s.sort (· ≤ ·)) s.sortedLT_sort.pairwise a b
    (fun _ hj ↦ (Finset.mem_sort _).mpr (Finset.subset_union_left hj))
    (fun _ hj ↦ (Finset.mem_sort _).mpr (Finset.subset_union_right hj))
  calc
    orderedMonomial u Λ U a * orderedMonomial u Λ U b
      = (Units.map (algebraMap R B) (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) *
          ((s.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod) *
        (Units.map (algebraMap R B) (u ^ (-Λ.strictUpper.finsuppBilinForm b b)) *
          ((s.sort (· ≤ ·)).map fun i ↦ U i ^ b i).prod) := by
        rw [orderedMonomial, orderedMonomial,
          orderedCoordProd_eq_sort_prod U a Finset.subset_union_left,
          orderedCoordProd_eq_sort_prod U b Finset.subset_union_right]
    _ = Units.map (algebraMap R B)
          ((u ^ (-Λ.strictUpper.finsuppBilinForm a a) *
            u ^ (-Λ.strictUpper.finsuppBilinForm b b)) *
            u ^ (-2 * Λ.strictUpper.finsuppBilinForm b a)) *
          orderedCoordProd U (a + b) := by
        rw [Units.map_algebraMap_mul_mul_map_algebraMap_mul, hprod,
          Units.map_algebraMap_mul_map_algebraMap,
          ← orderedCoordProd_eq_sort_prod U (a + b) Finsupp.support_add]
    _ = Units.map (algebraMap R B) (u ^ Λ.finsuppBilinForm a b) *
          orderedMonomial u Λ U (a + b) := by
        rw [orderedMonomial, Units.map_algebraMap_mul_map_algebraMap]
        congr 2
        simp only [← zpow_add, Matrix.finsuppBilinForm_eq_strictUpper_sub_flip hΛ a b,
          map_add, LinearMap.add_apply]
        congr 1
        ring

end QuasiComm

private noncomputable def liftOrderedMonomial [_ord : LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i)) :
    QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B :=
  QuantumTorus.lift u Λ.finsuppBilinForm (fun a ↦ (orderedMonomial u Λ U a : B))
    (by simp) fun a b ↦ by
      rw [← Units.val_mul, orderedMonomial_mul hΛ hU]
      simp [Algebra.smul_def, -map_zpow]

private theorem liftOrderedMonomial_monomial [_ord : LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i))
    (a : I →₀ ℤ) :
    liftOrderedMonomial hΛ U hU (QuantumTorus.monomial u Λ.finsuppBilinForm a) =
      orderedMonomial u Λ U a :=
  QuantumTorus.lift_monomial ..

/-- Under alternating `Λ` and `(u, 2 • Λ)`-quasi-commutation of `U`, `orderedMonomial u Λ U a` is
independent of the chosen `LinearOrder` on `I`. -/
theorem orderedMonomial_eq_of_linearOrder (l₁ l₂ : LinearOrder I) {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i))
    (a : I →₀ ℤ) :
    orderedMonomial (_ord := l₁) u Λ U a = orderedMonomial (_ord := l₂) u Λ U a := by
  have hhom : liftOrderedMonomial (_ord := l₁) hΛ U hU =
      liftOrderedMonomial (_ord := l₂) hΛ U hU :=
    QuantumTorus.algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ by
      rw [Finsupp.coe_basisSingleOne,
        liftOrderedMonomial_monomial (_ord := l₁),
        liftOrderedMonomial_monomial (_ord := l₂),
        orderedMonomial_single_one (_ord := l₁),
        orderedMonomial_single_one (_ord := l₂)]
  exact Units.ext <| by
    have ha := congrArg (· (QuantumTorus.monomial u Λ.finsuppBilinForm a)) hhom
    rwa [liftOrderedMonomial_monomial (_ord := l₁),
      liftOrderedMonomial_monomial (_ord := l₂)] at ha

namespace QuantumTorus

variable {u : Rˣ} {Λ : Matrix I I ℤ} (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
  (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i))

/-- Universal `R`-algebra map `QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B` sending each
standard generator `monomial (single i 1)` to `U i`. -/
noncomputable def liftCoordinates :
    QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B :=
  letI := (exists_wellFoundedLT I).choose
  liftOrderedMonomial hΛ U hU

@[simp]
theorem liftCoordinates_single_one (i : I) :
    liftCoordinates hΛ U hU (monomial u Λ.finsuppBilinForm (Finsupp.single i 1)) = U i := by
  dsimp only [liftCoordinates]
  rw [liftOrderedMonomial_monomial (_ord := (exists_wellFoundedLT I).choose),
    orderedMonomial_single_one (_ord := (exists_wellFoundedLT I).choose)]

/-- For any `LinearOrder` on `I`, `QuantumTorus.liftCoordinates` evaluates `monomial a` to the
normalized ordered product `orderedMonomial u Λ U a`. -/
theorem liftCoordinates_monomial [LinearOrder I] (a : I →₀ ℤ) :
    liftCoordinates hΛ U hU (monomial u Λ.finsuppBilinForm a) = orderedMonomial u Λ U a := by
  have heq : liftCoordinates hΛ U hU = liftOrderedMonomial hΛ U hU :=
    algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ by
      rw [Finsupp.coe_basisSingleOne, liftCoordinates_single_one,
        liftOrderedMonomial_monomial, orderedMonomial_single_one]
  rw [heq, liftOrderedMonomial_monomial]

/-- `QuantumTorus.liftCoordinates hΛ U hU` is the unique `R`-algebra map sending each standard
generator `monomial (single i 1)` to `U i`. -/
theorem liftCoordinates_unique
    {φ : QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B}
    (hφ : ∀ i, φ (monomial u Λ.finsuppBilinForm (Finsupp.single i 1)) = U i) :
    φ = liftCoordinates hΛ U hU :=
  algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ by
    simpa using (hφ i).trans (liftCoordinates_single_one hΛ U hU i).symm

end QuantumTorus

end Algebra

end TauCeti
