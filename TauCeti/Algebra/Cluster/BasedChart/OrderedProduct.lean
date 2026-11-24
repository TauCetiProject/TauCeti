/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.Algebra.Algebra.Units.Basic
public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.LinearAlgebra.Matrix.FinsuppBilinForm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Ring

/-!
# Ordered-product reconstruction of based quantum-torus charts

For a linearly ordered index type `I`, an unit `u : Rˣ`, a matrix `Λ : Matrix I I ℤ`, and a family
of ambient units `U : I → Bˣ`, `TauCeti.orderedMonomial u Λ U a` normalizes the increasing
coordinate product `TauCeti.orderedCoordProd U a = ∏_{i ∈ a.support} U_i^{a_i}` by the strict
upper-triangular twist `u ^ (-Λ.strictUpper.finsuppBilinForm a a)`.

When `Λ` has zero diagonal, every normalized monomial of `M : BasedChart u Λ.finsuppBilinForm B`
is recovered from its standard coordinates by `BasedChart.monomial_eq_orderedMonomial`. Conversely,
when `Λ.finsuppBilinForm` is alternating and `U` satisfies the `(u, 2 • Λ)`-quasi-commutation
relations, `orderedMonomial u Λ U` satisfies the `(u, Λ)`-multiplication law independently of the
linear order on `I`, yielding the universal coordinate lift `QuantumTorus.liftCoordinates` and the
coordinate chart constructor `BasedChart.ofCoordinates`.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §4.
-/

public section

namespace TauCeti

section ZsmulSelfZero

variable {R L I B : Type*} [CommSemiring R] [AddCommGroup L] [Semiring B] [Algebra R B]
  {u : Rˣ}

/-- When `Λ a a = 0`, scalar multiples of `a` correspond to integer powers of `monomialUnit u Λ a`
without requiring `Λ` to be globally alternating. -/
theorem QuantumTorus.monomialUnit_zsmul_of_self_eq_zero {Λ : LinearMap.BilinForm ℤ L} {a : L}
    (ha : Λ a a = 0) (n : ℤ) :
    QuantumTorus.monomialUnit u Λ (n • a) = QuantumTorus.monomialUnit u Λ a ^ n := by
  let f : Multiplicative ℤ →* (QuantumTorus R L u Λ)ˣ :=
    { toFun := fun m ↦ QuantumTorus.monomialUnit u Λ (m.toAdd • a)
      map_one' := by simp
      map_mul' := fun m k ↦ by simp [add_zsmul, ha] }
  simpa [f] using f.map_zpow (Multiplicative.ofAdd (1 : ℤ)) n

/-- When `Λ a a = 0`, scalar multiples of `a` correspond to integer powers of `M.monomial a`. -/
theorem BasedChart.monomial_zsmul_of_self_eq_zero {Λ : LinearMap.BilinForm ℤ L}
    (M : BasedChart u Λ B) {a : L} (ha : Λ a a = 0) (n : ℤ) :
    M.monomial (n • a) = M.monomial a ^ n := by
  rw [← M.map_eval_monomialUnit, QuantumTorus.monomialUnit_zsmul_of_self_eq_zero ha, map_zpow,
    M.map_eval_monomialUnit]

/-- When `Λ (single i 1) (single i 1) = 0`, `M.monomial (single i n)` is the `n`-th integer power of
the `i`-th standard coordinate monomial. -/
theorem BasedChart.monomial_single_of_self_eq_zero {Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)}
    (M : BasedChart u Λ B) {i : I} (hi : Λ (Finsupp.single i 1) (Finsupp.single i 1) = 0)
    (n : ℤ) :
    M.monomial (Finsupp.single i n) = M.monomial (Finsupp.single i 1) ^ n := by
  simpa using M.monomial_zsmul_of_self_eq_zero hi n

end ZsmulSelfZero

section OrderedProduct

variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- The ordered coordinate product `∏_{i ∈ a.support} U_i^{a_i}` taken in increasing order of
`I`. -/
noncomputable def orderedCoordProd [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) : Bˣ :=
  ((a.support.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod

theorem orderedCoordProd_def [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) :
    orderedCoordProd U a = ((a.support.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod :=
  (rfl)

@[simp]
theorem orderedCoordProd_zero [LinearOrder I] (U : I → Bˣ) : orderedCoordProd U 0 = 1 := by
  simp [orderedCoordProd]

/-- `orderedCoordProd U a` can be computed over any superset `s ⊇ a.support` sorted in increasing
order, since zero exponents contribute `1`. -/
theorem orderedCoordProd_eq_sort_prod [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) {s : Finset I}
    (hs : a.support ⊆ s) :
    orderedCoordProd U a = ((s.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod := by
  have hfilt : (s.sort (· ≤ ·)).filter (· ∈ a.support) = a.support.sort (· ≤ ·) :=
    List.Perm.eq_of_pairwise' ((s.pairwise_sort _).filter _) (a.support.pairwise_sort _) <|
      (List.perm_ext_iff_of_nodup ((s.sort_nodup _).filter _) (a.support.sort_nodup _)).mpr fun i ↦
        by simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq, and_iff_right_iff_imp]
           exact fun hi ↦ hs hi
  have hprod (l : List I) : ((l.filter (· ∈ a.support)).map fun i ↦ U i ^ a i).prod =
      (l.map fun i ↦ U i ^ a i).prod := by
    induction l with
    | nil => rfl
    | cons i tl ih =>
      rw [List.filter_cons]
      split_ifs with hp
      · rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih]
      · rw [List.map_cons, List.prod_cons, (by simpa using hp : a i = 0), zpow_zero, one_mul, ih]
  rw [orderedCoordProd, ← hfilt, hprod]

/-- On a finite index type, `orderedCoordProd U a` equals the product over `Finset.univ.sort`. -/
theorem orderedCoordProd_eq_univ_sort [LinearOrder I] [Fintype I] (U : I → Bˣ) (a : I →₀ ℤ) :
    orderedCoordProd U a = ((Finset.univ.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod :=
  orderedCoordProd_eq_sort_prod U a (Finset.subset_univ _)

/-- The normalized ordered-product monomial `u ^ (-∑_{i < j} a_i Λ_{ij} a_j) * ∏_i U_i^{a_i}`. -/
noncomputable def orderedMonomial [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
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
theorem orderedMonomial_single_one [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (i : I) : orderedMonomial u Λ U (Finsupp.single i 1) = U i := by
  rw [orderedMonomial, orderedCoordProd_eq_sort_prod U _ Finsupp.support_single_subset,
    Matrix.finsuppBilinForm_single_single]
  simp

private theorem strictUpper_finsuppBilinForm_single_of_lt [LinearOrder I] (Λ : Matrix I I ℤ)
    {i : I} (x : ℤ) {a : I →₀ ℤ} (ha : ∀ j ∈ a.support, i < j) :
    Λ.strictUpper.finsuppBilinForm (Finsupp.single i x) a =
        Λ.finsuppBilinForm (Finsupp.single i x) a ∧
      Λ.strictUpper.finsuppBilinForm a (Finsupp.single i x) = 0 :=
  ⟨by rw [Matrix.finsuppBilinForm_apply, Finsupp.sum_single_index (by simp),
        Matrix.finsuppBilinForm_apply, Finsupp.sum_single_index (by simp)]
      exact Finset.sum_congr rfl fun j hj ↦ by simp [ha j hj],
   by rw [Matrix.finsuppBilinForm_apply, Finsupp.sum]
      exact Finset.sum_eq_zero fun j hj ↦ by
        rw [Finsupp.sum_single_index (by simp)]
        simp [(ha j hj).not_gt]⟩

private theorem eq_zero_of_support_nil {b : I →₀ ℤ} (hb : ∀ j ∈ b.support, j ∈ ([] : List I)) :
    b = 0 :=
  Finsupp.support_eq_empty.mp
    (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (hb j hj))

private theorem erase_support_mem_of_cons {i : I} {tl : List I} {b : I →₀ ℤ}
    (hb : ∀ j ∈ b.support, j ∈ i :: tl) : ∀ j ∈ (b.erase i).support, j ∈ tl := fun j hj ↦ by
  classical
  have hj0 := Finsupp.mem_support_iff.mp hj
  have hji : j ≠ i := fun h ↦ hj0 (by simp [h])
  exact (List.mem_cons.mp
    (hb j (Finsupp.mem_support_iff.mpr (by simpa [hji] using hj0)))).resolve_left hji

private theorem map_zpow_erase_of_lt [LinearOrder I] (U : I → Bˣ) {i : I} {tl : List I}
    (hlt : ∀ j ∈ tl, i < j) (b : I →₀ ℤ) :
    (tl.map fun j ↦ U j ^ b j) = (tl.map fun j ↦ U j ^ (b.erase i) j) :=
  List.map_congr_left fun j hj ↦ by simp [(hlt j hj).ne']

/-- **Ordered-product reconstruction of chart monomials**: when `Λ` has zero diagonal, every
normalized monomial of `M` equals `orderedMonomial u Λ (M.coordinate Finsupp.basisSingleOne) a`. -/
theorem BasedChart.monomial_eq_orderedMonomial [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (M : BasedChart u Λ.finsuppBilinForm B) (hdiag : ∀ i, Λ i i = 0) (a : I →₀ ℤ) :
    M.monomial a = orderedMonomial u Λ (M.coordinate Finsupp.basisSingleOne) a := by
  let U : I → Bˣ := M.coordinate Finsupp.basisSingleOne
  have hU_single (i : I) (n : ℤ) : U i ^ n = M.monomial (Finsupp.single i n) := by
    have hii : Λ.finsuppBilinForm (Finsupp.single i 1) (Finsupp.single i 1) = 0 := by
      simp [hdiag i]
    simpa [U, BasedChart.coordinate_def] using (M.monomial_single_of_self_eq_zero hii n).symm
  suffices ∀ (l : List I), l.Pairwise (· < ·) → ∀ b : I →₀ ℤ, (∀ j ∈ b.support, j ∈ l) →
      ((l.map fun i ↦ U i ^ b i).prod : Bˣ) =
        Units.map (algebraMap R B) (u ^ Λ.strictUpper.finsuppBilinForm b b) * M.monomial b by
    rw [orderedMonomial, orderedCoordProd,
      this _ a.support.sortedLT_sort.pairwise a fun _ hj ↦ (Finset.mem_sort _).mpr hj,
      Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, neg_add_cancel, zpow_zero, map_one,
      one_mul]
  intro l hl
  induction l with
  | nil => intro b hb; simp [eq_zero_of_support_nil hb]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    intro b hb
    set b' := b.erase i
    have hb' := erase_support_mem_of_cons hb
    obtain ⟨hup₁, hup₂⟩ :=
      strictUpper_finsuppBilinForm_single_of_lt Λ (b i) fun j hj ↦ hl.1 j (hb' j hj)
    have hup : Λ.strictUpper.finsuppBilinForm b b =
        Λ.strictUpper.finsuppBilinForm b' b' +
          Λ.finsuppBilinForm (Finsupp.single i (b i)) b' := by
      conv_lhs => rw [← Finsupp.single_add_erase i b]
      simp only [map_add, LinearMap.add_apply, Matrix.finsuppBilinForm_single_single, hup₁, hup₂,
        Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]
      ring
    calc
      (List.map (fun j ↦ U j ^ b j) (i :: tl)).prod
        = M.monomial (Finsupp.single i (b i)) *
            (Units.map (algebraMap R B) (u ^ Λ.strictUpper.finsuppBilinForm b' b') *
              M.monomial b') := by
          rw [List.map_cons, List.prod_cons, hU_single, map_zpow_erase_of_lt U hl.1 b,
            ih hl.2 b' hb']
      _ = Units.map (algebraMap R B)
            (u ^ Λ.strictUpper.finsuppBilinForm b' b' *
              u ^ Λ.finsuppBilinForm (Finsupp.single i (b i)) b') *
            M.monomial b := by
          rw [Units.mul_map_algebraMap_mul, M.monomial_mul,
            Units.map_algebraMap_mul_map_algebraMap, Finsupp.single_add_erase i b]
      _ = Units.map (algebraMap R B) (u ^ Λ.strictUpper.finsuppBilinForm b b) * M.monomial b := by
          rw [← zpow_add, ← hup]

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
  | nil => simp [eq_zero_of_support_nil ha]
  | cons j rest ih =>
    rw [List.pairwise_cons] at htl
    set a' := a.erase j
    have ha' := erase_support_mem_of_cons ha
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
          rw [List.map_cons, List.prod_cons, map_zpow_erase_of_lt U htl.1 a, mul_assoc,
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
            List.map_cons, List.prod_cons, map_zpow_erase_of_lt U htl.1 a]

include hΛ hU in
private theorem prod_zpow_mul_prod_zpow [LinearOrder I] (l : List I) (hl : l.Pairwise (· < ·))
    (p q : I →₀ ℤ) (hp : ∀ j ∈ p.support, j ∈ l) (hq : ∀ j ∈ q.support, j ∈ l) :
    ((l.map fun i ↦ U i ^ p i).prod) * ((l.map fun i ↦ U i ^ q i).prod) =
      Units.map (algebraMap R B) (u ^ (-2 * Λ.strictUpper.finsuppBilinForm q p)) *
        ((l.map fun i ↦ U i ^ (p + q) i).prod) := by
  induction l generalizing p q with
  | nil => simp [eq_zero_of_support_nil hp, eq_zero_of_support_nil hq]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    set p' := p.erase i
    set q' := q.erase i
    have hp' := erase_support_mem_of_cons hp
    have hq' := erase_support_mem_of_cons hq
    have hup : -2 * Λ.strictUpper.finsuppBilinForm q p =
        -2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p' +
          (-2 * Λ.strictUpper.finsuppBilinForm q' p') := by
      conv_lhs => rw [← Finsupp.single_add_erase i p, ← Finsupp.single_add_erase i q]
      simp only [map_add, LinearMap.add_apply, Matrix.finsuppBilinForm_single_single,
        (strictUpper_finsuppBilinForm_single_of_lt Λ (p i) fun j hj ↦ hl.1 j (hq' j hj)).2,
        Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]
      ring
    calc
      (List.map (fun j ↦ U j ^ p j) (i :: tl)).prod *
          (List.map (fun j ↦ U j ^ q j) (i :: tl)).prod
        = U i ^ p i * (((tl.map fun j ↦ U j ^ p' j).prod * U i ^ q i) *
            (tl.map fun j ↦ U j ^ q' j).prod) := by
          rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
            map_zpow_erase_of_lt U hl.1 p, map_zpow_erase_of_lt U hl.1 q, mul_assoc (U i ^ p i),
            ← mul_assoc _ (U i ^ q i)]
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
            List.prod_cons, map_zpow_erase_of_lt U hl.1 (p + q), Finsupp.erase_add]

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

private noncomputable def liftOrderedMonomial [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i)) :
    QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B :=
  QuantumTorus.lift u Λ.finsuppBilinForm (fun a ↦ (orderedMonomial u Λ U a : B))
    (by simp) fun a b ↦ by
      rw [← Units.val_mul, orderedMonomial_mul hΛ hU]
      simp [Algebra.smul_def, -map_zpow]

private theorem liftOrderedMonomial_monomial [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
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
    @orderedMonomial R I B _ _ _ l₁ u Λ U a = @orderedMonomial R I B _ _ _ l₂ u Λ U a := by
  have hhom : @liftOrderedMonomial R I B _ _ _ l₁ u Λ hΛ U hU =
      @liftOrderedMonomial R I B _ _ _ l₂ u Λ hΛ U hU :=
    QuantumTorus.algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ by
      rw [Finsupp.coe_basisSingleOne,
        @liftOrderedMonomial_monomial R I B _ _ _ l₁,
        @liftOrderedMonomial_monomial R I B _ _ _ l₂,
        @orderedMonomial_single_one R I B _ _ _ l₁,
        @orderedMonomial_single_one R I B _ _ _ l₂]
  exact Units.ext <| by
    have ha := congrArg (· (QuantumTorus.monomial u Λ.finsuppBilinForm a)) hhom
    rwa [@liftOrderedMonomial_monomial R I B _ _ _ l₁,
      @liftOrderedMonomial_monomial R I B _ _ _ l₂] at ha

section LiftCoordinates

variable {u : Rˣ} {Λ : Matrix I I ℤ} (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
  (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i))

/-- Universal `R`-algebra map `QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B` sending each
standard generator `monomial (single i 1)` to `U i`. -/
noncomputable def QuantumTorus.liftCoordinates :
    QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B :=
  letI := (exists_wellFoundedLT I).choose
  liftOrderedMonomial hΛ U hU

@[simp]
theorem QuantumTorus.liftCoordinates_single_one (i : I) :
    QuantumTorus.liftCoordinates hΛ U hU
        (QuantumTorus.monomial u Λ.finsuppBilinForm (Finsupp.single i 1)) =
      U i := by
  let l₀ := (exists_wellFoundedLT I).choose
  exact (@liftOrderedMonomial_monomial R I B _ _ _ l₀ u Λ hΛ U hU (Finsupp.single i 1)).trans
    (congrArg Units.val (@orderedMonomial_single_one R I B _ _ _ l₀ u Λ U i))

/-- For any `LinearOrder` on `I`, `QuantumTorus.liftCoordinates` evaluates `monomial a` to the
normalized ordered product `orderedMonomial u Λ U a`. -/
theorem QuantumTorus.liftCoordinates_monomial [LinearOrder I] (a : I →₀ ℤ) :
    QuantumTorus.liftCoordinates hΛ U hU (QuantumTorus.monomial u Λ.finsuppBilinForm a) =
      orderedMonomial u Λ U a := by
  have heq : QuantumTorus.liftCoordinates hΛ U hU = liftOrderedMonomial hΛ U hU :=
    QuantumTorus.algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ by
      rw [Finsupp.coe_basisSingleOne, QuantumTorus.liftCoordinates_single_one,
        liftOrderedMonomial_monomial, orderedMonomial_single_one]
  rw [heq, liftOrderedMonomial_monomial]

/-- `QuantumTorus.liftCoordinates hΛ U hU` is the unique `R`-algebra map sending each standard
generator `monomial (single i 1)` to `U i`. -/
theorem QuantumTorus.liftCoordinates_unique
    {φ : QuantumTorus R (I →₀ ℤ) u Λ.finsuppBilinForm →ₐ[R] B}
    (hφ : ∀ i, φ (QuantumTorus.monomial u Λ.finsuppBilinForm (Finsupp.single i 1)) = U i) :
    φ = QuantumTorus.liftCoordinates hΛ U hU :=
  QuantumTorus.algHom_ext_of_basis Finsupp.basisSingleOne fun i ↦ by
    simpa using (hφ i).trans (QuantumTorus.liftCoordinates_single_one hΛ U hU i).symm

/-- Construct a based chart from `(u, 2 • Λ)`-quasi-commuting coordinates whose normalized ordered
products are `R`-linearly independent. -/
noncomputable def BasedChart.ofCoordinates [LinearOrder I]
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) :
    BasedChart u Λ.finsuppBilinForm B where
  monomial := orderedMonomial u Λ U
  monomial_zero := orderedMonomial_zero u Λ U
  monomial_mul := orderedMonomial_mul hΛ hU
  linearIndependent := hli

@[simp]
theorem BasedChart.ofCoordinates_monomial [LinearOrder I]
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) (a : I →₀ ℤ) :
    (BasedChart.ofCoordinates hΛ U hU hli).monomial a = orderedMonomial u Λ U a :=
  (rfl)

@[simp]
theorem BasedChart.coordinate_ofCoordinates [LinearOrder I]
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) (i : I) :
    (BasedChart.ofCoordinates hΛ U hU hli).coordinate Finsupp.basisSingleOne i = U i := by
  simp [BasedChart.coordinate_def]

end LiftCoordinates

/-- Rank-2 ordered-product formula for exponent `(-1, 2)` and skew matrix `!![0, 1; -1, 0]`:
`M(-e_0 + 2 e_1) = u^2 • (X_0⁻¹ * X_1^2)`. -/
theorem BasedChart.monomial_rankTwo_neg_one_two {u : Rˣ}
    (M : BasedChart u (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).finsuppBilinForm B) :
    M.monomial (-Finsupp.single 0 1 + 2 • Finsupp.single 1 1) =
      Units.map (algebraMap R B) (u ^ 2) *
        ((M.coordinate Finsupp.basisSingleOne 0)⁻¹ *
          M.coordinate Finsupp.basisSingleOne 1 ^ 2) := by
  set a : Fin 2 →₀ ℤ := -Finsupp.single 0 1 + 2 • Finsupp.single 1 1
  have hsort : (Finset.univ : Finset (Fin 2)).sort (· ≤ ·) = [0, 1] := by
    have huniv : ([0, 1] : List (Fin 2)).toFinset = Finset.univ := by decide
    rw [← huniv]
    exact (List.toFinset_sort (r := (· ≤ ·)) (by decide)).mpr (by decide)
  rw [M.monomial_eq_orderedMonomial (fun i ↦ by fin_cases i <;> rfl) a, orderedMonomial,
    orderedCoordProd_eq_univ_sort, hsort, Matrix.finsuppBilinForm_apply_eq_dotProduct]
  have ha : a 0 = -1 ∧ a 1 = 2 := by simp [a]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, ha.1, ha.2]

end OrderedProduct

end TauCeti
