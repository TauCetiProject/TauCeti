/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.Algebra.QuantumTorus.Lift
import Mathlib.Tactic.Ring

/-!
# Ordered-product reconstruction and coordinate construction of based charts

For a linearly ordered index type `I` and a matrix `Λ : Matrix I I ℤ` with zero diagonal, every
normalized monomial of `M : BasedChart u Λ.finsuppBilinForm B` equals the normalized ordered
coordinate product `TauCeti.orderedMonomial u Λ (M.coordinate Finsupp.basisSingleOne) a`
(`BasedChart.monomial_eq_orderedMonomial`). Conversely, when `Λ.finsuppBilinForm` is alternating and
`U : I → Bˣ` satisfies the `(u, 2 • Λ)` quasi-commutation relations with `R`-linearly independent
normalized ordered products, `BasedChart.ofCoordinates` packages `orderedMonomial u Λ U` as a
faithful based chart.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §4.
-/

public section

namespace TauCeti.BasedChart

variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- **Ordered-product reconstruction of chart monomials**: when `Λ` has zero diagonal, every
normalized monomial of `M` equals `orderedMonomial u Λ (M.coordinate Finsupp.basisSingleOne) a`. -/
theorem monomial_eq_orderedMonomial [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ}
    (M : BasedChart u Λ.finsuppBilinForm B) (hdiag : ∀ i, Λ i i = 0) (a : I →₀ ℤ) :
    M.monomial a = orderedMonomial u Λ (M.coordinate Finsupp.basisSingleOne) a := by
  let U : I → Bˣ := M.coordinate Finsupp.basisSingleOne
  have hU_single (i : I) (n : ℤ) : U i ^ n = M.monomial (Finsupp.single i n) := by
    have hii : Λ.finsuppBilinForm (Finsupp.single i 1) (Finsupp.single i 1) = 0 := by
      simp [hdiag i]
    simpa [U, coordinate_def] using (M.monomial_single_of_self_eq_zero hii n).symm
  suffices ∀ (l : List I), l.Pairwise (· < ·) → ∀ b : I →₀ ℤ, (∀ j ∈ b.support, j ∈ l) →
      ((l.map fun i ↦ U i ^ b i).prod : Bˣ) =
        Units.map (algebraMap R B) (u ^ Λ.strictUpper.finsuppBilinForm b b) * M.monomial b by
    rw [orderedMonomial_def, orderedCoordProd_def,
      this _ a.support.sortedLT_sort.pairwise a fun _ hj ↦ (Finset.mem_sort _).mpr hj,
      Units.map_algebraMap_mul_map_algebraMap, ← zpow_add, neg_add_cancel, zpow_zero, map_one,
      one_mul]
  intro l hl
  induction l with
  | nil => intro b hb; simp [Finsupp.eq_zero_of_support_mem_nil hb]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    intro b hb
    set b' := b.erase i
    have hb' : ∀ j ∈ b'.support, j ∈ tl := fun _ hj ↦ Finsupp.mem_of_mem_support_erase hb hj
    have hi_notMem : i ∉ tl := fun h ↦ (hl.1 i h).false
    have hmap := (b.list_map_erase_of_notMem hi_notMem fun j m ↦ U j ^ m).symm
    have hlt : ∀ j ∈ (b.erase i).support, i < j := fun j hj ↦ hl.1 j (hb' j hj)
    have hup : Λ.strictUpper.finsuppBilinForm b b =
        Λ.strictUpper.finsuppBilinForm b' b' +
          Λ.finsuppBilinForm (Finsupp.single i (b i)) b' := by
      dsimp only [b']
      conv_lhs => rw [← Finsupp.single_add_erase i b]
      simp only [map_add, LinearMap.add_apply, Matrix.finsuppBilinForm_single_single,
        Λ.finsuppBilinForm_strictUpper_single_left_of_lt (b i) hlt,
        Λ.finsuppBilinForm_strictUpper_single_right_eq_zero (b i) fun j hj ↦ (hlt j hj).le,
        Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]
      ring
    calc
      (List.map (fun j ↦ U j ^ b j) (i :: tl)).prod
        = M.monomial (Finsupp.single i (b i)) *
            (Units.map (algebraMap R B) (u ^ Λ.strictUpper.finsuppBilinForm b' b') *
              M.monomial b') := by
          rw [List.map_cons, List.prod_cons, hU_single, hmap, ih hl.2 b' hb']
      _ = Units.map (algebraMap R B)
            (u ^ Λ.strictUpper.finsuppBilinForm b' b' *
              u ^ Λ.finsuppBilinForm (Finsupp.single i (b i)) b') *
            M.monomial b := by
          rw [Units.mul_map_algebraMap_mul, M.monomial_mul,
            Units.map_algebraMap_mul_map_algebraMap, Finsupp.single_add_erase i b]
      _ = Units.map (algebraMap R B) (u ^ Λ.strictUpper.finsuppBilinForm b b) * M.monomial b := by
          rw [← zpow_add, ← hup]

section OfCoordinates

variable [LinearOrder I] {u : Rˣ} {Λ : Matrix I I ℤ} (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
  (hU : ∀ i j, U i * U j = Units.map (algebraMap R B) (u ^ (2 * Λ i j)) * (U j * U i))

/-- Construct a based chart from `(u, 2 • Λ)`-quasi-commuting coordinates whose normalized ordered
products are `R`-linearly independent. -/
noncomputable def ofCoordinates
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) :
    BasedChart u Λ.finsuppBilinForm B where
  monomial := orderedMonomial u Λ U
  monomial_zero := orderedMonomial_zero u Λ U
  monomial_mul := orderedMonomial_mul hΛ hU
  linearIndependent := hli

@[simp]
theorem ofCoordinates_monomial
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) (a : I →₀ ℤ) :
    (ofCoordinates hΛ U hU hli).monomial a = orderedMonomial u Λ U a :=
  (rfl)

@[simp]
theorem coordinate_ofCoordinates
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) (i : I) :
    (ofCoordinates hΛ U hU hli).coordinate Finsupp.basisSingleOne i = U i := by
  simp [coordinate_def]

end OfCoordinates

end TauCeti.BasedChart
