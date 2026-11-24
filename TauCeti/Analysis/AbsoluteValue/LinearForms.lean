/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.Order.AbsoluteValue.Basic

/-!
# Local bounds for linear forms and dot products

For an absolute value `v` on a ring or field, this file records local estimates relating
coordinate bounds, dot-product pairings `y ⬝ᵥ x`, and evaluations of linear forms `l i x`.

* At a nonarchimedean absolute value, entrywise bounds on two finite tuples multiply to bound their
  dot product (`AbsoluteValue.apply_dotProduct_le_mul_of_isNonarchimedean`); in particular, the unit
  ball of `ι → R` is closed under dot products
  (`AbsoluteValue.apply_dotProduct_le_one_of_isNonarchimedean`).
* Whenever a linear form `φ` lies in the span of a set `F` of linear forms on a module `E`, a
  constant `B ≥ 1` independent of `x` and `M` bounds `v (φ x)` by `B * M` whenever `v (f x) ≤ M` on
  `F` (`AbsoluteValue.exists_one_le_forall_apply_le_mul_of_mem_span`). In coordinates, this yields
  the same bound for `v (z ⬝ᵥ x)` when `z` lies in the span of the coefficient vectors
  `j ↦ l i (Pi.basisFun R ι j)` of a subfamily of linear forms
  (`AbsoluteValue.exists_one_le_forall_dotProduct_le_mul`).
* Whenever a family of linear forms `l : κ → Module.Dual R (ι → R)` spans the dual space, a
  constant `C ≥ 1` bounds every coordinate `v (x j)` by `C * M` whenever `v (l k x) ≤ M` for all
  `k`, at an absolute value with values in any ordered semiring; the family may be infinite
  (`AbsoluteValue.exists_one_le_forall_apply_le_mul`). For a finite family and real values, `C`
  bounds every coordinate by `C * ⨆ i, v (l i x)`
  (`AbsoluteValue.exists_one_le_forall_apply_le_mul_iSup`).

In Diophantine approximation over a number field, these single-place estimates convert bounds on
linear forms at archimedean and finite places into bounds on pairings with span vectors and on
coordinates of domain points.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §7.5.
* J.-H. Evertse, *An improvement of the quantitative Subspace Theorem*, Compos. Math. **101**
  (1996), Lemma 27.
-/

public section

namespace AbsoluteValue

/-- For a nonarchimedean absolute value `v`, entrywise bounds `v (y j) ≤ a` and `v (x j) ≤ b`
(`0 ≤ a`, `0 ≤ b`) pass to the dot product: `v (y ⬝ᵥ x) ≤ a * b`. -/
theorem apply_dotProduct_le_mul_of_isNonarchimedean {R S ι : Type*} [Semiring R] [Semiring S]
    [LinearOrder S] [IsOrderedRing S] [Fintype ι] (v : AbsoluteValue R S)
    (hv : IsNonarchimedean v) {a b : S} (ha : 0 ≤ a) (hb : 0 ≤ b) {y x : ι → R}
    (hy : ∀ j, v (y j) ≤ a) (hx : ∀ j, v (x j) ≤ b) :
    v (y ⬝ᵥ x) ≤ a * b := by
  rw [dotProduct]
  refine (v.apply_sum_le_pow_mul (c := 1) le_rfl (fun u w ↦ by simpa only [one_mul] using hv u w)
    Finset.univ _ (mul_nonneg ha hb) fun j _ ↦ ?_).trans_eq (by simp)
  rw [map_mul]
  exact mul_le_mul (hy j) (hx j) (v.nonneg _) ha

/-- For a nonarchimedean absolute value `v`, the dot product of two tuples in the unit ball lies in
the unit ball. -/
theorem apply_dotProduct_le_one_of_isNonarchimedean {R S ι : Type*} [Semiring R] [Semiring S]
    [LinearOrder S] [IsOrderedRing S] [Fintype ι] (v : AbsoluteValue R S)
    (hv : IsNonarchimedean v) {y x : ι → R} (hy : ∀ j, v (y j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) :
    v (y ⬝ᵥ x) ≤ 1 :=
  (v.apply_dotProduct_le_mul_of_isNonarchimedean hv zero_le_one zero_le_one hy hx).trans_eq
    (one_mul 1)

/-- If a linear form `φ` lies in the span of a set `F` of linear forms on `E`, then some constant
`B ≥ 1` (depending only on `v`, `F`, and `φ`) bounds `v (φ x)` by `B * M` whenever `0 ≤ M` and
`v (f x) ≤ M` for all `f ∈ F`. -/
theorem exists_one_le_forall_apply_le_mul_of_mem_span {R S E : Type*} [CommSemiring R]
    [Semiring S] [LinearOrder S] [IsOrderedRing S] [AddCommMonoid E] [Module R E]
    (v : AbsoluteValue R S) {F : Set (Module.Dual R E)} {φ : Module.Dual R E}
    (hφ : φ ∈ Submodule.span R F) :
    ∃ B : S, 1 ≤ B ∧ ∀ ⦃M : S⦄, 0 ≤ M → ∀ ⦃x : E⦄,
      (∀ f ∈ F, v (f x) ≤ M) → v (φ x) ≤ B * M := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
  · intro f hf
    exact ⟨1, le_rfl, fun M _ x hx ↦ by rw [one_mul]; exact hx f hf⟩
  · exact ⟨1, le_rfl, fun M hM _ _ ↦ by
      simpa only [LinearMap.zero_apply, AbsoluteValue.map_zero, one_mul] using hM⟩
  · rintro φ₁ φ₂ - - ⟨B₁, hB₁, h₁⟩ ⟨B₂, hB₂, h₂⟩
    refine ⟨B₁ + B₂, hB₁.trans (le_add_of_nonneg_right (zero_le_one.trans hB₂)),
      fun M hM x hx ↦ ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (v.add_le _ _).trans (add_le_add (h₁ hM hx) (h₂ hM hx))
  · rintro r φ - ⟨B, _, h⟩
    refine ⟨max (v r * B) 1, le_max_right _ _, fun M hM x hx ↦ ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, map_mul]
    calc v r * v (φ x)
        ≤ v r * (B * M) := mul_le_mul_of_nonneg_left (h hM hx) (v.nonneg _)
      _ = v r * B * M := (mul_assoc _ _ _).symm
      _ ≤ max (v r * B) 1 * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM

/-- If `z` lies in the span of the coefficient vectors `j ↦ l i (Pi.basisFun R ι j)` of the forms
`l i` with `i ∈ s`, then some constant `B ≥ 1` (depending only on `v`, `l`, `s`, and `z`) bounds
`v (z ⬝ᵥ x)` by `B * M` whenever `0 ≤ M` and `v (l i x) ≤ M` for all `i ∈ s`. -/
theorem exists_one_le_forall_dotProduct_le_mul {R S ι κ : Type*} [CommSemiring R] [Semiring S]
    [LinearOrder S] [IsOrderedRing S] [Fintype ι] (v : AbsoluteValue R S)
    (l : κ → Module.Dual R (ι → R)) (s : Set κ) {z : ι → R}
    (hz : z ∈ Submodule.span R ((fun i j ↦ l i (Pi.basisFun R ι j)) '' s)) :
    ∃ B : S, 1 ≤ B ∧ ∀ ⦃M : S⦄, 0 ≤ M → ∀ ⦃x : ι → R⦄,
      (∀ i ∈ s, v (l i x) ≤ M) → v (z ⬝ᵥ x) ≤ B * M := by
  have hmap : dotProductBilin R R z ∈ Submodule.span R (l '' s) := by
    have hmem := Submodule.apply_mem_span_image_of_mem_span (dotProductBilin R R) hz
    have himg : dotProductBilin R R '' ((fun i j ↦ l i (Pi.basisFun R ι j)) '' s) =
        l '' s := by
      rw [← Set.image_comp]
      refine Set.image_congr fun i _ ↦ ?_
      ext x
      conv_rhs => rw [← (Pi.basisFun R ι).sum_repr x, map_sum]
      simp [dotProduct, mul_comm]
    rwa [himg] at hmem
  obtain ⟨B, hB1, hB⟩ := v.exists_one_le_forall_apply_le_mul_of_mem_span hmap
  exact ⟨B, hB1, fun M hM x hx ↦ hB hM fun _ ⟨i, hi, hf⟩ ↦ hf ▸ hx i hi⟩

/-- At any real-valued absolute value where a finite family of linear forms `l` on `ι → R` spans
the dual space, some `C ≥ 1` bounds every coordinate `v (x j)` by `C * ⨆ i, v (l i x)`. -/
theorem exists_one_le_forall_apply_le_mul_iSup {R ι κ : Type*} [CommSemiring R] [Finite ι]
    [Finite κ] (v : AbsoluteValue R ℝ) {l : κ → Module.Dual R (ι → R)}
    (hl : Submodule.span R (Set.range l) = ⊤) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : ι → R) (j : ι), v (x j) ≤ C * ⨆ i, v (l i x) := by
  choose B _ hB using fun j : ι ↦
    v.exists_one_le_forall_apply_le_mul_of_mem_span
      (hl ▸ Submodule.mem_top : LinearMap.proj (R := R) (φ := fun _ : ι ↦ R) j ∈ _)
  refine ⟨max 1 (⨆ j, B j), le_max_left _ _, fun x j ↦ ?_⟩
  have : Nonempty ι := ⟨j⟩
  have hM0 : 0 ≤ ⨆ i, v (l i x) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine (hB j hM0 fun _ ⟨i, hf⟩ ↦ hf ▸ Finite.le_ciSup_of_le i le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_right ((Finite.le_ciSup_of_le j le_rfl).trans (le_max_right _ _)) hM0

/-- If linear forms `l k` span the dual of `R^ι`, then some constant `C ≥ 1` (depending only on `v`
and `l`) bounds every coordinate `v (x j)` by `C * M` whenever `0 ≤ M` and `v (l k x) ≤ M` for all
`k`. The family `l` may be infinite: each coordinate only uses finitely many of the forms. -/
theorem exists_one_le_forall_apply_le_mul {R S ι κ : Type*} [CommSemiring R] [Semiring S]
    [PartialOrder S] [IsOrderedRing S] [Finite ι] (v : AbsoluteValue R S)
    {l : κ → Module.Dual R (ι → R)} (hl : Submodule.span R (Set.range l) = ⊤) :
    ∃ C : S, 1 ≤ C ∧ ∀ ⦃M : S⦄, 0 ≤ M → ∀ ⦃x : ι → R⦄, (∀ k, v (l k x) ≤ M) →
      ∀ j, v (x j) ≤ C * M := by
  have := Fintype.ofFinite ι
  -- Write each coordinate form as a finite combination of the forms `l k`.
  choose a ha using fun j : ι ↦ Finsupp.mem_span_range_iff_exists_finsupp.mp
    (hl ▸ Submodule.mem_top : LinearMap.proj (φ := fun _ : ι ↦ R) j ∈ _)
  refine ⟨1 + ∑ j, ∑ k ∈ (a j).support, v (a j k),
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ v.nonneg _),
    fun M hM x hx j ↦ ?_⟩
  have hxj : x j = ∑ k ∈ (a j).support, a j k * l k x := by
    simpa [Finsupp.sum] using (LinearMap.congr_fun (ha j) x).symm
  calc v (x j) ≤ ∑ k ∈ (a j).support, v (a j k) * v (l k x) := by
        rw [hxj]
        exact (v.sum_le _ _).trans_eq (by simp only [map_mul])
    _ ≤ ∑ k ∈ (a j).support, v (a j k) * M :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hx k) (v.nonneg _)
    _ = (∑ k ∈ (a j).support, v (a j k)) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 + ∑ j, ∑ k ∈ (a j).support, v (a j k)) * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        refine (Finset.single_le_sum (f := fun j ↦ ∑ k ∈ (a j).support, v (a j k))
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ v.nonneg _) (Finset.mem_univ j)).trans ?_
        exact le_add_of_nonneg_left zero_le_one

end AbsoluteValue
