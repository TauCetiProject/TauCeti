/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import TauCeti.Algebra.Lie.Current.Basic
public import TauCeti.RingTheory.LaurentSeries.ResiduePairing

/-!
# The residue 2-cocycle on formal currents

For a bilinear form `Φ` on a Lie algebra `L` over a commutative ring `R`, the residue pairing on
formal currents `R⸨X⸩ ⊗[R] L` is

`(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)`,

the tensor product of the Laurent residue pairing `LaurentSeries.residuePairing` with `Φ`. It has
the finite coefficient formula `(u, v) ↦ ∑ n Φ(u₋ₙ, vₙ)`, where `uₖ` is the `L`-valued coefficient
of `Xᵏ` and only finitely many `n` contribute, because both currents have finite lower order. When
`Φ` is symmetric the pairing is alternating, hence a 2-cochain with trivial coefficients, and when
`Φ` is moreover invariant it is a 2-cocycle. Its restriction to polynomial currents is Mathlib's
residue pairing `LieAlgebra.LoopAlgebra.residuePairing` on `loopAlgebra R ℤ L`, and so its cochain
restricts to Mathlib's `LieAlgebra.LoopAlgebra.twoCochainOfBilinear`.

The pairing vanishes on currents of orders at least `M` and `N` with `M + N > 0`, and on two
currents of nonnegative order. In particular every current pairs to zero with all currents of
sufficiently high order, and the pairing vanishes on the positive currents, those of order at
least zero.

The sign convention is Mathlib's: on modes `x_m = Xᵐ ⊗ x`, the pairing is
`(x_m, y_n) ↦ n Φ(x, y) δ_{m + n, 0}`. The central extension cocycle `c_κ = -κ(x, y) Res(f dg)`
of an invariant symmetric form `κ` is the cocycle attached here to `Φ = -κ`.

## Main results

* `TauCeti.CurrentAlgebra.residuePairing`: the residue pairing on formal currents.
* `TauCeti.CurrentAlgebra.residuePairing_eq_sum`: its finite coefficient formula.
* `TauCeti.CurrentAlgebra.residuePairing_ofLoop`: its restriction to polynomial currents.
* `TauCeti.CurrentAlgebra.residuePairing_eq_zero_of_mem_orderSubmodule`: vanishing on currents of
  orders summing to a positive integer.
* `TauCeti.CurrentAlgebra.residuePairing_lie`: the 2-cocycle identity for an invariant form.
* `TauCeti.CurrentAlgebra.twoCochainOfBilinear`: the alternating 2-cochain of a symmetric form.
* `TauCeti.CurrentAlgebra.twoCocycleOfBilinear`: the 2-cocycle of an invariant symmetric form.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the residue cocycle
  defining the affine central extension.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the residue cocycle on the
  formal loop algebra `g((t))`.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

open _root_.LieModule.Cohomology

variable (R L : Type*) [CommRing R]

-- The coefficientwise algebra structure matches the module used by the tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

section Module

variable [AddCommGroup L] [Module R L] (Φ : LinearMap.BilinForm R L)

/-- The residue pairing `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` on formal currents. -/
def residuePairing : LinearMap.BilinForm R (currentAlgebra R L) :=
  (LaurentSeries.residuePairing R).tmul Φ

/-- The residue pairing on pure tensors. -/
@[simp]
theorem residuePairing_tmul (f g : R⸨X⸩) (x y : L) :
    residuePairing R L Φ (f ⊗ₜ x) (g ⊗ₜ y) = LaurentSeries.residuePairing R f g * Φ x y := by
  rw [residuePairing, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

/-- The residue pairing of the zero form is zero. -/
@[simp]
theorem residuePairing_zero : residuePairing R L 0 = 0 := by
  simp [residuePairing, LinearMap.BilinForm.tmul]

/-- The residue pairing is linear in the form: rescaling the form rescales the pairing. -/
@[simp]
theorem residuePairing_smul (r : R) : residuePairing R L (r • Φ) = r • residuePairing R L Φ := by
  simp [residuePairing, LinearMap.BilinForm.tmul]

/-- The finite coefficient formula for the residue pairing: if `u` has order at least `M` and `v`
has order at least `N`, then the pairing is `∑_{N ≤ n ≤ -M} n Φ(u₋ₙ, vₙ)`. -/
theorem residuePairing_eq_sum {M N : ℤ} {u v : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L M) (hv : v ∈ orderSubmodule R L N) :
    residuePairing R L Φ u v =
      ∑ n ∈ Finset.Icc N (-M), n • Φ (coeff R L (-n) u) (coeff R L n v) := by
  -- Both sides are bilinear in `(u, v)`, so it suffices to compare them on spanning tensors.
  let B : LinearMap.BilinForm R (currentAlgebra R L) :=
    ∑ n ∈ Finset.Icc N (-M), n • Φ.compl₁₂ (coeff R L (-n)) (coeff R L n)
  have hB (u v : currentAlgebra R L) :
      B u v = ∑ n ∈ Finset.Icc N (-M), n • Φ (coeff R L (-n) u) (coeff R L n v) := by
    simp [B, LinearMap.sum_apply]
  rw [← hB]
  rw [orderSubmodule_def] at hu hv
  refine LinearMap.eqOn_span (f := (residuePairing R L Φ).flip v) (g := B.flip v)
    (fun u hu ↦ ?_) hu
  obtain ⟨f, x, hf, rfl⟩ := hu
  refine LinearMap.eqOn_span (f := residuePairing R L Φ (f ⊗ₜ x)) (g := B (f ⊗ₜ x))
    (fun w hw ↦ ?_) hv
  obtain ⟨g, y, hg, rfl⟩ := hw
  rw [hB, residuePairing_tmul, LaurentSeries.residuePairing_eq_sum R hf hg, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [coeff_tmul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_mul_assoc]
  ring

/-- The residue pairing vanishes on currents of orders at least `M` and `N` when `M + N > 0`. -/
theorem residuePairing_eq_zero_of_mem_orderSubmodule {M N : ℤ} {u v : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L M) (hv : v ∈ orderSubmodule R L N) (hMN : 0 < M + N) :
    residuePairing R L Φ u v = 0 := by
  rw [residuePairing_eq_sum R L Φ hu hv, Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- The residue pairing vanishes on two currents of nonnegative order. -/
theorem residuePairing_eq_zero_of_mem_orderSubmodule_zero {u v : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L 0) (hv : v ∈ orderSubmodule R L 0) :
    residuePairing R L Φ u v = 0 := by
  rw [residuePairing_eq_sum R L Φ hu hv, neg_zero, Finset.Icc_self, Finset.sum_singleton,
    zero_smul]

/-- Every current pairs to zero with all currents of sufficiently high order. -/
theorem exists_orderSubmodule_le_ker_residuePairing (u : currentAlgebra R L) :
    ∃ N : ℤ, orderSubmodule R L N ≤ LinearMap.ker (residuePairing R L Φ u) := by
  obtain ⟨M, hu⟩ := exists_mem_orderSubmodule R L u
  exact ⟨1 - M, fun v hv ↦ residuePairing_eq_zero_of_mem_orderSubmodule R L Φ hu hv (by omega)⟩

variable {Φ}

/-- The residue pairing of a symmetric form is skew-symmetric. -/
theorem residuePairing_eq_neg_swap (hΦ : Φ.IsSymm) (u v : currentAlgebra R L) :
    residuePairing R L Φ u v = -residuePairing R L Φ v u := by
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    induction v using TensorProduct.inductionOn with
    | tmul g y =>
      rw [residuePairing_tmul, residuePairing_tmul, LaurentSeries.residuePairing_eq_neg_swap R f g,
        hΦ.eq x y, neg_mul]
    | add v w hv hw => simp [hv, hw, add_comm]
  | add u w hu hw => simp [hu, hw, add_comm]

/-- The residue pairing of a symmetric form is alternating, over every commutative ring. -/
@[simp]
theorem residuePairing_self (hΦ : Φ.IsSymm) (u : currentAlgebra R L) :
    residuePairing R L Φ u u = 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul f x => simp
  | add u v hu hv =>
    simp [hu, hv, residuePairing_eq_neg_swap R L hΦ v u]

end Module

section Lie

variable [LieRing L] [LieAlgebra R L] {Φ : LinearMap.BilinForm R L}

/-- The residue pairing of an invariant form satisfies the 2-cocycle identity with trivial
coefficients. -/
theorem residuePairing_lie (hΦ : Φ.lieInvariant L) (u v w : currentAlgebra R L) :
    residuePairing R L Φ u ⁅v, w⁆ =
      residuePairing R L Φ ⁅u, v⁆ w + residuePairing R L Φ v ⁅u, w⁆ := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, add_lie, hu, hu']; abel
  | tmul f x =>
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, lie_add, add_lie, hv, hv']; abel
  | tmul g y =>
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [map_add, lie_add, hw, hw']; abel
  | tmul h z =>
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, residuePairing_tmul]
  -- By invariance, all three values of `Φ` are `±Φ(⁅x, y⁆, z)`.
  have h₁ : Φ x ⁅y, z⁆ = Φ ⁅x, y⁆ z := by
    rw [← neg_neg (Φ x _), ← hΦ, ← lie_skew, LinearMap.map_neg, LinearMap.neg_apply, neg_neg]
  have h₂ : Φ y ⁅x, z⁆ = -Φ ⁅x, y⁆ z := by rw [hΦ, neg_neg]
  have e₁ := LaurentSeries.residuePairing_mul_right R f g h
  have e₂ := LaurentSeries.residuePairing_mul_right R g f h
  have e₃ := LaurentSeries.residuePairing_mul_add_cyclic R f g h
  rw [mul_comm h f] at e₃
  rw [mul_comm g f] at e₂
  rw [h₁, h₂]
  linear_combination Φ ⁅x, y⁆ z * (e₁ + e₂ + e₃)

/-- The residue pairing restricts to Mathlib's residue pairing on polynomial currents. -/
@[simp]
theorem residuePairing_ofLoop (Φ : LinearMap.BilinForm R L)
    (u v : _root_.LieAlgebra.loopAlgebra R ℤ L) :
    residuePairing R L Φ (ofLoop R L u) (ofLoop R L v) =
      _root_.LieAlgebra.LoopAlgebra.residuePairing R ℤ L Φ u v := by
  obtain ⟨u, rfl⟩ := (_root_.LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).symm.surjective u
  obtain ⟨v, rfl⟩ := (_root_.LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).symm.surjective v
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | single m x =>
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | single n y =>
  simp only [_root_.LieAlgebra.LoopAlgebra.toFinsupp_symm_single, ofLoop_tmul,
    residuePairing_tmul, _root_.LieAlgebra.LoopAlgebra.residuePairing_apply_apply,
    _root_.LieAlgebra.LoopAlgebra.toFinsupp_single_tmul]
  rw [LaurentPolynomial.toLaurentSeries_single, LaurentPolynomial.toLaurentSeries_single,
    LaurentSeries.residuePairing_single, Finsupp.sum_single_index (by simp), Finsupp.single_apply]
  -- Both sides test the same condition, `m + n = 0` on the left and `m = -n` on the right.
  by_cases h : m + n = 0
  · have hm : m = -n := by omega
    simp [hm]
  · have hm : m ≠ -n := by omega
    simp [h, hm]

/-- The alternating residue 2-cochain with trivial coefficients attached to a symmetric bilinear
form on `L`: `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)`. -/
def twoCochainOfBilinear (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) :
    twoCochain R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) where
  val := (residuePairing R L Φ).compr₂ (TrivialLieModule.equiv R (currentAlgebra R L) R).symm
  property := mem_twoCochain_iff.mpr fun u ↦ by simp [residuePairing_self R L hΦ u]

/-- The values of the residue cochain are those of the residue pairing. -/
@[simp]
theorem twoCochainOfBilinear_apply_apply (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm)
    (u v : currentAlgebra R L) :
    twoCochainOfBilinear R L Φ hΦ u v =
      (TrivialLieModule.equiv R (currentAlgebra R L) R).symm (residuePairing R L Φ u v) :=
  (rfl)

/-- The residue cochain restricts to Mathlib's residue cochain on polynomial currents. -/
theorem twoCochainOfBilinear_ofLoop [HasUniqueDiv R] (Φ : LinearMap.BilinForm R L)
    (hΦ : Φ.IsSymm) (u v : _root_.LieAlgebra.loopAlgebra R ℤ L) :
    TrivialLieModule.equiv R (currentAlgebra R L) R
        (twoCochainOfBilinear R L Φ hΦ (ofLoop R L u) (ofLoop R L v)) =
      TrivialLieModule.equiv R (_root_.LieAlgebra.loopAlgebra R ℤ L) R
        (_root_.LieAlgebra.LoopAlgebra.twoCochainOfBilinear R ℤ L Φ hΦ u v) := by
  simp

/-- The residue 2-cocycle with trivial coefficients attached to an invariant symmetric bilinear
form on `L`. For `Φ = -κ` it is the cocycle `-κ(x, y) Res(f dg)` defining the affine central
extension of level `κ`. -/
def twoCocycleOfBilinear (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) :
    twoCocycle R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) where
  val := twoCochainOfBilinear R L Φ hΦs
  property := (mem_twoCocycle_iff_of_trivial _ _ _ _).mpr fun u v w ↦ by
    simp only [twoCochainOfBilinear_apply_apply, residuePairing_lie R L hΦ u v w, map_add]

/-- The underlying cochain of the residue cocycle is the residue cochain. -/
@[simp]
theorem twoCocycleOfBilinear_coe (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) :
    (twoCocycleOfBilinear R L Φ hΦ hΦs : twoCochain R (currentAlgebra R L)
      (TrivialLieModule R (currentAlgebra R L) R)) = twoCochainOfBilinear R L Φ hΦs :=
  (rfl)

/-- Rescaling the form rescales the residue cocycle. -/
theorem twoCocycleOfBilinear_smul (r : R) (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (hrΦ : (r • Φ).lieInvariant L) (hrΦs : (r • Φ).IsSymm) :
    twoCocycleOfBilinear R L (r • Φ) hrΦ hrΦs = r • twoCocycleOfBilinear R L Φ hΦ hΦs := by
  refine Subtype.ext <| Subtype.ext <| LinearMap.ext₂ fun u v ↦ ?_
  simpa using map_smul (TrivialLieModule.equiv R (currentAlgebra R L) R).symm r
    (residuePairing R L Φ u v)

end Lie

end TauCeti.CurrentAlgebra
