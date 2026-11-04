/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.LeftIdeal
public import TauCeti.Algebra.Lie.Current.SmoothAction
public import TauCeti.Algebra.Vertex.VertexOperator

/-!
# Current fields on smooth modules

Let `σ` be a smooth action of the formal currents `L((t)) = R⸨X⸩ ⊗[R] L` on a module `M`
(`TauCeti.CurrentAlgebra.IsSmooth`): every vector is killed by the currents of some order. For
`x : L` write `xₙ = x ⊗ tⁿ` for its modes. The *current field* of `x` is the formal series

`J^x(z) = ∑ₙ σ(xₙ) z^{-n-1}`,

a vertex operator on `M` in the sense of Mathlib's `VertexOperator`
(`TauCeti.CurrentAlgebra.currentField`): its normalized coefficients are `J^x[[n]] = σ(xₙ)`. It is a
field because smoothness gives, for each vector `m`, a cutoff `N` with `σ(xₙ) m = 0` for all `x`
and all `n ≥ N`. The current field depends linearly on `x`.

Suppose now that `σ` satisfies the commutator relations of the residue central extension of a
bilinear form `Φ` at the central value `a`,

`[σ u, σ v] = σ ⁅u, v⁆ + a Res(u dv)`,

which are the relations defining the modules over `U(ĝ) / (ι K - a)`
(`TauCeti.CurrentAlgebra.liftOfCurrents`). On modes the residue `Res(tᵐ d tⁿ)` is `n` if
`m + n = 0` and `0` otherwise, so the coefficients of current fields satisfy

`[J^x[[m]], J^y[[n]]] = J^{⁅x, y⁆}[[m + n]] + a n δ_{m + n, 0} Φ(x, y)`

(`TauCeti.CurrentAlgebra.ncoeff_currentField_mul_sub_mul`). With the affine level form `κ = -Φ`
this is the familiar relation `[xₘ, yₙ] = [x, y]ₘ₊ₙ + m κ(x, y) δ_{m + n, 0} K` with `K = a`.
Equivalently, as formal distributions,

`[J^x(z), J^y(w)] = J^{⁅x, y⁆}(w) δ(z - w) - a Φ(x, y) ∂_w δ(z - w)`,

which is killed by `(z - w)²`: any two current fields are mutually local of order `2`
(`TauCeti.CurrentAlgebra.isLocalOfOrder_currentField`), in the coefficientwise sense of
`VertexOperator.IsLocalOfOrder`.

The commutator relations hold for the action `TauCeti.CurrentAlgebra.envelopingAction` of the
current generators on any module over `U(ĝ) / (ι K - a)`, and smoothness of this action is
smoothness of the module for the left ideals `I_N` of high-order currents
(`TauCeti.CurrentAlgebra.isSmooth_envelopingAction_iff`). So every smooth module at a fixed level,
for example each quotient `U / I_N`, carries mutually local current fields. No finiteness of `L`
and no topology are used: each coefficient of each field applied to a vector is a single operator.

## Main definitions

* `TauCeti.CurrentAlgebra.currentField`: the current field `J^x(z)` of a smooth action.

## Main results

* `TauCeti.CurrentAlgebra.ncoeff_currentField`: the coefficients of `J^x(z)` are the modes of `x`.
* `TauCeti.CurrentAlgebra.exists_forall_ncoeff_currentField_apply_eq_zero`: the fields are
  truncated uniformly in `x`.
* `TauCeti.CurrentAlgebra.ncoeff_currentField_mul_sub_mul`: the commutator formula.
* `TauCeti.CurrentAlgebra.isLocalOfOrder_currentField`: current fields are mutually local of
  order `2`.

## References

* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4, for the current
  fields of an affine Kac--Moody algebra and their locality.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.2 and §3.1.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.5.
* S. Carnahan, leanprover-community/mathlib4#25822, a prospective Mathlib development of vertex
  algebras, which sketches the affine vertex operator `of_coeff fun n v => x t^n • v` built here
  as `TauCeti.CurrentAlgebra.currentField` and states that these fields are mutually local.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries VertexOperator
open Finset
open LieAlgebra.ofTwoCocycle (centralElement)

attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

section Field

variable (σ : currentAlgebra R L →ₗ[R] Module.End R M) (hσ : IsSmooth σ)

include hσ

/-- A smooth action kills every vector by all modes of large order, uniformly in the element of
`L`. -/
private theorem exists_forall_apply_single_tmul_eq_zero (m : M) :
    ∃ N : ℤ, ∀ x : L, ∀ n, N ≤ n → σ (HahnSeries.single n 1 ⊗ₜ x) m = 0 := by
  obtain ⟨N, hN⟩ := isSmooth_iff.1 hσ m
  exact ⟨N, fun x n hn ↦ hN _ (tmul_mem_orderSubmodule R L N
    ((HahnSeries.orderTop_single_le).trans' (by exact_mod_cast hn)) x)⟩

/-- The coefficients `z^k ↦ σ(x_{-k-1})` of a current field have support bounded below at each
vector. -/
private theorem bddBelow_support_apply_single_tmul (x : L) (m : M) :
    BddBelow (Function.support fun k : ℤ ↦ σ (HahnSeries.single (-k - 1) 1 ⊗ₜ x) m) := by
  obtain ⟨N, hN⟩ := exists_forall_apply_single_tmul_eq_zero σ hσ m
  refine ⟨-N, fun k hk ↦ ?_⟩
  by_contra! h
  exact hk (hN x _ (by lia))

/-- The **current field** `J^x(z) = ∑ₙ σ(xₙ) z^{-n-1}` of `x : L` for a smooth action `σ` of the
formal currents, where `xₙ = x ⊗ tⁿ`. Its normalized coefficients are `J^x[[n]] = σ(xₙ)`
(`TauCeti.CurrentAlgebra.ncoeff_currentField`). -/
def currentField : L →ₗ[R] VertexOperator R M where
  toFun x := VertexOperator.of_coeff (fun k ↦ σ (HahnSeries.single (-k - 1) 1 ⊗ₜ x))
    (bddBelow_support_apply_single_tmul σ hσ x)
  map_add' x y := VertexOperator.ext_ncoeff fun n ↦ by
    simp [TensorProduct.tmul_add]
  map_smul' r x := VertexOperator.ext_ncoeff fun n ↦ by
    simp [TensorProduct.tmul_smul]

/-- The normalized coefficients of the current field of `x` are the modes `xₙ = x ⊗ tⁿ`. -/
@[simp]
theorem ncoeff_currentField (x : L) (n : ℤ) :
    (currentField σ hσ x)[[n]] = σ (HahnSeries.single n 1 ⊗ₜ x) := by
  simp [currentField]

/-- **Truncation.** For each vector `m` there is a cutoff `N` such that `J^x[[n]] m = 0` for every
`x` and every `n ≥ N`. -/
theorem exists_forall_ncoeff_currentField_apply_eq_zero (m : M) :
    ∃ N : ℤ, ∀ x : L, ∀ n, N ≤ n → ((currentField σ hσ x)[[n]]) m = 0 := by
  simpa using exists_forall_apply_single_tmul_eq_zero σ hσ m

end Field

section Commutator

variable (Φ : LinearMap.BilinForm R L) (a : R) {σ : currentAlgebra R L →ₗ[R] Module.End R M}
  (hσ : IsSmooth σ)
  (hσc : ∀ u v, σ u * σ v - σ v * σ u =
    σ ⁅u, v⁆ + algebraMap R (Module.End R M) (a * residuePairing R L Φ u v))

include hσc in
/-- **The commutator formula.** If `σ` satisfies the commutator relations of the residue central
extension of `Φ` at the central value `a`, then
`[J^x[[m]], J^y[[n]]] = J^{⁅x, y⁆}[[m + n]] + a n δ_{m + n, 0} Φ(x, y)`. -/
theorem ncoeff_currentField_mul_sub_mul (x y : L) (m n : ℤ) :
    (currentField σ hσ x)[[m]] * (currentField σ hσ y)[[n]] -
        (currentField σ hσ y)[[n]] * (currentField σ hσ x)[[m]] =
      (currentField σ hσ ⁅x, y⁆)[[m + n]] +
        algebraMap R (Module.End R M) (if m + n = 0 then a * n * Φ x y else 0) := by
  simp only [ncoeff_currentField, hσc, LieAlgebra.ExtendScalars.bracket_tmul,
    HahnSeries.single_mul_single, mul_one, residuePairing_tmul,
    LaurentSeries.residuePairing_single]
  split_ifs <;> simp [mul_assoc]

include hσc in
/-- **Locality.** If `σ` satisfies the commutator relations of a residue central extension, then
any two current fields are mutually local of order `2`: `(z - w)² [J^x(z), J^y(w)] = 0`. -/
theorem isLocalOfOrder_currentField (x y : L) :
    (currentField σ hσ x).IsLocalOfOrder (currentField σ hσ y) 2 := by
  refine VertexOperator.isLocalOfOrder_iff.2 fun m n ↦ ?_
  -- All three index pairs `(m + i, n + j)` with `i + j = 2` have the same sum `m + n + 2`.
  have hmn (i j : ℕ) (h : i + j = 2) : m + i + (n + j) = m + n + 2 := by lia
  simp only [Nat.sum_antidiagonal_succ, Nat.antidiagonal_zero, sum_singleton,
    ncoeff_currentField_mul_sub_mul Φ a hσ hσc, hmn]
  -- The central terms are integer multiples of `a Φ(x, y)`.
  have hc (k : ℤ) : algebraMap R (Module.End R M) (a * k * Φ x y) =
      k • algebraMap R (Module.End R M) (a * Φ x y) := by
    rw [mul_comm a, mul_assoc, ← zsmul_eq_mul, map_zsmul]
  split_ifs <;>
  · simp only [hc, map_zero, add_zero, zero_add, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self]
    module

end Commutator

section Enveloping

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => UniversalEnvelopingAlgebra.CentralQuotient R (centralElement c) a

variable [Module (UniversalEnvelopingAlgebra.CentralQuotient R
    (centralElement (twoCocycleOfBilinear R L Φ hΦ hΦs)) a) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra.CentralQuotient R
    (centralElement (twoCocycleOfBilinear R L Φ hΦ hΦs)) a) M]

/-- The action of the currents on a module over `U(ĝ) / (ι K - a)` is smooth exactly when the
module is smooth for the left ideals `I_N` of high-order currents. -/
theorem isSmooth_envelopingAction_iff :
    IsSmooth (envelopingAction (M := M) Φ hΦ hΦs a) ↔
      smoothModules (orderLeftIdeal Φ hΦ hΦs a) (ModuleCat.of UK M) := by
  rw [isSmooth_iff, smoothModules_orderLeftIdeal_iff]
  simp only [envelopingAction_apply]

/-- On a module over `U(ĝ) / (ι K - a)` which is smooth for the left ideals `I_N`, any two current
fields are mutually local of order `2`. -/
theorem isLocalOfOrder_currentField_envelopingAction
    (hM : smoothModules (orderLeftIdeal Φ hΦ hΦs a) (ModuleCat.of UK M)) (x y : L) :
    (currentField _ ((isSmooth_envelopingAction_iff Φ hΦ hΦs a).2 hM) x).IsLocalOfOrder
      (currentField _ ((isSmooth_envelopingAction_iff Φ hΦ hΦs a).2 hM) y) 2 :=
  isLocalOfOrder_currentField Φ a _ (envelopingAction_mul_sub_mul Φ hΦ hΦs a) x y

end Enveloping

end TauCeti.CurrentAlgebra
