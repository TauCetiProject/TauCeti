/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Cycle.Enumeration
public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Signed

/-!
# The integral fixed basis of a signed permutation of a basis

Let `π` be a permutation of `ι` and `s : ι → M` weights in a commutative monoid. Along the cycle
`x, π x, π² x, …` of a point `x`, the cycle coefficients are the prefix products
`c_r = s x * s (π x) * ⋯ * s (π ^ (r - 1) x)` (`Equiv.Perm.cycleCoeff`), and the monodromy of `x`
is `c_l` for the length `l` of its cycle (`Equiv.Perm.monodromy`), the product of `s` over the cycle
(`Equiv.Perm.monodromy_eq_prod`). If a linear endomorphism `f` sends `v i` to `s i • v (π i)`, then
`f ^ r` sends `v x` to `c_r • v (π ^ r x)` (`Module.End.pow_apply_of_apply_eq_units_smul`).

Now let `b` be a basis of a `ℤ`-module indexed by a finite type `ι`, and let
`f (b i) = s i • b (π i)` with signs `s : ι → ℤˣ`. Choose one representative `rep j` on every cycle
of `π`. The fixed submodule of `f` is free over `ℤ` (`Module.Basis.fixedBasisSignedPerm`), with
basis the signed orbit sums `∑_{r < l} c_r • b (π ^ r (rep j))` of the cycles of monodromy `1`
(`Module.Basis.fixedBasisSignedPerm_apply`); the coordinate of a fixed vector at such a cycle is its
coefficient on the representative (`Module.Basis.fixedBasisSignedPerm_repr`). A cycle of monodromy
`-1` carries no integral fixed vector. This is `Module.Basis.fixedBasisSignedFamily` applied to the
enumeration `Equiv.Perm.sigmaCycleEquiv` of `ι` along the cycles of `π`. For an unsigned
permutation of coordinates, compare `Equiv.Perm.permutationFixedBasis`.

## Main definitions

* `Equiv.Perm.cycleCoeff`: the cycle coefficients of a point.
* `Equiv.Perm.monodromy`: the monodromy of a point.
* `Module.Basis.fixedBasisSignedPerm`: the integral basis of the fixed submodule of a signed
  permutation of a basis.

## Main results

* `Equiv.Perm.monodromy_eq_prod`: the monodromy is the product of the weights over the cycle.
* `Module.End.pow_apply_of_apply_eq_units_smul`: the iterates of a weighted permutation of a family
  of vectors.
* `Module.Basis.fixedBasisSignedPerm_apply`, `Module.Basis.fixedBasisSignedPerm_repr`: the basis
  vectors are the signed orbit sums, and the coordinates are the coefficients on the
  representatives.
-/

public section

open Function

namespace Equiv.Perm

variable {α M : Type*} [CommMonoid M] (π : Perm α) (s : α → M)

/-! ### Cycle coefficients and monodromy -/

/-- The cycle coefficient `c_r = s x * s (π x) * ⋯ * s (π ^ (r - 1) x)` of a point `x`: the
product of the weights `s` over the first `r` points of the cycle of `x` under `π`. -/
def cycleCoeff (x : α) (r : ℕ) : M :=
  ∏ k ∈ Finset.range r, s ((π ^ k) x)

theorem cycleCoeff_def (x : α) (r : ℕ) :
    π.cycleCoeff s x r = ∏ k ∈ Finset.range r, s ((π ^ k) x) :=
  (rfl)

@[simp]
theorem cycleCoeff_zero (x : α) : π.cycleCoeff s x 0 = 1 := by
  simp [cycleCoeff_def]

theorem cycleCoeff_succ (x : α) (r : ℕ) :
    π.cycleCoeff s x (r + 1) = π.cycleCoeff s x r * s ((π ^ r) x) := by
  simp [cycleCoeff_def, Finset.prod_range_succ]

@[simp]
theorem cycleCoeff_one (x : α) (r : ℕ) : π.cycleCoeff (1 : α → M) x r = 1 := by
  simp [cycleCoeff_def]

/-- The monodromy of a point `x`: its cycle coefficient at the length
`Function.minimalPeriod π x` of its cycle, which is the product of the weights over the cycle
(`Equiv.Perm.monodromy_eq_prod`). -/
noncomputable def monodromy (x : α) : M :=
  π.cycleCoeff s x (minimalPeriod π x)

theorem monodromy_def (x : α) : π.monodromy s x = π.cycleCoeff s x (minimalPeriod π x) :=
  (rfl)

@[simp]
theorem monodromy_one (x : α) : π.monodromy (1 : α → M) x = 1 :=
  π.cycleCoeff_one x _

/-- The monodromy of a point is the product of the weights over the points of its cycle; in
particular it only depends on the cycle. -/
theorem monodromy_eq_prod [Fintype α] [DecidableRel π.SameCycle] (x : α) :
    π.monodromy s x = ∏ y with π.SameCycle x y, s y :=
  π.prod_range_minimalPeriod s x

section SumCongr

variable {β : Type*} (τ : Perm β) (t : β → M)

/-- The cycle coefficients of a point of the left summand under a sum permutation are those
under the left permutation. -/
@[simp]
theorem cycleCoeff_sumCongr_inl (x : α) (r : ℕ) :
    (sumCongr π τ).cycleCoeff (Sum.elim s t) (.inl x) r = π.cycleCoeff s x r := by
  simp [cycleCoeff_def]

/-- The cycle coefficients of a point of the right summand under a sum permutation are those
under the right permutation. -/
@[simp]
theorem cycleCoeff_sumCongr_inr (y : β) (r : ℕ) :
    (sumCongr π τ).cycleCoeff (Sum.elim s t) (.inr y) r = τ.cycleCoeff t y r := by
  simp [cycleCoeff_def]

@[simp]
theorem monodromy_sumCongr_inl (x : α) :
    (sumCongr π τ).monodromy (Sum.elim s t) (.inl x) = π.monodromy s x := by
  simp [monodromy_def]

@[simp]
theorem monodromy_sumCongr_inr (y : β) :
    (sumCongr π τ).monodromy (Sum.elim s t) (.inr y) = τ.monodromy t y := by
  simp [monodromy_def]

end SumCongr

end Equiv.Perm

/-! ### The iterates of a weighted permutation -/

namespace Module.End

variable {ι R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- If `f` sends `v i` to `s i • v (π i)`, then `f ^ r` sends `v x` to `c_r • v (π ^ r x)` for the
cycle coefficient `c_r = Equiv.Perm.cycleCoeff π s x r`. -/
theorem pow_apply_of_apply_eq_units_smul (f : Module.End R V) (π : Equiv.Perm ι) (s : ι → Rˣ)
    (v : ι → V) (h : ∀ i, f (v i) = s i • v (π i)) (x : ι) (r : ℕ) :
    (f ^ r) (v x) = π.cycleCoeff s x r • v ((π ^ r) x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Units.smul_def, map_smul, h,
      Equiv.Perm.cycleCoeff_succ, Units.smul_def, Units.smul_def, smul_smul, Units.val_mul,
      pow_succ', Equiv.Perm.mul_apply]

end Module.End

/-! ### The integral fixed basis -/

namespace Module.Basis

variable {ι V J : Type*} [Finite ι] [AddCommGroup V] (b : Module.Basis ι ℤ V)
  (π : Equiv.Perm ι) (s : ι → ℤˣ) (f : V →ₗ[ℤ] V) (h : ∀ i, f (b i) = s i • b (π i))
  (rep : J → ι) (hrep : ∀ x, ∃! j, π.SameCycle (rep j) x)

include hrep in
private theorem finite_of_existsUnique_sameCycle : Finite J :=
  _root_.Finite.of_injective rep (π.injective_of_existsUnique_sameCycle rep hrep)

/-- The signs of `f` along the enumeration of the basis by the cycles of `π`. -/
private noncomputable def cycleSign (j : J) (i : Fin (minimalPeriod π (rep j) - 1 + 1)) : ℤ :=
  s (π.sigmaCycleEquiv rep hrep ⟨j, i⟩)

private theorem cycleSign_eq_one_or (j : J) (i : Fin (minimalPeriod π (rep j) - 1 + 1)) :
    cycleSign π s rep hrep j i = 1 ∨ cycleSign π s rep hrep j i = -1 :=
  Int.isUnit_iff.mp (Units.isUnit _)

include h in
private theorem apply_sigmaCycleEquiv (j : J) (i : Fin (minimalPeriod π (rep j) - 1 + 1)) :
    f (b (π.sigmaCycleEquiv rep hrep ⟨j, i⟩)) =
      cycleSign π s rep hrep j i • b (π.sigmaCycleEquiv rep hrep ⟨j, finRotate _ i⟩) := by
  rw [h, Units.smul_def, cycleSign, Equiv.Perm.sigmaCycleEquiv_finRotate]

private theorem prod_cycleSign_eq_one_iff (j : J) :
    ∏ i, cycleSign π s rep hrep j i = 1 ↔ π.monodromy s (rep j) = 1 := by
  rw [← Units.val_eq_one, Equiv.Perm.monodromy_def, Equiv.Perm.cycleCoeff_def, Units.coe_prod]
  exact Eq.congr_left (π.prod_sigmaCycleEquiv_eq_prod_range rep hrep (fun x ↦ (s x : ℤ)) j)

include b h hrep in
/-- **The integral fixed basis of a signed permutation of a basis.** Let `f (b i) = s i • b (π i)`
for a basis `b` of a `ℤ`-module indexed by a finite type, a permutation `π` and signs `s`, and let
`rep j` be one point on every cycle of `π`. The fixed submodule of `f` is free with a basis indexed
by the cycles of monodromy `1`: its vectors are the signed orbit sums
(`Module.Basis.fixedBasisSignedPerm_apply`), and the coordinates of a fixed vector are its
coefficients on the representatives (`Module.Basis.fixedBasisSignedPerm_repr`). -/
noncomputable def fixedBasisSignedPerm :
    Module.Basis {j // π.monodromy s (rep j) = 1} ℤ f.fixedSubmodule :=
  haveI := finite_of_existsUnique_sameCycle π rep hrep
  (b.fixedBasisSignedFamily (n := fun j ↦ minimalPeriod π (rep j) - 1)
    (π.sigmaCycleEquiv rep hrep) (cycleSign π s rep hrep)
    (cycleSign_eq_one_or π s rep hrep) f (apply_sigmaCycleEquiv b π s f h rep hrep)).reindex
    (Equiv.subtypeEquivRight (prod_cycleSign_eq_one_iff π s rep hrep))

/-- The basis vector of a cycle of monodromy `1` is its signed orbit sum
`∑_{r < l} c_r • b (π ^ r (rep j))`, over the length `l` of the cycle and the cycle coefficients
`c_r = Equiv.Perm.cycleCoeff π s (rep j) r`. -/
theorem fixedBasisSignedPerm_apply (j : {j // π.monodromy s (rep j) = 1}) :
    (b.fixedBasisSignedPerm π s f h rep hrep j : V) =
      ∑ r ∈ Finset.range (minimalPeriod π (rep j)),
        π.cycleCoeff s (rep j) r • b ((π ^ r) (rep j)) := by
  have := finite_of_existsUnique_sameCycle π rep hrep
  rw [fixedBasisSignedPerm, Module.Basis.reindex_apply, fixedBasisSignedFamily_apply,
    Equiv.subtypeEquivRight_symm_apply_coe, ← π.sum_fin_eq_sum_range_minimalPeriod]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Units.smul_def, Equiv.Perm.cycleCoeff_def, Units.coe_prod,
    ← Equiv.Perm.sigmaCycleEquiv_apply π rep hrep]
  exact congrArg (· • _) (π.partialProd_init_sigmaCycleEquiv rep hrep (fun x ↦ (s x : ℤ)) j i)

/-- The coordinate of a fixed vector at a cycle of monodromy `1` is its coefficient on the
representative of the cycle. -/
@[simp]
theorem fixedBasisSignedPerm_repr (v : f.fixedSubmodule)
    (j : {j // π.monodromy s (rep j) = 1}) :
    (b.fixedBasisSignedPerm π s f h rep hrep).repr v j = b.repr v (rep j) := by
  have := finite_of_existsUnique_sameCycle π rep hrep
  rw [fixedBasisSignedPerm, Module.Basis.repr_reindex_apply, fixedBasisSignedFamily_repr,
    Equiv.subtypeEquivRight_symm_apply_coe, Equiv.Perm.sigmaCycleEquiv_apply, Fin.val_zero,
    pow_zero, Equiv.Perm.one_apply]

end Module.Basis
