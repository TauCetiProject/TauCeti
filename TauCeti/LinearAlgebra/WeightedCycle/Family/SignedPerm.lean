/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Cycle.Coeff
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Signed

/-!
# The integral fixed basis of a signed permutation of a basis

Let `π` be a permutation of `ι` and `s : ι → R` weights in a commutative semiring. If a linear
endomorphism `f` sends `v i` to `s i • v (π i)`, then `f ^ r` sends `v x` to `c_r • v (π ^ r x)` for
the cycle coefficients `c_r = Equiv.Perm.cycleCoeff π s x r`
(`Module.End.pow_apply_of_apply_eq_smul`).

Now let `b` be a basis of a `ℤ`-module indexed by a finite type `ι`, and let
`f (b i) = s i • b (π i)` with signs `s : ι → ℤˣ`. Choose one representative `rep j` on every cycle
of `π`. The fixed submodule of `f` is free over `ℤ` (`Module.Basis.fixedBasisSignedPerm`), with
basis the signed orbit sums `∑_{r < l} c_r • b (π ^ r (rep j))` of the cycles whose monodromy
`Equiv.Perm.monodromy` is `1` (`Module.Basis.fixedBasisSignedPerm_apply`); the coordinate of a
fixed vector at such a cycle is its coefficient on the representative
(`Module.Basis.fixedBasisSignedPerm_repr`). A cycle of monodromy `-1` carries no integral fixed
vector. This is `Module.Basis.fixedBasisSignedFamily` applied to the enumeration
`Equiv.Perm.sigmaCycleEquiv` of `ι` along the cycles of `π`. For an unsigned permutation of
coordinates, compare `Equiv.Perm.permutationFixedBasis`.

## Main definitions

* `Module.Basis.fixedBasisSignedPerm`: the integral basis of the fixed submodule of a signed
  permutation of a basis.

## Main results

* `Module.End.pow_apply_of_apply_eq_smul`: the iterates of a weighted permutation of a family
  of vectors.
* `Module.Basis.fixedBasisSignedPerm_apply`, `Module.Basis.fixedBasisSignedPerm_repr`: the basis
  vectors are the signed orbit sums, and the coordinates are the coefficients on the
  representatives.
-/

public section

open Function

/-! ### The iterates of a weighted permutation -/

namespace Module.End

variable {ι R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- If `f` sends `v i` to `s i • v (π i)`, then `f ^ r` sends `v x` to `c_r • v (π ^ r x)` for the
cycle coefficient `c_r = Equiv.Perm.cycleCoeff π s x r`. -/
theorem pow_apply_of_apply_eq_smul (f : Module.End R V) (π : Equiv.Perm ι) (s : ι → R)
    (v : ι → V) (h : ∀ i, f (v i) = s i • v (π i)) (x : ι) (r : ℕ) :
    (f ^ r) (v x) = π.cycleCoeff s x r • v ((π ^ r) x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, Equiv.Perm.cycleCoeff_succ, smul_smul,
      pow_succ', Equiv.Perm.mul_apply]

end Module.End

/-! ### The integral fixed basis -/

namespace Module.Basis

variable {ι V J : Type*} [Finite ι] [AddCommGroup V] (b : Module.Basis ι ℤ V)
  (π : Equiv.Perm ι) (s : ι → ℤˣ) (f : V →ₗ[ℤ] V) (h : ∀ i, f (b i) = s i • b (π i))
  (rep : J → ι) (hrep : ∀ x, ∃! j, π.SameCycle (rep j) x)

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
  haveI := π.finite_of_existsUnique_sameCycle rep hrep
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
  have := π.finite_of_existsUnique_sameCycle rep hrep
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
  have := π.finite_of_existsUnique_sameCycle rep hrep
  rw [fixedBasisSignedPerm, Module.Basis.repr_reindex_apply, fixedBasisSignedFamily_repr,
    Equiv.subtypeEquivRight_symm_apply_coe, Equiv.Perm.sigmaCycleEquiv_apply, Fin.val_zero,
    pow_zero, Equiv.Perm.one_apply]

end Module.Basis
