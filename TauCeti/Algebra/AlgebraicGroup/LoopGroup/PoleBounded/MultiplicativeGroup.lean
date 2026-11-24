/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.PoleBounded.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# Pole-bounded loops of the multiplicative group

For `𝔾ₘ = Spec k[T;T⁻¹]` a loop is a unit `u` of `R⸨X⸩`
(`TauCeti.MultiplicativeGroup.pointsMulEquiv`). This file computes the pieces `LG_(≤N)(R)` of
pole-bounded loops, both for the generators `T, T⁻¹` and for the single element `T`: in either
case `u` lies in `LG_(≤N)(R)` exactly when `u` and `u⁻¹` lie in `X^(-N) R⟦X⟧`.

The examples show that the pieces must bound the inverse loop as well as the loop. The loop `X^M`
lies in `LG_(≤N)(R)` exactly when `|M| ≤ N`, so for `M ≥ 0` it sends `T` into `R⟦X⟧` but lies in
no piece of level below `M`: the loops sending `T` into `R⟦X⟧` lie in no single piece. Over a
ring with `ε² = 0`, the loop `1 + ε X^(-N)`, with inverse `1 - ε X^(-N)`, lies in `LG_(≤N)(R)`.

## Main results

* `TauCeti.MultiplicativeGroup.mem_poleBoundedLoops_T_T_inv_iff`,
  `TauCeti.MultiplicativeGroup.mem_poleBoundedLoops_T_iff`: the pieces of `𝔾ₘ`.
* `TauCeti.MultiplicativeGroup.mem_poleBoundedLoops_iff_natAbs_le`: `X^M` lies in `LG_(≤N)` exactly
  when `|M| ≤ N`.
* `TauCeti.MultiplicativeGroup.exists_not_mem_poleBoundedLoops_T`: the loops sending `T` into
  `R⟦X⟧` lie in no single piece.
* `TauCeti.MultiplicativeGroup.mem_poleBoundedLoops_one_add_single`: the loop `1 + ε X^(-N)`.
-/

public section

open HahnSeries WithConv TauCeti.LaurentSeries TauCeti.HopfAlgebra LaurentPolynomial
open scoped LaurentSeries

namespace TauCeti

namespace MultiplicativeGroup

attribute [local instance 1100] HahnSeries.instAlgebra

variable {k : Type*} [CommSemiring k]

section Semiring

variable {R : Type*} [CommSemiring R] [Algebra k R]

/-- The loop `g` of `𝔾ₘ` sends `T` to the unit `pointsMulEquiv g`. -/
private theorem ofConv_T_one (g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)) :
    g.ofConv (T 1) = (pointsMulEquiv g : R⸨X⸩) := by
  rw [pointsMulEquiv_apply, laurentEvalEquiv_symm_apply]

/-- The loop `g` of `𝔾ₘ` sends `T⁻¹` to the inverse of the unit `pointsMulEquiv g`. -/
private theorem ofConv_T_neg_one (g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)) :
    g.ofConv (T (-1)) = ((pointsMulEquiv g)⁻¹ : R⸨X⸩ˣ) := by
  rw [pointsMulEquiv_apply, laurentEvalEquiv_symm_apply_inv]

/-- For the generators `T, T⁻¹` of `𝔾ₘ`, a loop `u` lies in `LG_(≤N)(R)` exactly when `u` and
`u⁻¹` lie in `X^(-N) R⟦X⟧`. -/
theorem mem_poleBoundedLoops_T_T_inv_iff {N : ℕ} {g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)} :
    g ∈ poleBoundedLoops k ![T 1, T (-1)] R N ↔
      (pointsMulEquiv g : R⸨X⸩) ∈ lattice R R (-N) ∧
        (((pointsMulEquiv g)⁻¹ : R⸨X⸩ˣ) : R⸨X⸩) ∈ lattice R R (-N) := by
  simp only [mem_poleBoundedLoops_iff, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, ofConv_T_one, ofConv_T_neg_one, map_inv, inv_inv]
  tauto

/-- For the single element `T` of `𝔾ₘ`, which does not generate `k[T;T⁻¹]` as an algebra, a loop
`u` still lies in the piece of level `N` exactly when `u` and `u⁻¹` lie in `X^(-N) R⟦X⟧`: the
bound on the inverse loop supplies the bound on `T⁻¹`. -/
theorem mem_poleBoundedLoops_T_iff {N : ℕ} {g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)} :
    g ∈ poleBoundedLoops k ![T 1] R N ↔
      (pointsMulEquiv g : R⸨X⸩) ∈ lattice R R (-N) ∧
        (((pointsMulEquiv g)⁻¹ : R⸨X⸩ˣ) : R⸨X⸩) ∈ lattice R R (-N) := by
  simp only [mem_poleBoundedLoops_iff, Fin.forall_fin_one, Matrix.cons_val_zero,
    ofConv_T_one, map_inv]

/-- The unit `X^M` of `R⸨X⸩`, with inverse `X^(-M)`. -/
private noncomputable def singleUnit (M : ℤ) : R⸨X⸩ˣ where
  val := single M 1
  inv := single (-M) 1
  val_inv := by simp [single_mul_single]
  inv_val := by simp [single_mul_single]

private theorem val_singleUnit (M : ℤ) : ((singleUnit M : R⸨X⸩ˣ) : R⸨X⸩) = single M 1 :=
  (rfl)

private theorem val_inv_singleUnit (M : ℤ) :
    (((singleUnit M)⁻¹ : R⸨X⸩ˣ) : R⸨X⸩) = single (-M) 1 :=
  (rfl)

/-- Over a nontrivial ring, the loop `X^M` of `𝔾ₘ` lies in `LG_(≤N)(R)`, for the generators
`T, T⁻¹`, exactly when `|M| ≤ N`. In particular `X^(-N)`, with inverse `X^N`, lies in
`LG_(≤N)(R)`. -/
theorem mem_poleBoundedLoops_iff_natAbs_le [Nontrivial R] {N : ℕ} {M : ℤ}
    {g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)} (hg : g.ofConv (T 1) = single M 1) :
    g ∈ poleBoundedLoops k ![T 1, T (-1)] R N ↔ M.natAbs ≤ N := by
  have hu : pointsMulEquiv g = singleUnit M :=
    Units.ext (by rw [← ofConv_T_one, hg, val_singleUnit])
  rw [mem_poleBoundedLoops_T_T_inv_iff, hu, val_singleUnit, val_inv_singleUnit]
  simp only [single_mem_lattice_iff, one_ne_zero, false_or]
  omega

/-- The loop `X^M` of `𝔾ₘ`, for `M : ℤ`. -/
theorem exists_ofConv_T_eq_single (M : ℤ) :
    ∃ g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩), g.ofConv (T 1) = single M 1 :=
  ⟨pointsMulEquiv.symm (singleUnit M), by
    rw [ofConv_T_one, MulEquiv.apply_symm_apply, val_singleUnit]⟩

/-- **The inverse bound is needed.** Over a nontrivial ring, for every `N` there is a loop of
`𝔾ₘ` sending `T` into `R⟦X⟧` (namely `X^(N + 1)`) that does not lie in the piece of level `N` for
`T`: the loops sending `T` into `R⟦X⟧` lie in no single piece. -/
theorem exists_not_mem_poleBoundedLoops_T [Nontrivial R] (N : ℕ) :
    ∃ g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩),
      g.ofConv (T 1) ∈ lattice R R 0 ∧ g ∉ poleBoundedLoops k ![T 1] R N := by
  obtain ⟨g, hg⟩ := exists_ofConv_T_eq_single (k := k) (R := R) (N + 1)
  refine ⟨g, hg ▸ single_mem_lattice (by omega) 1, fun hmem ↦ ?_⟩
  have h := (mem_poleBoundedLoops_iff_natAbs_le (N := N) hg).1 <| by
    rw [mem_poleBoundedLoops_T_T_inv_iff]
    exact mem_poleBoundedLoops_T_iff.1 hmem
  omega

end Semiring

section Ring

variable {R : Type*} [CommRing R] [Algebra k R]

/-- **A nilpotent loop.** If `ε² = 0` in `R`, a loop of `𝔾ₘ` sending `T` to `1 + ε X^(-N)` sends
`T⁻¹` to `1 - ε X^(-N)` and lies in `LG_(≤N)(R)`. -/
theorem mem_poleBoundedLoops_one_add_single {N : ℕ} {ε : R} (hε : ε * ε = 0)
    {g : WithConv (k[T;T⁻¹] →ₐ[k] R⸨X⸩)} (hg : g.ofConv (T 1) = 1 + single (-(N : ℤ)) ε) :
    g.ofConv (T (-1)) = 1 - single (-(N : ℤ)) ε ∧ g ∈ poleBoundedLoops k ![T 1, T (-1)] R N := by
  have hmul : (1 + single (-(N : ℤ)) ε) * (1 - single (-(N : ℤ)) ε) = 1 := by
    rw [← mul_self_sub_mul_self, mul_one, single_mul_single, hε, single_eq_zero, sub_zero]
  have hab : (1 + single (-(N : ℤ)) ε) * g.ofConv (T (-1)) = 1 := by
    rw [← hg, ← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have hinv : g.ofConv (T (-1)) = 1 - single (-(N : ℤ)) ε :=
    calc _ = g.ofConv (T (-1)) * ((1 + single (-(N : ℤ)) ε) * (1 - single (-(N : ℤ)) ε)) := by
          rw [hmul, mul_one]
      _ = ((1 + single (-(N : ℤ)) ε) * g.ofConv (T (-1))) * (1 - single (-(N : ℤ)) ε) := by ring
      _ = 1 - single (-(N : ℤ)) ε := by rw [hab, one_mul]
  have hmem (f : R⸨X⸩) (hf : f = 1 + single (-(N : ℤ)) ε ∨ f = 1 - single (-(N : ℤ)) ε) :
      f ∈ lattice R R (-N) := by
    have h1 : (1 : R⸨X⸩) ∈ lattice R R (-N) := single_mem_lattice (by omega) 1
    have h2 : single (-(N : ℤ)) ε ∈ lattice R R (-N) := single_mem_lattice le_rfl ε
    rcases hf with rfl | rfl
    exacts [add_mem h1 h2, sub_mem h1 h2]
  refine ⟨hinv, mem_poleBoundedLoops_T_T_inv_iff.2 ⟨?_, ?_⟩⟩
  · exact hmem _ (.inl ((ofConv_T_one g).symm.trans hg))
  · exact hmem _ (.inr ((ofConv_T_neg_one g).symm.trans hinv))

end Ring

end MultiplicativeGroup

end TauCeti
