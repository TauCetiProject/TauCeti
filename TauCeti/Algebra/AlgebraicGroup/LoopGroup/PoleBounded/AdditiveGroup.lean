/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.PoleBounded.Representable
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Pole-bounded loops of the additive group

For `𝔾ₐ = Spec k[x]`, with `k[x] = SymmetricAlgebra k k` and `x = ι k k 1`, a loop is a Laurent
series `f = g (x)` (`TauCeti.AdditiveGroup.gaPointsMulEquiv`), and its inverse is `-f`. This
file computes the pieces of pole-bounded loops for two presentations.

* For the generator `x`, the piece `LG_(≤N)(R)` is the lattice `X^(-N) R⟦X⟧`.
* For the generators `x, x²`, a loop lies in the piece of level `1` exactly when
  `f = a₋₁ X⁻¹ + a₀ + a₁ X + ⋯` with `a₋₁² = 0`: the piece is `Spec k[a₋₁, a₀, a₁, …] ⧸ (a₋₁²)`.
  Its representing algebra `poleBoundedAlgebra k ![x, x²] 1` is therefore not reduced when `k` is
  nonzero, although `𝔾ₐ` is smooth: the pieces of an ind-affine presentation need not be reduced,
  and depend on the presentation.

## Main results

* `TauCeti.AdditiveGroup.poleBoundedLoopsEquivLattice`: `LG_(≤N)(R) ≃ X^(-N) R⟦X⟧` for the
  generator `x`.
* `TauCeti.AdditiveGroup.mem_poleBoundedLoops_ι_sq_iff`: the piece of level `1` for `x, x²`.
* `TauCeti.AdditiveGroup.not_isReduced_poleBoundedAlgebra_ι_sq`: its representing algebra is not
  reduced.
-/

public section

open HahnSeries WithConv TauCeti.LaurentSeries TauCeti.HopfAlgebra SymmetricAlgebra
open scoped LaurentSeries PowerSeries DualNumber

namespace TauCeti

namespace AdditiveGroup

attribute [local instance 1100] HahnSeries.instAlgebra

variable {k : Type*} [CommRing k]

variable {R : Type*} [CommRing R] [Algebra k R]

/-- The inverse of a loop `f` of `𝔾ₐ` is `-f`. -/
private theorem inv_ofConv_ι_one (g : WithConv (SymmetricAlgebra k k →ₐ[k] R⸨X⸩)) :
    g⁻¹.ofConv (ι k k 1) = -g.ofConv (ι k k 1) := by
  rw [← toAdd_gaPointsMulEquiv, ← toAdd_gaPointsMulEquiv, toAdd_gaPointsMulEquiv_inv]

/-- For the generator `x` of `𝔾ₐ`, a loop lies in `LG_(≤N)(R)` exactly when it sends `x` into
`X^(-N) R⟦X⟧`. -/
theorem mem_poleBoundedLoops_ι_iff {N : ℕ} {g : WithConv (SymmetricAlgebra k k →ₐ[k] R⸨X⸩)} :
    g ∈ poleBoundedLoops k ![ι k k 1] R N ↔ g.ofConv (ι k k 1) ∈ lattice R R (-N) := by
  simp only [mem_poleBoundedLoops_iff, Fin.forall_fin_one, Matrix.cons_val_zero,
    inv_ofConv_ι_one, neg_mem_iff, and_self]

variable (k R) in
/-- For the generator `x` of `𝔾ₐ`, the piece `LG_(≤N)(R)` is the lattice `X^(-N) R⟦X⟧`, through
the value of a loop at `x`. -/
noncomputable def poleBoundedLoopsEquivLattice (N : ℕ) :
    poleBoundedLoops k ![ι k k 1] R N ≃ lattice R R (-N) :=
  (gaPointsMulEquiv.toEquiv.trans Multiplicative.toAdd).subtypeEquiv fun g ↦ by
    rw [mem_poleBoundedLoops_ι_iff, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv, toAdd_gaPointsMulEquiv]

@[simp]
theorem coe_poleBoundedLoopsEquivLattice_apply {N : ℕ} (g : poleBoundedLoops k ![ι k k 1] R N) :
    (poleBoundedLoopsEquivLattice k R N g : R⸨X⸩) = g.val.ofConv (ι k k 1) := by
  simp [poleBoundedLoopsEquivLattice]

/-- **The piece of level `1` for the generators `x, x²` of `𝔾ₐ`.** A loop `f` lies in it exactly
when `f = a₋₁ X⁻¹ + a₀ + a₁ X + ⋯` with `a₋₁² = 0`. -/
theorem mem_poleBoundedLoops_ι_sq_iff {g : WithConv (SymmetricAlgebra k k →ₐ[k] R⸨X⸩)} :
    g ∈ poleBoundedLoops k ![ι k k 1, ι k k 1 ^ 2] R 1 ↔
      g.ofConv (ι k k 1) ∈ lattice R R (-1) ∧ (g.ofConv (ι k k 1)).coeff (-1) ^ 2 = 0 := by
  -- A series `f ∈ X⁻¹ R⟦X⟧` has `f² ∈ X⁻¹ R⟦X⟧` exactly when its coefficient of `X⁻¹` squares
  -- to `0`.
  have sq_mem_lattice_neg_one_iff {f : R⸨X⸩} (hf : f ∈ lattice R R (-1)) :
      f ^ 2 ∈ lattice R R (-1) ↔ f.coeff (-1) ^ 2 = 0 := by
    simpa only [sq, Int.reduceNeg, Int.reduceAdd] using mul_mem_lattice_add_one_iff hf hf
  simp only [mem_poleBoundedLoops_iff, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_pow, inv_ofConv_ι_one, neg_mem_iff, neg_sq, Nat.cast_one]
  refine ⟨fun h ↦ ⟨h.1.1, (sq_mem_lattice_neg_one_iff h.1.1).1 h.2.1⟩, fun h ↦ ?_⟩
  have hsq := (sq_mem_lattice_neg_one_iff h.1).2 h.2
  exact ⟨⟨h.1, h.1⟩, hsq, hsq⟩

/-- The generators `x, x²` generate `k[x]`. -/
theorem adjoin_range_ι_sq : Algebra.adjoin k (Set.range ![ι k k 1, ι k k 1 ^ 2]) = ⊤ :=
  adjoin_eq_top_of_ι_one_mem ⟨0, rfl⟩

/-- **The piece of level `1` for `x, x²` is not reduced.** Over a nonzero ring `k`, the algebra
representing the pole-bounded loops of level `1` of `𝔾ₐ` for the generators `x, x²` is not
reduced: the coefficient `a₋₁` of the universal loop is a nonzero element with `a₋₁² = 0`. It is
nonzero because the loop `ε X⁻¹` over the dual numbers `k[ε]` lies in the piece. -/
theorem not_isReduced_poleBoundedAlgebra_ι_sq [Nontrivial k] :
    ¬ IsReduced (poleBoundedAlgebra k ![ι k k 1, ι k k 1 ^ 2] 1) := by
  intro hred
  have hx := adjoin_range_ι_sq (k := k)
  -- The universal loop has nilpotent, hence zero, coefficient `a₋₁`.
  have h0 : ((poleBoundedEquiv _ hx _ 1 (AlgHom.id k _)).val.ofConv (ι k k 1)).coeff (-1) = 0 :=
    IsReduced.eq_zero _
      ⟨2, (mem_poleBoundedLoops_ι_sq_iff.1 (poleBoundedEquiv _ hx _ 1 (AlgHom.id k _)).property).2⟩
  -- The loop `ε X⁻¹` over `k[ε]` lies in the piece.
  let g : WithConv (SymmetricAlgebra k k →ₐ[k] (k[ε])⸨X⸩) :=
    (gaPointsMulEquiv (R := k)).symm (Multiplicative.ofAdd (single (-1) (DualNumber.eps : k[ε])))
  have hgι : g.ofConv (ι k k 1) = single (-1) (DualNumber.eps : k[ε]) :=
    gaPointsMulEquiv_symm_apply_ι _
  have hg : g ∈ poleBoundedLoops k ![ι k k 1, ι k k 1 ^ 2] (k[ε]) 1 := by
    rw [mem_poleBoundedLoops_ι_sq_iff, hgι, coeff_single_same, sq, DualNumber.eps_mul_eps]
    exact ⟨single_mem_lattice (by norm_num) _, rfl⟩
  -- By naturality, its classifying map sends `a₋₁` to `ε`; it also sends it to `0`.
  have hφ := poleBoundedEquiv_comp_apply _ hx
    ((poleBoundedEquiv _ hx (k[ε]) 1).symm ⟨g, hg⟩) (AlgHom.id k _) (ι k k 1)
  rw [AlgHom.comp_id, Equiv.apply_symm_apply, hgι] at hφ
  have hε := congrArg (fun f ↦ f.coeff (-1)) hφ
  simp only [coeff_single_same, map_coeff, h0, map_zero] at hε
  simpa using congrArg TrivSqZeroExt.snd hε

end AdditiveGroup

end TauCeti
