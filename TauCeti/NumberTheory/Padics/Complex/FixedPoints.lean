/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction

import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.FieldTheory.Galois.AxSen
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The Ax–Sen–Tate theorem

Let `L` be a field between `ℚ_p` and its algebraic closure `PadicAlgCl p`, and let
`G_L = Gal(PadicAlgCl p / L)` act on `ℂ_p = PadicComplex p` by the continuous extensions of its
elements (`TauCeti.NumberTheory.Padics.Complex.GaloisAction`). The **Ax–Sen–Tate theorem**
computes the fixed points: the elements of `ℂ_p` fixed by `G_L` are the closure of `L` in `ℂ_p`,
that is the completion of `L`.

The closure cannot be dropped: for the field `ℚ_p(μ_{p^∞})` the fixed points form its completion,
which is strictly larger. When `L` is finite over `ℚ_p` it is complete, hence closed in `ℂ_p`, and
the fixed points are exactly `L`; in particular the elements of `ℂ_p` fixed by `G_{ℚ_p}` are
`ℚ_p`, so that `ℂ_p` has no transcendental Galois invariants.

By infinite Galois theory the closed subgroups `H` of `G_{ℚ_p}` are exactly the groups `G_L`,
with `L` the fixed field of `H`, so the theorem also computes the fixed points of every closed
subgroup.

The proof approximates a fixed point `x ∈ ℂ_p` by an algebraic `y` with `‖x - y‖ ≤ δ`. Every
`σ ∈ G_L` is an isometry fixing `x`, so `‖σ y - y‖ ≤ δ`, and the Ax–Sen lemma
`TauCeti.exists_norm_sub_algebraMap_le_of_forall_norm_smul_sub_le` gives `a ∈ L` with
`‖y - a‖ ≤ C δ` for a constant `C` depending only on `p`. Conversely the fixed points form a
closed set, by continuity of the action, which contains `L`.

## Main results

* `PadicComplex.fixedPoints_algEquiv_eq_closure`: the fixed points of `G_L` in `ℂ_p` are the
  closure of `L`.
* `PadicComplex.fixedPoints_eq_closure_fixedField`: the fixed points of a closed subgroup `H` of
  `G_{ℚ_p}` are the closure of the fixed field of `H`.
* `PadicComplex.fixedPoints_algEquiv_eq_range`: for `K` finite over `ℚ_p`, the fixed points of
  `G_K` in `ℂ_p` are `K`.

## References

* J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15 (1970),
  417–428.
* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966),
  Springer, 1967, §3.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.1.2, Proposition
  4.9.
* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.1,
  Proposition 2.1.2.
-/

public section

open UniformSpace.Completion

namespace PadicComplex

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Ax–Sen–Tate theorem.** For every field `L` between `ℚ_p` and `PadicAlgCl p`, the
elements of `ℂ_p` fixed by `Gal(PadicAlgCl p / L)` are the closure of `L` in `ℂ_p`. -/
theorem fixedPoints_algEquiv_eq_closure (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    MulAction.fixedPoints (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℂ_[p] =
      closure (Set.range fun a : L ↦ ((a : PadicAlgCl p) : ℂ_[p])) := by
  refine subset_antisymm (fun x hx ↦ Metric.mem_closure_iff.mpr fun ε hε ↦ ?_) <|
    closure_minimal ?_ ?_
  · -- Approximate `x` by an algebraic `y`, then `y` by an element of `L` (Ax–Sen).
    have hpE : ‖(p : PadicAlgCl p)‖ < 1 := by
      rw [← norm_extends, coe_natCast]
      exact norm_p_lt_one p
    set C : ℝ := ‖(p : PadicAlgCl p)‖ ^ (-((p : ℝ) / (p - 1) ^ 2))
    have hC : 1 ≤ C := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)) hpE.le
      (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    set δ := ε / (2 * C)
    have hδ : 0 < δ := by positivity
    obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp (denseRange_coe (α := PadicAlgCl p)) x δ hδ
    have hconj (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : ‖σ • y - y‖ ≤ δ := by
      rw [← dist_eq_norm, ← UniformSpace.Completion.dist_eq, UniformSpace.Completion.coe_smul]
      calc dist (σ • (y : ℂ_[p])) y ≤ max (dist (σ • (y : ℂ_[p])) (σ • x)) (dist (σ • x) y) :=
            dist_triangle_max _ _ _
        _ ≤ δ := by
            rw [dist_smul, hx σ, dist_comm]
            exact max_le hy.le hy.le
    obtain ⟨a, ha⟩ := TauCeti.exists_norm_sub_algebraMap_le_of_forall_norm_smul_sub_le hp.out
      hpE hconj
    refine ⟨_, ⟨a, rfl⟩, ?_⟩
    calc dist x ((a : PadicAlgCl p) : ℂ_[p])
        ≤ max (dist x y) (dist (y : ℂ_[p]) ((a : PadicAlgCl p) : ℂ_[p])) :=
          dist_triangle_max _ _ _
      _ < ε := by
          rw [UniformSpace.Completion.dist_eq, dist_eq_norm y]
          refine max_lt (hy.trans_le ?_) (ha.trans_lt ?_)
          · rw [div_le_iff₀ (by positivity)]
            nlinarith
          · have hCδ : C * δ = ε / 2 := by
              simp only [δ]
              field_simp
            rw [hCδ]
            linarith
  · rintro _ ⟨a, rfl⟩ σ
    rw [algEquiv_smul_coe]
    exact congrArg _ (σ.commutes a)
  · rw [MulAction.fixedPoints, Set.ofPred_forall]
    exact isClosed_iInter fun σ ↦ isClosed_eq (continuous_const_smul σ) continuous_id

/-- **The Ax–Sen–Tate theorem for closed subgroups.** For a closed subgroup `H` of
`Gal(PadicAlgCl p / ℚ_p)`, the elements of `ℂ_p` fixed by `H` are the closure in `ℂ_p` of the
fixed field of `H`. -/
theorem fixedPoints_eq_closure_fixedField
    (H : ClosedSubgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :
    MulAction.fixedPoints H.toSubgroup ℂ_[p] =
      closure (Set.range fun a : IntermediateField.fixedField H.toSubgroup ↦
        ((a : PadicAlgCl p) : ℂ_[p])) := by
  set L := IntermediateField.fixedField H.toSubgroup
  have hL : L.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  rw [← fixedPoints_algEquiv_eq_closure]
  -- An `L`-automorphism acts on `ℂ_p` as the underlying `ℚ_p`-automorphism does.
  have hsmul (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p]) :
      τ.restrictScalars ℚ_[p] • x = τ • x := by
    rw [algEquiv_smul_def, algEquiv_smul_def, AlgEquiv.coe_restrictScalars]
  ext x
  refine ⟨fun hx τ ↦ ?_, fun hx σ ↦ ?_⟩
  · have hτ : τ.restrictScalars ℚ_[p] ∈ H.toSubgroup := by
      rw [← hL, IntermediateField.mem_fixingSubgroup_iff]
      exact fun a ha ↦ τ.commutes ⟨a, ha⟩
    rw [← hsmul]
    exact hx ⟨_, hτ⟩
  · have hσ : (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ L.fixingSubgroup := by
      rw [hL]
      exact σ.property
    have h := hx (L.fixingSubgroupEquiv ⟨σ, hσ⟩)
    rwa [← hsmul] at h

/-- **The Ax–Sen–Tate theorem for finite extensions.** For a finite extension `K` of `ℚ_p` inside
`PadicAlgCl p`, the elements of `ℂ_p` fixed by `Gal(PadicAlgCl p / K)` are the elements of `K`. -/
theorem fixedPoints_algEquiv_eq_range (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    MulAction.fixedPoints (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) ℂ_[p] =
      Set.range fun a : K ↦ ((a : PadicAlgCl p) : ℂ_[p]) := by
  rw [fixedPoints_algEquiv_eq_closure, closure_eq_iff_isClosed]
  -- The image of `K` is a finite-dimensional `ℚ_p`-subspace of `ℂ_p`, hence closed; the function
  -- underlying `f` is `a ↦ ((a : PadicAlgCl p) : ℂ_[p])` by definition.
  let f : K →ₗ[ℚ_[p]] ℂ_[p] :=
    (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).toLinearMap ∘ₗ K.val.toLinearMap
  have h := (LinearMap.range f).isClosed_of_finiteDimensional
  rwa [LinearMap.coe_range] at h

end PadicComplex
