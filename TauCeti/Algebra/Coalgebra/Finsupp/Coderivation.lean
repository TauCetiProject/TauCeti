/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.Primitive

/-!
# Infinitesimal rigidity of diagonal coalgebras

The diagonal coalgebra `ι →₀ R` has comultiplication `eᵢ ↦ eᵢ ⊗ eᵢ`. An element `x`
primitive relative to a group-like element `g`, meaning `Δ(x) = x ⊗ g + g ⊗ x`, is zero.
Consequently, every coderivation between diagonal coalgebras, along any coalgebra morphism,
is zero.

For a diagonalizable group the coordinate coalgebra is diagonal in its character basis.
The vanishing result is the infinitesimal rigidity of its group homomorphisms: differentiating
a family of Hopf morphisms gives precisely the coderivation identity below. In particular,
this is the rigidity input in comparing the tangent Lie algebras of the normalizer and
centralizer of a diagonalizable subgroup.

The base may be any commutative semiring with additive cancellation; in particular, a ring
may be disconnected, nonreduced, or of positive characteristic. There are no
finiteness assumptions on the bases. The proof only uses the diagonal coefficients of the
comultiplication identity; it does not classify group-like elements over the base ring.
-/

public section

open Coalgebra TensorProduct

namespace Finsupp

variable {R ι κ : Type*} [CommSemiring R] [IsCancelAdd R]

/-- An element of a diagonal coalgebra primitive relative to an element satisfying the
group-like comultiplication identity is zero. The counit identity is unnecessary. -/
theorem eq_zero_of_comul_eq_tmul_add_tmul {g x : ι →₀ R}
    (hg : comul (R := R) g = g ⊗ₜ[R] g)
    (hx : comul (R := R) x = x ⊗ₜ[R] g + g ⊗ₜ[R] x) : x = 0 := by
  ext i
  let p : (ι →₀ R) →ₗ[R] R := lapply i
  let q := (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map p p)
  have diag (y : ι →₀ R) : q (comul (R := R) y) = y i := by
    have h := LinearMap.congr_fun (comul_comp_lapply R ι R i) y
    simpa [q, p] using congrArg (TensorProduct.lid R R) h.symm
  have hi : g i = g i * g i := by
    simpa [q, p, diag] using congrArg q hg
  have hxi : x i = x i * g i + g i * x i := by
    simpa [q, p, diag] using congrArg q hx
  have hxg : x i * g i = x i * g i + x i * g i := by
    calc
      x i * g i = (x i * g i + g i * x i) * g i := congrArg (· * g i) hxi
      _ = x i * g i + x i * g i := by
        simp only [mul_comm (g i) (x i), add_mul, mul_assoc, ← hi]
  have hxgzero : x i * g i = 0 := add_eq_left.mp hxg.symm
  have : x i = 0 := by
    simpa only [mul_comm (g i) (x i), hxgzero, zero_add] using hxi
  simpa only [Finsupp.zero_apply] using this

/-- The self-skew-primitive submodule at a group-like element of a diagonal coalgebra is zero.
Only the group-like comultiplication identity is needed. -/
@[simp]
theorem skewPrimitive_self_eq_bot (g : ι →₀ R)
    (hg : comul (R := R) g = g ⊗ₜ[R] g) :
    Coalgebra.skewPrimitive R g g = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  exact (Submodule.mem_bot R).mpr
    (eq_zero_of_comul_eq_tmul_add_tmul hg
      (by simpa only [add_comm] using hx.comul_eq_tmul_add_tmul))

end Finsupp

namespace LinearMap

variable {R ι κ : Type*} [CommSemiring R] [IsCancelAdd R]

/-- Every coderivation along a morphism between diagonal coalgebras is zero.

The hypothesis `hd` is the co-Leibniz identity, with `f` in both undifferentiated factors.
The linear map `f` need only preserve comultiplication, as expressed by `hf`; counit
preservation is unnecessary. In particular, taking `f` to be the identity rules out nonzero
coderivations of a diagonalizable coordinate coalgebra. -/
theorem eq_zero_of_finsupp_comul_comp_eq
    (d f : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (hf : comul ∘ₗ f = TensorProduct.map f f ∘ₗ comul)
    (hd : comul ∘ₗ d = (TensorProduct.map d f + TensorProduct.map f d) ∘ₗ comul) :
    d = 0 := by
  apply Finsupp.lhom_ext
  intro i r
  have hsingle : comul (R := R) (Finsupp.single i (1 : R)) =
      Finsupp.single i 1 ⊗ₜ[R] Finsupp.single i 1 := by
    simp
  have hgroup : comul (R := R) (f (Finsupp.single i 1)) =
      f (Finsupp.single i 1) ⊗ₜ[R] f (Finsupp.single i 1) := by
    simpa only [LinearMap.comp_apply, hsingle, TensorProduct.map_tmul] using
      LinearMap.congr_fun hf (Finsupp.single i 1)
  have hzero : d (Finsupp.single i 1) = 0 := by
    apply Finsupp.eq_zero_of_comul_eq_tmul_add_tmul hgroup
    simpa only [LinearMap.comp_apply, hsingle, LinearMap.add_apply, TensorProduct.map_tmul] using
      LinearMap.congr_fun hd (Finsupp.single i 1)
  rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, hzero, smul_zero]
  rfl

end LinearMap
