/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.Primitive

/-!
# Infinitesimal rigidity of diagonal coalgebras

The diagonal coalgebra `κ →₀ R` has comultiplication `eᵢ ↦ eᵢ ⊗ eᵢ`. Every coderivation
from a cocommutative coalgebra into a diagonal coalgebra, along a comultiplicative map, is zero.
Taking the source to be the coalgebra `R`, an element `x` of a diagonal coalgebra primitive
relative to a group-like element `g`, meaning `Δ(x) = x ⊗ g + g ⊗ x`, is zero.

For a diagonalizable group the coordinate coalgebra is diagonal in its character basis.
The vanishing result is the infinitesimal rigidity of its group homomorphisms: differentiating
a family of Hopf morphisms gives precisely the coderivation identity below. In particular,
this is the rigidity input in comparing the tangent Lie algebras of the normalizer and
centralizer of a diagonalizable subgroup.

The base may be any commutative semiring with additive cancellation; in particular, a ring
may be disconnected, nonreduced, or of positive characteristic. There are no finiteness
assumptions on the source or the index type. The argument works one coordinate at a time in the
commutative convolution algebra of linear functionals on the source; it does not classify
group-like elements over the base ring.
-/

public section

open Coalgebra TensorProduct WithConv

namespace LinearMap

variable {R C κ : Type*} [CommSemiring R] [IsCancelAdd R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C] [IsCocomm R C]

/-- Every coderivation from a cocommutative coalgebra into a diagonal coalgebra, along a
comultiplicative map, is zero.

The hypothesis `hd` is the co-Leibniz identity, with `f` in both undifferentiated factors.
The linear map `f` need only preserve comultiplication, as expressed by `hf`; counit
preservation is unnecessary. Taking `f` to be the identity of a diagonal coalgebra rules out
nonzero coderivations of a diagonalizable coordinate coalgebra.

Cocommutativity of the source cannot be dropped: on the `2 × 2` matrix coalgebra over `ℤ`, with
`f` the projection `eᵢⱼ ↦ δᵢⱼ eᵢ`, the map sending `e₁₂` to `e₁ - e₂` and the other basis
elements to zero is a nonzero coderivation. -/
theorem eq_zero_of_finsupp_comul_comp_eq (d f : C →ₗ[R] (κ →₀ R))
    (hf : comul ∘ₗ f = TensorProduct.map f f ∘ₗ comul)
    (hd : comul ∘ₗ d = (TensorProduct.map d f + TensorProduct.map f d) ∘ₗ comul) :
    d = 0 := by
  refine LinearMap.ext fun c => Finsupp.ext fun i => ?_
  -- Project to the coordinate `i` and argue in the commutative convolution algebra `C → R`.
  let p : (κ →₀ R) →ₗ[R] R := Finsupp.lapply i
  -- The coordinate projection `p` is comultiplicative, and `mul' R R` undoes the
  -- comultiplication `r ↦ 1 ⊗ r` of the coalgebra `R`.
  have hpc : comul ∘ₗ p = TensorProduct.map p p ∘ₗ comul := Finsupp.comul_comp_lapply R κ R i
  have hR : mul' R R ∘ₗ (comul : R →ₗ[R] R ⊗[R] R) = .id := by
    ext
    simp
  have hp (u : C →ₗ[R] (κ →₀ R)) :
      mul' R R ∘ₗ TensorProduct.map p p ∘ₗ comul ∘ₗ u = p ∘ₗ u := by
    rw [← comp_assoc _ comul, ← hpc, comp_assoc, ← comp_assoc _ comul, hR, id_comp]
  have hmul (u v : C →ₗ[R] (κ →₀ R)) : toConv (p ∘ₗ u) * toConv (p ∘ₗ v) =
      toConv (mul' R R ∘ₗ TensorProduct.map p p ∘ₗ TensorProduct.map u v ∘ₗ comul) := by
    simp only [convMul_def, map_comp, comp_assoc]
  let φ : WithConv (C →ₗ[R] R) := toConv (p ∘ₗ f)
  let δ : WithConv (C →ₗ[R] R) := toConv (p ∘ₗ d)
  have hφ : φ * φ = φ := by
    rw [hmul, ← hf, hp]
  have hδ : δ = δ * φ + φ * δ := by
    rw [hmul, hmul, ← toConv_add, ← comp_add, ← comp_add, ← add_comp, ← hd, hp]
  have hδφ : δ * φ = δ * φ + δ * φ := by
    calc
      δ * φ = (δ * φ + φ * δ) * φ := by rw [← hδ]
      _ = δ * φ + δ * φ := by rw [add_mul, mul_assoc, hφ, mul_comm φ δ, mul_assoc, hφ]
  have hδφ0 : δ * φ = 0 :=
    WithConv.ext <| LinearMap.ext fun x => add_eq_left.mp (congr($hδφ x)).symm
  have hδ0 : δ = 0 := by rw [hδ, mul_comm φ δ, hδφ0, add_zero]
  simpa [δ, p] using congr($hδ0 c)

end LinearMap

namespace Finsupp

variable {R ι : Type*} [CommSemiring R] [IsCancelAdd R]

/-- An element of a diagonal coalgebra primitive relative to an element satisfying the
group-like comultiplication identity is zero. The counit identity is unnecessary. -/
theorem eq_zero_of_comul_eq_tmul_add_tmul {g x : ι →₀ R}
    (hg : comul (R := R) g = g ⊗ₜ[R] g)
    (hx : comul (R := R) x = x ⊗ₜ[R] g + g ⊗ₜ[R] x) : x = 0 := by
  simpa using LinearMap.congr_fun (LinearMap.eq_zero_of_finsupp_comul_comp_eq
    (LinearMap.toSpanSingleton R _ x) (LinearMap.toSpanSingleton R _ g)
    (LinearMap.ext_ring (by simpa using hg)) (LinearMap.ext_ring (by simpa using hx))) 1

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
