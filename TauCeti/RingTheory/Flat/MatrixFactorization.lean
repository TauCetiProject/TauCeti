/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.Algebra.Exact.LiftCancel
import TauCeti.RingTheory.Flat.Pi

/-!
# Universal exactness of a matrix factorization

Let `S` be a commutative ring, `F ∈ S` a nonzerodivisor and `Φ Ψ` square matrices over `S` with
`Ψ * Φ = Φ * Ψ = F • 1`, a matrix factorization of `F`. Over `R = S ⧸ (F)` the two reductions
`Φ_R`, `Ψ_R` compose to zero in both orders, and the two-periodic complex
`⋯ → Rⁿ --Ψ_R--> Rⁿ --Φ_R--> Rⁿ --Ψ_R--> ⋯` is exact (Eisenbud). Here we prove more: if `S` and
`R` are algebras over a commutative ring `A` and `R` is flat over `A`, the complex stays exact
after tensoring over `A` with an arbitrary `A`-module `N`, flat or not.

The argument lifts and cancels. A vector `x` of `Rⁿ ⊗[A] N` killed by `Φ_R` lifts to `Sⁿ ⊗[A] N`,
where `Φ x` becomes `F • z` for some `z`. Then `F • x = Ψ Φ x = F • Ψ z`. Multiplication by `F`
stays injective on `Sⁿ ⊗[A] N` because its cokernel `Rⁿ` is `A`-flat, so `x = Ψ z` and the
class of `x` is the image of the class of `z` under `Ψ_R`.

This is the algebra behind Knudsen's presentation of the ideal of a section through a node and
of its dual: there `S = A[Y][X]`, `F = q(X, Y) - q(s, t)` is monic in `X`, and `R = S ⧸ (F)`
is free over `A`.

## Main results

* `Matrix.exact_rTensor_mulVecLin_map_of_mul_eq_smul_one`: the reduced complex stays exact after
  tensoring over `A` with any `A`-module.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. 260 (1980), 35–64, §5.
* F. F. Knudsen, *A closer look at the stacks of stable pointed curves*, arXiv:1106.1588v2
  (2012), §3, Key Example and the proof of Proposition 3.1.
-/

public section

open TensorProduct

namespace Matrix

variable {A S R : Type*} [CommRing A] [CommRing S] [CommRing R] [Algebra A S] [Algebra A R]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **Universal exactness of a matrix factorization.** Let `Ψ * Φ = Φ * Ψ = F • 1` be a matrix
factorization of a nonzerodivisor `F` of `S`, and `π : S → R` a surjection of `A`-algebras with
kernel `(F)` and `R` flat over `A`. Then for every `A`-module `N`, the reductions of `Ψ` and `Φ`
form an exact sequence `Rⁿ ⊗[A] N → Rⁿ ⊗[A] N → Rⁿ ⊗[A] N`. -/
theorem exact_rTensor_mulVecLin_map_of_mul_eq_smul_one (Φ Ψ : Matrix n n S) {F : S}
    (π : S →ₐ[A] R) (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {F})
    (hF : IsSMulRegular S F) [Module.Flat A R] (hΨΦ : Ψ * Φ = F • 1) (hΦΨ : Φ * Ψ = F • 1)
    (N : Type*) [AddCommGroup N] [Module A N] :
    Function.Exact (((Ψ.map π).mulVecLin.restrictScalars A).rTensor N)
      (((Φ.map π).mulVecLin.restrictScalars A).rTensor N) := by
  -- Multiplication by `F` on `Sⁿ` and the coordinatewise reduction `Sⁿ → Rⁿ`.
  set μ := ((F • 1 : Matrix n n S).mulVecLin).restrictScalars A
  set p : (n → S) →ₗ[A] (n → R) := π.toLinearMap.compLeft n
  have hπF : π F = 0 := RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self F)
  have hp : Function.Surjective p := hπ.comp_left
  have hμ : Function.Injective μ := fun x y h ↦ funext fun i ↦ hF <| by
    simpa [μ] using congr_fun h i
  have hμp : Function.Exact μ p := fun x ↦ by
    simp only [Set.mem_range]
    refine ⟨fun h ↦ ?_, ?_⟩
    · have hx i : ∃ a, a * F = x i := by
        rw [← Ideal.mem_span_singleton', ← hker, RingHom.mem_ker]
        exact congr_fun h i
      exact ⟨fun i ↦ (hx i).choose, funext fun i ↦ by simp [μ, mul_comm F, (hx i).choose_spec]⟩
    · rintro ⟨y, rfl⟩
      ext i
      simp [μ, p, hπF]
  have hcomm (M : Matrix n n S) :
      p ∘ₗ M.mulVecLin.restrictScalars A = (M.map π).mulVecLin.restrictScalars A ∘ₗ p := by
    refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
    simp [p, Matrix.mulVec, dotProduct, map_sum]
  -- Tensoring with `N` keeps `p` surjective and `μ, p` exact, and keeps `μ` injective since
  -- the cokernel `Rⁿ` of `μ` is `A`-flat. Then lift and cancel.
  exact Function.Exact.of_lift_of_comp_eq (LinearMap.rTensor_surjective N hp)
    ((LinearMap.lTensor_inj_iff_rTensor_inj N μ).mp
      (LinearMap.lTensor_injective_of_exact_of_flat p hp μ hμ hμp N))
    (rTensor_exact N hμp hp) (f := (Φ.mulVecLin.restrictScalars A).rTensor N)
    (g := (Ψ.mulVecLin.restrictScalars A).rTensor N)
    (hf := by simp only [← LinearMap.rTensor_comp, hcomm])
    (hg := by simp only [← LinearMap.rTensor_comp, hcomm])
    (hgf := by simp only [μ, ← LinearMap.rTensor_comp, ← LinearMap.restrictScalars_comp,
      ← Matrix.mulVecLin_mul, hΨΦ])
    (hgμ := by simp only [μ, ← LinearMap.rTensor_comp, ← LinearMap.restrictScalars_comp,
      ← Matrix.mulVecLin_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])
    (hfg := by
      have : (Φ * Ψ).map π = 0 := by
        ext
        simp [hΦΨ, hπF]
      rw [← LinearMap.rTensor_comp, ← LinearMap.restrictScalars_comp, ← Matrix.mulVecLin_mul,
        ← Matrix.map_mul, this, Matrix.mulVecLin_zero, LinearMap.restrictScalars_zero,
        LinearMap.rTensor_zero])

end Matrix
