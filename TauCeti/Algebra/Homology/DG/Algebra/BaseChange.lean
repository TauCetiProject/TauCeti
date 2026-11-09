/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.Algebra.Homology.DG.Algebra.Defs

/-!
# Base change of differential graded algebras

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, and let `S` be a
commutative `R`-algebra. The base change `S ⊗[R] A`, graded by the base changes `S ⊗[R] Aᵖ` of the
homogeneous pieces (Mathlib's `GradedAlgebra.baseChange`), with differential `1 ⊗ d`, is a
differential graded algebra over `S`. No flatness of `S` is needed: every axiom is an identity
between `R`-multilinear expressions in homogeneous elements, and these are preserved by
`S ⊗[R] -`.

The degree law and the graded Leibniz rule are transported separately, with the corresponding law
for `d` as a hypothesis, so that the base change of curved differential graded algebras in
`TauCeti.Algebra.Homology.Curved.Algebra.BaseChange` shares these arguments.

## Main results

* `TauCeti.map_mem_baseChange_of_map_mem`: the base change of a degree-one map has degree one.
* `TauCeti.leibniz_baseChange_of_leibniz`: the base change of a map satisfying the graded Leibniz
  rule satisfies it.
* `TauCeti.IsDGAlgebra.baseChange`: the base change of a differential graded algebra, with
  differential `1 ⊗ d`.
-/

public section

open TensorProduct

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Type*) [CommRing S] [Algebra R S]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}

/-- The base change `1 ⊗ d` of a linear map `d` raising degree by one raises degree by one for the
base-changed pieces `S ⊗[R] Aᵖ`. -/
theorem map_mem_baseChange_of_map_mem (hd : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p + 1))
    {p : ℤ} {x : S ⊗[R] A} (hx : x ∈ (𝒜 p).baseChange S) :
    d.baseChange S x ∈ (𝒜 (p + 1)).baseChange S := by
  obtain ⟨x, rfl⟩ := Submodule.toBaseChange_surjective' _ _ hx
  clear hx
  induction x with
  | tmul s a => simpa using Submodule.tmul_mem_baseChange_of_mem s (hd a.2)
  | add x y hx hy => simpa using add_mem hx hy

/-- The base change `1 ⊗ d` of a linear map `d` satisfying the graded Leibniz rule on a
homogeneous left factor satisfies it for the base-changed pieces `S ⊗[R] Aᵖ`. -/
theorem leibniz_baseChange_of_leibniz
    (hl : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * b + p.negOnePow • (a * d b))
    {p : ℤ} {x : S ⊗[R] A} (hx : x ∈ (𝒜 p).baseChange S) (y : S ⊗[R] A) :
    d.baseChange S (x * y) = d.baseChange S x * y + p.negOnePow • (x * d.baseChange S y) := by
  obtain ⟨x, rfl⟩ := Submodule.toBaseChange_surjective' _ _ hx
  clear hx
  induction x with
  | add x x' hx hx' => simp only [map_add, Submodule.coe_add, add_mul, hx, hx', smul_add]; abel
  | tmul s a =>
    obtain ⟨a, ha⟩ := a
    induction y with
    | add y y' hy hy' => simp only [map_add, mul_add, hy, hy', smul_add]; abel
    | tmul t b =>
      simp only [Submodule.coe_toBaseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.baseChange_tmul, hl ha b, tmul_add, Units.smul_def, tmul_smul]

variable [GradedAlgebra 𝒜]

/-- **Base change.** For a commutative `R`-algebra `S`, the base change `S ⊗[R] A` of a
differential graded `R`-algebra, graded by the base changes of the homogeneous pieces, is a
differential graded `S`-algebra with differential `1 ⊗ d`. -/
theorem IsDGAlgebra.baseChange (h : IsDGAlgebra 𝒜 d) :
    IsDGAlgebra (fun p ↦ (𝒜 p).baseChange S) (d.baseChange S) where
  map_mem := map_mem_baseChange_of_map_mem S h.map_mem
  leibniz := leibniz_baseChange_of_leibniz S h.leibniz
  sq_zero x := by
    induction x with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul s a => simp [h.sq_zero a]

end TauCeti
