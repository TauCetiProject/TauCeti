/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal
public import TauCeti.LinearAlgebra.Unimodular

/-!
# Finite tensor products of comodules and their pure tensors

A family of finitely generated comodules indexed by `Fin d` has a right-associated tensor
product, with the trivial comodule on the base as its empty product. This construction uses
the existing binary tensor comodule and tensor unit. A family of vectors determines a pure
tensor, and unimodularity of each factor makes the pure tensor unimodular.

## Main declarations

* `TauCeti.FGComoduleCat.tensorFin`: the right-associated tensor product of a finite family.
* `TauCeti.FGComoduleCat.tensorFinVector`: the pure tensor of a family of vectors.
* `TauCeti.FGComoduleCat.isUnimodular_tensorFinVector`: unimodularity of the pure tensor.

## References

* M. E. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v

variable (R : Type u) [CommSemiring R] (C : Type v) [Semiring C] [Bialgebra R C]

/-- The right-associated tensor product of a finite family of finite comodules, with the
trivial tensor unit as the empty product. -/
@[expose]
noncomputable def tensorFin : (d : ℕ) →
    (Fin d → FGComoduleCat.{u, v, u} R C) → FGComoduleCat.{u, v, u} R C
  | 0, _ => tensorUnit R C
  | d + 1, M => tensor R C (M 0) (tensorFin d (fun i ↦ M i.succ))

/-- The empty tensor product is the trivial tensor unit. -/
@[simp]
theorem tensorFin_zero (M : Fin 0 → FGComoduleCat.{u, v, u} R C) :
    tensorFin R C 0 M = tensorUnit R C := by rfl

/-- A nonempty finite tensor product separates its first factor. -/
@[simp]
theorem tensorFin_succ {d : ℕ} (M : Fin (d + 1) → FGComoduleCat.{u, v, u} R C) :
    tensorFin R C (d + 1) M =
      tensor R C (M 0) (tensorFin R C d (fun i ↦ M i.succ)) := by rfl

/-- The pure tensor determined by a finite family of vectors. Its empty value is one in
the trivial tensor unit. -/
noncomputable def tensorFinVector : {d : ℕ} →
    (M : Fin d → FGComoduleCat.{u, v, u} R C) →
    ((i : Fin d) → M i) → tensorFin R C d M
  | 0, _, _ => (1 : R)
  | d + 1, M, m => m 0 ⊗ₜ[R] tensorFinVector (fun i : Fin d ↦ M i.succ) (fun i ↦ m i.succ)

/-- The empty pure tensor is one in the trivial tensor unit. -/
@[simp]
theorem tensorFinVector_zero (M : Fin 0 → FGComoduleCat.{u, v, u} R C)
    (m : (i : Fin 0) → M i) : tensorFinVector R C M m = (1 : R) := by rfl

/-- A nonempty pure tensor separates its first vector. -/
@[simp]
theorem tensorFinVector_succ {d : ℕ} (M : Fin (d + 1) → FGComoduleCat.{u, v, u} R C)
    (m : (i : Fin (d + 1)) → M i) :
    tensorFinVector R C M m =
      m 0 ⊗ₜ[R] tensorFinVector R C (fun i : Fin d ↦ M i.succ) (fun i ↦ m i.succ) := by rfl

/-- A pure tensor of a finite family of unimodular vectors is unimodular, including the
empty pure tensor. -/
theorem isUnimodular_tensorFinVector {d : ℕ}
    (M : Fin d → FGComoduleCat.{u, v, u} R C) (m : (i : Fin d) → M i)
    (hm : ∀ i, Module.IsUnimodular R (m i)) :
    Module.IsUnimodular R (tensorFinVector R C M m) := by
  induction d with
  | zero =>
      exact Module.isUnimodular_of_apply_eq_one (f := LinearMap.id (R := R) (M := R)) rfl
  | succ d ih => exact (hm 0).tmul (ih _ _ fun i ↦ hm i.succ)

end TauCeti.FGComoduleCat
