/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.TrivSqZeroExt.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Degree-zero derivations of an exterior algebra

Every `R`-linear endomorphism `f : M →ₗ[R] M` extends uniquely to an `R`-linear degree-zero
derivation `TauCeti.ExteriorAlgebra.liftDeriv f` of `ExteriorAlgebra R M`, characterized by
`liftDeriv f (ι R m) = ι R (f m)` and the Leibniz rule
`liftDeriv f (x * y) = liftDeriv f x * y + x * liftDeriv f y`.

The extension is linear in `f`, preserves the Lie bracket `[f, g] = f ∘ g - g ∘ f`, commutes with
the grade involution, preserves each exterior power `⋀[R]^n M`, acts as multiplication by `n` on
`⋀[R]^n M` when `f = id`, and is natural with respect to `ExteriorAlgebra.map`.

## Main definitions

* `TauCeti.ExteriorAlgebra.liftDeriv`: the `R`-linear map lifting endomorphisms of `M` to
  degree-zero derivations of `ExteriorAlgebra R M`.

## Main results

* `TauCeti.ExteriorAlgebra.liftDeriv_ι`: `liftDeriv f (ι R m) = ι R (f m)`.
* `TauCeti.ExteriorAlgebra.liftDeriv_mul`: the Leibniz rule for `liftDeriv f`.
* `TauCeti.ExteriorAlgebra.liftDeriv_unique`: uniqueness among degree-zero derivations.
* `TauCeti.ExteriorAlgebra.liftDeriv_comp_sub_comp`: compatibility with the commutator bracket.
* `TauCeti.ExteriorAlgebra.liftDeriv_mem_exteriorPower`: `liftDeriv f` preserves `⋀[R]^n M`.
* `TauCeti.ExteriorAlgebra.liftDeriv_id_of_mem_exteriorPower`: `liftDeriv id` acts as `n • ·` on
  `⋀[R]^n M`.
* `TauCeti.ExteriorAlgebra.liftDeriv_ιMulti`: action on a wedge product of vectors.

## Implementation notes

The derivation is constructed via the universal property `ExteriorAlgebra.lift` into the trivial
square-zero extension `TrivSqZeroExt (ExteriorAlgebra R M) (ExteriorAlgebra R M)`, sending
`m ↦ inl (ι R m) + inr (ι R (f m))`. The squaring relation holds over any commutative ring,
including in characteristic two, because `ι R m * ι R m = 0` and
`ι R m * ι R (f m) + ι R (f m) * ι R m = 0`.
-/

public section

open ExteriorAlgebra TrivSqZeroExt

namespace TauCeti.ExteriorAlgebra

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The algebra map into `TrivSqZeroExt (⋀ M) (⋀ M)` sending `ι m` to `ι m + ε ι (f m)`. -/
private def liftDerivAlgHom (f : M →ₗ[R] M) :
    ExteriorAlgebra R M →ₐ[R] TrivSqZeroExt (ExteriorAlgebra R M) (ExteriorAlgebra R M) :=
  ExteriorAlgebra.lift R
    ⟨(inlAlgHom R (ExteriorAlgebra R M) (ExteriorAlgebra R M)).toLinearMap.comp (ι R) +
      ((inrHom (ExteriorAlgebra R M) (ExteriorAlgebra R M)).restrictScalars R).comp
        ((ι R).comp f), fun m ↦ by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        inlAlgHom_apply, LinearMap.coe_restrictScalars, inrHom_apply, add_mul, mul_add,
        inl_mul_inl, inl_mul_inr, inr_mul_inl, inr_mul_inr, ι_sq_zero, inl_zero, zero_add,
        add_zero, smul_eq_mul, op_smul_eq_mul, ← inr_add, ι_add_mul_swap, inr_zero]⟩

private theorem liftDerivAlgHom_fst (f : M →ₗ[R] M) (x : ExteriorAlgebra R M) :
    fst (liftDerivAlgHom f x) = x := by
  have h : (fstHom R (ExteriorAlgebra R M) (ExteriorAlgebra R M)).comp (liftDerivAlgHom f) =
      AlgHom.id R (ExteriorAlgebra R M) := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp [liftDerivAlgHom]
  exact AlgHom.congr_fun h x

/-- The underlying degree-zero derivation induced by `f : M →ₗ[R] M`. -/
private def liftDerivAux (f : M →ₗ[R] M) : Module.End R (ExteriorAlgebra R M) :=
  ((sndHom (ExteriorAlgebra R M) (ExteriorAlgebra R M)).restrictScalars R).comp
    (liftDerivAlgHom f).toLinearMap

private theorem liftDerivAux_ι (f : M →ₗ[R] M) (m : M) :
    liftDerivAux f (ι R m) = ι R (f m) := by
  simp [liftDerivAux, liftDerivAlgHom]

private theorem liftDerivAux_mul (f : M →ₗ[R] M) (x y : ExteriorAlgebra R M) :
    liftDerivAux f (x * y) = liftDerivAux f x * y + x * liftDerivAux f y := by
  simp only [liftDerivAux, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.coe_restrictScalars, sndHom_apply, map_mul, snd_mul, liftDerivAlgHom_fst,
    smul_eq_mul, op_smul_eq_mul, add_comm]

private theorem deriv_eq_of_eq_on_ι {D₁ D₂ : Module.End R (ExteriorAlgebra R M)}
    (h₁ : ∀ x y, D₁ (x * y) = D₁ x * y + x * D₁ y)
    (h₂ : ∀ x y, D₂ (x * y) = D₂ x * y + x * D₂ y)
    (hι : ∀ m, D₁ (ι R m) = D₂ (ι R m)) : D₁ = D₂ := by
  have h1₁ : D₁ 1 = 0 := by
    have h := h₁ 1 1
    simp only [mul_one, one_mul, left_eq_add] at h
    exact h
  have h1₂ : D₂ 1 = 0 := by
    have h := h₂ 1 1
    simp only [mul_one, one_mul, left_eq_add] at h
    exact h
  refine LinearMap.ext fun x ↦ ?_
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1₁, h1₂]
  | ι m => exact hι m
  | mul x y hx hy => rw [h₁, h₂, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Degree-zero derivation lift on an exterior algebra**: the unique `R`-linear map sending
`f : M →ₗ[R] M` to the degree-zero derivation of `ExteriorAlgebra R M` acting as `ι R m ↦ ι R (f m)`
on generators. -/
def liftDeriv : (M →ₗ[R] M) →ₗ[R] Module.End R (ExteriorAlgebra R M) where
  toFun := liftDerivAux
  map_add' f g := by
    refine deriv_eq_of_eq_on_ι (liftDerivAux_mul (f + g)) (fun x y ↦ ?_) (fun m ↦ ?_)
    · simp only [LinearMap.add_apply, liftDerivAux_mul, add_mul, mul_add]
      abel
    · simp [liftDerivAux_ι]
  map_smul' r f := by
    refine deriv_eq_of_eq_on_ι (liftDerivAux_mul (r • f)) (fun x y ↦ ?_) (fun m ↦ ?_)
    · simp only [RingHom.id_apply, LinearMap.smul_apply, liftDerivAux_mul, smul_add,
        smul_mul_assoc, mul_smul_comm]
    · simp [liftDerivAux_ι]

/-- On a degree-one generator, `liftDeriv f` applies `f` inside `ι`. -/
@[simp]
theorem liftDeriv_ι (f : M →ₗ[R] M) (m : M) : liftDeriv f (ι R m) = ι R (f m) :=
  liftDerivAux_ι f m

/-- `liftDeriv f` satisfies the degree-zero Leibniz rule on products. -/
theorem liftDeriv_mul (f : M →ₗ[R] M) (x y : ExteriorAlgebra R M) :
    liftDeriv f (x * y) = liftDeriv f x * y + x * liftDeriv f y :=
  liftDerivAux_mul f x y

/-- `liftDeriv f` vanishes on `1`. -/
@[simp]
theorem liftDeriv_one (f : M →ₗ[R] M) : liftDeriv f 1 = 0 := by
  have h := liftDeriv_mul f 1 1
  simp only [mul_one, one_mul, left_eq_add] at h
  exact h

/-- `liftDeriv f` vanishes on scalars. -/
@[simp]
theorem liftDeriv_algebraMap (f : M →ₗ[R] M) (r : R) :
    liftDeriv f (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, liftDeriv_one, smul_zero]

/-- **Uniqueness of the degree-zero derivation lift**: any `R`-linear derivation of
`ExteriorAlgebra R M` agreeing with `ι R ∘ f` on degree-one generators equals `liftDeriv f`. -/
theorem liftDeriv_unique (f : M →ₗ[R] M) (D : Module.End R (ExteriorAlgebra R M))
    (hmul : ∀ x y, D (x * y) = D x * y + x * D y)
    (hι : ∀ m, D (ι R m) = ι R (f m)) : D = liftDeriv f :=
  deriv_eq_of_eq_on_ι hmul (liftDeriv_mul f) (fun m ↦ by rw [hι, liftDeriv_ι])

/-- `liftDeriv` intertwines the commutator bracket on `M →ₗ[R] M` with the commutator bracket of
derivations on `ExteriorAlgebra R M`. -/
theorem liftDeriv_comp_sub_comp (f g : M →ₗ[R] M) :
    liftDeriv (f.comp g - g.comp f) =
      (liftDeriv f).comp (liftDeriv g) - (liftDeriv g).comp (liftDeriv f) := by
  symm
  refine liftDeriv_unique (f.comp g - g.comp f) _ (fun x y ↦ ?_) (fun m ↦ ?_)
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, liftDeriv_mul, map_add, sub_mul, mul_sub]
    abel
  · simp

/-- Commuting endomorphisms of `M` lift to commuting derivations of `ExteriorAlgebra R M`. -/
theorem liftDeriv_comm {f g : M →ₗ[R] M} (h : f.comp g = g.comp f) (x : ExteriorAlgebra R M) :
    liftDeriv f (liftDeriv g x) = liftDeriv g (liftDeriv f x) := by
  have hc := congrArg (fun T : Module.End R (ExteriorAlgebra R M) ↦ T x)
    (liftDeriv_comp_sub_comp f g)
  rw [h, sub_self, map_zero, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, eq_comm, sub_eq_zero] at hc
  exact hc

/-- Every lifted degree-zero derivation commutes with the grade involution. -/
theorem liftDeriv_involute (f : M →ₗ[R] M) (x : ExteriorAlgebra R M) :
    liftDeriv f (CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) x) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (liftDeriv f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [AlgHom.commutes]
  | ι m => simp [CliffordAlgebra.involute_ι]
  | mul x y hx hy =>
    simp only [map_mul, liftDeriv_mul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `liftDeriv f` preserves each exterior power `⋀[R]^n M`. -/
theorem liftDeriv_mem_exteriorPower (f : M →ₗ[R] M) {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) : liftDeriv f x ∈ ⋀[R]^n M := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [liftDeriv_mul, liftDeriv_ι]
    exact add_mem (ι_mul_mem_exteriorPower (f v) hx) (ι_mul_mem_exteriorPower v ih)

/-- **Euler degree operator**: lifting the identity endomorphism multiplies the `n`-th exterior
power by `n`. -/
theorem liftDeriv_id_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) : liftDeriv (LinearMap.id : M →ₗ[R] M) x = n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x _ ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [liftDeriv_mul, liftDeriv_ι, LinearMap.id_apply, ih, mul_smul_comm, succ_nsmul']

/-- Naturality of `liftDeriv` under a linear map `φ : M →ₗ[R] N` intertwining `f` and `g`. -/
theorem liftDeriv_map {N : Type*} [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N)
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : φ.comp f = g.comp φ) (x : ExteriorAlgebra R M) :
    liftDeriv g (ExteriorAlgebra.map φ x) = ExteriorAlgebra.map φ (liftDeriv f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m =>
    have hm : φ (f m) = g (φ m) := LinearMap.congr_fun h m
    simp [hm]
  | mul x y hx hy => simp only [map_mul, liftDeriv_mul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Action of `liftDeriv f` on a wedge product of `n` vectors: the sum over positions of applying
`f` to the `i`-th factor. -/
theorem liftDeriv_ιMulti (f : M →ₗ[R] M) {n : ℕ} (v : Fin n → M) :
    liftDeriv f (ιMulti R n v) =
      ∑ i : Fin n, ιMulti R n (Function.update v i (f (v i))) := by
  induction n with
  | zero => simp [ιMulti_zero_apply]
  | succ n ih =>
    rw [ιMulti_succ_apply, liftDeriv_mul, liftDeriv_ι, ih, Finset.mul_sum, Fin.sum_univ_succ]
    congr 1
    · rw [ιMulti_succ_apply, Function.update_self]
      congr 2
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ιMulti_succ_apply, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      ext j
      by_cases hji : j = i
      · subst hji
        simp [Matrix.vecTail]
      · simp [Matrix.vecTail, Function.update_of_ne hji,
          Function.update_of_ne ((Fin.succ_injective n).ne hji)]

end

end TauCeti.ExteriorAlgebra
