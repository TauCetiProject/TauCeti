/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Multilinear maps on blocks and contractions of a tuple

Two ways of building a multilinear map of a tuple `a = (a₀, …, aₙ₋₁)` of elements of `A` from
multilinear maps of shorter tuples, as in the operations and morphisms of `A∞` modules:

* `MultilinearMap.compSplit`: for `i + j = n`, a multilinear map `f` of `i` arguments with values
  in linear maps `N₁ → N₂` and a multilinear map `g` of `j` arguments with values in linear maps
  `N₂ → N₃` give `a ↦ g (aᵢ, …, aₙ₋₁) ∘ₗ f (a₀, …, aᵢ₋₁)`;
* `MultilinearMap.compContractNthMul`: for `A` an algebra, a multilinear map `f` of `n` arguments
  and a position `j < n` give the multilinear map
  `a ↦ f (a₀, …, aⱼ₋₁, aⱼ * aⱼ₊₁, aⱼ₊₂, …, aₙ)` of `n + 1` arguments.

They make the composite terms and the product terms of the `A∞` relations into multilinear maps
(see `TauCeti.UngradedAInfinityRightModule.morphismDifferential`), and the second gives the
Hochschild cofaces of cochains (see `TauCeti.hochschildCoface`).
-/

public section

namespace MultilinearMap

section Split

variable {R A N₁ N₂ N₃ : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃]
  [Module R N₃] {i j n : ℕ}

/-- For `i + j = n`, the multilinear map `a ↦ g (aᵢ, …, aₙ₋₁) ∘ₗ f (a₀, …, aᵢ₋₁)`, composing the
values of `f` on the first `i` entries of `a` with those of `g` on the last `j`. -/
def compSplit (h : i + j = n) (g : MultilinearMap (RingHom.id R) (fun _ : Fin j => A) (N₂ →ₗ[R] N₃))
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin i => A) (N₁ →ₗ[R] N₂)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (N₁ →ₗ[R] N₃) :=
  MultilinearMap.mk'
    (fun a => g (fun l => a (Fin.cast h (Fin.natAdd i l))) ∘ₗ
      f (fun l => a (Fin.cast h (Fin.castAdd j l))))
    (fun a p x y => by
      subst h
      obtain ⟨u, v, rfl⟩ : ∃ u v, a = Fin.append u v := ⟨_, _, Fin.append_castAdd_natAdd.symm⟩
      induction p using Fin.addCases <;> simp [LinearMap.comp_add, LinearMap.add_comp])
    (fun a p c x => by
      subst h
      obtain ⟨u, v, rfl⟩ : ∃ u v, a = Fin.append u v := ⟨_, _, Fin.append_castAdd_natAdd.symm⟩
      induction p using Fin.addCases <;> simp [LinearMap.comp_smul, LinearMap.smul_comp])

@[simp]
theorem compSplit_apply (h : i + j = n)
    (g : MultilinearMap (RingHom.id R) (fun _ : Fin j => A) (N₂ →ₗ[R] N₃))
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin i => A) (N₁ →ₗ[R] N₂)) (a : Fin n → A) :
    compSplit h g f a = g (fun l => a ⟨i + l, by omega⟩) ∘ₗ f (fun l => a ⟨l, by omega⟩) :=
  (rfl)

end Split

section Contract

variable {R A N : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommMonoid N] [Module R N] {n : ℕ}

/-- The multilinear map `a ↦ f (a₀, …, aⱼ₋₁, aⱼ * aⱼ₊₁, aⱼ₊₂, …, aₙ)` of `n + 1` arguments,
contracting the entries `j` and `j + 1` of `a` by multiplication before applying `f`. -/
def compContractNthMul (f : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) N) (j : Fin n) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) N :=
  MultilinearMap.mk' (fun a => f (Fin.contractNth j.castSucc (· * ·) a))
    (fun a p x y => by
      rcases eq_or_ne p j.succ with rfl | hp
      · simp [Fin.contractNth_castSucc_update_succ, mul_add, f.map_update_add]
      obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hp
      rcases eq_or_ne q j with rfl | hq
      · simp [Fin.contractNth_castSucc_update_castSucc, add_mul, f.map_update_add]
      · simp [Fin.contractNth_castSucc_update_succAbove _ hq, f.map_update_add])
    (fun a p c x => by
      rcases eq_or_ne p j.succ with rfl | hp
      · simp [Fin.contractNth_castSucc_update_succ, mul_smul_comm, f.map_update_smul]
      obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hp
      rcases eq_or_ne q j with rfl | hq
      · simp [Fin.contractNth_castSucc_update_castSucc, smul_mul_assoc, f.map_update_smul]
      · simp [Fin.contractNth_castSucc_update_succAbove _ hq, f.map_update_smul])

@[simp]
theorem compContractNthMul_apply (f : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) N)
    (j : Fin n) (a : Fin (n + 1) → A) :
    compContractNthMul f j a = f (Fin.contractNth j.castSucc (· * ·) a) :=
  (rfl)

end Contract

end MultilinearMap
