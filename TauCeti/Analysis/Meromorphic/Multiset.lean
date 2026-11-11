/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Meromorphic multiset products and their orders

A multiset product of meromorphic functions is meromorphic, and its order at a point is the
sum of the orders, including repetitions. Pointwise and function-algebra products are both
supported, as are meromorphy on a set and global meromorphy. These extend Mathlib's corresponding
finite-set product statements to families with multiplicities.
-/

public section

variable {𝕜 𝕜' ι : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {m : Multiset ι} {f : ι → 𝕜 → 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-- A multiset product of functions meromorphic at a point is meromorphic there. -/
@[fun_prop]
theorem MeromorphicAt.multisetProd (hf : ∀ i ∈ m, MeromorphicAt (f i) x) :
    MeromorphicAt (m.map f).prod x := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Pi.one_def]
    exact MeromorphicAt.const (1 : 𝕜') x
  | cons i m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (hf i (Multiset.mem_cons_self _ _)).mul
      (ih fun j hj ↦ hf j (Multiset.mem_cons_of_mem hj))

/-- The pointwise multiset product preserves meromorphy at a point. -/
@[fun_prop]
theorem MeromorphicAt.fun_multisetProd (hf : ∀ i ∈ m, MeromorphicAt (f i) x) :
    MeromorphicAt (fun z ↦ (m.map fun i ↦ f i z).prod) x := by
  convert MeromorphicAt.multisetProd hf using 1
  funext z
  simp only [Pi.multiset_prod_apply, Multiset.map_map, Function.comp_def]

/-- Multiset products of functions meromorphic on a set are meromorphic on that set. -/
@[fun_prop]
theorem MeromorphicOn.multisetProd (hf : ∀ i ∈ m, MeromorphicOn (f i) U) :
    MeromorphicOn (m.map f).prod U :=
  fun x hx ↦ MeromorphicAt.multisetProd (fun i hi ↦ hf i hi x hx)

/-- Pointwise multiset products preserve meromorphy on a set. -/
@[fun_prop]
theorem MeromorphicOn.fun_multisetProd (hf : ∀ i ∈ m, MeromorphicOn (f i) U) :
    MeromorphicOn (fun z ↦ (m.map fun i ↦ f i z).prod) U :=
  fun x hx ↦ MeromorphicAt.fun_multisetProd (fun i hi ↦ hf i hi x hx)

/-- A multiset product of globally meromorphic functions is globally meromorphic. -/
@[fun_prop]
theorem Meromorphic.multisetProd (hf : ∀ i ∈ m, Meromorphic (f i)) :
    Meromorphic (m.map f).prod :=
  fun x ↦ MeromorphicAt.multisetProd (fun i hi ↦ hf i hi x)

/-- Pointwise multiset products preserve global meromorphy. -/
@[fun_prop]
theorem Meromorphic.fun_multisetProd (hf : ∀ i ∈ m, Meromorphic (f i)) :
    Meromorphic (fun z ↦ (m.map fun i ↦ f i z).prod) :=
  fun x ↦ MeromorphicAt.fun_multisetProd (fun i hi ↦ hf i hi x)

/-- The order of a multiset product is the sum of its factors' orders, including repetitions. -/
theorem meromorphicOrderAt_multisetProd (hf : ∀ i ∈ m, MeromorphicAt (f i) x) :
    meromorphicOrderAt (m.map f).prod x = (m.map fun i ↦ meromorphicOrderAt (f i) x).sum := by
  induction m using Multiset.induction_on with
  | empty =>
    classical
    simp [Pi.one_def, meromorphicOrderAt_const]
  | cons i m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [meromorphicOrderAt_mul (hf i (Multiset.mem_cons_self _ _))
      (MeromorphicAt.multisetProd (fun j hj ↦ hf j (Multiset.mem_cons_of_mem hj))),
      ih (fun j hj ↦ hf j (Multiset.mem_cons_of_mem hj))]

/-- The order of the pointwise multiset product is the sum of the factor orders. -/
theorem meromorphicOrderAt_fun_multisetProd (hf : ∀ i ∈ m, MeromorphicAt (f i) x) :
    meromorphicOrderAt (fun z ↦ (m.map fun i ↦ f i z).prod) x =
      (m.map fun i ↦ meromorphicOrderAt (f i) x).sum := by
  convert meromorphicOrderAt_multisetProd hf using 1
  congr 1
  funext z
  simp only [Pi.multiset_prod_apply, Multiset.map_map, Function.comp_def]
