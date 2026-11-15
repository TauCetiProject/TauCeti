/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.FilteredAlgebra.Equiv

/-!
# Functoriality of completed tensor products

Tensoring filtered algebra maps preserves total degree. With independent monotone
cutoff moduli, their pointwise sum is a cutoff for the tensor map. The induced map
on completions sends a pure tensor to the pure tensor of the images. Factor exchange
also extends to an algebra equivalence of completions, reversing pure tensors.
These comparisons allow completed coproduct identities to be transported between
filtered coefficient algebras. Multiplication may be noncommutative; no flatness
or separatedness is required.

Adapted from `Mei/RingTheory/FilteredAlgebra/TensorProduct/{Basic,Completion}.lean`
in [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section Semiring

variable (R : Type*) {A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (F : AlgFiltration A) (G : AlgFiltration B)

/-- Tensoring filtration-preserving algebra maps preserves the total-degree filtration. -/
theorem tensorProduct_ideal_le_comap_map {C D : Type*} [Semiring C] [Semiring D]
    [Algebra R C] [Algebra R D] (H : AlgFiltration C) (K : AlgFiltration D)
    (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : ∀ k, F.ideal k ≤ (H.ideal k).comap f)
    (hg : ∀ k, G.ideal k ≤ (K.ideal k).comap g) (k : ℕ) :
    (F.tensorProduct R G).ideal k ≤
      ((H.tensorProduct R K).ideal k).comap (Algebra.TensorProduct.map f g) := by
  intro x hx
  apply (H.mem_tensorProduct_ideal_iff R K).mpr
  exact tensorFiltrationTail_le_comap_map
    (fun n => (F.ideal n).restrictScalars R) (fun n => (G.ideal n).restrictScalars R)
    (fun n => (H.ideal n).restrictScalars R) (fun n => (K.ideal n).restrictScalars R)
    f.toLinearMap g.toLinearMap hf hg k ((F.mem_tensorProduct_ideal_iff R G).mp hx)

/-- The sum of independent cutoff moduli bounds the tensor map at each order.
Monotonicity of the moduli is not needed for this finite-order bound. -/
theorem tensorProduct_ideal_le_comap_map_of_moduli {C D : Type*} [Semiring C] [Semiring D]
    [Algebra R C] [Algebra R D] (H : AlgFiltration C) (K : AlgFiltration D)
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (ρ σ : ℕ → ℕ)
    (hf : ∀ k, F.ideal (ρ k + 1) ≤ (H.ideal (k + 1)).comap f)
    (hg : ∀ k, G.ideal (σ k + 1) ≤ (K.ideal (k + 1)).comap g) (k : ℕ) :
    (F.tensorProduct R G).ideal (ρ k + σ k + 1) ≤
      ((H.tensorProduct R K).ideal (k + 1)).comap (Algebra.TensorProduct.map f g) := by
  have bound : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
      (fun n => (G.ideal n).restrictScalars R) (ρ k + σ k + 1) ≤
      (((H.tensorProduct R K).ideal (k + 1)).restrictScalars R).comap
        (Algebra.TensorProduct.map f g).toLinearMap := by
    refine tensorFiltrationTail_le_iff _ _ |>.mpr ?_
    intro a b hab x hx y hy
    simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul]
    by_cases ha : ρ k + 1 ≤ a
    · exact H.tmul_mem_tensorProduct_ideal R K (a := k + 1) (b := 0) (by omega)
        (hf k (F.antitone ha hx)) (by simp)
    · have hb : σ k + 1 ≤ b := by omega
      exact H.tmul_mem_tensorProduct_ideal R K (a := 0) (b := k + 1) (by omega)
        (by simp) (hg k (G.antitone hb hy))
  intro x hx
  exact bound ((F.mem_tensorProduct_ideal_iff R G).mp hx)

/-- Factor exchange identifies the total-degree tensor ideals. -/
@[simp]
theorem tensorProduct_ideal_comap_comm (k : ℕ) :
    ((G.tensorProduct R F).ideal k).comap (Algebra.TensorProduct.comm R A B).toAlgHom =
      (F.tensorProduct R G).ideal k := by
  have hc : (Algebra.TensorProduct.comm R A B).toLinearEquiv =
      TensorProduct.comm R A B := Algebra.TensorProduct.comm_toLinearEquiv R A B
  ext x
  simpa only [Ideal.mem_comap, mem_tensorProduct_ideal_iff, Submodule.mem_comap,
    AlgEquiv.coe_toAlgHom, ← AlgEquiv.toLinearEquiv_apply, hc, LinearEquiv.coe_coe] using
    SetLike.ext_iff.mp (tensorFiltrationTail_comap_comm
    (fun n => (F.ideal n).restrictScalars R) (fun n => (G.ideal n).restrictScalars R) k) x

end Semiring

section Ring

variable (R : Type*) {A B : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] (F : AlgFiltration A) (G : AlgFiltration B)

/-- Exchanging the factors induces an algebra equivalence of completed tensor products. -/
noncomputable def completedTensorComm :
    (F.tensorProduct R G).completion ≃ₐ[R] (G.tensorProduct R F).completion :=
  (F.tensorProduct R G).completionEquiv (G.tensorProduct R F)
    (Algebra.TensorProduct.comm R A B)
    (tensorProduct_ideal_comap_comm R F G)

/-- Completed factor exchange is the completion of the tensor factor equivalence. -/
theorem completedTensorComm_eq_completionEquiv :
    F.completedTensorComm R G =
      (F.tensorProduct R G).completionEquiv (G.tensorProduct R F)
        (Algebra.TensorProduct.comm R A B) (tensorProduct_ideal_comap_comm R F G) := (rfl)

/-- Completed factor exchange preserves and reflects every completed filtration ideal. -/
@[simp]
theorem completedTensorComm_mem_completionIdeal_iff (k : ℕ)
    (x : (F.tensorProduct R G).completion) :
    F.completedTensorComm R G x ∈ (G.tensorProduct R F).completionIdeal k ↔
      x ∈ (F.tensorProduct R G).completionIdeal k := by
  rw [completedTensorComm_eq_completionEquiv, completionEquiv_mem_completionIdeal_iff]

/-- Completed factor exchange identifies completed filtration ideals by comap. -/
@[simp]
theorem completionIdeal_comap_completedTensorComm (k : ℕ) :
    ((G.tensorProduct R F).completionIdeal k).comap (F.completedTensorComm R G).toAlgHom =
      (F.tensorProduct R G).completionIdeal k := by
  rw [completedTensorComm_eq_completionEquiv, completionIdeal_comap_completionEquiv]

/-- The finite projections of factor exchange are the induced quotient maps. -/
@[simp]
theorem projection_completedTensorComm (k : ℕ) (x : (F.tensorProduct R G).completion) :
    (G.tensorProduct R F).projection k (F.completedTensorComm R G x) =
      Ideal.quotientMapₐ ((G.tensorProduct R F).ideal (k + 1))
        (Algebra.TensorProduct.comm R A B).toAlgHom
        (by rw [tensorProduct_ideal_comap_comm])
        ((F.tensorProduct R G).projection k x) :=
  (F.tensorProduct R G).projection_completionEquiv (G.tensorProduct R F)
    (Algebra.TensorProduct.comm R A B)
    (tensorProduct_ideal_comap_comm R F G) k x

/-- On original tensors the completed exchange is the original factor exchange. -/
@[simp]
theorem completedTensorComm_toCompletion (t : A ⊗[R] B) :
    F.completedTensorComm R G ((F.tensorProduct R G).toCompletion t) =
      (G.tensorProduct R F).toCompletion (Algebra.TensorProduct.comm R A B t) :=
  (F.tensorProduct R G).completionEquiv_toCompletion (G.tensorProduct R F)
    (Algebra.TensorProduct.comm R A B)
    (tensorProduct_ideal_comap_comm R F G) t

/-- Factor exchange reverses arbitrary completed pure tensors. -/
@[simp]
theorem completedTensorComm_completedTensor (x : F.completion) (y : G.completion) :
    F.completedTensorComm R G (F.completedTensor R G x y) =
      G.completedTensor R F y x := by
  apply (G.tensorProduct R F).completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (G.projection k y)
  rw [projection_completedTensorComm,
    F.projection_completedTensor_of_representatives R G k x y a b ha hb,
    G.projection_completedTensor_of_representatives R F k y x b a hb ha]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.comm_tmul]

/-- The inverse completed exchange is the exchange in the opposite order. -/
@[simp]
theorem completedTensorComm_symm :
    (F.completedTensorComm R G).symm = G.completedTensorComm R F := by
  simp only [completedTensorComm, completionEquiv_symm, Algebra.TensorProduct.comm_symm]

/-- Tensoring maps with independent monotone cutoff moduli commutes with completed pure
tensors. The tensor map uses the sum of the two cutoffs. -/
theorem mapCompletionₐ_completedTensor_of_moduli {C D : Type*} [Ring C] [Ring D]
    [Algebra R C] [Algebra R D] (H : AlgFiltration C) (K : AlgFiltration D)
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (ρ σ : ℕ → ℕ)
    (hρ : Monotone ρ) (hσ : Monotone σ)
    (hf : ∀ k, F.ideal (ρ k + 1) ≤ (H.ideal (k + 1)).comap f)
    (hg : ∀ k, G.ideal (σ k + 1) ≤ (K.ideal (k + 1)).comap g)
    (x : F.completion) (y : G.completion) :
    (F.tensorProduct R G).mapCompletionₐ (H.tensorProduct R K)
      (Algebra.TensorProduct.map f g) (fun k => ρ k + σ k) (hρ.add hσ)
      (F.tensorProduct_ideal_le_comap_map_of_moduli R G H K f g ρ σ hf hg)
      (F.completedTensor R G x y) =
      H.completedTensor R K (F.mapCompletionₐ H f ρ hρ hf x)
        (G.mapCompletionₐ K g σ hσ hg y) := by
  apply (H.tensorProduct R K).completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection (ρ k + σ k) x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (G.projection (ρ k + σ k) y)
  have ha' : Ideal.Quotient.mk (F.ideal (ρ k + 1)) a = F.projection (ρ k) x := by
    simpa only [← ha, Ideal.Quotient.factor_mk] using
      F.factor_projection (Nat.le_add_right (ρ k) (σ k)) x
  have hb' : Ideal.Quotient.mk (G.ideal (σ k + 1)) b = G.projection (σ k) y := by
    simpa only [← hb, Ideal.Quotient.factor_mk] using
      G.factor_projection (Nat.le_add_left (σ k) (ρ k)) y
  rw [projection_mapCompletionₐ,
    F.projection_completedTensor_of_representatives R G _ x y a b ha hb]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Algebra.TensorProduct.map_tmul]
  exact (H.projection_completedTensor_of_representatives R K k _ _ (f a) (g b)
    (by simp [projection_mapCompletionₐ, ← ha'])
    (by simp [projection_mapCompletionₐ, ← hb'])).symm

/-- Tensoring filtration-preserving maps commutes with completed pure tensors at the same
cutoff in both factors. -/
theorem mapCompletionₐ_completedTensor {C D : Type*} [Ring C] [Ring D]
    [Algebra R C] [Algebra R D] (H : AlgFiltration C) (K : AlgFiltration D)
    (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : ∀ k, F.ideal k ≤ (H.ideal k).comap f)
    (hg : ∀ k, G.ideal k ≤ (K.ideal k).comap g)
    (x : F.completion) (y : G.completion) :
    (F.tensorProduct R G).mapCompletionₐ (H.tensorProduct R K)
      (Algebra.TensorProduct.map f g) id monotone_id
      (fun k => F.tensorProduct_ideal_le_comap_map R G H K f g hf hg (k + 1))
      (F.completedTensor R G x y) =
      H.completedTensor R K
        (F.mapCompletionₐ H f id monotone_id (fun k => hf (k + 1)) x)
        (G.mapCompletionₐ K g id monotone_id (fun k => hg (k + 1)) y) := by
  rw [(F.tensorProduct R G).mapCompletionₐ_eq (H.tensorProduct R K)
    (Algebra.TensorProduct.map f g) id monotone_id _ (fun k => k + k)
    (monotone_id.add monotone_id)
    (F.tensorProduct_ideal_le_comap_map_of_moduli R G H K f g id id
      (fun k => hf (k + 1)) (fun k => hg (k + 1)))]
  exact F.mapCompletionₐ_completedTensor_of_moduli R G H K f g id id
    monotone_id monotone_id (fun k => hf (k + 1)) (fun k => hg (k + 1)) x y

end Ring

end TauCeti.AlgFiltration
