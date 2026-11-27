/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant.Prod

/-!
# Native determinant Whitney clients

These clients retain the projective tensor model, exercise the actual inverse total-space map,
and check the empty base and rank-zero factors. Real line factors have a negative exchange sign;
a complex line and a complex rank-two factor have positive exchange sign. No model-basis
normalization is assumed.
-/

public noncomputable section

open Bundle Module TauCeti
open scoped Bundle TensorProduct TauCeti.ModuleTopology

namespace TauCeti.DetBundle.WhitneyClients

section EmptyFactor

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module K (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle K F E]

-- The canonical empty wedge on the left acts as the identity scalar, for an arbitrary bundle.
example (x : B) (b : DetBundle K F E x) :
    (linearEquiv K ((Fin 0 → K) × F) ((Trivial B (Fin 0 → K)) ×ᵇ E) x
      (prodEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) F E x
        ((zeroEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) (by simp) x).symm 1 ⊗ₜ b)) :
      ExteriorAlgebra K ((Trivial B (Fin 0 → K)) x × E x)) =
      ExteriorAlgebra.map (LinearMap.inr K ((Trivial B (Fin 0 → K)) x) (E x))
        (linearEquiv K F E x b) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply, one_smul] using
    coe_prodEquiv_tmul_of_finrank_left_eq_zero (K := K) (F₁ := Fin 0 → K)
      (E₁ := Trivial B (Fin 0 → K)) (F₂ := F) (E₂ := E) (by simp) x
      ((zeroEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) (by simp) x).symm 1) b

-- The empty wedge also acts as the identity scalar on the right.
example (x : B) (a : DetBundle K F E x) :
    (linearEquiv K (F × (Fin 0 → K)) (E ×ᵇ (Trivial B (Fin 0 → K))) x
      (prodEquiv K F E (Fin 0 → K) (Trivial B (Fin 0 → K)) x
        (a ⊗ₜ (zeroEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) (by simp) x).symm 1)) :
      ExteriorAlgebra K (E x × (Trivial B (Fin 0 → K)) x)) =
      ExteriorAlgebra.map (LinearMap.inl K (E x) ((Trivial B (Fin 0 → K)) x))
        (linearEquiv K F E x a) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply, one_smul] using
    coe_prodEquiv_tmul_of_finrank_right_eq_zero (K := K) (F₁ := F) (E₁ := E)
      (F₂ := Fin 0 → K) (E₂ := Trivial B (Fin 0 → K)) (by simp) x a
      ((zeroEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) (by simp) x).symm 1)

-- The inverse is the actual inverse native total-space map, also for a rank-zero factor.
example (p : TotalSpace (ProjectiveTensor K K K)
    (fun x ↦ DetBundle K (Fin 0 → K) (Trivial B (Fin 0 → K)) x ⊗[K] DetBundle K F E x)) :
    (prodHomeomorph K (Fin 0 → K) (Trivial B (Fin 0 → K)) F E).symm
      (prodHomeomorph K (Fin 0 → K) (Trivial B (Fin 0 → K)) F E p) = p :=
  (prodHomeomorph K (Fin 0 → K) (Trivial B (Fin 0 → K)) F E).symm_apply_apply p

-- Read the actual inverse formula on a decomposable tensor with a rank-zero left factor.
example (x : B) (b : DetBundle K F E x) :
    (prodHomeomorph K (Fin 0 → K) (Trivial B (Fin 0 → K)) F E).symm
      ⟨x, prodEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) F E x
        ((zeroEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) (by simp) x).symm 1 ⊗ₜ b)⟩ =
      ⟨x, (zeroEquiv K (Fin 0 → K) (Trivial B (Fin 0 → K)) (by simp) x).symm 1 ⊗ₜ b⟩ := by
  rw [prodHomeomorph_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

end EmptyFactor

section EmptyBase

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace K F₁] [FiniteDimensional K F₁]
  [NormedAddCommGroup F₂] [NormedSpace K F₂] [FiniteDimensional K F₂]

example : Nonempty
    (TotalSpace (ProjectiveTensor K K K)
      (fun x : Empty ↦ DetBundle K F₁ (Trivial Empty F₁) x ⊗[K]
        DetBundle K F₂ (Trivial Empty F₂) x) ≃ₜ
      TotalSpace K (DetBundle K (F₁ × F₂) ((Trivial Empty F₁) ×ᵇ (Trivial Empty F₂)))) :=
  ⟨prodHomeomorph K F₁ (Trivial Empty F₁) F₂ (Trivial Empty F₂)⟩

example : IsEmpty (TotalSpace K
    (DetBundle K (F₁ × F₂) ((Trivial Empty F₁) ×ᵇ (Trivial Empty F₂)))) :=
  ⟨fun p ↦ nomatch p.proj⟩

end EmptyBase

section RealLines

variable {B : Type*} [TopologicalSpace B]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace ℝ E₁)] [FiberBundle ℝ E₁] [VectorBundle ℝ ℝ E₁]
  [TopologicalSpace (TotalSpace ℝ E₂)] [FiberBundle ℝ E₂] [VectorBundle ℝ ℝ E₂]

-- The exchange of two real line factors is negative, for potentially nontrivial bundles.
example (x : B) (t : DetBundle ℝ ℝ E₁ x ⊗[ℝ] DetBundle ℝ ℝ E₂ x) :
    prodCommEquiv ℝ ℝ E₁ ℝ E₂ x (prodEquiv ℝ ℝ E₁ ℝ E₂ x t) =
      -(prodEquiv ℝ ℝ E₂ ℝ E₁ x (bundleTensorCommEquiv x t)) := by
  simpa only [Module.finrank_self, mul_one, pow_one, neg_one_smul] using
    prodCommEquiv_prodEquiv (K := ℝ) (F₁ := ℝ) (E₁ := E₁) (F₂ := ℝ) (E₂ := E₂) x t

end RealLines

section ComplexEvenRank

variable {B : Type*} [TopologicalSpace B]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace ℂ E₁)] [FiberBundle ℂ E₁] [VectorBundle ℂ ℂ E₁]
  [TopologicalSpace (TotalSpace (Fin 2 → ℂ) E₂)] [FiberBundle (Fin 2 → ℂ) E₂]
  [VectorBundle ℂ (Fin 2 → ℂ) E₂]

-- A complex line exchanged with a complex rank-two factor has positive sign.
example (x : B) (t : DetBundle ℂ ℂ E₁ x ⊗[ℂ] DetBundle ℂ (Fin 2 → ℂ) E₂ x) :
    prodCommEquiv ℂ ℂ E₁ (Fin 2 → ℂ) E₂ x (prodEquiv ℂ ℂ E₁ (Fin 2 → ℂ) E₂ x t) =
      prodEquiv ℂ (Fin 2 → ℂ) E₂ ℂ E₁ x (bundleTensorCommEquiv x t) := by
  have hdim : finrank ℂ (Fin 2 → ℂ) = 2 := by simp
  simpa only [Module.finrank_self, hdim, one_mul, neg_one_sq, one_smul] using
    prodCommEquiv_prodEquiv (K := ℂ) (F₁ := ℂ) (E₁ := E₁) (F₂ := Fin 2 → ℂ) (E₂ := E₂) x t

end ComplexEvenRank

section ConstantPullback

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  {B : Type*} [TopologicalSpace B]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace K F₁] [FiniteDimensional K F₁]
  [NormedAddCommGroup F₂] [NormedSpace K F₂] [FiniteDimensional K F₂]
  (E₁ E₂ : B → Type*)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]

-- Restriction to a single fibre uses native product-pullback and tensor-pullback carriers.
example (x : B) (t : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) :
    let f : C(Unit, B) := ContinuousMap.const Unit x
    prodPullbackEquiv K F₁ E₁ F₂ E₂ f () (prodEquiv K F₁ E₁ F₂ E₂ x t) =
      prodEquiv K F₁ ((f : Unit → B) *ᵖ E₁) F₂ ((f : Unit → B) *ᵖ E₂) ()
        (prodPullbackTensorEquiv K F₁ E₁ F₂ E₂ f () t) := by
  exact prodPullbackEquiv_prodEquiv (ContinuousMap.const Unit x) () t

end ConstantPullback

-- The model may change from a scalar line to a one-coordinate function space.
example {B : Type*} [TopologicalSpace B] (x : B)
    (t : DetBundle ℝ ℝ (Trivial B ℝ) x ⊗[ℝ] DetBundle ℝ ℝ (Trivial B ℝ) x) :
    let e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
    congrModelEquiv (F₁ := ℝ × ℝ) (F' := (Fin 1 → ℝ) × (Fin 1 → ℝ))
      (fun _ : B ↦ e.prodCongr e) x (prodEquiv ℝ ℝ (Trivial B ℝ) ℝ (Trivial B ℝ) x t) =
      prodEquiv ℝ (Fin 1 → ℝ) (Trivial B (Fin 1 → ℝ))
        (Fin 1 → ℝ) (Trivial B (Fin 1 → ℝ)) x
        (bundleTensorCongr
          (congrModelEquiv (F₁ := ℝ) (F' := Fin 1 → ℝ) (fun _ : B ↦ e))
          (congrModelEquiv (F₁ := ℝ) (F' := Fin 1 → ℝ) (fun _ : B ↦ e)) x t) := by
  exact congrModelEquiv_prodEquiv
    (F₁ := ℝ) (E₁ := Trivial B ℝ) (F₂ := ℝ) (E₂ := Trivial B ℝ)
    (F₁' := Fin 1 → ℝ) (E₁' := Trivial B (Fin 1 → ℝ))
    (F₂' := Fin 1 → ℝ) (E₂' := Trivial B (Fin 1 → ℝ))
    (fun _ ↦ (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm)
    (fun _ ↦ (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm) x t

section ThreeRealLines

variable {B : Type*} [TopologicalSpace B]

-- Three real line factors reassociate without a sign, on actual decomposable tensors.
example (x : B) (a b c : DetBundle ℝ ℝ (Trivial B ℝ) x) :
    prodAssocEquiv ℝ ℝ (Trivial B ℝ) ℝ (Trivial B ℝ) ℝ (Trivial B ℝ) x
      (prodEquiv ℝ (ℝ × ℝ) ((Trivial B ℝ) ×ᵇ (Trivial B ℝ)) ℝ (Trivial B ℝ) x
        (prodEquiv ℝ ℝ (Trivial B ℝ) ℝ (Trivial B ℝ) x (a ⊗ₜ b) ⊗ₜ c)) =
      prodEquiv ℝ ℝ (Trivial B ℝ) (ℝ × ℝ) ((Trivial B ℝ) ×ᵇ (Trivial B ℝ)) x
        (a ⊗ₜ prodEquiv ℝ ℝ (Trivial B ℝ) ℝ (Trivial B ℝ) x (b ⊗ₜ c)) := by
  simpa only [bundleTensorCongr_tmul, ContinuousLinearEquiv.refl_apply,
    bundleTensorAssocEquiv_tmul] using
    prodAssocEquiv_prodEquiv (K := ℝ) (F₁ := ℝ) (E₁ := Trivial B ℝ)
      (F₂ := ℝ) (E₂ := Trivial B ℝ) (F₃ := ℝ) (E₃ := Trivial B ℝ) x ((a ⊗ₜ b) ⊗ₜ c)

end ThreeRealLines

-- The model-degree-zero API is algebraic: these positive-dimensional fibres carry no
-- zero-model vector-bundle assumption. Replacing it by an intrinsic rank-zero map loses this case.
example (a : DetBundle ℂ (Fin 0 → ℂ) (fun _ : Unit ↦ Fin 2 → ℂ) ()) :
    (linearEquiv ℂ (Fin 0 → ℂ) (fun _ : Unit ↦ Fin 2 → ℂ) () a :
      ExteriorAlgebra ℂ (Fin 2 → ℂ)) =
      algebraMap ℂ (ExteriorAlgebra ℂ (Fin 2 → ℂ))
        (zeroEquiv ℂ (Fin 0 → ℂ) (fun _ : Unit ↦ Fin 2 → ℂ) (by simp) () a) := by
  exact coe_linearEquiv_zeroEquiv (by simp) () a

-- A nonlinear base map and arbitrary input charts do not force preferred-frame normalization.
example
    (e₁ : Trivialization ℂ (π ℂ (Trivial ℂ ℂ)))
    (e₂ : Trivialization (Fin 2 → ℂ) (π (Fin 2 → ℂ) (Trivial ℂ (Fin 2 → ℂ))))
    [e₁.IsLinear ℂ] [e₂.IsLinear ℂ] (z : ℂ)
    (hz₁ : z ^ 2 ∈ e₁.baseSet) (hz₂ : z ^ 2 ∈ e₂.baseSet)
    (v : DetBundle ℂ (ℂ × (Fin 2 → ℂ))
      ((Trivial ℂ ℂ) ×ᵇ (Trivial ℂ (Fin 2 → ℂ))) (z ^ 2)) :
    let f : C(ℂ, ℂ) := ⟨fun x ↦ x ^ 2, continuous_id.pow 2⟩
    chartCoord ((e₁.pullback f).prod (e₂.pullback f))
      (Trivialization.mem_prod_pullback_baseSet f hz₁ hz₂)
      (prodPullbackEquiv ℂ ℂ (Trivial ℂ ℂ) (Fin 2 → ℂ)
        (Trivial ℂ (Fin 2 → ℂ)) f z v) =
      chartCoord (e₁.prod e₂) (Trivialization.mem_prod_baseSet hz₁ hz₂) v := by
  exact chartCoord_prodPullbackEquiv
    (⟨fun x : ℂ ↦ x ^ 2, continuous_id.pow 2⟩ : C(ℂ, ℂ)) e₁ e₂ hz₁ hz₂ v

end TauCeti.DetBundle.WhitneyClients
