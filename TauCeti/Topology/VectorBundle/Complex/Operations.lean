/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.Clutching
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# Clutching numbers of direct sums and tensor products

Let `E₁` and `E₂` be complex vector bundles over a space `X`, with finite-dimensional model fibres
`F₁` and `F₂` of dimensions `n₁` and `n₂`, and let `p : Ω^ (Fin 2) X x` be a sphere. The clutching
number `c(E) = TauCeti.clutchingNumber F E p`, the first Chern number of `E` on `p`, satisfies the
laws of the first Chern class under the operations on bundles:

* **Whitney sum formula:** `c(E₁ ⊕ E₂) = c(E₁) + c(E₂)` (`TauCeti.clutchingNumber_prod`), for the
  direct sum `E₁ ×ᵇ E₂`;
* **tensor product formula:** `c(E₁ ⊗ E₂) = n₂ c(E₁) + n₁ c(E₂)`
  (`TauCeti.clutchingNumber_tensorProduct`), for the tensor product bundle `x ↦ E₁ x ⊗ E₂ x` of
  `TauCeti.Topology.VectorBundle.TensorProduct.Basic`. For line bundles this is
  `c(E₁ ⊗ E₂) = c(E₁) + c(E₂)` (`TauCeti.clutchingNumber_tensorProduct_of_finrank_eq_one`).

Both are proved by computing the clutching function, the normalized determinant of the transition
between a frame along `p` and a trivialization near `x`. Frames `φ₁` of `E₁` and `φ₂` of `E₂` along
`p` give the frames `φ₁ × φ₂` of `E₁ ⊕ E₂` (`TauCeti.prodFrame`) and `φ₁ ⊗ φ₂` of `E₁ ⊗ E₂`
(`TauCeti.tensorProductFrame`), continuous when `φ₁` and `φ₂` are
(`TauCeti.continuous_prodFrame`, `TauCeti.continuous_tensorProductFrame`). Read in the product
and tensor product trivializations, their transitions are `g₁ × g₂` and `g₁ ⊗ g₂`, where `g₁` and
`g₂` are the transitions of the factors. Since `det (g₁ × g₂) = det g₁ det g₂` and
`det (g₁ ⊗ g₂) = (det g₁) ^ n₂ (det g₂) ^ n₁` (`LinearMap.det_tensorProductMap`,
`ContinuousLinearEquiv.normalizedDet_eq_pow_mul_pow_of_apply_tmul`), the clutching functions are
`Γ₁ Γ₂` and `Γ₁ ^ n₂ Γ₂ ^ n₁` (`TauCeti.clutchingFunction_prodFrame`,
`TauCeti.clutchingFunction_tensorProductFrame`), whose degrees around the boundary of the square
are `deg Γ₁ + deg Γ₂` and `n₂ deg Γ₁ + n₁ deg Γ₂`.

These are the sphere forms of the identities `c₁(E₁ ⊕ E₂) = c₁(E₁) + c₁(E₂)` and
`c₁(L₁ ⊗ L₂) = c₁(L₁) + c₁(L₂)`, as used for instance for an embedded pseudoholomorphic sphere
`C` in an almost complex four-manifold `X`, where `TX|_C = TC ⊕ N_C` gives
`c₁(TX)[C] = c₁(TC)[C] + c₁(N_C)[C]`, and for the comparison of universal line bundles
`D ≃ E ⊗ U` in Taubes's correspondence between Seiberg–Witten solutions and pseudoholomorphic
curves.

## Main results

* `TauCeti.clutchingNumber_prod`, `TauCeti.clutchingNumberHom_prod`: the Whitney sum formula.
* `TauCeti.clutchingNumber_tensorProduct`, `TauCeti.clutchingNumberHom_tensorProduct`: the tensor
  product formula, and `TauCeti.clutchingNumber_tensorProduct_of_finrank_eq_one` for line bundles.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §14.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (clutching functions) and §3.1.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Bundle Module Set Topology
open scoped unitInterval Topology.Homotopy TensorProduct

namespace TauCeti

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  {E₁ : X → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  {E₂ : X → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂]

/-! ### Direct sums -/

section Prod

variable {f : B → X} {φ₁ : ∀ y, F₁ ≃L[ℂ] E₁ (f y)} {φ₂ : ∀ y, F₂ ≃L[ℂ] E₂ (f y)}

/-- The product frame of `E₁ ×ᵇ E₂` along `f`, made of two frames of `E₁` and `E₂`. -/
def prodFrame (φ₁ : ∀ y, F₁ ≃L[ℂ] E₁ (f y)) (φ₂ : ∀ y, F₂ ≃L[ℂ] E₂ (f y)) (y : B) :
    (F₁ × F₂) ≃L[ℂ] (E₁ ×ᵇ E₂) (f y) :=
  (φ₁ y).prodCongr (φ₂ y)

omit [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] in
@[simp]
theorem prodFrame_apply (y : B) (v : F₁ × F₂) :
    prodFrame φ₁ φ₂ y v = (φ₁ y v.1, φ₂ y v.2) :=
  (rfl)

omit [TopologicalSpace X] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] in
/-- The product of two continuous frames is a continuous frame of the direct sum. -/
theorem continuous_prodFrame
    (hφ₁ : Continuous fun q : B × F₁ ↦ TotalSpace.mk' F₁ (f q.1) (φ₁ q.1 q.2))
    (hφ₂ : Continuous fun q : B × F₂ ↦ TotalSpace.mk' F₂ (f q.1) (φ₂ q.1 q.2)) :
    Continuous fun q : B × (F₁ × F₂) ↦
      TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) (f q.1) (prodFrame φ₁ φ₂ q.1 q.2) :=
  (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous_iff.2 <|
    (hφ₁.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (hφ₂.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

variable [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  (e₁ : Trivialization F₁ (π F₁ E₁)) [e₁.IsLinear ℂ]
  (e₂ : Trivialization F₂ (π F₂ E₂)) [e₂.IsLinear ℂ]

omit [TopologicalSpace B] in
/-- The clutching function of a product frame in a product trivialization is the product of the
clutching functions, wherever both trivializations are defined. -/
theorem clutchingFunction_prodFrame {y : B} (hy₁ : f y ∈ e₁.baseSet) (hy₂ : f y ∈ e₂.baseSet) :
    clutchingFunction f (prodFrame φ₁ φ₂) (e₁.prod e₂) y =
      clutchingFunction f φ₁ e₁ y * clutchingFunction f φ₂ e₂ y := by
  have hy : f y ∈ (e₁.prod e₂).baseSet := ⟨hy₁, hy₂⟩
  have h : (prodFrame φ₁ φ₂ y).trans ((e₁.prod e₂).continuousLinearEquivAt ℂ (f y) hy) =
      ((φ₁ y).trans (e₁.continuousLinearEquivAt ℂ (f y) hy₁)).prodCongr
        ((φ₂ y).trans (e₂.continuousLinearEquivAt ℂ (f y) hy₂)) := by
    rw [Trivialization.continuousLinearEquivAt_prod]
    ext v <;> simp
  rw [clutchingFunction_of_mem hy, clutchingFunction_of_mem hy₁, clutchingFunction_of_mem hy₂, h,
    ContinuousLinearEquiv.normalizedDet_prodCongr, mul_inv]

end Prod

/-! ### Tensor products -/

section TensorProduct

variable [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]
  [∀ x, TopologicalSpace (E₁ x ⊗[ℂ] E₂ x)] [∀ x, IsModuleTopology ℂ (E₁ x ⊗[ℂ] E₂ x)]
  {f : B → X} {φ₁ : ∀ y, F₁ ≃L[ℂ] E₁ (f y)} {φ₂ : ∀ y, F₂ ≃L[ℂ] E₂ (f y)}

/-- The finite-dimensional model fibre `F₁ ⊗ F₂` carries the module topology, so that linear
equivalences out of it are continuous. -/
private local instance : IsModuleTopology ℂ (ProjectiveTensor ℂ F₁ F₂) :=
  isModuleTopologyOfFiniteDimensional

/-- The tensor product frame of `E₁ ⊗ E₂` along `f`, made of two frames of `E₁` and `E₂`: it sends
`v ⊗ w` to `φ₁ y v ⊗ φ₂ y w`. -/
noncomputable def tensorProductFrame (φ₁ : ∀ y, F₁ ≃L[ℂ] E₁ (f y)) (φ₂ : ∀ y, F₂ ≃L[ℂ] E₂ (f y))
    (y : B) :
    ProjectiveTensor ℂ F₁ F₂ ≃L[ℂ] E₁ (f y) ⊗[ℂ] E₂ (f y) :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology <|
    (ProjectiveTensor.linearEquiv ℂ F₁ F₂).trans
      (TensorProduct.congr (φ₁ y).toLinearEquiv (φ₂ y).toLinearEquiv)

omit [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] in
@[simp]
theorem tensorProductFrame_apply_tmul (y : B) (v : F₁) (w : F₂) :
    tensorProductFrame φ₁ φ₂ y ⟨v ⊗ₜ w⟩ = φ₁ y v ⊗ₜ φ₂ y w := by
  simp [tensorProductFrame]

variable [VectorBundle ℂ F₁ E₁] [VectorBundle ℂ F₂ E₂]

/-- The tensor product of two continuous frames is a continuous frame of `E₁ ⊗ E₂`. -/
theorem continuous_tensorProductFrame
    (hφ₁ : Continuous fun q : B × F₁ ↦ TotalSpace.mk' F₁ (f q.1) (φ₁ q.1 q.2))
    (hφ₂ : Continuous fun q : B × F₂ ↦ TotalSpace.mk' F₂ (f q.1) (φ₂ q.1 q.2)) :
    Continuous fun q : B × ProjectiveTensor ℂ F₁ F₂ ↦
      TotalSpace.mk' (ProjectiveTensor ℂ F₁ F₂) (E := fun x ↦ E₁ x ⊗[ℂ] E₂ x) (f q.1)
        (tensorProductFrame φ₁ φ₂ q.1 q.2) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  have hf : Continuous f := continuous_of_continuous_frame hφ₁
  -- Read both frames in the trivializations of `E₁` and `E₂` at `f q₀.1`.
  set e₁ := trivializationAt F₁ E₁ (f q₀.1)
  set e₂ := trivializationAt F₂ E₂ (f q₀.1)
  let A₁ : B → F₁ →L[ℂ] F₁ := fun y ↦ (e₁.continuousLinearMapAt ℂ (f y)).comp (φ₁ y : F₁ →L[ℂ] _)
  let A₂ : B → F₂ →L[ℂ] F₂ := fun y ↦ (e₂.continuousLinearMapAt ℂ (f y)).comp (φ₂ y : F₂ →L[ℂ] _)
  have hA₁ : ContinuousAt A₁ q₀.1 :=
    (continuousOn_continuousLinearMapAt_comp hφ₁ e₁).continuousAt <|
      hf.continuousAt.preimage_mem_nhds
      (e₁.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F₁ E₁ (f q₀.1)))
  have hA₂ : ContinuousAt A₂ q₀.1 :=
    (continuousOn_continuousLinearMapAt_comp hφ₂ e₂).continuousAt <|
      hf.continuousAt.preimage_mem_nhds
      (e₂.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F₂ E₂ (f q₀.1)))
  -- In these coordinates the tensor product frame is `A₁ ⊗ A₂`.
  have key (y : B) (u : ProjectiveTensor ℂ F₁ F₂) :
      TensorProduct.inCoordinates F₁ E₁ F₂ E₂ (f q₀.1) (f y) (f q₀.1) (f y)
        (tensorProductFrame φ₁ φ₂ y u) = ProjectiveTensor.mapL (A₁ y) (A₂ y) u := by
    obtain ⟨t⟩ := u
    induction t using TensorProduct.inductionOn with
    | tmul v w => simp [A₁, A₂, e₁, e₂]
    | add s t hs ht => rw [ProjectiveTensor.mk_add, map_add, map_add, map_add, hs, ht]
  rw [continuousAt_tensorProduct_bundle]
  refine ⟨(hf.comp continuous_fst).continuousAt, ?_⟩
  simp only [key]
  have hM : ContinuousAt (fun y ↦ ProjectiveTensor.mapL (A₁ y) (A₂ y)) q₀.1 := by
    simpa only [Function.comp_apply, ProjectiveTensor.mapLBilinear_apply] using
      ((ProjectiveTensor.mapLBilinear ℂ F₁ F₁ F₂ F₂).continuous.continuousAt.comp hA₁).clm_apply hA₂
  exact (hM.comp continuousAt_fst).clm_apply continuousAt_snd

variable (e₁ : Trivialization F₁ (π F₁ E₁)) [MemTrivializationAtlas e₁]
  (e₂ : Trivialization F₂ (π F₂ E₂)) [MemTrivializationAtlas e₂]

omit [TopologicalSpace B] in
/-- The clutching function of a tensor product frame in a tensor product trivialization is
`Γ₁ ^ dim F₂ * Γ₂ ^ dim F₁`, where `Γ₁` and `Γ₂` are the clutching functions of the factors,
wherever both trivializations are defined. -/
theorem clutchingFunction_tensorProductFrame {y : B} (hy₁ : f y ∈ e₁.baseSet)
    (hy₂ : f y ∈ e₂.baseSet) :
    clutchingFunction f (tensorProductFrame φ₁ φ₂) (e₁.tensorProduct ℂ e₂) y =
      clutchingFunction f φ₁ e₁ y ^ finrank ℂ F₂ * clutchingFunction f φ₂ e₂ y ^ finrank ℂ F₁ := by
  have hy : f y ∈ (e₁.tensorProduct ℂ e₂).baseSet := by
    rw [Trivialization.baseSet_tensorProduct]
    exact ⟨hy₁, hy₂⟩
  rw [clutchingFunction_of_mem hy, clutchingFunction_of_mem hy₁, clutchingFunction_of_mem hy₂,
    ContinuousLinearEquiv.normalizedDet_eq_pow_mul_pow_of_apply_tmul fun v w ↦ ?_, mul_inv,
    inv_pow, inv_pow]
  simp [hy₁, hy₂]

end TensorProduct

section ClutchingNumber

variable [VectorBundle ℂ F₁ E₁] [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul ℂ (E₁ x)]
  [FiniteDimensional ℂ F₁] [VectorBundle ℂ F₂ E₂] [∀ x, IsTopologicalAddGroup (E₂ x)]
  [∀ x, ContinuousSMul ℂ (E₂ x)] [FiniteDimensional ℂ F₂] {x : X}

/-- **Whitney sum formula.** The clutching number of a direct sum of complex vector bundles on a
sphere is the sum of their clutching numbers. -/
theorem clutchingNumber_prod (p : Ω^ (Fin 2) X x) :
    clutchingNumber (F₁ × F₂) (E₁ ×ᵇ E₂) p = clutchingNumber F₁ E₁ p + clutchingNumber F₂ E₂ p := by
  have : CompleteSpace F₁ := FiniteDimensional.completeSpace ℂ F₁
  have : CompleteSpace F₂ := FiniteDimensional.completeSpace ℂ F₂
  obtain ⟨φ₁, hφ₁⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F₁) (E := E₁) (map_continuous p)
  obtain ⟨φ₂, hφ₂⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F₂) (E := E₂) (map_continuous p)
  set e₁ := trivializationAt F₁ E₁ x
  set e₂ := trivializationAt F₂ E₂ x
  have hx₁ : x ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  have hx₂ : x ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ x
  have hc₁ := continuousOn_clutchingFunction_boundary p hφ₁ e₁ hx₁
  have hc₂ := continuousOn_clutchingFunction_boundary p hφ₂ e₂ hx₂
  rw [clutchingNumber_eq_squareBoundaryDegree p (e₁.prod e₂) ⟨hx₁, hx₂⟩
      (continuous_prodFrame hφ₁ hφ₂),
    clutchingNumber_eq_squareBoundaryDegree p e₁ hx₁ hφ₁,
    clutchingNumber_eq_squareBoundaryDegree p e₂ hx₂ hφ₂, ← squareBoundaryDegree_mul hc₁ hc₂]
  refine squareBoundaryDegree_congr fun y hy ↦ ?_
  have hpy : p y = x := GenLoop.boundary p y hy
  exact clutchingFunction_prodFrame e₁ e₂ (mem_of_eq_of_mem hpy hx₁) (mem_of_eq_of_mem hpy hx₂)

variable (F₁ E₁ F₂ E₂ x) in
/-- **Whitney sum formula** for the clutching number homomorphisms `π₂(X, x) → ℤ`. -/
theorem clutchingNumberHom_prod :
    clutchingNumberHom (F₁ × F₂) (E₁ ×ᵇ E₂) x =
      clutchingNumberHom F₁ E₁ x + clutchingNumberHom F₂ E₂ x := by
  refine AddMonoidHom.ext fun a ↦ ?_
  obtain ⟨p, hp⟩ := Quotient.exists_rep a.toMul
  rw [← ofMul_toMul a, ← hp]
  rw [AddMonoidHom.add_apply, clutchingNumberHom_apply_mk, clutchingNumberHom_apply_mk,
    clutchingNumberHom_apply_mk, clutchingNumber_prod]

section TensorProduct

variable [∀ x, TopologicalSpace (E₁ x ⊗[ℂ] E₂ x)] [∀ x, IsModuleTopology ℂ (E₁ x ⊗[ℂ] E₂ x)]

/-- **Tensor product formula.** The clutching number of a tensor product `E₁ ⊗ E₂` of complex
vector bundles of ranks `n₁` and `n₂` on a sphere is `n₂ c(E₁) + n₁ c(E₂)`, where `c(E₁)` and
`c(E₂)` are the clutching numbers of the factors. -/
theorem clutchingNumber_tensorProduct (p : Ω^ (Fin 2) X x) :
    clutchingNumber (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x) p =
      finrank ℂ F₂ * clutchingNumber F₁ E₁ p + finrank ℂ F₁ * clutchingNumber F₂ E₂ p := by
  have : CompleteSpace F₁ := FiniteDimensional.completeSpace ℂ F₁
  have : CompleteSpace F₂ := FiniteDimensional.completeSpace ℂ F₂
  obtain ⟨φ₁, hφ₁⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F₁) (E := E₁) (map_continuous p)
  obtain ⟨φ₂, hφ₂⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F₂) (E := E₂) (map_continuous p)
  set e₁ := trivializationAt F₁ E₁ x
  set e₂ := trivializationAt F₂ E₂ x
  have hx₁ : x ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  have hx₂ : x ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ x
  have hx : x ∈ (e₁.tensorProduct ℂ e₂).baseSet := by
    rw [Trivialization.baseSet_tensorProduct]
    exact ⟨hx₁, hx₂⟩
  have hc₁ := continuousOn_clutchingFunction_boundary p hφ₁ e₁ hx₁
  have hc₂ := continuousOn_clutchingFunction_boundary p hφ₂ e₂ hx₂
  rw [clutchingNumber_eq_squareBoundaryDegree p (e₁.tensorProduct ℂ e₂) hx
      (continuous_tensorProductFrame hφ₁ hφ₂),
    clutchingNumber_eq_squareBoundaryDegree p e₁ hx₁ hφ₁,
    clutchingNumber_eq_squareBoundaryDegree p e₂ hx₂ hφ₂, ← squareBoundaryDegree_pow hc₁,
    ← squareBoundaryDegree_pow hc₂, ← squareBoundaryDegree_mul (hc₁.pow _) (hc₂.pow _)]
  refine squareBoundaryDegree_congr fun y hy ↦ ?_
  have hpy : p y = x := GenLoop.boundary p y hy
  exact clutchingFunction_tensorProductFrame e₁ e₂ (mem_of_eq_of_mem hpy hx₁)
    (mem_of_eq_of_mem hpy hx₂)

/-- **Tensor product formula for line bundles.** The clutching number of a tensor product of
complex line bundles on a sphere is the sum of their clutching numbers. -/
theorem clutchingNumber_tensorProduct_of_finrank_eq_one (h₁ : finrank ℂ F₁ = 1)
    (h₂ : finrank ℂ F₂ = 1) (p : Ω^ (Fin 2) X x) :
    clutchingNumber (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x) p =
      clutchingNumber F₁ E₁ p + clutchingNumber F₂ E₂ p := by
  rw [clutchingNumber_tensorProduct, h₁, h₂, Nat.cast_one, one_mul, one_mul]

variable (F₁ E₁ F₂ E₂ x) in
/-- **Tensor product formula** for the clutching number homomorphisms `π₂(X, x) → ℤ`. -/
theorem clutchingNumberHom_tensorProduct :
    clutchingNumberHom (ProjectiveTensor ℂ F₁ F₂) (fun x ↦ E₁ x ⊗[ℂ] E₂ x) x =
      finrank ℂ F₂ • clutchingNumberHom F₁ E₁ x + finrank ℂ F₁ • clutchingNumberHom F₂ E₂ x := by
  refine AddMonoidHom.ext fun a ↦ ?_
  obtain ⟨p, hp⟩ := Quotient.exists_rep a.toMul
  rw [← ofMul_toMul a, ← hp]
  rw [AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, AddMonoidHom.nsmul_apply,
    clutchingNumberHom_apply_mk, clutchingNumberHom_apply_mk, clutchingNumberHom_apply_mk,
    clutchingNumber_tensorProduct, nsmul_eq_mul, nsmul_eq_mul]

end TensorProduct

end ClutchingNumber

end TauCeti
