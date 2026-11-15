/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.UCB.CompRight

/-!
# Bounded functions uniformly continuous under small left addition

For a topological additive group `A`, `TauCeti.addUcb A` is the subalgebra of real bounded
continuous functions `f` such that `f (u + x)` is uniformly close to `f x` for all `u` near `0`:

```text
∀ ε > 0,  ∀ᶠ u in 𝓝 0,  ∀ x,  |f (u + x) - f x| < ε.
```

`TauCeti.AddUCB A` is the corresponding type. It inherits the supremum norm, the unital algebra
structure and the pointwise order of `A →ᵇ ℝ`, and it is a lattice for the pointwise maximum and
minimum. Left translation `(L_a f)(x) = f (-a + x)` acts on `AddUCB A` by linear isometries, and
pullback along a continuous additive homomorphism `φ : A →ₜ+ B` maps `AddUCB B` to `AddUCB A`.

Precomposition with `Multiplicative.toAdd` identifies `AddUCB A` with
`TauCeti.UCB (Multiplicative A)` as an ordered normed unital ℝ-algebra, intertwining additive left
translation by `a` with multiplicative left translation by `Multiplicative.ofAdd a`.

## Main definitions

* `TauCeti.addUcb A`: the subalgebra of `A →ᵇ ℝ` of bounded functions uniformly continuous under
  small left addition.
* `TauCeti.AddUCB A`: its carrier type, a real Banach algebra and lattice.
* `TauCeti.AddUCB.equivMultiplicative`: the unital algebra isomorphism
  `AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A)`.
* `TauCeti.AddUCB.linearIsometryEquivMultiplicative`: the linear isometry equivalence
  `AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A)`.
* `TauCeti.UCB.equivAdditive`: the unital algebra isomorphism `UCB G ≃ₐ[ℝ] AddUCB (Additive G)`.
* `TauCeti.AddUCB.leftTranslation a`: left translation `f ↦ (x ↦ f (-a + x))` on `AddUCB A`.
* `TauCeti.AddUCB.compRightAlgHom φ`: pullback `f ↦ f ∘ φ` along `φ : A →ₜ+ B`.

## Main results

* `TauCeti.mem_addUcb_iff_tendsto`: membership in `addUcb A` means `u ↦ f (u + ·)` tends to `f` in
  supremum norm as `u → 0`.
* `TauCeti.mem_addUcb_iff_uniformContinuous`: membership in `addUcb A` is uniform continuity for
  `IsTopologicalAddGroup.rightUniformSpace A`.
* `TauCeti.isClosed_addUcb`: `addUcb A` is closed in `A →ᵇ ℝ`, so `AddUCB A` is complete.
* `TauCeti.AddUCB.equivMultiplicative_leftTranslation`: `equivMultiplicative` intertwines additive
  and multiplicative left translations.
* `TauCeti.AddUCB.continuous_leftTranslation_apply`: the orbit map `a ↦ L_a f` is continuous in
  supremum norm.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and
  Definition G.1.4.
-/

public section

noncomputable section

open Filter Topology Multiplicative Additive
open scoped BoundedContinuousFunction

namespace TauCeti

variable {A B C : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]

section UniformContinuous

variable {β : Type*} [PseudoMetricSpace β]

/-- A function on a topological additive group is uniformly continuous for the right uniformity
exactly when `f (u + x)` is uniformly close to `f x` for all `u` near `0`. -/
theorem uniformContinuous_rightUniformSpace_add_iff (f : A → β) :
    (letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
     UniformContinuous f) ↔
      ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, dist (f (u + x)) (f x) < ε := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero',
    ((𝓝 (0 : A)).basis_sets.comap _).tendsto_iff Metric.uniformity_basis_dist]
  refine forall₂_congr fun ε _ => ⟨fun ⟨U, hU, h⟩ => ?_, fun h => ?_⟩
  · filter_upwards [hU] with u hu x
    rw [dist_comm]
    exact h (x, u + x) (by simpa using hu)
  · refine ⟨_, h, fun p hp => ?_⟩
    simpa [dist_comm] using hp p.1

end UniformContinuous

variable (A) in
/-- The real bounded continuous functions `f` on `A` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ ℝ`. -/
def addUcb : Subalgebra ℝ (A →ᵇ ℝ) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, |f (u + x) - f x| < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← Real.dist_eq,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← Real.dist_eq,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' _ := by
    simp only [Set.mem_ofPred_eq, ← Real.dist_eq,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]
    exact tendsto_const_nhds

variable (A) in
/-- The real Banach algebra of bounded functions on `A` that are uniformly continuous under small
left addition, with the supremum norm, algebra operations and order of `A →ᵇ ℝ`. -/
abbrev AddUCB : Type _ := addUcb A

/-- The defining condition of `addUcb A`. -/
theorem mem_addUcb_iff {f : A →ᵇ ℝ} :
    f ∈ addUcb A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, |f (u + x) - f x| < ε :=
  Iff.rfl

/-- Membership in `addUcb A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as `u → 0`. -/
theorem mem_addUcb_iff_tendsto {f : A →ᵇ ℝ} :
    f ∈ addUcb A ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  simp only [mem_addUcb_iff, ← Real.dist_eq,
    BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]

/-- Membership in `addUcb A` is uniform continuity for the right uniformity of `A`. -/
theorem mem_addUcb_iff_uniformContinuous {f : A →ᵇ ℝ} :
    f ∈ addUcb A ↔
      (letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
       UniformContinuous f) := by
  simp only [mem_addUcb_iff, ← Real.dist_eq, uniformContinuous_rightUniformSpace_add_iff]

/-- A bounded continuous function with compact support belongs to `addUcb A`. -/
theorem mem_addUcb_of_hasCompactSupport {f : A →ᵇ ℝ} (hf : HasCompactSupport f) :
    f ∈ addUcb A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  simpa only [mem_addUcb_iff, ← Real.dist_eq] using
    (uniformContinuous_rightUniformSpace_add_iff f).1
      (hf.uniformContinuous_of_continuous f.continuous)

/-- `f ∈ addUcb A` if and only if its transport to `Multiplicative A` lies in
`ucb (Multiplicative A)`. -/
theorem mem_addUcb_iff_compContinuous_mem_ucb {f : A →ᵇ ℝ} :
    f ∈ addUcb A ↔
      f.compContinuous ⟨toAdd, continuous_toAdd⟩ ∈ ucb (Multiplicative A) := by
  simp only [mem_addUcb_iff, mem_ucb_iff]
  refine forall₂_congr fun ε _ => ?_
  rw [← ofAdd_zero, nhds_ofAdd, eventually_map]
  exact Filter.eventually_congr (Eventually.of_forall fun u =>
    ⟨fun h x => by simpa using h x.toAdd, fun h x => by simpa using h (ofAdd x)⟩)

/-- `f ∈ ucb (Multiplicative A)` if and only if its transport to `A` lies in `addUcb A`. -/
theorem mem_ucb_multiplicative_iff_compContinuous_mem_addUcb {f : Multiplicative A →ᵇ ℝ} :
    f ∈ ucb (Multiplicative A) ↔
      f.compContinuous ⟨ofAdd, continuous_ofAdd⟩ ∈ addUcb A := by
  rw [mem_addUcb_iff_compContinuous_mem_ucb]
  have hf : (f.compContinuous ⟨ofAdd, continuous_ofAdd⟩).compContinuous ⟨toAdd, continuous_toAdd⟩ =
      f := by ext x; simp
  rw [hf]

/-- `f ∈ ucb G` if and only if its transport to `Additive G` lies in `addUcb (Additive G)`. -/
theorem mem_ucb_iff_compContinuous_mem_addUcb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : G →ᵇ ℝ} :
    f ∈ ucb G ↔ f.compContinuous ⟨toMul, continuous_toMul⟩ ∈ addUcb (Additive G) := by
  simp only [mem_ucb_iff, mem_addUcb_iff]
  refine forall₂_congr fun ε _ => ?_
  rw [← ofMul_one, nhds_ofMul, eventually_map]
  exact Filter.eventually_congr (Eventually.of_forall fun u =>
    ⟨fun h x => by simpa using h x.toMul, fun h x => by simpa using h (ofMul x)⟩)

/-- `f ∈ addUcb (Additive G)` if and only if its transport to `G` lies in `ucb G`. -/
theorem mem_addUcb_additive_iff_compContinuous_mem_ucb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : Additive G →ᵇ ℝ} :
    f ∈ addUcb (Additive G) ↔ f.compContinuous ⟨ofMul, continuous_ofMul⟩ ∈ ucb G := by
  rw [mem_ucb_iff_compContinuous_mem_addUcb]
  have hf : (f.compContinuous ⟨ofMul, continuous_ofMul⟩).compContinuous ⟨toMul, continuous_toMul⟩ =
      f := by ext x; simp
  rw [hf]

/-- `addUcb A` is closed in `A →ᵇ ℝ`: a uniform limit of functions in `addUcb A` lies in
`addUcb A`. -/
theorem isClosed_addUcb : IsClosed (addUcb A : Set (A →ᵇ ℝ)) := by
  have hpre : (addUcb A : Set (A →ᵇ ℝ)) =
      (fun f : A →ᵇ ℝ => f.compContinuous ⟨toAdd, continuous_toAdd⟩) ⁻¹'
        (ucb (Multiplicative A) : Set (Multiplicative A →ᵇ ℝ)) :=
    Set.ext fun _ => mem_addUcb_iff_compContinuous_mem_ucb
  rw [hpre]
  exact isClosed_ucb.preimage
    (LipschitzWith.mk_one fun f g =>
      (BoundedContinuousFunction.dist_le dist_nonneg).2 fun x =>
        BoundedContinuousFunction.dist_coe_le_dist x.toAdd).continuous

/-- `AddUCB A` is a real normed group for the supremum norm of `A →ᵇ ℝ`. -/
instance : NormedAddCommGroup (AddUCB A) :=
  inferInstance

/-- `AddUCB A` is a real Banach space. -/
instance : CompleteSpace (AddUCB A) :=
  isClosed_addUcb.completeSpace_coe

/-- Scalar multiplication on `AddUCB A` scales the supremum norm. -/
instance : NormSMulClass ℝ (AddUCB A) :=
  ⟨fun c f => norm_smul c (f : A →ᵇ ℝ)⟩

/-- Constant functions belong to `addUcb A`. -/
@[simp]
theorem const_mem_addUcb (c : ℝ) : BoundedContinuousFunction.const A c ∈ addUcb A :=
  fun _ hε => .of_forall fun _ _ => by simpa using hε

/-- `addUcb A` is closed under the pointwise maximum. -/
theorem sup_mem_addUcb {f g : A →ᵇ ℝ} (hf : f ∈ addUcb A) (hg : g ∈ addUcb A) :
    f ⊔ g ∈ addUcb A := by
  rw [mem_addUcb_iff_tendsto] at hf hg ⊢
  exact hf.sup_nhds hg

/-- `addUcb A` is closed under the pointwise minimum. -/
theorem inf_mem_addUcb {f g : A →ᵇ ℝ} (hf : f ∈ addUcb A) (hg : g ∈ addUcb A) :
    f ⊓ g ∈ addUcb A := by
  rw [mem_addUcb_iff_tendsto] at hf hg ⊢
  exact hf.inf_nhds hg

/-- `addUcb A` is closed under the pointwise absolute value. -/
theorem abs_mem_addUcb {f : A →ᵇ ℝ} (hf : f ∈ addUcb A) : |f| ∈ addUcb A :=
  sup_mem_addUcb hf (neg_mem hf)

/-- `AddUCB A` is a lattice for the pointwise maximum and minimum. -/
instance : Lattice (AddUCB A) :=
  Subtype.lattice (fun _ _ => sup_mem_addUcb) (fun _ _ => inf_mem_addUcb)

/-- The supremum norm of `AddUCB A` is solid for its pointwise order. -/
instance : HasSolidNorm (AddUCB A) where
  solid _ _ h := HasSolidNorm.solid (α := A →ᵇ ℝ) h

/-- A left translate `x ↦ f (a + x)` of a function in `addUcb A` lies in `addUcb A`. -/
theorem compContinuous_addLeft_mem_addUcb {f : A →ᵇ ℝ} (hf : f ∈ addUcb A) (a : A) :
    f.compContinuous (ContinuousMap.addLeft a) ∈ addUcb A := by
  rw [mem_addUcb_iff_compContinuous_mem_ucb] at hf ⊢
  have h : (f.compContinuous (ContinuousMap.addLeft a)).compContinuous ⟨toAdd, continuous_toAdd⟩ =
      (f.compContinuous ⟨toAdd, continuous_toAdd⟩).compContinuous
        (ContinuousMap.mulLeft (ofAdd a)) := by ext x; simp
  rw [h]
  exact compContinuous_mulLeft_mem_ucb hf (ofAdd a)

/-- The pullback `x ↦ f (φ x)` of a function in `addUcb B` along a continuous additive homomorphism
`φ : A →ₜ+ B` lies in `addUcb A`. -/
theorem compContinuous_mem_addUcb {f : B →ᵇ ℝ} (hf : f ∈ addUcb B) (φ : A →ₜ+ B) :
    f.compContinuous (φ : C(A, B)) ∈ addUcb A := by
  have hφ : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa using φ.continuous.tendsto (0 : A)
  rw [mem_addUcb_iff] at hf ⊢
  intro ε hε
  filter_upwards [hφ.eventually (hf ε hε)] with u hu x
  simpa using hu (φ x)

namespace AddUCB

@[simp, norm_cast]
theorem coe_sup (f g : AddUCB A) : ((f ⊔ g : AddUCB A) : A →ᵇ ℝ) = (f : A →ᵇ ℝ) ⊔ (g : A →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_inf (f g : AddUCB A) : ((f ⊓ g : AddUCB A) : A →ᵇ ℝ) = (f : A →ᵇ ℝ) ⊓ (g : A →ᵇ ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_abs (f : AddUCB A) : ((|f| : AddUCB A) : A →ᵇ ℝ) = |(f : A →ᵇ ℝ)| :=
  rfl

/-- Two elements of `AddUCB A` are equal when they agree at every point. -/
@[ext]
theorem ext {f g : AddUCB A} (h : ∀ x, (f : A →ᵇ ℝ) x = (g : A →ᵇ ℝ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- The order on `AddUCB A` is the pointwise order. -/
theorem le_def {f g : AddUCB A} : f ≤ g ↔ ∀ x, (f : A →ᵇ ℝ) x ≤ (g : A →ᵇ ℝ) x :=
  Iff.rfl

/-- Each value of an element of `AddUCB A` is bounded by its supremum norm. -/
theorem abs_apply_le_norm (f : AddUCB A) (x : A) : |(f : A →ᵇ ℝ) x| ≤ ‖f‖ :=
  (f : A →ᵇ ℝ).norm_coe_le_norm x

/-- Every element of `AddUCB A` lies below the constant function with value its supremum norm. -/
theorem le_norm_smul_one (f : AddUCB A) : f ≤ ‖f‖ • 1 :=
  le_def.2 fun x => by simpa using (f : A →ᵇ ℝ).apply_le_norm x

/-- Precomposition with `Multiplicative.toAdd` identifies `AddUCB A` with `UCB (Multiplicative A)`
as a unital ℝ-algebra. -/
def equivMultiplicative : AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A) where
  toFun f := ⟨(f : A →ᵇ ℝ).compContinuous ⟨toAdd, continuous_toAdd⟩,
    mem_addUcb_iff_compContinuous_mem_ucb.1 f.2⟩
  invFun f := ⟨(f : Multiplicative A →ᵇ ℝ).compContinuous ⟨ofAdd, continuous_ofAdd⟩,
    mem_ucb_multiplicative_iff_compContinuous_mem_addUcb.1 f.2⟩
  left_inv _ := ext fun _ => by simp
  right_inv _ := UCB.ext fun _ => by simp
  map_mul' _ _ := UCB.ext fun _ => rfl
  map_add' _ _ := UCB.ext fun _ => rfl
  commutes' _ := UCB.ext fun _ => rfl

@[simp]
theorem equivMultiplicative_apply (f : AddUCB A) (x : Multiplicative A) :
    (equivMultiplicative f : Multiplicative A →ᵇ ℝ) x = (f : A →ᵇ ℝ) x.toAdd :=
  (rfl)

@[simp]
theorem equivMultiplicative_symm_apply (f : UCB (Multiplicative A)) (x : A) :
    (equivMultiplicative.symm f : A →ᵇ ℝ) x = (f : Multiplicative A →ᵇ ℝ) (ofAdd x) :=
  (rfl)

/-- `equivMultiplicative` preserves and reflects the pointwise order. -/
@[simp]
theorem equivMultiplicative_le_equivMultiplicative_iff {f g : AddUCB A} :
    equivMultiplicative f ≤ equivMultiplicative g ↔ f ≤ g := by
  simp only [UCB.le_def, equivMultiplicative_apply, le_def]
  exact ⟨fun h x => h (ofAdd x), fun h x => h x.toAdd⟩

/-- `equivMultiplicative.symm` preserves and reflects the pointwise order. -/
@[simp]
theorem equivMultiplicative_symm_le_equivMultiplicative_symm_iff
    {f g : UCB (Multiplicative A)} :
    equivMultiplicative.symm f ≤ equivMultiplicative.symm g ↔ f ≤ g := by
  simp only [le_def, equivMultiplicative_symm_apply, UCB.le_def]
  exact ⟨fun h x => h x.toAdd, fun h x => h (ofAdd x)⟩

/-- `equivMultiplicative` preserves the supremum norm. -/
@[simp]
theorem norm_equivMultiplicative (f : AddUCB A) :
    ‖(equivMultiplicative f : Multiplicative A →ᵇ ℝ)‖ = ‖(f : A →ᵇ ℝ)‖ := by
  refine le_antisymm ((f : A →ᵇ ℝ).norm_compContinuous_le ⟨toAdd, continuous_toAdd⟩) ?_
  exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
    (equivMultiplicative f : Multiplicative A →ᵇ ℝ).norm_coe_le_norm (ofAdd x)

/-- `equivMultiplicative.symm` preserves the supremum norm. -/
@[simp]
theorem norm_equivMultiplicative_symm (f : UCB (Multiplicative A)) :
    ‖(equivMultiplicative.symm f : A →ᵇ ℝ)‖ = ‖(f : Multiplicative A →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_equivMultiplicative (equivMultiplicative.symm f)).symm

variable (A) in
/-- Precomposition with `Multiplicative.toAdd` as a real linear isometry equivalence between
`AddUCB A` and `UCB (Multiplicative A)`. -/
def linearIsometryEquivMultiplicative : AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A) :=
  { equivMultiplicative.toLinearEquiv with norm_map' := norm_equivMultiplicative }

@[simp]
theorem linearIsometryEquivMultiplicative_apply (f : AddUCB A) :
    linearIsometryEquivMultiplicative A f = equivMultiplicative f :=
  (rfl)

@[simp]
theorem linearIsometryEquivMultiplicative_symm_apply (f : UCB (Multiplicative A)) :
    (linearIsometryEquivMultiplicative A).symm f = equivMultiplicative.symm f :=
  (rfl)

/-- Left translation `L_a`, where `(L_a f)(x) = f (-a + x)`, as a linear isometry equivalence of
`AddUCB A`. -/
def leftTranslation (a : A) : AddUCB A ≃ₗᵢ[ℝ] AddUCB A :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUcb A)
    (ContinuousMap.addLeft (-a)) (ContinuousMap.addLeft a) (by simp) (by simp)
    (fun _ hf => compContinuous_addLeft_mem_addUcb hf _)
    (fun _ hf => compContinuous_addLeft_mem_addUcb hf _)

/-- The left translate `L_a f` is the precomposition of `f` with `x ↦ -a + x`. -/
theorem coe_leftTranslation (a : A) (f : AddUCB A) :
    (leftTranslation a f : A →ᵇ ℝ) =
      (f : A →ᵇ ℝ).compContinuous (ContinuousMap.addLeft (-a)) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp]
theorem leftTranslation_apply (a : A) (f : AddUCB A) (x : A) :
    (leftTranslation a f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (-a + x) :=
  DFunLike.congr_fun (coe_leftTranslation a f) x

/-- The inverse of `L_a` is precomposition with `x ↦ a + x`. -/
theorem coe_leftTranslation_symm (a : A) (f : AddUCB A) :
    ((leftTranslation a).symm f : A →ᵇ ℝ) =
      (f : A →ᵇ ℝ).compContinuous (ContinuousMap.addLeft a) :=
  BoundedContinuousFunction.compContinuousₗᵢ_symm_apply ..

@[simp]
theorem leftTranslation_symm_apply (a : A) (f : AddUCB A) (x : A) :
    ((leftTranslation a).symm f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (a + x) :=
  DFunLike.congr_fun (coe_leftTranslation_symm a f) x

@[simp]
theorem leftTranslation_zero : leftTranslation (0 : A) = LinearIsometryEquiv.refl ℝ (AddUCB A) := by
  ext
  simp

theorem leftTranslation_add (a b : A) :
    leftTranslation (a + b) = leftTranslation a * leftTranslation b := by
  ext
  simp [add_assoc]

@[simp]
theorem leftTranslation_neg (a : A) : leftTranslation (-a) = (leftTranslation a).symm := by
  ext
  simp

/-- `equivMultiplicative` intertwines additive left translation by `a` with multiplicative left
translation by `Multiplicative.ofAdd a`. -/
@[simp]
theorem equivMultiplicative_leftTranslation (a : A) (f : AddUCB A) :
    equivMultiplicative (leftTranslation a f) =
      UCB.leftTranslation (ofAdd a) (equivMultiplicative f) := by
  ext x
  simp

/-- `equivMultiplicative.symm` intertwines multiplicative left translation by `g` with additive left
translation by `g.toAdd`. -/
@[simp]
theorem equivMultiplicative_symm_leftTranslation (g : Multiplicative A)
    (f : UCB (Multiplicative A)) :
    equivMultiplicative.symm (UCB.leftTranslation g f) =
      leftTranslation g.toAdd (equivMultiplicative.symm f) := by
  ext x
  simp

/-- The orbit map `a ↦ L_a f` of `f : AddUCB A` is continuous for the supremum norm. -/
theorem continuous_leftTranslation_apply (f : AddUCB A) :
    Continuous fun a : A => leftTranslation a f := by
  have h : (fun a : A => leftTranslation a f) =
      fun a => (linearIsometryEquivMultiplicative A).symm
        (UCB.leftTranslation (ofAdd a) (equivMultiplicative f)) := by
    ext a x
    simp
  rw [h]
  exact (linearIsometryEquivMultiplicative A).symm.continuous.comp
    ((UCB.continuous_leftTranslation_apply (equivMultiplicative f)).comp continuous_ofAdd)

/-- The pullback `f ↦ f ∘ φ` along a continuous additive homomorphism `φ : A →ₜ+ B`, as a unital
algebra homomorphism from `AddUCB B` to `AddUCB A`. -/
def compRightAlgHom (φ : A →ₜ+ B) : AddUCB B →ₐ[ℝ] AddUCB A where
  toFun f := ⟨(f : B →ᵇ ℝ).compContinuous (φ : C(A, B)), compContinuous_mem_addUcb f.2 φ⟩
  map_one' := ext fun _ => rfl
  map_mul' _ _ := ext fun _ => rfl
  map_zero' := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl
  commutes' _ := ext fun _ => rfl

@[simp]
theorem compRightAlgHom_apply (φ : A →ₜ+ B) (f : AddUCB B) (x : A) :
    (compRightAlgHom φ f : A →ᵇ ℝ) x = (f : B →ᵇ ℝ) (φ x) :=
  (rfl)

@[simp]
theorem compRightAlgHom_id :
    compRightAlgHom (ContinuousAddMonoidHom.id A) = AlgHom.id ℝ (AddUCB A) :=
  AlgHom.ext fun _ => ext fun _ => rfl

theorem compRightAlgHom_comp (ψ : B →ₜ+ C) (φ : A →ₜ+ B) :
    compRightAlgHom (ψ.comp φ) = (compRightAlgHom φ).comp (compRightAlgHom ψ) :=
  AlgHom.ext fun _ => ext fun _ => rfl

/-- The pullback preserves the pointwise order. -/
theorem monotone_compRightAlgHom (φ : A →ₜ+ B) : Monotone (compRightAlgHom φ) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (φ x)

/-- The pullback intertwines left translation by `φ a` with left translation by `a`. -/
theorem compRightAlgHom_leftTranslation (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    compRightAlgHom φ (leftTranslation (φ a) f) = leftTranslation a (compRightAlgHom φ f) := by
  ext
  simp

end AddUCB

namespace UCB

section Additive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Precomposition with `Additive.toMul` identifies `UCB G` with `AddUCB (Additive G)` as a unital
ℝ-algebra. -/
def equivAdditive : UCB G ≃ₐ[ℝ] AddUCB (Additive G) where
  toFun f := ⟨(f : G →ᵇ ℝ).compContinuous ⟨toMul, continuous_toMul⟩,
    mem_ucb_iff_compContinuous_mem_addUcb.1 f.2⟩
  invFun f := ⟨(f : Additive G →ᵇ ℝ).compContinuous ⟨ofMul, continuous_ofMul⟩,
    mem_addUcb_additive_iff_compContinuous_mem_ucb.1 f.2⟩
  left_inv _ := UCB.ext fun _ => by simp
  right_inv _ := AddUCB.ext fun _ => by simp
  map_mul' _ _ := AddUCB.ext fun _ => rfl
  map_add' _ _ := AddUCB.ext fun _ => rfl
  commutes' _ := AddUCB.ext fun _ => rfl

@[simp]
theorem equivAdditive_apply (f : UCB G) (x : Additive G) :
    (equivAdditive f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul :=
  (rfl)

@[simp]
theorem equivAdditive_symm_apply (f : AddUCB (Additive G)) (x : G) :
    (equivAdditive.symm f : G →ᵇ ℝ) x = (f : Additive G →ᵇ ℝ) (ofMul x) :=
  (rfl)

/-- `equivAdditive` preserves and reflects the pointwise order. -/
@[simp]
theorem equivAdditive_le_equivAdditive_iff {f g : UCB G} :
    equivAdditive f ≤ equivAdditive g ↔ f ≤ g := by
  simp only [AddUCB.le_def, equivAdditive_apply, UCB.le_def]
  exact ⟨fun h x => h (ofMul x), fun h x => h x.toMul⟩

/-- `equivAdditive.symm` preserves and reflects the pointwise order. -/
@[simp]
theorem equivAdditive_symm_le_equivAdditive_symm_iff {f g : AddUCB (Additive G)} :
    equivAdditive.symm f ≤ equivAdditive.symm g ↔ f ≤ g := by
  simp only [UCB.le_def, equivAdditive_symm_apply, AddUCB.le_def]
  exact ⟨fun h x => h x.toMul, fun h x => h (ofMul x)⟩

/-- `equivAdditive` preserves the supremum norm. -/
@[simp]
theorem norm_equivAdditive (f : UCB G) :
    ‖(equivAdditive f : Additive G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ := by
  refine le_antisymm ((f : G →ᵇ ℝ).norm_compContinuous_le ⟨toMul, continuous_toMul⟩) ?_
  exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
    (equivAdditive f : Additive G →ᵇ ℝ).norm_coe_le_norm (ofMul x)

/-- `equivAdditive.symm` preserves the supremum norm. -/
@[simp]
theorem norm_equivAdditive_symm (f : AddUCB (Additive G)) :
    ‖(equivAdditive.symm f : G →ᵇ ℝ)‖ = ‖(f : Additive G →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_equivAdditive (equivAdditive.symm f)).symm

/-- `equivAdditive` intertwines multiplicative left translation by `g` with additive left
translation by `Additive.ofMul g`. -/
@[simp]
theorem equivAdditive_leftTranslation (g : G) (f : UCB G) :
    equivAdditive (leftTranslation g f) = AddUCB.leftTranslation (ofMul g) (equivAdditive f) := by
  ext x
  simp

/-- `equivAdditive.symm` intertwines additive left translation by `a` with multiplicative left
translation by `a.toMul`. -/
@[simp]
theorem equivAdditive_symm_leftTranslation (a : Additive G) (f : AddUCB (Additive G)) :
    equivAdditive.symm (AddUCB.leftTranslation a f) =
      leftTranslation a.toMul (equivAdditive.symm f) := by
  ext x
  simp

end Additive

end UCB

end TauCeti
