/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Bounded uniformly continuous functions on an additive topological group

For an additive topological group `A`, `TauCeti.AddUCB A` (carrier of the subalgebra
`TauCeti.addUCB A` of `A →ᵇ ℝ`) consists of the bounded continuous real-valued functions `f` on `A`
such that `f (u + x)` is uniformly close to `f x` for all `u` near `0` — equivalently, functions
that are uniformly continuous for the right uniformity `IsTopologicalAddGroup.rightUniformSpace A`.

Precomposition with `Multiplicative.toAdd` / `Multiplicative.ofAdd` identifies `AddUCB A` with
`UCB (Multiplicative A)` as an ordered normed unital `ℝ`-algebra (`AddUCB.toMultiplicativeAlgEquiv`,
`AddUCB.toMultiplicativeLinearIsometryEquiv`), and similarly identifies `UCB G` with
`AddUCB (Additive G)`. Left translation `AddUCB.leftTranslation a` sends `f` to `x ↦ f (-a + x)` and
right translation `AddUCB.rightTranslation a` sends `f` to `x ↦ f (x + a)`; both are conjugated from
`UCB (Multiplicative A)` through `toMultiplicativeLinearIsometryEquiv`.

## Main definitions

* `TauCeti.addUCBSubalgebra 𝕜 A`: `𝕜`-valued bounded right-uniformly continuous functions on `A`.
* `TauCeti.addUCB A`, `TauCeti.AddUCB A`: the real Banach algebra of bounded right-uniformly
  continuous functions on `A`.
* `TauCeti.AddUCB.toMultiplicativeAlgEquiv`, `TauCeti.AddUCB.toMultiplicativeLinearIsometryEquiv`,
  `TauCeti.UCB.toAdditiveAlgEquiv`, `TauCeti.UCB.toAdditiveLinearIsometryEquiv`: canonical algebra
  and linear-isometry identifications across `Multiplicative` and `Additive`.
* `TauCeti.AddUCB.leftTranslation`, `TauCeti.AddUCB.rightTranslation`: left and right translations
  on `AddUCB A`.
* `TauCeti.AddUCB.compRightAlgHom`: pullback along a continuous additive homomorphism `φ : A →ₜ+ B`.
* `TauCeti.AddUCB.discreteAlgEquiv`, `TauCeti.AddUCB.discreteLinearIsometryEquiv`: identification of
  `AddUCB A` with `A →ᵇ ℝ` when `A` is discrete.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction NNReal

namespace TauCeti

section Subalgebra

variable {𝕜 A : Type*} [NormedField 𝕜] [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (𝕜 A) in
/-- The bounded continuous functions `f : A →ᵇ 𝕜` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ 𝕜`. -/
def addUCBSubalgebra : Subalgebra 𝕜 (A →ᵇ 𝕜) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, ‖f (u + x) - f x‖ < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' _ := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]
    exact tendsto_const_nhds

attribute [to_additive existing addUCBSubalgebra] ucbSubalgebra

/-- The defining condition of `addUCBSubalgebra 𝕜 A`. -/
theorem mem_addUCBSubalgebra_iff {f : A →ᵇ 𝕜} :
    f ∈ addUCBSubalgebra 𝕜 A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, ‖f (u + x) - f x‖ < ε :=
  Iff.rfl

attribute [to_additive existing mem_addUCBSubalgebra_iff] mem_ucbSubalgebra_iff

/-- Membership in `addUCBSubalgebra 𝕜 A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as
`u → 0`. -/
theorem mem_addUCBSubalgebra_iff_tendsto {f : A →ᵇ 𝕜} :
    f ∈ addUCBSubalgebra 𝕜 A ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  simp only [mem_addUCBSubalgebra_iff, ← dist_eq_norm,
    BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]

attribute [to_additive existing mem_addUCBSubalgebra_iff_tendsto] mem_ucbSubalgebra_iff_tendsto

/-- A bounded continuous function with compact support belongs to `addUCBSubalgebra 𝕜 A`. -/
theorem mem_addUCBSubalgebra_of_hasCompactSupport {f : A →ᵇ 𝕜} (hf : HasCompactSupport f) :
    f ∈ addUCBSubalgebra 𝕜 A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  simpa only [mem_addUCBSubalgebra_iff, dist_eq_norm] using
    (uniformContinuous_rightUniformSpace_add_iff f).1
      (hf.uniformContinuous_of_continuous f.continuous)

attribute [to_additive existing mem_addUCBSubalgebra_of_hasCompactSupport]
  mem_ucbSubalgebra_of_hasCompactSupport

end Subalgebra

section Real

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (A) in
/-- The real bounded continuous functions `f` on `A` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ ℝ`. -/
@[expose]
def addUCB : Subalgebra ℝ (A →ᵇ ℝ) :=
  addUCBSubalgebra ℝ A

attribute [to_additive existing addUCB] ucb

variable (A) in
/-- The real Banach algebra of bounded functions on `A` that are uniformly continuous under small
left addition, with the supremum norm, algebra operations and order of `A →ᵇ ℝ`. -/
abbrev AddUCB : Type _ := addUCB A

attribute [to_additive existing AddUCB] UCB
attribute [to_additive_dont_translate] UCB AddUCB

variable (A) in
/-- `addUCB A` is the case `𝕜 = ℝ` of `addUCBSubalgebra 𝕜 A`. -/
theorem addUCB_eq_addUCBSubalgebra : addUCB A = addUCBSubalgebra ℝ A :=
  rfl

/-- The defining condition of `addUCB A`. -/
theorem mem_addUCB_iff {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, |f (u + x) - f x| < ε := by
  simp only [addUCB_eq_addUCBSubalgebra, mem_addUCBSubalgebra_iff, Real.norm_eq_abs]

attribute [to_additive existing mem_addUCB_iff] mem_ucb_iff

/-- Membership in `addUCB A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as `u → 0`. -/
theorem mem_addUCB_iff_tendsto {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  rw [addUCB_eq_addUCBSubalgebra, mem_addUCBSubalgebra_iff_tendsto]

attribute [to_additive existing mem_addUCB_iff_tendsto] mem_ucb_iff_tendsto

/-- Membership in `addUCB A` is uniform continuity for the right uniformity of `A`. -/
theorem mem_addUCB_iff_uniformContinuous {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔
      (letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
       UniformContinuous f) := by
  simp only [mem_addUCB_iff, ← Real.dist_eq, uniformContinuous_rightUniformSpace_add_iff]

attribute [to_additive existing mem_addUCB_iff_uniformContinuous] mem_ucb_iff_uniformContinuous

/-- A bounded continuous function with compact support belongs to `addUCB A`. -/
theorem mem_addUCB_of_hasCompactSupport {f : A →ᵇ ℝ} (hf : HasCompactSupport f) : f ∈ addUCB A :=
  mem_addUCBSubalgebra_of_hasCompactSupport hf

attribute [to_additive existing mem_addUCB_of_hasCompactSupport] mem_ucb_of_hasCompactSupport

/-- Precomposing `f : A →ᵇ ℝ` with `Multiplicative.toAdd` lands in `ucb (Multiplicative A)`
precisely when `f` belongs to `addUCB A`. -/
@[simp]
theorem compContinuous_toAdd_mem_ucb_iff {f : A →ᵇ ℝ} :
    f.compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩ ∈ ucb (Multiplicative A) ↔
      f ∈ addUCB A := by
  have h1 : (1 : Multiplicative A) = Multiplicative.ofAdd 0 := rfl
  rw [mem_ucb_iff, mem_addUCB_iff, h1, nhds_ofAdd]
  simp only [Filter.eventually_map]
  exact forall₂_congr fun _ _ => eventually_congr <| .of_forall fun u =>
    ⟨fun h x => h (Multiplicative.ofAdd x), fun h x => h x.toAdd⟩

/-- Precomposing `f : Multiplicative A →ᵇ ℝ` with `Multiplicative.ofAdd` lands in `addUCB A`
precisely when `f` belongs to `ucb (Multiplicative A)`. -/
@[simp]
theorem compContinuous_ofAdd_mem_addUCB_iff {f : Multiplicative A →ᵇ ℝ} :
    f.compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ ∈ addUCB A ↔
      f ∈ ucb (Multiplicative A) := by
  rw [← compContinuous_toAdd_mem_ucb_iff]
  rfl

/-- `addUCB A` is closed in `A →ᵇ ℝ`: a uniform limit of functions in `addUCB A` lies in
`addUCB A`. -/
theorem isClosed_addUCB : IsClosed (addUCB A : Set (A →ᵇ ℝ)) := by
  let c : C(Multiplicative A, A) := ⟨Multiplicative.toAdd, continuous_toAdd⟩
  have hcont : Continuous fun f : A →ᵇ ℝ => f.compContinuous c :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun f g => by
      have hsub : f.compContinuous c - g.compContinuous c = (f - g).compContinuous c := by
        ext
        simp
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm, hsub] using
        (f - g).norm_compContinuous_le c).continuous
  have hpre : (addUCB A : Set (A →ᵇ ℝ)) =
      (fun f : A →ᵇ ℝ => f.compContinuous c) ⁻¹'
        (ucb (Multiplicative A) : Set (Multiplicative A →ᵇ ℝ)) := by
    ext f
    exact compContinuous_toAdd_mem_ucb_iff.symm
  rw [hpre]
  exact isClosed_ucb.preimage hcont

/-- `AddUCB A` is a real normed group for the supremum norm of `A →ᵇ ℝ`. -/
instance : NormedAddCommGroup (AddUCB A) :=
  inferInstance

attribute [to_additive existing instNormedAddCommGroupAddUCB] instNormedAddCommGroupUCB

/-- `AddUCB A` is a real Banach space. -/
instance : CompleteSpace (AddUCB A) :=
  isClosed_addUCB.completeSpace_coe

attribute [to_additive existing instCompleteSpaceAddUCB] instCompleteSpaceUCB

/-- Scalar multiplication on `AddUCB A` scales the supremum norm. -/
instance : NormSMulClass ℝ (AddUCB A) :=
  ⟨fun c f => norm_smul c (f : A →ᵇ ℝ)⟩

attribute [to_additive existing instNormSMulClassRealAddUCB] instNormSMulClassRealUCB

/-- Constant functions belong to `addUCB A`. -/
@[simp]
theorem const_mem_addUCB (c : ℝ) : BoundedContinuousFunction.const A c ∈ addUCB A :=
  fun ε hε => .of_forall fun _ _ => by simpa using hε

/-- `addUCB A` is closed under the pointwise maximum. -/
theorem sup_mem_addUCB {f g : A →ᵇ ℝ} (hf : f ∈ addUCB A) (hg : g ∈ addUCB A) :
    f ⊔ g ∈ addUCB A := by
  rw [mem_addUCB_iff_tendsto] at hf hg ⊢
  exact hf.sup_nhds hg

/-- `addUCB A` is closed under the pointwise minimum. -/
theorem inf_mem_addUCB {f g : A →ᵇ ℝ} (hf : f ∈ addUCB A) (hg : g ∈ addUCB A) :
    f ⊓ g ∈ addUCB A := by
  rw [mem_addUCB_iff_tendsto] at hf hg ⊢
  exact hf.inf_nhds hg

/-- `addUCB A` is closed under the pointwise absolute value. -/
theorem abs_mem_addUCB {f : A →ᵇ ℝ} (hf : f ∈ addUCB A) : |f| ∈ addUCB A :=
  sup_mem_addUCB hf (neg_mem hf)

/-- `AddUCB A` is a lattice for the pointwise maximum and minimum. -/
instance : Lattice (AddUCB A) :=
  Subtype.lattice (fun _ _ => sup_mem_addUCB) (fun _ _ => inf_mem_addUCB)

attribute [to_additive existing instLatticeAddUCB] instLatticeUCB

/-- The supremum norm of `AddUCB A` is solid for its pointwise order, as in `A →ᵇ ℝ`. -/
instance : HasSolidNorm (AddUCB A) where
  solid _ _ h := HasSolidNorm.solid (α := A →ᵇ ℝ) h

attribute [to_additive existing instHasSolidNormAddUCB] instHasSolidNormUCB

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

variable (A) in
/-- The canonical unital algebra isomorphism between `AddUCB A` and `UCB (Multiplicative A)`. -/
def toMultiplicativeAlgEquiv : AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A) where
  toFun f := ⟨(f : A →ᵇ ℝ).compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩,
    compContinuous_toAdd_mem_ucb_iff.2 f.2⟩
  invFun f := ⟨(f : Multiplicative A →ᵇ ℝ).compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩,
    compContinuous_ofAdd_mem_addUCB_iff.2 f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem toMultiplicativeAlgEquiv_apply (f : AddUCB A) (x : Multiplicative A) :
    (toMultiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ) x = (f : A →ᵇ ℝ) x.toAdd :=
  (rfl)

@[simp]
theorem toMultiplicativeAlgEquiv_symm_apply (f : UCB (Multiplicative A)) (x : A) :
    ((toMultiplicativeAlgEquiv A).symm f : A →ᵇ ℝ) x =
      (f : Multiplicative A →ᵇ ℝ) (Multiplicative.ofAdd x) :=
  (rfl)

@[simp]
theorem toMultiplicativeAlgEquiv_le_iff {f g : AddUCB A} :
    toMultiplicativeAlgEquiv A f ≤ toMultiplicativeAlgEquiv A g ↔ f ≤ g :=
  ⟨fun h => le_def.2 fun x => UCB.le_def.1 h (Multiplicative.ofAdd x),
    fun h => UCB.le_def.2 fun x => le_def.1 h x.toAdd⟩

@[simp]
theorem toMultiplicativeAlgEquiv_symm_le_iff {f g : UCB (Multiplicative A)} :
    (toMultiplicativeAlgEquiv A).symm f ≤ (toMultiplicativeAlgEquiv A).symm g ↔ f ≤ g :=
  ⟨fun h => UCB.le_def.2 fun x => le_def.1 h x.toAdd,
    fun h => le_def.2 fun x => UCB.le_def.1 h (Multiplicative.ofAdd x)⟩

variable (A) in
/-- The canonical linear isometry equivalence between `AddUCB A` and `UCB (Multiplicative A)`. -/
def toMultiplicativeLinearIsometryEquiv : AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A) where
  toLinearEquiv := (toMultiplicativeAlgEquiv A).toLinearEquiv
  norm_map' f := by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    refine le_antisymm ((f : A →ᵇ ℝ).norm_compContinuous_le _) ?_
    exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
      ((toMultiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ).norm_coe_le_norm
        (Multiplicative.ofAdd x))

@[simp]
theorem coe_toMultiplicativeLinearIsometryEquiv (f : AddUCB A) :
    toMultiplicativeLinearIsometryEquiv A f = toMultiplicativeAlgEquiv A f :=
  (rfl)

@[simp]
theorem coe_toMultiplicativeLinearIsometryEquiv_symm (f : UCB (Multiplicative A)) :
    (toMultiplicativeLinearIsometryEquiv A).symm f = (toMultiplicativeAlgEquiv A).symm f :=
  (rfl)

/-- Left translation `L_a` on `AddUCB A`, sending `f` to `x ↦ f (-a + x)`, as a linear isometry
equivalence. -/
def leftTranslation (a : A) : AddUCB A ≃ₗᵢ[ℝ] AddUCB A :=
  (toMultiplicativeLinearIsometryEquiv A).trans
    ((UCB.leftTranslation (Multiplicative.ofAdd a)).trans
      (toMultiplicativeLinearIsometryEquiv A).symm)

/-- Right translation `R_a` on `AddUCB A`, sending `f` to `x ↦ f (x + a)`, as a linear isometry
equivalence. -/
def rightTranslation (a : A) : AddUCB A ≃ₗᵢ[ℝ] AddUCB A :=
  (toMultiplicativeLinearIsometryEquiv A).trans
    ((UCB.rightTranslation (Multiplicative.ofAdd a)).trans
      (toMultiplicativeLinearIsometryEquiv A).symm)

@[simp]
theorem leftTranslation_apply (a : A) (f : AddUCB A) (x : A) :
    (leftTranslation a f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (-a + x) := by
  simp [leftTranslation]

@[simp]
theorem rightTranslation_apply (a : A) (f : AddUCB A) (x : A) :
    (rightTranslation a f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (x + a) := by
  simp [rightTranslation]

@[simp]
theorem toMultiplicativeAlgEquiv_leftTranslation (a : A) (f : AddUCB A) :
    toMultiplicativeAlgEquiv A (leftTranslation a f) =
      UCB.leftTranslation (Multiplicative.ofAdd a) (toMultiplicativeAlgEquiv A f) := by
  simp [leftTranslation]

@[simp]
theorem toMultiplicativeAlgEquiv_symm_leftTranslation (g : Multiplicative A)
    (f : UCB (Multiplicative A)) :
    (toMultiplicativeAlgEquiv A).symm (UCB.leftTranslation g f) =
      leftTranslation g.toAdd ((toMultiplicativeAlgEquiv A).symm f) := by
  apply (toMultiplicativeAlgEquiv A).injective
  simp

@[simp]
theorem leftTranslation_zero : leftTranslation (0 : A) = 1 := by
  ext
  simp

theorem leftTranslation_add (a b : A) :
    leftTranslation (a + b) = leftTranslation a * leftTranslation b := by
  ext
  simp [neg_add_rev, add_assoc]

@[simp]
theorem leftTranslation_symm (a : A) : (leftTranslation a).symm = leftTranslation (-a) := by
  ext
  simp [leftTranslation]

@[simp]
theorem leftTranslation_le_leftTranslation_iff {a : A} {f f' : AddUCB A} :
    leftTranslation a f ≤ leftTranslation a f' ↔ f ≤ f' := by
  rw [← toMultiplicativeAlgEquiv_le_iff (A := A), toMultiplicativeAlgEquiv_leftTranslation,
    toMultiplicativeAlgEquiv_leftTranslation, UCB.leftTranslation_le_leftTranslation_iff,
    toMultiplicativeAlgEquiv_le_iff]

@[simp]
theorem leftTranslation_apply_one (a : A) : leftTranslation a 1 = 1 := by
  ext
  simp

@[simp]
theorem leftTranslation_apply_algebraMap (a : A) (c : ℝ) :
    leftTranslation a (algebraMap ℝ (AddUCB A) c) = algebraMap ℝ (AddUCB A) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- The orbit map `a ↦ L_a f` of a function `f` in `AddUCB A` is continuous for the supremum
norm. -/
theorem continuous_leftTranslation_apply (f : AddUCB A) :
    Continuous fun a : A => leftTranslation a f := by
  have h : (fun a : A => leftTranslation a f) = fun a : A =>
      (toMultiplicativeLinearIsometryEquiv A).symm
        (UCB.leftTranslation (Multiplicative.ofAdd a) (toMultiplicativeAlgEquiv A f)) := by
    ext a x
    simp
  rw [h]
  exact (toMultiplicativeLinearIsometryEquiv A).symm.continuous.comp
    ((UCB.continuous_leftTranslation_apply _).comp continuous_ofAdd)

end AddUCB

end Real

section CompRight

variable {A B : Type*}
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- The pullback `x ↦ f (φ x)` of a function in `addUCB B` along a continuous additive homomorphism
`φ : A →ₜ+ B` lies in `addUCB A`. -/
theorem compContinuous_mem_addUCB {f : B →ᵇ ℝ} (hf : f ∈ addUCB B) (φ : A →ₜ+ B) :
    f.compContinuous (φ : C(A, B)) ∈ addUCB A := by
  have hφ : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa using φ.continuous.tendsto (0 : A)
  rw [mem_addUCB_iff] at hf ⊢
  intro ε hε
  filter_upwards [hφ.eventually (hf ε hε)] with u hu x
  simpa using hu (φ x)

attribute [to_additive existing compContinuous_mem_addUCB] compContinuous_mem_ucb

namespace AddUCB

/-- The pullback `f ↦ f ∘ φ` along a continuous additive homomorphism `φ : A →ₜ+ B`, as a unital
algebra homomorphism from `AddUCB B` to `AddUCB A`. -/
def compRightAlgHom (φ : A →ₜ+ B) : AddUCB B →ₐ[ℝ] AddUCB A where
  toFun f := ⟨(f : B →ᵇ ℝ).compContinuous (φ : C(A, B)), compContinuous_mem_addUCB f.2 φ⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

attribute [to_additive existing] UCB.compRightAlgHom

theorem coe_compRightAlgHom (φ : A →ₜ+ B) (f : AddUCB B) :
    (compRightAlgHom φ f : A →ᵇ ℝ) = (f : B →ᵇ ℝ).compContinuous (φ : C(A, B)) :=
  (rfl)

@[simp]
theorem compRightAlgHom_apply (φ : A →ₜ+ B) (f : AddUCB B) (x : A) :
    (compRightAlgHom φ f : A →ᵇ ℝ) x = (f : B →ᵇ ℝ) (φ x) :=
  (rfl)

@[simp]
theorem compRightAlgHom_id :
    compRightAlgHom (ContinuousAddMonoidHom.id A) = AlgHom.id ℝ (AddUCB A) :=
  (rfl)

theorem compRightAlgHom_comp {C : Type*} [AddGroup C] [TopologicalSpace C]
    [IsTopologicalAddGroup C] (ψ : B →ₜ+ C) (φ : A →ₜ+ B) :
    compRightAlgHom (ψ.comp φ) = (compRightAlgHom φ).comp (compRightAlgHom ψ) :=
  (rfl)

/-- The pullback preserves the pointwise order. -/
theorem monotone_compRightAlgHom (φ : A →ₜ+ B) : Monotone (compRightAlgHom φ) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (φ x)

/-- The pullback does not increase the supremum norm. -/
theorem norm_compRightAlgHom_apply_le (φ : A →ₜ+ B) (f : AddUCB B) :
    ‖compRightAlgHom φ f‖ ≤ ‖f‖ :=
  (f : B →ᵇ ℝ).norm_compContinuous_le _

/-- The pullback intertwines left translation by `φ a` with left translation by `a`. -/
theorem compRightAlgHom_leftTranslation (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    compRightAlgHom φ (leftTranslation (φ a) f) = leftTranslation a (compRightAlgHom φ f) := by
  ext
  simp

end AddUCB

end CompRight

section Discrete

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- On a discrete additive group the `addUCB` subalgebra is the entire bounded-function algebra. -/
@[simp]
theorem addUCB_eq_top : addUCB A = ⊤ := by
  ext f
  simp [mem_addUCB_iff, nhds_discrete]

namespace AddUCB

variable (A) in
/-- The canonical algebra equivalence from `AddUCB A` to all bounded functions on a discrete
additive group. -/
def discreteAlgEquiv : AddUCB A ≃ₐ[ℝ] (A →ᵇ ℝ) :=
  (Subalgebra.equivOfEq _ _ addUCB_eq_top).trans Subalgebra.topEquiv

@[simp]
theorem discreteAlgEquiv_apply (f : AddUCB A) : discreteAlgEquiv A f = (f : A →ᵇ ℝ) :=
  (rfl)

@[simp]
theorem coe_discreteAlgEquiv_symm (f : A →ᵇ ℝ) :
    ((discreteAlgEquiv A).symm f : A →ᵇ ℝ) = f :=
  (discreteAlgEquiv A).apply_symm_apply f

variable (A) in
/-- The discrete identification as a linear isometry equivalence for the supremum norm. -/
def discreteLinearIsometryEquiv : AddUCB A ≃ₗᵢ[ℝ] (A →ᵇ ℝ) where
  toLinearEquiv := (discreteAlgEquiv A).toLinearEquiv
  norm_map' _ := rfl

end AddUCB

end Discrete

section ToAdditive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace UCB

variable (G) in
/-- The canonical unital algebra isomorphism between `UCB G` and `AddUCB (Additive G)`. -/
def toAdditiveAlgEquiv : UCB G ≃ₐ[ℝ] AddUCB (Additive G) where
  toFun f := ⟨(f : G →ᵇ ℝ).compContinuous ⟨Additive.toMul, continuous_toMul⟩, by
    have h0 : (0 : Additive G) = Additive.ofMul 1 := rfl
    rw [mem_addUCB_iff, h0, nhds_ofMul]
    intro ε hε
    rw [Filter.eventually_map]
    filter_upwards [mem_ucb_iff.1 f.2 ε hε] with u hu x
    exact hu x.toMul⟩
  invFun f := ⟨(f : Additive G →ᵇ ℝ).compContinuous ⟨Additive.ofMul, continuous_ofMul⟩, by
    have h1 : (1 : G) = (0 : Additive G).toMul := rfl
    rw [mem_ucb_iff, h1, nhds_toMul]
    intro ε hε
    rw [Filter.eventually_map]
    filter_upwards [mem_addUCB_iff.1 f.2 ε hε] with u hu x
    exact hu (Additive.ofMul x)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem toAdditiveAlgEquiv_apply (f : UCB G) (x : Additive G) :
    (toAdditiveAlgEquiv G f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul :=
  (rfl)

@[simp]
theorem toAdditiveAlgEquiv_symm_apply (f : AddUCB (Additive G)) (x : G) :
    ((toAdditiveAlgEquiv G).symm f : G →ᵇ ℝ) x = (f : Additive G →ᵇ ℝ) (Additive.ofMul x) :=
  (rfl)

variable (G) in
/-- The canonical linear isometry equivalence between `UCB G` and `AddUCB (Additive G)`. -/
def toAdditiveLinearIsometryEquiv : UCB G ≃ₗᵢ[ℝ] AddUCB (Additive G) where
  toLinearEquiv := (toAdditiveAlgEquiv G).toLinearEquiv
  norm_map' f := by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    refine le_antisymm ((f : G →ᵇ ℝ).norm_compContinuous_le _) ?_
    exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x =>
      ((toAdditiveAlgEquiv G f : Additive G →ᵇ ℝ).norm_coe_le_norm (Additive.ofMul x))

@[simp]
theorem toAdditiveAlgEquiv_leftTranslation (g : G) (f : UCB G) :
    toAdditiveAlgEquiv G (leftTranslation g f) =
      AddUCB.leftTranslation (Additive.ofMul g) (toAdditiveAlgEquiv G f) := by
  ext
  simp [toAdditiveAlgEquiv_apply]

end UCB

end ToAdditive

end TauCeti
