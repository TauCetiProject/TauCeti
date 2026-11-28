/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.Topology.Algebra.Group.UCB.Basic

/-!
# Means on bounded uniformly continuous functions

For a topological group `G`, a *mean* on `TauCeti.UCB G` is a real linear functional `m` which is
positive, `0 ≤ f → 0 ≤ m f`, and normalized, `m 1 = 1`. A left-invariant mean is the object whose
existence defines amenability of `G`.

This file develops the basic theory of means. Continuity is not part of the definition: since
every `f` lies below the constant `‖f‖`, positivity and normalization give `|m f| ≤ ‖f‖`, so a mean
is `1`-Lipschitz for the supremum norm, and in particular compatible with uniform limits. The
derived continuous linear functional has operator norm one. The means form a convex subset of the
continuous dual of `UCB G`, and evaluation at a point of `G` is a mean, so this set is nonempty.

## Main definitions

* `TauCeti.Mean G`, `TauCeti.AddMean A`: a positive normalized linear functional on `UCB G` (or
  `AddUCB A`).
* `TauCeti.Mean.equivNormalizedPositiveLinearMap`,
  `TauCeti.AddMean.equivNormalizedPositiveLinearMap`: the bijection between means and normalized
  positive linear functionals.
* `TauCeti.Mean.toContinuousLinearMap`, `TauCeti.AddMean.toContinuousLinearMap`: the continuous
  linear functional underlying a mean.
* `TauCeti.Mean.eval`, `TauCeti.AddMean.eval`: evaluation at a point, as a mean.

## Main results

* `TauCeti.Mean.map_algebraMap` (and `AddMean` counterpart): a mean takes the value `c` at the
  constant function `c`.
* `TauCeti.Mean.ciInf_le_apply`, `TauCeti.Mean.apply_le_ciSup` (and `AddMean` counterparts):
  `⨅ x, f x ≤ m f ≤ ⨆ x, f x`.
* `TauCeti.Mean.abs_apply_le_norm`, `TauCeti.Mean.abs_apply_sub_apply_le` (and `AddMean`
  counterparts): `|m f| ≤ ‖f‖` and `|m f - m g| ≤ ‖f - g‖`.
* `TauCeti.Mean.lipschitzWith` (and `AddMean` counterpart): a mean is `1`-Lipschitz; it is
  therefore a `ContinuousLinearMapClass`.
* `TauCeti.Mean.norm_toContinuousLinearMap` (and `AddMean` counterpart): a mean has operator norm
  one.
* `TauCeti.Mean.mem_range_toContinuousLinearMap_iff` (and `AddMean` counterpart): the continuous
  linear functionals coming from means are exactly the positive ones taking the value `1` at `1`.
* `TauCeti.Mean.convex_range_toContinuousLinearMap` (and `AddMean` counterpart): the means form a
  convex set.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (A) in
/-- A mean on `AddUCB A`: a positive real linear functional taking the value `1` at the constant
function `1`. -/
structure AddMean extends AddUCB A →ₚ[ℝ] ℝ where
  /-- A mean takes the value `1` at the constant function `1`. -/
  map_one' : toFun 1 = 1

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (G) in
/-- A mean on `UCB G`: a positive real linear functional taking the value `1` at the constant
function `1`. -/
@[to_additive existing AddMean, to_additive_dont_translate]
structure Mean extends UCB G →ₚ[ℝ] ℝ where
  /-- A mean takes the value `1` at the constant function `1`. -/
  map_one' : toFun 1 = 1

namespace Mean

@[to_additive]
instance : FunLike (Mean G) (UCB G) ℝ where
  coe m := m.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

@[to_additive]
instance : LinearMapClass (Mean G) ℝ (UCB G) ℝ where
  map_add m := map_add m.toPositiveLinearMap
  map_smulₛₗ m := map_smul m.toPositiveLinearMap

@[to_additive]
instance : OrderHomClass (Mean G) (UCB G) ℝ where
  map_rel m _ _ h := OrderHomClass.mono m.toPositiveLinearMap h

/-- Two means are equal when they agree on every function. -/
@[to_additive (attr := ext) /-- Two additive means are equal when they agree on every function. -/]
theorem ext {m n : Mean G} (h : ∀ f, m f = n f) : m = n :=
  DFunLike.ext m n h

@[to_additive (attr := simp)]
theorem coe_toPositiveLinearMap (m : Mean G) : ⇑m.toPositiveLinearMap = ⇑m :=
  (rfl)

@[to_additive]
theorem toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap : Mean G → UCB G →ₚ[ℝ] ℝ) :=
  fun _ _ h => ext fun f => DFunLike.congr_fun h f

/-- A mean takes the value `1` at the constant function `1`. -/
@[to_additive (attr := simp) map_one
  /-- An additive mean takes the value `1` at the constant function `1`. -/]
theorem map_one (m : Mean G) : m 1 = 1 :=
  m.map_one'

/-- A mean built from a linear functional which is nonnegative on nonnegative functions and takes
the value `1` at `1`. -/
@[to_additive
  /-- An additive mean built from a linear functional which is nonnegative on nonnegative functions
  and takes the value `1` at `1`. -/]
def mk₀ (φ : UCB G →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1) : Mean G :=
  { PositiveLinearMap.mk₀ φ hφ with map_one' := h₁ }

@[to_additive (attr := simp)]
theorem mk₀_apply (φ : UCB G →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1) (f : UCB G) :
    mk₀ φ hφ h₁ f = φ f :=
  (rfl)

variable (G) in
/-- Means on `UCB G` correspond bijectively to normalized positive linear functionals on
`UCB G`. -/
@[to_additive
  /-- Additive means on `AddUCB G` correspond bijectively to normalized positive linear
  functionals on `AddUCB G`. -/]
def equivNormalizedPositiveLinearMap : Mean G ≃ {m : UCB G →ₚ[ℝ] ℝ // m 1 = 1} where
  toFun m := ⟨m.toPositiveLinearMap, m.map_one⟩
  invFun m := mk₀ m.val.toLinearMap (fun _ hf => map_nonneg m.val hf) m.property
  left_inv _ := ext fun _ => rfl
  right_inv _ :=
    Subtype.ext <| PositiveLinearMap.toLinearMap_injective <| LinearMap.ext fun _ => rfl

@[to_additive (attr := simp)]
theorem equivNormalizedPositiveLinearMap_apply (m : Mean G) (f : UCB G) :
    (equivNormalizedPositiveLinearMap G m).val f = m f :=
  (rfl)

@[to_additive (attr := simp)]
theorem equivNormalizedPositiveLinearMap_symm_apply
    (m : {m : UCB G →ₚ[ℝ] ℝ // m 1 = 1}) (f : UCB G) :
    (equivNormalizedPositiveLinearMap G).symm m f = m.val f :=
  (rfl)

variable (m : Mean G)

/-- A mean takes the value `c` at the constant function `c`. -/
@[to_additive (attr := simp) /-- An additive mean takes the value `c` at the constant function
`c`. -/]
theorem map_algebraMap (c : ℝ) : m (algebraMap ℝ (UCB G) c) = c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- A mean of a function bounded above by `c` is at most `c`. -/
@[to_additive /-- An additive mean of a function bounded above by `c` is at most `c`. -/]
theorem apply_le_of_forall_le {f : UCB G} {c : ℝ} (h : ∀ x, (f : G →ᵇ ℝ) x ≤ c) : m f ≤ c := by
  have hf : f ≤ algebraMap ℝ (UCB G) c := UCB.le_def.2 (by simpa)
  simpa using OrderHomClass.mono m hf

/-- A mean of a function bounded below by `c` is at least `c`. -/
@[to_additive /-- An additive mean of a function bounded below by `c` is at least `c`. -/]
theorem le_apply_of_forall_le {f : UCB G} {c : ℝ} (h : ∀ x, c ≤ (f : G →ᵇ ℝ) x) : c ≤ m f := by
  have hf : algebraMap ℝ (UCB G) c ≤ f := UCB.le_def.2 (by simpa)
  simpa using OrderHomClass.mono m hf

/-- A mean of a function is at least the infimum of its values. -/
@[to_additive /-- An additive mean of a function is at least the infimum of its values. -/]
theorem ciInf_le_apply (f : UCB G) : ⨅ x, (f : G →ᵇ ℝ) x ≤ m f :=
  m.le_apply_of_forall_le fun x =>
    ciInf_le ⟨-‖f‖, by rintro _ ⟨y, rfl⟩; exact (f : G →ᵇ ℝ).neg_norm_le_apply y⟩ x

/-- A mean of a function is at most the supremum of its values. -/
@[to_additive /-- An additive mean of a function is at most the supremum of its values. -/]
theorem apply_le_ciSup (f : UCB G) : m f ≤ ⨆ x, (f : G →ᵇ ℝ) x :=
  m.apply_le_of_forall_le fun x =>
    le_ciSup ⟨‖f‖, by rintro _ ⟨y, rfl⟩; exact (f : G →ᵇ ℝ).apply_le_norm y⟩ x

/-- A mean of a function is bounded in absolute value by its supremum norm. -/
@[to_additive /-- An additive mean of a function is bounded in absolute value by its supremum
norm. -/]
theorem abs_apply_le_norm (f : UCB G) : |m f| ≤ ‖f‖ := by
  simpa using PositiveLinearMap.abs_apply_le_mul_norm m (OrderHomClass.mono m)
    (UCB.le_norm_smul_one (G := G)) f

/-- A mean changes by at most the supremum distance between its arguments. -/
@[to_additive /-- An additive mean changes by at most the supremum distance between its
arguments. -/]
theorem abs_apply_sub_apply_le (f g : UCB G) : |m f - m g| ≤ ‖f - g‖ := by
  simpa using
    PositiveLinearMap.abs_apply_sub_apply_le_mul_norm m (UCB.le_norm_smul_one (G := G)) f g

/-- A mean is `1`-Lipschitz for the supremum norm. -/
@[to_additive /-- An additive mean is `1`-Lipschitz for the supremum norm. -/]
theorem lipschitzWith : LipschitzWith 1 m := by
  simpa using
    PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul m (UCB.le_norm_smul_one (G := G))

/-- A mean is continuous for the supremum norm. -/
@[to_additive /-- An additive mean is continuous for the supremum norm. -/]
instance : ContinuousLinearMapClass (Mean G) ℝ (UCB G) ℝ where
  map_continuous m := m.lipschitzWith.continuous

/-- The continuous linear functional underlying a mean. -/
@[to_additive /-- The continuous linear functional underlying an additive mean. -/]
def toContinuousLinearMap : UCB G →L[ℝ] ℝ where
  toLinearMap := m.toPositiveLinearMap.toLinearMap
  cont := map_continuous m

@[to_additive (attr := simp)]
theorem coe_toContinuousLinearMap : ⇑m.toContinuousLinearMap = ⇑m :=
  (rfl)

@[to_additive]
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : Mean G → UCB G →L[ℝ] ℝ) :=
  fun _ _ h => ext fun f => DFunLike.congr_fun h f

/-- A mean has operator norm one. -/
@[to_additive (attr := simp) /-- An additive mean has operator norm one. -/]
theorem norm_toContinuousLinearMap : ‖m.toContinuousLinearMap‖ = 1 := by
  rw [m.toContinuousLinearMap.opNorm_eq_apply_of_monotone (OrderHomClass.mono m)
    UCB.le_norm_smul_one norm_one.le]
  simp

/-- A continuous linear functional on `UCB G` comes from a mean exactly when it is nonnegative on
nonnegative functions and takes the value `1` at `1`. -/
@[to_additive
  /-- A continuous linear functional on `AddUCB G` comes from an additive mean exactly when it is
  nonnegative on nonnegative functions and takes the value `1` at `1`. -/]
theorem mem_range_toContinuousLinearMap_iff {φ : UCB G →L[ℝ] ℝ} :
    φ ∈ Set.range (toContinuousLinearMap : Mean G → UCB G →L[ℝ] ℝ) ↔
      (∀ f, 0 ≤ f → 0 ≤ φ f) ∧ φ 1 = 1 := by
  refine ⟨?_, fun ⟨hφ, h₁⟩ => ⟨mk₀ φ.toLinearMap hφ h₁, rfl⟩⟩
  rintro ⟨m, rfl⟩
  exact ⟨fun f hf => by simpa using map_nonneg m hf, by simp⟩

/-- The means on `UCB G` form a convex set of continuous linear functionals. -/
@[to_additive /-- The additive means on `AddUCB G` form a convex set of continuous linear
functionals. -/]
theorem convex_range_toContinuousLinearMap :
    Convex ℝ (Set.range (toContinuousLinearMap : Mean G → UCB G →L[ℝ] ℝ)) := by
  intro φ hφ ψ hψ a b ha hb hab
  rw [mem_range_toContinuousLinearMap_iff] at hφ hψ ⊢
  refine ⟨fun f hf => ?_, by simp [hφ.2, hψ.2, hab]⟩
  have := hφ.1 f hf
  have := hψ.1 f hf
  simp only [add_apply, smul_apply, smul_eq_mul]
  positivity

variable (G) in
/-- Evaluation at a point of `G` is a mean on `UCB G`. -/
@[to_additive /-- Evaluation at a point of `G` is an additive mean on `AddUCB G`. -/]
def eval (x : G) : Mean G :=
  mk₀ ((BoundedContinuousFunction.evalCLM ℝ x).toLinearMap ∘ₗ (ucb G).val.toLinearMap)
    (fun _ hf => UCB.le_def.1 hf x) rfl

@[to_additive (attr := simp)]
theorem eval_apply (x : G) (f : UCB G) : eval G x f = (f : G →ᵇ ℝ) x :=
  (rfl)

@[to_additive]
instance : Nonempty (Mean G) :=
  ⟨eval G 1⟩

end Mean

end TauCeti
