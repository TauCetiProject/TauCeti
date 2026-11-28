/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Topology.Algebra.Group.UCB.Basic
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Translations of bounded uniformly continuous functions

For a topological group `G`, the left translation of a function `f` on `G` by `g` is
`(L_g f)(x) = f (g⁻¹ * x)`, and its right translation is `(R_g f)(x) = f (x * g)`. Both preserve
`TauCeti.UCB G`, and both are linear isometries of the supremum norm, so they give two
commuting group homomorphisms

```text
TauCeti.UCB.leftTranslation, TauCeti.UCB.rightTranslation : G →* (UCB G ≃ₗᵢ[ℝ] UCB G).
```

Left translation is the action against which invariant means are defined. The defining
condition of `UCB G` says exactly that `u ↦ L_u f` is norm-continuous at `1`, so the orbit map
`g ↦ L_g f` is norm-continuous. The orbit map `g ↦ R_g f` is norm-continuous at `1` only when
`f (x * u)` is uniformly close to `f x` for all `u` near `1`, which is not part of the definition
of `UCB G`; no continuity statement is made for right translations.

## Main definitions

* `TauCeti.ucbSubalgebra.leftTranslation 𝕜 G`: `g ↦ L_g` on `ucbSubalgebra 𝕜 G`, with
  `L_g f = f (g⁻¹ * ·)`.
* `TauCeti.UCB.leftTranslation`: its case `𝕜 = ℝ`, on `UCB G`.
* `TauCeti.UCB.rightTranslation`: `g ↦ R_g`, with `R_g f = f (· * g)`.
* `TauCeti.AddUCB.leftTranslation`: additive left translation `a ↦ L_a` on `AddUCB A`, with
  `(L_a f)(x) = f (-a + x)`.
* `TauCeti.AddUCB.rightTranslation`: additive right translation `a ↦ R_a` on `AddUCB A`, with
  `(R_a f)(x) = f (x + a)`.

## Main results

* `TauCeti.compContinuous_mulLeft_mem_ucbSubalgebra`,
  `TauCeti.compContinuous_mulRight_mem_ucbSubalgebra` (and additive counterparts): `ucbSubalgebra`
  and `ucb` are closed under left and right translation.
* `TauCeti.UCB.leftTranslation_le_leftTranslation_iff`,
  `TauCeti.UCB.leftTranslation_apply_algebraMap` (and additive counterparts): left translation
  preserves the order and the constant functions; likewise for right translation.
* `TauCeti.UCB.continuous_leftTranslation_apply`,
  `TauCeti.AddUCB.continuous_leftTranslation_apply`: the orbit map `g ↦ L_g f` (or `a ↦ L_a f`) is
  continuous for the supremum norm.
* `TauCeti.UCB.commute_leftTranslation_rightTranslation`,
  `TauCeti.AddUCB.commute_leftTranslation_rightTranslation`: left and right translations commute.
* `TauCeti.UCB.sum_leftTranslation`: on a finite group, the sum of the left translates of `f` is
  the constant function `∑ x, f x`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and G.1.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {𝕜 G : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A left translate `x ↦ f (g * x)` of a function in `ucbSubalgebra 𝕜 G` lies in
`ucbSubalgebra 𝕜 G`. -/
@[to_additive (dont_translate := 𝕜) compContinuous_addLeft_mem_addUcbSubalgebra
  /-- A left translate `x ↦ f (g + x)` of a function in `addUcbSubalgebra 𝕜 G` lies in
  `addUcbSubalgebra 𝕜 G`. -/]
theorem compContinuous_mulLeft_mem_ucbSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ ucbSubalgebra 𝕜 G)
    (g : G) : f.compContinuous (ContinuousMap.mulLeft g) ∈ ucbSubalgebra 𝕜 G := by
  -- `g * u * x = (g * u * g⁻¹) * (g * x)`, and `g * u * g⁻¹ → 1` as `u → 1`.
  have hconj : Tendsto (fun u : G => g * u * g⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using ((continuous_const_mul g).mul_const g⁻¹).tendsto (1 : G)
  rw [mem_ucbSubalgebra_iff] at hf ⊢
  intro ε hε
  filter_upwards [hconj.eventually (hf ε hε)] with u hu x
  simpa [mul_assoc] using hu (g * x)

/-- A right translate `x ↦ f (x * g)` of a function in `ucbSubalgebra 𝕜 G` lies in
`ucbSubalgebra 𝕜 G`. -/
@[to_additive (dont_translate := 𝕜) compContinuous_addRight_mem_addUcbSubalgebra
  /-- A right translate `x ↦ f (x + g)` of a function in `addUcbSubalgebra 𝕜 G` lies in
  `addUcbSubalgebra 𝕜 G`. -/]
theorem compContinuous_mulRight_mem_ucbSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ ucbSubalgebra 𝕜 G)
    (g : G) : f.compContinuous (ContinuousMap.mulRight g) ∈ ucbSubalgebra 𝕜 G := by
  rw [mem_ucbSubalgebra_iff] at hf ⊢
  intro ε hε
  filter_upwards [hf ε hε] with u hu x
  simpa [mul_assoc] using hu (x * g)

/-- A left translate `x ↦ f (g * x)` of a function in `ucb G` lies in `ucb G`. -/
@[to_additive compContinuous_addLeft_mem_addUcb
  /-- A left translate `x ↦ f (g + x)` of a function in `addUcb G` lies in `addUcb G`. -/]
theorem compContinuous_mulLeft_mem_ucb {f : G →ᵇ ℝ} (hf : f ∈ ucb G) (g : G) :
    f.compContinuous (ContinuousMap.mulLeft g) ∈ ucb G := by
  rw [ucb_eq_ucbSubalgebra] at hf ⊢
  exact compContinuous_mulLeft_mem_ucbSubalgebra hf g

/-- A right translate `x ↦ f (x * g)` of a function in `ucb G` lies in `ucb G`. -/
@[to_additive compContinuous_addRight_mem_addUcb
  /-- A right translate `x ↦ f (x + g)` of a function in `addUcb G` lies in `addUcb G`. -/]
theorem compContinuous_mulRight_mem_ucb {f : G →ᵇ ℝ} (hf : f ∈ ucb G) (g : G) :
    f.compContinuous (ContinuousMap.mulRight g) ∈ ucb G := by
  rw [ucb_eq_ucbSubalgebra] at hf ⊢
  exact compContinuous_mulRight_mem_ucbSubalgebra hf g

namespace ucbSubalgebra

variable (𝕜 G) in
/-- Left translation `g ↦ L_g`, where `(L_g f)(x) = f (g⁻¹ * x)`, as a group homomorphism from `G`
to the linear isometry equivalences of `ucbSubalgebra 𝕜 G`. -/
def leftTranslation : G →* (ucbSubalgebra 𝕜 G ≃ₗᵢ[𝕜] ucbSubalgebra 𝕜 G) where
  toFun g := BoundedContinuousFunction.compContinuousₗᵢ (ucbSubalgebra 𝕜 G)
    (ContinuousMap.mulLeft g⁻¹) (ContinuousMap.mulLeft g) (by simp) (by simp)
    (fun _ hf => compContinuous_mulLeft_mem_ucbSubalgebra hf _)
    (fun _ hf => compContinuous_mulLeft_mem_ucbSubalgebra hf _)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_assoc]

/-- The left translate `L_g f` is the precomposition of `f` with `x ↦ g⁻¹ * x`. -/
theorem coe_leftTranslation (g : G) (f : ucbSubalgebra 𝕜 G) :
    (leftTranslation 𝕜 G g f : G →ᵇ 𝕜) =
      (f : G →ᵇ 𝕜).compContinuous (ContinuousMap.mulLeft g⁻¹) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp]
theorem leftTranslation_apply (g : G) (f : ucbSubalgebra 𝕜 G) (x : G) :
    (leftTranslation 𝕜 G g f : G →ᵇ 𝕜) x = (f : G →ᵇ 𝕜) (g⁻¹ * x) :=
  DFunLike.congr_fun (coe_leftTranslation g f) x

end ucbSubalgebra

namespace UCB

/-- Left translation `g ↦ L_g`, where `(L_g f)(x) = f (g⁻¹ * x)`, as a group homomorphism from `G`
to the linear isometry equivalences of `UCB G`; the case `𝕜 = ℝ` of
`ucbSubalgebra.leftTranslation`. -/
def leftTranslation : G →* (UCB G ≃ₗᵢ[ℝ] UCB G) :=
  ucbSubalgebra.leftTranslation ℝ G

/-- Right translation `g ↦ R_g`, where `(R_g f)(x) = f (x * g)`, as a group homomorphism from `G`
to the linear isometry equivalences of `UCB G`. -/
def rightTranslation : G →* (UCB G ≃ₗᵢ[ℝ] UCB G) where
  toFun g := BoundedContinuousFunction.compContinuousₗᵢ (ucb G) (ContinuousMap.mulRight g)
    (ContinuousMap.mulRight g⁻¹) (by simp) (by simp)
    (fun _ hf => compContinuous_mulRight_mem_ucb hf _)
    (fun _ hf => compContinuous_mulRight_mem_ucb hf _)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_assoc]

/-- The left translate `L_g f` is the precomposition of `f` with `x ↦ g⁻¹ * x`. -/
theorem coe_leftTranslation (g : G) (f : UCB G) :
    (leftTranslation g f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous (ContinuousMap.mulLeft g⁻¹) :=
  ucbSubalgebra.coe_leftTranslation ..

/-- The right translate `R_g f` is the precomposition of `f` with `x ↦ x * g`. -/
theorem coe_rightTranslation (g : G) (f : UCB G) :
    (rightTranslation g f : G →ᵇ ℝ) = (f : G →ᵇ ℝ).compContinuous (ContinuousMap.mulRight g) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp]
theorem leftTranslation_apply (g : G) (f : UCB G) (x : G) :
    (leftTranslation g f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) (g⁻¹ * x) :=
  DFunLike.congr_fun (coe_leftTranslation g f) x

@[simp]
theorem rightTranslation_apply (g : G) (f : UCB G) (x : G) :
    (rightTranslation g f : G →ᵇ ℝ) x = (f : G →ᵇ ℝ) (x * g) :=
  DFunLike.congr_fun (coe_rightTranslation g f) x

@[simp]
theorem leftTranslation_symm (g : G) : (leftTranslation g).symm = leftTranslation g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

@[simp]
theorem rightTranslation_symm (g : G) : (rightTranslation g).symm = rightTranslation g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- Left translation preserves and reflects the pointwise order. -/
@[simp]
theorem leftTranslation_le_leftTranslation_iff {g : G} {f f' : UCB G} :
    leftTranslation g f ≤ leftTranslation g f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (g * x)

/-- Left translation fixes the constant function `1`. -/
@[simp]
theorem leftTranslation_apply_one (g : G) : leftTranslation g 1 = 1 := by
  ext
  simp

/-- Left translation fixes every constant function. -/
@[simp]
theorem leftTranslation_apply_algebraMap (g : G) (c : ℝ) :
    leftTranslation g (algebraMap ℝ (UCB G) c) = algebraMap ℝ (UCB G) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- Right translation preserves and reflects the pointwise order. -/
@[simp]
theorem rightTranslation_le_rightTranslation_iff {g : G} {f f' : UCB G} :
    rightTranslation g f ≤ rightTranslation g f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (x * g⁻¹)

/-- Right translation fixes the constant function `1`. -/
@[simp]
theorem rightTranslation_apply_one (g : G) : rightTranslation g 1 = 1 := by
  ext
  simp

/-- Right translation fixes every constant function. -/
@[simp]
theorem rightTranslation_apply_algebraMap (g : G) (c : ℝ) :
    rightTranslation g (algebraMap ℝ (UCB G) c) = algebraMap ℝ (UCB G) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- Right translation preserves pointwise products. -/
@[simp]
theorem rightTranslation_apply_mul (g : G) (f f' : UCB G) :
    rightTranslation g (f * f') = rightTranslation g f * rightTranslation g f' := by
  ext
  simp

/-- The left translates `L_u f` of a function `f` in `UCB G` tend to `f` in supremum norm as
`u → 1`. -/
theorem tendsto_leftTranslation_apply_nhds_one (f : UCB G) :
    Tendsto (fun u : G => leftTranslation u f) (𝓝 1) (𝓝 f) := by
  simp only [tendsto_subtype_rng, coe_leftTranslation]
  exact (mem_ucb_iff_tendsto.1 f.property).comp (by simpa using tendsto_inv (1 : G))

/-- The orbit map `g ↦ L_g f` of a function `f` in `UCB G` is continuous for the supremum norm. -/
theorem continuous_leftTranslation_apply (f : UCB G) :
    Continuous fun g : G => leftTranslation g f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  -- Near `g`, write `L_h f = L_g (L_(g⁻¹ * h) f)`, where `g⁻¹ * h → 1`.
  have h₁ : Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 1) := by
    simpa using (continuous_const_mul g⁻¹).tendsto g
  have h₂ := ((leftTranslation g).continuous.tendsto f).comp
    ((tendsto_leftTranslation_apply_nhds_one f).comp h₁)
  refine h₂.congr fun h => ?_
  ext
  simp

/-- Left and right translations of `UCB G` commute. -/
theorem commute_leftTranslation_rightTranslation (g h : G) :
    Commute (leftTranslation g) (rightTranslation h) := by
  ext
  simp [mul_assoc]

/-- Left and right translations of `UCB G` commute, applied to a function. -/
theorem leftTranslation_rightTranslation (g h : G) (f : UCB G) :
    leftTranslation g (rightTranslation h f) = rightTranslation h (leftTranslation g f) :=
  congr($(commute_leftTranslation_rightTranslation g h) f)

end UCB

namespace AddUCB

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

-- Unlike `UCB.leftTranslation : G →* (UCB G ≃ₗᵢ[ℝ] UCB G)`, the codomain
-- `AddUCB A ≃ₗᵢ[ℝ] AddUCB A` is a multiplicative group under composition rather than an additive
-- group, so `leftTranslation` is defined directly on `A` rather than via `@[to_additive]`.

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

theorem leftTranslation_symm_apply (a : A) (f : AddUCB A) (x : A) :
    ((leftTranslation a).symm f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (a + x) :=
  DFunLike.congr_fun (coe_leftTranslation_symm a f) x

@[simp]
theorem leftTranslation_symm (a : A) : (leftTranslation a).symm = leftTranslation (-a) := by
  ext
  simp [leftTranslation_symm_apply]

@[simp]
theorem leftTranslation_zero : leftTranslation (0 : A) = LinearIsometryEquiv.refl ℝ (AddUCB A) := by
  ext
  simp

theorem leftTranslation_add (a b : A) :
    leftTranslation (a + b) = leftTranslation a * leftTranslation b := by
  ext
  simp [add_assoc]

theorem leftTranslation_neg (a : A) : leftTranslation (-a) = (leftTranslation a).symm :=
  (leftTranslation_symm a).symm

/-- Left translation preserves and reflects the pointwise order. -/
@[simp]
theorem leftTranslation_le_leftTranslation_iff {a : A} {f f' : AddUCB A} :
    leftTranslation a f ≤ leftTranslation a f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (a + x)

/-- Left translation fixes the constant function `1`. -/
@[simp]
theorem leftTranslation_apply_one (a : A) : leftTranslation a 1 = 1 := by
  ext
  simp

/-- Left translation fixes every constant function. -/
@[simp]
theorem leftTranslation_apply_algebraMap (a : A) (c : ℝ) :
    leftTranslation a (algebraMap ℝ (AddUCB A) c) = algebraMap ℝ (AddUCB A) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- The left translates `L_u f` of a function `f` in `AddUCB A` tend to `f` in supremum norm as
`u → 0`. -/
theorem tendsto_leftTranslation_apply_nhds_zero (f : AddUCB A) :
    Tendsto (fun u : A => leftTranslation u f) (𝓝 0) (𝓝 f) := by
  simp only [tendsto_subtype_rng, coe_leftTranslation]
  exact (mem_addUcb_iff_tendsto.1 f.property).comp (by simpa using tendsto_neg (0 : A))

/-- The orbit map `a ↦ L_a f` of a function `f` in `AddUCB A` is continuous for the supremum
norm. -/
theorem continuous_leftTranslation_apply (f : AddUCB A) :
    Continuous fun a : A => leftTranslation a f := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  -- Near `a`, write `L_b f = L_a (L_(-a + b) f)`, where `-a + b → 0`.
  have h₁ : Tendsto (fun b : A => -a + b) (𝓝 a) (𝓝 0) := by
    simpa using (continuous_const_add (-a)).tendsto a
  have h₂ := ((leftTranslation a).continuous.tendsto f).comp
    ((tendsto_leftTranslation_apply_nhds_zero f).comp h₁)
  refine h₂.congr fun b => ?_
  ext
  simp

-- As with `leftTranslation`, `AddUCB A ≃ₗᵢ[ℝ] AddUCB A` is a multiplicative group under
-- composition rather than an additive group, so `rightTranslation` is defined directly on `A`
-- rather than via `@[to_additive]`.

/-- Right translation `R_a`, where `(R_a f)(x) = f (x + a)`, as a linear isometry equivalence of
`AddUCB A`. -/
def rightTranslation (a : A) : AddUCB A ≃ₗᵢ[ℝ] AddUCB A :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUcb A)
    (ContinuousMap.addRight a) (ContinuousMap.addRight (-a)) (by simp) (by simp)
    (fun _ hf => compContinuous_addRight_mem_addUcb hf _)
    (fun _ hf => compContinuous_addRight_mem_addUcb hf _)

/-- The right translate `R_a f` is the precomposition of `f` with `x ↦ x + a`. -/
theorem coe_rightTranslation (a : A) (f : AddUCB A) :
    (rightTranslation a f : A →ᵇ ℝ) =
      (f : A →ᵇ ℝ).compContinuous (ContinuousMap.addRight a) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp]
theorem rightTranslation_apply (a : A) (f : AddUCB A) (x : A) :
    (rightTranslation a f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (x + a) :=
  DFunLike.congr_fun (coe_rightTranslation a f) x

/-- The inverse of `R_a` is precomposition with `x ↦ x + -a`. -/
theorem coe_rightTranslation_symm (a : A) (f : AddUCB A) :
    ((rightTranslation a).symm f : A →ᵇ ℝ) =
      (f : A →ᵇ ℝ).compContinuous (ContinuousMap.addRight (-a)) :=
  BoundedContinuousFunction.compContinuousₗᵢ_symm_apply ..

theorem rightTranslation_symm_apply (a : A) (f : AddUCB A) (x : A) :
    ((rightTranslation a).symm f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (x + -a) :=
  DFunLike.congr_fun (coe_rightTranslation_symm a f) x

@[simp]
theorem rightTranslation_symm (a : A) : (rightTranslation a).symm = rightTranslation (-a) := by
  ext
  simp [rightTranslation_symm_apply]

@[simp]
theorem rightTranslation_zero :
    rightTranslation (0 : A) = LinearIsometryEquiv.refl ℝ (AddUCB A) := by
  ext
  simp

/-- Right translation satisfies `R_(a + b) = R_a ∘ R_b`, with `R_b` applied to the function
first. -/
theorem rightTranslation_add (a b : A) :
    rightTranslation (a + b) = rightTranslation a * rightTranslation b := by
  ext
  simp [add_assoc]

/-- Right translation preserves and reflects the pointwise order. -/
@[simp]
theorem rightTranslation_le_rightTranslation_iff {a : A} {f f' : AddUCB A} :
    rightTranslation a f ≤ rightTranslation a f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (x + -a)

/-- Right translation fixes the constant function `1`. -/
@[simp]
theorem rightTranslation_apply_one (a : A) : rightTranslation a 1 = 1 := by
  ext
  simp

/-- Right translation fixes every constant function. -/
@[simp]
theorem rightTranslation_apply_algebraMap (a : A) (c : ℝ) :
    rightTranslation a (algebraMap ℝ (AddUCB A) c) = algebraMap ℝ (AddUCB A) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- Right translation preserves pointwise products. -/
@[simp]
theorem rightTranslation_apply_mul (a : A) (f g : AddUCB A) :
    rightTranslation a (f * g) = rightTranslation a f * rightTranslation a g := by
  ext
  simp

/-- Left and right translations of `AddUCB A` commute. -/
theorem commute_leftTranslation_rightTranslation (a b : A) :
    Commute (leftTranslation a) (rightTranslation b) := by
  ext
  simp [add_assoc]

/-- Left and right translations of `AddUCB A` commute, applied to a function. -/
theorem leftTranslation_rightTranslation (a b : A) (f : AddUCB A) :
    leftTranslation a (rightTranslation b f) = rightTranslation b (leftTranslation a f) :=
  congr($(commute_leftTranslation_rightTranslation a b) f)

/-- On a finite additive group, the sum of the left translates `L_a f` of a function `f` in
`AddUCB A` is the constant function `∑ x, f x`. -/
theorem sum_leftTranslation [Fintype A] (f : AddUCB A) :
    ∑ a, leftTranslation a f = algebraMap ℝ (AddUCB A) (∑ x, (f : A →ᵇ ℝ) x) := by
  refine ext fun x => ?_
  simp only [AddSubmonoidClass.coe_finsetSum, FunLike.coe_sum, Finset.sum_apply,
    leftTranslation_apply, SubalgebraClass.coe_algebraMap,
    BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one]
  exact Fintype.sum_equiv ((Equiv.neg A).trans (Equiv.addRight x)) _ _ fun _ => rfl

end AddUCB

namespace UCB

/-- On a finite group, the sum of the left translates `L_g f` of a function `f` in `UCB G` is the
constant function `∑ x, f x`. -/
theorem sum_leftTranslation [Fintype G] (f : UCB G) :
    ∑ g, leftTranslation g f = algebraMap ℝ (UCB G) (∑ x, (f : G →ᵇ ℝ) x) := by
  refine ext fun x => ?_
  simp only [AddSubmonoidClass.coe_finsetSum, FunLike.coe_sum, Finset.sum_apply,
    leftTranslation_apply, SubalgebraClass.coe_algebraMap,
    BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one]
  exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun _ => rfl

end UCB

end TauCeti
