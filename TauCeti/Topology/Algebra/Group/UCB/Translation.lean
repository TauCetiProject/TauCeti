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

* `TauCeti.ucbSubalgebra.leftTranslation 𝕜 G`, `TauCeti.addUcbSubalgebra.leftTranslation 𝕜 H`:
  left translation `g ↦ L_g` on `ucbSubalgebra 𝕜 G` and `addUcbSubalgebra 𝕜 H`.
* `TauCeti.UCB.leftTranslation`, `TauCeti.AddUCB.leftTranslation`: the case `𝕜 = ℝ`, on `UCB G` and
  `AddUCB H`.
* `TauCeti.UCB.rightTranslation`, `TauCeti.AddUCB.rightTranslation`: right translation `g ↦ R_g` on
  `UCB G` and `AddUCB H`.

## Main results

* `TauCeti.compContinuous_mulLeft_mem_ucbSubalgebra`,
  `TauCeti.compContinuous_mulRight_mem_ucbSubalgebra`: `ucbSubalgebra 𝕜 G`, and in particular
  `ucb G`, is closed under left and right translation; likewise for `addUcbSubalgebra 𝕜 H` and
  `addUcb H`.
* `TauCeti.UCB.leftTranslation_le_leftTranslation_iff`,
  `TauCeti.UCB.leftTranslation_apply_algebraMap`: left translation preserves the order and the
  constant functions; likewise for right translation and for `AddUCB`.
* `TauCeti.UCB.continuous_leftTranslation_apply`,
  `TauCeti.AddUCB.continuous_leftTranslation_apply`: the orbit map `g ↦ L_g f` is continuous for the
  supremum norm.
* `TauCeti.UCB.commute_leftTranslation_rightTranslation`,
  `TauCeti.AddUCB.commute_leftTranslation_rightTranslation`: left and right translations commute.
* `TauCeti.UCB.sum_leftTranslation`, `TauCeti.AddUCB.sum_leftTranslation`: on a finite group, the
  sum of the left translates of `f` is the constant function `∑ x, f x`.

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

/-- The left translates `L_u f` of a function `f` in `UCB G` tend to `f` in supremum norm as
`u → 1`. -/
theorem tendsto_leftTranslation_apply_nhds_one (f : UCB G) :
    Tendsto (fun u : G => leftTranslation u f) (𝓝 1) (𝓝 f) := by
  simp only [tendsto_subtype_rng, coe_leftTranslation]
  exact (mem_ucb_iff_tendsto.1 f.2).comp (by simpa using tendsto_inv (1 : G))

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

section Additive

variable {H : Type*} [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

namespace addUcbSubalgebra

/-- Left translation `(L_g f)(x) = f (-g + x)` as a linear isometry equivalence of
`addUcbSubalgebra 𝕜 H`. -/
def leftTranslation (𝕜 H : Type*) [NormedField 𝕜] [AddGroup H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] (g : H) : addUcbSubalgebra 𝕜 H ≃ₗᵢ[𝕜] addUcbSubalgebra 𝕜 H :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUcbSubalgebra 𝕜 H)
    (ContinuousMap.addLeft (-g)) (ContinuousMap.addLeft g) (by simp) (by simp)
    (fun _ hf => compContinuous_addLeft_mem_addUcbSubalgebra hf _)
    (fun _ hf => compContinuous_addLeft_mem_addUcbSubalgebra hf _)

/-- The left translate `L_g f` is the precomposition of `f` with `x ↦ -g + x`. -/
theorem coe_leftTranslation (g : H) (f : addUcbSubalgebra 𝕜 H) :
    (leftTranslation 𝕜 H g f : H →ᵇ 𝕜) =
      (f : H →ᵇ 𝕜).compContinuous (ContinuousMap.addLeft (-g)) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp]
theorem leftTranslation_apply (g : H) (f : addUcbSubalgebra 𝕜 H) (x : H) :
    (leftTranslation 𝕜 H g f : H →ᵇ 𝕜) x = (f : H →ᵇ 𝕜) (-g + x) :=
  DFunLike.congr_fun (coe_leftTranslation g f) x

@[simp]
theorem leftTranslation_zero : leftTranslation 𝕜 H (0 : H) = 1 := by
  ext
  simp

theorem leftTranslation_add (g h : H) :
    leftTranslation 𝕜 H (g + h) = leftTranslation 𝕜 H g * leftTranslation 𝕜 H h := by
  ext
  simp [add_assoc]

end addUcbSubalgebra

namespace AddUCB

/-- Left translation `(L_g f)(x) = f (-g + x)` as a linear isometry equivalence of `AddUCB H`; the
case `𝕜 = ℝ` of `addUcbSubalgebra.leftTranslation`. -/
def leftTranslation (g : H) : AddUCB H ≃ₗᵢ[ℝ] AddUCB H :=
  addUcbSubalgebra.leftTranslation ℝ H g

/-- Right translation `(R_g f)(x) = f (x + g)` as a linear isometry equivalence of `AddUCB H`. -/
def rightTranslation (g : H) : AddUCB H ≃ₗᵢ[ℝ] AddUCB H :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUcb H) (ContinuousMap.addRight g)
    (ContinuousMap.addRight (-g)) (by simp) (by simp)
    (fun _ hf => compContinuous_addRight_mem_addUcb hf _)
    (fun _ hf => compContinuous_addRight_mem_addUcb hf _)

/-- The left translate `L_g f` is the precomposition of `f` with `x ↦ -g + x`. -/
theorem coe_leftTranslation (g : H) (f : AddUCB H) :
    (leftTranslation g f : H →ᵇ ℝ) = (f : H →ᵇ ℝ).compContinuous (ContinuousMap.addLeft (-g)) :=
  addUcbSubalgebra.coe_leftTranslation ..

/-- The right translate `R_g f` is the precomposition of `f` with `x ↦ x + g`. -/
theorem coe_rightTranslation (g : H) (f : AddUCB H) :
    (rightTranslation g f : H →ᵇ ℝ) = (f : H →ᵇ ℝ).compContinuous (ContinuousMap.addRight g) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

@[simp]
theorem leftTranslation_apply (g : H) (f : AddUCB H) (x : H) :
    (leftTranslation g f : H →ᵇ ℝ) x = (f : H →ᵇ ℝ) (-g + x) :=
  DFunLike.congr_fun (coe_leftTranslation g f) x

@[simp]
theorem rightTranslation_apply (g : H) (f : AddUCB H) (x : H) :
    (rightTranslation g f : H →ᵇ ℝ) x = (f : H →ᵇ ℝ) (x + g) :=
  DFunLike.congr_fun (coe_rightTranslation g f) x

@[simp]
theorem leftTranslation_zero : leftTranslation (0 : H) = 1 :=
  addUcbSubalgebra.leftTranslation_zero

theorem leftTranslation_add (g h : H) :
    leftTranslation (g + h) = leftTranslation g * leftTranslation h :=
  addUcbSubalgebra.leftTranslation_add g h

@[simp]
theorem leftTranslation_symm (g : H) : (leftTranslation g).symm = leftTranslation (-g) :=
  LinearIsometryEquiv.ext fun _ => (leftTranslation g).symm_apply_eq.2 (by ext; simp)

theorem leftTranslation_neg (g : H) : leftTranslation (-g) = (leftTranslation g)⁻¹ := by
  rw [LinearIsometryEquiv.inv_def, leftTranslation_symm]

@[simp]
theorem rightTranslation_zero : rightTranslation (0 : H) = 1 := by
  ext
  simp

theorem rightTranslation_add (g h : H) :
    rightTranslation (g + h) = rightTranslation g * rightTranslation h := by
  ext
  simp [add_assoc]

@[simp]
theorem rightTranslation_symm (g : H) : (rightTranslation g).symm = rightTranslation (-g) :=
  LinearIsometryEquiv.ext fun _ => (rightTranslation g).symm_apply_eq.2 (by ext; simp)

theorem rightTranslation_neg (g : H) : rightTranslation (-g) = (rightTranslation g)⁻¹ := by
  rw [LinearIsometryEquiv.inv_def, rightTranslation_symm]

/-- Left translation preserves and reflects the pointwise order. -/
@[simp]
theorem leftTranslation_le_leftTranslation_iff {g : H} {f f' : AddUCB H} :
    leftTranslation g f ≤ leftTranslation g f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (g + x)

/-- Left translation fixes the constant function `1`. -/
@[simp]
theorem leftTranslation_apply_one (g : H) : leftTranslation g 1 = 1 := by
  ext
  simp

/-- Left translation fixes every constant function. -/
@[simp]
theorem leftTranslation_apply_algebraMap (g : H) (c : ℝ) :
    leftTranslation g (algebraMap ℝ (AddUCB H) c) = algebraMap ℝ (AddUCB H) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- Right translation preserves and reflects the pointwise order. -/
@[simp]
theorem rightTranslation_le_rightTranslation_iff {g : H} {f f' : AddUCB H} :
    rightTranslation g f ≤ rightTranslation g f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (x + -g)

/-- Right translation fixes the constant function `1`. -/
@[simp]
theorem rightTranslation_apply_one (g : H) : rightTranslation g 1 = 1 := by
  ext
  simp

/-- Right translation fixes every constant function. -/
@[simp]
theorem rightTranslation_apply_algebraMap (g : H) (c : ℝ) :
    rightTranslation g (algebraMap ℝ (AddUCB H) c) = algebraMap ℝ (AddUCB H) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- The left translates `L_u f` of a function `f` in `AddUCB H` tend to `f` in supremum norm as
`u → 0`. -/
theorem tendsto_leftTranslation_apply_nhds_zero (f : AddUCB H) :
    Tendsto (fun u : H => leftTranslation u f) (𝓝 0) (𝓝 f) := by
  simp only [tendsto_subtype_rng, coe_leftTranslation]
  exact (mem_addUcb_iff_tendsto.1 f.2).comp (by simpa using tendsto_neg (0 : H))

/-- The orbit map `g ↦ L_g f` of a function `f` in `AddUCB H` is continuous for the supremum
norm. -/
theorem continuous_leftTranslation_apply (f : AddUCB H) :
    Continuous fun g : H => leftTranslation g f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have h₁ : Tendsto (fun h : H => -g + h) (𝓝 g) (𝓝 0) := by
    simpa using (continuous_const_add (-g)).tendsto g
  have h₂ := ((leftTranslation g).continuous.tendsto f).comp
    ((tendsto_leftTranslation_apply_nhds_zero f).comp h₁)
  refine h₂.congr fun h => ?_
  ext
  simp [← add_assoc]

/-- Left and right translations of `AddUCB H` commute. -/
theorem commute_leftTranslation_rightTranslation (g h : H) :
    Commute (leftTranslation g) (rightTranslation h) := by
  ext
  simp [add_assoc]

/-- Left and right translations of `AddUCB H` commute, applied to a function. -/
theorem leftTranslation_rightTranslation (g h : H) (f : AddUCB H) :
    leftTranslation g (rightTranslation h f) = rightTranslation h (leftTranslation g f) :=
  congr($(commute_leftTranslation_rightTranslation g h) f)

/-- On a finite additive group, the sum of the left translates `L_g f` of a function `f` in
`AddUCB H` is the constant function `∑ x, f x`. -/
theorem sum_leftTranslation [Fintype H] (f : AddUCB H) :
    ∑ g, leftTranslation g f = algebraMap ℝ (AddUCB H) (∑ x, (f : H →ᵇ ℝ) x) := by
  refine ext fun x => ?_
  simp only [AddSubmonoidClass.coe_finsetSum, FunLike.coe_sum, Finset.sum_apply,
    leftTranslation_apply, SubalgebraClass.coe_algebraMap,
    BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one]
  exact Fintype.sum_equiv ((Equiv.neg H).trans (Equiv.addRight x)) _ _ fun _ => rfl

end AddUCB

end Additive

end TauCeti
