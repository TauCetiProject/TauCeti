/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Algebra.Group.UCB.Translation
public import TauCeti.Topology.ContinuousMap.Ordered

import TauCeti.Topology.ContinuousMap.Compact

/-!
# Orbit pullbacks of continuous functions on compact `G`-spaces into `UCB`

Let a topological group `G` act jointly continuously on a compact topological space `X`. For every
continuous function `f : C(X, 𝕜)` and basepoint `x : X`, the orbit function `g ↦ f (g • x)` is
bounded (since `X` is compact) and uniformly continuous under small left multiplication on `G`:
because `(u * g) • x = u • (g • x)` and `g • x` stays in the compact space `X`,
`ContinuousMap.eventually_forall_dist_smul_lt` supplies a neighborhood of `1 : G` on which
`dist (f (u • y)) (f y) < ε` holds uniformly for all `y : X`.

Bundling `f ↦ (g ↦ f (g • x))` gives unital algebra homomorphisms
`TauCeti.ucbSubalgebra.orbitAlgHom` and `TauCeti.UCB.orbitAlgHom`, as well as the positive linear
map `TauCeti.UCB.orbitPositiveLinearMap`. Left translation `L_g` on `UCB G` intertwines the orbit
pullback with precomposition by `(g⁻¹ • ·)` on `C(X, ℝ)`, while right translation `R_g` shifts the
basepoint from `x` to `g • x`. Pulling a left-invariant mean back along `orbitPositiveLinearMap`
therefore produces a `G`-invariant state on `C(X, ℝ)`.

## Main definitions

* `TauCeti.ucbSubalgebra.orbitAlgHom 𝕜 G x`: the unital algebra homomorphism
  `C(X, 𝕜) →ₐ[𝕜] ucbSubalgebra 𝕜 G` sending `f` to `g ↦ f (g • x)`.
* `TauCeti.UCB.orbitAlgHom G x`: the real specialization `C(X, ℝ) →ₐ[ℝ] UCB G`.
* `TauCeti.UCB.orbitPositiveLinearMap G x`: the same map as a `PositiveLinearMap`
  `C(X, ℝ) →ₚ[ℝ] UCB G`.

## Main results

* `TauCeti.mkOfCompact_compContinuous_smul_mem_ucbSubalgebra`,
  `TauCeti.mkOfCompact_compContinuous_smul_mem_ucb`: the orbit function `g ↦ f (g • x)` lies in
  `ucbSubalgebra 𝕜 G` (respectively `ucb G`).
* `TauCeti.UCB.leftTranslation_orbitAlgHom`, `TauCeti.UCB.leftTranslation_orbitPositiveLinearMap`:
  `L_g` on `UCB G` corresponds to precomposing `f` with `Homeomorph.smul g⁻¹`.
* `TauCeti.UCB.rightTranslation_orbitAlgHom`, `TauCeti.UCB.rightTranslation_orbitPositiveLinearMap`:
  `R_g` on `UCB G` shifts the orbit basepoint from `x` to `g • x`.

## References

* N. W. Rickert, *Amenable groups and groups with the fixed point property*, Trans. Amer. Math.
  Soc. **127** (1967), 221–232, Lemma 4.1.
* V. Runde, *Lectures on Amenability*, Lecture Notes in Mathematics **1774**, Springer, 2002,
  Lemma 1.3.1.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

section Membership

variable {𝕜 G X : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]

/-- For a continuous function `f : C(X, 𝕜)` on a compact `G`-space `X` with jointly continuous
action, the orbit function `g ↦ f (g • x)` belongs to `ucbSubalgebra 𝕜 G`. -/
theorem mkOfCompact_compContinuous_smul_mem_ucbSubalgebra (f : C(X, 𝕜)) (x : X) :
    (BoundedContinuousFunction.mkOfCompact f).compContinuous
      ⟨(· • x), continuous_id.smul continuous_const⟩ ∈ ucbSubalgebra 𝕜 G := by
  rw [mem_ucbSubalgebra_iff]
  intro ε hε
  filter_upwards [f.eventually_forall_dist_smul_lt (M := G) hε] with u hu g
  simpa [dist_eq_norm, mul_smul] using hu (g • x)

/-- For a real continuous function `f : C(X, ℝ)` on a compact `G`-space `X` with jointly continuous
action, the orbit function `g ↦ f (g • x)` belongs to `ucb G`. -/
theorem mkOfCompact_compContinuous_smul_mem_ucb (f : C(X, ℝ)) (x : X) :
    (BoundedContinuousFunction.mkOfCompact f).compContinuous
      ⟨(· • x), continuous_id.smul continuous_const⟩ ∈ ucb G :=
  mkOfCompact_compContinuous_smul_mem_ucbSubalgebra f x

end Membership

namespace ucbSubalgebra

variable (𝕜 G : Type*) {X : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [TopologicalSpace X] [CompactSpace X] [MulAction G X]
  [ContinuousSMul G X]

/-- Evaluation along the orbit `g ↦ g • x` in a compact `G`-space `X`, as a unital algebra
homomorphism `C(X, 𝕜) →ₐ[𝕜] ucbSubalgebra 𝕜 G`. -/
def orbitAlgHom (x : X) : C(X, 𝕜) →ₐ[𝕜] ucbSubalgebra 𝕜 G where
  toFun f :=
    ⟨(BoundedContinuousFunction.mkOfCompact f).compContinuous
        ⟨(· • x), continuous_id.smul continuous_const⟩,
      mkOfCompact_compContinuous_smul_mem_ucbSubalgebra f x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {𝕜 G}

/-- The underlying bounded continuous function of `orbitAlgHom 𝕜 G x f` is `g ↦ f (g • x)`. -/
theorem coe_orbitAlgHom (x : X) (f : C(X, 𝕜)) :
    (orbitAlgHom 𝕜 G x f : G →ᵇ 𝕜) =
      (BoundedContinuousFunction.mkOfCompact f).compContinuous
        ⟨(· • x), continuous_id.smul continuous_const⟩ :=
  (rfl)

@[simp]
theorem orbitAlgHom_apply (x : X) (f : C(X, 𝕜)) (g : G) :
    (orbitAlgHom 𝕜 G x f : G →ᵇ 𝕜) g = f (g • x) :=
  (rfl)

/-- Left translation `L_g` on `ucbSubalgebra 𝕜 G` intertwines `orbitAlgHom` with precomposition by
`Homeomorph.smul g⁻¹` on `C(X, 𝕜)`. -/
theorem leftTranslation_orbitAlgHom (g : G) (x : X) (f : C(X, 𝕜)) :
    leftTranslation 𝕜 G g (orbitAlgHom 𝕜 G x f) =
      orbitAlgHom 𝕜 G x (f.comp (Homeomorph.smul g⁻¹ : X ≃ₜ X)) := by
  ext h
  simp [mul_smul]

end ucbSubalgebra

namespace UCB

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Evaluation along the orbit `g ↦ g • x` in a compact `G`-space `X`, as a unital algebra
homomorphism `C(X, ℝ) →ₐ[ℝ] UCB G`; the case `𝕜 = ℝ` of `ucbSubalgebra.orbitAlgHom`. -/
def orbitAlgHom (x : X) : C(X, ℝ) →ₐ[ℝ] UCB G :=
  ucbSubalgebra.orbitAlgHom ℝ G x

/-- Evaluation along the orbit `g ↦ g • x` in a compact `G`-space `X`, as a positive linear map
`C(X, ℝ) →ₚ[ℝ] UCB G`. -/
def orbitPositiveLinearMap (x : X) : C(X, ℝ) →ₚ[ℝ] UCB G where
  toLinearMap := (orbitAlgHom G x).toLinearMap
  monotone' _ _ h := le_def.2 fun g => h (g • x)

variable {G}

/-- The underlying bounded continuous function of `orbitAlgHom G x f` is `g ↦ f (g • x)`. -/
theorem coe_orbitAlgHom (x : X) (f : C(X, ℝ)) :
    (orbitAlgHom G x f : G →ᵇ ℝ) =
      (BoundedContinuousFunction.mkOfCompact f).compContinuous
        ⟨(· • x), continuous_id.smul continuous_const⟩ :=
  (rfl)

@[simp]
theorem orbitAlgHom_apply (x : X) (f : C(X, ℝ)) (g : G) :
    (orbitAlgHom G x f : G →ᵇ ℝ) g = f (g • x) :=
  (rfl)

/-- The orbit pullback preserves the pointwise order. -/
theorem monotone_orbitAlgHom (x : X) : Monotone (orbitAlgHom G x) :=
  (orbitPositiveLinearMap G x).monotone

/-- `orbitPositiveLinearMap` and `orbitAlgHom` have the same underlying function. -/
theorem coe_orbitPositiveLinearMap (x : X) :
    ⇑(orbitPositiveLinearMap G x) = ⇑(orbitAlgHom G x) :=
  (rfl)

@[simp]
theorem orbitPositiveLinearMap_apply (x : X) (f : C(X, ℝ)) (g : G) :
    (orbitPositiveLinearMap G x f : G →ᵇ ℝ) g = f (g • x) :=
  (rfl)

@[simp]
theorem orbitPositiveLinearMap_one (x : X) :
    orbitPositiveLinearMap G x 1 = 1 :=
  (orbitAlgHom G x).map_one

/-- Left translation `L_g` on `UCB G` intertwines `orbitAlgHom` with precomposition by
`Homeomorph.smul g⁻¹` on `C(X, ℝ)`. -/
theorem leftTranslation_orbitAlgHom (g : G) (x : X) (f : C(X, ℝ)) :
    leftTranslation g (orbitAlgHom G x f) =
      orbitAlgHom G x (f.comp (Homeomorph.smul g⁻¹ : X ≃ₜ X)) := by
  ext h
  simp [mul_smul]

/-- Left translation `L_g` on `UCB G` intertwines `orbitPositiveLinearMap` with precomposition by
`Homeomorph.smul g⁻¹` on `C(X, ℝ)`. -/
theorem leftTranslation_orbitPositiveLinearMap (g : G) (x : X) (f : C(X, ℝ)) :
    leftTranslation g (orbitPositiveLinearMap G x f) =
      orbitPositiveLinearMap G x (f.comp (Homeomorph.smul g⁻¹ : X ≃ₜ X)) :=
  leftTranslation_orbitAlgHom g x f

/-- Right translation `R_g` on `UCB G` shifts the basepoint of `orbitAlgHom` from `x` to `g • x`. -/
theorem rightTranslation_orbitAlgHom (g : G) (x : X) (f : C(X, ℝ)) :
    rightTranslation g (orbitAlgHom G x f) = orbitAlgHom G (g • x) f := by
  ext h
  simp [mul_smul]

/-- Right translation `R_g` on `UCB G` shifts the basepoint of `orbitPositiveLinearMap` from `x` to
`g • x`. -/
theorem rightTranslation_orbitPositiveLinearMap (g : G) (x : X) (f : C(X, ℝ)) :
    rightTranslation g (orbitPositiveLinearMap G x f) = orbitPositiveLinearMap G (g • x) f :=
  rightTranslation_orbitAlgHom g x f

end UCB

end TauCeti
