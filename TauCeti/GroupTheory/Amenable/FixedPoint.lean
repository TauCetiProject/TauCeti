/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.Analysis.LocallyConvex.Barycenter
public import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
public import TauCeti.GroupTheory.Amenable.WeakStar
public import TauCeti.Topology.Algebra.Group.UCB.Orbit

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The Day–Rickert affine fixed-point characterization of amenable topological groups

A topological group `G` is amenable—meaning `TauCeti.UCB G` carries a left-invariant mean—if and
only if every jointly continuous affine action of `G` on a nonempty compact convex subset `K` of a
Hausdorff locally convex real topological vector space `E` has a fixed point. Neither local
compactness nor separation is needed on `G`, and the ambient real space `E` is completely
universe-polymorphic (`E : Type v` in the forward direction, and `E : Type (max u v)` for arbitrary
`v` in the equivalence).

Both implications connect `TauCeti.Mean G` to `TauCeti.barycenter`:

* **Averaging by a mean (`Amenable G →` fixed point).** Suppose `G` acts jointly continuously on a
  nonempty compact convex set `K ⊆ E` preserving binary convex combinations. For any `x₀ : K` and
  `m : Mean G`, pulling `m` back along `TauCeti.UCB.orbitPositiveLinearMap G x₀` gives a normalized
  positive functional `m.pullbackOrbit x₀` on `C(K, ℝ)`, whose Choquet–Rudin barycenter
  `m.orbitBarycenter K hK x₀` lies in `K`. When `m` is left invariant, `m.pullbackOrbit x₀` is
  invariant under precomposition with `g • ·`, so affine covariance of `TauCeti.barycenter` shows
  that `m.orbitBarycenter K hK x₀` is fixed by every `g : G`.
* **Action on the compact convex space of means (fixed point `→ Amenable G`).** Left translation
  induces a left action `(g • m) f = m (L_{g⁻¹} f)` on `Mean G` and a weak-* continuous linear
  action `TauCeti.UCB.leftTranslationWeakDual` on `WeakDual ℝ (UCB G)` whose fixed points in
  `Mean G` are the left-invariant means. Although evaluation `(φ, f) ↦ φ f` is not jointly
  continuous on `(UCB G)* × UCB G`, every mean is `1`-Lipschitz (`|m f₁ - m f₂| ≤ ‖f₁ - f₂‖`
  uniformly in `m`) and every `f : UCB G` has a norm-continuous translation orbit
  `g ↦ L_{g⁻¹} f`, so the triangle inequality makes `(g, m) ↦ g • m` jointly continuous on
  `G × Mean G`. Embedding `Mean G` as constant functions in `PUnit.{v + 1} → WeakDual ℝ (UCB G)`
  yields a fixed point in `Type (max u v)`, hence a left-invariant mean on `UCB G`.

## Main definitions

* `TauCeti.UCB.leftTranslationWeakDual`: the contragredient group action
  `G →* (WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G))` sending `g` to `φ ↦ (f ↦ φ (L_{g⁻¹} f))`.
* `TauCeti.Mean.instMulAction`, `TauCeti.Mean.instContinuousSMul`: the jointly continuous left
  action `(g • m) f = m (L_{g⁻¹} f)` of `G` on `Mean G`.
* `TauCeti.Mean.pullbackOrbit m x`: the normalized positive linear functional on `C(X, ℝ)` obtained
  by averaging along the orbit `g ↦ g • x` of a compact `G`-space `X`.
* `TauCeti.Mean.orbitBarycenter m K hK x`: the Choquet–Rudin barycenter in `K` of
  `m.pullbackOrbit x`.

## Main results

* `TauCeti.Mean.mem_fixedPoints_iff`: a mean is fixed by the `G`-action if and only if it is left
  invariant.
* `TauCeti.Mean.IsLeftInvariant.smul_orbitBarycenter`: the orbit barycenter of a left-invariant
  mean is fixed by every `g : G`.
* `TauCeti.Amenable.exists_fixedPoint_subtype`, `TauCeti.Amenable.exists_fixedPoint_of_convex`,
  `TauCeti.Amenable.exists_fixedPoint_affineMap`, `TauCeti.Amenable.exists_fixedPoint_affineEquiv`:
  forward Day–Rickert fixed-point theorems in arbitrary universe `Type v`.
* `TauCeti.Amenable.of_forall_exists_fixedPoint_affineEquiv`,
  `TauCeti.Amenable.of_forall_exists_fixedPoint_affineMap`,
  `TauCeti.Amenable.of_forall_exists_fixedPoint_subtype`: converse from fixed points in
  `Type (max u v)`.
* `TauCeti.amenable_iff_forall_exists_fixedPoint_affineMap`,
  `TauCeti.amenable_iff_forall_exists_fixedPoint_affineEquiv`,
  `TauCeti.amenable_iff_forall_exists_fixedPoint_subtype`: universe-polymorphic Day–Rickert
  fixed-point characterizations of `Amenable G`.

## References

* M. M. Day, *Fixed-point theorems for compact convex sets*, Illinois J. Math. **5** (1961),
  585–590.
* N. W. Rickert, *Amenable groups and groups with the fixed point property*, Trans. Amer. Math.
  Soc. **127** (1967), 221–232, Theorem 4.2.
* V. Runde, *Lectures on Amenability*, Lecture Notes in Mathematics **1774**, Springer, 2002,
  Theorem 1.3.2.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

universe u v

namespace UCB

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Auxiliary weak-* continuous linear map precomposing functionals in `WeakDual ℝ (UCB G)` with
`leftTranslation g⁻¹`. -/
private def leftTranslationWeakDualCLM (g : G) : WeakDual ℝ (UCB G) →L[ℝ] WeakDual ℝ (UCB G) where
  toFun φ := StrongDual.toWeakDual
    ((WeakDual.toStrongDual φ).comp
      (leftTranslation g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' _ _ := DFunLike.ext _ _ fun _ => by simp
  map_smul' _ _ := DFunLike.ext _ _ fun _ => by simp
  cont := WeakDual.continuous_of_continuous_eval fun f =>
    WeakDual.eval_continuous (leftTranslation g⁻¹ f)

@[simp]
private theorem leftTranslationWeakDualCLM_apply (g : G) (φ : WeakDual ℝ (UCB G)) (f : UCB G) :
    leftTranslationWeakDualCLM g φ f = φ (leftTranslation g⁻¹ f) :=
  (rfl)

/-- Contragredient left action of `G` on `WeakDual ℝ (UCB G)`, sending `g` to the weak-* continuous
linear equivalence `φ ↦ (f ↦ φ (L_{g⁻¹} f))`. -/
def leftTranslationWeakDual : G →* (WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G)) where
  toFun g := ContinuousLinearEquiv.equivOfInverse
    (leftTranslationWeakDualCLM g) (leftTranslationWeakDualCLM g⁻¹)
    (fun φ => DFunLike.ext _ _ fun f => by
      rw [leftTranslationWeakDualCLM_apply, leftTranslationWeakDualCLM_apply]
      exact congrArg φ (by ext x; rw [leftTranslation_apply, leftTranslation_apply]; simp))
    (fun φ => DFunLike.ext _ _ fun f => by
      rw [leftTranslationWeakDualCLM_apply, leftTranslationWeakDualCLM_apply]
      exact congrArg φ (by ext x; rw [leftTranslation_apply, leftTranslation_apply]; simp))
  map_one' := by
    ext φ
    rw [ContinuousLinearEquiv.equivOfInverse_apply,
      ← ContinuousLinearEquiv.coe_coe (1 : WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G)),
      ContinuousLinearEquiv.toContinuousLinearMap_one, one_apply_eq_self]
    exact DFunLike.ext _ _ fun f => by
      rw [leftTranslationWeakDualCLM_apply]
      exact congrArg φ (by ext x; simp)
  map_mul' g h := by
    ext φ
    rw [ContinuousLinearEquiv.equivOfInverse_apply,
      ← ContinuousLinearEquiv.coe_coe (_ * _ : WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G)),
      ContinuousLinearEquiv.toContinuousLinearMap_mul, mul_apply_eq_comp]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.equivOfInverse_apply]
    exact DFunLike.ext _ _ fun f => by
      rw [leftTranslationWeakDualCLM_apply, leftTranslationWeakDualCLM_apply,
        leftTranslationWeakDualCLM_apply]
      exact congrArg φ (by ext x; simp)

@[simp]
theorem leftTranslationWeakDual_apply (g : G) (φ : WeakDual ℝ (UCB G)) (f : UCB G) :
    leftTranslationWeakDual g φ f = φ (leftTranslation g⁻¹ f) :=
  (rfl)

/-- The inverse of `leftTranslationWeakDual g` is `leftTranslationWeakDual g⁻¹`. -/
theorem leftTranslationWeakDual_symm (g : G) :
    (leftTranslationWeakDual g).symm = leftTranslationWeakDual g⁻¹ := by
  ext φ
  exact DFunLike.ext _ _ fun f => rfl

end UCB

namespace Mean

section Action

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Left action of `G` on `Mean G` dual to left translation: `(g • m) f = m (L_{g⁻¹} f)`. -/
instance instSMul : SMul G (Mean G) where
  smul g m := mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.leftTranslation g⁻¹).toLinearMap)
    (fun f hf => map_nonneg m <| by
      have h := (UCB.leftTranslation_le_leftTranslation_iff (g := g⁻¹) (f := 0) (f' := f)).2 hf
      rwa [map_zero] at h)
    (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        UCB.leftTranslation_apply_one]
      exact m.map_one)

@[simp]
theorem smul_apply (g : G) (m : Mean G) (f : UCB G) :
    (g • m) f = m (UCB.leftTranslation g⁻¹ f) :=
  mk₀_apply _ _ _ f

/-- Multiplicative left action of `G` on `Mean G` dual to left translation on `UCB G`. -/
instance instMulAction : MulAction G (Mean G) where
  one_smul m := ext fun f => by
    rw [smul_apply]
    exact congrArg m (by ext x; simp)
  mul_smul g h m := ext fun f => by
    rw [smul_apply, smul_apply, smul_apply]
    exact congrArg m (by ext x; simp)

/-- Left action of `g : G` on the point-evaluation mean `eval G x` shifts the basepoint to
`g * x`. -/
@[simp]
theorem smul_eval (g x : G) : g • eval G x = eval G (g * x) :=
  ext fun f => by rw [smul_apply, eval_apply, eval_apply, UCB.leftTranslation_apply, inv_inv]

/-- A mean is fixed by the left `G`-action on `Mean G` if and only if it is left invariant. -/
theorem mem_fixedPoints_iff {m : Mean G} :
    m ∈ MulAction.fixedPoints G (Mean G) ↔ m.IsLeftInvariant := by
  rw [MulAction.mem_fixedPoints, isLeftInvariant_iff]
  refine ⟨fun h g f => ?_, fun h g => ext fun f => by rw [smul_apply, h g⁻¹ f]⟩
  have hg := DFunLike.congr_fun (h g⁻¹) f
  rwa [smul_apply, inv_inv] at hg

/-- The left action of `G` on `Mean G` is jointly continuous for the weak-* topology on `Mean G`. -/
instance instContinuousSMul : ContinuousSMul G (Mean G) where
  continuous_smul := by
    -- Every mean is `1`-Lipschitz and `g ↦ L_{g⁻¹} f` is norm-continuous for each `f : UCB G`.
    refine continuous_iff_continuousAt.2 fun ⟨g₀, m₀⟩ => ?_
    rw [ContinuousAt, tendsto_iff_forall_apply_tendsto]
    intro f
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound (p : G × Mean G) :
        ‖(p.1 • p.2) f - (g₀ • m₀) f‖ ≤
          ‖UCB.leftTranslation p.1⁻¹ f - UCB.leftTranslation g₀⁻¹ f‖ +
            ‖p.2 (UCB.leftTranslation g₀⁻¹ f) - m₀ (UCB.leftTranslation g₀⁻¹ f)‖ := by
      simp only [Real.norm_eq_abs, smul_apply]
      calc |p.2 (UCB.leftTranslation p.1⁻¹ f) - m₀ (UCB.leftTranslation g₀⁻¹ f)|
          = |(p.2 (UCB.leftTranslation p.1⁻¹ f) - p.2 (UCB.leftTranslation g₀⁻¹ f)) +
              (p.2 (UCB.leftTranslation g₀⁻¹ f) - m₀ (UCB.leftTranslation g₀⁻¹ f))| := by ring_nf
        _ ≤ |p.2 (UCB.leftTranslation p.1⁻¹ f) - p.2 (UCB.leftTranslation g₀⁻¹ f)| +
              |p.2 (UCB.leftTranslation g₀⁻¹ f) - m₀ (UCB.leftTranslation g₀⁻¹ f)| :=
            abs_add_le _ _
        _ ≤ ‖UCB.leftTranslation p.1⁻¹ f - UCB.leftTranslation g₀⁻¹ f‖ +
              |p.2 (UCB.leftTranslation g₀⁻¹ f) - m₀ (UCB.leftTranslation g₀⁻¹ f)| := by
            gcongr
            exact p.2.abs_apply_sub_apply_le _ _
    have h₁ : Tendsto
        (fun p : G × Mean G => ‖UCB.leftTranslation p.1⁻¹ f - UCB.leftTranslation g₀⁻¹ f‖)
        (𝓝 (g₀, m₀)) (𝓝 0) := by
      have hc : Continuous fun p : G × Mean G => UCB.leftTranslation p.1⁻¹ f :=
        (UCB.continuous_leftTranslation_apply f).comp (continuous_inv.comp continuous_fst)
      exact tendsto_iff_norm_sub_tendsto_zero.1 hc.continuousAt
    have h₂ : Tendsto
        (fun p : G × Mean G => ‖p.2 (UCB.leftTranslation g₀⁻¹ f) - m₀ (UCB.leftTranslation g₀⁻¹ f)‖)
        (𝓝 (g₀, m₀)) (𝓝 0) := by
      have hc : Continuous fun p : G × Mean G => p.2 (UCB.leftTranslation g₀⁻¹ f) :=
        (continuous_eval_const _).comp continuous_snd
      exact tendsto_iff_norm_sub_tendsto_zero.1 hc.continuousAt
    exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using h₁.add h₂)

/-- `Mean.toWeakDual` intertwines the left `G`-action on `Mean G` with
`UCB.leftTranslationWeakDual`. -/
@[simp]
theorem toWeakDual_smul (g : G) (m : Mean G) :
    (g • m).toWeakDual = UCB.leftTranslationWeakDual g m.toWeakDual :=
  DFunLike.ext _ _ fun f => by rw [toWeakDual_apply, smul_apply,
    UCB.leftTranslationWeakDual_apply, toWeakDual_apply]

/-- The range of `Mean.toWeakDual` in `WeakDual ℝ (UCB G)` is invariant under
`UCB.leftTranslationWeakDual`. -/
theorem mapsTo_leftTranslationWeakDual_range_toWeakDual (g : G) :
    MapsTo (UCB.leftTranslationWeakDual g)
      (Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)))
      (Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G))) := by
  rintro _ ⟨m, rfl⟩
  exact ⟨g • m, toWeakDual_smul g m⟩

/-- The means on `UCB G` form a convex subset of `WeakDual ℝ (UCB G)`. -/
theorem convex_range_toWeakDual :
    Convex ℝ (Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G))) := by
  have h : Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) =
      StrongDual.toWeakDual '' Set.range (toContinuousLinearMap : Mean G → UCB G →L[ℝ] ℝ) := by
    ext φ
    simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    refine exists_congr fun m => ⟨fun hm => WeakDual.toStrongDual.injective ?_,
      fun hm => WeakDual.toStrongDual.injective ?_⟩ <;>
      rw [← hm, toStrongDual_toWeakDual, StrongDual.toStrongDual_toWeakDual]
  rw [h]
  exact convex_range_toContinuousLinearMap.linear_image StrongDual.toWeakDual.toLinearMap

/-- The range of `Mean.toWeakDual` in `WeakDual ℝ (UCB G)` is nonempty. -/
theorem range_toWeakDual_nonempty :
    (Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G))).Nonempty :=
  range_nonempty toWeakDual

/-- `UCB.leftTranslationWeakDual` restricts to a jointly continuous map on
`G × Set.range Mean.toWeakDual`. -/
theorem continuous_leftTranslationWeakDual_range_toWeakDual :
    Continuous fun p : G × Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) =>
      UCB.leftTranslationWeakDual p.1 (p.2 : WeakDual ℝ (UCB G)) := by
  let e : Mean G ≃ₜ Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) :=
    isEmbedding_toWeakDual.toHomeomorph
  have heq : (fun p : G × Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) =>
      UCB.leftTranslationWeakDual p.1 (p.2 : WeakDual ℝ (UCB G))) =
      fun p => (p.1 • e.symm p.2).toWeakDual := by
    ext p
    have hp : (e.symm p.2).toWeakDual = (p.2 : WeakDual ℝ (UCB G)) :=
      congrArg Subtype.val (e.apply_symm_apply p.2)
    rw [toWeakDual_smul, hp]
  rw [heq]
  exact continuous_toWeakDual.comp (continuous_fst.smul (e.symm.continuous.comp continuous_snd))

end Action

section OrbitBarycenter

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section CompactSpace

variable {X : Type v} [TopologicalSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Pullback of a mean `m : Mean G` along the orbit map `g ↦ g • x` in a compact `G`-space `X`, as
a positive linear functional on `C(X, ℝ)`. -/
def pullbackOrbit (m : Mean G) (x : X) : C(X, ℝ) →ₚ[ℝ] ℝ :=
  m.toPositiveLinearMap.comp (UCB.orbitPositiveLinearMap G x)

@[simp]
theorem pullbackOrbit_apply (m : Mean G) (x : X) (f : C(X, ℝ)) :
    m.pullbackOrbit x f = m (UCB.orbitPositiveLinearMap G x f) :=
  (rfl)

/-- `m.pullbackOrbit x` is normalized (`m.pullbackOrbit x 1 = 1`). -/
theorem pullbackOrbit_one (m : Mean G) (x : X) : m.pullbackOrbit x 1 = 1 := by
  simp

/-- Pulling back the point-evaluation mean `eval G g` along the orbit of `x` evaluates at `g • x`.
-/
theorem eval_pullbackOrbit (g : G) (x : X) (f : C(X, ℝ)) :
    (eval G g).pullbackOrbit x f = f (g • x) := by
  simp

/-- Pulling back a left-invariant mean along an orbit produces a functional on `C(X, ℝ)` invariant
under precomposition with `Homeomorph.smul g`. -/
theorem IsLeftInvariant.pullbackOrbit_comp_smul {m : Mean G} (hm : m.IsLeftInvariant) (g : G)
    (x : X) (f : C(X, ℝ)) :
    m.pullbackOrbit x (f.comp (Homeomorph.smul g : X ≃ₜ X)) = m.pullbackOrbit x f := by
  have htr := UCB.leftTranslation_orbitPositiveLinearMap g⁻¹ x f
  simp only [inv_inv] at htr
  rw [pullbackOrbit_apply, pullbackOrbit_apply, ← htr, hm.apply_leftTranslation]

end CompactSpace

section Barycenter

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The Choquet–Rudin barycenter in `K` of the functional `m.pullbackOrbit x` obtained by averaging
along the orbit `g ↦ g • x` of `x : K` under a mean `m : Mean G`. -/
def orbitBarycenter (m : Mean G) (K : Set E) [MulAction G K] [ContinuousSMul G K]
    (hK : IsCompact K) (x : K) : E :=
  letI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  barycenter K (m.pullbackOrbit x)

/-- On a compact space `K`, `m.orbitBarycenter K hK x` is `barycenter K (m.pullbackOrbit x)`. -/
theorem orbitBarycenter_eq_barycenter (m : Mean G) {K : Set E} [CompactSpace K] [MulAction G K]
    [ContinuousSMul G K] (hK : IsCompact K) (x : K) :
    m.orbitBarycenter K hK x = barycenter K (m.pullbackOrbit x) :=
  (rfl)

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- The orbit barycenter `m.orbitBarycenter K hK x` lies in `K` whenever `K` is compact and convex.
-/
theorem orbitBarycenter_mem (m : Mean G) {K : Set E} [MulAction G K] [ContinuousSMul G K]
    (hK : IsCompact K) (hKc : Convex ℝ K) (x : K) :
    m.orbitBarycenter K hK x ∈ K := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact barycenter_mem hK hKc (m.pullbackOrbit x) (m.pullbackOrbit_one x)

/-- Every continuous linear functional `ℓ : StrongDual ℝ E` evaluates at `m.orbitBarycenter K hK x`
to the mean `m` applied to the orbit function `g ↦ ℓ (g • x)`. -/
theorem strongDual_orbitBarycenter (m : Mean G) {K : Set E} [CompactSpace K] [MulAction G K]
    [ContinuousSMul G K] (hK : IsCompact K) (hKc : Convex ℝ K) (x : K) (ℓ : StrongDual ℝ E) :
    ℓ (m.orbitBarycenter K hK x) =
      m (UCB.orbitPositiveLinearMap G x ((ℓ : C(E, ℝ)).restrict K)) :=
  strongDual_barycenter hK hKc (m.pullbackOrbit x) (m.pullbackOrbit_one x) ℓ

/-- If `m` is a left-invariant mean and the `G`-action on `K` preserves binary convex combinations
in `E`, then `m.orbitBarycenter K hK x` is fixed by every `g : G`. -/
theorem IsLeftInvariant.smul_orbitBarycenter {m : Mean G} (hm : m.IsLeftInvariant) {K : Set E}
    [MulAction G K] [ContinuousSMul G K] (hK : IsCompact K) (hKc : Convex ℝ K)
    (hcomb : ∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      ((g • (⟨a • (y : E) + b • (z : E), hKc y.2 z.2 ha hb hab⟩ : K) : K) : E) =
        a • ((g • y : K) : E) + b • ((g • z : K) : E))
    (g : G) (x : K) :
    ((g • (⟨m.orbitBarycenter K hK x, m.orbitBarycenter_mem hK hKc x⟩ : K) : K) : E) =
      m.orbitBarycenter K hK x := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hcov := map_barycenter hK hKc (m.pullbackOrbit x) (m.pullbackOrbit_one x)
    (T := ((Homeomorph.smul g : K ≃ₜ K) : C(K, K)))
    (fun y z a b ha hb hab => hcomb g y z a b ha hb hab)
  have hcongr := barycenter_congr (K := K)
    (φ := (PositiveLinearMap.ofClass (m.pullbackOrbit x)).comp
      (ContinuousMap.compPositiveLinearMap ℝ ℝ ((Homeomorph.smul g : K ≃ₜ K) : C(K, K))))
    (ψ := m.pullbackOrbit x) fun f => by
      simpa [PositiveLinearMap.ofClass] using hm.pullbackOrbit_comp_smul g x f
  simpa [orbitBarycenter_eq_barycenter] using hcov.trans hcongr

end Barycenter

end OrbitBarycenter

end Mean

/-! ### The Day–Rickert fixed-point theorem and characterizations of amenability -/

section FixedPoint

/-- Equip an invariant subset `K ⊆ E` with the `MulAction G K` induced by `π : G →* (E →ᵃ[ℝ] E)` and
deduce a `π`-fixed point in `K` from a subtype fixed-point principle. -/
private theorem exists_fixedPoint_affineMap_of_subtype {G : Type u} [Monoid G] [TopologicalSpace G]
    {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {K : Set E} (hKc : Convex ℝ K)
    (π : G →* (E →ᵃ[ℝ] E)) (hmaps : ∀ g : G, MapsTo (π g) K K)
    (hcont : Continuous fun p : G × K => π p.1 (p.2 : E))
    (hfp : ∀ [MulAction G K] [ContinuousSMul G K],
      (∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        ((g • (⟨a • (y : E) + b • (z : E), hKc y.2 z.2 ha hb hab⟩ : K) : K) : E) =
          a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
      ∃ x : K, ∀ g : G, g • x = x) :
    ∃ x ∈ K, ∀ g : G, π g x = x := by
  let _ : SMul G K := ⟨fun g x => ⟨π g x, hmaps g x.2⟩⟩
  have hcoe (g : G) (x : K) : ((g • x : K) : E) = π g x := rfl
  let _ : MulAction G K :=
    { one_smul x := Subtype.ext (by simp [hcoe, map_one])
      mul_smul g h x := Subtype.ext (by simp [hcoe, map_mul]) }
  have : ContinuousSMul G K := ⟨hcont.subtype_mk fun p => hmaps p.1 p.2.2⟩
  obtain ⟨x, hx⟩ := hfp fun g y z a b _ _ hab => by
    have ha' : a = 1 - b := eq_sub_of_add_eq hab
    rw [hcoe, hcoe, hcoe, Subtype.coe_mk, ha', ← AffineMap.lineMap_apply_module,
      (π g).apply_lineMap, AffineMap.lineMap_apply_module]
  exact ⟨x, x.2, fun g => congrArg Subtype.val (hx g)⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Day–Rickert fixed-point theorem** (intrinsic action on `K`). If an amenable topological group
`G` acts jointly continuously on a nonempty compact convex subset `K` of a Hausdorff locally convex
real space `E` preserving binary convex combinations in `E`, then `K` has a `G`-fixed point. -/
theorem Amenable.exists_fixedPoint_subtype [Amenable G] {E : Type v} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {K : Set E} [MulAction G K] [ContinuousSMul G K] (hKne : K.Nonempty)
    (hK : IsCompact K) (hKc : Convex ℝ K)
    (hcomb : ∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      ((g • (⟨a • (y : E) + b • (z : E), hKc y.2 z.2 ha hb hab⟩ : K) : K) : E) =
        a • ((g • y : K) : E) + b • ((g • z : K) : E)) :
    ∃ x : K, ∀ g : G, g • x = x := by
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  obtain ⟨x₀, hx₀⟩ := hKne
  refine ⟨⟨m.orbitBarycenter K hK ⟨x₀, hx₀⟩, m.orbitBarycenter_mem hK hKc ⟨x₀, hx₀⟩⟩,
    fun g => Subtype.ext (hm.smul_orbitBarycenter hK hKc hcomb g ⟨x₀, hx₀⟩)⟩

/-- **Day–Rickert fixed-point theorem** (ambient `MulAction` preserving convex combinations on
`K`). If `G` is amenable and acts on `E` leaving a nonempty compact convex subset `K` invariant,
jointly continuously on `G × K` and preserving binary convex combinations on `K`, then `K` contains
a `G`-fixed point. -/
theorem Amenable.exists_fixedPoint_of_convex [Amenable G] {E : Type v} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [MulAction G E] {K : Set E} (hKne : K.Nonempty)
    (hK : IsCompact K) (hKc : Convex ℝ K) (hmaps : ∀ g : G, MapsTo (g • ·) K K)
    (hcont : Continuous fun p : G × K => p.1 • (p.2 : E))
    (hcomb : ∀ (g : G) {y : E}, y ∈ K → ∀ {z : E}, z ∈ K → ∀ {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 → g • (a • y + b • z) = a • (g • y) + b • (g • z)) :
    ∃ x ∈ K, ∀ g : G, g • x = x := by
  let _ : SMul G K := ⟨fun g x => ⟨g • (x : E), hmaps g x.2⟩⟩
  have hcoe (g : G) (x : K) : ((g • x : K) : E) = g • (x : E) := rfl
  let _ : MulAction G K :=
    { one_smul x := Subtype.ext (by simp [hcoe])
      mul_smul g h x := Subtype.ext (by simp [hcoe, mul_smul]) }
  have : ContinuousSMul G K := ⟨hcont.subtype_mk fun p => hmaps p.1 p.2.2⟩
  obtain ⟨x, hx⟩ := Amenable.exists_fixedPoint_subtype (G := G) hKne hK hKc
    fun g y z a b ha hb hab => hcomb g y.2 z.2 ha hb hab
  exact ⟨x, x.2, fun g => congrArg Subtype.val (hx g)⟩

/-- **Day–Rickert fixed-point theorem** (monoid homomorphism into `E →ᵃ[ℝ] E`). Every jointly
continuous affine action of an amenable topological group `G` on a nonempty compact convex subset
`K` of a Hausdorff locally convex real space `E` has a fixed point in `K`. -/
theorem Amenable.exists_fixedPoint_affineMap [Amenable G] {E : Type v} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hKne : K.Nonempty) (hK : IsCompact K)
    (hKc : Convex ℝ K) (π : G →* (E →ᵃ[ℝ] E)) (hmaps : ∀ g : G, MapsTo (π g) K K)
    (hcont : Continuous fun p : G × K => π p.1 (p.2 : E)) :
    ∃ x ∈ K, ∀ g : G, π g x = x :=
  exists_fixedPoint_affineMap_of_subtype hKc π hmaps hcont fun hcomb =>
    Amenable.exists_fixedPoint_subtype hKne hK hKc hcomb

/-- **Day–Rickert fixed-point theorem** (group homomorphism into `E ≃ᵃ[ℝ] E`). Every jointly
continuous action by affine equivalences of an amenable topological group `G` on a nonempty compact
convex subset `K` of a Hausdorff locally convex real space `E` has a fixed point in `K`. -/
theorem Amenable.exists_fixedPoint_affineEquiv [Amenable G] {E : Type v} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] {K : Set E} (hKne : K.Nonempty) (hK : IsCompact K)
    (hKc : Convex ℝ K) (π : G →* (E ≃ᵃ[ℝ] E)) (hmaps : ∀ g : G, MapsTo (π g) K K)
    (hcont : Continuous fun p : G × K => π p.1 (p.2 : E)) :
    ∃ x ∈ K, ∀ g : G, π g x = x := by
  let π' : G →* (E →ᵃ[ℝ] E) :=
    { toFun g := (π g).toAffineMap
      map_one' := by ext x; simp
      map_mul' g h := by ext x; simp [map_mul] }
  exact Amenable.exists_fixedPoint_affineMap hKne hK hKc π' hmaps hcont

/-- Pointwise action of `UCB.leftTranslationWeakDual` on functions from an index type `ι` into
`WeakDual ℝ (UCB G)`, as a group homomorphism into affine equivalences. -/
private def piLeftTranslationAffineEquiv (ι : Type*) :
    G →* ((ι → WeakDual ℝ (UCB G)) ≃ᵃ[ℝ] (ι → WeakDual ℝ (UCB G))) where
  toFun g := LinearEquiv.toAffineEquiv
    { toFun x i := UCB.leftTranslationWeakDual g (x i)
      map_add' _ _ := by ext i; exact map_add _ _ _
      map_smul' c x := by ext i; exact map_smul (UCB.leftTranslationWeakDual g) c (x i)
      invFun x i := UCB.leftTranslationWeakDual g⁻¹ (x i)
      left_inv x := by
        ext i
        exact DFunLike.ext _ _ fun f => by
          rw [UCB.leftTranslationWeakDual_apply, UCB.leftTranslationWeakDual_apply]
          exact congrArg (x i)
            (by ext y; rw [UCB.leftTranslation_apply, UCB.leftTranslation_apply]; simp)
      right_inv x := by
        ext i
        exact DFunLike.ext _ _ fun f => by
          rw [UCB.leftTranslationWeakDual_apply, UCB.leftTranslationWeakDual_apply]
          exact congrArg (x i)
            (by ext y; rw [UCB.leftTranslation_apply, UCB.leftTranslation_apply]; simp) }
  map_one' := by
    ext x i
    simp only [AffineEquiv.coe_one, id_eq]
    exact DFunLike.ext _ _ fun f => congrArg (x i) (by ext y; simp)
  map_mul' g h := by
    ext x i
    simp only [AffineEquiv.coe_mul, Function.comp_apply]
    exact DFunLike.ext _ _ fun f => congrArg (x i) (by ext y; simp)

@[simp]
private theorem piLeftTranslationAffineEquiv_apply {ι : Type*} (g : G)
    (x : ι → WeakDual ℝ (UCB G)) (i : ι) :
    piLeftTranslationAffineEquiv ι g x i = UCB.leftTranslationWeakDual g (x i) :=
  (rfl)

/-- **Converse of the Day–Rickert fixed-point theorem.** If every jointly continuous action of `G`
by affine equivalences on a nonempty compact convex subset of a Hausdorff locally convex real space
in `Type (max u v)` has a fixed point, then `G` is amenable. -/
theorem Amenable.of_forall_exists_fixedPoint_affineEquiv
    (hfp : ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ (π : G →* (E ≃ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
        (Continuous fun p : G × K => π p.1 (p.2 : E)) → ∃ x ∈ K, ∀ g : G, π g x = x) :
    Amenable G := by
  -- Embed `Mean G` as constant functions `PUnit.{v + 1} → WeakDual ℝ (UCB G)` so the ambient
  -- Hausdorff locally convex real space lives in `Type (max u v)`.
  let lift : Mean G → (PUnit.{v + 1} → WeakDual ℝ (UCB G)) := fun m _ => m.toWeakDual
  have hlift_cont : Continuous lift := continuous_pi fun _ => Mean.continuous_toWeakDual
  let K₀ : Set (PUnit.{v + 1} → WeakDual ℝ (UCB G)) := Set.range lift
  have hK₀_cvx : Convex ℝ K₀ := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ a b ha hb hab
    obtain ⟨k, hk⟩ := Mean.convex_range_toWeakDual ⟨m, rfl⟩ ⟨n, rfl⟩ ha hb hab
    refine ⟨k, funext fun _ => ?_⟩
    exact hk
  have hmaps (g : G) : MapsTo (piLeftTranslationAffineEquiv (G := G) PUnit.{v + 1} g) K₀ K₀ := by
    rintro _ ⟨m, rfl⟩
    refine ⟨g • m, funext fun _ => ?_⟩
    simp [lift]
  have hcont : Continuous fun p : G × K₀ =>
      piLeftTranslationAffineEquiv (G := G) PUnit.{v + 1} p.1 p.2.1 := by
    refine continuous_pi fun i => ?_
    have heval : Continuous
        (fun x : K₀ => (⟨x.1 i, by obtain ⟨m, hm⟩ := x.2; exact ⟨m, congr_fun hm i⟩⟩ :
          Set.range (Mean.toWeakDual : Mean G → WeakDual ℝ (UCB G)))) :=
      ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    exact Mean.continuous_leftTranslationWeakDual_range_toWeakDual.comp
      (continuous_fst.prodMk (heval.comp continuous_snd))
  obtain ⟨_, ⟨m, rfl⟩, hx⟩ := hfp (PUnit.{v + 1} → WeakDual ℝ (UCB G)) K₀
    (Set.range_nonempty lift) (isCompact_range hlift_cont) hK₀_cvx
    (piLeftTranslationAffineEquiv PUnit.{v + 1}) hmaps hcont
  refine ⟨⟨m, Mean.mem_fixedPoints_iff.1 (MulAction.mem_fixedPoints.2 fun g => ?_)⟩⟩
  apply Mean.toWeakDual_injective
  have hxg := congr_fun (hx g) PUnit.unit
  simpa [lift] using hxg

/-- If every jointly continuous affine action of `G` on a nonempty compact convex subset of a
Hausdorff locally convex real space in `Type (max u v)` has a fixed point, then `G` is amenable. -/
theorem Amenable.of_forall_exists_fixedPoint_affineMap
    (hfp : ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ (π : G →* (E →ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
        (Continuous fun p : G × K => π p.1 (p.2 : E)) → ∃ x ∈ K, ∀ g : G, π g x = x) :
    Amenable G :=
  Amenable.of_forall_exists_fixedPoint_affineEquiv.{u, v} fun E _ _ _ _ _ _ _ K hKne hK hKc π =>
    hfp E K hKne hK hKc
      { toFun g := (π g).toAffineMap
        map_one' := by ext x; simp
        map_mul' g h := by ext x; simp [map_mul] }

/-- If every jointly continuous action of `G` on a nonempty compact convex subset `K` of a Hausdorff
locally convex real space in `Type (max u v)` preserving binary convex combinations in `E` has a
fixed point, then `G` is amenable. -/
theorem Amenable.of_forall_exists_fixedPoint_subtype
    (hfp : ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      (K : Set E) [MulAction G K] [ContinuousSMul G K],
      K.Nonempty → IsCompact K → (hKc : Convex ℝ K) →
      (∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
        ((g • (⟨a • (y : E) + b • (z : E), hKc y.2 z.2 ha hb hab⟩ : K) : K) : E) =
          a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
      ∃ x : K, ∀ g : G, g • x = x) :
    Amenable G :=
  Amenable.of_forall_exists_fixedPoint_affineMap.{u, v}
    fun E _ _ _ _ _ _ _ K hKne hK hKc π hmaps hcont =>
      exists_fixedPoint_affineMap_of_subtype hKc π hmaps hcont (hfp E K hKne hK hKc)

/-- **Day–Rickert fixed-point characterization of amenability** (`AffineMap` form, universe
polymorphic in `v`). A topological group `G : Type u` is amenable if and only if every jointly
continuous affine action of `G` on a nonempty compact convex subset of a Hausdorff locally convex
real space `E : Type (max u v)` has a fixed point. -/
theorem amenable_iff_forall_exists_fixedPoint_affineMap :
    Amenable G ↔
      ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
        (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
        ∀ (π : G →* (E →ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
          (Continuous fun p : G × K => π p.1 (p.2 : E)) → ∃ x ∈ K, ∀ g : G, π g x = x :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hKne hK hKc π hmaps hcont =>
      Amenable.exists_fixedPoint_affineMap hKne hK hKc π hmaps hcont,
    Amenable.of_forall_exists_fixedPoint_affineMap.{u, v}⟩

/-- **Day–Rickert fixed-point characterization of amenability** (`AffineEquiv` form, universe
polymorphic in `v`). A topological group `G : Type u` is amenable if and only if every jointly
continuous action of `G` by affine equivalences on a nonempty compact convex subset of a Hausdorff
locally convex real space `E : Type (max u v)` has a fixed point. -/
theorem amenable_iff_forall_exists_fixedPoint_affineEquiv :
    Amenable G ↔
      ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
        (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
        ∀ (π : G →* (E ≃ᵃ[ℝ] E)), (∀ g : G, MapsTo (π g) K K) →
          (Continuous fun p : G × K => π p.1 (p.2 : E)) → ∃ x ∈ K, ∀ g : G, π g x = x :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hKne hK hKc π hmaps hcont =>
      Amenable.exists_fixedPoint_affineEquiv hKne hK hKc π hmaps hcont,
    Amenable.of_forall_exists_fixedPoint_affineEquiv.{u, v}⟩

/-- **Day–Rickert fixed-point characterization of amenability** (intrinsic `MulAction G K` form,
universe polymorphic in `v`). A topological group `G : Type u` is amenable if and only if every
jointly continuous action of `G` on a nonempty compact convex subset `K` of a Hausdorff locally
convex real space `E : Type (max u v)` preserving binary convex combinations in `E` has a fixed
point. -/
theorem amenable_iff_forall_exists_fixedPoint_subtype :
    Amenable G ↔
      ∀ (E : Type (max u v)) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
        [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
        (K : Set E) [MulAction G K] [ContinuousSMul G K],
        K.Nonempty → IsCompact K → (hKc : Convex ℝ K) →
        (∀ (g : G) (y z : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
          ((g • (⟨a • (y : E) + b • (z : E), hKc y.2 z.2 ha hb hab⟩ : K) : K) : E) =
            a • ((g • y : K) : E) + b • ((g • z : K) : E)) →
        ∃ x : K, ∀ g : G, g • x = x :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hKne hK hKc hcomb =>
      Amenable.exists_fixedPoint_subtype hKne hK hKc hcomb,
    Amenable.of_forall_exists_fixedPoint_subtype.{u, v}⟩

end FixedPoint

end TauCeti
