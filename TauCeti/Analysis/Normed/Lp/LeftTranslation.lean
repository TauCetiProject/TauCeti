/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Analysis.Normed.Lp.BoundedContinuous

/-!
# Left translation on `ℓᵖ` of a group action

Let a group `G` act on a type `X`. Left translation of sequences,

```text
(L_g u)(x) = u (g⁻¹ • x),        L_g L_h = L_(g * h),
```

reindexes `ℓᵖ(X, E)` along the permutation `MulAction.toPerm g` and therefore defines a group
homomorphism `lp.leftTranslation p 𝕜 : G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : X ↦ E) p)`
for `1 ≤ p`. On point masses it satisfies `L_g (lp.single p x v) = lp.single p (g • x) v`, on
finitely supported probabilities `s : Convexity.StdSimplex ℝ X` it agrees with `s.map (g • ·)`,
and it preserves coordinate sums `∑' x, u x`.

When `X` is a topological space on which `G` acts continuously, the isometric inclusion
`BoundedContinuousFunction.toLpInfty` intertwines precomposition by `g⁻¹ • ·` with
`lp.leftTranslation ∞ 𝕜 g`, and the duality pairing `lp.bcfPairing` satisfies
`⟨L_g u, f⟩ = ⟨u, f (g • ·)⟩` (hence `⟨L_g u, L_g f⟩ = ⟨u, f⟩`).
Specializing to `X = G` gives the sequence-space counterpart of
`MeasureTheory.Lp.leftTranslation` on counting measure, without any measurability assumptions.

## Main definitions

* `lp.leftTranslation p 𝕜`: left translation `g ↦ L_g` on `lp (fun _ : X ↦ E) p`, as a group
  homomorphism into linear isometry equivalences.

## Main results

* `lp.leftTranslation_single`: `L_g (lp.single p x v) = lp.single p (g • x) v`.
* `lp.leftTranslation_stdSimplex_toLp`: `L_g (s.toLp p) = (s.map (g • ·)).toLp p`.
* `lp.tsum_leftTranslation`: left translation preserves `∑' x, u x`.
* `lp.norm_leftTranslation_one_sub`: `‖L_g u - u‖₁ = ∑' x, ‖u (g⁻¹ • x) - u x‖`.
* `lp.bcfPairing_leftTranslation`: `⟨L_g u, f⟩ = ⟨u, f (g • ·)⟩`.
-/

public section

noncomputable section

open scoped ENNReal BoundedContinuousFunction

namespace LinearIsometryEquiv

/-- Reindexing `ℓᵖ` along a bijection preserves the unconditional sum of coordinates. -/
theorem tsum_lpCongrLeft {α β 𝕜 E : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedAddCommGroup E]
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (e : α ≃ β) (f : lp (fun _ : α ↦ E) p) :
    ∑' y, lpCongrLeft p 𝕜 E e f y = ∑' x, f x := by
  simp_rw [lpCongrLeft_apply]
  exact e.symm.tsum_eq fun x ↦ f x

end LinearIsometryEquiv

namespace lp

section MulAction

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜]
  {G X E : Type*} [Group G] [MulAction G X] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Left translation `g ↦ L_g` on `lp (fun _ : X ↦ E) p` for a group `G` acting on `X`, where
`(L_g u)(x) = u (g⁻¹ • x)`, as a group homomorphism into linear isometry equivalences. -/
def leftTranslation : G →* (lp (fun _ : X ↦ E) p ≃ₗᵢ[𝕜] lp (fun _ : X ↦ E) p) where
  toFun g := LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g)
  map_one' := by
    ext u x
    simp
  map_mul' g h := by
    ext u x
    simp [mul_smul]

variable {p 𝕜}

theorem leftTranslation_eq_lpCongrLeft (g : G) :
    leftTranslation p 𝕜 (X := X) (E := E) g =
      LinearIsometryEquiv.lpCongrLeft p 𝕜 E (MulAction.toPerm g) := by
  rfl

theorem coeFn_leftTranslation (g : G) (u : lp (fun _ : X ↦ E) p) :
    ⇑(leftTranslation p 𝕜 g u) = fun x ↦ u (g⁻¹ • x) := by
  ext x
  simp [leftTranslation_eq_lpCongrLeft]

@[simp]
theorem leftTranslation_apply (g : G) (u : lp (fun _ : X ↦ E) p) (x : X) :
    leftTranslation p 𝕜 g u x = u (g⁻¹ • x) := by
  simp [leftTranslation_eq_lpCongrLeft]

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
theorem leftTranslation_symm (g : G) :
    (leftTranslation p 𝕜 (X := X) (E := E) g).symm = leftTranslation p 𝕜 g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

@[simp]
theorem leftTranslation_symm_apply (g : G) (u : lp (fun _ : X ↦ E) p) (x : X) :
    (leftTranslation p 𝕜 g).symm u x = u (g • x) := by
  rw [leftTranslation_symm, leftTranslation_apply, inv_inv]

/-- Left translation by `g` sends the coordinate vector `lp.single p x v` to
`lp.single p (g • x) v`. -/
@[simp]
theorem leftTranslation_single [DecidableEq X] (g : G) (x : X) (v : E) :
    leftTranslation p 𝕜 g (lp.single p x v) = lp.single p (g • x) v :=
  LinearIsometryEquiv.lpCongrLeft_single (MulAction.toPerm g) x v

@[simp]
theorem leftTranslation_symm_single [DecidableEq X] (g : G) (x : X) (v : E) :
    (leftTranslation p 𝕜 g).symm (lp.single p x v) = lp.single p (g⁻¹ • x) v := by
  rw [leftTranslation_symm, leftTranslation_single]

/-- Left translation preserves the series sum of coordinates. -/
theorem tsum_leftTranslation (g : G) (u : lp (fun _ : X ↦ E) p) :
    ∑' x, leftTranslation p 𝕜 g u x = ∑' x, u x :=
  LinearIsometryEquiv.tsum_lpCongrLeft (MulAction.toPerm g) u

/-- Left translation of `f.toLp p` pushes `f : X →₀ E` forward along `g • ·`. -/
theorem leftTranslation_finsupp_toLp (g : G) (f : X →₀ E) :
    leftTranslation p 𝕜 g (f.toLp p) = (f.mapDomain (g • ·)).toLp p := by
  simp_rw [← MulAction.toPerm_apply g, f.toLp_mapDomain_equiv (MulAction.toPerm g) p]
  rw [leftTranslation_eq_lpCongrLeft, LinearIsometryEquiv.coe_lpCongrLeft]

/-- Left translation preserves and reflects the pointwise order on `ℓᵖ`. -/
@[simp]
theorem coeFn_leftTranslation_le_coeFn_leftTranslation_iff [LE E] (g : G)
    {u v : lp (fun _ : X ↦ E) p} :
    ⇑(leftTranslation p 𝕜 g u) ≤ ⇑(leftTranslation p 𝕜 g v) ↔ ⇑u ≤ ⇑v := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ by simpa using h (g⁻¹ • x)⟩
  simpa using h (g • x)

/-- Left translation preserves and reflects pointwise nonnegativity on `ℓᵖ`. -/
@[simp]
theorem coeFn_leftTranslation_nonneg_iff [LE E] (g : G) {u : lp (fun _ : X ↦ E) p} :
    0 ≤ ⇑(leftTranslation p 𝕜 g u) ↔ 0 ≤ ⇑u :=
  ⟨fun h x ↦ by simpa using h (g • x), fun h x ↦ by simpa using h (g⁻¹ • x)⟩

/-- Left translation preserves pointwise nonnegativity on `ℓᵖ`. -/
theorem coeFn_leftTranslation_nonneg [LE E] (g : G) {u : lp (fun _ : X ↦ E) p} (hu : 0 ≤ ⇑u) :
    0 ≤ ⇑(leftTranslation p 𝕜 g u) :=
  (coeFn_leftTranslation_nonneg_iff g).2 hu

end MulAction

section Specializations

variable {G X : Type*} [Group G] [MulAction G X]

/-- The `ℓ¹` norm of `L_g u - u` is `∑' x, ‖u (g⁻¹ • x) - u x‖`. -/
theorem norm_leftTranslation_one_sub {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (g : G) (u : lp (fun _ : X ↦ E) 1) :
    ‖leftTranslation 1 𝕜 g u - u‖ = ∑' x, ‖u (g⁻¹ • x) - u x‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by simp) (leftTranslation 1 𝕜 g u - u)

/-- Left translation fixes the constant sequence `1` in `ℓ∞`. -/
@[simp]
theorem leftTranslation_one {𝕜 B : Type*} [NormedRing 𝕜] [NormedRing B] [NormOneClass B]
    [Module 𝕜 B] [IsBoundedSMul 𝕜 B] (g : G) :
    leftTranslation ∞ 𝕜 g (1 : lp (fun _ : X ↦ B) ∞) = 1 := by
  ext x
  simp

/-- Left translation of `s.toLp p` pushes `s : StdSimplex ℝ X` forward along `g • ·`. -/
theorem leftTranslation_stdSimplex_toLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : G)
    (s : Convexity.StdSimplex ℝ X) :
    leftTranslation p ℝ g (s.toLp p) = (s.map (g • ·)).toLp p := by
  simpa [Convexity.StdSimplex.toLp_def] using
    leftTranslation_finsupp_toLp (p := p) (𝕜 := ℝ) g s.weights

end Specializations

section BoundedContinuous

variable {G X E : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]
  [NormedAddCommGroup E]

/-- `BoundedContinuousFunction.toLpInfty` intertwines precomposition by `g⁻¹ • ·` with
`lp.leftTranslation ∞ 𝕜 g`. -/
theorem leftTranslation_toLpInfty {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (g : G) (f : X →ᵇ E) :
    leftTranslation ∞ 𝕜 g (BoundedContinuousFunction.toLpInfty 𝕜 f) =
      BoundedContinuousFunction.toLpInfty 𝕜
        (f.compContinuous ⟨(g⁻¹ • ·), continuous_const_smul g⁻¹⟩) := by
  ext x
  simp

/-- Pairing `L_g u` in `ℓ¹(X, 𝕜)` with `f : X →ᵇ E` equals pairing `u` with `x ↦ f (g • x)`. -/
theorem bcfPairing_leftTranslation {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [CompleteSpace E] (g : G) (u : lp (fun _ : X ↦ 𝕜) 1) (f : X →ᵇ E) :
    bcfPairing 𝕜 X E (leftTranslation 1 𝕜 g u) f =
      bcfPairing 𝕜 X E u (f.compContinuous ⟨(g • ·), continuous_const_smul g⟩) := by
  simp only [bcfPairing_apply, leftTranslation_apply,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
  rw [← (MulAction.toPerm g).tsum_eq]
  simp

/-- Pairing `L_g u` with the left translate `x ↦ f (g⁻¹ • x)` equals pairing `u` with `f`. -/
@[simp]
theorem bcfPairing_leftTranslation_compContinuous_inv_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [CompleteSpace E] (g : G) (u : lp (fun _ : X ↦ 𝕜) 1) (f : X →ᵇ E) :
    bcfPairing 𝕜 X E (leftTranslation 1 𝕜 g u)
        (f.compContinuous ⟨(g⁻¹ • ·), continuous_const_smul g⁻¹⟩) =
      bcfPairing 𝕜 X E u f := by
  rw [bcfPairing_leftTranslation]
  congr 1
  ext x
  simp

end BoundedContinuous

/-- On a group `G` with separately continuous multiplication, `BoundedContinuousFunction.toLpInfty`
intertwines precomposition with `ContinuousMap.mulLeft g⁻¹` and `lp.leftTranslation ∞ 𝕜 g`. -/
theorem leftTranslation_toLpInfty_mulLeft {G E 𝕜 : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (g : G) (f : G →ᵇ E) :
    leftTranslation ∞ 𝕜 g (BoundedContinuousFunction.toLpInfty 𝕜 f) =
      BoundedContinuousFunction.toLpInfty 𝕜 (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) :=
  leftTranslation_toLpInfty (X := G) g f

end lp
