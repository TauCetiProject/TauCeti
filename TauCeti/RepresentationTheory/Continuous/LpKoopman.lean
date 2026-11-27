/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.CompactOpen
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# The `Lᵖ` pullback representation of a measure-preserving group action

Let a group `G` act on a measurable space `X`, preserving a measure `μ`:
`hμ : ∀ g, MeasurePreserving (g • ·) μ μ`. For `1 ≤ p` and a normed space `E`, the *`Lᵖ` pullback
(Koopman) representation* `TauCeti.lpKoopman 𝕜 E p μ hμ : ContRepresentation 𝕜 G (Lp E p μ)`
sends `g` to the pullback along `x ↦ g⁻¹ • x`, so that `(π(g) f)(x) = f (g⁻¹ • x)` almost
everywhere (`TauCeti.coeFn_lpKoopman`). The inverse makes `g ↦ π(g)` a homomorphism,
`π(g h) = π(g) ∘ π(h)`, and each `π(g)` is an isometry (`TauCeti.norm_lpKoopman_apply`), so the
representation on `L²` is unitary (`TauCeti.isUnitary_lpKoopman`, `TauCeti.star_lpKoopman`). These
need no topology on `G` or `X` and no finiteness of `μ`. The scalar representation on `Lp ℂ p μ`
is `TauCeti.lpKoopman ℂ ℂ p μ hμ`, and the left regular representation
`MeasureTheory.Measure.leftRegular` is the case of a group acting on itself by left
multiplication.

For a continuous action of a group with continuous inversion on an R₁ space with its Borel
σ-algebra, a measure `μ` inner regular for compact sets on sets of finite measure and locally
finite, and `p ≠ ∞`, the orbit maps `g ↦ π(g) f` are continuous
(`TauCeti.continuous_lpKoopman_apply`), by Mathlib's `Lp.compMeasurePreserving_continuous`.

## Main definitions

* `TauCeti.lpKoopman 𝕜 E p μ hμ`: the representation `g ↦ (f ↦ f ∘ (g⁻¹ • ·))` on `Lp E p μ`.

## Main results

* `TauCeti.mem_invariants_lpKoopman_iff`: the invariant vectors are the classes `f` with
  `f (g • x) = f x` almost everywhere, for every `g`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {G X 𝕜 E : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [NormedRing 𝕜]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) (hμ : ∀ g : G, MeasurePreserving (g • ·) μ μ)

variable (𝕜 E) in
/-- The `Lᵖ` pullback representation of a measure-preserving group action:
`π(g) f = f ∘ (g⁻¹ • ·)`. -/
noncomputable def lpKoopman : ContRepresentation 𝕜 G (Lp E p μ) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (g⁻¹ • ·) (hμ g⁻¹)).toContinuousLinearMap
      map_one' := by
        ext f : 1
        simp only [inv_one, one_smul, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, one_apply_eq_self]
        exact Lp.compMeasurePreserving_id_apply f
      map_mul' g h := by
        ext f : 1
        have : (fun x : X ↦ (g * h)⁻¹ • x) = (h⁻¹ • ·) ∘ (g⁻¹ • ·) := by
          ext x
          simp [mul_smul]
        simp only [LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply,
          mul_apply_eq_comp, this]
        exact Lp.compMeasurePreserving_comp_apply f (hμ h⁻¹) (hμ g⁻¹) }

variable {p μ hμ}

/-- `π(g)` is the pullback along `x ↦ g⁻¹ • x`. -/
theorem lpKoopman_apply (g : G) (f : Lp E p μ) :
    lpKoopman 𝕜 E p μ hμ g f = Lp.compMeasurePreserving (g⁻¹ • ·) (hμ g⁻¹) f :=
  (rfl)

/-- `(π(g) f)(x) = f (g⁻¹ • x)` for almost every `x`. -/
theorem coeFn_lpKoopman (g : G) (f : Lp E p μ) :
    lpKoopman 𝕜 E p μ hμ g f =ᵐ[μ] fun x ↦ f (g⁻¹ • x) :=
  Lp.coeFn_compMeasurePreserving f (hμ g⁻¹)

/-- **The invariants of the pullback representation.** A class `f ∈ Lᵖ` is fixed by every `π(g)`
exactly when `f (g • x) = f x` for almost every `x`, for every `g`. -/
theorem mem_invariants_lpKoopman_iff {f : Lp E p μ} :
    f ∈ (lpKoopman 𝕜 E p μ hμ).invariants ↔ ∀ g : G, (fun x ↦ f (g • x)) =ᵐ[μ] f := by
  rw [ContRepresentation.mem_invariants, (Equiv.inv G).forall_congr_left]
  refine forall_congr' fun g ↦ ?_
  rw [Equiv.inv_symm, Equiv.inv_apply, Lp.ext_iff]
  simpa only [inv_inv] using (coeFn_lpKoopman (𝕜 := 𝕜) (hμ := hμ) g⁻¹ f).congr_left

/-- Each `π(g)` is an isometry. -/
@[simp]
theorem norm_lpKoopman_apply (g : G) (f : Lp E p μ) : ‖lpKoopman 𝕜 E p μ hμ g f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (hμ g⁻¹)

/-- The `L²` pullback representation of a measure-preserving action is unitary. -/
theorem isUnitary_lpKoopman {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : (lpKoopman 𝕜 E 2 μ hμ).IsUnitary := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  exact norm_lpKoopman_apply

/-- On a Hilbert space `E`, the operator `star` of the `L²` pullback by `g` is the pullback by
`g⁻¹`. -/
@[simp]
theorem star_lpKoopman {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (g : G) : star (lpKoopman 𝕜 E 2 μ hμ g) = lpKoopman 𝕜 E 2 μ hμ g⁻¹ :=
  isUnitary_lpKoopman.star_eq_inv g

/-- For a continuous action of a group with continuous inversion on an R₁ space, with a measure
that is inner regular for compact sets on sets of finite measure and locally finite, and `p ≠ ∞`,
the orbit map `g ↦ π(g) f` is continuous. -/
theorem continuous_lpKoopman_apply [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace X] [BorelSpace X] [R1Space X] [ContinuousSMul G X]
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g : G ↦ lpKoopman 𝕜 E p μ hμ g f := by
  let φ : C(G × X, X) := ⟨fun q ↦ q.1⁻¹ • q.2, by fun_prop⟩
  have hcurry (g : G) : ⇑(φ.curry g) = (g⁻¹ • ·) := by
    ext x
    simp [φ]
  have h := (continuous_const (y := f)).compMeasurePreservingLp φ.curry.continuous
    (fun g ↦ hcurry g ▸ hμ g⁻¹) hp
  simp only [hcurry] at h
  simpa only [lpKoopman_apply] using h

end TauCeti
