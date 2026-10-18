/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.Probability.Ergodic.FixedSpace
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv

/-!
# The Koopman Markov operator on measurable germs and `L∞`

For a measure-preserving endomorphism `T`, composition `g ↦ g ∘ T` is bundled as a real-linear
operator on almost-everywhere measurable real-valued functions. It preserves one and
multiplication, is positive and monotone, and its powers are composition with the corresponding
iterates of `T`.

On `L∞`, `linftyOne` supplies the constant-one element for an arbitrary measure, while Mathlib's
heterogeneous Hölder action supplies pointwise multiplication. Mathlib's existing composition
isometry preserves these operations. Its positivity, monotonicity, and fixed-point
characterization hold on general `Lᵖ` and are supplied by `TauCeti.Probability.Ergodic.FixedSpace`.

Mathlib provides the underlying composition maps as `AEEqFun.compMeasurePreserving` and
`Lp.compMeasurePreservingₗᵢ`. The only new construction here is their Markov-operator interface.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The deterministic Koopman Markov operator associated to a measure-preserving endomorphism.

It acts on measurable-function germs by precomposition and is bundled as a real-linear operator. -/
def koopmanMarkov (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : (Ω →ₘ[μ] ℝ) →ₗ[ℝ] (Ω →ₘ[μ] ℝ) where
  toFun := fun g => g.compMeasurePreserving T hT
  map_add' := by
    intro g h
    exact AEEqFun.induction_on₂ g h fun _ _ _ _ => by
      simp only [AEEqFun.compMeasurePreserving_mk, AEEqFun.mk_add_mk]; rfl
  map_smul' := by
    intro c g
    exact AEEqFun.induction_on g fun _ _ => by
      simp only [RingHom.id_apply, AEEqFun.compMeasurePreserving_mk, AEEqFun.smul_mk]; rfl

/-- A representative of `koopmanMarkov T hT g` is almost everywhere `g ∘ T`. -/
theorem coeFn_koopmanMarkov (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Ω →ₘ[μ] ℝ) :
    koopmanMarkov T hT g =ᵐ[μ] g ∘ T :=
  AEEqFun.coeFn_compMeasurePreserving g hT

/-- The Koopman Markov operator preserves the constant function `1`. -/
@[simp]
theorem koopmanMarkov_one (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    koopmanMarkov T hT 1 = 1 := by
  simp only [koopmanMarkov, LinearMap.coe_mk, AddHom.coe_mk, AEEqFun.one_def,
    AEEqFun.compMeasurePreserving_mk]
  rfl

/-- The Koopman Markov operator preserves products. -/
@[simp]
theorem koopmanMarkov_mul (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g h : Ω →ₘ[μ] ℝ) :
    koopmanMarkov T hT (g * h) = koopmanMarkov T hT g * koopmanMarkov T hT h := by
  exact AEEqFun.induction_on₂ g h fun _ _ _ _ => by
    simp only [koopmanMarkov, LinearMap.coe_mk, AddHom.coe_mk, AEEqFun.mk_mul_mk,
      AEEqFun.compMeasurePreserving_mk]; rfl

/-- The deterministic Koopman Markov operator is monotone. -/
theorem koopmanMarkov_monotone (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Monotone (koopmanMarkov T hT) := by
  intro g h hgh
  rw [← AEEqFun.coeFn_le] at hgh ⊢
  have hghT := hT.quasiMeasurePreserving.tendsto_ae hgh
  filter_upwards [hghT, coeFn_koopmanMarkov T hT g, coeFn_koopmanMarkov T hT h]
    with ω hghω hg hh
  simpa [Function.comp_apply, hg, hh] using hghω

/-- The deterministic Koopman Markov operator is positive. -/
theorem koopmanMarkov_nonneg (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {g : Ω →ₘ[μ] ℝ} (hg : 0 ≤ g) :
    0 ≤ koopmanMarkov T hT g := by
  have h := koopmanMarkov_monotone T hT hg
  rwa [map_zero] at h

/-- The Koopman Markov operator of the identity transformation acts as the identity. -/
@[simp]
theorem koopmanMarkov_id :
    koopmanMarkov (μ := μ) id (MeasurePreserving.id μ) = LinearMap.id := by
  apply LinearMap.ext
  intro g
  exact AEEqFun.compMeasurePreserving_id g

/-- Composing transformations reverses the order of their Koopman Markov operators. -/
theorem koopmanMarkov_comp {T S : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hS : MeasurePreserving S μ μ) :
    koopmanMarkov (T ∘ S) (hT.comp hS) =
      (koopmanMarkov S hS).comp (koopmanMarkov T hT) := by
  apply LinearMap.ext
  intro g
  exact AEEqFun.compMeasurePreserving_comp g hT hS

/-- The `n`th power of a Koopman Markov operator is composition with the `n`th iterate. -/
theorem koopmanMarkov_iterate (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (n : ℕ) :
    (koopmanMarkov T hT : (Ω →ₘ[μ] ℝ) → (Ω →ₘ[μ] ℝ))^[n] =
      koopmanMarkov (T^[n]) (hT.iterate n) := by
  funext g
  exact AEEqFun.compMeasurePreserving_iterate g hT n

/-- A measurable-function germ is fixed by the Koopman Markov operator exactly when its chosen
representative is almost everywhere invariant under the transformation. -/
theorem koopmanMarkov_eq_self_iff (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Ω →ₘ[μ] ℝ) :
    koopmanMarkov T hT g = g ↔ g ∘ T =ᵐ[μ] g := by
  constructor
  · intro h
    exact (coeFn_koopmanMarkov T hT g).symm.trans
      (Filter.Eventually.of_forall fun ω => congrArg (fun q : Ω →ₘ[μ] ℝ => q ω) h)
  · intro h
    exact AEEqFun.ext ((coeFn_koopmanMarkov T hT g).trans h)

/-! ## The `L∞` Markov laws -/

/-- Composition by a measure-preserving map preserves the constant-one element of `L∞`. -/
@[simp]
theorem compMeasurePreservingLInfty_one (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp.compMeasurePreserving T hT linftyOne = linftyOne := by
  apply Lp.ext
  have honeT := hT.quasiMeasurePreserving.tendsto_ae
    (coeFn_linftyOne (Ω := Ω) (μ := μ))
  filter_upwards [Lp.coeFn_compMeasurePreserving linftyOne hT, honeT,
    coeFn_linftyOne (Ω := Ω) (μ := μ)] with ω hop honeT hone
  rw [hop, Function.comp_apply, honeT, hone]

/-- Composition by a measure-preserving map preserves pointwise products in `L∞`. -/
theorem compMeasurePreservingLInfty_mul (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f g : Lp ℝ ∞ μ) :
    Lp.compMeasurePreservingₗᵢ ℝ T hT (f • g : Lp ℝ ∞ μ) =
      Lp.compMeasurePreservingₗᵢ ℝ T hT f • Lp.compMeasurePreservingₗᵢ ℝ T hT g := by
  rw [Lp.compMeasurePreservingₗᵢ_apply, Lp.compMeasurePreservingₗᵢ_apply,
    Lp.compMeasurePreservingₗᵢ_apply]
  apply Lp.ext
  have hmulT := hT.quasiMeasurePreserving.tendsto_ae (Lp.coeFn_lpSMul (r := ∞) f g)
  filter_upwards [Lp.coeFn_compMeasurePreserving (f • g : Lp ℝ ∞ μ) hT, hmulT,
    Lp.coeFn_lpSMul (r := ∞) (Lp.compMeasurePreserving T hT f)
      (Lp.compMeasurePreserving T hT g),
    Lp.coeFn_compMeasurePreserving f hT, Lp.coeFn_compMeasurePreserving g hT]
    with ω hlhs hmul hrhs hf hg
  rw [hlhs, Function.comp_apply, hmul, hrhs]
  simp only [Pi.smul_apply', hf, hg, Function.comp_apply]

end Probability

end TauCeti
