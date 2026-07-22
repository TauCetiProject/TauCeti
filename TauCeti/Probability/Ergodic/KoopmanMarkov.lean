module

public import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# The Koopman Markov operator on measurable-function germs

This file supplies the algebraic part of the generic Koopman lane in the Exchangeability roadmap.
For a measure-preserving endomorphism `T`, composition `g ↦ g ∘ T` is bundled as an additive
operator on almost-everywhere measurable real-valued functions.  It preserves one and
multiplication, is positive and monotone, and its powers are composition with the corresponding
iterates of `T`.

Mathlib already provides the underlying operation as `AEEqFun.compMeasurePreserving`, as well as
the isometric linear operator on every `Lᵖ`.  Unlike a general positive unital operator, a
Koopman operator is multiplicative.  The later `L∞` API can restrict this operator to essentially
bounded germs.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The deterministic Koopman Markov operator associated to a measure-preserving endomorphism.

It acts on measurable-function germs by precomposition and is bundled as an additive operator. -/
def koopmanMarkov (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    (Ω →ₘ[μ] ℝ) →+ (Ω →ₘ[μ] ℝ) where
  toFun := fun g => g.compMeasurePreserving T hT
  map_zero' := by
    rfl
  map_add' := by
    intro g h
    change (g + h).compMeasurePreserving T hT =
      g.compMeasurePreserving T hT + h.compMeasurePreserving T hT
    exact AEEqFun.induction_on₂ g h fun _ _ _ _ => rfl

/-- A representative of `koopmanMarkov T hT g` is almost everywhere `g ∘ T`. -/
theorem coe_koopmanMarkov_ae (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Ω →ₘ[μ] ℝ) :
    koopmanMarkov T hT g =ᵐ[μ] g ∘ T :=
  by change g.compMeasurePreserving T hT =ᵐ[μ] g ∘ T
     exact AEEqFun.coeFn_compMeasurePreserving g hT

/-- The Koopman Markov operator preserves the constant function `1`. -/
@[simp]
theorem koopmanMarkov_one (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    koopmanMarkov T hT 1 = 1 := by
  change (1 : Ω →ₘ[μ] ℝ).compMeasurePreserving T hT = 1
  rfl

/-- The Koopman Markov operator preserves products. -/
@[simp]
theorem koopmanMarkov_mul (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g h : Ω →ₘ[μ] ℝ) :
    koopmanMarkov T hT (g * h) = koopmanMarkov T hT g * koopmanMarkov T hT h := by
  change (g * h).compMeasurePreserving T hT =
    g.compMeasurePreserving T hT * h.compMeasurePreserving T hT
  exact AEEqFun.induction_on₂ g h fun _ _ _ _ => rfl

/-- The deterministic Koopman Markov operator is positive. -/
theorem koopmanMarkov_nonneg (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {g : Ω →ₘ[μ] ℝ} (hg : 0 ≤ g) :
    0 ≤ koopmanMarkov T hT g := by
  rw [← AEEqFun.coeFn_le] at hg ⊢
  have hgT := hT.quasiMeasurePreserving.tendsto_ae hg
  have hzeroT := hT.quasiMeasurePreserving.tendsto_ae
    (AEEqFun.coeFn_zero (α := Ω) (β := ℝ) (μ := μ))
  filter_upwards [hgT, hzeroT, coe_koopmanMarkov_ae T hT g,
    AEEqFun.coeFn_zero (α := Ω) (β := ℝ) (μ := μ)] with ω hgω hzeroT hcomp hzero
  change (0 : Ω →ₘ[μ] ℝ) (T ω) = (0 : ℝ) at hzeroT
  rw [hzero, hcomp, Function.comp_apply, Pi.zero_apply, ← hzeroT]
  exact hgω

/-- The deterministic Koopman Markov operator is monotone. -/
theorem koopmanMarkov_mono (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Monotone (koopmanMarkov T hT) := by
  intro g h hgh
  rw [← AEEqFun.coeFn_le] at hgh ⊢
  have hghT := hT.quasiMeasurePreserving.tendsto_ae hgh
  filter_upwards [hghT, coe_koopmanMarkov_ae T hT g, coe_koopmanMarkov_ae T hT h]
    with ω hghω hg hh
  simpa [Function.comp_apply, hg, hh] using hghω

/-- The Koopman Markov operator of the identity transformation acts as the identity. -/
@[simp]
theorem koopmanMarkov_id :
    ∀ g, koopmanMarkov (μ := μ) id (MeasurePreserving.id μ) g = g := by
  intro g
  change g.compMeasurePreserving id (MeasurePreserving.id μ) = g
  exact AEEqFun.compMeasurePreserving_id g

/-- Composing transformations reverses the order of their Koopman Markov operators. -/
theorem koopmanMarkov_comp {T S : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hS : MeasurePreserving S μ μ) :
    ∀ g, koopmanMarkov (T ∘ S) (hT.comp hS) g =
      koopmanMarkov S hS (koopmanMarkov T hT g) :=
  fun g => by
    change g.compMeasurePreserving (T ∘ S) (hT.comp hS) =
      (g.compMeasurePreserving T hT).compMeasurePreserving S hS
    exact AEEqFun.compMeasurePreserving_comp g hT hS

/-- The `n`th power of a Koopman Markov operator is composition with the `n`th iterate. -/
theorem koopmanMarkov_iterate (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Ω →ₘ[μ] ℝ) (n : ℕ) :
    (koopmanMarkov T hT)^[n] g = koopmanMarkov (T^[n]) (hT.iterate n) g :=
  by
    change (fun x => x.compMeasurePreserving T hT)^[n] g =
      g.compMeasurePreserving (T^[n]) (hT.iterate n)
    exact AEEqFun.compMeasurePreserving_iterate g hT n

/-- A measurable-function germ is fixed by the Koopman Markov operator exactly when its chosen
representative is almost everywhere invariant under the transformation. -/
theorem koopmanMarkov_eq_self_iff (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Ω →ₘ[μ] ℝ) :
    koopmanMarkov T hT g = g ↔ g ∘ T =ᵐ[μ] g := by
  constructor
  · intro h
    exact (coe_koopmanMarkov_ae T hT g).symm.trans (Filter.EventuallyEq.rfl.trans
      (Filter.Eventually.of_forall fun ω => congrArg (fun q : Ω →ₘ[μ] ℝ => q ω) h))
  · intro h
    exact AEEqFun.ext ((coe_koopmanMarkov_ae T hT g).trans h)

end Probability

end TauCeti
