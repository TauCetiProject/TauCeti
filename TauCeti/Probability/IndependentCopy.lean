/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Independent copies on a product extension

On the product probability space `μ × μ`, the second coordinate supplies an independent copy of
any random variable on the original space. The first coordinate retains the original joint law of
any pair of random variables. These facts let later arguments extend a space to introduce an
independent copy without changing relationships among variables already on the space.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Z : Ω → F}

/-- On the product extension, a fresh copy of `X` is independent of the original pair `(X, Z)`.
Thus any dependence between `X` and `Z` is retained on the first coordinate. -/
theorem indepFun_snd_comp_pair_fst_prod (hX : Measurable X) (hZ : Measurable Z) :
    (fun ω : Ω × Ω => X ω.2) ⟂ᵢ[μ.prod μ] (fun ω => (X ω.1, Z ω.1)) :=
  (indepFun_prod (hX.prodMk hZ) hX).symm

/-- The pair on the first coordinate of the product extension has the same joint law as `(X, Z)`
on the original space. -/
theorem map_pair_fst_prod (hX : Measurable X) (hZ : Measurable Z) :
    (μ.prod μ).map (fun ω : Ω × Ω => (X ω.1, Z ω.1)) =
      μ.map (fun ω => (X ω, Z ω)) := by
  calc
    (μ.prod μ).map (fun ω : Ω × Ω => (X ω.1, Z ω.1)) =
        (μ.prod μ).map ((fun ω => (X ω, Z ω)) ∘ Prod.fst) := rfl
    _ = ((μ.prod μ).map Prod.fst).map (fun ω => (X ω, Z ω)) :=
      (Measure.map_map (hX.prodMk hZ) measurable_fst).symm
    _ = μ.map (fun ω => (X ω, Z ω)) := by simp

/-- The second coordinate of the product extension gives a copy of `X` with the same law. -/
theorem map_copy_snd_prod (hX : Measurable X) :
    (μ.prod μ).map (fun ω : Ω × Ω => X ω.2) = μ.map X := by
  calc
    (μ.prod μ).map (fun ω : Ω × Ω => X ω.2) =
        (μ.prod μ).map (X ∘ Prod.snd) := rfl
    _ = ((μ.prod μ).map Prod.snd).map X :=
      (Measure.map_map hX measurable_snd).symm
    _ = μ.map X := by simp

end TauCeti.Probability
