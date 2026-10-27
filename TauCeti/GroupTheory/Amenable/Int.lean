/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.MeasureTheory.Group.Foelner.Int
import TauCeti.GroupTheory.Amenable.Sequence

/-!
# Amenability of the integer group

Transport the intervals `{0, …, n}` through `Multiplicative.ofAdd`. Their relative
translation boundaries tend to zero by the additive interval estimates, so the averaging
criterion gives a left-invariant mean on the integer group.

Amenability of the integers is the starting example for proving amenability of finitely
generated abelian groups using products and quotients. The final instance allows any group
topology on `Multiplicative ℤ`.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

open Filter Finset Topology
open scoped Pointwise symmDiff

namespace TauCeti

/-- The integer group has Følner sets, viewed multiplicatively through `Multiplicative.ofAdd`.
The translation of an interval is the image of its additive translate. -/
theorem hasFoelnerSets_multiplicative_int : HasFoelnerSets (Multiplicative ℤ) := by
  let F (n : ℕ) : Finset (Multiplicative ℤ) := (Icc 0 (n : ℤ)).image Multiplicative.ofAdd
  have hne (n : ℕ) : (F n).Nonempty :=
    (nonempty_Icc.mpr (Int.natCast_nonneg n)).image _
  have htranslate (g : Multiplicative ℤ) (n : ℕ) :
      g • F n = ((Icc 0 (n : ℤ)).image (g.toAdd + ·)).image Multiplicative.ofAdd := by
    simp only [F, smul_finset_def, image_image, smul_eq_mul]
    exact congrArg (fun f : ℤ → Multiplicative ℤ => (Icc 0 (n : ℤ)).image f)
      (funext fun x => by simp only [Function.comp_apply, ofAdd_add, ofAdd_toAdd])
  have hlimit (g : Multiplicative ℤ) :
      Tendsto (fun n => (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) := by
    simpa only [htranslate, F, ← image_symmDiff _ _ Multiplicative.ofAdd.injective,
      card_image_of_injective _ Multiplicative.ofAdd.injective] using
      Int.tendsto_card_image_add_left_Icc_symmDiff_div_card g.toAdd
  exact .of_tendsto_card_smul_symmDiff_div_card (Eventually.of_forall hne) hlimit

/-- The integer group is amenable for every group topology. -/
instance Amenable.multiplicative_int [TopologicalSpace (Multiplicative ℤ)]
    [IsTopologicalGroup (Multiplicative ℤ)] : Amenable (Multiplicative ℤ) :=
  .of_hasFoelnerSets hasFoelnerSets_multiplicative_int

end TauCeti
