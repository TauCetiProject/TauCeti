/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Diagonal
public import TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Complex

/-!
# Cohomological characterizations of amenable normed algebras

This file connects `TauCeti.IsAmenable` to bounded Hochschild cohomology
`ContinuousLinearMap.hochschildBimoduleCohomology`:

* `TauCeti.isAmenable_iff_forall_subsingleton_hochschildBimoduleCohomology_one`: by definition, a
  normed algebra `A` is amenable if and only if `H¹(A, E*)` vanishes for every Banach `A`-bimodule
  `E` in the universe of `A`.
* `TauCeti.IsAmenable.subsingleton_hochschildBimoduleCohomology_one`: for an amenable Banach
  algebra over `ℝ` or `ℂ`, `H¹(A, E*)` vanishes for every normed `A`-bimodule `E` in any universe.
-/

public section

noncomputable section

universe u v

open ContinuousLinearMap

namespace TauCeti

-- Shorten instance search for dual bimodules.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace

section Basic

variable (𝕜 : Type v) (A : Type u) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- A normed algebra is amenable exactly when the first bounded Hochschild cohomology
`H¹(A, E*)` vanishes for every Banach `A`-bimodule `E` in the universe of `A`. -/
theorem isAmenable_iff_forall_subsingleton_hochschildBimoduleCohomology_one :
    IsAmenable 𝕜 A ↔ ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      (L R : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b x, L (a * b) x = L a (L b x))
      (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x)),
        Subsingleton (hochschildBimoduleCohomology (dualAction R) (dualAction L)
          (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
          (dualAction_apply_dualAction_apply_comm hLR) 1) := by
  rw [isAmenable_def]
  constructor
  · intro h E _ _ _ L R hL hR hLR
    exact (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).2
      (h E L R hL hR hLR)
  · intro h E _ _ _ L R hL hR hLR
    exact (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).1
      (h E L R hL hR hLR)

end Basic

section ArbitraryUniverse

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- For an amenable Banach algebra `A` over `ℝ` or `ℂ`, the first bounded Hochschild cohomology
`H¹(A, E*)` vanishes for every normed `A`-bimodule `E` in any universe. -/
theorem IsAmenable.subsingleton_hochschildBimoduleCohomology_one (h : IsAmenable 𝕜 A)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (L R : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (hLR : ∀ a b x, L a (R b x) = R b (L a x)) :
    Subsingleton (hochschildBimoduleCohomology (dualAction R) (dualAction L)
      (dualAction_mul_apply_of_right hR) (dualAction_mul_apply_of_left hL)
      (dualAction_apply_dualAction_apply_comm hLR) 1) :=
  (hochschildBimoduleCohomology.subsingleton_one_iff _ _ _ _ _).2
    (h.exists_eq_dualAction_sub_dualAction' hL hR hLR)

end ArbitraryUniverse

end TauCeti
