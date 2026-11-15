/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Ranges of base-change maps for Kähler differentials

This file identifies the base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` with the `liftBaseChange`
of `KaehlerDifferential.map R R A B`. It then records two reusable consequences of the
Jacobi–Zariski sequence. The base-change map onto `Ω[B⁄R]` is surjective exactly when `Ω[B⁄A]`
vanishes, and if `Ω[A⁄R]` is spanned by a set `s` then its range is spanned by the image of `s`.

## Main results

* `TauCeti.mapBaseChange_eq_liftBaseChange`
* `TauCeti.subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top`
* `TauCeti.range_mapBaseChange_eq_span_image`
-/

public section

noncomputable section

namespace TauCeti

open KaehlerDifferential

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is the `B`-linear extension of the
`A`-linear map `KaehlerDifferential.map R R A B : Ω[A⁄R] → Ω[B⁄R]`. -/
theorem mapBaseChange_eq_liftBaseChange :
    mapBaseChange R A B = (map R R A B).liftBaseChange B := by
  ext; simp

/-- In a tower `R → A → B`, the first map in the Jacobi–Zariski sequence is surjective
exactly when the relative differential module `Ω[B⁄A]` vanishes. -/
theorem subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top :
    Subsingleton Ω[B⁄A] ↔ (mapBaseChange R A B).range = ⊤ := by
  -- The range of `mapBaseChange` is the kernel of `map R A B B : Ω[B⁄R] → Ω[B⁄A]`. That map
  -- is surjective, so it vanishes exactly when its range `⊤` is `⊥`, i.e. when `Ω[B⁄A]` is
  -- trivial.
  rw [range_mapBaseChange, LinearMap.ker_eq_top, ← LinearMap.range_eq_bot,
    LinearMap.range_eq_top.mpr (map_surjective R A B)]
  grind [subsingleton_iff_bot_eq_top, Submodule.subsingleton_iff]

/-- If `Ω[A⁄R]` is spanned by `s`, then the range of the base-change map to `Ω[B⁄R]` is
spanned by the image of `s`. -/
theorem range_mapBaseChange_eq_span_image {s : Set Ω[A⁄R]} (hs : Submodule.span A s = ⊤) :
    (mapBaseChange R A B).range = Submodule.span B (map R R A B '' s) := by
  rw [mapBaseChange_eq_liftBaseChange, LinearMap.range_liftBaseChange, LinearMap.range_eq_map,
    ← hs, ← Submodule.span_image, Submodule.span_span_of_tower]

end TauCeti
