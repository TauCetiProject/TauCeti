/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglySheafy
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.Restricted.Noetherian

/-!
# Tests for strongly sheafy Huber rings

The field `ℚ_[p]` and its Tate algebras `ℚ_p⟨X₁, …, Xₘ⟩` are strongly sheafy, being strongly
noetherian Tate rings; in particular they are sheafy. Stably sheafy rings are strongly sheafy.
-/

namespace TauCeti.Huber

variable (p : ℕ) [Fact p.Prime]

/-- *test_field*: the complete nonarchimedean field `ℚ_[p]` is strongly sheafy. -/
example : IsStronglySheafy ℚ_[p] :=
  .of_isStronglyNoetherian

/-- *test_field*, sheafiness: strong sheafiness of `ℚ_[p]` recovers its sheafiness. -/
example : IsSheafyRing ℚ_[p] :=
  IsStronglySheafy.of_isStronglyNoetherian.isSheafyRing

/-- *test_tateAlgebra*: every Tate algebra `ℚ_p⟨X₁, …, Xₘ⟩` is strongly sheafy. -/
example (m : ℕ) : IsStronglySheafy (restrictedMvPowerSeriesCompletion m ℚ_[p]) :=
  (IsStronglySheafy.of_isStronglyNoetherian (A := ℚ_[p])).restrictedMvPowerSeriesCompletion m

/-- *test_of_isStablySheafyRing*: a stably sheafy Huber ring is strongly sheafy. -/
example {A : Type} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsHuberRing A] (h : IsStablySheafyRing.{0, 0} A) : IsStronglySheafy A :=
  .of_isStablySheafyRing h

end TauCeti.Huber
