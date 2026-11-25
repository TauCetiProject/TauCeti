/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.CategoryTheory.Dagger.Basic
import Mathlib.Tactic.Module

/-!
# Polarization in complex linear dagger categories

In a complex linear dagger category, the pairing `(f, g) ↦ f†g` of two parallel arrows
`f g : X ⟶ Y` is an `End X`-valued form, linear in `g` and conjugate-linear in `f`. Written
categorically, `f†g` is `g ≫ dagger f`. Like any sesquilinear form, it is determined by its
diagonal values `h†h`, through the polarization identity

`4 f†g = (f + g)†(f + g) - (f - g)†(f - g) - i (f + ig)†(f + ig) + i (f - ig)†(f - ig)`.

No norm or positivity is involved. In a C*-category this is the polarization identity of the
Hilbert `End X`-module `X ⟶ Y`.
-/

public section

open CategoryTheory Complex

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C] [DaggerPreadditive C]
  [Linear ℂ C] [DaggerLinear ℂ C] {X Y : C}

/-- The polarization identity: for parallel arrows `f g : X ⟶ Y`, the composite `f†g`, that is
`g ≫ dagger f`, is determined by the composites `h ≫ dagger h` for `h` among `f + g`, `f - g`,
`f + i g` and `f - i g`. -/
theorem comp_dagger_polarization (f g : X ⟶ Y) :
    g ≫ dagger f = (4 : ℂ)⁻¹ • ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) -
      I • ((f + I • g) ≫ dagger (f + I • g)) + I • ((f - I • g) ≫ dagger (f - I • g))) := by
  simp only [dagger_add, dagger_sub, dagger_smul, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_neg, Linear.smul_comp,
    Linear.comp_smul, Complex.star_def, conj_I, smul_add, smul_sub, smul_neg, neg_smul,
    smul_smul, I_mul_I]
  module

end TauCeti
