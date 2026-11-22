/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated-derivative jets of germs

For germs on a nontrivially normed field, `Filter.Germ.iteratedDerivJet` is the unscaled `n`-jet
`(f(a), f'(a), …, f⁽ⁿ⁻¹⁾(a))` of a germ at `a`, computed on any representative `f`.
-/

public section

open Filter Topology

namespace Filter.Germ

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {a : 𝕜}

/-- The unscaled `n`-jet `(f(a), f'(a), …, f⁽ⁿ⁻¹⁾(a))` of a germ at `a`, computed on any
representative `f`. No factorials enter it. -/
noncomputable def iteratedDerivJet (n : ℕ) (φ : Germ (𝓝 a) F) : Fin n → F :=
  φ.liftOn (fun f j ↦ iteratedDeriv j f a) fun _ _ h ↦ funext fun j ↦ h.iteratedDeriv_eq j

/-- The jet of the germ of a function is its vector of unscaled iterated derivatives. -/
@[simp]
theorem iteratedDerivJet_coe (n : ℕ) (f : 𝕜 → F) :
    (f : Germ (𝓝 a) F).iteratedDerivJet n = fun j : Fin n ↦ iteratedDeriv j f a := (rfl)

end Filter.Germ
