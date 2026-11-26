/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# A nondegenerate multiplication pairing on a quotient of `k[X]`

A finite-dimensional quotient `A = k[X] ⧸ I` of the polynomial ring over a field carries a linear
form `L` for which the pairing `(x, y) ↦ L (x * y)` on `A` is nondegenerate
(`Ideal.exists_nondegenerate_mul_form`). Over the principal ideal domain `k[X]`, some linear form
on `A` has the same annihilator as the whole dual of `A`; such a form pairs nondegenerately.

## References

* Adapted from `New.exists_nondegenerate_mul_form` of `src/Lib/LocalGL/Green/HallAlgebra.lean` in
  grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open Module Polynomial

namespace Ideal

variable {k : Type*} [Field k]

/-- A finite-dimensional quotient `A` of `k[X]` carries a linear form `L` for which the pairing
`(x, y) ↦ L (x * y)` is nondegenerate. -/
theorem exists_nondegenerate_mul_form (I : Ideal k[X]) [Module.Finite k (k[X] ⧸ I)] :
    ∃ L : Dual k (k[X] ⧸ I),
      LinearMap.BilinForm.Nondegenerate ((LinearMap.mul k (k[X] ⧸ I)).compr₂ L) := by
  -- Let `k[X]` act on the dual by `(q • φ) x = φ (q • x)`. Over a principal ideal domain some `L`
  -- has the same annihilator as the whole module.
  let _ : Module k[X] (Dual k (k[X] ⧸ I)) :=
    Module.compHom _ (R := k[X]ᵈᵐᵃ) (.toOpposite (.id k[X]) .all)
  have _ : IsScalarTower k k[X] (Dual k (k[X] ⧸ I)) := ⟨fun c q φ ↦ by
    ext x
    -- `change` unfolds the action of `k[X]` on the dual, defined just above.
    change φ ((c • q) • x) = c • φ (q • x)
    rw [smul_assoc, map_smul]⟩
  have _ : Module.Finite k[X] (Dual k (k[X] ⧸ I)) := .of_restrictScalars_finite k k[X] _
  obtain ⟨L, hL⟩ : ∃ L : Dual k (k[X] ⧸ I),
      (LinearMap.toSpanSingleton k[X] (Dual k (k[X] ⧸ I)) L).ker =
        Module.annihilator k[X] (Dual k (k[X] ⧸ I)) :=
    Module.exists_ker_toSpanSingleton_eq_annihilator k[X] (Dual k (k[X] ⧸ I))
  refine ⟨L, .ofSeparatingLeft ?_⟩
  rintro ⟨q⟩ hq
  -- If `q` pairs to zero with everything then `q • L = 0`, so `q` kills every linear form `φ`;
  -- evaluating `q • φ = 0` at `1` shows that `φ` vanishes on the class of `q`.
  have h_ann : q ∈ Module.annihilator k[X] (Dual k (k[X] ⧸ I)) := hL.le (LinearMap.ext hq)
  refine (Module.forall_dual_apply_eq_zero_iff k _).mp fun φ ↦ ?_
  have h_eval : φ (q • 1) = 0 := LinearMap.congr_fun (Module.mem_annihilator.mp h_ann φ) 1
  rwa [← mul_one q]

end Ideal
