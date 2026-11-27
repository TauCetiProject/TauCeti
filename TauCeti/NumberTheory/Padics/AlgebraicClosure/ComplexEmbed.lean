/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.AlgebraicCard
import TauCeti.Analysis.Complex.FieldEmbedding
import TauCeti.NumberTheory.Padics.Cardinality

/-!
# `ℓ`-adic criterion for algebraicity of complex numbers

Using the continuum cardinality of `PadicAlgCl ℓ`
(`TauCeti.Padic.cardinalMk_eq_continuum_of_isAlgebraic`) and the extension of transcendental
correspondences to field isomorphisms `PadicAlgCl ℓ ≃ₐ[ℚ] ℂ`
(`TauCeti.Complex.exists_algEquiv_apply_eq`), any complex number whose spectral norm `‖ι x‖` is
uniformly bounded across all ring isomorphisms `ι : ℂ ≃+* PadicAlgCl ℓ` must be algebraic over `ℚ`.

## Main results

* `TauCeti.isAlgebraic_of_forall_norm_ringEquiv_le`: if `x : ℂ` has uniformly bounded spectral
  norm `‖ι x‖ ≤ c` across all ring isomorphisms `ι : ℂ ≃+* PadicAlgCl ℓ`, then `x` is algebraic
  over `ℚ`.

## References

* E. Steinitz, *Algebraische Theorie der Körper*, J. Reine Angew. Math. **137** (1910), 167–309.
* Adapted from `New.isAlgebraic_of_norm_complexToCp_le` in
  `src/Lib/General/NumberTheory/PadicLimitsValuation.lean` of `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

namespace TauCeti

/-- **`ℓ`-adic criterion for algebraicity of complex numbers.** Let `ℓ` be a prime. If the
spectral norms `‖ι x‖` of `x : ℂ` under all ring isomorphisms `ι : ℂ ≃+* PadicAlgCl ℓ` have a
common upper bound `c`, then `x` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_forall_norm_ringEquiv_le {ℓ : ℕ} [Fact ℓ.Prime] {x : ℂ} {c : ℝ}
    (h_bound : ∀ ι : ℂ ≃+* PadicAlgCl ℓ, ‖ι x‖ ≤ c) : IsAlgebraic ℚ x := by
  by_contra hx
  obtain ⟨y, hy, hcy⟩ : ∃ y : PadicAlgCl ℓ, ¬IsAlgebraic ℚ y ∧ c < ‖y‖ :=
    ((Algebraic.countable ℚ (PadicAlgCl ℓ)).dense_compl ℚ_[ℓ]).exists_mem_open
      (isOpen_Ioi.preimage continuous_norm) (NormedField.exists_lt_norm _ c)
  obtain ⟨φ, hφ⟩ := TauCeti.Complex.exists_algEquiv_apply_eq
    (TauCeti.Padic.cardinalMk_eq_continuum_of_isAlgebraic ℓ (PadicAlgCl ℓ)) hy hx
  exact hcy.not_ge (by simpa [← hφ] using h_bound φ.symm.toRingEquiv)

end TauCeti

end
