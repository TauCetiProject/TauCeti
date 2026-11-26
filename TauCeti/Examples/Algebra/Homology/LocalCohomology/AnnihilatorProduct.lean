/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.AnnihilatorProduct

/-!
# Annihilator products of local cohomology over `ℤ`

With support in `V(2)`, the module `ℤ ⧸ 4ℤ` is its own `H^0`, so its annihilator product with
cutoff `1` is exactly `4ℤ`, not the radical `2ℤ`. The module `ℤ` has no `2`-power torsion, so its
annihilator product with cutoff `1` is the unit ideal.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, arXiv:1810.04493v2,
  Definition 3.1(ii).
-/

public section

namespace localCohomology

/-- The annihilator product of `ℤ ⧸ 4ℤ` with support in `V(2)` and cutoff `1` is `4ℤ`, which is
strictly smaller than its radical `2ℤ`. -/
example : annihilatorProduct (Ideal.span {(2 : ℤ)}) (ℤ ⧸ Ideal.span {(4 : ℤ)}) 1 =
    Ideal.span {4} := by
  rw [annihilatorProduct_one, annihilator_obj_zero_of_pow_le _ _ (n := 2),
    Ideal.annihilator_quotient]
  rw [Ideal.annihilator_quotient, Ideal.span_singleton_pow]
  norm_num

/-- The ideal `4ℤ` is not its radical `2ℤ`. -/
example : Ideal.span {(4 : ℤ)} ≠ Ideal.span {2} := by
  rw [Ne, Ideal.span_singleton_eq_span_singleton, Int.associated_iff]
  norm_num

/-- The module `ℤ` has no `2`-power torsion, so its annihilator product with support in `V(2)`
and cutoff `1` is the unit ideal. -/
example : annihilatorProduct (Ideal.span {(2 : ℤ)}) ℤ 1 = ⊤ := by
  rw [annihilatorProduct_one, annihilator_obj_zero, Submodule.annihilator_eq_top_iff,
    eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem ℤ _ x).1 hx
  have := (Submodule.mem_torsionBySet_iff _ x).1 hn
    ⟨2 ^ n, by simp [Ideal.span_singleton_pow]⟩
  simpa using this

end localCohomology
