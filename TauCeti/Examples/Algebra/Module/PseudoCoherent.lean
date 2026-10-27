/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Regular.IsSMulRegular
import TauCeti.Algebra.Module.PseudoCoherent.TwoOutOfThree

/-!
# Tests for pseudocoherent modules

The quotient of a ring by a non-zero-divisor is pseudocoherent, with the resolution
`0 → R → R → R ⧸ fR → 0` given by multiplication by `f`. Finitely generated projective modules are
pseudocoherent, and over a noetherian ring pseudocoherence is finite generation. Dividing a
pseudocoherent module by a non-zero-divisor on it keeps it pseudocoherent.
-/

namespace TauCeti.Huber

open LinearMap

/-- *test_quotient_nonZeroDivisor*: for a non-zero-divisor `f`, the kernel `fR` of `R → R ⧸ fR` is
isomorphic to `R`, so `R ⧸ fR` is pseudocoherent. -/
example {R : Type*} [CommRing R] {f : R} (hf : f ∈ nonZeroDivisors R) :
    IsPseudoCoherentOver R (R ⧸ Ideal.span {f}) ⊤ := by
  have hinj : Function.Injective (toSpanSingleton R R f) := fun a b hab ↦
    (mul_cancel_right_mem_nonZeroDivisors hf).mp (by simpa using hab)
  have hrange : range (toSpanSingleton R R f) = ker (Ideal.span {f}).mkQ := by
    rw [Submodule.ker_mkQ]
    exact (span_singleton_eq_range R R f).symm
  rw [← top_add (1 : ℕ∞)]
  exact (IsPseudoCoherentOver.succ_iff_ker (Submodule.mkQ_surjective _)).mpr
    ((IsPseudoCoherentOver.of_projective (M := R)).of_equiv
      ((LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)))

/-- *test_finiteProjective*: a finitely generated projective module is pseudocoherent. -/
example {R P : Type*} [Ring R] [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] : IsPseudoCoherentOver R P ⊤ :=
  .of_projective

/-- *test_noetherian*: over a noetherian ring, a module is pseudocoherent exactly when it is
finitely generated. -/
example {R M : Type*} [Ring R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] :
    IsPseudoCoherentOver R M ⊤ ↔ Module.Finite R M :=
  ⟨IsPseudoCoherentOver.finite, fun _ ↦ .of_isNoetherianRing⟩

/-- *test_ker_mul_nonZeroDivisor*: if `M` is pseudocoherent and `f` is a non-zero-divisor on `M`,
then the cokernel `M ⧸ fM` of multiplication by `f` is pseudocoherent. -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : R} (hf : IsSMulRegular M f)
    (hM : IsPseudoCoherentOver R M ⊤) : IsPseudoCoherentOver R (M ⧸ range (lsmul R M f)) ⊤ :=
  IsPseudoCoherentOver.cokernel (ker_eq_bot.mp ((isSMulRegular_iff_ker_lsmul_eq_bot M f).mp hf))
    (exact_map_mkQ_range _) (Submodule.mkQ_surjective _)
    (fun _ ↦ ENat.top_sub_one ▸ hM) hM

end TauCeti.Huber
