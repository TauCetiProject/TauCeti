/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas

import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The quotient by the radical of an ideal

For an ideal `I` of a commutative ring `A`, the quotient `A ⧸ √I` is the universal reduced
quotient of `A ⧸ I`: every ring homomorphism from `A ⧸ I` to a reduced ring factors uniquely
through `A ⧸ √I` (`Ideal.Quotient.bijective_comp_factor_radical`).

A quotient algebra is module-finite if its reduced quotient is module-finite and its
nilradical is finitely generated (for instance, when the radical of the defining ideal is
finitely generated, or when the quotient is noetherian). This is useful for passing from
finite residue fields to finite infinitesimal neighbourhoods, without assuming that the algebra
itself is finite over the coefficient ring.

The descent step is Mathlib's `Module.finite_of_surjective_of_ker_le_nilradical`.
-/

public section

namespace Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **The universal reduced quotient of `A ⧸ I`.** Every ring homomorphism from `A ⧸ I` to a
reduced ring factors uniquely through `A ⧸ √I`: precomposition with the projection
`A ⧸ I → A ⧸ √I` is a bijection. -/
theorem Quotient.bijective_comp_factor_radical (I : Ideal A) (T : Type*) [Semiring T]
    [IsReduced T] :
    Function.Bijective fun g : A ⧸ I.radical →+* T ↦ g.comp (Quotient.factor I.le_radical) := by
  refine ⟨fun g₁ g₂ h ↦ (RingHom.cancel_right (Quotient.factor_surjective I.le_radical)).mp h,
    fun f ↦ ⟨Quotient.lift _ (f.comp (Quotient.mk I)) fun a ⟨n, hn⟩ ↦ ?_, ?_⟩⟩
  · -- `f [a]` is nilpotent, since `a ^ n ∈ I`
    refine IsNilpotent.eq_zero ⟨n, ?_⟩
    rw [RingHom.comp_apply, ← map_pow, ← map_pow, Quotient.eq_zero_iff_mem.mpr hn, map_zero]
  · refine Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    simp

/-- Finiteness of the quotient by the radical descends to the original quotient when the
nilradical of the original quotient is finitely generated. That hypothesis holds in particular
when `I.radical` is finitely generated, since its image in `A ⧸ I` is the nilradical, and when
`A ⧸ I` is noetherian. -/
theorem moduleFinite_quotient_of_radical (I : Ideal A) (hI : (nilradical (A ⧸ I)).FG)
    [Module.Finite R (A ⧸ I.radical)] : Module.Finite R (A ⧸ I) := by
  have hrad : I.radical.map (Quotient.mk I) = nilradical (A ⧸ I) := by
    rw [map_radical_of_surjective Quotient.mk_surjective mk_ker.le, map_quotient_self, nilradical,
      Submodule.zero_eq_bot]
  have hker : RingHom.ker (Quotient.factorₐ R I.le_radical) = nilradical (A ⧸ I) := by
    rw [← RingHom.ker_coe_toRingHom, Quotient.coe_factorₐ, Quotient.factor_ker, hrad]
  exact Module.finite_of_surjective_of_ker_le_nilradical _
    (Quotient.factor_surjective I.le_radical) hker.le (hker ▸ hI)

end Ideal
