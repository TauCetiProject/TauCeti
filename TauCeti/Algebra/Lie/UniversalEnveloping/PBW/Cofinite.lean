/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Finite
public import TauCeti.RingTheory.Ideal.Quotient.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Powers of cofinite enveloping-algebra ideals

If a two-sided quotient of `U(L)` is module-finite over the coefficient ring and `L` is
module-finite, quotients by all powers of the ideal are module-finite as well. Each Lie generator
satisfies a monic relation in the original finite quotient. Raising that polynomial gives a
monic relation modulo the ideal's power, and ordered PBW spanning then gives module-finiteness.

Over a field this says that every power of a cofinite two-sided ideal is cofinite. It is useful
when refining a representation kernel to an ideal stable under derivations, while retaining a
finite-dimensional quotient on which to represent the Lie algebra.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- If monic polynomials `p i` evaluated at a spanning family of Lie generators lie in `I`,
then modulo `I^n` the ordered products with exponents below the degrees of `p i ^ n` span.
These bounds give an explicit finite spanning family for the quotient. -/
theorem span_range_quotient_pow_orderedPowerProducts_eq_top {d : ℕ} (e : Fin d → L)
    (he : Submodule.span R (Set.range e) = ⊤) (I : Ideal U) [I.IsTwoSided]
    (p : Fin d → Polynomial R) (hp : ∀ i, (p i).Monic)
    (hI : ∀ i, Polynomial.aeval (_root_.UniversalEnvelopingAlgebra.ι R (e i)) (p i) ∈ I)
    (n : ℕ) :
    Submodule.span R (Set.range fun c : ∀ i, Fin ((p i ^ n).natDegree) ↦
      ((List.finRange d).map fun i ↦
        Ideal.Quotient.mk (I ^ n) (_root_.UniversalEnvelopingAlgebra.ι R (e i)) ^
          (c i : ℕ)).prod) = ⊤ := by
  apply span_range_bounded_orderedPowerProducts_eq_top R L R e he
    (Ideal.Quotient.mkₐ R (I ^ n)) Ideal.Quotient.mk_surjective (fun i ↦ p i ^ n)
    (fun i ↦ (hp i).pow n)
  intro i
  rw [Polynomial.aeval_algHom_apply, map_pow, map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (hI i) n)

/-- Monic relations modulo a two-sided ideal for a finite spanning family of `L` imply that
quotients by every power of the ideal are module-finite. -/
theorem moduleFinite_quotient_pow_of_isIntegral {d : ℕ} (e : Fin d → L)
    (he : Submodule.span R (Set.range e) = ⊤) (I : Ideal U) [I.IsTwoSided]
    (hI : ∀ i, IsIntegral R (Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι R (e i))))
    (n : ℕ) : Module.Finite R (U ⧸ I ^ n) := by
  exact moduleFinite_of_isIntegral_of_span_eq_top R L R e he
    (Ideal.Quotient.mkₐ R (I ^ n)) Ideal.Quotient.mk_surjective
    fun i ↦ isIntegral_quotient_pow_of_isIntegral_quotient _ (hI i) n

/-- Every power of a two-sided ideal with module-finite quotient has module-finite quotient,
provided the Lie algebra is module-finite. The coefficient ring need not be a field or
Noetherian. -/
theorem moduleFinite_quotient_pow [Module.Finite R L] (I : Ideal U) [I.IsTwoSided]
    [Module.Finite R (U ⧸ I)] (n : ℕ) : Module.Finite R (U ⧸ I ^ n) := by
  obtain ⟨d, e, he⟩ := Module.Finite.exists_fin (R := R) (M := L)
  exact moduleFinite_quotient_pow_of_isIntegral R L e he I
    (fun i ↦ IsIntegral.of_finite R _) n

end TauCeti.UniversalEnvelopingAlgebra
