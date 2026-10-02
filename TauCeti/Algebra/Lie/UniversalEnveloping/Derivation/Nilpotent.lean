/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic
public import TauCeti.Algebra.Lie.Derivation.LocallyNilpotent
public import TauCeti.Algebra.Lie.Derivation.Quotient
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Nilpotent derivations on finite enveloping quotients

A locally nilpotent Lie derivation lifts to a locally nilpotent derivation of the universal
enveloping algebra. On any stable quotient that is Noetherian as a module over the coefficient
ring, the induced derivation is nilpotent with a uniform bound. In particular this applies to
finite-dimensional stable quotients over a field.

The enveloping algebra itself need not have a uniform bound: in characteristic zero,
the lift of `x ↦ y, y ↦ 0` on a two-dimensional abelian Lie algebra is `y ∂/∂x`
on the polynomial algebra and has no uniform nilpotence bound.
The finite-quotient statement supplies the derivation part of the multiplication-plus-derivation
representations of split Lie extensions.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  Proposition E.5, for nilpotent derivations on finite enveloping quotients.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Powers of a lifted derivation agree on canonical generators with powers of the original
Lie derivation. -/
theorem envelopingDerivation_pow_apply_ι (D : LieDerivation R L L) (n : ℕ) (x : L) :
    ((envelopingDerivation R L D : Module.End R U) ^ n)
        (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R ((D.toLinearMap ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, envelopingDerivation_ι,
      pow_succ', Module.End.mul_apply]
    simp only [LieDerivation.coeFn_coe]

/-- A Lie derivation that kills each vector after finitely many iterations has a locally
nilpotent lift to the enveloping algebra. No finiteness assumption on the Lie algebra is needed. -/
theorem exists_envelopingDerivation_pow_apply_eq_zero (D : LieDerivation R L L)
    (hD : ∀ x : L, ∃ n : ℕ, (D.toLinearMap ^ n) x = 0) (a : U) :
    ∃ n : ℕ, ((envelopingDerivation R L D : Module.End R U) ^ n) a = 0 := by
  apply derivationLieAlgebra.exists_pow_apply_eq_zero_of_mem_adjoin
    (envelopingDerivation R L D) (s := Set.range (_root_.UniversalEnvelopingAlgebra.ι R))
  · rintro _ ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := hD x
    exact ⟨n, by rw [envelopingDerivation_pow_apply_ι, hn, map_zero]⟩
  · rw [adjoin_range_ι]
    exact Algebra.mem_top

/-- A locally nilpotent Lie derivation induces a nilpotent operator on every stable enveloping
quotient that is Noetherian as a module over the coefficient ring. -/
theorem isNilpotent_envelopingDerivation_quotient (D : LieDerivation R L L)
    (hD : ∀ x : L, ∃ n : ℕ, (D.toLinearMap ^ n) x = 0)
    (J : Ideal U) [J.IsTwoSided] [IsNoetherian R (U ⧸ J)]
    (hJ : envelopingDerivation R L D ∈ stableDerivations R (J.restrictScalars R)) :
    IsNilpotent (derivationQuotientHom R J ⟨envelopingDerivation R L D, hJ⟩ :
      Module.End R (U ⧸ J)) := by
  let δ : Module.End R (U ⧸ J) :=
    derivationQuotientHom R J ⟨envelopingDerivation R L D, hJ⟩
  have hlocal (q : U ⧸ J) : ∃ n : ℕ, (δ ^ n) q = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨n, hn⟩ := exists_envelopingDerivation_pow_apply_eq_zero R L D hD a
    refine ⟨n, ?_⟩
    have hcomm : Function.Semiconj (Ideal.Quotient.mk J)
        (envelopingDerivation R L D : Module.End R U) δ :=
      fun a ↦ (derivationQuotientHom_apply_mk R J
        ⟨envelopingDerivation R L D, hJ⟩ a).symm
    simpa only [← Module.End.pow_apply, hn, map_zero] using (hcomm.iterate_right n a).symm
  -- The increasing kernels stabilize on a Noetherian module, providing one bound for all
  -- quotient classes rather than a bound depending on a chosen representative.
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp δ.eventually_iSup_ker_pow_eq
  refine ⟨n, LinearMap.ext fun q ↦ ?_⟩
  obtain ⟨k, hk⟩ := hlocal q
  have hq : q ∈ ⨆ m, LinearMap.ker (δ ^ m) :=
    Submodule.mem_iSup_of_mem k (LinearMap.mem_ker.mpr hk)
  rw [hn n le_rfl] at hq
  exact LinearMap.mem_ker.mp hq

end TauCeti.UniversalEnvelopingAlgebra
