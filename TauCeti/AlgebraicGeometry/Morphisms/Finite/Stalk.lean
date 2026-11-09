/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import TauCeti.RingTheory.Localization.FiniteFiber
import Mathlib.Tactic.Algebraize

/-!
# Finite stalk maps at singleton fibres

A finite morphism induces a finite homomorphism on stalks at a point whose fibre consists of
that point alone. The singleton hypothesis matters: in general, localizing the source of a
finite algebra at just one of several primes over the same base prime need not preserve
finiteness over the localized base.

This supplies the finite local homomorphism obtained after isolating a point by elementary
étale localization in the proof of purity of the branch locus.

## References

* The Stacks Project, proof of Lemma 58.21.4 (Tag 0BMB).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A finite morphism has a finite stalk map at a point which is the only point in its fibre.
No Noetherian, reducedness or normality hypotheses are required. -/
theorem finite_stalkMap_of_unique_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (h : ∀ x' : X, f x' = f x → x' = x) : (f.stalkMap x).hom.Finite := by
  obtain ⟨U, hU', hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := ⊤) (x := f x) trivial
  -- Membership in the affine-open basis is the predicate `IsAffineOpen`.
  have hU : IsAffineOpen U := hU'
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  have hxV : x ∈ V := hxU
  have e : V ≤ f ⁻¹ᵁ U := le_rfl
  have hfin : (f.appLE U V e).hom.Finite := by
    rw [← f.app_eq_appLE]
    exact f.finite_app U hU
  algebraize [(f.appLE U V e).hom]
  set p := (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hqp : q.under Γ(Y, U) = p :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hxV)
  have : q.LiesOver p := ⟨hqp.symm⟩
  have huniq (q' : Ideal Γ(X, V)) (hq' : q'.IsPrime) (hqp' : q'.LiesOver p) : q' = q := by
    let z : V := hV.isoSpec.inv ⟨q', hq'⟩
    have hz : hV.primeIdealOf z = ⟨q', hq'⟩ := by
      exact Scheme.inv_hom_apply hV.isoSpec ⟨q', hq'⟩
    have hfz : hU.primeIdealOf ⟨f z, z.2⟩ = hU.primeIdealOf ⟨f x, hxU⟩ := by
      apply PrimeSpectrum.ext
      rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e z.2]
      simp only [Subtype.eta]
      rw [hz]
      exact (q'.over_def p).symm
    have hzx : (z : X) = x := h z <| by
      simpa only [IsAffineOpen.fromSpec_primeIdealOf] using congrArg hU.fromSpec hfz
    have hz' : z = ⟨x, hxV⟩ := Subtype.ext hzx
    exact congrArg PrimeSpectrum.asIdeal (hz.symm.trans (congrArg hV.primeIdealOf hz'))
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := p.finite_localizationAtPrime_of_unique_liesOver q huniq
    (Localization.AtPrime p) (Localization.AtPrime q)
  rw [RingHom.finite_respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV e hxV)]
  -- The algebra map between the prime localizations is precisely the local ring map in this
  -- affine description of the stalk map.
  exact (RingHom.finite_algebraMap).mpr
    (inferInstance : Module.Finite (Localization.AtPrime p) (Localization.AtPrime q))

end AlgebraicGeometry.Scheme.Hom
