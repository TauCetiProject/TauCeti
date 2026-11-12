/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-!
# Naturality of polynomial exponentials

The exponential of a tangent vector with locally nilpotent invariant vector field commutes
with morphisms of affine monoids. The comparison holds for the polynomial coordinate maps,
and hence for their one-parameter homomorphisms over every commutative value algebra.

Local nilpotence is invariant under bialgebra isomorphisms, so automorphism equivariance
requires no additional nilpotence hypothesis on the transported tangent vector. In particular,
conjugating a tangent vector and then exponentiating gives the conjugate exponential curve.
These intrinsic comparisons allow exponential curves to be transported between coordinate
models without choosing a common matrix realization.

The proofs use `BialgHom.map_leftInvariantDerivation`, `Derivation.map_taylorExp`, and
the coefficient formula for `TauCeti.Bialgebra.expPointPolynomial`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Chapter 1.
-/

public section

open TauCeti TauCeti.Bialgebra Polynomial

namespace BialgHom

variable {R H K : Type*} [CommRing R] [CommRing H] [CommRing K]
  [Bialgebra R H] [Bialgebra R K] [Algebra ℚ H] [Algebra ℚ K]

/-- Polynomial exponential curves commute with a morphism of affine monoids, whenever
the two related invariant vector fields are locally nilpotent. This is an equality of
coordinate maps, and therefore also applies to nonreduced value algebras. -/
theorem expPointPolynomial_comp (f : H →ₐc[R] K)
    (d : Derivation R K (CounitAlgebra R K R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    (hdf : ∀ x, ∃ n, (leftInvariantDerivation (derivationComp f d))^[n] x = 0) :
    (expPointPolynomial d hd).comp f.toAlgHom =
      expPointPolynomial (derivationComp f d) hdf := by
  ext x n
  simp only [AlgHom.comp_apply, coeff_expPointPolynomial, BialgHom.coe_toAlgHom]
  rw [← f.map_iterate_leftInvariantDerivation d n x, ← map_rat_smul f,
    CoalgHomClass.counit_comp_apply]

/-- The exponential point commutes with a morphism of affine monoids and its differential. -/
theorem expPoint_comp (f : H →ₐc[R] K)
    (d : Derivation R K (CounitAlgebra R K R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    (hdf : ∀ x, ∃ n, (leftInvariantDerivation (derivationComp f d))^[n] x = 0) :
    (expPoint d hd).comp f.toAlgHom = expPoint (derivationComp f d) hdf := by
  ext x
  simp only [AlgHom.comp_apply, expPoint_apply, BialgHom.coe_toAlgHom]
  have ht := (leftInvariantDerivation (derivationComp f d)).map_taylorExp hdf
    (leftInvariantDerivation d) hd f (f.map_leftInvariantDerivation d) x
  rw [← ht]
  exact CoalgHomClass.counit_comp_apply f _

/-- Naturality of the exponential curve at every parameter in every commutative value algebra. -/
theorem mapDomain_expPointAt (f : H →ₐc[R] K)
    (d : Derivation R K (CounitAlgebra R K R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    (hdf : ∀ x, ∃ n, (leftInvariantDerivation (derivationComp f d))^[n] x = 0)
    {B : Type*} [CommRing B] [Algebra R B] (t : B) :
    mapDomain f (expPointAt d hd t) = expPointAt (derivationComp f d) hdf t := by
  apply WithConv.ext
  ext x
  simpa only [mapDomain_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    expPointAt_apply] using
    congrArg (aeval t) (AlgHom.congr_fun (f.expPointPolynomial_comp d hd hdf) x)

/-- The exponential one-parameter homomorphisms form a commuting square with the map on
points induced by a bialgebra morphism. -/
theorem mapDomain_comp_expPointHom (f : H →ₐc[R] K)
    (d : Derivation R K (CounitAlgebra R K R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    (hdf : ∀ x, ∃ n, (leftInvariantDerivation (derivationComp f d))^[n] x = 0)
    (B : Type*) [CommRing B] [Algebra R B] :
    (mapDomain (A := B) f).comp (expPointHom d hd B) =
      expPointHom (derivationComp f d) hdf B := by
  apply MonoidHom.ext
  intro t
  simp only [MonoidHom.comp_apply, expPointHom_apply]
  exact f.mapDomain_expPointAt d hd hdf t.toAdd

end BialgHom

namespace WithConv

open TauCeti.HopfAlgebra

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- Conjugation preserves local nilpotence of the invariant field of a tangent vector.
The tangent vector is transported by the differential of the actual conjugation map. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_pointConjugation
    (g : WithConv (H →ₐ[R] R)) (d : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0) :
    ∀ x, ∃ n, (leftInvariantDerivation
      (derivationComp (pointConjugationBialgEquiv g).toBialgHom d))^[n] x = 0 :=
  ((pointConjugationBialgEquiv g).exists_iterate_leftInvariantDerivation_eq_zero_iff d).mpr hd

variable [Algebra ℚ H]

/-- The polynomial exponential is equivariant for conjugation, over every commutative
value algebra and for every parameter. No matrix realization is chosen. -/
theorem expPointAt_pointConjugation (g : WithConv (H →ₐ[R] R))
    (d : Derivation R H (CounitAlgebra R H R))
    (hd : ∀ x, ∃ n, (leftInvariantDerivation d)^[n] x = 0)
    {B : Type*} [CommRing B] [Algebra R B] (t : B) :
    expPointAt (derivationComp (pointConjugationBialgEquiv g).toBialgHom d)
        (exists_iterate_leftInvariantDerivation_eq_zero_pointConjugation g d hd) t =
      AlgHom.mapValue (Algebra.ofId R B) g * expPointAt d hd t *
        (AlgHom.mapValue (Algebra.ofId R B) g)⁻¹ := by
  rw [← BialgHom.mapDomain_expPointAt,
    mapDomain_pointConjugationBialgEquiv]

end WithConv
