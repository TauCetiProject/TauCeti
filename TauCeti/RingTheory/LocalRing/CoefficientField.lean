/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Coefficient fields of complete local rings

Let `R` be a local ring which is complete for the adic topology of its maximal ideal `𝔪`, and let
`k → R` be a ring homomorphism such that the residue field `R ⧸ 𝔪` is formally étale over `k`; the
main case is a field `k` over which `R ⧸ 𝔪` is separable (`Algebra.FormallyEtale.of_isSeparable`).
Then reduction `R → R ⧸ 𝔪` has a unique `k`-algebra section: the residue field lifts to a
*coefficient field* of `R` containing the image of `k`.

Existence is Hensel's lemma in the guise of formal smoothness: the identity of `R ⧸ 𝔪` lifts along
the `𝔪`-adically complete ring `R` (`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`).
Uniqueness only needs formal unramifiedness and the Krull intersection `⋂ 𝔪 ^ n = 0`.

Without separability the section need not exist over `k`: in `𝔽_p(s)[[T]]`, viewed as an
`𝔽_p(u)`-algebra through `u ↦ s ^ p + T`, a section would send `s` to a `p`-th root of `s ^ p + T`,
and there is none, since every `p`-th power in `𝔽_p(s)[[T]]` is a power series in `T ^ p`.

In the theory of algebraic function fields this is the device that turns the completion of the
function field at a place with residue field `F_P` into a field of Laurent series over `F_P`, and
so gives `F_P`-valued expansion coefficients and residues at places that are not rational.

## Main definitions

* `TauCeti.residueFieldSection`: the coefficient field, as a `k`-algebra map
  `ResidueField R →ₐ[k] R`.

## Main results

* `TauCeti.residue_residueFieldSection`: it is a section of reduction.
* `TauCeti.eq_residueFieldSection`: it is the only `k`-algebra section of reduction.

## References

* I. S. Cohen, *On the structure and ideal theory of complete local rings*, Trans. Amer. Math.
  Soc. 59 (1946), 54–106.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

public section

namespace TauCeti

open IsLocalRing

variable (k R : Type*) [CommRing k] [CommRing R] [IsLocalRing R] [Algebra k R]
  [IsAdicComplete (maximalIdeal R) R]

/-- The **coefficient field** of a complete local `k`-algebra `R` whose residue field is formally
smooth over `k` (for instance a field separable over a field `k`): a `k`-algebra section
`ResidueField R →ₐ[k] R` of reduction (`TauCeti.residue_residueFieldSection`). When the residue
field is moreover formally unramified over `k` it is the only one
(`TauCeti.eq_residueFieldSection`). -/
noncomputable def residueFieldSection [Algebra.FormallySmooth k (ResidueField R)] :
    ResidueField R →ₐ[k] R :=
  (Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (AlgHom.id k (ResidueField R))).choose

/-- The coefficient field is a section of reduction. -/
@[simp]
theorem residue_residueFieldSection [Algebra.FormallySmooth k (ResidueField R)]
    (a : ResidueField R) : residue R (residueFieldSection k R a) = a :=
  -- `residue R` is the quotient map by `𝔪`, which `Ideal.Quotient.mkₐ k` bundles over `k`.
  AlgHom.congr_fun (Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (AlgHom.id k (ResidueField R))).choose_spec a

/-- The coefficient field is the only `k`-algebra section of reduction when the residue field is
formally étale over `k`. Uniqueness uses only the Krull intersection `⋂ 𝔪 ^ n = 0`. -/
theorem eq_residueFieldSection [Algebra.FormallySmooth k (ResidueField R)]
    [Algebra.FormallyUnramified k (ResidueField R)]
    {s : ResidueField R →ₐ[k] R} (hs : ∀ a, residue R (s a) = a) :
    s = residueFieldSection k R := by
  have hI : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ := by
    simpa only [smul_eq_mul, Ideal.mul_top] using
      (IsAdicComplete.toIsHausdorff (I := maximalIdeal R) (M := R)).iInf_pow_smul
  -- As above, `residue R` is the quotient map `Ideal.Quotient.mk (maximalIdeal R)`.
  exact Algebra.FormallyUnramified.ext_of_iInf _ hI fun a ↦
    (hs a).trans (residue_residueFieldSection k R a).symm

end TauCeti
