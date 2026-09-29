/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Spec
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The grading of a resolvent with a homogeneous invariant

If the invariant `Φ` of a resolvent specification is homogeneous of degree `m`, so is every
element of its rename-orbit, and the coefficient of `X ^ k` in the universal resolvent is
homogeneous of degree `m * ([Sₙ : H] - k)`. The integral orbit product rewrites that coefficient
in the elementary symmetric polynomials, and it is therefore weighted homogeneous of the same
weight once the variable `i`, which stands for `eᵢ₊₁`, is given the weight `i + 1`.

This grading is what makes a specialization at a sparse polynomial computable. Specializing at
`f` substitutes the signed coefficients of `f` for the variables, so a variable whose coefficient
vanishes kills every monomial containing it, and the weight leaves only finitely many exponents
of the surviving variables, each with an integral coefficient independent of `f`.

## Main results

* `MvPolynomial.isHomogeneous_universalResolvent_coeff`: the coefficients of the universal
  resolvent of a homogeneous invariant are homogeneous.
* `TauCeti.ResolventSpec.isWeightedHomogeneous_orbitProduct_coeff`: the coefficients of the
  integral orbit product are weighted homogeneous for the weights `i + 1`.
-/

public section

namespace MvPolynomial

/-- If `Φ` is homogeneous of degree `m`, the coefficient of `X ^ k` in its universal resolvent is
homogeneous of degree `m` times the number of orbit elements left over. -/
theorem isHomogeneous_universalResolvent_coeff {n : ℕ} {Φ : MvPolynomial (Fin n) ℤ} {m : ℕ}
    (hΦ : Φ.IsHomogeneous m) (k : ℕ) :
    ((universalResolvent Φ).coeff k).IsHomogeneous (m * ((renameOrbit Φ).card - k)) := by
  rw [universalResolvent_def]
  refine isHomogeneous_coeff_prod_X_sub_C _ _ (fun Ψ hΨ => ?_) k
  obtain ⟨σ, rfl⟩ := (mem_renameOrbit Φ Ψ).mp hΨ
  exact hΦ.rename_isHomogeneous

end MvPolynomial

namespace TauCeti.ResolventSpec

open MvPolynomial

/-- **The grading of the orbit product.** If the invariant of a specification is homogeneous of
degree `m`, the coefficient of `X ^ k` in its integral orbit product is weighted homogeneous of
weight `m * ([Sₙ : H] - k)`, the variable `i` having the weight `i + 1` of the elementary
symmetric polynomial `eᵢ₊₁` it stands for. -/
theorem isWeightedHomogeneous_orbitProduct_coeff {n : ℕ} (spec : ResolventSpec n) {m : ℕ}
    (hΦ : spec.Φ.IsHomogeneous m) (k : ℕ) :
    (spec.orbitProduct.coeff k).IsWeightedHomogeneous (fun i : Fin n => (i : ℕ) + 1)
      (m * (spec.H.index - k)) := by
  have hhom : esymmSubst n = (aeval fun i : Fin n => esymm (Fin n) ℤ ((i : ℕ) + 1)).toRingHom :=
    ringHom_ext' (RingHom.ext_int _ _) fun i => by simp
  have hsubst (p : MvPolynomial (Fin n) ℤ) :
      esymmSubst n p = aeval (fun i : Fin n => esymm (Fin n) ℤ ((i : ℕ) + 1)) p := by
    rw [hhom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  refine isWeightedHomogeneous_of_isHomogeneous_aeval (fun i => isHomogeneous_esymm _)
    (fun p q h => esymmSubst_injective n (by rwa [hsubst, hsubst])) ?_
  have h := congrArg (fun p => p.coeff k) spec.orbitProduct_esymm
  simp only [Polynomial.coeff_map] at h
  rw [← hsubst, h, ← card_renameOrbit]
  exact isHomogeneous_universalResolvent_coeff hΦ k

end TauCeti.ResolventSpec
