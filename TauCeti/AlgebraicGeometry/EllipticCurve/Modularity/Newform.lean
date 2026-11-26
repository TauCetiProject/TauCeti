/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic

/-!
# Newforms attached to an elliptic curve over `ℚ`

A weight-two newform `F` of level `M` is *attached* to a Weierstrass curve `E` over `ℚ`
(`WeierstrassCurve.IsNewformOf`) when `F` has trivial nebentypus and its Fourier coefficient
`a_ℓ(F)` equals the coefficient `a_ℓ(E)` of the `L`-function of `E` (Mathlib's
`WeierstrassCurve.LFunction`) at all but finitely many primes `ℓ`. This is the coefficient
relation (4.6.4) of Serre's paper on modular Galois representations. The predicate neither
fixes the level `M`, nor says anything at the finitely many exceptional primes, nor asserts that
an attached newform exists.

Strong multiplicity one across levels (Miyake, Theorem 4.6.19, for two trivial nebentypes)
makes an attached newform unique: two newforms attached to the same curve have the same level
and the same underlying function, hence the same Fourier coefficient at every index, and at a
fixed level they are equal. The predicate only sees `a_ℓ(E)` at almost all primes, so curves
whose coefficients agree at almost all primes (for instance isogenous curves) have the same
attached newforms; conversely, curves sharing an attached newform have the same coefficients at
almost all primes.

## Main definitions

* `WeierstrassCurve.IsNewformOf`: the newform `F` is attached to the curve `E`.

## Main results

* `WeierstrassCurve.isNewformOf_iff_exists_finset`: attachment with an explicit finite set of
  exceptional primes.
* `WeierstrassCurve.isNewformOf_iff_eventually_eigenvalue_eq`: attachment through the Hecke
  eigenvalues at the primes not dividing the level.
* `WeierstrassCurve.IsNewformOf.level_eq_and_coe_eq`: two attached newforms have the same level
  and are the same function on the upper half-plane.
* `WeierstrassCurve.IsNewformOf.qExpansion_coeff_eq`: two attached newforms have the same Fourier
  coefficient at every index.
* `WeierstrassCurve.IsNewformOf.eq`: two attached newforms of the same level are equal.
* `WeierstrassCurve.isNewformOf_congr`: curves whose coefficients agree at almost all primes have
  the same attached newforms.

## References

* J.-P. Serre, *Sur les représentations modulaires de degré 2 de Gal(Qbar/Q)*, Duke Math. J. 54
  (1987), 179–230, §4.6, (4.6.4), p. 208.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.19.
-/

public section

open Filter UpperHalfPlane HeckeRing.GL2

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) {M M' : ℕ} [NeZero M] [NeZero M']

/-- **A newform attached to an elliptic curve over `ℚ`.** The weight-two newform `F` of level `M`
is attached to `E` when its nebentypus is trivial and its Fourier coefficient `a_ℓ(F)` equals the
coefficient `a_ℓ(E)` of the `L`-function of `E` at all but finitely many primes `ℓ`. The level
`M` is arbitrary, and nothing is required at the finitely many exceptional primes. -/
def IsNewformOf (F : Newform M 2) : Prop :=
  F.χ = 1 ∧ ∀ᶠ ℓ : ℕ in cofinite, ℓ.Prime →
    (qExpansion 1 F.toCuspForm).coeff ℓ = (E.LFunction ℓ : ℂ)

variable {E}

/-- The defining property of an attached newform. -/
theorem isNewformOf_iff {F : Newform M 2} :
    E.IsNewformOf F ↔ F.χ = 1 ∧ ∀ᶠ ℓ : ℕ in cofinite, ℓ.Prime →
      (qExpansion 1 F.toCuspForm).coeff ℓ = (E.LFunction ℓ : ℂ) :=
  Iff.rfl

/-- **Attachment with an explicit exceptional set**: `F` is attached to `E` exactly when its
nebentypus is trivial and `a_ℓ(F) = a_ℓ(E)` at every prime `ℓ` outside some finite set. -/
theorem isNewformOf_iff_exists_finset {F : Newform M 2} :
    E.IsNewformOf F ↔ F.χ = 1 ∧ ∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      (qExpansion 1 F.toCuspForm).coeff ℓ = (E.LFunction ℓ : ℂ) := by
  rw [isNewformOf_iff]
  refine and_congr_right fun _ ↦
    ⟨fun h ↦ ⟨(eventually_cofinite.mp h).toFinset, fun ℓ hℓ hℓS ↦ by simpa [hℓ] using hℓS⟩,
      fun ⟨S, hS⟩ ↦ S.eventually_cofinite_notMem.mono fun ℓ hℓS hℓ ↦ hS ℓ hℓ hℓS⟩

/-- **Attachment through the Hecke eigenvalues**: `F` is attached to `E` exactly when its
nebentypus is trivial and its eigenvalue `λ_ℓ(F)` equals `a_ℓ(E)` at all but finitely many
primes `ℓ` not dividing the level. -/
theorem isNewformOf_iff_eventually_eigenvalue_eq {F : Newform M 2} :
    E.IsNewformOf F ↔ F.χ = 1 ∧ ∀ᶠ ℓ : ℕ in cofinite, ∀ (hℓ : ℓ.Prime) (hℓM : ℓ.Coprime M),
      F.eigenvalue ⟨ℓ, hℓ.pos⟩ hℓM = (E.LFunction ℓ : ℂ) := by
  rw [isNewformOf_iff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ h.mono fun ℓ hℓ hp hℓM ↦ ?_, fun h ↦ ?_⟩
  · rw [← hℓ hp, ← F.qExpansion_coeff_eq_eigenvalue ⟨ℓ, hp.pos⟩ hℓM, PNat.mk_coe]
  · -- only the finitely many prime divisors of `M` are not coprime to `M`
    filter_upwards [h, M.primeFactors.eventually_cofinite_notMem] with ℓ hℓ hℓM hp
    have hcop : ℓ.Coprime M :=
      hp.coprime_iff_not_dvd.mpr fun hdvd ↦ hℓM (Nat.mem_primeFactors.mpr ⟨hp, hdvd, NeZero.ne M⟩)
    rw [← hℓ hp hcop, ← F.qExpansion_coeff_eq_eigenvalue ⟨ℓ, hp.pos⟩ hcop, PNat.mk_coe]

namespace IsNewformOf

variable {F : Newform M 2} {F' : Newform M' 2}

/-- An attached newform has trivial nebentypus. In particular, a newform with nontrivial
nebentypus is attached to no elliptic curve over `ℚ`. -/
theorem χ_eq_one (h : E.IsNewformOf F) : F.χ = 1 :=
  (isNewformOf_iff.mp h).1

/-- The Fourier coefficients of an attached newform at almost all primes are those of the
`L`-function of the curve. -/
theorem eventually_qExpansion_coeff_eq (h : E.IsNewformOf F) :
    ∀ᶠ ℓ : ℕ in cofinite, ℓ.Prime →
      (qExpansion 1 F.toCuspForm).coeff ℓ = (E.LFunction ℓ : ℂ) :=
  (isNewformOf_iff.mp h).2

/-- The Hecke eigenvalues of an attached newform at almost all primes not dividing the level are
the coefficients of the `L`-function of the curve. -/
theorem eventually_eigenvalue_eq (h : E.IsNewformOf F) :
    ∀ᶠ ℓ : ℕ in cofinite, ∀ (hℓ : ℓ.Prime) (hℓM : ℓ.Coprime M),
      F.eigenvalue ⟨ℓ, hℓ.pos⟩ hℓM = (E.LFunction ℓ : ℂ) :=
  (isNewformOf_iff_eventually_eigenvalue_eq.mp h).2

/-- **Uniqueness of the attached newform across levels.** Two newforms attached to the same curve
have the same level and are the same function on the upper half-plane. This is strong
multiplicity one across levels (Miyake, Theorem 4.6.19) for two trivial nebentypes: the
eigenvalues of both newforms at almost all good primes are the coefficients of the curve. -/
theorem level_eq_and_coe_eq (h : E.IsNewformOf F) (h' : E.IsNewformOf F') :
    M = M' ∧ ⇑F.toCuspForm = ⇑F'.toCuspForm := by
  obtain ⟨hχ, S, hS⟩ := isNewformOf_iff_exists_finset.mp h
  obtain ⟨hχ', S', hS'⟩ := isNewformOf_iff_exists_finset.mp h'
  refine Newform.level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq F F'
    (by rw [hχ, hχ', MonoidHom.one_comp, MonoidHom.one_comp]) (S := S ∪ S')
    fun p hp hpM hpM' hpS ↦ ?_
  rw [Finset.mem_union, not_or] at hpS
  rw [← F.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpM,
    ← F'.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpM', PNat.mk_coe, hS p hp hpS.1,
    hS' p hp hpS.2]

/-- Two newforms attached to the same curve have the same level. -/
theorem level_eq (h : E.IsNewformOf F) (h' : E.IsNewformOf F') : M = M' :=
  (h.level_eq_and_coe_eq h').1

/-- Two newforms attached to the same curve have the same Fourier coefficient at every index,
the indices dividing either level included. -/
theorem qExpansion_coeff_eq (h : E.IsNewformOf F) (h' : E.IsNewformOf F') (n : ℕ) :
    (qExpansion 1 F.toCuspForm).coeff n = (qExpansion 1 F'.toCuspForm).coeff n := by
  rw [(h.level_eq_and_coe_eq h').2]

/-- **Uniqueness of the attached newform at a fixed level**: two newforms of the same level
attached to the same curve are equal. Across levels, `IsNewformOf.level_eq` first identifies the
levels. -/
theorem eq {F F' : Newform M 2} (h : E.IsNewformOf F) (h' : E.IsNewformOf F') : F = F' :=
  Newform.ext <| CuspForm.ext <| congrFun (h.level_eq_and_coe_eq h').2

/-- Two curves sharing an attached newform have the same `L`-function coefficient at almost all
primes. -/
theorem eventually_LFunction_eq {E' : WeierstrassCurve ℚ} (h : E.IsNewformOf F)
    (h' : E'.IsNewformOf F) :
    ∀ᶠ ℓ : ℕ in cofinite, ℓ.Prime → E.LFunction ℓ = E'.LFunction ℓ := by
  filter_upwards [h.eventually_qExpansion_coeff_eq, h'.eventually_qExpansion_coeff_eq]
    with ℓ hℓ hℓ' hp
  exact_mod_cast (hℓ hp).symm.trans (hℓ' hp)

end IsNewformOf

/-- **Attachment depends only on the coefficients at almost all primes.** If two curves over `ℚ`
have the same `L`-function coefficient at all but finitely many primes, as isogenous curves do,
then a newform is attached to one exactly when it is attached to the other. -/
theorem isNewformOf_congr {E' : WeierstrassCurve ℚ}
    (hE : ∀ᶠ ℓ : ℕ in cofinite, ℓ.Prime → E.LFunction ℓ = E'.LFunction ℓ) {F : Newform M 2} :
    E.IsNewformOf F ↔ E'.IsNewformOf F := by
  -- each direction transports the almost-everywhere agreement through `hE`
  have key {E₁ E₂ : WeierstrassCurve ℚ}
      (h₁₂ : ∀ᶠ ℓ : ℕ in cofinite, ℓ.Prime → E₁.LFunction ℓ = E₂.LFunction ℓ)
      (h : E₁.IsNewformOf F) : E₂.IsNewformOf F := by
    refine isNewformOf_iff.mpr ⟨h.χ_eq_one, ?_⟩
    filter_upwards [h.eventually_qExpansion_coeff_eq, h₁₂] with ℓ hℓ hℓ₁₂ hp
    rw [hℓ hp, hℓ₁₂ hp]
  exact ⟨key hE, key (hE.mono fun ℓ hℓ hp ↦ (hℓ hp).symm)⟩

end WeierstrassCurve
