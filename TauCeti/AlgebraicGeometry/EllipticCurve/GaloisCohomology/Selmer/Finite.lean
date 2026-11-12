/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Finiteness
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.FixingSubgroup
-- Proof-only: good reduction outside a finite set of primes.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere
-- Proof-only: the canonical scalar towers between completions of number fields.
import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion

/-!
# Finiteness of Selmer groups of elliptic curves

For an elliptic curve `W` over a number field `K` and a nonzero natural number `m`, the
`m`-Selmer group of `W` is finite (Silverman X.4.2). Here the local conditions are taken at the
completions of `K` at its finite places.

The proof passes to the division field `L = K(E[m])`. Restriction to `L` has finite kernel, and
the local condition over each completion `L_w` lies over the condition at the completion `K_v`
below it. Over `L`, every `m`-torsion point is rational, so the Weil pairing embeds the classes
unramified outside a finite set into finitely many copies of the finite Kummer group `L(S, m)`.

## Main result

* `WeierstrassCurve.finite_selmerGroup`: the `m`-Selmer group of an elliptic curve over a number
  field is finite for `m ≠ 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1 and X.4.2.
-/

public section

noncomputable section

namespace WeierstrassCurve

open IsDedekindDomain NumberField TauCeti
open scoped AdicCompletionExtension NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- A choice of separable-closure embeddings for all finite completions of a number field. -/
private def completionSeparableClosureEmbeddings (F : Type*) [Field F] [NumberField F] :
    ∀ v : HeightOneSpectrum (𝓞 F),
      SeparableClosure F →ₐ[F] SeparableClosure (v.adicCompletion F) :=
  fun _ ↦ IsSepClosed.lift

/-- **The `m`-Selmer group of an elliptic curve over a number field is finite** (Silverman
X.4.2). The local conditions are the images of the Kummer maps over the completions at all finite
places. The conclusion holds for every nonzero natural number `m`. -/
theorem finite_selmerGroup [W.IsElliptic] (m : ℕ) [NeZero m]
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)) :
    Finite (W.selmerGroup τ m) := by
  classical
  let _ : NumberField (W.divisionField m) :=
    NumberField.of_module_finite K (W.divisionField m)
  let W' := W⁄(W.divisionField m)
  let below : HeightOneSpectrum (𝓞 (W.divisionField m)) → HeightOneSpectrum (𝓞 K) :=
    fun w ↦ w.under (𝓞 K)
  let τL := completionSeparableClosureEmbeddings (W.divisionField m)
  obtain ⟨S, -, hgood, -⟩ :=
    exists_finset_isElliptic_integralModel_adicCompletion (𝓞 (W.divisionField m)) W'
      (Nat.cast_ne_zero.2 (NeZero.ne m)) ∅
  apply W.finite_selmerGroup_of_finite_selmerGroup_divisionField m τ τL below
  apply W'.finite_selmerGroup_of_forall_smul_eq (S := (S : Set _)) S.finite_toSet
    hgood (NeZero.ne m)
  exact W.forall_smul_eq_torsionCoeff_divisionField m

end WeierstrassCurve
