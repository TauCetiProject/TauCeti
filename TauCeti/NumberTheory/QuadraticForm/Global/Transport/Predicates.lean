/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transport
public import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
public import TauCeti.NumberTheory.QuadraticForm.Global.Transport.Basic

/-!
# Transporting localizations and local predicates of quadratic forms along field isomorphisms

Let `e : K ≃+* L` be a ring isomorphism of number fields, and let `f : V ≃ₛₗ[e] V'` be an
`e`-semilinear equivalence from a `K`-vector space to an `L`-vector space. A quadratic form `Q`
over `K` on `V` transports to the form `Q.transport f` over `L` on `V'`; taking for `V'` the group
`V` with `L` acting through `e⁻¹` recovers the form `e ∘ Q`.

This file compares the localizations of `Q.transport f` with those of `Q`. At a finite place `v`
of `K` and the corresponding place `w` of `L`, the isomorphism `adicCompletionCongr : K_v ≃+* L_w`
extending `e` identifies the localization of `Q.transport f` at `w` with the transport of the
localization of `Q` at `v` along the semilinear scalar extension `K_v ⊗[K] V ≃ L_w ⊗[L] V'` of `f`.
At a real place `w` of `K` and the corresponding real place of `L`, the two real embeddings agree
along `e`, and the localizations are identified by an `ℝ`-linear transport.

Since transport preserves anisotropy, representation of scalars, injective representation and
isometry, each of the four local predicates holds for transported forms exactly when it holds for
the original forms, after reindexing the places along `e`. This carries statements about local
behaviour of quadratic forms over one number field to an isomorphic copy, for instance to a copy
in another universe.

## Main results

* `QuadraticForm.atFinitePlace_transport`, `QuadraticForm.atRealPlace_transport`: the localization
  of a transported form at the place corresponding to `v` (resp. `w`) is the transport of the
  localization at `v` (resp. `w`).
* `QuadraticForm.isLocallyIsotropic_transport_iff`: local isotropy is invariant under transport.
* `QuadraticForm.locallyRepresentsScalar_transport_iff`: `Q.transport f` locally represents `e a`
  exactly when `Q` locally represents `a`.
* `QuadraticForm.locallyRepresents_transport_iff`,
  `QuadraticForm.locallyEquivalent_transport_iff`: local representation and local equivalence of
  two forms are invariant under transporting both.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
open scoped TensorProduct

namespace QuadraticForm

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {K L : Type*} [Field K] [Field L]
variable {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module L V']

section Localization

/-- Localization commutes with transport at a finite place: if `e : K ≃+* L` carries the
`v`-adic valuation to the `w`-adic valuation, the localization at `w` of `Q.transport f` is the
transport of the localization at `v` of `Q` along the scalar extension of `f` by the isomorphism
`adicCompletionCongr : K_v ≃+* L_w` extending `e`. -/
theorem atFinitePlace_transport [NumberField K] [NumberField L] {e : K ≃+* L}
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (he : ∀ x, w.valuation L (e x) = v.valuation K x) (Q : _root_.QuadraticForm K V)
    (f : V ≃ₛₗ[(e : K →+* L)] V') :
    (Q.transport f).atFinitePlace w =
      (Q.atFinitePlace v).transport
        (f.baseChangeₛₗ
          (τ := (adicCompletionCongr v w e he : v.adicCompletion K →+* w.adicCompletion L))
          fun r ↦ by simp) := by
  refine baseChange_ext fun x ↦ ?_
  rw [QuadraticMap.transport_apply, LinearEquiv.baseChangeₛₗ_symm_tmul]
  simp

/-- Localization commutes with transport at a real place: the localization of `Q.transport f` at
the real place of `L` corresponding to `w` is the transport of the localization of `Q` at `w`
along the `ℝ`-linear scalar extension of `f`, since the two real embeddings agree along `e`. -/
theorem atRealPlace_transport (e : K ≃+* L) (w : {w : InfinitePlace K // w.IsReal})
    (Q : _root_.QuadraticForm K V) (f : V ≃ₛₗ[(e : K →+* L)] V') :
    let _ : Algebra K ℝ := (embedding_of_isReal w.property).toAlgebra
    let _ : Algebra L ℝ :=
      (embedding_of_isReal (realEquivOfRingEquiv e w).property).toAlgebra
    (Q.transport f).atRealPlace (realEquivOfRingEquiv e w) =
      (Q.atRealPlace w).transport
        (f.baseChangeₛₗ (τ := RingHom.id ℝ) fun r ↦ by simp [RingHom.algebraMap_toAlgebra]) := by
  let : Algebra K ℝ := (embedding_of_isReal w.property).toAlgebra
  let : Algebra L ℝ := (embedding_of_isReal (realEquivOfRingEquiv e w).property).toAlgebra
  refine baseChange_ext fun x ↦ ?_
  simp

end Localization

section Predicates

variable [NumberField K] [NumberField L]

/-- A transported quadratic form is locally isotropic exactly when the original form is. -/
theorem isLocallyIsotropic_transport_iff (e : K ≃+* L) (Q : _root_.QuadraticForm K V)
    (f : V ≃ₛₗ[(e : K →+* L)] V') :
    (Q.transport f).IsLocallyIsotropic ↔ Q.IsLocallyIsotropic := by
  rw [isLocallyIsotropic_iff, isLocallyIsotropic_iff]
  refine and_congr ?_ ?_
  · refine ((equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).forall_congr fun v ↦ ?_).symm
    rw [atFinitePlace_transport (TauCeti.valuation_equivOfRingEquiv e v),
      QuadraticMap.anisotropic_transport_iff]
  · refine ((realEquivOfRingEquiv e).forall_congr fun w ↦ ?_).symm
    rw [atRealPlace_transport, QuadraticMap.anisotropic_transport_iff]

/-- A transported quadratic form `Q.transport f` locally represents `e a` exactly when `Q` locally
represents `a`. -/
theorem locallyRepresentsScalar_transport_iff (e : K ≃+* L) (Q : _root_.QuadraticForm K V)
    (f : V ≃ₛₗ[(e : K →+* L)] V') (a : K) :
    (Q.transport f).LocallyRepresentsScalar (e a) ↔ Q.LocallyRepresentsScalar a := by
  rw [locallyRepresentsScalar_iff, locallyRepresentsScalar_iff]
  refine and_congr ?_ ?_
  · refine ((equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).forall_congr fun v ↦ ?_).symm
    have he := TauCeti.valuation_equivOfRingEquiv e v
    rw [atFinitePlace_transport he, ← adicCompletionCongr_algebraMap he a]
    exact (QuadraticMap.represents_transport_map_iff _ _ _).symm
  · refine ((realEquivOfRingEquiv e).forall_congr fun w ↦ ?_).symm
    rw [atRealPlace_transport]
    convert (QuadraticMap.represents_transport_map_iff _ _ _).symm using 2
    simp

variable {W W' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module L W']

/-- Transporting two quadratic forms along the same field isomorphism preserves local
representation of one by the other. -/
theorem locallyRepresents_transport_iff (e : K ≃+* L) (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (f₁ : V ≃ₛₗ[(e : K →+* L)] V')
    (f₂ : W ≃ₛₗ[(e : K →+* L)] W') :
    (Q.transport f₁).LocallyRepresents (R.transport f₂) ↔ Q.LocallyRepresents R := by
  rw [locallyRepresents_iff, locallyRepresents_iff]
  refine and_congr ?_ ?_
  · refine ((equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).forall_congr fun v ↦ ?_).symm
    rw [atFinitePlace_transport (TauCeti.valuation_equivOfRingEquiv e v),
      atFinitePlace_transport (TauCeti.valuation_equivOfRingEquiv e v),
      QuadraticMap.isRepresentedBy_transport_iff]
  · refine ((realEquivOfRingEquiv e).forall_congr fun w ↦ ?_).symm
    rw [atRealPlace_transport, atRealPlace_transport, QuadraticMap.isRepresentedBy_transport_iff]

/-- Transporting two quadratic forms along the same field isomorphism preserves local
equivalence. -/
theorem locallyEquivalent_transport_iff (e : K ≃+* L) (Q : _root_.QuadraticForm K V)
    (R : _root_.QuadraticForm K W) (f₁ : V ≃ₛₗ[(e : K →+* L)] V')
    (f₂ : W ≃ₛₗ[(e : K →+* L)] W') :
    (Q.transport f₁).LocallyEquivalent (R.transport f₂) ↔ Q.LocallyEquivalent R := by
  rw [locallyEquivalent_iff, locallyEquivalent_iff]
  refine and_congr ?_ ?_
  · refine ((equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).forall_congr fun v ↦ ?_).symm
    rw [atFinitePlace_transport (TauCeti.valuation_equivOfRingEquiv e v),
      atFinitePlace_transport (TauCeti.valuation_equivOfRingEquiv e v),
      QuadraticMap.equivalent_transport_iff]
  · refine ((realEquivOfRingEquiv e).forall_congr fun w ↦ ?_).symm
    rw [atRealPlace_transport, atRealPlace_transport, QuadraticMap.equivalent_transport_iff]

end Predicates

end QuadraticForm
