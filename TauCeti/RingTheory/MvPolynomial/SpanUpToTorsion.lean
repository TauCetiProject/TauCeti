/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.Localization.Finiteness

/-!
# Submodules of free modules over polynomial rings are finitely generated up to `A`-torsion

Let `A` be a domain, which need not be Noetherian, and `σ`, `ι` finite types. Every submodule `K`
of `ι → MvPolynomial σ A` is finitely generated up to `A`-torsion: a finite subset of `K` spans a
submodule containing a multiple `b • x`, with `b` a non-zero-divisor of `A`, of every `x ∈ K`.

This approximates an arbitrary presentation of a finite module over a polynomial ring over a
non-Noetherian domain by a finite presentation whose comparison map has `A`-torsion kernel. It
feeds generic freeness over a domain in `TauCeti.RingTheory.Spectrum.Prime.GenericFreeness`.

## Main declarations

* `Submodule.exists_finset_smul_mem_span_of_isDomain`: over a domain `A`, a submodule of a finite
  free module over a polynomial ring in finitely many variables is finitely generated up to
  `A`-torsion.
-/

public section

namespace Submodule

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Over a domain `A`, every submodule `K` of `ι → MvPolynomial σ A` is finitely generated up to
`A`-torsion: some finite subset of `K` spans a submodule containing a multiple `b • x`, with
`b ∈ nonZeroDivisors A`, of each `x ∈ K`. -/
theorem exists_finset_smul_mem_span_of_isDomain {A : Type*} [CommRing A] [IsDomain A]
    {σ ι : Type*} [Finite σ] [Finite ι] (K : Submodule (MvPolynomial σ A) (ι → MvPolynomial σ A)) :
    ∃ s : Finset (ι → MvPolynomial σ A), (s : Set (ι → MvPolynomial σ A)) ⊆ K ∧
      ∀ x ∈ K, ∃ b ∈ nonZeroDivisors A,
        b • x ∈ span (MvPolynomial σ A) (s : Set (ι → MvPolynomial σ A)) := by
  let F := FractionRing A
  let P := MvPolynomial σ A
  let PK := MvPolynomial σ F
  let S : Submonoid P := (nonZeroDivisors A).map (MvPolynomial.C (σ := σ))
  let f : (ι → P) →ₗ[P] (ι → PK) := (Algebra.linearMap P PK).compLeft ι
  have hf : Function.Injective f := fun x y h ↦ funext fun i ↦ by
    have hi :
        MvPolynomial.map (algebraMap A F) (x i) = MvPolynomial.map (algebraMap A F) (y i) := by
      simpa only [f, P, PK, LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply,
        MvPolynomial.algebraMap_def] using congrFun h i
    exact MvPolynomial.map_injective _ (IsFractionRing.injective A F) hi
  -- Over the Noetherian ring `PK`, the image of `K` spans a finitely generated submodule.
  obtain ⟨s, hsK, hs⟩ := exists_finset_smul_mem_span_of_fg_span_image (K := PK) hf S (N := K)
    (IsNoetherian.noetherian _)
  refine ⟨s, hsK, fun x hx ↦ ?_⟩
  obtain ⟨_, ⟨b, hb, rfl⟩, hbx⟩ := hs x hx
  exact ⟨b, hb, by rwa [← MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_smul P b x] at hbx⟩

end Submodule
