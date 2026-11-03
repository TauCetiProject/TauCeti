/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere

/-!
# The local Kummer images of an isogeny

Let `φ : E₁ → E₂` be a separable isogeny over a field `K`. Its Kummer map
`E₂(K) → H¹(G_K, E₁[φ])` has kernel `φ(E₁(K))`, so its image is a copy of the cokernel
`E₂(K) ⧸ φ(E₁(K))`; its order is the **Kummer-cokernel index** `[E₂(K) : φ(E₁(K))]`. Over a
completion `K_v` of a global field, this image is the local condition at `v` of the `φ`-Selmer
group `Sel_φ`. In Cassels' proof that the Birch–Swinnerton-Dyer quotient is invariant under
isogeny, the ratio of the orders of `Sel_φ(E₁)` and `Sel_φ̂(E₂)` is the global factor
`#E₁(K)[φ] / #E₂(K)[φ̂]` times the product over the places `v` of the local factors

`#H¹_φ(K_v) / #E₁(K_v)[φ] = [E₂(K_v) : φ(E₁(K_v))] / #E₁(K_v)[φ]`,

where `H¹_φ(K_v) ⊆ H¹(G_{K_v}, E₁[φ])` is the image of the local Kummer map.

This file identifies the local conditions with these indices and computes them where the residue
characteristic does not divide `deg φ`:

* over every field, the image of the Kummer map has order `[E₂(K) : φ(E₁(K))]`
  (`TauCeti.Isogeny.natCard_range_kummerMap`), and so does the local condition at `L i` of the
  `φ`-Selmer structure of a family of extensions `L i`;
* at a finite place `u` of a Dedekind domain with finite residue field, prime to `deg φ`, the
  Kummer image is finite;
* over the fraction field `K` of a Dedekind domain with finite residue fields, when `deg φ` is
  nonzero in `K`, the local factor is `1` at all but finitely many finite places: there both
  curves have good reduction and the place is prime to `deg φ`, so that
  `TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic_integralModel` applies. This is the
  finite support of the product of the local factors at the finite places.

The local factors at the places dividing `deg φ` and at the real places, which involve the
formal group and the real period, are not computed here.

## Main results

* `TauCeti.Isogeny.natCard_localCondition_selmerStructure`: the local condition of the `φ`-Selmer
  structure at `L i` has order `[E₂(L i) : φ(E₁(L i))]`.
* `TauCeti.Isogeny.finite_range_kummerMap_of_degree_notMem`: the local Kummer image at a finite
  place prime to `deg φ` is finite.
* `TauCeti.Isogeny.eventually_natCard_localCondition_selmerStructure_eq`: for almost every finite
  place `v`, `#H¹_φ(K_v) = #E₁(K_v)[φ]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114, §3.
-/

public section

noncomputable section

open IsDedekindDomain ValuativeRel WeierstrassCurve TauCeti.ContCohomology

namespace TauCeti.Isogeny

open Hom (ofIsogeny)

section Field

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-! ### The local conditions of the `φ`-Selmer structure -/

variable {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- **The local condition of `Sel_φ` at `L i` has order the local Kummer-cokernel index**
`[E₂(L i) : φ(E₁(L i))]`, for a separable isogeny `φ`: it is the image of the local Kummer map
of `φ` over `L i`. -/
theorem natCard_localCondition_selmerStructure
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (i : ι) [DecidableEq (L i)] :
    Nat.card ((φ.selmerStructure τ).localCondition i) =
      (ofIsogeny (φ.baseChange (L i))).pointMapHom.range.index := by
  rw [selmerStructure_localCondition, ← range_kummerMap, natCard_range_kummerMap]

end Field

/-! ### Places prime to the degree -/

section Local

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  {u : HeightOneSpectrum A} [Finite (A ⧸ u.asIdeal)] [DecidableEq (u.adicCompletion F)]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  {ψ : Isogeny W₁.toAffine W₂.toAffine}

/-- **The local Kummer image at a place prime to the degree is finite**: it is a copy of the
cokernel `E₂(F_u) ⧸ ψ(E₁(F_u))`, whose finiteness is
`TauCeti.Isogeny.Hom.finiteIndex_range_pointMapHom_of_degree_notMem`. An isogeny of degree prime
to `u` is automatically separable (`TauCeti.Isogeny.isSeparable_dual_and_self_iff`). -/
theorem finite_range_kummerMap_of_degree_notMem
    [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hψ : (ψ.degree : A) ∉ u.asIdeal) : Finite ψ.kummerMap.range :=
  finite_range_kummerMap_iff.2 <|
    Hom.finiteIndex_range_pointMapHom_of_degree_notMem u (by rwa [Hom.degree_ofIsogeny])

end Local

/-! ### Almost every place -/

section Global

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  [∀ v : HeightOneSpectrum R, DecidableEq (v.adicCompletion K)]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The local Kummer factor is trivial at almost every place**: if `deg φ` is nonzero in `K`,
then for all but finitely many finite places `v`, the local condition `H¹_φ(K_v)` at `v` of the
`φ`-Selmer structure of the completions has the order of the kernel `E₁(K_v)[φ]`. Such a `v` is
prime to `deg φ` and both curves have good reduction there, given by their own equations. -/
theorem eventually_natCard_localCondition_selmerStructure_eq
    (τ : ∀ v : HeightOneSpectrum R,
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hφ : (φ.degree : K) ≠ 0) :
    ∀ᶠ v in Filter.cofinite, Nat.card ((φ.selmerStructure τ).localCondition v) =
      Nat.card (ofIsogeny (φ.baseChange (v.adicCompletion K))).pointMapHom.ker := by
  have := (φ.isSeparable_dual_and_self_iff.2 hφ).2
  -- away from `T`, `W₁` has good reduction and `v` is prime to `deg φ`
  obtain ⟨T, -, hT₁, hTdeg⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ ∅
  filter_upwards [T.finite_toSet.eventually_cofinite_notMem,
    eventually_isElliptic_integralModel_adicCompletion R W₂] with v hv ⟨_, _⟩
  obtain ⟨_, _⟩ := hT₁ v hv
  rw [natCard_localCondition_selmerStructure]
  exact Hom.index_range_eq_card_ker_of_isElliptic_integralModel _ <| by
    have hd : (φ.baseChange (v.adicCompletion K)).degree = φ.degree := degree_map φ _
    rw [Hom.degree_ofIsogeny, hd]
    exact hTdeg v hv

end Global

end TauCeti.Isogeny
