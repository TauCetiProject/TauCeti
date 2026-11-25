/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Finiteness
public import TauCeti.RingTheory.MvPolynomial.Expand
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# The topological degree of the power map of affine space

For a domain `R`, a finite set of variables `σ` and `n > 0`, the power map `x_i ↦ x_i ^ n` of the
affine space `Spec R[x_i]` is `Spec` of `MvPolynomial.expand n`. It is dominant, since `expand n`
is injective, and it is finite and flat, `R[x_i]` being free of rank `n ^ |σ|` over
`R[x_i ^ n]` (`TauCeti.MvPolynomial.finrank_expand`). So its topological degree is its rank
`n ^ |σ|`, in every characteristic.

Over a field `K` of characteristic `p`, the case `n = p` is the `K`-linear Frobenius
`x_i ↦ x_i ^ p` of `𝔸^d_K`, with topological degree `p ^ d` although it is purely inseparable; the
case `n = 2`, `|σ| = 1` is `z ↦ z²` on the affine line, with topological degree `2`.

## Main results

* `AlgebraicGeometry.isDominant_SpecMap_expand`, `AlgebraicGeometry.flat_SpecMap_expand` and
  `AlgebraicGeometry.isFinite_SpecMap_expand`: the power map is dominant and flat, and finite for
  finitely many variables.
* `AlgebraicGeometry.finrank_SpecMap_expand`: its rank is `n ^ |σ|` at every point.
* `AlgebraicGeometry.topologicalDegree_toRationalMap_SpecMap_expand`: its topological degree is
  `n ^ |σ|`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

variable (σ R : Type*) [CommRing R] (n : ℕ) [NeZero n]

/-- The power map `x_i ↦ x_i ^ n` of affine space is dominant, `MvPolynomial.expand n` being
injective. -/
instance isDominant_SpecMap_expand :
    IsDominant (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)) :=
  ⟨RingHom.denseRange_comap_of_injective _
    (MvPolynomial.expand_injective (Nat.pos_of_neZero n))⟩

/-- The power map `x_i ↦ x_i ^ n` of affine space is flat. -/
instance flat_SpecMap_expand :
    Flat (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)) :=
  Flat.SpecMap_iff.2 (TauCeti.MvPolynomial.flat_expand (Nat.pos_of_neZero n))

variable [Finite σ]

/-- The power map `x_i ↦ x_i ^ n` of affine space in finitely many variables is finite. -/
instance isFinite_SpecMap_expand :
    IsFinite (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)) :=
  (IsFinite.SpecMap_iff _).2 (TauCeti.MvPolynomial.finite_expand (Nat.pos_of_neZero n))

/-- The power map `x_i ↦ x_i ^ n` of affine space in finitely many variables has rank `n ^ |σ|`
at every point. -/
theorem finrank_SpecMap_expand :
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)).finrank =
      fun _ ↦ n ^ Nat.card σ := by
  have hn := Nat.pos_of_neZero n
  exact (Scheme.Hom.finrank_SpecMap_eq_finrank (TauCeti.MvPolynomial.finite_expand hn)
    (TauCeti.MvPolynomial.flat_expand hn)).trans (TauCeti.MvPolynomial.finrank_expand hn)

/-- **The topological degree of the power map of affine space.** For a domain `R`, finitely many
variables `σ` and `n > 0`, the map `x_i ↦ x_i ^ n` of `Spec R[x_i]` has topological degree
`n ^ |σ|`. It is finite and flat, and its rank is `n ^ |σ|` at every point. -/
theorem topologicalDegree_toRationalMap_SpecMap_expand [IsDomain R] :
    Scheme.RationalMap.topologicalDegree (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand n : MvPolynomial σ R →ₐ[R] _).toRingHom)).toRationalMap =
      n ^ Nat.card σ := by
  obtain ⟨y⟩ : Nonempty (Spec (.of (MvPolynomial σ R))) := inferInstance
  rw [Scheme.Hom.topologicalDegree_toRationalMap_eq_finrank _ y, finrank_SpecMap_expand]

end AlgebraicGeometry
