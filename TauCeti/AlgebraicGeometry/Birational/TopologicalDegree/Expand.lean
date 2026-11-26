/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineSpace.Expand
public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Finiteness

/-!
# The topological degree of the power map of affine space

For a domain `R`, a finite set of variables `σ` and `n > 0`, the power map `x_i ↦ x_i ^ n` of the
affine space `Spec R[x_i]` is `Spec` of `MvPolynomial.expand n`. It is dominant, finite and flat
of rank `n ^ |σ|` (`AlgebraicGeometry.finrank_SpecMap_expand`), so its topological degree is its
rank `n ^ |σ|`, in every characteristic.

Over a field `K` of characteristic `p`, the case `n = p` is the `K`-linear Frobenius
`x_i ↦ x_i ^ p` of `𝔸^d_K`, with topological degree `p ^ d` although it is purely inseparable; the
case `n = 2`, `|σ| = 1` is `z ↦ z²` on the affine line, with topological degree `2`.

## Main results

* `AlgebraicGeometry.topologicalDegree_toRationalMap_SpecMap_expand`: the topological degree of
  the power map is `n ^ |σ|`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

variable (σ R : Type*) [CommRing R] (n : ℕ) [NeZero n] [Finite σ]

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
