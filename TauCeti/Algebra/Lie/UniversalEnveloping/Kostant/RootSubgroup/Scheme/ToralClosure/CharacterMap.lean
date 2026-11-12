/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullback on Kostant toral-closure points

The Frobenius and the integral numbered symmetries act on all points of a Kostant toral
closure, not just on its elementary subgroup. This file computes their character maps on the
represented weight torus, using `kostantToralFrobenius` and `kostantNumberedSymmetryPoints`.
The computations use the entrywise Frobenius and weight-component preservation, respectively;
no point-generation theorem or monomial action on a weight basis is needed.

If a symmetry sends the torus indices by a permutation `τ`, its character pullback is
precomposition by `τ`. Thus a fundamental character at `i` pulls back to the character at
`τ⁻¹ i`, whereas the symmetry sends root indices forward. Composing this symmetry after
`p ^ k`-Frobenius gives the character map `p ^ k` times that pullback, by the contravariant
composition law `TauCeti.IsCharacterMap.comp`.

The torus here is the one parametrized by the supplied weights. It need not be faithfully
parametrized: for a representation with a proper weight lattice, this is the image of the
full-weight parametrization, not all points of its actual weight-lattice torus. In the
full-weight case the two agree.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

/-- The `p ^ k`-Frobenius on the whole toral-closure point group has character map
`p ^ k • 1` on the represented weight torus. -/
theorem isCharacterMap_kostantToralFrobenius (p k : ℕ)
    (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A)
      (kostantToralFrobenius e h ρ M hM hnil b wt p k A) ((p ^ k : ℕ) • 1) := by
  refine isCharacterMap_iff.mpr fun s => Subtype.ext ?_
  rw [coe_kostantToralFrobenius, coe_kostantToralWeightTorusPoints,
    coe_kostantToralWeightTorusPoints, torusPointMap_nsmul, torusPointMap_one,
    MonoidHom.pow_apply, MonoidHom.id_apply]
  exact map_iterateFrobenius_kostantTorusMatrix M b wt p k s

section NumberedSymmetry

variable (σ : I → I) (θ : V ≃ₗ[ℚ] V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M)
variable (hθe : ∀ i, ∀ v : V,
  θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) v) =
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) (θ v))
variable (hσ : Function.Surjective σ) (τ : Equiv.Perm κ)
variable (hwt : ∀ i j, b.repr (θ.toAddEquiv.invariantRestrict M hθM (b j)) i ≠ 0 →
  ∀ k, wt i (τ k) = wt j k)

/-- A numbered symmetry of the whole toral-closure point group pulls characters back by
precomposition with the forward torus-index permutation. This is the inverse of the action
sending the fundamental character at `i` to the one at `τ i`. -/
theorem isCharacterMap_kostantNumberedSymmetryPoints (A : Type v) [CommRing A] :
    IsCharacterMap (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A)
      (kostantNumberedSymmetryPoints M b θ hθM A
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
        (map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
          e h ρ M hM hnil b wt σ θ hθM hθe hσ τ hwt A)).toMonoidHom
      (LinearMap.funLeft ℤ ℤ τ) := by
  refine isCharacterMap_iff.mpr fun s => Subtype.ext ?_
  rw [MulEquiv.coe_toMonoidHom, coe_kostantNumberedSymmetryPoints,
    coe_kostantToralWeightTorusPoints, coe_kostantToralWeightTorusPoints,
    kostantTorusMatrix_apply, kostantTorusMatrix_apply]
  refine kostantNumberedSymmetryMatrix_conj_diagGL M b θ hθM A _ _ fun i j hij => ?_
  rw [torusCharacter_torusPointMap]
  congr 1
  exact funext (hwt i j hij)

/-- A numbered symmetry composed after Frobenius has the scaled inverse-permutation
character pullback. The order of the two lattice maps is dictated by contravariance. -/
theorem isCharacterMap_kostantNumberedSymmetryPoints_comp_frobenius
    (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A)
      ((kostantNumberedSymmetryPoints M b θ hθM A
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
        (map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
          e h ρ M hM hnil b wt σ θ hθM hθe hσ τ hwt A)).toMonoidHom.comp
        (kostantToralFrobenius e h ρ M hM hnil b wt p k A))
      ((p ^ k : ℕ) • LinearMap.funLeft ℤ ℤ τ) := by
  simpa only [smul_mul_assoc, one_mul] using
    (isCharacterMap_kostantNumberedSymmetryPoints
      e h ρ M hM hnil b wt σ θ hθM hθe hσ τ hwt A).comp
      (isCharacterMap_kostantToralFrobenius e h ρ M hM hnil b wt p k A)

end NumberedSymmetry

end TauCeti.UniversalEnvelopingAlgebra
