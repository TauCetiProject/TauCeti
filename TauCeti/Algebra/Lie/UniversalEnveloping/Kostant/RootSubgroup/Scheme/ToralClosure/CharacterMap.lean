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
# Character pullbacks on a Kostant toral closure

The Frobenius and numbered lattice symmetries act on the entire group of points of a Kostant
toral closure. This file computes their character maps on its represented weight torus:
Frobenius pulls a character back to its `p ^ k` multiple, and a symmetry with torus permutation
`τ` pulls it back by precomposition with `τ`.

These statements use `kostantToralWeightTorusPoints`, `kostantToralFrobenius`
and `kostantNumberedSymmetryPoints`. They do not require generation by root subgroups or a
monomial action on the weight basis. The torus parametrization need not be faithful.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {I : Type w}
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

/-- Frobenius on the whole toral point group pulls characters of the represented weight torus
back to their `p ^ k` multiples. -/
theorem isCharacterMap_kostantToralFrobenius (p k : ℕ) (A : Type v) [CommRing A]
    [ExpChar A p] :
    IsCharacterMap (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A)
      (kostantToralFrobenius e h ρ M hM hnil b wt p k A) ((p ^ k : ℕ) • 1) := by
  refine isCharacterMap_iff.mpr fun s => ?_
  apply Subtype.ext
  rw [coe_kostantToralFrobenius, coe_kostantToralWeightTorusPoints,
    coe_kostantToralWeightTorusPoints, map_iterateFrobenius_kostantTorusMatrix,
    torusPointMap_nsmul, torusPointMap_one, MonoidHom.pow_apply, MonoidHom.id_apply]

/-- A numbered symmetry of the whole toral point group pulls characters back by precomposition
with its torus permutation. Only preservation of weight components is needed: the lattice
symmetry may act nonmonomially within them. -/
theorem isCharacterMap_kostantNumberedSymmetryPoints
    (σ : I → I) (θ : V ≃ₗ[ℚ] V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M)
    (hθe : ∀ i v, θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) v) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e (σ i))) (θ v))
    (hσ : Function.Surjective σ) (τ : Equiv.Perm κ)
    (hwt : ∀ i j, b.repr (θ.toAddEquiv.invariantRestrict M hθM (b j)) i ≠ 0 →
      ∀ k, wt i (τ k) = wt j k)
    (A : Type v) [CommRing A] :
    IsCharacterMap (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A)
      (kostantNumberedSymmetryPoints M b θ hθM A
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
        (map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
          e h ρ M hM hnil b wt σ θ hθM hθe hσ τ hwt A)).toMonoidHom
      (LinearMap.funLeft ℤ ℤ τ) := by
  refine isCharacterMap_iff.mpr fun s => ?_
  apply Subtype.ext
  rw [MulEquiv.coe_toMonoidHom, coe_kostantNumberedSymmetryPoints,
    coe_kostantToralWeightTorusPoints, coe_kostantToralWeightTorusPoints,
    kostantTorusMatrix_apply, kostantTorusMatrix_apply]
  apply kostantNumberedSymmetryMatrix_conj_diagGL
  intro i j hij
  rw [torusCharacter_torusPointMap]
  congr 1
  exact funext (hwt i j hij)

end TauCeti.UniversalEnvelopingAlgebra
