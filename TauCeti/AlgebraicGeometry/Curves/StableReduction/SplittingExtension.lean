/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.SeparablePoint
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Splitting

/-!
# A splitting extension with a rational point and a degree bound

Let `X` be a smooth proper geometrically integral curve of genus `g ≥ 2` over a field `k`, and let
`A` be a commutative group scheme over `k` whose `ℓ`-torsion `A[ℓ]`, for a prime `ℓ`, is finite
étale of rank `ℓ ^ r`. There is a finite separable extension `K' / k` of degree at most
`(2g - 2) · (ℓ ^ r)!` over which, simultaneously, `X` has a `K'`-rational point and the `ℓ`-torsion
of the group `A(K')` of `K'`-points is `(ℤ/ℓℤ) ^ r`.

This is the splitting extension of the Stacks Project's proof of semistable reduction in genus at
least two, in which `A` is the Jacobian `Pic⁰_{X/k}` and, for `ℓ` invertible in `k`, `r = 2g`,
giving the degree bound `(2g - 2) · (ℓ ^ (2g))!`. The rational point is what identifies the
`K'`-points of the Jacobian with the degree-zero line bundles on `X_{K'}`. The representability of
`Pic⁰_{X/k}`, its `ℓ`-torsion and that identification are not used or proved here: the statement
holds for every commutative group scheme `A` with finite étale `ℓ`-torsion of rank `ℓ ^ r`.

The extension is built in two steps. The curve has a point `x` whose residue field `κ(x)` is
separable of degree at most `2g - 2` over `k`
(`AlgebraicGeometry.Scheme.exists_finrank_residueField_le_and_isSeparable_of_two_le_genus`).
Over `κ(x)`, the `ℓ`-torsion of `A` splits after a Galois extension `K' / κ(x)` of degree dividing
`(ℓ ^ r)!`
(`TauCeti.GroupScheme.exists_isScalarTower_and_nonempty_mulEquiv_ker_zpowGroupHom`). Degrees
multiply and separability is transitive in the tower `k ⊆ κ(x) ⊆ K'`, and the point
`Spec K' ⟶ Spec κ(x) ⟶ X` is a section of the base change of `X` to `K'`.

## Main results

* `exists_finrank_le_and_section_and_nonempty_mulEquiv_ker_zpowGroupHom_of_two_le_genus`:
  the extension `K' / k` described above, in the namespace `AlgebraicGeometry.Scheme`.

## References

* [The Stacks Project, Section 55.18](https://stacks.math.columbia.edu/tag/0CDL), Theorem
  [0CDN](https://stacks.math.columbia.edu/tag/0CDN) and its proof, for the splitting extension
  and its degree bound.
-/

public section

open CategoryTheory Limits MonObj TauCeti TauCeti.AlgebraicGeometry TauCeti.GroupScheme
open Module (finrank)

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **A splitting extension of degree at most `(2g - 2) · (ℓ ^ r)!` with a rational point.** Let
`X` be a smooth proper geometrically integral curve over `k` of genus
`g = dim_k H¹(X, 𝒪_X) ≥ 2`, and let `A` be a commutative group scheme over `k` whose `ℓ`-torsion,
for a prime `ℓ`, is finite étale of rank `ℓ ^ r` over `Spec k`. There is a finite separable
extension `K' / k` of degree at most `(2g - 2) · (ℓ ^ r)!` such that `X ×_k K'` has a section over
`Spec K'` and the `ℓ`-torsion of the group of `K'`-points of `A` is isomorphic to
`(ZMod ℓ) ^ r`. -/
theorem exists_finrank_le_and_section_and_nonempty_mulEquiv_ker_zpowGroupHom_of_two_le_genus
    (hg : 2 ≤ finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1))
    (A : CommGrp (Over (Spec (.of k)))) {ℓ : ℕ} (hℓ : ℓ.Prime) [IsFinite (torsion A ℓ).X.hom]
    [Etale (torsion A ℓ).X.hom] {r : ℕ} (s : Spec (.of k))
    (hr : (torsion A ℓ).X.hom.finrank s = ℓ ^ r) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra k K'), FiniteDimensional k K' ∧
      Algebra.IsSeparable k K' ∧
      finrank k K' ≤
        (2 * finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) - 2) *
          (ℓ ^ r).factorial ∧
      (∃ σ : Spec (.of K') ⟶ pullback (X ↘ Spec (.of k)) (Spec.algebraMap k K'),
        σ ≫ pullback.snd _ _ = 𝟙 _) ∧
      Nonempty ((zpowGroupHom (ℓ : ℤ) :
        (Over.mk (Spec.algebraMap k K') ⟶ A.X) →* (Over.mk (Spec.algebraMap k K') ⟶ A.X)).ker ≃*
          Multiplicative (Fin r → ZMod ℓ)) := by
  -- A point `x` with residue field separable of degree at most `2g - 2` over `k`.
  obtain ⟨x, _, hx, _⟩ := X.exists_finrank_residueField_le_and_isSeparable_of_two_le_genus hg
  -- A Galois extension `K' / κ(x)` of degree dividing `(ℓ ^ r)!` splitting the `ℓ`-torsion of `A`.
  obtain ⟨K', _, _, _, _, _, _, hdeg, e⟩ :=
    exists_isScalarTower_and_nonempty_mulEquiv_ker_zpowGroupHom A hℓ s hr (X.residueField x)
  have : FiniteDimensional k K' := .trans k (X.residueField x) K'
  refine ⟨K', inferInstance, inferInstance, this, .trans k (X.residueField x) K', ?_, ?_, e⟩
  · rw [← Module.finrank_mul_finrank k (X.residueField x) K']
    exact Nat.mul_le_mul hx (Nat.le_of_dvd (Nat.factorial_pos _) hdeg)
  -- The point `Spec K' ⟶ Spec κ(x) ⟶ X` lies over `k`, so it is a section of the base change.
  refine ⟨pullback.lift (Spec.algebraMap (X.residueField x) K' ≫ X.fromSpecResidueField x) (𝟙 _)
    ?_, pullback.lift_snd _ _ _⟩
  rw [Category.assoc, X.fromSpecResidueField_comp_over (k := k), Category.id_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end AlgebraicGeometry.Scheme
