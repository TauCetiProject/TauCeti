/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.SeparablePoint
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Splitting

/-!
# A rational point and split `ℓ`-torsion over one separable extension

Let `X` be a smooth proper geometrically integral curve of genus `g ≥ 2` over a field `k`, and let
`A` be a commutative group scheme over `k` whose `ℓ`-torsion `A[ℓ]`, for a prime `ℓ`, is finite
étale of rank `ℓ ^ r`. This file produces one finite separable extension `K / k` of degree at most
`(2g - 2) · (ℓ ^ r)!` over which both

* `X` has a `K`-rational point, that is, `X ×_k K` has a section over `Spec K`; and
* the `ℓ`-torsion of the group `A(K)` of points of `A` with values in `K` is `(ℤ/ℓℤ) ^ r`.

The extension is built in two steps. First `X` acquires a rational point over a separable extension
`K₁ / k` of degree at most `2g - 2`
(`AlgebraicGeometry.Scheme.exists_finrank_le_and_section_of_two_le_genus`). Then `A[ℓ]` splits
over a Galois extension `K / K₁` of degree dividing `(ℓ ^ r)!`
(`TauCeti.GroupScheme.exists_nonempty_mulEquiv_ker_zpowGroupHom`, applied over `K₁`). The degrees
multiply in the tower `k ⊆ K₁ ⊆ K`, and the rational point over `K₁` remains one over `K`.

The intended `A` is the Jacobian of `X`, a group scheme representing the degree-zero Picard functor
`Pic⁰_{X/k}`. For `ℓ` distinct from the characteristic of `k` its `ℓ`-torsion is finite étale of
rank `ℓ ^ (2g)`, and the `ℓ`-torsion of its points with values in `K` is the `ℓ`-torsion of the
Picard group of `X ×_k K`
(`TauCeti.AlgebraicGeometry.relativePicardDegreeZeroTorsionLineBundleClassMulEquiv`); the bound is
then the `(2g - 2) · (ℓ ^ (2g))!` of the Stacks Project's proof of semistable reduction. No
hypothesis on `k` is needed here: it need not be perfect, and the characteristic enters only
through the étaleness of `A[ℓ]`.

## Main results

* `exists_finrank_le_and_section_and_nonempty_mulEquiv_ker_zpowGroupHom_of_two_le_genus`, in the
  namespace `AlgebraicGeometry.Scheme`: a finite separable extension of degree at most
  `(2g - 2) · (ℓ ^ r)!` over which the curve has a rational point and the `ℓ`-torsion of `A` is
  `(ℤ/ℓℤ) ^ r`.

## References

* The Stacks Project, [Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN), Theorem 55.18.1, whose
  proof chooses this extension.
-/

public section

open CategoryTheory Limits MonObj TauCeti TauCeti.AlgebraicGeometry
open Module (finrank)

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **A rational point and split `ℓ`-torsion over one separable extension.** Let `X` be a smooth
proper geometrically integral curve over `k` of genus `g = dim_k H¹(X, 𝒪_X) ≥ 2`, and let `A` be a
commutative group scheme over `k` whose `ℓ`-torsion, for a prime `ℓ`, is finite étale of rank
`ℓ ^ r`. There is a finite separable extension `K / k` of degree at most `(2g - 2) · (ℓ ^ r)!` such
that `X ×_k K` has a section over `Spec K` and the `ℓ`-torsion of the group of points of `A` with
values in `K` is isomorphic to `(ZMod ℓ) ^ r`. -/
theorem exists_finrank_le_and_section_and_nonempty_mulEquiv_ker_zpowGroupHom_of_two_le_genus
    (hg : 2 ≤ finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1))
    (A : CommGrp (Over (Spec (.of k)))) {ℓ : ℕ} (hℓ : ℓ.Prime)
    [IsFinite (GroupScheme.torsion A ℓ).X.hom] [Etale (GroupScheme.torsion A ℓ).X.hom] {r : ℕ}
    (s : Spec (.of k)) (hr : (GroupScheme.torsion A ℓ).X.hom.finrank s = ℓ ^ r) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧
      finrank k K ≤
        (2 * finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) - 2) *
          (ℓ ^ r).factorial ∧
      Algebra.IsSeparable k K ∧
      (∃ x : Spec (.of K) ⟶ pullback (X ↘ Spec (.of k)) (Spec.algebraMap k K),
        x ≫ pullback.snd _ _ = 𝟙 _) ∧
      Nonempty ((zpowGroupHom (ℓ : ℤ) :
          (Over.mk (Spec.algebraMap k K) ⟶ A.X) →* (Over.mk (Spec.algebraMap k K) ⟶ A.X)).ker ≃*
        Multiplicative (Fin r → ZMod ℓ)) := by
  -- A rational point over `K₁`, then split `ℓ`-torsion over `K / K₁`.
  obtain ⟨K₁, _, _, _, hdeg₁, _, x₁, hx₁⟩ := X.exists_finrank_le_and_section_of_two_le_genus hg
  obtain ⟨K, _, _, _, _, _, _, hdeg, e⟩ :=
    GroupScheme.exists_nonempty_mulEquiv_ker_zpowGroupHom A hℓ s hr K₁
  have hK : Spec.algebraMap K₁ K ≫ Spec.algebraMap k K₁ = Spec.algebraMap k K := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨K, inferInstance, inferInstance, .trans k K₁ K, ?_, .trans k K₁ K,
    ⟨pullback.lift (Spec.algebraMap K₁ K ≫ x₁ ≫ pullback.fst _ _) (𝟙 _) ?_,
      pullback.lift_snd _ _ _⟩, e⟩
  · rw [← Module.finrank_mul_finrank k K₁ K]
    exact Nat.mul_le_mul hdeg₁ (Nat.le_of_dvd (Nat.factorial_pos _) hdeg)
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hx₁, Category.id_comp, hK]

end AlgebraicGeometry.Scheme
