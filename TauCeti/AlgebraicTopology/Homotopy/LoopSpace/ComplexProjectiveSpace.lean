/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.LoopSpace
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Refl
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Hurewicz
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space

/-!
# The homology of the loop space of `CPⁿ` up to degree `2n`

Let `q : S²ⁿ⁺¹ → CPⁿ` be the Hopf fibration, `n ≥ 1`, and `ΩCPⁿ` the Moore loop space at the image
of a unit vector `v`. The based Hopf product `j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ` is a weak homotopy
equivalence (`TauCeti.ComplexProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`), and
the loop space `ΩS²ⁿ⁺¹` is `(2n - 1)`-connected
(`TauCeti.subsingleton_homotopyGroup_mooreLoopSpace_sphere`). This file reads off the homology of
`ΩCPⁿ` up to degree `2n` from the homology of a product with a circle
(`TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff` and
`TauCeti.isZero_singularHomology_circle_prod_succ_iff`), with coefficients in any ring `R`:

* `H_k(ΩCPⁿ; R) = 0` for `2 ≤ k < 2n`
  (`TauCeti.ComplexProjectiveSpace.isZero_singularHomology_mooreLoopSpace`);
* the looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ` induces an isomorphism
  `H_{2n}(ΩS²ⁿ⁺¹; R) ≅ H_{2n}(ΩCPⁿ; R)`
  (`TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`).

The restriction of `j ⋆ Ωq` to `{1} × ΩS²ⁿ⁺¹` is `Ωq`, since `j 1` is the unit
(`TauCeti.ComplexProjectiveSpace.hopfProduct_comp_prodMk_const_one`), and `H_{2n-1}(ΩS²ⁿ⁺¹)`
vanishes, so the inclusion at `1` is an isomorphism on `H_{2n}`.

With integer coefficients, composing with the Hurewicz isomorphism of the loop space gives the
explicit generator of `H_{2n}(ΩCPⁿ; ℤ) ≅ ℤ`: it is the image under `Ωq` of the Hurewicz class of
the loop of spheres adjoint to a generator of `π_{2n+1}(S²ⁿ⁺¹) ≅ ℤ`
(`TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` and
`TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`). These are stated for `CPⁿ⁺¹`,
so that the degree `2n + 2` is a positive numeral offset. The homology of `ΩCPⁿ` above degree
`2n` needs that of the loop space of the odd sphere, which is not computed here.

## Main results

* `TauCeti.ComplexProjectiveSpace.isZero_singularHomology_mooreLoopSpace`: `H_k(ΩCPⁿ; R) = 0` for
  `2 ≤ k < 2n`.
* `TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`:
  `Ωq : H_{2n}(ΩS²ⁿ⁺¹; R) ≅ H_{2n}(ΩCPⁿ; R)`.
* `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyAddEquiv`:
  `π_{2n+3}(S²ⁿ⁺³) ≃+ H_{2n+2}(ΩCPⁿ⁺¹; ℤ)`, through `Ωq` and the Hurewicz isomorphism.
* `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`:
  `H_{2n+2}(ΩCPⁿ⁺¹; ℤ) ≃+ ℤ`, given an orthonormal basis of `ℂⁿ⁺²` over `ℝ`.

## References

* A. Hatcher, *Algebraic Topology*, Example 4.45 and Section 2.2, Example 2.48.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.38).
-/

public section

noncomputable section

open CategoryTheory Limits Metric AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- **The homology of `ΩCPⁿ` vanishes in the degrees `2, …, 2n - 1`**, with coefficients in any
ring. -/
theorem isZero_singularHomology_mooreLoopSpace (R : Type) [Ring R] {k : ℕ}
    (hk₂ : 2 ≤ k) (hk : k < 2 * n) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)))) := by
  obtain ⟨j, -, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v (by omega)
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) k
  refine IsZero.of_iso ?_ (asIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj
    (ModuleCat.of R R)).map (TopCat.ofHom (hopfProduct v j)))).symm
  -- `ΩCPⁿ` is weakly equivalent to `S¹ × ΩS²ⁿ⁺¹`, whose `Hₘ₊₁` vanishes with `Hₘ₊₁` and `Hₘ` of
  -- `ΩS²ⁿ⁺¹`.
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact (isZero_singularHomology_circle_prod_succ_iff _ m).2
    ⟨isZero_singularHomology_mooreLoopSpace_sphere (finrank_real_euclideanSpace_complex n) v R
        (by omega) (by omega),
      isZero_singularHomology_mooreLoopSpace_sphere (finrank_real_euclideanSpace_complex n) v R
        (by omega) (by omega)⟩

/-- **The looped Hopf map `Ωq : ΩS²ⁿ⁺¹ → ΩCPⁿ` is an isomorphism on `H_{2n}`**, with coefficients
in any ring, for `n ≥ 1`. -/
theorem isIso_singularHomologyMap_mooreLoopSpaceMap (hn : n ≠ 0) (R : Type) [Ring R] :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} R) (2 * n)).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap)) := by
  obtain ⟨j, hj, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  rw [← hopfProduct_comp_prodMk_const_one v hj, TopCat.ofHom_comp, Functor.map_comp]
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) (2 * n)
  -- The inclusion at `1` is an isomorphism on `H_{2n}`, since `H_{2n-1}(ΩS²ⁿ⁺¹)` vanishes.
  have : IsIso (((singularHomologyFunctor (ModuleCat.{0} R) (2 * n)).obj (ModuleCat.of R R)).map
      (TopCat.ofHom ((ContinuousMap.const _ (1 : Circle)).prodMk (ContinuousMap.id
        (MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v))))) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm]
    exact (isIso_singularHomologyMap_prodMk_const_one_succ_iff _ m).2
      (isZero_singularHomology_mooreLoopSpace_sphere (finrank_real_euclideanSpace_complex n) v R
        (by omega) (by omega))
  infer_instance

/-! ### The integral generator -/

section Integral

variable (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1)

private instance isIso_homologyMap_mooreLoopSpaceMap :
    IsIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (2 * n + 2)) := by
  have h := isIso_singularHomologyMap_mooreLoopSpaceMap v n.succ_ne_zero ℤ
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex, and
  -- `2 * (n + 1)` unfolds to `2 * n + 2`.
  exact h

/-- **`H_{2n+2}(ΩCPⁿ⁺¹; ℤ) ≅ π_{2n+3}(S²ⁿ⁺³)`**: the Hurewicz isomorphism
`π_{2n+3}(S²ⁿ⁺³) ≅ H_{2n+2}(ΩS²ⁿ⁺³; ℤ)` of the loop space, followed by the isomorphism induced by
the looped Hopf map `Ωq`. -/
def mooreLoopSpaceHomologyAddEquiv :
    Additive (π_ (2 * n + 3) (sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) v) ≃+
      ((singularChains ℤ).obj
        (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace (n + 1)) (mk (n + 1) v)))).homology
          (2 * n + 2) :=
  (MooreLoopSpace.homologyAddEquiv v (2 * n)
      (fun k _ ↦ subsingleton_homotopyGroup_sphere (N := Fin (k + 1)) (by simp; omega) v)).trans
    (asIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (2 * n + 2))).toLinearEquiv.toAddEquiv

/-- `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` sends a class of
`π_{2n+3}(S²ⁿ⁺³)` to the image under `Ωq` of its Hurewicz class in the loop space. -/
theorem mooreLoopSpaceHomologyAddEquiv_apply
    (a : Additive (π_ (2 * n + 3) (sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) v)) :
    mooreLoopSpaceHomologyAddEquiv v a =
      (HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
          rfl).toContinuousMap)) (2 * n + 2)).hom
        (MooreLoopSpace.homologyAddEquiv v (2 * n)
          (fun k _ ↦ subsingleton_homotopyGroup_sphere (N := Fin (k + 1)) (by simp; omega) v) a) :=
  (rfl)

/-- **`H_{2n+2}(ΩCPⁿ⁺¹; ℤ) ≅ ℤ`.** The inverse of `mooreLoopSpaceHomologyAddEquiv`, followed by
the isomorphism `π_{2n+3}(S²ⁿ⁺³) ≅ ℤ` determined by an orthonormal basis `b` of `ℂⁿ⁺²` over `ℝ`.
The class corresponding to `1` is the image under `Ωq` of the Hurewicz class of the generator of
`π_{2n+3}(S²ⁿ⁺³)` fixed by `b`. -/
def mooreLoopSpaceHomologyIntAddEquiv
    (b : OrthonormalBasis (Fin (2 * n + 4)) ℝ (EuclideanSpace ℂ (Fin (n + 2)))) :
    ((singularChains ℤ).obj
        (TopCat.of (MooreLoopSpace (ComplexProjectiveSpace (n + 1)) (mk (n + 1) v)))).homology
          (2 * n + 2) ≃+ ℤ :=
  (mooreLoopSpaceHomologyAddEquiv v).symm.trans (homotopyGroupSphereAddEquiv (n := 2 * n + 1) b v)

/-- The generator `1` of `ℤ` corresponds under `mooreLoopSpaceHomologyIntAddEquiv` to the image
under `Ωq` of the Hurewicz class of the generator of `π_{2n+3}(S²ⁿ⁺³)` fixed by `b`. -/
theorem mooreLoopSpaceHomologyIntAddEquiv_symm_apply
    (b : OrthonormalBasis (Fin (2 * n + 4)) ℝ (EuclideanSpace ℂ (Fin (n + 2)))) (m : ℤ) :
    (mooreLoopSpaceHomologyIntAddEquiv v b).symm m =
      mooreLoopSpaceHomologyAddEquiv v
        ((homotopyGroupSphereAddEquiv (n := 2 * n + 1) b v).symm m) :=
  (rfl)

end Integral

end TauCeti.ComplexProjectiveSpace
