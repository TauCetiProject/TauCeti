/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.QuaternionicProjectiveSpace.Hopf.LoopSpace
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Sphere
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Sphere.Basic
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# The homology of the loop space of `HPⁿ` up to degree `4n + 2`

Let `q : S⁴ⁿ⁺³ → HPⁿ` be the quaternionic Hopf fibration, `n ≥ 1`, and `ΩHPⁿ` the Moore loop space
at the image of a unit vector `v`. The based Hopf product `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ` is a weak
homotopy equivalence
(`TauCeti.QuaternionicProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`), and the loop
space `ΩS⁴ⁿ⁺³` is `(4n + 1)`-connected
(`TauCeti.subsingleton_homotopyGroup_mooreLoopSpace_sphere`). This file reads off the homology of
`ΩHPⁿ` up to degree `4n + 2` from the homology of a product with the `3`-sphere
(`TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff` and
`TauCeti.isZero_singularHomology_sphere_prod_iff`), with coefficients in any ring `R`:

* `H_k(ΩHPⁿ; R) = 0` for `1 ≤ k ≤ 4n + 1` and `k ≠ 3`
  (`TauCeti.QuaternionicProjectiveSpace.isZero_singularHomology_mooreLoopSpace`);
* the looped Hopf map `Ωq : ΩS⁴ⁿ⁺³ → ΩHPⁿ` induces an isomorphism
  `H_{4n+2}(ΩS⁴ⁿ⁺³; R) ≅ H_{4n+2}(ΩHPⁿ; R)`
  (`TauCeti.QuaternionicProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`).

The restriction of `j ⋆ Ωq` to `{1} × ΩS⁴ⁿ⁺³` is `Ωq`
(`TauCeti.QuaternionicProjectiveSpace.hopfProduct_comp_prodMk_const_one`), and
`H_{4n-1}(ΩS⁴ⁿ⁺³)` vanishes, so the inclusion at `1` is an isomorphism on `H_{4n+2}`. The
remaining group below degree `4n + 2`, `H₃(ΩHPⁿ) ≅ H₃(S³)`, comes from the sphere factor and is
not used here.

With integer coefficients, composing with the Hurewicz isomorphism of the loop space gives the
explicit generator of `H_{4n+2}(ΩHPⁿ; ℤ) ≅ ℤ`: it is the image under `Ωq` of the Hurewicz class of
the loop of spheres adjoint to a generator of `π_{4n+3}(S⁴ⁿ⁺³) ≅ ℤ`
(`TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` and
`TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`). These are stated for
`HPⁿ⁺¹`, so that the degree `4n + 6` is a positive numeral offset. The homology of `ΩHPⁿ` above
degree `4n + 2` needs that of the loop space of the sphere `S⁴ⁿ⁺³`, which is not computed here.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.isZero_singularHomology_mooreLoopSpace`:
  `H_k(ΩHPⁿ; R) = 0` for `1 ≤ k ≤ 4n + 1`, `k ≠ 3`.
* `TauCeti.QuaternionicProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`:
  `Ωq : H_{4n+2}(ΩS⁴ⁿ⁺³; R) ≅ H_{4n+2}(ΩHPⁿ; R)`.
* `TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyAddEquiv`:
  `π_{4n+7}(S⁴ⁿ⁺⁷) ≃+ H_{4n+6}(ΩHPⁿ⁺¹; ℤ)`, through `Ωq` and the Hurewicz isomorphism.
* `TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`:
  `H_{4n+6}(ΩHPⁿ⁺¹; ℤ) ≃+ ℤ`, given an orthonormal basis of `ℍⁿ⁺²` over `ℝ`.

## References

* A. Hatcher, *Algebraic Topology*, the Hopf bundles of §4.2 and Theorem 4.41.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.39).
-/

public section

noncomputable section

open CategoryTheory Limits Metric AlgebraicTopology Module
open scoped Topology Topology.Homotopy Quaternion

namespace TauCeti.QuaternionicProjectiveSpace

variable {n : ℕ} (v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)

/-- **The homology of `ΩHPⁿ` vanishes in the degrees `1, 2` and `4, …, 4n + 1`**, with
coefficients in any ring, for `n ≥ 1`. -/
theorem isZero_singularHomology_mooreLoopSpace (hn : n ≠ 0) (R : Type) [Ring R] {k : ℕ}
    (hk₀ : k ≠ 0) (hk₃ : k ≠ 3) (hk : k < 4 * n + 2) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)))) := by
  obtain ⟨j, -, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) k
  refine IsZero.of_iso ?_ (asIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj
    (ModuleCat.of R R)).map (TopCat.ofHom (hopfProduct v j)))).symm
  -- `ΩHPⁿ` is weakly equivalent to `S³ × ΩS⁴ⁿ⁺³`, whose `H_k` vanishes with `H_k` and `H_{k-3}`
  -- of `ΩS⁴ⁿ⁺³`; below degree `3` only `H_k` of `ΩS⁴ⁿ⁺³` contributes.
  have hY {m : ℕ} (hm₀ : m ≠ 0) (hm : m < 4 * n + 2) :=
    isZero_singularHomology_mooreLoopSpace_sphere (finrank_piLp_quaternion_fin_succ 2 n)
      (by omega) v R (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm₀) (by omega))
  rcases lt_or_gt_of_ne hk₃ with hk3 | hk3
  · exact (isZero_singularHomology_sphere_prod_iff_of_lt _ Quaternion.finrank_eq_four hk3).2
      (hY hk₀ hk)
  · exact (isZero_singularHomology_sphere_prod_iff _ Quaternion.finrank_eq_four
      (n := k - 3) (by omega)).2 ⟨hY hk₀ hk, hY (by omega) (by omega)⟩

/-- **The looped Hopf map `Ωq : ΩS⁴ⁿ⁺³ → ΩHPⁿ` is an isomorphism on `H_{4n+2}`**, with
coefficients in any ring, for `n ≥ 1`. -/
theorem isIso_singularHomologyMap_mooreLoopSpaceMap (hn : n ≠ 0) (R : Type) [Ring R] :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} R) (4 * n + 2)).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap)) := by
  obtain ⟨j, hj, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  rw [← hopfProduct_comp_prodMk_const_one v hj, TopCat.ofHom_comp, Functor.map_comp]
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) (4 * n + 2)
  -- The inclusion at `1` is an isomorphism on `H_{4n+2}`, since `H_{4n-1}(ΩS⁴ⁿ⁺³)` vanishes.
  have := (isIso_singularHomologyMap_prodMk_sphere_iff (ModuleCat.of R R)
    (B := MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v)
    Quaternion.finrank_eq_four 1 (n := 4 * n - 1) (m := 4 * n + 2) (by omega)).2
    (isZero_singularHomology_mooreLoopSpace_sphere (finrank_piLp_quaternion_fin_succ 2 n)
      (by omega) v R (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
  infer_instance

/-! ### The integral generator -/

section Integral

variable (v : sphere (0 : PiLp 2 fun _ : Fin (n + 2) ↦ ℍ) 1)

private instance isIso_homologyMap_mooreLoopSpaceMap :
    IsIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (4 * n + 6)) := by
  have h := isIso_singularHomologyMap_mooreLoopSpaceMap v n.succ_ne_zero ℤ
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex, and
  -- `4 * (n + 1) + 2` unfolds to `4 * n + 6`.
  exact h

/-- **`H_{4n+6}(ΩHPⁿ⁺¹; ℤ) ≅ π_{4n+7}(S⁴ⁿ⁺⁷)`**: the Hurewicz isomorphism
`π_{4n+7}(S⁴ⁿ⁺⁷) ≅ H_{4n+6}(ΩS⁴ⁿ⁺⁷; ℤ)` of the loop space, followed by the isomorphism induced by
the looped Hopf map `Ωq`. -/
def mooreLoopSpaceHomologyAddEquiv :
    Additive (π_ (4 * n + 7) (sphere (0 : PiLp 2 fun _ : Fin (n + 2) ↦ ℍ) 1) v) ≃+
      ((singularChains ℤ).obj
        (TopCat.of (MooreLoopSpace (QuaternionicProjectiveSpace (n + 1)) (mk (n + 1) v)))).homology
          (4 * n + 6) :=
  (MooreLoopSpace.homologyAddEquiv v (4 * n + 4)
      (fun k _ ↦ subsingleton_homotopyGroup_sphere_piLp_quaternion (N := Fin (k + 1))
        (by simp; omega) v)).trans
    (asIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (4 * n + 6))).toLinearEquiv.toAddEquiv

/-- `TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` sends a class of
`π_{4n+7}(S⁴ⁿ⁺⁷)` to the image under `Ωq` of its Hurewicz class in the loop space. -/
theorem mooreLoopSpaceHomologyAddEquiv_apply
    (a : Additive (π_ (4 * n + 7) (sphere (0 : PiLp 2 fun _ : Fin (n + 2) ↦ ℍ) 1) v)) :
    mooreLoopSpaceHomologyAddEquiv v a =
      (HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
          rfl).toContinuousMap)) (4 * n + 6)).hom
        (MooreLoopSpace.homologyAddEquiv v (4 * n + 4)
          (fun k _ ↦ subsingleton_homotopyGroup_sphere_piLp_quaternion (N := Fin (k + 1))
            (by simp; omega) v) a) :=
  (rfl)

/-- **`H_{4n+6}(ΩHPⁿ⁺¹; ℤ) ≅ ℤ`.** The inverse of `mooreLoopSpaceHomologyAddEquiv`, followed by
the isomorphism `π_{4n+7}(S⁴ⁿ⁺⁷) ≅ ℤ` determined by an orthonormal basis `b` of `ℍⁿ⁺²` over `ℝ`.
The class corresponding to `1` is the image under `Ωq` of the Hurewicz class of the generator of
`π_{4n+7}(S⁴ⁿ⁺⁷)` fixed by `b`. -/
def mooreLoopSpaceHomologyIntAddEquiv
    (b : OrthonormalBasis (Fin (4 * n + 8)) ℝ (PiLp 2 fun _ : Fin (n + 2) ↦ ℍ)) :
    ((singularChains ℤ).obj
        (TopCat.of (MooreLoopSpace (QuaternionicProjectiveSpace (n + 1)) (mk (n + 1) v)))).homology
          (4 * n + 6) ≃+ ℤ :=
  (mooreLoopSpaceHomologyAddEquiv v).symm.trans (homotopyGroupSphereAddEquiv (n := 4 * n + 5) b v)

/-- The generator `1` of `ℤ` corresponds under `mooreLoopSpaceHomologyIntAddEquiv` to the image
under `Ωq` of the Hurewicz class of the generator of `π_{4n+7}(S⁴ⁿ⁺⁷)` fixed by `b`. -/
theorem mooreLoopSpaceHomologyIntAddEquiv_symm_apply
    (b : OrthonormalBasis (Fin (4 * n + 8)) ℝ (PiLp 2 fun _ : Fin (n + 2) ↦ ℍ)) (m : ℤ) :
    (mooreLoopSpaceHomologyIntAddEquiv v b).symm m =
      mooreLoopSpaceHomologyAddEquiv v
        ((homotopyGroupSphereAddEquiv (n := 4 * n + 5) b v).symm m) :=
  (rfl)

end Integral

end TauCeti.QuaternionicProjectiveSpace
