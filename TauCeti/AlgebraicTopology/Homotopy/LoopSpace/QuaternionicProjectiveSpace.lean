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
# The homology of the loop space of `HPⁿ`

Let `q : S⁴ⁿ⁺³ → HPⁿ` be the quaternionic Hopf fibration, `n ≥ 1`, and `ΩHPⁿ` the Moore loop space
at the image of a unit vector `v`. The based Hopf product `j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ` is a weak
homotopy equivalence
(`TauCeti.QuaternionicProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`), and the
homology of `ΩS⁴ⁿ⁺³` is `R` in the degrees divisible by `4n + 2` and zero in the others
(`TauCeti.singularHomologyMooreLoopSpaceSphereIso` and
`TauCeti.isZero_singularHomology_mooreLoopSpace_sphere`). This file reads off the homology of
`ΩHPⁿ` from the homology of a product with the `3`-sphere
(`TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff`,
`TauCeti.isZero_singularHomology_sphere_prod_iff` and `TauCeti.singularHomologySphereProdIso`),
with coefficients in any ring `R`: it is `R` in the degrees `0` and `3` modulo `4n + 2` and zero in
the others.

* `H_k(ΩHPⁿ; R) = 0` unless `k` is `0` or `3` modulo `4n + 2`
  (`TauCeti.QuaternionicProjectiveSpace.isZero_singularHomology_mooreLoopSpace`);
* the looped Hopf map `Ωq : ΩS⁴ⁿ⁺³ → ΩHPⁿ` induces an isomorphism
  `H_k(ΩS⁴ⁿ⁺³; R) ≅ H_k(ΩHPⁿ; R)` unless `k` is `3` modulo `4n + 2`
  (`TauCeti.QuaternionicProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`), and so
  `H_{(4n+2)j}(ΩHPⁿ; R) ≅ R` for every `j`
  (`TauCeti.QuaternionicProjectiveSpace.singularHomologyMooreLoopSpaceIso`);
* `H_{(4n+2)j+3}(ΩHPⁿ; R) ≅ R` for every `j`
  (`TauCeti.QuaternionicProjectiveSpace.singularHomologyMooreLoopSpaceAddThreeIso`), through
  `H_{(4n+2)j+3}(S³ × ΩS⁴ⁿ⁺³) ≅ H_{(4n+2)j}(ΩS⁴ⁿ⁺³)`.

The restriction of `j ⋆ Ωq` to `{1} × ΩS⁴ⁿ⁺³` is `Ωq`
(`TauCeti.QuaternionicProjectiveSpace.hopfProduct_comp_prodMk_const_one`), and the inclusion at
`1` is an isomorphism on `H_k` for `k < 3`, and for `k ≥ 3` exactly when `H_{k-3}(ΩS⁴ⁿ⁺³)`
vanishes, which is the case unless `k` is `3` modulo `4n + 2`. In the degrees `3` modulo `4n + 2`,
`H_k(S³ × ΩS⁴ⁿ⁺³) ≅ H_{k-3}(ΩS⁴ⁿ⁺³)` comes from the sphere factor, while `H_k(ΩS⁴ⁿ⁺³)` vanishes.

With integer coefficients, composing with the Hurewicz isomorphism of the loop space gives the
explicit generator of `H_{4n+2}(ΩHPⁿ; ℤ) ≅ ℤ`: it is the image under `Ωq` of the Hurewicz class of
the loop of spheres adjoint to a generator of `π_{4n+3}(S⁴ⁿ⁺³) ≅ ℤ`
(`TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyAddEquiv` and
`TauCeti.QuaternionicProjectiveSpace.mooreLoopSpaceHomologyIntAddEquiv`). These are stated for
`HPⁿ⁺¹`, so that the degree `4n + 6` is a positive numeral offset.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.isZero_singularHomology_mooreLoopSpace`:
  `H_k(ΩHPⁿ; R) = 0` unless `k` is `0` or `3` modulo `4n + 2`.
* `TauCeti.QuaternionicProjectiveSpace.isIso_singularHomologyMap_mooreLoopSpaceMap`:
  `Ωq : H_k(ΩS⁴ⁿ⁺³; R) ≅ H_k(ΩHPⁿ; R)` unless `k` is `3` modulo `4n + 2`.
* `TauCeti.QuaternionicProjectiveSpace.singularHomologyMooreLoopSpaceIso`:
  `H_{(4n+2)j}(ΩHPⁿ; R) ≅ R`.
* `TauCeti.QuaternionicProjectiveSpace.singularHomologyMooreLoopSpaceAddThreeIso`:
  `H_{(4n+2)j+3}(ΩHPⁿ; R) ≅ R`.
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

/-- The homology of `ΩS⁴ⁿ⁺³` vanishes in the degrees not divisible by `4n + 2`. -/
private lemma isZero_singularHomology_mooreLoopSpace_sphere_of_mod_ne_zero (R : Type) [Ring R]
    {k : ℕ} (hk : k % (4 * n + 2) ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v))) :=
  isZero_singularHomology_mooreLoopSpace_sphere (finrank_piLp_quaternion_fin_succ 2 n)
    (by omega) v R (by rwa [show 4 * n + 3 - 1 = 4 * n + 2 by omega, Nat.dvd_iff_mod_eq_zero])

/-- The homology of `ΩS⁴ⁿ⁺³` in the degrees divisible by `4n + 2`, in the degree normal form
`(4n + 2)j` of this file: `H_{(4n+2)j}(ΩS⁴ⁿ⁺³; R) ≅ R`. -/
private def singularHomologyMooreLoopSpaceSphereMulIso (R : Type) [Ring R] (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) ((4 * n + 2) * j)).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v)) ≅
      ModuleCat.of R R :=
  eqToIso (by rw [show 4 * n + 3 - 1 = 4 * n + 2 by omega, mul_comm]) ≪≫
    singularHomologyMooreLoopSpaceSphereIso (finrank_piLp_quaternion_fin_succ 2 n) (by omega) v
      R j

/-- For `n ≥ 1`, the degree `(4n + 2)j + 3` is `3` modulo `4n + 2`. -/
private lemma mul_add_three_mod (hn : n ≠ 0) (j : ℕ) :
    ((4 * n + 2) * j + 3) % (4 * n + 2) = 3 := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (show 3 < 4 * n + 2 by omega)]

/-- For `n ≥ 1`, a degree `k ≥ 3` which is not `3` modulo `4n + 2` has `k - 3` not divisible by
`4n + 2`. -/
private lemma sub_three_mod_ne_zero (hn : n ≠ 0) {k : ℕ} (hk : 3 ≤ k)
    (hk₃ : k % (4 * n + 2) ≠ 3) :
    (k - 3) % (4 * n + 2) ≠ 0 := fun h ↦ hk₃ <| by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
  rw [show k = (4 * n + 2) * c + 3 by omega, mul_add_three_mod hn]

/-- **The homology of `ΩHPⁿ` vanishes in the degrees that are not `0` or `3` modulo `4n + 2`**,
with coefficients in any ring, for `n ≥ 1`. -/
theorem isZero_singularHomology_mooreLoopSpace (hn : n ≠ 0) (R : Type) [Ring R] {k : ℕ}
    (hk₀ : k % (4 * n + 2) ≠ 0) (hk₃ : k % (4 * n + 2) ≠ 3) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v)))) := by
  obtain ⟨j, -, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) k
  refine IsZero.of_iso ?_ (asIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj
    (ModuleCat.of R R)).map (TopCat.ofHom (hopfProduct v j)))).symm
  -- `ΩHPⁿ` is weakly equivalent to `S³ × ΩS⁴ⁿ⁺³`, whose `H_k` vanishes with `H_k` and `H_{k-3}`
  -- of `ΩS⁴ⁿ⁺³`; below degree `3` only `H_k` of `ΩS⁴ⁿ⁺³` contributes.
  rcases lt_or_ge k 3 with hk3 | hk3
  · exact (isZero_singularHomology_sphere_prod_iff_of_lt _ Quaternion.finrank_eq_four hk3).2
      (isZero_singularHomology_mooreLoopSpace_sphere_of_mod_ne_zero v R hk₀)
  · exact (isZero_singularHomology_sphere_prod_iff _ Quaternion.finrank_eq_four
      (n := k - 3) (by omega)).2
      ⟨isZero_singularHomology_mooreLoopSpace_sphere_of_mod_ne_zero v R hk₀,
        isZero_singularHomology_mooreLoopSpace_sphere_of_mod_ne_zero v R
          (sub_three_mod_ne_zero hn hk3 hk₃)⟩

/-- **The looped Hopf map `Ωq : ΩS⁴ⁿ⁺³ → ΩHPⁿ` is an isomorphism on `H_k` unless `k` is `3`
modulo `4n + 2`**, with coefficients in any ring, for `n ≥ 1`. In particular it is one on
`H_{(4n+2)j}` for every `j`. -/
theorem isIso_singularHomologyMap_mooreLoopSpaceMap (hn : n ≠ 0) (R : Type) [Ring R] {k : ℕ}
    (hk₃ : k % (4 * n + 2) ≠ 3) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).map
      (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap)) := by
  obtain ⟨j, hj, hw⟩ := exists_isWeakHomotopyEquivalence_hopfProduct v hn
  rw [← hopfProduct_comp_prodMk_const_one v hj, TopCat.ofHom_comp, Functor.map_comp]
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) k
  -- The inclusion at `1` is an isomorphism on `H_k`, since `H_{k-3}(ΩS⁴ⁿ⁺³)` vanishes.
  have : IsIso (((singularHomologyFunctor (ModuleCat.{0} R) k).obj (ModuleCat.of R R)).map
      (TopCat.ofHom ((ContinuousMap.const _ (1 : sphere (0 : ℍ) 1)).prodMk (ContinuousMap.id
        (MooreLoopSpace (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) v))))) := by
    rcases lt_or_ge k 3 with hk3 | hk3
    · exact isIso_singularHomologyMap_prodMk_sphere_of_lt _ Quaternion.finrank_eq_four 1 hk3
    · exact (isIso_singularHomologyMap_prodMk_sphere_iff _ Quaternion.finrank_eq_four 1
        (n := k - 3) (by omega)).2
        (isZero_singularHomology_mooreLoopSpace_sphere_of_mod_ne_zero v R
          (sub_three_mod_ne_zero hn hk3 hk₃))
  infer_instance

/-- **The homology of `ΩHPⁿ` in the degrees divisible by `4n + 2`**: `H_{(4n+2)j}(ΩHPⁿ; R) ≅ R`
for every `j`, with coefficients in any ring, for `n ≥ 1`. It is the inverse of the isomorphism
induced by the looped Hopf map `Ωq : ΩS⁴ⁿ⁺³ → ΩHPⁿ`, followed by
`TauCeti.singularHomologyMooreLoopSpaceSphereIso`. -/
def singularHomologyMooreLoopSpaceIso (hn : n ≠ 0) (R : Type) [Ring R] (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) ((4 * n + 2) * j)).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))) ≅
      ModuleCat.of R R :=
  have := isIso_singularHomologyMap_mooreLoopSpaceMap v hn R (k := (4 * n + 2) * j)
    (by rw [Nat.mul_mod_right]; omega)
  (asIso (((singularHomologyFunctor (ModuleCat.{0} R) ((4 * n + 2) * j)).obj
      (ModuleCat.of R R)).map (TopCat.ofHom
        (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap))).symm ≪≫
    singularHomologyMooreLoopSpaceSphereMulIso v R j

/-- **The homology of `ΩHPⁿ` in the degrees `3` modulo `4n + 2`**: `H_{(4n+2)j+3}(ΩHPⁿ; R) ≅ R`
for every `j`, with coefficients in any ring, for `n ≥ 1`. Through the weak homotopy equivalence
`j ⋆ Ωq : S³ × ΩS⁴ⁿ⁺³ → ΩHPⁿ` it is `H_{(4n+2)j+3}(S³ × ΩS⁴ⁿ⁺³) ≅ H_{(4n+2)j}(ΩS⁴ⁿ⁺³)`
(`TauCeti.singularHomologySphereProdIso`), followed by
`TauCeti.singularHomologyMooreLoopSpaceSphereIso`. -/
def singularHomologyMooreLoopSpaceAddThreeIso (hn : n ≠ 0) (R : Type) [Ring R] (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) ((4 * n + 2) * j + 3)).obj
        (ModuleCat.of R R)).obj
        (TopCat.of (MooreLoopSpace (QuaternionicProjectiveSpace n) (mk n v))) ≅
      ModuleCat.of R R :=
  have hw := (exists_isWeakHomotopyEquivalence_hopfProduct v hn).choose_spec.2
  have := hw.isIso_singularHomologyMap (ModuleCat.of R R) ((4 * n + 2) * j + 3)
  (asIso (((singularHomologyFunctor (ModuleCat.{0} R) ((4 * n + 2) * j + 3)).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (hopfProduct v
        (exists_isWeakHomotopyEquivalence_hopfProduct v hn).choose)))).symm ≪≫
    singularHomologySphereProdIso _ Quaternion.finrank_eq_four rfl
      (isZero_singularHomology_mooreLoopSpace_sphere_of_mod_ne_zero v R
        (by rw [mul_add_three_mod hn]; omega)) ≪≫
    singularHomologyMooreLoopSpaceSphereMulIso v R j

/-! ### The integral generator -/

section Integral

variable (v : sphere (0 : PiLp 2 fun _ : Fin (n + 2) ↦ ℍ) 1)

private instance isIso_homologyMap_mooreLoopSpaceMap :
    IsIso (HomologicalComplex.homologyMap ((singularChains ℤ).map
      (TopCat.ofHom (MooreLoopSpace.map (x := v) ⟨mk (n + 1), continuous_mk (n + 1)⟩
        rfl).toContinuousMap)) (4 * n + 6)) := by
  have h := isIso_singularHomologyMap_mooreLoopSpaceMap v n.succ_ne_zero ℤ
    (k := 4 * (n + 1) + 2) (by rw [Nat.mod_self]; omega)
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
