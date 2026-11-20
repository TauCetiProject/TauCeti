/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
public import TauCeti.Topology.Grassmannian.StiefelFibration.Exact
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# The first homotopy group of the Stiefel manifold of two-frames of an odd space

Let `V₂(ℝ^N)` be the Stiefel manifold of orthonormal two-frames `(u, v)` of `ℝ^N`, the unit
tangent bundle of the sphere `S^(N-1)`. Forgetting the second vector is a sphere bundle
`S^(N-2) → V₂(ℝ^N) → S^(N-1)` (`TauCeti.finiteOrthonormalFrame.forgetLast_mem_serreFibrations`),
and `V₂(ℝ^N)` is `(N - 3)`-connected, so its first possibly nontrivial homotopy group is
`π_(N-2)`. This file proves that this group is a torsion group when `N` is odd and at least `5`:
in the notation `N = n + 4` with `n` odd, every element of `π_(n+2)(V₂(ℝ^(n+4)))` has finite order
(`TauCeti.finiteOrthonormalFrame.isMulTorsion_homotopyGroup_two`).

The proof reads the exact homotopy sequence of the sphere bundle,

`π_(n+3)(V₂) → π_(n+3)(S^(n+3)) → π_(n+2)(S^(n+2)) → π_(n+2)(V₂) → π_(n+2)(S^(n+3)) = 0`.

* **The first vector is trivial on `π_(n+3)`.** The first vector `u` of a frame is homotopic to its
  antipode `-u`, through the rotation `cos(π t) u + sin(π t) v` towards the second vector
  (`TauCeti.finiteOrthonormalFrame.firstVectorHomotopy`). The antipodal map of the
  even-dimensional sphere `S^(n+3)` acts by `-1` on `H_(n+3)(S^(n+3); ℤ) ≅ ℤ`
  (`TauCeti.reducedSingularHomologyFunctor_map_sphere_neg`). So the Hurewicz class of the image of
  any class of `π_(n+3)(V₂)` equals its negative, hence vanishes, and since the Hurewicz map of the
  sphere is an isomorphism onto a group without torsion the image itself is trivial
  (`TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_one`).
* **The boundary map is nonzero.** By exactness at `π_(n+3)(S^(n+3)) ≅ ℤ`, every nontrivial class
  has a nontrivial boundary in `π_(n+2)(S^(n+2))`
  (`TauCeti.finiteOrthonormalFrame.exists_fibrationBoundary_forgetLast_ne`).
* **The quotient is finite.** As `π_(n+2)(S^(n+3))` vanishes, every class of `π_(n+2)(V₂)` comes
  from the fibre `π_(n+2)(S^(n+2)) ≅ ℤ`. In `ℤ` a nonzero multiple of every element lies in the
  nonzero image of the boundary map, which dies in `V₂`.

The first step is the argument of the hairy ball theorem, read in homotopy groups. The boundary
map in fact sends a generator of `π_(n+3)(S^(n+3))` to `±2` times a generator, the Euler
characteristic of the sphere, so the group is `ℤ/2`; that computation is not made here.

In the exact sequence `π_m(V₂(ℝ^(2+m))) → π_(m-1)(SO(m)) → π_(m-1)(SO(2 + m))` of the Stiefel
fibration `SO(m) → SO(2 + m) → V₂(ℝ^(2+m))` (`TauCeti.specialOrthogonalFrameBoundary`), the group
`π_m(V₂(ℝ^(2+m)))` is the Stiefel term. For odd `m ≥ 3` it is a torsion group, so `π_(m-1)(SO(m))`
is a torsion group as soon as the group `π_(m-1)(SO(2 + m))`, already in the stable range, is
(`TauCeti.isMulTorsion_homotopyGroup_specialOrthogonalGroup_of_two_add`). For the odd sphere
`S^m`, this torsion is the hypothesis of
`TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion`.

## Main results

* `TauCeti.finiteOrthonormalFrame.firstVectorHomotopy`: the first vector of a two-frame is
  homotopic to its antipode.
* `TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_one`: for odd `n`, forgetting the
  second vector is trivial on `π_(n+3)`.
* `TauCeti.finiteOrthonormalFrame.exists_fibrationBoundary_forgetLast_ne`: for odd `n`, the
  boundary map `π_(n+3)(S^(n+3)) → π_(n+2)(S^(n+2))` of the sphere bundle is nontrivial.
* `TauCeti.finiteOrthonormalFrame.isMulTorsion_homotopyGroup_two`: for odd `N ≥ 5`, the group
  `π_(N-2)(V₂(ℝ^N))` is a torsion group.
* `TauCeti.isMulTorsion_homotopyGroup_specialOrthogonalGroup_of_two_add`: for odd `m ≥ 3`, if
  `π_(m-1)(SO(2 + m))` is a torsion group, then so is `π_(m-1)(SO(m))`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2, Example 4.55 (the
  homotopy groups of `V₂(ℝⁿ)` from the sphere bundle `S^(n-2) → V₂(ℝⁿ) → S^(n-1)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 6.35.
-/

public section

noncomputable section

open CategoryTheory Matrix Metric Set
open scoped Topology.Homotopy

namespace TauCeti.finiteOrthonormalFrame

variable {N : ℕ}

/-! ### The first vector and its antipode -/

/-- The first vector of an orthonormal two-frame of `ℝ^N`, a point of the unit sphere. -/
def firstVector (N : ℕ) :
    C(finiteOrthonormalFrame ℝ 2 N, sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  ⟨fun f ↦ sphereHomeomorph N (forgetLast f), by fun_prop⟩

/-- The first vector map reads off the first vector of the frame. -/
@[simp]
theorem coe_firstVector_apply (f : finiteOrthonormalFrame ℝ 2 N) :
    (firstVector N f : EuclideanSpace ℝ (Fin N)) = WithLp.toLp 2 (f.1 0) := by
  simp [firstVector]

/-- The second vector of an orthonormal two-frame of `ℝ^N`, a point of the unit sphere. -/
private def secondVector (f : finiteOrthonormalFrame ℝ 2 N) :
    sphere (0 : EuclideanSpace ℝ (Fin N)) 1 :=
  ⟨WithLp.toLp 2 (f.1 1), mem_sphere_zero_iff_norm.2 (f.2.1 1)⟩

/-- The second vector of a frame depends continuously on the frame. -/
private theorem continuous_secondVector :
    Continuous (secondVector : finiteOrthonormalFrame ℝ 2 N → _) :=
  ((PiLp.continuous_toLp 2 _).comp ((continuous_apply 1).comp continuous_subtype_val)).subtype_mk _

/-- The two vectors of an orthonormal two-frame are orthogonal. -/
private theorem inner_firstVector_secondVector (f : finiteOrthonormalFrame ℝ 2 N) :
    inner ℝ (firstVector N f : EuclideanSpace ℝ (Fin N)) (secondVector f) = 0 := by
  rw [coe_firstVector_apply]
  exact f.2.2 (by decide : (0 : Fin 2) ≠ 1)

/-- **The first vector of a two-frame is homotopic to its antipode**, through the rotation
`(t, (u, v)) ↦ cos(π t) • u + sin(π t) • v` of the first vector towards the second. -/
def firstVectorHomotopy (N : ℕ) :
    ContinuousMap.Homotopy (firstVector N)
      ((⟨Neg.neg, continuous_neg⟩ : C(sphere (0 : EuclideanSpace ℝ (Fin N)) 1, _)).comp
        (firstVector N)) where
  toFun p := ⟨Real.cos (Real.pi * p.1) • (firstVector N p.2 : EuclideanSpace ℝ (Fin N)) +
      Real.sin (Real.pi * p.1) • (secondVector p.2 : EuclideanSpace ℝ (Fin N)),
    mem_sphere_zero_iff_norm.2 (TauCeti.norm_cos_smul_add_sin_smul (firstVector N p.2)
      (secondVector p.2) (inner_firstVector_secondVector p.2) _)⟩
  continuous_toFun := by
    have ht : Continuous fun p : unitInterval × finiteOrthonormalFrame ℝ 2 N ↦
        Real.pi * (p.1 : ℝ) :=
      continuous_const.mul (continuous_subtype_val.comp continuous_fst)
    exact (((Real.continuous_cos.comp ht).smul (continuous_subtype_val.comp
      ((firstVector N).continuous.comp continuous_snd))).add
      ((Real.continuous_sin.comp ht).smul (continuous_subtype_val.comp
        (continuous_secondVector.comp continuous_snd)))).subtype_mk _
  map_zero_left f := by
    apply Subtype.ext
    simp
  map_one_left f := by
    apply Subtype.ext
    simp

/-! ### The first vector on the top homotopy group -/

/-- On the top integral homology of an even-dimensional sphere `S^(m+1)`, the first vector map
`V₂(ℝ^(m+2)) → S^(m+1)` induces the negative of itself, as it is homotopic to its antipode. -/
private theorem singularHomologyMap_firstVector_eq_neg {m : ℕ} (hm : Odd m) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (firstVector (m + 2))) =
      -((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (firstVector (m + 2))) := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj
    (ModuleCat.of ℤ ℤ)
  let ν : C(sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1, _) := ⟨Neg.neg, continuous_neg⟩
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 1 + 1 := by simp
  -- The antipodal map acts by `(-1) ^ (m + 2) = -1` on `H_(m+1)(S^(m+1); ℤ)`.
  have hν : H.map (TopCat.ofHom ν) = -𝟙 _ := by
    let α := (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) m).hom
    apply (cancel_epi (α.app (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)))).1
    rw [← α.naturality, reducedSingularHomologyFunctor_map_sphere_neg (ModuleCat.of ℤ ℤ) hE,
      (by simpa [add_assoc] using hm.add_even even_two : Odd (m + 1 + 1)).neg_one_pow,
      Preadditive.comp_neg, Category.comp_id, neg_one_zsmul,
      Preadditive.neg_comp, Category.id_comp]
  have hhom : H.map (TopCat.ofHom (firstVector (m + 2))) =
      H.map (TopCat.ofHom (ν.comp (firstVector (m + 2)))) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom (firstVector (m + 2))) (g := TopCat.ofHom (ν.comp (firstVector (m + 2))))
      (firstVectorHomotopy (m + 2)) (ModuleCat.of ℤ ℤ) (m + 1)
  conv_lhs => rw [hhom, TopCat.ofHom_comp, Functor.map_comp, hν, Preadditive.comp_neg,
    Category.comp_id]

/-- **The first vector is trivial on `π_(n+3)` for odd `n`.** The first vector map
`V₂(ℝ^(n+4)) → S^(n+3)` is homotopic to its antipode, and the antipodal map of the
even-dimensional sphere `S^(n+3)` acts by `-1` on its integral homology `ℤ`. So the Hurewicz class
of the image of every class of `π_(n+3)(V₂(ℝ^(n+4)))` is its own negative, hence zero, and the
image itself is trivial since the Hurewicz map of the sphere is injective. -/
theorem homotopyGroupMap_firstVector_eq_one {n : ℕ} (hn : Odd n)
    (f : finiteOrthonormalFrame ℝ 2 (n + 4))
    (a : HomotopyGroup (Fin (n + 3)) (finiteOrthonormalFrame ℝ 2 (n + 4)) f) :
    HomotopyGroup.map (firstVector (n + 4)) rfl a = 1 := by
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 4))) = n + 3 + 1 := by simp
  have hX : ∀ k < n + 3, Subsingleton
      (HomotopyGroup (Fin k) (sphere (0 : EuclideanSpace ℝ (Fin (n + 4))) 1)
        (firstVector (n + 4) f)) :=
    fun k hk ↦ subsingleton_homotopyGroup_sphere_of_lt hE (by simpa using hk) _
  let ψ := HomotopyGroup.hurewiczAddEquiv (n := n + 1) hX
  let φ := homotopyGroupSphereAddEquiv (n := n + 1) (EuclideanSpace.basisFun (Fin (n + 4)) ℝ)
    (firstVector (n + 4) f)
  set c := HomotopyGroup.map (firstVector (n + 4)) rfl a
  -- The Hurewicz class of `c` is the image of that of `a`, which is its own negative.
  have hψ : ψ (Additive.ofMul c) = (HomotopyGroup.hurewicz (ModuleCat.of ℤ ℤ) (n + 2) a ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 3)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (firstVector (n + 4)))).hom 1 := by
    simp only [ψ, c, HomotopyGroup.hurewiczAddEquiv_apply, HomotopyGroup.hurewiczHom_apply,
      toMul_ofMul, HomotopyGroup.hurewicz_map]
  have hneg : ψ (Additive.ofMul c) = -ψ (Additive.ofMul c) := by
    rw [hψ]
    nth_rewrite 1 [singularHomologyMap_firstVector_eq_neg (m := n + 2) (hn.add_even even_two)]
    rw [Preadditive.comp_neg, ModuleCat.hom_neg, LinearMap.neg_apply]
  -- In `ℤ` the only such element is zero.
  have hzero : φ (ψ.symm (ψ (Additive.ofMul c))) = 0 := by
    have h := congrArg (fun y ↦ φ (ψ.symm y)) hneg
    simp only [map_neg] at h
    omega
  rw [AddEquiv.symm_apply_apply, AddEquiv.map_eq_zero_iff] at hzero
  exact hzero

/-! ### The exact sequence of the sphere bundle -/

/-- **Forgetting the second vector is trivial on `π_(n+3)` for odd `n`**, read in the Stiefel
manifold `V₁(ℝ^(n+4))` of one-frames, the base of the sphere bundle
`S^(n+2) → V₂(ℝ^(n+4)) → V₁(ℝ^(n+4))`. -/
theorem homotopyGroupMap_forgetLast_eq_one {n : ℕ} (hn : Odd n)
    (f : finiteOrthonormalFrame ℝ 2 (n + 4))
    (a : HomotopyGroup (Fin (n + 3)) (finiteOrthonormalFrame ℝ 2 (n + 4)) f) :
    HomotopyGroup.map ⟨forgetLast, continuous_forgetLast⟩ rfl a = 1 := by
  apply (HomotopyGroup.homeomorphEquiv (sphereHomeomorph (n + 4)) (forgetLast f)).injective
  rw [HomotopyGroup.homeomorphEquiv_apply, HomotopyGroup.homeomorphEquiv_apply,
    HomotopyGroup.map_comp_apply, HomotopyGroup.map_one]
  exact homotopyGroupMap_firstVector_eq_one hn f a

/-- **The boundary map of the sphere bundle is nontrivial** for odd `n`: some class of
`π_(n+3)(V₁(ℝ^(n+4))) ≅ π_(n+3)(S^(n+3))` has a nontrivial boundary in the homotopy group
`π_(n+2)(S^(n+2))` of the fibre. By exactness, a class with trivial boundary comes from
`V₂(ℝ^(n+4))`, where forgetting the second vector is trivial
(`TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_one`), while `π_(n+3)(S^(n+3))` is
nontrivial. -/
theorem exists_fibrationBoundary_forgetLast_ne {n : ℕ} (hn : Odd n)
    (f : finiteOrthonormalFrame ℝ 2 (n + 4)) :
    ∃ b : HomotopyGroup (Option (Fin (n + 2))) (finiteOrthonormalFrame ℝ 1 (n + 4)) (forgetLast f),
      TopCat.fibrationBoundary (forgetLast_mem_serreFibrations (r := 1) (N := n + 4) (by omega))
        ⟨f, rfl⟩ b ≠ 1 := by
  let ε := (finSuccEquiv (n + 2)).symm
  have : Nontrivial
      (HomotopyGroup (Fin (n + 3)) (finiteOrthonormalFrame ℝ 1 (n + 4)) (forgetLast f)) := by
    have := nontrivial_homotopyGroup_sphere (n := n + 1) (by simp)
      (sphereHomeomorph (n + 4) (forgetLast f))
    exact (HomotopyGroup.homeomorphEquiv (sphereHomeomorph (n + 4)) (forgetLast f)).nontrivial
  obtain ⟨c, hc⟩ := exists_ne
    (1 : HomotopyGroup (Fin (n + 3)) (finiteOrthonormalFrame ℝ 1 (n + 4)) (forgetLast f))
  refine ⟨(HomotopyGroup.congrEquiv ε).symm c, fun h ↦ hc ?_⟩
  rw [← HomotopyGroup.mk_const_eq_one] at h
  obtain ⟨d, hd⟩ := (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq
    (forgetLast_mem_serreFibrations (r := 1) (N := n + 4) (by omega)) (e := ⟨f, rfl⟩)).2 h
  have hd' := congrArg (HomotopyGroup.congrEquiv ε) hd
  rw [← HomotopyGroup.map_congrEquiv, Equiv.apply_symm_apply] at hd'
  rw [← hd']
  exact homotopyGroupMap_forgetLast_eq_one hn f _

/-! ### The Stiefel term -/

/-- `π_(n+2)(V₂(ℝ^(n+4)))` is a torsion group for odd `n`, with the cube directions indexed by
`Fin (n + 2)`. Every class comes from the fibre `π_(n+2)(S^(n+2)) ≅ ℤ` of the sphere bundle
`V₂(ℝ^(n+4)) → S^(n+3)`, and in `ℤ` a nonzero multiple of every element lies in the nonzero image
of the boundary map, which dies in `V₂(ℝ^(n+4))`. -/
private theorem isMulTorsion_homotopyGroup_two_fin {n : ℕ} (hn : Odd n)
    (f : finiteOrthonormalFrame ℝ 2 (n + 4)) :
    IsMulTorsion (HomotopyGroup (Fin (n + 2)) (finiteOrthonormalFrame ℝ 2 (n + 4)) f) := by
  let p : _root_.TopCat.of (finiteOrthonormalFrame ℝ 2 (n + 4)) ⟶
      _root_.TopCat.of (finiteOrthonormalFrame ℝ 1 (n + 4)) :=
    _root_.TopCat.ofHom ⟨forgetLast, continuous_forgetLast⟩
  have hp : TopCat.serreFibrations p := forgetLast_mem_serreFibrations (by omega)
  let e : p.fiber (forgetLast f) := ⟨f, rfl⟩
  -- The fibre is a sphere of dimension `n + 2`, whose homotopy group in that degree is `ℤ`.
  let φF : p.fiber (forgetLast f) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 4 - 1))) 1 :=
    ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (forgetLastFiberSphere (forgetLast f))
  let ψ : Additive (HomotopyGroup (Fin (n + 2)) (p.fiber (forgetLast f)) e) ≃+ ℤ :=
    (HomotopyGroup.homeomorphMulEquiv φF e).toAdditive.trans
      (homotopyGroupSphereAddEquiv (n := n)
        ((EuclideanSpace.basisFun (Fin (n + 4 - 1)) ℝ).reindex (finCongr (by omega))) (φF e))
  obtain ⟨b, hb⟩ := exists_fibrationBoundary_forgetLast_ne hn f
  set w := TopCat.fibrationBoundary hp e b
  have hwι : HomotopyGroup.map (p.fiberι (forgetLast f)).hom
      (TopCat.Hom.fiberι_apply _ _ e) w = 1 := by
    rw [← HomotopyGroup.mk_const_eq_one]
    exact (TopCat.mem_range_fibrationBoundary_iff hp).1 ⟨b, rfl⟩
  have hB : ψ (Additive.ofMul w) ≠ 0 := by
    rw [Ne, AddEquiv.map_eq_zero_iff, ofMul_eq_zero]
    exact hb
  intro y
  -- Every class of `V₂(ℝ^(n+4))` comes from the fibre, since the base is `(n + 2)`-connected.
  obtain ⟨z, rfl⟩ : y ∈ range (HomotopyGroup.map (p.fiberι (forgetLast f)).hom
      (TopCat.Hom.fiberι_apply _ _ e)) := by
    have : Subsingleton (HomotopyGroup (Fin (n + 2)) (finiteOrthonormalFrame ℝ 1 (n + 4))
        (forgetLast f)) := subsingleton_homotopyGroup (by simp) _
    exact (TopCat.mem_range_homotopyGroupMap_fiberι_iff hp).2 (Subsingleton.elim _ _)
  -- In `ℤ`, the multiple `B • z` of `z` is the multiple `A • w` of the boundary class `w`.
  have hzw : z ^ ψ (Additive.ofMul w) = w ^ ψ (Additive.ofMul z) := by
    apply Additive.ofMul.injective
    apply ψ.injective
    rw [ofMul_zpow, ofMul_zpow, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm]
  refine isOfFinOrder_iff_zpow_eq_one.2 ⟨ψ (Additive.ofMul w), hB, ?_⟩
  rw [← HomotopyGroup.mapHom_apply, ← map_zpow, HomotopyGroup.mapHom_apply, hzw,
    ← HomotopyGroup.mapHom_apply, map_zpow, HomotopyGroup.mapHom_apply, hwι, _root_.one_zpow]

/-- **The first possibly nontrivial homotopy group of `V₂(ℝ^N)` is a torsion group for odd
`N ≥ 5`.** For the Stiefel manifold of orthonormal two-frames of an odd-dimensional space `ℝ^N`,
the unit tangent bundle of the even-dimensional sphere `S^(N-1)`, every element of `π_(N-2)` has
finite order. Here `π_(N-2)` is modelled on the cube `I^M` for a finite type `M` of cardinality
`N - 2`. -/
theorem isMulTorsion_homotopyGroup_two {N : ℕ} (hN : Odd N) (h5 : 5 ≤ N) {M : Type*} [Finite M]
    [DecidableEq M] [Nonempty M] (hM : Nat.card M + 2 = N) (f : finiteOrthonormalFrame ℝ 2 N) :
    IsMulTorsion (HomotopyGroup M (finiteOrthonormalFrame ℝ 2 N) f) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 4 := ⟨N - 4, by omega⟩
  have hn : Odd n := (Nat.odd_add.1 hN).2 (by decide)
  have := Fintype.ofFinite M
  let e : M ≃ Fin (n + 2) := Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; omega)
  intro y
  obtain ⟨k, hk, hyk⟩ := isOfFinOrder_iff_pow_eq_one.1
    (isMulTorsion_homotopyGroup_two_fin hn f (HomotopyGroup.congrMulEquiv e y))
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, (HomotopyGroup.congrMulEquiv e).injective ?_⟩
  rw [map_pow, hyk, map_one]

end TauCeti.finiteOrthonormalFrame

namespace TauCeti

/-! ### The homotopy group `π_(m-1)(SO(m))` for odd `m` -/

/-- **`π_(m-1)(SO(m))` is a torsion group for odd `m ≥ 3` as soon as `π_(m-1)(SO(m + 2))` is.**
In the exact sequence `π_m(V₂(ℝ^(2+m))) → π_(m-1)(SO(m)) → π_(m-1)(SO(2 + m))` of the Stiefel
fibration `SO(m) → SO(2 + m) → V₂(ℝ^(2+m))` (`TauCeti.specialOrthogonalFrameBoundary`), the Stiefel
term `π_m(V₂(ℝ^(2+m)))` is a torsion group
(`TauCeti.finiteOrthonormalFrame.isMulTorsion_homotopyGroup_two`). So a class of `π_(m-1)(SO(m))`
whose image in `π_(m-1)(SO(2 + m))` has finite order has a power which is a boundary, hence of
finite order. Here `π_(m-1)` is modelled on the cube `I^N` for a finite type `N` of cardinality
`m - 1`. -/
theorem isMulTorsion_homotopyGroup_specialOrthogonalGroup_of_two_add {m : ℕ} (hm : Odd m)
    (h3 : 3 ≤ m) {N : Type*} [Finite N] [DecidableEq N] [Nonempty N] (hN : Nat.card N + 1 = m)
    (h : IsMulTorsion (HomotopyGroup N (specialOrthogonalGroup (Fin (2 + m)) ℝ) 1)) :
    IsMulTorsion (HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1) := by
  have : NeZero m := ⟨by omega⟩
  intro y
  -- The image of `y` in `π_(m-1)(SO(2 + m))` has finite order.
  let ι := HomotopyGroup.mapHom (N := N) ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 2 m,
    finiteOrthonormalFrame.continuous_fromBlocksOne m⟩
    (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 2 m))
  obtain ⟨a, ha, hya⟩ := isOfFinOrder_iff_pow_eq_one.1 (h (ι y))
  -- So `y ^ a` is the boundary of a class of the Stiefel term, which has finite order.
  obtain ⟨x, hx⟩ : y ^ a ∈ range (specialOrthogonalFrameBoundary 2 m N) := by
    refine mem_range_specialOrthogonalFrameBoundary_iff.2 ?_
    rw [HomotopyGroup.mk_const_eq_one, ← HomotopyGroup.mapHom_apply, map_pow]
    exact hya
  obtain ⟨b, hb, hxb⟩ := isOfFinOrder_iff_pow_eq_one.1
    (finiteOrthonormalFrame.isMulTorsion_homotopyGroup_two (even_two.add_odd hm)
      (by omega) (by simp; omega) _ x)
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [pow_mul, ← hx, ← specialOrthogonalFrameBoundary_pow, hxb, specialOrthogonalFrameBoundary_one]

end TauCeti
