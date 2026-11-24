/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Antipodal
public import TauCeti.Topology.Grassmannian.StiefelFibration.Exact
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric

/-!
# The two-frame Stiefel manifolds of odd-dimensional spaces

For `N` odd the sphere `S^(N-1)` has even dimension, and the Stiefel manifold `V₂(ℝ^N)` of
orthonormal two-frames is its unit tangent bundle: forgetting the second vector,
`V₂(ℝ^N) → V₁(ℝ^N) ≅ S^(N-1)`, is a sphere bundle with fibre `S^(N-2)`, and the second vector of a
frame is a unit vector orthogonal to its first. So the projection is homotopic to its antipode,
through half great circles, and is therefore trivial on `π_(N-1)`
(`TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_const`). This is the homotopical
form of the hairy ball theorem.

In the exact homotopy sequence

`π_(N-1)(V₂) → π_(N-1)(S^(N-1)) → π_(N-2)(S^(N-2)) → π_(N-2)(V₂) → π_(N-2)(S^(N-1)) = 0`

of the sphere bundle, the boundary map is therefore injective on `π_(N-1)(S^(N-1)) ≅ ℤ`, so its
image is a nonzero subgroup of `π_(N-2)(S^(N-2)) ≅ ℤ`. For `N ≥ 5` this makes `π_(N-2)(V₂(ℝ^N))`,
the quotient of `ℤ` by that subgroup, a finite group
(`TauCeti.finiteOrthonormalFrame.finite_homotopyGroup_twoFrame`). (The boundary map is in fact
multiplication by the Euler characteristic `2` of `S^(N-1)`, so the group is `ℤ/2`; only its
finiteness is proved here.)

For odd `m = n + 1` this is the Stiefel term `π_m(V₂(ℝ^(m+2)))` in the exact sequence

`π_m(V₂(ℝ^(m+2))) → π_(m-1)(SO(m)) → π_(m-1)(SO(m + 2))`

of the fibration `SO(m) → SO(m + 2) → V₂(ℝ^(m+2))`. So the stabilization map
`π_(m-1)(SO(m)) → π_(m-1)(SO(m + 2))`, whose target is already the stable group `π_(m-1)(SO)`, has
a kernel all of whose elements have finite order
(`TauCeti.isOfFinOrder_of_homotopyGroupMap_fromBlocksOne_eq_one`), and `π_(m-1)(SO(m))` is a torsion
group as soon as the stable group is
(`TauCeti.isMulTorsion_homotopyGroup_specialOrthogonalGroup_of_isMulTorsion`). By real Bott
periodicity the stable groups `π_(m-1)(SO)` for odd `m` are `0` or `ℤ/2`, which gives the torsion
of `π_(m-1)(SO(m))` used for odd spheres in the first proof of Barraud–Damian–Humilière–Oancea's
Proposition 6.34, and stated as their Lemma 6.35.

## Main results

* `TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_const`: for `N` odd, forgetting
  the second vector `V₂(ℝ^N) → V₁(ℝ^N)` is trivial on `π_(N-1)`.
* `TauCeti.finiteOrthonormalFrame.finite_homotopyGroup_twoFrame`: for `N ≥ 5` odd,
  `π_(N-2)(V₂(ℝ^N))` is finite.
* `TauCeti.isOfFinOrder_of_homotopyGroupMap_fromBlocksOne_eq_one`: for `n ≥ 2` even, every class of
  `π_n(SO(n + 1))` that dies in `π_n(SO(n + 3))` has finite order.
* `TauCeti.isMulTorsion_homotopyGroup_specialOrthogonalGroup_of_isMulTorsion`: for `n ≥ 2` even,
  if `π_n(SO(n + 3))` is a torsion group then so is `π_n(SO(n + 1))`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2, Example 4.55 and the
  exact sequences of the fibrations `S^(n-k-1) → V_(k+1)(ℝⁿ) → V_k(ℝⁿ)`.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.34 and Lemma 6.35.
-/

public section

noncomputable section

open CategoryTheory Matrix Metric Module Set
open scoped Topology.Homotopy

namespace TauCeti

namespace finiteOrthonormalFrame

/-- Forgetting the second vector of an orthonormal two-frame, as a continuous map. -/
private abbrev forgetSecond (N : ℕ) :
    C(finiteOrthonormalFrame ℝ 2 N, finiteOrthonormalFrame ℝ 1 N) :=
  ⟨forgetLast, continuous_forgetLast⟩

/-- The first vector of an orthonormal two-frame, as a point of the unit sphere. -/
private abbrev firstVector (N : ℕ) :
    C(finiteOrthonormalFrame ℝ 2 N, sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  (sphereHomeomorph ℝ N : C(finiteOrthonormalFrame ℝ 1 N, _)).comp (forgetSecond N)

/-- The second vector of an orthonormal two-frame, as a point of the unit sphere. -/
private def secondVector (N : ℕ) :
    C(finiteOrthonormalFrame ℝ 2 N, sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  ⟨fun g ↦ ⟨WithLp.toLp 2 (g.val 1), mem_sphere_zero_iff_norm.2 (g.property.1 1)⟩,
    ((PiLp.continuous_toLp 2 _).comp ((continuous_apply 1).comp continuous_subtypeVal)).subtype_mk
      _⟩

/-- The two vectors of an orthonormal two-frame are orthogonal. -/
private theorem inner_firstVector_secondVector {N : ℕ} (g : finiteOrthonormalFrame ℝ 2 N) :
    inner ℝ (firstVector N g : EuclideanSpace ℝ (Fin N)) (secondVector N g) = 0 := by
  simpa [secondVector] using g.property.2 (show (0 : Fin 2) ≠ 1 by decide)

/-- **The unit tangent bundle of an even-dimensional sphere is trivial on its top homotopy
group.** For `N` odd, forgetting the second vector `V₂(ℝ^N) → V₁(ℝ^N)`, the projection of the
unit tangent bundle of the even-dimensional sphere `V₁(ℝ^N) ≅ S^(N-1)`, induces the trivial map on
`π_(N-1)`, modelled on any finite index type `M` of `N - 1` cube directions. -/
theorem homotopyGroupMap_forgetLast_eq_const {N : ℕ} (hN : Odd N) {M : Type*} [Finite M]
    (hM : Nat.card M + 1 = N) (f : finiteOrthonormalFrame ℝ 2 N)
    (a : HomotopyGroup M (finiteOrthonormalFrame ℝ 2 N) f) :
    HomotopyGroup.map ⟨forgetLast, continuous_forgetLast⟩ rfl a =
      (⟦GenLoop.const⟧ : HomotopyGroup M (finiteOrthonormalFrame ℝ 1 N) (forgetLast f)) := by
  classical
  have h2 : 2 ≤ N := by simpa using f.property.linearIndependent.fintype_card_le_finrank
  obtain ⟨k, rfl⟩ := hN
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : Even (2 * n) := even_two_mul n
  let e : M ≃ Fin (2 * n + 2) := Finite.equivFinOfCardEq (by omega)
  -- The first vector is homotopic to its antipode, through the second vector.
  have hu := ContinuousMap.homotopyGroupMap_eq_one_of_homotopic_neg (by simp; omega) hn
    ((firstVector _).homotopic_neg_of_inner_eq_zero (secondVector _)
      inner_firstVector_secondVector) rfl (HomotopyGroup.congrEquiv e a)
  have hu' : HomotopyGroup.map (firstVector (2 * (n + 1) + 1)) rfl a =
      (⟦GenLoop.const⟧ : HomotopyGroup M _ (firstVector _ f)) := by
    apply (HomotopyGroup.congrEquiv e).injective
    rw [← HomotopyGroup.map_congrEquiv, hu, HomotopyGroup.congrEquiv_const, HomotopyGroup.one_def]
  -- Forgetting the second vector is the first vector, read in `V₁` through `sphereHomeomorph`.
  apply (HomotopyGroup.homeomorphEquiv (sphereHomeomorph ℝ _) (forgetLast f)).injective
  -- `homeomorphEquiv` is by definition `homeomorphEquivOfEq` at `rfl`.
  have hc : HomotopyGroup.homeomorphEquiv (sphereHomeomorph ℝ _) (forgetLast f)
      (⟦GenLoop.const⟧ : HomotopyGroup M _ (forgetLast f)) = ⟦GenLoop.const⟧ :=
    HomotopyGroup.homeomorphEquivOfEq_mk_const _ _
  rw [hc, HomotopyGroup.homeomorphEquiv_apply, HomotopyGroup.map_comp_apply]
  -- `firstVector` is by definition `sphereHomeomorph` composed with `forgetSecond`.
  exact hu'

/-- **The Stiefel manifold `V₂(ℝ^N)` has finite `π_(N-2)` for `N ≥ 5` odd.** In the exact homotopy
sequence of the sphere bundle `S^(N-2) → V₂(ℝ^N) → V₁(ℝ^N) ≅ S^(N-1)`, the projection is trivial on
`π_(N-1)` (`TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_const`), so the boundary
map `π_(N-1)(S^(N-1)) → π_(N-2)(S^(N-2)) ≅ ℤ` has nonzero image, and `π_(N-2)(V₂(ℝ^N))` is the
quotient of `ℤ` by it. The group is modelled on any finite index type `M` of `N - 2` cube
directions. -/
theorem finite_homotopyGroup_twoFrame {N : ℕ} (hN : Odd N) (h5 : 5 ≤ N) {M : Type*} [Finite M]
    (hM : Nat.card M + 2 = N) (f : finiteOrthonormalFrame ℝ 2 N) :
    Finite (HomotopyGroup M (finiteOrthonormalFrame ℝ 2 N) f) := by
  classical
  have : Nonempty M := (Nat.card_pos_iff.1 (by omega : 0 < Nat.card M)).1
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 5 := ⟨N - 5, by omega⟩
  let p : TopCat.of (finiteOrthonormalFrame ℝ (1 + 1) (k + 5)) ⟶
      TopCat.of (finiteOrthonormalFrame ℝ 1 (k + 5)) :=
    TopCat.ofHom ⟨forgetLast, continuous_forgetLast⟩
  have hp : TopCat.serreFibrations p := forgetLast_mem_serreFibrations
  let e : p.fiber (forgetLast f) := ⟨f, rfl⟩
  -- The fibre is the sphere `S^(k+3)`, so its `π_(k+3)` is infinite cyclic, generated by `g`.
  let φ : p.fiber (forgetLast f) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (k + 1 + 3))) 1 :=
    ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (forgetLastFiberSphere (forgetLast f))
  let ψ : HomotopyGroup M (p.fiber (forgetLast f)) e ≃* Multiplicative ℤ :=
    (HomotopyGroup.homeomorphMulEquiv φ e).trans ((HomotopyGroup.congrMulEquiv
      (Finite.equivFinOfCardEq (by omega : Nat.card M = k + 1 + 2))).trans
        (AddEquiv.toMultiplicativeRight (homotopyGroupSphereAddEquiv
          (EuclideanSpace.basisFun (Fin (k + 1 + 3)) ℝ) (φ e))))
  let g := ψ.symm (.ofAdd 1)
  have hpow (x) : g ^ (ψ x).toAdd = x := by
    apply ψ.injective
    rw [map_zpow, MulEquiv.apply_symm_apply, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  -- A nontrivial class `a` of `π_(k+4)(V₁)` has a nontrivial boundary `∂ a`, since `a` does not
  -- come from `V₂`.
  have := nontrivial_homotopyGroup_oneFrame (k := k + 2) (M := Option M) (by simp; omega)
    (forgetLast f)
  obtain ⟨a, ha⟩ := exists_ne (α := HomotopyGroup (Option M) (finiteOrthonormalFrame ℝ 1 (k + 5))
    (forgetLast f)) ⟦GenLoop.const⟧
  have hbd : TopCat.fibrationBoundary hp e a ≠ 1 := fun h ↦ ha <| by
    obtain ⟨β, rfl⟩ := (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp).2
      (h.trans HomotopyGroup.one_def)
    -- `p.hom` is `⟨forgetLast, _⟩` by definition (`TopCat.hom_ofHom`), and `1 + 1` reduces to `2`.
    exact homotopyGroupMap_forgetLast_eq_const (by simpa using hN) (by simp; omega) f β
  -- The fibre inclusion `j` kills `∂ a`, and it is onto since `π_(k+3)(V₁)` is trivial.
  let j := HomotopyGroup.mapHom (N := M) (p.fiberι (forgetLast f)).hom
    (TopCat.Hom.fiberι_apply p _ e)
  have hjbd : j (TopCat.fibrationBoundary hp e a) = 1 :=
    (HomotopyGroup.mapHom_apply _ _ _).trans
      (((TopCat.mem_range_fibrationBoundary_iff hp).1 ⟨a, rfl⟩).trans HomotopyGroup.one_def.symm)
  have hj : Function.Surjective j := fun y ↦
    have : Subsingleton (HomotopyGroup M (finiteOrthonormalFrame ℝ 1 (k + 5)) (forgetLast f)) :=
      subsingleton_homotopyGroup_real (by omega) _
    (TopCat.mem_range_homotopyGroupMap_fiberι_iff hp).2 (Subsingleton.elim _ _)
  -- So `π_(k+3)(V₂)` is generated by `j g`, which has finite order.
  have hfin : IsOfFinOrder (j g) := isOfFinOrder_iff_zpow_eq_one.2
    ⟨(ψ (TopCat.fibrationBoundary hp e a)).toAdd,
      fun h0 ↦ hbd (by rw [← hpow (TopCat.fibrationBoundary hp e a), h0, zpow_zero]),
      by rw [← map_zpow, hpow, hjbd]⟩
  have := hfin.finite_zpowers
  refine Finite.of_surjective (Subtype.val : Subgroup.zpowers (j g) → _) fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hj y
  exact ⟨⟨j x, Subgroup.mem_zpowers_iff.2 ⟨(ψ x).toAdd, by rw [← map_zpow, hpow]⟩⟩, rfl⟩

end finiteOrthonormalFrame

/-- The block embedding `SO(n + 1) → SO(2 + (n + 1))`, `B ↦ diag(1₂, B)`, as a continuous map. -/
private abbrev blockEmbedding (n : ℕ) :
    C(specialOrthogonalGroup (Fin (n + 1)) ℝ, specialOrthogonalGroup (Fin (2 + (n + 1))) ℝ) :=
  ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 2 (n + 1),
    finiteOrthonormalFrame.continuous_fromBlocksOne (n + 1)⟩

/-- **The kernel of the stabilization `π_n(SO(n + 1)) → π_n(SO(n + 3))` is a torsion group.** For
`n ≥ 2` even, a class of `π_n(SO(n + 1))` that becomes trivial in `π_n(SO(n + 3))` under the
block embedding `B ↦ diag(1₂, B)` has finite order: by exactness of the homotopy sequence of
`SO(n + 1) → SO(n + 3) → V₂(ℝ^(n+3))` it is the boundary of a class of the finite group
`π_(n+1)(V₂(ℝ^(n+3)))`. -/
theorem isOfFinOrder_of_homotopyGroupMap_fromBlocksOne_eq_one {n : ℕ} [NeZero n] (hn : Even n)
    {c : HomotopyGroup (Fin n) (specialOrthogonalGroup (Fin (n + 1)) ℝ) 1}
    (hc : HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 2 (n + 1),
        finiteOrthonormalFrame.continuous_fromBlocksOne (n + 1)⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 2 (n + 1))) c = 1) :
    IsOfFinOrder c := by
  obtain ⟨j, hj⟩ := hn
  have hn0 := NeZero.ne n
  have hmem : c ∈ range (specialOrthogonalFrameBoundary 2 (n + 1) (Fin n)) :=
    mem_range_specialOrthogonalFrameBoundary_iff.2 (hc.trans HomotopyGroup.one_def)
  obtain ⟨a, rfl⟩ := hmem
  have : Finite (HomotopyGroup (Option (Fin n)) (finiteOrthonormalFrame ℝ 2 (2 + (n + 1)))
      (specialOrthogonalFrameMap 2 (n + 1) 1)) :=
    finiteOrthonormalFrame.finite_homotopyGroup_twoFrame ⟨j + 1, by omega⟩ (by omega)
      (by simp; omega) _
  have ha : IsOfFinOrder a := isOfFinOrder_of_finite a
  have := (specialOrthogonalFrameBoundaryHom 2 (n + 1) (Fin n)).isOfFinOrder ha
  rwa [coe_specialOrthogonalFrameBoundaryHom] at this

/-- **Reduction of the torsion of `π_n(SO(n + 1))` to the stable range.** For `n ≥ 2` even, if
`π_n(SO(n + 3))` is a torsion group, then so is `π_n(SO(n + 1))`: the kernel of the stabilization
`π_n(SO(n + 1)) → π_n(SO(n + 3))` is torsion
(`TauCeti.isOfFinOrder_of_homotopyGroupMap_fromBlocksOne_eq_one`). The group `π_n(SO(n + 3))` is
already the stable group `π_n(SO)`. -/
theorem isMulTorsion_homotopyGroup_specialOrthogonalGroup_of_isMulTorsion {n : ℕ} [NeZero n]
    (hn : Even n)
    (h : IsMulTorsion (HomotopyGroup (Fin n) (specialOrthogonalGroup (Fin (2 + (n + 1))) ℝ) 1)) :
    IsMulTorsion (HomotopyGroup (Fin n) (specialOrthogonalGroup (Fin (n + 1)) ℝ) 1) :=
  IsMulTorsion.extension_closed (f := HomotopyGroup.mapHom (blockEmbedding n)
    (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 2 (n + 1)))) rfl h fun c ↦
    Submonoid.isOfFinOrder_coe.1 (isOfFinOrder_of_homotopyGroupMap_fromBlocksOne_eq_one hn
      ((HomotopyGroup.mapHom_apply _ _ _).symm.trans (MonoidHom.mem_ker.1 c.property)))

end TauCeti
