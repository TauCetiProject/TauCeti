/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.ZMultiples
public import TauCeti.AlgebraicTopology.Sphere.NormalField
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# The first homotopy group of the Stiefel manifold of two-frames

Let `k ≥ 3` be odd. The Stiefel manifold `V₂(ℝᵏ⁺²)` of orthonormal two-frames is
`(k - 1)`-connected (`TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup`). This file
proves that its first possibly nontrivial homotopy group `πₖ(V₂(ℝᵏ⁺²))` is finite
(`TauCeti.finiteOrthonormalFrame.finite_homotopyGroup_of_odd`).

Forgetting the second vector is a fibration `V₂(ℝᵏ⁺²) → V₁(ℝᵏ⁺²) = Sᵏ⁺¹` whose fibre over a unit
vector `u` is the unit sphere `Sᵏ` of `u^⊥`
(`TauCeti.finiteOrthonormalFrame.forgetLast_mem_serreFibrations`). Its exact homotopy sequence
contains the segment

`πₖ₊₁(V₂(ℝᵏ⁺²)) → πₖ₊₁(Sᵏ⁺¹) → πₖ(Sᵏ) → πₖ(V₂(ℝᵏ⁺²)) → πₖ(Sᵏ⁺¹) = 0`.

* The first map is trivial when `k + 1` is even
  (`TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_const`). A sphere of two-frames
  `(u, v)` has its first vector `u` as its image in `Sᵏ⁺¹`, and the second vector `v` is a
  nowhere-vanishing field orthogonal to `u`. So the image sphere is homotopic to its antipode, and
  in even dimension this makes it nullhomotopic (`GenLoop.mk_eq_one_of_inner_eq_zero`).
* Hence the boundary map `πₖ₊₁(Sᵏ⁺¹) ≅ ℤ → πₖ(Sᵏ) ≅ ℤ` is injective, so its image is a nonzero
  subgroup of `ℤ`.
* Since `πₖ(Sᵏ⁺¹)` is trivial, `πₖ(Sᵏ) → πₖ(V₂(ℝᵏ⁺²))` is surjective, with kernel the image of
  the boundary map. A quotient of `ℤ` by a nonzero subgroup is finite.

The group is in fact `ℤ/2`: the boundary map is multiplication by the Euler characteristic `2` of
`Sᵏ⁺¹`. Only its injectivity is proved here, which is what finiteness needs. For `k = 1`,
`V₂(ℝ³) = SO(3)` has `π₁ = ℤ/2` as well; that case is not covered, as the argument above uses
`πₖ(Sᵏ) ≅ ℤ` for `k ≥ 2`.

The group `πₖ(V₂(ℝᵏ⁺²))` is the Stiefel term of the comparison of `πₖ₋₁(SO(k))` with the stable
group `πₖ₋₁(SO(k + 2))`, through the exact segment
`πₖ(V₂(ℝᵏ⁺²)) → πₖ₋₁(SO(k)) → πₖ₋₁(SO(k + 2))` of the Stiefel fibration
`SO(k) → SO(k + 2) → V₂(ℝᵏ⁺²)` (`TauCeti.mem_range_specialOrthogonalFrameBoundary_iff`).
Barraud–Damian–Humilière–Oancea (Lemma 6.35) use this comparison to show that `πₖ₋₁(SO(k))` is a
torsion group for odd `k`.

## Main results

* `TauCeti.finiteOrthonormalFrame.homotopyGroupMap_forgetLast_eq_const`: for `n` even, forgetting
  the second vector induces the trivial map `πₙ₊₂(V₂(ℝⁿ⁺³)) → πₙ₊₂(V₁(ℝⁿ⁺³))`.
* `TauCeti.finiteOrthonormalFrame.finite_homotopyGroup_of_odd`: `πₖ(V₂(ℝᵏ⁺²))` is finite for
  odd `k ≥ 3`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2, Example 4.53 and
  Theorem 4.41.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 6.35.
-/

public section

noncomputable section

open Metric Module Set
open scoped InnerProductSpace Topology Topology.Homotopy

namespace TauCeti.finiteOrthonormalFrame

variable {n : ℕ}

/-- `homotopyGroupMap_forgetLast_eq_const` for the cube directions `Fin (n + 2)`. -/
private theorem homotopyGroupMap_forgetLast_mk_eq_const (hn : Even n)
    {g : finiteOrthonormalFrame ℝ 2 (n + 3)}
    (p : Ω^ (Fin (n + 2)) (finiteOrthonormalFrame ℝ 2 (n + 3)) g) :
    HomotopyGroup.map ⟨forgetLast, continuous_forgetLast⟩ rfl
        (⟦p⟧ : π_ (n + 2) (finiteOrthonormalFrame ℝ 2 (n + 3)) g) =
      ⟦GenLoop.const⟧ := by
  -- Read the first vector in the unit sphere of `ℝⁿ⁺³`, where the second vector is a normal field.
  let s := sphereHomeomorph (n + 3)
  apply (HomotopyGroup.homeomorphEquivOfEq s rfl).injective
  rw [HomotopyGroup.homeomorphEquivOfEq_mk_const, HomotopyGroup.homeomorphEquivOfEq_apply,
    HomotopyGroup.map_mk, HomotopyGroup.map_mk, ← _root_.HomotopyGroup.one_def]
  refine GenLoop.mk_eq_one_of_inner_eq_zero finrank_euclideanSpace_fin hn _
    (v := fun y ↦ WithLp.toLp 2 ((GenLoop.toSphere p y).1 1))
    ((PiLp.continuous_toLp 2 _).comp ((continuous_apply 1).comp
      (continuous_subtype_val.comp (GenLoop.toSphere p).continuous))) (fun y ↦ ?_) (fun y ↦ ?_)
  · exact norm_ne_zero_iff.1 (by rw [(GenLoop.toSphere p y).2.1 1]; exact one_ne_zero)
  · simp only [GenLoop.toSphere_map, ContinuousMap.comp_apply, ContinuousMap.coe_mk, s,
      coe_sphereHomeomorph_apply, forgetLast_apply]
    exact (GenLoop.toSphere p y).2.2 (by decide : (1 : Fin 2) ≠ Fin.castSucc 0)

/-- **Spheres of orthonormal two-frames project to nullhomotopic spheres in even dimensions.** For
`n` even, forgetting the second vector of an orthonormal two-frame of `ℝⁿ⁺³` induces the trivial
map from `πₙ₊₂(V₂(ℝⁿ⁺³))` to `πₙ₊₂(V₁(ℝⁿ⁺³))`, where `V₁(ℝⁿ⁺³)` is the even-dimensional sphere
`Sⁿ⁺²`: along a sphere of two-frames, the second vector is a nowhere-vanishing field orthogonal
to the first. The homotopy groups are indexed by any finite type `M` of `n + 2` cube directions. -/
theorem homotopyGroupMap_forgetLast_eq_const (hn : Even n) {M : Type*} [Finite M]
    (hM : Nat.card M = n + 2) {g : finiteOrthonormalFrame ℝ 2 (n + 3)}
    (a : HomotopyGroup M (finiteOrthonormalFrame ℝ 2 (n + 3)) g) :
    HomotopyGroup.map ⟨forgetLast, continuous_forgetLast⟩ rfl a = ⟦GenLoop.const⟧ := by
  let e : M ≃ Fin (n + 2) := Finite.equivFinOfCardEq hM
  obtain ⟨p, hp⟩ := Quotient.exists_rep (HomotopyGroup.congrEquiv e a)
  apply (HomotopyGroup.congrEquiv e).injective
  rw [← HomotopyGroup.map_congrEquiv, ← hp, homotopyGroupMap_forgetLast_mk_eq_const hn p,
    HomotopyGroup.congrEquiv_const]

/-- The homotopy group `πₙ₊₄` of `V₁(ℝⁿ⁺⁵) ≅ Sⁿ⁺⁴`, indexed by the cube directions
`Option (Fin (n + 3))` of the exact sequence of a fibration, is nontrivial. -/
private theorem nontrivial_homotopyGroup_option_fin (b : finiteOrthonormalFrame ℝ 1 (n + 5)) :
    Nontrivial (HomotopyGroup (Option (Fin (n + 3))) (finiteOrthonormalFrame ℝ 1 (n + 5)) b) :=
  have := nontrivial_homotopyGroup_sphere (n := n + 2) (finrank_euclideanSpace_fin)
    (sphereHomeomorph (n + 5) b)
  ((HomotopyGroup.congrEquiv (finSuccEquiv (n + 3)).symm).trans
    (HomotopyGroup.homeomorphEquiv (sphereHomeomorph (n + 5)) b)).nontrivial

/-- `finite_homotopyGroup_of_odd` for `k = n + 3`. -/
private theorem finite_homotopyGroup_of_odd_aux (hn : Even n)
    (g : finiteOrthonormalFrame ℝ 2 (n + 5)) :
    Finite (π_ (n + 3) (finiteOrthonormalFrame ℝ 2 (n + 5)) g) := by
  -- The fibration `V₂(ℝⁿ⁺⁵) → V₁(ℝⁿ⁺⁵)`, with fibre the unit sphere of the complement of `b`.
  set b := forgetLast g
  have hp := forgetLast_mem_serreFibrations (r := 1) (N := n + 5) (by omega)
  let e : (_root_.TopCat.ofHom ⟨forgetLast, continuous_forgetLast⟩ :
      _root_.TopCat.of (finiteOrthonormalFrame ℝ 2 (n + 5)) ⟶
        _root_.TopCat.of (finiteOrthonormalFrame ℝ 1 (n + 5))).fiber b := ⟨g, rfl⟩
  let φ := ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (forgetLastFiberHomeomorph b)
  let i : C(sphere (0 : b.complement) 1, finiteOrthonormalFrame ℝ 2 (n + 5)) :=
    ⟨fun y ↦ (φ.symm y).1, by fun_prop⟩
  have hi₀ : i (φ e) = e.1 := congrArg Subtype.val (φ.symm_apply_apply e)
  -- The boundary map `πₙ₊₄(V₁) → πₙ₊₃(Sⁿ⁺³)` is injective.
  let δ := TopCat.fibrationBoundaryOfHomeomorphHom (Fin (n + 3)) hp (φ := φ) (e := e) rfl
  have hδ_apply (a) : δ a = TopCat.fibrationBoundaryOfHomeomorph (Fin (n + 3)) hp φ rfl a :=
    congrFun (TopCat.coe_fibrationBoundaryOfHomeomorphHom (N := Fin (n + 3)) hp φ rfl) a
  have hδ : Function.Injective δ := by
    refine (injective_iff_map_eq_one δ).2 fun a ha ↦ ?_
    rw [hδ_apply, _root_.HomotopyGroup.one_def] at ha
    obtain ⟨c, rfl⟩ := (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundaryOfHomeomorph_eq hp
      (e := e) (φ := φ) rfl).2 ha
    exact (homotopyGroupMap_forgetLast_eq_const (n := n + 2) (hn.add even_two)
      (by simp) c).trans _root_.HomotopyGroup.one_def.symm
  -- `πₙ₊₄(V₁) ≅ πₙ₊₄(Sⁿ⁺⁴)` is nontrivial, so some boundary `c` is nontrivial.
  have := nontrivial_homotopyGroup_option_fin (n := n) b
  obtain ⟨a, ha⟩ := exists_ne (1 : HomotopyGroup (Option (Fin (n + 3)))
    (finiteOrthonormalFrame ℝ 1 (n + 5)) b)
  set c := δ a
  have hc : c ≠ 1 := (map_ne_one_iff δ hδ).2 ha
  -- Its image in `πₙ₊₃(V₂)` is trivial.
  have hic : HomotopyGroup.mapHom i hi₀ c = 1 := by
    rw [HomotopyGroup.mapHom_apply, _root_.HomotopyGroup.one_def]
    exact (TopCat.mem_range_fibrationBoundaryOfHomeomorph_iff hp (e := e) (φ := φ) rfl (i := i)
      (fun _ ↦ rfl) hi₀).1 ⟨a, (hδ_apply a).symm⟩
  -- Every class of `πₙ₊₃(V₂)` comes from the fibre, as `πₙ₊₃(V₁)` is trivial.
  have := subsingleton_homotopyGroup (r := 1) (N := n + 5) (M := Fin (n + 3)) (by simp) b
  have hsurj : Function.Surjective (HomotopyGroup.mapHom i hi₀) := fun d ↦
    (TopCat.mem_range_homotopyGroupMap_of_homeomorph_iff hp (e := e) (φ := φ) rfl
      (N := Fin (n + 3)) (i := i) (fun _ ↦ rfl) hi₀ (d := d)).2 (Subsingleton.elim _ _)
  -- `πₙ₊₃(Sⁿ⁺³) ≅ ℤ`, in which `c` is a nonzero integer killed by the map to `πₙ₊₃(V₂)`, which is
  -- therefore a finite quotient of `ℤ`.
  let ψ := homotopyGroupSphereAddEquiv (n := n + 1) ((stdOrthonormalBasis ℝ b.complement).reindex
    (finCongr ((finrank_complement b).trans (by omega)))) (φ e)
  let F := (HomotopyGroup.mapHom i hi₀).toAdditive.comp ψ.symm.toAddMonoidHom
  have hF : Function.Surjective F :=
    (Additive.ofMul.surjective.comp hsurj).comp (Additive.toMul.surjective.comp ψ.symm.surjective)
  have hK : ψ (Additive.ofMul c) ≠ 0 := by simpa using hc
  have hFK : F (ψ (Additive.ofMul c)) = 0 := by
    simp only [F, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.symm_apply_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul, hic, ofMul_one]
  have := F.finite_of_surjective_of_map_eq_zero hF hK hFK
  exact Finite.of_equiv _ Additive.toMul

/-- **The first possibly nontrivial homotopy group of `V₂(ℝᵏ⁺²)` is finite.** For odd `k ≥ 3`,
the homotopy group `πₖ` of the Stiefel manifold of orthonormal two-frames of `ℝᵏ⁺²` is finite, at
every base point. -/
theorem finite_homotopyGroup_of_odd {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k)
    (g : finiteOrthonormalFrame ℝ 2 (k + 2)) :
    Finite (π_ k (finiteOrthonormalFrame ℝ 2 (k + 2)) g) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  exact finite_homotopyGroup_of_odd_aux (by simpa [Nat.even_add_one, parity_simps] using hk) g

end TauCeti.finiteOrthonormalFrame
