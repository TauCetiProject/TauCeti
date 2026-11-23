/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
import TauCeti.AlgebraicTopology.Singular.Fibration.FiberInclusion
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.AlgebraicTopology.Sphere.Puncture
import TauCeti.Analysis.Quaternion.Basic
import TauCeti.Geometry.Sphere.Quaternion
import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
import TauCeti.Topology.MappingSpace.Fibration

/-!
# Fibered families of two-spheres

Let `Q` be a closed connected oriented `n`-manifold, with evaluation `ev : Map(S², Q) → Q` at the
north pole. Barraud–Damian–Humilière–Oancea (Definition 6.14) say that `Q` admits a **fibered
family of 2-spheres** if there are a fibre bundle `π : Σ → Q` of closed oriented manifolds, with
fibre `Σ_b` of positive dimension, and a map `σ : Σ → Map(S², Q)` over `Q`, `ev ∘ σ = π`, whose
restriction `σ_b : Σ_b → Ω²Q` to the fibres over `b` sends the fundamental class of `Σ_b` to a
nonzero class. Their Proposition 6.15 says that `σ_*[Σ]` then lives over the fundamental class of
`Q`, by naturality of the shriek map of the point `b` (their Corollary 2.13), and has degree above
`n`, so that `Q` is abundant with 2-spheres (`TauCeti.IsAbundantWithTwoSpheres`).

The proposition is proved here with no manifold structure on `Σ`
(`TauCeti.isAbundantWithTwoSpheres_of_fiberedFamily`): `π` is a Serre fibration over a `T₁` space
`Q` with a chart of dimension `n` at `b`, and the class of `Σ` is any `A ∈ H_{k+n}(Σ; ℤ)`, `k > 0`,
whose shriek `j_! A ∈ H_k(Σ_b; ℤ)` is sent by `σ_b` to a nonzero class. For a bundle of closed
oriented manifolds and `A = [Σ]`, the shriek is the fundamental class of the fibre.

## Spheres with two orthonormal tangent fields

The source's Example 6.20 is the family of two-spheres of a sphere `Sⁿ` with two pointwise
orthonormal tangent vector fields `u` and `v`, such as `S^{4k-1}` with two of its quaternionic
fields: over `x ∈ Sⁿ` the parameter space `Σ` of `TauCeti.twoFieldSphereFamily` has the
`(n - 2)`-sphere `Σₓ` of the points orthogonal to `u x` and `v x`. Its Proposition 6.21, here for
`n ≥ 4` (`TauCeti.isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber`), says that the
family over `x` is an isomorphism `H_{n-2}(Σₓ; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)` of infinite cyclic groups.

A class `A` of `H_{2n-2}(Σ; ℤ)` whose shriek generates `H_{n-2}(Σₓ; ℤ)` is found without a
fundamental class of `Σ`. The part `Σ ∖ Σₓ` of `Σ` lies over the contractible punctured sphere
`Sⁿ ∖ {x}`, so its homology is that of a fibre, an `(n - 2)`-sphere, which vanishes in degree
`2n - 3`. By the exact sequence of the pair `(Σ, Σ ∖ Σₓ)`, every class of the local homology
`H_{2n-2}(Σ, Σ ∖ Σₓ; ℤ) ≅ H_{n-2}(Σₓ; ℤ)` is the localization of a class of `Σ`. So every sphere
`Sⁿ`, `n ≥ 4`, with two orthonormal tangent fields is abundant with 2-spheres
(`TauCeti.isAbundantWithTwoSpheres_sphere_of_orthonormal`), and in particular so is the unit
sphere `S^{4k-1}` of `ℍᵏ` for `k ≥ 2` (`TauCeti.isAbundantWithTwoSpheres_sphere_piLp_quaternion`).
The case `k = 1`, the group of unit quaternions, is
`TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_of_fiberedFamily`: a fibered family of 2-spheres with a class
  of positive fibre degree makes the base abundant with 2-spheres (Proposition 6.15).
* `TauCeti.isAbundantWithTwoSpheres_sphere_of_orthonormal`: a sphere `Sⁿ`, `n ≥ 4`, with two
  pointwise orthonormal tangent vector fields is abundant with 2-spheres.
* `TauCeti.isAbundantWithTwoSpheres_sphere_piLp_quaternion`: the quaternionic spheres `S^{4k-1}`,
  `k ≥ 2`, are abundant with 2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14,
  Proposition 6.15, Example 6.20 and Proposition 6.21, and §2.4, Corollary 2.13.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Module Set
open scoped RealInnerProductSpace

namespace TauCeti

section FiberedFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : Type} [TopologicalSpace Q] [T1Space Q] (e : OpenPartialHomeomorph Q V) {b : Q}
  (hb : b ∈ e.source) {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε)
  {S : TopCat.{0}} {π : S ⟶ TopCat.of Q} (hπ : TopCat.serreFibrations π)
  {σ : S ⟶ TopCat.of C(Sphere2, Q)}
  (hσ : σ ≫ TopCat.ofHom (mappingSpaceEval Sphere2.north) = π)

include hπ in
/-- **Fibered families of 2-spheres** (Barraud–Damian–Humilière–Oancea, Proposition 6.15). Let
`π : Σ ⟶ Q` be a Serre fibration over a `T₁` space with a chart `e` of dimension `n` at `b`, and
`σ : Σ ⟶ Map(S², Q)` a map over `Q` for evaluation at the north pole. If a class `A ∈ Hₘ(Σ; ℤ)`,
`m = k + n` with `k > 0`, has a shriek `j_! A ∈ H_k(π⁻¹(b); ℤ)` whose image under the restriction
`π⁻¹(b) ⟶ Map_*(S², Q)` of `σ` is nonzero, then `Q` is abundant with 2-spheres at `b`: the class
`σ_* A` lives over the fundamental class and has degree above `n`. -/
theorem isAbundantWithTwoSpheres_of_fiberedFamily {k m : ℕ} (hk : 0 < k)
    (h : k + finrank ℝ V = m)
    {A : ((TopCat.toSSet.obj S).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) m : ModuleCat.{0} ℤ)}
    (hA : (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (σ.preimageMap hσ {b})).hom
      ((TopCat.singularHomologyComplFiberIso (ModuleCat.of ℤ (ULift.{0} ℤ)) e hb hε hε₀ hπ k m
        h).hom.hom ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) π b m).hom A)) ≠ 0) :
    IsAbundantWithTwoSpheres Q (finrank ℝ V) b :=
  isAbundantWithTwoSpheres_of_lt ((livesOverFundamentalClass_homologyMap_iff e hb hε hε₀ hπ
    (isHurewiczFibration_mappingSpaceEval_sphere.{0} 2 Sphere2.north).mem_serreFibrations hσ h
      A).2 hA) (by omega)

end FiberedFamily

section TwoField

/-! ### Spheres with two orthonormal tangent fields -/

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])

include h in
private theorem inner_v_u (y : sphere (0 : E) 1) : ⟪v y, u y⟫ = 0 := by
  simpa using (h y).inner_eq_zero (by decide : (2 : Fin 3) ≠ 1)

include h in
/-- The fibres of the space of equators of `Sⁿ` are spheres of dimension `n - 2`. -/
private theorem finrank_equatorFiber {n : ℕ} (hE : finrank ℝ E = n + 1) (hn : 2 ≤ n)
    (y : sphere (0 : E) 1) :
    finrank ℝ (ℝ ∙ (⟨v y, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (inner_v_u h y)⟩ :
      (ℝ ∙ u y)ᗮ))ᗮ = n - 2 + 1 :=
  finrank_orthogonal_span_twoField (inner_v_u h y) (by omega)
    (fun h0 ↦ by simpa [h0] using (h y).norm_eq_one 1)
    (fun h0 ↦ by simpa [h0] using (h y).norm_eq_one 2)

include h in
/-- The fibres of the space of equators of `Sⁿ` have no homology in positive degrees other than
`n - 2`. -/
private theorem isZero_singularHomology_equatorProj_fiber {n : ℕ} (hE : finrank ℝ E = n + 1)
    (hn : 2 ≤ n) (y : sphere (0 : E) 1) (R : ModuleCat.{0} ℤ) {q : ℕ} (hq : q + 1 ≠ n - 2) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (q + 1)).obj R).obj
      (TopCat.of (twoFieldEquatorsProj u v ⁻¹' {y} : Set _))) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  rw [← reducedSingularHomologyFunctor_succ]
  exact (isZero_reducedSingularHomologyFunctor_sphere_of_ne R
    (finrank_equatorFiber h hE hn y) hq).of_iso
      ((reducedSingularHomologyFunctor R (q + 1)).mapIso
        (orthogonalSphereIsoTwoFieldEquatorsPreimage (inner_v_u h y)).symm)

include h in
/-- The fibres of the space of equators of `Sⁿ` have nonzero integral homology in degree
`n - 2`. -/
private theorem nontrivial_singularHomology_equatorProj_fiber {n : ℕ} (hE : finrank ℝ E = n + 1)
    (hn : 3 ≤ n) (y : sphere (0 : E) 1) :
    Nontrivial (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n - 2)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
        (TopCat.of (twoFieldEquatorsProj u v ⁻¹' {y} : Set _))) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have hrank := ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (finrank_equatorFiber h hE (by omega) y) (n - 2)
  rw [((((singularHomologyFunctor (ModuleCat.{0} ℤ) (n - 2)).obj
    (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso
      (orthogonalSphereIsoTwoFieldEquatorsPreimage (inner_v_u h y))).toLinearEquiv).finrank_eq]
    at hrank
  apply Module.nontrivial_of_finrank_pos (R := ℤ)
  rw [hrank]
  simp

variable (u v) in
/-- The projection `TauCeti.twoFieldEquatorsProj` is `TopCat.ofHom` of the first projection. -/
private theorem twoFieldEquatorsProj_eq :
    twoFieldEquatorsProj u v =
      TopCat.ofHom (ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v))) :=
  TopCat.hom_ext hom_twoFieldEquatorsProj

variable (hu : Continuous u) (hv : Continuous v)

include h hu hv in
/-- Off the fibre over `x`, the space of equators of `Sⁿ` has no homology in degree `2n - 3`: it
lies over the contractible punctured sphere, so in that degree it has the homology of the fibre
over `-x`, an `(n - 2)`-sphere. -/
private theorem isZero_singularHomology_equatorProj_compl {n : ℕ} (hE : finrank ℝ E = n + 1)
    (hn : 3 ≤ n) (x : sphere (0 : E) 1) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (2 * n - 3)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
        (TopCat.of ((twoFieldEquatorsProj u v ⁻¹' {x})ᶜ :
          Set (TopCat.of (twoFieldEquators u v))))) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have hπ := TopCat.mem_serreFibrations_twoFieldEquators hu hv
    fun y ↦ (orthonormal_vecCons_iff.1 (h y)).2.2
  have hx : -x ∈ ({x}ᶜ : Set (sphere (0 : E) 1)) := by
    simpa [eq_comm] using ne_neg_of_mem_unit_sphere ℝ x
  have : ContractibleSpace ({x}ᶜ : Set (sphere (0 : E) 1)) :=
    contractibleSpace_sphere_compl_singleton x
  -- Over the contractible punctured sphere, the fibre over `-x` carries the homology.
  have hiso := TopCat.isIso_singularHomologyMap_preimageInclusion ℤ (n := 2 * n - 2)
    (p := ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v)))
    (TopCat.mem_serreFibrations_restrictPreimage hπ _) hx (fun _ _ ↦ inferInstance)
    (m := 2 * n - 3) (by omega)
  have hF := isZero_singularHomology_equatorProj_fiber h hE (by omega) (-x) (ModuleCat.of ℤ ℤ)
    (q := 2 * n - 4) (by omega)
  have hdeg : 2 * n - 4 + 1 = 2 * n - 3 := by omega
  rw [hdeg, twoFieldEquatorsProj_eq] at hF
  rw [twoFieldEquatorsProj_eq]
  have hZ := hF.of_iso (asIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (2 * n - 3)).obj
    (ModuleCat.of ℤ ℤ)).map ((ContinuousMap.fst.comp
      (ContinuousMap.subtypeVal (twoFieldEquators u v))).preimageInclusion hx))).symm
  -- Pass to the coefficients `ULift ℤ`, and to the complement of the fibre over `x`.
  exact (hZ.of_iso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (2 * n - 3)).mapIso
    uliftIntIso).app _)).of_iso (((singularHomologyFunctor (ModuleCat.{0} ℤ)
      (2 * n - 3)).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso
        (TopCat.isoOfHomeo (Homeomorph.setCongr (preimage_compl (s := {x})))))

include h hu hv in
/-- In degree `2n - 2`, every class of the local homology of the space of equators of `Sⁿ` along
the fibre over `x` is the localization of a class of the space of equators. -/
private theorem epi_fiberLocalization_equatorProj {n : ℕ} (hE : finrank ℝ E = n + 1)
    (hn : 3 ≤ n) (x : sphere (0 : E) 1) :
    Epi (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) (twoFieldEquatorsProj u v) x
      (2 * n - 2)) :=
  (TopPair.singularHomology_exact_relative _ _ (2 * n - 2) (2 * n - 3)).epi_f
    ((isZero_singularHomology_equatorProj_compl h hu hv hE hn x).eq_of_tgt _ _)

/-- The family of two-spheres of the two fields, as a morphism of `TopCat`. -/
private abbrev twoFieldSphereFamilyHom :
    TopCat.of (twoFieldEquators u v) ⟶ TopCat.of C(Sphere2, sphere (0 : E) 1) :=
  TopCat.ofHom (twoFieldSphereFamily h hu hv)

private theorem twoFieldSphereFamilyHom_comp :
    twoFieldSphereFamilyHom h hu hv ≫ TopCat.ofHom (mappingSpaceEval Sphere2.north) =
      twoFieldEquatorsProj u v :=
  TopCat.hom_ext ((mappingSpaceEval_comp_twoFieldSphereFamily h hu hv).trans
    hom_twoFieldEquatorsProj.symm)

/-- Over `x`, the family of two-spheres is the family of based two-spheres
`TauCeti.twoFieldSphereFamilyFiber`. -/
private theorem preimageMap_twoFieldSphereFamilyHom (x : sphere (0 : E) 1) :
    (twoFieldSphereFamilyHom h hu hv).preimageMap (twoFieldSphereFamilyHom_comp h hu hv)
        ({x} : Set (sphere (0 : E) 1)) =
      (TopCat.isoOfHomeo (twoFieldEquatorsFiberHomeomorphPreimage x)).inv ≫
        TopCat.ofHom (twoFieldSphereFamilyFiber h hu hv x) ≫
          (TopCat.isoOfHomeo (basedMapHomeomorphPreimage Sphere2.north x)).hom := by
  ext z a
  rw [TopCat.Hom.coe_preimageMap_apply]
  simpa using congrArg (fun xq ↦ (twoFieldSphereFamily h hu hv xq a : E))
    (coe_twoFieldEquatorsFiberHomeomorphPreimage_symm_apply z).symm

include h hu hv in
/-- Over every point of `Sⁿ`, `n ≥ 4`, the family of two-spheres is an isomorphism on
`H_{n-2}(-; ℤ)` (Proposition 6.21). -/
private theorem isIso_singularHomologyFunctor_map_preimageMap {n : ℕ} (hE : finrank ℝ E = n + 1)
    (hn : 4 ≤ n) (x : sphere (0 : E) 1) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n - 2)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map ((twoFieldSphereFamilyHom h hu hv).preimageMap
        (twoFieldSphereFamilyHom_comp h hu hv) ({x} : Set (sphere (0 : E) 1)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h621 := (NatIso.isIso_map_iff ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).mapIso
    uliftIntIso) _).2 (isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber h hu hv
      (m := m) (by omega) x)
  have hdeg : m + 4 - 2 = m + 2 := by omega
  rw [hdeg, preimageMap_twoFieldSphereFamilyHom, Functor.map_comp, Functor.map_comp]
  infer_instance

include h hu hv in
/-- **Spheres with two orthonormal tangent fields are abundant with 2-spheres**
(Barraud–Damian–Humilière–Oancea, Example 6.20 and Propositions 6.15 and 6.21). Let `u` and `v` be
continuous tangent vector fields on the unit sphere `Sⁿ` of a real inner product space of
dimension `n + 1`, `n ≥ 4`, with `x`, `u x` and `v x` orthonormal at every point `x`. Then `Sⁿ`
is abundant with 2-spheres at every point, witnessed by a class of degree `2n - 2` of the
two-spheres `TauCeti.twoFieldSphereFamily` swept through the equators orthogonal to the two
fields. -/
theorem isAbundantWithTwoSpheres_sphere_of_orthonormal {n : ℕ} (hE : finrank ℝ E = n + 1)
    (hn : 4 ≤ n) (x : sphere (0 : E) 1) : IsAbundantWithTwoSpheres (sphere (0 : E) 1) n x := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have : Fact (finrank ℝ E = n + 1) := ⟨hE⟩
  -- A chart of the sphere at `x`: stereographic projection from `-x`.
  obtain ⟨e, hb⟩ : ∃ e : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source :=
    ⟨stereographic' n (-x), by
      rw [stereographic'_source]
      simpa using ne_neg_of_mem_unit_sphere ℝ x⟩
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hb)
  have hπ : TopCat.serreFibrations (twoFieldEquatorsProj u v) := by
    rw [twoFieldEquatorsProj_eq]
    exact TopCat.mem_serreFibrations_twoFieldEquators hu hv
      fun y ↦ (orthonormal_vecCons_iff.1 (h y)).2.2
  have hdim : n - 2 + finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * n - 2 := by
    simp only [finrank_euclideanSpace_fin]
    omega
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let G := ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n - 2)).obj R).map
    ((twoFieldSphereFamilyHom h hu hv).preimageMap (twoFieldSphereFamilyHom_comp h hu hv)
      ({x} : Set (sphere (0 : E) 1)))
  have := epi_fiberLocalization_equatorProj h hu hv hE (by omega) x
  have : IsIso G := isIso_singularHomologyFunctor_map_preimageMap h hu hv hE hn x
  -- The localization at the fibre over `x`, followed by the shriek identification with the
  -- homology of the fibre and by the family of two-spheres over `x`, is onto.
  let j := TopCat.singularHomologyComplFiberIso (E := TopCat.of (twoFieldEquators u v))
    (B := TopCat.of (sphere (0 : E) 1)) (p := twoFieldEquatorsProj u v) R e hb hε hε₀ hπ (n - 2)
      (2 * n - 2) hdim
  have hc : Function.Surjective fun A ↦
      G.hom (j.hom.hom ((fiberLocalization R (twoFieldEquatorsProj u v) x (2 * n - 2)).hom A)) :=
    ((ModuleCat.epi_iff_surjective G).1 inferInstance).comp
      (((ModuleCat.epi_iff_surjective j.hom).1 inferInstance).comp
        ((ModuleCat.epi_iff_surjective _).1 inferInstance))
  -- Its target is nonzero, since the homology of the fibre is.
  have := nontrivial_singularHomology_equatorProj_fiber h hE (by omega) x
  have := (asIso G).toLinearEquiv.injective.nontrivial
  obtain ⟨y, hy⟩ := exists_ne (0 : ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n - 2)).obj
    R).obj (TopCat.of (TopCat.ofHom (mappingSpaceEval (X := sphere (0 : E) 1) Sphere2.north) ⁻¹'
      ({x} : Set (sphere (0 : E) 1)))))
  obtain ⟨A, rfl⟩ := hc y
  have hab := isAbundantWithTwoSpheres_of_fiberedFamily (S := TopCat.of (twoFieldEquators u v))
    (π := twoFieldEquatorsProj u v) e hb hε hε₀ hπ (twoFieldSphereFamilyHom_comp h hu hv)
      (by omega) hdim (A := A) hy
  rwa [finrank_euclideanSpace_fin] at hab

end TwoField

section Quaternion

open scoped Quaternion RightActions

/-- **The quaternionic spheres are abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea,
Example 6.20). The unit sphere `S^{4k-1}` of the quaternionic coordinate space `ℍᵏ`, `k ≥ 2`, is
abundant with 2-spheres at every point, through the family of two-spheres of the quaternionic
tangent fields `y ↦ y • i` and `y ↦ y • j`. -/
theorem isAbundantWithTwoSpheres_sphere_piLp_quaternion {ι : Type} [Fintype ι]
    (hι : 2 ≤ Fintype.card ι) (x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) (4 * Fintype.card ι - 1)
      x := by
  have ho (y : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) : Orthonormal ℝ
      ![(y : PiLp 2 fun _ : ι ↦ ℍ), quaternionFrame (y : PiLp 2 fun _ : ι ↦ ℍ) 0,
        quaternionFrame (y : PiLp 2 fun _ : ι ↦ ℍ) 1] :=
    orthonormal_vecCons_quaternionFrame_of_ne (E := PiLp 2 fun _ : ι ↦ ℍ)
      (norm_eq_of_mem_sphere y) (by decide)
  have hc (j : Fin 3) : Continuous fun y : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1 ↦
      quaternionFrame (y : PiLp 2 fun _ : ι ↦ ℍ) j :=
    (contDiff_quaternionFrame (E := PiLp 2 fun _ : ι ↦ ℍ) (m := 0) j).continuous.comp
      continuous_subtypeVal
  exact isAbundantWithTwoSpheres_sphere_of_orthonormal ho (hc 0) (hc 1)
    (by rw [finrank_piLp_quaternion]; omega) (by omega) x

end Quaternion

end TauCeti
