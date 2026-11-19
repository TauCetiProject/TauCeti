/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Action
public import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
public import TauCeti.Geometry.Diffeomorphism.Sphere.RotationFamily
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Topology.Grassmannian.SphereBundle.Action
import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# Odd spheres are abundant with 2-spheres

This file proves Proposition 6.34 of Barraud–Damian–Humilière–Oancea: for odd `n ≥ 3`, the sphere
`Sⁿ` is abundant with 2-spheres at every point
(`TauCeti.isAbundantWithTwoSpheres_sphere_of_odd`). Abundance is the hypothesis of their Theorem
6.12, which concludes that the `π₁`-sensitive Hofer–Zehnder capacity of the unit codisc bundle
`D*Sⁿ` is finite.

The proof is the abundance criterion for a group action,
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero` (the argument of the
source's Propositions 6.29 and 6.33), for the action of `SO(n + 1)` on `Sⁿ ⊆ ℝⁿ⁺¹` at a point `b`.
It needs three inputs.

* **The action.** The orbit map `A ↦ A • b` has continuous local sections and the stabilizer of
  `b` is path connected (`TauCeti.exists_continuousOn_smul_eq_sphere`,
  `TauCeti.isPathConnected_stabilizer_specialOrthogonalGroup_sphere`).
* **A class `A ∈ Hₙ(SO(n + 1); ℤ)` with `π_* A = 2 • [Sⁿ]`.** The rotations in the planes through
  `b` form a family of special orthogonal matrices parametrized by `Sⁿ⁻¹ × S¹`
  (`TauCeti.sphereRotationMatrix`), whose orbit map at `b` is the rotation family of the sphere.
  That family has degree `1 + (-1)ⁿ⁻¹ = 2` for odd `n`
  (`Orientation.mapFundamentalClass_sphereRotationFamily`), so `A` is the image of the
  fundamental class of `Sⁿ⁻¹ × S¹`. This is the second, direct proof of the source; it needs no
  homotopy groups of orthogonal groups.
* **A class `α` of positive degree of `Map_*(S², Sⁿ)` with `2 • α ≠ 0`.** The double loops of
  Example 6.20 of the source induce an isomorphism `H_{n-2}(S^{n-2}; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`
  (Proposition 6.21, `TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`), so
  `H_{n-2}(Map_*(S², Sⁿ); ℤ)` has an element of infinite order
  (`TauCeti.exists_not_isOfFinAddOrder_homology_basedMap_sphere`). Here `n ≥ 3` is used, so that
  `n - 2 > 0`.

## Main results

* `TauCeti.exists_not_isOfFinAddOrder_homology_basedMap_sphere`: `H_{n-2}(Map_*(S², Sⁿ); ℤ)` has
  an element of infinite order, for `n ≥ 3`.
* `TauCeti.isAbundantWithTwoSpheres_sphere_of_odd`: odd spheres of dimension at least `3` are
  abundant with 2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, Example 6.20, Propositions 6.21,
  6.33 and 6.34.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Metric Module
open scoped RealInnerProductSpace Topology.Homotopy

namespace TauCeti

section DoubleLoop

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`H_{n-2}(Map_*(S², Sⁿ); ℤ)` has an element of infinite order**, for the unit sphere `Sⁿ` of
an `(n + 1)`-dimensional real inner product space with `n ≥ 3`, at every base point `x`. It is the
image of a generator of `H_{n-2}(S^{n-2}; ℤ)` under the double loops of
Barraud–Damian–Humilière–Oancea, Example 6.20, through three orthonormal vectors `x`, `u`, `v`
(`TauCeti.tangentCircleDoubleLoop`), which induce an isomorphism on `H_{n-2}`. -/
theorem exists_not_isOfFinAddOrder_homology_basedMap_sphere {m : ℕ} (hE : finrank ℝ E = m + 4)
    (x : sphere (0 : E) 1) :
    ∃ α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north
      x))).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) : ModuleCat.{0} ℤ),
      ¬IsOfFinAddOrder α := by
  classical
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  -- Unit vectors `u ⊥ x` and `v ⊥ x, u`; then `x` lies on the equator `Σ` of the unit sphere of
  -- `u⊥` orthogonal to `v`.
  obtain ⟨u, hu, hxu⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
    {(x : E)} (by rw [Finset.card_singleton, hE]; omega)
  obtain ⟨v, hv, hxv⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
    {(x : E), u} (Finset.card_le_two.trans_lt (by omega))
  have hux : ⟪u, (x : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact hxu _ (Finset.mem_singleton_self _)
  let v' : (ℝ ∙ u)ᗮ := ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hxv u (by simp))⟩
  have hv' : ‖v'‖ = 1 := hv
  let p₀ : sphereEquator v' :=
    ⟨⟨⟨x, Submodule.mem_orthogonal_singleton_iff_inner_right.2 hux⟩, by simp⟩,
      mem_sphereEquator.2 (hxv (x : E) (by simp))⟩
  have hV : finrank ℝ (ℝ ∙ u)ᗮ = m + 3 := by
    have : Fact (finrank ℝ E = m + 3 + 1) := ⟨hE⟩
    exact Submodule.finrank_orthogonal_span_singleton (norm_ne_zero_iff.1 (hu ▸ one_ne_zero))
  -- The Hurewicz class of a generalized loop of `Σ` that is a homeomorphism off the boundary of
  -- its cube generates `H_{m+1}(Σ; ℤ)`.
  let R := ModuleCat.of ℤ ℤ
  obtain ⟨c, hcs, hci⟩ := exists_genLoop_sphereEquator
    (norm_ne_zero_iff.1 (hv' ▸ one_ne_zero)) (k := m + 1) hV p₀
  have hcs' : Function.Surjective c := fun q ↦ by
    by_cases hq : q = p₀
    · exact ⟨0, hq ▸ GenLoop.boundary c 0 ⟨0, Or.inl rfl⟩⟩
    · exact hcs q hq
  have : IsIso (GenLoop.hurewicz R c) := GenLoop.isIso_hurewicz_of_bijective_toSphere R
    ⟨(GenLoop.injective_toSphere_iff c).2 hci, (GenLoop.surjective_toSphere_iff c).2 hcs'⟩
  have := isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop hE hu hv' p₀
  -- The double loops are based at `x`, and read as based maps `(S², north) → (Sⁿ, x)`.
  set a := (orthogonalSphereToEquator u (p₀ : sphere (0 : (ℝ ∙ u)ᗮ) 1) : sphere (0 : E) 1)
  have ha : a = x := Subtype.ext (by simp [a, p₀])
  let Φ : Ω (Ω (sphere (0 : E) 1) a) (Path.refl a) ≃ₜ
      BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north x :=
    (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
      ⟨sphere (0 : E) 1, a⟩ Sphere2.north).symm.trans
        ((Homeomorph.refl _).subtype fun f ↦ by rw [ha]; rfl)
  -- So `ℤ ≅ H_{m+1}(Map_*(S², Sⁿ); ℤ)`, through the coefficients `ULift ℤ ≅ ℤ`.
  let e : R ≅ ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north
      x))).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) : ModuleCat.{0} ℤ) :=
    asIso (GenLoop.hurewicz R c ≫ ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj R).map
      (TopCat.ofHom (tangentCircleDoubleLoop hu hv' p₀))) ≪≫
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm).app _ ≪≫
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo Φ)
  refine ⟨e.hom.hom (1 : ℤ), fun h ↦ ?_⟩
  obtain ⟨k, hk, hk0⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.1 h
  rw [← map_zsmul, ← map_zero e.hom.hom] at hk0
  have hinj : Function.Injective e.hom.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  exact hk (by simpa using hinj hk0)

end DoubleLoop

section Sphere

attribute [local instance] finrank_real_complex_fact'
attribute [local instance low] chartedSpaceProd

/-- **Odd spheres are abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea, Proposition
6.34). For odd `n ≥ 3`, the unit sphere `Sⁿ` of `ℝⁿ⁺¹` is abundant with 2-spheres at every
point `b`. The witness is the image of `A × α` under the action map
`SO(n + 1) × Map_*(S², Sⁿ) → Map(S², Sⁿ)`, where `A ∈ Hₙ(SO(n + 1); ℤ)` is the class of the
rotations in the planes through `b`, which evaluates at `b` to `2 • [Sⁿ]`, and `α` is a class of
infinite order of `H_{n-2}(Map_*(S², Sⁿ); ℤ)`. -/
theorem isAbundantWithTwoSpheres_sphere_of_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (b : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 1 := ⟨n - 3, by omega⟩
  have hm : Even (m + 2) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  -- `Fin (m + 2 + 1 + 1)` unifies with `Fin (k + 1)` at `k = m + 3`.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) = m + 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let oF : Orientation ℝ (EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) (Fin (m + 2 + 1 + 1)) :=
    (EuclideanSpace.basisFun (Fin (m + 2 + 1 + 1)) ℝ).toBasis.orientation
  let o := oF.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (m + 2)) × EuclideanSpace ℝ (Fin 1)) =
      m + 2 + 1 := by
    rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  let o' := ((oF.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere b)).sphereOrientation.prod
    Complex.orientation.sphereOrientation).toHomologicalOrientation hdim
  -- The orbit map of `b`, which sends the rotations in the planes through `b` to the rotation
  -- family of the sphere.
  let π : C(Matrix.specialOrthogonalGroup (Fin (m + 2 + 1 + 1)) ℝ,
      sphere (0 : EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) 1) :=
    ⟨fun g ↦ g • b, by fun_prop⟩
  have hπ : π.comp (sphereRotationMatrix b) =
      ⟨sphereRotationFamily b, continuous_sphereRotationFamily b⟩ := by
    ext x : 1
    exact sphereRotationMatrix_smul_self b x
  obtain ⟨α, hα⟩ := exists_not_isOfFinAddOrder_homology_basedMap_sphere
    (E := EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) (m := m) (by simp) b
  refine o.isAbundantWithTwoSpheres_of_smul_ne_zero finrank_euclideanSpace_fin π (fun _ ↦ rfl)
    (exists_continuousOn_smul_eq_sphere (by omega) b)
    (isPathConnected_stabilizer_specialOrthogonalGroup_sphere b) (ℓ := 2)
    (A := o'.mapFundamentalClass hdim (sphereRotationMatrix b)) ?_ (k := m + 1) (by omega)
    (α := α) fun h ↦ hα (isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨2, two_ne_zero, h⟩)
  -- The class of the rotations evaluates at `b` to `(1 + (-1) ^ (m + 2)) • [Sᵐ⁺³] = 2 • [Sᵐ⁺³]`.
  refine (o'.mapFundamentalClass_comp hdim π (sphereRotationMatrix b)).symm.trans ?_
  rw [hπ, oF.mapFundamentalClass_sphereRotationFamily b hdim, hm.neg_one_pow, one_add_one_eq_two]
  -- The two sides differ only in the proofs of the dimension facts.
  rfl

end Sphere

end TauCeti
