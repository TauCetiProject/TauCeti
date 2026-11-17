/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Maps into an even-dimensional sphere homotopic to their antipode

The antipodal map of the unit sphere `Sᵈ` acts on `H_d(Sᵈ; ℤ) ≅ ℤ` by `(-1)^(d + 1)`
(`TauCeti.singularHomologyMap_sphere_neg_apply`), which is `-1` when `d` is even. So if a map
`f : X → Sᵈ` into an even-dimensional sphere is homotopic to its antipode `-f`, then `f_* = -f_*`
on `H_d(-; ℤ)`, and since `H_d(Sᵈ; ℤ)` is torsion-free, `f_*` is zero there
(`ContinuousMap.singularHomologyMap_eq_zero_of_homotopic_neg`). The Hurewicz map of `Sᵈ` is
injective in degree `d` for `d ≥ 2`, and the Hurewicz map is natural, so `f` is then also trivial
on `π_d` (`ContinuousMap.homotopyGroupMap_eq_one_of_homotopic_neg`).

A map with a unit normal field `v`, that is `v x` orthogonal to `f x` for every `x`, is homotopic
to its antipode (`ContinuousMap.homotopic_neg_of_inner_eq_zero`). This is the obstruction behind
the hairy ball theorem: the identity of an even-dimensional sphere is nonzero on `H_d`, so it has
no unit tangent field. Applied to the projection `(x, v) ↦ x` of the unit tangent bundle
`V₂(ℝᵈ⁺¹) → Sᵈ`, whose second vector is such a field along it, it shows that this projection is
trivial on `π_d` and on `H_d`.

The sphere dimension is written `n + 2`, for a real inner product space `E` of dimension `n + 3`,
as for `TauCeti.homotopyGroupSphereAddEquiv`, so the even case is `Even n`.

## Main results

* `ContinuousMap.singularHomologyMap_eq_zero_of_homotopic_neg`: a map into an even-dimensional
  sphere homotopic to its antipode is zero on integral homology in the top degree.
* `ContinuousMap.homotopyGroupMap_eq_one_of_homotopic_neg`: such a map is trivial on the top
  homotopy group.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.2, the degree of the
  antipodal map and Theorem 2.28, and §4.2, the Hurewicz theorem.
-/

public section

noncomputable section

open CategoryTheory Metric Module
open scoped Topology.Homotopy

namespace ContinuousMap

open TauCeti

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Type} [TopologicalSpace X]
  {n : ℕ}

/-- **A map into an even-dimensional sphere homotopic to its antipode vanishes on top homology.**
Let `S` be the unit sphere of a real inner product space of dimension `n + 3`, with `n` even, so
that `S` has even dimension `n + 2`. If `f : X → S` is homotopic to `-f`, then `f` induces the zero
map `H_{n+2}(X; ℤ) → H_{n+2}(S; ℤ)`. -/
theorem singularHomologyMap_eq_zero_of_homotopic_neg (hE : finrank ℝ E = n + 3) (hn : Even n)
    {f : C(X, sphere (0 : E) 1)} (hf : f.Homotopic (-f)) :
    singularHomologyMap ℤ (n + 2) f = 0 := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  -- `H_{n+2}(S; ℤ) ≅ ℤ`, through an orthonormal basis of `E`.
  let e := ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (n + 1)).app
      (TopCat.of (sphere (0 : E) 1))).symm ≪≫
    reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ)
      ((stdOrthonormalBasis ℝ E).reindex (finCongr hE))
  let φ : ((singularChains ℤ).obj (TopCat.of (sphere (0 : E) 1))).homology (n + 2) →ₗ[ℤ] ℤ :=
    e.hom.hom
  have hφ : Function.Injective φ := (ConcreteCategory.bijective_of_isIso e.hom).1
  ext z
  -- Since `-f = ν ∘ f` is homotopic to `f` and `ν` acts by `-1`, the class `y = f_* z` is `-y`.
  have hy : singularHomologyMap ℤ (n + 2) f z = -singularHomologyMap ℤ (n + 2) f z := by
    have hν := singularHomologyMap_sphere_neg_apply ℤ (n := n + 1) hE
      (singularHomologyMap ℤ (n + 2) f z)
    rw [(hn.add_one.add_even even_two).neg_one_pow, neg_one_zsmul] at hν
    -- The last rewrite closes the goal because `ν.comp f` and `-f` are equal by definition.
    rw [← hν, ← singularHomologyMap_comp, singularHomologyMap_eq_of_homotopic ℤ (n + 2) hf]
  have h := congrArg φ hy
  rw [map_neg] at h
  exact hφ (by rw [LinearMap.zero_apply, map_zero]; omega)

/-- **A map into an even-dimensional sphere homotopic to its antipode is trivial on the top
homotopy group.** Let `S` be the unit sphere of a real inner product space of dimension `n + 3`,
with `n` even. If `f : X → S` is homotopic to `-f`, then `f` induces the trivial map
`π_{n+2}(X, x) → π_{n+2}(S, f x)`. -/
theorem homotopyGroupMap_eq_one_of_homotopic_neg (hE : finrank ℝ E = n + 3) (hn : Even n)
    {f : C(X, sphere (0 : E) 1)} (hf : f.Homotopic (-f)) {x : X} {y : sphere (0 : E) 1}
    (hy : f x = y) (a : HomotopyGroup (Fin (n + 2)) X x) :
    HomotopyGroup.map f hy a = 1 := by
  have hS (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup (Fin k) (sphere (0 : E) 1) y) :=
    subsingleton_homotopyGroup_sphere_of_lt (n := n + 2) (by omega) (by simpa using hk) y
  -- The Hurewicz class of `f_* a` is the image under `f_*` of that of `a`, hence zero.
  have h := HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewiczHom_naturality ℤ f hy
    (Additive.ofMul a)
  rw [← HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv_apply hS, toMul_ofMul] at h
  have h0 : HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hS
      (Additive.ofMul (HomotopyGroup.map f hy a)) = 0 := by
    rw [← h]
    exact LinearMap.congr_fun (singularHomologyMap_eq_zero_of_homotopic_neg hE hn hf) _
  exact Additive.ofMul.injective (by
    simpa using (map_eq_zero_iff _ (AddEquiv.injective _)).1 h0)

end ContinuousMap
