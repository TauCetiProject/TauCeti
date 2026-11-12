/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Sphere.TangentCircle
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Comparison
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup

/-!
# Double loops of a sphere swept by tangent circles

Let `u` be a unit vector of a real inner product space `E`, so that the equator of the unit sphere
`Sⁿ` of `E` orthogonal to `u` is the unit sphere `S_V` of `V = u^⊥`, and let `v` be a unit vector of
`V` and `p` a point of `S_V` orthogonal to `v`. The points of `S_V` orthogonal to `v` form a sphere
`Σ_p = Sⁿ ∩ ⟨u, v⟩^⊥` of dimension `n - 2` through `p`. Barraud–Damian–Humilière–Oancea
(Example 6.20) attach to each `q ∈ Σ_p` a double loop of `Sⁿ` at `p`, the composite

`Σ_p → Ω_p S_V → Ω_p Ω_p Sⁿ`

of the family of circles `φ_{V,v}` through `p` tangent to `v` (`TauCeti.tangentCircleLoop`) and
the loop map of the family of circles `φ_{E,u}` through `p` tangent to `u`: the point `q` goes to
the loop of loops `θ ↦ φ_{E,u}(φ_{V,v}(q)(θ))` (`TauCeti.tangentCircleDoubleLoop`).

Their Proposition 6.21 says that this family represents a generator of `H_{n-2}(Ω²Sⁿ; ℤ) ≅ ℤ`. Here
it is proved in every dimension `n ≥ 3`, in the form that the family induces an isomorphism
`H_{n-2}(Σ_p; ℤ) → H_{n-2}(Ω²Sⁿ; ℤ)`
(`TauCeti.bijective_singularHomologyMap_tangentCircleDoubleLoop`). The source applies it to the
spheres `S^{4k-1}`, which carry two orthonormal tangent vector fields, to let `p` vary.

The proof reads the family on a cube. A generalized loop `c` of `Σ_p` covering it off `p` and
identifying only boundary points has a generating Hurewicz class. Uncurrying `σ ∘ c` twice gives,
up to a permutation of the cube coordinates, the generalized loop of `Sⁿ` of circles tangent to `u`
through the circles tangent to `v` through the points of `c`. That generalized loop covers `Sⁿ`
off `p` and identifies only boundary points (`TauCeti.eq_or_of_tangentCircleGenLoop_eq`,
`TauCeti.surjective_tangentCircleGenLoop`), so its class generates `πₙ(Sⁿ) ≅ Hₙ(Sⁿ; ℤ)`. The loop
shifts `π_{n-2}(Ω²Sⁿ) ≅ πₙ(Sⁿ)` and the Hurewicz isomorphism of the `(n - 3)`-connected space
`Ω²Sⁿ` then carry it to a generator of `H_{n-2}(Ω²Sⁿ; ℤ)`, which is the image of the Hurewicz
class of `c` by naturality. For `n = 3` this Hurewicz isomorphism is the one in degree one, which
applies because `π₁(Ω²S³) ≅ π₂(ΩS³)` is commutative.

## Main declarations

* `TauCeti.tangentCircleDoubleLoop hu hv p`: the family `σ_p : Σ_p → Ω_p Ω_p Sⁿ`.
* `TauCeti.bijective_singularHomologyMap_tangentCircleDoubleLoop`: for `n ≥ 3` it induces an
  isomorphism `H_{n-2}(Σ_p; ℤ) → H_{n-2}(Ω²Sⁿ; ℤ)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Example 6.20 and Proposition 6.21.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Module Real
open scoped Topology unitInterval Topology.Homotopy

namespace TauCeti

open HomotopyGroup

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E} {v : (ℝ ∙ u)ᗮ}

/-- **The double loops swept by tangent circles** (Barraud–Damian–Humilière–Oancea,
Example 6.20). For a unit vector `u` of `E`, a unit vector `v` of `V = u^⊥` and a point `p₀` of the
unit sphere `S_V` orthogonal to `v`, a point `q` of `S_V` orthogonal to `v` goes to the double
loop `θ ↦ φ_{E,u}(φ_{V,v}(q)(θ))` of the unit sphere of `E` at `p₀`. Here `φ_{V,v}(q)` is the
circle in `S_V` through `p₀` tangent to `v` and through `q`, and `φ_{E,u}(w)` the circle in the unit
sphere of `E` through `p₀` tangent to `u` and through `w` (`TauCeti.tangentCircleLoop`); `S_V` is
read as the equator of the unit sphere of `E` orthogonal to `u`. -/
def tangentCircleDoubleLoop (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ : sphereEquator v) :
    C(sphereEquator v, Ω (Ω (sphere (0 : E) 1)
      ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator (p₀ : sphere (0 : (ℝ ∙ u)ᗮ) 1) :
        sphere (0 : E) 1)) (Path.refl _)) where
  toFun q :=
    { toFun t := tangentCircleLoop hu ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator p₀)
        ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator (tangentCircleLoop hv p₀ q t))
      continuous_toFun := (tangentCircleLoop hu _).continuous.comp
        ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator.continuous.comp
          (tangentCircleLoop hv p₀ q).continuous)
      source' := by simp
      target' := by simp }
  continuous_toFun := Path.continuous_uncurry_iff.1 <| (tangentCircleLoop hu _).continuous.comp
    ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator.continuous.comp
      (Path.continuous_uncurry_iff.2 (tangentCircleLoop hv p₀).continuous))

@[simp]
theorem tangentCircleDoubleLoop_apply (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ q : sphereEquator v)
    (θ : I) :
    tangentCircleDoubleLoop hu hv p₀ q θ =
      tangentCircleLoop hu ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator p₀)
        ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator (tangentCircleLoop hv p₀ q θ)) :=
  (rfl)

/-- The double loop at `p₀` itself is the constant double loop. -/
@[simp]
theorem tangentCircleDoubleLoop_self (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ : sphereEquator v) :
    tangentCircleDoubleLoop hu hv p₀ p₀ = Path.refl _ := by
  refine Path.ext (funext fun θ ↦ ?_)
  simp only [tangentCircleDoubleLoop_apply, tangentCircleLoop_self, Path.refl_apply]

/-! ### Reading the family on a cube -/

/-- The permutation of the coordinates of `I^(m + 3)` exchanging the two loop coordinates, which
come last after uncurrying a generalized loop of a double loop space, with the first two
coordinates of a generalized loop of tangent circles of tangent circles. -/
private def loopCoordPerm (m : ℕ) : Fin (m + 3) ≃ Fin (m + 3) :=
  Equiv.ofBijective
    (fun i ↦ ⟨if (i : ℕ) = 0 then m + 2 else if (i : ℕ) = 1 then m + 1 else i - 2, by
      split_ifs <;> omega⟩)
    (Finite.injective_iff_bijective.1 fun i j h ↦ by
      have h' := congrArg Fin.val h
      simp only at h'
      ext
      split_ifs at h' <;> omega)

variable {m : ℕ}

/-- Uncurried twice and with its coordinates permuted, the family of double loops read through a
generalized loop `c` of `Σ_p` is the generalized loop of circles tangent to `u` through the circles
tangent to `v` through the points of `c`. -/
private theorem pathLoopSpaceMulEquiv_map_tangentCircleDoubleLoop (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) {p₀ : sphereEquator v} (c : Ω^ (Fin (m + 1)) (sphereEquator v) p₀) :
    pathLoopSpaceMulEquiv (m + 1)
        (pathLoopSpaceMulEquiv m
          ⟦GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀)
            c⟧) =
      ⟦GenLoop.congr _ (loopCoordPerm m) (tangentCircleGenLoop hu
        (GenLoop.map (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator rfl
          (tangentCircleGenLoop hv c)))⟧ := by
  rw [pathLoopSpaceMulEquiv_mk, pathLoopSpaceMulEquiv_mk]
  congr 1
  ext y
  simp only [GenLoop.congr_apply, GenLoop.genLoopGenLoopEquiv_apply, GenLoop.map_apply,
    ContinuousMap.coe_mk, GenLoop.homeomorphOfUnique_symm_apply, tangentCircleDoubleLoop_apply,
    tangentCircleGenLoop_apply]
  -- Both sides are the same circles; only the indexing of the cube coordinates differs.
  congr! 5

/-! ### The Hurewicz classes -/

/-- The generalized loop of circles tangent to `u` through the circles tangent to `v` through the
points of a generalized loop `c` of `Σ_p`, with its coordinates permuted as after uncurrying, is a
homeomorphism off the boundary of the cube when `c` is. -/
private theorem bijective_toSphere_congr_tangentCircleGenLoop (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {p₀ : sphereEquator v} (c : Ω^ (Fin (m + 1)) (sphereEquator v) p₀)
    (hcs : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hci : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin (m + 1)) ∧
      z ∈ Cube.boundary (Fin (m + 1))) :
    Function.Bijective (GenLoop.toSphere (GenLoop.congr _ (loopCoordPerm m)
      (tangentCircleGenLoop hu (GenLoop.map (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator
        rfl (tangentCircleGenLoop hv c))))) := by
  set ι := (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator
  -- The circles tangent to `v` through the points of `c`, read in the equator orthogonal to `u`.
  set c' : Ω^ (Fin (m + 2)) (sphereEquator u) (ι p₀) :=
    GenLoop.map ι rfl (tangentCircleGenLoop hv c)
  have hcs' (q) (hq : q ≠ ι p₀) : ∃ y, c' y = q := by
    obtain ⟨s, rfl⟩ := (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).surjective_sphereToEquator q
    obtain ⟨y, hy⟩ := surjective_tangentCircleGenLoop hv c hcs s
    exact ⟨y, by rw [GenLoop.map_apply, hy]⟩
  have hci' (y z) (h : c' y = c' z) :
      y = z ∨ y ∈ Cube.boundary (Fin (m + 2)) ∧ z ∈ Cube.boundary (Fin (m + 2)) :=
    eq_or_of_tangentCircleGenLoop_eq hv c hcs hci
      ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).injective_sphereToEquator (by
        simpa only [c', GenLoop.map_apply] using h))
  -- The circles tangent to `u` through those, with the cube coordinates permuted.
  refine ⟨(GenLoop.injective_toSphere_iff _).2 fun y z h ↦ ?_,
    (GenLoop.surjective_toSphere_iff _).2 fun w ↦ ?_⟩
  · rcases eq_or_of_tangentCircleGenLoop_eq hu c' hcs' hci' h with h | ⟨hy, hz⟩
    · exact Or.inl (funext fun i ↦ by simpa using congrFun h ((loopCoordPerm m).symm i))
    · exact Or.inr ⟨(Cube.comp_mem_boundary_iff _).1 hy, (Cube.comp_mem_boundary_iff _).1 hz⟩
  · obtain ⟨y, hy⟩ := surjective_tangentCircleGenLoop hu c' hcs' w
    exact ⟨y ∘ (loopCoordPerm m).symm, by simpa [Function.comp_def] using hy⟩

end Family

section Homology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E} {v : (ℝ ∙ u)ᗮ}
  {m : ℕ}

/-- The integral Hurewicz homomorphisms of the sphere `Sⁿ = S^{m+3}` in degree `n` and of its
double loop space in degree `n - 2` are bijective. -/
private theorem bijective_hurewiczIntHom_sphere (hE : finrank ℝ E = m + 4)
    (x : sphere (0 : E) 1) :
    Function.Bijective (hurewiczIntHom (sphere (0 : E) 1) x (m + 2)) ∧
      Function.Bijective (hurewiczIntHom (Ω (Ω (sphere (0 : E) 1) x) (Path.refl _))
        (Path.refl _) m) := by
  have hS (j : ℕ) (hj : j < m + 1 + 2) : Subsingleton (π_ j (sphere (0 : E) 1) x) :=
    subsingleton_homotopyGroup_sphere_of_lt (n := m + 3) hE (by simpa using hj) _
  refine ⟨?_, ?_⟩
  · convert (bijective_hurewicz hS).comp Additive.toMul.bijective using 1
    funext a
    exact hurewiczIntHom_apply _ _ _ a
  have hΩ (j : ℕ) (hj : j < m + 1) :
      Subsingleton (π_ j (Ω (Ω (sphere (0 : E) 1) x) (Path.refl _)) (Path.refl _)) :=
    (subsingleton_homotopyGroup_loopSpace_iff _ j).2
      ((subsingleton_homotopyGroup_loopSpace_iff _ (j + 1)).2 (hS (j + 2) (by omega)))
  rcases m with _ | j
  · -- In degree one, `π₁(Ω²Sⁿ) ≅ π₂(ΩSⁿ)` is commutative.
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero _).2 (hΩ 0 (by omega))
    exact bijective_hurewiczIntHom_zero fundamentalGroupLoopSpaceMulEquiv
  · convert (bijective_hurewicz hΩ).comp Additive.toMul.bijective using 1
    funext a
    exact hurewiczIntHom_apply _ _ _ a

/-- The Hurewicz class of the family of double loops read through a generalized loop `c` of `Σ_p`
that is a homeomorphism off the boundary of the cube generates `H_{n-2}(Ω²Sⁿ; ℤ)` freely. -/
private theorem bijective_zsmul_hurewicz_map_tangentCircleDoubleLoop (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hE : finrank ℝ E = m + 4) {p₀ : sphereEquator v}
    (c : Ω^ (Fin (m + 1)) (sphereEquator v) p₀) (hcs : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hci : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin (m + 1)) ∧
      z ∈ Cube.boundary (Fin (m + 1))) :
    Function.Bijective (fun z : ℤ ↦ z • (GenLoop.hurewicz (ModuleCat.of ℤ ℤ)
      (GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀)
        c)).hom 1) := by
  -- A class `a` generates a group freely, `z ↦ z • a` being bijective, exactly when its image
  -- under an additive equivalence does.
  have bijective_zsmul_map_iff {A B : Type} [AddGroup A] [AddGroup B] (f : A ≃+ B)
      (a : A) : Function.Bijective (fun z : ℤ ↦ z • f a) ↔
        Function.Bijective (fun z : ℤ ↦ z • a) := by
    have h : (fun z : ℤ ↦ z • f a) = f ∘ fun z : ℤ ↦ z • a :=
      funext fun z ↦ (map_zsmul f z a).symm
    rw [h, f.bijective.of_comp_iff']
  set G := GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀) c
  set r := GenLoop.congr _ (loopCoordPerm m) (tangentCircleGenLoop hu
    (GenLoop.map (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator rfl
      (tangentCircleGenLoop hv c)))
  obtain ⟨hHS, hHΩ⟩ := bijective_hurewiczIntHom_sphere hE
    ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator p₀ : sphere (0 : E) 1)
  -- The class of `r` generates `πₙ(Sⁿ)`, hence that of `G` generates `π_{n-2}(Ω²Sⁿ)`.
  have hrgen := (bijective_zsmul_map_iff (AddEquiv.ofBijective _ hHS)
      (Additive.ofMul (⟦r⟧ : HomotopyGroup (Fin (m + 3)) _ _))).1 (by
    rw [AddEquiv.ofBijective_apply, hurewiczIntHom_ofMul_mk]
    exact GenLoop.bijective_zsmul_hurewicz_of_bijective_toSphere
      (bijective_toSphere_congr_tangentCircleGenLoop hu hv c hcs hci))
  have hD : ((pathLoopSpaceMulEquiv m).trans (pathLoopSpaceMulEquiv (m + 1))).toAdditive
      (Additive.ofMul ⟦G⟧) = Additive.ofMul ⟦r⟧ :=
    congrArg Additive.ofMul (pathLoopSpaceMulEquiv_map_tangentCircleDoubleLoop hu hv c)
  have hGgen := (bijective_zsmul_map_iff ((pathLoopSpaceMulEquiv m).trans
      (pathLoopSpaceMulEquiv (m + 1))).toAdditive
      (Additive.ofMul (⟦G⟧ : HomotopyGroup (Fin (m + 1)) _ _))).1 (by rw [hD]; exact hrgen)
  have h := (bijective_zsmul_map_iff (AddEquiv.ofBijective _ hHΩ)
    (Additive.ofMul (⟦G⟧ : HomotopyGroup (Fin (m + 1)) _ _))).2 hGgen
  rwa [AddEquiv.ofBijective_apply, hurewiczIntHom_ofMul_mk] at h

/-- **The double loops swept by tangent circles represent a generator** (Barraud–Damian–
Humilière–Oancea, Proposition 6.21). For orthonormal `u`, `v` and a unit vector `p₀ ⊥ u, v` in a
space `E` of dimension `n + 1 = m + 4`, the family `σ_p : Σ_p → Ω²Sⁿ` of
`TauCeti.tangentCircleDoubleLoop` induces an isomorphism
`H_{n-2}(Σ_p; ℤ) → H_{n-2}(Ω²Sⁿ; ℤ)` from the homology of the `(n - 2)`-sphere `Σ_p`. -/
theorem bijective_singularHomologyMap_tangentCircleDoubleLoop (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hE : finrank ℝ E = m + 4) (p₀ : sphereEquator v) :
    Function.Bijective
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (tangentCircleDoubleLoop hu hv p₀))).hom := by
  have : Fact (finrank ℝ E = m + 3 + 1) := ⟨hE⟩
  have hK : finrank ℝ (ℝ ∙ u)ᗮ = m + 1 + 2 :=
    Submodule.finrank_orthogonal_span_singleton (ne_zero_of_norm_ne_zero (by simp [hu]))
  -- A generalized loop of `Σ_p` covering it off `p₀` and identifying only boundary points.
  obtain ⟨c, hcs, hci⟩ := exists_genLoop_sphereEquator (ne_zero_of_norm_ne_zero (by simp [hv]))
    hK p₀
  have hc : Function.Bijective (GenLoop.toSphere c) :=
    ⟨(GenLoop.injective_toSphere_iff _).2 hci, (GenLoop.surjective_toSphere_iff _).2 fun q ↦ by
      by_cases hq : q = p₀
      · exact ⟨0, by rw [hq, GenLoop.boundary c 0 ⟨0, Or.inl rfl⟩]⟩
      · exact hcs q hq⟩
  -- The family carries the generator of `H_{n-2}(Σ_p)` given by `c` to the generator of
  -- `H_{n-2}(Ω²Sⁿ)` given by its image.
  have hcomp : (fun z : ℤ ↦ z • (GenLoop.hurewicz (ModuleCat.of ℤ ℤ)
      (GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀)
        c)).hom 1) =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (tangentCircleDoubleLoop hu hv p₀))).hom ∘
        fun z : ℤ ↦ z • (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) c).hom 1 := by
    funext z
    rw [Function.comp_apply, GenLoop.hurewicz_map, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (map_zsmul (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (tangentCircleDoubleLoop hu hv p₀))).hom z _).symm
  rw [← (GenLoop.bijective_zsmul_hurewicz_of_bijective_toSphere hc).of_comp_iff, ← hcomp]
  exact bijective_zsmul_hurewicz_map_tangentCircleDoubleLoop hu hv hE c hcs hci

end Homology

end TauCeti
