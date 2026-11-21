/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Sphere.TangentCircle
public import TauCeti.AlgebraicTopology.Sphere.TwoFieldFamily
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.LoopSpace
import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# Double loops of a sphere swept by tangent circles

Let `u` be a unit vector of a real inner product space `E` of dimension `n + 1`, with unit sphere
`Sⁿ`, and let `v` be a unit vector of the hyperplane `u⊥`. For a point `p` of the unit sphere
`S_{u⊥}` of `u⊥` orthogonal to `v`, the points of `S_{u⊥}` orthogonal to `v` form the equator
`Σ = E_{u⊥,p,v}` through `p`, a sphere of dimension `n - 2`. Barraud–Damian–Humilière–Oancea
(Example 6.20) attach to each `q ∈ Σ` a double loop `σ(q)` of `Sⁿ` at `p`, through the composite

`Σ = E_{u⊥,p,v} → Ω_p S_{u⊥} → Ω_p Ω_p Sⁿ`

of the map `φ_{u⊥,v}`, which sends `q` to the circle of `S_{u⊥}` through `p` tangent to `v` and
through `q`, and the loop map of `φ_{E,u}`, which sends a point `w` of the equator `S_{u⊥}` of
`Sⁿ` to the circle of `Sⁿ` through `p` tangent to `u` and through `w`
(`TauCeti.tangentCircleLoop`, `TauCeti.tangentCircleDoubleLoop`). Explicitly,

`σ(q)(s)(t) = tangentCircle p u (tangentCircle p v q (2πs)) (2πt)`.

The paper applies this construction at every point `p` of a sphere `S^{4k-1}`, with `u` and `v`
two pointwise orthonormal tangent vector fields (two of the quaternionic fields
`TauCeti.quaternionFrame`, say), to obtain a family of two-spheres in `Sⁿ` fibred over `Sⁿ`, a
map from its total space to `Map(S², Sⁿ)` (`TauCeti.twoFieldSphereFamily`); this file treats the
fibre over one point.

The main result is Proposition 6.21 of the same paper, for `n ≥ 3`: the map `σ : Σ → Ω²Sⁿ`
induces an isomorphism `σ_* : H_{n-2}(Σ; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`
(`TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`). Both groups are infinite
cyclic, so `σ_*` sends the fundamental class of `Σ` to a generator of `H_{n-2}(Ω²Sⁿ; ℤ)`. In
particular, at every point `x` of `Sⁿ`, the group `H_{n-2}(Map_*(S², Sⁿ); ℤ)` of based maps
`(S², north) → (Sⁿ, x)` has an element of infinite order
(`TauCeti.exists_not_isOfFinAddOrder_homology_basedMap_sphere`).

The same holds for the fibres of the fibred family. Over a point `x` of `Sⁿ`, the fibre `Σₓ` is the
equator through `x` orthogonal to `v x` in the unit sphere of `(u x)⊥`, and on the square the
restriction `Σₓ → Map_*(S², Sⁿ)` of the family is the family of double loops above for the unit
vectors `u x` and `v x`, read in `Map_*(S², Sⁿ) ≃ₜ Ω²Sⁿ` with the first cube coordinate as the
outer loop parameter. So it also induces an isomorphism on `H_{n-2}(-; ℤ)`
(`TauCeti.isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber`): the fibre class of the
family generates `H_{n-2}(Map_*(S², Sⁿ); ℤ) ≅ ℤ` over every point.

The proof reads through `σ` a generalized loop `c` of `Σ` that is a homeomorphism off the boundary
of its cube. Under the loop-space shifts `π_{n-2}(Ω²Sⁿ) ≅ π_{n-1}(ΩSⁿ) ≅ πₙ(Sⁿ)`
(`HomotopyGroup.pathLoopSpaceMulEquiv_mk_eq_genLoopLoopHomeomorph`) the class of `σ ∘ c` becomes the
class of the cube `(y, s, t) ↦ σ(c y)(s)(t)`, which is, up to the order of the cube coordinates,
the family of circles through the circles through the points of `c` (`TauCeti.tangentCircleGenLoop`,
applied twice). That cube is again a homeomorphism off the boundary, so its class generates
`πₙ(Sⁿ)`. Both loop-space shifts preserve generating Hurewicz classes
(`HomotopyGroup.isIso_hurewicz_genLoopLoopHomeomorph_iff`, from the Hurewicz theorem for `Sⁿ` and
the Hurewicz criterion for the loop spaces `ΩSⁿ` and `Ω²Sⁿ`, which in degree one, for `n = 3`, uses
that the fundamental group of a loop space is commutative), so the Hurewicz class of `σ ∘ c`
generates `H_{n-2}(Ω²Sⁿ; ℤ)`, while that of `c` generates `H_{n-2}(Σ; ℤ)`.

## Main declarations

* `TauCeti.tangentCircleDoubleLoop hu hv p`: the family `σ : Σ → Ω_p Ω_p Sⁿ` of Example 6.20.
* `TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`: `σ_*` is an isomorphism
  `H_{n-2}(Σ; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`.
* `TauCeti.exists_not_isOfFinAddOrder_homology_basedMap_sphere`: `H_{n-2}(Map_*(S², Sⁿ); ℤ)` has
  an element of infinite order, for `n ≥ 3`.
* `TauCeti.isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber`: over every point `x`, the
  restriction `Σₓ → Map_*(S², Sⁿ)` of the family of two-spheres of two orthonormal tangent fields
  is an isomorphism on `H_{n-2}(-; ℤ)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Example 6.20
  and Proposition 6.21.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Real Set
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

section DoubleLoop

/-! ### The double loops `σ` -/

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E} {v : (ℝ ∙ u)ᗮ}

/-- **The double loops of Barraud–Damian–Humilière–Oancea, Example 6.20.** For unit vectors `u` of
`E` and `v` of `u⊥`, and a point `p₀` of the equator `Σ` of the unit sphere of `u⊥` orthogonal to
`v`, the map `σ : Σ → Ω_p Ω_p Sⁿ` composing `φ_{u⊥,v} : Σ → Ω_p S_{u⊥}` with the loop map of
`φ_{E,u} : S_{u⊥} → Ω_p Sⁿ`, where `S_{u⊥}` is the equator of `Sⁿ` orthogonal to `u`:
`σ(q)(s)(t) = tangentCircle p₀ u (tangentCircle p₀ v q (2πs)) (2πt)`
(`TauCeti.coe_tangentCircleDoubleLoop_apply`). Since `φ_{E,u}` sends `p₀` to the constant loop,
`σ(q)` is a double loop based at the constant loop. -/
def tangentCircleDoubleLoop (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ : sphereEquator v) :
    C(sphereEquator v, Ω (Ω (sphere (0 : E) 1)
      (orthogonalSphereToEquator u (p₀ : sphere (0 : (ℝ ∙ u)ᗮ) 1) : sphere (0 : E) 1))
        (Path.refl _)) where
  toFun q := (((tangentCircleLoop hv p₀ q).map (orthogonalSphereToEquator u).continuous).map
    (tangentCircleLoop hu (orthogonalSphereToEquator u p₀)).continuous).cast
      (tangentCircleLoop_self hu _).symm (tangentCircleLoop_self hu _).symm
  continuous_toFun := by
    have h : Continuous fun x : sphereEquator v × I =>
        tangentCircleLoop hu (orthogonalSphereToEquator u p₀)
          (orthogonalSphereToEquator u (tangentCircleLoop hv p₀ x.1 x.2)) :=
      (tangentCircleLoop hu _).continuous.comp ((orthogonalSphereToEquator u).continuous.comp
        (Path.continuous_uncurry_iff.2 (tangentCircleLoop hv p₀).continuous))
    exact Path.continuous_uncurry_iff.1 (h.congr fun _ => rfl)

/-- The loop `σ(q)(s)` is the circle of `Sⁿ` through `p₀` tangent to `u` and through the point at
time `s` of the circle of the unit sphere of `u⊥` through `p₀` tangent to `v` and through `q`. -/
theorem tangentCircleDoubleLoop_apply (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ q : sphereEquator v)
    (s : I) :
    tangentCircleDoubleLoop hu hv p₀ q s = tangentCircleLoop hu (orthogonalSphereToEquator u p₀)
      (orthogonalSphereToEquator u (tangentCircleLoop hv p₀ q s)) :=
  (rfl)

@[simp]
theorem coe_tangentCircleDoubleLoop_apply (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ q : sphereEquator v)
    (s t : I) :
    (tangentCircleDoubleLoop hu hv p₀ q s t : E) =
      tangentCircle (((p₀ : sphere (0 : (ℝ ∙ u)ᗮ) 1) : (ℝ ∙ u)ᗮ) : E) u
        ((tangentCircle ((p₀ : sphere (0 : (ℝ ∙ u)ᗮ) 1) : (ℝ ∙ u)ᗮ) v
          ((q : sphere (0 : (ℝ ∙ u)ᗮ) 1) : (ℝ ∙ u)ᗮ) (2 * π * s) : (ℝ ∙ u)ᗮ) : E) (2 * π * t) := by
  simp [tangentCircleDoubleLoop_apply]

/-- The double loop of the base point is the constant double loop. -/
@[simp]
theorem tangentCircleDoubleLoop_self (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ : sphereEquator v) :
    tangentCircleDoubleLoop hu hv p₀ p₀ = Path.refl _ := by
  refine Path.ext (funext fun s => Path.ext (funext fun t => Subtype.ext ?_))
  simp

/-! ### The class of the double loops -/

/-- Under the two loop-space shifts, a generalized loop `c` of `Σ` read through the double loops
`σ` becomes the circles through the circles through the points of `c`, with the cube coordinates
reordered by `GenLoop.congr` along the permutation of `Fin (k + 3)` sending `0`, `1` and `j + 2`
to `k + 2`, `k + 1` and `j`. -/
private theorem genLoopLoopHomeomorph_map_tangentCircleDoubleLoop (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) {p₀ : sphereEquator v} {k : ℕ} (c : Ω^ (Fin (k + 1)) (sphereEquator v) p₀) :
    GenLoop.genLoopLoopHomeomorph _ (k + 2) (GenLoop.genLoopLoopHomeomorph _ (k + 1)
      (GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀) c)) =
      GenLoop.congr _ ((Equiv.swap 0 1).trans
          ((Fin.last (k + 2)).cycleRange.symm.trans (Fin.last (k + 2)).cycleRange.symm))
        (tangentCircleGenLoop hu (GenLoop.map (orthogonalSphereToEquator u) rfl
          (tangentCircleGenLoop hv c))) := by
  set e : Fin (k + 3) ≃ Fin (k + 3) := (Equiv.swap 0 1).trans
    ((Fin.last (k + 2)).cycleRange.symm.trans (Fin.last (k + 2)).cycleRange.symm)
  have he₀ : e 0 = Fin.last _ := by simp [e, Fin.ext_iff]
  have he₁ : e (0 : Fin (k + 2)).succ = (Fin.last _).castSucc := by
    simp [e, Fin.ext_iff, Fin.coe_sub_one]
  have he₂ (j : Fin (k + 1)) : e j.succ.succ = j.castSucc.castSucc := by
    simp [e, Equiv.swap_apply_of_ne_of_ne, Fin.succ_succ_ne_one]
  refine GenLoop.ext _ _ fun w => ?_
  rw [GenLoop.genLoopLoopHomeomorph_apply, GenLoop.genLoopLoopHomeomorph_apply,
    GenLoop.map_apply, tangentCircleDoubleLoop_apply, GenLoop.congr_apply,
    tangentCircleGenLoop_apply, GenLoop.map_apply, tangentCircleGenLoop_apply]
  simp only [Fin.tail_def, he₀, he₁, he₂]

/-- If a generalized loop `c` of `Σ` covers `Σ` off its base point and identifies only points of
the boundary of its cube, then so does the cube of `Sⁿ` that the two loop-space shifts attach to
`c` read through the double loops `σ`: it is the circles through the circles through the points of
`c`, up to the order of the coordinates. -/
private theorem bijective_toSphere_genLoopLoopHomeomorph_map_tangentCircleDoubleLoop
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {p₀ : sphereEquator v} {k : ℕ}
    (c : Ω^ (Fin (k + 1)) (sphereEquator v) p₀)
    (hcs : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hci : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin (k + 1)) ∧
      z ∈ Cube.boundary (Fin (k + 1))) :
    Function.Bijective (GenLoop.toSphere (GenLoop.genLoopLoopHomeomorph _ (k + 2)
      (GenLoop.genLoopLoopHomeomorph _ (k + 1) (GenLoop.map (tangentCircleDoubleLoop hu hv p₀)
        (tangentCircleDoubleLoop_self hu hv p₀) c)))) := by
  -- The circles `c₁` of the unit sphere of `u⊥` through the points of `c`, read in the equator
  -- `c₂` of `Sⁿ`; the cube is the circles of `Sⁿ` through the points of `c₂`, reordered.
  set c₁ := tangentCircleGenLoop hv c
  have hc₁i : ∀ y z, c₁ y = c₁ z →
      y = z ∨ y ∈ Cube.boundary (Fin (k + 2)) ∧ z ∈ Cube.boundary (Fin (k + 2)) :=
    fun _ _ h ↦ eq_or_of_tangentCircleGenLoop_eq hv c hcs hci h
  have hc₁s := surjective_tangentCircleGenLoop hv c hcs
  set c₂ := GenLoop.map (orthogonalSphereToEquator u) rfl c₁
  have hc₂s : ∀ q, q ≠ orthogonalSphereToEquator u p₀ → ∃ y, c₂ y = q := fun q _ ↦ by
    obtain ⟨q', rfl⟩ := surjective_orthogonalSphereToEquator u q
    obtain ⟨y, rfl⟩ := hc₁s q'
    exact ⟨y, GenLoop.map_apply _ _ _ _⟩
  have hc₂i : ∀ y z, c₂ y = c₂ z →
      y = z ∨ y ∈ Cube.boundary (Fin (k + 2)) ∧ z ∈ Cube.boundary (Fin (k + 2)) :=
    fun y z h ↦ hc₁i y z (injective_orthogonalSphereToEquator u (by
      rwa [GenLoop.map_apply, GenLoop.map_apply] at h))
  rw [genLoopLoopHomeomorph_map_tangentCircleDoubleLoop hu hv c]
  generalize (Equiv.swap (0 : Fin (k + 3)) 1).trans
    ((Fin.last (k + 2)).cycleRange.symm.trans (Fin.last (k + 2)).cycleRange.symm) = e
  -- Reordering the cube coordinates along `e` preserves the boundary of the cube.
  refine ⟨(GenLoop.injective_toSphere_iff _).2 fun y z h ↦ ?_,
    (GenLoop.surjective_toSphere_iff _).2 fun q ↦ ?_⟩
  · rw [GenLoop.congr_apply, GenLoop.congr_apply] at h
    rcases eq_or_of_tangentCircleGenLoop_eq hu c₂ hc₂s hc₂i h with h | ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    · exact Or.inl (funext fun i ↦ by simpa using congrFun h (e.symm i))
    · exact Or.inr ⟨⟨e i, hi⟩, ⟨e j, hj⟩⟩
  · obtain ⟨y, rfl⟩ := surjective_tangentCircleGenLoop hu c₂ hc₂s q
    refine ⟨fun i ↦ y (e.symm i), ?_⟩
    simp only [GenLoop.congr_apply, Equiv.symm_apply_apply, c₂, c₁]

/-- For `n ≥ 3`, every point `p₀` of the equator `Σ` is the base point of a generalized loop `c`
of `Σ` that is a homeomorphism off the boundary of its cube, so whose Hurewicz class generates
`H_{n-2}(Σ; ℤ)`. -/
private theorem exists_genLoop_sphereEquator_isIso_hurewicz {m : ℕ}
    (hE : Module.finrank ℝ E = m + 4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ : sphereEquator v) :
    ∃ c : Ω^ (Fin (m + 1)) (sphereEquator v) p₀, (∀ q, q ≠ p₀ → ∃ y, c y = q) ∧
      (∀ y z, c y = c z →
        y = z ∨ y ∈ Cube.boundary (Fin (m + 1)) ∧ z ∈ Cube.boundary (Fin (m + 1))) ∧
      IsIso (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) c) := by
  have hV : Module.finrank ℝ (ℝ ∙ u)ᗮ = m + 3 := by
    have : Fact (Module.finrank ℝ E = m + 3 + 1) := ⟨hE⟩
    exact Submodule.finrank_orthogonal_span_singleton (norm_ne_zero_iff.1 (hu ▸ one_ne_zero))
  obtain ⟨c, hcs, hci⟩ :=
    exists_genLoop_sphereEquator (norm_ne_zero_iff.1 (hv ▸ one_ne_zero)) (k := m + 1) hV p₀
  exact ⟨c, hcs, hci, GenLoop.isIso_hurewicz_of_forall_ne _ hcs hci⟩

/-- **The double loops generate the homology of the double loop space** (Proposition 6.21 of
Barraud–Damian–Humilière–Oancea). For a unit vector `u` of a real inner product space `E` of
dimension `n + 1 ≥ 4`, a unit vector `v` of `u⊥` and a point `p₀` of the equator `Σ` of the unit
sphere of `u⊥` orthogonal to `v`, the family of double loops `σ : Σ → Ω²Sⁿ` of Example 6.20
induces an isomorphism `σ_* : H_{n-2}(Σ; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`. As `Σ` is a sphere of dimension
`n - 2`, this says that `σ_*` sends the fundamental class of `Σ` to a generator of
`H_{n-2}(Ω²Sⁿ; ℤ) ≅ ℤ`. -/
theorem isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop {m : ℕ}
    (hE : Module.finrank ℝ E = m + 4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p₀ : sphereEquator v) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (tangentCircleDoubleLoop hu hv p₀))) := by
  let R := ModuleCat.of ℤ ℤ
  -- A generalized loop `c` of `Σ` that is a homeomorphism off the boundary of its cube.
  obtain ⟨c, hcs, hci, hc⟩ := exists_genLoop_sphereEquator_isIso_hurewicz hE hu hv p₀
  -- Read through `σ` and the loop-space shifts, `c` becomes a cube `Q` of `Sⁿ` that is again a
  -- homeomorphism off the boundary.
  set γ := GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀) c
  set Q := GenLoop.genLoopLoopHomeomorph _ (m + 2) (GenLoop.genLoopLoopHomeomorph _ (m + 1) γ)
  have hQiso : IsIso (GenLoop.hurewicz R Q) := GenLoop.isIso_hurewicz_of_bijective_toSphere R
    (bijective_toSphere_genLoopLoopHomeomorph_map_tangentCircleDoubleLoop hu hv c hcs hci)
  -- Connectivity of `Sⁿ`, for the Hurewicz theorem.
  have hS (x : sphere (0 : E) 1) :
      ∀ k < m + 1 + 2, Subsingleton (HomotopyGroup (Fin k) (sphere (0 : E) 1) x) :=
    fun k hk ↦ subsingleton_homotopyGroup_sphere_of_lt (n := m + 3) hE (by simpa using hk) x
  -- The loop-space shifts from `Ω²Sⁿ` to `ΩSⁿ` and from `ΩSⁿ` to `Sⁿ` preserve generating Hurewicz
  -- classes, so the Hurewicz class of `γ` generates.
  have hγ := (HomotopyGroup.isIso_hurewicz_genLoopLoopHomeomorph_iff (n := m)
    (fun k hk ↦ (subsingleton_homotopyGroup_loopSpace_iff _ k).2 (hS _ (k + 1) (by omega))) γ).1
    ((HomotopyGroup.isIso_hurewicz_genLoopLoopHomeomorph_iff (n := m + 1) (hS _) _).1 hQiso)
  rw [GenLoop.hurewicz_map] at hγ
  exact IsIso.of_isIso_comp_left (GenLoop.hurewicz R c) _

/-- The double loops of the unit sphere at a point `a`, read as the based maps
`(S², north) → (Sⁿ, x)` for a point `x = a`: `Ω (Ω X) = Ω^[2] X` by definition, and
`Ω^[2] X ≃ₜ Map_*(S², X)`. -/
private def doubleLoopBasedMapHomeomorph {a x : sphere (0 : E) 1} (ha : a = x) :
    Ω (Ω (sphere (0 : E) 1) a) (Path.refl a) ≃ₜ
      BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north x :=
  (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
    ⟨sphere (0 : E) 1, a⟩ Sphere2.north).symm.trans
      ((Homeomorph.refl _).subtype fun f ↦ by rw [ha]; rfl)

/-- **`H_{n-2}(Map_*(S², Sⁿ); ℤ)` has an element of infinite order**, for the unit sphere `Sⁿ` of
an `(n + 1)`-dimensional real inner product space with `n ≥ 3`, at every base point `x`. It is the
image of a generator of `H_{n-2}(S^{n-2}; ℤ)` under the double loops of
Barraud–Damian–Humilière–Oancea, Example 6.20, through three orthonormal vectors `x`, `u`, `v`
(`TauCeti.tangentCircleDoubleLoop`), which induce an isomorphism on `H_{n-2}`. -/
theorem exists_not_isOfFinAddOrder_homology_basedMap_sphere {m : ℕ}
    (hE : Module.finrank ℝ E = m + 4) (x : sphere (0 : E) 1) :
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
  -- The Hurewicz class of a generalized loop of `Σ` that is a homeomorphism off the boundary of
  -- its cube generates `H_{m+1}(Σ; ℤ)`.
  let R := ModuleCat.of ℤ ℤ
  obtain ⟨c, -, -, _⟩ := exists_genLoop_sphereEquator_isIso_hurewicz hE hu hv' p₀
  have := isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop hE hu hv' p₀
  -- The double loops are based at `x`, and read as based maps `(S², north) → (Sⁿ, x)`.
  set a := (orthogonalSphereToEquator u (p₀ : sphere (0 : (ℝ ∙ u)ᗮ) 1) : sphere (0 : E) 1)
  have ha : a = x := Subtype.ext (by simp [a, p₀])
  let Φ := doubleLoopBasedMapHomeomorph ha
  -- So `ℤ ≅ H_{m+1}(Map_*(S², Sⁿ); ℤ)`, through the coefficients `ULift ℤ ≅ ℤ`.
  let e : R ≅ ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north
      x))).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) : ModuleCat.{0} ℤ) :=
    asIso (GenLoop.hurewicz R c ≫ ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj R).map
      (TopCat.ofHom (tangentCircleDoubleLoop hu hv' p₀))) ≪≫
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).mapIso
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm).app _ ≪≫
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo Φ)
  have hinj : Function.Injective e.hom.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  exact ⟨e.hom.hom 1, (hinj.isOfFinAddOrder_iff (f := e.hom.hom.toAddMonoidHom)).not.2
    (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)⟩

end DoubleLoop

/-! ### The two-spheres over a point of a sphere with two orthonormal tangent fields -/

section TwoFieldFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])
  (hu : Continuous u) (hv : Continuous v)

/-- On the square, the based two-sphere over `x` of the point `(x, q)` of the fibre is the double
loop `σ(q)` of `TauCeti.tangentCircleDoubleLoop` for the unit vectors `u x` and `v x`, read with
the first cube coordinate as the loop parameter of the loop of loops. -/
private theorem twoFieldSphereFamilyFiber_sphereCollapse (x : sphere (0 : E) 1)
    (huv : ⟪v x, u x⟫ = 0) (hux : ‖u x‖ = 1)
    (hvx : ‖(⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ : (ℝ ∙ u x)ᗮ)‖ = 1)
    (p₀ q : sphereEquator
      (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ : (ℝ ∙ u x)ᗮ))
    (hp₀ : (((p₀ : sphere (0 : (ℝ ∙ u x)ᗮ) 1) : (ℝ ∙ u x)ᗮ) : E) = x) (y : I^(Fin 2)) :
    (twoFieldSphereFamilyFiber h hu hv x (twoFieldEquatorsFiberHomeomorph huv q)).val
        (sphereCollapse 2 Sphere2.north y) =
      tangentCircleDoubleLoop hux hvx p₀ q (y 0) (y 1) := by
  apply Subtype.ext
  rw [coe_twoFieldSphereFamilyFiber_apply, coe_twoFieldSphereFamily_sphereCollapse,
    coe_tangentCircleDoubleLoop_apply, Submodule.coe_tangentCircle]
  simp [hp₀]

/-- **The two-spheres over a point generate the homology of the double loop space**
(Proposition 6.21 of Barraud–Damian–Humilière–Oancea, for the fibred family of Example 6.20). Let
`u`, `v` be continuous tangent vector fields on the unit sphere `Sⁿ` of a real inner product space
of dimension `n + 1 ≥ 5`, orthonormal at every point. Over every point `x`, the family of
two-spheres `σ` restricts to the fibre `Σₓ ≅ Sⁿ⁻²` as a map `Σₓ → Map_*(S², Sⁿ)` into the based
mapping space, which is the double loop space of `Sⁿ`. This map induces an isomorphism
`H_{n-2}(Σₓ; ℤ) ≅ H_{n-2}(Map_*(S², Sⁿ); ℤ)`, so it sends the fundamental class of `Σₓ` to a
generator of `H_{n-2}(Ω²Sⁿ; ℤ) ≅ ℤ`. -/
theorem isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber {m : ℕ}
    (hE : Module.finrank ℝ E = m + 5) (x : sphere (0 : E) 1) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (twoFieldSphereFamilyFiber h hu hv x))) := by
  -- The unit vectors `u x` and `v x`, and the point `x` of the fibre over `x`.
  have huv : ⟪v x, u x⟫ = 0 := by simpa using (h x).inner_eq_zero (by decide : (2 : Fin 3) ≠ 1)
  have hux : ‖u x‖ = 1 := by simpa using (h x).norm_eq_one 1
  have hvx : ‖(⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ :
      (ℝ ∙ u x)ᗮ)‖ = 1 := by simpa using (h x).norm_eq_one 2
  set e := twoFieldEquatorsFiberHomeomorph huv
  set p₀ := e.symm ⟨⟨(x, x), mk_self_mem_twoFieldEquators (h x)⟩, rfl⟩
  have hp₀ : (((p₀ : sphere (0 : (ℝ ∙ u x)ᗮ) 1) : (ℝ ∙ u x)ᗮ) : E) = x :=
    coe_twoFieldEquatorsFiberHomeomorph_symm_apply huv _
  -- The double loops at the base point `a = x` of `tangentCircleDoubleLoop` are the based maps
  -- `(S², north) → (Sⁿ, x)`, through the generalized loops of the cube `I²`.
  set a := (orthogonalSphereToEquator (u x) p₀ : sphere (0 : E) 1)
  have ha : a = x := Subtype.ext (by simp [a, hp₀])
  let B := BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
    ⟨sphere (0 : E) 1, a⟩ Sphere2.north
  -- `Ω^[2] X` is `Ω (Ω X)` by definition (`iteratedLoopSpace` unfolds via `loopSpace^[2]`), so
  -- `B.symm` is a homeomorphism out of the nested loop space up to this unfolding.
  let Φ := doubleLoopBasedMapHomeomorph ha
  have hsq : (twoFieldSphereFamilyFiber h hu hv x).comp (e : C(_, _)) =
      (Φ : C(_, _)).comp (tangentCircleDoubleLoop hux hvx p₀) := by
    ext q z : 3
    obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
    refine (twoFieldSphereFamilyFiber_sphereCollapse h hu hv x huv hux hvx p₀ q hp₀ y).trans ?_
    -- Read through `Map_*(S², Sⁿ) ≃ₜ Ω^[2] Sⁿ`, the double loop `σ(q)` is the cube loop `σ(q)`.
    -- The nested loop `σ(q)` is an element of `Ω^[2] Sⁿ` by the same definitional unfolding.
    have hγ := (congrArg (BasedTopologicalSpace.iteratedLoopSpaceHomeomorph 2 _)
      (B.apply_symm_apply (tangentCircleDoubleLoop hux hvx p₀ q))).symm.trans
      (BasedTopologicalSpace.iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace
        2 ⟨sphere (0 : E) 1, a⟩ Sphere2.north _)
    exact ((BasedTopologicalSpace.iteratedLoopSpaceHomeomorph_two_apply _ _ y).symm.trans
      (DFunLike.congr_fun hγ y)).trans (basedMapSphereHomeomorph_apply ..)
  -- So the fibre map is the double loops of `tangentCircleDoubleLoop` up to homeomorphisms.
  let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj (ModuleCat.of ℤ ℤ)
  have hσ := isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop hE hux hvx p₀
  have hcomp : (TopCat.isoOfHomeo (X := TopCat.of _) (Y := TopCat.of _) e).hom ≫
      TopCat.ofHom (twoFieldSphereFamilyFiber h hu hv x) =
      TopCat.ofHom (tangentCircleDoubleLoop hux hvx p₀) ≫
        (TopCat.isoOfHomeo (X := TopCat.of _) (Y := TopCat.of _) Φ).hom := by
    ext q : 1
    exact DFunLike.congr_fun hsq q
  have : IsIso (F.map ((TopCat.isoOfHomeo (X := TopCat.of _) (Y := TopCat.of _) e).hom ≫
      TopCat.ofHom (twoFieldSphereFamilyFiber h hu hv x))) := by
    rw [hcomp, F.map_comp]
    infer_instance
  rw [F.map_comp] at this
  exact IsIso.of_isIso_comp_left
    (F.map (TopCat.isoOfHomeo (X := TopCat.of _) (Y := TopCat.of _) e).hom) _

end TwoFieldFamily

end TauCeti
