/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Sphere.TangentCircle
import TauCeti.Algebra.Group.ZMultiples

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
`TauCeti.quaternionFrame`, say), to obtain a fibred family of two-spheres; this file treats the
fibre over one point.

The main result is Proposition 6.21 of the same paper, for `n ≥ 3`: the map `σ : Σ → Ω²Sⁿ`
induces an isomorphism `σ_* : H_{n-2}(Σ; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`
(`TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`). Both groups are infinite
cyclic, so `σ_*` sends the fundamental class of `Σ` to a generator of `H_{n-2}(Ω²Sⁿ; ℤ)`.

The proof reads through `σ` a generalized loop `c` of `Σ` that is a homeomorphism off the boundary
of its cube. Under the loop-space shifts `π_{n-2}(Ω²Sⁿ) ≅ π_{n-1}(ΩSⁿ) ≅ πₙ(Sⁿ)`
(`HomotopyGroup.pathLoopSpaceMulEquiv_mk_eq_genLoopLoopHomeomorph`) the class of `σ ∘ c` becomes the
class of the cube `(y, s, t) ↦ σ(c y)(s)(t)`, which is, up to the order of the cube coordinates,
the family of circles through the circles through the points of `c` (`TauCeti.tangentCircleGenLoop`,
applied twice). That cube is again a homeomorphism off the boundary, so its class generates
`πₙ(Sⁿ)`. By the Hurewicz theorems for `Sⁿ` and for the `(n - 3)`-connected space `Ω²Sⁿ`
(`HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom`,
`HomotopyGroup.bijective_hurewiczIntHom_loopSpace_loopSpace`), the Hurewicz class of `σ ∘ c`
generates `H_{n-2}(Ω²Sⁿ; ℤ)`, while that of `c` generates `H_{n-2}(Σ; ℤ)`. For `n = 3` the
Hurewicz theorem for `Ω²S³` is the one in degree one, which applies because
`π₁(Ω²S³) ≅ π₂(ΩS³)` is commutative.

## Main declarations

* `TauCeti.tangentCircleDoubleLoop hu hv p`: the family `σ : Σ → Ω_p Ω_p Sⁿ` of Example 6.20.
* `TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`: `σ_*` is an isomorphism
  `H_{n-2}(Σ; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Example 6.20 and
  Proposition 6.21.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Real Set
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

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
    simp [e, Equiv.swap_apply_of_ne_of_ne, Fin.succ_succ_ne_one, sub_eq_iff_eq_add]
    grind [Fin.succ_castSucc, Fin.coeSucc_eq_succ]
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
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  have hV : Module.finrank ℝ (ℝ ∙ u)ᗮ = m + 3 := by
    have : Fact (Module.finrank ℝ E = m + 3 + 1) := ⟨hE⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  -- A generalized loop `c` of `Σ` that is a homeomorphism off the boundary of its cube.
  obtain ⟨c, hcs, hci⟩ := exists_genLoop_sphereEquator hv0 (k := m + 1) hV p₀
  have hcs' : Function.Surjective c := fun q ↦ by
    by_cases hq : q = p₀
    · exact ⟨0, hq ▸ GenLoop.boundary c 0 ⟨0, Or.inl rfl⟩⟩
    · exact hcs q hq
  have hc : IsIso (GenLoop.hurewicz R c) := GenLoop.isIso_hurewicz_of_bijective_toSphere R
    ⟨(GenLoop.injective_toSphere_iff c).2 hci, (GenLoop.surjective_toSphere_iff c).2 hcs'⟩
  -- Read through `σ` and the loop-space shifts, `c` becomes a cube `Q` of `Sⁿ` that is again a
  -- homeomorphism off the boundary.
  set γ := GenLoop.map (tangentCircleDoubleLoop hu hv p₀) (tangentCircleDoubleLoop_self hu hv p₀) c
  set Q := GenLoop.genLoopLoopHomeomorph _ (m + 2) (GenLoop.genLoopLoopHomeomorph _ (m + 1) γ)
  have hQiso : IsIso (GenLoop.hurewicz R Q) := GenLoop.isIso_hurewicz_of_bijective_toSphere R
    (bijective_toSphere_genLoopLoopHomeomorph_map_tangentCircleDoubleLoop hu hv c hcs hci)
  -- Connectivity of `Sⁿ` and of `Ω²Sⁿ`, for the Hurewicz theorem.
  have hS (x : sphere (0 : E) 1) :
      ∀ k < m + 1 + 2, Subsingleton (HomotopyGroup (Fin k) (sphere (0 : E) 1) x) :=
    fun k hk ↦ subsingleton_homotopyGroup_sphere_of_lt (n := m + 3) hE (by simpa using hk) x
  -- The two loop-space shifts send the class of `γ` to the class of `Q`.
  have hshift : HomotopyGroup.pathLoopSpaceMulEquiv (m + 1)
      (HomotopyGroup.pathLoopSpaceMulEquiv m ⟦γ⟧) = ⟦Q⟧ := by
    rw [HomotopyGroup.pathLoopSpaceMulEquiv_mk_eq_genLoopLoopHomeomorph,
      HomotopyGroup.pathLoopSpaceMulEquiv_mk_eq_genLoopLoopHomeomorph]
  -- Through the Hurewicz theorems for `Sⁿ` and for `Ω²Sⁿ`, the Hurewicz class of `γ` generates.
  have hQgen := (HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom (hS _) Q).1 hQiso
  have hF : ((HomotopyGroup.pathLoopSpaceMulEquiv m).trans
      (HomotopyGroup.pathLoopSpaceMulEquiv (m + 1))).toAdditive
        (Additive.ofMul (α := π_ (m + 1) (Ω (Ω (sphere (0 : E) 1) _) (Path.refl _)) _) ⟦γ⟧) =
      Additive.ofMul (α := π_ (m + 1 + 2) (sphere (0 : E) 1) _) ⟦Q⟧ := by
    -- `toMul (ofMul ⟦γ⟧)` is `⟦γ⟧`, read in `π_ (m + 1)`
    rw [MulEquiv.toAdditive_apply_apply, MulEquiv.trans_apply]
    exact congrArg Additive.ofMul hshift
  rw [← hF] at hQgen
  have hγgen := (AddEquiv.bijective_zmultiplesHom_apply_iff _ _).1 hQgen
  have hγ := (HomotopyGroup.isIso_hurewicz_iff_bijective_zmultiplesHom_of_bijective
    (HomotopyGroup.bijective_hurewiczIntHom_loopSpace_loopSpace (hS _)) γ).2 hγgen
  rw [GenLoop.hurewicz_map] at hγ
  exact IsIso.of_isIso_comp_left (GenLoop.hurewicz R c) _

end TauCeti
