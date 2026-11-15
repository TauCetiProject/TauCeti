/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.Geometry.Sphere.TangentCircle

/-!
# Sweeping a sphere by circles tangent to a direction

Let `p` and `u` be orthonormal vectors of a real inner product space `V`. The points `q` of the
unit sphere `S_V` orthogonal to `u` form the equator `E` through `p` orthogonal to `u`. For each
`q ∈ E`, `TauCeti.tangentCircle p u q` is the circle on `S_V` through `p` and `q` tangent to `u`
at `p`, run from `p` proportionally to arc length. Every point of `S_V` other than `p` lies on
exactly one of these circles, at exactly one time strictly between `0` and `2π`
(`TauCeti.eq_of_tangentCircle_eq`, `TauCeti.exists_tangentCircle_eq`, in
`TauCeti.Geometry.Sphere.TangentCircle`). Hence the family of circles, read on a cube through a
generalized loop `c` of `E` that covers `E` off `p` and identifies only points of the boundary of
its cube, is a generalized loop of `S_V` one dimension higher with the same two properties
(`TauCeti.tangentCircleGenLoop`, `TauCeti.eq_or_of_tangentCircleGenLoop_eq`,
`TauCeti.surjective_tangentCircleGenLoop`). Its pointed map out of the sphere is then a
homeomorphism, so its Hurewicz class generates the top homology of `S_V`
(`TauCeti.isIso_hurewicz_tangentCircleGenLoop`).

This is the family `φ_{V,u} : E_{V,p,u} → Ω_p S_V` of Barraud–Damian–Humilière–Oancea,
Example 6.20, and the statement that its adjoint represents a generator of the top homotopy and
homology of `S_V` is the first step of their Proposition 6.21. The two properties proved of the
circles are those asked of `c`, which is what the composite `Σ_p → Ω_p E → Ω_p Ω_p Sⁿ` of
Example 6.20 needs: there `c` is itself a family of circles, in a sphere of one dimension less.
For a sphere of dimension `k + 1`, the cube collapse `TauCeti.cubeToSphere` onto the equator
`TauCeti.sphereEquator u` meets the hypotheses on `c` (`TauCeti.exists_genLoop_sphereEquator`, in
`TauCeti.AlgebraicTopology.Sphere.Equator`).

## Main declarations

* `TauCeti.tangentCircleGenLoop hu c`: the circles through the points of a generalized loop `c`
  of the equator, as a generalized loop of the sphere.
* `TauCeti.tangentCircleLoop hu p`: the map `φ_{V,u}` itself, sending a point `q` of the equator
  to the circle through `p` and `q` as a loop at `p`; `tangentCircleGenLoop` reads it pointwise
  (`TauCeti.tangentCircleGenLoop_apply`).
* `TauCeti.isIso_hurewicz_tangentCircleGenLoop`: its Hurewicz class is an isomorphism
  `R ≅ H_{k+1}(S_V; R)` when `c` is surjective off `p` and identifies only boundary points.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Example 6.20 and Proposition 6.21.
-/

public section

noncomputable section

open Metric Real Set
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}

/-! ### The loops `φ_{V,u}` -/

/-- The map `φ_{V,u}` of Barraud–Damian–Humilière–Oancea, Example 6.20: for a point `p₀` of the
equator of the unit sphere `S_V` orthogonal to the unit vector `u`, it sends a point `q` of that
equator to the circle of `S_V` through `p₀` tangent to `u` and through `q`, run from `p₀`
proportionally to arc length, as a loop at `p₀`. It sends `p₀` to the constant loop
(`TauCeti.tangentCircleLoop_self`). -/
def tangentCircleLoop (hu : ‖u‖ = 1) (p₀ : sphereEquator u) :
    C(sphereEquator u, Ω (sphere (0 : V) 1) (p₀ : sphere (0 : V) 1)) where
  toFun q :=
    { toFun t := ⟨tangentCircle ((p₀ : sphere (0 : V) 1) : V) u ((q : sphere (0 : V) 1) : V)
          (2 * π * t),
        mem_sphere_zero_iff_norm.2 (norm_tangentCircle (mem_sphere_zero_iff_norm.1 p₀.1.2) hu
          (mem_sphereEquator.1 p₀.2) (mem_sphere_zero_iff_norm.1 q.1.2) (mem_sphereEquator.1 q.2)
          _)⟩
      continuous_toFun := ((continuous_tangentCircle _ u).comp
        (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by
        simpa using tangentCircle_add_two_pi ((p₀ : sphere (0 : V) 1) : V) u
          ((q : sphere (0 : V) 1) : V) 0) }
  continuous_toFun := by
    refine Path.continuous_uncurry_iff.1 (Continuous.subtype_mk ?_ _)
    exact (continuous_tangentCircle _ u).comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))

@[simp]
theorem coe_tangentCircleLoop_apply (hu : ‖u‖ = 1) (p₀ q : sphereEquator u) (t : I) :
    (tangentCircleLoop hu p₀ q t : V) =
      tangentCircle ((p₀ : sphere (0 : V) 1) : V) u ((q : sphere (0 : V) 1) : V) (2 * π * t) :=
  (rfl)

/-- The circle through `p₀` and `p₀` is the constant loop. -/
@[simp]
theorem tangentCircleLoop_self (hu : ‖u‖ = 1) (p₀ : sphereEquator u) :
    tangentCircleLoop hu p₀ p₀ = Path.refl _ :=
  Path.ext (funext fun t => Subtype.ext (by simp))

/-! ### The family of circles as a generalized loop -/

variable {k : ℕ} {p₀ : sphereEquator u}

/-- **The circles through the points of a generalized loop of the equator.** For a generalized
loop `c : I^k → E` of the equator `E` at `p₀`, the generalized loop of the unit sphere at `p₀`
sending `y` to the point at the angle `2π y₀` of the circle through `p₀` tangent to `u` and through
`c (Fin.tail y)`: it reads the loops `φ_{V,u}` of the points of `c`, the first cube coordinate
being the loop parameter (`TauCeti.tangentCircleGenLoop_apply`). -/
def tangentCircleGenLoop (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀) :
    Ω^ (Fin (k + 1)) (sphere (0 : V) 1) (p₀ : sphere (0 : V) 1) where
  val :=
    { toFun y := tangentCircleLoop hu p₀ (c (Fin.tail y)) (y 0)
      continuous_toFun := by
        have h : Continuous fun q : sphereEquator u × I => tangentCircleLoop hu p₀ q.1 q.2 :=
          Path.continuous_uncurry_iff.2 (tangentCircleLoop hu p₀).continuous
        exact h.comp (f := fun y : I^(Fin (k + 1)) => (c (Fin.tail y), y 0)) (by fun_prop) }
  property y hy := by
    dsimp only [ContinuousMap.coe_mk]
    rcases Cube.boundary_fin_succ_iff.1 hy with h | h
    · rcases h with h | h <;> simp [h]
    · rw [GenLoop.boundary c _ h, tangentCircleLoop_self, Path.refl_apply]

/-- The generalized loop of circles through the points of a generalized loop `c` of the equator
reads the loops `φ_{V,u}` of the points of `c`, the first cube coordinate being the loop
parameter. -/
theorem tangentCircleGenLoop_apply (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (y : I^(Fin (k + 1))) :
    tangentCircleGenLoop hu c y = tangentCircleLoop hu p₀ (c (Fin.tail y)) (y 0) :=
  (rfl)

@[simp]
theorem coe_tangentCircleGenLoop_apply (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (y : I^(Fin (k + 1))) :
    (tangentCircleGenLoop hu c y : V) = tangentCircle ((p₀ : sphere (0 : V) 1) : V) u
      ((c (Fin.tail y) : sphere (0 : V) 1) : V) (2 * π * y 0) :=
  (rfl)

/-- A generalized loop of the equator that covers the equator off `p₀` and identifies only points
of the boundary sends only points of the boundary to `p₀`. -/
private lemma mem_boundary_of_eq (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k))
    {y : I^(Fin k)} (hy : c y = p₀) : y ∈ Cube.boundary (Fin k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- The cube is a point; it must reach the antipode of `p₀`, which differs from `p₀`.
    let q : sphereEquator u := ⟨-(p₀ : sphere (0 : V) 1), by
      simp [coe_neg_sphere, inner_neg_left, mem_sphereEquator.1 p₀.2]⟩
    have hq : q ≠ p₀ := fun h ↦ ne_neg_of_mem_unit_sphere ℝ (p₀ : sphere (0 : V) 1)
      (congrArg Subtype.val h).symm
    obtain ⟨z, hz⟩ := hsurj q hq
    rw [Subsingleton.elim z y, hy] at hz
    exact absurd hz.symm hq
  · have h0 : (0 : I^(Fin k)) ∈ Cube.boundary (Fin k) := ⟨⟨0, hk⟩, Or.inl rfl⟩
    rcases hinj y 0 (hy.trans (GenLoop.boundary c 0 h0).symm) with rfl | ⟨h, -⟩
    exacts [h0, h]

/-- The generalized loop of circles sends only points of the boundary to `p₀`. -/
private lemma mem_boundary_of_tangentCircleGenLoop_eq (hu : ‖u‖ = 1)
    (c : Ω^ (Fin k) (sphereEquator u) p₀) (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k))
    {y : I^(Fin (k + 1))} (hy : tangentCircleGenLoop hu c y = p₀) :
    y ∈ Cube.boundary (Fin (k + 1)) := by
  have hy' := congrArg Subtype.val hy
  rw [coe_tangentCircleGenLoop_apply, tangentCircle_eq_self_iff hu (mem_sphereEquator.1 p₀.2)
    (mem_sphereEquator.1 (c (Fin.tail y)).2)] at hy'
  rcases hy' with h | h
  · exact Cube.boundary_fin_succ_iff.2 (Or.inr (mem_boundary_of_eq c hsurj hinj
      (Subtype.ext (Subtype.ext h))))
  · exact Cube.boundary_fin_succ_iff.2 (Or.inl (eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one h))

/-- **The circles identify only points of the boundary**, when `c` covers the equator off `p₀` and
identifies only points of the boundary. -/
theorem eq_or_of_tangentCircleGenLoop_eq (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k))
    {y z : I^(Fin (k + 1))} (h : tangentCircleGenLoop hu c y = tangentCircleGenLoop hu c z) :
    y = z ∨ y ∈ Cube.boundary (Fin (k + 1)) ∧ z ∈ Cube.boundary (Fin (k + 1)) := by
  by_cases hy : tangentCircleGenLoop hu c y = p₀
  · exact Or.inr ⟨mem_boundary_of_tangentCircleGenLoop_eq hu c hsurj hinj hy,
      mem_boundary_of_tangentCircleGenLoop_eq hu c hsurj hinj (h ▸ hy)⟩
  left
  have hp := mem_sphere_zero_iff_norm.1 (p₀ : sphere (0 : V) 1).2
  have hpu := mem_sphereEquator.1 p₀.2
  have hcu (y : I^(Fin k)) := mem_sphereEquator.1 (c y).2
  have hne : tangentCircle ((p₀ : sphere (0 : V) 1) : V) u
      ((c (Fin.tail y) : sphere (0 : V) 1) : V) (2 * π * y 0) ≠ p₀ :=
    fun h' ↦ hy (Subtype.ext h')
  obtain ⟨hq, hc, hs⟩ := eq_of_tangentCircle_eq hp hu hpu
    (mem_sphere_zero_iff_norm.1 (c (Fin.tail y)).1.2) (hcu _)
    (mem_sphere_zero_iff_norm.1 (c (Fin.tail z)).1.2) (hcu _)
    (congrArg Subtype.val h) hne
  have h1 : cos (2 * π * y 0) ≠ 1 := fun h1 ↦
    hne ((tangentCircle_eq_self_iff hu hpu (hcu _) _).2 (Or.inr h1))
  have h0 : y 0 = z 0 := by
    rcases eq_or_of_cos_sin_two_pi_mul_eq hc hs with h0 | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h0
    · simp [h0] at h1
    · simp [h0] at h1
  have htail : Fin.tail y = Fin.tail z := by
    rcases hinj _ _ (Subtype.ext (Subtype.ext hq)) with h' | ⟨h', -⟩
    · exact h'
    · exact absurd ((tangentCircle_eq_self_iff hu hpu (hcu _) _).2
        (Or.inl (by rw [GenLoop.boundary c _ h']))) hne
  rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail z, h0, htail]

/-- **The circles sweep the sphere**, when `c` covers the equator off `p₀`. -/
theorem surjective_tangentCircleGenLoop (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q) : Function.Surjective (tangentCircleGenLoop hu c) := by
  intro w
  have hp := mem_sphere_zero_iff_norm.1 (p₀ : sphere (0 : V) 1).2
  obtain ⟨q, hq, hqu, θ, hθ⟩ := exists_tangentCircle_eq hp hu (mem_sphereEquator.1 p₀.2)
    (mem_sphere_zero_iff_norm.1 w.2)
  by_cases hqp : q = p₀
  · refine ⟨0, Subtype.ext ?_⟩
    rw [← hθ, hqp, tangentCircle_self, coe_tangentCircleGenLoop_apply]
    simp
  obtain ⟨y, hy⟩ := hsurj ⟨⟨q, mem_sphere_zero_iff_norm.2 hq⟩, mem_sphereEquator.2 hqu⟩
    fun h ↦ hqp (congrArg (fun r : sphereEquator u ↦ ((r : sphere (0 : V) 1) : V)) h)
  obtain ⟨t, hc, hs⟩ := exists_cos_sin_two_pi_mul_eq (cos_sq_add_sin_sq θ)
  refine ⟨Fin.cons t y, Subtype.ext ?_⟩
  rw [coe_tangentCircleGenLoop_apply, Fin.tail_cons, Fin.cons_zero, hy, ← hθ]
  rw [tangentCircle_def, tangentCircle_def, hc, hs]


end TauCeti

namespace TauCeti

open CategoryTheory Limits

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V} {k : ℕ}
  {p₀ : sphereEquator u} {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **The circles represent a generator** (Barraud–Damian–Humilière–Oancea, Proposition 6.21, the
step for `φ_{V,u}`). If the generalized loop `c` of the equator covers the equator off `p₀` and
identifies only points of the boundary of its cube, then the Hurewicz class of the generalized
loop of circles through the points of `c` is an isomorphism `R ≅ H_{k+1}(S_V; R)`. -/
theorem isIso_hurewicz_tangentCircleGenLoop (hu : ‖u‖ = 1) (c : Ω^ (Fin k) (sphereEquator u) p₀)
    (hsurj : ∀ q, q ≠ p₀ → ∃ y, c y = q)
    (hinj : ∀ y z, c y = c z → y = z ∨ y ∈ Cube.boundary (Fin k) ∧ z ∈ Cube.boundary (Fin k)) :
    IsIso (GenLoop.hurewicz R (tangentCircleGenLoop hu c)) :=
  GenLoop.isIso_hurewicz_of_bijective_toSphere R
    ⟨(GenLoop.injective_toSphere_iff _).2 fun _ _ h ↦
        eq_or_of_tangentCircleGenLoop_eq hu c hsurj hinj h,
      (GenLoop.surjective_toSphere_iff _).2 (surjective_tangentCircleGenLoop hu c hsurj)⟩

end TauCeti
