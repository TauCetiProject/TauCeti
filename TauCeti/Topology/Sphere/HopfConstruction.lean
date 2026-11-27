/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Topology.Homotopy.HSpaces
public import TauCeti.Topology.Constructions.HopfConstruction
public import TauCeti.Topology.Sphere.Join
public import TauCeti.Topology.Sphere.UnreducedSuspension

/-!
# The Hopf construction on spheres

Let `E`, `F` and `G` be real normed spaces, with `E` and `F` nontrivial and finite dimensional,
and let `μ : Sᴱ × Sᶠ → Sᴳ` be a continuous map of their unit spheres. Its Hopf construction
`[x, y, t] ↦ [μ (x, y), t]` (`TauCeti.Join.hopfConstruction`) goes from the join `Sᴱ * Sᶠ`, which
is the unit sphere of `WithLp 2 (E × F)` (`TauCeti.sphereJoinHomeomorph`), to the unreduced
suspension `SSᴳ`, which maps onto the unit sphere of `WithLp 2 (G × ℝ)`
(`TauCeti.sphereUnreducedSuspensionMap`). The composite is the **Hopf map** of `μ`,

`H(μ) : S(E × F) → S(G × ℝ)` (`TauCeti.sphereHopfMap`).

For Euclidean spheres and `μ : Sⁿ × Sⁿ → Sⁿ` this is a map `S²ⁿ⁺¹ → Sⁿ⁺¹`.

In coordinates, a unit vector `(a, b)` has join coordinate `t = ‖b‖²`, so
`2 √(t (1 - t)) = 2 ‖a‖ ‖b‖`, and

`H(μ) (a, b) = (2 ‖a‖ ‖b‖ • μ (a / ‖a‖, b / ‖b‖), ‖a‖² - ‖b‖²)`

(`TauCeti.coe_sphereHopfMap`), the first component being `0` when `a` or `b` vanishes. When `μ` is
the restriction of a bilinear map `m`, this is `(2 • m a b, ‖a‖² - ‖b‖²)`
(`TauCeti.coe_sphereHopfMap_of_bilinear`). In particular, for the multiplication of a
finite-dimensional real normed division algebra, such as `ℂ` or `ℍ`, the Hopf map is
`(a, b) ↦ (2 a b, ‖a‖² - ‖b‖²)` (`TauCeti.coe_sphereHopfMap_mul`). Up to conjugating one
coordinate, these are the complex Hopf fibration `S³ → S²` and the quaternionic Hopf fibration
`S⁷ → S⁴`.

## Main declarations

* `TauCeti.sphereHopfMap`: the Hopf map `S(E × F) → S(G × ℝ)` of a map `Sᴱ × Sᶠ → Sᴳ`,
  characterized on the join by `TauCeti.sphereHopfMap_sphereJoinMap_mk`.
* `TauCeti.coe_sphereHopfMap`: its formula in coordinates.
* `TauCeti.coe_sphereHopfMap_of_bilinear`, `TauCeti.coe_sphereHopfMap_mul`: the Hopf maps of
  bilinear multiplications.

## References

* H. Hopf, *Über die Abbildungen von Sphären auf Sphären niedrigerer Dimension*, Fund. Math. 25
  (1935), 427–440.
* A. Hatcher, [*Vector Bundles and K-Theory*](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf),
  §2.3, the Hopf construction.
-/

public section

noncomputable section

namespace TauCeti

open Metric unitInterval WithLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [Nontrivial E] [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The **Hopf map** `S(E × F) → S(G × ℝ)` of a map `μ : Sᴱ × Sᶠ → Sᴳ` of unit spheres: its Hopf
construction `[x, y, t] ↦ [μ (x, y), t]`, read through the homeomorphism of the join `Sᴱ * Sᶠ`
with the unit sphere of `WithLp 2 (E × F)` and the map of the unreduced suspension `SSᴳ` onto the
unit sphere of `WithLp 2 (G × ℝ)`. -/
def sphereHopfMap (μ : C(sphere (0 : E) 1 × sphere (0 : F) 1, sphere (0 : G) 1)) :
    C(sphere (0 : WithLp 2 (E × F)) 1, sphere (0 : WithLp 2 (G × ℝ)) 1) :=
  sphereUnreducedSuspensionMap.comp
    ((Join.hopfConstruction μ).comp ((sphereJoinHomeomorph E F).symm : C(_, _)))

/-- The Hopf map sends the image `(√(1 - t) • x, √t • y)` of the point `[x, y, t]` of the join to
the image `(2 √(t (1 - t)) • μ (x, y), 1 - 2 t)` of the point `[μ (x, y), t]` of the
suspension. -/
@[simp]
theorem sphereHopfMap_sphereJoinMap_mk
    (μ : C(sphere (0 : E) 1 × sphere (0 : F) 1, sphere (0 : G) 1)) (x : sphere (0 : E) 1)
    (y : sphere (0 : F) 1) (t : I) :
    sphereHopfMap μ (sphereJoinMap (Join.mk _ _ (x, y, t))) =
      sphereUnreducedSuspensionMap (UnreducedSuspension.mk _ (μ (x, y), t)) := by
  have h : (sphereJoinHomeomorph E F).symm (sphereJoinMap (Join.mk _ _ (x, y, t))) =
      Join.mk _ _ (x, y, t) := by
    rw [← coe_sphereJoinHomeomorph, Homeomorph.symm_apply_apply]
  simp [sphereHopfMap, h]

/-- **The Hopf map in coordinates.** The Hopf map of `μ` sends a unit vector `(a, b)` of
`WithLp 2 (E × F)` to `(2 ‖a‖ ‖b‖ • μ (a / ‖a‖, b / ‖b‖), ‖a‖² - ‖b‖²)`, where the directions of
`a` and `b` are `TauCeti.sphereDirection` with any fallback unit vectors `e` and `e'`; these only
matter when `a` or `b` vanishes, where the first component is `0`. -/
theorem coe_sphereHopfMap (μ : C(sphere (0 : E) 1 × sphere (0 : F) 1, sphere (0 : G) 1))
    (e : sphere (0 : E) 1) (e' : sphere (0 : F) 1) (p : sphere (0 : WithLp 2 (E × F)) 1) :
    (sphereHopfMap μ p : WithLp 2 (G × ℝ)) =
      toLp 2 ((2 * ‖(p : WithLp 2 (E × F)).fst‖ * ‖(p : WithLp 2 (E × F)).snd‖) •
          (μ (sphereDirection e (p : WithLp 2 (E × F)).fst,
            sphereDirection e' (p : WithLp 2 (E × F)).snd) : G),
        ‖(p : WithLp 2 (E × F)).fst‖ ^ 2 - ‖(p : WithLp 2 (E × F)).snd‖ ^ 2) := by
  have hn := sq_norm_fst_add_sq_norm_snd_eq_one p
  -- The join coordinate of `(a, b)` is `t = ‖b‖²`, and then `1 - t = ‖a‖²`.
  conv_lhs => rw [← sphereJoinMap_mk_sphereDirection e e' p]
  rw [sphereHopfMap_sphereJoinMap_mk, coe_sphereUnreducedSuspensionMap_mk]
  have h2 : 2 * √(‖(p : WithLp 2 (E × F)).snd‖ ^ 2 * (1 - ‖(p : WithLp 2 (E × F)).snd‖ ^ 2)) =
      2 * ‖(p : WithLp 2 (E × F)).fst‖ * ‖(p : WithLp 2 (E × F)).snd‖ := by
    rw [show 1 - ‖(p : WithLp 2 (E × F)).snd‖ ^ 2 = ‖(p : WithLp 2 (E × F)).fst‖ ^ 2 by linarith,
      ← mul_pow, Real.sqrt_sq (by positivity)]
    ring
  simp only [h2]
  congr 2
  linarith

/-- **The Hopf map of a bilinear multiplication.** If `μ` is the restriction to the unit spheres
of a bilinear map `m : E → F → G`, its Hopf map sends a unit vector `(a, b)` to
`(2 • m a b, ‖a‖² - ‖b‖²)`. -/
theorem coe_sphereHopfMap_of_bilinear
    (μ : C(sphere (0 : E) 1 × sphere (0 : F) 1, sphere (0 : G) 1)) (m : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (hμ : ∀ x y, (μ (x, y) : G) = m x y) (p : sphere (0 : WithLp 2 (E × F)) 1) :
    (sphereHopfMap μ p : WithLp 2 (G × ℝ)) =
      toLp 2 ((2 : ℝ) • m (p : WithLp 2 (E × F)).fst (p : WithLp 2 (E × F)).snd,
        ‖(p : WithLp 2 (E × F)).fst‖ ^ 2 - ‖(p : WithLp 2 (E × F)).snd‖ ^ 2) := by
  obtain ⟨e⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one |>.coe_sort
  obtain ⟨e'⟩ := (NormedSpace.sphere_nonempty (x := (0 : F)) (r := 1)).2 zero_le_one |>.coe_sort
  rw [coe_sphereHopfMap μ e e' p, hμ]
  congr 2
  -- Pull the norms of `a` and `b` into the two arguments of `m`.
  conv_rhs => rw [← norm_smul_sphereDirection e (p : WithLp 2 (E × F)).fst,
    ← norm_smul_sphereDirection e' (p : WithLp 2 (E × F)).snd]
  rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_smul, smul_smul]

/-- **The Hopf map of an algebra multiplication.** For a finite-dimensional real normed division
algebra `𝕜`, such as `ℂ` or `ℍ`, the Hopf map of the multiplication of its unit sphere, the
H-space structure of this topological group, sends a unit vector `(a, b)` of `WithLp 2 (𝕜 × 𝕜)`
to `(2 a b, ‖a‖² - ‖b‖²)`. For `ℂ` and `ℍ`, up to conjugating one coordinate, these are the Hopf
fibrations `S³ → S²` and `S⁷ → S⁴`. -/
theorem coe_sphereHopfMap_mul {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜]
    [FiniteDimensional ℝ 𝕜] (p : sphere (0 : WithLp 2 (𝕜 × 𝕜)) 1) :
    (sphereHopfMap (HSpace.hmul : C(sphere (0 : 𝕜) 1 × sphere (0 : 𝕜) 1, sphere (0 : 𝕜) 1)) p :
        WithLp 2 (𝕜 × ℝ)) =
      toLp 2 ((2 : ℝ) • ((p : WithLp 2 (𝕜 × 𝕜)).fst * (p : WithLp 2 (𝕜 × 𝕜)).snd),
        ‖(p : WithLp 2 (𝕜 × 𝕜)).fst‖ ^ 2 - ‖(p : WithLp 2 (𝕜 × 𝕜)).snd‖ ^ 2) :=
  -- The H-space multiplication of a topological group is its multiplication by definition
  -- (`IsTopologicalGroup.toHSpace`), and Mathlib states no lemma for it.
  coe_sphereHopfMap_of_bilinear _ (LinearMap.mul ℝ 𝕜) (fun _ _ => rfl) p

end TauCeti
