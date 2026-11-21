/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Dynamics.Billiard.GeneratingFunction
public import TauCeti.Dynamics.Billiard.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Smoothness of the billiard map

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)` (`TauCeti.StrictConvexBilliardTable.nextCollision`).
If `χ` is `C^(n+1)` for some `n ≠ 0`, then `B` is `C^n` on the strip
(`TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`), and so is its inverse: `B` is a
`C^n` diffeomorphism of the strip onto itself
(`TauCeti.StrictConvexBilliardTable.nextCollisionPartialDiffeomorph`). One derivative is lost
because the tangential components are inner products with the derivative `χ'`. The billiard map
`β` induced by `B` on the space of collision states `AddCircle L × (-1, 1)` is therefore a
homeomorphism as soon as `χ` is `C²` (`TauCeti.StrictConvexBilliardTable.billiardHomeomorph`).

The proof is the implicit function theorem for the generating function
`S(s, t) = -‖χ(t) - χ(s)‖` (`TauCeti.StrictConvexBilliardTable.generatingFunction`). On the domain
`s < t < s + L` of chords between distinct boundary points, the map

`Φ(s, t) = (s, ∂_s S(s, t)) = (s, ⟪χ'(s), u⟫)`,

where `u` is the unit vector along the chord, is `C^n`
(`TauCeti.StrictConvexBilliardTable.contDiffAt_inner_deriv_chordDir`), and it is inverted by
`(s, v) ↦ (s, t(s, v))`, where `t(s, v)` is the next collision parameter: the generating function
generates the next-collision map. The derivative of `Φ` is triangular, with diagonal entries `1`
and the mixed partial derivative `∂_t ∂_s S`, which is negative by the twist condition
(`TauCeti.StrictConvexBilliardTable.deriv_deriv_generatingFunction_left_neg`). So the inverse
function theorem applies at every point, and the local `C^n` inverses agree with
`(s, v) ↦ (s, t(s, v))` because chords of the window are determined by their tangential
components. The next tangential component `w = ⟪u, χ'(t)⟫` is then `C^n` too.

The inverse of `B` is `τ⁻¹ ∘ ι ∘ B ∘ ι`, where `ι(s, v) = (s, -v)` and `τ(s, v) = (s + L, v)`
(`TauCeti.StrictConvexBilliardTable.nextCollisionEquiv_symm_apply`), so it is `C^n` as well.
Since `B` and its inverse commute with `τ`, their continuity passes to the quotient by the open
quotient map `ℝ × (-1, 1) → AddCircle L × (-1, 1)`.

Whether `β` is still a homeomorphism when `χ` is only `C¹` is not treated here.

## Main results

* `TauCeti.StrictConvexBilliardTable.contDiffAt_chordDir`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_inner_deriv_chordDir`: smoothness of the chord
  direction and of `∂_s S`, jointly in both endpoints.
* `TauCeti.StrictConvexBilliardTable.contDiffAt_nextParam`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_nextTangential`,
  `TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`: the next-collision map is `C^n`
  on the strip when `χ` is `C^(n+1)`.
* `TauCeti.StrictConvexBilliardTable.nextCollisionPartialDiffeomorph`: the next-collision map as a
  `C^n` diffeomorphism of the strip, with inverse `τ⁻¹ ∘ ι ∘ B ∘ ι`.
* `TauCeti.StrictConvexBilliardTable.continuous_nextCollisionEquiv`,
  `TauCeti.StrictConvexBilliardTable.continuous_nextCollisionEquiv_symm`: continuity of the
  next-collision bijection of `ℝ × (-1, 1)` and of its inverse.
* `TauCeti.StrictConvexBilliardTable.billiardHomeomorph`: the billiard map as a homeomorphism of
  `AddCircle L × (-1, 1)`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Module
open scoped RealInnerProductSpace ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o) {n : WithTop ℕ∞}

/-! ### Smoothness of the chord data -/

/-- The chord direction `u = (χ(t) - χ(s)) / ‖χ(t) - χ(s)‖` is as smooth as `χ` is at both
endpoints, jointly in the endpoints, at every chord between distinct boundary points. -/
theorem contDiffAt_chordDir {s t : ℝ} (hs : ContDiffAt ℝ n χ s) (ht : ContDiffAt ℝ n χ t)
    (h : χ t ≠ χ s) : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ χ.chordDir p.1 p.2) (s, t) := by
  have hd : ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ χ p.2 - χ p.1) (s, t) :=
    (ht.comp (s, t) contDiffAt_snd).sub (hs.comp (s, t) contDiffAt_fst)
  have h0 : χ t - χ s ≠ 0 := sub_ne_zero.2 h
  simp only [chordDir_def, NormedSpace.normalize]
  exact (((contDiffAt_norm ℝ h0).comp (s, t) hd).inv (norm_ne_zero_iff.2 h0)).smul hd

/-- The derivative `∂_s S(s, t) = ⟪χ'(s), u⟫` of the generating function in its first argument is
`C^n`, jointly in both endpoints, at every chord between distinct boundary points, when `χ` is
`C^(n+1)`. -/
theorem contDiffAt_inner_deriv_chordDir (hχ : ContDiff ℝ (n + 1) χ) {s t : ℝ} (h : χ t ≠ χ s) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫) (s, t) :=
  ((contDiff_succ_iff_deriv.1 hχ).2.2.comp contDiff_fst).contDiffAt.inner ℝ
    (χ.contDiffAt_chordDir (hχ.of_le le_self_add).contDiffAt (hχ.of_le le_self_add).contDiffAt h)

/-! ### Smoothness of the next-collision map -/

/-- The derivative of `Φ(s, t) = (s, ∂_s S(s, t))` at a chord between distinct boundary points is
invertible, when `χ` is `C^(n+1)` with `n ≠ 0`: it is triangular, with diagonal entries `1` and the
mixed partial derivative `∂_t ∂_s S`, which is negative by the twist condition. -/
private theorem exists_hasFDerivAt_inner_deriv_chordDir (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ)
    {s t : ℝ} (hst : χ t ≠ χ s) :
    ∃ f' : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ,
      HasFDerivAt (fun p : ℝ × ℝ ↦ (p.1, ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫))
        (f' : ℝ × ℝ →L[ℝ] ℝ × ℝ) (s, t) := by
  set G : ℝ × ℝ → ℝ := fun p ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫
  have hG1 : HasFDerivAt G (fderiv ℝ G (s, t)) (s, t) :=
    ((χ.contDiffAt_inner_deriv_chordDir hχ hst).differentiableAt hn).hasFDerivAt
  set G' := fderiv ℝ G (s, t)
  set α := G' (1, 0)
  set c := G' (0, 1)
  -- The derivative of `G` along `t` is the mixed partial derivative `∂_t ∂_s S < 0`.
  have hc : c ≠ 0 := by
    have h1 : HasDerivAt (fun t' ↦ G (s, t')) c t :=
      (hG1.comp t (hasFDerivAt_prodMk_right s t)).hasDerivAt
    have heq : (fun t' ↦ deriv (fun s' ↦ χ.generatingFunction s' t') s) =ᶠ[𝓝 t]
        fun t' ↦ G (s, t') := by
      filter_upwards [χ.continuous.continuousAt.eventually_ne hst] with t' ht'
      exact (χ.hasDerivAt_generatingFunction_left ht').deriv
    have h2 := χ.deriv_deriv_generatingFunction_left_neg hst
    rw [heq.deriv_eq, h1.deriv] at h2
    exact h2.ne
  have hG' : ∀ p : ℝ × ℝ, G' p = α * p.1 + c * p.2 := by
    intro p
    have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hp]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  -- The derivative is the map `(a, b) ↦ (a, α a + c b)`, inverted by `(a, z) ↦ (a, (z - α a) / c)`.
  refine ⟨ContinuousLinearEquiv.ofContinuousLinearMap ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod G')
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (c⁻¹ • (ContinuousLinearMap.snd ℝ ℝ ℝ - α • ContinuousLinearMap.fst ℝ ℝ ℝ)))
    (ContinuousLinearMap.ext fun p ↦ ?_) (ContinuousLinearMap.ext fun p ↦ ?_),
    hasFDerivAt_fst.prodMk hG1⟩
  · ext
    · simp
    · simp [hG']
      field_simp
      ring
  · ext
    · simp
    · simp [hG']
      field_simp

/-- **Smoothness of the next collision parameter.** If `χ` is `C^(n+1)` with `n ≠ 0`, the next
collision parameter `t(s, v)` is `C^n`, jointly in `s` and `v`, on the strip `ℝ × (-1, 1)`. It is
the second component of the local inverse of `(s, t) ↦ (s, ∂_s S(s, t))`, given by the inverse
function theorem and the twist condition. -/
theorem contDiffAt_nextParam (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) {s v : ℝ}
    (hv : v ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ χ.nextParam x.1 x.2) (s, v) := by
  set t := χ.nextParam s v
  have hst : χ t ≠ χ s := χ.apply_nextParam_ne hv
  set G : ℝ × ℝ → ℝ := fun p ↦ ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, G p)
  obtain ⟨f', hΦ'⟩ := χ.exists_hasFDerivAt_inner_deriv_chordDir hn hχ hst
  have hΦ : ContDiffAt ℝ n Φ (s, t) :=
    contDiffAt_fst.prodMk (χ.contDiffAt_inner_deriv_chordDir hχ hst)
  have hΦst : Φ (s, t) = (s, v) := by
    simp only [Φ, G, t, χ.inner_deriv_chordDir_nextParam hv]
  have hS := hΦ.hasStrictFDerivAt hΦ' hn
  -- The `C^n` local inverse `g` of `Φ` at `(s, t)`; by definition, it is the local inverse
  -- `hS.localInverse` given by the strict derivative, whose API supplies the facts below.
  set g := hΦ.localInverse hΦ' hn
  have hinv : ContDiffAt ℝ n g (Φ (s, t)) := hΦ.to_localInverse hΦ' hn
  have hR : ∀ᶠ y in 𝓝 (Φ (s, t)), Φ (g y) = y := hS.eventually_right_inverse
  -- The local inverse stays in the window of chords between distinct boundary points.
  have hD : ∀ᶠ y in 𝓝 (Φ (s, t)), g y ∈ {p : ℝ × ℝ | p.2 ∈ Ioo p.1 (p.1 + χ.period)} := by
    refine hS.localInverse_continuousAt.preimage_mem_nhds ?_
    rw [hS.localInverse_apply_image]
    exact ((isOpen_lt continuous_fst continuous_snd).inter
      (isOpen_lt continuous_snd (continuous_fst.add continuous_const))).mem_nhds
      (χ.nextParam_mem_Ioo hv)
  rw [hΦst] at hinv hR hD
  -- There it agrees with `(s, v) ↦ (s, t(s, v))`, since the generating function generates `B`.
  refine (contDiffAt_snd.comp _ hinv).congr_of_eventuallyEq ?_
  filter_upwards [hR, hD] with ⟨y₁, y₂⟩ hy hyD
  rw [comp_apply]
  generalize g (y₁, y₂) = q at hy hyD ⊢
  obtain ⟨a, b⟩ := q
  simp only [Φ, G, Prod.mk.injEq] at hy
  obtain ⟨rfl, rfl⟩ := hy
  exact χ.nextParam_inner_deriv_chordDir hyD

/-- **Smoothness of the next tangential component.** If `χ` is `C^(n+1)` with `n ≠ 0`, the next
tangential component `w(s, v)` is `C^n`, jointly in `s` and `v`, on the strip `ℝ × (-1, 1)`. -/
theorem contDiffAt_nextTangential (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) {s v : ℝ}
    (hv : v ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ χ.nextTangential x.1 x.2) (s, v) := by
  have hd : ContDiff ℝ n (deriv χ) := (contDiff_succ_iff_deriv.1 hχ).2.2
  have hds : ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ deriv χ x.1) (s, v) :=
    (hd.comp contDiff_fst).contDiffAt
  have hsq : ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ √(1 - x.2 ^ 2)) (s, v) :=
    (contDiffAt_const.sub (contDiffAt_snd.pow 2)).sqrt (by nlinarith [hv.1, hv.2])
  have hout : ContDiffAt ℝ n (fun x : ℝ × ℝ ↦ χ.outgoingDir x.1 x.2) (s, v) := by
    simp only [outgoingDir_def]
    exact (contDiffAt_snd.smul hds).add
      (hsq.smul (o.rightAngleRotation.contDiff.contDiffAt.comp (s, v) hds))
  simp only [nextTangential_def]
  exact hout.inner ℝ (hd.contDiffAt.comp (s, v) (χ.contDiffAt_nextParam hn hχ hv))

/-- **Smoothness of the billiard map.** If `χ` is `C^(n+1)` with `n ≠ 0`, the next-collision map
`(s, v) ↦ (t, w)` is `C^n` on the strip `ℝ × (-1, 1)`. -/
theorem contDiffOn_nextCollision (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) :
    ContDiffOn ℝ n χ.nextCollision (univ ×ˢ Ioo (-1) 1) := by
  rintro ⟨s, v⟩ ⟨-, hv⟩
  rw [show χ.nextCollision = fun x ↦ (χ.nextParam x.1 x.2, χ.nextTangential x.1 x.2) from
    funext χ.nextCollision_apply]
  exact ((χ.contDiffAt_nextParam hn hχ hv).prodMk
    (χ.contDiffAt_nextTangential hn hχ hv)).contDiffWithinAt

/-- The inverse `(t, w) ↦ (s - L, -v)` of the next-collision map, where `(s, v)` is the next
collision of `(t, -w)`, is `C^n` on the strip when `χ` is `C^(n+1)` with `n ≠ 0`. -/
private theorem contDiffOn_nextCollision_inv (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) :
    ContDiffOn ℝ n (fun x : ℝ × ℝ ↦ (χ.nextParam x.1 (-x.2) - χ.period,
      -χ.nextTangential x.1 (-x.2))) (univ ×ˢ Ioo (-1) 1) := by
  have hι : ContDiff ℝ n (fun x : ℝ × ℝ ↦ (x.1, -x.2)) := contDiff_fst.prodMk contDiff_snd.neg
  have h := (χ.contDiffOn_nextCollision hn hχ).comp hι.contDiffOn
    fun (x : ℝ × ℝ) (hx : x ∈ univ ×ˢ Ioo (-1 : ℝ) 1) ↦
      ⟨mem_univ _, show -x.2 ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hx.2.2], by linarith [hx.2.1]⟩⟩
  simpa [comp_def] using
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd.neg).comp_contDiffOn h

/-! ### The next-collision map as a diffeomorphism of the strip -/

/-- **The billiard map is a diffeomorphism of the strip.** If `χ` is `C^(n+1)` with `n ≠ 0`, the
next-collision map `B` is a `C^n` diffeomorphism of the strip `ℝ × (-1, 1)` onto itself. Its
inverse `τ⁻¹ ∘ ι ∘ B ∘ ι` sends `(t, w)` to `(s - L, -v)`, where `(s, v)` is the next collision of
`(t, -w)`. -/
def nextCollisionPartialDiffeomorph (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) n where
  toFun := χ.nextCollision
  invFun x := (χ.nextParam x.1 (-x.2) - χ.period, -χ.nextTangential x.1 (-x.2))
  source := univ ×ˢ Ioo (-1) 1
  target := univ ×ˢ Ioo (-1) 1
  map_source' x hx := ⟨mem_univ _, by rw [nextCollision_apply]; exact χ.nextTangential_mem_Ioo hx.2⟩
  map_target' x hx := ⟨mem_univ _, χ.neg_nextTangential_neg_mem_Ioo x.1 ⟨x.2, hx.2⟩⟩
  left_inv' x hx := by
    simpa [Prod.ext_iff, Subtype.ext_iff] using
      χ.nextCollisionEquiv.symm_apply_apply (x.1, ⟨x.2, hx.2⟩)
  right_inv' x hx := by
    simpa [Prod.ext_iff, Subtype.ext_iff] using
      χ.nextCollisionEquiv.apply_symm_apply (x.1, ⟨x.2, hx.2⟩)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := isOpen_univ.prod isOpen_Ioo
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 (χ.contDiffOn_nextCollision hn hχ)
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 (χ.contDiffOn_nextCollision_inv hn hχ)

/-- The partial diffeomorphism `nextCollisionPartialDiffeomorph` acts as the next-collision map. -/
@[simp]
theorem coe_nextCollisionPartialDiffeomorph (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) :
    ⇑(χ.nextCollisionPartialDiffeomorph hn hχ) = χ.nextCollision :=
  (rfl)

/-- The inverse of the next-collision map on the strip is `τ⁻¹ ∘ ι ∘ B ∘ ι`. -/
@[simp]
theorem nextCollisionPartialDiffeomorph_symm_apply (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ)
    (x : ℝ × ℝ) :
    (χ.nextCollisionPartialDiffeomorph hn hχ).toPartialEquiv.symm x =
      (χ.nextParam x.1 (-x.2) - χ.period, -χ.nextTangential x.1 (-x.2)) :=
  (rfl)

/-- The source of the next-collision diffeomorphism is the strip `ℝ × (-1, 1)`. -/
@[simp]
theorem nextCollisionPartialDiffeomorph_source (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) :
    (χ.nextCollisionPartialDiffeomorph hn hχ).source = univ ×ˢ Ioo (-1) 1 :=
  (rfl)

/-- The target of the next-collision diffeomorphism is the strip `ℝ × (-1, 1)`. -/
@[simp]
theorem nextCollisionPartialDiffeomorph_target (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ) :
    (χ.nextCollisionPartialDiffeomorph hn hχ).target = univ ×ˢ Ioo (-1) 1 :=
  (rfl)

/-! ### The billiard map as a homeomorphism -/

/-- A map of `ℝ × ℝ` that is continuous on the strip `ℝ × (-1, 1)` and maps it into itself
restricts to a continuous map of `ℝ × (-1, 1)`. -/
private theorem continuous_restrict_strip {f : ℝ × ℝ → ℝ × ℝ}
    (hf : ContinuousOn f (univ ×ˢ Ioo (-1) 1))
    (hmaps : ∀ x : ℝ × Ioo (-1 : ℝ) 1, (f (x.1, x.2)).2 ∈ Ioo (-1 : ℝ) 1) :
    Continuous fun x : ℝ × Ioo (-1 : ℝ) 1 ↦
      ((f (x.1, x.2)).1, (⟨(f (x.1, x.2)).2, hmaps x⟩ : Ioo (-1 : ℝ) 1)) := by
  have h := hf.comp_continuous (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))
    fun x ↦ ⟨mem_univ _, x.2.property⟩
  exact (continuous_fst.comp h).prodMk ((continuous_snd.comp h).subtype_mk hmaps)

/-- The next-collision bijection of `ℝ × (-1, 1)` is continuous when `χ` is `C²`. -/
theorem continuous_nextCollisionEquiv (hχ : ContDiff ℝ 2 χ) : Continuous χ.nextCollisionEquiv :=
  (continuous_restrict_strip (χ.contDiffOn_nextCollision one_ne_zero hχ).continuousOn
    fun x ↦ by simpa using χ.nextTangential_mem_Ioo x.2.property).congr fun x ↦ by simp

/-- The inverse of the next-collision bijection of `ℝ × (-1, 1)` is continuous when `χ` is
`C²`. -/
theorem continuous_nextCollisionEquiv_symm (hχ : ContDiff ℝ 2 χ) :
    Continuous χ.nextCollisionEquiv.symm :=
  (continuous_restrict_strip (χ.contDiffOn_nextCollision_inv one_ne_zero hχ).continuousOn
    fun x ↦ χ.neg_nextTangential_neg_mem_Ioo x.1 x.2).congr fun x ↦ by simp

/-- The projection `ℝ × (-1, 1) → AddCircle L × (-1, 1)` onto the space of collision states is an
open quotient map. -/
private theorem isOpenQuotientMap_prodMap_coe :
    IsOpenQuotientMap (Prod.map ((↑) : ℝ → AddCircle χ.period) (id : Ioo (-1 : ℝ) 1 → _)) :=
  QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id

/-- A map of `AddCircle L × (-1, 1)` is continuous when it lifts along the projection from
`ℝ × (-1, 1)` to a continuous map. -/
private theorem continuous_of_lift
    {g : AddCircle χ.period × Ioo (-1 : ℝ) 1 → AddCircle χ.period × Ioo (-1 : ℝ) 1}
    {F : ℝ × Ioo (-1 : ℝ) 1 → ℝ × Ioo (-1 : ℝ) 1} (hF : Continuous F)
    (h : ∀ (s : ℝ) v, g (s, v) = (((F (s, v)).1 : AddCircle χ.period), (F (s, v)).2)) :
    Continuous g := by
  rw [← χ.isOpenQuotientMap_prodMap_coe.continuous_comp_iff]
  convert χ.isOpenQuotientMap_prodMap_coe.continuous.comp hF using 1
  funext ⟨s, v⟩
  exact h s v

/-- **The billiard map is a homeomorphism.** If `χ` is `C²`, the billiard map `β` of the table is
a homeomorphism of the space of collision states `AddCircle L × (-1, 1)`. -/
def billiardHomeomorph (hχ : ContDiff ℝ 2 χ) :
    AddCircle χ.period × Ioo (-1 : ℝ) 1 ≃ₜ AddCircle χ.period × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.billiardMap
  continuous_toFun := χ.continuous_of_lift (χ.continuous_nextCollisionEquiv hχ) fun s v ↦ by simp
  continuous_invFun := χ.continuous_of_lift (χ.continuous_nextCollisionEquiv_symm hχ)
    fun s v ↦ by simp [AddCircle.coe_period]

/-- The underlying bijection of the billiard homeomorphism is the billiard map. -/
@[simp]
theorem billiardHomeomorph_toEquiv (hχ : ContDiff ℝ 2 χ) :
    (χ.billiardHomeomorph hχ).toEquiv = χ.billiardMap :=
  (rfl)

/-- The billiard homeomorphism acts as the billiard map. -/
@[simp]
theorem coe_billiardHomeomorph (hχ : ContDiff ℝ 2 χ) :
    ⇑(χ.billiardHomeomorph hχ) = χ.billiardMap :=
  (rfl)

/-- The inverse of the billiard homeomorphism acts as the inverse of the billiard map. -/
@[simp]
theorem coe_billiardHomeomorph_symm (hχ : ContDiff ℝ 2 χ) :
    ⇑(χ.billiardHomeomorph hχ).symm = χ.billiardMap.symm :=
  (rfl)

end StrictConvexBilliardTable

end TauCeti
