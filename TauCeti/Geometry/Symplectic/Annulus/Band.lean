/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Annulus.GeneratingFunction
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# Generating functions of twist maps on their bands

Let `F = (X, Y)` be a map of the plane `ℝ × ℝ`, for instance a lift of an area-preserving
diffeomorphism of the annulus `(ℝ / ℤ) × [0, 1]`, defined and `C²` on a strip `ℝ × I` around the
closed strip `ℝ × [0, 1]`, where `I` is an open interval. Suppose `F` *twists* on `ℝ × I`: the
derivative `∂_y X` vanishes nowhere there. This file turns the local generating function of
`TauCeti.Geometry.Symplectic.Annulus.GeneratingFunction` into a global one, defined on the whole
band swept out by `F` in the mixed coordinates `(x, X)`.

* **The mixed coordinates are a diffeomorphism onto the band.** On each vertical line `X` is
  strictly monotone in `y`, so `(x, y) ↦ (x, X(x, y))` (`TauCeti.stripTwistCoord`) is injective on
  `ℝ × I` (`TauCeti.injOn_stripTwistCoord`). Its image is open
  (`TauCeti.isOpen_image_stripTwistCoord`), and its inverse is `C^n` when `F` is
  (`TauCeti.contDiffOn_invFunOn_stripTwistCoord`). The closed strip `ℝ × [[a, b]]` is mapped onto
  the closed band `{(x, X) | X ∈ [[X(x, a), X(x, b)]]}` between the images of its two boundary
  lines (`TauCeti.image_stripTwistCoord_univ_prod_uIcc`).
* **The band generating function.** Transporting the generating function
  `S(x, y) = ∫₀ʸ Y(x, t) ∂_y X(x, t) dt` of `F` along the inverse of the mixed coordinates gives a
  function `S(x, X)` on the band (`TauCeti.bandGeneratingFunction`). When `F` maps the lower
  boundary line into itself and preserves the area form `dx ∧ dy`, it satisfies the generating
  equations `∂₁ S(x, X) = -y`, `∂₂ S(x, X) = Y` at `X = X(x, y)`, so that `dS = Y dX - y dx`
  (`TauCeti.hasFDerivAt_bandGeneratingFunction`). It is `C^n` on the band when `F` is `C^(n + 1)`
  (`TauCeti.contDiffOn_bandGeneratingFunction`), it vanishes on the lower boundary graph
  `X = X(x, 0)` (`TauCeti.bandGeneratingFunction_stripTwistCoord_mk_zero`), which fixes its
  additive constant, and it is invariant under the diagonal translation
  `(x, X) ↦ (x + 1, X + 1)` when `F` commutes with the deck translation `(x, y) ↦ (x + 1, y)`
  (`TauCeti.bandGeneratingFunction_add_diag`).

For the affine shear `(x, y) ↦ (x + a + c y, y)`, `c ≠ 0`, the band generating function is
`(X - x - a)² / (2c)` on the whole plane (`TauCeti.bandGeneratingFunction_affineShear`).

In the generating-function proof of the Poincaré–Birkhoff theorem, an area-preserving
diffeomorphism of the annulus is factored into twist maps, each of which has such a global
generating function `S_k`; the sum `Σ S_k(x_k, x_(k+1))` over cyclic configurations is the
discrete action whose critical points are the fixed points of the composite.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 4 (generating functions).
-/

public section

noncomputable section

open Filter Function Set
open scoped ContDiff Topology Interval

namespace TauCeti

variable {F : ℝ × ℝ → ℝ × ℝ} {I : Set ℝ}

/-! ### The mixed coordinates on a twisting strip -/

/-- Where `F` is `C^n`, `n ≠ 0`, and twists, the mixed coordinates have an invertible strict
derivative. -/
private theorem exists_hasStrictFDerivAt_stripTwistCoord_of_contDiffAt {n : WithTop ℕ∞}
    {p : ℝ × ℝ} (hF : ContDiffAt ℝ n F p) (hn : n ≠ 0) (htwist : (fderiv ℝ F p (0, 1)).1 ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ,
      HasStrictFDerivAt (stripTwistCoord F) (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p :=
  (exists_hasStrictFDerivAt_stripTwistCoord
    (hF.hasStrictFDerivAt (hF.differentiableAt hn).hasFDerivAt hn) htwist).imp fun _ ↦ And.right

/-- **The mixed coordinates are injective on a twisting strip.** If `I` is an interval and `F` is
differentiable with nonzero twist `∂_y X` on the strip `ℝ × I`, then `(x, y) ↦ (x, X(x, y))` is
injective there. -/
theorem injOn_stripTwistCoord (hI : I.OrdConnected)
    (hF : ∀ p ∈ univ ×ˢ I, DifferentiableAt ℝ F p)
    (htwist : ∀ p ∈ univ ×ˢ I, (fderiv ℝ F p (0, 1)).1 ≠ 0) :
    InjOn (stripTwistCoord F) (univ ×ˢ I) := by
  -- By Rolle's theorem, equal values of `X` at two heights on a vertical line force a zero twist
  -- between them.
  have key (x : ℝ) {y₁ y₂ : ℝ} (h₁ : y₁ ∈ I) (h₂ : y₂ ∈ I) (hlt : y₁ < y₂) :
      (F (x, y₁)).1 ≠ (F (x, y₂)).1 := by
    intro heq
    have hIcc : Icc y₁ y₂ ⊆ I := hI.out h₁ h₂
    -- On the segment, the derivative of `X` in `y` is the twist.
    have hd (t : ℝ) (ht : t ∈ Icc y₁ y₂) :
        HasDerivAt (fun s ↦ (F (x, s)).1) (fderiv ℝ F (x, t) (0, 1)).1 t :=
      hasFDerivAt_fst.comp_hasDerivAt (f := fun s ↦ F (x, s)) t
        (hasDerivAt_slice_right (hF _ ⟨mem_univ _, hIcc ht⟩))
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt) heq
      (fun t ht ↦ hd t (Ioo_subset_Icc_self ht))
    exact htwist _ ⟨mem_univ _, hIcc (Ioo_subset_Icc_self hc)⟩ hc0
  rintro ⟨x, y₁⟩ ⟨-, h₁⟩ ⟨x', y₂⟩ ⟨-, h₂⟩ h
  simp only [stripTwistCoord_apply, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rcases lt_trichotomy y₁ y₂ with hlt | rfl | hlt
  · exact absurd h (key x h₁ h₂ hlt)
  · rfl
  · exact absurd h.symm (key x h₂ h₁ hlt)

/-- The mixed coordinates map every open set on which `F` is `C¹` and twists to an open set. -/
theorem isOpen_image_stripTwistCoord {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ 1 F V) (htwist : ∀ p ∈ V, (fderiv ℝ F p (0, 1)).1 ≠ 0) :
    IsOpen (stripTwistCoord F '' V) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨e, hG⟩ := exists_hasStrictFDerivAt_stripTwistCoord_of_contDiffAt
    (hF.contDiffAt (hV.mem_nhds hp)) one_ne_zero (htwist p hp)
  rw [← hG.map_nhds_eq_of_equiv]
  exact image_mem_map (hV.mem_nhds hp)

/-- **The inverse of the mixed coordinates is smooth.** If `I` is an open interval and `F` is
`C^n`, `n ≠ 0`, with nonzero twist on the strip `ℝ × I`, then the inverse of the mixed
coordinates `(x, y) ↦ (x, X(x, y))`, from the band they sweep out back to `ℝ × I`, is `C^n`. -/
theorem contDiffOn_invFunOn_stripTwistCoord {n : WithTop ℕ∞} (hn : n ≠ 0) (hI : IsOpen I)
    (hIc : I.OrdConnected) (hF : ContDiffOn ℝ n F (univ ×ˢ I))
    (htwist : ∀ p ∈ univ ×ˢ I, (fderiv ℝ F p (0, 1)).1 ≠ 0) :
    ContDiffOn ℝ n (invFunOn (stripTwistCoord F) (univ ×ˢ I))
      (stripTwistCoord F '' (univ ×ˢ I)) := by
  have hU : IsOpen ((univ : Set ℝ) ×ˢ I) := isOpen_univ.prod hI
  have hF1 : ContDiffOn ℝ 1 F (univ ×ˢ I) := hF.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have hinj : InjOn (stripTwistCoord F) (univ ×ˢ I) := injOn_stripTwistCoord hIc
    (fun p hp ↦ (hF1.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero) htwist
  have hGd : ContDiffOn ℝ n (stripTwistCoord F) (univ ×ˢ I) := by
    rw [stripTwistCoord_def]
    exact contDiffOn_fst.prodMk (contDiff_fst.comp_contDiffOn hF)
  -- The restriction of the mixed coordinates to `ℝ × I` is an open map.
  have hGo : IsOpenMap ((univ ×ˢ I).domRestrict (stripTwistCoord F)) := by
    intro W hW
    rw [domRestrict_eq, image_comp]
    exact isOpen_image_stripTwistCoord (hU.isOpenMap_subtype_val W hW)
      (hF1.mono (Subtype.coe_image_subset _ W))
      fun p hp ↦ htwist p (Subtype.coe_image_subset _ W hp)
  -- So the mixed coordinates form an open partial homeomorphism from `ℝ × I` onto the band. Its
  -- inverse is `invFunOn` and its target is the band, by construction of
  -- `Set.InjOn.toPartialEquiv`.
  refine (OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv _ _)
    hGd.continuousOn hGo hU).contDiffOn_symm_of_isInvertible_fderiv hGd fun p hp ↦ ?_
  obtain ⟨e, hG⟩ := exists_hasStrictFDerivAt_stripTwistCoord_of_contDiffAt
    (hF.contDiffAt (hU.mem_nhds hp)) hn (htwist p hp)
  exact ⟨e, hG.hasFDerivAt.fderiv.symm⟩

/-- **The closed band.** If `F` is continuous on the closed strip `ℝ × [[a, b]]` and its mixed
coordinates are injective there, they map that strip onto the closed band between the images
`x ↦ (x, X(x, a))` and `x ↦ (x, X(x, b))` of its boundary lines. -/
theorem image_stripTwistCoord_univ_prod_uIcc {a b : ℝ} (hF : ContinuousOn F (univ ×ˢ [[a, b]]))
    (hinj : InjOn (stripTwistCoord F) (univ ×ˢ [[a, b]])) :
    stripTwistCoord F '' (univ ×ˢ [[a, b]]) = {z | z.2 ∈ [[(F (z.1, a)).1, (F (z.1, b)).1]]} := by
  -- On each vertical line, `y ↦ X(x, y)` is continuous and injective, hence strictly monotone, so
  -- it maps `[[a, b]]` onto the interval between its values at the endpoints.
  have hslice (x : ℝ) :
      (fun y ↦ (F (x, y)).1) '' [[a, b]] = [[(F (x, a)).1, (F (x, b)).1]] := by
    have hc : ContinuousOn (fun y ↦ (F (x, y)).1) [[a, b]] :=
      continuous_fst.comp_continuousOn (hF.comp (by fun_prop) fun y hy ↦ ⟨mem_univ x, hy⟩)
    have hi : InjOn (fun y ↦ (F (x, y)).1) [[a, b]] := fun y₁ h₁ y₂ h₂ h ↦ by
      simpa using congrArg Prod.snd
        (hinj (show (x, y₁) ∈ univ ×ˢ [[a, b]] from ⟨mem_univ x, h₁⟩)
          (show (x, y₂) ∈ univ ×ˢ [[a, b]] from ⟨mem_univ x, h₂⟩) (by simp [h]))
    rcases hc.strictMonoOn_of_injOn_Icc' inf_le_sup hi with hmono | hanti
    · exact hc.image_uIcc_of_monotoneOn hmono.monotoneOn
    · exact hc.image_uIcc_of_antitoneOn hanti.antitoneOn
  ext ⟨x, X⟩
  simp only [mem_ofPred_eq, ← hslice x]
  constructor
  · rintro ⟨⟨x', y⟩, ⟨-, hy⟩, h⟩
    simp only [stripTwistCoord_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact mem_image_of_mem _ hy
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(x, y), ⟨mem_univ x, hy⟩, by simp⟩

/-! ### The generating function on the band -/

/-- The **generating function on the band** of a map `F = (X, Y)` of the plane, in the mixed
coordinates `(x, X)`: the generating function `S(x, y) = ∫₀ʸ Y(x, t) ∂_y X(x, t) dt` of `F`
(`TauCeti.stripGeneratingFunction`) evaluated at the point `(x, y)` of the strip `ℝ × I` with
`X(x, y) = X`. Where the mixed coordinates are injective on `ℝ × I`, this is `S` transported along
them (`TauCeti.bandGeneratingFunction_stripTwistCoord`); its values off the band carry no meaning.
-/
def bandGeneratingFunction (F : ℝ × ℝ → ℝ × ℝ) (I : Set ℝ) (z : ℝ × ℝ) : ℝ :=
  stripGeneratingFunction F (invFunOn (stripTwistCoord F) (univ ×ˢ I) z)

theorem bandGeneratingFunction_eq_comp :
    bandGeneratingFunction F I =
      stripGeneratingFunction F ∘ invFunOn (stripTwistCoord F) (univ ×ˢ I) :=
  (rfl)

/-- At the point `(x, X(x, y))` of the band, with `y ∈ I`, the band generating function takes the
value `S(x, y)` of the generating function of `F`. -/
theorem bandGeneratingFunction_stripTwistCoord (hinj : InjOn (stripTwistCoord F) (univ ×ˢ I))
    {p : ℝ × ℝ} (hp : p.2 ∈ I) :
    bandGeneratingFunction F I (stripTwistCoord F p) = stripGeneratingFunction F p := by
  rw [bandGeneratingFunction_eq_comp, comp_apply, hinj.leftInvOn_invFunOn ⟨mem_univ _, hp⟩]

/-- The band generating function vanishes on the lower boundary graph `X = X(x, 0)`. -/
theorem bandGeneratingFunction_stripTwistCoord_mk_zero
    (hinj : InjOn (stripTwistCoord F) (univ ×ˢ I)) (h0 : (0 : ℝ) ∈ I) (x : ℝ) :
    bandGeneratingFunction F I (stripTwistCoord F (x, 0)) = 0 := by
  rw [bandGeneratingFunction_stripTwistCoord hinj h0, stripGeneratingFunction_mk_zero]

/-- If `F` commutes with the translation `(x, y) ↦ (x + a, y)`, such as the deck translation
`a = 1`, and its mixed coordinates are injective on `ℝ × I`, then its band generating function is
invariant under the diagonal translation `(x, X) ↦ (x + a, X + a)`. -/
theorem bandGeneratingFunction_add_diag {a : ℝ} (hinj : InjOn (stripTwistCoord F) (univ ×ˢ I))
    (hT : ∀ q, F (q + (a, 0)) = F q + (a, 0)) (z : ℝ × ℝ) :
    bandGeneratingFunction F I (z + (a, a)) = bandGeneratingFunction F I z := by
  have hG (q : ℝ × ℝ) : stripTwistCoord F (q + (a, 0)) = stripTwistCoord F q + (a, a) := by
    simp [hT]
  by_cases hz : ∃ p ∈ univ ×ˢ I, stripTwistCoord F p = z
  · obtain ⟨p, ⟨-, hp⟩, rfl⟩ := hz
    rw [← hG, bandGeneratingFunction_stripTwistCoord hinj (by simpa using hp),
      bandGeneratingFunction_stripTwistCoord hinj hp, stripGeneratingFunction_add_fst hT]
  · -- Off the band, both values are the junk value of `invFunOn`.
    have hz' : ¬∃ p ∈ univ ×ˢ I, stripTwistCoord F p = z + (a, a) := by
      rintro ⟨p, ⟨-, hp⟩, hpz⟩
      refine hz ⟨p - (a, 0), ⟨mem_univ _, by simpa using hp⟩, add_right_cancel (b := (a, a)) ?_⟩
      rw [← hG, sub_add_cancel, hpz]
    simp only [bandGeneratingFunction_eq_comp, comp_apply, invFunOn_neg hz, invFunOn_neg hz']

/-- **The generating equations on the band.** Let `I` be an open interval containing `0`, and let
`F = (X, Y)` be `C²` with nonzero twist `∂_y X` on the strip `ℝ × I`. Let `p = (x, y)` with
`y ∈ I`, and suppose that `F` maps `(x, 0)` to the line `Y = 0` and preserves the area form
`dx ∧ dy` at the interior points of the segment from `(x, 0)` to `p`. Then the band generating
function has derivative `Y(p) dX - y dx` at `(x, X(p))`: `∂₁ S = -y` and `∂₂ S = Y(p)`. -/
theorem hasFDerivAt_bandGeneratingFunction (hI : IsOpen I) (hIc : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I) (hF : ContDiffOn ℝ 2 F (univ ×ˢ I))
    (htwist : ∀ q ∈ univ ×ˢ I, (fderiv ℝ F q (0, 1)).1 ≠ 0) {p : ℝ × ℝ} (hp : p.2 ∈ I)
    (hY : (F (p.1, 0)).2 = 0) (hdet : ∀ t ∈ uIoo 0 p.2, (fderiv ℝ F (p.1, t)).det = 1) :
    HasFDerivAt (bandGeneratingFunction F I)
      ((F p).2 • ContinuousLinearMap.snd ℝ ℝ ℝ - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (stripTwistCoord F p) := by
  have hU : IsOpen ((univ : Set ℝ) ×ˢ I) := isOpen_univ.prod hI
  have hinj : InjOn (stripTwistCoord F) (univ ×ˢ I) := injOn_stripTwistCoord hIc
    (fun q hq ↦ (hF.contDiffAt (hU.mem_nhds hq)).differentiableAt two_ne_zero) htwist
  have hseg (t : ℝ) (ht : t ∈ [[0, p.2]]) : (p.1, t) ∈ univ ×ˢ I :=
    ⟨mem_univ _, hIc.uIcc_subset h0 hp ht⟩
  rw [stripTwistCoord_apply]
  refine hasFDerivAt_of_eventuallyEq_stripGeneratingFunction
    (fun t ht ↦ hF.contDiffAt (hU.mem_nhds (hseg t ht))) hY hdet
    (htwist p ⟨mem_univ _, hp⟩) ?_
  filter_upwards [hU.mem_nhds (show p ∈ univ ×ˢ I from ⟨mem_univ _, hp⟩)] with q hq
  simpa using bandGeneratingFunction_stripTwistCoord hinj hq.2

/-- **The band generating function is smooth.** If `I` is an open interval containing `0` and `F`
is `C^(n + 1)` with nonzero twist on the strip `ℝ × I`, its band generating function is `C^n` on
the band swept out by the mixed coordinates. -/
theorem contDiffOn_bandGeneratingFunction {n : ℕ∞} (hI : IsOpen I) (hIc : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I) (hF : ContDiffOn ℝ (n + 1) F (univ ×ˢ I))
    (htwist : ∀ p ∈ univ ×ˢ I, (fderiv ℝ F p (0, 1)).1 ≠ 0) :
    ContDiffOn ℝ n (bandGeneratingFunction F I) (stripTwistCoord F '' (univ ×ˢ I)) := by
  have hU : IsOpen ((univ : Set ℝ) ×ˢ I) := isOpen_univ.prod hI
  have hinv := contDiffOn_invFunOn_stripTwistCoord (by simp) hI hIc hF htwist
  have hinj : InjOn (stripTwistCoord F) (univ ×ˢ I) := injOn_stripTwistCoord hIc
    (fun q hq ↦ (hF.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)) htwist
  rintro _ ⟨p, hp, rfl⟩
  -- The generating function is `C^n` at the point `p` of the strip over the band point.
  have hS : ContDiffAt ℝ n (stripGeneratingFunction F)
      (invFunOn (stripTwistCoord F) (univ ×ˢ I) (stripTwistCoord F p)) := by
    rw [hinj.leftInvOn_invFunOn hp]
    exact contDiffAt_stripGeneratingFunction fun t ht ↦
      hF.contDiffAt (hU.mem_nhds ⟨mem_univ _, hIc.uIcc_subset h0 hp.2 ht⟩)
  rw [bandGeneratingFunction_eq_comp]
  exact hS.comp_contDiffWithinAt _ ((hinv _ (mem_image_of_mem _ hp)).of_le le_self_add)

/-! ### Affine shears -/

/-- **The band generating function of an affine shear.** For `c ≠ 0`, the affine shear
`(x, y) ↦ (x + a + c y, y)` twists everywhere, and its band generating function over the whole
plane is `S(x, X) = (X - x - a)² / (2c)`. -/
theorem bandGeneratingFunction_affineShear {a c : ℝ} (hc : c ≠ 0) (z : ℝ × ℝ) :
    bandGeneratingFunction (fun q : ℝ × ℝ ↦ (q.1 + a + c * q.2, q.2)) univ z =
      (z.2 - z.1 - a) ^ 2 / (2 * c) := by
  set F : ℝ × ℝ → ℝ × ℝ := fun q ↦ (q.1 + a + c * q.2, q.2)
  have hinj : InjOn (stripTwistCoord F) (univ ×ˢ univ) := by
    rintro ⟨x, y⟩ - ⟨x', y'⟩ - h
    simp only [stripTwistCoord_apply, F, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simpa [hc] using h
  -- The point of the plane over `z` is `(z.1, (z.2 - z.1 - a) / c)`.
  have hz : stripTwistCoord F (z.1, (z.2 - z.1 - a) / c) = z := by
    ext
    · simp
    · simp only [stripTwistCoord_apply, F]
      field_simp
      ring
  calc bandGeneratingFunction F univ z
      = bandGeneratingFunction F univ (stripTwistCoord F (z.1, (z.2 - z.1 - a) / c)) := by
        rw [hz]
    _ = (z.2 - z.1 - a) ^ 2 / (2 * c) := by
        rw [bandGeneratingFunction_stripTwistCoord hinj (mem_univ _),
          stripGeneratingFunction_affineShear]
        field_simp

end TauCeti
