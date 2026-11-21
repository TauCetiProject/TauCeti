/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Symplectic.Annulus.GeneratingFunction
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# Global generating functions of twist maps of the strip

Let `F = (X, Y)` be a map of the plane, `C²` on a strip `ℝ × J` over an open interval `J`, which
*twists* there: `∂_y X` vanishes nowhere on the strip. For instance `F` is a lift of an
area-preserving twist diffeomorphism of the annulus `(ℝ / ℤ) × [0, 1]`, extended to an open collar
`J ⊇ [0, 1]`. This file shows that the twist coordinates `G(x, y) = (x, X(x, y))`
(`TauCeti.stripTwistCoord`) identify the strip with a *band* in the `(x, X)`-plane, and transports
the generating function `S` of `TauCeti.stripGeneratingFunction` to a single function on the whole
band, satisfying the generating equations everywhere.

* Each vertical slice `t ↦ X(x, t)` has a derivative of constant sign on `J`, by Darboux's
  theorem, so it is strictly monotone or strictly antitone
  (`TauCeti.strictMonoOn_or_strictAntiOn_fst_slice`), and `G` is injective on the strip
  (`TauCeti.injOn_stripTwistCoord`).
* For heights `c, d ∈ J`, `G` maps the closed strip `ℝ × [c, d]` onto the band between the two
  boundary graphs, `{(x, X) | X ∈ [X(x, c), X(x, d)]}`
  (`TauCeti.image_stripTwistCoord_preimage_snd_uIcc`). For `[c, d] = [0, 1]` this is the
  boundary-graph band of the twist map.
* By the inverse function theorem, `G` is a `C^n` local diffeomorphism on the open strip when `F`
  is `C^n`, `1 ≤ n` (`TauCeti.isLocalDiffeomorphOn_stripTwistCoord`). Being injective, it is a
  `C^n` diffeomorphism from the strip onto an open band
  (`IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn`), with inverse `Function.invFunOn G (ℝ × J)`.

The **band generating function** `S'(x, X) = S(G⁻¹(x, X))`
(`TauCeti.stripBandGeneratingFunction`) is then defined on an open neighbourhood of the closed
band, and when `F` preserves area and the line `y = 0`:

* it satisfies the generating equations `∂₁ S'(x, X) = -y`, `∂₂ S'(x, X) = Y` at every point
  `(x, X) = G(x, y)` of the band (`TauCeti.hasFDerivAt_stripBandGeneratingFunction`);
* it is `C^n` on the band when `F` is `C^(n + 1)`
  (`TauCeti.contDiffAt_stripBandGeneratingFunction`);
* it vanishes on the lower boundary graph `X = X(x, 0)`
  (`TauCeti.stripBandGeneratingFunction_stripTwistCoord_mk_zero`), which fixes its additive
  constant;
* it is invariant under the simultaneous translation `(x, X) ↦ (x + a, X + a)` when `F` commutes
  with `(x, y) ↦ (x + a, y)` on the strip, as a lift of an annulus map does for `a = 1`
  (`TauCeti.stripBandGeneratingFunction_add_diag`);
* its second derivative is `d²S'(v, w) = (X_x v₁ w₁ - v₁ w₂ - v₂ w₁ + Y_y v₂ w₂) / X_y`
  (`TauCeti.fderiv_fderiv_stripBandGeneratingFunction_apply`), so its mixed derivative
  `∂₁ ∂₂ S' = -1 / ∂_y X` has the sign opposite to that of the twist.

These are the global generating functions of the twist factors in the generating-function proof of
the Poincaré–Birkhoff theorem. With the convention `y = -∂₁ S'`, `Y = ∂₂ S'`, a positive twist
`(x, y) ↦ (x + c y, y)`, `c > 0`, has the generator `(X - x)² / (2c)`, with `∂₁ ∂₂ S' = -1 / c`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 4 (generating functions).
-/

public section

noncomputable section

open Filter Function Set
open scoped ContDiff Manifold Topology Interval

namespace TauCeti

variable {F : ℝ × ℝ → ℝ × ℝ} {J : Set ℝ}

/-! ### The twist coordinates on a strip -/

/-- Where `F = (X, Y)` twists at `(x, t)`, the vertical slice `s ↦ X(x, s)` has derivative the
twist `∂_y X(x, t)` at `t`. -/
private theorem hasDerivAt_fst_slice {x t : ℝ} (htwist : (fderiv ℝ F (x, t) (0, 1)).1 ≠ 0) :
    HasDerivAt (fun s ↦ (F (x, s)).1) (fderiv ℝ F (x, t) (0, 1)).1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t <| hasDerivAt_slice_right <|
    differentiableAt_of_fderiv_ne_zero fun h ↦ htwist (by simp [h])

/-- On a strip `ℝ × J` over an interval `J`, where `F = (X, Y)` twists,
each vertical slice `t ↦ X(x, t)` is strictly monotone or strictly antitone on `J`: by Darboux's
theorem the twist `∂_y X` has constant sign along it. -/
theorem strictMonoOn_or_strictAntiOn_fst_slice (hJ : J.OrdConnected)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) (x : ℝ) :
    StrictMonoOn (fun t ↦ (F (x, t)).1) J ∨ StrictAntiOn (fun t ↦ (F (x, t)).1) J := by
  have hd (t : ℝ) (ht : t ∈ J) := hasDerivAt_fst_slice (htwist (x, t) (mem_preimage.2 ht))
  have hc : ContinuousOn (fun t ↦ (F (x, t)).1) J :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hd' (t : ℝ) (ht : t ∈ interior J) :=
    (hd t (interior_subset ht)).hasDerivWithinAt (s := interior J)
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hJ.convex
      (fun t ht ↦ (hd t ht).hasDerivWithinAt) (m := 0)
      (fun t ht ↦ htwist _ (mem_preimage.2 ht)) with h | h
  · exact .inr <| strictAntiOn_of_hasDerivWithinAt_neg hJ.convex hc hd'
      fun t ht ↦ h t (interior_subset ht)
  · exact .inl <| strictMonoOn_of_hasDerivWithinAt_pos hJ.convex hc hd'
      fun t ht ↦ h t (interior_subset ht)

/-- On a strip `ℝ × J` over an interval `J`, where `F` twists, the twist coordinates
`(x, y) ↦ (x, X(x, y))` are injective. -/
theorem injOn_stripTwistCoord (hJ : J.OrdConnected)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) :
    InjOn (stripTwistCoord F) (Prod.snd ⁻¹' J) := by
  rintro ⟨x, s⟩ hs ⟨x', t⟩ ht h
  rw [stripTwistCoord_apply, stripTwistCoord_apply] at h
  obtain ⟨rfl, h⟩ := Prod.mk.inj h
  simp only [mem_preimage] at hs ht
  rcases strictMonoOn_or_strictAntiOn_fst_slice hJ htwist x with hm | ha
  · rw [hm.injOn hs ht h]
  · rw [ha.injOn hs ht h]

/-- **The boundary-graph band.** On a strip `ℝ × J` over an interval `J`, where `F = (X, Y)` twists,
the twist coordinates map the closed strip `ℝ × [c, d]`, for heights
`c, d ∈ J`, onto the band `{(x, X) | X ∈ [X(x, c), X(x, d)]}` between the two boundary graphs. -/
theorem image_stripTwistCoord_preimage_snd_uIcc (hJ : J.OrdConnected)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {c d : ℝ} (hc : c ∈ J)
    (hd : d ∈ J) :
    stripTwistCoord F '' (Prod.snd ⁻¹' [[c, d]]) =
      {z | z.2 ∈ [[(F (z.1, c)).1, (F (z.1, d)).1]]} := by
  have hsub : [[c, d]] ⊆ J := hJ.uIcc_subset hc hd
  ext ⟨x, X⟩
  constructor
  · rintro ⟨⟨x', t⟩, ht, h⟩
    rw [stripTwistCoord_apply] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp only [mem_preimage] at ht
    rcases strictMonoOn_or_strictAntiOn_fst_slice hJ htwist x' with hm | ha
    · exact (hm.monotoneOn.mono hsub).mapsTo_uIcc ht
    · exact (ha.antitoneOn.mono hsub).mapsTo_uIcc ht
  · intro hX
    have hcont : ContinuousOn (fun t ↦ (F (x, t)).1) [[c, d]] := fun t ht ↦
      (hasDerivAt_fst_slice (htwist (x, t) (mem_preimage.2 (hsub ht)))).continuousAt
        |>.continuousWithinAt
    obtain ⟨t, ht, htX⟩ := intermediate_value_uIcc hcont hX
    exact ⟨(x, t), mem_preimage.2 ht, by simp [htX]⟩

/-- **The twist coordinates are a local diffeomorphism.** On a strip `ℝ × J` over an open set `J`,
where `F` is `C^n`, `1 ≤ n`, and twists, the twist coordinates `(x, y) ↦ (x, X(x, y))` are a `C^n`
local diffeomorphism. When `J` is an interval they are injective on the strip
(`TauCeti.injOn_stripTwistCoord`), so `IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn` makes them
a `C^n` diffeomorphism from the strip onto the open band, its image. -/
theorem isLocalDiffeomorphOn_stripTwistCoord {n : WithTop ℕ∞} (hn : 1 ≤ n) (hJ : IsOpen J)
    (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ n F q)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n (stripTwistCoord F) (Prod.snd ⁻¹' J) := by
  rintro ⟨q, hq⟩
  obtain ⟨e, -, he⟩ := exists_hasStrictFDerivAt_stripTwistCoord (hF q hq)
    (zero_lt_one.trans_le hn).ne' (htwist q hq)
  exact isLocalDiffeomorphAt_of_fderiv_eq
    (fun r hr ↦ (contDiffAt_stripTwistCoord (hF r hr)).contDiffWithinAt)
    (hJ.preimage continuous_snd) hq hn he.hasFDerivAt.fderiv.symm

/-- The inverse of the twist coordinates on a strip over an open interval, where `F` is `C^n` and
twists, is `C^n` at every point of the band. -/
private theorem contDiffAt_invFunOn_stripTwistCoord {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hJ : IsOpen J) (hJc : J.OrdConnected) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ n F q)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {q : ℝ × ℝ}
    (hq : q ∈ Prod.snd ⁻¹' J) :
    ContDiffAt ℝ n (invFunOn (stripTwistCoord F) (Prod.snd ⁻¹' J)) (stripTwistCoord F q) := by
  have hS : IsOpen (Prod.snd ⁻¹' J : Set (ℝ × ℝ)) := hJ.preimage continuous_snd
  have hinj := injOn_stripTwistCoord hJc htwist
  have hd := isLocalDiffeomorphOn_stripTwistCoord hn hJ hF htwist
  exact (contMDiffOn_iff_contDiffOn.1 (hd.contMDiffOn_invFunOn hS hinj)).contDiffAt
    ((hd.isLocalHomeomorphOn.isOpen_image hS).mem_nhds (mem_image_of_mem _ hq))

/-! ### The generating function on the band -/

/-- The **generating function on the twist band** of `F` over the strip `ℝ × J`: the function
`S'(x, X) = S(x, y)` of the twist coordinates `(x, X) = (x, X(x, y))` of a point `(x, y)` of the
strip, where `S` is `TauCeti.stripGeneratingFunction F`. Its value off the band is unspecified. -/
def stripBandGeneratingFunction (F : ℝ × ℝ → ℝ × ℝ) (J : Set ℝ) (z : ℝ × ℝ) : ℝ :=
  stripGeneratingFunction F (invFunOn (stripTwistCoord F) (Prod.snd ⁻¹' J) z)

theorem stripBandGeneratingFunction_def (z : ℝ × ℝ) :
    stripBandGeneratingFunction F J z =
      stripGeneratingFunction F (invFunOn (stripTwistCoord F) (Prod.snd ⁻¹' J) z) :=
  (rfl)

/-- Where the twist coordinates are injective on the strip, the band generating function at
`(x, X(x, y))` is the generating function at `(x, y)`. -/
theorem stripBandGeneratingFunction_stripTwistCoord
    (hinj : InjOn (stripTwistCoord F) (Prod.snd ⁻¹' J)) {q : ℝ × ℝ} (hq : q ∈ Prod.snd ⁻¹' J) :
    stripBandGeneratingFunction F J (stripTwistCoord F q) = stripGeneratingFunction F q := by
  rw [stripBandGeneratingFunction_def, hinj.leftInvOn_invFunOn hq]

/-- The band generating function vanishes on the lower boundary graph `X = X(x, 0)`, the image
of the line `y = 0` under the twist coordinates. -/
theorem stripBandGeneratingFunction_stripTwistCoord_mk_zero
    (hinj : InjOn (stripTwistCoord F) (Prod.snd ⁻¹' J)) (h0 : 0 ∈ J) (x : ℝ) :
    stripBandGeneratingFunction F J (stripTwistCoord F (x, 0)) = 0 := by
  simpa using stripBandGeneratingFunction_stripTwistCoord hinj (q := (x, 0)) (mem_preimage.2 h0)

/-- **Periodicity of the band generating function.** Let `J` be an open interval containing `0`.
If `F` commutes on the strip `ℝ × J` with the translation `(x, y) ↦ (x + a, y)`, as a lift of an
annulus map does for `a = 1`, and the twist coordinates are injective there, then the band
generating function is invariant under the simultaneous translation `(x, X) ↦ (x + a, X + a)` of
the band. -/
theorem stripBandGeneratingFunction_add_diag (hJ : IsOpen J) (hJc : J.OrdConnected) (h0 : 0 ∈ J)
    (hinj : InjOn (stripTwistCoord F) (Prod.snd ⁻¹' J)) {a : ℝ}
    (hFa : ∀ q ∈ Prod.snd ⁻¹' J, F (q + (a, 0)) = F q + (a, 0)) {z : ℝ × ℝ}
    (hz : z ∈ stripTwistCoord F '' (Prod.snd ⁻¹' J)) :
    stripBandGeneratingFunction F J (z + (a, a)) = stripBandGeneratingFunction F J z := by
  obtain ⟨q, hq, rfl⟩ := hz
  have hqa : q + (a, 0) ∈ Prod.snd ⁻¹' J := by simpa using hq
  have hGa : stripTwistCoord F q + (a, a) = stripTwistCoord F (q + (a, 0)) := by
    simp [hFa q hq]
  rw [hGa, stripBandGeneratingFunction_stripTwistCoord hinj hqa,
    stripBandGeneratingFunction_stripTwistCoord hinj hq]
  -- The vertical segment below `q` lies in the open strip, where `F` commutes with the
  -- translation.
  refine stripGeneratingFunction_add_fst_of_eventuallyEq fun t ht ↦ ?_
  have ht' : (q.1, t) ∈ Prod.snd ⁻¹' J :=
    mem_preimage.2 (hJc.uIcc_subset h0 (mem_preimage.1 hq) (uIoo_subset_uIcc_self ht))
  exact eventually_of_mem ((hJ.preimage continuous_snd).mem_nhds ht') hFa

/-- **The generating equations on the band.** Let the twist coordinates be injective on the strip
`ℝ × J` over an open set `J`, and let `p = (x, y)` be a point of the strip at which `F = (X, Y)`
twists, such that `F` is `C²` along the segment from `(x, 0)` to `p`, maps `(x, 0)` to the line
`y = 0` and preserves area at the interior points of that segment. Then the band generating
function has derivative `Y(p) dX - y dx` at `(x, X(p))`: `∂₁ S'(x, X) = -y` and
`∂₂ S'(x, X) = Y(p)`. -/
theorem hasFDerivAt_stripBandGeneratingFunction (hJ : IsOpen J)
    (hinj : InjOn (stripTwistCoord F) (Prod.snd ⁻¹' J)) {p : ℝ × ℝ} (hp : p ∈ Prod.snd ⁻¹' J)
    (hF : ∀ t ∈ [[0, p.2]], ContDiffAt ℝ 2 F (p.1, t)) (hY : (F (p.1, 0)).2 = 0)
    (hdet : ∀ t ∈ uIoo 0 p.2, (fderiv ℝ F (p.1, t)).det = 1)
    (htwist : (fderiv ℝ F p (0, 1)).1 ≠ 0) :
    HasFDerivAt (stripBandGeneratingFunction F J)
      ((F p).2 • ContinuousLinearMap.snd ℝ ℝ ℝ - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (stripTwistCoord F p) :=
  hasFDerivAt_of_eventuallyEq_stripGeneratingFunction hF hY hdet htwist <|
    eventually_of_mem ((hJ.preimage continuous_snd).mem_nhds hp) fun _ hq ↦
      stripBandGeneratingFunction_stripTwistCoord hinj hq

/-- On a strip `ℝ × J` over an open interval `J` containing `0`, where `F` is `C^(n + 1)` and
twists, the band generating function is `C^n` at every point of the band. -/
theorem contDiffAt_stripBandGeneratingFunction {n : ℕ∞} (hJ : IsOpen J) (hJc : J.OrdConnected)
    (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ (n + 1) F q)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {q : ℝ × ℝ}
    (hq : q ∈ Prod.snd ⁻¹' J) :
    ContDiffAt ℝ n (stripBandGeneratingFunction F J) (stripTwistCoord F q) := by
  have hn : 1 ≤ ((n + 1 : ℕ∞) : WithTop ℕ∞) := by simp
  have hinj := injOn_stripTwistCoord hJc htwist
  have hS : ContDiffAt ℝ n (stripGeneratingFunction F) q :=
    contDiffAt_stripGeneratingFunction fun t ht ↦
      hF _ (mem_preimage.2 (hJc.uIcc_subset h0 (mem_preimage.1 hq) ht))
  rw [← hinj.leftInvOn_invFunOn hq] at hS
  exact hS.comp _ ((contDiffAt_invFunOn_stripTwistCoord hn hJ hJc hF htwist hq).of_le (by simp))

/-- If `e (u, v) = (u, (A (u, v)).1)` for a linear map `A` of the plane with
`(A (0, 1)).1 ≠ 0`, then `e⁻¹ (a, b) = (a, (b - X_x a) / X_y)` in the notation `A = d(X, Y)`. -/
private theorem symm_apply_of_coe_eq_prod {A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ} {e : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ}
    (he : (e : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp A))
    (htw : (A (0, 1)).1 ≠ 0) (v : ℝ × ℝ) :
    e.symm v = (v.1, (v.2 - (A (1, 0)).1 * v.1) / (A (0, 1)).1) := by
  set t := (v.2 - (A (1, 0)).1 * v.1) / (A (0, 1)).1
  have hA := A.apply_mk_eq_smul_add_smul v.1 t
  rw [e.symm_apply_eq, ← ContinuousLinearEquiv.coe_coe, he]
  ext
  · simp
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.comp_apply, hA, Prod.fst_add, Prod.smul_fst, smul_eq_mul, t]
    field_simp
    ring

/-- On the open band the derivative of the band generating function is `Y dX - y dx`, read through
the inverse `k` of the twist coordinates: `dS'(z) = Y(k z) dX - (k z).2 dx` near every point of
the band. -/
private theorem fderiv_stripBandGeneratingFunction_eventuallyEq (hJ : IsOpen J)
    (hJc : J.OrdConnected) (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q)
    (hY : ∀ x, (F (x, 0)).2 = 0) (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {q : ℝ × ℝ}
    (hq : q ∈ Prod.snd ⁻¹' J) :
    fderiv ℝ (stripBandGeneratingFunction F J) =ᶠ[𝓝 (stripTwistCoord F q)]
      fun z ↦ (F (invFunOn (stripTwistCoord F) (Prod.snd ⁻¹' J) z)).2 •
          ContinuousLinearMap.snd ℝ ℝ ℝ -
        (invFunOn (stripTwistCoord F) (Prod.snd ⁻¹' J) z).2 • ContinuousLinearMap.fst ℝ ℝ ℝ := by
  have hS : IsOpen (Prod.snd ⁻¹' J : Set (ℝ × ℝ)) := hJ.preimage continuous_snd
  have hinj := injOn_stripTwistCoord hJc htwist
  have hband := ((isLocalDiffeomorphOn_stripTwistCoord one_le_two hJ hF
    htwist).isLocalHomeomorphOn.isOpen_image hS).mem_nhds (mem_image_of_mem _ hq)
  filter_upwards [hband]
  rintro _ ⟨r, hr, rfl⟩
  have hseg : [[0, r.2]] ⊆ J := hJc.uIcc_subset h0 (mem_preimage.1 hr)
  have hd := hasFDerivAt_stripBandGeneratingFunction hJ hinj hr
    (fun t ht ↦ hF _ (mem_preimage.2 (hseg ht))) (hY r.1)
    (fun t ht ↦ hdet _ (mem_preimage.2 (hseg (uIoo_subset_uIcc_self ht)))) (htwist r hr)
  rw [hd.fderiv, hinj.leftInvOn_invFunOn hr]

/-- **The Hessian of the band generating function.** On a strip `ℝ × J` over an open interval `J`
containing `0`, let `F = (X, Y)` be `C²`, twist, preserve area and map the line `y = 0` into
itself. Then at every point `(x, X(x, y))` of the band the second derivative of the band
generating function `S'` is

`d²S'(v, w) = (X_x v₁ w₁ - v₁ w₂ - v₂ w₁ + Y_y v₂ w₂) / X_y`,

the derivatives of `F` being taken at `(x, y)`. In particular `∂₁ ∂₁ S' = X_x / X_y`, the mixed
derivative `∂₁ ∂₂ S' = -1 / X_y` has the sign opposite to the twist, and `∂₂ ∂₂ S' = Y_y / X_y`. -/
theorem fderiv_fderiv_stripBandGeneratingFunction_apply (hJ : IsOpen J) (hJc : J.OrdConnected)
    (h0 : 0 ∈ J) (hF : ∀ q ∈ Prod.snd ⁻¹' J, ContDiffAt ℝ 2 F q) (hY : ∀ x, (F (x, 0)).2 = 0)
    (hdet : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q).det = 1)
    (htwist : ∀ q ∈ Prod.snd ⁻¹' J, (fderiv ℝ F q (0, 1)).1 ≠ 0) {q : ℝ × ℝ}
    (hq : q ∈ Prod.snd ⁻¹' J) (v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (stripBandGeneratingFunction F J)) (stripTwistCoord F q) v w =
      ((fderiv ℝ F q (1, 0)).1 * v.1 * w.1 - v.1 * w.2 - v.2 * w.1 +
        (fderiv ℝ F q (0, 1)).2 * v.2 * w.2) / (fderiv ℝ F q (0, 1)).1 := by
  set S := Prod.snd ⁻¹' J
  set G := stripTwistCoord F
  set k := invFunOn G S
  have hS : IsOpen S := hJ.preimage continuous_snd
  have hinj := injOn_stripTwistCoord hJc htwist
  have heq := fderiv_stripBandGeneratingFunction_eventuallyEq hJ hJc h0 hF hY hdet htwist hq
  -- The inverse `k` has derivative `e⁻¹` at `G q`, where `e` is the derivative of `G` at `q`.
  obtain ⟨e, he, hG⟩ := exists_hasStrictFDerivAt_stripTwistCoord (hF q hq) two_ne_zero (htwist q hq)
  have hk : HasFDerivAt k (e.symm : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (G q) :=
    (hG.to_local_left_inverse (eventually_of_mem (hS.mem_nhds hq)
      fun _ hr ↦ hinj.leftInvOn_invFunOn hr)).hasFDerivAt
  have hkq : k (G q) = q := hinj.leftInvOn_invFunOn hq
  have hFq : HasFDerivAt F (fderiv ℝ F q) (k (G q)) := by
    rw [hkq]
    exact ((hF q hq).differentiableAt two_ne_zero).hasFDerivAt
  have hYk : HasFDerivAt (fun z ↦ (F (k z)).2)
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ F q)).comp
        (e.symm : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)) (G q) :=
    (hasFDerivAt_snd.comp _ hFq).comp _ hk
  have hyk : HasFDerivAt (fun z ↦ (k z).2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (e.symm : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)) (G q) :=
    hasFDerivAt_snd.comp _ hk
  have hD : HasFDerivAt (fun z ↦ (F (k z)).2 • ContinuousLinearMap.snd ℝ ℝ ℝ -
      (k z).2 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      ((((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ F q)).comp
        (e.symm : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (e.symm : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)) (G q) :=
    (hYk.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ)).sub
      (hyk.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ))
  rw [heq.fderiv_eq, hD.fderiv]
  -- Evaluate with `e⁻¹ v = (v₁, (v₂ - X_x v₁) / X_y)` and `X_x Y_y - X_y Y_x = 1`.
  have hdetq : (fderiv ℝ F q (1, 0)).1 * (fderiv ℝ F q (0, 1)).2 -
      (fderiv ℝ F q (1, 0)).2 * (fderiv ℝ F q (0, 1)).1 = 1 := by
    have h := hdet q hq
    rwa [ContinuousLinearMap.det, LinearMap.det_finTwoProd] at h
  have htw := htwist q hq
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    symm_apply_of_coe_eq_prod he htw, ContinuousLinearMap.coe_snd']
  rw [(fderiv ℝ F q).apply_mk_eq_smul_add_smul v.1]
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, smul_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst']
  field_simp
  linear_combination (-(v.1 * w.2)) * hdetq

end TauCeti
