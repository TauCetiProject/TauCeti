/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval
public import TauCeti.RingTheory.PowerSeries.Restricted.Taylor
import TauCeti.RingTheory.PowerSeries.TateAlgebra

/-!
# Translation and affine changes of coordinates on an open disc

Let `R` be an ultrametric normed commutative ring and `f = ∑ aₖ Xᵏ` a power series on the open disc
of radius `R₀` (`PowerSeries.OnOpenDisc`), so that `f` is restricted at every radius `0 < r < R₀`.
For a point `a` of the open disc, `‖a‖ < R₀`, the Taylor translate `taylor a f = ∑ₙ (Δⁿ f)(a) Xⁿ`
(`PowerSeries.taylor`) is again a series on the open disc of radius `R₀`: no radius is lost, since
over an ultrametric ring the open disc of radius `R₀` centred at `a` is the open disc centred
at `0`. At every radius `r` with `‖a‖ ≤ r < R₀` translation preserves the Gauss norm, and
over a complete ring it is the series `f(X + a)`:

```text
‖taylor a f‖_r = ‖f‖_r,    (taylor a f)(b) = f(b + a)    for ‖a‖ ≤ r < R₀ and ‖b‖ < R₀.
```

These are the open-disc counterparts of the translation of restricted series
(`PowerSeries.IsRestricted.taylor`) and of entire series (`PowerSeries.IsEntire.taylor`).
Translation is additive and multiplicative, commutes with Hasse derivatives, and translations
by `a` and `b` compose to the translation by `b + a`. It is therefore a ring automorphism
`PowerSeries.OnOpenDisc.taylorEquiv` of the algebra of series on the open disc, with inverse the
translation by `-a`. This automorphism is a homeomorphism for the topology of the Gauss norms at
all radii below `R₀` (`TauCeti.PowerSeries.OnOpenDisc.continuous_taylorEquiv`).

Combined with rescaling (`PowerSeries.OnOpenDisc.rescale`), translation gives the affine changes
of coordinates `X ↦ a + uX`: if `‖a‖ < R₀` and `‖u‖ S₀ ≤ R₀`, then `f(a + uX)` lies on the open
disc of radius `S₀`, and its value at `b` is `f(ub + a)`. These are the changes of disc coordinates
used for locally analytic functions on open discs. No factorial is inverted, so all of this holds
in every characteristic.

## Main definitions

* `PowerSeries.OnOpenDisc.taylorEquiv`: translation by a point `a` of the open disc, as a ring
  automorphism of the series on the open disc of radius `R₀`.

## Main results

* `PowerSeries.OnOpenDisc.taylor`: the translate of a series on an open disc by a point of that
  disc lies on the same disc.
* `PowerSeries.OnOpenDisc.gaussNorm_taylor`: translation preserves the Gauss norm at every radius
  between `‖a‖` and `R₀`.
* `PowerSeries.OnOpenDisc.evalAt_taylor` and `PowerSeries.OnOpenDisc.hasSum_taylor`: the Taylor
  identity `(taylor a f)(b) = f(b + a)` and the convergent Taylor expansion
  `f(b + a) = ∑ₖ (Δᵏ f)(a) bᵏ` on the open disc.
* `PowerSeries.OnOpenDisc.taylor_add`, `PowerSeries.OnOpenDisc.taylor_smul`,
  `PowerSeries.OnOpenDisc.taylor_mul`, `PowerSeries.OnOpenDisc.hasseDeriv_taylor` and
  `PowerSeries.OnOpenDisc.taylor_taylor`: translation is linear and multiplicative, commutes with
  Hasse derivatives, and composes additively; `PowerSeries.OnOpenDisc.taylor_inj` makes it
  injective.
* `PowerSeries.OnOpenDisc.taylorEquiv_symm`, `PowerSeries.OnOpenDisc.taylorEquiv_trans` and
  `PowerSeries.OnOpenDisc.evalAtHom_taylorEquiv`: the inverse, composition and evaluation laws of
  the translation automorphisms.
* `TauCeti.PowerSeries.OnOpenDisc.continuous_taylorEquiv`: translation is continuous for the Gauss
  topology on the open disc.
* `PowerSeries.OnOpenDisc.rescale_taylor` and `PowerSeries.OnOpenDisc.evalAt_rescale_taylor`: the
  affine change of coordinates `X ↦ a + uX` carries the open disc of radius `R₀` to the open disc
  of radius `S₀` when `‖a‖ < R₀` and `‖u‖ S₀ ≤ R₀`, and evaluates as `f(ub + a)`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ} {f g : R⟦X⟧} {a b : R}

omit [IsUltrametricDist R] in
/-- A series on the open disc of radius `R₀` is restricted at the larger of a nonnegative radius
`s < R₀` and a radius `t < R₀`. -/
private theorem OnOpenDisc.isRestricted_max (hf : f.OnOpenDisc R₀) {s t : ℝ} (hs : 0 ≤ s)
    (hsR : s < R₀) (htR : t < R₀) : f.IsRestricted (max s t) :=
  hf.isRestricted (by rw [abs_of_nonneg (le_max_of_le_left hs)]; exact max_lt hsR htR)

omit [IsUltrametricDist R] in
/-- A series on the open disc of radius `R₀` is restricted at the norm of a point of that disc. -/
private theorem OnOpenDisc.isRestricted_norm (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    f.IsRestricted ‖a‖ :=
  hf.isRestricted (by rwa [abs_norm])

/-- **Translates of series on an open disc stay on the disc.** Over an ultrametric normed ring,
if `f` lies on the open disc of radius `R₀` and `‖a‖ < R₀`, then the expansion `taylor a f` of `f`
at `a` lies on the open disc of radius `R₀`. -/
theorem OnOpenDisc.taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    (PowerSeries.taylor a f).OnOpenDisc R₀ := onOpenDisc_iff.mpr fun r hr hrR ↦
  TauCeti.PowerSeries.isRestricted_of_abs_le
    ((hf.isRestricted_max hr.le hrR ha).taylor (le_max_right _ _))
    (by rw [abs_of_pos hr, abs_of_nonneg (le_max_of_le_left hr.le)]; exact le_max_left _ _)

variable [CompleteSpace R]

/-- **Translation preserves the Gauss norms.** Over a complete ultrametric normed ring, for a
series `f` on the open disc of radius `R₀` and a radius `0 < r < R₀` with `‖a‖ ≤ r`,
`‖taylor a f‖_r = ‖f‖_r`. -/
theorem OnOpenDisc.gaussNorm_taylor (hf : f.OnOpenDisc R₀) {r : ℝ} (hr : 0 < r) (har : ‖a‖ ≤ r)
    (hrR : r < R₀) : (PowerSeries.taylor a f).gaussNorm norm r = f.gaussNorm norm r :=
  (hf.isRestricted (by rwa [abs_of_pos hr])).gaussNorm_taylor hr har

/-- **The Taylor identity on an open disc.** Over a complete ultrametric normed ring, if `f` lies
on the open disc of radius `R₀` and `‖a‖ < R₀`, `‖b‖ < R₀`, then the expansion of `f` at `a`
evaluated at `b` is `f(b + a)`. -/
theorem OnOpenDisc.evalAt_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀) :
    (PowerSeries.taylor a f).evalAt b = f.evalAt (b + a) :=
  (hf.isRestricted_max (norm_nonneg a) ha hb).evalAt_taylor (le_max_left _ _) (le_max_right _ _)

/-- **The Taylor expansion on an open disc.** Over a complete ultrametric normed ring, if `f` lies
on the open disc of radius `R₀` and `‖a‖ < R₀`, `‖b‖ < R₀`, then
`f(b + a) = ∑ₖ (Δᵏ f)(a) bᵏ`. -/
theorem OnOpenDisc.hasSum_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀) :
    HasSum (fun k ↦ (PowerSeries.hasseDeriv k f).evalAt a * b ^ k) (f.evalAt (b + a)) :=
  (hf.isRestricted_max (norm_nonneg a) ha hb).hasSum_taylor (le_max_left _ _) (le_max_right _ _)

/-- Translation by a point of the open disc is additive on series on that disc. -/
theorem OnOpenDisc.taylor_add (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a (f + g) = PowerSeries.taylor a f + PowerSeries.taylor a g :=
  (hf.isRestricted_norm ha).taylor_add (hg.isRestricted_norm ha) le_rfl

/-- Translation by a point of the open disc commutes with scalar multiplication. -/
theorem OnOpenDisc.taylor_smul (hf : f.OnOpenDisc R₀) (c : R) (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a (c • f) = c • PowerSeries.taylor a f :=
  (hf.isRestricted_norm ha).taylor_smul c le_rfl

/-- Translation by a point of the open disc is multiplicative on series on that disc. -/
theorem OnOpenDisc.taylor_mul (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a (f * g) = PowerSeries.taylor a f * PowerSeries.taylor a g :=
  (hf.isRestricted_norm ha).taylor_mul (hg.isRestricted_norm ha) le_rfl

/-- **Hasse derivatives commute with translation** of series on an open disc. -/
theorem OnOpenDisc.hasseDeriv_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) (k : ℕ) :
    PowerSeries.hasseDeriv k (PowerSeries.taylor a f) =
      PowerSeries.taylor a (PowerSeries.hasseDeriv k f) :=
  (hf.isRestricted_norm ha).hasseDeriv_taylor le_rfl k

/-- **Translations compose**: for a series `f` on the open disc of radius `R₀` and points `a`, `b`
of that disc, `taylor b (taylor a f) = taylor (b + a) f`. -/
theorem OnOpenDisc.taylor_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀) :
    PowerSeries.taylor b (PowerSeries.taylor a f) = PowerSeries.taylor (b + a) f :=
  (hf.isRestricted_max (norm_nonneg a) ha hb).taylor_taylor (le_max_left _ _) (le_max_right _ _)

/-- Translation by `-a` inverts translation by a point `a` of the open disc. -/
theorem OnOpenDisc.taylor_neg_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    PowerSeries.taylor (-a) (PowerSeries.taylor a f) = f :=
  (hf.isRestricted_norm ha).taylor_neg_taylor le_rfl

/-- Translation by a point of the open disc is injective on series on that disc. -/
theorem OnOpenDisc.taylor_inj (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a f = PowerSeries.taylor a g ↔ f = g :=
  ⟨fun h ↦ by rw [← hf.taylor_neg_taylor ha, h, hg.taylor_neg_taylor ha], fun h ↦ h ▸ rfl⟩

/-- A series on an open disc has zero translate at a point of the disc exactly when it is zero. -/
theorem OnOpenDisc.taylor_eq_zero_iff (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a f = 0 ↔ f = 0 := by
  simpa using hf.taylor_inj onOpenDisc_zero ha

variable (R) in
/-- **Translation as a ring automorphism.** Over a complete ultrametric normed ring, translation
`f ↦ taylor a f` by a point `a` of the open disc of radius `R₀` is a ring automorphism of the
series on that disc, with inverse the translation by `-a`. -/
noncomputable def OnOpenDisc.taylorEquiv (ha : ‖a‖ < R₀) :
    OnOpenDisc.subring R R₀ ≃+* OnOpenDisc.subring R R₀ where
  toFun f := ⟨PowerSeries.taylor a f,
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).taylor ha)⟩
  invFun f := ⟨PowerSeries.taylor (-a) f,
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).taylor (by rwa [norm_neg]))⟩
  left_inv f := Subtype.ext ((OnOpenDisc.mem_subring.mp f.2).taylor_neg_taylor ha)
  right_inv f := Subtype.ext <| by
    simpa using (OnOpenDisc.mem_subring.mp f.2).taylor_neg_taylor (a := -a) (by rwa [norm_neg])
  map_mul' f g := Subtype.ext
    ((OnOpenDisc.mem_subring.mp f.2).taylor_mul (OnOpenDisc.mem_subring.mp g.2) ha)
  map_add' f g := Subtype.ext
    ((OnOpenDisc.mem_subring.mp f.2).taylor_add (OnOpenDisc.mem_subring.mp g.2) ha)

/-- The translation automorphism sends a series `f` to its translate `taylor a f`. -/
@[simp]
theorem OnOpenDisc.coe_taylorEquiv (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    (OnOpenDisc.taylorEquiv R ha f : R⟦X⟧) = PowerSeries.taylor a f :=
  (rfl)

/-- Translation by `0` is the identity automorphism. -/
@[simp]
theorem OnOpenDisc.taylorEquiv_zero (h : ‖(0 : R)‖ < R₀) :
    OnOpenDisc.taylorEquiv R h = RingEquiv.refl _ :=
  RingEquiv.ext fun f ↦ Subtype.ext (by simp)

/-- The inverse of the translation by `a` is the translation by `-a`. -/
@[simp]
theorem OnOpenDisc.taylorEquiv_symm (ha : ‖a‖ < R₀) :
    (OnOpenDisc.taylorEquiv R ha).symm =
      OnOpenDisc.taylorEquiv R (a := -a) (by rwa [norm_neg]) :=
  RingEquiv.ext fun _ ↦ (rfl)

/-- Translation by `a` followed by translation by `b` is translation by `b + a`. -/
@[simp]
theorem OnOpenDisc.taylorEquiv_trans (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀) :
    (OnOpenDisc.taylorEquiv R ha).trans (OnOpenDisc.taylorEquiv R hb) =
      OnOpenDisc.taylorEquiv R (a := b + a)
        ((IsUltrametricDist.norm_add_le_max b a).trans_lt (max_lt hb ha)) :=
  RingEquiv.ext fun f ↦ Subtype.ext ((OnOpenDisc.mem_subring.mp f.2).taylor_taylor ha hb)

/-- **Evaluation of a translate.** Evaluating the translate of a series on the open disc by `a`
at `b` is evaluating the series at `b + a`. -/
theorem OnOpenDisc.evalAtHom_taylorEquiv (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    OnOpenDisc.evalAtHom R hb (OnOpenDisc.taylorEquiv R ha f) =
      OnOpenDisc.evalAtHom R (b := b + a)
        ((IsUltrametricDist.norm_add_le_max b a).trans_lt (max_lt hb ha)) f := by
  simp only [OnOpenDisc.evalAtHom_apply, OnOpenDisc.coe_taylorEquiv]
  exact (OnOpenDisc.mem_subring.mp f.2).evalAt_taylor ha hb

omit [CompleteSpace R] in
/-- **Affine changes of coordinates.** If `f` lies on the open disc of radius `R₀`, `‖a‖ < R₀` and
`‖u‖ S₀ ≤ R₀`, then `f(a + uX)`, the rescaling by `u` of the translate of `f` by `a`, lies on the
open disc of radius `S₀`. -/
theorem OnOpenDisc.rescale_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) {u : R} {S₀ : ℝ}
    (hu : ‖u‖ * S₀ ≤ R₀) : (PowerSeries.rescale u (PowerSeries.taylor a f)).OnOpenDisc S₀ :=
  ((hf.taylor ha).mono hu).rescale

/-- **Evaluation after an affine change of coordinates.** If `f` lies on the open disc of radius
`R₀`, `‖a‖ < R₀` and `‖u‖ ‖b‖ < R₀`, then `f(a + uX)` takes the value `f(ub + a)` at `b`. -/
theorem OnOpenDisc.evalAt_rescale_taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) {u : R}
    (hub : ‖u‖ * ‖b‖ < R₀) :
    (PowerSeries.rescale u (PowerSeries.taylor a f)).evalAt b = f.evalAt (u * b + a) := by
  rw [evalAt_rescale, smul_eq_mul, hf.evalAt_taylor ha ((norm_mul_le u b).trans_lt hub)]

end PowerSeries

namespace TauCeti.PowerSeries.OnOpenDisc

open Filter _root_.PowerSeries
open scoped Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {R₀ : ℝ} {a : R}

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
attribute [local instance] radius_pos

/-- **Translation is continuous** for the topology of the Gauss norms at all radii below `R₀`:
at every radius between `‖a‖` and `R₀` it preserves the Gauss norm, and these radii are cofinal
among the radii below `R₀`. Its inverse is the translation by `-a`
(`PowerSeries.OnOpenDisc.taylorEquiv_symm`), so it is a homeomorphism. -/
theorem continuous_taylorEquiv (ha : ‖a‖ < R₀) :
    Continuous (OnOpenDisc.taylorEquiv R ha) := by
  -- the radii `max r s` with `‖a‖ < s < R₀` lie between `‖a‖` and `R₀` and are cofinal below `R₀`
  obtain ⟨ρ, hrρ, haρ⟩ : ∃ ρ : Set.Ioo (0 : ℝ) R₀ → Set.Ioo (0 : ℝ) R₀,
      (∀ r : Set.Ioo (0 : ℝ) R₀, (r : ℝ) ≤ ρ r) ∧ ∀ r, ‖a‖ ≤ ρ r := by
    obtain ⟨s, has, hsR⟩ := exists_between ha
    have hs : 0 < s := (norm_nonneg a).trans_lt has
    exact ⟨fun r ↦ ⟨max r s, hs.trans_le (le_max_right _ _), max_lt r.2.2 hsR⟩,
      fun r ↦ le_max_left _ _, fun r ↦ has.le.trans (le_max_right _ _)⟩
  refine continuous_of_continuousAt_zero (OnOpenDisc.taylorEquiv R ha) ?_
  rw [ContinuousAt, map_zero, tendsto_iff_of_cofinal_radius (ρ := ρ) fun r ↦ ⟨r, hrρ r⟩]
  intro r
  have h := (uniformContinuous_restrict (R := R) (ρ r)).continuous.tendsto 0
  rw [map_zero] at h ⊢
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  refine h.congr fun f ↦ ?_
  rw [TauCeti.PowerSeries.norm_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict,
    coe_restrict, OnOpenDisc.coe_taylorEquiv,
    (OnOpenDisc.mem_subring.mp f.2).gaussNorm_taylor (ρ r).2.1 (haρ r) (ρ r).2.2]

end TauCeti.PowerSeries.OnOpenDisc
