/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Perturbation
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Homotopy invariance of the spectral flow on a compactly embedded common domain

Let `ι : D →L H` be a compact operator from a Banach space into a Hilbert space and let
`G : ℝ → ℝ → (D →L H)` be a two-parameter family of operators, continuous on a rectangle
`[u, v] × [a, b]`, each symmetric through `ι` and with some invertible shift `c₀ ι - G s t`. This
file proves that the spectral flow `TauCeti.domainSpectralFlow` of the paths `G s`, as `t` runs
from `a` to `b`, is invariant under such homotopies, provided the endpoints `G s a` and `G s b`
either stay fixed or stay invertible as maps `D → H`.

The underlying statement is that the spectral flow around the boundary of the rectangle vanishes
(`TauCeti.domainSpectralFlow_add_domainSpectralFlow_eq_add`). On a small enough box a single real
shift `c ≠ 0` is admissible, by the Lebesgue number lemma, and there every side's spectral flow is
the bounded spectral flow of the shifted resolvent transforms at `c`. The bounded statement
`TauCeti.spectralFlow_add_spectralFlow_eq_add` then gives the identity on the box. Concatenation
of the spectral flow along the sides extends it first from boxes to thin horizontal strips and
then to the whole rectangle.

Homotopy invariance makes the spectral flow depend only on the homotopy class of the path
relative to its endpoints. This is what allows the path `A` in the index formula
`ind (∂ₛ - A) = -SF(A)` for the linearized Floer operator to be deformed into a normal form; that
formula is not proved here.

**Deformations bounded through `ι`.** The invertible shifts need only be given along one path
`G u` when the other paths differ from it by operators bounded through `ι`,
`‖(G s t - G u t) x‖ ≤ C ‖ι x‖`: a symmetric perturbation of this kind keeps an invertible shift
(`ContinuousLinearMap.exists_isInvertible_ofReal_smul_sub_of_norm_sub_apply_le`). For instance the
operators `J₀ ∂ₜ + S(t)` of the Floer equation differ by multiplication operators, bounded on `L²`.
Since the straight segment between two paths is such a deformation, the spectral flow of a path
with given endpoints `A a` and `A b` does not depend on the path, among those differing from it by
operators bounded through `ι` (`TauCeti.domainSpectralFlow_eq_of_norm_sub_apply_le`). This is the
counterpart of the fact that the index of the operator `∂ₛ + A` depends only on the limits of `A`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq`); together they reduce the index
formula to a single path for each pair of endpoints.

## Main results

* `TauCeti.domainSpectralFlow_add_domainSpectralFlow_eq_add`: the spectral flow around a
  rectangle vanishes.
* `TauCeti.domainSpectralFlow_eq_of_homotopy`: homotopy invariance with fixed endpoints.
* `TauCeti.domainSpectralFlow_eq_of_homotopy_of_isInvertible`: homotopy invariance with
  invertible endpoints.
* `TauCeti.domainSpectralFlow_eq_of_homotopy_of_norm_sub_apply_le`,
  `TauCeti.domainSpectralFlow_eq_of_homotopy_of_isInvertible_of_norm_sub_apply_le`: the same for
  deformations bounded through `ι`, with invertible shifts given along one path only.
* `TauCeti.domainSpectralFlow_eq_of_norm_sub_apply_le`: paths with the same endpoints, differing
  by operators bounded through `ι`, have the same spectral flow.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4.
* B. Booss-Bavnbek, M. Lesch and J. Phillips, *Unbounded Fredholm operators and spectral flow*,
  Canad. J. Math. **57** (2005), 225--250.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] {ι : D →L[𝕜] H} {G : ℝ → ℝ → D →L[𝕜] H} {u v a b : ℝ}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (hι : IsCompactOperator ι)
include hι

/-- The spectral flow around a box `[u, v] × [a, b]` along which a single shift `c ≠ 0` is
admissible vanishes: every side is the bounded spectral flow of the shifted resolvent transforms
at `c`. -/
private theorem domainSpectralFlow_add_domainSpectralFlow_eq_add_of_isInvertible {c : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫) (hc : c ≠ 0)
    (hinv : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ((c : 𝕜) • ι - G s t).IsInvertible) :
    domainSpectralFlow ι (G u) a b + domainSpectralFlow ι (fun s ↦ G s b) u v =
      domainSpectralFlow ι (fun s ↦ G s a) u v + domainSpectralFlow ι (G v) a b := by
  have hrow {s : ℝ} (hs : s ∈ Icc u v) :=
    domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform hι hab (hG.uncurry_left s hs)
      (hsymm s hs) hc (hinv s hs)
  have hcol {t : ℝ} (ht : t ∈ Icc a b) :=
    domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform hι huv (hG.uncurry_right t ht)
      (fun s hs ↦ hsymm s hs t ht) hc fun s hs ↦ hinv s hs t ht
  rw [hrow (left_mem_Icc.2 huv), hrow (right_mem_Icc.2 huv), hcol (left_mem_Icc.2 hab),
    hcol (right_mem_Icc.2 hab)]
  exact spectralFlow_add_spectralFlow_eq_add (G := fun s t ↦ ι.shiftedResolventTransform (G s t) c)
    hab huv (hG.shiftedResolventTransform fun z hz ↦ hinv z.1 hz.1 z.2 hz.2)
    (fun s hs t ht ↦ ι.isSelfAdjoint_shiftedResolventTransform (hsymm s hs t ht))
    fun s hs t ht ↦ ι.isFredholm_shiftedResolventTransform hι hc (hinv s hs t ht)

/-- The spectral flow around a rectangle `[u, v] × [a, b]` vanishes if near every `t₀ ∈ [a, b]` a
single shift `c ≠ 0` is admissible across the whole width `[u, v]`. The boxes over the subintervals
of `[a, b]` of length less than `δ` are glued by concatenating the horizontal sides. -/
private theorem domainSpectralFlow_add_domainSpectralFlow_eq_add_of_forall_exists {δ : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫) (hδ : 0 < δ)
    (hloc : ∀ t₀ ∈ Icc a b, ∃ c : ℝ, c ≠ 0 ∧ ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, |t - t₀| < δ →
      ((c : 𝕜) • ι - G s t).IsInvertible) :
    domainSpectralFlow ι (G u) a b + domainSpectralFlow ι (fun s ↦ G s b) u v =
      domainSpectralFlow ι (fun s ↦ G s a) u v + domainSpectralFlow ι (G v) a b := by
  -- Concatenation of the horizontal sides at heights `u` and `v`.
  have hrow {s : ℝ} (hs : s ∈ Icc u v) {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      domainSpectralFlow ι (G s) a y =
        domainSpectralFlow ι (G s) a x + domainSpectralFlow ι (G s) x y := by
    have hsub : Icc a y ⊆ Icc a b := Icc_subset_Icc le_rfl hyb
    refine domainSpectralFlow_add_adjacent_intervals hι hax hxy ((hG.uncurry_left s hs).mono hsub)
      (fun t ht ↦ hsymm s hs t (hsub ht)) fun t ht ↦ ?_
    obtain ⟨c, -, hinv⟩ := hloc t (hsub ht)
    exact ⟨c, hinv s hs t (hsub ht) (by simpa using hδ)⟩
  -- The box over an interval `[x, y]` of length less than `δ`, with a shift admissible near `x`.
  have hbox {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) (hlt : y - x < δ) :
      domainSpectralFlow ι (G u) x y + domainSpectralFlow ι (fun s ↦ G s y) u v =
        domainSpectralFlow ι (fun s ↦ G s x) u v + domainSpectralFlow ι (G v) x y := by
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hax hyb
    obtain ⟨c, hc, hinv⟩ := hloc x ⟨hax, hxy.trans hyb⟩
    refine domainSpectralFlow_add_domainSpectralFlow_eq_add_of_isInvertible hι hxy huv
      (hG.mono (prod_mono subset_rfl hsub)) (fun s hs t ht ↦ hsymm s hs t (hsub ht)) hc
      fun s hs t ht ↦ hinv s hs t (hsub ht) ?_
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  -- `Φ y` is the defect of the identity over `[u, v] × [a, y]`; it is unchanged across short
  -- subintervals.
  set Φ : ℝ → ℤ := fun y ↦ domainSpectralFlow ι (G u) a y +
    domainSpectralFlow ι (fun s ↦ G s y) u v - domainSpectralFlow ι (fun s ↦ G s a) u v -
      domainSpectralFlow ι (G v) a y
  have hu : u ∈ Icc u v := left_mem_Icc.2 huv
  have hv : v ∈ Icc u v := right_mem_Icc.2 huv
  have := apply_eq_of_forall_sub_lt (f := Φ) hab hδ fun p q hap hpq hqb hlt ↦ by
    have := hbox hap hpq hqb hlt
    simp only [Φ, hrow hu hap hpq hqb, hrow hv hap hpq hqb]
    linarith
  simp only [Φ, domainSpectralFlow_self] at this
  linarith

/-- **The spectral flow around a rectangle vanishes.** For a continuous two-parameter family
`G s t` of operators on `[u, v] × [a, b]`, symmetric through a compact `ι` and each with some
invertible shift, the spectral flow along the bottom side `G u` followed by the right side
`s ↦ G s b` equals the spectral flow along the left side `s ↦ G s a` followed by the top side
`G v`. -/
theorem domainSpectralFlow_add_domainSpectralFlow_eq_add (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫)
    (h₀ : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G s t).IsInvertible) :
    domainSpectralFlow ι (G u) a b + domainSpectralFlow ι (fun s ↦ G s b) u v =
      domainSpectralFlow ι (fun s ↦ G s a) u v + domainSpectralFlow ι (G v) a b := by
  -- A Lebesgue number `δ` for admissible shifts on the rectangle.
  obtain ⟨δ, hδ, hloc⟩ := ι.exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub hι
    (isCompact_Icc.prod isCompact_Icc) hG (fun z hz ↦ h₀ z.1 hz.1 z.2 hz.2) zero_lt_one
  -- The identity over a strip `[p, q] × [a, b]` of width less than `δ`.
  have hstrip {p q : ℝ} (hup : u ≤ p) (hpq : p ≤ q) (hqv : q ≤ v) (hw : q - p < δ) :
      domainSpectralFlow ι (G p) a b + domainSpectralFlow ι (fun s ↦ G s b) p q =
        domainSpectralFlow ι (fun s ↦ G s a) p q + domainSpectralFlow ι (G q) a b := by
    have hsub : Icc p q ⊆ Icc u v := Icc_subset_Icc hup hqv
    refine domainSpectralFlow_add_domainSpectralFlow_eq_add_of_forall_exists hι hab hpq
      (hG.mono (prod_mono hsub subset_rfl)) (fun s hs ↦ hsymm s (hsub hs)) hδ fun t₀ ht₀ ↦ ?_
    obtain ⟨c, hc, hinv⟩ := hloc (p, t₀) ⟨⟨hup, hpq.trans hqv⟩, ht₀⟩
    refine ⟨c, hc.1.ne', fun s hs t ht htt₀ ↦ hinv (s, t) ⟨hsub hs, ht⟩ ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
    exact max_lt (by linarith [hs.2]) htt₀
  -- Concatenation of the vertical sides at `a` and `b`.
  have hcol {t : ℝ} (ht : t ∈ Icc a b) {p q : ℝ} (hup : u ≤ p) (hpq : p ≤ q) (hqv : q ≤ v) :
      domainSpectralFlow ι (fun s ↦ G s t) u q =
        domainSpectralFlow ι (fun s ↦ G s t) u p + domainSpectralFlow ι (fun s ↦ G s t) p q := by
    have hsub : Icc u q ⊆ Icc u v := Icc_subset_Icc le_rfl hqv
    exact domainSpectralFlow_add_adjacent_intervals hι hup hpq
      ((hG.uncurry_right t ht).mono hsub) (fun s hs ↦ hsymm s (hsub hs) t ht)
      fun s hs ↦ h₀ s (hsub hs) t ht
  -- `Θ q` is the defect of the identity over `[u, q] × [a, b]`; it is unchanged across short
  -- subintervals.
  set Θ : ℝ → ℤ := fun q ↦ domainSpectralFlow ι (G u) a b +
    domainSpectralFlow ι (fun s ↦ G s b) u q - domainSpectralFlow ι (fun s ↦ G s a) u q -
      domainSpectralFlow ι (G q) a b
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  have := apply_eq_of_forall_sub_lt (f := Θ) huv hδ fun p q hup hpq hqv hlt ↦ by
    have := hstrip hup hpq hqv hlt
    simp only [Θ, hcol ha hup hpq hqv, hcol hb hup hpq hqv]
    linarith
  simp only [Θ, domainSpectralFlow_self] at this
  linarith

/-- **Homotopy invariance of the spectral flow.** Two continuous paths of operators on `[a, b]`,
symmetric through a compact `ι` and each with some invertible shift, joined by a continuous family
`G` of such paths over `[u, v]` whose endpoints `G s a` and `G s b` do not move, have the same
spectral flow. -/
theorem domainSpectralFlow_eq_of_homotopy (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫)
    (h₀ : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G s t).IsInvertible)
    (ha : ∀ s ∈ Icc u v, G s a = G u a) (hb : ∀ s ∈ Icc u v, G s b = G u b) :
    domainSpectralFlow ι (G v) a b = domainSpectralFlow ι (G u) a b := by
  have hu : u ∈ Icc u v := left_mem_Icc.2 huv
  have ha' : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb' : b ∈ Icc a b := right_mem_Icc.2 hab
  have := domainSpectralFlow_add_domainSpectralFlow_eq_add hι hab huv hG hsymm h₀
  rw [domainSpectralFlow_eq_zero_of_forall_eq hι huv (hsymm u hu a ha') (h₀ u hu a ha') ha,
    domainSpectralFlow_eq_zero_of_forall_eq hι huv (hsymm u hu b hb') (h₀ u hu b hb') hb] at this
  linarith

/-- **Homotopy invariance with invertible endpoints.** Two continuous paths of operators on
`[a, b]`, symmetric through a compact `ι` and each with some invertible shift, joined by a
continuous family `G` of such paths over `[u, v]` whose endpoints `G s a` and `G s b` stay
invertible as maps `D → H`, have the same spectral flow. -/
theorem domainSpectralFlow_eq_of_homotopy_of_isInvertible (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫)
    (h₀ : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G s t).IsInvertible)
    (ha : ∀ s ∈ Icc u v, (G s a).IsInvertible) (hb : ∀ s ∈ Icc u v, (G s b).IsInvertible) :
    domainSpectralFlow ι (G v) a b = domainSpectralFlow ι (G u) a b := by
  have ha' : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb' : b ∈ Icc a b := right_mem_Icc.2 hab
  have := domainSpectralFlow_add_domainSpectralFlow_eq_add hι hab huv hG hsymm h₀
  rw [domainSpectralFlow_eq_zero_of_forall_isInvertible hι huv (hG.uncurry_right a ha')
      (fun s hs ↦ hsymm s hs a ha') ha,
    domainSpectralFlow_eq_zero_of_forall_isInvertible hι huv (hG.uncurry_right b hb')
      (fun s hs ↦ hsymm s hs b hb') hb] at this
  linarith

/-! ### Deformations bounded through `ι` -/

omit [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Paths symmetric through `ι` and differing from a path `G u` with invertible shifts by operators
bounded through `ι` have invertible shifts. -/
private theorem forall_exists_isInvertible_smul_sub_of_norm_sub_apply_le
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G u t).IsInvertible)
    (hbdd : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ C, ∀ x, ‖(G s t - G u t) x‖ ≤ C * ‖ι x‖) :
    ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G s t).IsInvertible := fun s hs t ht ↦ by
  obtain ⟨c₀, hc₀⟩ := h₀ t ht
  obtain ⟨C, hC⟩ := hbdd s hs t ht
  obtain ⟨c, hc⟩ := ι.exists_isInvertible_ofReal_smul_sub_of_norm_sub_apply_le hι hc₀
    (hsymm s hs t ht) hC
  exact ⟨c, hc⟩

/-- **Homotopy invariance under deformations bounded through `ι`.** Let `G` be a continuous family
over `[u, v]` of paths of operators on `[a, b]`, symmetric through a compact `ι`, whose endpoints
`G s a` and `G s b` do not move. If every `G u t` has some invertible shift and every `G s t`
differs from `G u t` by an operator bounded through `ι`, then `G v` and `G u` have the same spectral
flow. -/
theorem domainSpectralFlow_eq_of_homotopy_of_norm_sub_apply_le (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G u t).IsInvertible)
    (hbdd : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ C, ∀ x, ‖(G s t - G u t) x‖ ≤ C * ‖ι x‖)
    (ha : ∀ s ∈ Icc u v, G s a = G u a) (hb : ∀ s ∈ Icc u v, G s b = G u b) :
    domainSpectralFlow ι (G v) a b = domainSpectralFlow ι (G u) a b :=
  domainSpectralFlow_eq_of_homotopy hι hab huv hG hsymm
    (forall_exists_isInvertible_smul_sub_of_norm_sub_apply_le hι hsymm h₀ hbdd) ha hb

/-- **Homotopy invariance with invertible endpoints, under deformations bounded through `ι`.** Let
`G` be a continuous family over `[u, v]` of paths of operators on `[a, b]`, symmetric through a
compact `ι`, whose endpoints `G s a` and `G s b` stay invertible as maps `D → H`. If every `G u t`
has some invertible shift and every `G s t` differs from `G u t` by an operator bounded through
`ι`, then `G v` and `G u` have the same spectral flow. -/
theorem domainSpectralFlow_eq_of_homotopy_of_isInvertible_of_norm_sub_apply_le (hab : a ≤ b)
    (huv : u ≤ v) (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsymm : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - G u t).IsInvertible)
    (hbdd : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, ∃ C, ∀ x, ‖(G s t - G u t) x‖ ≤ C * ‖ι x‖)
    (ha : ∀ s ∈ Icc u v, (G s a).IsInvertible) (hb : ∀ s ∈ Icc u v, (G s b).IsInvertible) :
    domainSpectralFlow ι (G v) a b = domainSpectralFlow ι (G u) a b :=
  domainSpectralFlow_eq_of_homotopy_of_isInvertible hι hab huv hG hsymm
    (forall_exists_isInvertible_smul_sub_of_norm_sub_apply_le hι hsymm h₀ hbdd) ha hb

/-- **The spectral flow depends only on the endpoints.** Let `A` and `A'` be continuous paths of
operators on `[a, b]`, symmetric through a compact `ι`, with the same endpoints `A' a = A a` and
`A' b = A b`. If every `A t` has some invertible shift and every `A' t` differs from `A t` by an
operator bounded through `ι`, then `A` and `A'` have the same spectral flow. -/
theorem domainSpectralFlow_eq_of_norm_sub_apply_le {A A' : ℝ → D →L[𝕜] H} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hA' : ContinuousOn A' (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (hsymm' : ∀ t ∈ Icc a b, ∀ x y, ⟪A' t x, ι y⟫ = ⟪ι x, A' t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible)
    (hbdd : ∀ t ∈ Icc a b, ∃ C, ∀ x, ‖(A' t - A t) x‖ ≤ C * ‖ι x‖) (ha : A' a = A a)
    (hb : A' b = A b) : domainSpectralFlow ι A' a b = domainSpectralFlow ι A a b := by
  -- Deform `A` into `A'` along the straight segment `A t + s (A' t - A t)`, `s ∈ [0, 1]`.
  set G : ℝ → ℝ → D →L[𝕜] H := fun s t ↦ A t + (s : 𝕜) • (A' t - A t)
  have hG0 : G 0 = A := funext fun t ↦ by simp [G]
  have hG1 : G 1 = A' := funext fun t ↦ by simp [G]
  have hGc : ContinuousOn (Function.uncurry G) (Icc 0 1 ×ˢ Icc a b) := by
    have hA₂ : ContinuousOn (fun p : ℝ × ℝ ↦ A p.2) (Icc 0 1 ×ˢ Icc a b) :=
      hA.comp continuousOn_snd fun _ hp ↦ hp.2
    have hA'₂ : ContinuousOn (fun p : ℝ × ℝ ↦ A' p.2) (Icc 0 1 ×ˢ Icc a b) :=
      hA'.comp continuousOn_snd fun _ hp ↦ hp.2
    have hs : ContinuousOn (fun p : ℝ × ℝ ↦ ((p.1 : ℝ) : 𝕜)) (Icc 0 1 ×ˢ Icc a b) := by fun_prop
    exact (hA₂.add (hs.smul (hA'₂.sub hA₂))).congr fun _ _ ↦ rfl
  have hGsymm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ x y, ⟪G s t x, ι y⟫ = ⟪ι x, G s t y⟫ :=
    fun s _ t ht x y ↦ by
      simp only [G, add_apply, smul_apply, sub_apply, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, RCLike.conj_ofReal,
        hsymm t ht, hsymm' t ht]
  have hGbdd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∃ C, ∀ x, ‖(G s t - G 0 t) x‖ ≤ C * ‖ι x‖ := by
    intro s _ t ht
    obtain ⟨C, hC⟩ := hbdd t ht
    refine ⟨|s| * C, fun x ↦ ?_⟩
    rw [hG0]
    simp only [G, add_sub_cancel_left, smul_apply, norm_smul, RCLike.norm_ofReal, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg s)
  have h := domainSpectralFlow_eq_of_homotopy_of_norm_sub_apply_le hι hab zero_le_one hGc hGsymm
    (by rwa [hG0]) hGbdd (fun s _ ↦ by simp [G, ha]) (fun s _ ↦ by simp [G, hb])
  rwa [hG0, hG1] at h

end TauCeti
