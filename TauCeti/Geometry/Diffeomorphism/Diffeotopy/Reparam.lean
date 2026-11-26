/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homotopy
public import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# Time reparametrization, reversal and concatenation of diffeotopies

The operations `TauCeti.Diffeotopy.trans` and `TauCeti.Diffeotopy.symm` act on diffeotopies
pointwise in time: `Φ.trans Ψ` has time slices `ψ_t ∘ φ_t` and `Φ.symm` has time slices `φ_t⁻¹`.
This file constructs the *temporal* operations, which act on the time variable instead.

* **Reparametrization.** For a `C^n` map `ρ` of the unit interval, `Φ.reparam ρ` has time slices
  `φ_{ρ t} ∘ φ_{ρ 0}⁻¹`. Composing with `φ_{ρ 0}⁻¹` makes it start at the identity; when
  `ρ 0 = 0` its slices are just `φ_{ρ t}`. Reparametrizations compose:
  `(Φ.reparam ρ).reparam ρ' = Φ.reparam (ρ ∘ ρ')`.
* **Time reversal.** `Φ.reverse` is the reparametrization by `t ↦ 1 - t`, with time slices
  `φ_{1 - t} ∘ φ₁⁻¹`. It runs from the identity to `φ₁⁻¹` backwards along the motion of `Φ`, and
  `Φ.reverse.reverse = Φ`.
* **Concatenation.** `Φ.concat Ψ hn` first runs through `Φ` and then through `Ψ` after `φ₁`: its
  time slices are `φ_{a t}` for `t ≤ 1 / 2` and `ψ_{b t} ∘ φ₁` for `1 / 2 ≤ t`, where `a` and `b`
  are smooth transitions which are constant near the ends and the middle of the interval. It is the
  pointwise composite `(Φ.reparam a).trans (Ψ.reparam b)` of two reparametrizations with disjoint
  time supports, so it is `C^n` without any collar hypothesis on `Φ` or `Ψ`. Its final
  diffeomorphism is `ψ₁ ∘ φ₁`, the final diffeomorphism of `Φ.trans Ψ`.

A diffeotopy is **collared** (`TauCeti.Diffeotopy.IsCollared`) when it is stationary on
neighbourhoods of both time ends. Native diffeotopies carry no collar data, so collared ones form a
separately specified subclass. It is closed under `trans`, `symm` and `reverse`, and every
concatenation is collared, whether or not its two factors are.

The temporal operations agree with the pointwise ones up to homotopy through diffeotopies fixing
both time ends (`TauCeti.Diffeotopy.Homotopic`). A reparametrization fixing both ends of the
interval is homotopic to the original diffeotopy, through the straight-line homotopy of time maps.
Hence the concatenation of `Φ` and `Ψ` is homotopic to `Φ.trans Ψ`, and the reversal of `Φ` is
homotopic to `Φ.symm`, through `((x, t), s) ↦ φ_{(1 - s)(1 - t)} (φ_{(1 - s) + s t}⁻¹ x)`. So on
homotopy classes concatenation is the pointwise product and reversal is the inverse, and both
respect homotopy.

## Main definitions

* `TauCeti.Diffeotopy.reparam`: the time reparametrization `t ↦ φ_{ρ t} ∘ φ_{ρ 0}⁻¹`.
* `TauCeti.Diffeotopy.reverse`: the time reversal `t ↦ φ_{1 - t} ∘ φ₁⁻¹`.
* `TauCeti.Diffeotopy.concat`: the smooth concatenation of two diffeotopies.
* `TauCeti.Diffeotopy.IsCollared`: stationarity near both time ends.

## Main results

* `TauCeti.Diffeotopy.reparam_reparam`, `reparam_id`: reparametrizations compose.
* `TauCeti.Diffeotopy.final_reverse`, `reverse_reverse`: reversal ends at `φ₁⁻¹` and is
  involutive.
* `TauCeti.Diffeotopy.concat_apply_of_le`, `concat_apply_of_ge`: the two halves of a
  concatenation.
* `TauCeti.Diffeotopy.final_concat`: a concatenation ends at `ψ₁ ∘ φ₁`.
* `TauCeti.Diffeotopy.isCollared_concat`: every concatenation is collared.
* `TauCeti.Diffeotopy.reparam_homotopic`: a reparametrization fixing both ends is homotopic to
  the original diffeotopy.
* `TauCeti.Diffeotopy.exists_homotopic_timeSlice_eq_comp`: every diffeotopy is homotopic to one
  whose time slices are those of a jointly smooth real-time family.
* `TauCeti.Diffeotopy.concat_homotopic_trans`, `reverse_homotopic_symm`: the path-class laws of
  concatenation and reversal.
* `TauCeti.Diffeotopy.concat_reverse_homotopic_refl`: reversal inverts concatenation up to
  homotopy.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for the
  stationary-time reparametrization of isotopies.
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2, for paths of symplectomorphisms and their concatenation.
-/

public section

noncomputable section

namespace TauCeti

namespace Diffeotopy

open unitInterval Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (Φ Ψ : Diffeotopy J n M)

/-! ### Reparametrization -/

/-- **Reparametrize a diffeotopy in time** by a `C^n` map `ρ` of the unit interval: the time-`t`
slice is `φ_{ρ t} ∘ φ_{ρ 0}⁻¹`. The map `ρ` need not fix either end of the interval, nor be
monotone; composing with `φ_{ρ 0}⁻¹` makes the result start at the identity. -/
def reparam (ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯) : Diffeotopy J n M where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, Φ (ρ p.1, Φ.symm (ρ 0, p.2)))
      invFun := fun p ↦ (p.1, Φ (ρ 0, Φ.symm (ρ p.1, p.2)))
      left_inv := fun p ↦ by simp only [symm_apply_apply_mk, apply_symm_apply_mk]
      right_inv := fun p ↦ by simp only [symm_apply_apply_mk, apply_symm_apply_mk]
      contMDiff_toFun := contMDiff_fst.prodMk (Φ.contMDiff.comp
        ((ρ.contMDiff.comp contMDiff_fst).prodMk
          (Φ.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_snd))))
      contMDiff_invFun := contMDiff_fst.prodMk (Φ.contMDiff.comp
        (contMDiff_const.prodMk
          (Φ.symm.contMDiff.comp ((ρ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)))) }
  fst_apply _ := rfl
  snd_apply_zero' x := Φ.apply_symm_apply_mk (ρ 0) x

/-- The reparametrized diffeotopy at `(t, x)` is `φ_{ρ t} (φ_{ρ 0}⁻¹ x)`. -/
@[simp]
theorem reparam_apply (ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯) (p : I × M) :
    Φ.reparam ρ p = Φ (ρ p.1, Φ.symm (ρ 0, p.2)) :=
  (rfl)

/-- The inverse of the reparametrized diffeotopy at `(t, x)` is `φ_{ρ 0} (φ_{ρ t}⁻¹ x)`. -/
theorem symm_reparam_apply (ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯) (p : I × M) :
    (Φ.reparam ρ).symm p = Φ (ρ 0, Φ.symm (ρ p.1, p.2)) := by
  -- The inverse of the total diffeomorphism of `Φ.reparam ρ` is its `invFun` field.
  rw [symm_apply]
  rfl

/-- When `ρ 0 = 0`, the reparametrized diffeotopy at `(t, x)` is `φ_{ρ t} x`. -/
theorem reparam_apply_of_map_zero {ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯} (h₀ : ρ 0 = 0) (p : I × M) :
    Φ.reparam ρ p = Φ (ρ p.1, p.2) := by
  rw [reparam_apply, h₀, Φ.symm.apply_zero]

/-- The time slices of a reparametrized diffeotopy are `φ_{ρ t} ∘ φ_{ρ 0}⁻¹`. -/
theorem timeSlice_reparam (ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯) (t : I) :
    (Φ.reparam ρ).timeSlice t = (Φ.timeSlice (ρ 0)).symm.trans (Φ.timeSlice (ρ t)) :=
  _root_.Diffeomorph.ext fun x ↦ by simp

/-- The final diffeomorphism of a reparametrized diffeotopy is `φ_{ρ 1} ∘ φ_{ρ 0}⁻¹`. -/
theorem final_reparam (ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯) :
    (Φ.reparam ρ).final = (Φ.timeSlice (ρ 0)).symm.trans (Φ.timeSlice (ρ 1)) := by
  rw [final_def, timeSlice_reparam]

/-- Reparametrizing by the identity does nothing. -/
@[simp]
theorem reparam_id : Φ.reparam ContMDiffMap.id = Φ :=
  ext fun p ↦ Φ.reparam_apply_of_map_zero rfl p

/-- Reparametrizing by a constant map gives the constant diffeotopy. -/
@[simp]
theorem reparam_const (c : I) : Φ.reparam (ContMDiffMap.const c) = refl J n M :=
  ext fun p ↦ by
    rw [reparam_apply, refl_apply]
    exact Φ.apply_symm_apply_mk c p.2

/-- **Reparametrizations compose.** Reparametrizing by `ρ` and then by `ρ'` is reparametrizing by
`ρ ∘ ρ'`. -/
theorem reparam_reparam (ρ ρ' : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯) :
    (Φ.reparam ρ).reparam ρ' = Φ.reparam (ρ.comp ρ') := by
  refine ext fun p ↦ ?_
  rw [reparam_apply, reparam_apply, reparam_apply, symm_reparam_apply, symm_apply_apply_mk,
    ContMDiffMap.comp_apply, ContMDiffMap.comp_apply]

/-- Reparametrizing by a map fixing `0` commutes with pointwise composition. -/
theorem reparam_trans {ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯} (h₀ : ρ 0 = 0) :
    (Φ.trans Ψ).reparam ρ = (Φ.reparam ρ).trans (Ψ.reparam ρ) :=
  ext fun p ↦ by
    rw [reparam_apply_of_map_zero _ h₀, trans_apply, trans_apply, reparam_apply_of_map_zero _ h₀,
      reparam_apply_of_map_zero _ h₀]

/-- Reparametrizing by a map fixing `0` commutes with pointwise inversion. -/
theorem reparam_symm {ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯} (h₀ : ρ 0 = 0) :
    Φ.symm.reparam ρ = (Φ.reparam ρ).symm :=
  ext fun p ↦ by
    rw [reparam_apply_of_map_zero _ h₀, ← symm_timeSlice_apply, ← symm_timeSlice_apply,
      timeSlice_reparam, h₀, timeSlice_zero]
    simp

/-! ### Time reversal -/

/-- **Time reversal** of a diffeotopy: the time-`t` slice is `φ_{1 - t} ∘ φ₁⁻¹`. It runs backwards
along the motion of `Φ`, from the identity to `φ₁⁻¹`. This is the reparametrization by
`t ↦ 1 - t`, and differs from the pointwise inverse `Φ.symm`, whose slices are `φ_t⁻¹`. -/
def reverse : Diffeotopy J n M :=
  Φ.reparam ⟨σ, contMDiff_symm⟩

/-- The time reversal is the reparametrization by `t ↦ 1 - t`. -/
theorem reverse_def : Φ.reverse = Φ.reparam ⟨σ, contMDiff_symm⟩ :=
  (rfl)

/-- The reversed diffeotopy at `(t, x)` is `φ_{1 - t} (φ₁⁻¹ x)`. -/
@[simp]
theorem reverse_apply (p : I × M) : Φ.reverse p = Φ (σ p.1, Φ.symm (1, p.2)) := by
  rw [reverse_def, Φ.reparam_apply ⟨σ, contMDiff_symm⟩, ContMDiffMap.coeFn_mk, symm_zero]

/-- The inverse of the reversed diffeotopy at `(t, x)` is `φ₁ (φ_{1 - t}⁻¹ x)`. -/
theorem symm_reverse_apply (p : I × M) : Φ.reverse.symm p = Φ (1, Φ.symm (σ p.1, p.2)) := by
  rw [reverse_def, Φ.symm_reparam_apply ⟨σ, contMDiff_symm⟩, ContMDiffMap.coeFn_mk, symm_zero]

/-- The time slices of the reversed diffeotopy are `φ_{1 - t} ∘ φ₁⁻¹`. -/
theorem timeSlice_reverse (t : I) :
    Φ.reverse.timeSlice t = Φ.final.symm.trans (Φ.timeSlice (σ t)) :=
  _root_.Diffeomorph.ext fun x ↦ by simp [final_def]

/-- The reversed diffeotopy ends at the inverse final diffeomorphism. -/
@[simp]
theorem final_reverse : Φ.reverse.final = Φ.final.symm :=
  _root_.Diffeomorph.ext fun x ↦ by
    rw [final_apply, reverse_apply, symm_one, apply_zero, ← symm_timeSlice_apply, final_def]

/-- Time reversal is an involution. -/
@[simp]
theorem reverse_reverse : Φ.reverse.reverse = Φ :=
  ext fun p ↦ by
    simp only [reverse_apply, symm_reverse_apply, symm_apply_apply_mk, symm_one, apply_zero,
      unitInterval.symm_symm]

/-- The reversal of the constant diffeotopy is constant. -/
@[simp]
theorem reverse_refl : (refl J n M).reverse = refl J n M :=
  ext fun p ↦ by
    simp only [reverse_apply, refl_apply, ← symm_timeSlice_apply, timeSlice_refl,
      _root_.Diffeomorph.symm_refl, _root_.Diffeomorph.coe_refl, id_eq]

/-! ### Concatenation -/

/-- **Concatenation** of diffeotopies: run through `Φ` and then through `Ψ` after `φ₁`. On
`[0, 1 / 2]` the time-`t` slice is `φ_{a t}`, and on `[1 / 2, 1]` it is `ψ_{b t} ∘ φ₁`, for the
smooth transitions `a = TauCeti.collaredFirstHalf hn` and `b = TauCeti.collaredSecondHalf hn`, so
`a t = collaredSmoothTransitionUnit (2 t)` and `b t = collaredSmoothTransitionUnit (2 t - 1)`.
These are constant near both ends and near the middle of the interval, so the concatenation is
`C^n` and collared (`isCollared_concat`) without any hypothesis on `Φ` and `Ψ`. It is the
pointwise composite of the two reparametrizations. -/
def concat (hn : n ≤ ∞) : Diffeotopy J n M :=
  (Φ.reparam (collaredFirstHalf hn)).trans (Ψ.reparam (collaredSecondHalf hn))

/-- The concatenation is the pointwise composite of the reparametrizations of `Φ` and `Ψ` by the
two collared half-interval time maps. -/
theorem concat_def (hn : n ≤ ∞) :
    Φ.concat Ψ hn = (Φ.reparam (collaredFirstHalf hn)).trans (Ψ.reparam (collaredSecondHalf hn)) :=
  (rfl)

/-- The concatenation at `(t, x)` is `ψ_{b t} (φ_{a t} x)`, where `a` and `b` are the two time
maps of the concatenation. -/
theorem concat_apply (hn : n ≤ ∞) (p : I × M) :
    Φ.concat Ψ hn p = Ψ (collaredSmoothTransitionUnit (2 * p.1 - 1),
      Φ (collaredSmoothTransitionUnit (2 * p.1), p.2)) := by
  rw [concat_def, trans_apply, reparam_apply_of_map_zero _ (collaredFirstHalf_zero hn),
    reparam_apply_of_map_zero _ (collaredSecondHalf_zero hn), collaredFirstHalf_apply,
    collaredSecondHalf_apply]

/-- On the first half of the interval the concatenation runs through `Φ`. -/
theorem concat_apply_of_le (hn : n ≤ ∞) {t : I} (ht : (t : ℝ) ≤ 1 / 2) (x : M) :
    Φ.concat Ψ hn (t, x) = Φ (collaredSmoothTransitionUnit (2 * t), x) := by
  rw [concat_apply, collaredSmoothTransitionUnit_eq_zero_of_le (by linarith), apply_zero]

/-- On the second half of the interval the concatenation runs through `Ψ` after `φ₁`. -/
theorem concat_apply_of_ge (hn : n ≤ ∞) {t : I} (ht : 1 / 2 ≤ (t : ℝ)) (x : M) :
    Φ.concat Ψ hn (t, x) = Ψ (collaredSmoothTransitionUnit (2 * t - 1), Φ.final x) := by
  rw [concat_apply, collaredSmoothTransitionUnit_eq_one_of_ge (t := 2 * (t : ℝ)) (by linarith),
    final_apply]

/-- The concatenation ends at `ψ₁ ∘ φ₁`, the final diffeomorphism of the pointwise composite. -/
@[simp]
theorem final_concat (hn : n ≤ ∞) : (Φ.concat Ψ hn).final = Φ.final.trans Ψ.final :=
  _root_.Diffeomorph.ext fun x ↦ by
    rw [final_apply, concat_apply_of_ge _ _ _ (by norm_num), Set.Icc.coe_one,
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num), _root_.Diffeomorph.coe_trans,
      Function.comp_apply, final_apply, final_apply]

/-! ### Collared diffeotopies -/

/-- A diffeotopy is **collared** when it is stationary on a neighbourhood of each time end: its
time slices are the identity for all times near `0` and the final diffeomorphism for all times
near `1`. -/
structure IsCollared : Prop where
  /-- The time slices are the identity near time `0`. -/
  eventually_zero : ∀ᶠ t in 𝓝 (0 : I), Φ.timeSlice t = _root_.Diffeomorph.refl J M n
  /-- The time slices are the final diffeomorphism near time `1`. -/
  eventually_one : ∀ᶠ t in 𝓝 (1 : I), Φ.timeSlice t = Φ.final

variable {Φ Ψ}

/-- The constant diffeotopy is collared. -/
theorem isCollared_refl : (refl J n M).IsCollared :=
  ⟨by simp, by simp⟩

/-- The pointwise composite of collared diffeotopies is collared. -/
theorem IsCollared.trans (hΦ : Φ.IsCollared) (hΨ : Ψ.IsCollared) : (Φ.trans Ψ).IsCollared where
  eventually_zero := (hΦ.eventually_zero.and hΨ.eventually_zero).mono fun t ht ↦ by
    rw [timeSlice_trans, ht.1, ht.2, _root_.Diffeomorph.refl_trans]
  eventually_one := (hΦ.eventually_one.and hΨ.eventually_one).mono fun t ht ↦ by
    rw [timeSlice_trans, ht.1, ht.2, final_trans]

/-- The pointwise inverse of a collared diffeotopy is collared. -/
theorem IsCollared.symm (hΦ : Φ.IsCollared) : Φ.symm.IsCollared where
  eventually_zero := hΦ.eventually_zero.mono fun t ht ↦ by
    rw [timeSlice_symm, ht, _root_.Diffeomorph.symm_refl]
  eventually_one := hΦ.eventually_one.mono fun t ht ↦ by rw [timeSlice_symm, ht, final_symm]

/-- A reparametrization of a diffeotopy is collared exactly when the reparametrized slices
`φ_{ρ t}` are constant for `t` near each end of the interval. -/
theorem isCollared_reparam_iff {ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯} :
    (Φ.reparam ρ).IsCollared ↔ (∀ᶠ t in 𝓝 (0 : I), Φ.timeSlice (ρ t) = Φ.timeSlice (ρ 0)) ∧
      ∀ᶠ t in 𝓝 (1 : I), Φ.timeSlice (ρ t) = Φ.timeSlice (ρ 1) := by
  -- Both conditions say that `φ_{ρ 0}⁻¹ ∘ φ_{ρ t}` is eventually constant, and composition
  -- with `φ_{ρ 0}⁻¹` is injective.
  have key (t s : I) : (Φ.reparam ρ).timeSlice t = (Φ.reparam ρ).timeSlice s ↔
      Φ.timeSlice (ρ t) = Φ.timeSlice (ρ s) := by
    rw [timeSlice_reparam, timeSlice_reparam]
    refine ⟨fun h ↦ _root_.Diffeomorph.ext fun x ↦ ?_, fun h ↦ by rw [h]⟩
    have h' := DFunLike.congr_fun h (Φ.timeSlice (ρ 0) x)
    simpa only [_root_.Diffeomorph.coe_trans, Function.comp_apply,
      _root_.Diffeomorph.symm_apply_apply] using h'
  have h₀ : (Φ.reparam ρ).timeSlice 0 = _root_.Diffeomorph.refl J M n := timeSlice_zero _
  constructor
  · rintro ⟨hz, ho⟩
    exact ⟨hz.mono fun t ht ↦ (key t 0).mp (ht.trans h₀.symm),
      ho.mono fun t ht ↦ (key t 1).mp (ht.trans (final_def _))⟩
  · rintro ⟨hz, ho⟩
    exact ⟨hz.mono fun t ht ↦ ((key t 0).mpr ht).trans h₀,
      ho.mono fun t ht ↦ ((key t 1).mpr ht).trans (final_def _).symm⟩

/-- The reversal of a collared diffeotopy is collared. -/
theorem IsCollared.reverse (hΦ : Φ.IsCollared) : Φ.reverse.IsCollared := by
  have hσ₀ : Tendsto σ (𝓝 (0 : I)) (𝓝 1) := by
    simpa only [symm_zero] using continuous_symm.tendsto (0 : I)
  have hσ₁ : Tendsto σ (𝓝 (1 : I)) (𝓝 0) := by
    simpa only [symm_one] using continuous_symm.tendsto (1 : I)
  rw [reverse_def, isCollared_reparam_iff (ρ := ⟨σ, contMDiff_symm⟩), ContMDiffMap.coeFn_mk]
  refine ⟨(hσ₀.eventually hΦ.eventually_one).mono fun t ht ↦ ?_,
    (hσ₁.eventually hΦ.eventually_zero).mono fun t ht ↦ ?_⟩
  · rw [ht, symm_zero, final_def]
  · rw [ht, symm_one, timeSlice_zero]

variable (Φ Ψ)

/-- **Every concatenation is collared**, whether or not its factors are: it is the identity up to
time `1 / 8` and equal to its final diffeomorphism from time `7 / 8` on. -/
theorem isCollared_concat (hn : n ≤ ∞) : (Φ.concat Ψ hn).IsCollared := by
  have hcoe : Continuous fun t : I ↦ (t : ℝ) := continuous_subtypeVal
  have h₀ : ∀ᶠ t : I in 𝓝 0, (t : ℝ) < 1 / 8 :=
    (isOpen_lt hcoe continuous_const).mem_nhds (by norm_num [Set.Icc.coe_zero])
  have h₁ : ∀ᶠ t : I in 𝓝 1, 7 / 8 < (t : ℝ) :=
    (isOpen_lt continuous_const hcoe).mem_nhds (by norm_num [Set.Icc.coe_one])
  refine ⟨h₀.mono fun t ht ↦ _root_.Diffeomorph.ext fun x ↦ ?_,
    h₁.mono fun t ht ↦ _root_.Diffeomorph.ext fun x ↦ ?_⟩
  · rw [timeSlice_apply, concat_apply_of_le _ _ _ (by linarith),
      collaredSmoothTransitionUnit_eq_zero_of_le (by linarith), apply_zero,
      _root_.Diffeomorph.coe_refl, id_eq]
  · rw [timeSlice_apply, final_apply, concat_apply_of_ge _ _ _ (by linarith),
      concat_apply_of_ge _ _ _ (by norm_num), Set.Icc.coe_one,
      collaredSmoothTransitionUnit_eq_one_of_ge (by linarith),
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num)]

/-! ### Homotopy laws -/

section Homotopy

/-- **A reparametrization fixing both ends is homotopic to the original diffeotopy**, through the
straight-line homotopy `((x, t), s) ↦ φ_{(1 - s) ρ t + s t} x` of time maps. -/
theorem reparam_homotopic {ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯} (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) :
    (Φ.reparam ρ).Homotopic Φ := by
  have hτ : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((𝓡∂ 1).prod J) n
      fun q : (M × I) × I ↦ (Set.Icc.convexComb (ρ q.1.2) q.1.2 q.2, q.1.1) :=
    ((ρ.contMDiff.comp (contMDiff_snd.comp contMDiff_fst)).convexComb
      (contMDiff_snd.comp contMDiff_fst) contMDiff_snd).prodMk (contMDiff_fst.comp contMDiff_fst)
  refine homotopic_iff.mpr ⟨fun q ↦ Φ (Set.Icc.convexComb (ρ q.1.2) q.1.2 q.2, q.1.1),
    fun q ↦ Φ.symm (Set.Icc.convexComb (ρ q.1.2) q.1.2 q.2, q.1.1), Φ.contMDiff.comp hτ,
    fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ ?_, fun x s ↦ ?_, Φ.symm.contMDiff.comp hτ,
    fun x t s ↦ symm_apply_apply_mk _ _ _, fun x t s ↦ apply_symm_apply_mk _ _ _⟩
  · simp only [Set.Icc.convexComb_zero, cylinderMap_apply, reparam_apply_of_map_zero _ h₀]
  · simp only [Set.Icc.convexComb_one, cylinderMap_apply]
  · simp only [h₀, Set.Icc.convexComb_eq, apply_zero]
  · simp only [h₁, Set.Icc.convexComb_eq, final_apply, reparam_apply_of_map_zero _ h₀]

/-- **Every diffeotopy is homotopic to the restriction of a real-time family.** There are a
diffeotopy `Φ'`, homotopic to `Φ` relative to both time ends, and a `C^n` map `c : ℝ → [0, 1]` such
that the time slices of `Φ'` are `φ_{c t}` and the family `u ↦ φ_{c u}`, `u ∈ ℝ`, and its inverses
are `C^n` jointly in time and space. Here `c` is the collared smooth transition and `Φ'` is the
reparametrization of `Φ` by it. -/
theorem exists_homotopic_timeSlice_eq_comp (hn : n ≤ ∞) :
    ∃ (Φ' : Diffeotopy J n M) (c : ℝ → I), Φ'.Homotopic Φ ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) n c ∧
      (∀ t : I, Φ'.timeSlice t = Φ.timeSlice (c t)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J n (fun p : ℝ × M ↦ Φ (c p.1, p.2)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J n (fun p : ℝ × M ↦ Φ.symm (c p.1, p.2)) := by
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) n collaredSmoothTransitionUnit :=
    contMDiff_collaredSmoothTransitionUnit hn
  let ρ : C^n⟮𝓡∂ 1, I; 𝓡∂ 1, I⟯ :=
    ⟨fun t ↦ collaredSmoothTransitionUnit t, hc.comp (contMDiff_subtypeVal_Icc (x := 0) (y := 1))⟩
  have hρ₀ : ρ 0 = 0 := collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num)
  refine ⟨Φ.reparam ρ, collaredSmoothTransitionUnit,
    Φ.reparam_homotopic hρ₀ (collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num)), hc,
    fun t ↦ _root_.Diffeomorph.ext fun x ↦ ?_, Φ.contMDiff.comp (hc.prodMap contMDiff_id),
    Φ.symm.contMDiff.comp (hc.prodMap contMDiff_id)⟩
  rw [timeSlice_apply, timeSlice_apply, reparam_apply_of_map_zero _ hρ₀]
  rfl

/-- **The path-class law of concatenation.** The concatenation of `Φ` and `Ψ` is homotopic to their
pointwise composite `ψ_t ∘ φ_t`. -/
theorem concat_homotopic_trans (hn : n ≤ ∞) : (Φ.concat Ψ hn).Homotopic (Φ.trans Ψ) := by
  rw [concat_def]
  exact (Φ.reparam_homotopic (collaredFirstHalf_zero hn) (collaredFirstHalf_one hn)).trans_congr
    (Ψ.reparam_homotopic (collaredSecondHalf_zero hn) (collaredSecondHalf_one hn))

/-- **The path-class law of time reversal.** The reversal `φ_{1 - t} ∘ φ₁⁻¹` is homotopic to the
pointwise inverse `φ_t⁻¹`, through `((x, t), s) ↦ φ_{(1 - s)(1 - t)} (φ_{(1 - s) + s t}⁻¹ x)`. -/
theorem reverse_homotopic_symm : Φ.reverse.Homotopic Φ.symm := by
  have ha : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (𝓡∂ 1) n
      fun q : (M × I) × I ↦ Set.Icc.convexComb (σ q.1.2) 0 q.2 :=
    (contMDiff_symm.comp (contMDiff_snd.comp contMDiff_fst)).convexComb contMDiff_const
      contMDiff_snd
  have hb : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (𝓡∂ 1) n
      fun q : (M × I) × I ↦ Set.Icc.convexComb 1 q.1.2 q.2 :=
    contMDiff_const.convexComb (contMDiff_snd.comp contMDiff_fst) contMDiff_snd
  -- The inverse homotopy is `((x, t), s) ↦ φ_{(1 - s) + s t} (φ_{(1 - s)(1 - t)}⁻¹ x)`.
  refine homotopic_iff.mpr ⟨fun q ↦ Φ (Set.Icc.convexComb (σ q.1.2) 0 q.2,
      Φ.symm (Set.Icc.convexComb 1 q.1.2 q.2, q.1.1)),
    fun q ↦ Φ (Set.Icc.convexComb 1 q.1.2 q.2, Φ.symm (Set.Icc.convexComb (σ q.1.2) 0 q.2, q.1.1)),
    Φ.contMDiff.comp (ha.prodMk (Φ.symm.contMDiff.comp
      (hb.prodMk (contMDiff_fst.comp contMDiff_fst)))),
    fun p ↦ ?_, fun p ↦ ?_, fun x s ↦ ?_, fun x s ↦ ?_,
    Φ.contMDiff.comp (hb.prodMk (Φ.symm.contMDiff.comp
      (ha.prodMk (contMDiff_fst.comp contMDiff_fst)))),
    fun x t s ↦ by simp only [symm_apply_apply_mk, apply_symm_apply_mk],
    fun x t s ↦ by simp only [symm_apply_apply_mk, apply_symm_apply_mk]⟩
  · simp only [Set.Icc.convexComb_zero, cylinderMap_apply, reverse_apply]
  · simp only [Set.Icc.convexComb_one, cylinderMap_apply, apply_zero]
  · simp only [symm_zero, apply_symm_apply_mk]
  · simp only [symm_one, Set.Icc.convexComb_eq, apply_zero, final_reverse]
    rw [final_def, symm_timeSlice_apply]

variable {Φ Ψ} {Φ' Ψ' : Diffeotopy J n M}

/-- Concatenation is compatible with homotopy. -/
theorem Homotopic.concat_congr (h : Φ.Homotopic Φ') (h' : Ψ.Homotopic Ψ') (hn : n ≤ ∞) :
    (Φ.concat Ψ hn).Homotopic (Φ'.concat Ψ' hn) :=
  ((Φ.concat_homotopic_trans Ψ hn).trans (h.trans_congr h') hn).trans
    (Φ'.concat_homotopic_trans Ψ' hn).symm hn

/-- Time reversal is compatible with homotopy. -/
theorem Homotopic.reverse_congr (h : Φ.Homotopic Φ') (hn : n ≤ ∞) :
    Φ.reverse.Homotopic Φ'.reverse :=
  ((Φ.reverse_homotopic_symm.trans h.symm_congr hn).trans Φ'.reverse_homotopic_symm.symm hn)

variable (Φ) in
/-- **Reversal inverts concatenation up to homotopy**: running through `Φ` and then back along it is
homotopic to the constant diffeotopy. -/
theorem concat_reverse_homotopic_refl (hn : n ≤ ∞) :
    (Φ.concat Φ.reverse hn).Homotopic (refl J n M) := by
  have h := (Φ.concat_homotopic_trans Φ.reverse hn).trans
    ((Homotopic.refl Φ).trans_congr Φ.reverse_homotopic_symm) hn
  rwa [self_trans_symm] at h

end Homotopy

end Diffeotopy

end TauCeti
