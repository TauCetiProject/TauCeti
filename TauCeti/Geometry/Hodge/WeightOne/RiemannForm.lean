/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.Lattice
public import TauCeti.Geometry.Hodge.WeightOne.Polarization

/-!
# Riemann forms polarize the weight-one Hodge structure of a lattice

Let `V` be an integral module with an almost complex structure `J` on its realification
`ℝ ⊗[ℤ] V`, and let `E` be an integral bilinear form on `V`. Classically, `E` is a **Riemann form**
for `(V, J)` when it is alternating and its real scalar extension `E_ℝ` satisfies the two Riemann
bilinear relations

* `E_ℝ (J x) (J y) = E_ℝ x y` for all real `x` and `y`, and
* `0 < E_ℝ (J x) x` for every nonzero real `x`;

that is, `H (x, y) = E_ℝ (J x) y + i E_ℝ x y` is a positive definite Hermitian form for the
complex structure `J`. This is the datum of a polarized abelian variety: `(ℤ^{2g}, J, E)` with
`E` a Riemann form is a complex torus `ℂ^g / Λ` together with a polarization.

When `V` is flat over `ℤ`, this file shows that a Riemann form is exactly an integral form
polarizing the effective weight-one Hodge structure
`TauCeti.AlmostComplexStructure.latticeHodgeStructure` that `J` defines on `V`: the
Hodge–Riemann relations for that structure, whose Weil operator is the
transported `J`, reduce to the two relations above on the real points, which are the realification.
A Riemann form is also nondegenerate when `V` is flat over `ℤ`, so nondegeneracy is not part of
the definition.

Sign convention: positivity is `0 < E_ℝ (J x) x`, as in Birkenhake–Lange, so that the Hermitian
form `H` above is positive definite. It matches the pinned convention of
`TauCeti.Hodge.IsPolarization`, `0 < Q (C x) x` for the Weil operator `C`. The symplectic
compatibility predicate `TauCeti.SymplecticForm.Compatible` uses the opposite sign,
`0 < ω x (J x)`, so a Riemann form is `J`-compatible in that sense only up to a sign.

## Main declarations

* `TauCeti.AlmostComplexStructure.IsRiemannForm`: `E` is a Riemann form for `J`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.nondegenerate`: a Riemann form is nondegenerate
  when `V` is flat over `ℤ`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.isPolarization`: **when `V` is flat over `ℤ`,
  a Riemann form polarizes the weight-one Hodge structure of `J`**.
* `TauCeti.AlmostComplexStructure.isRiemannForm_of_isPolarization`: every form polarizing that
  Hodge structure is a Riemann form, with no flatness assumption.
* `TauCeti.AlmostComplexStructure.isRiemannForm_iff_isPolarization`: when `V` is flat over `ℤ`,
  the Riemann forms are exactly the polarizing forms.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.polarization`: the polarized effective weight-one
  Hodge structure of a lattice with a complex structure and a Riemann form.

The definitions and conventions follow Birkenhake–Lange, *Complex Abelian Varieties*, §2.1 and
§4.1, and Mumford, *Abelian Varieties*, §I.3; the Hodge-theoretic reading is Voisin, *Hodge Theory
and Complex Algebraic Geometry I*, Chapter 7.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- An integral bilinear form `E` on `V` is a **Riemann form** for an almost complex structure `J`
on the realification of `V` when it is alternating, its real scalar extension is `J`-invariant, and
`E_ℝ (J x) x` is positive for every nonzero real vector `x`.

Nondegeneracy follows when `V` is flat over `ℤ` (`IsRiemannForm.nondegenerate`), so it is not part
of this definition. -/
structure IsRiemannForm (J : AlmostComplexStructure (Hodge.Realification V))
    (E : LinearMap.BilinForm ℤ V) : Prop where
  /-- The form is alternating. -/
  isAlt : E.IsAlt
  /-- The first Riemann bilinear relation: the real scalar extension is `J`-invariant. -/
  invariant : ∀ x y, E.baseChange ℝ (J x) (J y) = E.baseChange ℝ x y
  /-- The second Riemann bilinear relation: `E_ℝ (J x) x` is positive on nonzero real vectors. -/
  positive : ∀ x, x ≠ 0 → 0 < E.baseChange ℝ (J x) x

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}

/-- **A Riemann form is nondegenerate**, on a flat (for instance free) integral module: the
positivity of `E_ℝ (J x) x` leaves no room for a radical. -/
theorem nondegenerate [Module.Flat ℤ V] (h : IsRiemannForm J E) : E.Nondegenerate := by
  have hleft : E.SeparatingLeft := by
    intro x hx
    have hreal : ∀ y : Hodge.Realification V, E.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℤ] x) y = 0 := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul s y => simp [hx y]
      | add y z hy hz => rw [map_add, hy, hz, add_zero]
    -- Invariance with `J x'` and `x'` reads `E (-x') (J x') = E (J x') x'`, and the left side
    -- vanishes because `x'` pairs to zero with everything.
    have hpair : E.baseChange ℝ (J ((1 : ℝ) ⊗ₜ[ℤ] x)) ((1 : ℝ) ⊗ₜ[ℤ] x) = 0 := by
      have hinv := h.invariant (J ((1 : ℝ) ⊗ₜ[ℤ] x)) ((1 : ℝ) ⊗ₜ[ℤ] x)
      rw [apply_apply, map_neg, LinearMap.neg_apply, hreal, neg_zero] at hinv
      exact hinv.symm
    by_contra hx0
    have hne : (1 : ℝ) ⊗ₜ[ℤ] x ≠ 0 := fun h0 ↦
      hx0 (Hodge.realificationMap_injective (by simpa using h0))
    exact (h.positive _ hne).ne' hpair
  exact (LinearMap.IsRefl.nondegenerate_iff_separatingLeft h.isAlt.isRefl).mpr hleft

/-- **A Riemann form on a flat integral module polarizes the weight-one Hodge structure of its
complex structure.** For the effective weight-one structure `J.latticeHodgeStructure hℂ`, whose
Weil operator is `J`, the Hodge–Riemann relations of `E` are exactly the two Riemann bilinear
relations. -/
theorem isPolarization [Module.Flat ℤ V] (h : IsRiemannForm J E) (hℂ : IsBaseChange ℂ ιℂ) :
    Hodge.IsPolarization hℂ (J.latticeHodgeStructure hℂ) E := by
  refine Hodge.isPolarization_of_weilOperator_invariant_on_realPoints_of_pos
    (J.isEffective_latticeHodgeStructure hℂ) (fun x y ↦ (h.isAlt.neg_eq x y).symm)
    h.nondegenerate ?_ ?_
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := Hodge.exists_eq_realificationComplexEquiv_one_tmul hℂ hx
    obtain ⟨b, rfl⟩ := Hodge.exists_eq_realificationComplexEquiv_one_tmul hℂ hy
    simp [h.invariant]
  · intro x hx hx0
    obtain ⟨a, rfl⟩ := Hodge.exists_eq_realificationComplexEquiv_one_tmul hℂ hx
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hx0
    simp only [latticeHodgeStructure_weilOperator,
      latticeComplexification_realificationComplexEquiv_one_tmul,
      Hodge.integralFormBaseChange_realificationComplexEquiv_one_tmul]
    exact Complex.zero_lt_real.mpr (h.positive a ha)

/-- The polarized effective weight-one Hodge structure of a flat integral module with a complex
structure and a Riemann form: the Riemann form, bundled with its Hodge–Riemann relations. -/
def polarization [Module.Flat ℤ V] (h : IsRiemannForm J E) (hℂ : IsBaseChange ℂ ιℂ) :
    Hodge.Polarization hℂ (J.latticeHodgeStructure hℂ) where
  Qint := E
  isPolarization := h.isPolarization hℂ

/-- The integral form of the polarization defined by a Riemann form is that form. -/
@[simp]
theorem polarization_Qint [Module.Flat ℤ V] (h : IsRiemannForm J E) (hℂ : IsBaseChange ℂ ιℂ) :
    (h.polarization hℂ).Qint = E := (rfl)

/-- The complex form of the polarization defined by a Riemann form is the complexification of
that form. -/
@[simp]
theorem polarization_Q [Module.Flat ℤ V] (h : IsRiemannForm J E) (hℂ : IsBaseChange ℂ ιℂ) :
    (h.polarization hℂ).Q = Hodge.integralFormBaseChange hℂ E := by
  rw [Hodge.Polarization.Q_def, polarization_Qint]

end IsRiemannForm

/-- **Every form polarizing the weight-one Hodge structure of `J` is a Riemann form for `J`**, with
no flatness assumption: `J`-invariance of `E_ℝ` says that the Weil operator is an isometry of the
polarization, and positivity of `E_ℝ (J x) x` is positivity of the Hodge form on real vectors. -/
theorem isRiemannForm_of_isPolarization {J : AlmostComplexStructure (Hodge.Realification V)}
    {hℂ : IsBaseChange ℂ ιℂ} {E : LinearMap.BilinForm ℤ V}
    (h : Hodge.IsPolarization hℂ (J.latticeHodgeStructure hℂ) E) : J.IsRiemannForm E := by
  refine ⟨LinearMap.isAlt_iff_eq_neg_flip.mpr ?_, fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · ext x y
    exact h.eq_neg_of_odd odd_one y x
  · have hiso := h.isOrthogonal_weilOperator (Hodge.realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x))
      (Hodge.realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] y))
    simp only [latticeHodgeStructure_weilOperator,
      latticeComplexification_realificationComplexEquiv_one_tmul,
      Hodge.integralFormBaseChange_realificationComplexEquiv_one_tmul] at hiso
    exact_mod_cast hiso
  · have hne : Hodge.realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      intro h0
      exact hx (Module.Flat.tensorProduct_mk_injective ℝ (Hodge.Realification V) ℂ
        (by simpa using h0))
    have hpos := h.integralFormBaseChange_weilOperator_self_pos (by simp) hne
    simp only [latticeHodgeStructure_weilOperator,
      latticeComplexification_realificationComplexEquiv_one_tmul,
      Hodge.integralFormBaseChange_realificationComplexEquiv_one_tmul] at hpos
    exact Complex.zero_lt_real.mp hpos

/-- **When `V` is flat over `ℤ`, the Riemann forms for `J` are exactly the forms polarizing its
weight-one Hodge structure.** Flatness is used only in the forward direction, for nondegeneracy. -/
theorem isRiemannForm_iff_isPolarization [Module.Flat ℤ V]
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)
    (E : LinearMap.BilinForm ℤ V) :
    J.IsRiemannForm E ↔ Hodge.IsPolarization hℂ (J.latticeHodgeStructure hℂ) E :=
  ⟨fun h ↦ h.isPolarization hℂ, isRiemannForm_of_isPolarization⟩

end TauCeti.AlmostComplexStructure
