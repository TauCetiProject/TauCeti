/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.Lattice
public import TauCeti.Geometry.Hodge.WeightOne.Polarization
import Mathlib.RingTheory.Flat.TorsionFree

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
* `TauCeti.AlmostComplexStructure.IsRiemannForm.neg`: `-E` is a Riemann form for `-J`, while
  `TauCeti.AlmostComplexStructure.IsRiemannForm.not_isRiemannForm_neg`: when the realification is
  nonzero (for instance for a nonzero free lattice), `-E` is not a Riemann form for `J`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.scale`: a positive integer multiple of a Riemann
  form is a Riemann form.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.pullback_of_injective_baseChange`: the pullback of
  a Riemann form along an integral map whose real extension is injective and complex linear is a
  Riemann form. `TauCeti.AlmostComplexStructure.IsRiemannForm.pullback`: the real extension of an
  injective integral map is injective, so it suffices that the integral map is injective and its
  real extension intertwines the two complex structures.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.baseChange_apply_left_symm`: the real extension of
  a Riemann form satisfies `E_ℝ (J v) w = E_ℝ (J w) v`.
* `TauCeti.Hodge.HodgeStructureOn.isRiemannForm_latticeAlmostComplexStructure_iff`: read from the
  Hodge-structure side, when `V` is flat over `ℤ` the forms polarizing an effective weight-one
  Hodge structure are exactly the Riemann forms of its complex structure on the realification.

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
      TauCeti.Hodge.bilinForm_realificationComplexEquiv_one_tmul]
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
    (h.polarization hℂ).Q = IsBaseChange.bilinForm hℂ E := by
  rw [Hodge.Polarization.Q_def, polarization_Qint]

/-- Negating both the form and the complex structure preserves the Riemann form condition: if `E`
is a Riemann form for `J`, then `-E` is a Riemann form for `-J`, since
`(-E)_ℝ ((-J) v) v = E_ℝ (J v) v`. -/
theorem neg (h : J.IsRiemannForm E) : (-J).IsRiemannForm (-E) := by
  refine ⟨h.isAlt.neg, fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · simp [h.invariant]
  · simpa using h.positive x hx

/-- When the realification is nonzero (for instance for a nonzero free lattice), the negative of a
Riemann form for `J` is not a Riemann form for `J`: it fails positivity. -/
theorem not_isRiemannForm_neg [Nontrivial (Hodge.Realification V)] (h : J.IsRiemannForm E) :
    ¬ J.IsRiemannForm (-E) := by
  intro h'
  obtain ⟨x, hx⟩ := exists_ne (0 : Hodge.Realification V)
  have := h'.positive x hx
  rw [LinearMap.BilinForm.baseChange_neg, LinearMap.neg_apply, LinearMap.neg_apply] at this
  linarith [h.positive x hx]

/-- **A positive integer multiple of a Riemann form is a Riemann form.** -/
theorem scale (h : J.IsRiemannForm E) {n : ℕ} (hn : 0 < n) : J.IsRiemannForm (n • E) := by
  have hn' (x y : Hodge.Realification V) :
      (n • E).baseChange ℝ x y = n * E.baseChange ℝ x y := by
    rw [← Nat.cast_smul_eq_nsmul ℤ, LinearMap.BilinForm.baseChange_smul]
    simp
  refine ⟨h.isAlt.smul n, fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · simp [hn', h.invariant]
  · simpa [hn'] using mul_pos (Nat.cast_pos.mpr hn) (h.positive x hx)

variable {W : Type*} [AddCommGroup W] {J' : AlmostComplexStructure (Hodge.Realification W)}

/-- **The pullback of a Riemann form along an integral map whose real extension is injective and
complex linear is a Riemann form.** For complex tori this is pulling back a polarization along an
injective complex-linear map carrying lattice into lattice. -/
theorem pullback_of_injective_baseChange (h : J.IsRiemannForm E) {f : W →ₗ[ℤ] V}
    (hfℝ : Function.Injective (f.baseChange ℝ)) (hJ : IsComplexLinearMap J' J (f.baseChange ℝ)) :
    J'.IsRiemannForm (E.compl₁₂ f f) := by
  have hJ' := (isComplexLinearMap_iff_apply J' J (f.baseChange ℝ)).mp hJ
  have hbc (x y : Hodge.Realification W) :
      LinearMap.BilinForm.baseChange ℝ (E.compl₁₂ f f) x y =
        E.baseChange ℝ (f.baseChange ℝ x) (f.baseChange ℝ y) :=
    (LinearMap.BilinForm.baseChange_baseChange_baseChange (B := E.compl₁₂ f f)
      (fun _ _ ↦ rfl) x y).symm
  refine ⟨fun x ↦ h.isAlt (f x), fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [hbc, hJ', h.invariant]
  · rw [hbc, hJ']
    exact h.positive _ ((injective_iff_map_eq_zero' _).mp hfℝ x |>.not.mpr hx)

/-- **The pullback of a Riemann form along an injective integral map whose real extension is
complex linear is a Riemann form**: `ℝ` is flat over `ℤ`, so the real extension of `f` is
injective. -/
theorem pullback (h : J.IsRiemannForm E) {f : W →ₗ[ℤ] V} (hf : Function.Injective f)
    (hJ : IsComplexLinearMap J' J (f.baseChange ℝ)) :
    J'.IsRiemannForm (E.compl₁₂ f f) := by
  refine h.pullback_of_injective_baseChange ?_ hJ
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- The real extension of a Riemann form satisfies `E_ℝ (J v) w = E_ℝ (J w) v`. -/
theorem baseChange_apply_left_symm (h : J.IsRiemannForm E) (v w : Hodge.Realification V) :
    E.baseChange ℝ (J v) w = E.baseChange ℝ (J w) v :=
  J.bilinForm_apply_left_symm h.isAlt.baseChange h.invariant v w

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
      TauCeti.Hodge.bilinForm_realificationComplexEquiv_one_tmul] at hiso
    exact_mod_cast hiso
  · have hne : Hodge.realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      intro h0
      exact hx (Module.Flat.tensorProduct_mk_injective ℝ (Hodge.Realification V) ℂ
        (by simpa using h0))
    have hpos := h.bilinForm_weilOperator_self_pos (by simp) hne
    simp only [latticeHodgeStructure_weilOperator,
      latticeComplexification_realificationComplexEquiv_one_tmul,
      TauCeti.Hodge.bilinForm_realificationComplexEquiv_one_tmul] at hpos
    exact Complex.zero_lt_real.mp hpos

/-- **When `V` is flat over `ℤ`, the Riemann forms for `J` are exactly the forms polarizing its
weight-one Hodge structure.** Flatness is used only in the forward direction, for nondegeneracy. -/
theorem isRiemannForm_iff_isPolarization [Module.Flat ℤ V]
    (J : AlmostComplexStructure (Hodge.Realification V)) (hℂ : IsBaseChange ℂ ιℂ)
    (E : LinearMap.BilinForm ℤ V) :
    J.IsRiemannForm E ↔ Hodge.IsPolarization hℂ (J.latticeHodgeStructure hℂ) E :=
  ⟨fun h ↦ h.isPolarization hℂ, isRiemannForm_of_isPolarization⟩

end TauCeti.AlmostComplexStructure

namespace TauCeti.Hodge.HodgeStructureOn

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ}

/-- **When `V` is flat over `ℤ`, the forms polarizing an effective weight-one Hodge structure are
exactly the Riemann forms of its complex structure on the realification.** This is
`TauCeti.AlmostComplexStructure.isRiemannForm_iff_isPolarization` read through the round trip
`TauCeti.AlmostComplexStructure.latticeHodgeStructureEquiv`: polarized effective weight-one Hodge
structures on a lattice are the data `(Λ, J, E)` of a polarized abelian variety. -/
theorem isRiemannForm_latticeAlmostComplexStructure_iff [Module.Flat ℤ V]
    (hs : HodgeStructure hℂ 1) (h : hs.IsEffective) (E : LinearMap.BilinForm ℤ V) :
    (hs.latticeAlmostComplexStructure odd_one).IsRiemannForm E ↔ IsPolarization hℂ hs E := by
  rw [AlmostComplexStructure.isRiemannForm_iff_isPolarization _ hℂ,
    hs.latticeHodgeStructure_latticeAlmostComplexStructure (hs.isEffective_iff.mp h)]

end TauCeti.Hodge.HodgeStructureOn
