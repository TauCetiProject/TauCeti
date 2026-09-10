/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# The hyperbolic plane

The hyperbolic plane over a field of characteristic different from two is the diagonal quadratic
form `⟨1, -1⟩`. It represents every scalar. More generally, every plane `⟨a, -a⟩` with
`a ≠ 0` is isometric to it.

The main result is the hyperbolic splitting theorem: every nondegenerate isotropic quadratic form
splits as the orthogonal sum of a hyperbolic plane and another nondegenerate form. The proof uses
an isotropic pair whose polar pairing is one, then takes its orthogonal complement.

## Main definitions

* `TauCeti.hyperbolicPlane`: the diagonal form `⟨1, -1⟩`.

## Main results

* `TauCeti.hyperbolicPlane_represents`: the hyperbolic plane represents every scalar.
* `TauCeti.equivalent_weightedSumSquares_self_neg`: every `⟨a, -a⟩`, for `a ≠ 0`, is
  hyperbolic.
* `TauCeti.exists_hyperbolicPlane_prod_equivalent`: every nondegenerate isotropic form splits off
  a hyperbolic plane.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §3.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

section CommRing

variable {R : Type u} [CommRing R]

/-- The hyperbolic plane `⟨1, -1⟩`. -/
def hyperbolicPlane (R : Type u) [CommRing R] : QuadraticForm R (Fin 2 → R) :=
  weightedSumSquares R ![(1 : R), -1]

/-- Evaluation of the hyperbolic plane in its diagonal coordinates. -/
@[simp]
theorem hyperbolicPlane_apply (x : Fin 2 → R) :
    hyperbolicPlane R x = x 0 ^ 2 - x 1 ^ 2 := by
  simp [hyperbolicPlane, weightedSumSquares_apply, Fin.sum_univ_two, pow_two]
  ring

end CommRing

variable {K : Type u} [Field K]

/-- The hyperbolic plane is nondegenerate when two is invertible. -/
theorem hyperbolicPlane_nondegenerate [Invertible (2 : K)] :
    (hyperbolicPlane K).Nondegenerate := by
  let p : RegularFormPresentation K := ⟨2, ![(1 : Kˣ), (-1 : Kˣ)]⟩
  have hp : presentedForm p = hyperbolicPlane K := by
    ext x
    rw [presentedForm_eq_weightedSumSquares]
    simp [hyperbolicPlane, weightedSumSquares_apply, Fin.sum_univ_two, p, Units.smul_def]
  rw [← hp]
  exact nondegenerate_presentedForm p

/-- The hyperbolic plane represents every scalar. -/
theorem hyperbolicPlane_represents [Invertible (2 : K)] (a : K) :
    (hyperbolicPlane K).Represents a := by
  rw [represents_iff, Set.mem_range]
  refine ⟨![(a + 1) / 2, (a - 1) / 2], ?_⟩
  rw [hyperbolicPlane_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have htwo : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  field_simp [htwo]
  ring

/-- Every diagonal plane `⟨a, -a⟩` with `a` a unit is isometric to the hyperbolic plane. -/
theorem equivalent_weightedSumSquares_self_neg [Invertible (2 : K)] (a : Kˣ) :
    (weightedSumSquares K ![(a : K), -(a : K)]).Equivalent (hyperbolicPlane K) := by
  have hdisc : IsSquare (a * (-a) * ((1 : Kˣ) * (-1))) := by
    refine ⟨a, ?_⟩
    simp
  have hsource : a ∈ unitValueSet
      (weightedSumSquares K ![(a : K), -(a : K)]) :=
    mem_unitValueSet_binary_left a (-(a : K))
  have htarget : a ∈ unitValueSet (hyperbolicPlane K) := by
    rw [mem_unitValueSet]
    exact hyperbolicPlane_represents (a : K)
  exact equivalent_binary_of_isSquare_of_mem_unitValueSet
    (a := a) (b := -a) (c := 1) (d := -1) (e := a) hdisc hsource htarget

variable {V : Type v} [AddCommGroup V] [Module K V]

/-- A nondegenerate isotropic quadratic form contains two isotropic vectors whose polar pairing
is one. -/
theorem _root_.QuadraticMap.Nondegenerate.exists_isotropic_pair [Invertible (2 : K)]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) :
    ∃ x y : V, x ≠ 0 ∧ Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1 := by
  obtain ⟨x, hx, hxQ⟩ := (not_anisotropic_iff_exists Q).mp hiso
  obtain ⟨w, hw⟩ : ∃ w, polar Q x w ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    have hxrad : x ∈ Q.radical := by
      rw [mem_radical_iff']
      refine ⟨hxQ, fun z ↦ ?_⟩
      rw [QuadraticMap.map_add Q, hxQ, h z, zero_add, add_zero]
    rw [hQ.radical_eq_bot] at hxrad
    exact hxrad
  let z := w - (Q w / polar Q x w) • x
  have hzQ : Q z = 0 := by
    have hw' : polar Q w x ≠ 0 := by simpa only [polar_comm] using hw
    dsimp [z]
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, Q.map_smul, hxQ,
      polar_smul_right, polar_comm]
    simp only [smul_eq_mul]
    field_simp [hw']
    ring
  have hxz : polar Q x z = polar Q x w := by
    simp [z, polar_sub_right, polar_smul_right, polar_self, hxQ]
  let y := (polar Q x w)⁻¹ • z
  refine ⟨x, y, hx, hxQ, ?_, ?_⟩
  · simp [y, Q.map_smul, hzQ]
  · simp [y, polar_smul_right, hxz, hw]

private def hyperbolicPairMap (x y : V) : K × K →ₗ[K] V where
  toFun p := (p.1 + p.2) • x + (p.1 - p.2) • y
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add]
    module
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    module

private theorem hyperbolicPairMap_injective [Invertible (2 : K)]
    (Q : QuadraticForm K V) {x y : V} (hxQ : Q x = 0) (hyQ : Q y = 0)
    (hxy : polar Q x y = 1) : Function.Injective (hyperbolicPairMap (K := K) x y) := by
  intro p q hpq
  have hpqzero : hyperbolicPairMap (K := K) x y (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hsub : (p - q).1 - (p - q).2 = 0 := by
    have := congrArg (polar Q x) hpqzero
    simpa [hyperbolicPairMap, polar_add_right, polar_smul_right, polar_self, hxQ, hxy] using this
  have hadd : (p - q).1 + (p - q).2 = 0 := by
    have := congrArg (fun z ↦ polar Q z y) hpqzero
    simpa [hyperbolicPairMap, polar_add_left, polar_smul_left, polar_self, hyQ, hxy,
      polar_comm] using this
  have hpq' : p - q = 0 := by
    apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero]
    · apply (mul_left_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero)
      linear_combination hadd + hsub
    · apply (mul_left_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero)
      linear_combination hadd - hsub
  exact sub_eq_zero.mp hpq'

private noncomputable def hyperbolicPairIsometryEquiv [Invertible (2 : K)]
    (Q : QuadraticForm K V) (x y : V) (hxQ : Q x = 0) (hyQ : Q y = 0)
    (hxy : polar Q x y = 1) :
    (hyperbolicPlane K).IsometryEquiv
      (Q.restrict (LinearMap.range (hyperbolicPairMap (K := K) x y))) where
  toLinearEquiv := (LinearEquiv.finTwoArrow K K).trans
    (LinearEquiv.ofInjective (hyperbolicPairMap (K := K) x y)
      (hyperbolicPairMap_injective Q hxQ hyQ hxy))
  map_app' v := by
    -- Expose the range equivalence so the quadratic-form calculation sees its underlying map.
    change Q ((v 0 + v 1) • x + (v 0 - v 1) • y) = hyperbolicPlane K v
    rw [hyperbolicPlane_apply, QuadraticMap.map_add Q, Q.map_smul, Q.map_smul, hxQ, hyQ,
      polar_smul_left, polar_smul_right, hxy]
    simp only [smul_eq_mul, mul_one]
    ring

/-- Every nondegenerate isotropic quadratic form splits as the orthogonal sum of a hyperbolic
plane and a nondegenerate diagonal form. -/
theorem exists_hyperbolicPlane_prod_equivalent [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) :
    ∃ p : RegularFormPresentation K,
      Q.Equivalent ((hyperbolicPlane K).prod (presentedForm p)) := by
  obtain ⟨x, y, hx, hxQ, hyQ, hxy⟩ := hQ.exists_isotropic_pair hiso
  let W := LinearMap.range (hyperbolicPairMap (K := K) x y)
  let eH := hyperbolicPairIsometryEquiv Q x y hxQ hyQ hxy
  have hWQ : (Q.restrict W).Nondegenerate := by
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    have hr := eH.map_radical
    rw [hyperbolicPlane_nondegenerate.radical_eq_bot, Submodule.map_bot] at hr
    exact hr.symm
  let B := QuadraticMap.associated Q
  have associated_restrict (S : Submodule K V) :
      QuadraticMap.associated (Q.restrict S) = LinearMap.BilinForm.restrict B S := by
    ext a b
    rfl
  have hBW : (LinearMap.BilinForm.restrict B W).Nondegenerate := by
    rw [← associated_restrict]
    exact QuadraticMap.nondegenerate_associated_iff.mpr hWQ
  have hcomp : IsCompl W (LinearMap.BilinForm.orthogonal B W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm K Q)).isRefl hBW
  have horth : (Q.restrict (LinearMap.BilinForm.orthogonal B W)).Nondegenerate := by
    have hB : B.Nondegenerate := QuadraticMap.nondegenerate_associated_iff.mpr hQ
    have hBsymm :=
      (LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm K Q)).isRefl
    have hBorth :
        (LinearMap.BilinForm.restrict B (LinearMap.BilinForm.orthogonal B W)).Nondegenerate := by
      rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBsymm,
        LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm]
      exact hcomp.symm
    rw [← QuadraticMap.nondegenerate_associated_iff]
    rw [associated_restrict]
    exact hBorth
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent
    (Q.restrict (LinearMap.BilinForm.orthogonal B W)) horth
  have hdecomp : Q.Equivalent
      ((Q.restrict W).prod (Q.restrict (LinearMap.BilinForm.orthogonal B W))) :=
    ⟨(QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q W hcomp).symm⟩
  have hreplace :
      ((Q.restrict W).prod (Q.restrict (LinearMap.BilinForm.orthogonal B W))).Equivalent
        ((hyperbolicPlane K).prod (presentedForm p)) :=
    QuadraticMap.Equivalent.prod
      (⟨eH.symm⟩ : (Q.restrict W).Equivalent (hyperbolicPlane K)) hp
  exact ⟨p, hdecomp.trans hreplace⟩

end TauCeti
