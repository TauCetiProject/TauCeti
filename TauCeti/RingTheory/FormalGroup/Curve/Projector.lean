/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Arithmetic
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Group.Idempotent

/-!
# Elementary Cartier projectors on curves

When `n` is invertible in the coefficient ring, multiplication by `n` on the group of curves
is an automorphism. The elementary Cartier projector
`γ ↦ γ - V_n ([n]⁻¹ (f_n γ))` projects onto the kernel of `f_n`, along the image of `V_n`.
It preserves coefficients below degree `n`. Over a rational algebra, its effect on the formal
logarithm is to delete precisely the degrees divisible by `n`.

These are the individual factors in Cartier's prime-to-`p` projection onto typical curves;
this file constructs individual factors, without taking an infinite product.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]
variable (F : FormalGroup R) [F.IsComm]

/-- The elementary Cartier projector `1 - V_n [n]⁻¹ f_n`, for `n` invertible in `R`. -/
noncomputable def cartierProjectorCurve (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    F.Curve →+ F.Curve :=
  AddMonoidHom.id F.Curve -
    (F.verschiebungCurve n hn).comp
      ((F.nsmulCurveEquiv n hunit).symm.toAddMonoidHom.comp (F.frobeniusCurve n hn))

/-- The characteristic formula for the elementary Cartier projector. -/
theorem cartierProjectorCurve_apply (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R))
    (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit γ =
      γ - F.verschiebungCurve n hn ((F.nsmulCurveEquiv n hunit).symm
        (F.frobeniusCurve n hn γ)) := (rfl)

/-- The image of the elementary Cartier projector is killed by `f_n`. -/
@[simp]
theorem frobeniusCurve_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.cartierProjectorCurve n hn hunit γ) = 0 := by
  simp [cartierProjectorCurve_apply]

/-- The elementary Cartier projector kills every Verschiebung of the same index. -/
@[simp]
theorem cartierProjectorCurve_verschiebungCurve (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit (F.verschiebungCurve n hn γ) = 0 := by
  simp [cartierProjectorCurve_apply]

/-- A curve killed by Frobenius is fixed by the corresponding Cartier projector. -/
theorem cartierProjectorCurve_eq_self (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R))
    {γ : F.Curve} (hγ : F.frobeniusCurve n hn γ = 0) :
    F.cartierProjectorCurve n hn hunit γ = γ := by
  simp [cartierProjectorCurve_apply, hγ]

/-- The fixed curves of the elementary Cartier projector are exactly `ker f_n`. -/
theorem cartierProjectorCurve_eq_self_iff (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit γ = γ ↔ F.frobeniusCurve n hn γ = 0 := by
  constructor
  · intro h
    rw [← h]
    exact F.frobeniusCurve_cartierProjectorCurve n hn hunit γ
  · exact F.cartierProjectorCurve_eq_self n hn hunit

/-- The elementary Cartier projector is idempotent. -/
@[simp]
theorem cartierProjectorCurve_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit (F.cartierProjectorCurve n hn hunit γ) =
      F.cartierProjectorCurve n hn hunit γ :=
  F.cartierProjectorCurve_eq_self n hn hunit
    (F.frobeniusCurve_cartierProjectorCurve n hn hunit γ)

/-- The Cartier projector is an idempotent in the endomorphism ring of curves. -/
theorem isIdempotentElem_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.cartierProjectorCurve n hn hunit) := by
  apply AddMonoidHom.ext
  intro γ
  exact F.cartierProjectorCurve_cartierProjectorCurve n hn hunit γ

/-- Every curve decomposes into its Cartier projection and a Verschiebung. -/
theorem cartierProjectorCurve_add_verschiebungCurve (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit γ +
      F.verschiebungCurve n hn ((F.nsmulCurveEquiv n hunit).symm
        (F.frobeniusCurve n hn γ)) = γ := by
  rw [cartierProjectorCurve_apply, sub_add_cancel]

/-- The Cartier projector has precisely the Frobenius kernel as its image. -/
theorem range_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    (F.cartierProjectorCurve n hn hunit).range = (F.frobeniusCurve n hn).ker := by
  ext γ
  constructor
  · rintro ⟨δ, rfl⟩
    exact F.frobeniusCurve_cartierProjectorCurve n hn hunit δ
  · intro hγ
    exact ⟨γ, F.cartierProjectorCurve_eq_self n hn hunit hγ⟩

/-- The kernel of the Cartier projector is precisely the Verschiebung image. -/
theorem ker_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    (F.cartierProjectorCurve n hn hunit).ker = (F.verschiebungCurve n hn).range := by
  ext γ
  constructor
  · intro hγ
    exact ⟨_, (sub_eq_zero.mp ((F.cartierProjectorCurve_apply n hn hunit γ).symm.trans hγ)).symm⟩
  · rintro ⟨δ, rfl⟩
    exact F.cartierProjectorCurve_verschiebungCurve n hn hunit δ

/-- Frobenius is surjective when its index is invertible in the coefficient ring. -/
theorem frobeniusCurve_surjective_of_isUnit (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) : Function.Surjective (F.frobeniusCurve n hn) := by
  intro γ
  exact ⟨F.verschiebungCurve n hn ((F.nsmulCurveEquiv n hunit).symm γ), by simp⟩

/-- A curve has a unique decomposition into a curve killed by `f_n` and a curve in the image
of `V_n`. The second coordinate is the parameter of that Verschiebung. -/
noncomputable def cartierCurveEquiv (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    F.Curve ≃+ (F.frobeniusCurve n hn).ker × F.Curve where
  toFun γ :=
    (⟨F.cartierProjectorCurve n hn hunit γ, F.frobeniusCurve_cartierProjectorCurve n hn hunit γ⟩,
      (F.nsmulCurveEquiv n hunit).symm (F.frobeniusCurve n hn γ))
  invFun δ := δ.1.val + F.verschiebungCurve n hn δ.2
  left_inv := F.cartierProjectorCurve_add_verschiebungCurve n hn hunit
  right_inv := by
    rintro ⟨⟨δ, hδ⟩, ε⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [F.cartierProjectorCurve_eq_self n hn hunit hδ]
    · have hδ' : F.frobeniusCurve n hn δ = 0 := hδ
      simp [hδ']
  map_add' γ δ := by
    apply Prod.ext
    · exact Subtype.ext (map_add _ γ δ)
    · simp

/-- The first coordinate of the Cartier decomposition is the Cartier projection. -/
@[simp]
theorem cartierCurveEquiv_fst (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    ((F.cartierCurveEquiv n hn hunit γ).1 : F.Curve) =
      F.cartierProjectorCurve n hn hunit γ := (rfl)

/-- The second coordinate of the Cartier decomposition is normalized Frobenius. -/
@[simp]
theorem cartierCurveEquiv_snd (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    (F.cartierCurveEquiv n hn hunit γ).2 =
      (F.nsmulCurveEquiv n hunit).symm (F.frobeniusCurve n hn γ) := (rfl)

/-- The inverse Cartier decomposition adds a Frobenius-kernel curve to a Verschiebung. -/
theorem cartierCurveEquiv_symm_apply (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R))
    (δ : (F.frobeniusCurve n hn).ker × F.Curve) :
    (F.cartierCurveEquiv n hn hunit).symm δ = δ.1.val + F.verschiebungCurve n hn δ.2 := (rfl)

/-- Base change commutes with the elementary Cartier projector. -/
theorem map_cartierProjectorCurve (φ : R →+* S) (n : ℕ) (hn : n ≠ 0)
    (hR : IsUnit (n : R)) (γ : F.Curve) :
    Curve.map φ (F.cartierProjectorCurve n hn hR γ) =
      (F.map φ).cartierProjectorCurve n hn (by simpa using hR.map φ) (Curve.map φ γ) := by
  simp only [cartierProjectorCurve_apply, map_sub, map_verschiebungCurve,
    F.map_nsmulCurveEquiv_symm (Curve.map φ) n hR (by simpa using hR.map φ), map_frobeniusCurve]

/-- Formal-group homomorphisms commute with the elementary Cartier projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_cartierProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    f.mapCurve (F.cartierProjectorCurve n hn hunit γ) =
      G.cartierProjectorCurve n hn hunit (f.mapCurve γ) := by
  simp only [cartierProjectorCurve_apply, map_sub, f.mapCurve_verschiebungCurve,
    F.map_nsmulCurveEquiv_symm f.mapCurve n hunit hunit, f.mapCurve_frobeniusCurve]

/-- Projecting at index `n` leaves all coefficients of degree `< n` unchanged. -/
theorem coeff_cartierProjectorCurve_of_lt (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) {k : ℕ} (hk : k < n) (γ : F.Curve) :
    PowerSeries.coeff k (F.cartierProjectorCurve n hn hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  rw [cartierProjectorCurve_apply, sub_eq_add_neg, ← map_neg]
  exact Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero _ _ hk
    (fun i hi ↦ F.coeff_verschiebungCurve_eq_zero_of_lt hn hi _)

/-- At coprime indices, a Cartier projector commutes with Verschiebung. -/
theorem cartierProjectorCurve_verschiebungCurve_of_coprime {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hunit : IsUnit (m : R)) (hcop : m.Coprime n) (γ : F.Curve) :
    F.cartierProjectorCurve m hm hunit (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.cartierProjectorCurve m hm hunit γ) := by
  have hV (δ : F.Curve) :
      F.verschiebungCurve m hm (F.verschiebungCurve n hn δ) =
        F.verschiebungCurve n hn (F.verschiebungCurve m hm δ) := by
    rw [verschiebungCurve_verschiebungCurve, verschiebungCurve_verschiebungCurve]
    exact F.verschiebungCurve_congr (Nat.mul_comm m n) _ _ δ
  rw [cartierProjectorCurve_apply, cartierProjectorCurve_apply, map_sub,
    frobeniusCurve_verschiebungCurve_of_coprime F hm hn hcop,
    ← F.map_nsmulCurveEquiv_symm (F.verschiebungCurve n hn) m hunit hunit, hV]

/-- At coprime indices, Frobenius commutes with a Cartier projector. -/
theorem frobeniusCurve_cartierProjectorCurve_of_coprime {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hunit : IsUnit (n : R)) (hcop : m.Coprime n) (γ : F.Curve) :
    F.frobeniusCurve m hm (F.cartierProjectorCurve n hn hunit γ) =
      F.cartierProjectorCurve n hn hunit (F.frobeniusCurve m hm γ) := by
  have hf : F.frobeniusCurve m hm (F.frobeniusCurve n hn γ) =
      F.frobeniusCurve n hn (F.frobeniusCurve m hm γ) := by
    rw [frobeniusCurve_frobeniusCurve, frobeniusCurve_frobeniusCurve]
    exact F.frobeniusCurve_congr (Nat.mul_comm m n) _ _ γ
  rw [cartierProjectorCurve_apply, cartierProjectorCurve_apply, map_sub,
    frobeniusCurve_verschiebungCurve_of_coprime F hm hn hcop,
    F.map_nsmulCurveEquiv_symm (F.frobeniusCurve m hm) n hunit hunit, hf]

/-- Elementary Cartier projectors at coprime indices commute. -/
theorem cartierProjectorCurve_cartierProjectorCurve_of_coprime {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hR : IsUnit (m : R)) (hS : IsUnit (n : R)) (hcop : m.Coprime n)
    (γ : F.Curve) :
    F.cartierProjectorCurve m hm hR (F.cartierProjectorCurve n hn hS γ) =
      F.cartierProjectorCurve n hn hS (F.cartierProjectorCurve m hm hR γ) := by
  rw [cartierProjectorCurve_apply F n hn hS, map_sub,
    cartierProjectorCurve_verschiebungCurve_of_coprime F hm hn hR hcop,
    F.map_nsmulCurveEquiv_symm (F.cartierProjectorCurve m hm hR) n hS hS,
    ← frobeniusCurve_cartierProjectorCurve_of_coprime F hn hm hR hcop.symm,
    ← cartierProjectorCurve_apply]

/-- On the formal logarithm, the elementary Cartier projector deletes precisely the coefficients
whose degrees are divisible by its index. -/
theorem coeff_subst_cartierProjectorCurve_log [Algebra ℚ R] (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k (PowerSeries.subst
      (F.cartierProjectorCurve n hn hunit γ).toPowerSeries F.log) =
      if n ∣ k then 0 else PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  let L : F.Curve →+ PowerSeries R :=
    Curve.additiveToPowerSeriesHom.comp F.logHom.mapCurve
  have hL (δ : F.Curve) : L δ = PowerSeries.subst δ.toPowerSeries F.log := by
    simp [L]
  have hdiv (δ : F.Curve) : n • L ((F.nsmulCurveEquiv n hunit).symm δ) = L δ := by
    rw [← map_nsmul, nsmul_nsmulCurveEquiv_symm]
  have hV (δ : F.Curve) : L (F.verschiebungCurve n hn δ) =
      PowerSeries.expand n hn (L δ) := by
    simp only [hL, subst_verschiebungCurve_log]
  have hf : L (F.frobeniusCurve n hn γ) =
      (n : R) • PowerSeries.cartier R n 0 (L γ) := by
    simp only [hL, subst_frobeniusCurve_log]
  simp only [← hL]
  rw [cartierProjectorCurve_apply, map_sub, hV, map_sub]
  by_cases hdvd : n ∣ k
  · obtain ⟨j, rfl⟩ := hdvd
    rw [ite_eq_left ⟨j, rfl⟩, PowerSeries.coeff_expand_mul n hn]
    apply sub_eq_zero.mpr
    apply hunit.mul_left_cancel
    have h := congrArg (PowerSeries.coeff j) (hdiv (F.frobeniusCurve n hn γ))
    simp only [map_nsmul] at h
    simpa only [nsmul_eq_mul, hf, PowerSeries.coeff_smul,
      PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul] using h.symm
  · rw [ite_eq_right hdvd, PowerSeries.coeff_expand_of_not_dvd n hn _ hdvd, sub_zero]

/-- The logarithm of a projected curve is obtained by subtracting the part supported in degrees
divisible by `n`. -/
theorem subst_cartierProjectorCurve_log [Algebra ℚ R] (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    PowerSeries.subst (F.cartierProjectorCurve n hn hunit γ).toPowerSeries F.log =
      PowerSeries.subst γ.toPowerSeries F.log -
        PowerSeries.expand n hn (PowerSeries.cartier R n 0
          (PowerSeries.subst γ.toPowerSeries F.log)) := by
  ext k
  rw [coeff_subst_cartierProjectorCurve_log, map_sub, PowerSeries.coeff_expand]
  by_cases hdvd : n ∣ k
  · rw [ite_eq_left hdvd, ite_eq_left hdvd, PowerSeries.coeff_cartier, Nat.add_zero,
      Nat.mul_div_cancel' hdvd, sub_self]
  · rw [ite_eq_right hdvd, ite_eq_right hdvd, sub_zero]

end FormalGroup
