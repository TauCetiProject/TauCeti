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

For a commutative formal group law `F`, when `n` is invertible in the coefficient ring,
multiplication by `n` on the group of curves is an automorphism. The elementary Cartier projector
`γ ↦ γ - V_n ([n]⁻¹ (f_n γ))` projects onto the kernel of `f_n`, along the image of `V_n`.
It preserves coefficients below degree `n`. Over a rational algebra, its effect on the formal
logarithm is to delete precisely the degrees divisible by `n`.

These are the individual factors in Cartier's prime-to-`p` projection onto typical curves;
their infinite composite is `FormalGroup.typicalProjectorCurve` in
`TauCeti.RingTheory.FormalGroup.Curve.Typical`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]
variable (F : FormalGroup R) [F.IsComm]

/-- The elementary Cartier projector `1 - V_n [n]⁻¹ f_n` on curves of a commutative formal
group law, for `n` invertible in `R`. -/
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

/-- The elementary Cartier projector at index one is zero. -/
@[simp]
theorem cartierProjectorCurve_one (hn : (1 : ℕ) ≠ 0) (hunit : IsUnit ((1 : ℕ) : R)) :
    F.cartierProjectorCurve 1 hn hunit = 0 := by
  ext γ
  simp [cartierProjectorCurve_apply]

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
@[simp]
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
@[simp]
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
@[simp]
theorem range_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    (F.cartierProjectorCurve n hn hunit).range = (F.frobeniusCurve n hn).ker := by
  ext γ
  simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨δ, rfl⟩
    exact F.frobeniusCurve_cartierProjectorCurve n hn hunit δ
  · intro hγ
    exact ⟨γ, F.cartierProjectorCurve_eq_self n hn hunit hγ⟩

/-- The kernel of the Cartier projector is precisely the Verschiebung image. -/
@[simp]
theorem ker_cartierProjectorCurve (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    (F.cartierProjectorCurve n hn hunit).ker = (F.verschiebungCurve n hn).range := by
  ext γ
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  constructor
  · intro hγ
    exact ⟨_, (sub_eq_zero.mp ((F.cartierProjectorCurve_apply n hn hunit γ).symm.trans hγ)).symm⟩
  · rintro ⟨δ, rfl⟩
    exact F.cartierProjectorCurve_verschiebungCurve n hn hunit δ

/-- A curve is killed by the Cartier projector exactly when it is a Verschiebung. -/
theorem cartierProjectorCurve_eq_zero_iff (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit γ = 0 ↔ ∃ δ, F.verschiebungCurve n hn δ = γ := by
  rw [← AddMonoidHom.mem_ker, ker_cartierProjectorCurve, AddMonoidHom.mem_range]

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
    (⟨F.cartierProjectorCurve n hn hunit γ,
      AddMonoidHom.mem_ker.mpr (F.frobeniusCurve_cartierProjectorCurve n hn hunit γ)⟩,
      (F.nsmulCurveEquiv n hunit).symm (F.frobeniusCurve n hn γ))
  invFun δ := δ.1.val + F.verschiebungCurve n hn δ.2
  left_inv := F.cartierProjectorCurve_add_verschiebungCurve n hn hunit
  right_inv := by
    rintro ⟨⟨δ, hδ⟩, ε⟩
    rw [AddMonoidHom.mem_ker] at hδ
    apply Prod.ext
    · apply Subtype.ext
      simp [F.cartierProjectorCurve_eq_self n hn hunit hδ]
    · simp [hδ]
  map_add' γ δ := by
    apply Prod.ext
    · exact Subtype.ext (map_add _ γ δ)
    · simp

/-- The first coordinate of the Cartier decomposition is the Cartier projection. -/
@[simp]
theorem coe_cartierCurveEquiv_fst (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) (γ : F.Curve) :
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

/-- On the additive formal group, the Cartier projector subtracts the part supported in
degrees divisible by its index. -/
@[simp]
theorem toPowerSeries_cartierProjectorCurve_𝔾ₐ (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : (𝔾ₐ (R := R)).Curve) :
    ((𝔾ₐ (R := R)).cartierProjectorCurve n hn hunit γ).toPowerSeries =
      γ.toPowerSeries - PowerSeries.expand n hn (PowerSeries.cartier R n 0 γ.toPowerSeries) := by
  have hnorm : (((𝔾ₐ (R := R)).nsmulCurveEquiv n hunit).symm
      ((𝔾ₐ (R := R)).frobeniusCurve n hn γ)).toPowerSeries =
      PowerSeries.cartier R n 0 γ.toPowerSeries := by
    apply hunit.smul_left_cancel.mp
    rw [Nat.cast_smul_eq_nsmul R, ← Curve.additiveToPowerSeriesHom_apply, ← map_nsmul,
      nsmul_nsmulCurveEquiv_symm, Curve.additiveToPowerSeriesHom_apply,
      toPowerSeries_frobeniusCurve_𝔾ₐ]
  rw [cartierProjectorCurve_apply]
  rw [← Curve.additiveToPowerSeriesHom_apply, map_sub,
    Curve.additiveToPowerSeriesHom_apply, Curve.additiveToPowerSeriesHom_apply,
    toPowerSeries_verschiebungCurve, hnorm]

/-- On the additive formal group, the Cartier projector deletes precisely the coefficients whose
degrees are divisible by its index. -/
theorem coeff_cartierProjectorCurve_𝔾ₐ (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) (k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).cartierProjectorCurve n hn hunit γ).toPowerSeries =
      if n ∣ k then 0 else PowerSeries.coeff k γ.toPowerSeries := by
  rw [toPowerSeries_cartierProjectorCurve_𝔾ₐ, map_sub, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · rw [PowerSeries.coeff_cartier, Nat.add_zero, Nat.mul_div_cancel' hdvd, sub_self]
  · rw [sub_zero]

/-- The logarithm of a projected curve is obtained by subtracting the part supported in degrees
divisible by `n`. -/
theorem subst_cartierProjectorCurve_log [Algebra ℚ R] (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (γ : F.Curve) :
    PowerSeries.subst (F.cartierProjectorCurve n hn hunit γ).toPowerSeries F.log =
      PowerSeries.subst γ.toPowerSeries F.log -
        PowerSeries.expand n hn (PowerSeries.cartier R n 0
          (PowerSeries.subst γ.toPowerSeries F.log)) := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    toPowerSeries_cartierProjectorCurve_𝔾ₐ] using
    congrArg Curve.toPowerSeries (F.logHom.mapCurve_cartierProjectorCurve n hn hunit γ)

/-- On the formal logarithm, the elementary Cartier projector deletes precisely the coefficients
whose degrees are divisible by its index. -/
theorem coeff_subst_cartierProjectorCurve_log [Algebra ℚ R] (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k (PowerSeries.subst
      (F.cartierProjectorCurve n hn hunit γ).toPowerSeries F.log) =
      if n ∣ k then 0 else PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [subst_cartierProjectorCurve_log, map_sub, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · rw [PowerSeries.coeff_cartier, Nat.add_zero, Nat.mul_div_cancel' hdvd, sub_self]
  · rw [sub_zero]

/-- Elementary Cartier projectors commute at arbitrary nonzero invertible indices. -/
theorem cartierProjectorCurve_comm {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hR : IsUnit (m : R)) (hS : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve m hm hR (F.cartierProjectorCurve n hn hS γ) =
      F.cartierProjectorCurve n hn hS (F.cartierProjectorCurve m hm hR γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {m, n}
    (by simpa only [Set.forall_mem_insert, Set.forall_mem_singleton] using And.intro hR hS)
    (fun G _ h δ ↦ G.cartierProjectorCurve m hm (h m (by simp))
      (G.cartierProjectorCurve n hn (h n (by simp)) δ))
    (fun G _ h δ ↦ G.cartierProjectorCurve n hn (h n (by simp))
      (G.cartierProjectorCurve m hm (h m (by simp)) δ))
    (fun G _ h δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        coeff_subst_cartierProjectorCurve_log]
      split_ifs <;> rfl)
    (fun G _ _ _ φ δ ↦ by rw [map_cartierProjectorCurve, map_cartierProjectorCurve])
    (fun G _ _ _ φ δ ↦ by rw [map_cartierProjectorCurve, map_cartierProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_cartierProjectorCurve, f.mapCurve_cartierProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_cartierProjectorCurve, f.mapCurve_cartierProjectorCurve])

end FormalGroup
