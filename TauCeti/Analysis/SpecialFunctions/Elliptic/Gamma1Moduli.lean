/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Pointed
public import TauCeti.Analysis.SpecialFunctions.Elliptic.LatticeClassification
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.GammaSet

/-!
# The complex moduli of elliptic curves with a point of order `N`

A point `z` of the upper half-plane gives the complex elliptic curve `E_z = ℂ / (ℤ z + ℤ)`, in its
Weierstrass model `y² = x³ - (g₂ / 4) x - g₃ / 4` (`PeriodPair.weierstrassCurve`), together with
the point `P_z` of exact order `N` given by `1 / N`
(`UpperHalfPlane.pointedWeierstrassCurve`). This file proves that `z ↦ (E_z, P_z)` induces a
bijection from `Γ₁(N) \ ℍ` onto the isomorphism classes of pairs `(E, P)` of an elliptic curve
over `ℂ` and a point `P ∈ E(ℂ)` of exact order `N` (`TauCeti.gamma1QuotientEquivExactOrder`). An
isomorphism of such pairs is a change of variables of Weierstrass curves carrying one marked point
to the other, so the isomorphism classes are the orbits of the sub-action
`TauCeti.PointedWeierstrassCurve.exactOrder ℂ N`.

A choice of primitive `N`-th root of unity identifies points of exact order `N` with embeddings
`μ_N ↪ E[N]`, so this is also the complex moduli description of the `μ_N`-marked curves. It is the
input that identifies `Γ₁(N) \ ℍ` with the complex points of the modular curve `Y₁(N)`.

* **Surjectivity.** Every elliptic curve over `ℂ` is a change of variables of some `E_τ`
  (`WeierstrassCurve.exists_variableChange_smul_weierstrassCurve_periodPair_eq`), and its point
  of order `N` is then the image of `(m τ + n) / N` with `gcd(m, n)` prime to `N`. Such a pair is
  congruent modulo `N` to a coprime pair (`TauCeti.EisensteinSeries.nonempty_gammaSet_intCast_iff`),
  the bottom row of some `γ ∈ SL(2, ℤ)`, and rescaling the lattice by `(c τ + d)⁻¹` carries
  `(E_τ, (m τ + n) / N)` to `(E_{γ τ}, 1 / N)`.
* **Injectivity.** A change of variables between lattice curves is a rescaling `u` of the lattices
  (`PeriodPair.lattice_eq_smul_of_variableChange_smul_eq`), and a rescaling `ℤ z' + ℤ = u (ℤ z + ℤ)`
  comes from `γ ∈ SL(2, ℤ)` with `γ z' = z` and `u = c z' + d`
  (`UpperHalfPlane.exists_smul_eq_and_denom_eq_of_lattice_periodPair_eq`). The rescaling carries
  `1 / N` to `u / N`, which is `1 / N` modulo `ℤ z' + ℤ` exactly when `c ≡ 0` and `d ≡ 1 mod N`,
  that is, when `γ ∈ Γ₁(N)`.

## Main definitions

* `UpperHalfPlane.pointedWeierstrassCurve N z`: the curve `E_z` with the point given by `1 / N`.
* `TauCeti.gamma1QuotientEquivExactOrder N`: the bijection from `Γ₁(N) \ ℍ` to the isomorphism
  classes of complex elliptic curves with a point of exact order `N`.

## Main results

* `UpperHalfPlane.addOrderOf_weierstrassPoint_one_div`: `1 / N` has exact order `N` on `E_z`.
* `UpperHalfPlane.smul_mk_weierstrassPoint_denom_div`: rescaling by `(c z + d)⁻¹` carries `E_z`
  with the point of `(c z + d) / N` to `(E_{γ z}, P_{γ z})`.
* `UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq`: every complex elliptic curve with a
  point of exact order `N` is isomorphic to some `(E_z, P_z)`.
* `UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq_iff`: `(E_z, P_z)` and `(E_{z'}, P_{z'})`
  are isomorphic exactly when `z' ∈ Γ₁(N) z`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, Theorem 1.5.1.
* J. S. Milne, *Modular Functions and Modular Forms*, Lemma 8.7.
-/

public section

open Complex UpperHalfPlane WeierstrassCurve CongruenceSubgroup TauCeti
open scoped MatrixGroups

namespace UpperHalfPlane

variable {N : ℕ}

variable (N) in
/-- The complex elliptic curve `E_z = ℂ / (ℤ z + ℤ)`, in its Weierstrass model
`y² = x³ - (g₂ / 4) x - g₃ / 4`, with the point given by `1 / N`. For `N ≠ 0` this point has exact
order `N` (`UpperHalfPlane.addOrderOf_weierstrassPoint_one_div`). -/
noncomputable def pointedWeierstrassCurve (z : ℍ) : PointedWeierstrassCurve ℂ :=
  ⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint (1 / N)⟩

/-- The defining equation of `UpperHalfPlane.pointedWeierstrassCurve`. -/
theorem pointedWeierstrassCurve_def (z : ℍ) :
    z.pointedWeierstrassCurve N =
      ⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint (1 / N)⟩ :=
  (rfl)

@[simp]
theorem pointedWeierstrassCurve_curve (z : ℍ) :
    (z.pointedWeierstrassCurve N).curve = z.periodPair.weierstrassCurve :=
  (rfl)

/-- The point of `1 / N` on `E_z` has exact order `N`. -/
theorem addOrderOf_weierstrassPoint_one_div [NeZero N] (z : ℍ) :
    addOrderOf (z.periodPair.weierstrassPoint (1 / N)) = N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine (addOrderOf_eq_iff (Nat.pos_of_neZero N)).mpr ⟨?_, fun m hm hm₀ ↦ ?_⟩
  · rw [PeriodPair.nsmul_weierstrassPoint, mul_one_div_cancel hN,
      PeriodPair.weierstrassPoint_eq_zero_iff]
    simpa using z.periodPair.ω₂_mem_lattice
  · rw [PeriodPair.nsmul_weierstrassPoint, Ne, PeriodPair.weierstrassPoint_eq_zero_iff]
    intro hmem
    have h := congrFun (intCast_comp_eq_zero_of_div_mem_lattice_periodPair (N := N) (b := ![0, m])
      (z := z) (by convert hmem using 1; simp [div_eq_mul_inv])) 1
    simp only [Function.comp_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_natCast,
      Pi.zero_apply, ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hm₀ h) (not_le.mpr hm)

/-- The pair `(E_z, P_z)` is an elliptic curve with a point of exact order `N`. -/
theorem pointedWeierstrassCurve_mem_exactOrder [NeZero N] (z : ℍ) :
    z.pointedWeierstrassCurve N ∈ PointedWeierstrassCurve.exactOrder ℂ N :=
  (PointedWeierstrassCurve.mem_exactOrder_iff _).mpr
    ⟨inferInstanceAs z.periodPair.weierstrassCurve.IsElliptic,
      addOrderOf_weierstrassPoint_one_div z⟩

variable (N) in
/-- **Rescaling by `(c z + d)⁻¹` gives `(E_{γ z}, P_{γ z})`**: the change of variables with
`u = (c z + d)⁻¹` carries `E_z` with the point of `(c z + d) / N` to `E_{γ z}` with the point of
`1 / N`. -/
theorem smul_mk_weierstrassPoint_denom_div (γ : SL(2, ℤ)) (z : ℍ) :
    (⟨(Units.mk0 _ (denom_ne_zero γ z))⁻¹, 0, 0, 0⟩ : VariableChange ℂ) •
        (⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint (denom γ z / N)⟩ :
          PointedWeierstrassCurve ℂ) =
      (γ • z).pointedWeierstrassCurve N := by
  rw [PeriodPair.smul_mk_weierstrassPoint (lattice_periodPair_smul γ z),
    pointedWeierstrassCurve_def, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_eq_div,
    div_div_cancel_left₀ (denom_ne_zero γ z), one_div]

/-- If the point of `(m τ + n) / N` on `E_τ` has exact order `N`, then `gcd(m, n)` is prime to `N`:
for `d = gcd(m, n, N)` the multiple `(N / d) • P` is the point of the period `(m / d) τ + n / d`. -/
private lemma coprime_gcd_of_addOrderOf_weierstrassPoint [NeZero N] {τ : ℍ} {m n : ℤ}
    (h : addOrderOf (τ.periodPair.weierstrassPoint ((m * τ + n) / N)) = N) :
    Nat.Coprime (Int.gcd m n) N := by
  set d := Nat.gcd (Int.gcd m n) N
  have hdN : d ∣ N := Nat.gcd_dvd_right _ N
  obtain ⟨m', hm'⟩ := (Int.natCast_dvd.mpr ((Nat.gcd_dvd_left _ N).trans
    (Int.gcd_dvd_natAbs_left m n)) : (d : ℤ) ∣ m)
  obtain ⟨n', hn'⟩ := (Int.natCast_dvd.mpr ((Nat.gcd_dvd_left _ N).trans
    (Int.gcd_dvd_natAbs_right m n)) : (d : ℤ) ∣ n)
  have hd₀ : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_right _
    (Nat.pos_of_neZero N)).ne'
  have hzero : (N / d) • τ.periodPair.weierstrassPoint ((m * τ + n) / N) = 0 := by
    rw [PeriodPair.nsmul_weierstrassPoint, PeriodPair.weierstrassPoint_eq_zero_iff,
      Nat.cast_div hdN hd₀]
    convert intCast_mul_add_intCast_mem_lattice_periodPair τ m' n' using 1
    rw [hm', hn']
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
    push_cast
    ring
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hzero
  rw [h] at hdvd
  exact (Nat.div_eq_self.mp (Nat.dvd_antisymm (Nat.div_dvd_of_dvd hdN) hdvd)).resolve_left
    (NeZero.ne N)

/-- **Every complex elliptic curve with a point of exact order `N` is some `(E_z, P_z)`**: it is
isomorphic, by a change of variables, to `E_z` with the point given by `1 / N`. -/
theorem exists_smul_pointedWeierstrassCurve_eq [NeZero N] {X : PointedWeierstrassCurve ℂ}
    (hX : X ∈ PointedWeierstrassCurve.exactOrder ℂ N) :
    ∃ (z : ℍ) (C : VariableChange ℂ), C • z.pointedWeierstrassCurve N = X := by
  obtain ⟨hE, hN⟩ := (PointedWeierstrassCurve.mem_exactOrder_iff X).mp hX
  -- Move `X` onto the lattice curve `E_τ`, where its point is the image of some `w`.
  obtain ⟨τ, C, hC⟩ := X.curve.exists_variableChange_smul_weierstrassCurve_periodPair_eq
  obtain ⟨Q, hQ⟩ := PointedWeierstrassCurve.exists_eq_mk (X := C⁻¹ • X)
    (W := τ.periodPair.weierstrassCurve) (by rw [PointedWeierstrassCurve.smul_curve, ← hC,
      inv_smul_smul])
  have hQN : addOrderOf Q = N := by
    rw [← PointedWeierstrassCurve.addOrderOf_smul_point C⁻¹ X, hQ] at hN
    exact hN
  obtain ⟨w, rfl⟩ := τ.periodPair.weierstrassPoint_surjective Q
  -- `N w = m τ + n` is a period, and `(m, n)` is the bottom row of some `γ` modulo `N`.
  have hNw : (N : ℂ) * w ∈ τ.periodPair.lattice := by
    rw [← PeriodPair.weierstrassPoint_eq_zero_iff, ← PeriodPair.nsmul_weierstrassPoint, ← hQN,
      addOrderOf_nsmul_eq_zero]
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hNw
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one] at hmn
  have hN₀ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hw : w = (m * τ + n) / N := by rw [hmn, mul_div_cancel_left₀ _ hN₀]
  obtain ⟨y, hy, hy₁⟩ := (EisensteinSeries.nonempty_gammaSet_intCast_iff ![m, n]).mpr
    (by simpa using coprime_gcd_of_addOrderOf_weierstrassPoint (hw ▸ hQN))
  obtain ⟨γ, hγ₀, hγ₁⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hy₁).exists_SL2_row 1
  replace hγ₀ : ((γ 1 0 : ℤ) : ZMod N) = m := by simpa [hγ₀] using congrFun hy 0
  replace hγ₁ : ((γ 1 1 : ℤ) : ZMod N) = n := by simpa [hγ₁] using congrFun hy 1
  -- `w = (m τ + n) / N` is `(c τ + d) / N` modulo `ℤ τ + ℤ`; rescale by `(c τ + d)⁻¹`.
  have hwD : τ.periodPair.weierstrassPoint w = τ.periodPair.weierstrassPoint (denom γ τ / N) := by
    rw [PeriodPair.weierstrassPoint_eq_weierstrassPoint_iff, hw]
    convert div_mem_lattice_periodPair_of_intCast_comp_eq_zero (N := N)
      (b := ![m - γ 1 0, n - γ 1 1]) τ (by ext i; fin_cases i <;> simp [hγ₀, hγ₁]) using 1
    simp only [ModularGroup.denom_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    push_cast
    ring
  refine ⟨γ • τ, (⟨(Units.mk0 _ (denom_ne_zero γ τ))⁻¹, 0, 0, 0⟩ * C⁻¹)⁻¹, ?_⟩
  rw [inv_smul_eq_iff, mul_smul, hQ, hwD, smul_mk_weierstrassPoint_denom_div]

/-- **Isomorphic pairs `(E_z, P_z)` are `Γ₁(N)`-equivalent**: `(E_z, P_z)` and `(E_{z'}, P_{z'})`
are isomorphic by a change of variables exactly when `z' = γ z` for some `γ ∈ Γ₁(N)`. -/
theorem exists_smul_pointedWeierstrassCurve_eq_iff [NeZero N] {z z' : ℍ} :
    (∃ C : VariableChange ℂ, C • z.pointedWeierstrassCurve N = z'.pointedWeierstrassCurve N) ↔
      ∃ γ ∈ Gamma1 N, γ • z = z' := by
  constructor
  · rintro ⟨C, hC⟩
    -- The change of variables is a rescaling `u` of the lattices, with `u = c z' + d`.
    have hcurve : C • z.periodPair.weierstrassCurve = z'.periodPair.weierstrassCurve :=
      congrArg PointedWeierstrassCurve.curve hC
    have hlat := PeriodPair.lattice_eq_smul_of_variableChange_smul_eq hcurve
    rw [PeriodPair.variableChange_eq_mk_of_smul_eq hcurve, pointedWeierstrassCurve_def,
      pointedWeierstrassCurve_def, PeriodPair.smul_mk_weierstrassPoint hlat,
      PointedWeierstrassCurve.mk_inj,
      PeriodPair.weierstrassPoint_eq_weierstrassPoint_iff] at hC
    obtain ⟨σ, hσ, hden⟩ := exists_smul_eq_and_denom_eq_of_lattice_periodPair_eq hlat
    -- `u / N - 1 / N = (c z' + (d - 1)) / N` is a period, so `c ≡ 0` and `d ≡ 1 mod N`.
    have hmod := intCast_comp_eq_zero_of_div_mem_lattice_periodPair (N := N)
      (b := ![σ 1 0, σ 1 1 - 1]) (z := z') (by
        convert hC using 1
        rw [← hden, ModularGroup.denom_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        push_cast
        ring)
    have h₀ : ((σ 1 0 : ℤ) : ZMod N) = 0 := by simpa using congrFun hmod 0
    have h₁ : ((σ 1 1 : ℤ) : ZMod N) = 1 := by
      simpa [sub_eq_zero] using congrFun hmod 1
    have hσ₁ : σ ∈ Gamma1 N := by
      refine (Gamma1_mem N σ).mpr ⟨?_, h₁, h₀⟩
      simpa [h₀, h₁] using Matrix.SpecialLinearGroup.intCast_fin_two_mul_sub_mul_eq_one
        (R := ZMod N) σ
    exact ⟨σ⁻¹, inv_mem hσ₁, by rw [← hσ, inv_smul_smul]⟩
  · rintro ⟨γ, hγ, rfl⟩
    -- For `γ ∈ Γ₁(N)`, `1 / N` is `(c z + d) / N` modulo `ℤ z + ℤ`; rescale by `(c z + d)⁻¹`.
    obtain ⟨-, h₁, h₀⟩ := (Gamma1_mem N γ).mp hγ
    have hD : z.periodPair.weierstrassPoint (1 / N) =
        z.periodPair.weierstrassPoint (denom γ z / N) := by
      rw [PeriodPair.weierstrassPoint_eq_weierstrassPoint_iff]
      convert div_mem_lattice_periodPair_of_intCast_comp_eq_zero (N := N)
        (b := ![-γ 1 0, 1 - γ 1 1]) z (by ext i; fin_cases i <;> simp [h₀, h₁]) using 1
      simp only [ModularGroup.denom_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      push_cast
      ring
    refine ⟨⟨(Units.mk0 _ (denom_ne_zero γ z))⁻¹, 0, 0, 0⟩, ?_⟩
    rw [pointedWeierstrassCurve_def z, hD, smul_mk_weierstrassPoint_denom_div]

end UpperHalfPlane

namespace TauCeti

variable (N : ℕ) [NeZero N]

/-- **The moduli bijection for `Γ₁(N)`**: `z ↦ (E_z, P_z)`, the curve `ℂ / (ℤ z + ℤ)` with the
point given by `1 / N`, induces a bijection from `Γ₁(N) \ ℍ` onto the isomorphism classes of
complex elliptic curves with a point of exact order `N`. -/
noncomputable def gamma1QuotientEquivExactOrder :
    MulAction.orbitRel.Quotient (Gamma1 N) ℍ ≃
      MulAction.orbitRel.Quotient (VariableChange ℂ) (PointedWeierstrassCurve.exactOrder ℂ N) :=
  Equiv.ofBijective
    (Quotient.map (fun z ↦ ⟨z.pointedWeierstrassCurve N, z.pointedWeierstrassCurve_mem_exactOrder⟩)
      fun z z' h ↦ by
        obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
        obtain ⟨C, hC⟩ := UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq_iff.mpr
          ⟨γ, γ.2, hγ⟩
        exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨C, Subtype.ext hC⟩))
    ⟨fun q q' ↦ Quotient.inductionOn₂ q q' fun z z' h ↦ by
        obtain ⟨C, hC⟩ := MulAction.mem_orbit_iff.mp
          (MulAction.orbitRel_apply.mp (Quotient.exact h))
        obtain ⟨γ, hγ, hγz⟩ := UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq_iff.mp
          ⟨C, congrArg Subtype.val hC⟩
        exact Quotient.sound (MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr ⟨⟨γ, hγ⟩, hγz⟩)),
      fun q ↦ Quotient.inductionOn q fun X ↦ by
        obtain ⟨z, C, hC⟩ := UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq X.2
        exact ⟨⟦z⟧, Quotient.sound (MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr
            ⟨C⁻¹, Subtype.ext (by rw [SubMulAction.val_smul, ← hC, inv_smul_smul])⟩))⟩⟩

@[simp]
theorem gamma1QuotientEquivExactOrder_mk (z : ℍ) :
    gamma1QuotientEquivExactOrder N ⟦z⟧ =
      ⟦⟨z.pointedWeierstrassCurve N, z.pointedWeierstrassCurve_mem_exactOrder⟩⟧ :=
  (rfl)

end TauCeti
