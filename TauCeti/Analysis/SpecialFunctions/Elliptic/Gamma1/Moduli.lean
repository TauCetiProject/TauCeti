/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Pointed.Quotient
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.Pointed
public import TauCeti.Analysis.SpecialFunctions.Elliptic.LatticeClassification
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Diamond
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.GammaSet

/-!
# The complex moduli of elliptic curves with a point of order `N`

Fix a positive level `N`. A point `z` of the upper half-plane gives the complex elliptic curve
`E_z = ℂ / (ℤ z + ℤ)`, in its Weierstrass model `y² = x³ - (g₂ / 4) x - g₃ / 4`
(`PeriodPair.weierstrassCurve`), together with
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

At positive levels the bijection is natural. For `γ ∈ Γ₀(N)` with lower-right entry `d`, the point
`(c z + d) / N` is `d / N` modulo `ℤ z + ℤ`, so the class of `γ z` corresponds to
`(E_z, d • P_z)`: the diamond
operator `⟨d⟩` multiplies the marked point by `d`, that is, it precomposes the embedding
`μ_N ↪ E[N]` with multiplication by `d`. For `M ≠ 0`, the map `Γ₁(N M) \ ℍ → Γ₁(N) \ ℍ`
corresponds to multiplying the marked point by `M`, since `M / (N M) = 1 / N`: it restricts an
embedding `μ_{NM} ↪ E[NM]` to `μ_N`, using compatible primitive roots
`ζ_N = ζ_{NM}^M`, for example `ζ_k = exp(2πi/k)`.

## Main definitions

* `UpperHalfPlane.pointedWeierstrassCurve N z`: the curve `E_z` with the point given by `1 / N`.
* `TauCeti.gamma1QuotientDiamond N`: the diamond action on `Γ₁(N) \ ℍ`, as permutations.
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
* `UpperHalfPlane.smul_mk_zsmul_weierstrassPoint_one_div`: for `γ ∈ Γ₀(N)` with lower-right
  entry `d`, rescaling by `(c z + d)⁻¹` carries `(E_z, d • P_z)` to `(E_{γ z}, P_{γ z})`.
* `TauCeti.gamma1QuotientEquivExactOrder_smul`: the moduli bijection carries the diamond
  operator `⟨d⟩` to multiplication of the marked point by `d`.
* `TauCeti.gamma1QuotientEquivExactOrder_map_of_le`: the moduli bijection carries the map
  `Γ₁(N M) \ ℍ → Γ₁(N) \ ℍ` to multiplication of the marked point by `M`.

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
/-- **Rescaling by `(c z + d)⁻¹` gives `(E_{γ z}, P_{γ z})`**: the change of variables with
`u = (c z + d)⁻¹` carries `E_z` with the point of `(c z + d) / N` to `E_{γ z}` with the point of
`1 / N`. At `N = 0`, both marked points are zero by Lean’s division-by-zero convention. -/
theorem smul_mk_weierstrassPoint_denom_div (γ : SL(2, ℤ)) (z : ℍ) :
    (⟨(Units.mk0 _ (denom_ne_zero γ z))⁻¹, 0, 0, 0⟩ : VariableChange ℂ) •
        (⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint (denom γ z / N)⟩ :
          PointedWeierstrassCurve ℂ) =
      (γ • z).pointedWeierstrassCurve N := by
  rw [PeriodPair.smul_mk_weierstrassPoint (lattice_periodPair_smul γ z),
    pointedWeierstrassCurve_def, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_eq_div,
    div_div_cancel_left₀ (denom_ne_zero γ z), one_div]

/-- If `m ≡ c` and `n ≡ d` modulo `N` for the bottom row `(c, d)` of `γ`, then `(m z + n) / N` is
`(c z + d) / N` modulo `ℤ z + ℤ`, so both give the same point of `E_z`. This specializes
`PeriodPair.weierstrassPoint_div_eq_of_intCast_eq` to the bottom row of `γ`. -/
private lemma weierstrassPoint_div_eq_weierstrassPoint_denom_div {γ : SL(2, ℤ)} {z : ℍ} {m n : ℤ}
    (hm : ((γ 1 0 : ℤ) : ZMod N) = m) (hn : ((γ 1 1 : ℤ) : ZMod N) = n) :
    z.periodPair.weierstrassPoint ((m * z + n) / N) =
      z.periodPair.weierstrassPoint (denom γ z / N) := by
  simpa only [periodPair_ω₁, periodPair_ω₂, mul_one, ModularGroup.denom_apply] using
    (z.periodPair.weierstrassPoint_div_eq_of_intCast_eq N hm hn).symm

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
    rw [hw, weierstrassPoint_div_eq_weierstrassPoint_denom_div hγ₀ hγ₁]
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
      by simpa only [PointedWeierstrassCurve.smul_curve, pointedWeierstrassCurve_curve] using
        congrArg PointedWeierstrassCurve.curve hC
    have hlat := PeriodPair.lattice_eq_smul_of_variableChange_smul_eq hcurve
    rw [PeriodPair.variableChange_eq_mk_of_smul_eq hcurve, pointedWeierstrassCurve_def,
      pointedWeierstrassCurve_def, PeriodPair.smul_mk_weierstrassPoint hlat,
      PointedWeierstrassCurve.mk_inj,
      PeriodPair.weierstrassPoint_eq_weierstrassPoint_iff] at hC
    obtain ⟨σ, hσ, hden⟩ := exists_smul_eq_and_denom_eq_of_lattice_periodPair_eq hlat
    -- `u / N - 1 / N = (c z' + (d - 1)) / N` is a period, so `c ≡ 0` and `d ≡ 1 mod N`.
    obtain ⟨h₀, h₁⟩ := (z'.periodPair.div_mem_lattice_iff_intCast_eq_zero (N := N)
      (m := σ 1 0) (n := σ 1 1 - 1)).mp (by
        convert hC using 1
        rw [← hden, ModularGroup.denom_apply, periodPair_ω₁, periodPair_ω₂]
        push_cast
        ring)
    replace h₁ : ((σ 1 1 : ℤ) : ZMod N) = 1 := by simpa [sub_eq_zero] using h₁
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
      simpa using weierstrassPoint_div_eq_weierstrassPoint_denom_div (z := z) (m := 0) (n := 1)
        (by simpa using h₀) (by simpa using h₁)
    refine ⟨⟨(Units.mk0 _ (denom_ne_zero γ z))⁻¹, 0, 0, 0⟩, ?_⟩
    rw [pointedWeierstrassCurve_def z, hD, smul_mk_weierstrassPoint_denom_div]

variable (N) in
/-- **Diamond operators on `(E_z, P_z)`**: for `γ ∈ Γ₀(N)` with lower-right entry `d`, rescaling
by `(c z + d)⁻¹` carries `E_z` with the point `d • P_z` to `(E_{γ z}, P_{γ z})`. Indeed
`(c z + d) / N` is `d / N` modulo `ℤ z + ℤ`, since `N ∣ c`. This is the diamond
interpretation for `N > 0`; at `N = 0`, both points are zero by Lean’s division-by-zero
convention. -/
theorem smul_mk_zsmul_weierstrassPoint_one_div {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (z : ℍ) :
    (⟨(Units.mk0 _ (denom_ne_zero γ z))⁻¹, 0, 0, 0⟩ : VariableChange ℂ) •
        (⟨z.periodPair.weierstrassCurve, γ 1 1 • z.periodPair.weierstrassPoint (1 / N)⟩ :
          PointedWeierstrassCurve ℂ) =
      (γ • z).pointedWeierstrassCurve N := by
  have hD : γ 1 1 • z.periodPair.weierstrassPoint (1 / N) =
      z.periodPair.weierstrassPoint (denom γ z / N) := calc
    _ = z.periodPair.weierstrassPoint (((0 : ℤ) * z + γ 1 1) / N) := by
      rw [← PeriodPair.weierstrassPointHom_apply, ← map_zsmul, PeriodPair.weierstrassPointHom_apply]
      simp [zsmul_eq_mul, div_eq_mul_inv]
    _ = _ := weierstrassPoint_div_eq_weierstrassPoint_denom_div
      (by simpa using Gamma0_mem.mp hγ) rfl
  rw [hD, smul_mk_weierstrassPoint_denom_div]

end UpperHalfPlane

namespace TauCeti

variable (N : ℕ)

variable [NeZero N]

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
          ⟨γ, γ.property, hγ⟩
        exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨C, Subtype.ext hC⟩))
    ⟨fun q q' ↦ Quotient.inductionOn₂ q q' fun z z' h ↦ by
        obtain ⟨C, hC⟩ := MulAction.mem_orbit_iff.mp
          (MulAction.orbitRel_apply.mp (Quotient.exact h))
        obtain ⟨γ, hγ, hγz⟩ := UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq_iff.mp
          ⟨C, congrArg Subtype.val hC⟩
        exact Quotient.sound (MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr ⟨⟨γ, hγ⟩, hγz⟩)),
      fun q ↦ Quotient.inductionOn q fun X ↦ by
        obtain ⟨z, C, hC⟩ := UpperHalfPlane.exists_smul_pointedWeierstrassCurve_eq X.property
        exact ⟨⟦z⟧, Quotient.sound (MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr
            ⟨C⁻¹, Subtype.ext (by rw [SubMulAction.val_smul, ← hC, inv_smul_smul])⟩))⟩⟩

@[simp]
theorem gamma1QuotientEquivExactOrder_mk (z : ℍ) :
    gamma1QuotientEquivExactOrder N ⟦z⟧ =
      ⟦⟨z.pointedWeierstrassCurve N, z.pointedWeierstrassCurve_mem_exactOrder⟩⟧ :=
  (rfl)

/-- **The moduli bijection commutes with the diamond operators**: for `γ ∈ Γ₀(N)` with
lower-right entry `d`, the class of `γ z` corresponds to `(E_z, d • P_z)`. In terms of the
embeddings `α : μ_N ↪ E[N]`, the diamond operator `⟨d⟩` precomposes `α` with multiplication by
`d` on `μ_N`. -/
theorem gamma1QuotientEquivExactOrder_mk_smul (γ : Gamma0 N) (z : ℍ) :
    gamma1QuotientEquivExactOrder N ⟦(γ : SL(2, ℤ)) • z⟧ =
      ⟦(Gamma0Map N).toHomUnits γ •
        ⟨z.pointedWeierstrassCurve N, z.pointedWeierstrassCurve_mem_exactOrder⟩⟧ := by
  rw [gamma1QuotientEquivExactOrder_mk]
  refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
    ⟨⟨(Units.mk0 _ (denom_ne_zero (γ : SL(2, ℤ)) z))⁻¹, 0, 0, 0⟩, Subtype.ext ?_⟩))
  rw [SubMulAction.val_smul, PointedWeierstrassCurve.val_units_smul_of_intCast_eq
    (n := (γ : SL(2, ℤ)) 1 1) _ _ (by rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply])]
  -- The goal still projects out of the subtype `⟨z.pointedWeierstrassCurve N, _⟩`, whose
  -- membership proof mentions `z.pointedWeierstrassCurve N`, so rewriting with its defining
  -- equation would give an ill-typed motive. `change` reduces these projections first.
  change _ • (⟨(z.pointedWeierstrassCurve N).curve,
    (γ : SL(2, ℤ)) 1 1 • (z.pointedWeierstrassCurve N).point⟩ : PointedWeierstrassCurve ℂ) =
      (γ • z).pointedWeierstrassCurve N
  rw [UpperHalfPlane.pointedWeierstrassCurve_def z]
  exact UpperHalfPlane.smul_mk_zsmul_weierstrassPoint_one_div N γ.property z

/-- The moduli bijection is equivariant for diamonds on arbitrary quotient classes. Over ℂ
with a chosen primitive `N`-th root, this is precomposition of the μ-marking by the unit. -/
@[simp↓]
theorem gamma1QuotientEquivExactOrder_smul (d : (ZMod N)ˣ)
    (q : MulAction.orbitRel.Quotient (Gamma1 N) ℍ) :
    gamma1QuotientEquivExactOrder N (d • q) = d • gamma1QuotientEquivExactOrder N q := by
  obtain ⟨γ, rfl⟩ := Gamma0Map_toHomUnits_surjective d
  induction q using Quotient.inductionOn with
  | h z =>
    rw [units_smul_gamma1Quotient_mk, gamma1QuotientEquivExactOrder_mk_smul,
      gamma1QuotientEquivExactOrder_mk, PointedWeierstrassCurve.units_smul_quotient_mk]

/-- **The moduli bijection is natural in the level**: for `M ≠ 0`, the map
`Γ₁(N M) \ ℍ → Γ₁(N) \ ℍ` induced by `Γ₁(N M) ≤ Γ₁(N)` corresponds to multiplying the point of
exact order `N M` by `M`. In terms of the embeddings `α : μ_{NM} ↪ E[NM]`, it restricts `α` to
`μ_N`, forgetting the auxiliary marking, using compatible primitive roots
`ζ_N = ζ_{NM}^M` (for example `ζ_k = exp(2πi/k)`). -/
@[simp↓]
theorem gamma1QuotientEquivExactOrder_map_of_le (M : ℕ) [NeZero M]
    (q : MulAction.orbitRel.Quotient (Gamma1 (N * M)) ℍ) :
    gamma1QuotientEquivExactOrder N (Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le
        (Gamma1_le_Gamma1_of_dvd (dvd_mul_right N M))) q) =
      (PointedWeierstrassCurve.nsmulExactOrder N M).orbitRelQuotientMap
        (gamma1QuotientEquivExactOrder (N * M) q) := by
  induction q using Quotient.inductionOn with
  | h z =>
    rw [Setoid.map_of_le_mk, gamma1QuotientEquivExactOrder_mk, gamma1QuotientEquivExactOrder_mk,
      MulActionHom.orbitRelQuotientMap_mk]
    refine congrArg _ (Subtype.ext ?_)
    rw [PointedWeierstrassCurve.val_nsmulExactOrder_apply]
    -- As in `gamma1QuotientEquivExactOrder_mk_smul`, reduce the projections out of the subtype
    -- `⟨z.pointedWeierstrassCurve (N * M), _⟩` so that its defining equation can be rewritten.
    change z.pointedWeierstrassCurve N =
      ⟨(z.pointedWeierstrassCurve (N * M)).curve, M • (z.pointedWeierstrassCurve (N * M)).point⟩
    rw [UpperHalfPlane.pointedWeierstrassCurve_def, UpperHalfPlane.pointedWeierstrassCurve_def,
      PointedWeierstrassCurve.mk_inj, PeriodPair.nsmul_weierstrassPoint]
    congr 1
    push_cast
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne M)]

end TauCeti
