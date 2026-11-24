/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.StrictVariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Grading
public import TauCeti.RingTheory.PowerSeries.Coordinate.Graded
import TauCeti.RingTheory.FormalGroup.CoordinateChange.Graded

/-!
# Homological homogeneity of Weierstrass formal groups

Applying the pure-scaling identities from `FormalGroup.VariableChange`
(`formalCoordinate_scaling`, `formalGroup_scaling_smul`, `formalW_scaling_smul`,
`formalInvariantDifferentialDenom_scaling_smul`, `invariantDifferential_formalGroup_scaling_smul`)
at the Laurent degree unit `T (-w)` via `map_toLaurent_toPolynomial_eq_scaling` gives homological
and weighted homogeneity of Weierstrass formal groups, `[k]`-series, `formalW`, invariant
differentials, and formal coordinate transitions
(`VariableChange.formalCoordinate_mem_gradedSubgroup`,
`Strict.formalCoordinate_mem_gradedSubgroup`).

## Main definitions and results

* `WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling`: applying `toLaurent ∘ toPolynomial 𝒜`
  to a graded Weierstrass curve scales its constant base change by `T (-w)`.
* `WeierstrassCurve.Universal.coeff_*_mem_baseGrading`, `isWeightedHomogeneous_coeff_*`, and
  general `WeierstrassCurve.coeff_*_mem`.
* `WeierstrassCurve.VariableChange.formalCoordinate_mem_gradedSubgroup`,
  `TauCeti.WeierstrassHopfAlgebroid.Strict.formalCoordinate_mem_gradedSubgroup`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section

noncomputable section

open TauCeti.GradedAlgebra

namespace WeierstrassCurve

/-- Applying `toLaurent ∘ toPolynomial 𝒜` to a Weierstrass curve whose coefficients `aᵢ` lie in
degree `w * i` scales its constant base change by `T (-w)`. -/
theorem map_toLaurent_toPolynomial_eq_scaling {B σ : Type*} [CommRing B] [SetLike σ B]
    [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ) {W : WeierstrassCurve B}
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i)) :
    W.map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
      VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ •
        W.map LaurentPolynomial.C := by
  have hspec : (W.map (Polynomial.toLaurent.comp (toPolynomial 𝒜))).specialize =
      (VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ •
          W.map LaurentPolynomial.C).specialize := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ ?_
    rw [specialize_map, RingHom.comp_apply, RingHom.comp_apply, toPolynomial_of_mem (hW i),
      Polynomial.toLaurent_C_mul_T, VariableChange.scaling_apply, specialize_mk_smul,
      MvPolynomial.aeval_X, specialize_map, RingHom.comp_apply]
    simp only [inv_inv, val_unitOfInvertible, LaurentPolynomial.T_pow,
      mul_comm (LaurentPolynomial.C _)]
    congr 2; push_cast; ring
  rw [← map_specialize (W.map _), hspec, map_specialize]

/-! ### Homogeneity of Weierstrass formal groups and formal expansions -/

namespace Universal

open TauCeti.WeierstrassHopfAlgebroid

private abbrev degreeUnit : (LaurentPolynomial (MvPolynomial Coeff ℤ))ˣ :=
  (unitOfInvertible (LaurentPolynomial.T ↑(2 : ℕ)))⁻¹
private theorem val_degreeUnit :
    (degreeUnit : LaurentPolynomial (MvPolynomial Coeff ℤ)) = LaurentPolynomial.T (-2) := by
  simp [degreeUnit, val_inv_unitOfInvertible]
private theorem val_inv_degreeUnit :
    (↑degreeUnit⁻¹ : LaurentPolynomial (MvPolynomial Coeff ℤ)) = LaurentPolynomial.T 2 := by
  simp [degreeUnit]

private theorem map_toLaurent_toPolynomial_curve :
    WeierstrassCurve.map Universal.curve
        (Polynomial.toLaurent.comp (toPolynomial Strict.baseGrading)) =
      VariableChange.scaling _ degreeUnit •
        WeierstrassCurve.map Universal.curve LaurentPolynomial.C :=
  map_toLaurent_toPolynomial_eq_scaling Strict.baseGrading 2 fun _ ↦ by
    simp [Universal.specialize_curve]

private theorem mem_baseGrading_of_toLaurent_eq {a : MvPolynomial Coeff ℤ} {m : ℕ} {k : ℤ}
    (hk : k = m) (ha : Polynomial.toLaurent (toPolynomial Strict.baseGrading a) =
      LaurentPolynomial.T k * LaurentPolynomial.C a) : a ∈ Strict.baseGrading m :=
  toPolynomial_eq_monomial_iff.mp <| Polynomial.toLaurent_injective <| by
    rw [ha, hk, mul_comm, Polynomial.toLaurent_C_mul_T]

private theorem coeff_mem_baseGrading_of_rescale (P : PowerSeries (MvPolynomial Coeff ℤ))
    (hP : PowerSeries.map (Polynomial.toLaurent.comp (toPolynomial Strict.baseGrading)) P =
      PowerSeries.rescale (↑degreeUnit⁻¹) (PowerSeries.map LaurentPolynomial.C P)) (n : ℕ) :
    PowerSeries.coeff n P ∈ Strict.baseGrading (2 * n) :=
  mem_baseGrading_of_toLaurent_eq (k := (n : ℤ) * 2) (by push_cast; ring) <| by
    simpa [val_inv_degreeUnit] using congrArg (PowerSeries.coeff n) hP

/-- **Homological homogeneity of the universal Weierstrass formal group law**. -/
theorem coeff_formalGroup_mem_baseGrading (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries ∈
      Strict.baseGrading (2 * (d.degree - 1)) := by
  refine ((FormalGroup.map_toLaurent_eq_homothety_smul_iff (𝒜 := Strict.baseGrading)
    (formalGroup Universal.curve) 2).mp ?_) d
  have h := congrArg formalGroup map_toLaurent_toPolynomial_curve
  rwa [map_formalGroup, formalGroup_scaling_smul, map_formalGroup,
    ← FormalGroup.homothety_smul] at h
/-- **Weighted homogeneity of the universal Weierstrass formal group law**. -/
theorem isWeightedHomogeneous_coeff_formalGroup (d : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries).IsWeightedHomogeneous
      coefficientWeight (d.degree - 1) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalGroup_mem_baseGrading d)

/-- Coefficient `m` of `[k](z)` on `Universal.curve` has homological degree `2 * (m - 1)`. -/
theorem coeff_nsmulSeries_formalGroup_mem_baseGrading (k m : ℕ) :
    PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k) ∈
      Strict.baseGrading (2 * (m - 1)) :=
  FormalGroup.coeff_nsmulSeries_mem (formalGroup Universal.curve) coeff_formalGroup_mem_baseGrading
    k m
/-- The coefficient of `zᵐ` in `[k](z)` on `Universal.curve` has modular weight `m - 1`. -/
theorem isWeightedHomogeneous_coeff_nsmulSeries_formalGroup (k m : ℕ) :
    (PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k)).IsWeightedHomogeneous
      coefficientWeight (m - 1) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_nsmulSeries_formalGroup_mem_baseGrading k m)

/-- The coefficient of `zⁿ` in `formalW Universal.curve` has homological degree `2 * (n - 3)`. -/
theorem coeff_formalW_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n (formalW Universal.curve) ∈ Strict.baseGrading (2 * (n - 3)) := by
  rcases lt_or_ge n 3 with hn | hn
  · rw [coeff_formalW, formalWCoeff_eq_zero_of_lt _ hn]; exact zero_mem _
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [Nat.add_sub_cancel]
    refine mem_baseGrading_of_toLaurent_eq (k := (3 : ℕ) * (-2 : ℤ) + (n + 3 : ℕ) * 2)
      (by push_cast; ring) ?_
    have h := congrArg formalW map_toLaurent_toPolynomial_curve
    rw [map_formalW, formalW_scaling_smul, map_formalW] at h
    simpa [val_degreeUnit, val_inv_degreeUnit, ← mul_assoc, ← LaurentPolynomial.T_add] using
      congrArg (PowerSeries.coeff (n + 3)) h
/-- The coefficient of `zⁿ` in `formalW Universal.curve` has modular weight `n - 3`. -/
theorem isWeightedHomogeneous_coeff_formalW (n : ℕ) :
    (PowerSeries.coeff n (formalW Universal.curve)).IsWeightedHomogeneous
      coefficientWeight (n - 3) :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalW_mem_baseGrading n)

/-- Coefficient `n` of `Universal.curve.formalInvariantDifferentialDenom` has degree `2 * n`. -/
theorem coeff_formalInvariantDifferentialDenom_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom ∈
      Strict.baseGrading (2 * n) :=
  coeff_mem_baseGrading_of_rescale _ (by
    have h := congrArg formalInvariantDifferentialDenom map_toLaurent_toPolynomial_curve
    rwa [map_formalInvariantDifferentialDenom, formalInvariantDifferentialDenom_scaling_smul,
      map_formalInvariantDifferentialDenom] at h) n
/-- Coefficient `n` of `Universal.curve.formalInvariantDifferentialDenom` has modular weight `n`. -/
theorem isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom (n : ℕ) :
    (PowerSeries.coeff n Universal.curve.formalInvariantDifferentialDenom).IsWeightedHomogeneous
      coefficientWeight n :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_formalInvariantDifferentialDenom_mem_baseGrading n)

/-- Coefficient `n` of `(formalGroup Universal.curve).invariantDifferential` has degree `2 * n`. -/
theorem coeff_invariantDifferential_formalGroup_mem_baseGrading (n : ℕ) :
    PowerSeries.coeff n (formalGroup Universal.curve).invariantDifferential ∈
      Strict.baseGrading (2 * n) :=
  coeff_mem_baseGrading_of_rescale _ (by
    have h := congrArg (fun W ↦ (formalGroup W).invariantDifferential)
      map_toLaurent_toPolynomial_curve
    rwa [invariantDifferential_formalGroup_scaling_smul, map_formalGroup,
      ← FormalGroup.map_invariantDifferential, map_formalGroup,
      ← FormalGroup.map_invariantDifferential] at h) n
/-- Coefficient `n` of `(formalGroup Universal.curve).invariantDifferential` has weight `n`. -/
theorem isWeightedHomogeneous_coeff_invariantDifferential_formalGroup (n : ℕ) :
    (PowerSeries.coeff n
      (formalGroup Universal.curve).invariantDifferential).IsWeightedHomogeneous
        coefficientWeight n :=
  Strict.mem_baseGrading_two_mul_iff.mp (coeff_invariantDifferential_formalGroup_mem_baseGrading n)

end Universal

section GradedWeierstrassCurve

variable {B σ ι : Type*} [CommRing B] [SetLike σ B] [AddSubgroupClass σ B] [AddCommMonoid ι]
  (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι) {W : WeierstrassCurve B}

private theorem specialize_mem_of_isWeightedHomogeneous
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (e (coefficientWeight i))) {k : ℕ}
    {p : MvPolynomial Coeff ℤ} (hp : p.IsWeightedHomogeneous coefficientWeight k) :
    W.specialize p ∈ 𝒜 (e k) :=
  (MvPolynomial.WeightedHomogeneousSubmodule.map_mem_iff coefficientWeight 𝒜 e W.specialize).mpr
    hW hp

/-- Homogeneity of the formal group law of any Weierstrass curve with graded coefficients. -/
theorem coeff_formalGroup_mem
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (e (coefficientWeight i))) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup W).toPowerSeries ∈ 𝒜 (e (d.degree - 1)) := by
  rw [← W.map_specialize, map_formalGroup, FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
  exact specialize_mem_of_isWeightedHomogeneous 𝒜 e hW
    (Universal.isWeightedHomogeneous_coeff_formalGroup d)

/-- Homogeneity of the `[k]`-series of the formal group of a graded Weierstrass curve. -/
theorem coeff_nsmulSeries_formalGroup_mem
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (e (coefficientWeight i))) (k m : ℕ) :
    PowerSeries.coeff m ((formalGroup W).nsmulSeries k) ∈ 𝒜 (e (m - 1)) := by
  rw [← W.map_specialize, map_formalGroup, FormalGroup.coeff_nsmulSeries_map]
  exact specialize_mem_of_isWeightedHomogeneous 𝒜 e hW
    (Universal.isWeightedHomogeneous_coeff_nsmulSeries_formalGroup k m)

/-- Homogeneity of `formalW W` for a graded Weierstrass curve (`coeff n` in `𝒜 (e (n - 3))`). -/
theorem coeff_formalW_mem
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (e (coefficientWeight i))) (n : ℕ) :
    PowerSeries.coeff n (formalW W) ∈ 𝒜 (e (n - 3)) := by
  rw [← W.map_specialize, map_formalW, PowerSeries.coeff_map]
  exact specialize_mem_of_isWeightedHomogeneous 𝒜 e hW
    (Universal.isWeightedHomogeneous_coeff_formalW n)

/-- Homogeneity of the invariant-differential denominator of a graded Weierstrass curve. -/
theorem coeff_formalInvariantDifferentialDenom_mem
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (e (coefficientWeight i))) (n : ℕ) :
    PowerSeries.coeff n W.formalInvariantDifferentialDenom ∈ 𝒜 (e n) := by
  rw [← W.map_specialize, map_formalInvariantDifferentialDenom, PowerSeries.coeff_map]
  exact specialize_mem_of_isWeightedHomogeneous 𝒜 e hW
    (Universal.isWeightedHomogeneous_coeff_formalInvariantDifferentialDenom n)

/-- Homogeneity of the normalised invariant differential of a graded Weierstrass curve. -/
theorem coeff_invariantDifferential_formalGroup_mem
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (e (coefficientWeight i))) (n : ℕ) :
    PowerSeries.coeff n (formalGroup W).invariantDifferential ∈ 𝒜 (e n) := by
  rw [← W.map_specialize, map_formalGroup, ← FormalGroup.map_invariantDifferential,
    PowerSeries.coeff_map]
  exact specialize_mem_of_isWeightedHomogeneous 𝒜 e hW
    (Universal.isWeightedHomogeneous_coeff_invariantDifferential_formalGroup n)

end GradedWeierstrassCurve

namespace VariableChange

/-- If `W` has homogeneous Weierstrass coefficients of degrees `w * i` and `C = (u, r, s, t)` has
`u ∈ 𝒜 0`, `r ∈ 𝒜 (w * 2)`, `s ∈ 𝒜 w`, `t ∈ 𝒜 (w * 3)`, then `C.formalCoordinate W` lies in
`FormalCoordinate.gradedSubgroup 𝒜 w`. -/
theorem formalCoordinate_mem_gradedSubgroup {B σ : Type*} [CommRing B] [SetLike σ B]
    [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ) {W : WeierstrassCurve B}
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i))
    {C : VariableChange B} (hu : (C.u : B) ∈ 𝒜 0) (hr : C.r ∈ 𝒜 (w * 2)) (hs : C.s ∈ 𝒜 w)
    (ht : C.t ∈ 𝒜 (w * 3)) :
    C.formalCoordinate W ∈ TauCeti.FormalCoordinate.gradedSubgroup 𝒜 w := by
  rw [TauCeti.FormalCoordinate.mem_gradedSubgroup,
    ← TauCeti.FormalCoordinate.map_toLaurent_eq_conjugate_iff]
  let ω : B →+* LaurentPolynomial B := Polynomial.toLaurent.comp (toPolynomial 𝒜)
  let u : (LaurentPolynomial B)ˣ := (unitOfInvertible (LaurentPolynomial.T (w : ℤ)))⁻¹
  have hC : C.map ω = scaling _ u * C.map LaurentPolynomial.C * (scaling _ u)⁻¹ := by
    rw [← _root_.map_inv]; ext
    · simp [ω, u, mul_def, toPolynomial_of_mem hu]
    · simp [ω, u, mul_def, toPolynomial_of_mem hr, Polynomial.toLaurent_C_mul_T,
        LaurentPolynomial.T_pow, mul_comm (2 : ℤ)]
    · simp [ω, u, mul_def, toPolynomial_of_mem hs, Polynomial.toLaurent_C_mul_T,
        mul_comm (LaurentPolynomial.T _) (LaurentPolynomial.C _)]
    · simp [ω, u, mul_def, toPolynomial_of_mem ht, Polynomial.toLaurent_C_mul_T,
        LaurentPolynomial.T_pow, mul_comm (3 : ℤ)]
  rw [← map_formalCoordinate, hC, WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling 𝒜 w hW,
    formalCoordinate_scaling_mul_mul_inv, map_formalCoordinate]
  simp [u]

end VariableChange

end WeierstrassCurve

/-! ### The universal strict formal coordinate transition over `A[r, s, t]` -/

namespace TauCeti.WeierstrassHopfAlgebroid.Strict

open MvPolynomial _root_.WeierstrassCurve

/-- **Homological homogeneity of the universal strict Weierstrass formal coordinate**. -/
theorem formalCoordinate_mem_gradedSubgroup :
    formalCoordinate ∈ TauCeti.FormalCoordinate.gradedSubgroup arrowGrading 2 := by
  rw [formalCoordinate_def]
  refine Subgroup.inv_mem _ (VariableChange.formalCoordinate_mem_gradedSubgroup arrowGrading 2
    (fun i ↦ ?_) (by simpa using SetLike.one_mem_graded arrowGrading)
    (by simpa using X_mem_arrowGrading 0) (by simpa using X_mem_arrowGrading 1)
    (by simpa using X_mem_arrowGrading 2))
  rw [WeierstrassCurve.specialize_map, Universal.specialize_curve]
  exact C_mem_arrowGrading (X_mem_baseGrading i)

/-- The coefficient of `z^(i + 1)` in `Strict.formalCoordinate` lies in `arrowGrading (2 * i)`. -/
theorem coeff_succ_formalCoordinate_mem_arrowGrading (i : ℕ+) :
    PowerSeries.coeff (i + 1) formalCoordinate.toPowerSeries ∈ arrowGrading (2 * (i : ℕ)) := by
  simpa using (TauCeti.FormalCoordinate.mem_gradedSubgroup arrowGrading 2 formalCoordinate).mp
    formalCoordinate_mem_gradedSubgroup (i + 1)

end TauCeti.WeierstrassHopfAlgebroid.Strict
