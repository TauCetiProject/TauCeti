/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Field
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Analysis.Normed.Algebra.ScaleRoots
import TauCeti.Analysis.Normed.Ring.UnitBall
import TauCeti.RingTheory.AdicCompletion.Newton
import TauCeti.RingTheory.AdicCompletion.Perfection
import TauCeti.RingTheory.Perfectoid.IsAlgClosed
import TauCeti.RingTheory.Perfectoid.PreTilt.ApproximateRoot
import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing
import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta
import TauCeti.RingTheory.Polynomial.ScaleRoots
import TauCeti.Topology.Algebra.Valued.Integer
import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# The tilt of an algebraically closed field is algebraically closed

Let `K` be a complete nontrivially normed field with an ultrametric norm in which the prime `p`
is topologically nilpotent, with valuation ring `O_K = 𝒪[K]` and tilt `K♭ = tiltField p K`. The
valuation ring of `K♭` is Mathlib's tilt `O_K♭ = PreTilt O_K p`: under the identification of
`O_K♭` with the compatible systems of `p`-power roots in `O_K`, the norm of `K♭` is
`‖x‖ = ‖x♯‖`. If `K` is algebraically closed, for instance `K = ℂ_p`, then `K♭` is algebraically
closed, and `O♭ = PreTilt O_K p` is absolutely integrally closed: every monic polynomial of
positive degree over `O♭` has a root in `O♭`, so the fraction field of `O♭` is algebraically
closed.

The proof works in `O♭`. Let `Q` be a monic polynomial of positive degree over `O♭` whose
resultant `r` with its derivative is nonzero, and choose `ϖ ∈ O♭` whose untilt `ϖ♯ ≠ 0` divides
`p` and has norm less than one; then `O♭` is `ϖ`-adically complete, and `r` divides some power
`ϖ ^ k`. Roots of `Q` modulo `p` after untilting, together with Frobenius twists, give approximate
roots of `Q` to any precision (`PreTilt.exists_pow_dvd_untilt_eval`), and Hensel's lemma in the
form controlled by the Bézout identity `Q a + Q' b = r`
(`TauCeti.IsAdicComplete.existsUnique_eval_eq_zero_of_mul_add_mul_eq_C`) turns an approximate
root modulo `ϖ ^ (2k + 1)` into a root. For the field `K♭`, an irreducible polynomial is separable
since `K♭` is perfect, and rescaling its roots by a small nonzero scalar makes its coefficients
integral without losing separability; its resultant with its derivative is then nonzero.

## Main definitions

* `TauCeti.Perfectoid.tiltField.integerEquivPreTilt p K`: the ring isomorphism
  `𝒪[K♭] ≃+* PreTilt O_K p` between the valuation ring of the tilt and Mathlib's tilt of `O_K`.

## Main results

* `TauCeti.Perfectoid.tiltField.untilt_integerEquivPreTilt`,
  `TauCeti.Perfectoid.tiltField.coeff_zero_integerEquivPreTilt_symm`: under this isomorphism the
  untilt is the sharp map `x ↦ x♯` of `K♭`.
* `TauCeti.Perfectoid.tiltField.instIsAlgClosed`: if `K` is algebraically closed, so is its tilt
  `K♭`.
* `PreTilt.instIsAbsolutelyIntegrallyClosed`: if `C` is a complete algebraically closed
  nonarchimedean field in which `p` is not a unit of `O_C`, then every monic polynomial of positive
  degree over `O_C♭ = PreTilt O_C p` has a root there; so the fraction field of `O_C♭` is
  algebraically closed (`TauCeti.IsAbsolutelyIntegrallyClosed.isAlgClosed`).

## References

* P. Scholze, *Perfectoid spaces*, §3.
* O. Brinon, B. Conrad, *CMI Summer School notes on `p`-adic Hodge theory*, §4.3. Here the
  passage from approximate to exact roots is made by Hensel's lemma for a polynomial with nonzero
  discriminant.
-/

public section

open scoped NormedField Valued
open Ideal Polynomial TauCeti TauCeti.Huber

namespace TauCeti.Perfectoid

section Integer

variable {p : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]
  [hpK : Fact (IsTopologicallyNilpotent (p : K))]

/-- If `p` is topologically nilpotent in the nonarchimedean field `K`, then `p` is not a unit of
`O_K`, as `‖p‖ < 1`; so Mathlib's tilt `PreTilt O_K p` is a ring of characteristic `p`. -/
instance fact_not_isUnit_natCast_integer : Fact ¬IsUnit (p : 𝒪[K]) :=
  ⟨(Valuation.integer.integers (NormedField.valuation (K := K))).norm_algebraMap_lt_one_iff.mp <| by
    simpa using (isTopologicallyNilpotent_iff_norm_lt_one_of_isPowMul fun x n _ ↦ norm_pow x n).mp
      hpK.out⟩

/-- If `K` is complete and `p` is topologically nilpotent in `K`, then `O_K` is `p`-adically
complete, as `‖p‖ < 1`; so the untilt `PreTilt O_K p → O_K` is defined. -/
instance isAdicComplete_span_natCast_integer [CompleteSpace K] :
    IsAdicComplete (span {(p : 𝒪[K])}) 𝒪[K] :=
  (Valuation.integer.integers (NormedField.valuation (K := K))).isAdicComplete_span_singleton <| by
    simpa using (isTopologicallyNilpotent_iff_norm_lt_one_of_isPowMul fun x n _ ↦ norm_pow x n).mp
      hpK.out

end Integer

namespace tiltField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (IsTopologicallyNilpotent (p : K))]

omit [CompleteSpace K] in
/-- The valuation ring `O_K` is a ring of integral elements of `K`. -/
private theorem isRingOfIntegralElements_integer : IsRingOfIntegralElements 𝒪[K] :=
  powerBoundedSubring_eq_integer (K := K) ▸ isRingOfIntegralElements_powerBoundedSubring K

variable {p K} in
/-- Membership in the valuation ring of the tilt is the bound `‖x‖ ≤ 1`. -/
private theorem mem_integer_iff {x : tiltField p K} : x ∈ 𝒪[tiltField p K] ↔ ‖x‖ ≤ 1 := by
  simp [Valuation.mem_integer_iff, ← NNReal.coe_le_coe]

/-- The ring homomorphism `O_K♭ → K♭`: the integral tilt `PreTilt O_K p` is the subring of
`uniformTilt p K` of compatible systems of `p`-power roots in `O_K`. -/
private noncomputable def preTiltToTilt : PreTilt 𝒪[K] p →+* tiltField p K :=
  (WithAbs.equiv (uniformTilt.sharpAbsoluteValue p K)).symm.toRingHom.comp
    ((uniformTilt.plusSubring p (isRingOfIntegralElements_integer K)).subtype.comp
      (uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_integer K)).symm.toRingHom)

variable {p K} in
private theorem preTiltToTilt_apply (x : PreTilt 𝒪[K] p) :
    preTiltToTilt p K x = WithAbs.toAbs _
      ((uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_integer K)).symm x :
        uniformTilt p K) :=
  (rfl)

variable {p K} in
/-- `preTiltToTilt` is injective. -/
private theorem preTiltToTilt_injective : Function.Injective (preTiltToTilt p K) :=
  fun x y h ↦ by simpa [preTiltToTilt_apply] using h

variable {p K} in
/-- `preTiltToTilt` takes values in the closed unit ball. -/
private theorem preTiltToTilt_mem_integer (x : PreTilt 𝒪[K] p) :
    preTiltToTilt p K x ∈ 𝒪[tiltField p K] := by
  rw [mem_integer_iff, preTiltToTilt_apply, norm_toAbs, ← Valued.integer.mem_iff]
  exact uniformTilt.mem_plusSubring_iff.mp (Subtype.property _) 0

variable {p K} in
/-- Every element of the closed unit ball is a value of `preTiltToTilt`: its coordinates are a
compatible system of `p`-power roots in `O_K`. -/
private theorem exists_preTiltToTilt_eq {y : tiltField p K} (hy : y ∈ 𝒪[tiltField p K]) :
    ∃ x, preTiltToTilt p K x = y := by
  have hmem :
      WithAbs.equiv _ y ∈ uniformTilt.plusSubring p (isRingOfIntegralElements_integer K) := by
    rw [uniformTilt.mem_plusSubring_iff_coeff_zero, Valued.integer.mem_iff, ← norm_def]
    exact mem_integer_iff.mp hy
  refine ⟨uniformTilt.plusEquivPreTilt p _ ⟨_, hmem⟩, ?_⟩
  rw [preTiltToTilt_apply, RingEquiv.symm_apply_apply]
  rfl

/-- The ring homomorphism `preTiltToTilt` is an isomorphism onto the closed unit ball. -/
private noncomputable def preTiltEquivInteger : PreTilt 𝒪[K] p ≃+* 𝒪[tiltField p K] :=
  RingEquiv.ofBijective
    ((preTiltToTilt p K).codRestrict 𝒪[tiltField p K] preTiltToTilt_mem_integer)
    ⟨fun _ _ h ↦ preTiltToTilt_injective (congrArg Subtype.val h),
      fun y ↦ (exists_preTiltToTilt_eq y.property).imp fun _ hx ↦ Subtype.ext hx⟩

/-- **The valuation ring of the tilt is the tilt of the valuation ring.** The closed unit ball
`𝒪[K♭]` of the tilt `K♭ = tiltField p K` is isomorphic to Mathlib's tilt
`PreTilt O_K p = lim_{x ↦ x ^ p} O_K ⧸ p`, by reducing every coordinate modulo `p`; under this
isomorphism the untilt is the sharp map (`tiltField.untilt_integerEquivPreTilt`), so
`‖x‖ = ‖x♯‖`. -/
noncomputable def integerEquivPreTilt : 𝒪[tiltField p K] ≃+* PreTilt 𝒪[K] p :=
  (preTiltEquivInteger p K).symm

variable {p K}

private theorem preTiltToTilt_integerEquivPreTilt (y : 𝒪[tiltField p K]) :
    preTiltToTilt p K (integerEquivPreTilt p K y) = y :=
  congrArg Subtype.val ((preTiltEquivInteger p K).apply_symm_apply y)

/-- **The untilt is the sharp map.** For `y` in the valuation ring of the tilt `K♭`, the untilt of
the corresponding element of `PreTilt O_K p` is the zeroth coordinate `y♯` of `y`. In particular
`‖y‖ = ‖(integerEquivPreTilt p K y)♯‖` (`tiltField.norm_def`). -/
@[simp]
theorem untilt_integerEquivPreTilt (y : 𝒪[tiltField p K]) :
    ((integerEquivPreTilt p K y).untilt : K) =
      uniformTilt.coeff p K 0 (WithAbs.ofAbs (y : tiltField p K)) := by
  conv_rhs => rw [← preTiltToTilt_integerEquivPreTilt y, preTiltToTilt_apply]
  rw [← uniformTilt.plusSharp_plusEquivPreTilt_symm (isRingOfIntegralElements_integer K),
    uniformTilt.coe_plusSharp]

/-- **The sharp map is the untilt.** For `x ∈ PreTilt O_K p`, the sharp of the corresponding
element of the tilt `K♭` is the untilt `x♯`. -/
@[simp]
theorem coeff_zero_integerEquivPreTilt_symm (x : PreTilt 𝒪[K] p) :
    uniformTilt.coeff p K 0 (WithAbs.ofAbs ((integerEquivPreTilt p K).symm x : tiltField p K)) =
      (x.untilt : K) := by
  rw [← untilt_integerEquivPreTilt, RingEquiv.apply_symm_apply]

end tiltField

end TauCeti.Perfectoid

namespace PreTilt

open TauCeti.Perfectoid

variable {p : ℕ} [hp : Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [Fact ¬IsUnit (p : 𝒪[C])]

/-- Over the tilt of `O_C` for an algebraically closed `C`, a monic polynomial of positive degree
whose resultant with its derivative is nonzero has a root: approximate roots modulo high powers of
a pseudouniformiser `ϖ` are refined to a root by Hensel's lemma. -/
private theorem exists_isRoot_of_resultant_ne_zero [IsAlgClosed C] {Q : (PreTilt 𝒪[C] p)[X]}
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (hr : Q.resultant (derivative Q) ≠ 0) :
    ∃ x, Q.IsRoot x := by
  have : IsAbsolutelyIntegrallyClosed 𝒪[C] := .of_isIntegrallyClosed_of_isAlgClosed C
  have hp1 : ‖((p : 𝒪[C]) : C)‖ < 1 := (Valued.integer.norm_le_one (p : 𝒪[C])).lt_of_ne
    (Valued.integer.isUnit_iff_norm_eq_one.not.mp Fact.out)
  have : IsAdicComplete (span {(p : 𝒪[C])}) 𝒪[C] :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).isAdicComplete_span_singleton hp1
  -- `c ≠ 0` of norm less than one dividing `p`, and `ϖ ∈ O♭` with `ϖ♯ = c`
  obtain ⟨c, hc0, hc1, hcp⟩ : ∃ c : 𝒪[C], c ≠ 0 ∧ ‖(c : C)‖ < 1 ∧ c ∣ (p : 𝒪[C]) := by
    by_cases h : (p : 𝒪[C]) = 0
    · obtain ⟨d, hd0, hd1⟩ := NormedField.exists_norm_lt_one C
      exact ⟨⟨d, Valued.integer.mem_iff.mpr hd1.le⟩,
        fun h0 ↦ norm_pos_iff.mp hd0 (by simpa using congrArg Subtype.val h0), hd1, h ▸ dvd_zero _⟩
    · exact ⟨p, h, hp1, dvd_rfl⟩
  obtain ⟨ϖ, hϖ⟩ := untilt_surjective
    (fun x ↦ IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq x hp.out.pos) c
  have : IsAdicComplete (span {ϖ.untilt}) 𝒪[C] := hϖ ▸
    (Valuation.integer.integers (NormedField.valuation (K := C))).isAdicComplete_span_singleton hc1
  have : IsAdicComplete (span {ϖ}) (PreTilt 𝒪[C] p) := isAdicComplete_span_singleton (hϖ ▸ hcp)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hϖ, untilt_zero])
  -- a Bézout identity `Q a + Q' b = r` whose constant `r` divides a power of `ϖ`
  obtain ⟨a, b, -, -, hab⟩ :=
    exists_mul_add_mul_eq_C_resultant Q (derivative Q) le_rfl le_rfl (Or.inl hdeg.ne')
  obtain ⟨k, hk⟩ : ∃ k, ‖(c : C)‖ ^ k < ‖((Q.resultant (derivative Q)).untilt : C)‖ :=
    exists_pow_lt_of_lt_one (by simpa using untilt_ne_zero_iff.mpr hr) hc1
  have hrk : Q.resultant (derivative Q) ∣ ϖ ^ k := by
    rw [← untilt_dvd_untilt_iff, map_pow, hϖ, Valued.integer.dvd_iff_norm_le]
    simpa using hk.le
  -- an approximate root modulo `ϖ ^ (2k + 1)`, refined to a root by Hensel's lemma
  obtain ⟨x, hx⟩ := exists_pow_dvd_untilt_eval hQ hdeg (2 * k + 1)
  have hxk : ϖ ^ (2 * k + 1) ∣ Q.eval x := by
    rw [← untilt_dvd_untilt_iff, map_pow, hϖ]
    exact (pow_dvd_pow_of_dvd hcp _).trans hx
  obtain ⟨u, ⟨-, hu⟩, -⟩ := IsAdicComplete.existsUnique_eval_eq_zero_of_mul_add_mul_eq_C
    (IsRegular.of_ne_zero hϖ0).left hab hrk hxk
  exact ⟨u, hu⟩

end PreTilt

namespace TauCeti.Perfectoid.tiltField

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (IsTopologicallyNilpotent (p : K))] [IsAlgClosed K]

/-- Over the tilt of an algebraically closed field, a separable monic polynomial of positive degree
whose coefficients have norm at most one has a root: it comes from a monic polynomial over
`PreTilt O_K p` whose resultant with its derivative is nonzero. -/
private theorem exists_isRoot_of_separable {Q : (tiltField p K)[X]} (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (hsep : Q.Separable) (hint : ∀ n, ‖Q.coeff n‖ ≤ 1) :
    ∃ y, Q.IsRoot y := by
  set ι : PreTilt 𝒪[K] p →+* tiltField p K :=
    (𝒪[tiltField p K]).subtype.comp (integerEquivPreTilt p K).symm.toRingHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (RingEquiv.injective _)
  have hlift : Q ∈ lifts ι := lifts_iff_coeff_lifts _ |>.mpr fun n ↦
    ⟨integerEquivPreTilt p K ⟨_, mem_integer_iff.mpr (hint n)⟩, by simp [ι]⟩
  obtain ⟨Q₀, hQ₀, hdeg₀, hm₀⟩ := lifts_and_natDegree_eq_and_monic hlift hQ
  -- the resultant of `Q₀` and `Q₀'` maps to that of the separable `Q`, which is nonzero
  have hr : Q₀.resultant (derivative Q₀) ≠ 0 := fun h ↦ by
    apply resultant_ne_zero _ _ hsep
    rw [← hQ₀, derivative_map, natDegree_map_eq_of_injective hι Q₀,
      natDegree_map_eq_of_injective hι (derivative Q₀), resultant_map_map, h, map_zero]
  obtain ⟨x, hx⟩ := PreTilt.exists_isRoot_of_resultant_ne_zero hm₀ (hdeg₀ ▸ hdeg) hr
  exact ⟨ι x, by rw [IsRoot, ← hQ₀, eval_map_apply, hx.eq_zero, map_zero]⟩

/-- **The tilt of an algebraically closed field is algebraically closed.** Let `K` be a complete
algebraically closed nontrivially normed field with an ultrametric norm in which `p` is
topologically nilpotent, for instance `ℂ_p`; it is a perfectoid field. Then its tilt
`K♭ = tiltField p K` is algebraically closed (Scholze, *Perfectoid spaces*, §3). -/
instance instIsAlgClosed : IsAlgClosed (tiltField p K) := by
  have : IsPerfectoidField p K := isPerfectoidField_iff_isPerfectoidTateRing.mpr
    (isPerfectoidTateRing_of_isAlgClosed
      ((isTopologicallyNilpotent_iff_norm_lt_one_of_isPowMul fun x n _ ↦ norm_pow x n).mp Fact.out))
  have := PerfectRing.toPerfectField (tiltField p K) p
  refine IsAlgClosed.of_exists_root _ fun P hP hirr ↦ ?_
  -- Rescale the roots of the separable `P` by a small `c ≠ 0` to make its coefficients integral.
  obtain ⟨c, hc0, hc⟩ := P.exists_norm_coeff_scaleRoots_le_one (K := tiltField p K)
  rw [Algebra.algebraMap_self, RingHom.id_apply] at hc
  have hQ : (P.scaleRoots c).Monic := (monic_scaleRoots_iff c).mpr hP
  obtain ⟨y, hy⟩ := exists_isRoot_of_separable hQ (natDegree_scaleRoots P c ▸ hirr.natDegree_pos)
    ((PerfectField.separable_of_irreducible hirr).scaleRoots (isUnit_iff_ne_zero.mpr hc0))
    fun n ↦ by
      rcases lt_trichotomy n (P.scaleRoots c).natDegree with hn | hn | hn
      · exact hc n (natDegree_scaleRoots P c ▸ hn)
      · rw [hn, hQ.coeff_natDegree, norm_one]
      · rw [coeff_eq_zero_of_natDegree_lt hn, norm_zero]
        exact zero_le_one
  -- A root `y` of the rescaled polynomial gives the root `y / c` of `P`.
  refine ⟨y / c, (pow_ne_zero P.natDegree hc0).isUnit.mul_right_eq_zero.mp ?_⟩
  rw [← scaleRoots_eval_mul, mul_div_cancel₀ _ hc0, hy.eq_zero]

end TauCeti.Perfectoid.tiltField

namespace PreTilt

open TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [Fact ¬IsUnit (p : 𝒪[C])] [IsAlgClosed C]

/-- **The tilt of `O_C` is absolutely integrally closed.** Let `C` be a complete algebraically
closed nontrivially normed field with an ultrametric norm in which `p` is not a unit of the
valuation ring `O_C`. Then every monic polynomial of positive degree over the tilt
`O_C♭ = PreTilt O_C p` has a root in `O_C♭`. So `O_C♭` is integrally closed and its fraction
field `C♭` is algebraically closed (`TauCeti.IsAbsolutelyIntegrallyClosed.isAlgClosed`). -/
instance instIsAbsolutelyIntegrallyClosed : IsAbsolutelyIntegrallyClosed (PreTilt 𝒪[C] p) := by
  have : Fact (IsTopologicallyNilpotent (p : C)) :=
    ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one ((Valued.integer.norm_le_one (p : 𝒪[C])).lt_of_ne
      (Valued.integer.isUnit_iff_norm_eq_one.not.mp Fact.out))⟩
  have : IsAbsolutelyIntegrallyClosed 𝒪[tiltField p C] :=
    .of_isIntegrallyClosed_of_isAlgClosed (tiltField p C)
  exact .of_surjective (tiltField.integerEquivPreTilt p C : 𝒪[tiltField p C] →+* PreTilt 𝒪[C] p)
    (tiltField.integerEquivPreTilt p C).surjective

end PreTilt
