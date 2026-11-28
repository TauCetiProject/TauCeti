/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Integer
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Analysis.Normed.Algebra.ScaleRoots
import TauCeti.RingTheory.AdicCompletion.Newton
import TauCeti.RingTheory.AdicCompletion.Perfection
import TauCeti.RingTheory.Perfectoid.IsAlgClosed
import TauCeti.RingTheory.Perfectoid.PreTilt.ApproximateRoot
import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing
import TauCeti.RingTheory.Polynomial.ScaleRoots
import TauCeti.Topology.Algebra.Valued.Integer

/-!
# The tilt of an algebraically closed field is algebraically closed

Let `K` be a complete nontrivially normed field with an ultrametric norm in which the prime `p`
is topologically nilpotent, with valuation ring `O_K = 𝒪[K]` and tilt `K♭ = tiltField p K`. The
valuation ring of `K♭` is Mathlib's tilt `O_K♭ = PreTilt O_K p`
(`TauCeti.Perfectoid.tiltField.integerEquivPreTilt`), and under this identification the norm of
`K♭` is `‖x‖ = ‖x♯‖`. If `K` is algebraically closed, for instance `K = ℂ_p`, then `K♭` is
algebraically closed, and `O♭ = PreTilt O_K p` is absolutely integrally closed: every monic
polynomial of positive degree over `O♭` has a root in `O♭`, so the fraction field of `O♭` is
algebraically closed.

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

## Main results

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
open Ideal Polynomial TauCeti

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
  -- `c ≠ 0` of norm less than one dividing `p`, and `ϖ ∈ O♭` with `ϖ♯ = c`
  obtain ⟨c, hc0, hc1, hcp⟩ : ∃ c : 𝒪[C], c ≠ 0 ∧ ‖(c : C)‖ < 1 ∧ c ∣ (p : 𝒪[C]) := by
    by_cases h : (p : 𝒪[C]) = 0
    · obtain ⟨d, hd0, hd1⟩ := NormedField.exists_norm_lt_one C
      exact ⟨⟨d, Valued.integer.mem_iff.mpr hd1.le⟩,
        fun h0 ↦ norm_pos_iff.mp hd0 (by simpa using congrArg Subtype.val h0), hd1, h ▸ dvd_zero _⟩
    · exact ⟨p, h, Valued.integer.norm_natCast_lt_one, dvd_rfl⟩
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
    (isPerfectoidTateRing_of_isAlgClosed Valued.integer.norm_natCast_lt_one)
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
    ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one Valued.integer.norm_natCast_lt_one⟩
  have : IsAbsolutelyIntegrallyClosed 𝒪[tiltField p C] :=
    .of_isIntegrallyClosed_of_isAlgClosed (tiltField p C)
  exact .of_surjective (tiltField.integerEquivPreTilt p C : 𝒪[tiltField p C] →+* PreTilt 𝒪[C] p)
    (tiltField.integerEquivPreTilt p C).surjective

end PreTilt
