/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Complexification
public import TauCeti.Analysis.Polynomial.Puiseux.Monic
public import TauCeti.Analysis.Polynomial.Puiseux.RealRoots
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Polynomial.RealRoots.Reciprocal
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Ramified splittings and real roots from constant discriminant order

A monic polynomial with real polynomial coefficients, restricted along a real analytic
parametrization, admits a local analytic complex splitting after a ramified transverse
substitution when its discriminant has constant finite ambient order along the parametrization.
The complexification, transverse direction, branches and discriminant unit are constructed
from the real data. Neither a prepared discriminant nor a splitting is assumed.

The branches retain repeated labels on the exceptional hyperplane. Their restrictions there
give complex roots, even when the central fiber has multiple roots. Selecting the real branches
gives a local strictly ordered analytic enumeration of the real roots of the fibers, with constant
positive multiplicities.

The real root enumeration does not need monicity: it holds whenever the central fiber is
nonzero and the fibers have constant degree, even if the formal leading coefficient vanishes.
Translate the root coordinate to a nonroot `τ` of the central fiber and reverse at the formal
degree. The leading coefficient becomes the value at `τ`, which is nonzero near the center.
The integral normalization is then a monic polynomial over the same coefficient ring, and its
discriminant differs from the original one by a power of that value
(`Polynomial.discr_integralNormalization_reverse_comp_X_add_C`), so it has the same ambient order.
The monic case applies to it, and undoing normalization, reversal and translation recovers the
roots of the original fibers. None of these results assert constancy of the ambient order of the
original polynomial on the root sections.

## Main results

* `Polynomial.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq`: a monic family splits into
  analytic factors after a ramified transverse substitution, in every direction of an open dense
  set.
* `Polynomial.exists_analyticOnNhd_ordered_roots_of_orderAt_discr_eq`: the real roots of a
  family with nonzero central fiber and constant fiber degree have a local ordered analytic
  enumeration with constant multiplicities.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

/-- Constant finite ambient order of the formal discriminant along a real analytic
parametrization produces complex analytic splittings after transverse power substitutions.
The complexification of the parametrization is shared, and every real direction in an open
dense set gives such a splitting. The ramification exponent is the factorial of the formal
degree. The constructed discriminant unit is nonzero at the center; root labels may collide on
the exceptional hyperplane. -/
theorem _root_.Polynomial.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq
    (p : Polynomial (MvPolynomial σ ℝ)) (hp : p.Monic)
    {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m) :
    ∃ Φ : (ι → ℂ) → σ → ℂ, ∃ V : Set (σ → ℝ), IsOpen V ∧ Dense V ∧
      AnalyticAt ℂ Φ (fun j ↦ (a j : ℂ)) ∧
      (∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) ∧
      ∀ v ∈ V, ∃ r : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ, ∃ u : (ι → ℂ) × ℂ → ℂ,
        (∀ i, AnalyticAt ℂ (r i) ((fun j ↦ (a j : ℂ)), 0)) ∧
        AnalyticAt ℂ u ((fun j ↦ (a j : ℂ)), 0) ∧
        u ((fun j ↦ (a j : ℂ)), 0) ≠ 0 ∧
        ∀ᶠ z in 𝓝 ((fun j ↦ (a j : ℂ)), (0 : ℂ)),
          p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
            (Φ z.1 + z.2 ^ p.natDegree.factorial • (fun i ↦ (v i : ℂ)))) =
              ∏ i, (X - C (r i z)) ∧
          (p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
            (Φ z.1 + z.2 ^ p.natDegree.factorial • (fun i ↦ (v i : ℂ))))).discr =
              z.2 ^ (p.natDegree.factorial * m) * u z := by
  -- Prepare the discriminant on one complex polydisc directly from its real ambient order.
  obtain ⟨ρ₀, hρ₀, Φ, V, hVo, hV, hΦ₀, hreal₀, -, hdir⟩ :=
    p.discr.exists_complexification_dense_open_directions_eval_add_smul_eq_pow_mul hφ hm
  refine ⟨Φ, V, hVo, hV, hΦ₀ _ (mem_ball_self hρ₀),
    Filter.Eventually.mono (ball_mem_nhds a hρ₀) hreal₀, fun v hv ↦ ?_⟩
  obtain ⟨ρ, hρ, hρle, u, hu, hunit⟩ := hdir v hv
  have hΦ := hΦ₀.mono (ball_subset_ball hρle)
  have hreal := fun x hx ↦ hreal₀ x (ball_subset_ball hρle hx)
  let ac : ι → ℂ := fun j ↦ (a j : ℂ)
  let U := ball ac ρ
  let F : (ι → ℂ) × ℂ → ℂ[X] := fun z ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
      (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))))
  have hU : IsOpen U := isOpen_ball
  have hac : ac ∈ U := mem_ball_self hρ
  let : ContractibleSpace U := (convex_ball ac ρ).contractibleSpace ⟨ac, hac⟩
  let : SimplyConnectedSpace U := SimplyConnectedSpace.ofContractible U
  have hcoeff (i : ℕ) : AnalyticOnNhd ℂ (fun z ↦ (F z).coeff i) (U ×ˢ ball 0 ρ) := by
    intro z hz
    have hcoord (j : σ) : AnalyticAt ℂ
        (fun z : (ι → ℂ) × ℂ ↦ (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) j) z := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact ((analyticAt_pi_iff.1 (hΦ z.1 hz.1) j).comp analyticAt_fst).add
        (analyticAt_snd.mul analyticAt_const)
    simpa only [F, coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map,
      MvPolynomial.aeval_eq_eval] using
      AnalyticAt.aeval_mvPolynomial hcoord ((p.coeff i).map Complex.ofRealHom)
  have hmonic (z) : (F z).Monic := hp.map _
  have hdeg (z) : (F z).natDegree = p.natDegree := hp.natDegree_map _
  have hdiscr (z) (hz : z ∈ U ×ˢ ball 0 ρ) : (F z).discr = z.2 ^ m * u z := by
    rw [hp.discr_map]
    simpa only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_map] using (hunit z hz).2
  -- Monicity keeps the formal degree unchanged throughout the transverse family.
  obtain ⟨R, hR, hfit, r, hr, hsplit, -, -⟩ :=
    Polynomial.exists_analyticOnNhd_prod_X_sub_C_of_discr_eq_pow_mul hU hρ
      (fun i _ ↦ hcoeff i) (fun z _ ↦ hmonic z) (fun z _ ↦ hdeg z)
      hu (fun z hz ↦ (hunit z hz).1) hdiscr
  let Q : (ι → ℂ) × ℂ → (ι → ℂ) × ℂ := fun z ↦ (z.1, z.2 ^ p.natDegree.factorial)
  have hQ : AnalyticAt ℂ Q (ac, 0) := analyticAt_fst.prod (analyticAt_snd.pow _)
  have hzero : Q (ac, 0) = (ac, 0) := by simp [Q, p.natDegree.factorial_ne_zero]
  have hQmem (z) (hz : z ∈ U ×ˢ ball 0 R) : Q z ∈ U ×ˢ ball 0 ρ := by
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hz.2) (norm_nonneg _)
      p.natDegree.factorial_ne_zero).trans_le hfit
  refine ⟨r, fun z ↦ u (Q z), fun i ↦ hr i (ac, 0) ⟨hac, mem_ball_self hR⟩,
    (hu (ac, 0) ⟨hac, mem_ball_self hρ⟩).comp_of_eq hQ hzero,
    by simpa only [ac, Q, zero_pow p.natDegree.factorial_ne_zero] using
      (hunit (ac, 0) ⟨hac, mem_ball_self hρ⟩).1, ?_⟩
  filter_upwards [(hU.prod isOpen_ball).mem_nhds ⟨hac, mem_ball_self hR⟩] with z hz
  exact ⟨hsplit z hz, by simpa only [Q, ← pow_mul] using hdiscr (Q z) (hQmem z hz)⟩

/-- The real roots of a monic family along a real analytic parametrization, on which the formal
discriminant has constant finite ambient order, have a local strictly ordered analytic
enumeration with constant positive multiplicities. -/
private theorem exists_analyticOnNhd_ordered_roots_of_monic_of_orderAt_discr_eq
    (p : Polynomial (MvPolynomial σ ℝ)) (hp : p.Monic)
    {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m) :
    ∃ k : ℕ, ∃ s : Fin k → (ι → ℝ) → ℝ, ∃ U : Set (ι → ℝ), IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ s i x)) ∧
      (∀ x ∈ U, ∀ t,
        (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).IsRoot t ↔ ∃ i, s i x = t) ∧
      (∀ i, 0 < (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a))).rootMultiplicity (s i a)) ∧
      ∀ x ∈ U, ∀ i,
        (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).rootMultiplicity (s i x) =
          (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a))).rootMultiplicity (s i a) := by
  obtain ⟨Φ, V, -, hV, -, hreal, hdir⟩ :=
    p.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq hp hφ hm
  obtain ⟨v, hv⟩ := hV.nonempty
  obtain ⟨r, u, hr, hu, hu0, hsplit⟩ := hdir v hv
  let P : (ι → ℂ) × ℂ → ℂ[X] := fun z ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
      (Φ z.1 + z.2 ^ p.natDegree.factorial • (fun i ↦ (v i : ℂ))))
  let ψ : (ι → ℝ) → ι → ℂ := fun x i ↦ (x i : ℂ)
  have hψ : AnalyticAt ℝ ψ a := by
    apply analyticAt_pi_iff.2
    intro i
    exact Complex.ofRealCLM.analyticAt _ |>.comp
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).analyticAt a)
  have hP : ∀ᶠ x in 𝓝 a, P (ψ x, 0) =
      (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).map (algebraMap ℝ ℂ) := by
    filter_upwards [hreal] with x hx
    simp only [P, ψ, zero_pow p.natDegree.factorial_ne_zero, zero_smul, add_zero, hx,
      Polynomial.map_map]
    congr 1
    rw [MvPolynomial.comp_eval₂Hom]
    rfl
  exact exists_analyticOnNhd_ordered_real_roots_on_hyperplane hr
    (hsplit.mono fun _ hz ↦ hz.1) hu hu0 (hsplit.mono fun _ hz ↦ hz.2) hψ hP

/-- **Local analytic roots from constant discriminant order.** Let `p` be a polynomial whose
coefficients are real polynomials, specialized along a real analytic parametrization `φ`. If the
fiber at `a` is nonzero, the fibers near `a` have constant degree, and the formal discriminant of
`p` has constant finite ambient order near `a`, then the real roots of the fibers near `a` have a
strictly ordered analytic enumeration with constant positive multiplicities.

The formal leading coefficient of `p` may vanish at `a`, so the degree of the fibers can be
smaller than the formal degree at which the discriminant is taken. -/
theorem _root_.Polynomial.exists_analyticOnNhd_ordered_roots_of_orderAt_discr_eq
    (p : Polynomial (MvPolynomial σ ℝ)) {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {d m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hp : p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a)) ≠ 0)
    (hd : ∀ᶠ x in 𝓝 a, (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).natDegree = d)
    (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m) :
    ∃ k : ℕ, ∃ s : Fin k → (ι → ℝ) → ℝ, ∃ U : Set (ι → ℝ), IsOpen U ∧ a ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (s i) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ s i x)) ∧
      (∀ x ∈ U, ∀ t,
        (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).IsRoot t ↔ ∃ i, s i x = t) ∧
      (∀ i, 0 < (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a))).rootMultiplicity (s i a)) ∧
      ∀ x ∈ U, ∀ i,
        (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).rootMultiplicity (s i x) =
          (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a))).rootMultiplicity (s i a) := by
  let ev : (ι → ℝ) → MvPolynomial σ ℝ →+* ℝ := fun x ↦
    MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x)
  -- Center reciprocal coordinates at a point `τ` which is not a root of the central fiber.
  obtain ⟨τ, hτ⟩ := Infinite.exists_notMem_finset (p.map (ev a)).roots.toFinset
  have hτ0 : (p.map (ev a)).eval τ ≠ 0 :=
    fun h ↦ hτ (Multiset.mem_toFinset.2 ((mem_roots hp).2 h))
  let c : MvPolynomial σ ℝ := p.eval (MvPolynomial.C τ)
  have hevc (x : ι → ℝ) : ev x c = (p.map (ev x)).eval τ := by
    simp only [c, eval_map, ← eval₂_hom, ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      RingHom.id_apply]
  have hτA : AnalyticAt ℝ (fun x ↦ (p.map (ev x)).eval τ) a := by
    simpa only [← hevc, ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.aeval_eq_eval₂Hom,
      Algebra.algebraMap_self] using
      AnalyticAt.aeval_mvPolynomial (fun i ↦ analyticAt_pi_iff.1 hφ i) c
  have hτnear : ∀ᶠ x in 𝓝 a, ev x c ≠ 0 := by
    simpa only [hevc] using hτA.continuousAt.eventually_ne hτ0
  have hc : c ≠ 0 := fun h ↦ hτ0 (by rw [← hevc, h, map_zero])
  -- The normalized reversal is monic, and its discriminant has the same order near `a`.
  let P := (p.comp (X + C (MvPolynomial.C τ))).reverse.integralNormalization
  have hP : P.Monic := monic_integralNormalization fun h ↦ hc <|
    (p.leadingCoeff_reverse_comp_X_add_C hc).symm.trans (by rw [h, leadingCoeff_zero])
  have hPm : ∀ᶠ x in 𝓝 a, P.discr.orderAt (φ x) = m := by
    filter_upwards [hm, hτnear] with x hx hxc
    rw [p.discr_integralNormalization_reverse_comp_X_add_C hc, MvPolynomial.orderAt_mul,
      MvPolynomial.orderAt_pow, MvPolynomial.orderAt_eq_zero_iff.2 hxc, smul_zero, zero_add, hx]
  obtain ⟨k, s, U, hU, haU, hs, hmono, hroots, -, hmult⟩ :=
    exists_analyticOnNhd_ordered_roots_of_monic_of_orderAt_discr_eq P hP hφ hPm
  -- Near `a`, specialization commutes with translation, reversal and normalization.
  have hnorm : ∀ᶠ x in 𝓝 a, P.map (ev x) =
      ((((p.map (ev x)).comp (X + C τ)).reflect p.natDegree).integralNormalization) := by
    filter_upwards [hτnear] with x hx
    rw [← integralNormalization_map _ _ (by rwa [p.leadingCoeff_reverse_comp_X_add_C hc]),
      reverse, ← taylor_apply, natDegree_taylor, ← reflect_map, taylor_apply]
    simp only [Polynomial.map_comp, Polynomial.map_add, map_X, map_C, ev,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.id_apply]
  have hUa : ∀ᶠ x in 𝓝 a, x ∈ U := hU.mem_nhds haU
  -- Undo normalization, reversal and translation to obtain the roots of the fibers.
  exact exists_analyticOnNhd_ordered_roots_of_integralNormalization_reflect_comp_X_add_C
    (F := fun x ↦ p.map (ev x)) (N := p.natDegree) (fun i ↦ hs i a haU)
    (hmono a haU).injective (by rw [← hd.self_of_nhds]; exact natDegree_map_le) hd hτA hτ0
    (by filter_upwards [hUa, hnorm] with x hx hn; rw [← hn]; exact hroots x hx)
    (by
      filter_upwards [hUa, hnorm] with x hx hn
      rw [← hn, ← hnorm.self_of_nhds]
      exact hmult x hx)

end TauCeti
