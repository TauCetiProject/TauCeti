/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.WittenLaplacian.Gap
public import TauCeti.Analysis.Calculus.WittenLaplacian.Quasimode
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The low-energy forms of the Witten Laplacian are counted by the critical points

Witten's analytic proof of the Morse inequalities shows that, for large `t`, the number of
low-lying eigenvalues of the Witten Laplacian `Δ_t` (`TauCeti.euclideanWittenLaplacian`) in degree
`m` is the number of critical points of Morse index `m`. This file proves the two halves of that
count for the quadratic form of `Δ_t` on compactly supported forms, for a function `f` on `ℝ^ι`
which near each point `p` of a finite separated set `P` is a diagonal quadratic model
`y ↦ f p + ∑ᵢ a p i (yᵢ - pᵢ)² / 2` with every `|a p i| ≥ c > 0`, and whose gradient and Hessian
are bounded below and above away from `P`. The Morse index of `p` is the number of negative
`a p i`.

**The upper bound.** For large `t`, every space of compactly supported `C²` forms of degree `m` on
which the quadratic form of `Δ_t` is at most `t c` times the squared norm has dimension at most the
number `N` of points of `P` of index `m`
(`TauCeti.exists_forall_rank_le_of_integral_sum_euclideanWittenLaplacian_mul_le`). Such a space
meets the common kernel of the `N` linear functionals `φ ↦ ⟪J p φ, Ψ_{p,t}⟫`, the pairings of the
localized pieces with the translated Gaussian ground states of the quadratic models, only in `0`:
a nonzero form in that kernel has quadratic form at least `(2 t c - K) ‖φ‖²` by the gap above the
ground states (`TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal`),
which exceeds `t c ‖φ‖²` once `t c > K`. So the space embeds into `ℝ^N`.

**The count.** The cut-off ground states at the points of index `m` span a space of dimension
exactly `N` on which the quadratic form is small, by
`TauCeti.exists_forall_exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le`.
Together, for all large `t`, `N` is the largest dimension of a space of compactly supported `C²`
forms of degree `m` on which the quadratic form of `Δ_t` is at most `t c` times the squared norm
(`TauCeti.exists_forall_isGreatest_rank_of_integral_sum_euclideanWittenLaplacian_mul_le`). For a
self-adjoint realization of `Δ_t` whose quadratic form is the closure of this one, the min-max
principle would turn this into the statement that `Δ_t` has exactly `N` eigenvalues below `t c`
in degree `m`, counted with multiplicity; no such realization is constructed here.

## Main results

* `TauCeti.exists_forall_rank_le_of_integral_sum_euclideanWittenLaplacian_mul_le`: for large `t`,
  a space of forms of degree `m` with quadratic form at most `t c ‖φ‖²` has dimension at most the
  number of critical points of index `m`.
* `TauCeti.exists_forall_isGreatest_rank_of_integral_sum_euclideanWittenLaplacian_mul_le`: for
  large `t`, that number is the largest such dimension.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 11 (Witten's proof of the Morse inequalities).
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Under the hypotheses of
`TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal`, a form whose
quadratic form is at most `t c ‖φ‖²` vanishes once `t c > K`. -/
private theorem eq_zero_of_orthogonal_of_integral_sum_euclideanWittenLaplacian_mul_le
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {P : Finset (ι → ℝ)} {J₀ : (ι → ℝ) → ℝ}
    {J : (ι → ℝ) → (ι → ℝ) → ℝ} {a : (ι → ℝ) → ι → ℝ} {b : (ι → ℝ) → ℝ} {t c c₀ h K : ℝ}
    {m : ℕ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφm : ∀ x s, φ x s ≠ 0 → s.card = m) (hJ₀ : ContDiff ℝ 2 J₀)
    (hJ : ∀ p ∈ P, ContDiff ℝ 2 (J p))
    (hJ1 : ∀ x, φ x ≠ 0 → J₀ x ^ 2 + ∑ p ∈ P, J p x ^ 2 = 1)
    (hK : ∀ x, φ x ≠ 0 → ∑ i, fderiv ℝ J₀ x (Pi.single i 1) ^ 2 +
      ∑ p ∈ P, ∑ i, fderiv ℝ (J p) x (Pi.single i 1) ^ 2 ≤ K)
    (hmodel : ∀ p ∈ P, ∀ x, J p x ≠ 0 →
      f =ᶠ[𝓝 x] fun y ↦ b p + diagonalQuadratic (a p) (y - p))
    (hc : ∀ p ∈ P, ∀ i, c ≤ |a p i|)
    (horth : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card = m →
      ∫ x, ∑ s, diagonalQuadraticWittenEigenform (a p) t 0
        (Finset.univ.filter fun i ↦ a p i < 0) (x - p) s * (J p • φ) x s = 0)
    (hc₀ : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    (ht : 0 ≤ t) (htc : 2 * c + h ≤ t * c₀) (htK : K < t * c)
    (hE : ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ t * c * ∫ x, ∑ s, φ x s ^ 2) :
    φ = 0 := by
  have key := mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal hf hφ hφc
    hφm hJ₀ hJ hJ1 hK hmodel hc horth hc₀ hh ht htc
  -- `(t c - K) ‖φ‖² ≤ 0` with `t c > K`, so `φ` has norm zero.
  have hN : ∫ x, ∑ s, φ x s ^ 2 ≤ 0 := by nlinarith
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hx
  refine hN.not_gt (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp hφ.continuous).pow 2)
    (hφc.comp_left (g := fun v : Finset ι → ℝ ↦ ∑ s, v s ^ 2) (by simp))
    (fun y ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (x := x) ?_)
  exact (Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨s, Finset.mem_univ s, sq_pos_iff.2 hs⟩).ne'

/-- **At most as many low-energy forms as critical points.** Let `f` be a `C²` function on `ℝ^ι`
and `P` a finite set of points at mutual distance at least `2 r`. Suppose that on the ball of
radius `r` around each `p ∈ P`, `f` is the quadratic model `y ↦ f p + ∑ᵢ a p i (yᵢ - pᵢ)² / 2`
with every `|a p i| ≥ c > 0`, and that outside the balls of radius `ρ < r` around the points of
`P`, `|df|² ≥ c₀ > 0` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h`. Then for all large `t`, every space `V` of
compactly supported `C²` forms of degree `m` on which the quadratic form of the Witten Laplacian
is at most `t c ‖φ‖²` has dimension at most the number of points of `P` of Morse index `m`, the
number of negative `a p i`. -/
theorem exists_forall_rank_le_of_integral_sum_euclideanWittenLaplacian_mul_le
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} {ρ r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) (hP : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q) {a : (ι → ℝ) → ι → ℝ}
    (hfa : ∀ p ∈ P, EqOn f (fun y ↦ f p + diagonalQuadratic (a p) (y - p)) (ball p r))
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdf : ∀ x, (∀ p ∈ P, ρ < dist x p) → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {h : ℝ} (hh : ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h) (m : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ V : Submodule ℝ ((ι → ℝ) → Finset ι → ℝ),
      (∀ φ ∈ V, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ (∀ x s, φ x s ≠ 0 → s.card = m) ∧
        ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ t * c * ∫ x, ∑ s, φ x s ^ 2) →
      Module.rank ℝ V ≤
        (P.filter fun p ↦ (Finset.univ.filter fun i ↦ a p i < 0).card = m).card := by
  classical
  obtain ⟨J₀, J, hJ₀, hJ, hJ1, hJr, hJ₀ρ, hJ₀c, hJc⟩ := exists_sq_add_sum_sq_eq_one hρ hρr hP
  obtain ⟨K₀, hK₀⟩ :=
    (hJ₀.of_le (by simp)).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv hJ₀c
  choose K hK using fun p ↦
    ((hJ p).of_le (by simp)).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv
      ((hJc p).fderiv (𝕜 := ℝ))
  refine ⟨max (max ((2 * c + h) / c₀) ((K₀ + ∑ p ∈ P, K p + 1) / c)) 0, fun t ht V hV ↦ ?_⟩
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have ht₁ : 2 * c + h ≤ t * c₀ :=
    (div_le_iff₀ hc₀).1 ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  have ht₂ : K₀ + ∑ p ∈ P, K p + 1 ≤ t * c :=
    (div_le_iff₀ hc).1 ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
  set Pm := P.filter fun p ↦ (Finset.univ.filter fun i ↦ a p i < 0).card = m
  -- The translated Gaussian ground state of the quadratic model at `p`.
  set Ψ : (ι → ℝ) → (ι → ℝ) → Finset ι → ℝ := fun p x ↦
    diagonalQuadraticWittenEigenform (a p) t 0 (Finset.univ.filter fun i ↦ a p i < 0) (x - p)
  have hΨ : ∀ p, Continuous (Ψ p) := fun p ↦
    (contDiff_diagonalQuadraticWittenEigenform (n := 0) _ _ _ _).continuous.comp
      (continuous_id.sub continuous_const)
  have hint : ∀ φ ∈ V, ∀ p, Integrable fun x ↦ ∑ s, Ψ p x s * (J p • φ) x s := fun φ hφ p ↦
    ((hJ p).continuous.smul (hV φ hφ).1.continuous).integrable_sum_mul_of_continuousOn
      (hV φ hφ).2.1.smul_left subset_rfl (hΨ p).continuousOn
  -- The pairings of the localized pieces with the ground states at the points of index `m`.
  let L : V →ₗ[ℝ] Pm → ℝ :=
    { toFun := fun φ p ↦ ∫ x, ∑ s, Ψ p x s * (J p • (φ : (ι → ℝ) → Finset ι → ℝ)) x s
      map_add' := fun φ ψ ↦ by
        funext p
        simp only [Submodule.coe_add, smul_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        exact integral_add (hint φ φ.property p) (hint ψ ψ.property p)
      map_smul' := fun u φ ↦ by
        funext p
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Finset.mul_sum, Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun s _ ↦ by ring }
  -- A form of `V` orthogonal to the ground states is zero, by the gap above the ground states.
  have hL : Function.Injective L := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun φ hφ0 ↦ Subtype.ext ?_)
    obtain ⟨hφ, hφc, hφm, hE⟩ := hV φ φ.property
    exact eq_zero_of_orthogonal_of_integral_sum_euclideanWittenLaplacian_mul_le
      (fun x _ ↦ hf.contDiffAt) hφ hφc hφm (hJ₀.of_le (by simp))
      (fun p _ ↦ (hJ p).of_le (by simp)) (fun x _ ↦ hJ1 x)
      (fun x _ ↦ add_le_add (hK₀ x) (Finset.sum_le_sum fun p _ ↦ hK p x))
      (fun p hp x hx ↦ eventuallyEq_of_mem (isOpen_ball.mem_nhds (hJr p x hx)) (hfa p hp)) hca
      (fun p hp hpm ↦ congrFun hφ0 ⟨p, Finset.mem_filter.2 ⟨hp, hpm⟩⟩)
      (fun x hx _ ↦ hdf x (hJ₀ρ x hx)) (fun x hx _ ↦ hh x (hJ₀ρ x hx)) ht₀ ht₁ (by linarith) hE
  calc Module.rank ℝ V ≤ Module.rank ℝ (Pm → ℝ) := LinearMap.rank_le_of_injective L hL
    _ = Pm.card := by rw [rank_fun', Fintype.card_coe]

/-- **The low-energy forms are counted by the critical points.** Under the hypotheses of
`TauCeti.exists_forall_rank_le_of_integral_sum_euclideanWittenLaplacian_mul_le`, for all large `t`
the largest dimension of a space of compactly supported `C²` forms of degree `m` on which the
quadratic form of the Witten Laplacian is at most `t c ‖φ‖²` is the number of points of `P` of
Morse index `m`. -/
theorem exists_forall_isGreatest_rank_of_integral_sum_euclideanWittenLaplacian_mul_le
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} {ρ r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) (hP : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q) {a : (ι → ℝ) → ι → ℝ}
    (hfa : ∀ p ∈ P, EqOn f (fun y ↦ f p + diagonalQuadratic (a p) (y - p)) (ball p r))
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdf : ∀ x, (∀ p ∈ P, ρ < dist x p) → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {h : ℝ} (hh : ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h) (m : ℕ) :
    ∃ T, ∀ t, T ≤ t → IsGreatest
      {d | ∃ V : Submodule ℝ ((ι → ℝ) → Finset ι → ℝ), Module.rank ℝ V = d ∧
        ∀ φ ∈ V, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ (∀ x s, φ x s ≠ 0 → s.card = m) ∧
          ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ t * c * ∫ x, ∑ s, φ x s ^ 2}
      ((P.filter fun p ↦ (Finset.univ.filter fun i ↦ a p i < 0).card = m).card) := by
  obtain ⟨T₁, hT₁⟩ :=
    exists_forall_exists_finrank_eq_forall_integral_sum_euclideanWittenLaplacian_mul_le
      (hρ.trans hρr) hP hfa (fun p hp i ↦ abs_pos.1 (hc.trans_le (hca p hp i))) m hc
  obtain ⟨T₂, hT₂⟩ := exists_forall_rank_le_of_integral_sum_euclideanWittenLaplacian_mul_le hf hρ
    hρr hP hfa hc hca hc₀ hdf hh m
  refine ⟨max (max T₁ T₂) 1, fun t ht ↦ ⟨?_, ?_⟩⟩
  · -- The span of the cut-off ground states, whose energy is at most `c ≤ t c` times its norm.
    obtain ⟨V, hVN, hV⟩ := hT₁ t ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
    have ht₁ : 1 ≤ t := (le_max_right _ _).trans ht
    have hV' : ∀ φ ∈ V, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ (∀ x s, φ x s ≠ 0 → s.card = m) ∧
        ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ≤ t * c * ∫ x, ∑ s, φ x s ^ 2 := by
      intro φ hφ
      obtain ⟨hφ, hφc, hφm, hE⟩ := hV φ hφ
      refine ⟨hφ.of_le (by simp), hφc, hφm, hE.trans (mul_le_mul_of_nonneg_right
        (by nlinarith) (integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))⟩
    -- By the upper bound `V` is finite dimensional, so its rank is its `finrank`.
    have hle := hT₂ t ((le_max_right _ _).trans ((le_max_left _ _).trans ht)) V hV'
    have : Module.Finite ℝ V :=
      Module.rank_lt_aleph0_iff.1 (hle.trans_lt (Cardinal.natCast_lt_aleph0))
    exact ⟨V, by rw [← hVN, Module.finrank_eq_rank], hV'⟩
  · rintro _ ⟨V, rfl, hV⟩
    exact hT₂ t ((le_max_right _ _).trans ((le_max_left _ _).trans ht)) V hV

end TauCeti
