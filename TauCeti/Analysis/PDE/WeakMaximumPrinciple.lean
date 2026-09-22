/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.ChainRule

/-!
# The weak maximum principle for `H¹` subsolutions

Let `Ω` be open and let `L u = -∂ⱼ(aⁱʲ ∂ᵢu) + c u` be a divergence-form operator whose
principal part is measurable and uniformly elliptic with constants `0 < λ ≤ Λ` and whose
zeroth-order coefficient satisfies `c ≥ 0`. A function `u ∈ H¹(Ω)` is a **weak subsolution**,
`L u ≤ 0` in `Ω`, when its energy form

`a(u, v) = ∫_Ω ⟨a ∇u, ∇v⟩ + c u v`

is nonpositive against every nonnegative `v ∈ H¹₀(Ω)`. This file proves that such a `u` is
bounded above in `Ω` by any level `k ≥ 0` that it respects on the boundary:

`(u - k)⁺ ∈ H¹₀(Ω)` implies `u ≤ k` almost everywhere in `Ω`.

Membership of the truncation in `H¹₀(Ω)` is the `H¹` formulation of the boundary condition
`u ≤ k on ∂Ω`, so no regularity of `∂Ω` enters, and no regularity of the coefficients beyond
measurability. The comparison principle for a subsolution against a supersolution, and
uniqueness of a weak solution with prescribed boundary values, follow by applying the estimate
to the difference at the level `k = 0`.

## The argument

The truncation `(u - k)⁺` is itself an admissible test function: it is nonnegative, and by
hypothesis it lies in `H¹₀(Ω)`. Its weak gradient is `1_{u > k} ∇u`, so on the set where the
truncation is active the pairing `a(u, (u - k)⁺)` has the same principal part as the diagonal
energy `a((u - k)⁺, (u - k)⁺)`, while off that set both vanish. The zeroth-order terms compare
because `c ≥ 0` and `0 ≤ (u - k)⁺ ≤ u` on the active set, and that last inequality is where
`k ≥ 0` is used. Hence

`λ ‖∇(u - k)⁺‖²_{L²} ≤ a((u - k)⁺, (u - k)⁺) ≤ a(u, (u - k)⁺) ≤ 0`,

so the truncation has vanishing weak gradient, and a Poincaré inequality on `H¹₀(Ω)` forces it
to vanish altogether.

## What the hypotheses do

The Poincaré inequality is what turns the vanishing of `∇(u - k)⁺` into the vanishing of
`(u - k)⁺`, and it is load-bearing: on a domain of finite measure the nonzero constants lie in
`H¹(Ω)` with vanishing gradient, and on the whole space no Poincaré inequality holds at all
(`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`). It is carried as a bound on the
single vector `(u - k)⁺`, so a caller may supply it from any source; the corollaries below
supply it from membership in `H¹₀(Ω)` for a domain trapped in a slab, hence for any bounded
domain.

The sign condition `c ≥ 0` is the same one the classical weak maximum principle needs
(`TauCeti.le_of_mul_le_laplacian_add_fderiv_le_frontier`), and it cannot be dropped:
`TauCeti.exists_neg_constant_laplacian_eq_mul_eq_zero_on_frontier_pos` exhibits a solution of
`-Δu + cu = 0` with the constant `c = -1` that vanishes on the frontier and is positive
inside. The level condition `k ≥ 0` enters only through the zeroth-order term: it is what
gives `(u - k)⁺ ≤ u` where the truncation is active, hence `c u (u - k)⁺ ≥ c ((u - k)⁺)²`. At
`k = 0` that inequality is an identity, which is what makes the comparison principle below
available for the difference of two functions of either sign.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.energyFormH1_posPartAbove_self_le`: testing a subsolution
  against its own truncation dominates the energy of the truncation.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_of_energyFormH1_nonpos_of_poincare`: the weak
  maximum principle, with the Poincaré inequality as a hypothesis.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_of_energyFormH1_nonpos_of_subset_slab` and
  `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_of_energyFormH1_nonpos_of_subset_ball`: the
  weak maximum principle on a slab-contained, hence on a bounded, domain, with
  `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_value_of_energyFormH1_le_of_subset_ball` and
  `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_value_of_energyFormH1_eq_of_subset_ball`
  beside them.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_le_value_of_energyFormH1_le_of_poincare`: the
  comparison principle for a subsolution against a supersolution, and
  `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_value_of_energyFormH1_eq_of_poincare`:
  uniqueness of a weak solution with prescribed boundary values.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.1.
* L. C. Evans, *Partial Differential Equations*, §6.4.1.
-/

public section

noncomputable section

open MeasureTheory Matrix Metric Set TopologicalSpace

namespace TauCeti

namespace PDE

section Domain

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam gamma P : ℝ}

omit [DecidableEq ι] in
/-- The pointwise comparison behind the weak maximum principle: at almost every point of `Ω`
the energy density of the truncation `w = (u - k)⁺` against itself is at most the energy
density of `u` against `w`. On `{u > k}` the two gradients agree and `0 ≤ w ≤ u`; off that set
both `w` and its gradient vanish. -/
private theorem ae_energyIntegrand_jetField_posPartAbove_self_le
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k) :
    ∀ᵐ x ∂mu.restrict Omega,
      energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) (c x)
          (jetField (W1p.posPartAbove ENNReal.ofNat_ne_top hk u) x)
          (jetField (W1p.posPartAbove ENNReal.ofNat_ne_top hk u) x) ≤
        energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) (c x)
          (jetField u x) (jetField (W1p.posPartAbove ENNReal.ofNat_ne_top hk u) x) := by
  set w := W1p.posPartAbove (p := 2) ENNReal.ofNat_ne_top hk u
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet,
    W1p.value_posPartAbove_ae (p := 2) ENNReal.ofNat_ne_top hk u,
    W1p.gradient_posPartAbove_ae (p := 2) ENNReal.ofNat_ne_top hk u] with x hx hval hgrad
  rcases lt_or_ge k (W1p.value u x) with hxu | hxu
  · have hgradx : W1p.gradient w x = W1p.gradient u x := by
      rw [hgrad]
      exact Set.indicator_of_mem (show x ∈ {y | k < W1p.value u y} from hxu)
        (⇑(W1p.gradient u))
    have hvalx : W1p.value w x = W1p.value u x - k := by
      rw [hval, max_eq_left (by linarith)]
    have hwnn : 0 ≤ W1p.value w x := by rw [hvalx]; linarith
    have hwle : W1p.value w x ≤ W1p.value u x := by rw [hvalx]; linarith
    simp only [energyIntegrand_apply, jetField_apply, hgradx, driftForm_apply, massForm_apply,
      Pi.zero_apply, inner_zero_left, zero_mul]
    have hmass : c x * W1p.value w x * W1p.value w x ≤
        c x * W1p.value u x * W1p.value w x := by
      nlinarith [mul_nonneg (mul_nonneg (hc_nonneg x hx) hwnn) (sub_nonneg.2 hwle)]
    linarith
  · have hgradx : W1p.gradient w x = 0 := by
      rw [hgrad]
      exact Set.indicator_of_notMem (show x ∉ {y | k < W1p.value u y} by simpa using hxu)
        (⇑(W1p.gradient u))
    have hvalx : W1p.value w x = 0 := by
      rw [hval, max_eq_right (by linarith)]
    simp [energyIntegrand_apply, hgradx, hvalx, massForm_apply]

/-- **A subsolution tested against its own truncation dominates the truncation's energy.**
For a measurable, uniformly elliptic principal part `a`, a nonnegative zeroth-order
coefficient `c` and a level `k ≥ 0`, the truncation `w = (u - k)⁺` of `u ∈ H¹(Ω)` satisfies

`a(w, w) ≤ a(u, w)`.

This is the inequality that makes the truncation an efficient test function: the left-hand
side is bounded below by `λ‖∇w‖²_{L²}` through uniform ellipticity, while the right-hand side
is what the subsolution hypothesis controls. -/
theorem UniformlyEllipticOn.energyFormH1_posPartAbove_self_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k) :
    energyFormH1 a 0 c (W1p.posPartAbove ENNReal.ofNat_ne_top hk u)
        (W1p.posPartAbove ENNReal.ofNat_ne_top hk u) ≤
      energyFormH1 a 0 c u (W1p.posPartAbove ENNReal.ofNat_ne_top hk u) := by
  have hb : AEStronglyMeasurable (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      (mu.restrict Omega) := aestronglyMeasurable_const
  have hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖(0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤ 0 := fun _ _ => by simp
  rw [energyFormH1_def, energyFormH1_def]
  exact integral_mono_ae
    (h.integrable_energyIntegrand_jetField ha hb hc hb_bound hc_bound _ _)
    (h.integrable_energyIntegrand_jetField ha hb hc hb_bound hc_bound _ _)
    (ae_energyIntegrand_jetField_posPartAbove_self_le hc_nonneg hk)

/-- **The weak maximum principle for a weak subsolution.** Let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `c ≥ 0` be measurable and bounded, and let
`u ∈ H¹(Ω)` satisfy `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. If, at a level `k ≥ 0`,
the truncation `(u - k)⁺` lies in `H¹₀(Ω)` — the `H¹` reading of `u ≤ k` on `∂Ω` — and obeys
the Poincaré bound `‖(u - k)⁺‖_{L²} ≤ P‖∇(u - k)⁺‖_{L²}`, then `u ≤ k` almost everywhere
in `Ω`.

The Poincaré hypothesis is carried on the single vector `(u - k)⁺`, as in
`TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_poincare`; the slab and
ball corollaries below supply it from the membership hypothesis. -/
theorem UniformlyEllipticOn.ae_value_le_of_energyFormH1_nonpos_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p mu Omega 2) ≤ 0)
    (hmem : W1p.posPartAbove ENNReal.ofNat_ne_top hk u ∈ w1p0Submodule mu Omega 2)
    (hP : ‖W1p.value (W1p.posPartAbove ENNReal.ofNat_ne_top hk u)‖ ≤
      P * ‖W1p.gradient (W1p.posPartAbove ENNReal.ofNat_ne_top hk u)‖) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  set w := W1p.posPartAbove (p := 2) ENNReal.ofNat_ne_top hk u
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value w x := by
    filter_upwards [W1p.value_posPartAbove_ae (p := 2) ENNReal.ofNat_ne_top hk u] with x hx
    rw [hx]
    exact le_max_right _ _
  have hself : energyFormH1 a 0 c w w ≤ 0 :=
    (h.energyFormH1_posPartAbove_self_le ha hc hc_bound hc_nonneg hk).trans
      (hu ⟨w, hmem⟩ hnonneg)
  have hlow : lam * ‖W1p.gradient w‖ ^ 2 ≤ energyFormH1 a 0 c w w :=
    h.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift ha hc (fun _ _ => rfl)
      hc_bound hc_nonneg w
  have hsq : ‖W1p.gradient w‖ ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (by simpa using hlow.trans hself) h.pos
  have hgrad : ‖W1p.gradient w‖ = 0 :=
    pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hsq (sq_nonneg _))
  have hvalue : W1p.value w = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm ?_ (norm_nonneg _)
    simpa [hgrad] using hP
  have hzero : ∀ᵐ x ∂mu.restrict Omega, W1p.value w x = 0 := by
    rw [hvalue]
    filter_upwards [Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx
    simpa using hx
  filter_upwards [hzero, W1p.value_posPartAbove_ae (p := 2) ENNReal.ofNat_ne_top hk u] with
    x hx hval
  rw [hval] at hx
  have := le_max_left (W1p.value u x - k) 0
  rw [hx] at this
  linarith

/-- **The comparison principle for weak sub- and supersolutions.** If `u, v ∈ H¹(Ω)` satisfy
`a(u, z) ≤ a(v, z)` for every nonnegative `z ∈ H¹₀(Ω)` — as a weak subsolution and a weak
supersolution of one equation do — and `(u - v)⁺ ∈ H¹₀(Ω)` obeys a Poincaré bound, then
`u ≤ v` almost everywhere in `Ω`.

This is the weak maximum principle at the level `k = 0` applied to the difference `u - v`, for
which the hypothesis `u ≤ v on ∂Ω` is the membership `(u - v)⁺ ∈ H¹₀(Ω)`. -/
theorem UniformlyEllipticOn.ae_value_le_value_of_energyFormH1_le_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    {u v : W1p mu Omega 2}
    (huv : ∀ z : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (z : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (z : W1p mu Omega 2) ≤
          energyFormH1 a 0 c v (z : W1p mu Omega 2))
    (hmem : W1p.posPart ENNReal.ofNat_ne_top (u - v) ∈ w1p0Submodule mu Omega 2)
    (hP : ‖W1p.value (W1p.posPart ENNReal.ofNat_ne_top (u - v))‖ ≤
      P * ‖W1p.gradient (W1p.posPart ENNReal.ofNat_ne_top (u - v))‖) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hb : AEStronglyMeasurable (0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      (mu.restrict Omega) := aestronglyMeasurable_const
  have hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖(0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤ 0 := fun _ _ => by simp
  have hcoeff : MemLp (fun x => energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) (c x)) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun x hx => h.upper_bound hx) hb_bound hc_bound
  have hsub : ∀ z : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (z : W1p mu Omega 2) x) →
        energyFormH1 a 0 c (u - v) (z : W1p mu Omega 2) ≤ 0 := by
    intro z hz
    rw [energyFormH1_sub_left hcoeff, sub_nonpos]
    exact huv z hz
  have hposPart : W1p.posPartAbove (p := 2) ENNReal.ofNat_ne_top le_rfl (u - v) =
      W1p.posPart ENNReal.ofNat_ne_top (u - v) := W1p.posPartAbove_zero _ _
  have key := h.ae_value_le_of_energyFormH1_nonpos_of_poincare ha hc hc_bound hc_nonneg
    (le_refl (0 : ℝ)) hsub (by rwa [hposPart]) (by rwa [hposPart])
  have hvalsub : W1p.value (u - v) = W1p.value u - W1p.value v := by
    rw [← W1p.valueL_apply, ← W1p.valueL_apply u, ← W1p.valueL_apply v, map_sub]
  filter_upwards [key, Lp.coeFn_sub (W1p.value u) (W1p.value v)] with x hx hsubx
  rw [hvalsub, hsubx] at hx
  simp only [Pi.sub_apply] at hx
  linarith

/-- **Uniqueness of a weak solution with prescribed boundary values.** If `u, v ∈ H¹(Ω)` have
the same energy form against every nonnegative test function, and each dominates the other on
`∂Ω` in the `H¹` sense — both `(u - v)⁺` and `(v - u)⁺` lie in `H¹₀(Ω)` and obey a Poincaré
bound — then `u = v` almost everywhere in `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_value_of_energyFormH1_eq_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    {u v : W1p mu Omega 2}
    (huv : ∀ z : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (z : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (z : W1p mu Omega 2) =
          energyFormH1 a 0 c v (z : W1p mu Omega 2))
    (hmem : W1p.posPart ENNReal.ofNat_ne_top (u - v) ∈ w1p0Submodule mu Omega 2)
    (hP : ‖W1p.value (W1p.posPart ENNReal.ofNat_ne_top (u - v))‖ ≤
      P * ‖W1p.gradient (W1p.posPart ENNReal.ofNat_ne_top (u - v))‖)
    (hmem' : W1p.posPart ENNReal.ofNat_ne_top (v - u) ∈ w1p0Submodule mu Omega 2)
    (hP' : ‖W1p.value (W1p.posPart ENNReal.ofNat_ne_top (v - u))‖ ≤
      P * ‖W1p.gradient (W1p.posPart ENNReal.ofNat_ne_top (v - u))‖) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = W1p.value v x := by
  have hle := h.ae_value_le_value_of_energyFormH1_le_of_poincare ha hc hc_bound hc_nonneg
    (fun z hz => (huv z hz).le) hmem hP
  have hge := h.ae_value_le_value_of_energyFormH1_le_of_poincare ha hc hc_bound hc_nonneg
    (fun z hz => (huv z hz).ge) hmem' hP'
  filter_upwards [hle, hge] with x h1 h2
  exact le_antisymm h1 h2

end Domain

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam gamma : ℝ}

/-- **The weak maximum principle on a domain trapped in a slab.** If `Ω ⊆ ℝ^{n+1}` lies
between the hyperplanes `xᵢ = s` and `xᵢ = t`, a `u ∈ H¹(Ω)` satisfying
`-∂ⱼ(aⁱʲ ∂ᵢu) + c u ≤ 0` weakly, with `c ≥ 0`, is `≤ k` almost everywhere for every level
`k ≥ 0` with `(u - k)⁺ ∈ H¹₀(Ω)`. The domain need not be bounded: boundedness in one direction
is enough, and no regularity of `∂Ω` is used. -/
theorem UniformlyEllipticOn.ae_value_le_of_energyFormH1_nonpos_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ} (hst : s ≤ t)
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    {u : W1p volume Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p volume Omega 2) ≤ 0)
    (hmem : W1p.posPartAbove ENNReal.ofNat_ne_top hk u ∈ w1p0Submodule volume Omega 2) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ k :=
  h.ae_value_le_of_energyFormH1_nonpos_of_poincare ha hc hc_bound hc_nonneg hk hu hmem
    (W1p.norm_value_le_mul_norm_gradient_of_subset_slab ENNReal.ofNat_ne_top hst hslab hmem)

/-- **The weak maximum principle on a bounded domain.** For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}`, a
`u ∈ H¹(Ω)` satisfying `-∂ⱼ(aⁱʲ ∂ᵢu) + c u ≤ 0` weakly, with `c ≥ 0`, is `≤ k` almost
everywhere for every level `k ≥ 0` with `(u - k)⁺ ∈ H¹₀(Ω)`. -/
theorem UniformlyEllipticOn.ae_value_le_of_energyFormH1_nonpos_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {u : W1p volume Omega 2} {k : ℝ} (hk : 0 ≤ k)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a 0 c u (v : W1p volume Omega 2) ≤ 0)
    (hmem : W1p.posPartAbove ENNReal.ofNat_ne_top hk u ∈ w1p0Submodule volume Omega 2) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ k :=
  h.ae_value_le_of_energyFormH1_nonpos_of_poincare ha hc hc_bound hc_nonneg hk hu hmem
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball ENNReal.ofNat_ne_top hball hmem)

/-- **The comparison principle on a bounded domain.** For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}`, two
elements `u, v ∈ H¹(Ω)` with `a(u, w) ≤ a(v, w)` against every nonnegative `w ∈ H¹₀(Ω)` — a
weak subsolution and a weak supersolution of one equation, for instance — and with `u ≤ v` on
`∂Ω`, in the sense that `(u - v)⁺ ∈ H¹₀(Ω)`, satisfy `u ≤ v` almost everywhere in `Ω`. -/
theorem UniformlyEllipticOn.ae_value_le_value_of_energyFormH1_le_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {u v : W1p volume Omega 2}
    (huv : ∀ w : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (w : W1p volume Omega 2) x) →
        energyFormH1 a 0 c u (w : W1p volume Omega 2) ≤
          energyFormH1 a 0 c v (w : W1p volume Omega 2))
    (hmem : W1p.posPart ENNReal.ofNat_ne_top (u - v) ∈ w1p0Submodule volume Omega 2) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ W1p.value v x :=
  h.ae_value_le_value_of_energyFormH1_le_of_poincare ha hc hc_bound hc_nonneg huv hmem
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball ENNReal.ofNat_ne_top hball hmem)

/-- **Uniqueness of a weak solution with prescribed boundary values on a bounded domain.**
For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}`, two elements of `H¹(Ω)` with the same energy form against every
nonnegative test function and with the same boundary values, in the sense that both
`(u - v)⁺` and `(v - u)⁺` lie in `H¹₀(Ω)`, agree almost everywhere in `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_value_of_energyFormH1_eq_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {u v : W1p volume Omega 2}
    (huv : ∀ w : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (w : W1p volume Omega 2) x) →
        energyFormH1 a 0 c u (w : W1p volume Omega 2) =
          energyFormH1 a 0 c v (w : W1p volume Omega 2))
    (hmem : W1p.posPart ENNReal.ofNat_ne_top (u - v) ∈ w1p0Submodule volume Omega 2)
    (hmem' : W1p.posPart ENNReal.ofNat_ne_top (v - u) ∈ w1p0Submodule volume Omega 2) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x = W1p.value v x :=
  h.ae_value_eq_value_of_energyFormH1_eq_of_poincare ha hc hc_bound hc_nonneg huv hmem
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball ENNReal.ofNat_ne_top hball hmem) hmem'
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball ENNReal.ofNat_ne_top hball hmem')

end Euclidean

end PDE

end TauCeti
