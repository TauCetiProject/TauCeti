/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace
import TauCeti.Analysis.PDE.Ellipticity.PosDef
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.Analysis.Sobolev.W1p.TangentialDerivative
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.Sobolev.Wkp.Leibniz

/-!
# All-order local regularity at a flat Dirichlet boundary

Let `Ω ∩ U = H ∩ U` for an open half-space `H`, allowing the empty and whole-space
degeneracies. A scalar weak solution on `Ω ∩ U` of
`-div(a ∇u) = f`, with smooth coefficients and forcing on `U` and a uniform positive
lower bound on the quadratic form of `a` on `Ω ∩ U`, is in every Sobolev order on `Ω ∩ V`
whenever `closure V` is compact and contained in `U`. The homogeneous
boundary condition is imposed by requiring every cutoff supported in `U` times the
solution to lie in `H¹₀(Ω)` when the half-space has a nonzero normal.

For each Sobolev order, an intermediate open set supplies the derivatives used in the
localized forcing. The cutoff one on `closure V` then gives the same solution there
as the global half-space problem, where tangential differentiation and the conormal
flux recover all derivatives.

The global theorem gives `H^{k+2}` regularity for `H^k` forcing and smooth uniformly
elliptic coefficients constant off a compact set. It also covers convex domains invariant
under tangential translations. The finite-order local theorem accepts `H^k` forcing on
the chart patch; the smooth-forcing theorem gives every Sobolev order on a fixed patch.

The differentiated equation, conormal argument, and cutoff localization adapt the proofs in
`Regularity/HigherOrder.lean`, `Regularity/HalfSpace.lean`, and `Regularity/FlatBoundary.lean`.

## Main results

* `UniformlyEllipticOn.exists_value_succ_succ_eq_of_isWeakSolutionDirichlet_of_mapsTo`:
  global finite-order regularity.
* `UniformlyEllipticOn.exists_value_succ_succ_eq_value_restrictL_of_mapsTo`:
  finite-order regularity with Sobolev forcing on a chart patch.
* `exists_value_eq_value_restrictL_allOrders_of_halfSpace`:
  every finite Sobolev order on a fixed patch with smooth local data.

Reference: L. C. Evans, *Partial Differential Equations*, §6.3.2, Theorem 5.
-/

public section

section NormalRecovery

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {K : Set (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ} {lam Lam : ℝ}

local notation "E" => EuclideanSpace ℝ ι
local notation "b" => EuclideanSpace.basisFun ι ℝ

private noncomputable def flux (u : W1p mu Omega 2) (a : E → Matrix ι ι ℝ) (p x : E) : ℝ :=
  matrixBilinearForm (a x) p (W1p.gradient u x)

private theorem flux_eq_sum (u : W1p mu Omega 2) (p x : E) :
    flux u a p x = ∑ j, matrixBilinearForm (a x) p (b j) *
      ⟪W1p.gradient u x, b j⟫_ℝ := by
  unfold flux
  simpa only [real_inner_comm (W1p.gradient u x)] using
    ((b).sum_apply_mul_inner (matrixBilinearForm (a x) p) (W1p.gradient u x)).symm

private theorem flux_eq_normal_add_tangential (u : W1p mu Omega 2) {e : E} (he : ‖e‖ = 1)
    (x : E) :
    flux u a e x =
      matrixBilinearForm (a x) e e * ⟪W1p.gradient u x, e⟫_ℝ +
        ∑ i, matrixBilinearForm (a x) e (b i) *
          ⟪W1p.gradient u x, (ℝ ∙ e)ᗮ.starProjection (b i)⟫_ℝ := by
  have h := (b).sum_apply_mul_inner_sub_sum_apply_mul_inner_starProjection
    (matrixBilinearForm (a x) e) e (W1p.gradient u x)
  simp only [RCLike.ofReal_real_eq_id, id_eq, he, one_pow, inv_one, one_smul,
    real_inner_comm (W1p.gradient u x)] at h
  rw [flux_eq_sum]
  exact sub_eq_iff_eq_add.mp h

private theorem exists_value_ae_eq_flux (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) {u : W1p mu Omega 2} (U : Wkp mu Omega 2 (k + 1))
    (hU : Wkp.value (k + 1) U = W1p.value u) (p : E) :
    ∃ Q : Wkp mu Omega 2 k, Wkp.value k Q =ᵐ[mu.restrict Omega] flux u a p := by
  obtain ⟨Q, hQ⟩ := Wkp.exists_value_ae_eq_sum k fun j ↦ by
    obtain ⟨D, hD⟩ := Wkp.exists_value_ae_eq_gradient_inner k U hU (b j)
    obtain ⟨M, hM⟩ := exists_value_ae_eq_mul_coefficient hK hconst hsm k p (b j) D
    exact ⟨M, hM.trans (hD.mono fun x hx ↦ congrArg (matrixBilinearForm (a x) p (b j) * ·) hx)⟩
  exact ⟨Q, hQ.mono fun x hx ↦ hx.trans (flux_eq_sum u p x).symm⟩

private theorem exists_hasWeakLineDerivOn_flux_components (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) {u : W1p mu Omega 2} (U : Wkp mu Omega 2 (k + 1))
    (hU : Wkp.value (k + 1) U = W1p.value u) (p τ : E)
    (T : Wkp mu Omega 2 (k + 1))
    (hT : HasWeakLineDerivOn mu Omega (W1p.value u) (Wkp.value (k + 1) T) τ) :
    ∀ j, ∃ Q : Wkp mu Omega 2 k, HasWeakLineDerivOn mu Omega
      (fun x ↦ matrixBilinearForm (a x) p (b j) * ⟪W1p.gradient u x, b j⟫_ℝ)
      (Wkp.value k Q) τ := by
  let C (j : ι) (x : E) := matrixBilinearForm (a x) p (b j)
  have hC (j : ι) : ContDiff ℝ ∞ (C j) :=
    contDiff_matrixBilinearForm_apply hsm contDiff_const contDiff_const
  intro j
  obtain ⟨D, hD⟩ := Wkp.exists_value_ae_eq_gradient_inner k U hU (b j)
  obtain ⟨Tj, hTj⟩ := Wkp.exists_hasWeakLineDerivOn_value k T (b j)
  have hDτ := hT.comm hTj (W1p.hasWeakLineDerivOn_inner_gradient u (b j))
  have hc : EqOn (C j) (fun _ ↦ matrixBilinearForm A p (b j)) Kᶜ :=
    fun _ hx ↦ congrArg (fun B ↦ matrixBilinearForm B p (b j)) (hconst hx)
  obtain ⟨M, hM⟩ := exists_value_ae_eq_mul_coefficient hK hconst hsm k p (b j) Tj
  obtain ⟨N, hN⟩ := Wkp.exists_value_ae_eq_mul_fderiv_of_eqOn_const k hK (hC j) hc τ D
  refine ⟨M + N, ?_⟩
  apply ((hDτ.contDiffOn_smul_of_ne_zero (hC j).contDiffOn (by simp)).congr_ae
    (Eventually.of_forall fun x ↦ smul_eq_mul _ _)).congr_ae_deriv
  filter_upwards [Wkp.value_add_ae k M N, hM, hN, hD] with x h₁ h₂ h₃ h₄
  simp only [smul_eq_mul, h₁, Pi.add_apply, h₂, h₃, h₄, C]

private theorem exists_value_ae_eq_normal_flux (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) (F : Wkp mu Omega 2 (k + 1)) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value (k + 1) F) u)
    (U : Wkp mu Omega 2 (k + 2)) (hU : Wkp.value (k + 2) U = W1p.value (u : W1p mu Omega 2))
    {e : E} (he : ‖e‖ = 1)
    (hT : ∀ τ : E, ⟪τ, e⟫_ℝ = 0 → ∃ T : Wkp mu Omega 2 (k + 2),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) T) τ) :
    ∃ Q : Wkp mu Omega 2 (k + 2), Wkp.value (k + 2) Q =ᵐ[mu.restrict Omega]
      flux (u : W1p mu Omega 2) a e := by
  let P := (ℝ ∙ e)ᗮ.starProjection
  have hP (i : ι) : ⟪P (b i), e⟫_ℝ = 0 := by
    simp [P]
  have hTang (p τ : E) (hτ : ⟪τ, e⟫_ℝ = 0) :
      ∃ Q : Wkp mu Omega 2 (k + 1),
        HasWeakLineDerivOn mu Omega (flux (u : W1p mu Omega 2) a p) (Wkp.value (k + 1) Q) τ := by
    obtain ⟨T, ht⟩ := hT τ hτ
    choose G hG using exists_hasWeakLineDerivOn_flux_components hK hconst hsm
      (k + 1) U hU p τ T ht
    refine ⟨∑ j, G j, ?_⟩
    refine ((HasWeakLineDerivOn.sum Finset.univ fun j _ ↦ hG j).congr_ae
      (Eventually.of_forall fun x ↦ (flux_eq_sum _ _ x).symm)).congr_ae_deriv ?_
    exact EventuallyEq.symm (Wkp.value_finsetSum_ae (k + 1) Finset.univ G)
  obtain ⟨q, hq⟩ := exists_value_ae_eq_flux hK hconst hsm (k + 1) U hU e
  have hqLp := (Lp.memLp (Wkp.value (k + 1) q)).ae_eq hq
  have hGcomp (i j : ι) : ∃ Q : Wkp mu Omega 2 (k + 1), HasWeakLineDerivOn mu Omega
      (fun x ↦ matrixBilinearForm (a x) (b i) (b j) * ⟪W1p.gradient (u : W1p mu Omega 2) x, b j⟫_ℝ)
      (Wkp.value (k + 1) Q) (P (b i)) := by
    obtain ⟨T, ht⟩ := hT (P (b i)) (hP i)
    exact exists_hasWeakLineDerivOn_flux_components hK hconst hsm (k + 1) U hU
      (b i) (P (b i)) T ht j
  choose G hG using hGcomp
  have hn := hasWeakLineDerivOn_sum_smul_inner_gradient (ν := e)
    (fun p q ↦ (contDiff_matrixBilinearForm_apply hsm
      (contDiff_const (c := p)) (contDiff_const (c := q))).continuous.continuousOn)
    hu.energyFormH1_ofTestFunctionₗ (fun i j ↦ by simpa only [smul_eq_mul] using hG i j)
  simp only [he, one_pow, inv_one, one_smul, smul_eq_mul, ← flux_eq_sum] at hn
  have hN : HasWeakLineDerivOn mu Omega (flux (u : W1p mu Omega 2) a e)
      (Wkp.value (k + 1) (-(F + ∑ i, ∑ j, G i j))) e := by
    apply hn.congr_ae_deriv
    filter_upwards [Wkp.value_neg_ae (k + 1) (F + ∑ i, ∑ j, G i j),
      Wkp.value_add_ae (k + 1) F (∑ i, ∑ j, G i j),
      Wkp.value_finsetSum_ae (k + 1) Finset.univ (fun i ↦ ∑ j, G i j),
      ae_all_iff.2 (fun i ↦ Wkp.value_finsetSum_ae (k + 1) Finset.univ (G i))]
      with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, Pi.neg_apply, Pi.add_apply, h₃, h₄]
  choose d hd using Wkp.exists_hasWeakLineDerivOn_of_normal_and_tangential (k + 1) he hN (hTang e)
  exact Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn (k + 1) hqLp d hd

/-- For a weak elliptic solution already in `H^{k+2}`, if every tangential first derivative
belongs to `H^{k+2}` and the forcing belongs to `H^{k+1}`, then the normal first derivative
belongs to `H^{k+2}`. The equation determines the normal derivative of the conormal flux. -/
private theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_normal_of_tangential [DecidableEq ι]
    (ha : UniformlyEllipticOn (Omega : Set E) a lam Lam) (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ) (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j))
    (k : ℕ) (F : Wkp mu Omega 2 (k + 1)) {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value (k + 1) F) u)
    (U : Wkp mu Omega 2 (k + 2)) (hU : Wkp.value (k + 2) U = W1p.value (u : W1p mu Omega 2))
    {e : E} (he : ‖e‖ = 1)
    (hT : ∀ τ : E, ⟪τ, e⟫_ℝ = 0 → ∃ T : Wkp mu Omega 2 (k + 2),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) T) τ) :
    ∃ N : Wkp mu Omega 2 (k + 2),
      HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) N) e := by
  let P := (ℝ ∙ e)ᗮ.starProjection
  have hP (i : ι) : ⟪P (b i), e⟫_ℝ = 0 := by
    simp [P]
  obtain ⟨Q, hQ⟩ := exists_value_ae_eq_normal_flux hK hconst hsm k F hu U hU he hT
  obtain ⟨T, hTeq⟩ := Wkp.exists_value_ae_eq_sum (k + 2) fun i ↦ by
    obtain ⟨Ti, hi⟩ := hT (P (b i)) (hP i)
    obtain ⟨M, hM⟩ := exists_value_ae_eq_mul_coefficient hK hconst hsm (k + 2) e (b i) Ti
    refine ⟨M, hM.trans ((hi.ae_eq (W1p.hasWeakLineDerivOn_inner_gradient (u : W1p mu Omega 2)
      (P (b i)))).mono fun x hx ↦ ?_)⟩
    exact congrArg (matrixBilinearForm (a x) e (b i) * ·) hx
  let ann (x : E) := matrixBilinearForm (a x) e e
  have hann : ContDiff ℝ ∞ ann :=
    contDiff_matrixBilinearForm_apply hsm contDiff_const contDiff_const
  have hAnn (x : E) (hx : x ∈ closure (Omega : Set E)) : lam ≤ ann x :=
    closure_minimal (fun z hz ↦ by
      simpa only [Set.mem_ofPred_eq, ann, matrixBilinearForm_self, he, one_pow, mul_one] using
        ha.lower_bound hz e)
      (isClosed_le continuous_const hann.continuous) hx
  let S : Set E := {x | 0 < ann x}
  have hS : IsOpen S := isOpen_lt continuous_const hann.continuous
  have hΩS : closure (Omega : Set E) ⊆ S := fun x hx ↦ ha.pos.trans_le (hAnn x hx)
  obtain ⟨N, hNval⟩ := Wkp.exists_value_ae_eq_mul_of_eqOn_compl_isCompact (k + 2)
    hS hΩS hK (hann.contDiffOn.inv fun x hx ↦ ne_of_gt hx)
    (c := (matrixBilinearForm A e e)⁻¹)
    (fun x hx ↦ by
      simp only [Pi.inv_apply, ann, hconst hx.2]) (Q - T)
  refine ⟨N, (W1p.hasWeakLineDerivOn_inner_gradient (u : W1p mu Omega 2) e).congr_ae_deriv ?_⟩
  filter_upwards [hNval, Wkp.value_sub (k + 2) Q T ▸ Lp.coeFn_sub (Wkp.value (k + 2) Q)
      (Wkp.value (k + 2) T), hQ, hTeq, ae_restrict_mem Omega.isOpen.measurableSet]
    with x h₁ h₂ h₃ h₄ hx
  rw [h₁, h₂, Pi.sub_apply, h₃, h₄, flux_eq_normal_add_tangential _ he]
  simp only [Pi.inv_apply]
  rw [add_sub_cancel_right, inv_mul_cancel_left₀ (ne_of_gt (hΩS (subset_closure hx)))]

/-- Global `H^{k+2}` regularity with `H^k` forcing and smooth uniformly elliptic coefficients
constant off a compact set, on a convex domain invariant under tangential translations. -/
theorem UniformlyEllipticOn.exists_value_succ_succ_eq_of_isWeakSolutionDirichlet_of_mapsTo
    [DecidableEq ι]
    {ν : E} (hν : ν ≠ 0) (hΩc : Convex ℝ (Omega : Set E))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set E) a lam Lam) (hK : IsCompact K)
    (hconst : EqOn a (fun _ ↦ A) Kᶜ)
    (hsm : ∀ i j, ContDiff ℝ ∞ (fun x ↦ a x i j)) (k : ℕ)
    {F : Wkp mu Omega 2 k} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value k F) u) :
    ∃ W : Wkp mu Omega 2 (k + 2), Wkp.value (k + 2) W = W1p.value (u : W1p mu Omega 2) := by
  induction k generalizing u with
  | zero =>
    obtain ⟨_, _, hL, -⟩ := exists_lipschitzWith_and_norm_bound_of_eqOn_const hK hconst hsm
    obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_of_mapsTo hν hΩ hL.lipschitzOnWith hu
    exact ⟨U, by
      rw [Wkp.value_succ, hU]
      exact Wkp.value_one (u : W1p mu Omega 2)⟩
  | succ k ih =>
    have hv : IsWeakSolutionDirichlet a 0 0 (Wkp.value k (Wkp.lowerOrder k F)) u := by
      rw [← Wkp.value_succ]
      exact hu
    obtain ⟨U, hU⟩ := ih hv
    let e : E := ‖ν‖⁻¹ • ν
    have he : ‖e‖ = 1 := norm_smul_inv_norm hν
    have hT (τ : E) (hτ : ⟪τ, e⟫_ℝ = 0) :
        ∃ T : Wkp mu Omega 2 (k + 2),
          HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2)) (Wkp.value (k + 2) T) τ := by
      obtain ⟨d, G, hd, hdG⟩ :=
        exists_hasWeakLineDerivOn_and_energyFormH1_eq_of_eqOn_const hK hconst hsm k F
          U hU ((isWeakSolutionDirichlet_iff _ _).1 hu) τ
      have hτν : ⟪τ, ν⟫_ℝ = 0 := by
        dsimp only [e] at hτ
        rw [real_inner_smul_right] at hτ
        exact (mul_eq_zero.1 hτ).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hν))
      have hd₁ : HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2))
          (W1p.value (Wkp.firstOrder k d)) τ := by simpa only [Wkp.value_firstOrder] using hd
      have hD (j : ι) : ∃ D : W1p mu Omega 2, HasWeakLineDerivOn mu Omega
          (W1p.value (u : W1p mu Omega 2)) (W1p.value D) (b j) := by
        obtain ⟨D, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) U (b j)
        exact ⟨Wkp.firstOrder k D, by simpa only [hU, Wkp.value_firstOrder] using hd⟩
      choose D hD using hD
      have hmem := W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn (by simp)
        hΩc (hΩ τ hτν) b u.property hD hd₁
      let d₀ : W1p0 mu Omega 2 := ⟨Wkp.firstOrder k d, hmem⟩
      have hd₀ : IsWeakSolutionDirichlet a 0 0 (Wkp.value k G) d₀ :=
        (isWeakSolutionDirichlet_iff _ _).2 hdG
      obtain ⟨T, hT⟩ := ih hd₀
      exact ⟨T, hT.symm ▸ hd₁⟩
    obtain ⟨N, hN⟩ := ha.exists_hasWeakLineDerivOn_normal_of_tangential hK hconst hsm k F
      hu U hU he hT
    exact (Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn (k + 2) _).2
      (Wkp.exists_hasWeakLineDerivOn_of_normal_and_tangential (k + 2) he hN hT)

end TauCeti.PDE

end NormalRecovery

section LocalRegularity

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Distributions Gradient InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega H U V : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c₀ : ℝ} {ν : EuclideanSpace ℝ ι}
  {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}

local notation "E" => EuclideanSpace ℝ ι

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_iff_mem_of_inter_eq (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    {x : E} (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H := by
  simpa only [← SetLike.mem_coe, mem_inter_iff, hx, and_true] using Set.ext_iff.1 hΩU x

private theorem exists_value_eq_value_restrictL_of_mapsTo_of_order
    (hν : ν ≠ 0) (hHc : Convex ℝ (H : Set E))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (k : ℕ) (F : Wkp mu (Omega ⊓ U) 2 k)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, Wkp.value k F x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    {W : Opens E} (hW : IsCompact (closure (W : Set E)))
    (hWU : closure (W : Set E) ⊆ U) (hV : IsCompact (closure (V : Set E)))
    (hVW : closure (V : Set E) ⊆ W) (Z : Wkp mu (Omega ⊓ W) 2 (k + 1))
    (hZ : Wkp.value (k + 1) Z = W1p.value (W1p.restrictL inf_le_left u)) :
    ∃ Q : Wkp mu (Omega ⊓ V) 2 (k + 2),
      Wkp.value (k + 2) Q = W1p.value (W1p.restrictL inf_le_left u) := by
  have hHU : (H : Set E) ∩ U ⊆ (Omega : Set E) ∩ U := hΩU.ge
  obtain ⟨a', L, _, M, W', hWW', -, ha', hsm', hL, -, hM, hagree', K, hK, -, hconst⟩ :=
    ha.exists_contDiff_eqOn_inter hsmooth hHU hW hWU
  have hagree : EqOn a' a (closure (W : Set E)) := fun x hx ↦ hagree' (hWW' hx)
  let D := Omega ⊓ W
  have hD : D ≤ Omega := inf_le_left
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hΩH (x : E) (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H :=
    mem_iff_mem_of_inter_eq hΩU hx
  have hDU : D ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hDH : D ≤ H := fun x hx ↦ (hΩH x (hWsub hx.2)).1 hx.1
  have hz₁ : Wkp.firstOrder k Z = W1p.restrictL hD u :=
    W1p.ext_value ((Wkp.value_firstOrder k Z).trans hZ)
  let FD := Wkp.restrictL hDU k F
  have huD (v : W1p0 mu D 2) :
      energyFormH1 a' 0 0 (Wkp.firstOrder k Z) (v : W1p mu D 2) =
        ∫ x in D, Wkp.value k FD x * W1p.value (v : W1p mu D 2) x ∂mu := by
    rw [hz₁, ← W1p.restrictL_restrictL inf_le_left hDU,
      energyFormH1_restrictL_eq_setIntegral_of_eqOn hDU
      (fun x hx ↦ hagree (subset_closure hx.2)) hu]
    exact integral_congr_ae ((Wkp.value_restrictL_ae hDU k F).mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu D 2) x) hx.symm)
  obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
    hV.exists_contDiff_cutoff_with_bounds W.isOpen hVW
  obtain ⟨d, hd⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL hWsub hu0 hψ hψc hψs
  have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ ↦ hψN x) (fun x _ ↦ hgradN x)
      (Wkp.firstOrder k Z) = (d : W1p mu D 2) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ ↦ hψN x) (fun x _ ↦ hgradN x)
      (Wkp.firstOrder k Z), hd] with x h₁ h₂
    rw [h₁, h₂, hz₁, smul_eq_mul]
  have hts : tsupport ψ ∩ H ⊆ (D : Set E) := fun x hx ↦
    ⟨(hΩH x (hWsub (hψs hx.1))).2 hx.2, hψs hx.1⟩
  obtain ⟨w, G, hw, hwv⟩ := exists_isWeakSolutionDirichlet_value_ae_eq_indicator
    hM hL hsm' hDH k FD Z huD hψ hψc hts hN _ _ (hψu ▸ d.property)
  obtain ⟨Q, hQ⟩ := ha'.exists_value_succ_succ_eq_of_isWeakSolutionDirichlet_of_mapsTo
    hν hHc hH hK hconst hsm' k hw
  have hVD : Omega ⊓ V ≤ D := fun _ hx ↦ ⟨hx.1, hVW (subset_closure hx.2)⟩
  have hVH : Omega ⊓ V ≤ H := hVD.trans hDH
  refine ⟨Wkp.restrictL hVH (k + 2) Q, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVH (k + 2) Q,
    ae_restrict_of_ae_restrict_of_subset hVH hwv,
    ae_restrict_of_ae_restrict_of_subset hVD (W1p.value_restrictL_ae hD u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h₁ h₂ h₃ h₄ hx
  have hψx : ψ x = 1 := interior_subset (hψ1 (subset_closure hx.2))
  rw [h₁, hQ, h₂, indicator_of_mem (hVD hx), hψx, one_mul, hz₁, h₃, h₄]

/-- Local `H^{k+2}` regularity for `H^k` forcing near a flat homogeneous Dirichlet boundary.
The model domain is convex and invariant under translations orthogonal to a nonzero normal;
in particular it may be a half-space or a slab. The equation and coefficient assumptions
are local to `Ω ∩ U`, and the forcing need only belong to `H^k(Ω ∩ U)`. -/
theorem UniformlyEllipticOn.exists_value_succ_succ_eq_value_restrictL_of_mapsTo
    (hν : ν ≠ 0) (hHc : Convex ℝ (H : Set E))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (k : ℕ) (F : Wkp mu (Omega ⊓ U) 2 k)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, Wkp.value k F x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∃ Q : Wkp mu (Omega ⊓ V) 2 (k + 2),
      Wkp.value (k + 2) Q = W1p.value (W1p.restrictL inf_le_left u) := by
  induction k using Nat.strong_induction_on generalizing V with
  | ind k ih =>
    obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
      exists_open_between_and_isCompact_closure hV U.isOpen hVU
    let W : Opens E := ⟨W₀, hWo⟩
    have hZ : ∃ Z : Wkp mu (Omega ⊓ W) 2 (k + 1),
        Wkp.value (k + 1) Z = W1p.value (W1p.restrictL inf_le_left u) := by
      cases k with
      | zero => exact ⟨W1p.restrictL inf_le_left u, Wkp.value_one _⟩
      | succ k =>
        exact ih k (Nat.lt_succ_self k) (Wkp.lowerOrder k F)
          (by simpa only [← Wkp.value_succ] using hu) hW hWU
    obtain ⟨Z, hZ⟩ := hZ
    exact exists_value_eq_value_restrictL_of_mapsTo_of_order hν hHc hH hΩU ha hsmooth
      k F hu hu0 hW hWU hV hVW Z hZ

private theorem exists_value_eq_value_restrictL_allOrders_of_ne_zero
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hDU : Omega ⊓ W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hΩW : (Omega : Set E) ∩ W = (H : Set E) ∩ W := by
    ext x
    simp only [mem_inter_iff]
    exact and_congr_left fun hx ↦ mem_iff_mem_of_inter_eq hΩU (hWsub hx)
  intro k
  obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact
    (mu := mu) (Omega := Omega ⊓ W) (p := 2) k U.isOpen (hf.of_le (by simp)) hW
    (fun x hx ↦ subset_closure hx.2) hWU
  have huD (v : W1p0 mu (Omega ⊓ W) 2) :
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ W) 2) =
        ∫ x in Omega ⊓ W, Wkp.value k F x * W1p.value (v : W1p mu (Omega ⊓ W) 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hDU,
      energyFormH1_restrictL_eq_setIntegral hDU hu]
    exact integral_congr_ae (hF.mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu (Omega ⊓ W) 2) x) hx.symm)
  obtain ⟨Q, hQ⟩ := (ha.mono_set hDU).exists_value_succ_succ_eq_value_restrictL_of_mapsTo
    hν (TauCeti.convex_of_halfSpace hH)
    (fun _ hτ ↦ TauCeti.mapsTo_add_smul_of_halfSpace hH hτ) hΩW
    (fun i j ↦ (hsmooth i j).mono hWsub) k F huD
    (fun ψ hψ hψc hψs ↦ hu0 ψ hψ hψc (hψs.trans hWsub)) hV hVW
  exact ⟨Wkp.toOrderL (by omega : k ≤ k + 2) Q, (Wkp.value_toOrderL _ Q).trans hQ⟩

private theorem exists_value_eq_value_restrictL_allOrders_of_interior
    (hUΩ : U ≤ Omega) (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hWΩU : W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hUΩ (hWsub hx), hWsub hx⟩
  have hWΩ : W ≤ Omega := hWΩU.trans inf_le_left
  have haW : UniformlyEllipticOn (W : Set E) a lam Lam := ha.mono_set hWΩU
  have hY : closure ((Omega ⊓ V : Opens E) : Set E) ⊆ closure (V : Set E) :=
    closure_mono inter_subset_right
  intro k
  obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := mu) (Omega := W)
    (p := 2) k U.isOpen (hf.of_le (by simp)) hW subset_closure hWU
  have huW (v : W1p0 mu W 2) :
      energyFormH1 a 0 0 (W1p.restrictL hWΩ u) (v : W1p mu W 2) =
        ∫ x in W, Wkp.value k F x * W1p.value (v : W1p mu W 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hWΩU,
      energyFormH1_restrictL_eq_setIntegral hWΩU hu]
    exact integral_congr_ae (hF.mono fun x hx ↦
      congrArg (· * W1p.value (v : W1p mu W 2) x) hx.symm)
  obtain ⟨Q, hQ⟩ := haW.exists_value_eq_value_restrictL_of_contDiffOn k
    (fun i j ↦ ((hsmooth i j).mono hWsub).of_le (by simp))
    (b := 0) (c := 0) contDiffOn_const contDiffOn_const huW
    (V := Omega ⊓ V) (hV.of_isClosed_subset isClosed_closure hY) (hY.trans hVW)
  have hk : k ≤ k + 2 := by omega
  refine ⟨Wkp.toOrderL hk Q, ?_⟩
  rw [Wkp.value_toOrderL, hQ, W1p.restrictL_restrictL]

private theorem exists_value_eq_value_restrictL_allOrders_of_uniformlyElliptic
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set E) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ v : W1p0 mu (Omega ⊓ U) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ U) 2) =
        ∫ x in Omega ⊓ U, f x * W1p.value (v : W1p mu (Omega ⊓ U) 2) x ∂mu)
    (hu0 : ν ≠ 0 → ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  by_cases hν : ν = 0
  · have hH₀ (x : E) : x ∈ H ↔ c₀ < 0 := by simpa [hν] using hH x
    have hΩH (x : E) (hx : x ∈ (U : Set E)) : x ∈ Omega ↔ x ∈ H :=
      mem_iff_mem_of_inter_eq hΩU hx
    by_cases hc : c₀ < 0
    · exact exists_value_eq_value_restrictL_allOrders_of_interior
        (fun x hx ↦ (hΩH x hx).2 ((hH₀ x).2 hc)) ha hsmooth hf hu hV hVU
    · intro k
      refine ⟨0, Lp.ext ?_⟩
      filter_upwards [ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x hx
      exact (hc ((hH₀ x).1 ((hΩH x (hVU (subset_closure hx.2))).1 hx.1))).elim
  · exact exists_value_eq_value_restrictL_allOrders_of_ne_zero
      hν hH hΩU ha hsmooth hf hu (hu0 hν) hV hVU

omit [DecidableEq ι] in
/-- A scalar weak solution with smooth coefficients and forcing has every finite Sobolev
order locally up to a flat homogeneous Dirichlet boundary.

The weak equation and the uniform positive lower bound for the coefficient field are required
only on the chart patch. The equation is tested against smooth compactly supported functions.
No upper bound on the coefficients is assumed; smoothness on `U` suffices.
A zero normal gives an interior or empty patch, for which there is no trace condition. -/
theorem exists_value_eq_value_restrictL_allOrders_of_halfSpace
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set E) ∩ U = (H : Set E) ∩ U)
    (hlam : 0 < lam) (ha : ∀ x ∈ (Omega : Set E) ∩ U, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ matrixBilinearForm (a x) v v)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hu : ∀ φ : 𝓓(Omega ⊓ U, ℝ),
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
        (W1p.ofTestFunctionₗ mu (Omega ⊓ U) 2 φ) =
          ∫ x in Omega ⊓ U, f x * φ x ∂mu)
    (hu0 : ν ≠ 0 → ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x ↦ ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set E))) (hVU : closure (V : Set E) ⊆ U) :
    ∀ k : ℕ, ∃ Q : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k Q = W1p.value (W1p.restrictL inf_le_left u) := by
  classical
  obtain ⟨W₀, hWo, hVW, hWU, hW⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  let W : Opens E := ⟨W₀, hWo⟩
  have hWsub : (W : Set E) ⊆ U := subset_closure.trans hWU
  have hWΩU : Omega ⊓ W ≤ Omega ⊓ U := fun _ hx ↦ ⟨hx.1, hWsub hx.2⟩
  have hΩW : (Omega : Set E) ∩ W = (H : Set E) ∩ W := by
    ext x
    simp only [mem_inter_iff]
    exact and_congr_left fun hx ↦ mem_iff_mem_of_inter_eq hΩU (hWsub hx)
  obtain ⟨_, haW⟩ :=
    exists_uniformlyEllipticOn_inter_of_isCompact_closure (W := W) hW hWU hlam
      ha hsmooth
  have huW (v : W1p0 mu (Omega ⊓ W) 2) :
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ W) 2) =
        ∫ x in Omega ⊓ W, f x * W1p.value (v : W1p mu (Omega ⊓ W) 2) x ∂mu := by
    rw [← W1p.restrictL_restrictL inf_le_left hWΩU]
    have hcl : closure ((Omega ⊓ W : Opens E) : Set E) ⊆ closure (W : Set E) :=
      closure_mono inter_subset_right
    have hcoeff := memLp_energyIntegrand_of_continuousOn (mu := mu) (b := 0) (c := 0)
      (hW.of_isClosed_subset isClosed_closure hcl)
      ((continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
        (hsmooth i j).continuousOn).mono (hcl.trans hWU))
      continuousOn_const continuousOn_const (Omega := Omega ⊓ W)
    obtain ⟨F, hF⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact
      (mu := mu) (Omega := Omega ⊓ W) (p := 2) 0 U.isOpen (hf.of_le (by simp))
      hW (fun x hx ↦ subset_closure hx.2) hWU
    have hfLp : MemLp f 2 (mu.restrict (Omega ⊓ W)) := (Lp.memLp (Wkp.value 0 F)).ae_eq hF
    exact forall_energyFormH1_restrictL_eq_setIntegral hWΩU hcoeff hu hfLp v
  exact exists_value_eq_value_restrictL_allOrders_of_uniformlyElliptic hH hΩW haW
    (fun i j ↦ (hsmooth i j).mono hWsub) (hf.mono hWsub) huW
    (fun hν ψ hψ hψc hψs ↦ hu0 hν ψ hψ hψc (hψs.trans hWsub)) hV hVW

end TauCeti.PDE

end LocalRegularity
