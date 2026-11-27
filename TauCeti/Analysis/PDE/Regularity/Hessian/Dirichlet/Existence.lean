/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Regularity
import TauCeti.Analysis.Calculus.IteratedGradient.Trace
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.Regularity.CurvedBoundary
import TauCeti.Analysis.PDE.WeakLaplacian
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry

/-!
# Solvability of the `W^{2,p}` Dirichlet problem

Let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, let `1 < p < ∞`, and let

`L u = tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u`

with `A` continuous up to the boundary and elliptic there, `b` bounded and measurable, and `c`
bounded, measurable and `c ≤ 0`. This file proves that the Dirichlet problem `L u = f` in `Ω`,
`u = 0` on `∂Ω`, is uniquely solvable in `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` for every `f ∈ Lᵖ(Ω)`
(`TauCeti.existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_add_inner_add_mul_eq`).
This is Gilbarg–Trudinger's Theorem 9.15 for zero boundary values. The solution is a strong
solution: `u` has weak second derivatives in `Lᵖ(Ω)` and the equation holds almost everywhere.

## The argument

* **The Laplacian in `W^{2,2}`.** An isometric copy of `Ω` in a Euclidean space carries the weak
  solution `u ∈ H¹₀` of `-Δu = -f` given by the Poincaré inequality and Lax–Milgram
  (`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`). It lies in `H²` up
  to the `C²` boundary (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`),
  and Green's identity turns the weak equation into `tr D²u = f` almost everywhere
  (`TauCeti.Wkp.forall_integral_laplacian_smul_value_eq_iff`). The trace of the Hessian is
  invariant under the isometry back to `Ω`.
* **The Laplacian in `W^{2,p}`.** For `p ≥ 2` the solution gains integrability by Lemma 9.16
  (in the `TauCeti` namespace,
  `exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq`).
  For every `p`, Lemma 9.17 bounds `Δ` below on `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`, so its range is
  closed; it contains the simple functions, which lie in `L^{max p 2}(Ω)`, and these are dense.
* **The method of continuity.** Along the segment `L_t = (1 - t) Δ + t L`, `t ∈ [0, 1]`, the
  coefficients `(1 - t) I + t A`, `t b` and `t c` satisfy the same hypotheses, so Lemma 9.17
  bounds each `L_t` below. Compactness of `[0, 1]` makes the bound uniform
  (`IsCompact.exists_forall_norm_le_mul_norm_apply`), and the method of continuity
  (`IsPreconnected.surjective_iff_of_forall_norm_le`) carries the surjectivity of `Δ` to `L`. The
  bound for `L` itself gives uniqueness.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity), Theorem 9.15 and Lemmas 9.16 and 9.17.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 4 (`H²` regularity up
  to the boundary).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace Filter Module Laplacian
open scoped ENNReal NNReal Topology Distributions

namespace TauCeti

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Omega : Opens (WithLp 2 (ℝ × E))}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `C²` boundary charts of `Ω ⊆ ℝ × E`, composed with a linear isometry `g`, are `C²` boundary
charts of the isometric copy `g Ω = g⁻¹⁻¹(Ω)`. -/
private theorem exists_affineIsometryEquiv_of_mem_frontier_preimage {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (g : WithLp 2 (ℝ × E) ≃ₗᵢ[ℝ] F)
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {y : F} (hy : y ∈ frontier (g.symm ⁻¹' (Omega : Set (WithLp 2 (ℝ × E))))) :
    ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
      e y = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 2 γ ∧
        ∀ z ∈ normalCylinder h₀ r₀, (g.symm (e.symm z) ∈ Omega ↔ γ z.snd < z.fst) := by
  have hy' : g.symm y ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))) := by
    have h := g.symm.toHomeomorph.preimage_frontier (Omega : Set (WithLp 2 (ℝ × E)))
    rw [LinearIsometryEquiv.coe_toHomeomorph] at h
    rw [← mem_preimage, h]
    exact hy
  obtain ⟨e, γ, h₀, r₀, hey, hh₀, hr₀, hγ0, hγ, hgraph⟩ := hbdry _ hy'
  refine ⟨g.symm.toAffineIsometryEquiv.trans e, γ, h₀, r₀, hey, hh₀, hr₀, hγ0, hγ,
    fun z hz => ?_⟩
  rw [← hgraph z hz]
  exact iff_of_eq (congrArg (· ∈ Omega) (g.symm.toAffineIsometryEquiv.apply_symm_apply _))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- On a bounded open set `Ω' ⊆ ℝⁿ⁺¹` with `C²` boundary, the Dirichlet problem `Δu = f`,
`u = 0` on `∂Ω'`, is solvable in `W^{2,2}(Ω') ∩ W^{1,2}_0(Ω')` for every `f ∈ L²(Ω')`: the weak
solution in `H¹₀(Ω')` lies in `H²(Ω')`, and Green's identity makes it a strong solution. -/
private theorem exists_lowerOrder_mem_w1p0Submodule_and_trace_iteratedGradient_ae_eq_of_euclidean
    {n : ℕ} {Ω' : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ' : Bornology.IsBounded (Ω' : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbdry : ∀ y ∈ frontier (Ω' : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
        e y = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 2 γ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω' ↔ γ z.snd < z.fst))
    (f : Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Ω')) :
    ∃ w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Ω' 2 2,
      lowerOrder 1 w ∈ w1p0Submodule volume Ω' 2 ∧
      ∀ᵐ y ∂volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n + 1))) (iteratedGradient 1 w y) = f y := by
  -- The weak solution `u ∈ H¹₀(Ω')` of `-Δu = -f`, which lies in `H²(Ω')`.
  obtain ⟨R, hR⟩ := hΩ'.subset_ball 0
  obtain ⟨u, hu, -⟩ := PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball hR (-f)
  obtain ⟨w, hw⟩ := PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph hΩ' hbdry
    (PDE.uniformlyEllipticOn_const_one_one _)
    (LipschitzWith.const (PDE.matrixBilinearForm
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))).lipschitzOnWith MemLp.zero MemLp.zero
    u.property ((PDE.isWeakSolutionDirichlet_iff _ _).1 hu)
  refine ⟨w, hw ▸ u.property, (forall_integral_laplacian_smul_value_eq_iff w
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp f).locallyIntegrable one_le_two))).1 fun φ => ?_⟩
  -- Green's identity: `∫ Δφ w = ∫ φ f` for every test function `φ`.
  have h := (PDE.isWeakSolutionDirichlet_one_zero_zero_iff_forall_neg_setIntegral_laplacian_mul_eq
    (-f) u).1 hu φ
  have hL : ∫ x, Δ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x • value 2 w x =
      ∫ x in Ω', Δ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x *
        W1p.value (u : W1p volume Ω' 2) x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h' =>
        hx (φ.tsupport_subset (tsupport_laplacian_subset _ h')), zero_smul], ← hw,
      value_lowerOrder_one]
    simp_rw [smul_eq_mul]
  have hR : ∫ x, (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x • f x = ∫ x in Ω', f x * φ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := (Ω' : Set (EuclideanSpace ℝ (Fin (n + 1))))) fun x hx => by
        simp [φ.zero_on_compl hx]]
    simp_rw [smul_eq_mul, mul_comm]
  have hneg : ∫ x in Ω', (-f) x * φ x = -∫ x in Ω', f x * φ x := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg f] with x hx
    rw [hx, Pi.neg_apply, neg_mul]
  rw [hL, hR]
  linarith

/-- The Dirichlet problem `Δu = f`, `u = 0` on `∂Ω`, is solvable in `W^{2,2}(Ω) ∩ W^{1,2}_0(Ω)`
for every `f ∈ L²(Ω)` on a bounded open set `Ω ⊆ ℝ × E` with `C²` boundary, by transport from an
isometric copy of `Ω` in Euclidean space. -/
private theorem exists_firstOrder_mem_w1p0Submodule_and_trace_iteratedGradient_ae_eq_two
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (f : Lp ℝ 2 ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :
    ∃ u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega 2 2,
      firstOrder 1 u ∈ w1p0Submodule volume Omega 2 ∧
      ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x) = f x := by
  -- A linear isometry `g` onto a Euclidean space, and the copy `Ω' = g Ω`.
  have hdim : finrank ℝ (WithLp 2 (ℝ × E)) = finrank ℝ E + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × E)).finrank_eq, finrank_prod, finrank_self, add_comm]
  set g : WithLp 2 (ℝ × E) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E + 1)) :=
    ((stdOrthonormalBasis ℝ (WithLp 2 (ℝ × E))).reindex (finCongr hdim)).repr
  set Ω' : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) :=
    ⟨g.symm ⁻¹' Omega, Omega.isOpen.preimage g.symm.continuous⟩
  have hΩΩ' : (Omega : Set (WithLp 2 (ℝ × E))) = g ⁻¹' Ω' := by
    ext x
    simp [Ω']
  have hg : MeasurePreserving g volume volume := g.measurePreserving
  have hg' : MeasurePreserving g.symm (volume.restrict (Ω' : Set _))
      (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    g.symm.measurePreserving.restrict_preimage Omega.isOpen.measurableSet
  have hΩ'b : Bornology.IsBounded (Ω' : Set (EuclideanSpace ℝ (Fin (finrank ℝ E + 1)))) := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hΩ
    exact isBounded_iff_forall_norm_le.2 ⟨R, fun y hy => by
      simpa using hR (g.symm y) (by simpa [Ω'] using hy)⟩
  -- The carrier of `Ω'` is `g⁻¹⁻¹(Ω)` by definition, so the charts of `Ω` transport to `Ω'`.
  obtain ⟨w, hw0, hw⟩ :=
    exists_lowerOrder_mem_w1p0Submodule_and_trace_iteratedGradient_ae_eq_of_euclidean hΩ'b
      (fun y hy => exists_affineIsometryEquiv_of_mem_frontier_preimage g hbdry hy)
      (Lp.compMeasurePreserving g.symm hg' f)
  -- Transport `w` back to `Ω` along `g`.
  refine ⟨compLinearIsometryEquiv hg hΩΩ' 2 w,
    firstOrder_compLinearIsometryEquiv_mem_w1p0Submodule hg hΩΩ' (by rwa [firstOrder_one]), ?_⟩
  have hgr : MeasurePreserving g (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))
      (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (finrank ℝ E + 1))))) := by
    rw [hΩΩ']
    exact hg.restrict_preimage Ω'.isOpen.measurableSet
  filter_upwards [iteratedGradient_compLinearIsometryEquiv_ae hg hΩΩ' 1 w,
    hgr.quasiMeasurePreserving.ae hw,
    hgr.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hg')] with x h₁ h₂ h₃
  rw [h₁, LinearIsometryEquiv.trace_iteratedGradientCongr_symm_one, h₂, h₃, Function.comp_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- The Dirichlet problem for the Laplacian in `W^{2,p}`, `2 ≤ p < ∞`: for every `f ∈ Lᵖ(Ω)` the
solution in `W^{2,2}(Ω) ∩ W^{1,2}_0(Ω)` of `Δu = f` lies in `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`, by
Lemma 9.16. -/
private theorem exists_firstOrder_mem_w1p0Submodule_and_trace_iteratedGradient_ae_eq (hp : 2 ≤ p)
    (hp_top : p ≠ ⊤) (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :
    ∃ u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2,
      firstOrder 1 u ∈ w1p0Submodule volume Omega p ∧
      ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x) = f x := by
  have : IsFiniteMeasure (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  -- The solution in `W^{2,2}(Ω)`, which gains integrability since `f ∈ Lᵖ(Ω)`.
  obtain ⟨u, hu0, hu⟩ := exists_firstOrder_mem_w1p0Submodule_and_trace_iteratedGradient_ae_eq_two
    hΩ hbdry ((Lp.memLp f).mono_exponent hp |>.toLp f)
  obtain ⟨v, hv0, -, hv⟩ :=
    exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq
      ENNReal.one_lt_two ENNReal.ofNat_ne_top hΩ hbdry (A := fun _ => ContinuousLinearMap.id ℝ _)
      (fun _ _ => continuousWithinAt_const)
      (fun _ _ => ⟨1, one_pos, fun ξ => by simp⟩)
      (b := 0) (β := 0) aestronglyMeasurable_const (ae_of_all _ fun _ => by simp)
      (c := 0) (γ := 0) aestronglyMeasurable_const (ae_of_all _ fun _ => by simp) hu0
      (f := f) (by
        filter_upwards [hu, MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp)] with x hx hfx
        simp [hx, hfx]) hp hp_top (Lp.memLp f)
  refine ⟨v, hv0, ?_⟩
  filter_upwards [hv, hu, MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp)] with x hx hux hfx
  rw [hx, hux, hfx]

/-- The a priori estimate along the segment from the Laplacian to
`L u = tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u`: if `T₀` and `T₁` realize the two operators on `W^{2,p}(Ω)`,
then for each `t ∈ [0, 1]` the operator `(1 - t) T₀ + t T₁`, which is the operator of the same
form with coefficients `(1 - t) I + t A`, `t b` and `t c`, is bounded below on
`W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` by Lemma 9.17. -/
private theorem exists_norm_le_mul_norm_lineMap_apply (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    {T₀ T₁ : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
      Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)}
    (hT₀ : ∀ u, ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      T₀ u x = LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x))
    (hT₁ : ∀ u, ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      T₁ u x = traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ, ∀ u, firstOrder 1 u ∈ w1p0Submodule volume Omega p →
      ‖u‖ ≤ C * ‖AffineMap.lineMap T₀ T₁ t u‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_eq hp
    hp_top hΩ hbdry (A := fun x => (1 - t) • ContinuousLinearMap.id ℝ _ + t • A x)
    (fun x hx => continuousWithinAt_const.add ((hcont x hx).const_smul t))
    (fun x hx => by
      obtain ⟨lam, hlam, h⟩ := hell x hx
      refine ⟨min 1 lam, lt_min one_pos hlam, fun ξ => ?_⟩
      have hm₁ : min 1 lam * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) (min_le_left _ _)
      have hm₂ : min 1 lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ :=
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (h ξ)
      simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_left hm₁ (sub_nonneg.2 ht.2),
        mul_le_mul_of_nonneg_left hm₂ ht.1])
    (b := fun x => t • b x) (β := β) (hb.const_smul t)
    (hbβ.mono fun x hx => by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      nlinarith [norm_nonneg (b x), ht.2])
    (c := fun x => t * c x) (γ := γ) (hc.const_mul t)
    (hcγ.mono fun x hx => by
      rw [abs_mul, abs_of_nonneg ht.1]
      nlinarith [abs_nonneg (c x), ht.2])
    (hc0.mono fun x hx => mul_nonpos_of_nonneg_of_nonpos ht.1 hx)
  refine ⟨C, fun u hu0 => hC u _ hu0 ?_⟩
  rw [AffineMap.lineMap_apply_module]
  filter_upwards [hT₀ u, hT₁ u, Lp.coeFn_add ((1 - t) • T₀ u) (t • T₁ u),
    Lp.coeFn_smul (1 - t) (T₀ u), Lp.coeFn_smul t (T₁ u)] with x h₀ h₁ hadd hs₀ hs₁
  simp only [add_apply, smul_apply, hadd, Pi.add_apply, hs₀, hs₁, Pi.smul_apply, h₀, h₁,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp,
    map_add, map_smul, traceCLM_apply, smul_eq_mul, real_inner_smul_left]
  ring

/-- The Laplacian is onto `Lᵖ(Ω)` from `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` once it is bounded below there.
Its range is then closed, and it contains the simple functions: they lie in `L^q(Ω)` for
`q = max p 2`, where the Laplacian is onto, and lowering the exponent of the solution from `q`
to `p` keeps its boundary values and its Hessian. -/
private theorem surjective_comp_subtypeL_of_forall_norm_le (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {T₀ : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
      Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)}
    (hT₀ : ∀ u, ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      T₀ u x = LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x))
    {M : Submodule ℝ (Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)} [CompleteSpace M]
    (hM : ∀ u, u ∈ M ↔ firstOrder 1 u ∈ w1p0Submodule volume Omega p) {C : ℝ}
    (hC : ∀ u : M, ‖u‖ ≤ C * ‖T₀.comp M.subtypeL u‖) :
    Function.Surjective (T₀.comp M.subtypeL) := by
  have : IsFiniteMeasure (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hclosed : IsClosed (range (T₀.comp M.subtypeL)) :=
    ((T₀.comp M.subtypeL).antilipschitz_of_bound (K := ⟨max C 0, le_max_right _ _⟩) fun u =>
      (hC u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))).isClosed_range
      (T₀.comp M.subtypeL).uniformContinuous
  have hsimple : (Lp.simpleFunc ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega) :
      Set (Lp ℝ p _)) ⊆ range (T₀.comp M.subtypeL) := fun g hg => by
    have hgq : MemLp g (max p 2) (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
      ((SimpleFunc.memLp_top _ _).ae_eq
        (Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨g, hg⟩)).mono_exponent le_top
    have : Fact (1 ≤ max p 2) := ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans (le_max_left _ _)⟩
    obtain ⟨u, hu0, hu⟩ := exists_firstOrder_mem_w1p0Submodule_and_trace_iteratedGradient_ae_eq
      (le_max_right p 2) (max_ne_top hp_top ENNReal.ofNat_ne_top) hΩ hbdry (hgq.toLp g)
    -- Lower the exponent from `max p 2` to `p`.
    set v := ofExponentLEL (le_max_left p 2) 2 u
    have hv0 : firstOrder 1 v ∈ w1p0Submodule volume Omega p :=
      firstOrder_mem_w1p0Submodule_of_value_ae_eq (W1p.ofExponentLE_mem_w1p0Submodule
        (le_max_left p 2) hu0) (by
          rw [W1p.coeFn_value_ofExponentLE, value_firstOrder]
          exact (value_ofExponentLEL_ae (le_max_left p 2) 2 u).symm)
    refine ⟨⟨v, (hM v).2 hv0⟩, Lp.ext ?_⟩
    filter_upwards [hT₀ v, iteratedGradient_ofExponentLEL_ae (le_max_left p 2) 1 u, hu,
      hgq.coeFn_toLp] with x h₁ h₂ h₃ h₄
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, h₁, ← h₄, ← h₃]
    exact congrArg (fun M : IteratedGradient (WithLp 2 (ℝ × E)) 1 =>
      LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (M : WithLp 2 (ℝ × E) →ₗ[ℝ] WithLp 2 (ℝ × E))) h₂
  rw [← range_eq_univ, ← hclosed.closure_eq, eq_univ_iff_forall]
  have hdense := (Lp.simpleFunc.dense (E := ℝ)
    (μ := (volume : Measure (WithLp 2 (ℝ × E))).restrict Omega) hp_top).closure_eq
  exact fun g => closure_mono hsimple (hdense ▸ mem_univ g)

/-- **The Dirichlet problem in `W^{2,p}`** (Gilbarg–Trudinger, Theorem 9.15). Let
`Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, and let `1 < p < ∞`. Let `A` be continuous
within `Ω` and elliptic at every point of `closure Ω`, let `b` be measurable and bounded, and let
`c` be measurable, bounded and `c ≤ 0` almost everywhere. Then for every `f ∈ Lᵖ(Ω)` there is
exactly one `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost
everywhere on `Ω`. -/
theorem existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_add_inner_add_mul_eq
    (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :
    ∃! u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2,
      firstOrder 1 u ∈ w1p0Submodule volume Omega p ∧
      ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x := by
  -- The operators `T₀ = Δ` and `T₁ = L` on `W^{2,p}(Ω)`.
  obtain ⟨T₀, hT₀⟩ :=
    exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul_of_continuousWithinAt (p := p) hΩ
      (A := fun _ => ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E)))
      (fun _ _ => continuousWithinAt_const) (b := 0) (β := 0) aestronglyMeasurable_const
      (ae_of_all _ fun _ => by simp) (c := 0) (γ := 0) aestronglyMeasurable_const
      (ae_of_all _ fun _ => by simp)
  obtain ⟨T₁, hT₁⟩ :=
    exists_continuousLinearMap_traceCLM_comp_add_inner_add_mul_of_continuousWithinAt (p := p) hΩ
      hcont hb hbβ hc hcγ
  have hT₀' : ∀ u, ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      T₀ u x = LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x) :=
    fun u => (hT₀ u).mono fun x hx => by simpa using hx
  -- The Banach space `M = W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` and the segment `t ↦ (1 - t) T₀ + t T₁` on it.
  set M : Submodule ℝ (Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) :=
    (w1p0Submodule volume Omega p).toSubmodule.comap (firstOrderL 1).toLinearMap
  have hM : ∀ u, u ∈ M ↔ firstOrder 1 u ∈ w1p0Submodule volume Omega p := fun u => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, firstOrderL_apply,
      ClosedSubmodule.mem_toSubmodule_iff]
  have : CompleteSpace M :=
    ((w1p0Submodule volume Omega p).isClosed.preimage (firstOrderL 1).continuous).completeSpace_coe
  set T : ℝ → M →L[ℝ] Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega) :=
    fun t => (AffineMap.lineMap T₀ T₁ t).comp M.subtypeL
  have hTc : Continuous T := AffineMap.lineMap_continuous.clm_comp continuous_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_forall_norm_le_mul_norm_apply hTc.continuousOn
    fun t ht => by
      obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_lineMap_apply hp hp_top hΩ hbdry hcont hell
        hb hbβ hc hcγ hc0 hT₀' hT₁ ht
      exact ⟨C, fun u => hC u ((hM u).1 u.property)⟩
  -- The Laplacian is onto, and by the method of continuity so is `L`.
  have hsurj₀ : Function.Surjective (T 0) := by
    simpa [T] using surjective_comp_subtypeL_of_forall_norm_le hp_top hΩ hbdry hT₀' hM
      (by simpa [T] using hC 0 (left_mem_Icc.2 zero_le_one))
  obtain ⟨u, hu⟩ := (isPreconnected_Icc.surjective_iff_of_forall_norm_le hTc.continuousOn hC
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)).1 hsurj₀ f
  have hTu : T₁ u = f := by simpa [T] using hu
  refine ⟨u, ⟨(hM u).1 u.property, ?_⟩, fun v ⟨hv0, hv⟩ => ?_⟩
  · filter_upwards [hT₁ u] with x hx
    rw [← hx, hTu]
  -- Uniqueness: `v - u ∈ M` and `T₁ (v - u) = 0`.
  have hTv : T₁ v = f := Lp.ext <| by
    filter_upwards [hT₁ v, hv] with x h₁ h₂
    rw [h₁, h₂]
  have h := hC 1 (right_mem_Icc.2 zero_le_one) ⟨v - u, M.sub_mem ((hM v).2 hv0) u.property⟩
  simp only [T, AffineMap.lineMap_apply_one, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, map_sub, hTv, hTu, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (Subtype.ext_iff.1 (norm_le_zero_iff.1 h))

end TauCeti

end
