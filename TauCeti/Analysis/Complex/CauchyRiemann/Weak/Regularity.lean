/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Data.ENNReal.Holder

/-!
# Interior regularity of weak solutions of the nonlinear Cauchy–Riemann equation

Let `V` be a finite-dimensional real normed space, `Ω ⊆ ℂ` open, and let `u : ℂ → V` be a weak
solution on `Ω` of the nonlinear Cauchy–Riemann equation

`∂ₛu + J(z, u) ∂ₜu = η(z, u)`

in the sense of `TauCeti.IsWeakCauchyRiemannOn p Ω J η u`: `u` is continuous, of class
`W^{1,p}_loc`, and satisfies the equation almost everywhere. Here `J(z, x)` is a field of complex
structures, `J(z, u(z))² = -1`, and `J` and `η` may depend on the domain point `z`, as for Floer's
equation and for Gromov's graph trick. This file proves the interior elliptic bootstrapping
theorem: for `2 < p < ∞`, if `J` and `η` are `C^ℓ` near the graph of `u`, then
`u ∈ W^{ℓ+1,p}_loc(Ω)` (`TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_succ`). By Morrey's embedding
`u` is then `C^ℓ` on `Ω`, for every exponent `p > 2` including `p = ∞`, and smooth when `J` and
`η` are (`TauCeti.IsWeakCauchyRiemannOn.contDiffOn`). In particular a `C¹` solution of the
classical equation for smooth data is smooth (`TauCeti.contDiffOn_of_cauchyRiemann`).

The finite exponent is needed for the Sobolev conclusion: the graph of
`z ↦ z² log log (1 / |z|)` is a `W^{1,∞}` solution for a `C¹` structure that is not `W^{2,∞}`
(`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`).

## The argument

The proof is an induction on the order. Suppose that `u ∈ W^{m+1,p}_loc` for some `m < ℓ`.
Since `p > 2` and `u` is continuous, the coefficients `z ↦ J(z, u(z))` and `z ↦ η(z, u(z))` are in
`W^{m+1,p}_loc` too, by the composition theorem
`TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ`. Then `u` is a weak solution of the *linear*
equation `∂ₛξ + A ∂ₜξ = f` with the frozen coefficients `A(z) = J(z, u(z))` and
`f(z) = η(z, u(z))` (`TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_iff_ae`), and interior
regularity for linear equations with Sobolev coefficients
(`TauCeti.IsWeakCRSolution.memWkpLoc_succ`, McDuff–Salamon Proposition B.4.9) puts `u` in
`W^{m+2,p}_loc`. The linear theory needs an inner product on the target; a finite-dimensional
normed `V` is first identified with a Euclidean space
(`ContinuousLinearEquiv.isWeakCauchyRiemannOn_iff_comp`).

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_succ`: `C^ℓ` data give `u ∈ W^{ℓ+1,p}_loc`, `p < ∞`.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn`: `C^n` data give `u` of class `C^n` on `Ω`, for every
  `n ≤ ∞` and every `p > 2`.
* `TauCeti.contDiffOn_of_cauchyRiemann`: the same for `C¹` solutions of the classical equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4: Theorem B.4.1, Remark B.4.3 and Proposition B.4.9.
-/

public section

open Complex MeasureTheory TopologicalSpace Function
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Inner product targets -/

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens ℂ} {J : ℂ → E → E →L[ℝ] E} {η : ℂ → E → E} {u : ℂ → E} {W : Set (ℂ × E)}

/-- **One step of the bootstrap** on an inner product space: a weak solution in `W^{m+1,p}_loc`
for data that are `C^{m+1}` near its graph lies in `W^{m+2,p}_loc`. -/
private theorem IsWeakCauchyRiemannOn.memWkpLoc_add_one_add_one {p : ℝ≥0} {m : ℕ}
    (h : IsWeakCauchyRiemannOn p Ω J η u) (hp : 2 < p) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ (m + 1) (uncurry J) W) (hη : ContDiffOn ℝ (m + 1) (uncurry η) W)
    (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ E)
    (hu : MemWkpLoc p Ω (m + 1) u) : MemWkpLoc p Ω (m + 1 + 1) u := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- the frozen coefficients `J(z, u(z))` and `η(z, u(z))` are as regular as `u`
  have hJu : MemWkpLoc p Ω (m + 1) (fun z => J z (u z)) :=
    hu.contDiffOn_comp_graph_succ hp h.continuousOn hW hJ huW
  have hηu : MemWkpLoc p Ω (m + 1) (fun z => η z (u z)) :=
    hu.contDiffOn_comp_graph_succ hp h.continuousOn hW hη huW
  obtain ⟨DJ, hDJ, hDJm⟩ := hJu.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω (fun z => J z (u z)) DJ 0 :=
    ⟨hDJ, hJu.memLpLoc, hDJm.memLpLoc, memLpLoc_zero⟩
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 :=
    ENNReal.inv_add_inv_lt_one_of_two_lt (by exact_mod_cast hp)
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp.le
  -- `u` solves the linear equation with the frozen coefficients
  obtain ⟨-, hup, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff_of_isOpen.1 h
  have hsol : IsWeakCRSolution p Ω (fun z => J z (u z)) DJ 0 u (fun z => η z (u z)) :=
    (hc.isWeakCRSolution_iff_ae hpp.le ENNReal.coe_ne_top ENNReal.coe_ne_top hD hup hDp
      (hηu.memLpLoc.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed)).2 (by simpa using hae)
  have hJ2 : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), J z (u z) * J z (u z) = -1 :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall hJJ)
  exact hsol.memWkpLoc_succ hc hp hJ2 hpp le_rfl hJu memWkpLoc_zero_fun hηu

/-- Interior bootstrapping on an inner product space, for a finite exponent `p > 2`. -/
private theorem IsWeakCauchyRiemannOn.memWkpLoc_succ_of_innerProductSpace {p : ℝ≥0} {ℓ : ℕ}
    (h : IsWeakCauchyRiemannOn p Ω J η u) (hp : 2 < p) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ (uncurry J) W) (hη : ContDiffOn ℝ ℓ (uncurry η) W)
    (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ E) :
    MemWkpLoc p Ω (ℓ + 1) u := by
  suffices ∀ m ≤ ℓ, MemWkpLoc p Ω (m + 1) u from this ℓ le_rfl
  intro m hm
  induction m with
  | zero => exact h.memWkpLoc_one
  | succ m ih =>
    have hmℓ : (m : WithTop ℕ∞) + 1 ≤ ℓ := by exact_mod_cast hm
    exact h.memWkpLoc_add_one_add_one hp hW (hJ.of_le hmℓ) (hη.of_le hmℓ) huW hJJ
      (ih (by omega))

end InnerProduct

/-! ### Normed targets -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V} {W : Set (ℂ × V)}

/-- **Interior elliptic bootstrapping** (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). Let
`2 < p < ∞` and let `u` be a weak solution on an open set `Ω` of
`∂ₛu + J(z, u) ∂ₜu = η(z, u)`, with values in a finite-dimensional real normed space. If `J` and
`η` are of class `C^ℓ` on an open set `W` containing the graph of `u` over `Ω`, and
`J(z, u(z))² = -1` on `Ω`, then `u ∈ W^{ℓ+1,p}_loc(Ω)`. -/
theorem IsWeakCauchyRiemannOn.memWkpLoc_succ {p : ℝ≥0∞} {ℓ : ℕ}
    (h : IsWeakCauchyRiemannOn p Ω J η u) (hp : 2 < p) (hp_top : p ≠ ⊤) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ (uncurry J) W) (hη : ContDiffOn ℝ ℓ (uncurry η) W)
    (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V) :
    MemWkpLoc p Ω (ℓ + 1) u := by
  lift p to ℝ≥0 using hp_top
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  -- read the equation in the Euclidean model `e`, over the preimage of `W` under `id × e⁻¹`
  let σ : ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ × V := Prod.map id e.symm
  have hσ : ContDiffOn ℝ ℓ σ (σ ⁻¹' W) :=
    (contDiff_id.prodMap e.symm.contDiff).contDiffOn
  have hJ' : ContDiffOn ℝ ℓ (uncurry fun z y => (e : V →L[ℝ] _).comp ((J z (e.symm y)).comp
      (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V))) (σ ⁻¹' W) :=
    ((e.arrowCongr e).contDiff.comp_contDiffOn (hJ.comp hσ (Set.mapsTo_preimage σ W))).congr
      fun ⟨z, y⟩ _ => ContinuousLinearMap.ext fun v => by simp [σ]
  have hη' : ContDiffOn ℝ ℓ (uncurry fun z y => e (η z (e.symm y))) (σ ⁻¹' W) :=
    e.contDiff.comp_contDiffOn (hη.comp hσ (Set.mapsTo_preimage σ W))
  have hJJ' (z : ℂ) (hz : z ∈ Ω) : (e : V →L[ℝ] _).comp ((J z (e.symm (e (u z)))).comp
      (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)) ∘L
        (e : V →L[ℝ] _).comp ((J z (e.symm (e (u z)))).comp
          (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)) =
        -ContinuousLinearMap.id ℝ _ := by
    have h2 (w : V) : J z (u z) (J z (u z) w) = -w := by
      simpa using DFunLike.congr_fun (hJJ z hz) w
    ext1 v
    simp [h2]
  have he := ((e.isWeakCauchyRiemannOn_iff_comp).1 h).memWkpLoc_succ_of_innerProductSpace
    (by exact_mod_cast hp)
    (hW.preimage (continuous_id.prodMap e.symm.continuous)) hJ' hη'
    (fun z hz => by simpa [σ] using huW z hz) hJJ'
  simpa using he.clm_comp (e.symm : _ →L[ℝ] V)

/-- **Interior smoothness of weak solutions.** Let `p > 2`, including `p = ∞`, and let `u` be a
weak solution on an open set `Ω` of `∂ₛu + J(z, u) ∂ₜu = η(z, u)`, with values in a
finite-dimensional real normed space. If `J` and `η` are of class `C^n`, `n ≤ ∞`, on an open set
`W` containing the graph of `u` over `Ω`, and `J(z, u(z))² = -1` on `Ω`, then `u` is of class
`C^n` on `Ω`. -/
theorem IsWeakCauchyRiemannOn.contDiffOn {p : ℝ≥0∞} {n : ℕ∞}
    (h : IsWeakCauchyRiemannOn p Ω J η u) (hp : 2 < p) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (uncurry J) W) (hη : ContDiffOn ℝ n (uncurry η) W)
    (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V) :
    ContDiffOn ℝ n u Ω := by
  refine contDiffOn_iff_forall_nat_le.2 fun m hm => ?_
  have hmn : (m : WithTop ℕ∞) ≤ n := by exact_mod_cast hm
  -- pass to a finite exponent `2 < q ≤ p`, then apply Morrey's embedding `W^{m+1,q} ⊆ Cᵐ`
  have hq : 2 < min p 3 := lt_min hp (by norm_num)
  have hq_top : min p 3 ≠ ⊤ := ((min_le_right p 3).trans_lt (by norm_num)).ne
  obtain ⟨g, hg, hug⟩ := ((h.mono_exponent (min_le_left p 3)).memWkpLoc_succ hq hq_top hW
    (hJ.of_le hmn) (hη.of_le hmn) huW hJJ).exists_contDiffOn_ae_eq hq
  refine hg.congr (Measure.eqOn_of_ae_eq hug h.continuousOn hg.continuousOn ?_)
  rw [Ω.isOpen.interior_eq]
  exact subset_closure

/-- **Smoothness of classical solutions.** Let `u` be of class `C¹` on an open set `Ω`, with
values in a finite-dimensional real normed space, and solve `∂ₛu + J(z, u) ∂ₜu = η(z, u)` at every
point of `Ω`. If `J` and `η` are of class `C^n`, `n ≤ ∞`, on an open set `W` containing the graph
of `u` over `Ω`, and `J(z, u(z))² = -1` on `Ω`, then `u` is of class `C^n` on `Ω`. -/
theorem contDiffOn_of_cauchyRiemann {n : ℕ∞} (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z)) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (uncurry J) W) (hη : ContDiffOn ℝ n (uncurry η) W)
    (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V) :
    ContDiffOn ℝ n u Ω := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  exact (isWeakCauchyRiemannOn_of_contDiffOn (p := ⊤) hu hCR).contDiffOn
    ENNReal.ofNat_ne_top.lt_top hW hJ hη huW hJJ

end TauCeti
