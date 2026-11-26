/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Data.ENNReal.Holder

/-!
# Interior elliptic bootstrapping for the nonlinear Cauchy–Riemann equation

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real normed space.
Let `J : ℂ → V → (V →L[ℝ] V)` and `η : ℂ → V → V` be of class `C^ℓ` jointly in `(z, x)` on an
open set containing the graph of `u`, with `J(z, u z)² = -1`. A weak solution
`TauCeti.IsWeakCauchyRiemannOn p Ω J η u` of the nonlinear Cauchy–Riemann equation

`∂ₛu + J(z, u) ∂ₜu = η(z, u)`

with finite `p > 2` gains `ℓ` derivatives: `u ∈ W^{ℓ+1,p}_loc(Ω)`
(`TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn`). By Morrey's embedding `u` is then of class `C^ℓ`
on `Ω`, and smooth when `J` and `η` are smooth; this holds for every `p > 2`, including `p = ∞`
(`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`). This is the interior case of McDuff–Salamon,
Theorem B.4.1 and Remark B.4.3, for domain-dependent `J` and inhomogeneous terms, in the planar
coordinates to which the statement for maps from Riemann surfaces reduces.

The proof freezes the solution in the coefficients. The map `u` solves the linear equation
`∂ₛu + A ∂ₜu = f` with `A(z) = J(z, u z)` and `f(z) = η(z, u z)`. If `u ∈ W^{m,p}_loc` with
`1 ≤ m ≤ ℓ`, then `A, f ∈ W^{m,p}_loc` by the composition theorem
`TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ` (which uses `p > 2` and the continuity of `u`),
and interior regularity for real Cauchy–Riemann equations with Sobolev coefficients
(`TauCeti.IsWeakCRSolution.memWkpLoc_succ`, McDuff–Salamon, Proposition B.4.9, with `S = 0` and
`q = p`) gives `u ∈ W^{m+1,p}_loc`. The linear theory needs an inner product on the target, so a
finite-dimensional normed `V` is first identified with a Euclidean space.

The exponent `p = ∞` is excluded from the Sobolev conclusion: a `W^{1,∞}` solution for a `C¹`
structure need not be `W^{2,∞}` (`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`).

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.isWeakCRSolution`: a weak solution of the equation with frozen
  coefficients `∂ₛu + A ∂ₜu = f` is a weak solution of the real Cauchy–Riemann equation with
  coefficients `(A, DA, 0)`, to which the linear theory applies.
* `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn`: a weak solution for `C^ℓ` data and finite
  `p > 2` lies in `W^{ℓ+1,p}_loc(Ω)`.
* `TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`: a weak solution for `C^ℓ` data, `ℓ ≤ ∞`, and any
  `p > 2` is of class `C^ℓ` on `Ω`.
* `TauCeti.contDiffOn_of_isWeakCauchyRiemannOn_of_sq_eq_neg_one`: for a structure `J` depending
  only on the target, with `J(u)² = -1` along the image, a weak solution of `∂ₛu + J(u) ∂ₜu = 0` is
  of class `C^ℓ` when `J` is.
* `TauCeti.contDiffOn_of_fderiv_apply_I_eq`: a `C¹` solution of `∂ₜu = J(u) ∂ₛu` for such a
  structure is of class `C^ℓ` when `J` is.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1, Remark B.4.3 and Proposition B.4.9).
-/

public section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-! ### The linear step -/

/-- **The frozen equation as a real Cauchy–Riemann equation.** Let `p ≥ 2` be finite. If `u` solves
`∂ₛu + A ∂ₜu = f` weakly on `Ω`, with `A ∈ W^{1,p}_loc` of weak derivative `DA` and `f` locally
`Lᵖ`, then `u` is a weak solution of the real Cauchy–Riemann equation with coefficients
`(A, DA, 0)` and right side `f`, in the sense of `TauCeti.IsWeakCRSolution`. -/
theorem IsWeakCauchyRiemannOn.isWeakCRSolution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p : ℝ≥0} (hp : 2 ≤ p)
    {A : ℂ → V →L[ℝ] V} {DA : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {f u : ℂ → V}
    (h : IsWeakCauchyRiemannOn p Ω (fun z _ => A z) (fun z _ => f z) u)
    (hc : IsSobolevCRCoefficients p Ω A DA 0) (hf : MemLpLoc p Ω f) :
    IsWeakCRSolution p Ω A DA 0 u f := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  obtain ⟨-, hu, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff_of_isOpen.1 h
  have hp' : (2 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [← ENNReal.inv_two_add_inv_two]
    exact add_le_add (ENNReal.inv_le_inv.2 hp') (ENNReal.inv_le_inv.2 hp')
  exact (hc.isWeakCRSolution_iff_ae hpp ENNReal.coe_ne_top ENNReal.coe_ne_top hD hu hDp
    (hf.locallyIntegrableOn (by exact_mod_cast one_le_two.trans hp)
      Ω.isOpen.isLocallyClosed)).2 (by simpa using hae)

/-- **The linear step on an inner product space.** If `u` solves `∂ₛu + A ∂ₜu = f` weakly on `Ω`
for `p > 2`, with `A, f ∈ W^{k+1,p}_loc` and `A² = -1`, then `u ∈ W^{k+2,p}_loc`. -/
private theorem memWkpLoc_add_two_of_inner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p : ℝ≥0} (hp : 2 < p)
    {k : ℕ} {A : ℂ → V →L[ℝ] V} {f u : ℂ → V}
    (h : IsWeakCauchyRiemannOn p Ω (fun z _ => A z) (fun z _ => f z) u)
    (hA : MemWkpLoc p Ω (k + 1) A) (hA2 : ∀ᵐ z ∂volume.restrict Ω, A z * A z = -1)
    (hf : MemWkpLoc p Ω (k + 1) f) : MemWkpLoc p Ω (k + 2) u := by
  obtain ⟨DA, hDA, hDAk⟩ := hA.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω A DA 0 :=
    ⟨hDA, hA.memLpLoc, hDAk.memLpLoc, memLpLoc_zero⟩
  exact (h.isWeakCRSolution hp.le hc hf.memLpLoc).memWkpLoc_succ hc hp hA2
    (ENNReal.inv_add_inv_lt_one_of_two_lt (by exact_mod_cast hp)) le_rfl hA memWkpLoc_zero_fun hf

/-- **The linear step.** If `u` solves `∂ₛu + A ∂ₜu = f` weakly on `Ω` for `p > 2`, with
`A, f ∈ W^{k+1,p}_loc` and `A² = -1`, then `u ∈ W^{k+2,p}_loc`. The target is read in a
Euclidean model, where the linear theory applies. -/
private theorem memWkpLoc_add_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p : ℝ≥0} (hp : 2 < p) {k : ℕ}
    {A : ℂ → V →L[ℝ] V} {f u : ℂ → V}
    (h : IsWeakCauchyRiemannOn p Ω (fun z _ => A z) (fun z _ => f z) u)
    (hA : MemWkpLoc p Ω (k + 1) A) (hA2 : ∀ᵐ z ∂volume.restrict Ω, A z * A z = -1)
    (hf : MemWkpLoc p Ω (k + 1) f) : MemWkpLoc p Ω (k + 2) u := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃L[ℝ] E := toEuclidean
  let A' : ℂ → E →L[ℝ] E := fun z => (e : V →L[ℝ] E) ∘L A z ∘L (e.symm : E →L[ℝ] V)
  have hA' : MemWkpLoc p Ω (k + 1) A' := by
    simpa [A', ← ContinuousLinearEquiv.conjContinuousAlgEquiv_apply] using
      hA.clm_comp (e.conjContinuousAlgEquiv.toContinuousLinearEquiv :
        (V →L[ℝ] V) ≃L[ℝ] (E →L[ℝ] E)).toContinuousLinearMap
  have hA2' : ∀ᵐ z ∂volume.restrict Ω, A' z * A' z = -1 := by
    filter_upwards [hA2] with z hz
    simp only [A', ← ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ← map_mul, hz, map_neg,
      map_one]
  have h' := memWkpLoc_add_two_of_inner hp (h.continuousLinearEquiv_comp e) hA' hA2'
    (hf.clm_comp (e : V →L[ℝ] E))
  simpa using h'.clm_comp (e.symm : E →L[ℝ] V)

/-! ### Bootstrapping -/

section Bootstrapping

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {W : Set (ℂ × V)} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- **Interior elliptic bootstrapping** (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3, interior
case). Let `2 < p < ∞` and `ℓ : ℕ`, and let `J` and `η` be of class `C^ℓ` jointly in `(z, x)` on
an open set `W` containing the graph of `u` over `Ω`, with `J(z, u z)² = -1` for almost every
`z ∈ Ω`. A weak solution `u` of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `Ω` then lies in
`W^{ℓ+1,p}_loc(Ω)`. -/
theorem memWkpLoc_of_isWeakCauchyRiemannOn {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤) {ℓ : ℕ}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × V => J x.1 x.2) W)
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × V => η x.1 x.2) W) (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z (u z) * J z (u z) = -1)
    (h : IsWeakCauchyRiemannOn p Ω J η u) : MemWkpLoc p Ω (ℓ + 1) u := by
  lift p to ℝ≥0 using hp'
  have hp2 : 2 < p := by exact_mod_cast hp
  -- `u` solves the linear equation with the coefficients frozen along its graph.
  have hlin : IsWeakCauchyRiemannOn p Ω (fun z _ => J z (u z)) (fun z _ => η z (u z)) u :=
    (isWeakCauchyRiemannOn_congr_ae (J' := fun z _ => J z (u z)) (η' := fun z _ => η z (u z))
      (.of_forall fun _ => rfl) (.of_forall fun _ => rfl)).1 h
  suffices ∀ m ≤ ℓ, MemWkpLoc p Ω (m + 1) u from this ℓ le_rfl
  intro m hm
  induction m with
  | zero => exact h.memWkpLoc_one
  | succ m ih =>
    -- The frozen coefficients are as regular as `u`, which gains one derivative.
    have hu := ih (by omega)
    have hmℓ : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hm
    exact memWkpLoc_add_two hp2 hlin
      (hu.contDiffOn_comp_graph_succ hp2 h.continuousOn hW (hJ.of_le hmℓ) huW) hJ2
      (hu.contDiffOn_comp_graph_succ hp2 h.continuousOn hW (hη.of_le hmℓ) huW)

/-- **Interior regularity of weak solutions** (McDuff–Salamon, Remark B.4.3, interior case). Let
`p > 2`, possibly `p = ∞`, and `ℓ ≤ ∞`, and let `J` and `η` be of class `C^ℓ` jointly in `(z, x)`
on an open set `W` containing the graph of `u` over `Ω`, with `J(z, u z)² = -1` for almost every
`z ∈ Ω`. A weak solution `u` of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `Ω` is then of class `C^ℓ` on
`Ω`; in particular it is smooth when `J` and `η` are smooth. -/
theorem contDiffOn_of_isWeakCauchyRiemannOn {p : ℝ≥0∞} (hp : 2 < p) {ℓ : ℕ∞}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × V => J x.1 x.2) W)
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × V => η x.1 x.2) W) (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z (u z) * J z (u z) = -1)
    (h : IsWeakCauchyRiemannOn p Ω J η u) : ContDiffOn ℝ ℓ u Ω := by
  -- Pass to the finite exponent `q = min p 3 > 2`.
  have hq : 2 < min p 3 := lt_min hp (by norm_num)
  have hq' : min p 3 ≠ ⊤ := ((min_le_right _ _).trans_lt (by norm_num)).ne
  have hC (n : ℕ) (hn : (n : ℕ∞) ≤ ℓ) : ContDiffOn ℝ n u Ω := by
    have hnℓ : (n : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hn
    exact (memWkpLoc_of_isWeakCauchyRiemannOn hq hq' hW (hJ.of_le hnℓ) (hη.of_le hnℓ) huW hJ2
      (h.mono_exponent (min_le_left _ _))).contDiffOn_of_continuousOn hq h.continuousOn
      (Filter.EventuallyEq.refl _ _)
  induction ℓ using ENat.recTopCoe with
  | top => exact contDiffOn_infty.2 fun n => hC n le_top
  | coe n => exact_mod_cast hC n le_rfl

end Bootstrapping

/-! ### Structures depending only on the target -/

section Autonomous

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Regularity of weak pseudoholomorphic maps.** Let `p > 2` and let `J` be of class `C^ℓ` on
an open set `W ⊆ V`, as a map into `V →L[ℝ] V`. A weak solution `u` of `∂ₛu + J(u) ∂ₜu = 0` on an
open set `Ω ⊆ ℂ`, with values in `W` and such that `J(u z)` is a complex structure at every point
of `Ω`, is of class `C^ℓ` on `Ω`. -/
theorem contDiffOn_of_isWeakCauchyRiemannOn_of_sq_eq_neg_one {p : ℝ≥0∞} (hp : 2 < p)
    {J : V → V →L[ℝ] V} {Ω : Opens ℂ} {W : Set V} {u : ℂ → V} {ℓ : ℕ∞} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ J W) (huW : MapsTo u Ω W)
    (hJsq : ∀ z ∈ Ω, ∀ v, J (u z) (J (u z) v) = -v)
    (h : IsWeakCauchyRiemannOn p Ω (fun _ ↦ J) 0 u) : ContDiffOn ℝ ℓ u Ω :=
  contDiffOn_of_isWeakCauchyRiemannOn (J := fun _ ↦ J) (η := 0) hp (isOpen_univ.prod hW)
    (hJ.comp contDiff_snd.contDiffOn fun q hq ↦ (mem_prod.1 hq).2) contDiffOn_const
    (fun z hz ↦ ⟨mem_univ _, huW hz⟩)
    ((ae_restrict_iff' Ω.isOpen.measurableSet).2 <| .of_forall fun z hz ↦
      ContinuousLinearMap.ext fun v ↦ by simp [hJsq z hz])
    h

/-- **Regularity of `C¹` pseudoholomorphic maps, in the complex coordinate.** Let `J` be of class
`C^ℓ` on an open set `W ⊆ V`, as a map into `V →L[ℝ] V`. A map `u` of class `C¹` on an open set
`Ω ⊆ ℂ`, with values in `W`, such that `J(u z)` is a complex structure and
`∂ₜu = J(u) ∂ₛu` at every point of `Ω`, is of class `C^ℓ` on `Ω`. -/
theorem contDiffOn_of_fderiv_apply_I_eq {J : V → V →L[ℝ] V} {Ω : Set ℂ} {W : Set V}
    {u : ℂ → V} {ℓ : ℕ∞} (hΩ : IsOpen Ω) (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W)
    (hu : ContDiffOn ℝ 1 u Ω) (huW : MapsTo u Ω W)
    (hJsq : ∀ z ∈ Ω, ∀ v, J (u z) (J (u z) v) = -v)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) :
    ContDiffOn ℝ ℓ u Ω := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  -- With `J² = -1`, the equation `∂ₜu = J(u) ∂ₛu` is `∂ₛu + J(u) ∂ₜu = 0`.
  have hweak := isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨Ω, hΩ⟩) (p := ⊤)
    (J := fun _ ↦ J) (η := fun _ _ ↦ 0) hu fun z hz ↦ by simp [hCR z hz, hJsq z hz]
  exact contDiffOn_of_isWeakCauchyRiemannOn_of_sq_eq_neg_one (Ω := ⟨Ω, hΩ⟩) (by simp) hW hJ huW
    hJsq hweak


end Autonomous

end TauCeti
