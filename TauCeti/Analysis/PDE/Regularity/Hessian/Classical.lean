/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.ContinuousRepresentative
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Classical second differentiability for Poisson's equation with Hölder data

A weak `H¹` solution of `-Δu = f` with Hölder continuous data has a `C²` representative
in the interior. No boundary condition or regularity of the domain boundary is needed.

The Hölder estimates for weak second derivatives in `Hessian.Holder` alone do not assert
classical differentiability of the solution. Here continuous representatives of these fields
first give `C¹` representatives of the first derivatives, by
`HasWeakFDerivOn.exists_contDiffOn_one_ae_eq`. Their assembly into a `C¹` weak derivative of
`u` then gives a `C²` representative. This requires no extra derivatives of the data.

The result is a regularity statement, not a quantitative Schauder estimate: no estimate of
the `C^{2,α}` norm in terms of the data and the value of `u` is asserted here.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 4.6.
-/

public section

noncomputable section

open InnerProductSpace LineDeriv MeasureTheory Metric Set TopologicalSpace
open TauCeti.MeasureTheory
open scoped ContDiff Gradient InnerProductSpace NNReal Topology

namespace TauCeti.PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- A weak solution of `-Δu = f` with Hölder data has a `C²` representative on an open
set whose positive thickening lies in a relatively compact subdomain. -/
private theorem exists_contDiffOn_two_ae_eq_on_of_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {u : W1p volume Omega 2} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega))
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {V S : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hVO : closure (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Omega)
    {K : ℝ≥0} {R : ℝ}
    (hfK : HolderOnWith K α f (thickening R (S : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hR : 0 < R)
    (hSV : thickening R (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ V) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ 2 g S ∧
      W1p.value u =ᵐ[volume.restrict S] g := by
  obtain ⟨C, -, hsecond⟩ :=
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient hα hα1 (n := n)
  have hSV' : S ≤ V := (self_subset_thickening hR _).trans hSV
  have hSO : S ≤ Omega := hSV'.trans (subset_closure.trans hVO)
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  -- Each directional derivative has a continuous weak gradient, hence a `C¹` representative.
  have hfirst : ∀ i, ∃ gi : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiffOn ℝ 1 gi S ∧ HasWeakLineDerivOn volume S (W1p.value u) gi (b i) := by
    intro i
    obtain ⟨d, hd, hG⟩ := hsecond hf hu hV hVO hfK hR hSV (b i)
    let G := preciseRepresentative volume
      (W1p.gradient d : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    have hGc : ContinuousOn G S := hG.continuousOn hα
    have hdG : (W1p.gradient d : EuclideanSpace ℝ (Fin (n + 1)) → _)
        =ᵐ[volume.restrict S] G :=
      ae_restrict_of_ae_restrict_of_subset hSV'
        (ae_eq_restrict_preciseRepresentative V.isOpen (W1p.locallyIntegrableOn_gradient d))
    have hweak : HasWeakFDerivOn volume S (W1p.value d) (fun x => innerSL ℝ (G x)) :=
      ((W1p.hasWeakFDerivOn d).mono hSV').congr_ae_deriv (hdG.fun_comp (innerSL ℝ))
    obtain ⟨gi, hgi, hdgi, -⟩ := hweak.exists_contDiffOn_one_ae_eq
      ((innerSL ℝ).continuous.comp_continuousOn hGc)
    exact ⟨gi, hgi, (hd.mono hSV').congr_ae_deriv hdgi⟩
  choose g hg hdg using hfirst
  -- Assemble the first derivatives into a `C¹` derivative field, then recover `u` itself.
  let D : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    fun x => ∑ i, g i x • innerSL ℝ (b i)
  have hD : ContDiffOn ℝ 1 D S :=
    ContDiffOn.sum fun i _ => (hg i).smul contDiffOn_const
  have hDb : ∀ i x, D x (b i) = g i x := by
    intro i x
    simp [D, b.inner_eq_ite]
  have huD : HasWeakFDerivOn volume S (W1p.value u) D :=
    b.toBasis.hasWeakFDerivOn_of_forall
      ((W1p.hasWeakFDerivOn u).locallyIntegrableOn.mono_set hSO)
      (fun i => by simpa only [OrthonormalBasis.coe_toBasis, hDb] using hdg i)
  obtain ⟨g, hg, hug, -⟩ := huD.exists_contDiffOn_succ_ae_eq (n := 1) hD
  exact ⟨g, by exact_mod_cast hg, hug⟩

/-- **Classical second differentiability for Poisson's equation with Hölder data.**
Let `0 < α < 1`. A weak `H¹(Ω)` solution of `-Δu = f`, with `f ∈ L²(Ω)` and `f` locally
`α`-Hölder on `Ω`, agrees almost everywhere with a `C²` function on `Ω`. The Hölder constants
and neighbourhoods may vary with the point. No boundary condition or boundary regularity is
assumed. This does not assert a quantitative Schauder norm estimate. -/
theorem exists_contDiffOn_two_ae_eq_of_locally_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {u : W1p volume Omega 2} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega))
    (hfK : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α f T)
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ 2 g Omega ∧
      W1p.value u =ᵐ[volume.restrict Omega] g := by
  refine exists_contDiffOn_ae_eq_of_locally Omega.isOpen fun x hx => ?_
  obtain ⟨T, hT, K, hfT⟩ := hfK x hx
  obtain ⟨r, hr, hrOT⟩ := nhds_basis_closedBall.mem_iff.1
    (Filter.inter_mem (Omega.isOpen.mem_nhds hx) hT)
  have hrO := hrOT.trans inter_subset_left
  let V : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x r, isOpen_ball⟩
  let S : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x (r / 4), isOpen_ball⟩
  have hSV : thickening (r / 4) (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ V := by
    rw [thickening_eq_biUnion_ball]
    intro y hy
    obtain ⟨z, hz, hy⟩ := mem_iUnion₂.1 hy
    have hdist := dist_triangle y z x
    have hz' := mem_ball.1 hz
    have hy' := mem_ball.1 hy
    exact mem_ball.2 (by linarith)
  have hVO : closure (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Omega :=
    closure_ball_subset_closedBall.trans hrO
  obtain ⟨g, hg, hug⟩ := exists_contDiffOn_two_ae_eq_on_of_holderOnWith hα hα1 hf hu
    ((isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall) hVO
    (hfT.mono (hSV.trans (ball_subset_closedBall.trans (hrOT.trans inter_subset_right))))
    (by positivity) hSV
  exact ⟨S, ball_mem_nhds x (by positivity), g, hg, hug⟩

end TauCeti.PDE
