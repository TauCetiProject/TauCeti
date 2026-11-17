/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# `L²` jets of sections over the strip

Sections of the trivial bundle with fibre `V` over the strip `ℝ × [0, 1]` and over the cylinder
`ℝ × S¹`, whose fundamental domain is the strip, are maps `ξ : ℝ × ℝ → V`. This file collects
what their Sobolev spaces `W^{1,2}` have in common: the Lebesgue measure
`TauCeti.StripSobolev.stripMeasure` of the strip and the jet `jet ξ = (ξ, ∂s ξ, ∂t ξ)`
(`TauCeti.StripSobolev.jet`).

A space `S` of differentiable maps with square integrable jets
(`TauCeti.StripSobolev.HasL2Jets`) has the linear map `TauCeti.StripSobolev.jetLp S` into
`L²(ℝ × [0, 1], V × V × V)`, whose norm is the `W^{1,2}` norm up to a factor between `1` and
`√3` (`TauCeti.StripSobolev.sq_norm_jet_le`). The closure of its range
(`TauCeti.StripSobolev.jetClosure S`) is the completion of `S` in the `W^{1,2}` norm, realized
inside `L²` as a closed subspace. It gives the Sobolev space `TauCeti.CylinderSobolev.H1` of the
cylinder and the Sobolev space `TauCeti.StripSobolev.H1` of the strip with boundary conditions.

## Main definitions

* `TauCeti.StripSobolev.stripMeasure`: Lebesgue measure on the strip `ℝ × [0, 1]`.
* `TauCeti.StripSobolev.jet`: the jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`.
* `TauCeti.StripSobolev.HasL2Jets`: a space of differentiable maps with square integrable jets.
* `TauCeti.StripSobolev.jetLp`: the `L²` jet of an element of such a space.
* `TauCeti.StripSobolev.jetClosure`: the closure of the `L²` jets, a Sobolev space `W^{1,2}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lebesgue measure on the strip `ℝ × [0, 1]`, also the fundamental domain
of the cylinder `ℝ × S¹`. -/
abbrev stripMeasure : Measure (ℝ × ℝ) := volume.restrict (univ ×ˢ Icc 0 1)

/-- Translation by `a` in the `s` direction preserves the Lebesgue measure of the strip. -/
theorem measurePreserving_add_right_stripMeasure (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ z + (a, 0)) stripMeasure stripMeasure := by
  -- `volume` on `ℝ × ℝ` is `volume.prod volume`, whose translation invariance is an instance.
  have h : MeasurePreserving (fun z : ℝ × ℝ ↦ z + (a, 0)) volume volume :=
    measurePreserving_add_right (volume.prod volume) (a, 0)
  replace h := h.restrict_preimage
    (MeasurableSet.univ.prod (measurableSet_Icc (a := (0 : ℝ)) (b := 1)))
  have hpre : (fun z : ℝ × ℝ ↦ z + (a, 0)) ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1) =
      univ ×ˢ Icc (0 : ℝ) 1 := by
    ext z
    simp
  rwa [hpre] at h

/-- The jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`. -/
@[expose] def jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V :=
  (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))

/-- The components of the jet. -/
theorem jet_apply (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    jet ξ z = (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) :=
  (rfl)

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a `C¹` map is continuous. -/
theorem continuous_jet (hξ : ContDiff ℝ 1 ξ) : Continuous (jet ξ) := by
  unfold jet
  fun_prop

/-- The jet is additive on differentiable maps. -/
theorem jet_add (hξ : Differentiable ℝ ξ) (hη : Differentiable ℝ η) :
    jet (ξ + η) = jet ξ + jet η := by
  funext z
  simp [jet, fderiv_add (hξ z) (hη z)]

/-- The jet commutes with scalar multiplication. -/
theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) : jet (c • ξ) = c • jet ξ := by
  funext z
  simp [jet, fderiv_const_smul_field]

/-- The jet of a compactly supported map has compact support: it vanishes off the support of the
map. -/
theorem hasCompactSupport_jet (hξ : HasCompactSupport ξ) : HasCompactSupport (jet ξ) := by
  refine hξ.mono' fun z hz ↦ ?_
  by_contra h
  exact hz (by simp [jet_apply, image_eq_zero_of_notMem_tsupport h,
    fderiv_of_notMem_tsupport ℝ h])

/-- The jet of the translate of a map is the translate of its jet. -/
theorem jet_comp_add_right (ξ : ℝ × ℝ → V) (c : ℝ × ℝ) :
    jet (fun z ↦ ξ (z + c)) = fun z ↦ jet ξ (z + c) := by
  funext z
  simp [jet_apply, fderiv_comp_add_right]

/-- The squared norm of the jet is at most the pointwise `W^{1,2}` energy density. -/
theorem sq_norm_jet_le (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖jet ξ z‖ ^ 2 ≤ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  have h : ‖jet ξ z‖ ≤ √(‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) := by
    simp only [jet, Prod.norm_def, max_le_iff]
    refine ⟨?_, ?_, ?_⟩ <;> refine Real.le_sqrt_of_sq_le ?_ <;> nlinarith [sq_nonneg ‖ξ z‖,
      sq_nonneg ‖fderiv ℝ ξ z (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ z (0, 1)‖]
  calc ‖jet ξ z‖ ^ 2 ≤ (√(‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 +
        ‖ξ z‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt (by positivity)

/-! ### The `L²` jets of a space of sections and their closure -/

/-- A space `S` of maps `ξ : ℝ × ℝ → V` whose elements are differentiable with square integrable
jet on the strip. The closure of their `L²` jets (`TauCeti.StripSobolev.jetClosure`) is a
Sobolev space `W^{1,2}` of sections over the strip, such as the space
`TauCeti.CylinderSobolev.H1` of the cylinder and the space `TauCeti.StripSobolev.H1` of the strip
with boundary conditions. -/
class HasL2Jets (S : Submodule ℝ (ℝ × ℝ → V)) : Prop where
  /-- The elements of `S` are differentiable. -/
  differentiable : ∀ ξ ∈ S, Differentiable ℝ ξ
  /-- The elements of `S` have square integrable jet on the strip. -/
  memLp_jet : ∀ ξ ∈ S, MemLp (jet ξ) 2 stripMeasure

section JetLp

variable (S : Submodule ℝ (ℝ × ℝ → V)) [HasL2Jets S]

/-- The `L²` jet `(ξ, ∂s ξ, ∂t ξ)` of the elements of a space `S` of sections with square
integrable jets, as a linear map into `L²(ℝ × [0, 1], V × V × V)`. -/
def jetLp : S →ₗ[ℝ] Lp (V × V × V) 2 stripMeasure where
  toFun ξ := (HasL2Jets.memLp_jet _ ξ.2).toLp (jet (ξ : ℝ × ℝ → V))
  map_add' ξ η := by
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by
      rw [jet_add (HasL2Jets.differentiable _ ξ.2) (HasL2Jets.differentiable _ η.2)])
  map_smul' c ξ := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_smul])

/-- The closure in `L²(ℝ × [0, 1], V × V × V)` of the jets of the elements of `S`, that is, the
completion of `S` in the `W^{1,2}` norm. -/
def jetClosure : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  (LinearMap.range (jetLp S)).topologicalClosure

/-- The definition of `jetClosure`: the closure of the span of the jets of the elements of `S`. -/
theorem jetClosure_def : jetClosure S = (LinearMap.range (jetLp S)).topologicalClosure :=
  (rfl)

/-- `jetClosure S` is the closure of the set of jets of the elements of `S`. -/
theorem coe_jetClosure :
    (jetClosure S : Set (Lp (V × V × V) 2 stripMeasure)) = closure (Set.range (jetLp S)) := by
  rw [jetClosure_def, Submodule.topologicalClosure_coe, LinearMap.coe_range]

/-- `jetClosure S` is a closed subspace of `L²`. -/
theorem isClosed_jetClosure : IsClosed (jetClosure S : Set (Lp (V × V × V) 2 stripMeasure)) :=
  Submodule.isClosed_topologicalClosure _

/-- `jetClosure S` is complete: it is a closed subspace of the complete space `L²`. -/
instance [CompleteSpace V] : CompleteSpace (jetClosure S) :=
  Submodule.topologicalClosure.completeSpace _

variable {S}

/-- The `L²` jet of an element of `S` is represented by its jet. -/
theorem coeFn_jetLp (ξ : S) : jetLp S ξ =ᵐ[stripMeasure] jet (ξ : ℝ × ℝ → V) :=
  MemLp.coeFn_toLp (HasL2Jets.memLp_jet _ ξ.2)

/-- The `L²` jet of an element of `S` is the class of its jet. -/
theorem jetLp_apply (ξ : S) :
    jetLp S ξ = (HasL2Jets.memLp_jet _ ξ.2).toLp (jet (ξ : ℝ × ℝ → V)) :=
  (rfl)

/-- The norm of the `L²` jet of an element of `S` is the `L²` norm of its jet on the strip. -/
theorem norm_jetLp (ξ : S) :
    ‖jetLp S ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure).toReal := by
  rw [jetLp_apply, Lp.norm_toLp]

/-- The squared norm of the `L²` jet of an element of `S` is the integral of the squared norm of
its jet over the strip. -/
theorem sq_norm_jetLp (ξ : S) :
    ‖jetLp S ξ‖ ^ 2 = ∫ z, ‖jet (ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure := by
  rw [jetLp_apply, MemLp.norm_toLp_sq]

/-- A closed set containing the jets of all elements of `S` contains `jetClosure S`. -/
theorem jetClosure_subset_of_isClosed {s : Set (Lp (V × V × V) 2 stripMeasure)}
    (hs : IsClosed s) (h : Set.range (jetLp S) ⊆ s) :
    (jetClosure S : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ s := by
  rw [coe_jetClosure]
  exact closure_minimal h hs

/-- The jet of an element of `S` lies in `jetClosure S`. -/
theorem jetLp_mem_jetClosure (ξ : S) : jetLp S ξ ∈ jetClosure S :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ ξ)

variable (S) in
/-- The jets of the elements of `S` are dense in `jetClosure S`. -/
theorem denseRange_codRestrict_jetLp :
    DenseRange ((jetLp S).codRestrict (jetClosure S) jetLp_mem_jetClosure) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact (coe_jetClosure S).subset

end JetLp

end TauCeti.StripSobolev
