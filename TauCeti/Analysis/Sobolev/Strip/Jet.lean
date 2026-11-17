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
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
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

Translation `f ↦ f (· + a, ·)` in the `s` direction preserves the measure of the strip and acts
on `L^p(ℝ × [0, 1], E)` as a linear isometry (`TauCeti.StripSobolev.translateL`). When `S` is
invariant under translation (`TauCeti.StripSobolev.IsTranslationInvariant`), it maps
`jetClosure S` onto itself and is a linear isometric equivalence of it
(`TauCeti.StripSobolev.translate`), so the `W^{1,2}` norm is translation invariant
(`TauCeti.StripSobolev.norm_jetLp_comp_add_right`).

## Main definitions

* `TauCeti.StripSobolev.stripMeasure`: Lebesgue measure on the strip `ℝ × [0, 1]`.
* `TauCeti.StripSobolev.jet`: the jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`.
* `TauCeti.StripSobolev.HasL2Jets`: a space of differentiable maps with square integrable jets.
* `TauCeti.StripSobolev.jetLp`: the `L²` jet of an element of such a space.
* `TauCeti.StripSobolev.jetClosure`: the closure of the `L²` jets, a Sobolev space `W^{1,2}`.
* `TauCeti.StripSobolev.translateL E p a`: translation by `a` in the `s` direction on `L^p`.
* `TauCeti.StripSobolev.IsTranslationInvariant`: a space of maps invariant under translation in
  the `s` direction.
* `TauCeti.StripSobolev.translate S a`: translation by `a` as a linear isometric equivalence of
  `jetClosure S`.

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

section Translation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Translation by `a` in the `s` direction on `L^p` functions on the strip,
`f ↦ f (· + a, ·)`. It is a linear isometry (`TauCeti.StripSobolev.norm_translateL`). -/
def translateL (a : ℝ) : Lp E p stripMeasure →L[ℝ] Lp E p stripMeasure :=
  (Lp.compMeasurePreservingₗᵢ ℝ _
    (measurePreserving_add_right_stripMeasure a)).toContinuousLinearMap

variable {E p}

/-- Translation is composition with the translation `z ↦ z + (a, 0)` of the strip. -/
theorem translateL_apply (a : ℝ) (f : Lp E p stripMeasure) :
    translateL E p a f =
      Lp.compMeasurePreserving _ (measurePreserving_add_right_stripMeasure a) f :=
  (rfl)

/-- Translation acts on representatives by composition. -/
theorem coeFn_translateL (a : ℝ) (f : Lp E p stripMeasure) :
    translateL E p a f =ᵐ[stripMeasure] fun z ↦ f (z + (a, 0)) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Translation preserves the `L^p` norm. -/
@[simp]
theorem norm_translateL (a : ℝ) (f : Lp E p stripMeasure) : ‖translateL E p a f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- Translation by `a + b` is translation by `b` followed by translation by `a`. -/
theorem translateL_add (a b : ℝ) (f : Lp E p stripMeasure) :
    translateL E p (a + b) f = translateL E p a (translateL E p b f) := by
  rw [translateL_apply, translateL_apply, translateL_apply,
    ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext z
  ext <;> simp [add_assoc]

/-- Translation by `0` is the identity. -/
@[simp]
theorem translateL_zero (f : Lp E p stripMeasure) : translateL E p 0 f = f := by
  rw [translateL_apply]
  conv_rhs => rw [← Lp.compMeasurePreserving_id_apply f]
  congr 2
  funext z
  simp

/-- Translation by `-a` undoes translation by `a`. -/
@[simp]
theorem translateL_neg_translateL (a : ℝ) (f : Lp E p stripMeasure) :
    translateL E p (-a) (translateL E p a f) = f := by
  rw [← translateL_add, neg_add_cancel, translateL_zero]

/-- Translation by `a` undoes translation by `-a`. -/
@[simp]
theorem translateL_translateL_neg (a : ℝ) (f : Lp E p stripMeasure) :
    translateL E p a (translateL E p (-a) f) = f := by
  rw [← translateL_add, add_neg_cancel, translateL_zero]

end Translation

/-- The jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`. -/
def jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V :=
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

/-! ### Spaces of sections invariant under translation -/

/-- A space `S` of maps `ξ : ℝ × ℝ → V` that is invariant under translation in the `s` direction,
`ξ ↦ ξ (· + a, ·)`. Translation then acts on `jetClosure S` as a linear isometric equivalence
(`TauCeti.StripSobolev.translate`). -/
class IsTranslationInvariant (S : Submodule ℝ (ℝ × ℝ → V)) : Prop where
  /-- The translate `ξ (· + a, ·)` of an element of `S` lies in `S`. -/
  comp_add_right_mem : ∀ ξ ∈ S, ∀ a : ℝ, (fun z ↦ ξ (z + (a, 0))) ∈ S

section Translate

variable {S : Submodule ℝ (ℝ × ℝ → V)} [HasL2Jets S] [IsTranslationInvariant S]

/-- The translate of the `L²` jet of an element of `S` is the `L²` jet of its translate. -/
theorem translateL_jetLp (a : ℝ) (ξ : S) :
    translateL (V × V × V) 2 a (jetLp S ξ) =
      jetLp S ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.2 a⟩ := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_translateL a (jetLp S ξ),
    (measurePreserving_add_right_stripMeasure a).quasiMeasurePreserving.ae_eq_comp (coeFn_jetLp ξ),
    coeFn_jetLp ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.2 a⟩] with z h₁ h₂ h₃
  rw [h₁, h₃, jet_comp_add_right]
  exact h₂

/-- Translation maps `jetClosure S` into itself. -/
theorem translateL_mem_jetClosure (a : ℝ) {f : Lp (V × V × V) 2 stripMeasure}
    (hf : f ∈ jetClosure S) : translateL (V × V × V) 2 a f ∈ jetClosure S := by
  have h : (jetClosure S : Set (Lp (V × V × V) 2 stripMeasure)) ⊆
      translateL (V × V × V) 2 a ⁻¹' jetClosure S :=
    jetClosure_subset_of_isClosed
      ((isClosed_jetClosure S).preimage (translateL (V × V × V) 2 a).continuous) <| by
      rintro _ ⟨ξ, rfl⟩
      rw [mem_preimage, translateL_jetLp]
      exact jetLp_mem_jetClosure _
  exact h hf

/-- An `L²` jet lies in `jetClosure S` exactly when its translate does: translation maps
`jetClosure S` onto itself. -/
@[simp]
theorem translateL_mem_jetClosure_iff (a : ℝ) {f : Lp (V × V × V) 2 stripMeasure} :
    translateL (V × V × V) 2 a f ∈ jetClosure S ↔ f ∈ jetClosure S := by
  refine ⟨fun h ↦ ?_, translateL_mem_jetClosure a⟩
  simpa using translateL_mem_jetClosure (-a) h

variable (S) in
/-- Translation by `a` in the `s` direction, `x ↦ x (· + a, ·)`, as a linear isometric
equivalence of `jetClosure S`. Its inverse is translation by `-a`
(`TauCeti.StripSobolev.translate_symm`). -/
def translate (a : ℝ) : jetClosure S ≃ₗᵢ[ℝ] jetClosure S :=
  ((Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_add_right_stripMeasure a)
      (measurePreserving_add_right_stripMeasure (-a))
      (EventuallyEq.of_eq (funext fun z ↦ by simp [add_assoc]))).submoduleMap
        (jetClosure S)).trans <|
    LinearIsometryEquiv.ofEq _ _ <| le_antisymm
      (Submodule.map_le_iff_le_comap.2 fun f hf ↦ by
        simpa [translateL_apply] using translateL_mem_jetClosure a hf)
      fun f hf ↦ ⟨_, translateL_mem_jetClosure (-a) hf, by
        simpa [translateL_apply] using translateL_translateL_neg a f⟩

/-- Translation on `jetClosure S` is translation of `L²` jets. -/
@[simp]
theorem coe_translate (a : ℝ) (x : jetClosure S) :
    (translate S a x : Lp (V × V × V) 2 stripMeasure) = translateL (V × V × V) 2 a x := by
  simp [translate, translateL_apply]

/-- The inverse of translation by `a` on `jetClosure S` is translation by `-a`. -/
@[simp]
theorem translate_symm (a : ℝ) : (translate S a).symm = translate S (-a) :=
  LinearIsometryEquiv.ext fun x ↦ (translate S a).symm_apply_eq.2 <| Subtype.ext <| by simp

/-- **The `W^{1,2}` norm is translation invariant**: an element of `S` and its translate in the
`s` direction have `L²` jets of the same norm. -/
theorem norm_jetLp_comp_add_right (a : ℝ) (ξ : S) :
    ‖jetLp S ⟨_, IsTranslationInvariant.comp_add_right_mem _ ξ.2 a⟩‖ = ‖jetLp S ξ‖ := by
  rw [← translateL_jetLp, norm_translateL]

end Translate

end TauCeti.StripSobolev
