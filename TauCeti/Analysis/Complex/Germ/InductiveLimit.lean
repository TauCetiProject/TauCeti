/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Algebra
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bounded
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.LocallyConvex.CompactInductiveLimit
public import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Holomorphic germs along a compact set as an inductive limit

Let `V` be a finite-dimensional complex normed space and `K ⊆ V`. The space `A[K]` of germs along
`K` of complex-valued functions holomorphic near `K` is `TauCeti.HolomorphicGermSpace K`, the
underlying vector space of the algebra `TauCeti.holomorphicGerms K`
(`TauCeti.HolomorphicGermSpace.equivHolomorphicGerms`). Every bounded holomorphic function on an
open neighbourhood `U` of `K` has a germ along `K` (`TauCeti.HolomorphicGermSpace.ofBounded`), and
`A[K]` carries the finest locally convex topology making all these maps `H^∞(U) → A[K]`
continuous. This topology is canonical: it involves no choice of neighbourhoods.

A sequence of open neighbourhoods `U n` of `K` is a *stage sequence*
(`TauCeti.IsGermStageSequence`) when each `closure (U (n + 1))` is compact and contained in `U n`,
every connected component of each `U n` meets `K`, and every open neighbourhood of `K` contains
some `U n`. Every compact set has stage sequences inside any given neighbourhood
(`TauCeti.exists_isGermStageSequence`), for instance the thickenings of `K`. Along a stage
sequence:

* the restrictions `H^∞(U n) → H^∞(U (n + 1))` are compact by Montel's theorem and the germ maps
  `H^∞(U n) → A[K]` are injective by the identity theorem;
* the topology of `A[K]` is the final locally convex topology of the countably many germ maps
  `H^∞(U n) → A[K]` (`TauCeti.IsGermStageSequence.topologicalSpace_eq`), so it does not depend on
  the stage sequence.

Continuous functionals separate the points of `A[K]`: for `x ∈ K` and `v ∈ V`, the `n`-th
derivative at `0` of `t ↦ g (x + t • v)` is a continuous linear functional
(`TauCeti.HolomorphicGermSpace.iteratedLineDeriv`), by the Cauchy estimates on each `H^∞(U)`,
and a germ all of whose jets at the points of `K` vanish is zero by Taylor expansion. In
particular `A[K]` is Hausdorff.

The theory of compact inductive limits in `TauCeti.Analysis.LocallyConvex.CompactInductiveLimit`
then applies along any stage sequence, and so for every compact `K` it gives:

* **regularity**: a bounded subset of `A[K]` is the image of a bounded subset of a single
  `H^∞(U n)` (`TauCeti.IsGermStageSequence.isVonNBounded_iff`);
* the strong dual `A[K]′_b` is the projective limit `lim_n H^∞(U n)′` of Banach dual spaces, a
  Fréchet space (`TauCeti.IsGermStageSequence.strongDualEquiv`);
* `A[K]` is the strong dual of that Fréchet space (`TauCeti.IsGermStageSequence.evalEquiv`), it is
  complete (`TauCeti.HolomorphicGermSpace.completeSpace`), and it is reflexive: canonical
  evaluation is an isomorphism onto the strong bidual
  (`TauCeti.HolomorphicGermSpace.bidualEquiv`).

## References

* G. Köthe, *Dualität in der Funktionentheorie*, J. Reine Angew. Math. **191** (1953), 30–49.
* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan **19** (1967), 366–383.
-/

public section

noncomputable section

open Filter Metric Set Topology TopologicalSpace

namespace TauCeti

open BoundedHolomorphicFunctions
open holomorphicGerms (ofFun exists_ofFun_eq ofFun_eq_of_eqOn ofFun_eq_zero_iff ofFun_add
  ofFun_smul)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The space `A[K]` of germs along `K` of complex-valued functions holomorphic near `K`. When
`V` is finite-dimensional it carries the inductive-limit topology of the bounded holomorphic
functions on the open neighbourhoods of `K` (`TauCeti.HolomorphicGermSpace.instTopologicalSpace`).
-/
@[expose] def HolomorphicGermSpace (K : Set V) : Type _ := holomorphicGerms K

namespace HolomorphicGermSpace

variable {K : Set V}

instance : AddCommGroup (HolomorphicGermSpace K) :=
  inferInstanceAs (AddCommGroup (holomorphicGerms K))

instance : Module ℂ (HolomorphicGermSpace K) :=
  inferInstanceAs (Module ℂ (holomorphicGerms K))

instance : Module ℝ (HolomorphicGermSpace K) :=
  inferInstanceAs (Module ℝ (holomorphicGerms K))

instance : IsScalarTower ℝ ℂ (HolomorphicGermSpace K) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (holomorphicGerms K))

/-- The underlying germ along `K` of an element of `A[K]`. -/
def toGerm : HolomorphicGermSpace K →ₗ[ℂ] Germ (𝓝ˢ K) ℂ :=
  (holomorphicGerms K).val.toLinearMap

theorem toGerm_injective : Function.Injective (toGerm (K := K)) :=
  Subtype.val_injective

@[simp]
theorem toGerm_inj {g g' : HolomorphicGermSpace K} : toGerm g = toGerm g' ↔ g = g' :=
  toGerm_injective.eq_iff

@[ext]
theorem ext {g g' : HolomorphicGermSpace K} (h : toGerm g = toGerm g') : g = g' :=
  toGerm_injective h

/-- The identification of `A[K]` with the underlying vector space of the algebra
`TauCeti.holomorphicGerms K`. -/
def equivHolomorphicGerms : HolomorphicGermSpace K ≃ₗ[ℂ] holomorphicGerms K :=
  LinearEquiv.refl ℂ (holomorphicGerms K)

@[simp]
theorem coe_equivHolomorphicGerms (g : HolomorphicGermSpace K) :
    (equivHolomorphicGerms g : Germ (𝓝ˢ K) ℂ) = toGerm g :=
  (rfl)

@[simp]
theorem toGerm_equivHolomorphicGerms_symm (g : holomorphicGerms K) :
    toGerm (equivHolomorphicGerms.symm g) = g :=
  (rfl)

variable [FiniteDimensional ℂ V]

/-- The germ along `K` of a bounded holomorphic function on an open neighbourhood `U` of `K`, as a
linear map. Its continuous version is `TauCeti.HolomorphicGermSpace.ofBounded`. -/
def ofBoundedₗ {U : Opens V} (h : K ⊆ U) :
    boundedHolomorphicFunctions ℂ U →ₗ[ℂ] HolomorphicGermSpace K where
  toFun f := equivHolomorphicGerms.symm <| ofFun (extend f)
    (((differentiableOn_extend f).analyticOnNhd_of_finiteDimensional U.isOpen).mono h)
  map_add' f f' := by
    rw [← map_add, ← ofFun_add]
    refine congrArg _ (ofFun_eq_of_eqOn _ _ U.isOpen h fun z hz => ?_)
    simp [extend_apply _ ⟨z, hz⟩]
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul, ← ofFun_smul]
    refine congrArg _ (ofFun_eq_of_eqOn _ _ U.isOpen h fun z hz => ?_)
    simp [extend_apply _ ⟨z, hz⟩]

/-- The inductive-limit topology on `A[K]`: the finest locally convex topology for which the germ
maps `H^∞(U) → A[K]` are continuous for all open neighbourhoods `U` of `K`. -/
instance instTopologicalSpace : TopologicalSpace (HolomorphicGermSpace K) :=
  finalLocallyConvexTopology fun U : {U : Opens V // K ⊆ U} =>
    (ofBoundedₗ U.property).restrictScalars ℝ

instance : IsTopologicalAddGroup (HolomorphicGermSpace K) :=
  inferInstanceAs (@IsTopologicalAddGroup _ (finalLocallyConvexTopology _) _)

instance : LocallyConvexSpace ℝ (HolomorphicGermSpace K) :=
  inferInstanceAs (@LocallyConvexSpace ℝ _ _ _ _ _ (finalLocallyConvexTopology _))

instance : ContinuousSMul ℂ (HolomorphicGermSpace K) :=
  FinalLocallyConvexTopology.continuousSMul
    (fun U : {U : Opens V // K ⊆ U} => (ofBoundedₗ U.property).restrictScalars ℝ)
    fun U c f => map_smul (ofBoundedₗ U.property) c f

instance : UniformSpace (HolomorphicGermSpace K) :=
  IsTopologicalAddGroup.rightUniformSpace (HolomorphicGermSpace K)

instance : IsUniformAddGroup (HolomorphicGermSpace K) :=
  isUniformAddGroup_of_addCommGroup

/-- The germ along `K` of a bounded holomorphic function on an open neighbourhood `U` of `K`. -/
def ofBounded {U : Opens V} (h : K ⊆ U) :
    boundedHolomorphicFunctions ℂ U →L[ℂ] HolomorphicGermSpace K :=
  { toLinearMap := ofBoundedₗ h
    cont := FinalLocallyConvexTopology.continuous
      (fun W : {U : Opens V // K ⊆ U} => (ofBoundedₗ W.property).restrictScalars ℝ) ⟨U, h⟩ }

@[simp]
theorem toLinearMap_ofBounded {U : Opens V} (h : K ⊆ U) :
    (ofBounded h).toLinearMap = ofBoundedₗ h :=
  (rfl)

@[simp]
theorem toGerm_ofBounded {U : Opens V} (h : K ⊆ U) (f : boundedHolomorphicFunctions ℂ U) :
    toGerm (ofBounded h f) = extend f :=
  holomorphicGerms.coe_ofFun _ _

theorem ofBounded_apply {U : Opens V} (h : K ⊆ U) (f : boundedHolomorphicFunctions ℂ U) :
    ofBounded h f = equivHolomorphicGerms.symm (ofFun (extend f)
      ((DifferentiableOn.analyticOnNhd_of_finiteDimensional (differentiableOn_extend f)
        U.isOpen).mono h)) :=
  (rfl)

section UniversalProperty

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G]

/-- **Universal property of the inductive-limit topology.** A complex-linear map from `A[K]` into a
locally convex space is continuous exactly when its composites with the germ maps
`H^∞(U) → A[K]` are continuous for all open neighbourhoods `U` of `K`. -/
theorem continuous_iff_continuous_comp_ofBounded (φ : HolomorphicGermSpace K →ₗ[ℂ] G) :
    Continuous φ ↔ ∀ (U : Opens V) (h : K ⊆ U), Continuous (φ ∘ ofBounded h) :=
  (FinalLocallyConvexTopology.continuous_iff_continuous_comp
    (fun W : {U : Opens V // K ⊆ U} => (ofBoundedₗ W.property).restrictScalars ℝ) φ).trans
    ⟨fun H U h => H ⟨U, h⟩, fun H W => H W.val W.property⟩

end UniversalProperty

/-- Restricting a bounded holomorphic function to a smaller neighbourhood of `K` does not change
its germ along `K`. -/
@[simp]
theorem ofBounded_comp_restrict {U U' : Opens V} (h' : K ⊆ U') (hU : U' ≤ U) :
    (ofBounded h').comp (restrict (E := ℂ) hU) = ofBounded (h'.trans hU) := by
  ext f : 1
  rw [ContinuousLinearMap.comp_apply, ofBounded_apply, ofBounded_apply]
  refine congrArg _ (ofFun_eq_of_eqOn _ _ U'.isOpen h' fun z hz => ?_)
  simp [extend_apply _ ⟨z, hz⟩, extend_apply _ ⟨z, hU hz⟩]

/-- **Identity theorem.** If every connected component of `U` meets `K`, a bounded holomorphic
function on `U` is determined by its germ along `K`. -/
theorem ofBounded_injective {U : Opens V} (h : K ⊆ U)
    (hU : ∀ x ∈ U, (connectedComponentIn (U : Set V) x ∩ K).Nonempty) :
    Function.Injective (ofBounded h) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  rw [ofBounded_apply, LinearEquiv.map_eq_zero_iff] at hf
  obtain ⟨W, hW, hKW, hfW⟩ := eventually_nhdsSet_iff_exists.1 ((ofFun_eq_zero_iff _).1 hf)
  refine restrict_injective (E := ℂ) (U' := U ⊓ ⟨W, hW⟩) inf_le_left
    (fun x hx => ?_) ?_
  · obtain ⟨y, hyx, hyK⟩ := hU x hx
    exact ⟨y, hyx, h hyK, hKW hyK⟩
  · rw [map_zero]
    refine Subtype.ext (BoundedContinuousFunction.ext fun z => ?_)
    rw [BoundedHolomorphicFunctions.restrict_apply, ← extend_apply]
    simpa using hfW z z.property.2

section Jet

variable {x : V}

omit [FiniteDimensional ℂ V] in
/-- If two functions agree near `K` and `x ∈ K`, their restrictions to a complex line through `x`
have the same derivatives at `x`. -/
private theorem iteratedLineDeriv_congr (hx : x ∈ K) (v : V) (n : ℕ) {f f' : V → ℂ}
    (h : f =ᶠ[𝓝ˢ K] f') :
    iteratedDeriv n (fun t : ℂ => f (x + t • v)) 0 =
      iteratedDeriv n (fun t : ℂ => f' (x + t • v)) 0 := by
  have hline : Tendsto (fun t : ℂ => x + t • v) (𝓝 0) (𝓝 x) :=
    (by fun_prop : Continuous fun t : ℂ => x + t • v).tendsto' 0 x (by simp)
  exact (((h.filter_mono (nhds_le_nhdsSet hx)).comp_tendsto hline).iteratedDeriv n).eq_of_nhds

omit [FiniteDimensional ℂ V] in
private theorem analyticAt_line {f : V → ℂ} (hf : AnalyticOnNhd ℂ f K) (hx : x ∈ K) (v : V) :
    AnalyticAt ℂ (fun t : ℂ => f (x + t • v)) 0 :=
  (hf x hx).comp_of_eq (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) (by simp)

/-- The `n`-th derivative at `0` of `t ↦ g (x + t • v)`, as a linear functional on germs. -/
private def iteratedLineDerivₗ (hx : x ∈ K) (v : V) (n : ℕ) :
    HolomorphicGermSpace K →ₗ[ℂ] ℂ where
  toFun g := Germ.liftOn (toGerm g)
    (fun f => iteratedDeriv n (fun t : ℂ => f (x + t • v)) 0)
    fun _ _ h => iteratedLineDeriv_congr hx v n h
  map_add' g g' := by
    obtain ⟨f, hf, hfg⟩ := exists_ofFun_eq (equivHolomorphicGerms g)
    obtain ⟨f', hf', hfg'⟩ := exists_ofFun_eq (equivHolomorphicGerms g')
    rw [← equivHolomorphicGerms.symm_apply_apply g, ← equivHolomorphicGerms.symm_apply_apply g',
      ← hfg, ← hfg', ← map_add, ← ofFun_add]
    simp only [toGerm_equivHolomorphicGerms_symm, holomorphicGerms.coe_ofFun]
    -- `Germ.liftOn` on the germ of a function is the defining formula applied to that function.
    change iteratedDeriv n ((fun t : ℂ => f (x + t • v)) + fun t : ℂ => f' (x + t • v)) 0 =
      iteratedDeriv n (fun t : ℂ => f (x + t • v)) 0 +
        iteratedDeriv n (fun t : ℂ => f' (x + t • v)) 0
    exact iteratedDeriv_add (analyticAt_line hf hx v).contDiffAt
      (analyticAt_line hf' hx v).contDiffAt
  map_smul' c g := by
    obtain ⟨f, hf, hfg⟩ := exists_ofFun_eq (equivHolomorphicGerms g)
    rw [← equivHolomorphicGerms.symm_apply_apply g, ← hfg, ← map_smul, ← ofFun_smul]
    simp only [toGerm_equivHolomorphicGerms_symm, holomorphicGerms.coe_ofFun]
    -- `Germ.liftOn` on the germ of a function is the defining formula applied to that function.
    change iteratedDeriv n (c • fun t : ℂ => f (x + t • v)) 0 =
      c • iteratedDeriv n (fun t : ℂ => f (x + t • v)) 0
    exact iteratedDeriv_const_smul (analyticAt_line hf hx v).contDiffAt c

omit [FiniteDimensional ℂ V] in
private theorem iteratedLineDerivₗ_ofFun (hx : x ∈ K) (v : V) (n : ℕ) {f : V → ℂ}
    (hf : AnalyticOnNhd ℂ f K) :
    iteratedLineDerivₗ hx v n (equivHolomorphicGerms.symm (ofFun f hf)) =
      iteratedDeriv n (fun t : ℂ => f (x + t • v)) 0 := by
  rw [iteratedLineDerivₗ, LinearMap.coe_mk, AddHom.coe_mk, toGerm_equivHolomorphicGerms_symm,
    holomorphicGerms.coe_ofFun]
  -- `Germ.liftOn` on the germ of a function is the defining formula applied to that function.
  rfl

/-- The **jet functional** at a point `x ∈ K` in direction `v`: the continuous linear functional
on `A[K]` sending a germ `g` to the `n`-th complex derivative at `0` of `t ↦ g (x + t • v)`. Its
composite with the germ map of `H^∞(U)` is the point jet
`TauCeti.BoundedHolomorphicFunctions.iteratedLineDeriv`, which is continuous by Cauchy's
estimate. -/
def iteratedLineDeriv (hx : x ∈ K) (v : V) (n : ℕ) : StrongDual ℂ (HolomorphicGermSpace K) where
  toLinearMap := iteratedLineDerivₗ hx v n
  cont := by
    refine (continuous_iff_continuous_comp_ofBounded _).2 fun U h => ?_
    refine (BoundedHolomorphicFunctions.iteratedLineDeriv (E := ℂ) ⟨x, h hx⟩ v n).continuous.congr
      fun f => ?_
    rw [Function.comp_apply, ofBounded_apply, iteratedLineDerivₗ_ofFun,
      BoundedHolomorphicFunctions.iteratedLineDeriv_apply]

@[simp]
theorem iteratedLineDeriv_ofFun (hx : x ∈ K) (v : V) (n : ℕ) {f : V → ℂ}
    (hf : AnalyticOnNhd ℂ f K) :
    iteratedLineDeriv hx v n (equivHolomorphicGerms.symm (ofFun f hf)) =
      iteratedDeriv n (fun t : ℂ => f (x + t • v)) 0 :=
  iteratedLineDerivₗ_ofFun hx v n hf

@[simp]
theorem iteratedLineDeriv_ofBounded (hx : x ∈ K) (v : V) (n : ℕ) {U : Opens V} (h : K ⊆ U)
    (f : boundedHolomorphicFunctions ℂ U) :
    iteratedLineDeriv hx v n (ofBounded h f) =
      iteratedDeriv n (fun t : ℂ => extend f (x + t • v)) 0 := by
  rw [ofBounded_apply, iteratedLineDeriv_ofFun]

/-- A germ along `K` all of whose jets at the points of `K` vanish is zero. -/
theorem eq_zero_of_forall_iteratedLineDeriv_eq_zero {g : HolomorphicGermSpace K}
    (h : ∀ (x : V) (hx : x ∈ K) (v : V) (n : ℕ), iteratedLineDeriv hx v n g = 0) : g = 0 := by
  obtain ⟨f, hf, hfg⟩ := exists_ofFun_eq (equivHolomorphicGerms g)
  rw [← equivHolomorphicGerms.symm_apply_apply g, ← hfg] at h ⊢
  refine (LinearEquiv.map_eq_zero_iff _).2 <|
    (ofFun_eq_zero_iff hf).2 (eventually_nhdsSet_iff_forall.2 fun x hx => ?_)
  obtain ⟨ε, hε, hfε⟩ := Metric.eventually_nhds_iff_ball.1 (hf x hx).eventually_analyticAt
  filter_upwards [ball_mem_nhds x (half_pos hε)] with w hw
  -- On the disc of radius `2`, `t ↦ f (x + t • (w - x))` is holomorphic with vanishing Taylor
  -- coefficients at `0`, so its value at `1`, which is `f w`, vanishes.
  have hφ : DifferentiableOn ℂ (fun t : ℂ => f (x + t • (w - x))) (ball 0 2) := by
    intro t ht
    refine ((hfε _ ?_).differentiableAt.comp t (by fun_prop)).differentiableWithinAt
    rw [mem_ball, dist_zero_right] at ht
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (w - x)]
  have key := Complex.taylorSeries_eq_on_ball' (z := 1) (by norm_num [mem_ball]) hφ
  have hzero (n : ℕ) : iteratedDeriv n (fun t : ℂ => f (x + t • (w - x))) 0 = 0 := by
    simpa using h x hx (w - x) n
  simpa [hzero] using key.symm

/-- Continuous linear functionals separate the points of `A[K]`. -/
instance : SeparatingDual ℂ (HolomorphicGermSpace K) :=
  ⟨fun g hg => by
    by_contra! H
    exact hg (eq_zero_of_forall_iteratedLineDeriv_eq_zero fun x hx v n => H _)⟩

instance : T2Space (HolomorphicGermSpace K) :=
  SeparatingDual.t2Space (R := ℂ)

end Jet

end HolomorphicGermSpace

open HolomorphicGermSpace

/-- A **stage sequence** for `K`: a sequence of open neighbourhoods `U n` of `K` such that each
`closure (U (n + 1))` is compact and contained in `U n`, every connected component of each `U n`
meets `K`, and every open neighbourhood of `K` contains some `U n`. Along a stage sequence, `A[K]`
is the inductive limit of the Banach spaces `H^∞(U n)` with compact injective bonding maps. -/
structure IsGermStageSequence (K : Set V) (U : ℕ → Opens V) : Prop where
  subset (n : ℕ) : K ⊆ U n
  isCompact_closure (n : ℕ) : IsCompact (closure (U (n + 1) : Set V))
  closure_subset (n : ℕ) : closure (U (n + 1) : Set V) ⊆ U n
  connectedComponentIn_inter_nonempty (n : ℕ) :
    ∀ x ∈ U n, (connectedComponentIn (U n : Set V) x ∩ K).Nonempty
  exists_subset {W : Set V} : IsOpen W → K ⊆ W → ∃ n, (U n : Set V) ⊆ W

/-- Every compact set has a stage sequence inside any open neighbourhood, namely a sequence of
thickenings. -/
theorem exists_isGermStageSequence [ProperSpace V] {K W : Set V} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ U : ℕ → Opens V, IsGermStageSequence K U ∧ (U 0 : Set V) ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_thickening_subset_open hW hKW
  have hlt (n : ℕ) : δ / ((n + 1 : ℕ) + 1 : ℝ) < δ / ((n : ℝ) + 1) :=
    div_lt_div_of_pos_left hδ (by positivity) (by push_cast; linarith)
  refine ⟨fun n => ⟨thickening (δ / ((n : ℝ) + 1)) K, isOpen_thickening⟩,
    ⟨fun n => self_subset_thickening (by positivity) K, fun n => ?_, fun n => ?_,
      fun n x hx => ?_, fun {W'} hW' hKW' => ?_⟩, by simpa using hδW⟩
  · exact hK.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening _ _)
  · exact (closure_thickening_subset_cthickening _ _).trans
      (cthickening_subset_thickening' (by positivity) (hlt n) K)
  · obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    exact ⟨y, (convex_ball y _).isPreconnected.subset_connectedComponentIn (mem_ball.2 hxy)
      (ball_subset_thickening hy _) (mem_ball_self (dist_nonneg.trans_lt hxy)), hy⟩
  · obtain ⟨ε, hε, hεW⟩ := hK.exists_thickening_subset_open hW' hKW'
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε hδ)
    refine ⟨n, (thickening_mono ?_ K).trans hεW⟩
    calc δ / ((n : ℝ) + 1) = δ * (1 / ((n : ℝ) + 1)) := by ring
      _ ≤ δ * (ε / δ) := by gcongr
      _ = ε := by field_simp

namespace IsGermStageSequence

variable {K : Set V} {U : ℕ → Opens V} (hU : IsGermStageSequence K U)
include hU

omit [NormedSpace ℂ V] in
theorem succ_le (n : ℕ) : U (n + 1) ≤ U n :=
  subset_closure.trans (hU.closure_subset n)

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- **Montel's theorem**: the bonding maps of a stage sequence are compact. -/
theorem isCompactOperator_restrict (n : ℕ) :
    IsCompactOperator (restrict (E := ℂ) (hU.succ_le n)) :=
  BoundedHolomorphicFunctions.isCompactOperator_restrict (hU.isCompact_closure n) subset_closure
    (hU.closure_subset n)

/-- The germ maps of a stage sequence are injective. -/
theorem ofBounded_injective (n : ℕ) : Function.Injective (ofBounded (hU.subset n)) :=
  HolomorphicGermSpace.ofBounded_injective _ (hU.connectedComponentIn_inter_nonempty n)

/-- Every germ along `K` is the germ of a bounded holomorphic function on some stage. -/
theorem exists_ofBounded_eq (g : HolomorphicGermSpace K) :
    ∃ n, ∃ f : boundedHolomorphicFunctions ℂ (U n), ofBounded (hU.subset n) f = g := by
  obtain ⟨f, hf, hfg⟩ := exists_ofFun_eq (equivHolomorphicGerms g)
  rw [← equivHolomorphicGerms.symm_apply_apply g, ← hfg]
  obtain ⟨n, hn⟩ := hU.exists_subset (isOpen_analyticAt ℂ f) hf
  have hcl : closure (U (n + 1) : Set V) ⊆ {z | AnalyticAt ℂ f z} :=
    (hU.closure_subset n).trans hn
  obtain ⟨C, hC⟩ := (hU.isCompact_closure n).exists_bound_of_continuousOn
    fun z hz => (hcl hz).continuousAt.continuousWithinAt
  refine ⟨n + 1, of (U (n + 1)) f
    (fun z hz => (hcl (subset_closure hz)).differentiableAt.differentiableWithinAt) C
    fun z hz => hC z (subset_closure hz), ?_⟩
  rw [ofBounded_apply]
  refine congrArg _ (ofFun_eq_of_eqOn _ _ (U (n + 1)).isOpen (hU.subset _) fun z hz => ?_)
  rw [extend_apply _ ⟨z, hz⟩]
  exact of_apply _ _ _ _ _

/-- **Independence of the stage sequence.** The topology of `A[K]` is the final locally convex
topology of the germ maps `H^∞(U n) → A[K]` along any stage sequence. -/
theorem topologicalSpace_eq :
    (instTopologicalSpace : TopologicalSpace (HolomorphicGermSpace K)) =
      finalLocallyConvexTopology fun n => (ofBoundedₗ (hU.subset n)).restrictScalars ℝ := by
  refine le_antisymm ((FinalLocallyConvexTopology.le_iff _ _).2 fun W => ?_)
    ((FinalLocallyConvexTopology.le_iff _ _).2 fun n => (ofBounded (hU.subset n)).continuous)
  obtain ⟨n, hn⟩ := hU.exists_subset W.val.isOpen W.property
  have hcomp : ⇑((ofBoundedₗ W.property).restrictScalars ℝ) =
      (ofBoundedₗ (hU.subset n)).restrictScalars ℝ ∘ restrict (E := ℂ) (U' := U n) hn := by
    ext f : 1
    exact congr($(ofBounded_comp_restrict (hU.subset n) hn) f).symm
  rw [hcomp]
  exact @Continuous.comp _ _ _ _ _ (finalLocallyConvexTopology _) _ _
    (FinalLocallyConvexTopology.continuous
      (fun n => (ofBoundedₗ (hU.subset n)).restrictScalars ℝ) n)
    (restrict (E := ℂ) hn).continuous

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G] in
/-- A complex-linear map from `A[K]` into a locally convex space is continuous exactly when its
composites with the germ maps of a stage sequence are continuous. -/
theorem continuous_iff_continuous_comp_ofBounded (φ : HolomorphicGermSpace K →ₗ[ℂ] G) :
    Continuous φ ↔ ∀ n, Continuous (φ ∘ ofBounded (hU.subset n)) := by
  refine ⟨fun h n => h.comp (ofBounded _).continuous,
    fun h => (HolomorphicGermSpace.continuous_iff_continuous_comp_ofBounded φ).2 fun W hW => ?_⟩
  obtain ⟨n, hn⟩ := hU.exists_subset W.isOpen hW
  rw [← ofBounded_comp_restrict (hU.subset n) hn, ContinuousLinearMap.coe_comp,
    ← Function.comp_assoc]
  exact (h n).comp (restrict (E := ℂ) hn).continuous

omit [FiniteDimensional ℂ V] in
/-- The bonding maps of a stage sequence are weakly compact, since they are compact. -/
theorem isWeaklyCompact_restrict (n : ℕ) :
    (restrict (E := ℂ) (hU.succ_le n)).IsWeaklyCompact :=
  (hU.isCompactOperator_restrict n).isWeaklyCompact

/-- The germ maps of a stage sequence are compatible with its bonding maps. -/
theorem ofBounded_comp_restrict_succ (n : ℕ) :
    (ofBounded (hU.subset (n + 1))).comp (restrict (E := ℂ) (hU.succ_le n)) =
      ofBounded (hU.subset n) :=
  HolomorphicGermSpace.ofBounded_comp_restrict _ _

/-- Along a stage sequence, the canonical map from `A[K]` to the strong dual of the projective
limit `lim_n H^∞(U n)′` is continuous. -/
theorem continuous_evalInductive :
    Continuous (dualProjectiveLimit.evalInductive hU.ofBounded_comp_restrict_succ
      hU.ofBounded_injective hU.exists_ofBounded_eq) :=
  dualProjectiveLimit.continuous_evalInductive_of_le_finalLocallyConvexTopology _ _ _
    hU.topologicalSpace_eq.le

/-- **Regularity of `A[K]`.** A subset of `A[K]` is bounded exactly when it is the image of a
bounded subset of a single stage `H^∞(U n)`. -/
theorem isVonNBounded_iff {A : Set (HolomorphicGermSpace K)} :
    Bornology.IsVonNBounded ℂ A ↔
      ∃ n, ∃ R : ℝ, A ⊆ ofBounded (hU.subset n) '' closedBall 0 R :=
  isVonNBounded_iff_exists_subset_image_closedBall hU.isWeaklyCompact_restrict
    hU.ofBounded_comp_restrict_succ hU.ofBounded_injective hU.exists_ofBounded_eq
    fun ψ hψ => (hU.continuous_iff_continuous_comp_ofBounded ψ).2 hψ

/-- **The strong dual of `A[K]`.** Precomposition with the germ maps of a stage sequence
identifies the strong dual of `A[K]` with the projective limit `lim_n H^∞(U n)′` of the dual
Banach spaces, a Fréchet space. -/
def strongDualEquiv :
    StrongDual ℂ (HolomorphicGermSpace K) ≃L[ℂ]
      dualProjectiveLimit fun n => restrict (E := ℂ) (hU.succ_le n) :=
  dualProjectiveLimit.strongDualEquiv hU.isWeaklyCompact_restrict
    hU.ofBounded_comp_restrict_succ hU.ofBounded_injective hU.exists_ofBounded_eq
    fun ψ hψ => (hU.continuous_iff_continuous_comp_ofBounded ψ).2 hψ

@[simp]
theorem strongDualEquiv_apply (φ : StrongDual ℂ (HolomorphicGermSpace K)) (n : ℕ) :
    (hU.strongDualEquiv φ : ∀ n, StrongDual ℂ (boundedHolomorphicFunctions ℂ (U n))) n =
      φ.comp (ofBounded (hU.subset n)) := by
  simp [strongDualEquiv]

/-- The functional on `A[K]` corresponding to a compatible family `f` takes the value `f n z` at
the germ of `z ∈ H^∞(U n)`. -/
@[simp]
theorem strongDualEquiv_symm_apply_ofBounded
    (f : dualProjectiveLimit fun n => restrict (E := ℂ) (hU.succ_le n)) {n : ℕ}
    (z : boundedHolomorphicFunctions ℂ (U n)) :
    hU.strongDualEquiv.symm f (ofBounded (hU.subset n) z) =
      (f : ∀ n, StrongDual ℂ (boundedHolomorphicFunctions ℂ (U n))) n z :=
  dualProjectiveLimit.strongDualEquiv_symm_apply_apply _ _ _ _ _ f z

/-- **`A[K]` is the strong dual of a Fréchet space.** Evaluation identifies `A[K]` with the strong
dual of the Fréchet space `lim_n H^∞(U n)′`. -/
def evalEquiv :
    HolomorphicGermSpace K ≃L[ℂ]
      StrongDual ℂ (dualProjectiveLimit fun n => restrict (E := ℂ) (hU.succ_le n)) :=
  dualProjectiveLimit.evalEquiv hU.isWeaklyCompact_restrict
    hU.ofBounded_comp_restrict_succ hU.ofBounded_injective hU.exists_ofBounded_eq
    hU.continuous_evalInductive

@[simp]
theorem evalEquiv_ofBounded_apply (n : ℕ) (f : boundedHolomorphicFunctions ℂ (U n))
    (φ : dualProjectiveLimit fun n => restrict (E := ℂ) (hU.succ_le n)) :
    hU.evalEquiv (ofBounded (hU.subset n) f) φ =
      (φ : ∀ n, StrongDual ℂ (boundedHolomorphicFunctions ℂ (U n))) n f := by
  simp [evalEquiv]

/-- The germ of `f ∈ H^∞(U n)` is recovered from evaluation at `f`. -/
@[simp]
theorem evalEquiv_symm_eval (n : ℕ) (f : boundedHolomorphicFunctions ℂ (U n)) :
    hU.evalEquiv.symm (dualProjectiveLimit.eval (fun n => restrict (E := ℂ) (hU.succ_le n)) n f) =
      ofBounded (hU.subset n) f :=
  dualProjectiveLimit.evalEquiv_symm_eval hU.isWeaklyCompact_restrict
    hU.ofBounded_comp_restrict_succ hU.ofBounded_injective hU.exists_ofBounded_eq
    hU.continuous_evalInductive n f

end IsGermStageSequence

namespace HolomorphicGermSpace

variable [FiniteDimensional ℂ V] {K : Set V}

/-- For compact `K`, the space `A[K]` is complete. -/
theorem completeSpace (hK : IsCompact K) : CompleteSpace (HolomorphicGermSpace K) := by
  have := FiniteDimensional.proper_rclike ℂ V
  obtain ⟨U, hU, -⟩ := exists_isGermStageSequence hK isOpen_univ (subset_univ K)
  exact dualProjectiveLimit.completeSpace_of_continuous_evalInductive hU.isWeaklyCompact_restrict
    hU.ofBounded_comp_restrict_succ hU.ofBounded_injective hU.exists_ofBounded_eq
    hU.continuous_evalInductive

/-- **Reflexivity of `A[K]`.** For compact `K`, canonical evaluation is an isomorphism of `A[K]`
onto its strong bidual. -/
def bidualEquiv (hK : IsCompact K) :
    HolomorphicGermSpace K ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (HolomorphicGermSpace K)) :=
  have := FiniteDimensional.proper_rclike ℂ V
  have hU := (exists_isGermStageSequence hK isOpen_univ (subset_univ K)).choose_spec.1
  dualProjectiveLimit.inductiveBidualEquiv hU.isWeaklyCompact_restrict
    hU.ofBounded_comp_restrict_succ hU.ofBounded_injective hU.exists_ofBounded_eq
    hU.continuous_evalInductive

@[simp]
theorem bidualEquiv_apply_apply (hK : IsCompact K) (g : HolomorphicGermSpace K)
    (φ : StrongDual ℂ (HolomorphicGermSpace K)) : bidualEquiv hK g φ = φ g := by
  simp [bidualEquiv]

end HolomorphicGermSpace

end TauCeti
