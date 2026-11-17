/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Algebra.IsUniformGroup.Subalgebra
public import TauCeti.Topology.ContinuousMap.CompactConvergence
public import TauCeti.Topology.Sets.Opens

/-!
# Holomorphic functions with the compact-open topology

`holomorphicFunctions U` is the complex subalgebra of `C(U, ℂ)` consisting of holomorphic
functions on the open set `U`. Holomorphy can be checked on any ambient representative;
in particular, extension by zero outside `U` gives the same condition. The topology and
uniformity are inherited from continuous maps, so convergence means locally uniform
convergence. This subalgebra is closed and complete; restriction to a subset `K ⊆ U`
(`HolomorphicFunctions.restrictContinuousMap`), restriction to a smaller open set
(`HolomorphicFunctions.restrict`), and pointwise evaluation (`HolomorphicFunctions.eval`,
`HolomorphicFunctions.evalCLM`) are continuous algebra homomorphisms.

These algebras provide domains for continuous holomorphic functional calculi without
choosing a supremum norm on a possibly noncompact open set.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.

The closedness argument uses Mathlib's `TendstoLocallyUniformlyOn.differentiableOn`.
-/

public section

namespace TauCeti

open Filter Set Topology TopologicalSpace

/-- The algebra of holomorphic functions on an open subset of the complex plane, with the
topology inherited from `C(U, ℂ)`. -/
def holomorphicFunctions (U : Opens ℂ) : Subalgebra ℂ C(U, ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z}
  zero_mem' := ⟨0, differentiableOn_const _, fun _ => rfl⟩
  one_mem' := ⟨1, differentiableOn_const _, fun _ => rfl⟩
  add_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g + k, hg.add hk, fun z => by simp [hgf, hkh]⟩
  mul_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g * k, hg.mul hk, fun z => by simp [hgf, hkh]⟩
  algebraMap_mem' c := ⟨fun _ => c, differentiableOn_const _, fun _ => rfl⟩

/-- The algebra operations are continuous in the compact-open topology. -/
instance (U : Opens ℂ) : IsTopologicalRing (holomorphicFunctions U) := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact (holomorphicFunctions U).toSubring.instIsTopologicalRing

/-- Membership is equivalent to having an ambient holomorphic representative. -/
theorem mem_holomorphicFunctions_iff {U : Opens ℂ} {f : C(U, ℂ)} :
    f ∈ holomorphicFunctions U ↔
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z := Iff.rfl

/-- Holomorphy on an open set is independent of all values outside that set. -/
theorem mem_holomorphicFunctions_iff_of_eqOn {U : Opens ℂ} {f : C(U, ℂ)}
    {g : ℂ → ℂ} (hgf : ∀ z : U, g z = f z) :
    f ∈ holomorphicFunctions U ↔ DifferentiableOn ℂ g U := by
  constructor
  · rintro ⟨k, hk, hkf⟩
    exact hk.congr fun z hz => (hgf ⟨z, hz⟩).trans (hkf ⟨z, hz⟩).symm
  · exact fun hg => ⟨g, hg, hgf⟩

/-- Equivalently, the extension by zero is holomorphic on the domain. -/
theorem mem_holomorphicFunctions_iff_extend {U : Opens ℂ} {f : C(U, ℂ)} :
    f ∈ holomorphicFunctions U ↔
      DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ => 0)) U :=
  mem_holomorphicFunctions_iff_of_eqOn fun z =>
    Subtype.val_injective.extend_apply f (fun _ => 0) z

namespace HolomorphicFunctions

variable {U V W : Opens ℂ}

/-- On an empty open set `U`, `0` is the unique holomorphic function. -/
noncomputable instance instUniqueOfIsEmpty [IsEmpty U] : Unique (holomorphicFunctions U) :=
  uniqueOfSubsingleton 0

/-- Restrict an ambient holomorphic function to its open domain. -/
def of (U : Opens ℂ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    holomorphicFunctions U :=
  ⟨⟨fun z => g z, hg.continuousOn.domRestrict⟩, g, hg, fun _ => rfl⟩

@[simp]
theorem of_apply (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) (z : U) :
    (of U g hg).val z = g z := (rfl)

/-- The ambient representative obtained by extending by zero. -/
noncomputable def extend (f : holomorphicFunctions U) : ℂ → ℂ :=
  Function.extend Subtype.val f.val (fun _ => 0)

@[simp]
theorem extend_apply (f : holomorphicFunctions U) (z : U) : extend f z = f.val z :=
  Subtype.val_injective.extend_apply _ _ _

/-- The zero extension vanishes outside its original domain. -/
@[simp]
theorem extend_apply_of_not_mem (f : holomorphicFunctions U) {z : ℂ} (hz : z ∉ U) :
    extend f z = 0 := by
  rw [extend, Function.extend_apply']
  rintro ⟨w, rfl⟩
  exact hz w.property

/-- Extension by zero remains holomorphic on the original open domain. -/
theorem differentiableOn_extend (f : holomorphicFunctions U) :
    DifferentiableOn ℂ (extend f) U :=
  mem_holomorphicFunctions_iff_extend.mp f.property

/-- Extension by zero is analytic near every subset of the original open domain. -/
theorem analyticOnNhd_extend {s : Set ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U) :
    AnalyticOnNhd ℂ (extend f) s :=
  ((differentiableOn_extend f).analyticOnNhd U.isOpen).mono hs

/-- Recovering a holomorphic function from its zero extension does not change it. -/
@[simp]
theorem of_extend (f : holomorphicFunctions U) :
    of U (extend f) (differentiableOn_extend f) = f := by
  apply Subtype.ext
  ext z
  simp

/-- Restriction of `holomorphicFunctions U` to `C(K, ℂ)` for any subset `K ⊆ U`, as a `ℂ`-algebra
homomorphism. -/
noncomputable def restrictContinuousMap {K : Set ℂ} (hKU : K ⊆ U) :
    holomorphicFunctions U →ₐ[ℂ] C(K, ℂ) :=
  (ContinuousMap.compRightAlgHom ℂ ℂ (ContinuousMap.inclusion hKU)).comp
    (holomorphicFunctions U).val

/-- Evaluating `restrictContinuousMap hKU f` at `z : K` agrees with `f.val ⟨z.1, hKU z.2⟩`. -/
@[simp]
theorem restrictContinuousMap_apply {K : Set ℂ} (hKU : K ⊆ U) (f : holomorphicFunctions U)
    (z : K) : restrictContinuousMap hKU f z = f.val ⟨z.1, hKU z.2⟩ := (rfl)

/-- Evaluating `restrictContinuousMap hKU f` at `z : K` agrees with `extend f z`. -/
theorem restrictContinuousMap_apply_eq_extend {K : Set ℂ} (hKU : K ⊆ U)
    (f : holomorphicFunctions U) (z : K) : restrictContinuousMap hKU f z = extend f z :=
  (extend_apply f ⟨z.1, hKU z.2⟩).symm

/-- Restricting `restrictContinuousMap hKU f` further along `hLK : L ⊆ K` gives
`restrictContinuousMap (hLK.trans hKU) f`. -/
@[simp]
theorem restrictContinuousMap_comp_inclusion {K L : Set ℂ} (hKU : K ⊆ U) (hLK : L ⊆ K)
    (f : holomorphicFunctions U) :
    (restrictContinuousMap hKU f).comp (ContinuousMap.inclusion hLK) =
      restrictContinuousMap (hLK.trans hKU) f := by
  ext z
  rfl

/-- Composing `restrictContinuousMap hKU` with `ContinuousMap.compRightAlgHom` along
`hLK : L ⊆ K` gives `restrictContinuousMap (hLK.trans hKU)`. -/
@[simp]
theorem compRightAlgHom_inclusion_comp_restrictContinuousMap {K L : Set ℂ} (hKU : K ⊆ U)
    (hLK : L ⊆ K) :
    (ContinuousMap.compRightAlgHom ℂ ℂ (ContinuousMap.inclusion hLK)).comp
      (restrictContinuousMap hKU) = restrictContinuousMap (hLK.trans hKU) := by
  ext f z
  rfl

/-- `restrictContinuousMap hKU` is uniformly continuous from `holomorphicFunctions U` to
`C(K, ℂ)`. -/
theorem uniformContinuous_restrictContinuousMap {K : Set ℂ} (hKU : K ⊆ U) :
    UniformContinuous (restrictContinuousMap hKU) :=
  (ContinuousMap.uniformContinuous_comp_left (ContinuousMap.inclusion hKU)).comp
    uniformContinuous_subtype_val

/-- `restrictContinuousMap hKU` is continuous for compact convergence. -/
@[continuity, fun_prop]
theorem continuous_restrictContinuousMap {K : Set ℂ} (hKU : K ⊆ U) :
    Continuous (restrictContinuousMap hKU) :=
  (uniformContinuous_restrictContinuousMap hKU).continuous

/-- Restriction along an inclusion of open domains. -/
noncomputable def restrict (h : V ≤ U) : holomorphicFunctions U →ₐ[ℂ] holomorphicFunctions V :=
  (restrictContinuousMap h).codRestrict (holomorphicFunctions V) fun f =>
    ⟨extend f, (differentiableOn_extend f).mono h, fun z => extend_apply f (Set.inclusion h z)⟩

@[simp]
theorem restrict_apply (h : V ≤ U) (f : holomorphicFunctions U) (z : V) :
    (restrict h f).val z = f.val (Set.inclusion h z) := (rfl)

/-- Restricting to `V ≤ U` and then to `K ⊆ V` agrees with restricting directly to `K ⊆ U`. -/
@[simp]
theorem restrictContinuousMap_restrict {K : Set ℂ} (hVU : V ≤ U) (hKV : K ⊆ V)
    (f : holomorphicFunctions U) :
    restrictContinuousMap hKV (restrict hVU f) =
      restrictContinuousMap (hKV.trans hVU) f := by
  ext z
  rfl

/-- Algebra-homomorphism composition of `restrictContinuousMap` and `restrict`. -/
@[simp]
theorem restrictContinuousMap_comp_restrict {K : Set ℂ} (hVU : V ≤ U) (hKV : K ⊆ V) :
    (restrictContinuousMap hKV).comp (restrict hVU) =
      restrictContinuousMap (hKV.trans hVU) := by
  ext f z
  rfl

/-- Restriction agrees with restricting the same ambient representative. -/
@[simp]
theorem restrict_of (h : V ≤ U) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    restrict h (of U g hg) = of V g (hg.mono h) := by
  apply Subtype.ext
  ext z
  simp

@[simp]
theorem restrict_refl : restrict (le_refl U) = AlgHom.id ℂ (holomorphicFunctions U) := by
  ext f z
  simp

@[simp]
theorem restrict_comp (hVU : V ≤ U) (hWV : W ≤ V) :
    (restrict hWV).comp (restrict hVU) = restrict (hWV.trans hVU) := by
  ext f z
  simp

/-- Restriction is continuous for the compact-open topology. -/
@[continuity, fun_prop]
theorem continuous_restrict (h : V ≤ U) : Continuous (restrict h) :=
  (continuous_restrictContinuousMap h).subtype_mk _

section PointEvaluation

/-- Pointwise evaluation at `z : U` as a `ℂ`-algebra homomorphism
`holomorphicFunctions U →ₐ[ℂ] ℂ`. -/
noncomputable def eval (z : U) : holomorphicFunctions U →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ z).comp (holomorphicFunctions U).val

/-- Evaluating `eval z` at `f` returns `f.val z`. -/
@[simp]
theorem eval_apply (z : U) (f : holomorphicFunctions U) : eval z f = f.val z := (rfl)

/-- Pointwise evaluation at `z : U` agrees with `extend f z`. -/
theorem eval_apply_eq_extend (z : U) (f : holomorphicFunctions U) : eval z f = extend f z :=
  (extend_apply f z).symm

/-- Evaluating `of U g hg` at `z : U` recovers `g z`. -/
theorem eval_of (z : U) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    eval z (of U g hg) = g z := (rfl)

/-- Compatibility of pointwise evaluation with `restrict`. -/
theorem eval_restrict (h : V ≤ U) (z : V) (f : holomorphicFunctions U) :
    eval z (restrict h f) = eval (Set.inclusion h z) f := (rfl)

/-- Pointwise evaluation at `z : U` is continuous for compact convergence. -/
@[continuity, fun_prop]
theorem continuous_eval (z : U) : Continuous (eval z) :=
  (ContinuousMap.evalCLM ℂ z).continuous.comp continuous_subtype_val

/-- Pointwise evaluation at `z : U` as a continuous linear map
`holomorphicFunctions U →L[ℂ] ℂ`. -/
noncomputable def evalCLM (z : U) : holomorphicFunctions U →L[ℂ] ℂ where
  toLinearMap := (eval z).toLinearMap
  cont := continuous_eval z

/-- Coercing `evalCLM z` to a function recovers `eval z`. -/
@[simp]
theorem coe_evalCLM (z : U) : ⇑(evalCLM z) = eval z := (rfl)

/-- Underlying linear map of `evalCLM z`. -/
@[simp]
theorem toLinearMap_evalCLM (z : U) : (evalCLM z).toLinearMap = (eval z).toLinearMap := (rfl)

/-- Evaluating `evalCLM z` at `f` returns `f.val z`. -/
theorem evalCLM_apply (z : U) (f : holomorphicFunctions U) : evalCLM z f = f.val z := (rfl)

/-- Pointwise evaluation at `z : U` is uniformly continuous. -/
theorem uniformContinuous_eval (z : U) : UniformContinuous (eval z) := by
  rw [← coe_evalCLM]
  exact ContinuousLinearMap.uniformContinuous (E₁ := holomorphicFunctions U) (E₂ := ℂ)
    (evalCLM z)

end PointEvaluation

/-- Convergence in the inherited topology is locally uniform convergence on the open domain. -/
theorem tendsto_iff_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} {f : holomorphicFunctions U} :
    Tendsto F p (𝓝 f) ↔ TendstoLocallyUniformlyOn (fun i => extend (F i)) (extend f) p U := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, extend_apply]
  rfl

end HolomorphicFunctions

/-- The holomorphic functions form a closed subalgebra of the continuous functions. -/
theorem isClosed_holomorphicFunctions (U : Opens ℂ) :
    IsClosed (holomorphicFunctions U : Set C(U, ℂ)) := by
  refine isClosed_iff_forall_filter.mpr ?_
  intro f p hp hpSet hpnhds
  let : p.NeBot := hp
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let g : ℂ → ℂ := Function.extend Subtype.val f (fun _ => 0)
  apply mem_holomorphicFunctions_iff_extend.mpr
  have hconv : TendstoLocallyUniformly (fun k z => k z) f p :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hpnhds
  have hext : TendstoLocallyUniformlyOn
      (fun k : C(U, ℂ) => Function.extend Subtype.val k (fun _ => 0)) g p U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simp only [Function.comp_def, g, Subtype.val_injective.extend_apply]
    convert hconv using 1
  have hmem : ∀ᶠ k in p, k ∈ holomorphicFunctions U := le_principal_iff.mp hpSet
  exact hext.differentiableOn
    (hmem.mono fun k hk => mem_holomorphicFunctions_iff_extend.mp hk) U.isOpen

/-- Holomorphic functions are complete for compact convergence. -/
instance (U : Opens ℂ) : CompleteSpace (holomorphicFunctions U) := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact (isClosed_holomorphicFunctions U).completeSpace_coe

end TauCeti
