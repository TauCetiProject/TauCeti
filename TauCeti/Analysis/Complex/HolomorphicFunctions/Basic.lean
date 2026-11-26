/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.RemovableSingularity
public import TauCeti.Topology.Algebra.IsUniformGroup.Subalgebra
public import TauCeti.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.ContinuousMap.CompactConvergence.Group
public import TauCeti.Topology.Sets.Opens

/-!
# Holomorphic functions with the compact-open topology

`holomorphicFunctions U` is the complex subalgebra of `C(U, ℂ)` consisting of holomorphic
functions on the open set `U`. Holomorphy can be checked on any ambient representative;
in particular, extension by zero outside `U` gives the same condition. The topology and
uniformity are inherited from continuous maps, so convergence means locally uniform
convergence. This subalgebra is closed and complete; restriction to a subset `K ⊆ U`
(`HolomorphicFunctions.restrictContinuousMap`), restriction to a smaller open set
(`HolomorphicFunctions.restrict`), precomposition along a holomorphic map into another open set
(`HolomorphicFunctions.comp`), and pointwise evaluation (`HolomorphicFunctions.eval`, bundled as a
continuous linear map in `HolomorphicFunctions.evalCLM`) are continuous algebra homomorphisms, and
`HolomorphicFunctions.vanishingAt` cuts out the nonunital subalgebra of holomorphic functions
vanishing at a marked point.

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

/-- Extending `of U g hg` agrees with `g` on `U`. -/
@[simp]
theorem extend_of {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    extend (of U g hg) z = g z := by
  rw [extend_apply _ ⟨z, hz⟩, of_apply]

/-- The zero extension of zero is zero. -/
@[simp]
theorem extend_zero : extend (0 : holomorphicFunctions U) = 0 := by
  ext z
  by_cases hz : z ∈ U
  · simp [extend_apply _ ⟨z, hz⟩]
  · simp [hz]

/-- Restriction of `holomorphicFunctions U` to `C(K, ℂ)` for any subset `K ⊆ U`, as a `ℂ`-algebra
homomorphism. -/
noncomputable def restrictContinuousMap {K : Set ℂ} (hKU : K ⊆ U) :
    holomorphicFunctions U →ₐ[ℂ] C(K, ℂ) :=
  (ContinuousMap.compRightAlgHom ℂ ℂ (ContinuousMap.inclusion hKU)).comp
    (holomorphicFunctions U).val

/-- Evaluating `restrictContinuousMap hKU f` at `z : K` agrees with `f.val ⟨z.val, hKU z.property⟩`.
-/
@[simp]
theorem restrictContinuousMap_apply {K : Set ℂ} (hKU : K ⊆ U) (f : holomorphicFunctions U)
    (z : K) : restrictContinuousMap hKU f z = f.val ⟨z.val, hKU z.property⟩ := (rfl)

/-- Evaluating `restrictContinuousMap hKU f` at `z : K` agrees with `extend f z`. -/
theorem restrictContinuousMap_apply_eq_extend {K : Set ℂ} (hKU : K ⊆ U)
    (f : holomorphicFunctions U) (z : K) : restrictContinuousMap hKU f z = extend f z :=
  (extend_apply f ⟨z.val, hKU z.property⟩).symm

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
    uniformContinuous_subtypeVal

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

/-- Extending a restricted function agrees with the original extension on the smaller domain. -/
@[simp]
theorem extend_restrict (h : V ≤ U) (f : holomorphicFunctions U) {z : ℂ} (hz : z ∈ V) :
    extend (restrict h f) z = extend f z := by
  rw [extend_apply _ ⟨z, hz⟩, restrict_apply, extend_apply f ⟨z, h hz⟩]

@[simp]
theorem restrict_refl : restrict (le_refl U) = AlgHom.id ℂ (holomorphicFunctions U) := by
  ext f z
  simp

@[simp]
theorem restrict_comp_restrict (hVU : V ≤ U) (hWV : W ≤ V) :
    (restrict hWV).comp (restrict hVU) = restrict (hWV.trans hVU) := by
  ext f z
  simp

/-- Restriction is continuous for the compact-open topology. -/
@[continuity, fun_prop]
theorem continuous_restrict (h : V ≤ U) : Continuous (restrict h) :=
  (continuous_restrictContinuousMap h).subtype_mk _

/-- Convergence in the inherited topology is locally uniform convergence on the open domain. -/
theorem tendsto_iff_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} {f : holomorphicFunctions U} :
    Tendsto F p (𝓝 f) ↔ TendstoLocallyUniformlyOn (fun i => extend (F i)) (extend f) p U := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, extend_apply]
  rfl

/-- If a holomorphic function on `U` maps a subset `s ⊆ U` into an open set `V`, it maps a smaller
open neighbourhood `U' ≤ U` of `s` into `V`. -/
theorem exists_le_mapsTo_extend {s : Set ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) s V) :
    ∃ U' : Opens ℂ, s ⊆ U' ∧ U' ≤ U ∧ MapsTo (extend f) U' V := by
  refine ⟨⟨Subtype.val '' (f.val ⁻¹' (V : Set ℂ)),
    U.isOpen.isOpenMap_subtypeVal _ (V.isOpen.preimage f.val.continuous)⟩,
    fun z hz => ⟨⟨z, hs hz⟩, ?_, rfl⟩, ?_, ?_⟩
  · rw [mem_preimage, ← extend_apply]
    exact hf hz
  · rintro _ ⟨z, -, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩
    rw [extend_apply]
    exact mem_preimage.mp hz

/-- Values of `f` on `U` lie in `V` when `extend f` maps `U` into `V`. -/
theorem apply_mem_of_mapsTo_extend (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) U V) (z : U) : f.val z ∈ V := by
  rw [← extend_apply]
  exact hf z.property

/-- Precomposition with holomorphic functions on `V` along a holomorphic map from `U` into `V`. -/
noncomputable def comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V) :
    holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ
    (ContinuousMap.mk
      (fun z : U => (⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩ : V))
      (f.val.continuous.subtype_mk _))).comp (holomorphicFunctions V).val).codRestrict
      (holomorphicFunctions U) fun g =>
        ⟨extend g ∘ extend f, (differentiableOn_extend g).comp (differentiableOn_extend f) hf,
          fun z => by
            simp only [Function.comp_apply, AlgHom.comp_apply, Subalgebra.coe_val,
              ContinuousMap.compRightAlgHom_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
            rw [extend_apply f z, extend_apply g ⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩]⟩

@[simp]
theorem comp_apply (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : holomorphicFunctions V) (z : U) :
    (comp f hf g).val z =
      g.val ⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩ := (rfl)

/-- On the domain `U`, the zero extension of `comp f hf g` is `extend g ∘ extend f`. -/
theorem extend_comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : holomorphicFunctions V) {z : ℂ} (hz : z ∈ U) :
    extend (comp f hf g) z = extend g (extend f z) := by
  rw [extend_apply _ ⟨z, hz⟩, comp_apply, ← extend_apply g]
  congr 1
  exact (extend_apply f ⟨z, hz⟩).symm

/-- Composition with an ambient holomorphic representative agrees with function composition. -/
@[simp]
theorem comp_of (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g V) :
    comp f hf (of V g hg) = of U (g ∘ extend f) (hg.comp (differentiableOn_extend f) hf) := by
  apply Subtype.ext
  ext z
  simp [Function.comp_apply]

/-- Restricting the domain commutes with precomposition. -/
@[simp]
theorem restrict_comp (hWU : W ≤ U) (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) U V) (g : holomorphicFunctions V) :
    restrict hWU (comp f hf g) =
      comp (restrict hWU f)
        (fun z hz => by
          rw [extend_apply _ ⟨z, hz⟩, restrict_apply]
          exact extend_apply f ⟨z, hWU hz⟩ ▸ hf (hWU hz)) g := by
  apply Subtype.ext
  ext z
  simp only [restrict_apply, comp_apply]
  rfl

/-- Restricting the codomain before precomposing agrees with precomposing directly. -/
@[simp]
theorem comp_restrict {V' : Opens ℂ} (hVV' : V ≤ V') (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) U V) (g : holomorphicFunctions V') :
    comp f hf (restrict hVV' g) = comp f (hf.mono_right hVV') g := by
  apply Subtype.ext
  ext z
  rfl

/-- Precomposition of holomorphic functions is associative. -/
theorem comp_comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : holomorphicFunctions V) (hg : MapsTo (extend g) V W) (h : holomorphicFunctions W) :
    comp f hf (comp g hg h) =
      comp (comp f hf g)
        (fun z hz => by rw [extend_comp f hf g hz]; exact hg (hf hz)) h := by
  apply Subtype.ext
  ext z
  rfl

/-- Precomposition along a holomorphic map is continuous for the compact-open topology. -/
@[continuity]
theorem continuous_comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V) :
    Continuous (comp f hf) := by
  unfold comp
  exact (ContinuousMap.compRightAlgHom_continuous ℂ ℂ
    (ContinuousMap.mk
      (fun z : U => (⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩ : V))
      (f.val.continuous.subtype_mk _))).comp continuous_subtypeVal |>.subtype_mk _

/-- Point evaluation of a holomorphic function on `U` at `x ∈ U`. -/
noncomputable def eval (x : ℂ) (hx : x ∈ U) : holomorphicFunctions U →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ (⟨x, hx⟩ : U)).comp (holomorphicFunctions U).val

@[simp]
theorem eval_apply (x : ℂ) (hx : x ∈ U) (f : holomorphicFunctions U) :
    eval x hx f = f.val ⟨x, hx⟩ := (rfl)

/-- Pointwise evaluation at `x ∈ U` agrees with `extend f x`. -/
theorem eval_apply_eq_extend (x : ℂ) (hx : x ∈ U) (f : holomorphicFunctions U) :
    eval x hx f = extend f x :=
  (extend_apply f ⟨x, hx⟩).symm

/-- Evaluating `of U g hg` at `x ∈ U` recovers `g x`. -/
theorem eval_of (x : ℂ) (hx : x ∈ U) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    eval x hx (of U g hg) = g x := (rfl)

/-- Compatibility of pointwise evaluation with `restrict`. -/
theorem eval_restrict (h : V ≤ U) (x : ℂ) (hx : x ∈ V) (f : holomorphicFunctions U) :
    eval x hx (restrict h f) = eval x (h hx) f := (rfl)

/-- Pointwise evaluation at `x ∈ U` is continuous for compact convergence. -/
@[continuity, fun_prop]
theorem continuous_eval (x : ℂ) (hx : x ∈ U) : Continuous (eval x hx) :=
  (ContinuousMap.evalCLM ℂ (⟨x, hx⟩ : U)).continuous.comp continuous_subtypeVal

/-- Pointwise evaluation at `x ∈ U` as a continuous linear map
`holomorphicFunctions U →L[ℂ] ℂ`. -/
noncomputable def evalCLM (x : ℂ) (hx : x ∈ U) : holomorphicFunctions U →L[ℂ] ℂ where
  toLinearMap := (eval x hx).toLinearMap
  cont := continuous_eval x hx

/-- Coercing `evalCLM x hx` to a function recovers `eval x hx`. -/
@[simp]
theorem coe_evalCLM (x : ℂ) (hx : x ∈ U) : ⇑(evalCLM x hx) = eval x hx := (rfl)

/-- Underlying linear map of `evalCLM x hx`. -/
@[simp]
theorem toLinearMap_evalCLM (x : ℂ) (hx : x ∈ U) :
    (evalCLM x hx).toLinearMap = (eval x hx).toLinearMap := (rfl)

/-- Evaluating `evalCLM x hx` at `f` returns `f.val ⟨x, hx⟩`. -/
theorem evalCLM_apply (x : ℂ) (hx : x ∈ U) (f : holomorphicFunctions U) :
    evalCLM x hx f = f.val ⟨x, hx⟩ := (rfl)

/-- Pointwise evaluation at `x ∈ U` is uniformly continuous. -/
theorem uniformContinuous_eval (x : ℂ) (hx : x ∈ U) : UniformContinuous (eval x hx) := by
  rw [← coe_evalCLM]
  exact ContinuousLinearMap.uniformContinuous (E₁ := holomorphicFunctions U) (E₂ := ℂ)
    (evalCLM x hx)

/-- The nonunital complex subalgebra of `holomorphicFunctions U` consisting of functions
vanishing at a marked point `x ∈ U`. -/
noncomputable def vanishingAt (U : Opens ℂ) (x : ℂ) (hx : x ∈ U) :
    NonUnitalSubalgebra ℂ (holomorphicFunctions U) :=
  NonUnitalAlgHom.equalizer (eval x hx).toNonUnitalAlgHom 0

/-- Membership in `HolomorphicFunctions.vanishingAt U x hx` means vanishing at `⟨x, hx⟩`. -/
@[simp]
theorem mem_vanishingAt_iff {U : Opens ℂ} {x : ℂ} {hx : x ∈ U} {f : holomorphicFunctions U} :
    f ∈ vanishingAt U x hx ↔ f.val ⟨x, hx⟩ = 0 := by
  simp [vanishingAt, NonUnitalAlgHom.mem_equalizer]

/-- Pointwise evaluation of a function in `HolomorphicFunctions.vanishingAt U x hx` at `⟨x, hx⟩`
vanishes. -/
@[simp]
theorem apply_coe_vanishingAt {U : Opens ℂ} {x : ℂ} {hx : x ∈ U} (f : vanishingAt U x hx) :
    (f : holomorphicFunctions U).val ⟨x, hx⟩ = 0 :=
  mem_vanishingAt_iff.mp f.property

/-- Restriction of holomorphic functions vanishing at `x` along an inclusion of open domains. -/
noncomputable def restrictVanishingAt {x : ℂ} (h : V ≤ U) (hx : x ∈ V) :
    vanishingAt U x (h hx) →ₙₐ[ℂ] vanishingAt V x hx :=
  ((restrict h).toNonUnitalAlgHom.comp
    (NonUnitalSubalgebraClass.subtype (vanishingAt U x (h hx)))).codRestrict
      (vanishingAt V x hx) fun f => mem_vanishingAt_iff.mpr (by simp)

/-- Coercing `restrictVanishingAt` back to `holomorphicFunctions V` recovers `restrict`. -/
@[simp]
theorem coe_restrictVanishingAt {x : ℂ} (h : V ≤ U) (hx : x ∈ V)
    (f : vanishingAt U x (h hx)) :
    (restrictVanishingAt h hx f : holomorphicFunctions V) = restrict h f.val := (rfl)

/-- Restricting `vanishingAt` along `le_refl` is the identity homomorphism. -/
@[simp]
theorem restrictVanishingAt_refl {x : ℂ} (hx : x ∈ U) :
    restrictVanishingAt (le_refl U) hx = NonUnitalAlgHom.id ℂ (vanishingAt U x hx) := by
  ext f
  simp

/-- Successive restrictions of `vanishingAt` compose to restriction along the composite
inclusion. -/
@[simp]
theorem restrictVanishingAt_comp_restrictVanishingAt {x : ℂ} (hVU : V ≤ U) (hWV : W ≤ V)
    (hx : x ∈ W) :
    (restrictVanishingAt hWV hx).comp (restrictVanishingAt hVU (hWV hx)) =
      restrictVanishingAt (hWV.trans hVU) hx := by
  ext f
  simp [← AlgHom.comp_apply]

/-- Restriction on `HolomorphicFunctions.vanishingAt` is continuous for the compact-open
topology. -/
@[continuity]
theorem continuous_restrictVanishingAt {x : ℂ} (h : V ≤ U) (hx : x ∈ V) :
    Continuous (restrictVanishingAt h hx) :=
  ((continuous_restrict h).comp continuous_subtypeVal).subtype_mk _

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
