/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.IdempotentRange
public import TauCeti.Topology.VectorBundle.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.ContMDiff.IdempotentRange

/-!
# Smooth range bundles of idempotent families

The existing range bundle of a smooth family of projections has smooth Kato transition maps.
The carrier, subspace topology and atlas are those of the native continuous range construction.
Ground-field differentiation is compatible with extension-linear projections, including real
bases and complex fibres. A common range model is supplied explicitly. The complementary range
bundles sum smoothly to the fixed trivial ambient bundle, with inverse the two projections.

See Kato, *Perturbation Theory for Linear Operators*, Chapter I, §4.6.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Ring

namespace TauCeti

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] [CompleteSpace F]
  {n : ℕ∞ω} {p : B → F →L[𝕜'] F}

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕜' F']
  [IsScalarTower 𝕜 𝕜' F']

/-- The native Kato range-atlas coordinate changes are smooth, over the ground field. -/
theorem contMDiffOn_coordChangeL_rangeTrivialization (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p)
    (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ x₁ : B)
    (φ : F' ≃L[𝕜'] (p x₀).range) (φ₁ : F' ≃L[𝕜'] (p x₁).range) :
    ContMDiffOn I 𝓘(𝕜, F' →L[𝕜'] F') n
      (fun x ↦ ((rangeTrivialization hp.continuous hidem x₀ φ).coordChangeL 𝕜'
        (rangeTrivialization hp.continuous hidem x₁ φ₁) x : F' →L[𝕜'] F'))
      ((rangeTrivialization hp.continuous hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp.continuous hidem x₁ φ₁).baseSet) := by
  let : NormedAlgebra 𝕜 (F →L[𝕜'] F) :=
    { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
  let P : F →L[𝕜'] F' := (φ₁.symm : (p x₁).range →L[𝕜'] F') ∘L (p x₁).rangeRestrict
  let Q : F' →L[𝕜'] F := ((p x₀).range).subtypeL ∘L (φ : F' →L[𝕜'] (p x₀).range)
  let D : (F →L[𝕜'] F) →L[𝕜'] (F' →L[𝕜'] F') :=
    (ContinuousLinearMap.compL 𝕜' F' F F' P).comp
      ((ContinuousLinearMap.compL 𝕜' F' F F).flip Q)
  have hA : ContMDiffOn I 𝓘(𝕜, F →L[𝕜'] F) n
      (fun x ↦ (p x * p x₁ + (1 - p x) * (1 - p x₁))⁻¹ʳ * p x *
        (p x * p x₀ + (1 - p x) * (1 - p x₀)))
      ((rangeTrivialization hp.continuous hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp.continuous hidem x₁ φ₁).baseSet) := by
    have hi := (contMDiffOn_inverse_intertwiner hp x₁).mono
      (t := (rangeTrivialization hp.continuous hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp.continuous hidem x₁ φ₁).baseSet)
      (fun x hx ↦ (mem_baseSet_rangeTrivialization_iff hp.continuous hidem x₁ φ₁).mp hx.2)
    intro x hx
    exact contDiff_mul.comp_contMDiffWithinAt
      ((contDiff_mul.comp_contMDiffWithinAt
        ((hi x hx).prodMk_space (hp x).contMDiffWithinAt)).prodMk_space
        ((contMDiff_intertwiner hp x₀) x).contMDiffWithinAt)
  have hD : ContMDiffOn I 𝓘(𝕜, F' →L[𝕜'] F') n
      (fun x ↦ D ((p x * p x₁ + (1 - p x) * (1 - p x₁))⁻¹ʳ * p x *
        (p x * p x₀ + (1 - p x) * (1 - p x₀))))
      ((rangeTrivialization hp.continuous hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp.continuous hidem x₁ φ₁).baseSet) :=
    fun x hx ↦ (D.restrictScalars 𝕜).contDiff.comp_contMDiffWithinAt (hA x hx)
  refine hD.congr ?_
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [(rangeTrivialization hp.continuous hidem x₀ φ).coordChangeL_apply'
    (R := 𝕜') _ hx v, rangeTrivialization_symm_apply, rangeTrivialization_apply]
  rfl
/-- A smooth idempotent family gives a smooth bundle on the existing range atlas.
Scalar restriction retains the same total topology and all the extension-linear charts. -/
theorem rangeContMDiffVectorBundle
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range)) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeVectorBundle hp.continuous hidem hF'
    let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
    ContMDiffVectorBundle n F' (fun x ↦ (p x).range) I := by
  let _ := rangeFiberBundle hp.continuous hidem hF'
  let _ := rangeVectorBundle hp.continuous hidem hF'
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
  refine ⟨fun e e' he he' ↦ ?_⟩
  obtain ⟨x₀, φ, rfl⟩ :=
    (mem_trivializationAtlas_rangeFiberBundle_iff hp.continuous hidem hF' e).mp he.out
  obtain ⟨x₁, φ₁, rfl⟩ :=
    (mem_trivializationAtlas_rangeFiberBundle_iff hp.continuous hidem hF' e').mp he'.out
  have h := contMDiffOn_coordChangeL_rangeTrivialization hp hidem x₀ x₁ φ φ₁
  have hr : ContMDiffOn I 𝓘(𝕜, F' →L[𝕜] F') n
      (fun x ↦ ((rangeTrivialization hp.continuous hidem x₀ φ).coordChangeL 𝕜'
        (rangeTrivialization hp.continuous hidem x₁ φ₁) x : F' →L[𝕜'] F').restrictScalars 𝕜)
      ((rangeTrivialization hp.continuous hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp.continuous hidem x₁ φ₁).baseSet) :=
    fun x hx ↦ (ContinuousLinearMap.restrictScalarsIsometry 𝕜' F' F' 𝕜 𝕜
      ).toContinuousLinearMap.contDiff.comp_contMDiffWithinAt (h x hx)
  exact hr.congr fun x hx ↦
    (Trivialization.restrictScalars_coordChangeL 𝕜 𝕜' _ _ hx).symm

/-- The canonical inclusion of the native range bundle into the trivial ambient bundle is smooth. -/
theorem contMDiff_range_inclusion
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range)) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeVectorBundle hp.continuous hidem hF'
    let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
    ContMDiff (I.prod 𝓘(𝕜, F')) (I.prod 𝓘(𝕜, F)) n
      (fun v : TotalSpace F' (fun x ↦ (p x).range) ↦ (v.proj, (v.2 : F))) := by
  let _ := rangeFiberBundle hp.continuous hidem hF'
  let _ := rangeVectorBundle hp.continuous hidem hF'
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
  let _ := rangeContMDiffVectorBundle hp hidem hF'
  dsimp only
  intro v
  let φ : F' ≃L[𝕜'] (p v.proj).range := (hF' v.proj).some
  let e := rangeTrivialization hp.continuous hidem v.proj φ
  have : MemTrivializationAtlas e :=
    ⟨(mem_trivializationAtlas_rangeFiberBundle_iff hp.continuous hidem hF' e).mpr
      ⟨v.proj, φ, rfl⟩⟩
  have hv : v ∈ e.source :=
    e.mem_source.mpr (mem_baseSet_rangeTrivialization hp.continuous hidem _ _)
  have hb : ContMDiffAt (I.prod 𝓘(𝕜, F')) I n
      (fun w : TotalSpace F' (fun x ↦ (p x).range) ↦ w.proj) v :=
    (e.contMDiffAt_iff hv).mp contMDiffAt_id |>.1
  have hc : ContMDiffAt (I.prod 𝓘(𝕜, F')) 𝓘(𝕜, F') n
      (fun w : TotalSpace F' (fun x ↦ (p x).range) ↦ (e w).2) v :=
    (e.contMDiffAt_iff hv).mp contMDiffAt_id |>.2
  let Q : F' →L[𝕜'] F := ((p v.proj).range).subtypeL ∘L (φ : F' →L[𝕜'] (p v.proj).range)
  have hu := (contMDiff_intertwiner hp v.proj v.proj).comp v hb
  have hur : ContMDiffAt (I.prod 𝓘(𝕜, F')) 𝓘(𝕜, F →L[𝕜] F) n
      (fun w : TotalSpace F' (fun x ↦ (p x).range) ↦
        (p w.proj * p v.proj + (1 - p w.proj) * (1 - p v.proj)).restrictScalars 𝕜) v :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕜' F F 𝕜 𝕜
      ).toContinuousLinearMap.contDiff.comp_contMDiffAt hu
  have hq := (Q.restrictScalars 𝕜).contDiff.comp_contMDiffAt hc
  have hpr : ContMDiffAt (I.prod 𝓘(𝕜, F')) 𝓘(𝕜, F →L[𝕜] F) n
      (fun w : TotalSpace F' (fun x ↦ (p x).range) ↦ (p w.proj).restrictScalars 𝕜) v :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕜' F F 𝕜 𝕜
      ).toContinuousLinearMap.contDiff.comp_contMDiffAt ((hp v.proj).comp v hb)
  refine hb.prodMk ((hpr.clm_apply (hur.clm_apply hq)).congr_of_eventuallyEq ?_)
  filter_upwards [e.open_source.mem_nhds hv] with w hw
  have he := congrArg (fun z : TotalSpace F' (fun x ↦ (p x).range) ↦ (z.proj, (z.2 : F)))
    (e.toOpenPartialHomeomorph.left_inv hw)
  rw [rangeTrivialization_symm_apply] at he
  have he' := congrArg Prod.snd he
  -- Remove the range subtype before rewriting the base coordinate.
  change p (e w).1
    ((p (e w).1 * p v.proj + (1 - p (e w).1) * (1 - p v.proj))
      (φ (e w).2)) = (w.2 : F) at he'
  rw [e.coe_fst' (e.mem_source.mp hw)] at he'
  exact he'.symm

section RangeMaps

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- A smooth ambient vector with values in the moving range defines a smooth range-bundle map. -/
theorem contMDiffAt_range_mk
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range))
    {b : M → B} {v : M → F} {x : M}
    (hb : ContMDiffAt J I n b x) (hv : ContMDiffAt J 𝓘(𝕜, F) n v x)
    (hr : ∀ y, v y ∈ (p (b y)).range) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeVectorBundle hp.continuous hidem hF'
    let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
    ContMDiffAt J (I.prod 𝓘(𝕜, F')) n
      (fun y ↦ (⟨b y, ⟨v y, hr y⟩⟩ : TotalSpace F' (fun x ↦ (p x).range))) x := by
  let _ := rangeFiberBundle hp.continuous hidem hF'
  let _ := rangeVectorBundle hp.continuous hidem hF'
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
  let _ := rangeContMDiffVectorBundle hp hidem hF'
  dsimp only
  let φ : F' ≃L[𝕜'] (p (b x)).range := (hF' (b x)).some
  let e := rangeTrivialization hp.continuous hidem (b x) φ
  have : MemTrivializationAtlas e :=
    ⟨(mem_trivializationAtlas_rangeFiberBundle_iff hp.continuous hidem hF' e).mpr
      ⟨b x, φ, rfl⟩⟩
  have he : (⟨b x, ⟨v x, hr x⟩⟩ : TotalSpace F' (fun x ↦ (p x).range)) ∈ e.source :=
    e.mem_source.mpr (mem_baseSet_rangeTrivialization hp.continuous hidem _ _)
  refine (e.contMDiffAt_iff (IM := J)
    (f := fun y ↦ (⟨b y, ⟨v y, hr y⟩⟩ : TotalSpace F' (fun x ↦ (p x).range)))
    he).mpr ⟨hb, ?_⟩
  let P : F →L[𝕜'] F' := (φ.symm : (p (b x)).range →L[𝕜'] F') ∘L (p (b x)).rangeRestrict
  have hi := (contMDiffOn_inverse_intertwiner hp (b x)).contMDiffAt
    ((isOpen_setOf_isUnit_intertwiner hp.continuous (b x)).mem_nhds
      (ContinuousLinearMap.IsIdempotentElem.isUnit_mul_self_add_one_sub_mul_one_sub (hidem (b x))))
  have hir : ContMDiffAt J 𝓘(𝕜, F →L[𝕜] F) n
      (fun y ↦ ((p (b y) * p (b x) + (1 - p (b y)) * (1 - p (b x)))⁻¹ʳ).restrictScalars 𝕜) x :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕜' F F 𝕜 𝕜
      ).toContinuousLinearMap.contDiff.comp_contMDiffAt (hi.comp x hb)
  have hh := (P.restrictScalars 𝕜).contDiff.comp_contMDiffAt (hir.clm_apply hv)
  refine hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only [e]
  rw [rangeTrivialization_apply]
  rfl

/-- Smoothness into the native range bundle is exactly ambient smoothness. -/
theorem contMDiffAt_range_iff
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range))
    {f : M → TotalSpace F' (fun x ↦ (p x).range)} {x : M} :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeVectorBundle hp.continuous hidem hF'
    let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
    ContMDiffAt J (I.prod 𝓘(𝕜, F')) n f x ↔
      ContMDiffAt J (I.prod 𝓘(𝕜, F)) n (fun y ↦ ((f y).proj, ((f y).2 : F))) x := by
  let _ := rangeFiberBundle hp.continuous hidem hF'
  let _ := rangeVectorBundle hp.continuous hidem hF'
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
  dsimp only
  constructor
  · intro h
    exact (contMDiff_range_inclusion hp hidem hF' (f x)).comp x h
  · intro h
    exact contMDiffAt_range_mk hp hidem hF' h.fst h.snd (fun y ↦ (f y).2.2)

/-- The given projection, valued in its native range bundle, is a smooth map of total spaces. -/
theorem contMDiff_range_projection
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range)) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeVectorBundle hp.continuous hidem hF'
    let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      (fun q : B × F ↦ (⟨q.1, (p q.1).rangeRestrict q.2⟩ :
        TotalSpace F' (fun x ↦ (p x).range))) := by
  let _ := rangeFiberBundle hp.continuous hidem hF'
  let _ := rangeVectorBundle hp.continuous hidem hF'
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
  dsimp only
  intro q
  refine (contMDiffAt_range_iff hp hidem hF').mpr (contMDiffAt_fst.prodMk ?_)
  have hpr : ContMDiffAt (I.prod 𝓘(𝕜, F)) 𝓘(𝕜, F →L[𝕜] F) n
      (fun y : B × F ↦ (p y.1).restrictScalars 𝕜) q :=
    (ContinuousLinearMap.restrictScalarsIsometry 𝕜' F F 𝕜 𝕜
      ).toContinuousLinearMap.contDiff.comp_contMDiffAt ((hp q.1).comp q contMDiffAt_fst)
  exact hpr.clm_apply contMDiffAt_snd

end RangeMaps

variable {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  [NormedSpace 𝕜' F''] [IsScalarTower 𝕜 𝕜' F'']
/-- Complementary native range bundles split the trivial ambient bundle smoothly.
The underlying equivalence is the existing complementary-range sum homeomorphism. -/
noncomputable def rangeProdRangeOneSubDiffeomorph
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range))
    (hF'' : ∀ x, Nonempty (F'' ≃L[𝕜'] (1 - p x).range)) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeFiberBundle (continuous_const.sub hp.continuous) (fun x ↦ (hidem x).one_sub) hF''
    Diffeomorph (I.prod 𝓘(𝕜, F' × F'')) (I.prod 𝓘(𝕜, F))
      (TotalSpace (F' × F'') ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range))
      (B × F) n := by
  let _ := rangeFiberBundle hp.continuous hidem hF'
  let _ := rangeFiberBundle (continuous_const.sub hp.continuous) (fun x ↦ (hidem x).one_sub) hF''
  let _ := rangeVectorBundle hp.continuous hidem hF'
  let _ := rangeVectorBundle (continuous_const.sub hp.continuous) (fun x ↦ (hidem x).one_sub) hF''
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F' (fun x ↦ (p x).range)
  let _ := VectorBundle.restrictScalars 𝕜 𝕜' F'' (fun x ↦ (1 - p x).range)
  dsimp only
  have hp' : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n (fun x ↦ 1 - p x) :=
    (contDiff_fst.sub contDiff_snd).comp_contMDiff
      ((contMDiff_const (c := (1 : F →L[𝕜'] F))).prodMk_space hp)
  refine { toEquiv := (rangeProdRangeOneSubHomeomorph F' F'' hp.continuous hidem).toEquiv
           contMDiff_toFun := ?_
           contMDiff_invFun := ?_ }
  · intro v
    have hc := Bundle.contMDiffAt_totalSpace_prod_iff.mp (contMDiffAt_id
      (I := I.prod 𝓘(𝕜, F' × F'')) (n := n) (x := v))
    have h₁ := (contMDiff_range_inclusion hp hidem hF' ⟨v.proj, v.2.1⟩).comp v hc.1
    have h₂ := (contMDiff_range_inclusion hp' (fun x ↦ (hidem x).one_sub)
      hF'' ⟨v.proj, v.2.2⟩).comp v hc.2
    have h := h₁.fst.prodMk
      ((contDiff_fst.add contDiff_snd).comp_contMDiffAt (h₁.snd.prodMk_space h₂.snd))
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦
      rangeProdRangeOneSubHomeomorph_apply F' F'' hp.continuous hidem w)
  · intro q
    apply Bundle.contMDiffAt_totalSpace_prod_iff.mpr
    constructor
    · exact (contMDiff_range_projection hp hidem hF' q).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ congrArg
          (fun w : TotalSpace (F' × F'')
              ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range) ↦
            (⟨w.proj, w.2.1⟩ : TotalSpace F' (fun x ↦ (p x).range)))
          (rangeProdRangeOneSubHomeomorph_symm_apply F' F'' hp.continuous hidem y))
    · exact (contMDiff_range_projection hp' (fun x ↦ (hidem x).one_sub) hF'' q
      ).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ congrArg
          (fun w : TotalSpace (F' × F'')
              ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range) ↦
            (⟨w.proj, w.2.2⟩ : TotalSpace F'' (fun x ↦ (1 - p x).range)))
          (rangeProdRangeOneSubHomeomorph_symm_apply F' F'' hp.continuous hidem y))

/- As for the underlying homeomorphism, these getters are not simp lemmas: simplification of
`1 - p x` inside the dependent total-space type changes the left-hand sides. -/

/-- The smooth complementary splitting has the native summation formula. -/
theorem rangeProdRangeOneSubDiffeomorph_apply
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range))
    (hF'' : ∀ x, Nonempty (F'' ≃L[𝕜'] (1 - p x).range))
    (v : TotalSpace (F' × F'') ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range)) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeFiberBundle (continuous_const.sub hp.continuous)
      (fun x ↦ (hidem x).one_sub) hF''
    rangeProdRangeOneSubDiffeomorph hp hidem hF' hF'' v =
      (v.proj, (v.2.1 : F) + v.2.2) :=
  rangeProdRangeOneSubHomeomorph_apply F' F'' hp.continuous hidem v

/-- The inverse smooth splitting applies the two complementary projections. -/
theorem rangeProdRangeOneSubDiffeomorph_symm_apply
    (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜'] (p x).range))
    (hF'' : ∀ x, Nonempty (F'' ≃L[𝕜'] (1 - p x).range)) (q : B × F) :
    let _ := rangeFiberBundle hp.continuous hidem hF'
    let _ := rangeFiberBundle (continuous_const.sub hp.continuous)
      (fun x ↦ (hidem x).one_sub) hF''
    (rangeProdRangeOneSubDiffeomorph hp hidem hF' hF'').symm q =
      ⟨q.1, ((p q.1).rangeRestrict q.2, (1 - p q.1).rangeRestrict q.2)⟩ :=
  rangeProdRangeOneSubHomeomorph_symm_apply F' F'' hp.continuous hidem q

end TauCeti
