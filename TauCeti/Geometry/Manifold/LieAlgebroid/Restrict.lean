/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Locality, open restriction, and open-cover gluing for Lie algebroids

For a Lie algebroid `A` on `V → M`, `smulCommutator ℝ f (A.bracket a)` is scalar multiplication by
`A.anchorDeriv a f`, placing `A.bracket a` in Grothendieck's order-`1` differential operators
(`bracket_mem_differentialOperators_one`, EGA IV₄ §16.8). Over a finite-dimensional Hausdorff base,
`A.bracket` is local (`bracket_congr_of_eventuallyEq`, `restrict_bracket_congr`), restricts to
`U : Opens M` (`restrict`, `restrictLieHom`, `eq_restrict_of_bracket_restrict`), and glues along
open covers (`glueOpenCover`, `glueOpenCover_restrict`, `eq_glueOpenCover`; Mackenzie 2005, §3.3).
-/

public noncomputable section

open Bundle Filter Manifold Set TopologicalSpace VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

local notation "V|[" U "]" => ((ContinuousMap.mk Subtype.val continuous_subtype_val : C(U, M)) *ᵖ V)
local notation "τOpen" => Manifold.tangentSpaceOpenEquiv (I := I)

section WithAlgebroid

variable (A : LieAlgebroid I F V)

/-- Skew-symmetry of the Lie algebroid bracket: `[a, b] = -[b, a]`. -/
theorem bracket_swap (a b : Cₛ^∞⟮I; F, V⟯) : A.bracket a b = -A.bracket b a := by
  have h := A.bracket_self (a + b)
  simp only [map_add, LinearMap.add_apply, A.bracket_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

@[simp] theorem bracket_smul_left (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.bracket (f • a) b = f • A.bracket a b - A.anchorDeriv b f • a := by
  rw [A.bracket_swap, A.bracket_smul_right, neg_add, ← smul_neg, ← A.bracket_swap, sub_eq_add_neg]

theorem bracket_smul_left_apply (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    A.bracket (f • a) b x = f x • A.bracket a b x - mvfderiv I f x (A.anchor x (b x)) • a x := by
  simp [A.bracket_smul_left]

theorem bracket_smul_smul (a b : Cₛ^∞⟮I; F, V⟯) (f g : C^∞⟮I, M; ℝ⟯) : A.bracket (f • a) (g • b) =
    (f * g) • A.bracket a b + (f * A.anchorDeriv a g) • b - (g * A.anchorDeriv b f) • a := by
  rw [A.bracket_smul_right, A.bracket_smul_left, smul_sub, A.anchorDeriv_smul_left, smul_smul,
    smul_smul, mul_comm g f]; abel

theorem jacobi_bracket (a b c : Cₛ^∞⟮I; F, V⟯) :
    A.bracket a (A.bracket b c) + A.bracket b (A.bracket c a) + A.bracket c (A.bracket a b) = 0 :=
  by rw [A.bracket_bracket a b c, A.bracket_swap c a, map_neg, A.bracket_swap _ c]; abel

/-- Pointwise evaluation of sections in `A.Sections` as an `ℝ`-linear map into `V x`. -/
def Sections.evalLinearMap (x : M) : A.Sections →ₗ[ℝ] V x :=
  (ContMDiffSection.evalLinearMap I F ∞ V x).comp (A.sectionsEquiv.toLinearMap.restrictScalars ℝ)

@[simp] theorem Sections.evalLinearMap_apply (x : M) (s : A.Sections) :
    Sections.evalLinearMap A x s = A.sectionsEquiv s x := by
  rw [Sections.evalLinearMap, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, ContMDiffSection.evalLinearMap_apply]

theorem Sections.evalLinearMap_smul_function (x : M) (f : C^∞⟮I, M; ℝ⟯) (s : A.Sections) :
    Sections.evalLinearMap A x (f • s) = f x • Sections.evalLinearMap A x s := by
  simp [Sections.evalLinearMap_apply]

theorem Sections.evalLinearMap_surjective [FiniteDimensional ℝ E] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] (x : M) : Function.Surjective (Sections.evalLinearMap A x) :=
  (ContMDiffSection.evalLinearMap_surjective ∞ x).comp A.sectionsEquiv.surjective

@[simp] theorem smulCommutator_bracket (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    smulCommutator ℝ f (A.bracket a) = A.anchorDeriv a f • LinearMap.id := by
  ext b; simp [A.bracket_smul_right]

/-- Adjoint action `A.bracket a` is a linear differential operator of order at most `1`. -/
theorem bracket_mem_differentialOperators_one (a : Cₛ^∞⟮I; F, V⟯) :
    A.bracket a ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1 :=
  mem_differentialOperators_succ_iff.2 fun f ↦ by
    rw [A.smulCommutator_bracket, mem_differentialOperators_zero_iff]; intro g b; ext x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, ContMDiffSection.smul_apply]
    exact smul_comm (A.anchorDeriv a f x) (g x) (b x)

theorem anchorDeriv_congr {a a' : Cₛ^∞⟮I; F, V⟯} {f f' : C^∞⟮I, M; ℝ⟯} {x : M}
    (ha : a x = a' x) (hf : (f : M → ℝ) =ᶠ[𝓝 x] f') :
    A.anchorDeriv a f x = A.anchorDeriv a' f' x := by
  simp only [anchorDeriv_apply, ha, hf.mvfderiv_eq]

/-- Restrict the anchor of `A` to an open submanifold `U` via `tangentSpaceOpenEquiv`. -/
def restrictAnchor (U : Opens M) :
    Cₛ^∞⟮I; F →L[ℝ] E, fun x : U ↦ V|[U] x →L[ℝ] TangentSpace I x⟯ where
  toFun := Manifold.restrictOpenTargetTangentHom A.anchor U
  contMDiff_toFun := Manifold.contMDiff_restrictOpenTargetTangentHom A.anchor U A.anchor.contMDiff

@[simp] theorem restrictAnchor_apply (U : Opens M) (x : U) (v : V|[U] x) :
    dsimp% only [ContinuousMap.coe_mk] (A.restrictAnchor U x v = (τOpen x).symm (A.anchor x v)) :=
  Manifold.restrictOpenTargetTangentHom_apply A.anchor U x v

section LocalityAndRestrict

variable [FiniteDimensional ℝ E] [T2Space M]

theorem bracket_eq_zero_of_eventuallyEq_zero_right (a : Cₛ^∞⟮I; F, V⟯) {b : Cₛ^∞⟮I; F, V⟯} {x : M}
    (hb : ∀ᶠ y in 𝓝 x, b y = 0) : A.bracket a b x = 0 :=
  differentialOperators_section_apply_eq_zero_of_eventuallyEq
    (A.bracket_mem_differentialOperators_one a) hb

theorem bracket_eq_zero_of_eventuallyEq_zero_left {a : Cₛ^∞⟮I; F, V⟯} (b : Cₛ^∞⟮I; F, V⟯) {x : M}
    (ha : ∀ᶠ y in 𝓝 x, a y = 0) : A.bracket a b x = 0 := by
  rw [A.bracket_swap, ContMDiffSection.coe_neg, Pi.neg_apply,
    A.bracket_eq_zero_of_eventuallyEq_zero_right b ha, neg_zero]

theorem bracket_congr_right_of_eventuallyEq (a : Cₛ^∞⟮I; F, V⟯) {b b' : Cₛ^∞⟮I; F, V⟯} {x : M}
    (hb : ∀ᶠ y in 𝓝 x, b y = b' y) : A.bracket a b x = A.bracket a b' x := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← ContMDiffSection.coe_sub, ← map_sub]
  exact A.bracket_eq_zero_of_eventuallyEq_zero_right a (hb.mono fun _ hy ↦ by simp [hy])

theorem bracket_congr_left_of_eventuallyEq {a a' : Cₛ^∞⟮I; F, V⟯} (b : Cₛ^∞⟮I; F, V⟯) {x : M}
    (ha : ∀ᶠ y in 𝓝 x, a y = a' y) : A.bracket a b x = A.bracket a' b x := by
  rw [A.bracket_swap a b, A.bracket_swap a' b, ContMDiffSection.coe_neg, ContMDiffSection.coe_neg,
    Pi.neg_apply, Pi.neg_apply, A.bracket_congr_right_of_eventuallyEq b ha]

/-- **Locality of the Lie algebroid bracket.** `A.bracket a b x` depends only on germs at `x`. -/
theorem bracket_congr_of_eventuallyEq {a a' b b' : Cₛ^∞⟮I; F, V⟯} {x : M}
    (ha : ∀ᶠ y in 𝓝 x, a y = a' y) (hb : ∀ᶠ y in 𝓝 x, b y = b' y) :
    A.bracket a b x = A.bracket a' b' x :=
  (A.bracket_congr_left_of_eventuallyEq b ha).trans (A.bracket_congr_right_of_eventuallyEq a' hb)

theorem restrict_bracket_congr {U : Opens M} {a a' b b' : Cₛ^∞⟮I; F, V⟯}
    (ha : a.restrict U = a'.restrict U) (hb : b.restrict U = b'.restrict U) :
    (A.bracket a b).restrict U = (A.bracket a' b').restrict U := by
  have hev {u u' : Cₛ^∞⟮I; F, V⟯} (hu : u.restrict U = u'.restrict U) (x : U) :
      ∀ᶠ y in 𝓝 (x : M), u y = u' y := by
    rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
    exact Eventually.of_forall fun y ↦ (ContMDiffSection.restrict_apply u U y).symm.trans
      (congr($(hu) y).trans (ContMDiffSection.restrict_apply u' U y))
  exact ContMDiffSection.ext fun x ↦ (ContMDiffSection.restrict_apply _ U x).trans
    ((A.bracket_congr_of_eventuallyEq (hev ha x) (hev hb x)).trans
      (ContMDiffSection.restrict_apply _ U x).symm)

/-- Localize a smooth section `s` over `U : Opens M` around `x : U` to a global section on `M`. -/
def localizeSection (U : Opens M) (x : U) (s : Cₛ^∞⟮I; F, V|[U]⟯) : Cₛ^∞⟮I; F, V⟯ :=
  let ρ : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let ρMap : C^∞⟮I, U; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  ContMDiffSection.extendByZero ⟨ρMap • s,
    ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport
      ρMap ρ.hasCompactSupport s⟩

theorem localizeSection_eventuallyEq_on_open (U : Opens M) (x : U) (s : Cₛ^∞⟮I; F, V|[U]⟯) :
    ∀ᶠ y : U in 𝓝 x, localizeSection U x s (y : M) = s y := by
  let ρ : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let ρMap : C^∞⟮I, U; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  filter_upwards [ρ.eventuallyEq_one] with y (hy : ρMap y = 1)
  exact (ContMDiffSection.extendByZero_apply_of_mem
    ⟨ρMap • s, ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport
      ρMap ρ.hasCompactSupport s⟩ y).trans
    ((ContMDiffSection.smul_apply ρMap s y).trans (by rw [hy, one_smul]))

@[simp] theorem localizeSection_apply_self (U : Opens M) (x : U) (s : Cₛ^∞⟮I; F, V|[U]⟯) :
    dsimp% only [ContinuousMap.coe_mk] (localizeSection U x s (x : M) = s x) :=
  (localizeSection_eventuallyEq_on_open U x s).self_of_nhds

theorem eventuallyEq_localizeSection {U : Opens M} {a : Cₛ^∞⟮I; F, V⟯} {s : Cₛ^∞⟮I; F, V|[U]⟯}
    {x : U} (ha : ∀ᶠ y : U in 𝓝 x, a (y : M) = s y) :
    ∀ᶠ z : M in 𝓝 (x : M), a z = localizeSection U x s z := by
  rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
  exact (ha.and (localizeSection_eventuallyEq_on_open U x s)).mono fun _ ⟨h1, h2⟩ ↦ h1.trans h2.symm

/-- Pointwise formula for the restricted bracket of `A` on `U : Opens M`. -/
def restrictBracketFun (U : Opens M) (s t : Cₛ^∞⟮I; F, V|[U]⟯) (x : U) : V|[U] x :=
  A.bracket (localizeSection U x s) (localizeSection U x t) (x : M)

theorem restrictBracketFun_eq_of_eventuallyEq {U : Opens M} {a b : Cₛ^∞⟮I; F, V⟯}
    {s t : Cₛ^∞⟮I; F, V|[U]⟯} {x : U}
    (ha : ∀ᶠ y : U in 𝓝 x, a (y : M) = s y) (hb : ∀ᶠ y : U in 𝓝 x, b (y : M) = t y) :
    dsimp% only [ContinuousMap.coe_mk] (A.restrictBracketFun U s t x = A.bracket a b (x : M)) :=
  (A.bracket_congr_of_eventuallyEq (eventuallyEq_localizeSection ha)
    (eventuallyEq_localizeSection hb)).symm

theorem restrictBracketFun_eventuallyEq_restrict (U : Opens M) (s t : Cₛ^∞⟮I; F, V|[U]⟯) (x₀ : U) :
    ∀ᶠ y : U in 𝓝 x₀, A.restrictBracketFun U s t y =
      A.bracket (localizeSection U x₀ s) (localizeSection U x₀ t) (y : M) :=
  Filter.Eventually.mono (interior_mem_nhds.2 ((localizeSection_eventuallyEq_on_open U x₀ s).and
    (localizeSection_eventuallyEq_on_open U x₀ t))) fun _ hy ↦
      A.restrictBracketFun_eq_of_eventuallyEq
        (Filter.Eventually.mono (mem_interior_iff_mem_nhds.1 hy) fun _ hz ↦ hz.1)
        (Filter.Eventually.mono (mem_interior_iff_mem_nhds.1 hy) fun _ hz ↦ hz.2)

/-- The restricted Lie bracket of smooth sections over `U : Opens M`, bundled as a section. -/
def restrictBracketSection (U : Opens M) (s t : Cₛ^∞⟮I; F, V|[U]⟯) : Cₛ^∞⟮I; F, V|[U]⟯ where
  toFun := A.restrictBracketFun U s t
  contMDiff_toFun x₀ := (((A.bracket (localizeSection U x₀ s)
    (localizeSection U x₀ t)).restrict U).contMDiff x₀).congr_of_eventuallyEq <|
      (A.restrictBracketFun_eventuallyEq_restrict U s t x₀).mono fun y hy ↦
        TotalSpace.mk_inj.2 (hy.trans (ContMDiffSection.restrict_apply _ U y).symm)

@[simp] theorem restrictBracketSection_apply (U : Opens M) (s t : Cₛ^∞⟮I; F, V|[U]⟯) (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (A.restrictBracketSection U s t x =
      A.restrictBracketFun U s t x) := (rfl)

/-- The restricted Lie bracket on sections over `U : Opens M` as an `ℝ`-bilinear map. -/
def restrictBracket (U : Opens M) :
    Cₛ^∞⟮I; F, V|[U]⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V|[U]⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V|[U]⟯ :=
  have hex := localizeSection_eventuallyEq_on_open U
  have hadd {p p' : Cₛ^∞⟮I; F, V|[U]⟯} (x : U) :
      ∀ᶠ y : U in 𝓝 x, (localizeSection U x p + localizeSection U x p') (y : M) = (p + p') y :=
    ((hex x p).and (hex x p')).mono fun _ ⟨h1, h2⟩ ↦ by
      simp only [ContMDiffSection.coe_add, Pi.add_apply, h1, h2]; rfl
  have hsmul (r : ℝ) {p : Cₛ^∞⟮I; F, V|[U]⟯} (x : U) :
      ∀ᶠ y : U in 𝓝 x, (r • localizeSection U x p) (y : M) = (r • p) y :=
    (hex x p).mono fun _ h1 ↦ by simp only [ContMDiffSection.coe_smul, Pi.smul_apply, h1]; rfl
  LinearMap.mk₂ ℝ (A.restrictBracketSection U)
    (fun _ _ t ↦ ContMDiffSection.ext fun x ↦ by
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_add,
        Pi.add_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq (hadd x) (hex x t), map_add, LinearMap.add_apply,
        ContMDiffSection.coe_add, Pi.add_apply, restrictBracketFun, restrictBracketFun]; rfl)
    (fun r _ t ↦ ContMDiffSection.ext fun x ↦ by
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_smul,
        Pi.smul_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq (hsmul r x) (hex x t), map_smul,
        LinearMap.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply, restrictBracketFun]; rfl)
    (fun s _ _ ↦ ContMDiffSection.ext fun x ↦ by
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_add,
        Pi.add_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq (hex x s) (hadd x), map_add,
        ContMDiffSection.coe_add, Pi.add_apply, restrictBracketFun, restrictBracketFun]; rfl)
    (fun r s _ ↦ ContMDiffSection.ext fun x ↦ by
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_smul,
        Pi.smul_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq (hex x s) (hsmul r x), map_smul,
        ContMDiffSection.coe_smul, Pi.smul_apply, restrictBracketFun]; rfl)

private theorem restrictBracket_bracket_bracket (U : Opens M) (s t u : Cₛ^∞⟮I; F, V|[U]⟯) :
    A.restrictBracket U s (A.restrictBracket U t u) =
      A.restrictBracket U (A.restrictBracket U s t) u +
        A.restrictBracket U t (A.restrictBracket U s u) := by
  refine ContMDiffSection.ext fun x₀ ↦ ?_
  have hloc {p q : Cₛ^∞⟮I; F, V|[U]⟯} :
      ∀ᶠ y : U in 𝓝 x₀, A.bracket (localizeSection U x₀ p) (localizeSection U x₀ q) (y : M) =
        A.restrictBracketSection U p q y :=
    (A.restrictBracketFun_eventuallyEq_restrict U p q x₀).mono fun _ h ↦ h.symm
  simp only [ContinuousMap.coe_mk, restrictBracket, LinearMap.mk₂_apply,
    restrictBracketSection_apply, ContMDiffSection.coe_add, Pi.add_apply]
  rw [A.restrictBracketFun_eq_of_eventuallyEq (localizeSection_eventuallyEq_on_open U x₀ s) hloc,
    A.restrictBracketFun_eq_of_eventuallyEq hloc (localizeSection_eventuallyEq_on_open U x₀ u),
    A.restrictBracketFun_eq_of_eventuallyEq (localizeSection_eventuallyEq_on_open U x₀ t) hloc]
  exact congr($(A.bracket_bracket _ _ _) (x₀ : M))

private theorem restrictBracket_smul_apply (U : Opens M) (s t : Cₛ^∞⟮I; F, V|[U]⟯)
    (f : C^∞⟮I, U; ℝ⟯) (x : U) : A.restrictBracket U s (f • t) x =
      f x • A.restrictBracket U s t x + mvfderiv I f x (A.restrictAnchor U x (s x)) • t x := by
  obtain ⟨fExt, hfExt⟩ := (ContMDiffMap.contMDiffOn_extend U f 0).exists_contMDiffMap_eventuallyEq
    (U.isOpen.mem_nhds x.2)
  have hFU : ((fExt : M → ℝ) ∘ (Subtype.val : U → M)) =ᶠ[𝓝 x] f := by
    have hf' : ∀ᶠ z : M in 𝓝 (x : M), fExt z = Function.extend Subtype.val f 0 z := hfExt
    rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map] at hf'
    exact hf'.mono fun y hy ↦ hy.trans (Subtype.val_injective.extend_apply f 0 y)
  have hFx : fExt (x : M) = f x := hFU.self_of_nhds
  have hsmul : ∀ᶠ y : U in 𝓝 x, (fExt • localizeSection U x t) (y : M) = (f • t) y := by
    filter_upwards [hFU, localizeSection_eventuallyEq_on_open U x t] with y hyF hyt
    have hyF' : fExt (y : M) = f y := hyF
    simp only [ContMDiffSection.smul_apply, hyF', hyt]; exact rfl
  have hderiv : mvfderiv I fExt (x : M) (A.anchor (x : M) (s x)) =
      mvfderiv I f x (A.restrictAnchor U x (s x)) := by
    have h1 := mvfderiv_comp_apply (I := I) (I' := I) x (g := fExt) (f := (Subtype.val : U → M))
      (fExt.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)) (A.restrictAnchor U x (s x))
    rw [hFU.mvfderiv_eq] at h1
    rw [h1, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, restrictAnchor_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  simp only [ContinuousMap.coe_mk, restrictBracket, LinearMap.mk₂_apply,
    restrictBracketSection_apply]
  rw [A.restrictBracketFun_eq_of_eventuallyEq (localizeSection_eventuallyEq_on_open U x s) hsmul,
    A.bracket_smul_apply, localizeSection_apply_self, localizeSection_apply_self, hFx, hderiv]
  exact rfl

/-- **Restriction of a Lie algebroid to an open submanifold `U : Opens M`.** -/
def restrict (U : Opens M) : LieAlgebroid I F V|[U] where
  anchor := A.restrictAnchor U
  bracket := A.restrictBracket U
  bracket_self _ := ContMDiffSection.ext fun _ ↦ by
    simp only [ContinuousMap.coe_mk, restrictBracket, LinearMap.mk₂_apply,
      restrictBracketSection_apply, restrictBracketFun, A.bracket_self,
      ContMDiffSection.coe_zero, Pi.zero_apply]; rfl
  bracket_bracket := A.restrictBracket_bracket_bracket U
  bracket_smul_apply := A.restrictBracket_smul_apply U

@[simp] theorem restrict_anchor_apply (U : Opens M) (x : U) (v : V|[U] x) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).anchor x v = (τOpen x).symm (A.anchor x v)) := A.restrictAnchor_apply U x v

theorem tangentSpaceOpenEquiv_restrict_anchor_apply (U : Opens M) (x : U) (v : V|[U] x) :
    τOpen x ((A.restrict U).anchor x v) = A.anchor x v := by
  rw [restrict_anchor_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem restrict_bracket_apply_of_eventuallyEq {U : Opens M} {a b : Cₛ^∞⟮I; F, V⟯}
    {s t : Cₛ^∞⟮I; F, V|[U]⟯} {x : U}
    (ha : ∀ᶠ y : U in 𝓝 x, a (y : M) = s y) (hb : ∀ᶠ y : U in 𝓝 x, b (y : M) = t y) :
    dsimp% only [ContinuousMap.coe_mk] ((A.restrict U).bracket s t x = A.bracket a b (x : M)) :=
  A.restrictBracketFun_eq_of_eventuallyEq ha hb

@[simp] theorem restrict_bracket_restrict (U : Opens M) (a b : Cₛ^∞⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U) :=
  show (A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U from
    ContMDiffSection.ext fun x ↦ (A.restrict_bracket_apply_of_eventuallyEq
      (Eventually.of_forall fun y ↦ (ContMDiffSection.restrict_apply a U y).symm)
      (Eventually.of_forall fun y ↦ (ContMDiffSection.restrict_apply b U y).symm)).trans
        (ContMDiffSection.restrict_apply _ U x).symm

@[simp] theorem restrict_anchorDeriv_comp (U : Opens M) (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (A.restrict U).anchorDeriv (a.restrict U)
        (f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯)) =
      (A.anchorDeriv a f).comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯) := by
  let ιU : C^∞⟮I, U; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  change (A.restrict U).anchorDeriv (a.restrict U) (f.comp ιU) = (A.anchorDeriv a f).comp ιU
  ext x; rw [anchorDeriv_apply, ContMDiffMap.comp_apply, anchorDeriv_apply]
  refine (mvfderiv_comp_apply (I := I) (I' := I) x (g := f) (f := (Subtype.val : U → M))
    (f.contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    ((A.restrict U).anchor x (a.restrict U x))).trans ?_
  rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, restrict_anchor_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (mvfderiv I f (x : M) ∘ A.anchor (x : M)) (ContMDiffSection.restrict_apply a U x)

theorem eq_restrict_of_bracket_restrict {U : Opens M} {B : LieAlgebroid I F V|[U]}
    (hanchor : B.anchor = A.restrictAnchor U)
    (hbracket : ∀ a b : Cₛ^∞⟮I; F, V⟯,
      B.bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U) : B = A.restrict U :=
  LieAlgebroid.ext hanchor <| LinearMap.ext₂ fun s t ↦ ContMDiffSection.ext fun x ↦ by
    rw [B.bracket_congr_of_eventuallyEq
      ((localizeSection_eventuallyEq_on_open U x s).mono fun y h ↦
        h.symm.trans (ContMDiffSection.restrict_apply _ U y).symm)
      ((localizeSection_eventuallyEq_on_open U x t).mono fun y h ↦
        h.symm.trans (ContMDiffSection.restrict_apply _ U y).symm), hbracket]
    exact ContMDiffSection.restrict_apply _ U x

/-- Restriction of sections from `M` to `U` as a Lie algebra homomorphism `Γ(A) →ₗ⁅ℝ⁆ Γ(A|_U)`. -/
def restrictLieHom (U : Opens M) : A.Sections →ₗ⁅ℝ⁆ (A.restrict U).Sections where
  toFun s := (A.restrict U).sectionsEquiv.symm ((A.sectionsEquiv s).restrict U)
  map_add' _ _ := by simp
  map_smul' _ _ := by
    rw [LinearMapClass.map_smul_of_tower, ContMDiffSection.restrict_smul,
      LinearMapClass.map_smul_of_tower, RingHom.id_apply]
  map_lie' := (A.restrict U).sectionsEquiv.injective <| by simp [A.restrict_bracket_restrict U]

@[simp] theorem sectionsEquiv_restrictLieHom (U : Opens M) (s : A.Sections) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).sectionsEquiv (A.restrictLieHom U s) = (A.sectionsEquiv s).restrict U) :=
  (A.restrict U).sectionsEquiv.apply_symm_apply _

end LocalityAndRestrict

end WithAlgebroid

section Glue

variable {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
  (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
  (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
    Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
  (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
    (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
      (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)

private def glueOpenCoverAnchor : Cₛ^∞⟮I; F →L[ℝ] E, fun x : M ↦ V x →L[ℝ] TangentSpace I x⟯ := by
  let pt (x : M) : U (hcover x).choose := ⟨x, (hcover x).choose_spec⟩
  let ρ (x : M) : V x →L[ℝ] TangentSpace I x := (τOpen (pt x)).toContinuousLinearMap.comp
    ((B (hcover x).choose).anchor (pt x) : V x →L[ℝ] TangentSpace I (pt x))
  have hρ (i : α) (y : U i) : Manifold.restrictOpenTargetTangentHom ρ (U i) y = (B i).anchor y := by
    ext v; rw [Manifold.restrictOpenTargetTangentHom_apply]
    exact (τOpen y).injective
      ((ContinuousLinearEquiv.apply_symm_apply _ _).trans (hanchor _ i y _ y.2 v))
  refine ContMDiffSection.mk ρ fun x ↦ ?_; obtain ⟨i, hi⟩ := hcover x
  exact (Manifold.contMDiffAt_restrictOpenTargetTangentHom_iff (G := F) ρ (U i) ⟨x, hi⟩).1
    (((B i).anchor.contMDiff ⟨x, hi⟩).congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦ TotalSpace.mk_inj.2 (hρ i y)))

private theorem glueOpenCoverAnchor_apply (i : α) (x : U i) (v : V|[U i] x) :
    dsimp% only [ContinuousMap.coe_mk]
      (glueOpenCoverAnchor U hcover B hanchor (x : M) v = τOpen x ((B i).anchor x v)) :=
  hanchor _ i x _ x.2 v

private def glueOpenCoverBracket : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ := by
  let idx (x : M) : α := (hcover x).choose
  let brFun (a b : Cₛ^∞⟮I; F, V⟯) (x : M) : V x :=
    (B (idx x)).bracket (a.restrict (U (idx x))) (b.restrict (U (idx x)))
      ⟨x, (hcover x).choose_spec⟩
  let brSec (a b : Cₛ^∞⟮I; F, V⟯) : Cₛ^∞⟮I; F, V⟯ := ⟨brFun a b, fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x
    have hlift := ((Bundle.Pullback.contMDiff_iff
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) contMDiff_subtype_val).1
        ((B i).bracket (a.restrict (U i)) (b.restrict (U i))).contMDiff).2
    exact (contMDiffAt_subtype_iff (x := (⟨x, hi⟩ : U i))).1
      ((hlift ⟨x, hi⟩).congr_of_eventuallyEq (Eventually.of_forall fun y ↦
        TotalSpace.mk_inj.2 (hbracket (idx y) i a b y _ y.2)))⟩
  exact LinearMap.mk₂ ℝ brSec
    (fun a a' b ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_add, Pi.add_apply]; change brFun (a + a') b x = _ + _
      simp only [brFun, ContMDiffSection.restrict_add, map_add, LinearMap.add_apply,
        ContMDiffSection.coe_add, Pi.add_apply]; rfl)
    (fun r a b ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_smul, Pi.smul_apply]; change brFun (r • a) b x = r • _
      simp only [brFun, ContMDiffSection.restrict_smul, map_smul, LinearMap.smul_apply,
        ContMDiffSection.coe_smul, Pi.smul_apply]; rfl)
    (fun a b b' ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_add, Pi.add_apply]; change brFun a (b + b') x = _ + _
      simp only [brFun, ContMDiffSection.restrict_add, map_add, ContMDiffSection.coe_add,
        Pi.add_apply]; rfl)
    (fun r a b ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_smul, Pi.smul_apply]; change brFun a (r • b) x = r • _
      simp only [brFun, ContMDiffSection.restrict_smul, map_smul, ContMDiffSection.coe_smul,
        Pi.smul_apply]; rfl)

private theorem glueOpenCoverBracket_apply (i : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : U i) :
    dsimp% only [ContinuousMap.coe_mk] (glueOpenCoverBracket U hcover B hbracket a b (x : M) =
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) x) := hbracket _ i a b x _ x.2

private theorem glueOpenCoverBracket_restrict (i : α) (a b : Cₛ^∞⟮I; F, V⟯) :
    (glueOpenCoverBracket U hcover B hbracket a b).restrict (U i) =
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) :=
  ContMDiffSection.ext fun x ↦ (ContMDiffSection.restrict_apply _ (U i) x).trans
    (glueOpenCoverBracket_apply U hcover B hbracket i a b x)

/-- **Gluing Lie algebroids on an open cover** from compatible local anchors and brackets. -/
def glueOpenCover : LieAlgebroid I F V where
  anchor := glueOpenCoverAnchor U hcover B hanchor
  bracket := glueOpenCoverBracket U hcover B hbracket
  bracket_self a := ContMDiffSection.ext fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x
    rw [glueOpenCoverBracket_apply U hcover B hbracket i a a ⟨x, hi⟩, (B i).bracket_self,
      ContMDiffSection.coe_zero, ContMDiffSection.coe_zero, Pi.zero_apply, Pi.zero_apply]; rfl
  bracket_bracket a b c := ContMDiffSection.ext fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x; let hx : U i := ⟨x, hi⟩
    rw [ContMDiffSection.coe_add, Pi.add_apply,
      glueOpenCoverBracket_apply U hcover B hbracket i a _ hx,
      glueOpenCoverBracket_apply U hcover B hbracket i _ c hx,
      glueOpenCoverBracket_apply U hcover B hbracket i b _ hx,
      glueOpenCoverBracket_restrict, glueOpenCoverBracket_restrict, glueOpenCoverBracket_restrict]
    exact congr($((B i).bracket_bracket
      (a.restrict (U i)) (b.restrict (U i)) (c.restrict (U i))) hx)
  bracket_smul_apply a b f x := by
    obtain ⟨i, hi⟩ := hcover x; let hx : U i := ⟨x, hi⟩
    let fU : C^∞⟮I, U i; ℝ⟯ := f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U i; I, M⟯)
    have h1 : glueOpenCoverBracket U hcover B hbracket a (f • b) x =
        (B i).bracket (a.restrict (U i)) (fU • b.restrict (U i)) hx := by
      rw [glueOpenCoverBracket_apply U hcover B hbracket i a (f • b) hx,
        ContMDiffSection.restrict_smul_function]
    rw [h1, (B i).bracket_smul_apply, ← glueOpenCoverBracket_apply U hcover B hbracket i a b hx]
    have hderiv : mvfderiv I fU hx ((B i).anchor hx (a.restrict (U i) hx)) =
        mvfderiv I f x (glueOpenCoverAnchor U hcover B hanchor x (a x)) :=
      (mvfderiv_comp_apply (I := I) (I' := I) hx (g := f) (f := (Subtype.val : U i → M))
        (f.contMDiff.mdifferentiableAt (by simp))
        ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
        ((B i).anchor hx (a.restrict (U i) hx))).trans <| by
          rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
            ← glueOpenCoverAnchor_apply U hcover B hanchor i hx (a.restrict (U i) hx)]
          exact congrArg (mvfderiv I f x ∘ glueOpenCoverAnchor U hcover B hanchor x)
            (ContMDiffSection.restrict_apply a (U i) hx)
    rw [show fU hx = f x from rfl, hderiv,
      show b.restrict (U i) hx = b x from ContMDiffSection.restrict_apply b (U i) hx]; exact rfl

@[simp] theorem glueOpenCover_anchor_apply (i : α) (x : U i) (v : V|[U i] x) :
    dsimp% only [ContinuousMap.coe_mk]
      ((glueOpenCover U hcover B hanchor hbracket).anchor (x : M) v = τOpen x ((B i).anchor x v)) :=
  glueOpenCoverAnchor_apply U hcover B hanchor i x v

@[simp] theorem glueOpenCover_bracket_apply (i : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : U i) :
    dsimp% only [ContinuousMap.coe_mk]
      ((glueOpenCover U hcover B hanchor hbracket).bracket a b (x : M) =
        (B i).bracket (a.restrict (U i)) (b.restrict (U i)) x) :=
  glueOpenCoverBracket_apply U hcover B hbracket i a b x

section GlueRestrict
variable [FiniteDimensional ℝ E] [T2Space M]

@[simp] theorem glueOpenCover_restrict (i : α) :
    (glueOpenCover U hcover B hanchor hbracket).restrict (U i) = B i :=
  ((glueOpenCover U hcover B hanchor hbracket).eq_restrict_of_bracket_restrict
    (ContMDiffSection.ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by
      rw [restrictAnchor_apply, glueOpenCover_anchor_apply, ContinuousLinearEquiv.symm_apply_apply])
    fun a b ↦ ContMDiffSection.ext fun x ↦
      (glueOpenCover_bracket_apply U hcover B hanchor hbracket i a b x).symm.trans
        (ContMDiffSection.restrict_apply _ (U i) x).symm).symm

include hcover in
theorem eq_of_forall_restrict_eq {A₁ A₂ : LieAlgebroid I F V}
    (h : ∀ i, A₁.restrict (U i) = A₂.restrict (U i)) : A₁ = A₂ :=
  LieAlgebroid.ext (ContMDiffSection.ext fun x ↦ by
      obtain ⟨i, hi⟩ := hcover x; refine ContinuousLinearMap.ext fun v ↦ ?_
      let vU : V|[U i] ⟨x, hi⟩ := v; have ha := congr($((h i)).anchor ⟨x, hi⟩ vU)
      rw [restrict_anchor_apply, restrict_anchor_apply] at ha
      exact (τOpen (⟨x, hi⟩ : U i)).symm.injective ha)
    (LinearMap.ext₂ fun a b ↦ ContMDiffSection.ext fun x ↦ by
      obtain ⟨i, hi⟩ := hcover x
      have hb := congr($((h i)).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩)
      rw [A₁.restrict_bracket_restrict, A₂.restrict_bracket_restrict] at hb
      exact (ContMDiffSection.restrict_apply _ (U i) ⟨x, hi⟩).symm.trans
        (hb.trans (ContMDiffSection.restrict_apply _ (U i) ⟨x, hi⟩)))

theorem eq_glueOpenCover {A : LieAlgebroid I F V} (hA : ∀ i, A.restrict (U i) = B i) :
    A = glueOpenCover U hcover B hanchor hbracket :=
  eq_of_forall_restrict_eq U hcover fun i ↦
    (hA i).trans (glueOpenCover_restrict U hcover B hanchor hbracket i).symm

end GlueRestrict
end Glue
end TauCeti.LieAlgebroid
