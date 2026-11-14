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

For a Lie algebroid `A` on a vector bundle `V → M`, the Leibniz rule computes the commutator of
`A.bracket a` with multiplication by a smooth function `f` as scalar multiplication by
`A.anchorDeriv a f`. In Grothendieck's algebraic order filtration (`TauCeti.differentialOperators`),
`A.bracket a` is therefore a linear differential operator of order at most `1` without any
finite-rank or smoothness assumption on `V`. Over a finite-dimensional Hausdorff base `M`, smooth
bump functions then make `A.bracket` local in both arguments: `A.bracket a b x` depends only on the
germs of `a` and `b` at `x`.

Locality lets `A` restrict canonically to every open subset `U : Opens M`, as a Lie algebroid
`A.restrict U` on `((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)` characterized by
`(A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U`.
Conversely, compatible Lie algebroid structures on an open cover glue uniquely to a global Lie
algebroid (`TauCeti.LieAlgebroid.glueOpenCover`).

## Main definitions

* `TauCeti.LieAlgebroid.Sections.evalLinearMap`: pointwise evaluation `Γ(A) →ₗ[ℝ] V x`.
* `TauCeti.LieAlgebroid.restrictAnchor`: restriction of the anchor to `U : Opens M`.
* `TauCeti.LieAlgebroid.restrict`: the restricted Lie algebroid `A|_U` over `U : Opens M`.
* `TauCeti.LieAlgebroid.restrictLieHom`: restriction of sections `Γ(A) →ₗ⁅ℝ⁆ Γ(A|_U)` as a Lie
  algebra homomorphism.
* `TauCeti.LieAlgebroid.glueOpenCover`: gluing compatible local Lie algebroids along an open cover.

## Main results

* `TauCeti.LieAlgebroid.bracket_swap`, `TauCeti.LieAlgebroid.bracket_smul_left`,
  `TauCeti.LieAlgebroid.bracket_smul_smul`, `TauCeti.LieAlgebroid.jacobi_bracket`: skew-symmetry,
  left and bilateral Leibniz rules, and cyclic Jacobi identity.
* `TauCeti.LieAlgebroid.bracket_mem_differentialOperators_one`: `A.bracket a` is a first-order
  linear differential operator on sections.
* `TauCeti.LieAlgebroid.bracket_congr_of_eventuallyEq`,
  `TauCeti.LieAlgebroid.restrict_bracket_congr`: germ and open-set locality of the Lie bracket.
* `TauCeti.LieAlgebroid.restrict_bracket_restrict`,
  `TauCeti.LieAlgebroid.eq_restrict_of_bracket_restrict`: characterization and uniqueness of
  `A.restrict U`.
* `TauCeti.LieAlgebroid.glueOpenCover_restrict`, `TauCeti.LieAlgebroid.eq_glueOpenCover`: gluing
  and uniqueness on an open cover.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), §1.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

section Algebraic

variable (A : LieAlgebroid I F V)

/-- Skew-symmetry of the Lie algebroid bracket: `[a, b] = -[b, a]`. -/
theorem bracket_swap (a b : Cₛ^∞⟮I; F, V⟯) : A.bracket a b = -A.bracket b a := by
  have h := A.bracket_self (a + b)
  simp only [map_add, LinearMap.add_apply, A.bracket_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Left Leibniz rule: `[f • a, b] = f • [a, b] - (ρ(b) f) • a`. -/
@[simp]
theorem bracket_smul_left (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    A.bracket (f • a) b = f • A.bracket a b - A.anchorDeriv b f • a := by
  rw [A.bracket_swap, A.bracket_smul_right, neg_add, ← smul_neg, ← A.bracket_swap, sub_eq_add_neg]

/-- Pointwise left Leibniz rule for `[f • a, b]`. -/
theorem bracket_smul_left_apply (a b : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    A.bracket (f • a) b x = f x • A.bracket a b x - mvfderiv I f x (A.anchor x (b x)) • a x := by
  simp [A.bracket_smul_left]

/-- Bilateral Leibniz rule for `[f • a, g • b]`. -/
theorem bracket_smul_smul (a b : Cₛ^∞⟮I; F, V⟯) (f g : C^∞⟮I, M; ℝ⟯) :
    A.bracket (f • a) (g • b) =
      (f * g) • A.bracket a b + (f * A.anchorDeriv a g) • b - (g * A.anchorDeriv b f) • a := by
  rw [A.bracket_smul_right, A.bracket_smul_left, smul_sub, A.anchorDeriv_smul_left, smul_smul,
    smul_smul, mul_comm g f]
  abel

/-- Cyclic Jacobi identity `[a, [b, c]] + [b, [c, a]] + [c, [a, b]] = 0`. -/
theorem jacobi_bracket (a b c : Cₛ^∞⟮I; F, V⟯) :
    A.bracket a (A.bracket b c) + A.bracket b (A.bracket c a) +
      A.bracket c (A.bracket a b) = 0 := by
  rw [A.bracket_bracket a b c, A.bracket_swap c a, map_neg, A.bracket_swap (A.bracket a b) c]
  abel

/-- Pointwise evaluation of sections in `A.Sections` as an `ℝ`-linear map into the fibre `V x`. -/
def Sections.evalLinearMap (x : M) : A.Sections →ₗ[ℝ] V x :=
  (ContMDiffSection.evalLinearMap I F ∞ V x).comp (A.sectionsEquiv.toLinearMap.restrictScalars ℝ)

@[simp]
theorem Sections.evalLinearMap_apply (x : M) (s : A.Sections) :
    Sections.evalLinearMap A x s = A.sectionsEquiv s x := by
  rw [Sections.evalLinearMap, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, ContMDiffSection.evalLinearMap_apply]

theorem Sections.evalLinearMap_smul_function (x : M) (f : C^∞⟮I, M; ℝ⟯) (s : A.Sections) :
    Sections.evalLinearMap A x (f • s) = f x • Sections.evalLinearMap A x s := by
  rw [Sections.evalLinearMap_apply, map_smul, ContMDiffSection.smul_apply,
    Sections.evalLinearMap_apply]

/-- Over a finite-dimensional Hausdorff base, smooth sections of a smooth vector bundle evaluate
surjectively onto every fibre. -/
theorem Sections.evalLinearMap_surjective [FiniteDimensional ℝ E] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] (x : M) :
    Function.Surjective (Sections.evalLinearMap A x) :=
  (ContMDiffSection.evalLinearMap_surjective ∞ x).comp A.sectionsEquiv.surjective

/-- The commutator of `A.bracket a` with multiplication by `f : C^∞(M)` is scalar multiplication by
`A.anchorDeriv a f`. -/
@[simp]
theorem smulCommutator_bracket (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    smulCommutator ℝ f (A.bracket a) = A.anchorDeriv a f • LinearMap.id := by
  ext b
  simp [A.bracket_smul_right]

/-- Adjoint action `A.bracket a` is a linear differential operator of order at most `1` on smooth
sections, in Grothendieck's algebraic sense. -/
theorem bracket_mem_differentialOperators_one (a : Cₛ^∞⟮I; F, V⟯) :
    A.bracket a ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  rw [mem_differentialOperators_succ_iff]
  intro f
  rw [A.smulCommutator_bracket, mem_differentialOperators_zero_iff]
  intro g b
  ext x
  simp only [LinearMap.smul_apply, LinearMap.id_apply, ContMDiffSection.smul_apply]
  exact smul_comm (A.anchorDeriv a f x) (g x) (b x)

/-- `A.anchorDeriv a f x` depends on `a` only through `a x` and on `f` only through its germ at
`x`. -/
theorem anchorDeriv_congr {a a' : Cₛ^∞⟮I; F, V⟯} {f f' : C^∞⟮I, M; ℝ⟯} {x : M}
    (ha : a x = a' x) (hf : (f : M → ℝ) =ᶠ[𝓝 x] f') :
    A.anchorDeriv a f x = A.anchorDeriv a' f' x := by
  simp only [anchorDeriv_apply, ha, hf.mvfderiv_eq]

end Algebraic

/-! ### Locality of the Lie bracket -/

section Locality

variable [FiniteDimensional ℝ E] [T2Space M] (A : LieAlgebroid I F V)

/-- If `b` vanishes in a neighbourhood of `x`, then `[a, b] x = 0`. -/
theorem bracket_eq_zero_of_eventuallyEq_zero_right (a : Cₛ^∞⟮I; F, V⟯) {b : Cₛ^∞⟮I; F, V⟯} {x : M}
    (hb : ∀ᶠ y in 𝓝 x, b y = 0) : A.bracket a b x = 0 :=
  differentialOperators_section_apply_eq_zero_of_eventuallyEq
    (A.bracket_mem_differentialOperators_one a) hb

/-- If `a` vanishes in a neighbourhood of `x`, then `[a, b] x = 0`. -/
theorem bracket_eq_zero_of_eventuallyEq_zero_left {a : Cₛ^∞⟮I; F, V⟯} (b : Cₛ^∞⟮I; F, V⟯) {x : M}
    (ha : ∀ᶠ y in 𝓝 x, a y = 0) : A.bracket a b x = 0 := by
  rw [A.bracket_swap, ContMDiffSection.coe_neg, Pi.neg_apply,
    A.bracket_eq_zero_of_eventuallyEq_zero_right b ha, neg_zero]

/-- Germ locality in the right argument of `A.bracket`. -/
theorem bracket_congr_right_of_eventuallyEq (a : Cₛ^∞⟮I; F, V⟯) {b b' : Cₛ^∞⟮I; F, V⟯} {x : M}
    (hb : ∀ᶠ y in 𝓝 x, b y = b' y) : A.bracket a b x = A.bracket a b' x := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← ContMDiffSection.coe_sub, ← map_sub]
  refine A.bracket_eq_zero_of_eventuallyEq_zero_right a ?_
  filter_upwards [hb] with y hy
  simp [hy]

/-- Germ locality in the left argument of `A.bracket`. -/
theorem bracket_congr_left_of_eventuallyEq {a a' : Cₛ^∞⟮I; F, V⟯} (b : Cₛ^∞⟮I; F, V⟯) {x : M}
    (ha : ∀ᶠ y in 𝓝 x, a y = a' y) : A.bracket a b x = A.bracket a' b x := by
  rw [A.bracket_swap a b, A.bracket_swap a' b,
    ContMDiffSection.coe_neg, ContMDiffSection.coe_neg, Pi.neg_apply, Pi.neg_apply,
    A.bracket_congr_right_of_eventuallyEq b ha]

/-- **Locality of the Lie algebroid bracket.** `A.bracket a b x` depends only on the germs of `a`
and `b` at `x`. -/
theorem bracket_congr_of_eventuallyEq {a a' b b' : Cₛ^∞⟮I; F, V⟯} {x : M}
    (ha : ∀ᶠ y in 𝓝 x, a y = a' y) (hb : ∀ᶠ y in 𝓝 x, b y = b' y) :
    A.bracket a b x = A.bracket a' b' x :=
  (A.bracket_congr_left_of_eventuallyEq b ha).trans (A.bracket_congr_right_of_eventuallyEq a' hb)

/-- Open-set locality: if two pairs of global sections have equal restrictions to `U : Opens M`,
then the restrictions of their brackets to `U` coincide. -/
theorem restrict_bracket_congr {U : Opens M} {a a' b b' : Cₛ^∞⟮I; F, V⟯}
    (ha : a.restrict U = a'.restrict U) (hb : b.restrict U = b'.restrict U) :
    (A.bracket a b).restrict U = (A.bracket a' b').restrict U := by
  apply ContMDiffSection.ext
  intro x
  refine (ContMDiffSection.restrict_apply _ U x).trans
    (Eq.trans ?_ (ContMDiffSection.restrict_apply _ U x).symm)
  refine A.bracket_congr_of_eventuallyEq ?_ ?_
  · rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
    exact Filter.Eventually.of_forall fun y ↦
      (ContMDiffSection.restrict_apply a U y).symm.trans
        (congr($(ha) y).trans (ContMDiffSection.restrict_apply a' U y))
  · rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
    exact Filter.Eventually.of_forall fun y ↦
      (ContMDiffSection.restrict_apply b U y).symm.trans
        (congr($(hb) y).trans (ContMDiffSection.restrict_apply b' U y))

end Locality

/-! ### Restriction to an open submanifold -/

section RestrictAnchor

variable (A : LieAlgebroid I F V)

/-- Restrict the anchor of `A` to an open submanifold `U`, using `tangentSpaceOpenEquiv` on the
target tangent spaces. No finite-dimensionality or separation assumption is required. -/
def restrictAnchor (U : Opens M) :
    Cₛ^∞⟮I; F →L[ℝ] E,
      fun x : U ↦
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x →L[ℝ] TangentSpace I x⟯ where
  toFun := Manifold.restrictOpenTargetTangentHom A.anchor U
  contMDiff_toFun := Manifold.contMDiff_restrictOpenTargetTangentHom A.anchor U A.anchor.contMDiff

@[simp]
theorem restrictAnchor_apply (U : Opens M) (x : U)
    (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) :
    dsimp% only [ContinuousMap.coe_mk]
      (A.restrictAnchor U x v = (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (A.anchor x v)) :=
  Manifold.restrictOpenTargetTangentHom_apply A.anchor U x v

end RestrictAnchor

section Restrict

variable [FiniteDimensional ℝ E] [T2Space M] (A : LieAlgebroid I F V)

/-- Localize a smooth section `s` over `U : Opens M` around `x : U` to a globally smooth section on
`M`, by multiplying `s` by a smooth bump function on `U` equal to `1` near `x` and extending by
zero. -/
def localizeSection (U : Opens M) (x : U)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) : Cₛ^∞⟮I; F, V⟯ :=
  let ρ : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let ρMap : C^∞⟮I, U; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  ContMDiffSection.extendByZero
    ⟨ρMap • s,
      ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport
        ρMap ρ.hasCompactSupport s⟩

/-- At the base point `x : U`, `localizeSection U x s` takes the value `s x`. -/
@[simp]
theorem localizeSection_apply_self (U : Opens M) (x : U)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    dsimp% only [ContinuousMap.coe_mk] (localizeSection U x s (x : M) = s x) := by
  let ρ : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let ρMap : C^∞⟮I, U; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  have h := ContMDiffSection.extendByZero_apply_of_mem
    ⟨ρMap • s, ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport
      ρMap ρ.hasCompactSupport s⟩ x
  have hx1 : ρMap x = 1 := ρ.eq_one
  exact h.trans <| (ContMDiffSection.smul_apply ρMap s x).trans <| by rw [hx1, one_smul]

/-- `localizeSection U x s` agrees with `s` on a neighbourhood of `x` in `U`. -/
theorem localizeSection_eventuallyEq_on_open (U : Opens M) (x : U)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    ∀ᶠ y : U in 𝓝 x, localizeSection U x s (y : M) = s y := by
  let ρ : SmoothBumpFunction I x := Classical.arbitrary (SmoothBumpFunction I x)
  let ρMap : C^∞⟮I, U; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  filter_upwards [ρ.eventuallyEq_one] with y hy
  have h := ContMDiffSection.extendByZero_apply_of_mem
    ⟨ρMap • s, ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport
      ρMap ρ.hasCompactSupport s⟩ y
  have hy1 : ρMap y = 1 := hy
  exact h.trans <| (ContMDiffSection.smul_apply ρMap s y).trans <| by rw [hy1, one_smul]

/-- Any global section `a` agreeing with `s` near `x : U` agrees with `localizeSection U x s` in
`𝓝 (x : M)`. -/
theorem eventuallyEq_localizeSection {U : Opens M} {a : Cₛ^∞⟮I; F, V⟯}
    {s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    (ha : ∀ᶠ y : U in 𝓝 x, a (y : M) = s y) :
    ∀ᶠ z : M in 𝓝 (x : M), a z = localizeSection U x s z := by
  rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
  filter_upwards [ha, localizeSection_eventuallyEq_on_open U x s] with y hya hyl
  exact hya.trans hyl.symm

/-- Pointwise formula for the restricted bracket of `A` on `U : Opens M`. -/
def restrictBracketFun (U : Opens M)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x :=
  A.bracket (localizeSection U x s) (localizeSection U x t) (x : M)

/-- If global sections `a` and `b` agree with `s` and `t` near `x : U`, then
`restrictBracketFun A U s t x = A.bracket a b (x : M)`. -/
theorem restrictBracketFun_eq_of_eventuallyEq {U : Opens M} {a b : Cₛ^∞⟮I; F, V⟯}
    {s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    (ha : ∀ᶠ y : U in 𝓝 x, a (y : M) = s y) (hb : ∀ᶠ y : U in 𝓝 x, b (y : M) = t y) :
    dsimp% only [ContinuousMap.coe_mk]
      (A.restrictBracketFun U s t x = A.bracket a b (x : M)) :=
  (A.bracket_congr_of_eventuallyEq (eventuallyEq_localizeSection ha)
    (eventuallyEq_localizeSection hb)).symm

/-- Near any point `x₀ : U`, `restrictBracketFun A U s t` agrees with the restriction of a single
ambient bracket `A.bracket (localizeSection U x₀ s) (localizeSection U x₀ t)`. -/
theorem restrictBracketFun_eventuallyEq_restrict (U : Opens M)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) (x₀ : U) :
    ∀ᶠ y : U in 𝓝 x₀, A.restrictBracketFun U s t y =
      A.bracket (localizeSection U x₀ s) (localizeSection U x₀ t) (y : M) := by
  let a₀ := localizeSection U x₀ s
  let b₀ := localizeSection U x₀ t
  have hmem : interior {y : U | a₀ (y : M) = s y ∧ b₀ (y : M) = t y} ∈ 𝓝 x₀ :=
    interior_mem_nhds.2 ((localizeSection_eventuallyEq_on_open U x₀ s).and
      (localizeSection_eventuallyEq_on_open U x₀ t))
  filter_upwards [hmem] with y hy
  have hnhds : {z : U | a₀ (z : M) = s z ∧ b₀ (z : M) = t z} ∈ 𝓝 y :=
    mem_interior_iff_mem_nhds.1 hy
  exact A.restrictBracketFun_eq_of_eventuallyEq
    (by filter_upwards [hnhds] with z hz using hz.1)
    (by filter_upwards [hnhds] with z hz using hz.2)

/-- The restricted Lie bracket of two smooth sections over `U : Opens M`, bundled as a smooth
section. -/
def restrictBracketSection (U : Opens M)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ where
  toFun := A.restrictBracketFun U s t
  contMDiff_toFun x₀ := by
    let c₀ := (A.bracket (localizeSection U x₀ s) (localizeSection U x₀ t)).restrict U
    refine (c₀.contMDiff x₀).congr_of_eventuallyEq ?_
    filter_upwards [A.restrictBracketFun_eventuallyEq_restrict U s t x₀] with y hy
    exact TotalSpace.mk_inj.2 (hy.trans (ContMDiffSection.restrict_apply _ U y).symm)

@[simp]
theorem restrictBracketSection_apply (U : Opens M)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    dsimp% only [ContinuousMap.coe_mk]
      (A.restrictBracketSection U s t x = A.restrictBracketFun U s t x) :=
  (rfl)

/-- The restricted Lie bracket on sections over `U : Opens M` as an `ℝ`-bilinear map. -/
def restrictBracket (U : Opens M) :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ :=
  LinearMap.mk₂ ℝ (A.restrictBracketSection U)
    (fun s s' t ↦ ContMDiffSection.ext fun x ↦ by
      have hs := localizeSection_eventuallyEq_on_open U x s
      have hs' := localizeSection_eventuallyEq_on_open U x s'
      have ht := localizeSection_eventuallyEq_on_open U x t
      have hadd : ∀ᶠ y : U in 𝓝 x,
          (localizeSection U x s + localizeSection U x s') (y : M) = (s + s') y := by
        filter_upwards [hs, hs'] with y h1 h2
        simp only [ContMDiffSection.coe_add, Pi.add_apply, h1, h2]
        exact rfl
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_add,
        Pi.add_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq hadd ht, map_add, LinearMap.add_apply,
        ContMDiffSection.coe_add, Pi.add_apply, restrictBracketFun, restrictBracketFun]
      exact rfl)
    (fun r s t ↦ ContMDiffSection.ext fun x ↦ by
      have hs := localizeSection_eventuallyEq_on_open U x s
      have ht := localizeSection_eventuallyEq_on_open U x t
      have hsmul : ∀ᶠ y : U in 𝓝 x, (r • localizeSection U x s) (y : M) = (r • s) y := by
        filter_upwards [hs] with y h1
        simp only [ContMDiffSection.coe_smul, Pi.smul_apply, h1]
        exact rfl
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_smul,
        Pi.smul_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq hsmul ht, map_smul, LinearMap.smul_apply,
        ContMDiffSection.coe_smul, Pi.smul_apply, restrictBracketFun]
      exact rfl)
    (fun s t t' ↦ ContMDiffSection.ext fun x ↦ by
      have hs := localizeSection_eventuallyEq_on_open U x s
      have ht := localizeSection_eventuallyEq_on_open U x t
      have ht' := localizeSection_eventuallyEq_on_open U x t'
      have hadd : ∀ᶠ y : U in 𝓝 x,
          (localizeSection U x t + localizeSection U x t') (y : M) = (t + t') y := by
        filter_upwards [ht, ht'] with y h1 h2
        simp only [ContMDiffSection.coe_add, Pi.add_apply, h1, h2]
        exact rfl
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_add,
        Pi.add_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq hs hadd, map_add,
        ContMDiffSection.coe_add, Pi.add_apply, restrictBracketFun, restrictBracketFun]
      exact rfl)
    (fun r s t ↦ ContMDiffSection.ext fun x ↦ by
      have hs := localizeSection_eventuallyEq_on_open U x s
      have ht := localizeSection_eventuallyEq_on_open U x t
      have hsmul : ∀ᶠ y : U in 𝓝 x, (r • localizeSection U x t) (y : M) = (r • t) y := by
        filter_upwards [ht] with y h1
        simp only [ContMDiffSection.coe_smul, Pi.smul_apply, h1]
        exact rfl
      simp only [ContinuousMap.coe_mk, restrictBracketSection_apply, ContMDiffSection.coe_smul,
        Pi.smul_apply]
      rw [A.restrictBracketFun_eq_of_eventuallyEq hs hsmul, map_smul,
        ContMDiffSection.coe_smul, Pi.smul_apply, restrictBracketFun]
      exact rfl)

private theorem restrictBracket_bracket_bracket (U : Opens M)
    (s t u : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    A.restrictBracket U s (A.restrictBracket U t u) =
      A.restrictBracket U (A.restrictBracket U s t) u +
        A.restrictBracket U t (A.restrictBracket U s u) := by
  apply ContMDiffSection.ext
  intro x₀
  let a₀ := localizeSection U x₀ s
  let b₀ := localizeSection U x₀ t
  let c₀ := localizeSection U x₀ u
  have hmem : interior {y : U | a₀ (y : M) = s y ∧ b₀ (y : M) = t y ∧ c₀ (y : M) = u y} ∈ 𝓝 x₀ :=
    interior_mem_nhds.2 ((localizeSection_eventuallyEq_on_open U x₀ s).and
      ((localizeSection_eventuallyEq_on_open U x₀ t).and
        (localizeSection_eventuallyEq_on_open U x₀ u)))
  have htu : ∀ᶠ y : U in 𝓝 x₀, A.bracket b₀ c₀ (y : M) = A.restrictBracketSection U t u y := by
    filter_upwards [hmem] with y hy
    have hnhds := mem_interior_iff_mem_nhds.1 hy
    exact (A.restrictBracketFun_eq_of_eventuallyEq
      (by filter_upwards [hnhds] with z hz using hz.2.1)
      (by filter_upwards [hnhds] with z hz using hz.2.2)).symm
  have hst : ∀ᶠ y : U in 𝓝 x₀, A.bracket a₀ b₀ (y : M) = A.restrictBracketSection U s t y := by
    filter_upwards [hmem] with y hy
    have hnhds := mem_interior_iff_mem_nhds.1 hy
    exact (A.restrictBracketFun_eq_of_eventuallyEq
      (by filter_upwards [hnhds] with z hz using hz.1)
      (by filter_upwards [hnhds] with z hz using hz.2.1)).symm
  have hsu : ∀ᶠ y : U in 𝓝 x₀, A.bracket a₀ c₀ (y : M) = A.restrictBracketSection U s u y := by
    filter_upwards [hmem] with y hy
    have hnhds := mem_interior_iff_mem_nhds.1 hy
    exact (A.restrictBracketFun_eq_of_eventuallyEq
      (by filter_upwards [hnhds] with z hz using hz.1)
      (by filter_upwards [hnhds] with z hz using hz.2.2)).symm
  have ha₀ := localizeSection_eventuallyEq_on_open U x₀ s
  have hb₀ := localizeSection_eventuallyEq_on_open U x₀ t
  have hc₀ := localizeSection_eventuallyEq_on_open U x₀ u
  simp only [ContinuousMap.coe_mk, restrictBracket, LinearMap.mk₂_apply,
    restrictBracketSection_apply, ContMDiffSection.coe_add, Pi.add_apply]
  rw [A.restrictBracketFun_eq_of_eventuallyEq ha₀ htu,
    A.restrictBracketFun_eq_of_eventuallyEq hst hc₀,
    A.restrictBracketFun_eq_of_eventuallyEq hb₀ hsu]
  exact congr($(A.bracket_bracket a₀ b₀ c₀) (x₀ : M))

private theorem restrictBracket_smul_apply (U : Opens M)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯)
    (f : C^∞⟮I, U; ℝ⟯) (x : U) :
    A.restrictBracket U s (f • t) x =
      f x • A.restrictBracket U s t x +
        mvfderiv I f x (A.restrictAnchor U x (s x)) • t x := by
  obtain ⟨fExt, hfExt⟩ := (ContMDiffMap.contMDiffOn_extend U f 0).exists_contMDiffMap_eventuallyEq
    (U.isOpen.mem_nhds x.2)
  have hFU : ((fExt : M → ℝ) ∘ (Subtype.val : U → M)) =ᶠ[𝓝 x] f := by
    have hfExt' : ∀ᶠ z : M in 𝓝 (x : M), fExt z = Function.extend Subtype.val f 0 z := hfExt
    rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
      at hfExt'
    filter_upwards [hfExt'] with y hy
    exact hy.trans (Subtype.val_injective.extend_apply f 0 y)
  have hFx : fExt (x : M) = f x := hFU.self_of_nhds
  have hsmul : ∀ᶠ y : U in 𝓝 x, (fExt • localizeSection U x t) (y : M) = (f • t) y := by
    filter_upwards [hFU, localizeSection_eventuallyEq_on_open U x t] with y hyF hyt
    have hyF' : fExt (y : M) = f y := hyF
    simp only [ContMDiffSection.smul_apply, hyF', hyt]
    exact rfl
  have hderiv : mvfderiv I fExt (x : M) (A.anchor (x : M) (s x)) =
      mvfderiv I f x (A.restrictAnchor U x (s x)) := by
    have h1 := mvfderiv_comp_apply (I := I) (I' := I) x
      (g := fExt) (f := (Subtype.val : U → M))
      (fExt.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (A.restrictAnchor U x (s x))
    rw [hFU.mvfderiv_eq] at h1
    rw [h1, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      restrictAnchor_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [ContinuousMap.coe_mk, restrictBracket, LinearMap.mk₂_apply,
    restrictBracketSection_apply]
  rw [A.restrictBracketFun_eq_of_eventuallyEq (localizeSection_eventuallyEq_on_open U x s) hsmul,
    A.bracket_smul_apply, localizeSection_apply_self, localizeSection_apply_self, hFx, hderiv]
  exact rfl

/-- **Restriction of a Lie algebroid to an open submanifold.** Over a finite-dimensional Hausdorff
base `M`, a Lie algebroid `A` restricts to any open subset `U : Opens M` on the open-restricted
bundle `(⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V`. -/
def restrict (U : Opens M) :
    LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) where
  anchor := A.restrictAnchor U
  bracket := A.restrictBracket U
  bracket_self s := ContMDiffSection.ext fun x ↦ by
    simp only [ContinuousMap.coe_mk, restrictBracket, LinearMap.mk₂_apply,
      restrictBracketSection_apply, restrictBracketFun, A.bracket_self,
      ContMDiffSection.coe_zero, Pi.zero_apply]
    exact rfl
  bracket_bracket := A.restrictBracket_bracket_bracket U
  bracket_smul_apply := A.restrictBracket_smul_apply U

@[simp]
theorem restrict_anchor_apply (U : Opens M) (x : U)
    (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).anchor x v =
        (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (A.anchor x v)) :=
  A.restrictAnchor_apply U x v

theorem tangentSpaceOpenEquiv_restrict_anchor_apply (U : Opens M) (x : U)
    (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) :
    Manifold.tangentSpaceOpenEquiv (I := I) x ((A.restrict U).anchor x v) = A.anchor x v := by
  rw [restrict_anchor_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- If global sections `a` and `b` agree with `s` and `t` near `x : U`, then
`(A.restrict U).bracket` evaluates at `x` to `A.bracket a b (x : M)`. -/
theorem restrict_bracket_apply_of_eventuallyEq {U : Opens M} {a b : Cₛ^∞⟮I; F, V⟯}
    {s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    (ha : ∀ᶠ y : U in 𝓝 x, a (y : M) = s y) (hb : ∀ᶠ y : U in 𝓝 x, b (y : M) = t y) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).bracket s t x = A.bracket a b (x : M)) :=
  A.restrictBracketFun_eq_of_eventuallyEq ha hb

/-- Restricting global sections to `U` intertwines `A.bracket` with `(A.restrict U).bracket`. -/
@[simp]
theorem restrict_bracket_restrict (U : Opens M) (a b : Cₛ^∞⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U) :=
  show (A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U by
    apply ContMDiffSection.ext
    intro x
    refine (A.restrict_bracket_apply_of_eventuallyEq ?_ ?_).trans
      (ContMDiffSection.restrict_apply _ U x).symm
    · exact Filter.Eventually.of_forall fun y ↦ (ContMDiffSection.restrict_apply a U y).symm
    · exact Filter.Eventually.of_forall fun y ↦ (ContMDiffSection.restrict_apply b U y).symm

/-- Differentiation along the restricted anchor commutes with restricting smooth functions to
`U`. -/
@[simp]
theorem restrict_anchorDeriv_comp (U : Opens M) (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) :
    (A.restrict U).anchorDeriv (a.restrict U)
        (f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯)) =
      (A.anchorDeriv a f).comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U; I, M⟯) := by
  let ιU : C^∞⟮I, U; I, M⟯ := ⟨Subtype.val, contMDiff_subtype_val⟩
  -- Bind the open inclusion as `ιU` so `rw` does not unfold its `ContMDiffMap` subtype constructor.
  change (A.restrict U).anchorDeriv (a.restrict U) (f.comp ιU) = (A.anchorDeriv a f).comp ιU
  ext x
  rw [anchorDeriv_apply, ContMDiffMap.comp_apply, anchorDeriv_apply]
  have h1 := mvfderiv_comp_apply (I := I) (I' := I) x
    (g := f) (f := (Subtype.val : U → M))
    (f.contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    ((A.restrict U).anchor x (a.restrict U x))
  exact h1.trans <| by
    rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      restrict_anchor_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (mvfderiv I f (x : M) ∘ A.anchor (x : M)) (ContMDiffSection.restrict_apply a U x)

/-- Uniqueness of the restricted Lie algebroid: a Lie algebroid `B` over `U` with the restricted
anchor whose bracket agrees with `A.bracket` on restricted global sections equals `A.restrict U`. -/
theorem eq_restrict_of_bracket_restrict {U : Opens M}
    {B : LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)}
    (hanchor : B.anchor = A.restrictAnchor U)
    (hbracket : ∀ a b : Cₛ^∞⟮I; F, V⟯,
      B.bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U) :
    B = A.restrict U := by
  ext1
  · exact hanchor
  · ext s t : 2
    apply ContMDiffSection.ext
    intro x
    have hs : ∀ᶠ y : U in 𝓝 x, s y = ((localizeSection U x s).restrict U) y :=
      (localizeSection_eventuallyEq_on_open U x s).mono fun y h ↦
        h.symm.trans (ContMDiffSection.restrict_apply _ U y).symm
    have ht : ∀ᶠ y : U in 𝓝 x, t y = ((localizeSection U x t).restrict U) y :=
      (localizeSection_eventuallyEq_on_open U x t).mono fun y h ↦
        h.symm.trans (ContMDiffSection.restrict_apply _ U y).symm
    rw [B.bracket_congr_of_eventuallyEq hs ht, hbracket]
    exact ContMDiffSection.restrict_apply _ U x

/-- Restriction of sections from `M` to `U` as a Lie algebra homomorphism `Γ(A) →ₗ⁅ℝ⁆ Γ(A|_U)`. -/
def restrictLieHom (U : Opens M) : A.Sections →ₗ⁅ℝ⁆ (A.restrict U).Sections where
  toFun s := (A.restrict U).sectionsEquiv.symm ((A.sectionsEquiv s).restrict U)
  map_add' s t := by simp
  map_smul' c s := by
    rw [LinearMapClass.map_smul_of_tower, ContMDiffSection.restrict_smul,
      LinearMapClass.map_smul_of_tower, RingHom.id_apply]
  map_lie' {s t} := (A.restrict U).sectionsEquiv.injective <| by
    simp [A.restrict_bracket_restrict U]

@[simp]
theorem sectionsEquiv_restrictLieHom (U : Opens M) (s : A.Sections) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).sectionsEquiv (A.restrictLieHom U s) = (A.sectionsEquiv s).restrict U) :=
  (A.restrict U).sectionsEquiv.apply_symm_apply _

end Restrict

/-! ### Gluing Lie algebroids along an open cover -/

section Glue

private def glueOpenCoverAnchor {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v)) :
    Cₛ^∞⟮I; F →L[ℝ] E, fun x : M ↦ V x →L[ℝ] TangentSpace I x⟯ := by
  let idx (x : M) : α := (hcover x).choose
  let hidx (x : M) : x ∈ U (idx x) := (hcover x).choose_spec
  let pt (x : M) : U (idx x) := ⟨x, hidx x⟩
  let ρ (x : M) : V x →L[ℝ] TangentSpace I x :=
    (Manifold.tangentSpaceOpenEquiv (I := I) (pt x)).toContinuousLinearMap.comp
      ((B (idx x)).anchor (pt x) : V x →L[ℝ] TangentSpace I (pt x))
  have hρ (i : α) (x : U i) : Manifold.restrictOpenTargetTangentHom ρ (U i) x = (B i).anchor x := by
    ext v
    rw [Manifold.restrictOpenTargetTangentHom_apply]
    apply (Manifold.tangentSpaceOpenEquiv (I := I) x).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hanchor (idx x) i x (hidx x) x.2 v
  refine ContMDiffSection.mk ρ fun x ↦ ?_
  obtain ⟨i, hi⟩ := hcover x
  refine (Manifold.contMDiffAt_restrictOpenTargetTangentHom_iff (G := F) ρ (U i) ⟨x, hi⟩).1 ?_
  exact ((B i).anchor.contMDiff ⟨x, hi⟩).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ TotalSpace.mk_inj.2 (hρ i y))

private theorem glueOpenCoverAnchor_apply {α : Type*} (U : α → Opens M)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
    (i : α) (x : U i) (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V) x) :
    dsimp% only [ContinuousMap.coe_mk]
      (glueOpenCoverAnchor U hcover B hanchor (x : M) v =
        Manifold.tangentSpaceOpenEquiv (I := I) x ((B i).anchor x v)) :=
  hanchor _ i x _ x.2 v

private def glueOpenCoverBracket {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ := by
  let idx (x : M) : α := (hcover x).choose
  let hidx (x : M) : x ∈ U (idx x) := (hcover x).choose_spec
  let brFun (a b : Cₛ^∞⟮I; F, V⟯) (x : M) : V x :=
    (B (idx x)).bracket (a.restrict (U (idx x))) (b.restrict (U (idx x))) ⟨x, hidx x⟩
  have hbr_smooth (a b : Cₛ^∞⟮I; F, V⟯) : CMDiff ∞ (T% (brFun a b)) := fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x
    let ιU : C(U i, M) := ⟨Subtype.val, continuous_subtype_val⟩
    have hlift := ((Bundle.Pullback.contMDiff_iff ιU contMDiff_subtype_val).1
      ((B i).bracket (a.restrict (U i)) (b.restrict (U i))).contMDiff).2
    refine (contMDiffAt_subtype_iff (x := (⟨x, hi⟩ : U i))).1 ?_
    exact (hlift ⟨x, hi⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦
      TotalSpace.mk_inj.2 (hbracket (idx y) i a b y (hidx y) y.2))
  let brSec (a b : Cₛ^∞⟮I; F, V⟯) : Cₛ^∞⟮I; F, V⟯ := ⟨brFun a b, hbr_smooth a b⟩
  exact LinearMap.mk₂ ℝ brSec
    (fun a a' b ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_add, Pi.add_apply]
      -- Evaluate `brSec` on both sides as `brFun` at `x`.
      change brFun (a + a') b x = brFun a b x + brFun a' b x
      simp only [brFun, ContMDiffSection.restrict_add, map_add, LinearMap.add_apply,
        ContMDiffSection.coe_add, Pi.add_apply]
      exact rfl)
    (fun r a b ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_smul, Pi.smul_apply]
      -- Evaluate `brSec` on both sides as `brFun` at `x`.
      change brFun (r • a) b x = r • brFun a b x
      simp only [brFun, ContMDiffSection.restrict_smul, map_smul, LinearMap.smul_apply,
        ContMDiffSection.coe_smul, Pi.smul_apply]
      exact rfl)
    (fun a b b' ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_add, Pi.add_apply]
      -- Evaluate `brSec` on both sides as `brFun` at `x`.
      change brFun a (b + b') x = brFun a b x + brFun a b' x
      simp only [brFun, ContMDiffSection.restrict_add, map_add,
        ContMDiffSection.coe_add, Pi.add_apply]
      exact rfl)
    (fun r a b ↦ ContMDiffSection.ext fun x ↦ by
      rw [ContMDiffSection.coe_smul, Pi.smul_apply]
      -- Evaluate `brSec` on both sides as `brFun` at `x`.
      change brFun a (r • b) x = r • brFun a b x
      simp only [brFun, ContMDiffSection.restrict_smul, map_smul,
        ContMDiffSection.coe_smul, Pi.smul_apply]
      exact rfl)

private theorem glueOpenCoverBracket_apply {α : Type*} (U : α → Opens M)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)
    (i : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : U i) :
    dsimp% only [ContinuousMap.coe_mk]
      (glueOpenCoverBracket U hcover B hbracket a b (x : M) =
        (B i).bracket (a.restrict (U i)) (b.restrict (U i)) x) :=
  hbracket _ i a b x _ x.2

private theorem glueOpenCoverBracket_restrict {α : Type*} (U : α → Opens M)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)
    (i : α) (a b : Cₛ^∞⟮I; F, V⟯) :
    (glueOpenCoverBracket U hcover B hbracket a b).restrict (U i) =
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) :=
  ContMDiffSection.ext fun x ↦
    (ContMDiffSection.restrict_apply _ (U i) x).trans
      (glueOpenCoverBracket_apply U hcover B hbracket i a b x)

/-- **Gluing Lie algebroids on an open cover.** Let `U : α → Opens M` cover `M`, and let `B i` be a
Lie algebroid on the restriction of `V` to `U i` for each `i`. Assume that on every overlap
`U i ∩ U j`:
* the anchors agree under `tangentSpaceOpenEquiv`;
* the brackets of restrictions of ambient smooth sections agree pointwise.

Then there is a global Lie algebroid on `V` whose restriction to every `U i` is `B i`. -/
def glueOpenCover {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩) :
    LieAlgebroid I F V where
  anchor := glueOpenCoverAnchor U hcover B hanchor
  bracket := glueOpenCoverBracket U hcover B hbracket
  bracket_self a := ContMDiffSection.ext fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x
    rw [glueOpenCoverBracket_apply U hcover B hbracket i a a ⟨x, hi⟩, (B i).bracket_self,
      ContMDiffSection.coe_zero, ContMDiffSection.coe_zero, Pi.zero_apply, Pi.zero_apply]
    exact rfl
  bracket_bracket a b c := ContMDiffSection.ext fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x
    let hx : U i := ⟨x, hi⟩
    rw [ContMDiffSection.coe_add, Pi.add_apply,
      glueOpenCoverBracket_apply U hcover B hbracket i a _ hx,
      glueOpenCoverBracket_apply U hcover B hbracket i _ c hx,
      glueOpenCoverBracket_apply U hcover B hbracket i b _ hx,
      glueOpenCoverBracket_restrict, glueOpenCoverBracket_restrict, glueOpenCoverBracket_restrict]
    exact congr($((B i).bracket_bracket
      (a.restrict (U i)) (b.restrict (U i)) (c.restrict (U i))) hx)
  bracket_smul_apply a b f x := by
    obtain ⟨i, hi⟩ := hcover x
    let hx : U i := ⟨x, hi⟩
    let fU : C^∞⟮I, U i; ℝ⟯ :=
      f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^∞⟮I, U i; I, M⟯)
    have h1 : glueOpenCoverBracket U hcover B hbracket a (f • b) x =
        (B i).bracket (a.restrict (U i)) (fU • b.restrict (U i)) hx := by
      rw [glueOpenCoverBracket_apply U hcover B hbracket i a (f • b) hx,
        ContMDiffSection.restrict_smul_function]
    rw [h1, (B i).bracket_smul_apply, ← glueOpenCoverBracket_apply U hcover B hbracket i a b hx]
    have hfx : fU hx = f x := rfl
    have hbx : b.restrict (U i) hx = b x := ContMDiffSection.restrict_apply b (U i) hx
    have hderiv : mvfderiv I fU hx ((B i).anchor hx (a.restrict (U i) hx)) =
        mvfderiv I f x (glueOpenCoverAnchor U hcover B hanchor x (a x)) := by
      have hc := mvfderiv_comp_apply (I := I) (I' := I) hx
        (g := f) (f := (Subtype.val : U i → M))
        (f.contMDiff.mdifferentiableAt (by simp))
        ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
        ((B i).anchor hx (a.restrict (U i) hx))
      exact hc.trans <| by
        rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
          ← glueOpenCoverAnchor_apply U hcover B hanchor i hx (a.restrict (U i) hx)]
        exact congrArg (mvfderiv I f x ∘ glueOpenCoverAnchor U hcover B hanchor x)
          (ContMDiffSection.restrict_apply a (U i) hx)
    rw [hfx, hderiv, hbx]
    exact rfl

/-- Evaluating the anchor of `glueOpenCover` over `x ∈ U i` agrees with `(B i).anchor`. -/
@[simp]
theorem glueOpenCover_anchor_apply {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)
    (i : α) (x : U i) (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V) x) :
    dsimp% only [ContinuousMap.coe_mk]
      ((glueOpenCover U hcover B hanchor hbracket).anchor (x : M) v =
        Manifold.tangentSpaceOpenEquiv (I := I) x ((B i).anchor x v)) :=
  glueOpenCoverAnchor_apply U hcover B hanchor i x v

/-- Evaluating the bracket of `glueOpenCover` on `U i` agrees with `(B i).bracket` on restricted
sections. -/
@[simp]
theorem glueOpenCover_bracket_apply {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)
    (i : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : U i) :
    dsimp% only [ContinuousMap.coe_mk]
      ((glueOpenCover U hcover B hanchor hbracket).bracket a b (x : M) =
        (B i).bracket (a.restrict (U i)) (b.restrict (U i)) x) :=
  glueOpenCoverBracket_apply U hcover B hbracket i a b x

section
variable [FiniteDimensional ℝ E] [T2Space M]

/-- Restricting `glueOpenCover` back to `U i` recovers `B i`. -/
@[simp]
theorem glueOpenCover_restrict {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)
    (i : α) :
    (glueOpenCover U hcover B hanchor hbracket).restrict (U i) = B i := by
  symm
  refine (glueOpenCover U hcover B hanchor hbracket).eq_restrict_of_bracket_restrict ?_ ?_
  · apply ContMDiffSection.ext
    intro x
    ext v
    rw [restrictAnchor_apply, glueOpenCover_anchor_apply, ContinuousLinearEquiv.symm_apply_apply]
  · intro a b
    apply ContMDiffSection.ext
    intro x
    exact ((glueOpenCover_bracket_apply U hcover B hanchor hbracket i a b x).symm.trans
      (ContMDiffSection.restrict_apply _ (U i) x).symm)

/-- Two global Lie algebroids whose restrictions to every open set of an open cover agree are
equal. -/
theorem eq_of_forall_restrict_eq {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {A₁ A₂ : LieAlgebroid I F V} (h : ∀ i, A₁.restrict (U i) = A₂.restrict (U i)) :
    A₁ = A₂ := by
  ext1
  · apply ContMDiffSection.ext
    intro x
    obtain ⟨i, hi⟩ := hcover x
    ext v
    let vU : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V) ⟨x, hi⟩ := v
    have ha := congr($((h i)).anchor ⟨x, hi⟩ vU)
    rw [restrict_anchor_apply, restrict_anchor_apply] at ha
    exact (Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, hi⟩ : U i)).symm.injective ha
  · ext a b : 2
    apply ContMDiffSection.ext
    intro x
    obtain ⟨i, hi⟩ := hcover x
    have hb := congr($((h i)).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩)
    rw [A₁.restrict_bracket_restrict, A₂.restrict_bracket_restrict] at hb
    exact (ContMDiffSection.restrict_apply _ (U i) ⟨x, hi⟩).symm.trans
      (hb.trans (ContMDiffSection.restrict_apply _ (U i) ⟨x, hi⟩))

/-- Uniqueness of `glueOpenCover`: a global Lie algebroid whose restriction to every `U i` is `B i`
equals `glueOpenCover U hcover B hanchor hbracket`. -/
theorem eq_glueOpenCover {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (B : ∀ i, LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M)) *ᵖ V))
    (hanchor : ∀ (i j : α) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v : V x),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hi⟩ ((B i).anchor ⟨x, hi⟩ v) =
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, hj⟩ ((B j).anchor ⟨x, hj⟩ v))
    (hbracket : ∀ (i j : α) (a b : Cₛ^∞⟮I; F, V⟯) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (B i).bracket (a.restrict (U i)) (b.restrict (U i)) ⟨x, hi⟩ =
        (B j).bracket (a.restrict (U j)) (b.restrict (U j)) ⟨x, hj⟩)
    {A : LieAlgebroid I F V} (hA : ∀ i, A.restrict (U i) = B i) :
    A = glueOpenCover U hcover B hanchor hbracket :=
  eq_of_forall_restrict_eq U hcover fun i ↦
    (hA i).trans (glueOpenCover_restrict U hcover B hanchor hbracket i).symm

end

end Glue

end LieAlgebroid

end TauCeti
