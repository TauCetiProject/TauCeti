/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction

/-!
# Restriction of a Lie algebroid to an open subset

Let `A` be a Lie algebroid on a smooth vector bundle `V` of finite rank over a finite-dimensional
Hausdorff manifold `M`, and let `U` be an open subset of `M`. The restriction of `V` to `U` (the
pullback of `V` along the inclusion of `U`) carries a Lie algebroid structure
`TauCeti.LieAlgebroid.restrict A U`, whose anchor is the anchor of `A` read through the canonical
identification of the tangent spaces of `U` and `M`.

A smooth section over `U` agrees near each point of `U` with a global smooth section
(`ContMDiffSection.exists_eventually_eq_of_opens`), and the bracket of `A` is local
(`TauCeti.LieAlgebroid.bracket_apply_eq_of_eventuallyEq`). The bracket of two sections over `U`
at a point `x` is therefore the bracket at `x` of any two global sections agreeing with them near
`x` (`TauCeti.LieAlgebroid.restrict_bracket_apply_eq_of_eventuallyEq`). In particular,
restriction of global sections intertwines the brackets
(`TauCeti.LieAlgebroid.restrict_bracket_restrict`), so it is a morphism of Lie algebras
`TauCeti.LieAlgebroid.restrictLieHom` from the sections of `A` to those of its restriction.

## Main definitions

* `TauCeti.LieAlgebroid.restrict`: the restriction of a Lie algebroid to an open subset.
* `TauCeti.LieAlgebroid.restrictLieHom`: restriction of sections, as a Lie algebra morphism.

## Implementation notes

The fibre of the restricted bundle over `x : U` is, by definition of the pullback bundle, the
fibre `V x` of `V`, with the same algebraic structure. The algebraic laws of the restricted bracket
are reduced to those of `A` through restrictions of global sections, which keeps both sides of
each comparison in the fibres of the restricted bundle. The remaining comparisons of values in the
fibres of `V` and of the restriction use this definitional identification.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
-/

public section

noncomputable section

open Bundle Manifold TopologicalSpace Filter
open scoped ContDiff Topology

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : LieAlgebroid I F V) (U : Opens M)

/-- A global smooth section of `V` agreeing near `x` with a smooth section over `U`. -/
private def extendAt (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯)
    (x : U) : Cₛ^∞⟮I; F, V⟯ :=
  (ContMDiffSection.exists_eventually_eq_of_opens s x).choose

private theorem eventually_extendAt
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    ∀ᶠ y : U in 𝓝 x, extendAt U s x y = s y :=
  (ContMDiffSection.exists_eventually_eq_of_opens s x).choose_spec

/-- The bracket of two sections over `U` at `x`: the bracket at `x` of chosen global sections
agreeing with them near `x`. -/
private def restrictBracketAt
    (a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    V x :=
  A.bracket (extendAt U a x) (extendAt U b x) x

/-- The bracket of two sections over `U` at `x` is the bracket at `x` of any two global sections
agreeing with them near `x`. -/
private theorem restrictBracketAt_eq
    {a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {a' b' : Cₛ^∞⟮I; F, V⟯} (ha : ∀ᶠ y : U in 𝓝 x, a' y = a y)
    (hb : ∀ᶠ y : U in 𝓝 x, b' y = b y) :
    restrictBracketAt A U a b x = A.bracket a' b' x := by
  refine A.bracket_apply_eq_of_eventuallyEq ?_ ?_ <;>
    rw [← U.isOpenEmbedding'.map_nhds_eq x, eventually_map]
  · filter_upwards [eventually_extendAt U a x, ha] with y h h'
    exact h.trans h'.symm
  · filter_upwards [eventually_extendAt U b x, hb] with y h h'
    exact h.trans h'.symm

/-- Near `x`, the bracket of two sections over `U` is the bracket of any two global sections
agreeing with them near `x`. -/
private theorem eventually_restrictBracketAt_eq
    {a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {a' b' : Cₛ^∞⟮I; F, V⟯} (ha : ∀ᶠ y : U in 𝓝 x, a' y = a y)
    (hb : ∀ᶠ y : U in 𝓝 x, b' y = b y) :
    ∀ᶠ y : U in 𝓝 x, A.bracket a' b' y = restrictBracketAt A U a b y := by
  filter_upwards [eventually_eventually_nhds.2 ha, eventually_eventually_nhds.2 hb] with y ha hb
  exact (restrictBracketAt_eq A U ha hb).symm

/-- The bracket of two sections over `U`, as a smooth section over `U`. -/
private def restrictBracketSection
    (a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ where
  toFun := restrictBracketAt A U a b
  contMDiff_toFun x := by
    refine (((A.bracket (extendAt U a x) (extendAt U b x)).restrict U).contMDiff
      x).congr_of_eventuallyEq ?_
    filter_upwards [eventually_restrictBracketAt_eq A U (eventually_extendAt U a x)
      (eventually_extendAt U b x)] with y hy
    rw [← hy, ContMDiffSection.restrict_apply]

/-- The bracket of two sections over `U` at `x` is the value at `x` of the restriction of the
bracket of any two global sections agreeing with them near `x`. -/
private theorem restrictBracketSection_apply_eq_restrict
    {a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {a' b' : Cₛ^∞⟮I; F, V⟯} (ha : ∀ᶠ y : U in 𝓝 x, a' y = a y)
    (hb : ∀ᶠ y : U in 𝓝 x, b' y = b y) :
    restrictBracketSection A U a b x = (A.bracket a' b').restrict U x :=
  (restrictBracketAt_eq A U ha hb).trans (ContMDiffSection.restrict_apply _ U x).symm

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- Global sections agreeing near `x` with two sections over `U` have a sum agreeing near `x`
with their sum. -/
private theorem eventually_add_eq
    {s s' : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {t t' : Cₛ^∞⟮I; F, V⟯} (h : ∀ᶠ y : U in 𝓝 x, t y = s y)
    (h' : ∀ᶠ y : U in 𝓝 x, t' y = s' y) :
    ∀ᶠ y : U in 𝓝 x, (t + t') y = (s + s') y := by
  filter_upwards [h, h'] with y hy hy'
  rw [ContMDiffSection.coe_add, Pi.add_apply, hy, hy']
  -- The sum of the fibre of `V` over `y` is the sum of the fibre of the restriction.
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- A global section agreeing near `x` with a section over `U` has a multiple agreeing near `x`
with the same multiple. -/
private theorem eventually_smul_eq
    {s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {t : Cₛ^∞⟮I; F, V⟯} (c : ℝ) (h : ∀ᶠ y : U in 𝓝 x, t y = s y) :
    ∀ᶠ y : U in 𝓝 x, (c • t) y = (c • s) y := by
  filter_upwards [h] with y hy
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, hy]
  -- The scalar action on the fibre of `V` over `y` is that on the fibre of the restriction.
  rfl

/-- The bracket of sections over `U`, as an `ℝ`-bilinear map. Each law at `x` is the
corresponding law of the bracket of `A`, applied to global sections agreeing with the given
sections near `x`. -/
private def restrictBracket :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ :=
  LinearMap.mk₂ ℝ (restrictBracketSection A U)
    (fun a a' b ↦ ContMDiffSection.ext fun x ↦ by
      have ha := eventually_extendAt U a x
      have ha' := eventually_extendAt U a' x
      have hb := eventually_extendAt U b x
      simp only [ContMDiffSection.coe_add, Pi.add_apply,
        restrictBracketSection_apply_eq_restrict A U (eventually_add_eq U ha ha') hb,
        restrictBracketSection_apply_eq_restrict A U ha hb,
        restrictBracketSection_apply_eq_restrict A U ha' hb, map_add, LinearMap.add_apply,
        ContMDiffSection.restrict_add])
    (fun c a b ↦ ContMDiffSection.ext fun x ↦ by
      have ha := eventually_extendAt U a x
      have hb := eventually_extendAt U b x
      simp only [ContMDiffSection.coe_smul, Pi.smul_apply,
        restrictBracketSection_apply_eq_restrict A U (eventually_smul_eq U c ha) hb,
        restrictBracketSection_apply_eq_restrict A U ha hb, map_smul, LinearMap.smul_apply,
        ContMDiffSection.restrict_smul])
    (fun a b b' ↦ ContMDiffSection.ext fun x ↦ by
      have ha := eventually_extendAt U a x
      have hb := eventually_extendAt U b x
      have hb' := eventually_extendAt U b' x
      simp only [ContMDiffSection.coe_add, Pi.add_apply,
        restrictBracketSection_apply_eq_restrict A U ha (eventually_add_eq U hb hb'),
        restrictBracketSection_apply_eq_restrict A U ha hb,
        restrictBracketSection_apply_eq_restrict A U ha hb', map_add,
        ContMDiffSection.restrict_add])
    (fun c a b ↦ ContMDiffSection.ext fun x ↦ by
      have ha := eventually_extendAt U a x
      have hb := eventually_extendAt U b x
      simp only [ContMDiffSection.coe_smul, Pi.smul_apply,
        restrictBracketSection_apply_eq_restrict A U ha (eventually_smul_eq U c hb),
        restrictBracketSection_apply_eq_restrict A U ha hb, map_smul,
        ContMDiffSection.restrict_smul])

private theorem restrictBracket_apply
    (a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    restrictBracket A U a b x = restrictBracketAt A U a b x :=
  (rfl)

private theorem eventually_restrictBracket_eq
    {a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {a' b' : Cₛ^∞⟮I; F, V⟯} (ha : ∀ᶠ y : U in 𝓝 x, a' y = a y)
    (hb : ∀ᶠ y : U in 𝓝 x, b' y = b y) :
    ∀ᶠ y : U in 𝓝 x, A.bracket a' b' y = restrictBracket A U a b y :=
  (eventually_restrictBracketAt_eq A U ha hb).mono fun y hy ↦ hy.trans
    (restrictBracket_apply A U a b y).symm

private theorem restrictBracket_apply_eq_restrict
    {a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {a' b' : Cₛ^∞⟮I; F, V⟯} (ha : ∀ᶠ y : U in 𝓝 x, a' y = a y)
    (hb : ∀ᶠ y : U in 𝓝 x, b' y = b y) :
    restrictBracket A U a b x = (A.bracket a' b').restrict U x :=
  restrictBracketSection_apply_eq_restrict A U ha hb

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- The anchor of the restriction of `A` to `U`: the anchor of `A`, read through the canonical
identification of the tangent spaces of `U` and `M`. -/
private def restrictAnchor :
    Cₛ^∞⟮I; F →L[ℝ] E, fun x : U ↦
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ] TangentSpace I x⟯ where
  toFun x := (Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap ∘L A.anchor x
  contMDiff_toFun := by
    have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := F) (E := V)
      (f := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) (contMDiff_subtypeVal (I := I))
    refine (Manifold.contMDiff_hom_iff _).2 fun s hs x ↦ ?_
    -- Near `x`, the section `s` agrees with a global smooth section `t`, so its anchor field is
    -- the restriction of the anchor field of `t`.
    let t := extendAt U ⟨s, hs⟩ x
    refine (Manifold.contMDiffAt_restrictOpen_vectorField
      ((A.anchorField t).contMDiff (x : M))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_extendAt U ⟨s, hs⟩ x] with y hy
    simp only [ContMDiffSection.coeFn_mk] at hy
    rw [anchorField_apply, hy]
    -- The anchor of `A` applied to the vector `s y` of the fibre of `V` over `y`.
    rfl

private theorem restrictAnchor_apply (x : U)
    (v : ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x) :
    restrictAnchor A U x v = (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (A.anchor x v) :=
  (rfl)

/-- The restriction of a Lie algebroid to an open subset `U`: the restricted bundle, with the
anchor read through the identification of the tangent spaces of `U` and `M`, and the bracket of
global sections agreeing near each point with the given sections over `U`. -/
def restrict : LieAlgebroid I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) where
  anchor := restrictAnchor A U
  bracket := restrictBracket A U
  bracket_self a := ContMDiffSection.ext fun x ↦ by
    have ha := eventually_extendAt U a x
    simp only [restrictBracket_apply_eq_restrict A U ha ha, A.bracket_self,
      ContMDiffSection.restrict_zero]
  bracket_bracket a b c := ContMDiffSection.ext fun x ↦ by
    -- Each iterated bracket at `x` is the corresponding iterated bracket of the chosen global
    -- extensions at `x`, where the Jacobi identity of `A` applies.
    have ha := eventually_extendAt U a x
    have hb := eventually_extendAt U b x
    have hc := eventually_extendAt U c x
    simp only [ContMDiffSection.coe_add, Pi.add_apply,
      restrictBracket_apply_eq_restrict A U ha (eventually_restrictBracket_eq A U hb hc),
      restrictBracket_apply_eq_restrict A U (eventually_restrictBracket_eq A U ha hb) hc,
      restrictBracket_apply_eq_restrict A U hb (eventually_restrictBracket_eq A U ha hc),
      A.bracket_bracket (extendAt U a x), ContMDiffSection.restrict_add]
  bracket_smul_apply a b f x := by
    -- Extend `f` and the sections from a neighbourhood of `x` to `M`, and apply the Leibniz rule
    -- of `A` there.
    obtain ⟨g, hg⟩ := f.contMDiff.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := x)
    have ha := eventually_extendAt U a x
    have hb := eventually_extendAt U b x
    have hgb : ∀ᶠ y : U in 𝓝 x, (g • extendAt U b x) y = (f • b) y := by
      filter_upwards [hg, hb] with y hgy hby
      rw [ContMDiffSection.smul_apply, ContMDiffSection.smul_apply, ← hby, ← hgy]
      -- `(g ∘ Subtype.val) y` is `g y`, which acts on the fibre of `V` over `y` as on the
      -- fibre of the restriction.
      rfl
    have hderiv (v : TangentSpace I x) : mvfderiv I f x v = mvfderiv I g x v := by
      rw [← hg.mvfderiv_eq]
      exact (mvfderiv_apply_eq_mfderiv_apply _ _ v).trans
        ((Manifold.mfderiv_comp_subtype_val_apply v).trans
          (mvfderiv_apply_eq_mfderiv_apply (I := I) (g : M → ℝ) (x : M) v).symm)
    -- Express the brackets and the anchor through the extensions. The derivative of `f` is
    -- replaced while it is still applied to a tangent vector of `U`.
    simp only [restrictBracket_apply, restrictBracketAt_eq A U ha hgb,
      restrictBracketAt_eq A U ha hb, restrictAnchor_apply, hderiv]
    simp only [Manifold.tangentSpaceOpenEquiv_symm_apply, ← ha.self_of_nhds, ← hb.self_of_nhds,
      ← hg.self_of_nhds, Function.comp_apply]
    -- This is the Leibniz rule of `A` for the extensions, read in the fibre of `V` over `x`.
    exact A.bracket_smul_apply (extendAt U a x) (extendAt U b x) g x

/-- The anchor of the restriction of `A` to `U` is the anchor of `A`, read through the canonical
identification of the tangent spaces of `U` and `M`. -/
-- Normalize the bundled inclusion in the implicit pullback-fibre type for simplification.
@[simp]
theorem restrict_anchor_apply (x : U) (v : V x) :
    dsimp% only [ContinuousMap.coe_mk] ((A.restrict U).anchor x v =
      (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (A.anchor x v)) :=
  (rfl)

/-- The bracket of two sections over `U` at a point `x` is the bracket at `x` of any two global
sections agreeing with them near `x`. -/
theorem restrict_bracket_apply_eq_of_eventuallyEq
    {a b : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {a' b' : Cₛ^∞⟮I; F, V⟯} (ha : ∀ᶠ y : U in 𝓝 x, a' y = a y)
    (hb : ∀ᶠ y : U in 𝓝 x, b' y = b y) :
    (A.restrict U).bracket a b x = A.bracket a' b' x :=
  restrictBracketAt_eq A U ha hb

/-- Restriction to `U` intertwines the brackets of global sections and of sections over `U`. -/
-- Normalize the bundled inclusion in the implicit pullback-bundle type for simplification.
@[simp]
theorem restrict_bracket_restrict (a b : Cₛ^∞⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U) := by
  have h : (A.restrict U).bracket (a.restrict U) (b.restrict U) = (A.bracket a b).restrict U :=
    ContMDiffSection.ext fun x ↦ by
      rw [A.restrict_bracket_apply_eq_of_eventuallyEq U (a' := a) (b' := b)
        (.of_forall fun y ↦ (ContMDiffSection.restrict_apply a U y).symm)
        (.of_forall fun y ↦ (ContMDiffSection.restrict_apply b U y).symm),
        ContMDiffSection.restrict_apply]
  exact h

/-- Restriction of sections to `U`, as a morphism of Lie algebras from the sections of `A` to the
sections of its restriction to `U`. -/
def restrictLieHom : A.Sections →ₗ⁅ℝ⁆ (A.restrict U).Sections where
  toFun s := (A.restrict U).sectionsEquiv.symm ((A.sectionsEquiv s).restrict U)
  map_add' s t := by simp
  map_smul' c s := (A.restrict U).sectionsEquiv.injective <| by
    rw [RingHom.id_apply, LinearMapClass.map_smul_of_tower (A.restrict U).sectionsEquiv c,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearMapClass.map_smul_of_tower A.sectionsEquiv c, ContMDiffSection.restrict_smul]
  map_lie' {s t} := (A.restrict U).sectionsEquiv.injective <| by
    simp only [LinearEquiv.apply_symm_apply, sectionsEquiv_lie]
    exact (A.restrict_bracket_restrict U _ _).symm

/-- The restriction morphism sends a section of `A` to its restriction to `U`. -/
-- Normalize the bundled inclusion in the implicit pullback-bundle type for simplification.
@[simp]
theorem sectionsEquiv_restrictLieHom (s : A.Sections) :
    dsimp% only [ContinuousMap.coe_mk]
      ((A.restrict U).sectionsEquiv (A.restrictLieHom U s) = (A.sectionsEquiv s).restrict U) :=
  (A.restrict U).sectionsEquiv.apply_symm_apply _

end LieAlgebroid

end TauCeti
