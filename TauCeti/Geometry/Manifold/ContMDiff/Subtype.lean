/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.Convex.Segment
import TauCeti.Logic.Function.Extend

/-!
# Smoothness of maps into an open submanifold

A map into an open submanifold `U ⊆ M` is `C^n` exactly when its composition with the inclusion
`U → M` is `C^n`: the charts of `U` are restrictions of the charts of `M`, so smoothness is
insensitive to whether the codomain is read in the submanifold or in the ambient manifold.

Mathlib records this through `ContMDiffWithinAt.subtypeVal_comp_iff` within a set and through
`ContMDiffAt.subtypeVal_comp_iff` at a point, both at regularity `∞`. Since smoothness into a
manifold is a local invariant property at *every* regularity, the same characterizations hold for
arbitrary `n`; this file supplies them. In a convex open subset of a normed real space, these
characterizations show that the clamped affine segment is `C^n` on `[0, 1]` at every regularity.
In the other direction, a map out of an open submanifold that is `C^n` at a point stays `C^n`
there after extension to the whole manifold, as for Mathlib's `ContMDiff.extend_one`.

## Main results

* `TauCeti.ContMDiffWithinAt.subtypeVal_comp_iff`, `TauCeti.ContMDiffAt.subtypeVal_comp_iff`,
  `TauCeti.ContMDiffOn.subtypeVal_comp_iff`, and `TauCeti.ContMDiff.subtypeVal_comp_iff`: a map
  into an open submanifold is `C^n` (within a set, at a point, on a set, globally) iff its
  composition with the inclusion is.
* `ContMDiffAt.extend_subtypeVal`, `TauCeti.contMDiffAt_extend_subtypeVal_iff`,
  `ContMDiff.contMDiffOn_extend_subtypeVal`, `ContMDiff.contDiffOn_extend_subtypeVal`, and
  `ContDiffOn.contMDiff_comp_subtypeVal`: an extension to `M` of a map on an open submanifold is
  `C^n` at a point (or on the open set) exactly when the map is, and on an open subset of a normed
  space `ContMDiff` on `U` transfers back and forth with `ContDiffOn` on `(U : Set E)`.
* `ContMDiff.extend_one_of_mulTSupport_subset`, `ContMDiff.extend_zero_of_tsupport_subset`,
  `ContMDiff.extend_prodMap_subtypeVal_one`, and `ContMDiff.extend_prodMap_subtypeVal_zero`: global
  `C^n` extension by `1` (or `0`) of a `C^n` map on an open submanifold whose topological support
  lies in the submanifold, and of a `C^n` family `U × N → M'` trivial outside a closed subset of
  `U` in the first factor.
* `TopologicalSpace.Opens.contMDiffOn_convexSegment`: the affine segment in a convex open subset
  of a normed real space is smooth on `[0, 1]` at every regularity.

## References

* Used to lift ambient curves (e.g. straight segments) to `C¹` curves in open submanifolds;
  see `TauCeti.Geometry.Manifold.Riemannian.Convex`.
-/

public section

open ChartedSpace Manifold Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω}

/-- A map into an open submanifold is `C^n` within a set at a point iff its composition with the
inclusion is, at every regularity: smoothness is a local invariant property and the charts agree. -/
@[simp]
theorem ContMDiffWithinAt.subtypeVal_comp_iff (U : Opens M') (f : M → U) (s : Set M)
    (x : M) :
    ContMDiffWithinAt I I' n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I I' n f s x :=
  liftPropWithinAt_subtypeVal_comp_iff ..

/-- A map into an open submanifold is `C^n` at a point iff its composition with the inclusion
is, at every regularity. -/
@[simp]
theorem ContMDiffAt.subtypeVal_comp_iff (U : Opens M') (f : M → U) (x : M) :
    ContMDiffAt I I' n (Subtype.val ∘ f) x ↔ ContMDiffAt I I' n f x :=
  ContMDiffWithinAt.subtypeVal_comp_iff U f Set.univ x

/-- A map into an open submanifold is `C^n` on a set iff its composition with the inclusion is,
at every regularity. -/
@[simp]
theorem ContMDiffOn.subtypeVal_comp_iff (U : Opens M') (f : M → U) (s : Set M) :
    ContMDiffOn I I' n (Subtype.val ∘ f) s ↔ ContMDiffOn I I' n f s :=
  ⟨fun h a ha => (ContMDiffWithinAt.subtypeVal_comp_iff U f s a).mp (h a ha),
   fun h a ha => (ContMDiffWithinAt.subtypeVal_comp_iff U f s a).mpr (h a ha)⟩

/-- A map into an open submanifold is `C^n` iff its composition with the inclusion is, at every
regularity. -/
@[simp]
theorem ContMDiff.subtypeVal_comp_iff (U : Opens M') (f : M → U) :
    ContMDiff I I' n (Subtype.val ∘ f) ↔ ContMDiff I I' n f :=
  ⟨fun h _ => (ContMDiffWithinAt.subtypeVal_comp_iff U f Set.univ _).mp (h _),
   fun h _ => (ContMDiffWithinAt.subtypeVal_comp_iff U f Set.univ _).mpr (h _)⟩

end TauCeti

section Extend

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω}

/-- **Extending a map from an open submanifold.** If `g : U → M'` is `C^n` at a point `x` of the
open set `U`, then any extension of `g` to all of `M`, for instance by zero, is `C^n` at `x`: it
agrees with `g` on the neighbourhood `U` of `x`. -/
theorem ContMDiffAt.extend_subtypeVal {U : Opens M} {g : U → M'} {x : U}
    (hg : ContMDiffAt I I' n g x) (e : M → M') :
    ContMDiffAt I I' n (Subtype.val.extend g e) x := by
  rw [← contMDiffAt_subtype_iff]
  refine hg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
  exact Subtype.val_injective.extend_apply g e z

/-- A map on an open submanifold `U` is `C^n` at a point of `U` exactly when any of its extensions
to all of `M` is. -/
theorem TauCeti.contMDiffAt_extend_subtypeVal_iff {U : Opens M} {g : U → M'} {x : U} (e : M → M') :
    ContMDiffAt I I' n (Subtype.val.extend g e) x ↔ ContMDiffAt I I' n g x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.extend_subtypeVal e⟩
  rw [← contMDiffAt_subtype_iff] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦
    (Subtype.val_injective.extend_apply g e z).symm)

/-- If `g : U → M'` is `C^n` on an open submanifold `U ⊆ M`, then any extension of `g` to `M` is
`C^n` on `(U : Set M)`. -/
theorem ContMDiff.contMDiffOn_extend_subtypeVal {U : Opens M} {g : U → M'}
    (hg : ContMDiff I I' n g) (e : M → M') :
    ContMDiffOn I I' n (Subtype.val.extend g e) (U : Set M) := fun x hx ↦
  ((hg ⟨x, hx⟩).extend_subtypeVal e).contMDiffWithinAt

/-- If `g : U → E'` is `C^n` on an open subset `U` of a normed space `E`, then any extension of
`g` to `E` is `C^n` on `(U : Set E)` in the normed-space sense. -/
theorem ContMDiff.contDiffOn_extend_subtypeVal {U : Opens E} {g : U → E'}
    (hg : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n g) (e : E → E') :
    ContDiffOn 𝕜 n (Subtype.val.extend g e) (U : Set E) :=
  contMDiffOn_iff_contDiffOn.1 (hg.contMDiffOn_extend_subtypeVal e)

/-- If `g : E → E'` is `C^n` on an open subset `U` of a normed space `E`, then its restriction
`g ∘ Subtype.val : U → E'` to the open submanifold `U` is `C^n`. -/
theorem ContDiffOn.contMDiff_comp_subtypeVal {U : Opens E} {g : E → E'}
    (hg : ContDiffOn 𝕜 n g (U : Set E)) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n (g ∘ (Subtype.val : U → E)) :=
  (contMDiffOn_iff_contDiffOn.2 hg).comp_contMDiff contMDiff_subtypeVal fun x ↦ x.property

/-- If the topological multiplicative support of `Subtype.val.extend g 1` is contained in the open
set `U` and `g : U → M'` is `C^n`, then `Subtype.val.extend g 1` is `C^n` on all of `M`. -/
@[to_additive /-- If the topological support of `Subtype.val.extend g 0` is contained in the open
set `U` and `g : U → M'` is `C^n`, then `Subtype.val.extend g 0` is `C^n` on all of `M`. -/]
theorem ContMDiff.extend_one_of_mulTSupport_subset [One M'] {U : Opens M} {g : U → M'}
    (hg : ContMDiff I I' n g) (hsupp : mulTSupport (Subtype.val.extend g 1) ⊆ (U : Set M)) :
    ContMDiff I I' n (Subtype.val.extend g 1) :=
  contMDiff_of_mulTSupport fun x hx ↦ (hg ⟨x, hsupp hx⟩).extend_subtypeVal 1

/-- **Extending a smooth family from an open submanifold.** If `g : U × N → M'` is `C^n` on the
product of an open subset `U ⊆ M` with a manifold `N` and equals `1` outside `s ×ˢ univ` for a
closed set `s ⊆ U`, then extending `g` by `1` outside `U ×ˢ univ` yields a `C^n` map on `M × N`. -/
@[to_additive ContMDiff.extend_prodMap_subtypeVal_zero
/-- **Extending a smooth family by zero from an open submanifold.** If `g : U × N → M'` is `C^n` on
the product of an open subset `U ⊆ M` with a manifold `N` and vanishes outside `s ×ˢ univ` for a
closed set `s ⊆ U`, then extending `g` by `0` outside `U ×ˢ univ` yields a `C^n` map on
`M × N`. -/]
theorem ContMDiff.extend_prodMap_subtypeVal_one
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] [One M']
    {U : Opens M} {s : Set M} (hs : IsClosed s) (hsU : s ⊆ U) {g : U × N → M'}
    (hg : ContMDiff (I.prod I'') I' n g)
    (hsupp : ∀ x : U, (x : M) ∉ s → ∀ y : N, g (x, y) = 1) :
    ContMDiff (I.prod I'') I' n ((Prod.map (Subtype.val : U → M) id).extend g 1) := by
  let V : Opens (M × N) := ⟨(U : Set M) ×ˢ univ, U.isOpen.prod isOpen_univ⟩
  let g' : V → M' := fun v ↦ g (⟨v.val.1, v.property.1⟩, v.val.2)
  have hπ₁ : ContMDiff (I.prod I'') I n (fun v : V ↦ (⟨v.val.1, v.property.1⟩ : U)) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff U _).1 (contMDiff_fst.comp contMDiff_subtypeVal)
  have hg' : ContMDiff (I.prod I'') I' n g' :=
    hg.comp (hπ₁.prodMk (contMDiff_snd.comp contMDiff_subtypeVal))
  have hext : (Prod.map (Subtype.val : U → M) id).extend g 1 = Subtype.val.extend g' 1 := by
    ext ⟨x, y⟩
    by_cases hx : x ∈ U
    · exact ((Subtype.val_injective.prodMap Function.injective_id).extend_apply g 1
        (⟨x, hx⟩, y)).trans (Subtype.val_injective.extend_apply g' 1 ⟨(x, y), hx, trivial⟩).symm
    · rw [Function.extend_prodMap_subtypeVal_eq g 1 y fun hxU ↦ (hx hxU).elim,
        Function.extend_subtypeVal_eq g' 1 fun hxy ↦ (hx hxy.1).elim]
  rw [hext]
  refine hg'.extend_one_of_mulTSupport_subset (Subset.trans (b := s ×ˢ univ)
    (closure_minimal (fun ⟨x, y⟩ hr ↦ ⟨?_, trivial⟩) (hs.prod isClosed_univ))
    (prod_mono hsU Subset.rfl))
  by_contra hxs
  exact hr (hext ▸ Function.extend_prodMap_subtypeVal_eq g 1 y fun hxU ↦ hsupp ⟨x, hxU⟩ hxs y)

end Extend

namespace TopologicalSpace.Opens

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (U : Opens F) {n : ℕ∞ω}

/-- The clamped affine segment in a convex open subset is `C^n` on `[0, 1]` for every `n`. -/
theorem contMDiffOn_convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) :
    ContMDiffOn (M' := U) 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n
      ((U : Set F).convexSegment hU x y) (Icc 0 1) := by
  apply (TauCeti.ContMDiffOn.subtypeVal_comp_iff U _ (Icc 0 1)).mp
  apply ContMDiffOn.congr _ ((U : Set F).convexSegment_val_eqOn hU x y)
  exact contMDiffOn_iff_contDiffOn.mpr (AffineMap.contDiff_lineMap _ _).contDiffOn

end TopologicalSpace.Opens
