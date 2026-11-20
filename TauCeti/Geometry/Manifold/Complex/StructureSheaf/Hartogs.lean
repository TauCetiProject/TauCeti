/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
import TauCeti.Geometry.Manifold.Complex.Hartogs
import TauCeti.Geometry.Manifold.ModelWithCorners.Perfect
import TauCeti.Topology.Perfect

/-!
# Hartogs' extension theorem for the holomorphic structure sheaf

On a boundaryless complex manifold `X` of complex dimension at least two, restricting sections of
`TauCeti.holomorphicStructureSheaf I X` via `TauCeti.holomorphicStructureSheaf.restrictAlgHom` along
an inclusion `V ≤ U` of open sets whose set difference `(U : Set X) \ (V : Set X)` is discrete is an
isomorphism of `ℂ`-algebras. In particular, removing a finite set or a single point from an open
set — or removing a point globally from `X` — does not change its `ℂ`-algebra of holomorphic
sections, with no Hausdorffness or second-countability assumption on `X`.

Composing with `TauCeti.holomorphicStructureSheaf.smoothSectionsEquiv` yields the corresponding ring
isomorphism for Mathlib's complex-smooth structure sheaf `smoothSheafCommRing I 𝓘(ℂ) X ℂ`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.restrictAlgHom_bijective_of_isDiscrete`: restriction along
  `V ≤ U` is bijective when `2 ≤ Module.finrank ℂ E` and `(U : Set X) \ (V : Set X)` is discrete.
* `TauCeti.holomorphicStructureSheaf.restrictAlgEquivOfIsDiscrete`,
  `TauCeti.holomorphicStructureSheaf.restrictAlgEquivOfFinite`,
  `TauCeti.holomorphicStructureSheaf.restrictSdiffSingletonAlgEquiv`,
  `TauCeti.holomorphicStructureSheaf.restrictComplSingletonAlgEquiv`: the resulting `ℂ`-algebra
  equivalences of holomorphic sections across closed discrete, finite, and singleton subsets.
* `TauCeti.holomorphicStructureSheaf.smoothRestrictRingEquivOfIsDiscrete`: the induced ring
  equivalence on sections of `smoothSheafCommRing I 𝓘(ℂ) X ℂ`.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I, §B,
  Theorem 5.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §4.
-/

public noncomputable section

open CategoryTheory Opposite Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Hartogs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

variable (I) in
/-- **Hartogs' theorem for sections of the holomorphic structure sheaf.** When
`2 ≤ Module.finrank ℂ E` and `V ≤ U` are open subsets of `X` such that `(U : Set X) \ (V : Set X)`
is discrete, restricting holomorphic sections from `U` to `V` is bijective. -/
theorem restrictAlgHom_bijective_of_isDiscrete (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X}
    (h : V ≤ U) (hUV : IsDiscrete ((U : Set X) \ (V : Set X))) :
    Function.Bijective (restrictAlgHom I h) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have := I.perfectSpace X
  have hsub : (V : Set X) ⊆ (U : Set X) := SetLike.coe_subset_coe.2 h
  have hsdiff : (U : Set X) \ ((U : Set X) \ (V : Set X)) = (V : Set X) := by
    rw [sdiff_sdiff_right_self, inf_eq_right.2 hsub]
  have hinter : (U : Set X) ∩ ((U : Set X) \ (V : Set X)) = (U : Set X) \ (V : Set X) :=
    inter_eq_right.2 sdiff_subset
  constructor
  · intro s₁ s₂ hs
    set F₁ : X → ℂ := Subtype.val.extend s₁ 0
    set F₂ : X → ℂ := Subtype.val.extend s₂ 0
    have hF₁_eq : ∀ x : U, F₁ x = s₁ x := fun x ↦ Subtype.val_injective.extend_apply s₁ 0 x
    have hF₂_eq : ∀ x : U, F₂ x = s₂ x := fun x ↦ Subtype.val_injective.extend_apply s₂ 0 x
    have hF₁_cont : ContinuousOn F₁ U :=
      continuousOn_iff_continuous_domRestrict.2
        ((contMDiff s₁).continuous.congr fun x ↦ (hF₁_eq x).symm)
    have hF₂_cont : ContinuousOn F₂ U :=
      continuousOn_iff_continuous_domRestrict.2
        ((contMDiff s₂).continuous.congr fun x ↦ (hF₂_eq x).symm)
    have heq_V : EqOn F₁ F₂ (V : Set X) := fun y hy ↦ by
      have hyV := congrArg (fun t : (holomorphicStructureSheaf I X).obj.obj (op V) ↦ t ⟨y, hy⟩) hs
      rw [restrictAlgHom_apply, restrictAlgHom_apply] at hyV
      dsimp only [Opens.inclusion] at hyV
      rw [Set.inclusion_mk (h := hsub), ← hF₁_eq ⟨y, h hy⟩, ← hF₂_eq ⟨y, h hy⟩] at hyV
      exact hyV
    have heq_U : EqOn F₁ F₂ U :=
      U.isOpen.eqOn_of_continuousOn_of_eqOn_sdiff_of_isDiscrete (S := (U : Set X) \ (V : Set X))
        (hinter.symm ▸ hUV) hF₁_cont hF₂_cont (hsdiff.symm ▸ heq_V)
    exact ext fun x ↦ (hF₁_eq x).symm.trans ((heq_U x.2).trans (hF₂_eq x))
  · intro t
    set f : X → ℂ := Subtype.val.extend t 0
    have hf : MDifferentiableOn I 𝓘(ℂ) f (V : Set X) := fun y hy ↦
      (((contMDiff t ⟨y, hy⟩).extend_subtypeVal 0).mdifferentiableAt (by simp))
        |>.mdifferentiableWithinAt
    obtain ⟨g, hg, hgf⟩ :=
      exists_mdifferentiableOn_eqOn_sdiff_of_isDiscrete hE U.isOpen
        (S := (U : Set X) \ (V : Set X)) (hsdiff.symm ▸ V.isOpen) (hinter.symm ▸ hUV)
        (hsdiff.symm ▸ hf)
    have hgfV : EqOn g f (V : Set X) := hsdiff ▸ hgf
    have hg_omega : ContMDiffOn I 𝓘(ℂ) ω g U := hg.contMDiffOn U.isOpen
    have hg_sub : ContMDiff I 𝓘(ℂ) ω (fun x : U ↦ g x) := fun x ↦
      (hg_omega.contMDiffAt (U.isOpen.mem_nhds x.2)).comp x contMDiff_subtype_val.contMDiffAt
    refine ⟨ofContMDiff (fun x : U ↦ g x) hg_sub, ext fun y ↦ ?_⟩
    rw [restrictAlgHom_apply, ofContMDiff_apply]
    dsimp only [Opens.inclusion]
    rw [Set.coe_inclusion hsub, hgfV y.2]
    exact Subtype.val_injective.extend_apply t 0 y

variable (I) in
/-- **Hartogs' algebra isomorphism of holomorphic sections across a discrete complement.** When
`2 ≤ Module.finrank ℂ E`, `V ≤ U`, and `(U : Set X) \ (V : Set X)` is discrete, restriction gives a
`ℂ`-algebra isomorphism `𝒪(U) ≃ₐ[ℂ] 𝒪(V)`. -/
def restrictAlgEquivOfIsDiscrete (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X} (h : V ≤ U)
    (hUV : IsDiscrete ((U : Set X) \ (V : Set X))) :
    (holomorphicStructureSheaf I X).obj.obj (op U) ≃ₐ[ℂ]
      (holomorphicStructureSheaf I X).obj.obj (op V) :=
  AlgEquiv.ofBijective (restrictAlgHom I h) (restrictAlgHom_bijective_of_isDiscrete I hE h hUV)

/-- The forward direction of `restrictAlgEquivOfIsDiscrete` evaluates a section on `V`. -/
@[simp]
theorem restrictAlgEquivOfIsDiscrete_apply (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X}
    (h : V ≤ U) (hUV : IsDiscrete ((U : Set X) \ (V : Set X)))
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : V) :
    (no_index (restrictAlgEquivOfIsDiscrete I hE h hUV s)) x = s (Opens.inclusion h x) := by
  rw [restrictAlgEquivOfIsDiscrete, AlgEquiv.ofBijective_apply, restrictAlgHom_apply]

/-- The Hartogs extension `(restrictAlgEquivOfIsDiscrete I hE h hUV).symm t` agrees with `t` on `V`.
-/
@[simp]
theorem restrictAlgEquivOfIsDiscrete_symm_apply_inclusion (hE : 2 ≤ Module.finrank ℂ E)
    {U V : Opens X} (h : V ≤ U) (hUV : IsDiscrete ((U : Set X) \ (V : Set X)))
    (t : (holomorphicStructureSheaf I X).obj.obj (op V)) (x : V) :
    (no_index ((restrictAlgEquivOfIsDiscrete I hE h hUV).symm t)) (Opens.inclusion h x) = t x := by
  have hx := congrArg (fun r : (holomorphicStructureSheaf I X).obj.obj (op V) ↦ r x)
    ((restrictAlgEquivOfIsDiscrete I hE h hUV).apply_symm_apply t)
  rwa [restrictAlgEquivOfIsDiscrete_apply] at hx

variable (I) in
/-- Forgetting the inverse of `restrictAlgEquivOfIsDiscrete` recovers `restrictAlgHom`. -/
@[simp]
theorem restrictAlgEquivOfIsDiscrete_toAlgHom (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X}
    (h : V ≤ U) (hUV : IsDiscrete ((U : Set X) \ (V : Set X))) :
    AlgEquiv.toAlgHom (R := ℂ) (A₁ := no_index _) (A₂ := no_index _)
      (restrictAlgEquivOfIsDiscrete I hE h hUV) = restrictAlgHom I h := by
  rw [restrictAlgEquivOfIsDiscrete, AlgEquiv.toAlgHom_ofBijective]

variable (I) in
/-- **Hartogs' algebra isomorphism of holomorphic sections across a finite complement.** When
`2 ≤ Module.finrank ℂ E`, `V ≤ U`, and `(U : Set X) \ (V : Set X)` is finite, restriction gives a
`ℂ`-algebra isomorphism `𝒪(U) ≃ₐ[ℂ] 𝒪(V)`. -/
def restrictAlgEquivOfFinite (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X} (h : V ≤ U)
    (hUV : ((U : Set X) \ (V : Set X)).Finite) :
    (holomorphicStructureSheaf I X).obj.obj (op U) ≃ₐ[ℂ]
      (holomorphicStructureSheaf I X).obj.obj (op V) := by
  have := I.t1Space X
  exact restrictAlgEquivOfIsDiscrete I hE h hUV.isDiscrete

/-- The forward direction of `restrictAlgEquivOfFinite` evaluates a section on `V`. -/
@[simp]
theorem restrictAlgEquivOfFinite_apply (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X} (h : V ≤ U)
    (hUV : ((U : Set X) \ (V : Set X)).Finite)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : V) :
    (no_index (restrictAlgEquivOfFinite I hE h hUV s)) x = s (Opens.inclusion h x) := by
  rw [restrictAlgEquivOfFinite, restrictAlgEquivOfIsDiscrete_apply]

/-- The Hartogs extension `(restrictAlgEquivOfFinite I hE h hUV).symm t` agrees with `t` on `V`. -/
@[simp]
theorem restrictAlgEquivOfFinite_symm_apply_inclusion (hE : 2 ≤ Module.finrank ℂ E)
    {U V : Opens X} (h : V ≤ U) (hUV : ((U : Set X) \ (V : Set X)).Finite)
    (t : (holomorphicStructureSheaf I X).obj.obj (op V)) (x : V) :
    (no_index ((restrictAlgEquivOfFinite I hE h hUV).symm t)) (Opens.inclusion h x) = t x := by
  rw [restrictAlgEquivOfFinite, restrictAlgEquivOfIsDiscrete_symm_apply_inclusion]

variable (I) in
/-- Forgetting the inverse of `restrictAlgEquivOfFinite` recovers `restrictAlgHom`. -/
@[simp]
theorem restrictAlgEquivOfFinite_toAlgHom (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X}
    (h : V ≤ U) (hUV : ((U : Set X) \ (V : Set X)).Finite) :
    AlgEquiv.toAlgHom (R := ℂ) (A₁ := no_index _) (A₂ := no_index _)
      (restrictAlgEquivOfFinite I hE h hUV) = restrictAlgHom I h := by
  rw [restrictAlgEquivOfFinite, restrictAlgEquivOfIsDiscrete_toAlgHom]

variable (I) in
/-- **Hartogs' algebra isomorphism of holomorphic sections across a point.** When
`2 ≤ Module.finrank ℂ E`, restriction gives a `ℂ`-algebra isomorphism `𝒪(U) ≃ₐ[ℂ] 𝒪(U \ {p})` for
every open set `U` and point `p : X`. -/
def restrictSdiffSingletonAlgEquiv (hE : 2 ≤ Module.finrank ℂ E) (U : Opens X) (p : X) :
    (holomorphicStructureSheaf I X).obj.obj (op U) ≃ₐ[ℂ]
      (holomorphicStructureSheaf I X).obj.obj
        (op (⟨(U : Set X) \ {p}, by have := I.t1Space X; exact U.isOpen.sdiff isClosed_singleton⟩ :
          Opens X)) :=
  restrictAlgEquivOfFinite I hE (SetLike.coe_subset_coe.1 sdiff_subset)
    ((finite_singleton p).subset fun _ hx ↦ by
      by_contra hyp
      exact hx.2 ⟨hx.1, hyp⟩)

/-- The forward direction of `restrictSdiffSingletonAlgEquiv` evaluates a section on `U \ {p}`. -/
@[simp]
theorem restrictSdiffSingletonAlgEquiv_apply (hE : 2 ≤ Module.finrank ℂ E) (U : Opens X) (p : X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U))
    (x : (⟨(U : Set X) \ {p}, by have := I.t1Space X; exact U.isOpen.sdiff isClosed_singleton⟩ :
      Opens X)) :
    (no_index (restrictSdiffSingletonAlgEquiv I hE U p s)) x = s ⟨x.1, x.2.1⟩ := by
  rw [restrictSdiffSingletonAlgEquiv, restrictAlgEquivOfFinite_apply]

/-- The Hartogs extension `(restrictSdiffSingletonAlgEquiv I hE U p).symm t` agrees with `t` away
from `p`. -/
@[simp]
theorem restrictSdiffSingletonAlgEquiv_symm_apply_inclusion (hE : 2 ≤ Module.finrank ℂ E)
    (U : Opens X) (p : X)
    (t : (holomorphicStructureSheaf I X).obj.obj
      (op (⟨(U : Set X) \ {p}, by have := I.t1Space X; exact U.isOpen.sdiff isClosed_singleton⟩ :
        Opens X)))
    (x : (⟨(U : Set X) \ {p}, by have := I.t1Space X; exact U.isOpen.sdiff isClosed_singleton⟩ :
      Opens X)) :
    (no_index ((restrictSdiffSingletonAlgEquiv I hE U p).symm t))
      (Opens.inclusion (SetLike.coe_subset_coe.1 sdiff_subset) x) = t x := by
  rw [restrictSdiffSingletonAlgEquiv, restrictAlgEquivOfFinite_symm_apply_inclusion]

variable (I) in
/-- Forgetting the inverse of `restrictSdiffSingletonAlgEquiv` recovers `restrictAlgHom`. -/
@[simp]
theorem restrictSdiffSingletonAlgEquiv_toAlgHom (hE : 2 ≤ Module.finrank ℂ E) (U : Opens X)
    (p : X) :
    AlgEquiv.toAlgHom (R := ℂ) (A₁ := no_index _) (A₂ := no_index _)
      (restrictSdiffSingletonAlgEquiv I hE U p) =
      restrictAlgHom I (SetLike.coe_subset_coe.1 sdiff_subset) := by
  rw [restrictSdiffSingletonAlgEquiv, restrictAlgEquivOfFinite_toAlgHom]

variable (I) in
/-- **Global Hartogs isomorphism of holomorphic sections across a point.** When
`2 ≤ Module.finrank ℂ E`, restriction identifies global holomorphic sections on `X` with holomorphic
sections on `{p}ᶜ`. -/
def restrictComplSingletonAlgEquiv (hE : 2 ≤ Module.finrank ℂ E) (p : X) :
    (holomorphicStructureSheaf I X).obj.obj (op (⊤ : Opens X)) ≃ₐ[ℂ]
      (holomorphicStructureSheaf I X).obj.obj
        (op (⟨{p}ᶜ, by have := I.t1Space X; exact isOpen_compl_singleton⟩ : Opens X)) :=
  restrictAlgEquivOfFinite I hE le_top
    ((finite_singleton p).subset fun _ hx ↦ by
      by_contra hyp
      exact hx.2 hyp)

/-- The forward direction of `restrictComplSingletonAlgEquiv` evaluates a global section on
`{p}ᶜ`. -/
@[simp]
theorem restrictComplSingletonAlgEquiv_apply (hE : 2 ≤ Module.finrank ℂ E) (p : X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op (⊤ : Opens X)))
    (x : (⟨{p}ᶜ, by have := I.t1Space X; exact isOpen_compl_singleton⟩ : Opens X)) :
    (no_index (restrictComplSingletonAlgEquiv I hE p s)) x = s ⟨x.1, trivial⟩ := by
  rw [restrictComplSingletonAlgEquiv, restrictAlgEquivOfFinite_apply]

/-- The global Hartogs extension `(restrictComplSingletonAlgEquiv I hE p).symm t` agrees with `t`
away from `p`. -/
@[simp]
theorem restrictComplSingletonAlgEquiv_symm_apply_inclusion (hE : 2 ≤ Module.finrank ℂ E) (p : X)
    (t : (holomorphicStructureSheaf I X).obj.obj
      (op (⟨{p}ᶜ, by have := I.t1Space X; exact isOpen_compl_singleton⟩ : Opens X)))
    (x : (⟨{p}ᶜ, by have := I.t1Space X; exact isOpen_compl_singleton⟩ : Opens X)) :
    (no_index ((restrictComplSingletonAlgEquiv I hE p).symm t))
      (Opens.inclusion le_top x) = t x := by
  rw [restrictComplSingletonAlgEquiv, restrictAlgEquivOfFinite_symm_apply_inclusion]

variable (I) in
/-- Forgetting the inverse of `restrictComplSingletonAlgEquiv` recovers `restrictAlgHom`. -/
@[simp]
theorem restrictComplSingletonAlgEquiv_toAlgHom (hE : 2 ≤ Module.finrank ℂ E) (p : X) :
    AlgEquiv.toAlgHom (R := ℂ) (A₁ := no_index _) (A₂ := no_index _)
      (restrictComplSingletonAlgEquiv I hE p) = restrictAlgHom I le_top := by
  rw [restrictComplSingletonAlgEquiv, restrictAlgEquivOfFinite_toAlgHom]

variable (I) in
/-- **Hartogs' ring isomorphism for Mathlib's complex-smooth structure sheaf.** When
`2 ≤ Module.finrank ℂ E`, `V ≤ U`, and `(U : Set X) \ (V : Set X)` is discrete, restriction along
`V ≤ U` gives a ring isomorphism on sections of `smoothSheafCommRing I 𝓘(ℂ) X ℂ`. -/
def smoothRestrictRingEquivOfIsDiscrete (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X} (h : V ≤ U)
    (hUV : IsDiscrete ((U : Set X) \ (V : Set X))) :
    (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U) ≃+*
      (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op V) :=
  (smoothSectionsEquiv I X U).symm.trans
    ((restrictAlgEquivOfIsDiscrete I hE h hUV).toRingEquiv.trans (smoothSectionsEquiv I X V))

/-- The forward direction of `smoothRestrictRingEquivOfIsDiscrete` evaluates a section on `V`. -/
@[simp]
theorem smoothRestrictRingEquivOfIsDiscrete_apply (hE : 2 ≤ Module.finrank ℂ E) {U V : Opens X}
    (h : V ≤ U) (hUV : IsDiscrete ((U : Set X) \ (V : Set X)))
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) (x : V) :
    (no_index (smoothRestrictRingEquivOfIsDiscrete I hE h hUV s)) x = s (Opens.inclusion h x) := by
  rw [smoothRestrictRingEquivOfIsDiscrete, RingEquiv.trans_apply, RingEquiv.trans_apply,
    smoothSectionsEquiv_apply, AlgEquiv.coe_toRingEquiv, restrictAlgEquivOfIsDiscrete_apply,
    smoothSectionsEquiv_symm_apply]

/-- The Hartogs extension `(smoothRestrictRingEquivOfIsDiscrete I hE h hUV).symm t` agrees with `t`
on `V`. -/
@[simp]
theorem smoothRestrictRingEquivOfIsDiscrete_symm_apply_inclusion (hE : 2 ≤ Module.finrank ℂ E)
    {U V : Opens X} (h : V ≤ U) (hUV : IsDiscrete ((U : Set X) \ (V : Set X)))
    (t : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op V)) (x : V) :
    (no_index ((smoothRestrictRingEquivOfIsDiscrete I hE h hUV).symm t))
      (Opens.inclusion h x) = t x := by
  have hx := congrArg (fun r : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op V) ↦ r x)
    ((smoothRestrictRingEquivOfIsDiscrete I hE h hUV).apply_symm_apply t)
  rwa [smoothRestrictRingEquivOfIsDiscrete_apply] at hx

end Hartogs

end TauCeti.holomorphicStructureSheaf
