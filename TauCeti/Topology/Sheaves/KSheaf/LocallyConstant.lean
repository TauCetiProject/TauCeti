/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.KSheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import TauCeti.Topology.LocallyConstant.Extend

/-!
# The K-sheaf of locally constant functions

A K-presheaf on a Hausdorff space `X` is a presheaf on the compact subsets of `X`
(`TopCat.KPresheaf`). It is a K-sheaf (`TopCat.KPresheaf.IsKSheaf`) when its value on `∅` is
terminal, its values on `K₁ ∪ K₂` are the pullbacks of its values on `K₁` and `K₂` over
`K₁ ∩ K₂`, and its value on each compact `K` is the colimit of its values on the compact
neighbourhoods of `K`. On a locally compact Hausdorff space K-sheaves are another description of
sheaves (Pardon, Lemma A.1.8), and Pardon's construction of virtual fundamental cycles works with
complexes of K-presheaves.

This file constructs the basic example, the K-sheaf avatar of the constant sheaf with fibre `M`:
the K-presheaf `K ↦ LocallyConstant K M` of locally constant functions, with restriction of
functions as restriction maps (`TopCat.KPresheaf.locallyConstant`). On a locally compact Hausdorff
space it is a K-sheaf (`TopCat.KPresheaf.isKSheaf_locallyConstant`):

* there is exactly one function on `∅`;
* locally constant functions on two compact sets that agree on their intersection glue to a
  locally constant function on the union, since compact sets are closed;
* a locally constant function on `K` extends to a compact neighbourhood of `K`, and two that agree
  on `K` agree on a smaller compact neighbourhood (`LocallyConstant.exists_isCompact_comap_eq`,
  `LocallyConstant.exists_isCompact_comap_eq_comap`), so the colimit over the compact
  neighbourhoods of `K` is computed by restriction to `K`.

Local compactness is needed for the last axiom: a point with no compact neighbourhood has an empty
diagram of neighbourhoods, whose colimit is empty, while the locally constant functions on the
point form a copy of `M`. Local constancy is needed for the last axiom too: the continuous real
functions do not form a K-sheaf, since two of them may agree on `K` without agreeing on any
neighbourhood of `K`.

For an `R`-module `M` the locally constant functions form a K-presheaf of `R`-modules
(`TopCat.KPresheaf.locallyConstantModule`), which is a K-sheaf as well
(`TopCat.KPresheaf.isKSheaf_locallyConstantModule`): the forgetful functor from `R`-modules to
types reflects limits and filtered colimits, and the diagrams of compact neighbourhoods are
filtered.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.1, Definitions A.1.1–A.1.4.
* J. Lurie, *Higher Topos Theory*, Section 7.3.4.
-/

public section

universe u v

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

namespace TopCat.KPresheaf

section Types

variable (X : TopCat.{u}) (M : Type v)

/-- The K-presheaf of locally constant functions with values in `M`: its value on a compact set
`K` is `LocallyConstant K M`, and its restriction maps restrict functions to smaller compact sets.
-/
abbrev locallyConstant : KPresheaf (Type (max u v)) X where
  obj K := LocallyConstant (K.unop : Set X) M
  map f := TypeCat.ofHom fun g =>
    g.comap ⟨inclusion (leOfHom f.unop), continuous_inclusion (leOfHom f.unop)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {X M}

@[simp]
theorem locallyConstant_map_apply {K L : (Compacts X)ᵒᵖ} (f : K ⟶ L)
    (g : LocallyConstant (K.unop : Set X) M) (x : (L.unop : Set X)) :
    ((locallyConstant X M).map f g : LocallyConstant (L.unop : Set X) M) x =
      g (inclusion (leOfHom f.unop) x) :=
  rfl

/-- On a locally compact Hausdorff space, the locally constant functions with values in a type `M`
form a K-sheaf. -/
theorem isKSheaf_locallyConstant [T2Space X] [LocallyCompactSpace X] :
    (locallyConstant X M).IsKSheaf where
  nonempty_isTerminal := by
    have : IsEmpty ((⊥ : Compacts X) : Set X) := ⟨fun x => x.2⟩
    exact ⟨(Types.isTerminalEquivUnique _).symm
      { default := ⟨isEmptyElim, IsLocallyConstant.of_constant _ isEmptyElim⟩
        uniq := fun _ => LocallyConstant.ext isEmptyElim }⟩
  isPullback {K₁ K₂ K₃ K₄} sq := by
    rw [Types.isPullback_iff]
    refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp], ?_, ?_⟩
    · -- Two functions on `K₄ = K₂ ∪ K₃` agreeing on `K₂` and on `K₃` are equal.
      rintro (f g : LocallyConstant (K₄ : Set X) M) ⟨h₂, h₃⟩
      refine LocallyConstant.ext fun ⟨x, hx⟩ => ?_
      rw [← sq.sup_eq] at hx
      rcases hx with hx | hx
      · exact congr($h₂ ⟨x, hx⟩)
      · exact congr($h₃ ⟨x, hx⟩)
    · -- Functions on `K₂` and `K₃` agreeing on `K₁ = K₂ ∩ K₃` glue along the closed cover.
      rintro (f₂ : LocallyConstant (K₂ : Set X) M) (f₃ : LocallyConstant (K₃ : Set X) M) h
      classical
      have h₀ : (K₄ : Set X) ⊆ K₂ ∪ K₃ := by rw [← sq.sup_eq]; rfl
      have hf : ∀ x (hx : x ∈ (K₂ : Set X) ∩ K₃), f₂ ⟨x, hx.1⟩ = f₃ ⟨x, hx.2⟩ := fun x hx => by
        have hx₁ : x ∈ (K₁ : Set X) := by rw [← sq.inf_eq]; exact hx
        exact congr($h ⟨x, hx₁⟩)
      have h₂ := K₂.isCompact.isClosed
      have h₃ := K₃.isCompact.isClosed
      refine ⟨LocallyConstant.piecewise' h₀ h₂ h₃ f₂ f₃ hf, ?_, ?_⟩
      · exact LocallyConstant.ext fun x => LocallyConstant.piecewise'_apply_left h₀ h₂ h₃ f₂ f₃ hf
          ⟨x, sq.le₂₄ x.2⟩ x.2
      · exact LocallyConstant.ext fun x => LocallyConstant.piecewise'_apply_right h₀ h₂ h₃ f₂ f₃ hf
          ⟨x, sq.le₃₄ x.2⟩ x.2
  nonempty_isColimit_coconeOfCompacts K := by
    have hnhds : ∀ {L : Set X} (hL : IsCompact L), (K : Set X) ⊆ interior L →
        (⟨L, hL⟩ : Compacts X) ∈ K.compactNhds := fun _ hKL x =>
      mem_interior_iff_mem_nhds.1 (hKL x.2)
    refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
    · intro (f : LocallyConstant (K : Set X) M)
      obtain ⟨L, hL, hKL, g, hg⟩ := LocallyConstant.exists_isCompact_comap_eq K.isCompact f
      exact ⟨op ⟨_, hnhds hL hKL⟩, g, hg.symm⟩
    · rintro ⟨L⟩ (f : LocallyConstant (L.1 : Set X) M) (g : LocallyConstant (L.1 : Set X) M) h
      obtain ⟨L', hL', hKL', hL'L, hfg⟩ := LocallyConstant.exists_isCompact_comap_eq_comap
        K.isCompact (fun x hx => mem_interior_iff_mem_nhds.2 (L.2 ⟨x, hx⟩)) f g h
      exact ⟨op ⟨_, hnhds hL' hKL'⟩, (homOfLE hL'L).op, hfg⟩

end Types

section Module

variable (X : TopCat.{u}) (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The K-presheaf of `R`-modules of locally constant functions with values in an `R`-module `M`.
Its underlying K-presheaf of types is `TopCat.KPresheaf.locallyConstant X M`. -/
abbrev locallyConstantModule : KPresheaf (ModuleCat.{u} R) X where
  obj K := ModuleCat.of R (LocallyConstant (K.unop : Set X) M)
  map f := ModuleCat.ofHom <|
    LocallyConstant.comapₗ R ⟨inclusion (leOfHom f.unop), continuous_inclusion (leOfHom f.unop)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying K-presheaf of types of `TopCat.KPresheaf.locallyConstantModule X R M` is
`TopCat.KPresheaf.locallyConstant X M`. -/
theorem locallyConstantModule_comp_forget :
    locallyConstantModule X R M ⋙ forget (ModuleCat.{u} R) = locallyConstant X M :=
  rfl

variable {X R M}

/-- On a locally compact Hausdorff space, the locally constant functions with values in an
`R`-module `M` form a K-sheaf of `R`-modules. -/
theorem isKSheaf_locallyConstantModule [T2Space X] [LocallyCompactSpace X] :
    (locallyConstantModule X R M).IsKSheaf where
  nonempty_isTerminal := by
    have : IsEmpty ((⊥ : Compacts X) : Set X) := ⟨fun x => x.2⟩
    have : Subsingleton (LocallyConstant ((⊥ : Compacts X) : Set X) M) :=
      ⟨fun _ _ => LocallyConstant.ext isEmptyElim⟩
    exact ⟨(ModuleCat.isZero_of_subsingleton _).isTerminal⟩
  isPullback sq := by
    refine IsPullback.of_map (forget (ModuleCat.{u} R)) ?_
      ((isKSheaf_locallyConstant (M := M)).isPullback sq)
    rw [← Functor.map_comp, ← Functor.map_comp]
  nonempty_isColimit_coconeOfCompacts K := by
    -- The compact neighbourhoods of `K` form a nonempty codirected set, so the diagram is filtered
    -- and the forgetful functor reflects its colimits.
    have : Nonempty K.compactNhds := by
      obtain ⟨L, hL, hKL, -⟩ := exists_compact_between K.isCompact isOpen_univ (subset_univ _)
      exact ⟨⟨⟨L, hL⟩, fun x => mem_interior_iff_mem_nhds.1 (hKL x.2)⟩⟩
    have : ReflectsColimitsOfShape (K.compactNhds)ᵒᵖ (forget (ModuleCat.{u} R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact ⟨isColimitOfReflects (forget (ModuleCat.{u} R))
      ((isKSheaf_locallyConstant (M := M)).nonempty_isColimit_coconeOfCompacts K).some⟩

end Module

end TopCat.KPresheaf
