/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import TauCeti.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# `Tor` from a projective presentation of length one

Mathlib's `CategoryTheory.Tor C n` derives the tensor product in its second variable:
`((Tor C n).obj X).obj M` is `Lₙ(X ⊗ -)(M)`. Let `S : 0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` be a short exact
sequence with `P₁` and `P₀` projective. Then

* `Tor₁(X, M)` is the kernel of `X ◁ S.f : X ⊗ P₁ ⟶ X ⊗ P₀`
  (`CategoryTheory.ShortComplex.ShortExact.torOneIsoKernel`), naturally in `X` and in maps of
  such presentations, sending the homology class of a cycle of `X ⊗ -` applied to the resolution
  to that cycle;
* `Torₙ(X, M)` vanishes for `n ≥ 2`
  (`CategoryTheory.ShortComplex.ShortExact.isZero_Tor_add_two`).

Over a principal ideal domain the boundaries and cycles of a complex of free modules are free, so
the homology `Hⱼ` has the presentation `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ ⟶ 0`. This identifies the `Tor₁` terms
of the Künneth short exact sequence `0 ⟶ ⨁ Hᵢ ⊗ Hⱼ ⟶ Hₙ(K ⊗ L) ⟶ ⨁ Tor₁(Hᵢ, Hⱼ) ⟶ 0` with the
kernels of `Hᵢ(K) ⊗ Bⱼ(L) ⟶ Hᵢ(K) ⊗ Zⱼ(L)`.

These are the specializations to `X ⊗ -` of the computation of left derived functors in
`TauCeti.CategoryTheory.Abelian.LeftDerived`.

For Mathlib's `CategoryTheory.Tor' C n`, which derives the first variable instead,
`((Tor' C n).obj X).obj Y` is `Lₙ(- ⊗ Y)(X)`. The file records two facts about it in the
underived variable `Y`: it is an additive functor of `Y`, and `Tor'ₙ₊₁(X, 𝟙_ C)` vanishes
(`CategoryTheory.isZero_Tor'_succ_tensorUnit`), since `- ⊗ 𝟙_ C` is isomorphic to the identity
functor and hence exact.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4 and 3.1, and Theorem 3.6.3 for
  the Künneth formula.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [HasProjectiveResolutions C] {S S' : ShortComplex C}

namespace ShortComplex.ShortExact

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- For a projective presentation `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0`, `Tor₁(X, M)` is the kernel of
`X ◁ S.f : X ⊗ P₁ ⟶ X ⊗ P₀`. -/
def torOneIsoKernel (X : C) : ((Tor C 1).obj X).obj S.X₃ ≅ kernel (X ◁ S.f) :=
  hS.leftDerivedOneIsoKernel ((tensoringLeft C).obj X)

/-- The identification of `Tor₁(X, M)` with the kernel of `X ◁ S.f` sends the homology class of a
cycle of `X ⊗ -` applied to the resolution to that cycle. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_isoLeftDerivedObj_inv_comp_torOneIsoKernel_hom_comp_ι (X : C) :
    ((((tensoringLeft C).obj X).mapHomologicalComplex _).obj S.resolutionComplex).homologyπ 1 ≫
      (hS.projectiveResolution.isoLeftDerivedObj ((tensoringLeft C).obj X) 1).inv ≫
        (hS.torOneIsoKernel X).hom ≫ kernel.ι (X ◁ S.f) =
      ((((tensoringLeft C).obj X).mapHomologicalComplex _).obj S.resolutionComplex).iCycles 1 :=
  hS.homologyπ_comp_isoLeftDerivedObj_inv_comp_leftDerivedOneIsoKernel_hom_comp_ι _

include hS in
/-- `Torₙ(X, M)` vanishes for `n ≥ 2` when `M` has a projective presentation of length one. -/
lemma isZero_Tor_add_two (X : C) (n : ℕ) : IsZero (((Tor C (n + 2)).obj X).obj S.X₃) :=
  hS.isZero_leftDerived_add_two _ n

/-- The identification of `Tor₁(X, M)` with the kernel of `X ◁ S.f` is natural in `X`. -/
@[reassoc]
lemma Tor_map_app_comp_torOneIsoKernel_hom {X Y : C} (f : X ⟶ Y) :
    ((Tor C 1).map f).app S.X₃ ≫ (hS.torOneIsoKernel Y).hom =
      (hS.torOneIsoKernel X).hom ≫
        kernel.map (X ◁ S.f) (Y ◁ S.f) (f ▷ S.X₁) (f ▷ S.X₂) (whisker_exchange f S.f) :=
  hS.leftDerived_app_comp_leftDerivedOneIsoKernel_hom _ ((tensoringLeft C).map f)

variable {hS} (hS' : S'.ShortExact) [Projective S'.X₁] [Projective S'.X₂]

/-- The identification of `Tor₁(X, M)` with the kernel of `X ◁ S.f` is natural in maps of
projective presentations. -/
@[reassoc]
lemma Tor_obj_map_comp_torOneIsoKernel_hom (X : C) (φ : S ⟶ S') :
    ((Tor C 1).obj X).map φ.τ₃ ≫ (hS'.torOneIsoKernel X).hom =
      (hS.torOneIsoKernel X).hom ≫
        kernel.map (X ◁ S.f) (X ◁ S'.f) (X ◁ φ.τ₁) (X ◁ φ.τ₂)
          (by simp only [← whiskerLeft_comp, φ.comm₁₂]) :=
  leftDerived_map_comp_leftDerivedOneIsoKernel_hom _ hS' φ

end ShortComplex.ShortExact

/-- `Tor'` is additive in its second variable, the one that is not derived. -/
instance (X : C) (n : ℕ) : ((Tor' C n).obj X).Additive where
  map_add := by
    simp only [Tor'_obj_map, Functor.map_add, NatTrans.leftDerived_add, NatTrans.app_add]
    -- The two sums are formed in the hom-groups of `((Tor' C n).obj X).obj Y` and of
    -- `(((tensoringRight C).obj Y).leftDerived n).obj X`, which agree by definition
    -- (`CategoryTheory.Tor'_obj_obj`).
    exact fun {_ _ _ _} ↦ rfl

/-- The higher `Tor'` groups with the tensor unit as second variable vanish: `- ⊗ 𝟙_ C` is
isomorphic to the identity functor, so it is exact. -/
lemma isZero_Tor'_succ_tensorUnit (X : C) (n : ℕ) :
    IsZero (((Tor' C (n + 1)).obj X).obj (𝟙_ C)) := by
  have : ((tensoringRight C).obj (𝟙_ C)).PreservesHomology :=
    Functor.preservesHomology_of_map_exact _ fun S hS ↦
      ShortComplex.exact_of_iso (S.mapNatIso (rightUnitorNatIso C)).symm hS
  exact Functor.isZero_leftDerived_succ _ X n

end CategoryTheory
