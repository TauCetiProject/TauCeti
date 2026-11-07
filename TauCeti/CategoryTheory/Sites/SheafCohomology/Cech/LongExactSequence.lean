/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# The long exact coefficient sequence of Čech cohomology

A sequence of presheaves whose Čech complexes are short exact on every chosen family gives
a long exact sequence of Čech cohomology for any system of families with exact colimits.
With exact products of the required sizes, `shortExact_map_cechComplexFunctor` supplies this
hypothesis from short exactness on family intersections; no exactness at other objects is needed.
For an objectwise short exact sequence `hS : S.ShortExact`, use
`fun j ↦ hS.map_of_exact (cechComplexFunctor (E j).obj)` throughout the API below.
In particular this applies to the point-neighborhood cover system and module coefficients on any
topological space. A short exact sequence of sheaves need not be exact on sections.

The connecting map `cechCohomologyδ` is induced by the native connecting maps of the
fixed-family complexes. `cechCohomologyι_app_δ` identifies it on every structure map, and
`cechCohomologyδ_naturality` gives naturality in short exact coefficient sequences.
The three exactness lemmas describe all positions in the long exact sequence, whose
initial map in degree zero is monic. These sequences permit comparison of a presheaf
with its sheafification using its locally zero kernel and cokernel.

The construction follows the Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY).
It uses Mathlib's `ShortComplex.ShortExact.δ` and its naturality, and exactness of colimits;
there is no choice of cocycle lifts in the cover colimit.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w t v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i))
  {S : ShortComplex (Cᵒᵖ ⥤ A)}
  (hS : ∀ j, (S.map (cechComplexFunctor (E j).obj)).ShortExact)

private def cechRefinementShortComplexHom {i j : J} (φ : E j ⟶ E i) :
    S.map (cechComplexFunctor (E i).obj) ⟶ S.map (cechComplexFunctor (E j).obj) where
  τ₁ := cechComplexMap S.X₁ φ
  τ₂ := cechComplexMap S.X₂ φ
  τ₃ := cechComplexMap S.X₃ φ
  comm₁₂ := (cechComplexMap_naturality S.X₁ S.f φ).symm
  comm₂₃ := (cechComplexMap_naturality S.X₂ S.g φ).symm

/-- The fixed-family connecting maps form a morphism of diagrams on the refinement preorder. -/
private def cechCohomologyδDiagram (n : ℕ) :
    (cechCohomologyDiagram A E hE n).flip.obj S.X₃ ⟶
      (cechCohomologyDiagram A E hE (n + 1)).flip.obj S.X₁ where
  app j := (hS j).δ n (n + 1) rfl
  naturality {i j} f := by
    dsimp only [Functor.flip_obj_map]
    rw [cechCohomologyDiagram_map A E hE n f (hE (leOfHom f)).some,
      cechCohomologyDiagram_map A E hE (n + 1) f (hE (leOfHom f)).some,
      cechComplexHomologyMap_app, cechComplexHomologyMap_app]
    exact (HomologicalComplex.HomologySequence.δ_naturality
      (cechRefinementShortComplexHom E (hE (leOfHom f)).some)
      (hS i) (hS j) n (n + 1) rfl).symm

variable [HasColimitsOfShape J A]

/-- The connecting map for a coefficient sequence whose Čech complexes on the chosen families
are short exact. On each family it is induced by the native connecting map of complexes. -/
def cechCohomologyδ (n : ℕ) :
    (cechCohomology A E hE n).obj S.X₃ ⟶ (cechCohomology A E hE (n + 1)).obj S.X₁ :=
  colim.map (cechCohomologyδDiagram E hE hS n)

/-- The connecting map agrees with the fixed-family connecting map on every colimit insertion.
-/
@[reassoc (attr := simp)]
theorem cechCohomologyι_app_δ (n : ℕ) (j : J) :
    (cechCohomologyι E hE n j).app S.X₃ ≫ cechCohomologyδ E hE hS n =
      (hS j).δ n (n + 1) rfl ≫
        (cechCohomologyι E hE (n + 1) j).app S.X₁ := by
  rw [cechCohomologyι_app, cechCohomologyι_app, cechCohomologyδ]
  exact colimit.ι_map (cechCohomologyδDiagram E hE hS n) j

/-- Connecting maps are natural in coefficient sequences whose Čech complexes on the chosen
families are short exact. -/
@[reassoc]
theorem cechCohomologyδ_naturality {T : ShortComplex (Cᵒᵖ ⥤ A)}
    (hT : ∀ j, (T.map (cechComplexFunctor (E j).obj)).ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    cechCohomologyδ E hE hS n ≫ (cechCohomology A E hE (n + 1)).map φ.τ₁ =
      (cechCohomology A E hE n).map φ.τ₃ ≫ cechCohomologyδ E hE hT n := by
  have h : cechCohomologyδDiagram E hE hS n ≫
      (cechCohomologyDiagram A E hE (n + 1)).flip.map φ.τ₁ =
        (cechCohomologyDiagram A E hE n).flip.map φ.τ₃ ≫
          cechCohomologyδDiagram E hE hT n := by
    ext j
    exact HomologicalComplex.HomologySequence.δ_naturality
      ((cechComplexFunctor (E j).obj).mapShortComplex.map φ)
      (hS j) (hT j) n (n + 1) rfl
  simpa only [cechCohomologyδ, cechCohomology, Functor.comp_map, Functor.map_comp]
    using congrArg colim.map h

/-- Two successive arrows at the source of the connecting map compose to zero. -/
@[reassoc (attr := simp)]
theorem cechCohomology_comp_δ (n : ℕ) :
    (cechCohomology A E hE n).map S.g ≫ cechCohomologyδ E hE hS n = 0 := by
  have h : (cechCohomologyDiagram A E hE n).flip.map S.g ≫
      cechCohomologyδDiagram E hE hS n = 0 := by
    ext j
    exact (hS j).comp_δ n (n + 1) rfl
  exact (colim.map_comp _ _).symm.trans ((congrArg colim.map h).trans (colim.map_zero _ _))

/-- Two successive arrows at the target of the connecting map compose to zero. -/
@[reassoc (attr := simp)]
theorem cechCohomologyδ_comp (n : ℕ) :
    cechCohomologyδ E hE hS n ≫ (cechCohomology A E hE (n + 1)).map S.f = 0 := by
  have h : cechCohomologyδDiagram E hE hS n ≫
      (cechCohomologyDiagram A E hE (n + 1)).flip.map S.f = 0 := by
    ext j
    exact (hS j).δ_comp n (n + 1) rfl
  exact (colim.map_comp _ _).symm.trans ((congrArg colim.map h).trans (colim.map_zero _ _))

variable [HasExactColimitsOfShape J A]

include hS in
/-- Exactness at the middle coefficient in every degree. -/
theorem cechCohomology_exact₂ (n : ℕ) : (S.map (cechCohomology A E hE n)).Exact := by
  have h : (S.map (cechCohomologyDiagram A E hE n).flip).Exact := by
    apply ShortComplex.exact_of_forall_evaluation
    intro j
    exact (hS j).homology_exact₂ n
  exact h.map colim

/-- Exactness at the right coefficient, immediately before the connecting map. -/
theorem cechCohomology_exact₃ (n : ℕ) :
    (ShortComplex.mk ((cechCohomology A E hE n).map S.g)
      (cechCohomologyδ E hE hS n) (cechCohomology_comp_δ E hE hS n)).Exact := by
  let D : ShortComplex (J ⥤ A) := ShortComplex.mk
    ((cechCohomologyDiagram A E hE n).flip.map S.g)
    (cechCohomologyδDiagram E hE hS n) (by
      ext j
      exact (hS j).comp_δ n (n + 1) rfl)
  have hD : D.Exact := by
    apply ShortComplex.exact_of_forall_evaluation
    intro j
    exact (hS j).homology_exact₃ n (n + 1) rfl
  exact hD.map colim

/-- Exactness at the left coefficient in positive degree, immediately after the connecting map.
-/
theorem cechCohomology_exact₁ (n : ℕ) :
    (ShortComplex.mk (cechCohomologyδ E hE hS n)
      ((cechCohomology A E hE (n + 1)).map S.f) (cechCohomologyδ_comp E hE hS n)).Exact := by
  let D : ShortComplex (J ⥤ A) := ShortComplex.mk
    (cechCohomologyδDiagram E hE hS n)
    ((cechCohomologyDiagram A E hE (n + 1)).flip.map S.f) (by
      ext j
      exact (hS j).δ_comp n (n + 1) rfl)
  have hD : D.Exact := by
    apply ShortComplex.exact_of_forall_evaluation
    intro j
    exact (hS j).homology_exact₁ n (n + 1) rfl
  exact hD.map colim

include hS in
/-- The coefficient sequence starts with a monomorphism on degree-zero Čech cohomology. -/
theorem mono_cechCohomology_map_zero : Mono ((cechCohomology A E hE 0).map S.f) := by
  have (j : J) : Mono (((cechCohomologyDiagram A E hE 0).flip.map S.f).app j) := by
    have : Mono ((cechComplexFunctor (E j).obj).map S.f) :=
      (hS j).mono_f
    exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 (by simp)
  have := NatTrans.mono_of_mono_app ((cechCohomologyDiagram A E hE 0).flip.map S.f)
  exact Functor.map_mono colim _

include hS in
/-- A coefficient sequence with short exact fixed-family Čech complexes induces an
isomorphism on the right map if its left coefficient has zero Čech cohomology in every degree. -/
theorem isIso_cechCohomology_map_g_of_isZero
    (h₁ : ∀ n, IsZero ((cechCohomology A E hE n).obj S.X₁)) (n : ℕ) :
    IsIso ((cechCohomology A E hE n).map S.g) := by
  have : Mono ((cechCohomology A E hE n).map S.g) :=
    (ShortComplex.exact_iff_mono _ ((h₁ n).eq_zero_of_src _)).1
      (cechCohomology_exact₂ E hE hS n)
  have : Epi ((cechCohomology A E hE n).map S.g) :=
    (ShortComplex.exact_iff_epi _ ((h₁ (n + 1)).eq_zero_of_tgt _)).1
      (cechCohomology_exact₃ E hE hS n)
  exact isIso_of_mono_of_epi _

include hS in
/-- A coefficient sequence with short exact fixed-family Čech complexes induces an
isomorphism on the left map if its right coefficient has zero Čech cohomology in every degree. -/
theorem isIso_cechCohomology_map_f_of_isZero
    (h₃ : ∀ n, IsZero ((cechCohomology A E hE n).obj S.X₃)) (n : ℕ) :
    IsIso ((cechCohomology A E hE n).map S.f) := by
  have : Epi ((cechCohomology A E hE n).map S.f) :=
    (ShortComplex.exact_iff_epi _ ((h₃ n).eq_zero_of_tgt _)).1
      (cechCohomology_exact₂ E hE hS n)
  have : Mono ((cechCohomology A E hE n).map S.f) := by
    cases n with
    | zero => exact mono_cechCohomology_map_zero E hE hS
    | succ n =>
      exact (ShortComplex.exact_iff_mono _ ((h₃ n).eq_zero_of_src _)).1
        (cechCohomology_exact₁ E hE hS n)
  exact isIso_of_mono_of_epi _

end TauCeti.CategoryTheory
