/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExactCochains

/-!
# The long exact sequence of continuous cohomology in every degree

A short exact sequence `0 → A → B → C → 0` of discrete `G`-modules over a compact topological
group `G` induces a long exact sequence

```text
⋯ → Hⁿ(G, A) → Hⁿ(G, B) → Hⁿ(G, C) --δ--> Hⁿ⁺¹(G, A) → Hⁿ⁺¹(G, B) → ⋯
```

of Mathlib's canonical continuous cohomology `continuousCohomology n`, in every degree `n`. This
file constructs the connecting map `δ` and proves exactness at the three repeating nodes and
naturality of `δ` in the short exact sequence.

The construction starts from the short complex of homogeneous-cochain complexes
`TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact`, which becomes a short
exact sequence of cochain complexes of `ℤ`-modules after forgetting topologies. `TopModuleCat ℤ`
is not abelian, so the snake lemma (`CategoryTheory.ShortComplex.ShortExact.δ`) is applied in
`ModuleCat ℤ`. The
forgetful functor `TopModuleCat ℤ ⥤ ModuleCat ℤ` is both a left and a right adjoint, so it
preserves homology, and `CategoryTheory.ShortComplex.mapHomologyIso` identifies the homology of the
forgotten complexes with the underlying modules of continuous cohomology. This produces `δ` as a
linear map. It is continuous because continuous cohomology of a discrete representation of a
compact group is discrete (`TauCeti.discreteTopology_continuousCohomology`), so `δ` is a morphism
in `TopModuleCat ℤ`. The same identification transports the exactness statements and the
naturality square from `ModuleCat ℤ`.

The coefficient maps are the named `TauCeti.ContinuousCohomology.coeffMap` of the canonical
coefficient maps `TauCeti.ofDiscreteModuleMap`, the form in which a consumer meets them.

## Main definitions

* `TauCeti.ContCohomology.DiscreteShortExact.delta`: the connecting map
  `Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)` in `TopModuleCat ℤ`.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.forget₂_map_delta`: `δ` is the snake-lemma
  connecting map of the forgotten cochain sequence, read through `mapHomologyIso`.
* `TauCeti.ContCohomology.DiscreteShortExact.longExact_exact₁`,
  `longExact_exact₂` and `longExact_exact₃`: exactness at `Hⁿ⁺¹(G, A)`, `Hⁿ(G, B)` and
  `Hⁿ(G, C)`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_naturality`: a morphism of short exact
  sequences commutes with `δ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.3.2) (the long exact cohomology sequence of a short exact sequence of discrete modules).
-/

public section

open CategoryTheory

namespace TauCeti

namespace ContinuousCohomology

open _root_.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- After forgetting topologies, the coefficient map `Hⁿ(G, X) ⟶ Hⁿ(G, Y)` is the map induced on
the homology of the forgotten homogeneous-cochain complexes, conjugated by the identifications
`CategoryTheory.ShortComplex.mapHomologyIso` of that homology with the underlying modules of
continuous cohomology. -/
theorem forget₂_map_coeffMap {X Y : TopRep.{v} R G} (f : X ⟶ Y) (n : ℕ) :
    (forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap f n) =
      ((X.homogeneousCochains.sc n).mapHomologyIso
          (forget₂ (TopModuleCat R) (ModuleCat R))).inv ≫
        HomologicalComplex.homologyMap
          (((forget₂ (TopModuleCat R) (ModuleCat R)).mapHomologicalComplex _).map
            ((continuousCochainsFunctor R G).map f)) n ≫
          ((Y.homogeneousCochains.sc n).mapHomologyIso
            (forget₂ (TopModuleCat R) (ModuleCat R))).hom := by
  rw [coeffMap_def]
  exact (Iso.eq_inv_comp _).2 (ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map ((continuousCochainsFunctor R G).map f))
    (forget₂ (TopModuleCat R) (ModuleCat R))).symm

end ContinuousCohomology

namespace ContCohomology.DiscreteShortExact

open _root_.ContinuousCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- **The connecting map of continuous cohomology** `δ : Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)` attached to a
short exact sequence `0 → A → B → C → 0` of discrete `G`-modules over a compact group, in every
degree `n`. It is the snake-lemma connecting map of the short exact sequence of homogeneous
continuous cochains (`forget₂_map_delta`); it is continuous because its source is discrete. -/
noncomputable def delta (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ G C) ⟶
      continuousCohomology (n + 1) (ofDiscreteModule ℤ G A) :=
  TopModuleCat.ofHom
    ⟨(((S.continuousCochainsShortExact.X₃.sc n).mapHomologyIso
          (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).inv ≫
        S.continuousCochainsShortExact_shortExact.δ n (n + 1) rfl ≫
          ((S.continuousCochainsShortExact.X₁.sc (n + 1)).mapHomologyIso
            (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).hom).hom,
      -- The expected type presents the source through Mathlib's homology data rather than as
      -- `continuousCohomology n _`, so the discreteness instance is supplied by name.
      @continuous_of_discreteTopology _ _ (discreteTopology_continuousCohomology _ n) _ _ _⟩

/-- After forgetting topologies, `δ` is the connecting map of the snake lemma for the short exact
sequence of homogeneous-cochain complexes, conjugated by the identifications
`CategoryTheory.ShortComplex.mapHomologyIso` of the homology of the forgotten complexes with the
underlying modules of continuous cohomology. -/
theorem forget₂_map_delta (n : ℕ) :
    (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map (S.delta n) =
      ((S.continuousCochainsShortExact.X₃.sc n).mapHomologyIso
          (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).inv ≫
        S.continuousCochainsShortExact_shortExact.δ n (n + 1) rfl ≫
          ((S.continuousCochainsShortExact.X₁.sc (n + 1)).mapHomologyIso
            (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).hom :=
  (rfl)

omit [CompactSpace G] [ContinuousSMul G B] in
/-- Exactness of a pair of composable maps of topological modules follows from exactness of the
maps of modules they become after forgetting topologies, up to conjugation by isomorphisms. -/
private theorem exact_of_forget₂_map_eq {X₁ X₂ X₃ : TopModuleCat.{u} ℤ} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {Y₁ Y₂ Y₃ : ModuleCat.{u} ℤ} {f' : Y₁ ⟶ Y₂} {g' : Y₂ ⟶ Y₃}
    {e₁ : Y₁ ≅ (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj X₁}
    {e₂ : Y₂ ≅ (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj X₂}
    {e₃ : Y₃ ≅ (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj X₃}
    (hf : (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map f = e₁.inv ≫ f' ≫ e₂.hom)
    (hg : (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map g = e₂.inv ≫ g' ≫ e₃.hom)
    (h : Function.Exact f' g') : Function.Exact f g :=
  Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e₁.toLinearEquiv) (e₂ := e₂.toLinearEquiv)
    (e₃ := e₃.toLinearEquiv) (g₁₂ := f.hom.toLinearMap) (g₂₃ := g.hom.toLinearMap)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq e₁).1 hf.symm).symm)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq e₂).1 hg.symm).symm) h

/-- **Exactness at `Hⁿ⁺¹(G, A)`**: the image of the connecting map `Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)` is
the kernel of the coefficient map induced by `A → B`. -/
theorem longExact_exact₁ (n : ℕ) :
    Function.Exact (S.delta n)
      (coeffMap (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 1)) :=
  exact_of_forget₂_map_eq (S.forget₂_map_delta n) (forget₂_map_coeffMap _ _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (S.continuousCochainsShortExact_shortExact.homology_exact₁ n (n + 1) rfl))

omit [CompactSpace G] in
/-- **Exactness at `Hⁿ(G, B)`**: the image of the coefficient map induced by `A → B` is the
kernel of the coefficient map induced by `B → C`. No connecting map is involved, so local
compactness of `G` suffices. -/
theorem longExact_exact₂ [LocallyCompactSpace G] (n : ℕ) :
    Function.Exact (coeffMap (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) n)
      (coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n) :=
  exact_of_forget₂_map_eq (forget₂_map_coeffMap _ _) (forget₂_map_coeffMap _ _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (S.continuousCochainsShortExact_shortExact.homology_exact₂ n))

/-- **Exactness at `Hⁿ(G, C)`**: the image of the coefficient map induced by `B → C` is the
kernel of the connecting map `Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)`. -/
theorem longExact_exact₃ (n : ℕ) :
    Function.Exact (coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n)
      (S.delta n) :=
  exact_of_forget₂_map_eq (forget₂_map_coeffMap _ _) (S.forget₂_map_delta n)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (S.continuousCochainsShortExact_shortExact.homology_exact₃ n (n + 1) rfl))

/-- The connecting map kills the image of `Hⁿ(G, B) → Hⁿ(G, C)`. -/
@[reassoc (attr := simp)]
theorem coeffMap_proj_comp_delta (n : ℕ) :
    coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n ≫ S.delta n = 0 :=
  ConcreteCategory.hom_ext _ _ fun x ↦ (S.longExact_exact₃ n).apply_apply_eq_zero x

/-- The coefficient map `Hⁿ⁺¹(G, A) → Hⁿ⁺¹(G, B)` kills the image of the connecting map. -/
@[reassoc (attr := simp)]
theorem delta_comp_coeffMap_incl (n : ℕ) :
    S.delta n ≫ coeffMap (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 1) =
      0 :=
  ConcreteCategory.hom_ext _ _ fun x ↦ (S.longExact_exact₁ n).apply_apply_eq_zero x

variable {A' : Type u} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [DistribMulAction G A']
  {B' : Type u} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
    [DistribMulAction G B'] [ContinuousSMul G B']
  {C' : Type u} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction G C']

/-- **Naturality of the connecting map.** Equivariant maps `fA`, `fB`, `fC` from one short exact
sequence of discrete `G`-modules to another, commuting with the inclusions and the projections,
carry the connecting map of the first sequence to that of the second:

```text
Hⁿ(G, C) ---δ---> Hⁿ⁺¹(G, A)
   |                  |
   fC                 fA
   v                  v
Hⁿ(G, C') --δ--> Hⁿ⁺¹(G, A')
```
-/
theorem delta_naturality (T : DiscreteShortExact G A' B' C')
    (fA : A →+[G] A') (fB : B →+[G] B') (fC : C →+[G] C')
    (hincl : ∀ a : A, fB (S.incl a) = T.incl (fA a))
    (hproj : ∀ b : B, fC (S.proj b) = T.proj (fB b)) (n : ℕ) :
    S.delta n ≫
        coeffMap (ofDiscreteModuleMap fA.toAddMonoidHom.toIntLinearMap fun g a ↦ map_smul fA g a)
          (n + 1) =
      coeffMap (ofDiscreteModuleMap fC.toAddMonoidHom.toIntLinearMap fun g c ↦ map_smul fC g c)
          n ≫
        T.delta n := by
  set τA := ofDiscreteModuleMap fA.toAddMonoidHom.toIntLinearMap fun g a ↦ map_smul fA g a
  set τC := ofDiscreteModuleMap fC.toAddMonoidHom.toIntLinearMap fun g c ↦ map_smul fC g c
  -- The morphism of coefficient short complexes, and its image on forgotten cochain complexes.
  let φ : S.toShortComplex ⟶ T.toShortComplex :=
    ShortComplex.homMk τA
      (ofDiscreteModuleMap fB.toAddMonoidHom.toIntLinearMap fun g b ↦ map_smul fB g b) τC
      (TopRep.hom_ext <| DFunLike.ext _ _ fun a : A ↦ (hincl a).symm)
      (TopRep.hom_ext <| DFunLike.ext _ _ fun b : B ↦ (hproj b).symm)
  let Φ := ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapHomologicalComplex _).mapShortComplex.map
    ((continuousCochainsFunctor ℤ G).mapShortComplex.map φ)
  -- Three commuting squares in `ModuleCat ℤ`: the snake-lemma naturality in the middle, and the
  -- coefficient maps read through `mapHomologyIso` on either side.
  have h := HomologicalComplex.HomologySequence.δ_naturality Φ
    S.continuousCochainsShortExact_shortExact T.continuousCochainsShortExact_shortExact n (n + 1)
    rfl
  have h₁ : ((S.continuousCochainsShortExact.X₁.sc (n + 1)).mapHomologyIso
          (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).hom ≫
        (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map (coeffMap τA (n + 1)) =
      HomologicalComplex.homologyMap Φ.τ₁ (n + 1) ≫
        ((T.continuousCochainsShortExact.X₁.sc (n + 1)).mapHomologyIso
          (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).hom :=
    (Iso.eq_inv_comp _).1 (forget₂_map_coeffMap τA (n + 1))
  have h₃ : ((S.continuousCochainsShortExact.X₃.sc n).mapHomologyIso
          (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).inv ≫
        HomologicalComplex.homologyMap Φ.τ₃ n =
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map (coeffMap τC n) ≫
        ((T.continuousCochainsShortExact.X₃.sc n).mapHomologyIso
          (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).inv :=
    (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans (forget₂_map_coeffMap τC n).symm)
  apply (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map_injective
  rw [Functor.map_comp, Functor.map_comp, forget₂_map_delta, forget₂_map_delta]
  -- Paste the three squares. `Category.assoc` cannot be rewritten here because the objects of the
  -- two sides agree only after unfolding `continuousCohomology`.
  exact ((CommSq.mk h₃).horiz_comp ((CommSq.mk h).horiz_comp (CommSq.mk h₁))).w

end ContCohomology.DiscreteShortExact

end TauCeti
