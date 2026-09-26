/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
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
naturality of `δ` in compatible pairs: along a continuous homomorphism `φ : H →ₜ* G` of compact
groups, maps of short exact sequences that are equivariant along `φ` carry `δ` over `G` to `δ`
over `H`. Morphisms of short exact sequences over `G` and restriction to a compact subgroup are the
two instances stated here; inflation is stated in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.ConnectingMap`.

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
naturality squares from `ModuleCat ℤ`.

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
* `TauCeti.ContCohomology.DiscreteShortExact.delta_map`: the maps induced by compatible pairs
  commute with `δ`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_naturality`: a morphism of short exact
  sequences commutes with `δ`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_res`: restriction to a compact subgroup
  commutes with `δ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.3.2) (the long exact cohomology sequence of a short exact sequence of discrete modules) and
  Ch. I, §5 (compatibility of the connecting maps with change of groups).
-/

public section

open CategoryTheory

namespace TauCeti

namespace ContCohomology.DiscreteShortExact

open _root_.ContinuousCohomology _root_.TauCeti _root_.TauCeti.ContinuousCohomology

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
            (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).hom := by
  -- The `rfl` tactic checks the definitional unfolding once; the term `(rfl)` checks it twice,
  -- once while propagating the expected type and once more against it (0.3 s).
  rfl

/-- **Exactness at `Hⁿ⁺¹(G, A)`**: the image of the connecting map `Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)` is
the kernel of the coefficient map induced by `A → B`. -/
theorem longExact_exact₁ (n : ℕ) :
    Function.Exact (S.delta n)
      (coeffMap (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 1)) :=
  TopModuleCat.exact_of_forget₂_map_eq (S.forget₂_map_delta n) (forget₂_map_coeffMap _ _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (S.continuousCochainsShortExact_shortExact.homology_exact₁ n (n + 1) rfl))

omit [CompactSpace G] in
/-- **Exactness at `Hⁿ(G, B)`**: the image of the coefficient map induced by `A → B` is the
kernel of the coefficient map induced by `B → C`. No connecting map is involved, so local
compactness of `G` suffices. -/
theorem longExact_exact₂ [LocallyCompactSpace G] (n : ℕ) :
    Function.Exact (coeffMap (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) n)
      (coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n) :=
  TopModuleCat.exact_of_forget₂_map_eq (forget₂_map_coeffMap _ _) (forget₂_map_coeffMap _ _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (S.continuousCochainsShortExact_shortExact.homology_exact₂ n))

/-- **Exactness at `Hⁿ(G, C)`**: the image of the coefficient map induced by `B → C` is the
kernel of the connecting map `Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)`. -/
theorem longExact_exact₃ (n : ℕ) :
    Function.Exact (coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n)
      (S.delta n) :=
  TopModuleCat.exact_of_forget₂_map_eq (forget₂_map_coeffMap _ _) (S.forget₂_map_delta n)
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

section Map

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {A' : Type u} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [DistribMulAction H A']
  {B' : Type u} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
    [DistribMulAction H B'] [ContinuousSMul H B']
  {C' : Type u} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction H C']

omit [CompactSpace G] [CompactSpace H] in
/-- Compatible pairs `(φ, f)` and `(φ, f')` and equivariant coefficient maps `i` and `j`
induce a commuting square of homogeneous-cochain complexes when `f' (i m) = j (f m)` for every
`m : M`. -/
private theorem cochainsMap_comp_cochainsMap_id
    {M M' : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M']
    {N N' : Type u} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction H N] [AddCommGroup N'] [TopologicalSpace N'] [DiscreteTopology N']
    [DistribMulAction H N'] (φ : H →ₜ* G)
    (f : M →+ N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (f' : M' →+ N') (hf' : ∀ (h : H) (m : M'), f' (φ h • m) = h • f' m)
    (i : M →+ M') (hi : ∀ (g : G) (m : M), i (g • m) = g • i m)
    (j : N →+ N') (hj : ∀ (h : H) (n : N), j (h • n) = h • j n)
    (hcomm : ∀ m : M, f' (i m) = j (f m)) :
    cochainsMap φ (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap hf) ≫
        (continuousCochainsFunctor ℤ H).map (ofDiscreteModuleMap j.toIntLinearMap hj) =
      (continuousCochainsFunctor ℤ G).map (ofDiscreteModuleMap i.toIntLinearMap hi) ≫
        cochainsMap φ (ofDiscreteModulePair (φ : H →* G) f'.toIntLinearMap hf') :=
  -- Both compositions act along `φ`; equality reduces to the coefficient maps on elements.
  (cochainsMap_comp φ (ContinuousMonoidHom.id H) _ _).symm.trans <|
    (congrArg (cochainsMap φ) <| by
      ext (m : M)
      exact (congrArg j
        (ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap hf m)).trans <|
          (hcomm m).symm.trans
            (ofDiscreteModulePair_hom_apply (φ : H →* G) f'.toIntLinearMap hf' (i m)).symm).trans <|
    cochainsMap_comp (ContinuousMonoidHom.id G) φ _ _

/-- **Naturality of the connecting map in compatible pairs.** Let `φ : H →ₜ* G` be a continuous
homomorphism of compact groups, `S` a short exact sequence of discrete `G`-modules and `T` one of
discrete `H`-modules, and let `fA`, `fB`, `fC` be additive maps from the terms of `S` to those of
`T` that are equivariant along `φ` (`f (φ h • x) = h • f x`) and commute with the inclusions and
the projections. Then the maps these compatible pairs induce on continuous cohomology carry the
connecting map of `S` to that of `T`:

```text
Hⁿ(G, C) ---δ---> Hⁿ⁺¹(G, A)
   |                  |
 (φ, fC)            (φ, fA)
   v                  v
Hⁿ(H, C') --δ--> Hⁿ⁺¹(H, A')
```

Coefficient maps (`delta_naturality`, at `φ = id`), restriction (`delta_res`) and inflation
(`delta_infl`) are instances of this square. -/
@[reassoc]
theorem delta_map (T : DiscreteShortExact H A' B' C') (φ : H →ₜ* G)
    (fA : A →+ A') (fB : B →+ B') (fC : C →+ C')
    (hA : ∀ (h : H) (a : A), fA (φ h • a) = h • fA a)
    (hB : ∀ (h : H) (b : B), fB (φ h • b) = h • fB b)
    (hC : ∀ (h : H) (c : C), fC (φ h • c) = h • fC c)
    (hincl : ∀ a : A, fB (S.incl a) = T.incl (fA a))
    (hproj : ∀ b : B, fC (S.proj b) = T.proj (fB b)) (n : ℕ) :
    S.delta n ≫ map φ (ofDiscreteModulePair (φ : H →* G) fA.toIntLinearMap hA) (n + 1) =
      map φ (ofDiscreteModulePair (φ : H →* G) fC.toIntLinearMap hC) n ≫ T.delta n := by
  -- The morphism of short exact sequences of homogeneous-cochain complexes given by the three
  -- compatible pairs, and its image on the forgotten complexes.
  let ψ : S.toShortComplex.map (continuousCochainsFunctor ℤ G) ⟶
      T.toShortComplex.map (continuousCochainsFunctor ℤ H) :=
    ShortComplex.homMk
      (cochainsMap φ (ofDiscreteModulePair (φ : H →* G) fA.toIntLinearMap hA))
      (cochainsMap φ (ofDiscreteModulePair (φ : H →* G) fB.toIntLinearMap hB))
      (cochainsMap φ (ofDiscreteModulePair (φ : H →* G) fC.toIntLinearMap hC))
      (cochainsMap_comp_cochainsMap_id φ fA hA fB hB S.incl S.incl_equivariant T.incl
        T.incl_equivariant hincl)
      (cochainsMap_comp_cochainsMap_id φ fB hB fC hC S.proj S.proj_equivariant T.proj
        T.proj_equivariant hproj)
  let Φ := ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapHomologicalComplex _).mapShortComplex.map ψ
  -- Three commuting squares in `ModuleCat ℤ`: the snake-lemma naturality in the middle, and the
  -- compatible-pair maps read through `mapHomologyIso` on either side (`forget₂_map_map`).
  have h := HomologicalComplex.HomologySequence.δ_naturality Φ
    S.continuousCochainsShortExact_shortExact T.continuousCochainsShortExact_shortExact n (n + 1)
    rfl
  have h₁ := (Iso.eq_inv_comp _).1 (forget₂_map_map φ
    (ofDiscreteModulePair (φ : H →* G) fA.toIntLinearMap hA) (n + 1))
  have h₃ := (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans
    (forget₂_map_map φ (ofDiscreteModulePair (φ : H →* G) fC.toIntLinearMap hC) n).symm)
  apply (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map_injective
  rw [Functor.map_comp, Functor.map_comp, forget₂_map_delta, forget₂_map_delta]
  -- Paste the three squares. `Category.assoc` cannot be rewritten here because the objects of the
  -- two sides agree only after unfolding `continuousCohomology`.
  exact ((CommSq.mk h₃).horiz_comp ((CommSq.mk h).horiz_comp (CommSq.mk h₁))).w

end Map

section Naturality

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
@[reassoc]
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
  -- A coefficient map is the compatible pair at `φ = id`.
  -- `_root_.map_smul` is named in full: the bare name also resolves to
  -- `ContinuousCohomology.map_smul`, and elaborating that failed alternative costs 0.05 s each.
  have hA : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      fA.toAddMonoidHom.toIntLinearMap (fun g a ↦ _root_.map_smul fA g a) =
      ofDiscreteModuleMap fA.toAddMonoidHom.toIntLinearMap fun g a ↦ _root_.map_smul fA g a :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  have hC : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      fC.toAddMonoidHom.toIntLinearMap (fun g c ↦ _root_.map_smul fC g c) =
      ofDiscreteModuleMap fC.toAddMonoidHom.toIntLinearMap fun g c ↦ _root_.map_smul fC g c :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [coeffMap_def, coeffMap_def, ← hA, ← hC]
  exact S.delta_map T (ContinuousMonoidHom.id G) fA.toAddMonoidHom fB.toAddMonoidHom
    fC.toAddMonoidHom (fun g a ↦ _root_.map_smul fA g a) (fun g b ↦ _root_.map_smul fB g b)
    (fun g c ↦ _root_.map_smul fC g c) hincl hproj n

end Naturality

/-- **Restriction commutes with the connecting map.** For a compact subgroup `T` of `G`, restricting
the connecting map of `S` to `T` gives the connecting map of the restricted sequence
`S.restrict T`:

```text
Hⁿ(G, C) ---δ---> Hⁿ⁺¹(G, A)
   |                  |
  res                res
   v                  v
Hⁿ(T, C) ---δ---> Hⁿ⁺¹(T, A)
```

The restriction of `ofDiscreteModule ℤ G M` to `T` is `ofDiscreteModule ℤ T M` by definition
(`TauCeti.res_ofDiscreteModule`), which is how the two sides compose. -/
@[reassoc]
theorem delta_res (T : Subgroup G) [CompactSpace T] (n : ℕ) :
    S.delta n ≫ res T (ofDiscreteModule ℤ G A) (n + 1) =
      res T (ofDiscreteModule ℤ G C) n ≫ (S.restrict T).delta n := by
  -- Restriction is the compatible pair of the inclusion `T ↪ G` and the identity.
  have hA : ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype T : T →* G)
      (AddMonoidHom.id A).toIntLinearMap (fun _ _ ↦ rfl) =
      𝟙 (TopRep.res (T.subtype : T →* G) (ofDiscreteModule ℤ G A)) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  have hC : ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype T : T →* G)
      (AddMonoidHom.id C).toIntLinearMap (fun _ _ ↦ rfl) =
      𝟙 (TopRep.res (T.subtype : T →* G) (ofDiscreteModule ℤ G C)) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [res_def, res_def, ← hA, ← hC]
  exact S.delta_map (S.restrict T) (ContinuousMonoidHom.subgroupSubtype T) (AddMonoidHom.id A)
    (AddMonoidHom.id B) (AddMonoidHom.id C) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ by simp) (fun _ ↦ by simp) n

end ContCohomology.DiscreteShortExact

end TauCeti
