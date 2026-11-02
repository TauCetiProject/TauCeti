/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.LongExactSequence

/-!
# The coefficient sequence for module-valued local cohomology

Sheafifying the presheaf coefficient sequence constructed in
`TauCeti.Topology.Sheaves.SupportedCohomology.LongExactSequence` gives the long
exact sequence of local cohomology sheaves, retaining the module coefficients
throughout. Its connecting maps commute with morphisms of short exact sequences.

Flasque sheaves have zero positive local cohomology sheaves. Consequently a
short exact sequence with flasque middle term gives dimension-shift
isomorphisms in positive degrees. These are the connecting maps used to compare
flasque resolutions, not arbitrary isomorphisms between the cohomology objects.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)
  {T T' : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}

noncomputable section

/-- The connecting morphism of module-valued local cohomology sheaves. -/
def supportedModuleHSheafδ (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedModuleHSheaf S n ⟶ T.X₁.supportedModuleHSheaf S (n + 1) :=
  (presheafToSheaf _ _).map (supportedModuleHPresheafδ S hT n)

/-- The sheaf connecting map is induced by the presheaf connecting map. -/
@[reassoc (attr := simp)]
lemma toSheafify_supportedModuleHSheafδ (hT : T.ShortExact) (n : ℕ) :
    toSheafify (Opens.grothendieckTopology X) (T.X₃.supportedModuleHPresheaf S n) ≫
        (supportedModuleHSheafδ S hT n).hom =
      supportedModuleHPresheafδ S hT n ≫
        toSheafify (Opens.grothendieckTopology X) (T.X₁.supportedModuleHPresheaf S (n + 1)) :=
  (toSheafify_naturality _ _).symm

/-- The local cohomology connecting map is natural in short exact sequences. -/
@[reassoc]
lemma supportedModuleHSheafδ_naturality (hT : T.ShortExact) (hT' : T'.ShortExact)
    (f : T ⟶ T') (n : ℕ) :
    (supportedModuleHSheafFunctor S n).map f.τ₃ ≫ supportedModuleHSheafδ S hT' n =
      supportedModuleHSheafδ S hT n ≫
        (supportedModuleHSheafFunctor S (n + 1)).map f.τ₁ := by
  let a := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  exact (a.map_comp _ _).symm.trans
    ((a.congr_map (supportedModuleHPresheafδ_naturality S hT hT' f n)).trans
      (a.map_comp _ _))

@[simp, reassoc]
lemma supportedModuleHSheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (supportedModuleHSheafFunctor S n).map T.g ≫ supportedModuleHSheafδ S hT n = 0 := by
  let a := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  exact (a.map_comp _ _).symm.trans
    ((a.congr_map (supportedModuleHPresheafFunctor_map_g_δ S hT n)).trans (a.map_zero _ _))

@[simp, reassoc]
lemma supportedModuleHSheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    supportedModuleHSheafδ S hT n ≫
      (supportedModuleHSheafFunctor S (n + 1)).map T.f = 0 := by
  let a := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  exact (a.map_comp _ _).symm.trans
    ((a.congr_map (supportedModuleHPresheafδ_map_f S hT n)).trans (a.map_zero _ _))

/-- The coefficient sequence of local cohomology sheaves is exact at its middle term. -/
theorem exact_map_supportedModuleHSheafFunctor (hT : T.ShortExact) (n : ℕ) :
    (T.map (supportedModuleHSheafFunctor S n)).Exact := by
  have : (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive :=
    inferInstance
  have : (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact (exact_map_supportedModuleHPresheafFunctor S hT n).map
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- The local cohomology sequence is exact immediately before its connecting map. -/
theorem exact_supportedModuleHSheafFunctor_map_g_δ (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((supportedModuleHSheafFunctor S n).map T.g)
      (supportedModuleHSheafδ S hT n)
      (supportedModuleHSheafFunctor_map_g_δ S hT n)).Exact := by
  have : (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive :=
    inferInstance
  have : (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact (exact_supportedModuleHPresheafFunctor_map_g_δ S hT n).map
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- The local cohomology sequence is exact immediately after its connecting map. -/
theorem exact_supportedModuleHSheafδ_map_f (hT : T.ShortExact) (n : ℕ) :
    (ShortComplex.mk (supportedModuleHSheafδ S hT n)
      ((supportedModuleHSheafFunctor S (n + 1)).map T.f)
      (supportedModuleHSheafδ_map_f S hT n)).Exact := by
  have : (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive :=
    inferInstance
  have : (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact (exact_supportedModuleHPresheafδ_map_f S hT n).map
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- A flasque sheaf has zero positive local cohomology sheaves. -/
theorem isZero_supportedModuleHSheaf_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) : IsZero (F.supportedModuleHSheaf S (n + 1)) := by
  apply Functor.map_isZero
  apply (Functor.isZero_iff _).2
  intro W
  rw [F.supportedModuleHPresheaf_obj]
  exact ModuleCat.isZero_iff_subsingleton.2 inferInstance

/-- Dimension shifting for local cohomology sheaves along a flasque middle term. -/
instance isIso_supportedModuleHSheafδ_succ (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (n : ℕ) :
    IsIso (supportedModuleHSheafδ S hT (n + 1)) := by
  have := isIso_supportedModuleHPresheafδ_succ S hT n
  exact Functor.map_isIso (presheafToSheaf _ _) (supportedModuleHPresheafδ S hT (n + 1))

end

end CategoryTheory.Sheaf
