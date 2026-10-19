/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Closeds
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Relative
public import TauCeti.Topology.Sheaves.Flasque

/-!
# Sheaf cohomology with closed supports

Let `F` be a sheaf of abelian groups on a topological space `X`, let `W` be an open subset and
let `S` be a closed subset. The sections of `F` over `W` *supported in `S`* are those whose
restriction to `W ∖ S` vanishes; they form the subgroup `Γ_S(W, F)` of `F(W)`, and a morphism of
sheaves maps supported sections to supported sections.

The cohomology of `F` on `W` with supports in `S` is the relative cohomology
`H_Sⁿ(W, F) = Hⁿ(W, W ∖ S; F) = Extⁿ(ℤ_{W, W ∖ S}, F)` of the inclusion `W ∖ S ⟶ W`
(`CategoryTheory.Sheaf.relativeH'`), where `ℤ_{W, W ∖ S}` is the cokernel of the map of free
abelian sheaves `ℤ_{W ∖ S} ⟶ ℤ_W`. In degree zero it is `Γ_S(W, F)`, and the long exact sequence of
the pair is the support sequence

`⋯ ⟶ H_Sⁿ(W, F) ⟶ Hⁿ(W, F) ⟶ Hⁿ(W ∖ S, F) ⟶ H_Sⁿ⁺¹(W, F) ⟶ ⋯`

(`CategoryTheory.Sheaf.relativeH'.exact_toH'_precomp`, `relativeH'.exact_precomp_δ` and
`relativeH'.exact_δ_toH'`). Flasque sheaves have no cohomology with supports in positive degrees;
this is the acyclicity input for computing cohomology with supports by flasque resolutions.

## Main declarations

* `TauCeti.Topology.supportedSections F S W`: the sections `Γ_S(W, F)` of `F` over `W` supported
  in `S`;
* `TauCeti.Topology.supportedH F S W n`: the cohomology `H_Sⁿ(W, F)` of `F` on `W` with supports
  in `S`;
* `TauCeti.Topology.supportedHZeroEquiv`: `H_S⁰(W, F) ≃+ Γ_S(W, F)`;
* `TauCeti.Topology.subsingleton_relativeH'_succ_of_isFlasque`: a flasque sheaf has no relative
  cohomology in positive degrees for an inclusion of opens; in particular it has no cohomology with
  supports in positive degrees.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* R. Hartshorne, *Algebraic Geometry*, Exercises III.2.3–2.4.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.3 and §2.6.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

noncomputable section

/-- The inclusion `W ∖ S ⟶ W` of the complement of a closed subset `S` in an open `W`. -/
abbrev complInclusion (S : Closeds X) (W : Opens X) : W ⊓ S.compl ⟶ W :=
  homOfLE inf_le_left

/-- The sections of `F` over `W` supported in the closed subset `S`, that is, whose restriction to
`W ∖ S` vanishes. -/
def supportedSections (S : Closeds X) (W : Opens X) : AddSubgroup (F.obj.obj (op W)) :=
  (F.obj.map (complInclusion S W).op).hom.ker

@[simp]
lemma mem_supportedSections_iff {S : Closeds X} {W : Opens X} {s : F.obj.obj (op W)} :
    s ∈ supportedSections F S W ↔ F.obj.map (complInclusion S W).op s = 0 :=
  Iff.rfl

/-- A morphism of sheaves maps sections supported in `S` to sections supported in `S`. -/
lemma map_mem_supportedSections {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) {S : Closeds X} {W : Opens X} {s : F.obj.obj (op W)}
    (hs : s ∈ supportedSections F S W) : f.hom.app (op W) s ∈ supportedSections G S W := by
  rw [mem_supportedSections_iff] at hs ⊢
  rw [← ConcreteCategory.comp_apply, ← f.hom.naturality, ConcreteCategory.comp_apply, hs, map_zero]

/-- The restriction of a section supported in `S` to a smaller open is supported in `S`. -/
lemma map_mem_supportedSections_of_le {S : Closeds X} {W' W : Opens X} (h : W' ≤ W)
    {s : F.obj.obj (op W)} (hs : s ∈ supportedSections F S W) :
    F.obj.map (homOfLE h).op s ∈ supportedSections F S W' := by
  rw [mem_supportedSections_iff] at hs ⊢
  -- both composites are the inclusion `W' ∖ S ⟶ W`, and morphisms of opens are unique
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    Subsingleton.elim (complInclusion S W' ≫ homOfLE h)
      (homOfLE (inf_le_inf_right _ h) ≫ complInclusion S W),
    op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, hs, map_zero]

/-- The cohomology `H_Sⁿ(W, F)` of `F` on `W` with supports in the closed subset `S`: the relative
cohomology of the inclusion `W ∖ S ⟶ W`. -/
abbrev supportedH (S : Closeds X) (W : Opens X) (n : ℕ) : Type u :=
  F.relativeH' (complInclusion S W) n

/-- Degree-zero cohomology with supports in `S` is the group of sections supported in `S`. -/
def supportedHZeroEquiv (S : Closeds X) (W : Opens X) :
    supportedH F S W 0 ≃+ supportedSections F S W :=
  Sheaf.relativeH'.zeroEquiv F (complInclusion S W)

@[simp]
lemma coe_supportedHZeroEquiv_apply (S : Closeds X) (W : Opens X) (x : supportedH F S W 0) :
    (supportedHZeroEquiv F S W x : F.obj.obj (op W)) =
      Sheaf.relativeH'.zeroEquiv F (complInclusion S W) x :=
  (rfl)

/-- A flasque sheaf has no relative cohomology in positive degrees for an inclusion of opens. In
particular, `H_Sⁿ⁺¹(W, F)` vanishes for a flasque sheaf `F`. -/
instance subsingleton_relativeH'_succ_of_isFlasque [TopCat.Presheaf.IsFlasque F.obj]
    {U V : Opens X} (i : U ⟶ V) (n : ℕ) : Subsingleton (F.relativeH' i (n + 1)) := by
  cases n with
  | zero =>
    refine Sheaf.relativeH'.subsingleton_one F i ?_ inferInstance
    rw [← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  | succ n => exact Sheaf.relativeH'.subsingleton_add_two F i inferInstance inferInstance

end

end Topology

end TauCeti
