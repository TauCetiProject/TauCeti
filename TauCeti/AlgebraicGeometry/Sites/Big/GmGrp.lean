/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Basic

/-!
# The multiplicative group as a sheaf of groups on a big site

The abelian sheaf `AlgebraicGeometry.Scheme.Gm S`, the multiplicative group `T ↦ Γ(T, 𝒪_T)ˣ` on
the big fpqc site of a scheme `S`, is a sheaf for every topology `J` coarser than the fpqc
topology. This file records it as a sheaf of groups on the big `J`-site, the form in which it acts
on torsors (`CategoryTheory.Sheaf.Torsor`), and identifies its sections over an `S`-scheme `T`
with the units of `Γ(T, 𝒪_T)`, the restriction maps being the maps of units induced by pullback
of functions.

## Main declarations

* `AlgebraicGeometry.Scheme.isSheaf_Gm_of_le`: `𝔾_m` is a sheaf for every topology coarser than
  the fpqc topology.
* `AlgebraicGeometry.Scheme.GmGrp S J hJ`: `𝔾_m` as a sheaf of groups on the big `J`-site of `S`.
* `AlgebraicGeometry.Scheme.GmGrpObjEquiv`: its sections over `T` are the units of `Γ(T, 𝒪_T)`.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {J : GrothendieckTopology Scheme.{u}}

/-- The abelian sheaf `𝔾_m : T ↦ Γ(T, 𝒪_T)ˣ` on the big fpqc site of `S` is a sheaf for every
topology coarser than the fpqc topology. -/
lemma isSheaf_Gm_of_le (hJ : J ≤ fpqcTopology) : Presheaf.IsSheaf (J.over S) (Gm S).obj :=
  fun E ↦ Presieve.isSheaf_of_le _ (fun _ _ hR ↦ hJ _ hR) ((Gm S).property E)

variable (J) in
/-- The multiplicative group `𝔾_m : T ↦ Γ(T, 𝒪_T)ˣ` as a sheaf of groups on the big site of `S`
for a topology `J` coarser than the fpqc topology. -/
-- An abbreviation, so that statements about its sections see the sheaf of groups underlying the
-- abelian sheaf `Gm S` (`GmGrpObjEquiv`).
noncomputable abbrev GmGrp (hJ : J ≤ fpqcTopology) : Sheaf (J.over S) GrpCat.{u} :=
  (abelianSheafToGrpSheaf (J.over S)).obj ⟨(Gm S).obj, isSheaf_Gm_of_le S hJ⟩

variable {S} {hJ : J ≤ fpqcTopology}

/-- The sections of `𝔾_m` over an `S`-scheme `T` are the units of `Γ(T, 𝒪_T)`. -/
noncomputable def GmGrpObjEquiv (T : Over S) : Γ(T.left, ⊤)ˣ ≃* (GmGrp S J hJ).obj.obj (op T) :=
  (MulEquiv.multiplicativeAdditive _).symm.trans
    (abelianSheafToGrpSheafObjEquiv ⟨(Gm S).obj, isSheaf_Gm_of_le S hJ⟩ (op T))

/-- The restriction maps of `𝔾_m` are the maps of units induced by pullback of functions. -/
@[simp]
lemma GmGrp_map_GmGrpObjEquiv {T T' : Over S} (f : T ⟶ T') (a : Γ(T'.left, ⊤)ˣ) :
    (GmGrp S J hJ).obj.map f.op (GmGrpObjEquiv T' a) =
      GmGrpObjEquiv T (Units.map f.left.appTop.hom a) :=
  abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv _ _ _

end AlgebraicGeometry.Scheme
