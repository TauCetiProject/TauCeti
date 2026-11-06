/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import TauCeti.AlgebraicGeometry.Sites.Big.Module

/-!
# The big presheaf of a module is a Zariski sheaf

Let `S` be a scheme and `F` an `𝒪_S`-module. The presheaf of modules
`AlgebraicGeometry.Scheme.Modules.bigPresheaf F : (T, h) ↦ Γ(T, h^* F)` on the big site `Over S`
is a sheaf for the Zariski topology
(`AlgebraicGeometry.Scheme.Modules.isSheaf_bigPresheaf_zariskiTopology`).
No quasi-coherence is needed: for an open cover `U` of an `S`-scheme `T`, global sections of the
pullback of `F` to the `S`-scheme `U i` are the sections of `h^* F` over `U i`
(`AlgebraicGeometry.Scheme.Modules.bijective_bigSectionsRestrictLE_ι`), so the sheaf condition
for the cover is the sheaf condition of the `𝒪_T`-module `h^* F`.

The Zariski sheaf property is one of the two inputs of fpqc descent of sections of quasi-coherent
modules (Stacks, Lemma 35.8.1), the other being descent along a single faithfully flat map of
affine schemes; Mathlib's `AlgebraicGeometry.isSheaf_propQCTopology_iff` (Stacks, Tag 022H)
reduces fpqc sheaves on schemes to these two cases.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isSheafFor_bigPresheaf_ofArrows_ι`: the sheaf condition for
  the inclusions of the members of an open cover of an `S`-scheme.
* `AlgebraicGeometry.Scheme.Modules.isSheaf_bigPresheaf_zariskiTopology`: `bigPresheaf F` is a
  sheaf for the Zariski topology on `Over S`.

## References

* The Stacks Project, Section 35.8, *Quasi-coherent sheaves and topologies*, Lemma 35.8.1.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (F : S.Modules)

/-- For an open cover `U` of an `S`-scheme `T`, the presheaf `(T', h') ↦ Γ(T', h'^* F)` satisfies
the sheaf condition for the family of inclusions of the `S`-schemes `U i` into `T`. -/
theorem isSheafFor_bigPresheaf_ofArrows_ι (T : Over S) {ι : Type*} {U : ι → T.left.Opens}
    (hU : TopologicalSpace.IsOpenCover U) :
    Presieve.IsSheafFor (F.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (Presieve.ofArrows (fun i ↦ Over.mk ((U i).ι ≫ T.hom))
        (fun i ↦ (Over.homMk (U i).ι : Over.mk ((U i).ι ≫ T.hom) ⟶ T))) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- Read each `x i` as a section `s i` of `G = h^* F` over `U i`; compatibility of the family
  -- makes these sections agree on overlaps, so they glue in the sheaf `G` to a global section.
  let G := (pullback T.hom).obj F
  have he (V : T.left.Opens) := bijective_bigSectionsRestrictLE_ι F T.hom V
  choose s hs using fun i ↦ (he (U i)).2 (x i)
  have hcompat : TopCat.Presheaf.IsCompatible G.presheaf U s := by
    intro i j
    refine (he (U i ⊓ U j)).1 ((bigSectionsRestrict_homMk_homOfLE F T inf_le_left (s i)).symm.trans
      (((congrArg _ (hs i)).trans ?_).trans (bigSectionsRestrict_homMk_homOfLE F T inf_le_right
        (s j))))
    refine (hx i j (Over.mk ((U i ⊓ U j).ι ≫ T.hom))
      (Over.homMk (T.left.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (by simp))
      (Over.homMk (T.left.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (by simp))
      (by ext; simp)).trans ?_
    exact congrArg (bigSectionsRestrict F _) (hs j).symm
  obtain ⟨t, ht, ht'⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨G.presheaf, G.isSheaf⟩ U ⊤
    (fun i ↦ homOfLE le_top) hU.iSup_eq_top.ge s hcompat
  refine ⟨t, fun i ↦ ?_, fun t' h' ↦ ht' t' fun i ↦ (he (U i)).1 ?_⟩
  · -- The restriction maps of the underlying presheaf of sets are `bigSectionsRestrict`.
    change bigSectionsRestrict F (Over.homMk (U i).ι : Over.mk ((U i).ι ≫ T.hom) ⟶ T) t = x i
    exact (bigSectionsRestrict_homMk_ι F T (U i) t).trans ((congrArg _ (ht i)).trans (hs i))
  · -- As above, `h' i` is a statement about `bigSectionsRestrict`.
    rw [hs]
    exact (bigSectionsRestrict_homMk_ι F T (U i) t').symm.trans (h' i)

/-- **The big presheaf of a module is a Zariski sheaf.** For every `𝒪_S`-module `F`, the presheaf
of abelian groups `(T, h) ↦ Γ(T, h^* F)` underlying `bigPresheaf F` is a sheaf for the Zariski
topology on the big site `Over S`. -/
theorem isSheaf_bigPresheaf_zariskiTopology :
    Presheaf.IsSheaf (zariskiTopology.over S) F.bigPresheaf.presheaf := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u}) ?_
  rw [isSheaf_iff_isSheaf_of_type, zariskiTopology, grothendieckTopology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget,
    ← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck, Presieve.isSheaf_pretopology]
  intro T R hR
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  simp only [Precoverage.toPretopology_toPrecoverage, Precoverage.mem_comap_iff,
    Presieve.map_ofArrows, ofArrows_mem_precoverage_iff, Over.forget_map] at hR
  obtain ⟨hsurj, hopen⟩ := hR
  let U (i : ι) : T.left.Opens := (g i).left.opensRange
  have hU : TopologicalSpace.IsOpenCover U := by
    refine .mk (top_le_iff.mp fun x _ ↦ ?_)
    obtain ⟨i, y, rfl⟩ := hsurj x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩
  -- The covering family and the inclusions of the opens `U i` generate the same sieve.
  rw [Presieve.isSheafFor_iff_generate]
  convert (Presieve.isSheafFor_iff_generate _).mp (isSheafFor_bigPresheaf_ofArrows_ι F T hU)
    using 2
  refine le_antisymm (Sieve.generate_le_iff _ _ |>.mpr ?_) (Sieve.generate_le_iff _ _ |>.mpr ?_)
  · rintro _ _ ⟨i⟩
    have hle : Set.range (g i).left ⊆ Set.range (U i).ι := by simp [U]
    refine ⟨Over.mk ((U i).ι ≫ T.hom),
      Over.homMk (IsOpenImmersion.lift (U i).ι (g i).left hle) ?_,
      (Over.homMk (U i).ι : Over.mk ((U i).ι ≫ T.hom) ⟶ T), ⟨i⟩, ?_⟩
    · -- The structure morphism of `Over.mk ((U i).ι ≫ T.hom)` is `(U i).ι ≫ T.hom`.
      change _ ≫ (U i).ι ≫ T.hom = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w (g i)]
    · ext
      exact IsOpenImmersion.lift_fac _ _ _
  · rintro _ _ ⟨i⟩
    have hle : Set.range (U i).ι ⊆ Set.range (g i).left := by simp [U]
    refine ⟨Z i, Over.homMk (IsOpenImmersion.lift (g i).left (U i).ι hle) ?_, g i, ⟨i⟩, ?_⟩
    · -- As above, unfold the structure morphism of `Over.mk ((U i).ι ≫ T.hom)`.
      change _ = (U i).ι ≫ T.hom
      rw [← Over.w (g i), ← Category.assoc, IsOpenImmersion.lift_fac]
    · ext
      exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme.Modules
