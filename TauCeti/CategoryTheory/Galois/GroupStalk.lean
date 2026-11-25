/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Galois.Sheaf
public import TauCeti.CategoryTheory.Sites.Point.GrpStalk

/-!
# Stalks of presheaves of groups on finite continuous `G`-sets

Let `G` be a topological group and `P` a presheaf of groups on the finite continuous `G`-sets
`ContAction FintypeCat G`. Its stalk `(ContAction.point G).GrpStalk P` at the point
`ContAction.point G` is a group (`TauCeti.CategoryTheory.Sites.Point.GrpStalk`), and it is the
stalk of the underlying presheaf of sets, on which `G` acts by translating the point
(`ContAction.stalk`). This action is by group automorphisms, and its stabilizers are open
(`ContAction.isSmooth_stalk`), so the stalk is a group with a smooth `MulDistribMulAction` of `G`,
as for the coefficients `A` of `TauCeti.NonabelianH1.SmoothTorsor`. A morphism of presheaves of
groups induces a `G`-equivariant homomorphism of stalks (`ContAction.grpStalkMap_smul`).

## Main results

* `ContAction.smul_grpGerm`: `G` acts on germs by translating the point.
* `ContAction.grpStalkMap_smul`: the induced homomorphism of stalks is `G`-equivariant.
-/

public section

open CategoryTheory Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ GrpCat.{u})

/-- `G` acts on the stalk of a presheaf of groups as on the stalk of its underlying presheaf of
sets, by translating the point. -/
noncomputable instance instMulActionGrpStalk : MulAction G ((point G).GrpStalk P) :=
  inferInstanceAs (MulAction G ((stalk G).obj (P ⋙ forget GrpCat)).V)

/-- `G` acts on germs by translating the point. -/
@[simp]
theorem smul_grpGerm (g : G) (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S)
    (a : P.obj (op S)) : g • (point G).grpGerm P S s a = (point G).grpGerm P S (g • s) a :=
  smul_germ (P ⋙ forget GrpCat) S s a g

/-- **`G` acts on the stalk of a presheaf of groups by group automorphisms.** -/
noncomputable instance instMulDistribMulActionGrpStalk :
    MulDistribMulAction G ((point G).GrpStalk P) where
  smul_mul g p q := by
    obtain ⟨S, s, a, b, rfl, rfl⟩ := (point G).exists_grpGerm_eq₂ P p q
    rw [← map_mul, smul_grpGerm, smul_grpGerm, smul_grpGerm, map_mul]
  smul_one g := by
    obtain ⟨S, s, -, -⟩ := (point G).exists_grpGerm_eq P 1
    rw [← map_one ((point G).grpGerm P S s), smul_grpGerm, map_one, map_one]

variable {P} {Q : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ GrpCat.{u}}

/-- The homomorphism of stalks induced by a morphism of presheaves of groups is
`G`-equivariant. -/
theorem grpStalkMap_smul (f : P ⟶ Q) (g : G) (p : (point G).GrpStalk P) :
    (point G).grpStalkMap f (g • p) = g • (point G).grpStalkMap f p := by
  obtain ⟨S, s, a, rfl⟩ := (point G).exists_grpGerm_eq P p
  rw [smul_grpGerm, GrothendieckTopology.Point.grpStalkMap_grpGerm,
    GrothendieckTopology.Point.grpStalkMap_grpGerm, smul_grpGerm]

end ContAction
