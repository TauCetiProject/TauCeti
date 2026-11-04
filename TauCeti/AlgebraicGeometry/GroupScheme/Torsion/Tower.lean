/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The prime-power torsion tower

For a commutative group scheme `G/S`, `G.torsionTower p` is the functor on the ordered
natural numbers with value `G[pⁿ]` at `n`. Its arrows are inclusions, not multiplication
transitions. Homomorphisms induce natural transformations of these towers. Thus an
isomorphism of towers is a compatible system of finite-level group-scheme isomorphisms,
as used in deformation theory of elliptic curves.

The construction makes sense for any natural number `p` and any commutative group scheme;
no finiteness, flatness, or divisibility is asserted here.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 5.
-/

public section

open CategoryTheory AlgebraicGeometry MonObj
open TauCeti.GroupScheme

universe u

namespace CategoryTheory.CommGrp

variable {S : Scheme.{u}} (G : CommGrp (Over S)) (p : ℕ)

/-- The tower `G[pⁿ]`, with the canonical inclusions as its transition arrows.
The object formula is exposed so that finite-level morphisms have their usual types. -/
@[expose]
noncomputable def torsionTower : ℕ ⥤ Grp (Over S) where
  obj n := torsion G ((p : ℤ) ^ n)
  map {m n} f := Grp.homMk (torsionLift (torsionι G ((p : ℤ) ^ m)) (by
    obtain ⟨k, hk⟩ := pow_dvd_pow (p : ℤ) (leOfHom f)
    rw [hk, zpow_mul, torsionι_zpow, one_zpow]))
  map_id n := by
    apply Grp.hom_ext
    apply torsion_hom_ext G
    simp
  map_comp f g := by
    apply Grp.hom_ext
    apply torsion_hom_ext G
    simp

/-- The value of the torsion tower at `n` is `G[pⁿ]`. -/
@[simp]
theorem torsionTower_obj (n : ℕ) :
    (G.torsionTower p).obj n = torsion G ((p : ℤ) ^ n) :=
  (rfl)

/-- Every arrow in the torsion tower preserves the underlying point of `G`. -/
@[reassoc, simp]
theorem torsionTower_map_ι {m n : ℕ} (f : m ⟶ n) :
    ((G.torsionTower p).map f).hom.hom ≫ torsionι G ((p : ℤ) ^ n) =
      torsionι G ((p : ℤ) ^ m) := by
  simp [torsionTower]

variable {G p} {H K : CommGrp (Over S)}

/-- Restriction of a group-scheme homomorphism to all prime-power torsion levels. -/
noncomputable def torsionTowerMap (f : G ⟶ H) (p : ℕ) :
    G.torsionTower p ⟶ H.torsionTower p where
  app n := by
    dsimp only [torsionTower]
    exact Grp.homMk (torsionMap f ((p : ℤ) ^ n))
  naturality {m n} g := by
    apply Grp.hom_ext
    apply torsion_hom_ext H
    simp [torsionTower, Grp.homMk_hom_hom]

/-- At each level, the map of towers is the restriction of the original homomorphism. -/
@[simp]
theorem torsionTowerMap_app (f : G ⟶ H) (p n : ℕ) :
    ((torsionTowerMap f p).app n).hom.hom = torsionMap f ((p : ℤ) ^ n) := by
  simp [torsionTowerMap, torsionTower, Grp.homMk_hom_hom]

/-- Restricting the identity gives the identity of the torsion tower. -/
@[simp]
theorem torsionTowerMap_id (G : CommGrp (Over S)) (p : ℕ) :
    torsionTowerMap (𝟙 G) p = 𝟙 (G.torsionTower p) := by
  apply NatTrans.ext
  funext n
  apply Grp.hom_ext
  simp [torsionTower]

/-- Restriction to torsion towers respects composition. -/
@[simp]
theorem torsionTowerMap_comp (f : G ⟶ H) (g : H ⟶ K) (p : ℕ) :
    torsionTowerMap (f ≫ g) p = torsionTowerMap f p ≫ torsionTowerMap g p := by
  apply NatTrans.ext
  funext n
  rw [NatTrans.comp_app]
  apply Grp.hom_ext
  simp [torsionTower]

/-- Taking the prime-power torsion tower is functorial in the commutative group scheme. -/
noncomputable def torsionTowerFunctor (S : Scheme.{u}) (p : ℕ) :
    CommGrp (Over S) ⥤ (ℕ ⥤ Grp (Over S)) where
  obj G := G.torsionTower p
  map f := torsionTowerMap f p

variable (G p)

/-- Base change of the whole torsion tower, including all its inclusion arrows. -/
noncomputable def torsionTowerBaseChangeIso {T : Scheme.{u}} (s : T ⟶ S) :
    G.torsionTower p ⋙ (Over.pullback s).mapGrp ≅
      ((Over.pullback s).mapCommGrp.obj G).torsionTower p :=
  NatIso.ofComponents (fun n ↦ torsionBaseChangeIso G s ((p : ℤ) ^ n)) (by
    intro m n f
    -- Normalize the functor objects before comparing their group laws.
    dsimp only [torsionTower, Functor.comp_map, Functor.comp_obj]
    apply Grp.hom_ext
    apply torsion_hom_ext ((Over.pullback s).mapCommGrp.obj G)
    simp only [Functor.mapGrp_map_hom_hom, Grp.comp_hom_hom, Grp.homMk_hom_hom,
      Category.assoc, torsionLift_ι, torsionBaseChangeIso_hom_hom_hom_torsionι]
    refine (Category.assoc _ _ _).trans ?_
    rw [torsionBaseChangeIso_hom_hom_hom_torsionι]
    -- The two presentations of the pullback carrier are definitionally equal only.
    exact ((Over.pullback s).map_comp _ _).symm.trans
      (congrArg (Over.pullback s).map (torsionLift_ι _ _)))

/-- The base-change comparison at level `n` is the canonical comparison for `G[pⁿ]`. -/
@[simp]
theorem torsionTowerBaseChangeIso_app {T : Scheme.{u}} (s : T ⟶ S) (n : ℕ) :
    (G.torsionTowerBaseChangeIso p s).app n = torsionBaseChangeIso G s ((p : ℤ) ^ n) :=
  (rfl)

end CategoryTheory.CommGrp
