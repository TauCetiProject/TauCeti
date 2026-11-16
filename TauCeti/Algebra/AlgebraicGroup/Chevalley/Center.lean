/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Conjugation

/-!
# Central integral points of a Chevalley datum

An integral point `c : D.points ℤ` whose base change centralizes all positive/negative simple root
subgroups and the torus over every commutative ring centralizes `D.points A` over every ring `A`
(`conj_eq_self_of_forall_conj_simpleRootSubgroup_and_torus`). In particular, integral torus points
annihilating all simple coordinate roots are central (`torusPoints_map_algebraMap_conj_eq_self`),
as is `D.simpleCorootPoints i A (-1)` whenever every simple root pairs evenly with `α_i^∨`
(`simpleCorootPoints_neg_one_conj_eq_self`, and in rank one
`simpleCorootPoints_neg_one_conj_eq_self_of_rank_eq_one`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Ch. 3; J. C. Jantzen, *Representations of
  Algebraic Groups*, II.1; G. Malle & D. Testerman, *Linear Algebraic Groups and Finite Groups of
  Lie Type*, Cambridge Univ. Press (2011), §9.2 and Example 22.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum
open Multiplicative
noncomputable section
universe v
variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem mem_equalizer_conj_iff (c : D.points ℤ) (B : Type*) [CommRing B] (x : D.points B) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ B) (1 : Matrix.GeneralLinearGroup (Fin D.dim) ℤ) *
        (x : Matrix.GeneralLinearGroup (Fin D.dim) B) *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ B) 1)⁻¹ ∈
      GeneralLinear.hopfIdealPointsSubgroup D.dim (CommHopfAlgCat.equalizerHopfIdeal
        (GeneralLinear.conjCoordinateIso (c : Matrix.GeneralLinearGroup (Fin D.dim) ℤ)).hom
        (CategoryTheory.CategoryStruct.id (GeneralLinear.coordinateHopfAlgebra ℤ D.dim))) B ↔
    (D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c * x *
        ((D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c)⁻¹ = x := by
  simp only [map_one, one_mul, inv_one, mul_one,
    GeneralLinear.mem_hopfIdealPointsSubgroup_equalizer_conjCoordinateIso_iff,
    ← GeneralLinear.IntegralPointsPresentation.coe_map (D.pointsPresentation ℤ)
      (D.pointsPresentation B) (algebraMap ℤ B) c, ← Subgroup.coe_inv, ← Subgroup.coe_mul,
    Subtype.ext_iff]

/-- **Centrality criterion for integral points of a Chevalley datum**: `c : D.points ℤ` centralizes
`D.points A` over every commutative ring `A` if its base change centralizes all positive/negative
simple root subgroups and torus points over every commutative ring `B : Type`. -/
theorem conj_eq_self_of_forall_conj_simpleRootSubgroup_and_torus (c : D.points ℤ)
    (hpos : ∀ (B : Type) [CommRing B] (m : Fin t.rank) (u : Multiplicative B),
      (D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c *
          D.rootSubgroupPoints (t.simpleIndex ht m) B u *
          ((D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c)⁻¹ =
        D.rootSubgroupPoints (t.simpleIndex ht m) B u)
    (hneg : ∀ (B : Type) [CommRing B] (m : Fin t.rank) (u : Multiplicative B),
      (D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c *
          D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
            (t.simpleIndex ht m) (t.simpleIndex ht m)) B u *
          ((D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c)⁻¹ =
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht m) (t.simpleIndex ht m)) B u)
    (htorus : ∀ (B : Type) [CommRing B] (s : Fin t.rank → Bˣ),
      (D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c *
          D.torusPoints B s *
          ((D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) c)⁻¹ =
        D.torusPoints B s)
    (A : Type v) [CommRing A] (g : D.points A) :
    (D.pointsPresentation ℤ).map (D.pointsPresentation A) (algebraMap ℤ A) c * g *
        ((D.pointsPresentation ℤ).map (D.pointsPresentation A) (algebraMap ℤ A) c)⁻¹ = g :=
  (D.mem_equalizer_conj_iff c A g).mp
    (UniversalEnvelopingAlgebra.conj_mem_hopfIdealPointsSubgroup_of_mem_kostantToralPointsSubgroup
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis
      D.coordinateWeight _ 1 (fun B _ k q => by
        let u := AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B) q
        have hq := (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B)).symm_apply_apply q
        rcases k with m | m
        · rw [← hq, ← D.coe_rootSubgroupPoints_simpleIndex m B u]
          exact (D.mem_equalizer_conj_iff c B _).mpr (hpos B m u)
        · rw [← hq, ← D.coe_rootSubgroupPoints_reflectionPerm_simpleIndex m B u]
          exact (D.mem_equalizer_conj_iff c B _).mpr (hneg B m u))
      (fun B _ s => by
        rw [← D.coe_torusPoints B s]; exact (D.mem_equalizer_conj_iff c B _).mpr (htorus B s))
      A (D.points_eq_kostantToralPointsSubgroup A ▸ g.2))

/-- **Integral torus points annihilating all simple coordinate roots are central in `D.points A`
over every commutative ring `A`.** -/
theorem torusPoints_map_algebraMap_conj_eq_self (s₀ : Fin t.rank → ℤˣ)
    (hs₀ : ∀ m : Fin t.rank, torusCharacter s₀ (D.coordinateRoot (t.simpleIndex ht m)) = 1)
    (A : Type v) [CommRing A] (g : D.points A) :
    D.torusPoints A (fun j => Units.map (algebraMap ℤ A).toMonoidHom (s₀ j)) * g *
        (D.torusPoints A (fun j => Units.map (algebraMap ℤ A).toMonoidHom (s₀ j)))⁻¹ = g := by
  let f (B : Type) [CommRing B] :=
    (D.pointsPresentation ℤ).map (D.pointsPresentation B) (algebraMap ℤ B) (D.torusPoints ℤ s₀)
  have hconj (B : Type) [CommRing B] (γ : Fin t.numRoots)
      (hγ : torusCharacter s₀ (D.coordinateRoot γ) = 1) (u : Multiplicative B) :
      f B * D.rootSubgroupPoints γ B u * (f B)⁻¹ = D.rootSubgroupPoints γ B u := by
    have hmap : torusCharacter (fun j => Units.map (algebraMap ℤ B).toMonoidHom (s₀ j))
        (D.coordinateRoot γ) = 1 := by
      simpa only [RingHom.toMonoidHom_eq_coe, hγ, map_one] using
        (map_torusCharacter (algebraMap ℤ B) s₀ (D.coordinateRoot γ)).symm
    rw [show f B = _ from D.map_torusPoints _ _, ← ofAdd_toAdd u,
      D.torusPoints_conj_rootSubgroupPoints, hmap, Units.val_one, one_mul]
  simpa only [D.map_torusPoints] using
    D.conj_eq_self_of_forall_conj_simpleRootSubgroup_and_torus (D.torusPoints ℤ s₀)
      (fun B _ m => hconj B _ (hs₀ m)) (fun B _ m => hconj B _ (by
        rw [D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hs₀ m, inv_one]))
      (fun B _ s => by rw [D.map_torusPoints, D.torusPoints_conj_torusPoints]) A g

/-- **If every simple root pairs evenly with `α_i^∨`, then `D.simpleCorootPoints i A (-1)` is
central in `D.points A` over every commutative ring `A`.** -/
theorem simpleCorootPoints_neg_one_conj_eq_self (i : Fin t.rank)
    (heven : ∀ m : Fin t.rank, Even ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht m) i))
    (A : Type v) [CommRing A] (g : D.points A) :
    D.simpleCorootPoints i A (-1) * g * (D.simpleCorootPoints i A (-1))⁻¹ = g := by
  have h := D.torusPoints_map_algebraMap_conj_eq_self (D.simpleCorootParameter i ℤ (-1))
    (fun m => by
      rw [D.coordinateRoot_def, D.torusCharacter_simpleCorootParameter]
      rcases heven m with ⟨k, hk⟩; dsimp only; rw [hk, ← two_mul, zpow_mul]; simp) A g
  rwa [show (fun j => Units.map (algebraMap ℤ A).toMonoidHom (D.simpleCorootParameter i ℤ (-1) j)) =
      D.simpleCorootParameter i A (-1) from funext fun j => by simp [D.simpleCorootParameter_apply],
    ← D.simpleCorootPoints_eq_torusPoints] at h

/-- **In rank one, `D.simpleCorootPoints i A (-1)` is central in `D.points A` over every ring.** -/
theorem simpleCorootPoints_neg_one_conj_eq_self_of_rank_eq_one (hr : t.rank = 1) (i : Fin t.rank)
    (A : Type v) [CommRing A] (g : D.points A) :
    D.simpleCorootPoints i A (-1) * g * (D.simpleCorootPoints i A (-1))⁻¹ = g :=
  D.simpleCorootPoints_neg_one_conj_eq_self i (fun m => by
    obtain rfl : m = i := Fin.ext (by omega); simp) A g

end
end TauCeti.DynkinType.ChevalleyDatum
