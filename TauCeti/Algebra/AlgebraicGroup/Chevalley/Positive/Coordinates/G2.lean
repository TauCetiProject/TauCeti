/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2

/-!
# Positive-root coordinates in type G₂

Every positive point of a G₂ Chevalley datum is an ordered product of the six positive root
subgroups, over any commutative ring. For the full-weight datum these six parameters are unique.
The order may be any duplicate-free enumeration of the six native positive-root indices.
Parameters are indexed only by these six roots, so the uniqueness statement contains no unused
negative-root coordinates.

These are pointwise coordinates for the positive factor in Bruhat and big-cell factorizations.
They assert neither a scheme isomorphism nor generation of all points of the ambient group.
In particular, they work in characteristics two and three and over nonreduced rings.

Existence uses `DynkinType.mem_biSup_posRoots_g2_iff_exists_list_prod_map` on the admissible
lattice, transported through the datum's matrix realization. Uniqueness uses the integral
full-weight theorem `DynkinType.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable {ht : G2.Valid} (D : ChevalleyDatum G2 ht)
variable (A : Type*) [CommRing A]
variable (l : List (Fin 6))

/-- Every positive point of a G₂ Chevalley datum has an ordered six-root product expression.
The order is arbitrary, and the value ring need not be a field. Uniqueness is not asserted
for a general datum. -/
theorem ChevalleyDatum.mem_positivePoints_iff_exists_prod_G2
    (hl : l.Nodup) (hcover : ∀ i, i ∈ l) (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : Fin 6 → A,
      (l.map fun i => D.rootSubgroupPoints (Fin.castAdd 6 i) A
        (Multiplicative.ofAdd (u i))).prod = g := by
  constructor
  · intro hg
    obtain ⟨v, hv, hvg⟩ := Subgroup.mem_map.mp (D.mem_positivePoints_iff.mp hg)
    rw [D.positiveSubgroup_eq_iSup] at hv
    obtain ⟨u, hu⟩ := (mem_biSup_posRoots_g2_iff_exists_list_prod_map
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A) l hl hcover v).mp hv
    refine ⟨u, (D.points A).subtype_injective ?_⟩
    let m := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
    calc
      _ = m ((l.map fun i => chevalleyRootSubgroup D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
          (Fin.castAdd 6 i) (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u i))).prod) := by
        simp only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply]
        exact congrArg List.prod (List.map_congr_left fun i _ =>
          D.coe_rootSubgroupPoints (Fin.castAdd 6 i) A (Multiplicative.ofAdd (u i)))
      _ = m v := congrArg m hu
      _ = _ := hvg
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact D.rootSubgroupPoints_mem_positivePoints A
      ((mem_posRoots_rational_g2_iff ht _).mpr i.isLt) _

/-- In the full-weight G₂ model, a positive point has exactly one tuple of six root parameters
in any prescribed order. This includes bad characteristic and rings with nilpotents. -/
theorem mem_scChevalleyDatum_positivePoints_iff_existsUnique_prod_G2
    (hl : l.Nodup) (hcover : ∀ i, i ∈ l)
    (g : (G2.scChevalleyDatum ht).points A) :
    g ∈ (G2.scChevalleyDatum ht).positivePoints A ↔ ∃! u : Fin 6 → A,
      (l.map fun i => (G2.scChevalleyDatum ht).rootSubgroupPoints (Fin.castAdd 6 i) A
        (Multiplicative.ofAdd (u i))).prod = g := by
  let D := G2.scChevalleyDatum ht
  have hinj {u v : Fin 6 → A}
      (huv : (l.map fun i => D.rootSubgroupPoints (Fin.castAdd 6 i) A
          (Multiplicative.ofAdd (u i))).prod =
        (l.map fun i => D.rootSubgroupPoints (Fin.castAdd 6 i) A
          (Multiplicative.ofAdd (v i))).prod) : u = v := by
    have h := (G2.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
      (l := l.map fun i => (Fin.castAdd 6 i : Fin G2.numRoots))
      (hl.map (Fin.castAdd_injective 6 6))
      (by
        intro γ hγ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hγ
        exact (mem_posRoots_rational_g2_iff ht _).mpr i.isLt)
      (u := Fin.addCases (n := 6) u (fun _ => 0))
      (v := Fin.addCases (n := 6) v (fun _ => 0))).mp
      (by
        -- Expose the native root-count equality so list composition sees Fin (6 + 6).
        dsimp only [numRoots]
        simpa only [List.map_map, Function.comp_def, Fin.addCases_left] using huv)
    funext i
    simpa only [Fin.addCases_left] using h (Fin.castAdd 6 i) (List.mem_map.mpr ⟨i, hcover i, rfl⟩)
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := (D.mem_positivePoints_iff_exists_prod_G2 A l hl hcover g).mp hg
    exact ⟨u, hu, fun v hv => hinj (hv.trans hu.symm)⟩
  · rintro ⟨u, hu, _⟩
    exact (D.mem_positivePoints_iff_exists_prod_G2 A l hl hcover g).mpr ⟨u, hu⟩

end TauCeti.DynkinType
