/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.B2

/-!
# Positive-root coordinates in type B₂

Every positive point of a B₂ Chevalley datum has a product expression with one additive
parameter per positive root, in any prescribed order without repetitions. For the full-weight
simply connected datum these four parameters are unique over every commutative ring, including
characteristic two and nonreduced rings. The parameters are indexed only by `Fin 4`; no unused
negative-root coordinates are carried.

These are coordinates on the positive subgroup, as needed for Bruhat normal forms and the
unipotent factors of the big cell. They assert neither generation of all scheme points nor
a scheme-theoretic product isomorphism. Existence uses the integral collection theorem
`mem_biSup_posRoots_b2_iff_exists_list_prod_map`; uniqueness uses
`list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable {ht : (B 2).Valid} (D : ChevalleyDatum (B 2) ht)

/-- A B₂ datum point is positive exactly when it is a product of its four positive root
subgroups. The native table is ordered by any list containing each index exactly once.
Existence holds for every Chevalley datum and every commutative value ring. -/
theorem mem_positivePoints_iff_exists_prod_b2 (A : Type*) [CommRing A]
    {l : List (Fin 4)} (hl : l.Nodup) (hall : ∀ i, i ∈ l) (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : Fin 4 → A,
      (l.map fun i => D.rootSubgroupPoints (b2Index (Fin.castAdd 4 i)) A
        (Multiplicative.ofAdd (u i))).prod = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, hxg⟩ := (D.mem_positivePoints_iff.mp hg)
    have hle : D.positiveSubgroup (CommAlgCat.of ℤ A) ≤
        ⨆ γ ∈ posRoots ((B 2).rationalRootSystem ht) ((B 2).rationalBase ht),
          (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
            D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)).range := by
      rw [D.positiveSubgroup_le_iff]
      intro γ hγ u
      exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ ⟨u, rfl⟩)
    obtain ⟨u, hu⟩ := (mem_biSup_posRoots_b2_iff_exists_list_prod_map D.representation
      D.lattice D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
      (CommAlgCat.of ℤ A) hl hall).mp (hle hx)
    refine ⟨u, ?_⟩
    apply (D.points A).subtype_injective
    have hmatrix := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom) hu
    simp only [map_list_prod, List.map_map, Function.comp_def]
    calc
      _ = (l.map fun i => Units.map
          (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom
          (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
            D.isNilpotent_representation_rootGenerator (b2Index (Fin.castAdd 4 i))
            (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u i)))).prod :=
        congrArg List.prod (List.map_congr_left fun i _ => D.coe_rootSubgroupPoints _ A _)
      _ = _ := by
        simp only [map_list_prod, List.map_map, Function.comp_def] at hmatrix
        -- Reconcile the ring and endomorphism monoid instances on lattice automorphisms.
        convert hmatrix.trans hxg using 1
        rfl
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact D.rootSubgroupPoints_mem_positivePoints A
      ((b2Index_mem_posRoots_rational_iff ht _).mpr i.isLt) _

/-- In the full-weight simply connected B₂ datum, every positive point has exactly one tuple
of four root parameters in any prescribed duplicate-free order. No characteristic or
reducedness hypothesis is needed. -/
theorem mem_positivePoints_iff_existsUnique_prod_b2 (A : Type*) [CommRing A]
    {l : List (Fin 4)} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    (g : ((B 2).scChevalleyDatum ht).points A) :
    g ∈ ((B 2).scChevalleyDatum ht).positivePoints A ↔ ∃! u : Fin 4 → A,
      (l.map fun i => ((B 2).scChevalleyDatum ht).rootSubgroupPoints
        (b2Index (Fin.castAdd 4 i)) A (Multiplicative.ofAdd (u i))).prod = g := by
  classical
  let f : Fin 4 → Fin (B 2).numRoots := fun i => b2Index (Fin.castAdd 4 i)
  have hf : Function.Injective f := b2Index_injective.comp (Fin.castAdd_injective 4 4)
  have hinj : Function.Injective (fun u : Fin 4 → A =>
      (l.map fun i => ((B 2).scChevalleyDatum ht).rootSubgroupPoints
        (f i) A (Multiplicative.ofAdd (u i))).prod) := by
    intro u v huv
    let U := Function.extend f u (fun _ => (0 : A))
    let V := Function.extend f v (fun _ => (0 : A))
    have hprod : ((l.map f).map fun γ => ((B 2).scChevalleyDatum ht).rootSubgroupPoints
        γ A (Multiplicative.ofAdd (U γ))).prod =
        ((l.map f).map fun γ => ((B 2).scChevalleyDatum ht).rootSubgroupPoints
          γ A (Multiplicative.ofAdd (V γ))).prod := by
      simpa only [List.map_map, Function.comp_def, U, V, hf.extend_apply] using huv
    have hparams := ((B 2).list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
      (hl.map hf) (by
        intro γ hγ
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hγ
        exact (b2Index_mem_posRoots_rational_iff ht _).mpr i.isLt)).mp hprod
    funext i
    simpa only [U, V, hf.extend_apply] using
      hparams (f i) (List.mem_map.mpr ⟨i, hall i, rfl⟩)
  rw [((B 2).scChevalleyDatum ht).mem_positivePoints_iff_exists_prod_b2 A hl hall g]
  exact hinj.existsUnique_iff_exists.symm

end TauCeti.DynkinType.ChevalleyDatum
