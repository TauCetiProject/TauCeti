/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2

/-!
# Positive-root coordinates

For a Chevalley datum of any valid Dynkin type, every positive point is an ordered product
of positive root elements. For the simply connected full-weight datum these coordinates are
unique. The ordering may be any list enumerating the positive roots without repetitions.
Parameters are indexed only by positive roots, with no unused coordinates at negative roots.

These are coordinates on the positive subgroup, not a generation theorem for the entire
point group or an identification of the positive subgroup scheme with affine space.
Both results hold over arbitrary commutative rings, including characteristics two and three
and nonreduced rings.

Existence uses `ChevalleyDatum.mem_positiveSubgroup_iff_exists_prod_of_isSimplyLaced`,
`mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod` outside G₂, and
`mem_biSup_posRoots_g2_iff_exists_list_prod_map` in G₂. Uniqueness uses
`list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`, whose integral root-operator
faithfulness comes from the fundamental modules rather than an assumption on the value ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

variable {t : DynkinType} {ht : t.Valid}

attribute [local instance high] Algebra.toModule

-- Reindex the native G₂ collection theorem by positive roots rather than its six-row table.
private theorem exists_prod_of_mem_iSup_G2 {ht : G2.Valid} (D : ChevalleyDatum G2 ht)
    (l : List (posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht)))
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type*) [CommRing A]
    (q : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice))
    (hq : q ∈ ⨆ γ ∈ posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht),
      (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)).range) :
    ∃ u : posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht) → A,
      (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ.val
          (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u γ))).prod = q := by
  let e : posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht) ≃ Fin 6 :=
    { toFun := fun γ => ⟨γ.val.val, (mem_posRoots_rational_g2_iff ht γ.val).mp γ.property⟩
      invFun := fun i => ⟨Fin.castAdd 6 i, (mem_posRoots_rational_g2_iff ht _).mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨u, hu⟩ := (mem_biSup_posRoots_g2_iff_exists_list_prod_map
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A)
    (l.map e) (hl.map e.injective)
    (fun i => List.mem_map.mpr ⟨e.symm i, hcover _, e.apply_symm_apply i⟩) q).mp hq
  have he (γ) : Fin.castAdd 6 (e γ) = γ.val := Fin.ext rfl
  exact ⟨fun γ => u (e γ), by simpa only [List.map_map, Function.comp_def, he] using hu⟩

/-- Over every commutative ring, a positive point of a Chevalley datum is a product
of positive root elements in any prescribed order without repetitions. -/
theorem ChevalleyDatum.mem_positivePoints_iff_exists_prod
    (D : ChevalleyDatum t ht)
    (l : List (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)))
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type*) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : posRoots (t.rationalRootSystem ht)
        (t.rationalBase ht) → A,
      (l.map fun γ => D.rootSubgroupPoints γ.val A (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  constructor
  · intro hg
    obtain ⟨q, hq, hqg⟩ := Subgroup.mem_map.mp (D.mem_positivePoints_iff.mp hg)
    have hq' : q ∈ ⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)).range := by
      refine D.positiveSubgroup_le_iff.mpr (fun γ hγ u => ?_) hq
      exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ ⟨u, rfl⟩)
    have hlist : ∀ γ, γ ∈ l.map Subtype.val ↔
        γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      intro γ
      simp only [List.mem_map]
      exact ⟨fun ⟨δ, _, hδ⟩ => hδ ▸ δ.property,
        fun hγ => ⟨⟨γ, hγ⟩, hcover _, rfl⟩⟩
    -- Collect on the lattice first; only the collection step depends on the Dynkin family.
    have hcollect [(t.rationalRootSystem ht).IsNotG2] :
        ∃ u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A,
          (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
            D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ.val
              (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u γ))).prod = q := by
      obtain ⟨u, hu⟩ := (mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod
        D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A)
        (l.map Subtype.val) (hl.map Subtype.val_injective) hlist q).mp hq'
      exact ⟨fun γ => u γ.val, by simpa only [List.map_map, Function.comp_def] using hu⟩
    have hex : ∃ u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A,
        (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ.val
            (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u γ))).prod = q := by
      by_cases hs : t.IsSimplyLaced
      · obtain ⟨u, hu⟩ := (D.mem_positiveSubgroup_iff_exists_prod_of_isSimplyLaced hs
          (l.map Subtype.val) (hl.map Subtype.val_injective) hlist (CommAlgCat.of ℤ A) q).mp hq
        exact ⟨fun γ => (u γ.val).toAdd, by
          simpa only [ofAdd_toAdd, List.map_map, Function.comp_def] using hu⟩
      · cases t with
        | B n | C n | F4 => exact hcollect
        | G2 => exact exists_prod_of_mem_iSup_G2 D l hl hcover A q hq'
        | _ => simp at hs
    -- The same matrix map transports every family to the datum's point group.
    obtain ⟨u, hu⟩ := hex
    refine ⟨u, Subtype.ext ?_⟩
    have hmatrix := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.val_list_prod,
      D.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using hmatrix.trans hqg
  · rintro ⟨u, rfl⟩
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
      exact D.rootSubgroupPoints_mem_positivePoints A γ.property _

/-- In the simply connected model of any valid Dynkin type, every positive point has exactly
one tuple of positive-root parameters, in any prescribed order without repetitions. No field or
characteristic restriction is required. -/
theorem existsUnique_prod_scChevalleyDatum_rootSubgroupPoints
    (l : List (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)))
    (hl : l.Nodup) (hcover : ∀ γ, γ ∈ l)
    (A : Type*) [CommRing A] (g : (t.scChevalleyDatum ht).points A)
    (hg : g ∈ (t.scChevalleyDatum ht).positivePoints A) :
    ∃! u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A,
      (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ.val A
        (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  have hinj : Function.Injective (fun u : posRoots (t.rationalRootSystem ht)
      (t.rationalBase ht) → A =>
      (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ.val A
        (Multiplicative.ofAdd (u γ))).prod) := by
    intro u v huv
    let u' := Function.extend Subtype.val u (fun _ => 0)
    let v' := Function.extend Subtype.val v (fun _ => 0)
    have hprod : ((l.map Subtype.val).map fun γ =>
        (t.scChevalleyDatum ht).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (u' γ))).prod =
      ((l.map Subtype.val).map fun γ =>
        (t.scChevalleyDatum ht).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (v' γ))).prod := by
      simpa only [List.map_map, Function.comp_def, u', v', Subtype.val_injective.extend_apply]
        using huv
    have heq := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A
      (hl.map Subtype.val_injective)
      (fun γ hγ => by
        obtain ⟨δ, _, rfl⟩ := List.mem_map.mp hγ
        exact δ.property)).mp hprod
    funext γ
    simpa only [u', v', Subtype.val_injective.extend_apply] using
      heq γ.val (List.mem_map.mpr ⟨γ, hcover γ, rfl⟩)
  exact hinj.existsUnique_iff_exists.mpr
    (((t.scChevalleyDatum ht).mem_positivePoints_iff_exists_prod l hl hcover A g).mp hg)

end TauCeti.DynkinType
