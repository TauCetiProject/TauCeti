/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.DoublyLaced
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree
public import TauCeti.GroupTheory.Commutator
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Height-raising positive-root commutators outside G₂

On every Kostant-stable lattice whose rational root system satisfies `IsNotG2`, commutators of
positive root subgroups lie in the join of positive root subgroups of strictly greater root height
over every commutative ring, including characteristic two and nonreduced rings. In particular, this
applies to classical types B and C as well as F₄.

The `IsNotG2` hypothesis excludes triple root strings, so the native one- and two-factor integral
commutator formulas show that commutators strictly raise height without inverting structure
constants. Ordered-product collection across all valid Dynkin types is derived uniformly in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 15 and 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorems 5.2.2 and 5.3.3.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid}

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
    ∀ v ∈ M, ρ u v ∈ M)
  (hnil : ∀ i, IsNilpotent
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

private theorem commutator_mem_higher_roots
    [(t.rationalRootSystem ht).IsNotG2]
    {α β : Fin t.numRoots}
    (hα : α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (hβ : β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ ∈
      ⨆ γ ∈ {γ ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        max ((t.rationalBase ht).height α) ((t.rationalBase ht).height β) <
          (t.rationalBase ht).height γ},
        (chevalleyRootSubgroup ρ M hM hnil γ A).range := by
  classical
  let P := t.rationalRootSystem ht
  let Q := t.simplyConnectedRootDatum ht
  let b := t.rationalBase ht
  let H := ⨆ γ ∈ {γ ∈ posRootsFinset P b | max (b.height α) (b.height β) < b.height γ},
    (chevalleyRootSubgroup ρ M hM hnil γ A).range
  have hmem {d : Fin t.numRoots} (hd : d ∈ posRoots P b)
      (hheight : max (b.height α) (b.height β) < b.height d) (w : Multiplicative A) :
      chevalleyRootSubgroup ρ M hM hnil d A w ∈ H :=
    (le_iSup₂ (f := fun γ _ => (chevalleyRootSubgroup ρ M hM hnil γ A).range)
      d (Finset.mem_filter.mpr ⟨(mem_posRootsFinset P b d).mpr hd, hheight⟩)) ⟨w, rfl⟩
  have he := t.pairingIn_rationalRootSystem ht
  have hadd := RootPairing.root_eq_add_iff_of_pairingIn (Equiv.refl _) he
  by_cases hsum : P.root α + P.root β ∈ Set.range P.root
  · obtain ⟨γ, hγ⟩ := hsum
    have hγZ : Q.root γ = Q.root α + Q.root β := (hadd γ α β).mp hγ
    have hγpos := add_mem_posRoots P b hα hβ hγ
    have hγlt : max (b.height α) (b.height β) < b.height γ := by
      rw [b.height_add hγ, max_lt_iff]
      exact ⟨lt_add_of_pos_right _ (b.isPos_iff.mp ((mem_posRoots P b β).mp hβ)),
        lt_add_of_pos_left _ (b.isPos_iff.mp ((mem_posRoots P b α).mp hα))⟩
    have hdouble {a d : Fin t.numRoots} (ha : a ∈ posRoots P b)
        (hd : Q.root d = Q.root a + Q.root γ) (w : Multiplicative A) :
        chevalleyRootSubgroup ρ M hM hnil d A w ∈ H := by
      have hdQ := (hadd d a γ).mpr hd
      refine hmem (add_mem_posRoots P b ha hγpos hdQ) ?_ w
      rw [b.height_add hdQ]
      exact hγlt.trans (lt_add_of_pos_left _ (b.isPos_iff.mp ((mem_posRoots P b a).mp ha)))
    have hne : t ≠ .G2 := isNotG2_rationalRootSystem_iff.mp inferInstance
    by_cases ha : Q.root α + Q.root γ ∈ Set.range Q.root
    · obtain ⟨δ, hδ⟩ := ha
      rw [commutatorElement_chevalleyRootSubgroup_of_ne_G2_of_root_eq_add_of_root_eq_add
        ρ M hM hnil hne hγZ hδ]
      exact H.mul_mem (hmem hγpos hγlt _) (hdouble hα hδ _)
    · by_cases hb : Q.root β + Q.root γ ∈ Set.range Q.root
      · obtain ⟨δ, hδ⟩ := hb
        rw [← commutatorElement_inv,
          commutatorElement_chevalleyRootSubgroup_of_ne_G2_of_root_eq_add_of_root_eq_add
            ρ M hM hnil hne (hγZ.trans (add_comm _ _)) hδ]
        exact H.inv_mem (H.mul_mem (hmem hγpos hγlt _) (hdouble hβ hδ _))
      · rw [commutatorElement_chevalleyRootSubgroup_of_root_eq_add ρ M hM hnil hγZ
          (by simpa only [hγZ, two_nsmul, add_assoc] using ha)
          (by simpa only [hγZ, two_nsmul, add_left_comm] using hb)]
        exact hmem hγpos hγlt _
  · have hsZ := mt (RootPairing.root_add_mem_range_iff_of_pairingIn (Equiv.refl _) he α β).mpr hsum
    have hzero : Q.root α + Q.root β ≠ 0 := fun hz ↦
      (add_pos (t.weightDegree_root_pos ht hα) (t.weightDegree_root_pos ht hβ)).ne' (by
        simpa only [map_add, map_zero] using congrArg (t.weightDegree ht) hz)
    rw [(commute_chevalleyRootSubgroup ρ M hM hnil hsZ hzero A u v).commutator_eq]
    exact H.one_mem

/-- Outside G₂, commutators of positive root groups strictly raise root height over
any commutative value ring. The roots are those of the native pinned positive system. -/
theorem commutator_range_chevalleyRootSubgroup_le
    [(t.rationalRootSystem ht).IsNotG2]
    {α β : Fin t.numRoots}
    (hα : α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (hβ : β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat ℤ) :
    ⁅(chevalleyRootSubgroup ρ M hM hnil α A).range,
      (chevalleyRootSubgroup ρ M hM hnil β A).range⁆ ≤
      ⨆ γ ∈ {γ ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        max ((t.rationalBase ht).height α) ((t.rationalBase ht).height β) <
          (t.rationalBase ht).height γ},
        (chevalleyRootSubgroup ρ M hM hnil γ A).range := by
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  exact commutator_mem_higher_roots ρ M hM hnil hα hβ A u.toAdd v.toAdd

end

end TauCeti.DynkinType
