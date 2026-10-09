/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Transfer.Basic
public import TauCeti.Topology.Covering.Comp

/-!
# Composition of singular transfers

For a tower `E ⟶ B ⟶ A` of covering maps with finite fibres, transferring from `A` to `E`
agrees with transferring first to `B` and then to `E`, on singular chains and on homology.
The result uses the sum-of-lifts characterization of `IsCoveringMap.singularTransfer`: lifts
through the composite are partitioned by their image in `B`. No connectedness, surjectivity,
or constant fibre cardinality is required.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G, for the singular transfer of a finite covering.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace IsCoveringMap

variable {E B A : TopCat.{w}} {p : E ⟶ B} {q : B ⟶ A}
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The transfer of a composite of finite-fibre coverings is the composite of their transfers,
in the reverse order. The composite fibre proof `hfinpq` follows from `hfinp` and `hfinq` using
`Set.Finite.preimage'`; it records finiteness without imposing an additional restriction. -/
theorem singularTransfer_comp (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (hfinq : ∀ a, Finite ↥(q ⁻¹' {a})) (hfinp : ∀ b, Finite ↥(p ⁻¹' {b}))
    (hfinpq : ∀ a, Finite ↥((p ≫ q) ⁻¹' {a})) (R : C) :
    (hq.comp hp (fun a ↦ Set.finite_coe_iff.mp (hfinq a))).singularTransfer hfinpq R =
      hq.singularTransfer hfinq R ≫ hp.singularTransfer hfinp R := by
  classical
  let hpq : IsCoveringMap (p ≫ q) :=
    hq.comp hp (fun a ↦ Set.finite_coe_iff.mp (hfinq a))
  ext n σ
  simp only [HomologicalComplex.comp_f, ιChainComplex_singularTransfer_f_assoc,
    ιChainComplex_singularTransfer_f, Preadditive.sum_comp]
  let s := (hpq.finite_preimage_singleton_toSSet_map_app hfinpq σ).toFinset
  let t := (hq.finite_preimage_singleton_toSSet_map_app hfinq σ).toFinset
  have hmaps : ∀ τ ∈ s, (TopCat.toSSet.map p).app _ τ ∈ t := by
    intro τ hτ
    simpa [s, t, ← NatTrans.comp_app_apply, ← Functor.map_comp] using hτ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun τ hτ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext υ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_singleton_iff] at hτ ⊢
  simp only [s, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
    Functor.map_comp, NatTrans.comp_app_apply]
  constructor
  · exact And.right
  · intro hυ
    exact ⟨hυ ▸ hτ, hυ⟩

/-- Singular homology transfers compose contravariantly along a tower of finite-fibre
coverings. -/
theorem homologyMap_singularTransfer_comp [CategoryWithHomology C]
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (hfinq : ∀ a, Finite ↥(q ⁻¹' {a})) (hfinp : ∀ b, Finite ↥(p ⁻¹' {b}))
    (hfinpq : ∀ a, Finite ↥((p ≫ q) ⁻¹' {a})) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((hq.comp hp (fun a ↦ Set.finite_coe_iff.mp (hfinq a))).singularTransfer hfinpq R) n =
      HomologicalComplex.homologyMap (hq.singularTransfer hfinq R) n ≫
        HomologicalComplex.homologyMap (hp.singularTransfer hfinp R) n := by
  rw [singularTransfer_comp, HomologicalComplex.homologyMap_comp]

end IsCoveringMap
