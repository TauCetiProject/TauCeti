/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.ClassFieldTheory.ClassField
import TauCeti.NumberTheory.ClassFieldTheory.Formation.CoprimeNorm
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree

/-!
# The second fundamental inequality from its Kummer case

Let `K` be a number field. The **second fundamental inequality** for the idele-class formation
`globalFormation K` says that `#H²(U/V, C_L) ∣ [U : V]` on every finite normal layer `V ◁ U`, and it
comes together with the vanishing of `H¹(U/V, C_L)` (Milne, *Class Field Theory*, VII,
Theorem 5.1). Classically both are reduced, by Sylow and tower arguments, to cyclic extensions of
prime degree `p`, and then, by adjoining the `p`-th roots of unity, to the **Kummer case**: for a
cyclic extension `L/F` of number fields of prime degree `p` whose ground field `F` contains the
`p`-th roots of unity,

```text
[C_F : N_{L/F}(C_L)] ≤ p.
```

This file assembles that reduction for the idele-class formation. It shows that the Kummer case,
for all number fields, implies `H¹ = 0` and `#H² ∣ [U : V]` for every layer of `globalFormation K`
(`subsingleton_h1_globalFormation_of_forall_index_le`,
`natCard_H2_globalFormation_dvd_degree_of_forall_index_le`). The Kummer case itself, Milne's
computation with the `S`-units and the auxiliary set of places `T` of VII §6, is not proved here.

The steps are the following.

* A layer `V ◁ U` whose ground field `F`, the fixed field of `U`, contains the `p`-th roots of unity
  of `Kˢ` and whose degree is `p` is read on number fields: with `L` the fixed field of `V`, the
  extension `L/F` is Galois of degree `p` (`NormalLayer.galEquivOfFixedField`), `F` contains a
  primitive `p`-th root of unity, and the norm quotient of the layer is
  `C_F / N_{L/F}(C_L)` (`NormalLayer.ideleClassNormQuotientEquiv`). The Kummer case bounds its
  order by `p`.
* With the first inequality (`degree_le_natCard_normQuotient_of_isCyclic`), the norm quotient of
  every such layer has exactly `p` elements, and adjoining the `p`-th roots of unity, a step of
  degree prime to `p`, carries the divisibility `#(C_F / N_{L/F}(C_L)) ∣ p` to every layer of
  prime degree `p` (`NormalLayer.natCard_normQuotient_dvd_prime_of_adjoin_nth_roots`). So every
  layer of prime degree has norm quotient of order its degree
  (`natCard_normQuotient_globalFormation_eq_degree_of_forall_index_le`).
* A layer of prime degree is cyclic, so its Herbrand quotient is its degree
  (`herbrandQuotient_rep_globalFormation_eq_degree`). The reduction to layers of prime degree
  (`NormalLayer.subsingleton_h1_of_herbrandQuotient_of_prime_degree`,
  `NormalLayer.natCard_H2_dvd_degree_of_herbrandQuotient_of_prime_degree`) then gives the two
  statements for every layer.

## Main results

* `TauCeti.ClassFieldTheory.natCard_normQuotient_globalFormation_eq_degree_of_forall_index_le`:
  from the Kummer case, a layer of prime degree has norm quotient of order its degree.
* `TauCeti.ClassFieldTheory.subsingleton_h1_globalFormation_of_forall_index_le`: from the Kummer
  case, `H¹` of every layer of the idele-class formation vanishes.
* `TauCeti.ClassFieldTheory.natCard_H2_globalFormation_dvd_degree_of_forall_index_le`: from the
  Kummer case, the order of `H²` of every layer divides its degree.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §5 (Theorem 5.1 and its reduction to the
  Kummer case) and §6.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4.
-/

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]
  (h : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p],
    Module.finrank F L = p → (GlobalNumberFields.ideleClassNormMap F L).range.index ≤ p)

include h in
/-- **A layer of degree `p` over the `p`-th roots of unity, read on number fields.** If a layer
`V ◁ U` of `globalFormation K` has prime degree `p` and its ground subgroup fixes the `p`-th roots
of unity of `Kˢ`, then, with `F` and `L` the fixed fields of `U` and `V`, the extension `L/F` is
Galois of degree `p`, `F` has enough `p`-th roots of unity, and the norm quotient of the layer has
the order of `C_F / N_{L/F}(C_L)`. So a bound on the index of the norm group in the Kummer case
bounds the order of the norm quotient. -/
private theorem natCard_normQuotient_le_of_le_fixingSubgroup
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) {p : ℕ} [Fact p.Prime] (hdeg : Lay.degree = p)
    (hμ : Lay.ground.toSubgroup ≤
      (adjoin K {x : SeparableClosure K | x ^ p = 1}).fixingSubgroup) :
    Nat.card (Lay.NormQuotient (globalFormation K)) ≤ p := by
  have hle : fixedField Lay.ground.toSubgroup ≤ fixedField Lay.top.toSubgroup :=
    fixedField_le (OpenSubgroup.toSubgroup_le.2 Lay.top_le_ground)
  have : NumberField (fixedField Lay.ground.toSubgroup) := .of_module_finite K _
  have : NumberField (fixedField Lay.top.toSubgroup) := .of_module_finite K _
  let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower (fixedField Lay.ground.toSubgroup) (fixedField Lay.top.toSubgroup)
      (SeparableClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have := Lay.isGalois_of_fixedField rfl rfl
  -- The ground field contains the `p`-th roots of unity of `Kˢ`, among them a primitive one.
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) p
  have hζF : ζ ∈ fixedField Lay.ground.toSubgroup :=
    (le_iff_le _ _).2 hμ (subset_adjoin K _ hζ.pow_eq_one)
  have : HasEnoughRootsOfUnity (fixedField Lay.ground.toSubgroup) p :=
    ⟨⟨⟨ζ, hζF⟩, hζ.of_map_of_injective (f := (fixedField Lay.ground.toSubgroup).val)
      (fixedField Lay.ground.toSubgroup).val.injective⟩, inferInstance⟩
  have hfin : Module.finrank (fixedField Lay.ground.toSubgroup) (fixedField Lay.top.toSubgroup) =
      p := by
    rw [← IsGalois.card_aut_eq_finrank, ← hdeg, NormalLayer.degree_eq_natCard_gal,
      Nat.card_congr (Lay.galEquivOfFixedField rfl rfl).toEquiv]
  -- The norm quotient of the layer is `C_F / N_{L/F}(C_L)`, written additively.
  calc Nat.card (Lay.NormQuotient (globalFormation K))
      = (GlobalNumberFields.ideleClassNormMap (fixedField Lay.ground.toSubgroup)
          (fixedField Lay.top.toSubgroup)).range.index := by
        rw [Subgroup.index_eq_card]
        exact (Nat.card_congr (Lay.ideleClassNormQuotientEquiv rfl rfl).toEquiv).symm.trans
          (Nat.card_congr Additive.ofMul.symm)
    _ ≤ p := h _ _ p hfin

include h in
/-- **The norm index of a layer of prime degree, from the Kummer case.** Suppose that for every
Galois extension `L/F` of number fields of prime degree `p` such that `F` contains the `p`-th roots
of unity, `N_{L/F}(C_L)` has index at most `p` in `C_F`. Then every layer of prime degree of the
idele-class formation `globalFormation K` has norm quotient of order its degree. -/
theorem natCard_normQuotient_globalFormation_eq_degree_of_forall_index_le
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) (hp : Lay.degree.Prime) :
    Nat.card (Lay.NormQuotient (globalFormation K)) = Lay.degree := by
  have := NormalLayer.isCyclic_gal_of_prime_degree hp
  have : Fact Lay.degree.Prime := ⟨hp⟩
  -- Over the `p`-th roots of unity, the Kummer case and the first inequality give `= p`, and
  -- adjoining them carries the divisibility by `p` down to `Lay`.
  refine le_antisymm (Nat.le_of_dvd hp.pos ?_) (degree_le_natCard_normQuotient_of_isCyclic Lay)
  refine NormalLayer.natCard_normQuotient_dvd_prime_of_adjoin_nth_roots _ hp
    (fun L' hL' hμ ↦ ?_) Lay rfl
  have := NormalLayer.isCyclic_gal_of_prime_degree (hL' ▸ hp)
  refine (le_antisymm (natCard_normQuotient_le_of_le_fixingSubgroup h L' hL' hμ) ?_).dvd
  exact hL' ▸ degree_le_natCard_normQuotient_of_isCyclic L'

include h in
/-- **`H¹` of the idele classes vanishes, from the Kummer case.** Suppose that for every Galois
extension `L/F` of number fields of prime degree `p` such that `F` contains the `p`-th roots of
unity, `N_{L/F}(C_L)` has index at most `p` in `C_F`. Then `H¹` of every layer of the idele-class
formation `globalFormation K` vanishes. -/
theorem subsingleton_h1_globalFormation_of_forall_index_le
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) :
    Subsingleton (Lay.H (globalFormation K) 1) :=
  Lay.subsingleton_h1_of_herbrandQuotient_of_prime_degree _ fun L' _ _ hp ↦
    have := NormalLayer.isCyclic_gal_of_prime_degree hp
    ⟨herbrandQuotient_rep_globalFormation_eq_degree L',
      (natCard_normQuotient_globalFormation_eq_degree_of_forall_index_le h L' hp).dvd⟩

include h in
/-- **The second fundamental inequality, from the Kummer case.** Suppose that for every Galois
extension `L/F` of number fields of prime degree `p` such that `F` contains the `p`-th roots of
unity, `N_{L/F}(C_L)` has index at most `p` in `C_F`. Then the order of `H²` of every layer
`V ◁ U` of the idele-class formation `globalFormation K` divides its degree `[U : V]`. -/
theorem natCard_H2_globalFormation_dvd_degree_of_forall_index_le
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) :
    Nat.card (Lay.H (globalFormation K) 2) ∣ Lay.degree :=
  Lay.natCard_H2_dvd_degree_of_herbrandQuotient_of_prime_degree _ fun L' _ _ hp ↦
    have := NormalLayer.isCyclic_gal_of_prime_degree hp
    ⟨herbrandQuotient_rep_globalFormation_eq_degree L',
      (natCard_normQuotient_globalFormation_eq_degree_of_forall_index_le h L' hp).dvd⟩

end TauCeti.ClassFieldTheory
