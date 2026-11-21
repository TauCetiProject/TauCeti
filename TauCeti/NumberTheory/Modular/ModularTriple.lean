/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.GroupTheory.TriangleGroup.Regular
public import TauCeti.NumberTheory.Modular.Generators

/-!
# The modular triple of a subgroup of `PSL(2, ℤ)`

`PSL(2, ℤ)` acts on the left cosets `g Γ` of a subgroup `Γ` by left multiplication. Numbering
the cosets by `e : PSL(2, ℤ) ⧸ Γ ≃ Fin n` turns the action into the permutation representation
`ρ := e.permutationRepresentation`, and the *modular triple* of `Γ` is the permutation triple
`(σ0, σ1, σinf) := (ρ U, ρ S, ρ T)` with `U = S T⁻¹`. The product relation `σinf σ1 σ0 = 1` of a
permutation triple is the projective relation `T S U = 1`, and `σ0 ^ 3 = σ1 ^ 2 = 1`. This is
the combinatorial datum from which the cusp widths (the cycles of `σinf`), the elliptic points
(the fixed points of `σ1` and `σ0`) and the genus of `Γ` are read off. The permutations
`σ1 = ρ S`, `σinf = ρ T` and `ρ R`, where `R = S T`, are the ones the LMFDB calls `permS`, `permT`
and `permR`, although its tabulated rows are written in the opposite composition convention.

The triple is built as the triple of the representation `ρ ∘ modularHom` of the triangle group
`Δ(3, 2, ∞)`, so it is the coset triple of the preimage of `Γ` in the triangle group
(`TauCeti.ModularGroup.modularTriple_eq_cosetTriple`). Only the surjectivity of `modularHom` is
used for this, not the presentation `PSL(2, ℤ) ≅ Δ(3, 2, ∞)`.

## Main definitions

* `TauCeti.ModularGroup.modularTriple`: the modular triple of `Γ` for a numbering `e` of its
  cosets.
* `TauCeti.ModularGroup.modularIsoClass`: its isomorphism class, which does not depend on the
  numbering, for `Γ` of finite index.

## Main results

* `TauCeti.ModularGroup.modularTriple_σ1_mul_σinf` and
  `TauCeti.ModularGroup.modularTriple_σ1_inv_mul_σ0_inv_mul_σ1`: the permutation of `R = S T` is
  `σ1 σinf = σ1⁻¹ σ0⁻¹ σ1`.
* `TauCeti.ModularGroup.modularTriple_eq_cosetTriple`: the modular triple is the coset triple of
  the preimage of `Γ` in `Δ(3, 2, ∞)`, numbered through the induced bijection of cosets.
* `TauCeti.ModularGroup.isConnected_modularTriple`: the modular triple is connected; in
  particular `n ≠ 0`, while `Nat.card_eq_of_equiv_fin e` gives `Γ.index = n`.
* `TauCeti.ModularGroup.modularTriple_eq_smul` and `TauCeti.ModularGroup.equivalent_modularTriple`:
  changing the numbering relabels the triple.
* `TauCeti.ModularGroup.quotientNormalCoreMulEquivMonodromyGroup`: the monodromy group of the
  modular triple is `PSL(2, ℤ) ⧸ Γ.normalCore`, so its order is the index of the normal core
  (`TauCeti.ModularGroup.natCard_monodromyGroup_modularTriple`).
* `TauCeti.ModularGroup.isRegular_modularTriple_iff`: the modular triple is regular exactly when
  `Γ` is normal.
* `TauCeti.ModularGroup.isConnected_modularIsoClass`: the isomorphism class of the modular triple
  is connected.

## References

* R. S. Kulkarni, *An arithmetic-geometric method in the study of the subgroups of the modular
  group*, Amer. J. Math. 113 (1991), 1053–1133.
* C. Kurth, L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey symbols*,
  arXiv:0710.1835, §4.
* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1
  (1969), 351–357.
-/

public section

open Equiv
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

variable {n : ℕ} (Γ : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ ≃ Fin n)

/-- **The modular triple** of a subgroup `Γ` of `PSL(2, ℤ)` whose cosets are numbered by `e`:
the permutations `(σ0, σ1, σinf) = (ρ U, ρ S, ρ T)` of the cosets, where `ρ` is the action of
`PSL(2, ℤ)` on the left cosets `g Γ` by left multiplication and `U = S T⁻¹`. It is the triple of
the representation `ρ ∘ modularHom` of the triangle group `Δ(3, 2, ∞)`. -/
noncomputable def modularTriple : PermutationTriple n :=
  (TriangleGroup.permutationTripleEquiv
    ((e.permutationRepresentation (G := PSL(2, ℤ))).comp modularHom)).1

@[simp]
theorem modularTriple_σ0 :
    (modularTriple Γ e).σ0 = e.permutationRepresentation (U : PSL(2, ℤ)) := by
  simp [modularTriple]

@[simp]
theorem modularTriple_σ1 :
    (modularTriple Γ e).σ1 = e.permutationRepresentation (S : PSL(2, ℤ)) := by
  simp [modularTriple]

@[simp]
theorem modularTriple_σinf :
    (modularTriple Γ e).σinf = e.permutationRepresentation (T : PSL(2, ℤ)) := by
  simp [modularTriple]

/-- The permutation `σ0` of `U` has order dividing three. -/
theorem modularTriple_σ0_pow_three : (modularTriple Γ e).σ0 ^ 3 = 1 :=
  (TriangleGroup.permutationTripleEquiv
    ((e.permutationRepresentation (G := PSL(2, ℤ))).comp modularHom)).2.1

/-- The permutation `σ1` of `S` is an involution. -/
theorem modularTriple_σ1_sq : (modularTriple Γ e).σ1 ^ 2 = 1 :=
  (TriangleGroup.permutationTripleEquiv
    ((e.permutationRepresentation (G := PSL(2, ℤ))).comp modularHom)).2.2.1

/-- The permutation of `R = S T` is `σ1 σinf`. -/
theorem modularTriple_σ1_mul_σinf :
    (modularTriple Γ e).σ1 * (modularTriple Γ e).σinf =
      e.permutationRepresentation (R : PSL(2, ℤ)) := by
  rw [modularTriple_σ1, modularTriple_σinf, ← map_mul, R_def, QuotientGroup.mk_mul]

/-- The permutation of `R = S T` is also `σ1⁻¹ σ0⁻¹ σ1`, since `R = S⁻¹ U⁻¹ S` projectively. -/
theorem modularTriple_σ1_inv_mul_σ0_inv_mul_σ1 :
    (modularTriple Γ e).σ1⁻¹ * (modularTriple Γ e).σ0⁻¹ * (modularTriple Γ e).σ1 =
      e.permutationRepresentation (R : PSL(2, ℤ)) := by
  rw [modularTriple_σ1, modularTriple_σ0, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← coe_S_mul_coe_R_inv_mul_coe_S_inv]
  congr 1
  group

/-- The representation of `Δ(3, 2, ∞)` attached to the modular triple is the action on the
cosets of `Γ` through `modularHom`. -/
@[simp]
theorem toPerm_modularTriple {ha hb hc} :
    TriangleGroup.toPerm (modularTriple Γ e) ha hb hc =
      (e.permutationRepresentation (G := PSL(2, ℤ))).comp modularHom :=
  TriangleGroup.toPerm_permutationTripleEquiv _

/-- The modular triple is the coset triple of the preimage of `Γ` in `Δ(3, 2, ∞)`, with the
cosets numbered through the bijection of coset spaces induced by `modularHom`. -/
theorem modularTriple_eq_cosetTriple :
    modularTriple Γ e = TriangleGroup.cosetTriple (Γ.comap modularHom)
      ((QuotientGroup.congrComapOfSurjectiveMk modularHom Γ
        (QuotientGroup.mk_surjective.comp modularHom_surjective)).trans e) := by
  have h : ((QuotientGroup.congrComapOfSurjectiveMk modularHom Γ
      (QuotientGroup.mk_surjective.comp modularHom_surjective)).trans e).permutationRepresentation =
        (e.permutationRepresentation (G := PSL(2, ℤ))).comp modularHom :=
    Equiv.permutationRepresentation_eq_of_map_smul _ fun g x ↦ by
      induction x using QuotientGroup.induction_on
      simp [MulAction.Quotient.smul_mk]
  ext1 <;> simp [h]

/-- The monodromy group of the modular triple is the image of the action on the cosets. -/
@[simp]
theorem monodromyGroup_modularTriple :
    (modularTriple Γ e).monodromyGroup = (e.permutationRepresentation (G := PSL(2, ℤ))).range := by
  rw [modularTriple, TriangleGroup.monodromyGroup_permutationTripleEquiv, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr modularHom_surjective, ← MonoidHom.range_eq_map]

/-- The modular triple is connected: `PSL(2, ℤ)` acts transitively on the nonempty set of
cosets. -/
@[simp]
theorem isConnected_modularTriple : (modularTriple Γ e).IsConnected := by
  rw [modularTriple_eq_cosetTriple]
  exact TriangleGroup.isConnected_cosetTriple _ _

/-- Changing the numbering of the cosets from `e` to `e'` relabels the modular triple by the
re-indexing permutation `e.symm.trans e'`. -/
theorem modularTriple_eq_smul (e' : PSL(2, ℤ) ⧸ Γ ≃ Fin n) :
    modularTriple Γ e' = (e.symm.trans e') • modularTriple Γ e := by
  ext1 <;> simp [Equiv.permutationRepresentation_eq_conj e e']

/-- Changing the numbering of the cosets relabels the modular triple, so its isomorphism class
does not depend on the numbering. -/
theorem equivalent_modularTriple (e' : PSL(2, ℤ) ⧸ Γ ≃ Fin n) :
    (modularTriple Γ e).Equivalent (modularTriple Γ e') :=
  PermutationTriple.equivalent_iff_exists_smul_eq.mpr ⟨_, (modularTriple_eq_smul Γ e e').symm⟩

/-- `PSL(2, ℤ) ⧸ Γ.normalCore` is the monodromy group of the modular triple, by the first
isomorphism theorem for the action on the cosets, whose kernel is the normal core of `Γ`. -/
noncomputable def quotientNormalCoreMulEquivMonodromyGroup :
    PSL(2, ℤ) ⧸ Γ.normalCore ≃* (modularTriple Γ e).monodromyGroup :=
  (Equiv.quotientNormalCoreMulEquivRange e).trans
    (MulEquiv.subgroupCongr (monodromyGroup_modularTriple Γ e)).symm

/-- The coset of `g` modulo the normal core corresponds to the permutation of `g`. -/
@[simp]
theorem coe_quotientNormalCoreMulEquivMonodromyGroup_mk (g : PSL(2, ℤ)) :
    (quotientNormalCoreMulEquivMonodromyGroup Γ e g : Perm (Fin n)) =
      e.permutationRepresentation g := by
  simp [quotientNormalCoreMulEquivMonodromyGroup]

/-- The order of the monodromy group of the modular triple is the index of the normal core of
`Γ`. -/
theorem natCard_monodromyGroup_modularTriple :
    Nat.card (modularTriple Γ e).monodromyGroup = Γ.normalCore.index := by
  rw [monodromyGroup_modularTriple,
    Equiv.natCard_range_permutationRepresentation_eq_index_normalCore]

/-- **The modular triple is regular exactly when `Γ` is normal**, that is, exactly when its
monodromy group has order the index `n`
(`TauCeti.PermutationTriple.isRegular_iff_card_monodromyGroup`). -/
@[simp]
theorem isRegular_modularTriple_iff : (modularTriple Γ e).IsRegular ↔ Γ.Normal := by
  rw [modularTriple_eq_cosetTriple, TriangleGroup.isRegular_cosetTriple_iff,
    Subgroup.normal_comap_iff_of_surjective modularHom_surjective]

/-- On the whole group the modular triple is trivial: there is a single coset. -/
@[simp]
theorem modularTriple_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin n) :
    modularTriple ⊤ e = 1 := by
  have := QuotientGroup.subsingleton_quotient_top (G := PSL(2, ℤ))
  have := e.symm.subsingleton
  exact Subsingleton.elim _ _

/-- The isomorphism class of the modular triple of a finite-index subgroup `Γ`, a triple of
degree the index of `Γ`. It is the class of `modularTriple Γ e` for every numbering `e`
(`TauCeti.ModularGroup.modularIsoClass_eq_mk`). -/
noncomputable def modularIsoClass [Γ.FiniteIndex] : PermutationTriple.IsoClass Γ.index :=
  .mk (modularTriple Γ (Finite.equivFinOfCardEq Γ.index_eq_card.symm))

/-- The isomorphism class of the modular triple is that of the triple of any numbering. -/
theorem modularIsoClass_eq_mk [Γ.FiniteIndex] (e : PSL(2, ℤ) ⧸ Γ ≃ Fin Γ.index) :
    modularIsoClass Γ = .mk (modularTriple Γ e) :=
  PermutationTriple.IsoClass.mk_eq_mk_iff.mpr (equivalent_modularTriple Γ _ e)

/-- The isomorphism class of the modular triple is connected. -/
@[simp]
theorem isConnected_modularIsoClass [Γ.FiniteIndex] : (modularIsoClass Γ).IsConnected := by
  rw [modularIsoClass, PermutationTriple.IsoClass.isConnected_mk]
  exact isConnected_modularTriple Γ _

end TauCeti.ModularGroup
