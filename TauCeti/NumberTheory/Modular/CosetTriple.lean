/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup
public import TauCeti.Combinatorics.PermutationTriple.Examples
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import TauCeti.GroupTheory.TriangleGroup.CosetTriple
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjJ
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# The modular coset triple, Millington's theorem, and subgroup counts

Through `TauCeti.ModularGroup.modularEquiv : TriangleGroup 3 2 0 ≃* PSL(2, ℤ)` sending `x, y, z` to
`U = S T⁻¹`, `S`, and `T`, every subgroup `Γ'` of `PSL(2, ℤ)` with a coset numbering
`e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` determines a connected permutation triple
`TauCeti.ModularGroup.modularTriple Γ' e` (bundled as `modularConnectedTriple Γ' e`) of degree `n`
with `σ0 ^ 3 = 1` and `σ1 ^ 2 = 1`. Specializing `TauCeti.GroupTheory.TriangleGroup.CosetTriple`
along `modularEquiv` gives Millington's dictionary and subgroup counts for `PSL(2, ℤ)`:

* **The modular triple (`TauCeti.ModularGroup.modularTriple`).** Its components are the coset
  permutations of `U`, `S`, and `T` (`permS`, `permT`, and `permR` for `S`, `T`, and `R = S T`).
  Via `TauCeti.ModularGroup.modularTriple_eq_cosetTriple`, it is connected with stabilizer `Γ'` at
  `e 1`, monodromy `PSL(2, ℤ) ⧸ Γ'.normalCore`, and `IsRegular ↔ Γ'.Normal`.
* **Opposite and mirror conventions.** Passing from right cosets `Γ' g` to left cosets via
  `g Γ' ↦ Γ' g⁻¹` gives `TauCeti.ModularGroup.ofRightCosetPerms`
  (`modularTriple_quotientRightRel_eq_ofRightCosetPerms`,
  `modularTriple_quotientEquivOp_eq_ofRightCosetPerms`), and conjugation by `diag(-1, 1)`
  (`TauCeti.ModularGroup.conjJAut`) mirrors the modular triple
  (`TauCeti.ModularGroup.equivalent_mirror_modularTriple`).
* **Millington's theorem (`TauCeti.ModularGroup.millington`, `exists_modularTriple_eq`,
  `modularIsoClassEquiv`, `modularConnectedIsoClassEquiv`, `modularMarkedIsoClassEquiv`).** Modular
  triples are isomorphic iff the subgroups are conjugate in `PSL(2, ℤ)`, giving bijections with
  `modularIsoClasses n`, `{C : ConnectedIsoClass n // C.HasDividingOrders 3 2 0}`, and
  `modularMarkedIsoClasses n` for `n ≠ 0`.
* **Finiteness, class counts, and subgroup counts (`TauCeti.ModularGroup.finite_ofIndex`,
  `natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders`,
  `natCard_ofIndex_eq_sum_div_automorphismOrder`).** For `n ≠ 0`, both collections are finite, the
  number of index-`n` conjugacy classes is `#(connectedIsoClassesWithDividingOrders n 3 2 0)`, and
  the number of index-`n` subgroups is `∑ C, n / C.automorphismOrder`; the all-`n` identities hold
  using `Nat.card`, which returns `0` at `n = 0` where both collections are infinite
  (`infinite_orbitRel_quotient_ofIndex_zero`, `infinite_ofIndex_zero`). Evaluating at `n = 1, 2, 3`
  yields `1, 1, 2` classes and `1, 1, 4` subgroups (`connectedIsoClassesWithDividingOrders_three`,
  `natCard_subgroups_index_three`).

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1 (1969),
  351–357.
* C. Kurth, L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey symbols*,
  in *Advances in Algebra and Combinatorics*, World Scientific (2008), 225–242, arXiv:0710.1835.
-/

open Equiv Matrix
open scoped MatrixGroups Pointwise

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup PermutationTriple

variable {n : ℕ}

/-! ### The modular coset triple and its generator permutations -/

/-- **The modular coset triple** `(σ0, σ1, σinf) = (ρ U, ρ S, ρ T)` attached to a subgroup
`Γ' ≤ PSL(2, ℤ)` and an enumeration `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` of its left cosets, where
`ρ := e.permutationRepresentation`. -/
noncomputable def modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    PermutationTriple n where
  σ0 := e.permutationRepresentation (U : PSL(2, ℤ))
  σ1 := e.permutationRepresentation (S : PSL(2, ℤ))
  σinf := e.permutationRepresentation (T : PSL(2, ℤ))
  product_eq_one := by rw [← map_mul, ← map_mul, coe_T_mul_coe_S_mul_coe_U, map_one]

/-- The `0`-component of `modularTriple Γ' e` is the coset permutation of `U = S T⁻¹`. -/
@[simp] theorem modularTriple_σ0 (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).σ0 = e.permutationRepresentation (U : PSL(2, ℤ)) := (rfl)

/-- The `1`-component of `modularTriple Γ' e` is the coset permutation of `S`. -/
@[simp] theorem modularTriple_σ1 (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).σ1 = e.permutationRepresentation (S : PSL(2, ℤ)) := (rfl)

/-- The `∞`-component of `modularTriple Γ' e` is the coset permutation of `T`. -/
@[simp] theorem modularTriple_σinf (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).σinf = e.permutationRepresentation (T : PSL(2, ℤ)) := (rfl)

/-- The coset permutation of `S`, equal to `(modularTriple Γ' e).σ1`. -/
noncomputable abbrev permS (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : Perm (Fin n) :=
  (modularTriple Γ' e).σ1

/-- The coset permutation of `T`, equal to `(modularTriple Γ' e).σinf`. -/
noncomputable abbrev permT (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : Perm (Fin n) :=
  (modularTriple Γ' e).σinf

/-- The coset permutation of `R = S T`. -/
noncomputable def permR (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : Perm (Fin n) :=
  e.permutationRepresentation (R : PSL(2, ℤ))

/-- `permR Γ' e` factors as `permS Γ' e * permT Γ' e`. -/
theorem permR_eq_permS_mul_permT (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    permR Γ' e = permS Γ' e * permT Γ' e := by
  rw [permR, R_def, QuotientGroup.mk_mul, map_mul, permS, permT, modularTriple_σ1,
    modularTriple_σinf]

/-- `permR Γ' e` is conjugate to `(modularTriple Γ' e).σ0⁻¹` by `permS Γ' e`. -/
theorem permR_eq_permS_inv_mul_σ0_inv_mul_permS (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    permR Γ' e = (permS Γ' e)⁻¹ * (modularTriple Γ' e).σ0⁻¹ * permS Γ' e := by
  rw [permR, permS, modularTriple_σ1, modularTriple_σ0, ← map_inv, ← map_inv, ← map_mul,
    ← map_mul, ← coe_S_mul_coe_R_inv_mul_coe_S_inv]
  exact congrArg _ (by group)

/-- `permR Γ' e` has order dividing `3`. -/
@[simp] theorem permR_pow_three (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    permR Γ' e ^ 3 = 1 := by
  rw [permR, ← map_pow, coe_R_pow_three, map_one]

/-- Integer powers of `permT Γ' e` act on `e (g Γ')` by left multiplication by `T ^ k`. -/
theorem permT_zpow_apply (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (k : ℤ) :
    ((permT Γ' e) ^ k) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e ((((T : PSL(2, ℤ)) ^ k * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  rw [permT, modularTriple_σinf, ← map_zpow, Equiv.permutationRepresentation_apply,
    Equiv.symm_apply_apply, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- Natural powers of `permT Γ' e` act on `e (g Γ')` by left multiplication by `T ^ k`. -/
theorem permT_pow_apply (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (k : ℕ) :
    ((permT Γ' e) ^ k) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e ((((T : PSL(2, ℤ)) ^ k * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  simpa only [zpow_natCast] using permT_zpow_apply Γ' e g k

/-- `(permT Γ' e) ^ k` fixes `e (g Γ')` if and only if `g⁻¹ * T ^ k * g ∈ Γ'`. -/
theorem permT_pow_apply_eq_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (k : ℕ) :
    ((permT Γ' e) ^ k) (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (T : PSL(2, ℤ)) ^ k * g ∈ Γ' := by
  rw [permT, modularTriple_σinf, ← map_pow]
  exact e.permutationRepresentation_quotient_apply_eq_self_iff ((T : PSL(2, ℤ)) ^ k) g

/-- `permS Γ' e` fixes `e (g Γ')` if and only if `g⁻¹ * S * g ∈ Γ'`. -/
theorem permS_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permS Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (S : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [permS, modularTriple_σ1]
  exact e.permutationRepresentation_quotient_apply_eq_self_iff S g

/-- `(modularTriple Γ' e).σ0` fixes `e (g Γ')` if and only if `g⁻¹ * U * g ∈ Γ'`. -/
theorem modularTriple_σ0_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    (modularTriple Γ' e).σ0 (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (U : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [modularTriple_σ0]
  exact e.permutationRepresentation_quotient_apply_eq_self_iff U g

/-- `permR Γ' e` fixes `e (g Γ')` if and only if `g⁻¹ * R * g ∈ Γ'`. -/
theorem permR_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permR Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (R : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [permR]
  exact e.permutationRepresentation_quotient_apply_eq_self_iff R g

/-- Transporting cosets along `modularEquiv : TriangleGroup 3 2 0 ≃* PSL(2, ℤ)` identifies
`modularTriple Γ' e` with `TriangleGroup.cosetTriple`. -/
theorem modularTriple_eq_cosetTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    modularTriple Γ' e =
      TriangleGroup.cosetTriple (Γ'.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)))
        ((TauCeti.QuotientGroup.congrOfMapEq modularEquiv
          (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ')).trans e) := by
  ext1 <;> simp [Equiv.permutationRepresentation_congrOfMapEq]

/-- The `0`-component of `modularTriple Γ' e` has order dividing `3`. -/
theorem modularTriple_σ0_pow_three (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).σ0 ^ 3 = 1 := by
  rw [modularTriple_σ0, ← map_pow, coe_U_pow_three, map_one]

/-- The `1`-component of `modularTriple Γ' e` has order dividing `2`. -/
theorem modularTriple_σ1_sq (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).σ1 ^ 2 = 1 := by
  rw [modularTriple_σ1, ← map_pow, coe_S_sq, map_one]

/-- Every modular coset triple has component orders dividing `(3, 2, 0)`. -/
theorem hasDividingOrders_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).HasDividingOrders 3 2 0 :=
  (hasDividingOrders_iff _).mpr
    ⟨modularTriple_σ0_pow_three Γ' e, modularTriple_σ1_sq Γ' e, pow_zero _⟩

/-- Every modular coset triple is connected. -/
theorem isConnected_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).IsConnected := by
  rw [modularTriple_eq_cosetTriple]
  exact TriangleGroup.isConnected_cosetTriple _ _

/-- `modularTriple Γ' e` bundled as a `ConnectedTriple n`. -/
noncomputable def modularConnectedTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ConnectedTriple n :=
  ⟨modularTriple Γ' e, isConnected_modularTriple Γ' e⟩

/-- The underlying permutation triple of `modularConnectedTriple Γ' e` is `modularTriple Γ' e`. -/
@[simp] theorem coe_modularConnectedTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularConnectedTriple Γ' e : PermutationTriple n) = modularTriple Γ' e := (rfl)

/-- The base point `e 1` has stabilizer `Γ'` under the coset permutation representation. -/
theorem comap_stabilizer_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (MulAction.stabilizer (Perm (Fin n)) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))).comap
        (e.permutationRepresentation (G := PSL(2, ℤ))) = Γ' := by
  rw [Equiv.comap_stabilizer_permutationRepresentation, MulAction.stabilizer_quotient]

/-- Changing the numbering of the cosets of `Γ'` yields an isomorphic modular triple. -/
theorem equivalent_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).Equivalent (modularTriple Γ' e') := by
  rw [modularTriple_eq_cosetTriple Γ' e, modularTriple_eq_cosetTriple Γ' e']
  exact TriangleGroup.equivalent_cosetTriple _ _ _

/-- The connected isomorphism class of the modular triple of a finite-index subgroup
`Γ' ≤ PSL(2, ℤ)`, independent of the coset numbering. -/
noncomputable def modularConnectedIsoClass (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    ConnectedIsoClass Γ'.index :=
  have : NeZero Γ'.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  ConnectedIsoClass.mk (modularConnectedTriple Γ' (Γ'.quotientEquivFin rfl))

/-- `modularConnectedIsoClass Γ'` equals `ConnectedIsoClass.mk (modularConnectedTriple Γ' e)` for
every coset numbering `e`. -/
theorem modularConnectedIsoClass_eq_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin Γ'.index) :
    modularConnectedIsoClass Γ' = ConnectedIsoClass.mk (modularConnectedTriple Γ' e) :=
  ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr (equivalent_modularTriple Γ' _ e)

/-- The isomorphism class of the modular triple of a finite-index subgroup `Γ' ≤ PSL(2, ℤ)`,
independent of the coset numbering. -/
noncomputable def modularIsoClass (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    IsoClass Γ'.index :=
  (modularConnectedIsoClass Γ').forget

/-- Forgetting connectedness of `modularConnectedIsoClass Γ'` yields `modularIsoClass Γ'`. -/
@[simp] theorem forget_modularConnectedIsoClass (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    (modularConnectedIsoClass Γ').forget = modularIsoClass Γ' := (rfl)

/-- `modularIsoClass Γ'` equals `IsoClass.mk (modularTriple Γ' e)` for every coset numbering `e`. -/
theorem modularIsoClass_eq_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin Γ'.index) :
    modularIsoClass Γ' = IsoClass.mk (modularTriple Γ' e) := by
  rw [← forget_modularConnectedIsoClass, modularConnectedIsoClass_eq_mk Γ' e,
    ConnectedIsoClass.forget_mk, coe_modularConnectedTriple]

/-- On the full modular group `⊤`, the modular triple is the trivial triple `1`. -/
@[simp] theorem modularTriple_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    modularTriple ⊤ e = 1 :=
  Subsingleton.elim _ _

/-! ### Monodromy group and regularity -/

/-- The monodromy group of `modularTriple Γ' e` is the image of the coset representation on
`PSL(2, ℤ) ⧸ Γ'`. -/
theorem monodromyGroup_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).monodromyGroup =
      (e.permutationRepresentation (G := PSL(2, ℤ))).range := by
  rw [modularTriple_eq_cosetTriple, TriangleGroup.monodromyGroup_cosetTriple,
    Equiv.permutationRepresentation_congrOfMapEq, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ modularEquiv.surjective, Subgroup.map_top]

/-- The monodromy group of `modularTriple Γ' e` is canonically isomorphic to
`PSL(2, ℤ) ⧸ Γ'.normalCore`. -/
noncomputable def monodromyGroupModularTripleMulEquivQuotientNormalCore
    (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).monodromyGroup ≃* PSL(2, ℤ) ⧸ Γ'.normalCore :=
  (MulEquiv.subgroupCongr (monodromyGroup_modularTriple Γ' e)).trans
    e.rangePermutationRepresentationQuotientMulEquiv

/-- The order of the monodromy group of `modularTriple Γ' e` equals `[PSL(2, ℤ) : Γ'.normalCore]`.
-/
theorem natCard_monodromyGroup_modularTriple (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Nat.card (modularTriple Γ' e).monodromyGroup = Γ'.normalCore.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (monodromyGroupModularTripleMulEquivQuotientNormalCore Γ' e).toEquiv

/-- `modularTriple Γ' e` is regular if and only if `Γ'` is normal in `PSL(2, ℤ)`. -/
@[simp] theorem isRegular_modularTriple_iff (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).IsRegular ↔ Γ'.Normal := by
  rw [modularTriple_eq_cosetTriple, TriangleGroup.isRegular_cosetTriple_iff]
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  have hmap : (Γ'.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ))).map
      (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) = Γ' :=
    Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ'
  rw [← hmap]
  exact Subgroup.Normal.map h (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ))
    modularEquiv.surjective

/-- `Γ'` is normal in `PSL(2, ℤ)` if and only if the monodromy group of `modularTriple Γ' e` has
order `n`. -/
theorem normal_iff_card_monodromyGroup_modularTriple (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Γ'.Normal ↔ Nat.card (modularTriple Γ' e).monodromyGroup = n := by
  rw [← isRegular_modularTriple_iff Γ' e, isRegular_iff_card_monodromyGroup,
    and_iff_right (isConnected_modularTriple Γ' e)]

/-! ### Opposite (right-coset / LMFDB) convention and mirror subgroup -/

section OppositeAndMirror

/-- Build the permutation triple `(σS * σT, σS, σT⁻¹)` from right-coset permutations `σS, σT` of an
involution `S` and translation `T`. -/
def ofRightCosetPerms (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) : PermutationTriple n where
  σ0 := σS * σT
  σ1 := σS
  σinf := σT⁻¹
  product_eq_one := by
    have hS' : σS * σS = 1 := by rwa [← sq]
    calc σT⁻¹ * σS * (σS * σT)
        = σT⁻¹ * (σS * σS) * σT := by group
      _ = 1 := by rw [hS', mul_one, inv_mul_cancel]

/-- The `0`-component of `ofRightCosetPerms σS σT hS` is `σS * σT`. -/
@[simp] theorem ofRightCosetPerms_σ0 (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) :
    (ofRightCosetPerms σS σT hS).σ0 = σS * σT := (rfl)

/-- The `1`-component of `ofRightCosetPerms σS σT hS` is `σS`. -/
@[simp] theorem ofRightCosetPerms_σ1 (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) :
    (ofRightCosetPerms σS σT hS).σ1 = σS := (rfl)

/-- The `∞`-component of `ofRightCosetPerms σS σT hS` is `σT⁻¹`. -/
@[simp] theorem ofRightCosetPerms_σinf (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) :
    (ofRightCosetPerms σS σT hS).σinf = σT⁻¹ := (rfl)

/-- Under the left-coset numbering `(quotientRightRelEquivQuotientLeftRel Γ').symm.trans r`
induced from a right-coset numbering `r` by `g Γ' ↦ Γ' g⁻¹`, passing to
`PermutationTriple.equivOppositeConvention` recovers the right-multiplication permutations of
`U`, `S`, and `T` on right cosets. -/
theorem equivOppositeConvention_modularTriple_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    (equivOppositeConvention n
      (modularTriple Γ'
        ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r))).val =
      (r.permCongr (Γ'.rightCosetPerm (U : PSL(2, ℤ))),
        r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))),
        r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))) := by
  simp [Equiv.permCongr_rightCosetPerm]

/-- **LMFDB row translation.** In terms of the right-coset permutations
`sRow := r.permCongr (Γ'.rightCosetPerm S)` and `tRow := r.permCongr (Γ'.rightCosetPerm T)`,
the right-coset permutation of `R = S T` is `tRow * sRow`, the modular triple under the induced
left-coset numbering is `(sRow * tRow, sRow, tRow⁻¹)`, and `permR` is the inverse of the
right-coset permutation of `R`. -/
theorem modularTriple_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    let e := (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r
    let sRow := r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ)))
    let tRow := r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))
    r.permCongr (Γ'.rightCosetPerm (R : PSL(2, ℤ))) = tRow * sRow ∧
      (modularTriple Γ' e).σ0 = sRow * tRow ∧
      (modularTriple Γ' e).σ1 = sRow ∧
      (modularTriple Γ' e).σinf = tRow⁻¹ ∧
      permR Γ' e = (r.permCongr (Γ'.rightCosetPerm (R : PSL(2, ℤ))))⁻¹ := by
  intro e sRow tRow
  have hS : sRow = e.permutationRepresentation (S : PSL(2, ℤ)) := by
    dsimp only [sRow, e]
    rw [Equiv.permCongr_rightCosetPerm, ← map_inv, coe_S_inv]
  refine ⟨?_, ?_, hS.symm, ?_, ?_⟩
  · dsimp only [sRow, tRow]
    rw [R_def, QuotientGroup.mk_mul, Γ'.rightCosetPerm_mul, r.permCongr_mul]
  · rw [modularTriple_σ0, U_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hS]
    dsimp only [tRow, e]
    rw [Equiv.permCongr_rightCosetPerm]
  · dsimp only [tRow, e]
    rw [modularTriple_σinf, Equiv.permCongr_rightCosetPerm, inv_inv]
  · dsimp only [e]
    rw [permR, Equiv.permCongr_rightCosetPerm, inv_inv]

/-- Bundled form of `modularTriple_quotientRightRel` in terms of `ofRightCosetPerms`. -/
theorem modularTriple_quotientRightRel_eq_ofRightCosetPerms (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    modularTriple Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      ofRightCosetPerms
        (r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))))
        (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ))))
        (by
          rw [sq, ← r.permCongr_mul, ← Γ'.rightCosetPerm_mul, ← sq, coe_S_sq,
            Γ'.rightCosetPerm_one]
          exact Equiv.ext fun _ ↦ by simp) := by
  obtain ⟨-, h0, h1, _⟩ := modularTriple_quotientRightRel Γ' r
  exact ext_of_two h0 h1

/-- For a numbering `eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n` of the right cosets `Γ' g`, the
right-action permutations satisfy `ρR (op R) = ρR (op T) * ρR (op S)`. -/
theorem rightCoset_permR_eq (Γ' : Subgroup PSL(2, ℤ)) (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    eR.permutationRepresentation (MulOpposite.op (R : PSL(2, ℤ))) =
      eR.permutationRepresentation (MulOpposite.op (T : PSL(2, ℤ))) *
        eR.permutationRepresentation (MulOpposite.op (S : PSL(2, ℤ))) := by
  rw [← map_mul, ← MulOpposite.op_mul, ← QuotientGroup.mk_mul, R_def]

/-- Under `Γ'.quotientEquivOp : PSL(2, ℤ) ⧸ Γ' ≃ PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op` (`g Γ' ↦ Γ' g⁻¹`),
`equivOppositeConvention` sends `modularTriple` to the right-action permutations of `U, S, T`. -/
theorem equivOppositeConvention_modularTriple_quotientEquivOp (Γ' : Subgroup PSL(2, ℤ))
    (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    (equivOppositeConvention n (modularTriple Γ' (Γ'.quotientEquivOp.trans eR))).val =
      (eR.permutationRepresentation (MulOpposite.op (U : PSL(2, ℤ))),
        eR.permutationRepresentation (MulOpposite.op (S : PSL(2, ℤ))),
        eR.permutationRepresentation (MulOpposite.op (T : PSL(2, ℤ)))) := by
  simp [equivOppositeConvention_apply_coe]

/-- Transporting a right-coset numbering `eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n` along
`Γ'.quotientEquivOp` yields `ofRightCosetPerms` for `op S` and `op T`. -/
theorem modularTriple_quotientEquivOp_eq_ofRightCosetPerms (Γ' : Subgroup PSL(2, ℤ))
    (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    modularTriple Γ' (Γ'.quotientEquivOp.trans eR) =
      ofRightCosetPerms
        (eR.permutationRepresentation (MulOpposite.op (S : PSL(2, ℤ))))
        (eR.permutationRepresentation (MulOpposite.op (T : PSL(2, ℤ))))
        (by rw [← map_pow, ← MulOpposite.op_pow, coe_S_sq, MulOpposite.op_one, map_one]) := by
  have hUinv : (U : PSL(2, ℤ))⁻¹ = (T : PSL(2, ℤ)) * S := by
    rw [U_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, _root_.mul_inv_rev, inv_inv, coe_S_inv]
  refine ext_of_two ?_ ?_
  · rw [modularTriple_σ0, Equiv.permutationRepresentation_quotientEquivOp_trans_apply,
      ← map_inv, ← MulOpposite.op_inv, hUinv, MulOpposite.op_mul, map_mul, ofRightCosetPerms_σ0]
  · rw [modularTriple_σ1, Equiv.permutationRepresentation_quotientEquivOp_trans_apply,
      ← map_inv, ← MulOpposite.op_inv, coe_S_inv, ofRightCosetPerms_σ1]

/-- Under `Γ'.quotientEquivOp.trans eR`, `permR` is the inverse of the right-action permutation of
`op R`. -/
@[simp] theorem permR_quotientEquivOp_trans (Γ' : Subgroup PSL(2, ℤ))
    (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    permR Γ' (Γ'.quotientEquivOp.trans eR) =
      (eR.permutationRepresentation (MulOpposite.op (R : PSL(2, ℤ))))⁻¹ :=
  Equiv.permutationRepresentation_quotientEquivOp_trans_apply Γ' eR (R : PSL(2, ℤ))

/-- Coordinate reflection by `diag(-1, 1)` inverts `T` in `SL(2, ℤ)`. -/
@[simp] theorem conjJ_T : SpecialLinearGroup.conjJ T = T⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_T]

/-- Coordinate reflection by `diag(-1, 1)` sends `U = S T⁻¹` to `-R` in `SL(2, ℤ)`. -/
@[simp] theorem conjJ_U : SpecialLinearGroup.conjJ U = -R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_U, coe_R]

/-- The involutive automorphism of `PSL(2, ℤ)` induced by conjugation by `diag(-1, 1)` on
`SL(2, ℤ)`. -/
def conjJAut : MulAut PSL(2, ℤ) :=
  MulAut.mapQuotient (Subgroup.center SL(2, ℤ)) SpecialLinearGroup.conjJMulAut

/-- `conjJAut` acts on the projective class of `γ : SL(2, ℤ)` via `SpecialLinearGroup.conjJ`. -/
theorem conjJAut_mk (γ : SL(2, ℤ)) :
    conjJAut (γ : PSL(2, ℤ)) = (SpecialLinearGroup.conjJ γ : PSL(2, ℤ)) :=
  (MulAut.mapQuotient_mk (Subgroup.center SL(2, ℤ)) SpecialLinearGroup.conjJMulAut γ).trans
    (congrArg _ (SpecialLinearGroup.conjJMulAut_apply γ))

/-- `conjJAut` is an involution of `PSL(2, ℤ)`. -/
@[simp] theorem conjJAut_conjJAut (g : PSL(2, ℤ)) : conjJAut (conjJAut g) = g :=
  QuotientGroup.induction_on g fun γ ↦ by
    rw [conjJAut_mk, conjJAut_mk, SpecialLinearGroup.conjJ_conjJ]

/-- Being an involution, `conjJAut` equals its own inverse. -/
@[simp] theorem conjJAut_symm : conjJAut.symm = conjJAut :=
  MulEquiv.ext fun g ↦ conjJAut.symm_apply_eq.mpr (conjJAut_conjJAut g).symm

/-- `conjJAut` fixes `S` in `PSL(2, ℤ)`. -/
@[simp] theorem conjJAut_S : conjJAut (S : PSL(2, ℤ)) = S := by
  rw [conjJAut_mk, SpecialLinearGroup.conjJ_S, QuotientGroup.eq,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  simp

/-- `conjJAut` inverts `T` in `PSL(2, ℤ)`. -/
@[simp] theorem conjJAut_T : conjJAut (T : PSL(2, ℤ)) = (T : PSL(2, ℤ))⁻¹ := by
  rw [conjJAut_mk, conjJ_T, QuotientGroup.mk_inv]

/-- `conjJAut` sends `U = S T⁻¹` to `R = S T`. -/
@[simp] theorem conjJAut_U : conjJAut (U : PSL(2, ℤ)) = R := by
  rw [U_def, R_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, conjJAut_S,
    conjJAut_T, inv_inv, QuotientGroup.mk_mul]

/-- `conjJAut` sends `R = S T` to `U = S T⁻¹`. -/
@[simp] theorem conjJAut_R : conjJAut (R : PSL(2, ℤ)) = U := by
  rw [← conjJAut_U, conjJAut_conjJAut]

/-- Under `modularEquiv`, `conjJAut` corresponds to `TriangleGroup.mirror`. -/
theorem conjJAut_modularEquiv (x : TriangleGroup 3 2 0) :
    conjJAut (modularEquiv x) = modularEquiv (TriangleGroup.mirror x) := by
  have h : conjJAut.toMonoidHom.comp (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) =
      (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)).comp
        (TriangleGroup.mirror (a := 3) (b := 2) (c := 0)).toMonoidHom := by
    apply TriangleGroup.hom_ext
    · simp [coe_S_mul_coe_U_inv_mul_coe_S]
    · simp
  exact DFunLike.congr_fun h x

/-- Transporting a coset numbering along `conjJAut` mirrors the modular triple. -/
theorem modularTriple_congrOfMapEq_conjJAut {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    (h : Γ₁.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) = Γ₂) (e : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n) :
    modularTriple Γ₁ ((TauCeti.QuotientGroup.congrOfMapEq conjJAut h).trans e) =
      (modularTriple Γ₂ e).mirror := by
  ext1
  · simp only [modularTriple_σ0, mirror_σ0, modularTriple_σ1,
      Equiv.permutationRepresentation_congrOfMapEq, MonoidHom.comp_apply]
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (by simpa [coe_S_inv] using coe_S_mul_coe_U_inv_mul_coe_S.symm)
  · simp [Equiv.permutationRepresentation_congrOfMapEq, ← map_inv]

/-- For any coset numberings, the modular triple of the mirror subgroup `Γ'.map conjJAut` is
isomorphic to the mirror of `modularTriple Γ' e`. -/
theorem equivalent_mirror_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    (modularTriple (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e').Equivalent
      (modularTriple Γ' e).mirror := by
  have hmap : (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))).map
      (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) = Γ' := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id Γ'
    exact MonoidHom.ext conjJAut_conjJAut
  rw [← IsoClass.mk_eq_mk_iff,
    IsoClass.mk_eq_mk_iff.mpr
      (equivalent_modularTriple _ e' ((TauCeti.QuotientGroup.congrOfMapEq conjJAut hmap).trans e)),
    modularTriple_congrOfMapEq_conjJAut hmap e]

end OppositeAndMirror

/-! ### Millington's theorem and pointed Millington for `PSL(2, ℤ)` -/

/-- **Millington's theorem.** Two modular coset triples of degree `n` are isomorphic if and only
if the subgroups are conjugate in `PSL(2, ℤ)`. -/
theorem millington {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n) (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n) :
    (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂) ↔
      ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂ := by
  rw [modularTriple_eq_cosetTriple Γ₁ e₁, modularTriple_eq_cosetTriple Γ₂ e₂,
    TriangleGroup.cosetTriple_equivalent_cosetTriple_iff]
  simp_rw [← MulAction.mem_orbit_iff, TauCeti.mem_orbit_conjAct_iff]
  exact Subgroup.exists_map_conj_comap_eq_iff modularEquiv Γ₁ Γ₂

/-- **Pointed Millington criterion for `PSL(2, ℤ)`.** Two modular triples marked at their base
cosets `e₁ 1` and `e₂ 1` define the same marked isomorphism class if and only if `Γ₁ = Γ₂`. -/
theorem markedIsoClass_modularTriple_eq_iff {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n) (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n) :
    MarkedIsoClass.mk ⟨modularTriple Γ₁ e₁, isConnected_modularTriple Γ₁ e₁⟩
        (e₁ ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₁)) =
      MarkedIsoClass.mk ⟨modularTriple Γ₂ e₂, isConnected_modularTriple Γ₂ e₂⟩
        (e₂ ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₂)) ↔
      Γ₁ = Γ₂ := by
  let f₁ := (TauCeti.QuotientGroup.congrOfMapEq modularEquiv
    (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ₁)).trans e₁
  let f₂ := (TauCeti.QuotientGroup.congrOfMapEq modularEquiv
    (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ₂)).trans e₂
  have hf₁ : e₁ ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₁) =
      f₁ ((1 : TriangleGroup 3 2 0) : TriangleGroup 3 2 0 ⧸ _) := by simp [f₁]
  have hf₂ : e₂ ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₂) =
      f₂ ((1 : TriangleGroup 3 2 0) : TriangleGroup 3 2 0 ⧸ _) := by simp [f₂]
  have hc₁ : (⟨modularTriple Γ₁ e₁, isConnected_modularTriple Γ₁ e₁⟩ : ConnectedTriple n) =
      ⟨TriangleGroup.cosetTriple _ f₁, TriangleGroup.isConnected_cosetTriple _ f₁⟩ :=
    Subtype.ext (modularTriple_eq_cosetTriple Γ₁ e₁)
  have hc₂ : (⟨modularTriple Γ₂ e₂, isConnected_modularTriple Γ₂ e₂⟩ : ConnectedTriple n) =
      ⟨TriangleGroup.cosetTriple _ f₂, TriangleGroup.isConnected_cosetTriple _ f₂⟩ :=
    Subtype.ext (modularTriple_eq_cosetTriple Γ₂ e₂)
  rw [hc₁, hc₂, hf₁, hf₂, TriangleGroup.markedIsoClass_cosetTriple_eq_iff,
    (Subgroup.comap_injective modularEquiv.surjective).eq_iff]

/-- **Pointed surjectivity of `modularTriple`.** Every connected permutation triple `t` of degree
`n` with `σ0 ^ 3 = 1` and `σ1 ^ 2 = 1` and chosen sheet `i : Fin n` is literally equal to
`modularTriple Γ' e` for a finite-index subgroup `Γ'` of `PSL(2, ℤ)` of index `n` and a coset
numbering `e` sending `1` to `i`. -/
theorem exists_modularTriple_eq {t : PermutationTriple n} (ht : t.IsConnected)
    (h0 : t.σ0 ^ 3 = 1) (h1 : t.σ1 ^ 2 = 1) (i : Fin n) :
    ∃ (Γ' : Subgroup PSL(2, ℤ)) (_ : Γ'.FiniteIndex) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n),
      Γ'.index = n ∧ e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') = i ∧ modularTriple Γ' e = t := by
  obtain ⟨H, _, eH, -, heH1, rfl⟩ :=
    TriangleGroup.exists_cosetTriple_eq ht ((hasDividingOrders_iff t).mpr ⟨h0, h1, pow_zero _⟩) i
  let Γ' : Subgroup PSL(2, ℤ) := H.map (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ))
  let cv := TauCeti.QuotientGroup.congrOfMapEq modularEquiv (rfl : H.map _ = Γ')
  let e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n := cv.symm.trans eH
  refine ⟨Γ', Γ'.finiteIndex_of_equiv e, e, Γ'.index_eq_of_equiv e, ?_, ?_⟩
  · have hsymm : cv.symm ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') =
        ((1 : TriangleGroup 3 2 0) : TriangleGroup 3 2 0 ⧸ H) := by
      rw [Equiv.symm_apply_eq, TauCeti.QuotientGroup.congrOfMapEq_mk, map_one]
    exact (congrArg eH hsymm).trans heH1
  · have hcv : cv.trans e = eH := Equiv.ext fun _ ↦ by simp [e]
    ext1 <;> simp [← hcv, cv]

/-- **Surjectivity of Millington's dictionary.** Every connected permutation triple of degree `n`
with `σ0 ^ 3 = 1` and `σ1 ^ 2 = 1` is isomorphic to the modular triple of a finite-index subgroup
of `PSL(2, ℤ)` of index `n`. -/
theorem exists_modularTriple_equivalent {t : PermutationTriple n} (ht : t.IsConnected)
    (h0 : t.σ0 ^ 3 = 1) (h1 : t.σ1 ^ 2 = 1) :
    ∃ (Γ' : Subgroup PSL(2, ℤ)) (_ : Γ'.FiniteIndex) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n),
      Γ'.index = n ∧ (modularTriple Γ' e).Equivalent t := by
  obtain ⟨Γ', hfin, e, hΓ, -, rfl⟩ :=
    exists_modularTriple_eq ht h0 h1 ⟨0, Nat.pos_of_ne_zero ht.ne_zero⟩
  exact ⟨Γ', hfin, e, hΓ, IsoClass.mk_eq_mk_iff.mp rfl⟩

/-- The isomorphism classes of connected permutation triples of degree `n` with `σ0 ^ 3 = 1` and
`σ1 ^ 2 = 1`. -/
def modularIsoClasses (n : ℕ) : Set (IsoClass n) :=
  IsoClass.mk '' {t | t.IsConnected ∧ t.σ0 ^ 3 = 1 ∧ t.σ1 ^ 2 = 1}

/-- The isomorphism class of `t` lies in `modularIsoClasses n` if and only if `t` is connected with
`t.σ0 ^ 3 = 1` and `t.σ1 ^ 2 = 1`. -/
@[simp] theorem mk_mem_modularIsoClasses_iff {t : PermutationTriple n} :
    IsoClass.mk t ∈ modularIsoClasses n ↔ t.IsConnected ∧ t.σ0 ^ 3 = 1 ∧ t.σ1 ^ 2 = 1 := by
  refine ⟨?_, fun h ↦ ⟨t, h, rfl⟩⟩
  rintro ⟨t', ⟨hc, h0, h1⟩, h⟩
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp (IsoClass.mk_eq_mk_iff.mp h)
  exact ⟨(isConnected_smul_iff τ t').mpr hc, by simp [h0], by simp [h1]⟩

/-- `modularIsoClasses n` agrees with `TriangleGroup.connectedIsoClasses 3 2 0 n`. -/
theorem modularIsoClasses_eq_connectedIsoClasses (n : ℕ) :
    modularIsoClasses n = TriangleGroup.connectedIsoClasses 3 2 0 n := by
  ext c
  obtain ⟨t, rfl⟩ := IsoClass.mk_surjective c
  simp [hasDividingOrders_iff]

/-- **Millington's theorem (bundled bijection).** For `n ≠ 0`, conjugacy classes of subgroups of
`PSL(2, ℤ)` of index `n` are in bijection with `modularIsoClasses n`. -/
noncomputable def modularIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n) ≃
      modularIsoClasses n :=
  (modularEquiv.symm.orbitRelQuotientOfIndexEquiv n).trans <|
    TriangleGroup.cosetIsoClassEquiv.trans <|
      Set.equivOfEq (modularIsoClasses_eq_connectedIsoClasses n).symm

/-- `modularIsoClassEquiv` sends the conjugacy class of `Γ'` to `IsoClass.mk (modularTriple Γ' e)`
for any numbering `e` of the cosets of `Γ'`. -/
theorem coe_modularIsoClassEquiv_mk [NeZero n] (Γ' : Subgroup.ofIndex PSL(2, ℤ) n)
    (e : PSL(2, ℤ) ⧸ Γ'.val ≃ Fin n) :
    (modularIsoClassEquiv (Quotient.mk'' Γ') : IsoClass n) =
      IsoClass.mk (modularTriple Γ'.val e) := by
  have hcomap : (modularEquiv.symm.ofIndexEquiv n Γ' : Subgroup (TriangleGroup 3 2 0)) =
      Γ'.val.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) :=
    (modularEquiv.symm.coe_ofIndexEquiv_apply n Γ').trans
      (Subgroup.comap_equiv_eq_map_symm modularEquiv Γ'.val).symm
  rw [modularIsoClassEquiv, Equiv.trans_apply, Equiv.trans_apply,
    MulEquiv.orbitRelQuotientOfIndexEquiv_mk, Set.equivOfEq_apply]
  have heq := TriangleGroup.coe_cosetIsoClassEquiv_mk (modularEquiv.symm.ofIndexEquiv n Γ')
    ((Subgroup.quotientEquivOfEq hcomap).trans
      ((TauCeti.QuotientGroup.congrOfMapEq modularEquiv
        (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ'.val)).trans e))
  rw [heq, modularTriple_eq_cosetTriple Γ'.val e, IsoClass.mk_eq_mk_iff,
    TriangleGroup.cosetTriple_equivalent_cosetTriple_iff]
  exact ⟨1, by rw [one_smul, hcomap]⟩

/-- **Millington's theorem on `ConnectedIsoClass`.** For `n ≠ 0`, conjugacy classes of index-`n`
subgroups of `PSL(2, ℤ)` biject with `{C : ConnectedIsoClass n // C.HasDividingOrders 3 2 0}`. -/
noncomputable def modularConnectedIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n) ≃
      {C : ConnectedIsoClass n // C.HasDividingOrders 3 2 0} :=
  (modularEquiv.symm.orbitRelQuotientOfIndexEquiv n).trans TriangleGroup.cosetConnectedIsoClassEquiv

/-- `modularConnectedIsoClassEquiv` sends the conjugacy class of `Γ'` to
`ConnectedIsoClass.mk (modularConnectedTriple Γ'.1 e)`, for any coset numbering `e`. -/
theorem coe_modularConnectedIsoClassEquiv_mk [NeZero n] (Γ' : Subgroup.ofIndex PSL(2, ℤ) n)
    (e : PSL(2, ℤ) ⧸ Γ'.val ≃ Fin n) :
    (modularConnectedIsoClassEquiv (Quotient.mk'' Γ') : ConnectedIsoClass n) =
      ConnectedIsoClass.mk (modularConnectedTriple Γ'.val e) := by
  have hcomap : (modularEquiv.symm.ofIndexEquiv n Γ' : Subgroup (TriangleGroup 3 2 0)) =
      Γ'.val.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) :=
    (modularEquiv.symm.coe_ofIndexEquiv_apply n Γ').trans
      (Subgroup.comap_equiv_eq_map_symm modularEquiv Γ'.val).symm
  rw [modularConnectedIsoClassEquiv, Equiv.trans_apply, MulEquiv.orbitRelQuotientOfIndexEquiv_mk,
    TriangleGroup.coe_cosetConnectedIsoClassEquiv_mk _
      ((Subgroup.quotientEquivOfEq hcomap).trans
        ((TauCeti.QuotientGroup.congrOfMapEq modularEquiv
          (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ'.val)).trans e)),
    ConnectedIsoClass.mk_eq_mk_iff_equivalent, TriangleGroup.coe_cosetConnectedTriple,
    coe_modularConnectedTriple, modularTriple_eq_cosetTriple Γ'.val e,
    TriangleGroup.cosetTriple_equivalent_cosetTriple_iff]
  exact ⟨1, by rw [one_smul, hcomap]⟩

/-- The marked isomorphism classes of connected permutation triples of degree `n` with
`σ0 ^ 3 = 1` and `σ1 ^ 2 = 1`. -/
def modularMarkedIsoClasses (n : ℕ) : Set (MarkedIsoClass n) :=
  {m | ∃ (t : ConnectedTriple n) (i : Fin n),
    t.val.σ0 ^ 3 = 1 ∧ t.val.σ1 ^ 2 = 1 ∧ MarkedIsoClass.mk t i = m}

/-- The marked class of `(t, i)` lies in `modularMarkedIsoClasses n` if and only if
`t.1.σ0 ^ 3 = 1` and `t.1.σ1 ^ 2 = 1`. -/
@[simp] theorem mk_mem_modularMarkedIsoClasses_iff {t : ConnectedTriple n} {i : Fin n} :
    MarkedIsoClass.mk t i ∈ modularMarkedIsoClasses n ↔ t.val.σ0 ^ 3 = 1 ∧ t.val.σ1 ^ 2 = 1 := by
  refine ⟨?_, fun ⟨h0, h1⟩ ↦ ⟨t, i, h0, h1, rfl⟩⟩
  rintro ⟨t', i', h0, h1, h⟩
  obtain ⟨τ, hτ, -⟩ := MarkedIsoClass.mk_eq_mk_iff_exists_smul.mp h.symm
  have hval : (t : PermutationTriple n) = τ • t'.val := by rw [← hτ, ConnectedTriple.coe_smul]
  rw [hval]
  exact ⟨by simp [h0], by simp [h1]⟩

/-- `modularMarkedIsoClasses n` agrees with `TriangleGroup.markedIsoClasses 3 2 0 n`. -/
theorem modularMarkedIsoClasses_eq_markedIsoClasses (n : ℕ) :
    modularMarkedIsoClasses n = TriangleGroup.markedIsoClasses 3 2 0 n := by
  ext m
  obtain ⟨t, i, rfl⟩ := MarkedIsoClass.mk_surjective m
  simp [hasDividingOrders_iff]

/-- **Pointed Millington bijection for `PSL(2, ℤ)`.** For `n ≠ 0`, subgroups of `PSL(2, ℤ)` of
index `n` are in bijection with `modularMarkedIsoClasses n`. -/
noncomputable def modularMarkedIsoClassEquiv [NeZero n] :
    Subgroup.ofIndex PSL(2, ℤ) n ≃ modularMarkedIsoClasses n :=
  (modularEquiv.symm.ofIndexEquiv n).trans <|
    TriangleGroup.cosetMarkedIsoClassEquiv.trans <|
      Set.equivOfEq (modularMarkedIsoClasses_eq_markedIsoClasses n).symm

/-- `modularMarkedIsoClassEquiv` sends `Γ'` to the class of `modularTriple Γ' e` marked at the base
coset `e 1`, independently of `e`. -/
theorem coe_modularMarkedIsoClassEquiv_apply [NeZero n] (Γ' : Subgroup.ofIndex PSL(2, ℤ) n)
    (e : PSL(2, ℤ) ⧸ Γ'.val ≃ Fin n) :
    (modularMarkedIsoClassEquiv Γ' : MarkedIsoClass n) =
      MarkedIsoClass.mk ⟨modularTriple Γ'.val e, isConnected_modularTriple Γ'.val e⟩
        (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'.val)) := by
  have hcomap : (modularEquiv.symm.ofIndexEquiv n Γ' : Subgroup (TriangleGroup 3 2 0)) =
      Γ'.val.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) :=
    (modularEquiv.symm.coe_ofIndexEquiv_apply n Γ').trans
      (Subgroup.comap_equiv_eq_map_symm modularEquiv Γ'.val).symm
  let f := (TauCeti.QuotientGroup.congrOfMapEq modularEquiv
    (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ'.val)).trans e
  rw [modularMarkedIsoClassEquiv, Equiv.trans_apply, Equiv.trans_apply, Set.equivOfEq_apply,
    TriangleGroup.coe_cosetMarkedIsoClassEquiv_apply _
      ((Subgroup.quotientEquivOfEq hcomap).trans f)]
  have hf : e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'.val) =
      f ((1 : TriangleGroup 3 2 0) : TriangleGroup 3 2 0 ⧸ _) := by simp [f]
  have hc : (⟨modularTriple Γ'.val e, isConnected_modularTriple Γ'.val e⟩ : ConnectedTriple n) =
      ⟨TriangleGroup.cosetTriple _ f, TriangleGroup.isConnected_cosetTriple _ f⟩ :=
    Subtype.ext (modularTriple_eq_cosetTriple Γ'.val e)
  rw [hc, hf, TriangleGroup.markedIsoClass_cosetTriple_eq_iff]
  exact hcomap

/-! ### Automorphism group, class-count formula, and finiteness at fixed index -/

/-- The automorphism group of `modularTriple Γ' e` is canonically isomorphic to
`(Γ'.normalizerQuotient)ᵐᵒᵖ`. -/
noncomputable def automorphismGroupModularTripleMulEquiv (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).automorphismGroup ≃* (Γ'.normalizerQuotient)ᵐᵒᵖ :=
  (MulEquiv.subgroupCongr <| by
    rw [automorphismGroup_eq_centralizer_monodromyGroup, monodromyGroup_modularTriple,
      MonoidHom.coe_range]).trans
    e.centralizerPermutationRepresentationQuotientMulEquiv

/-- The order of the automorphism group of `modularTriple Γ' e` equals `[N_{PSL(2,ℤ)}(Γ') : Γ']`. -/
theorem natCard_automorphismGroup_modularTriple (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Nat.card (modularTriple Γ' e).automorphismGroup =
      Γ'.relIndex (Subgroup.normalizer (Γ' : Set PSL(2, ℤ))) := by
  rw [Nat.card_congr (automorphismGroupModularTripleMulEquiv Γ' e).toEquiv,
    ← e.natCard_centralizer_permutationRepresentation_quotient,
    Nat.card_congr e.centralizerPermutationRepresentationQuotientMulEquiv.toEquiv]

/-- The subgroups `Γ'' ≤ PSL(2, ℤ)` realizing the isomorphism class of `modularTriple Γ' e` are
precisely the conjugates of `Γ'` in `PSL(2, ℤ)`. -/
theorem setOf_exists_modularTriple_equivalent_eq_orbit (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    {Γ'' : Subgroup PSL(2, ℤ) | ∃ e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin n,
      (modularTriple Γ'' e'').Equivalent (modularTriple Γ' e)} =
      MulAction.orbit (ConjAct PSL(2, ℤ)) Γ' := by
  ext Γ''
  rw [Set.mem_ofPred, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨e'', heq⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · obtain ⟨g, hg⟩ := (millington e'' e).mp heq
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  · obtain ⟨c, rfl⟩ := ConjAct.toConjAct.surjective g
    exact ⟨(Subgroup.quotientEquivOfConjAct hg).symm.trans e,
      (millington _ e).mpr ⟨(ConjAct.toConjAct c)⁻¹, by rw [← hg, inv_smul_smul]⟩⟩

/-- **Number of subgroups in a modular triple class.** The number of subgroups of `PSL(2, ℤ)`
realizing the isomorphism class of `modularTriple Γ' e` times `#Aut(modularTriple Γ' e)` equals `n`.
-/
theorem card_subgroups_of_class (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Nat.card {Γ'' : Subgroup PSL(2, ℤ) // ∃ e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin n,
        (modularTriple Γ'' e'').Equivalent (modularTriple Γ' e)} *
      Nat.card (modularTriple Γ' e).automorphismGroup = n := by
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, setOf_exists_modularTriple_equivalent_eq_orbit Γ' e,
    natCard_automorphismGroup_modularTriple Γ' e, Γ'.ncard_orbit_mul_relIndex_normalizer,
    Γ'.index_eq_of_equiv e]

/-- The number of conjugates of `Γ'` in `PSL(2, ℤ)` equals `n` divided by the order of
`(modularTriple Γ' e).automorphismGroup`. -/
theorem natCard_orbit_conjAct_eq_div_automorphismGroup (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Nat.card (MulAction.orbit (ConjAct PSL(2, ℤ)) Γ') =
      n / Nat.card (modularTriple Γ' e).automorphismGroup := by
  rw [(modularTriple Γ' e).automorphismGroup_eq_centralizer_monodromyGroup,
    monodromyGroup_modularTriple, MonoidHom.coe_range,
    e.natCard_orbit_conjAct_eq_index_div_natCard_centralizer, Γ'.index_eq_of_equiv e]

/-- The number of subgroups in an index-`n` conjugacy class `ω` of `PSL(2, ℤ)` equals `n` divided
by the automorphism order of its modular triple class. -/
theorem natCard_orbit_ofIndex_eq_div_automorphismOrder [NeZero n]
    (ω : MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n)) :
    Nat.card (MulAction.orbitRel.Quotient.orbit ω) =
      n / (modularConnectedIsoClassEquiv ω).val.automorphismOrder :=
  Quotient.inductionOn' ω fun Γ' ↦ by
    let e := Γ'.val.quotientEquivFin (Subgroup.mem_ofIndex.mp Γ'.property)
    rw [MulAction.orbitRel.Quotient.orbit_mk, Nat.card_congr (Subgroup.orbitOfIndexEquiv Γ'),
      natCard_orbit_conjAct_eq_div_automorphismGroup Γ'.val e,
      coe_modularConnectedIsoClassEquiv_mk Γ' e, ConnectedIsoClass.automorphismOrder_mk,
      coe_modularConnectedTriple]

/-- **Finiteness at fixed index.** For every `n ≠ 0`, `PSL(2, ℤ)` has only finitely many subgroups
of index `n`. -/
instance finite_ofIndex (n : ℕ) [NeZero n] : Finite (Subgroup.ofIndex PSL(2, ℤ) n) :=
  Finite.of_equiv (Subgroup.ofIndex (TriangleGroup 3 2 0) n) (modularEquiv.ofIndexEquiv n)

/-- Unbundled form of `finite_ofIndex`: `{Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}` is finite for
`n ≠ 0`. -/
instance finite_subgroups_of_index (n : ℕ) [NeZero n] :
    Finite {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} :=
  Finite.of_equiv (Subgroup.ofIndex PSL(2, ℤ) n)
    (Equiv.subtypeEquivRight fun _ ↦ Subgroup.mem_ofIndex)

/-- For every `n ≠ 0`, `PSL(2, ℤ)` has only finitely many conjugacy classes of subgroups of
index `n`. -/
theorem finite_orbitRel_quotient_ofIndex (n : ℕ) [NeZero n] :
    Finite (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n)) :=
  Quotient.finite _

/-- At `n = 0` (infinite index), `PSL(2, ℤ)` has infinitely many conjugacy classes of subgroups,
witnessed by the parabolic subgroups `⟨T ^ (m + 1)⟩`. Thus `[NeZero n]` in `finite_ofIndex`,
`finite_subgroups_of_index`, and `finite_orbitRel_quotient_ofIndex` is sharp. -/
theorem infinite_orbitRel_quotient_ofIndex_zero :
    Infinite (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 0)) := by
  refine Infinite.of_injective
    (fun m : ℕ ↦ (Quotient.mk''
      ⟨Subgroup.zpowers ((T : PSL(2, ℤ)) ^ (m + 1)),
        Subgroup.mem_ofIndex.mpr <| by
          rw [← zpow_natCast]
          exact index_zpowers_coe_T_zpow (m + 1 : ℕ)⟩ :
      MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 0)))
    fun i j hij ↦ ?_
  obtain ⟨g, hg⟩ := Quotient.exact' hij
  have hg' : g • Subgroup.zpowers ((T : PSL(2, ℤ)) ^ ((j + 1 : ℕ) : ℤ)) =
      Subgroup.zpowers ((T : PSL(2, ℤ)) ^ ((i + 1 : ℕ) : ℤ)) := by
    rw [zpow_natCast, zpow_natCast]
    exact congrArg Subtype.val hg
  have hg'' : g⁻¹ • Subgroup.zpowers ((T : PSL(2, ℤ)) ^ ((i + 1 : ℕ) : ℤ)) =
      Subgroup.zpowers ((T : PSL(2, ℤ)) ^ ((j + 1 : ℕ) : ℤ)) := by
    rw [← hg', inv_smul_smul]
  exact Nat.succ_injective <| Nat.dvd_antisymm
    (Int.natCast_dvd_natCast.mp (dvd_of_conj_zpowers_coe_T_zpow_le hg'.le))
    (Int.natCast_dvd_natCast.mp (dvd_of_conj_zpowers_coe_T_zpow_le hg''.le))

/-- `PSL(2, ℤ)` has infinitely many infinite-index (`index = 0`) subgroups. -/
theorem infinite_ofIndex_zero : Infinite (Subgroup.ofIndex PSL(2, ℤ) 0) :=
  have := infinite_orbitRel_quotient_ofIndex_zero
  Infinite.of_surjective
    (Quotient.mk'' : Subgroup.ofIndex PSL(2, ℤ) 0 →
      MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 0))
    fun q ↦ Quotient.inductionOn' q fun H ↦ ⟨H, rfl⟩

/-! ### Computable conjugacy-class and subgroup counts -/

/-- For every `n : ℕ` (including `n = 0`), `Nat.card` of the conjugacy classes of index-`n`
subgroups of `PSL(2, ℤ)` equals `#(connectedIsoClassesWithDividingOrders n 3 2 0)`. -/
theorem natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders (n : ℕ) :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n)) =
      (connectedIsoClassesWithDividingOrders n 3 2 0).card := by
  rcases eq_or_ne n 0 with rfl | hn
  · have := infinite_orbitRel_quotient_ofIndex_zero
    rw [Nat.card_eq_zero_of_infinite, connectedIsoClassesWithDividingOrders_zero,
      Finset.card_empty]
  · have : NeZero n := ⟨hn⟩
    exact (Nat.card_congr (modularEquiv.symm.orbitRelQuotientOfIndexEquiv n)).trans
      (TriangleGroup.natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders
        3 2 0 n)

/-- **Index-`n` subgroup count for `PSL(2, ℤ)`.** For every `n : ℕ` (including `n = 0`, where both
sides equal `0`), `Nat.card` of the index-`n` subgroups of `PSL(2, ℤ)` is
`∑ C ∈ connectedIsoClassesWithDividingOrders n 3 2 0, n / C.automorphismOrder`. -/
theorem natCard_ofIndex_eq_sum_div_automorphismOrder (n : ℕ) :
    Nat.card (Subgroup.ofIndex PSL(2, ℤ) n) =
      ∑ C ∈ connectedIsoClassesWithDividingOrders n 3 2 0, n / C.automorphismOrder := by
  rcases eq_or_ne n 0 with rfl | hn
  · have := infinite_ofIndex_zero
    rw [Nat.card_eq_zero_of_infinite, connectedIsoClassesWithDividingOrders_zero, Finset.sum_empty]
  · have : NeZero n := ⟨hn⟩
    exact (Nat.card_congr (modularEquiv.symm.ofIndexEquiv n)).trans
      (TriangleGroup.natCard_ofIndex_eq_sum_div_automorphismOrder 3 2 0 n)

/-- Unbundled form of `natCard_ofIndex_eq_sum_div_automorphismOrder` on
`{Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}` for every `n : ℕ`. -/
theorem natCard_subgroups_of_index_eq_sum_div_automorphismOrder (n : ℕ) :
    Nat.card {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} =
      ∑ C ∈ connectedIsoClassesWithDividingOrders n 3 2 0, n / C.automorphismOrder :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Subgroup.mem_ofIndex.symm)).trans
    (natCard_ofIndex_eq_sum_div_automorphismOrder n)

/-- The two connected modular triple classes in degree `3` are the regular cyclic class
`PermutationTriple.cyclicTriple 3` (the unique normal index-`3` subgroup, of monodromy order `3`)
and `PermutationTriple.s3Triple` (the three conjugate subgroups in the `Γ₀(2)` class, of monodromy
order `6`). -/
theorem connectedIsoClassesWithDividingOrders_three :
    connectedIsoClassesWithDividingOrders 3 3 2 0 =
      {ConnectedIsoClass.mk ⟨cyclicTriple 3, isConnected_cyclicTriple_iff.mpr (by decide)⟩,
        ConnectedIsoClass.mk ⟨s3Triple, isConnected_s3Triple⟩} := by
  decide +kernel

/-- `PSL(2, ℤ)` has `1` conjugacy class of subgroups of index `1`. -/
theorem natCard_conjClasses_index_one :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 1)) =
      1 := by
  rw [natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders 1]
  decide

/-- `PSL(2, ℤ)` has `1` conjugacy class of subgroups of index `2`. -/
theorem natCard_conjClasses_index_two :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 2)) =
      1 := by
  rw [natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders 2]
  decide

/-- `PSL(2, ℤ)` has `2` conjugacy classes of subgroups of index `3`. -/
theorem natCard_conjClasses_index_three :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 3)) =
      2 := by
  rw [natCard_orbitRel_quotient_ofIndex_eq_card_connectedIsoClassesWithDividingOrders 3,
    connectedIsoClassesWithDividingOrders_three]
  decide

/-- `PSL(2, ℤ)` has `1` subgroup of index `1`. -/
theorem natCard_subgroups_index_one : Nat.card (Subgroup.ofIndex PSL(2, ℤ) 1) = 1 := by
  rw [natCard_ofIndex_eq_sum_div_automorphismOrder 1]
  simp only [← ConnectedIsoClass.computedAutomorphismOrder_eq]
  decide

/-- `PSL(2, ℤ)` has `1` subgroup of index `2` (the unique index-`2` subgroup is normal). -/
theorem natCard_subgroups_index_two : Nat.card (Subgroup.ofIndex PSL(2, ℤ) 2) = 1 := by
  rw [natCard_ofIndex_eq_sum_div_automorphismOrder 2]
  simp only [← ConnectedIsoClass.computedAutomorphismOrder_eq]
  decide

/-- `PSL(2, ℤ)` has `4` subgroups of index `3`: one normal subgroup of automorphism order `3` and
three conjugate subgroups of automorphism order `1`. -/
theorem natCard_subgroups_index_three : Nat.card (Subgroup.ofIndex PSL(2, ℤ) 3) = 4 := by
  rw [natCard_ofIndex_eq_sum_div_automorphismOrder 3]
  simp only [← ConnectedIsoClass.computedAutomorphismOrder_eq]
  decide +kernel

end TauCeti.ModularGroup
