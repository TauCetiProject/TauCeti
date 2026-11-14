/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Examples
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import TauCeti.GroupTheory.TriangleGroup.CosetClassification
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjJ
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup

/-!
# The modular coset dictionary and Millington's theorem

A subgroup `Γ' ≤ PSL(2, ℤ)` of finite index `n` and a numbering `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` of
its left cosets determine a permutation representation `ρ = e.permutationRepresentation` and hence a
degree-`n` permutation triple `modularTriple Γ' e = (ρ U, ρ S, ρ T)` for the projective generators
`U = S T⁻¹`, `S`, and `T`, satisfying `T S U = 1`, `U³ = 1`, and `S² = 1`.

Combining the triangle-group presentation `Δ(3, 2, ∞) ≃* PSL(2, ℤ)` with the coset classification
of `TauCeti.TriangleGroup` yields Millington's classification of finite-index subgroups of the
projective modular group:

* **The modular coset triple.** `modularTriple Γ' e` agrees with `TriangleGroup.cosetTriple`
  pulled back along `modularHom : Δ(3, 2, ∞) →* PSL(2, ℤ)`, so it is connected, has basepoint
  stabilizer `Γ'` at `e 1`, kernel `Γ'.normalCore`, and monodromy group isomorphic to
  `PSL(2, ℤ) ⧸ Γ'.normalCore`; it is regular if and only if `Γ'` is normal.
* **Alternative conventions.** Under the left-to-right coset bijection
  `Γ'.quotientEquivOp : PSL(2, ℤ) ⧸ Γ' ≃ PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op` (`gΓ' ↦ Γ'g⁻¹`), the right-action
  permutations `(σ_S, σ_R, σ_T)` satisfy `σ_R = σ_T * σ_S` and give `modularTriple` as
  `(σ_S * σ_T, σ_S, σ_T⁻¹)` (`modularTriple_quotientEquivOp_eq_ofRightCosetPerms`). Under the
  coordinate-reflection automorphism `mirrorAut` (`J = diag(-1, 1)`), the coset triple of
  `Γ'.map mirrorAut` is `(σ1 * σ0⁻¹ * σ1⁻¹, σ1, σinf⁻¹)` (`modularTriple_map_mirrorAut_eq`).
* **Millington's theorem and subgroup counts.** Two coset triples are isomorphic if and only if
  their subgroups are conjugate in `PSL(2, ℤ)` (`millington`), and define the same marked class at
  the base cosets if and only if the subgroups are equal
  (`markedIsoClass_modularConnectedTriple_eq_iff`). At each nonzero index `n`, subgroups of index
  `n` biject with marked connected triple classes of dividing orders `(3, 2, 0)`
  (`markedSubgroupEquiv`), conjugacy classes biject with unmarked connected classes
  (`conjClassesConnectedIsoClassEquiv`, `conjClassesIsoClassEquiv`), the automorphism group of
  `modularTriple Γ' e` is isomorphic to `N(Γ') ⧸ Γ'`, each conjugacy class `ω` contains
  `n / #Aut` subgroups (`card_subgroups_of_class`), and `PSL(2, ℤ)` has finitely many index-`n`
  subgroups, with small-index counts verified at `n = 1, 2, 3`.

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) **1**
  (1969), 351–357.
* C. Kurth, L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey symbols*,
  in *Advances in Algebra and Combinatorics*, World Scientific, 2008, 225–242 (arXiv:0710.1835).
-/

public section

open Equiv MulAction
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularGroup

open _root_.ModularGroup

variable {n : ℕ}

/-! ### The modular coset triple and LMFDB permutations -/

section ModularTriple

variable (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)

/-- **The modular coset triple** of a subgroup `Γ' ≤ PSL(2, ℤ)` with left-coset numbering
`e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n`: its components `(σ0, σ1, σinf)` are the permutations induced by left
multiplication by `U = S T⁻¹`, `S`, and `T`, satisfying `σinf * σ1 * σ0 = 1` from `T S U = 1`. -/
def modularTriple : PermutationTriple n where
  σ0 := e.permutationRepresentation (U : PSL(2, ℤ))
  σ1 := e.permutationRepresentation (S : PSL(2, ℤ))
  σinf := e.permutationRepresentation (T : PSL(2, ℤ))
  product_eq_one := by
    rw [← map_mul, ← map_mul, coe_T_mul_coe_S_mul_coe_U, map_one]

@[simp]
theorem modularTriple_σ0 :
    (modularTriple Γ' e).σ0 = e.permutationRepresentation (U : PSL(2, ℤ)) :=
  (rfl)

@[simp]
theorem modularTriple_σ1 :
    (modularTriple Γ' e).σ1 = e.permutationRepresentation (S : PSL(2, ℤ)) :=
  (rfl)

@[simp]
theorem modularTriple_σinf :
    (modularTriple Γ' e).σinf = e.permutationRepresentation (T : PSL(2, ℤ)) :=
  (rfl)

/-- The order-three component `σ0 = ρ U` satisfies `σ0 ^ 3 = 1`. -/
theorem modularTriple_σ0_pow_three : (modularTriple Γ' e).σ0 ^ 3 = 1 := by
  rw [modularTriple_σ0, ← map_pow, coe_U_pow_three, map_one]

/-- The order-two component `σ1 = ρ S` satisfies `σ1 ^ 2 = 1`. -/
theorem modularTriple_σ1_sq : (modularTriple Γ' e).σ1 ^ 2 = 1 := by
  rw [modularTriple_σ1, ← map_pow, coe_S_sq, map_one]

/-- The involution `σ1 = ρ S` is equal to its own inverse. -/
theorem modularTriple_σ1_inv : (modularTriple Γ' e).σ1⁻¹ = (modularTriple Γ' e).σ1 := by
  rw [modularTriple_σ1, ← map_inv, coe_S_inv]

/-- Every modular coset triple has component orders dividing `(3, 2, 0)`. -/
theorem hasDividingOrders_modularTriple : (modularTriple Γ' e).HasDividingOrders 3 2 0 :=
  (PermutationTriple.hasDividingOrders_iff _).mpr
    ⟨modularTriple_σ0_pow_three Γ' e, modularTriple_σ1_sq Γ' e, pow_zero _⟩

/-- The coset permutation of the order-two generator `S`. -/
def permS : Perm (Fin n) :=
  e.permutationRepresentation (S : PSL(2, ℤ))

/-- The coset permutation of the cusp translation `T`. -/
def permT : Perm (Fin n) :=
  e.permutationRepresentation (T : PSL(2, ℤ))

/-- The coset permutation of the order-three generator `R = S T`. -/
def permR : Perm (Fin n) :=
  e.permutationRepresentation (R : PSL(2, ℤ))

@[simp]
theorem permS_eq_σ1 : permS Γ' e = (modularTriple Γ' e).σ1 :=
  (rfl)

@[simp]
theorem permT_eq_σinf : permT Γ' e = (modularTriple Γ' e).σinf :=
  (rfl)

theorem permR_def : permR Γ' e = e.permutationRepresentation (R : PSL(2, ℤ)) :=
  (rfl)

/-- Since `R = S T`, its left-coset permutation is `permS * permT`. -/
theorem permR_eq_permS_mul_permT : permR Γ' e = permS Γ' e * permT Γ' e := by
  rw [permR, permS, permT, ← map_mul, ← QuotientGroup.mk_mul, R_def]

/-- Since `U = S R⁻¹ S⁻¹` projectively, `permR` is `(permS)⁻¹ * σ0⁻¹ * permS`. -/
theorem permR_eq_permS_inv_mul_σ0_inv_mul_permS :
    permR Γ' e = (permS Γ' e)⁻¹ * (modularTriple Γ' e).σ0⁻¹ * permS Γ' e := by
  have hR : (R : PSL(2, ℤ)) = (S : PSL(2, ℤ))⁻¹ * (U : PSL(2, ℤ))⁻¹ * S := by
    rw [← coe_S_mul_coe_R_inv_mul_coe_S_inv]
    group
  rw [permR, hR, map_mul, map_mul, map_inv, map_inv, permS, modularTriple_σ0]

@[simp]
theorem permR_pow_three : permR Γ' e ^ 3 = 1 := by
  rw [permR, ← map_pow, coe_R_pow_three, map_one]

/-- The equivariant bijection of left-coset spaces induced by
`modularHom : Δ(3, 2, ∞) →* PSL(2, ℤ)`. -/
noncomputable def modularCosetEquiv :
    TriangleGroup 3 2 0 ⧸ Γ'.comap modularHom ≃ PSL(2, ℤ) ⧸ Γ' :=
  TauCeti.QuotientGroup.congrComapOfSurjectiveMk modularHom Γ'
    (QuotientGroup.mk_surjective.comp modularHom_surjective)

@[simp]
theorem modularCosetEquiv_mk (u : TriangleGroup 3 2 0) :
    modularCosetEquiv Γ' (u : TriangleGroup 3 2 0 ⧸ Γ'.comap modularHom) =
      (modularHom u : PSL(2, ℤ) ⧸ Γ') :=
  TauCeti.QuotientGroup.congrComapOfSurjectiveMk_mk _ _ _ u

/-- **Comparison with `TriangleGroup.cosetTriple`.** Pulling `e` back along `modularHom` identifies
`modularTriple Γ' e` with the triangle-group coset triple of `Γ'.comap modularHom`. -/
theorem modularTriple_eq_cosetTriple :
    modularTriple Γ' e =
      TriangleGroup.cosetTriple (Γ'.comap modularHom) ((modularCosetEquiv Γ').trans e) := by
  refine PermutationTriple.ext_of_two ?_ ?_
  · rw [modularTriple_σ0, TriangleGroup.cosetTriple_σ0, modularCosetEquiv,
      permutationRepresentation_congrComapOfSurjectiveMk_trans, MonoidHom.comp_apply, modularHom_x]
  · rw [modularTriple_σ1, TriangleGroup.cosetTriple_σ1, modularCosetEquiv,
      permutationRepresentation_congrComapOfSurjectiveMk_trans, MonoidHom.comp_apply, modularHom_y]

/-- Every modular coset triple is connected. -/
theorem isConnected_modularTriple : (modularTriple Γ' e).IsConnected := by
  rw [modularTriple_eq_cosetTriple]
  exact TriangleGroup.isConnected_cosetTriple _ _

/-- `modularTriple Γ' e` bundled as a connected permutation triple. -/
def modularConnectedTriple : ConnectedTriple n :=
  ⟨modularTriple Γ' e, isConnected_modularTriple Γ' e⟩

@[simp]
theorem coe_modularConnectedTriple :
    (modularConnectedTriple Γ' e : PermutationTriple n) = modularTriple Γ' e :=
  (rfl)

/-- Pulling `e` back along `modularHom` identifies `modularConnectedTriple Γ' e` with the bundled
triangle-group coset triple of `Γ'.comap modularHom`. -/
theorem modularConnectedTriple_eq_cosetConnectedTriple :
    modularConnectedTriple Γ' e =
      TriangleGroup.cosetConnectedTriple (Γ'.comap modularHom)
        ((modularCosetEquiv Γ').trans e) :=
  Subtype.ext <| (coe_modularConnectedTriple Γ' e).trans <|
    (modularTriple_eq_cosetTriple Γ' e).trans (TriangleGroup.coe_cosetConnectedTriple _ _).symm

/-- Under the coset permutation representation `e.permutationRepresentation`, the stabilizer of the
base coset `e 1` is `Γ'` itself. -/
theorem comap_stabilizer_modularTriple :
    (MulAction.stabilizer (Perm (Fin n)) (e (1 : PSL(2, ℤ)))).comap
        (e.permutationRepresentation (G := PSL(2, ℤ))) =
      Γ' :=
  (e.comap_stabilizer_permutationRepresentation ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')).trans
    (MulAction.stabilizer_quotient Γ')

/-- The kernel of the coset permutation representation `e.permutationRepresentation` is the normal
core of `Γ'`. -/
theorem ker_permutationRepresentation_eq_normalCore :
    (e.permutationRepresentation (G := PSL(2, ℤ))).ker = Γ'.normalCore :=
  e.ker_permutationRepresentation.trans Γ'.normalCore_eq_ker.symm

/-- The monodromy group of `modularTriple Γ' e` is the image of `e.permutationRepresentation`. -/
@[simp]
theorem monodromyGroup_modularTriple :
    (modularTriple Γ' e).monodromyGroup = (e.permutationRepresentation (G := PSL(2, ℤ))).range := by
  rw [modularTriple_eq_cosetTriple, TriangleGroup.monodromyGroup_cosetTriple, modularCosetEquiv,
    permutationRepresentation_congrComapOfSurjectiveMk_trans, MonoidHom.range_eq_map,
    ← Subgroup.map_map, Subgroup.map_top_of_surjective _ modularHom_surjective,
    ← MonoidHom.range_eq_map]

/-- The quotient `PSL(2, ℤ) ⧸ Γ'.normalCore` is canonically isomorphic to the monodromy group of
`modularTriple Γ' e`. -/
noncomputable def quotientNormalCoreMulEquivMonodromyGroup :
    PSL(2, ℤ) ⧸ Γ'.normalCore ≃* (modularTriple Γ' e).monodromyGroup :=
  (QuotientGroup.quotientMulEquivOfEq (ker_permutationRepresentation_eq_normalCore Γ' e).symm).trans
    ((QuotientGroup.quotientKerEquivRange
      (e.permutationRepresentation (G := PSL(2, ℤ)))).trans
      (MulEquiv.subgroupCongr (monodromyGroup_modularTriple Γ' e).symm))

@[simp]
theorem coe_quotientNormalCoreMulEquivMonodromyGroup_mk (g : PSL(2, ℤ)) :
    (quotientNormalCoreMulEquivMonodromyGroup Γ' e (g : PSL(2, ℤ) ⧸ Γ'.normalCore) :
        Perm (Fin n)) =
      e.permutationRepresentation g :=
  (rfl)

/-- The order of the monodromy group of `modularTriple Γ' e` equals the index of `Γ'.normalCore`. -/
theorem card_monodromyGroup_modularTriple :
    Nat.card (modularTriple Γ' e).monodromyGroup = Γ'.normalCore.index := by
  rw [← Nat.card_congr (quotientNormalCoreMulEquivMonodromyGroup Γ' e).toEquiv,
    Subgroup.index_eq_card]

/-- `modularTriple Γ' e` is regular if and only if `Γ'` is normal in `PSL(2, ℤ)`. -/
theorem isRegular_modularTriple_iff : (modularTriple Γ' e).IsRegular ↔ Γ'.Normal := by
  rw [modularTriple_eq_cosetTriple, TriangleGroup.isRegular_cosetTriple_iff]
  constructor
  · intro hN
    have hmap : (Γ'.comap modularHom).map modularHom = Γ' :=
      Γ'.map_comap_eq_self_of_surjective modularHom_surjective
    rw [← hmap]
    exact Subgroup.Normal.map hN modularHom modularHom_surjective
  · intro _
    infer_instance

/-- `Γ'` is normal in `PSL(2, ℤ)` if and only if the monodromy group of `modularTriple Γ' e` has
order `n`. -/
theorem normal_iff_card_monodromyGroup_modularTriple_eq :
    Γ'.Normal ↔ Nat.card (modularTriple Γ' e).monodromyGroup = n := by
  rw [← isRegular_modularTriple_iff Γ' e, PermutationTriple.isRegular_iff_card_monodromyGroup,
    and_iff_right (isConnected_modularTriple Γ' e)]

/-- **Independence of the numbering.** Two coset enumerations of the same subgroup `Γ'` yield
isomorphic modular triples. -/
theorem equivalent_modularTriple (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).Equivalent (modularTriple Γ' e') := by
  rw [modularTriple_eq_cosetTriple Γ' e, modularTriple_eq_cosetTriple Γ' e']
  exact TriangleGroup.equivalent_cosetTriple _ _ _

end ModularTriple

/-- The connected isomorphism class of the modular coset triple of an index-`n` subgroup `Γ'`,
independent of the coset numbering. -/
noncomputable def modularConnectedIsoClass [NeZero n] (Γ' : Subgroup PSL(2, ℤ))
    (hΓ : Γ'.index = n) : ConnectedIsoClass n :=
  ConnectedIsoClass.mk (modularConnectedTriple Γ' (Γ'.quotientEquivFin hΓ))

theorem modularConnectedIsoClass_eq_mk [NeZero n] (Γ' : Subgroup PSL(2, ℤ)) (hΓ : Γ'.index = n)
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    modularConnectedIsoClass Γ' hΓ = ConnectedIsoClass.mk (modularConnectedTriple Γ' e) := by
  rw [modularConnectedIsoClass, ConnectedIsoClass.mk_eq_mk_iff_equivalent]
  exact equivalent_modularTriple Γ' _ e

/-- The isomorphism class in `PermutationTriple.IsoClass n` of the modular coset triple of an
index-`n` subgroup `Γ'`. -/
noncomputable def modularIsoClass [NeZero n] (Γ' : Subgroup PSL(2, ℤ)) (hΓ : Γ'.index = n) :
    PermutationTriple.IsoClass n :=
  (modularConnectedIsoClass Γ' hΓ).forget

theorem modularIsoClass_eq_mk [NeZero n] (Γ' : Subgroup PSL(2, ℤ)) (hΓ : Γ'.index = n)
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    modularIsoClass Γ' hΓ = PermutationTriple.IsoClass.mk (modularTriple Γ' e) := by
  rw [modularIsoClass, modularConnectedIsoClass_eq_mk Γ' hΓ e, ConnectedIsoClass.forget_mk,
    coe_modularConnectedTriple]

/-! ### Opposite (right-coset) convention and the coordinate-reflection mirror -/

section Conventions

/-- Build a permutation triple `(σS * σT, σS, σT⁻¹)` from right-coset permutations `σS, σT` of an
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

@[simp]
theorem ofRightCosetPerms_σ0 (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) :
    (ofRightCosetPerms σS σT hS).σ0 = σS * σT :=
  (rfl)

@[simp]
theorem ofRightCosetPerms_σ1 (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) :
    (ofRightCosetPerms σS σT hS).σ1 = σS :=
  (rfl)

@[simp]
theorem ofRightCosetPerms_σinf (σS σT : Perm (Fin n)) (hS : σS ^ 2 = 1) :
    (ofRightCosetPerms σS σT hS).σinf = σT⁻¹ :=
  (rfl)

/-- For a numbering `eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n` of the right cosets `Γ' g`, the right-action
permutations satisfy `ρR(.op R) = ρR(.op T) * ρR(.op S)`. -/
theorem rightCoset_permR_eq (Γ' : Subgroup PSL(2, ℤ)) (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    eR.permutationRepresentation (MulOpposite.op (R : PSL(2, ℤ))) =
      eR.permutationRepresentation (MulOpposite.op (T : PSL(2, ℤ))) *
        eR.permutationRepresentation (MulOpposite.op (S : PSL(2, ℤ))) := by
  rw [← map_mul, ← MulOpposite.op_mul, ← QuotientGroup.mk_mul, R_def]

/-- **Opposite-convention translation.** Under the left-to-right coset bijection
`Γ'.quotientEquivOp : PSL(2, ℤ) ⧸ Γ' ≃ PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op` (`gΓ' ↦ Γ'g⁻¹`),
`PermutationTriple.equivOppositeConvention` sends `modularTriple` to the right-action permutations
of `U, S, T`. -/
theorem equivOppositeConvention_modularTriple_quotientEquivOp (Γ' : Subgroup PSL(2, ℤ))
    (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    (PermutationTriple.equivOppositeConvention n
      (modularTriple Γ' (Γ'.quotientEquivOp.trans eR))).1 =
      (eR.permutationRepresentation (MulOpposite.op (U : PSL(2, ℤ))),
        eR.permutationRepresentation (MulOpposite.op (S : PSL(2, ℤ))),
        eR.permutationRepresentation (MulOpposite.op (T : PSL(2, ℤ)))) := by
  simp [PermutationTriple.equivOppositeConvention_apply_coe]

/-- **LMFDB right-coset row formula.** Transporting a right-coset numbering `eR` along `gΓ' ↦ Γ'g⁻¹`
produces the exact triple `(σS * σT, σS, σT⁻¹)` for `σS = ρR(.op S)` and `σT = ρR(.op T)`, while
`permR` is `(ρR(.op R))⁻¹`. -/
theorem modularTriple_quotientEquivOp_eq_ofRightCosetPerms (Γ' : Subgroup PSL(2, ℤ))
    (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    modularTriple Γ' (Γ'.quotientEquivOp.trans eR) =
      ofRightCosetPerms
        (eR.permutationRepresentation (MulOpposite.op (S : PSL(2, ℤ))))
        (eR.permutationRepresentation (MulOpposite.op (T : PSL(2, ℤ))))
        (by rw [← map_pow, ← MulOpposite.op_pow, coe_S_sq, MulOpposite.op_one, map_one]) := by
  have hUinv : (U : PSL(2, ℤ))⁻¹ = (T : PSL(2, ℤ)) * S := by
    rw [U_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_rev, inv_inv, coe_S_inv]
  refine PermutationTriple.ext_of_two ?_ ?_
  · rw [modularTriple_σ0, permutationRepresentation_quotientEquivOp_trans_apply,
      ← map_inv, ← MulOpposite.op_inv, hUinv, MulOpposite.op_mul, map_mul, ofRightCosetPerms_σ0]
  · rw [modularTriple_σ1, permutationRepresentation_quotientEquivOp_trans_apply,
      ← map_inv, ← MulOpposite.op_inv, coe_S_inv, ofRightCosetPerms_σ1]

@[simp]
theorem permR_quotientEquivOp_trans (Γ' : Subgroup PSL(2, ℤ))
    (eR : PSL(2, ℤ)ᵐᵒᵖ ⧸ Γ'.op ≃ Fin n) :
    permR Γ' (Γ'.quotientEquivOp.trans eR) =
      (eR.permutationRepresentation (MulOpposite.op (R : PSL(2, ℤ))))⁻¹ :=
  permutationRepresentation_quotientEquivOp_trans_apply Γ' eR (R : PSL(2, ℤ))

/-- **The coordinate-reflection automorphism of `PSL(2, ℤ)`** induced by conjugation by
`J = diag(-1, 1)` on `SL(2, ℤ)`. -/
def mirrorAut : MulAut PSL(2, ℤ) :=
  MulAut.mapQuotient (Subgroup.center SL(2, ℤ)) Matrix.SpecialLinearGroup.conjJMulAut

@[simp]
theorem mirrorAut_mk (γ : SL(2, ℤ)) :
    mirrorAut (γ : PSL(2, ℤ)) = (Matrix.SpecialLinearGroup.conjJ γ : PSL(2, ℤ)) :=
  (MulAut.mapQuotient_mk (Subgroup.center SL(2, ℤ)) Matrix.SpecialLinearGroup.conjJMulAut γ).trans
    (congrArg _ (Matrix.SpecialLinearGroup.conjJMulAut_apply γ))

@[simp]
theorem mirrorAut_mirrorAut (g : PSL(2, ℤ)) : mirrorAut (mirrorAut g) = g := by
  induction g using QuotientGroup.induction_on with
  | H γ => rw [mirrorAut_mk, mirrorAut_mk, Matrix.SpecialLinearGroup.conjJ_conjJ]

@[simp]
theorem mirrorAut_symm : mirrorAut.symm = mirrorAut :=
  MulEquiv.ext fun g ↦ mirrorAut.symm_apply_eq.mpr (mirrorAut_mirrorAut g).symm

/-- Coordinate reflection negates `S` in `SL(2, ℤ)`. -/
@[simp]
theorem conjJ_S : Matrix.SpecialLinearGroup.conjJ S = -S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_S]

/-- Coordinate reflection inverts `T` in `SL(2, ℤ)`. -/
@[simp]
theorem conjJ_T : Matrix.SpecialLinearGroup.conjJ T = T⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, coe_T]

/-- Coordinate reflection sends `U = S T⁻¹` to `-R` in `SL(2, ℤ)`. -/
@[simp]
theorem conjJ_U : Matrix.SpecialLinearGroup.conjJ U = -R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_U, coe_R]

/-- Coordinate reflection sends `R = S T` to `-U` in `SL(2, ℤ)`. -/
@[simp]
theorem conjJ_R : Matrix.SpecialLinearGroup.conjJ R = -U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_R, coe_U]

theorem mirrorAut_coe_S : mirrorAut (S : PSL(2, ℤ)) = S := by
  rw [mirrorAut_mk, conjJ_S, QuotientGroup.eq,
    Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by simp)

theorem mirrorAut_coe_T : mirrorAut (T : PSL(2, ℤ)) = (T : PSL(2, ℤ))⁻¹ := by
  rw [mirrorAut_mk, conjJ_T, QuotientGroup.mk_inv]

theorem mirrorAut_coe_U : mirrorAut (U : PSL(2, ℤ)) = R := by
  rw [mirrorAut_mk, conjJ_U, QuotientGroup.eq,
    Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by simp)

theorem mirrorAut_coe_R : mirrorAut (R : PSL(2, ℤ)) = U := by
  rw [← mirrorAut_coe_U, mirrorAut_mirrorAut]

/-- The mirror of a permutation triple with involutive `σ1`, given by
`(σ1 * σ0⁻¹ * σ1⁻¹, σ1, σinf⁻¹)`. -/
def mirrorTriple (t : PermutationTriple n) (h1 : t.σ1 ^ 2 = 1) : PermutationTriple n where
  σ0 := t.σ1 * t.σ0⁻¹ * t.σ1⁻¹
  σ1 := t.σ1
  σinf := t.σinf⁻¹
  product_eq_one := by
    have h1' : t.σ1 * t.σ1 = 1 := by rwa [← sq]
    rw [← t.σ1_mul_σ0_eq_σinf_inv]
    calc t.σ1 * t.σ0 * t.σ1 * (t.σ1 * t.σ0⁻¹ * t.σ1⁻¹)
        = t.σ1 * t.σ0 * (t.σ1 * t.σ1) * t.σ0⁻¹ * t.σ1⁻¹ := by group
      _ = 1 := by rw [h1', mul_one]; group

@[simp]
theorem mirrorTriple_σ0 (t : PermutationTriple n) (h1 : t.σ1 ^ 2 = 1) :
    (mirrorTriple t h1).σ0 = t.σ1 * t.σ0⁻¹ * t.σ1⁻¹ :=
  (rfl)

@[simp]
theorem mirrorTriple_σ1 (t : PermutationTriple n) (h1 : t.σ1 ^ 2 = 1) :
    (mirrorTriple t h1).σ1 = t.σ1 :=
  (rfl)

@[simp]
theorem mirrorTriple_σinf (t : PermutationTriple n) (h1 : t.σ1 ^ 2 = 1) :
    (mirrorTriple t h1).σinf = t.σinf⁻¹ :=
  (rfl)

/-- Mapping a subgroup of `PSL(2, ℤ)` twice by the involution `mirrorAut` returns the subgroup. -/
@[simp]
theorem map_mirrorAut_map_mirrorAut (Γ' : Subgroup PSL(2, ℤ)) :
    (Γ'.map (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ))).map (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ)) =
      Γ' := by
  rw [Subgroup.map_map]
  have hcomp : (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ)).comp (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ)) =
      MonoidHom.id PSL(2, ℤ) :=
    MonoidHom.ext mirrorAut_mirrorAut
  rw [hcomp, Subgroup.map_id]

/-- **Mirror coset triple formula.** Under the coset bijection induced by `mirrorAut`, the modular
triple of `Γ'.map mirrorAut` is literally `(σ1 * σ0⁻¹ * σ1⁻¹, σ1, σinf⁻¹)`. -/
theorem modularTriple_map_mirrorAut_eq (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    modularTriple (Γ'.map (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ)))
        ((TauCeti.QuotientGroup.congrOfMapEq mirrorAut (map_mirrorAut_map_mirrorAut Γ')).trans e) =
      mirrorTriple (modularTriple Γ' e) (modularTriple_σ1_sq Γ' e) := by
  have hR : (R : PSL(2, ℤ)) = S * (U : PSL(2, ℤ))⁻¹ * (S : PSL(2, ℤ))⁻¹ := by
    rw [← coe_S_mul_coe_R_inv_mul_coe_S_inv, coe_S_inv]
    group
  refine PermutationTriple.ext_of_two ?_ ?_
  · rw [modularTriple_σ0, permutationRepresentation_congrOfMapEq_trans]
    simp [-mirrorAut_mk, mirrorAut_coe_U, hR, ← map_inv]
  · rw [modularTriple_σ1, permutationRepresentation_congrOfMapEq_trans]
    simp [-mirrorAut_mk, mirrorAut_coe_S]

/-- For any numbering `e'` of `PSL(2, ℤ) ⧸ Γ'.map mirrorAut`, its modular triple is isomorphic to
`mirrorTriple (modularTriple Γ' e) _`. -/
theorem equivalent_modularTriple_map_mirrorAut (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    (modularTriple (Γ'.map (mirrorAut : PSL(2, ℤ) →* PSL(2, ℤ))) e').Equivalent
      (mirrorTriple (modularTriple Γ' e) (modularTriple_σ1_sq Γ' e)) := by
  rw [← modularTriple_map_mirrorAut_eq Γ' e]
  exact equivalent_modularTriple _ e' _

end Conventions

/-! ### Millington's theorem, marked and unmarked bijections, and subgroup counts -/

section Millington

private theorem coe_modularEquiv :
    (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) = modularHom :=
  TriangleGroup.hom_ext _ _ _ (by simp) (by simp)

private theorem cosetTriple_congrOfMapEq_modularEquiv {H : Subgroup (TriangleGroup 3 2 0)}
    {Γ' : Subgroup PSL(2, ℤ)} (h : H.map (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) = Γ')
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    TriangleGroup.cosetTriple H ((TauCeti.QuotientGroup.congrOfMapEq modularEquiv h).trans e) =
      modularTriple Γ' e := by
  refine PermutationTriple.ext_of_two ?_ ?_
  · rw [TriangleGroup.cosetTriple_σ0, permutationRepresentation_congrOfMapEq_trans]
    simp
  · rw [TriangleGroup.cosetTriple_σ1, permutationRepresentation_congrOfMapEq_trans]
    simp

/-- **Millington's theorem (conjugacy criterion).** Two subgroups `Γ₁, Γ₂ ≤ PSL(2, ℤ)` with coset
enumerations of the same degree `n` yield isomorphic modular triples if and only if `Γ₁` and `Γ₂`
are conjugate in `PSL(2, ℤ)`. -/
theorem millington {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n) (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n) :
    (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂) ↔
      ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂ := by
  rw [modularTriple_eq_cosetTriple, modularTriple_eq_cosetTriple,
    TriangleGroup.equivalent_cosetTriple_iff, ← MulAction.mem_orbit_iff,
    TauCeti.mem_orbit_conjAct_iff, ← coe_modularEquiv,
    Subgroup.exists_map_conj_comap_eq_iff, ← TauCeti.mem_orbit_conjAct_iff,
    MulAction.mem_orbit_iff]

/-- **Pointed Millington classification.** Marking the base cosets `e₁ 1` and `e₂ 1` determines the
subgroup of `PSL(2, ℤ)` on the nose. -/
theorem markedIsoClass_modularConnectedTriple_eq_iff {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n) (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n) :
    MarkedIsoClass.mk (modularConnectedTriple Γ₁ e₁) (e₁ (1 : PSL(2, ℤ))) =
      MarkedIsoClass.mk (modularConnectedTriple Γ₂ e₂) (e₂ (1 : PSL(2, ℤ))) ↔
        Γ₁ = Γ₂ := by
  have he1 (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
      e (1 : PSL(2, ℤ)) = ((modularCosetEquiv Γ').trans e) (1 : TriangleGroup 3 2 0) := by
    -- Rewrite `1` in the quotient as `QuotientGroup.mk 1` to evaluate `modularCosetEquiv_mk`.
    change e (QuotientGroup.mk 1) = e (modularCosetEquiv Γ' (QuotientGroup.mk 1))
    rw [modularCosetEquiv_mk, map_one]
  rw [modularConnectedTriple_eq_cosetConnectedTriple Γ₁ e₁,
    modularConnectedTriple_eq_cosetConnectedTriple Γ₂ e₂, he1 Γ₁ e₁, he1 Γ₂ e₂,
    TriangleGroup.markedIsoClass_cosetConnectedTriple_eq_iff]
  exact ⟨fun h ↦ by
    rw [← Γ₁.map_comap_eq_self_of_surjective modularHom_surjective,
      ← Γ₂.map_comap_eq_self_of_surjective modularHom_surjective, h],
    congrArg (Subgroup.comap modularHom)⟩

/-- **Surjectivity of `modularTriple` at a chosen sheet.** Every connected degree-`n` triple `t`
with `t.σ0 ^ 3 = 1` and `t.σ1 ^ 2 = 1` and chosen sheet `i` equals `modularTriple Γ' e` for an
index-`n` subgroup `Γ' ≤ PSL(2, ℤ)` and coset enumeration `e` sending `1` to `i`. -/
theorem exists_modularTriple_eq {t : PermutationTriple n} (ht : t.IsConnected)
    (h0 : t.σ0 ^ 3 = 1) (h1 : t.σ1 ^ 2 = 1) (i : Fin n) :
    ∃ (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n),
      Γ'.index = n ∧ e (1 : PSL(2, ℤ)) = i ∧ modularTriple Γ' e = t := by
  obtain ⟨H, eH, hH, heH1, het⟩ := TriangleGroup.exists_cosetTriple_eq ht h0 h1 (pow_zero _) i
  let Γ' : Subgroup PSL(2, ℤ) := H.map (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ))
  let cv := TauCeti.QuotientGroup.congrOfMapEq modularEquiv (rfl : H.map _ = Γ')
  let e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n := cv.symm.trans eH
  have htrans : cv.trans e = eH := by
    ext q
    simp [e]
  refine ⟨Γ', e, (H.index_map_equiv modularEquiv).trans hH, ?_, ?_⟩
  · -- Unfold `e` on `QuotientGroup.mk 1` through `cv.symm`.
    change eH (cv.symm (QuotientGroup.mk 1)) = i
    have hsymm : cv.symm (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
      rw [Equiv.symm_apply_eq, TauCeti.QuotientGroup.congrOfMapEq_mk, map_one]
    rw [hsymm]
    exact heH1
  · rw [← cosetTriple_congrOfMapEq_modularEquiv rfl e, htrans, het]

/-- **Millington's theorem (surjectivity).** Every connected degree-`n` triple `t` satisfying
`t.σ0 ^ 3 = 1` and `t.σ1 ^ 2 = 1` is isomorphic to `modularTriple Γ' e` for an index-`n` subgroup
`Γ' ≤ PSL(2, ℤ)`. -/
theorem exists_modularTriple_equivalent {t : PermutationTriple n} (ht : t.IsConnected)
    (h0 : t.σ0 ^ 3 = 1) (h1 : t.σ1 ^ 2 = 1) :
    ∃ (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n),
      Γ'.index = n ∧ (modularTriple Γ' e).Equivalent t := by
  obtain ⟨Γ', e, hΓ, -, rfl⟩ := exists_modularTriple_eq ht h0 h1 ⟨0, Nat.pos_of_ne_zero ht.ne_zero⟩
  exact ⟨Γ', e, hΓ, PermutationTriple.equivalent_iff_exists_smul_eq.mpr ⟨1, one_smul _ _⟩⟩

/-- **Marked subgroup bijection for `PSL(2, ℤ)`.** For `n ≠ 0`, subgroups of index `n` in
`PSL(2, ℤ)` biject with marked isomorphism classes of connected degree-`n` triples whose component
orders divide `(3, 2, 0)`. -/
noncomputable def markedSubgroupEquiv [NeZero n] :
    {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} ≃
      {m : MarkedIsoClass n // m.HasDividingOrders 3 2 0} :=
  (modularEquiv.fixedIndexSubgroupEquiv n).symm.trans TriangleGroup.markedSubgroupEquiv

/-- For any coset enumeration `e`, `markedSubgroupEquiv` sends `Γ'` to the class of
`modularConnectedTriple Γ' e` marked at `e 1`. -/
theorem coe_markedSubgroupEquiv_apply [NeZero n]
    (Γ' : {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}) (e : PSL(2, ℤ) ⧸ Γ'.1 ≃ Fin n) :
    (markedSubgroupEquiv Γ' : MarkedIsoClass n) =
      MarkedIsoClass.mk (modularConnectedTriple Γ'.1 e) (e (1 : PSL(2, ℤ))) := by
  let K := (modularEquiv.fixedIndexSubgroupEquiv n).symm Γ'
  have hmap : K.1.map (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) = Γ'.1 := by
    rw [MulEquiv.coe_fixedIndexSubgroupEquiv_symm_apply]
    exact Γ'.1.map_comap_eq_self_of_surjective modularEquiv.surjective
  let eK : TriangleGroup 3 2 0 ⧸ K.1 ≃ Fin n :=
    (TauCeti.QuotientGroup.congrOfMapEq modularEquiv hmap).trans e
  have hconn : TriangleGroup.cosetConnectedTriple K.1 eK = modularConnectedTriple Γ'.1 e :=
    Subtype.ext <| (TriangleGroup.coe_cosetConnectedTriple K.1 eK).trans <|
      (cosetTriple_congrOfMapEq_modularEquiv hmap e).trans (coe_modularConnectedTriple Γ'.1 e).symm
  have he1 : eK (1 : TriangleGroup 3 2 0) = e (1 : PSL(2, ℤ)) := by
    -- Express `1` as `QuotientGroup.mk 1` to apply `congrOfMapEq_mk`.
    change e (TauCeti.QuotientGroup.congrOfMapEq modularEquiv hmap (QuotientGroup.mk 1)) =
      e (QuotientGroup.mk 1)
    rw [TauCeti.QuotientGroup.congrOfMapEq_mk, map_one]
  rw [markedSubgroupEquiv, Equiv.trans_apply, ← hconn, ← he1]
  exact TriangleGroup.coe_markedSubgroupEquiv_apply K eK

/-- **Millington's bijection on conjugacy classes.** For `n ≠ 0`, conjugacy classes of index-`n`
subgroups of `PSL(2, ℤ)` biject with connected isomorphism classes of degree-`n` triples with
dividing orders `(3, 2, 0)`. -/
noncomputable def conjClassesConnectedIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} ≃
      {C : ConnectedIsoClass n // C.HasDividingOrders 3 2 0} :=
  (modularEquiv.fixedIndexConjClassesEquiv n).symm.trans
    TriangleGroup.conjClassesConnectedIsoClassEquiv

/-- For any coset enumeration `e`, `conjClassesConnectedIsoClassEquiv` sends the conjugacy class of
`Γ'` to `ConnectedIsoClass.mk (modularConnectedTriple Γ' e)`. -/
theorem coe_conjClassesConnectedIsoClassEquiv_mk [NeZero n]
    (Γ' : {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}) (e : PSL(2, ℤ) ⧸ Γ'.1 ≃ Fin n) :
    (conjClassesConnectedIsoClassEquiv (Quotient.mk'' Γ') : ConnectedIsoClass n) =
      ConnectedIsoClass.mk (modularConnectedTriple Γ'.1 e) := by
  let K := (modularEquiv.fixedIndexSubgroupEquiv n).symm Γ'
  have hmap : K.1.map (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) = Γ'.1 := by
    rw [MulEquiv.coe_fixedIndexSubgroupEquiv_symm_apply]
    exact Γ'.1.map_comap_eq_self_of_surjective modularEquiv.surjective
  let eK : TriangleGroup 3 2 0 ⧸ K.1 ≃ Fin n :=
    (TauCeti.QuotientGroup.congrOfMapEq modularEquiv hmap).trans e
  have hconn : TriangleGroup.cosetConnectedTriple K.1 eK = modularConnectedTriple Γ'.1 e :=
    Subtype.ext <| (TriangleGroup.coe_cosetConnectedTriple K.1 eK).trans <|
      (cosetTriple_congrOfMapEq_modularEquiv hmap e).trans (coe_modularConnectedTriple Γ'.1 e).symm
  rw [conjClassesConnectedIsoClassEquiv, Equiv.trans_apply,
    modularEquiv.fixedIndexConjClassesEquiv_symm_mk, ← hconn]
  exact TriangleGroup.coe_conjClassesConnectedIsoClassEquiv_mk K eK

/-- **Millington's bijection into `PermutationTriple.IsoClass n`.** For `n ≠ 0`, conjugacy classes
of index-`n` subgroups of `PSL(2, ℤ)` biject with the subtype of `PermutationTriple.IsoClass n` cut
out by connectedness and `σ0 ^ 3 = 1`, `σ1 ^ 2 = 1`. -/
noncomputable def conjClassesIsoClassEquiv [NeZero n] :
    MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} ≃
      {C : PermutationTriple.IsoClass n // C.IsConnected ∧ C.HasDividingOrders 3 2 0} :=
  conjClassesConnectedIsoClassEquiv.trans
    (ConnectedIsoClass.equivIsoClassSubtypeDividingOrders n 3 2 0)

/-- For any coset enumeration `e`, `conjClassesIsoClassEquiv` sends the conjugacy class of `Γ'` to
`PermutationTriple.IsoClass.mk (modularTriple Γ' e)`. -/
theorem coe_conjClassesIsoClassEquiv_mk [NeZero n]
    (Γ' : {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}) (e : PSL(2, ℤ) ⧸ Γ'.1 ≃ Fin n) :
    (conjClassesIsoClassEquiv (Quotient.mk'' Γ') : PermutationTriple.IsoClass n) =
      PermutationTriple.IsoClass.mk (modularTriple Γ'.1 e) := by
  rw [conjClassesIsoClassEquiv, Equiv.trans_apply,
    ConnectedIsoClass.coe_equivIsoClassSubtypeDividingOrders_apply,
    coe_conjClassesConnectedIsoClassEquiv_mk Γ' e, ConnectedIsoClass.forget_mk,
    coe_modularConnectedTriple]

/-- **The deck-transformation isomorphism.** Right multiplication on cosets identifies the
normalizer quotient `N(Γ') ⧸ Γ'` with the automorphism group of `modularTriple Γ' e`. -/
noncomputable def normalizerQuotientEquivAutomorphismGroup
    (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Subgroup.normalizer (Γ' : Set PSL(2, ℤ)) ⧸
        Γ'.subgroupOf (Subgroup.normalizer (Γ' : Set PSL(2, ℤ))) ≃*
      (modularTriple Γ' e).automorphismGroup :=
  (Γ'.normalizerQuotientEquivCentralizer e).trans <|
    MulEquiv.subgroupCongr <| by
      rw [(modularTriple Γ' e).automorphismGroup_eq_centralizer_monodromyGroup,
        monodromyGroup_modularTriple]

@[simp]
theorem coe_normalizerQuotientEquivAutomorphismGroup_mk_apply
    (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (m : Subgroup.normalizer (Γ' : Set PSL(2, ℤ))) (g : PSL(2, ℤ)) :
    (normalizerQuotientEquivAutomorphismGroup Γ' e (m : _ ⧸ _) : Perm (Fin n))
        (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e ((g * (m : PSL(2, ℤ))⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') :=
  Γ'.coe_normalizerQuotientEquivCentralizer_mk_apply e m g

/-- The automorphism group of `modularTriple Γ' e` has order `[N(Γ') : Γ']`. -/
theorem card_automorphismGroup_modularTriple
    (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Nat.card (modularTriple Γ' e).automorphismGroup =
      Γ'.relIndex (Subgroup.normalizer (Γ' : Set PSL(2, ℤ))) := by
  rw [(modularTriple Γ' e).automorphismGroup_eq_centralizer_monodromyGroup,
    monodromyGroup_modularTriple, Γ'.card_centralizer_permutationRepresentation e]

/-- The number of conjugates of `Γ'` in `PSL(2, ℤ)` is
`n / #(modularTriple Γ' e).automorphismGroup`. -/
theorem card_orbit_conjAct_eq_div_automorphismGroup
    (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Nat.card (MulAction.orbit (ConjAct PSL(2, ℤ)) Γ') =
      n / Nat.card (modularTriple Γ' e).automorphismGroup := by
  rw [(modularTriple Γ' e).automorphismGroup_eq_centralizer_monodromyGroup,
    monodromyGroup_modularTriple, Γ'.card_orbit_conjAct_eq_index_div_card_centralizer e,
    Γ'.index_eq_of_equiv_fin e]

/-- **Class-size formula.** The number of index-`n` subgroups in a conjugacy class `ω` of
`PSL(2, ℤ)` equals `n` divided by the automorphism order of its modular triple class. -/
theorem card_subgroups_of_class [NeZero n]
    (ω : MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}) :
    Nat.card (MulAction.orbitRel.Quotient.orbit ω) =
      n / (conjClassesConnectedIsoClassEquiv ω).1.automorphismOrder := by
  induction ω using Quotient.inductionOn' with
  | h Γ' =>
    let e := Γ'.1.quotientEquivFin Γ'.2
    rw [MulAction.orbitRel.Quotient.orbit_mk,
      Nat.card_congr (Subgroup.orbitConjActSubtypeIndexEquiv Γ'),
      card_orbit_conjAct_eq_div_automorphismGroup Γ'.1 e,
      coe_conjClassesConnectedIsoClassEquiv_mk Γ' e, ConnectedIsoClass.automorphismOrder_mk,
      coe_modularConnectedTriple]

/-! ### Finiteness at fixed index and small-index checks -/

/-- **Finiteness at fixed index.** For `n ≠ 0`, `PSL(2, ℤ)` has only finitely many subgroups of
index `n`. -/
instance [NeZero n] : Finite {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} :=
  Finite.of_equiv _ markedSubgroupEquiv.symm

/-- For `n ≠ 0`, `PSL(2, ℤ)` has only finitely many conjugacy classes of index-`n` subgroups. -/
instance [NeZero n] :
    Finite (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}) :=
  Quotient.finite _

/-- The number of conjugacy classes of index-`n` subgroups of `PSL(2, ℤ)` equals the cardinality of
`connectedIsoClassesWithDividingOrders n 3 2 0`. -/
theorem card_conjClasses_index_eq [NeZero n] :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}) =
      (connectedIsoClassesWithDividingOrders n 3 2 0).card :=
  (Nat.card_congr (modularEquiv.fixedIndexConjClassesEquiv n).symm).trans
    TriangleGroup.card_conjClasses_eq_card_connectedIsoClassesWithDividingOrders

/-- **Index-`n` subgroup count for `PSL(2, ℤ)`.** For `n ≠ 0`, the number of index-`n` subgroups of
`PSL(2, ℤ)` is `∑ C ∈ connectedIsoClassesWithDividingOrders n 3 2 0, n / C.automorphismOrder`. -/
theorem card_subgroups_index_eq_sum_div_automorphismOrder [NeZero n] :
    Nat.card {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} =
      ∑ C ∈ connectedIsoClassesWithDividingOrders n 3 2 0, n / C.automorphismOrder :=
  (Nat.card_congr (modularEquiv.fixedIndexSubgroupEquiv n).symm).trans
    TriangleGroup.card_subgroups_index_eq_sum_div_automorphismOrder

/-- On the full modular group `⊤`, the modular coset triple is the trivial degree-one triple `1`. -/
@[simp]
theorem modularTriple_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    modularTriple ⊤ e = 1 :=
  Subsingleton.elim _ _

/-- `PSL(2, ℤ)` has `1` conjugacy class of subgroups of index `1`. -/
theorem card_conjClasses_index_one :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = 1}) = 1 := by
  rw [card_conjClasses_index_eq]
  decide +kernel

/-- `PSL(2, ℤ)` has `1` conjugacy class of subgroups of index `2`. -/
theorem card_conjClasses_index_two :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = 2}) = 1 := by
  rw [card_conjClasses_index_eq]
  decide +kernel

/-- `PSL(2, ℤ)` has `2` conjugacy classes of subgroups of index `3`. -/
theorem card_conjClasses_index_three :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ))
      {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = 3}) = 2 := by
  rw [card_conjClasses_index_eq]
  decide +kernel

/-- The two connected modular triple classes in degree `3` are the regular cyclic class
`PermutationTriple.cyclicTriple 3` (corresponding to the unique normal index-`3` subgroup, of
monodromy order `3`) and `PermutationTriple.s3Triple` (corresponding to the three conjugate
subgroups in the `Γ₀(2)` class, of monodromy order `6`). -/
theorem connectedIsoClassesWithDividingOrders_three :
    connectedIsoClassesWithDividingOrders 3 3 2 0 =
      {ConnectedIsoClass.mk ⟨PermutationTriple.cyclicTriple 3,
          PermutationTriple.isConnected_cyclicTriple_iff.mpr (by decide)⟩,
        ConnectedIsoClass.mk
          ⟨PermutationTriple.s3Triple, PermutationTriple.isConnected_s3Triple⟩} := by
  decide +kernel

/-- `PSL(2, ℤ)` has `1` subgroup of index `1`. -/
theorem card_subgroups_index_one :
    Nat.card {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = 1} = 1 := by
  rw [card_subgroups_index_eq_sum_div_automorphismOrder]
  simp only [← ConnectedIsoClass.computedAutomorphismOrder_eq]
  decide +kernel

/-- `PSL(2, ℤ)` has `1` subgroup of index `2` (the unique index-`2` subgroup is normal). -/
theorem card_subgroups_index_two :
    Nat.card {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = 2} = 1 := by
  rw [card_subgroups_index_eq_sum_div_automorphismOrder]
  simp only [← ConnectedIsoClass.computedAutomorphismOrder_eq]
  decide +kernel

/-- `PSL(2, ℤ)` has `4` subgroups of index `3`: one normal subgroup of automorphism order `3` and
three conjugate subgroups of automorphism order `1`. -/
theorem card_subgroups_index_three :
    Nat.card {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = 3} = 4 := by
  rw [card_subgroups_index_eq_sum_div_automorphismOrder]
  simp only [← ConnectedIsoClass.computedAutomorphismOrder_eq]
  decide +kernel

end Millington

end TauCeti.ModularGroup
