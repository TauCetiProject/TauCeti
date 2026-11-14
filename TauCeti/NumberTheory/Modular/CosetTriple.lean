/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup
public import TauCeti.Combinatorics.PermutationTriple.Enumeration
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import TauCeti.GroupTheory.TriangleGroup.CosetTriple
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjJ
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The modular coset triple and Millington's theorem

Through `TauCeti.ModularGroup.modularEquiv : TriangleGroup 3 2 0 ≃* PSL(2, ℤ)` sending `x, y, z` to
`U = S T⁻¹`, `S`, and `T`, every subgroup `Γ'` of `PSL(2, ℤ)` with a coset numbering
`e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` determines a connected permutation triple
`TauCeti.ModularGroup.modularTriple Γ' e` of degree `n` with `σ0 ^ 3 = 1` and `σ1 ^ 2 = 1`.
Specializing `TauCeti.GroupTheory.TriangleGroup.CosetTriple` along `modularEquiv` gives Millington's
dictionary for `PSL(2, ℤ)`:

* **The modular triple (`TauCeti.ModularGroup.modularTriple`).** Its components are the coset
  permutations of `U`, `S`, and `T` (`permS`, `permT`, and `permR` for `S`, `T`, and `R = S T`).
  Via `TauCeti.ModularGroup.modularTriple_eq_cosetTriple`, it is connected with stabilizer `Γ'` at
  `e 1`, monodromy `PSL(2, ℤ) ⧸ Γ'.normalCore`, and `IsRegular ↔ Γ'.Normal`.
* **Opposite and mirror conventions.** Passing from right cosets `Γ' g` to left cosets via
  `g Γ' ↦ Γ' g⁻¹` gives the LMFDB formulas (`TauCeti.ModularGroup.modularTriple_quotientRightRel`),
  and conjugation by `diag(-1, 1)` (`TauCeti.ModularGroup.conjJAut`) mirrors the modular triple
  (`TauCeti.ModularGroup.equivalent_mirror_modularTriple`).
* **Millington's theorem (`TauCeti.ModularGroup.millington`, `modularIsoClassEquiv`,
  `modularMarkedIsoClassEquiv`).** Modular triples are isomorphic iff the subgroups are conjugate in
  `PSL(2, ℤ)`, giving bijections with `modularIsoClasses n` and `modularMarkedIsoClasses n` for
  `n ≠ 0` and the subgroup-count identity `TauCeti.ModularGroup.card_subgroups_of_class`.
* **Finiteness and small indices (`TauCeti.ModularGroup.finite_subgroups_of_index`,
  `infinite_orbitRel_quotient_ofIndex_zero`, `natCard_orbitRel_quotient_ofIndex_eq`).** `PSL(2, ℤ)`
  has finitely many subgroups of each nonzero index `n`, infinitely many conjugacy classes of
  infinite index (`n = 0`), and `1`, `1`, `2` conjugacy classes in indices `1`, `2`, `3`.

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

/-- A coset numbering `PSL(2, ℤ) ⧸ Γ' ≃ Fin n` witnesses that `Γ'` has index `n`. -/
theorem index_eq_of_equiv (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Γ'.index = n := by
  rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_fin]

/-- A coset space `PSL(2, ℤ) ⧸ Γ'` is nonempty, so any `Fin n` numbering forces `n ≠ 0`. -/
theorem ne_zero_of_equiv (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : n ≠ 0 :=
  TriangleGroup.ne_zero_of_equiv _
    ((TauCeti.QuotientGroup.congrOfMapEq modularEquiv
      (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ')).trans e)

/-- A subgroup of `PSL(2, ℤ)` whose cosets are numbered by `Fin n` has finite index. -/
theorem finiteIndex_of_equiv (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Γ'.FiniteIndex :=
  ⟨by rw [index_eq_of_equiv Γ' e]; exact ne_zero_of_equiv Γ' e⟩

/-- Every modular coset triple is connected. -/
theorem isConnected_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).IsConnected := by
  rw [modularTriple_eq_cosetTriple]
  exact TriangleGroup.isConnected_cosetTriple _ _

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

/-- The isomorphism class of the modular triple of a finite-index subgroup `Γ' ≤ PSL(2, ℤ)`,
independent of the coset numbering. -/
noncomputable def modularIsoClass (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    IsoClass Γ'.index :=
  have : Finite (PSL(2, ℤ) ⧸ Γ') :=
    Nat.finite_of_card_ne_zero
      (by rw [← Subgroup.index_eq_card]; exact Subgroup.FiniteIndex.index_ne_zero)
  IsoClass.mk (modularTriple Γ' (Finite.equivFinOfCardEq (Subgroup.index_eq_card Γ').symm))

/-- `modularIsoClass Γ'` equals `IsoClass.mk (modularTriple Γ' e)` for every coset numbering `e`. -/
theorem modularIsoClass_eq_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin Γ'.index) :
    modularIsoClass Γ' = IsoClass.mk (modularTriple Γ' e) :=
  IsoClass.mk_eq_mk_iff.mpr (equivalent_modularTriple Γ' _ e)

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

/-- Under the left-coset numbering `(quotientRightRelEquivQuotientLeftRel Γ').symm.trans r`
induced from a right-coset numbering `r` by `g Γ' ↦ Γ' g⁻¹`, passing to
`PermutationTriple.equivOppositeConvention` recovers the right-multiplication permutations of
`U`, `S`, and `T` on right cosets. -/
theorem equivOppositeConvention_modularTriple_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    (equivOppositeConvention n
      (modularTriple Γ'
        ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r))).1 =
      (r.permCongr (Γ'.rightCosetPerm (U : PSL(2, ℤ))),
        r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))),
        r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))) := by
  simp [Equiv.permCongr_rightCosetPerm]

/-- **LMFDB row translation.** In terms of the right-coset permutations
`s_row := r.permCongr (Γ'.rightCosetPerm S)` and `t_row := r.permCongr (Γ'.rightCosetPerm T)`,
the right-coset permutation of `R = S T` is `t_row * s_row`, the modular triple under the induced
left-coset numbering is `(s_row * t_row, s_row, t_row⁻¹)`, and `permR` is `(t_row * s_row)⁻¹`. -/
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

/-- The involutive outer automorphism of `PSL(2, ℤ)` induced by conjugation by `diag(-1, 1)` on
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

/-- `conjJAut` fixes `S` in `PSL(2, ℤ)`. -/
@[simp] theorem conjJAut_S : conjJAut (S : PSL(2, ℤ)) = S := by
  have hS : SpecialLinearGroup.conjJ S = -S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_S]
  rw [conjJAut_mk, hS, QuotientGroup.eq, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  simp

/-- `conjJAut` inverts `T` in `PSL(2, ℤ)`. -/
@[simp] theorem conjJAut_T : conjJAut (T : PSL(2, ℤ)) = (T : PSL(2, ℤ))⁻¹ := by
  have hT : SpecialLinearGroup.conjJ T = T⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_T]
  rw [conjJAut_mk, hT, QuotientGroup.mk_inv]

/-- `conjJAut` sends `U = S T⁻¹` to `R = S T`. -/
@[simp] theorem conjJAut_U : conjJAut (U : PSL(2, ℤ)) = R := by
  rw [U_def, R_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, conjJAut_S,
    conjJAut_T, inv_inv, QuotientGroup.mk_mul]

/-- `conjJAut` sends `R = S T` to `U = S T⁻¹`. -/
@[simp] theorem conjJAut_R : conjJAut (R : PSL(2, ℤ)) = U := by
  rw [← conjJAut_U, conjJAut_conjJAut]

private theorem coe_S_mul_coe_U_inv_mul_coe_S :
    (S : PSL(2, ℤ)) * (U : PSL(2, ℤ))⁻¹ * S = R := by
  rw [R_def, U_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    _root_.mul_inv_rev, inv_inv, coe_S_inv, ← mul_assoc (S : PSL(2, ℤ)) T S,
    _root_.Matrix.ProjectiveSpecialLinearGroup.mul_coe_S_mul_coe_S]

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

/-- **Surjectivity of Millington's dictionary.** Every connected permutation triple of degree `n`
with `σ0 ^ 3 = 1` and `σ1 ^ 2 = 1` is isomorphic to the modular triple of a finite-index subgroup
of `PSL(2, ℤ)` of index `n`. -/
theorem exists_modularTriple_equivalent {t : PermutationTriple n} (ht : t.IsConnected)
    (h0 : t.σ0 ^ 3 = 1) (h1 : t.σ1 ^ 2 = 1) :
    ∃ (Γ' : Subgroup PSL(2, ℤ)) (_ : Γ'.FiniteIndex) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n),
      Γ'.index = n ∧ (modularTriple Γ' e).Equivalent t := by
  obtain ⟨H, _, eH, -, heq⟩ := TriangleGroup.exists_cosetTriple_equivalent ht
    ((hasDividingOrders_iff t).mpr ⟨h0, h1, pow_zero _⟩)
  let Γ' := H.map (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ))
  let e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n :=
    (TauCeti.QuotientGroup.congrOfMapEq modularEquiv (rfl : Γ' = Γ')).symm.trans eH
  refine ⟨Γ', finiteIndex_of_equiv Γ' e, e, index_eq_of_equiv Γ' e, ?_⟩
  rw [modularTriple_eq_cosetTriple Γ' e, ← IsoClass.mk_eq_mk_iff, ← IsoClass.mk_eq_mk_iff.mpr heq,
    IsoClass.mk_eq_mk_iff, TriangleGroup.cosetTriple_equivalent_cosetTriple_iff]
  exact ⟨1, by rw [one_smul, Subgroup.comap_map_eq_self_of_injective modularEquiv.injective H]⟩

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
    (e : PSL(2, ℤ) ⧸ Γ'.1 ≃ Fin n) :
    (modularIsoClassEquiv (Quotient.mk'' Γ') : IsoClass n) =
      IsoClass.mk (modularTriple Γ'.1 e) := by
  have hcomap : (modularEquiv.symm.ofIndexEquiv n Γ' : Subgroup (TriangleGroup 3 2 0)) =
      Γ'.1.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) :=
    (modularEquiv.symm.coe_ofIndexEquiv_apply n Γ').trans
      (Subgroup.comap_equiv_eq_map_symm modularEquiv Γ'.1).symm
  rw [modularIsoClassEquiv, Equiv.trans_apply, Equiv.trans_apply,
    MulEquiv.orbitRelQuotientOfIndexEquiv_mk, Set.equivOfEq_apply]
  have heq := TriangleGroup.coe_cosetIsoClassEquiv_mk (modularEquiv.symm.ofIndexEquiv n Γ')
    ((Subgroup.quotientEquivOfEq hcomap).trans
      ((TauCeti.QuotientGroup.congrOfMapEq modularEquiv
        (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ'.1)).trans e))
  rw [heq, modularTriple_eq_cosetTriple Γ'.1 e, IsoClass.mk_eq_mk_iff,
    TriangleGroup.cosetTriple_equivalent_cosetTriple_iff]
  exact ⟨1, by rw [one_smul, hcomap]⟩

/-- The marked isomorphism classes of connected permutation triples of degree `n` with
`σ0 ^ 3 = 1` and `σ1 ^ 2 = 1`. -/
def modularMarkedIsoClasses (n : ℕ) : Set (MarkedIsoClass n) :=
  {m | ∃ (t : ConnectedTriple n) (i : Fin n),
    t.1.σ0 ^ 3 = 1 ∧ t.1.σ1 ^ 2 = 1 ∧ MarkedIsoClass.mk t i = m}

/-- The marked class of `(t, i)` lies in `modularMarkedIsoClasses n` if and only if
`t.1.σ0 ^ 3 = 1` and `t.1.σ1 ^ 2 = 1`. -/
@[simp] theorem mk_mem_modularMarkedIsoClasses_iff {t : ConnectedTriple n} {i : Fin n} :
    MarkedIsoClass.mk t i ∈ modularMarkedIsoClasses n ↔ t.1.σ0 ^ 3 = 1 ∧ t.1.σ1 ^ 2 = 1 := by
  refine ⟨?_, fun ⟨h0, h1⟩ ↦ ⟨t, i, h0, h1, rfl⟩⟩
  rintro ⟨t', i', h0, h1, h⟩
  obtain ⟨τ, hτ, -⟩ := MarkedIsoClass.mk_eq_mk_iff_exists_smul.mp h.symm
  have hval : (t : PermutationTriple n) = τ • t'.1 := by rw [← hτ, ConnectedTriple.coe_smul]
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
    (e : PSL(2, ℤ) ⧸ Γ'.1 ≃ Fin n) :
    (modularMarkedIsoClassEquiv Γ' : MarkedIsoClass n) =
      MarkedIsoClass.mk ⟨modularTriple Γ'.1 e, isConnected_modularTriple Γ'.1 e⟩
        (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'.1)) := by
  have hcomap : (modularEquiv.symm.ofIndexEquiv n Γ' : Subgroup (TriangleGroup 3 2 0)) =
      Γ'.1.comap (modularEquiv : TriangleGroup 3 2 0 →* PSL(2, ℤ)) :=
    (modularEquiv.symm.coe_ofIndexEquiv_apply n Γ').trans
      (Subgroup.comap_equiv_eq_map_symm modularEquiv Γ'.1).symm
  let f := (TauCeti.QuotientGroup.congrOfMapEq modularEquiv
    (Subgroup.map_comap_eq_self_of_surjective modularEquiv.surjective Γ'.1)).trans e
  rw [modularMarkedIsoClassEquiv, Equiv.trans_apply, Equiv.trans_apply, Set.equivOfEq_apply,
    TriangleGroup.coe_cosetMarkedIsoClassEquiv_apply _
      ((Subgroup.quotientEquivOfEq hcomap).trans f)]
  have hf : e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'.1) =
      f ((1 : TriangleGroup 3 2 0) : TriangleGroup 3 2 0 ⧸ _) := by simp [f]
  have hc : (⟨modularTriple Γ'.1 e, isConnected_modularTriple Γ'.1 e⟩ : ConnectedTriple n) =
      ⟨TriangleGroup.cosetTriple _ f, TriangleGroup.isConnected_cosetTriple _ f⟩ :=
    Subtype.ext (modularTriple_eq_cosetTriple Γ'.1 e)
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
    index_eq_of_equiv Γ' e]

/-- **Finiteness at fixed index.** For every `n ≠ 0`, `PSL(2, ℤ)` has only finitely many subgroups
of index `n`. -/
theorem finite_ofIndex (n : ℕ) [NeZero n] : Finite (Subgroup.ofIndex PSL(2, ℤ) n) :=
  have := TriangleGroup.finite_ofIndex 3 2 0 n
  Finite.of_equiv (Subgroup.ofIndex (TriangleGroup 3 2 0) n) (modularEquiv.ofIndexEquiv n)

/-- Unbundled form of `finite_ofIndex`: `{Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n}` is finite for
`n ≠ 0`. -/
theorem finite_subgroups_of_index (n : ℕ) [NeZero n] :
    Finite {Γ' : Subgroup PSL(2, ℤ) // Γ'.index = n} :=
  have := finite_ofIndex n
  Finite.of_equiv (Subgroup.ofIndex PSL(2, ℤ) n)
    (Equiv.subtypeEquivRight fun _ ↦ Subgroup.mem_ofIndex)

/-- For every `n ≠ 0`, `PSL(2, ℤ)` has only finitely many conjugacy classes of subgroups of
index `n`. -/
theorem finite_orbitRel_quotient_ofIndex (n : ℕ) [NeZero n] :
    Finite (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n)) :=
  have := TriangleGroup.finite_orbitRel_quotient_ofIndex 3 2 0 n
  Finite.of_equiv _ (modularEquiv.orbitRelQuotientOfIndexEquiv n)

private theorem eq_or_eq_neg_of_pslMk_eq {a b : SL(2, ℤ)}
    (h : (a : PSL(2, ℤ)) = (b : PSL(2, ℤ))) : a = b ∨ a = -b := by
  rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp
      (QuotientGroup.eq.mp h) with h1 | hneg
  · exact Or.inl (inv_mul_eq_one.mp h1)
  · exact Or.inr <| by
      calc a = a * (-(a⁻¹ * b)) := by rw [hneg, neg_neg, mul_one]
        _ = -b := by rw [mul_neg, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem index_zpowers_T_pow (m : ℕ) :
    (Subgroup.zpowers ((T : PSL(2, ℤ)) ^ m)).index = 0 := by
  have : Infinite (PSL(2, ℤ) ⧸ Subgroup.zpowers ((T : PSL(2, ℤ)) ^ m)) := by
    refine Infinite.of_injective
      (fun j : ℕ ↦ (((T ^ (j : ℤ) * S : SL(2, ℤ)) : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ Subgroup.zpowers ((T : PSL(2, ℤ)) ^ m))) fun i j hij ↦ ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq.mp hij)
    have hpsl : (((T ^ (i : ℤ) * S)⁻¹ * (T ^ (j : ℤ) * S) : SL(2, ℤ)) : PSL(2, ℤ)) =
        ((T ^ ((m : ℤ) * k) : SL(2, ℤ)) : PSL(2, ℤ)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hk, _root_.zpow_mul, zpow_natCast,
        ← QuotientGroup.mk_pow, ← QuotientGroup.mk_zpow]
    have lhs_eq : (((T ^ (i : ℤ) * S)⁻¹ * (T ^ (j : ℤ) * S) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (i : ℤ) - j, 1] := by
      have hinv : (T ^ (i : ℤ) * S)⁻¹ = S⁻¹ * T ^ (-(i : ℤ)) := by
        rw [_root_.mul_inv_rev, _root_.zpow_neg]
      rw [hinv, mul_assoc, ← mul_assoc (T ^ (-(i : ℤ))), ← _root_.zpow_add]
      have hSinv : ((S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by decide
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hSinv,
        ModularGroup.coe_T_zpow, ModularGroup.coe_S, Matrix.mul_fin_two, Matrix.mul_fin_two]
      ext a b
      fin_cases a <;> fin_cases b <;> simp
      omega
    rcases eq_or_eq_neg_of_pslMk_eq hpsl with hmat | hmat
    · have h10 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 1) 0
      rw [lhs_eq, ModularGroup.coe_T_zpow] at h10
      simp at h10
      omega
    · have h00 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 0) 0
      rw [lhs_eq, Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow] at h00
      simp at h00
  rw [Subgroup.index_eq_card]
  exact Nat.card_eq_zero_of_infinite

private theorem conj_T_zpow_matrix (γ : SL(2, ℤ)) (a : ℤ) :
    ((γ * T ^ a * γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - γ 0 0 * γ 1 0 * a, γ 0 0 * γ 0 0 * a;
        -(γ 1 0 * γ 1 0 * a), 1 + γ 0 0 * γ 1 0 * a] := by
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0, γ 0 1; γ 1 0, γ 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hginv : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 1 1, -γ 0 1; -γ 1 0, γ 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hγ,
    ModularGroup.coe_T_zpow, hginv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linarith [calc γ 0 0 * γ 1 1 - (γ 0 0 * a + γ 0 1) * γ 1 0
        = (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) - γ 0 0 * γ 1 0 * a := by ring
      _ = 1 - γ 0 0 * γ 1 0 * a := by rw [hdet]]
  · ring
  · ring
  · linarith [calc -(γ 1 0 * γ 0 1) + (γ 1 0 * a + γ 1 1) * γ 0 0
        = (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) + γ 0 0 * γ 1 0 * a := by ring
      _ = 1 + γ 0 0 * γ 1 0 * a := by rw [hdet]]

private theorem dvd_of_conj_zpowers_T_pow {a b : ℕ} {g : ConjAct PSL(2, ℤ)}
    (h : g • Subgroup.zpowers ((T : PSL(2, ℤ)) ^ a) =
      Subgroup.zpowers ((T : PSL(2, ℤ)) ^ b)) : b ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact Nat.dvd_zero b
  obtain ⟨p, rfl⟩ := ConjAct.toConjAct.surjective g
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective p
  have hmem : ((γ * T ^ (a : ℤ) * γ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) ∈
      Subgroup.zpowers ((T : PSL(2, ℤ)) ^ b) := by
    rw [← h]
    exact ⟨(T : PSL(2, ℤ)) ^ a, Subgroup.mem_zpowers _, by
      simp [ConjAct.smul_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, zpow_natCast]⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hpsl : ((γ * T ^ (a : ℤ) * γ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) =
      ((T ^ ((b : ℤ) * k) : SL(2, ℤ)) : PSL(2, ℤ)) := by
    rw [← hk, _root_.zpow_mul, zpow_natCast, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_zpow]
  have hc0 : γ 1 0 = 0 := by
    rcases eq_or_eq_neg_of_pslMk_eq hpsl with hmat | hmat
    · have h10 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 1) 0
      rw [conj_T_zpow_matrix, ModularGroup.coe_T_zpow] at h10
      simp at h10
      exact h10.resolve_right ha
    · have h10 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 1) 0
      rw [conj_T_zpow_matrix, Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow] at h10
      simp at h10
      exact h10.resolve_right ha
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  rw [hc0, mul_zero, sub_zero] at hdet
  have hp2 : γ 0 0 * γ 0 0 = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨h0, _⟩ | ⟨h0, _⟩ <;> simp [h0]
  rcases eq_or_eq_neg_of_pslMk_eq hpsl with hmat | hmat
  · have h01 := congr_fun (congr_fun
      (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 0) 1
    rw [conj_T_zpow_matrix, ModularGroup.coe_T_zpow, hp2, one_mul] at h01
    exact Int.natCast_dvd_natCast.mp ⟨k, by simpa using h01⟩
  · have h00 := congr_fun (congr_fun
      (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 0) 0
    rw [conj_T_zpow_matrix, Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow, hc0] at h00
    simp at h00

/-- At `n = 0` (infinite index), `PSL(2, ℤ)` has infinitely many conjugacy classes of subgroups,
witnessed by the parabolic subgroups `⟨T ^ (m + 1)⟩`. Thus `[NeZero n]` in `finite_ofIndex`,
`finite_subgroups_of_index`, and `finite_orbitRel_quotient_ofIndex` is sharp. -/
theorem infinite_orbitRel_quotient_ofIndex_zero :
    Infinite (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 0)) := by
  refine Infinite.of_injective
    (fun m : ℕ ↦ (Quotient.mk''
      ⟨Subgroup.zpowers ((T : PSL(2, ℤ)) ^ (m + 1)),
        Subgroup.mem_ofIndex.mpr (index_zpowers_T_pow (m + 1))⟩ :
      MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 0)))
    fun i j hij ↦ ?_
  obtain ⟨g, hg⟩ := Quotient.exact' hij
  have hg' : g • Subgroup.zpowers ((T : PSL(2, ℤ)) ^ (j + 1)) =
      Subgroup.zpowers ((T : PSL(2, ℤ)) ^ (i + 1)) := congrArg Subtype.val hg
  have hg'' : g⁻¹ • Subgroup.zpowers ((T : PSL(2, ℤ)) ^ (i + 1)) =
      Subgroup.zpowers ((T : PSL(2, ℤ)) ^ (j + 1)) := by rw [← hg', inv_smul_smul]
  exact Nat.succ_injective <| Nat.dvd_antisymm
    (dvd_of_conj_zpowers_T_pow hg') (dvd_of_conj_zpowers_T_pow hg'')

/-- `PSL(2, ℤ)` has infinitely many infinite-index (`index = 0`) subgroups. -/
theorem infinite_ofIndex_zero : Infinite (Subgroup.ofIndex PSL(2, ℤ) 0) :=
  have := infinite_orbitRel_quotient_ofIndex_zero
  Infinite.of_surjective
    (Quotient.mk'' : Subgroup.ofIndex PSL(2, ℤ) 0 →
      MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 0))
    fun q ↦ Quotient.inductionOn' q fun H ↦ ⟨H, rfl⟩

/-! ### Computable conjugacy-class counts in small indices -/

private noncomputable def modularConnectedIsoClassEquiv :
    {c : ConnectedIsoClass n // ∀ t ∈ c.orbitFinset, t.1.σ0 ^ 3 = 1 ∧ t.1.σ1 ^ 2 = 1} ≃
      modularIsoClasses n :=
  Equiv.ofBijective
    (fun c ↦ ⟨c.1.forget, by
      obtain ⟨t, ht⟩ := ConnectedIsoClass.mk_surjective c.1
      rw [← ht, ConnectedIsoClass.forget_mk, mk_mem_modularIsoClasses_iff]
      exact ⟨t.2, c.2 t (ConnectedIsoClass.mem_orbitFinset.mpr ht)⟩⟩)
    ⟨fun _ _ h ↦ Subtype.ext (ConnectedIsoClass.forget_injective (congrArg Subtype.val h)),
      fun C ↦ by
        obtain ⟨t₀, ⟨ht₀, h0, h1⟩, hC⟩ := C.2
        refine ⟨⟨ConnectedIsoClass.mk ⟨t₀, ht₀⟩, fun t ht ↦ ?_⟩, Subtype.ext ?_⟩
        · obtain ⟨τ, hτ⟩ := ConnectedIsoClass.mk_eq_mk_iff_exists_smul.mp
            (ConnectedIsoClass.mem_orbitFinset.mp ht)
          have hval : (t : PermutationTriple n) = τ • t₀ := by rw [← hτ, ConnectedTriple.coe_smul]
          rw [hval]
          exact ⟨by simp [h0], by simp [h1]⟩
        · dsimp only
          rw [ConnectedIsoClass.forget_mk, hC]⟩

/-- For every `n : ℕ`, `Nat.card` of the conjugacy classes of index-`n` subgroups of `PSL(2, ℤ)`
equals the number of connected degree-`n` isomorphism classes whose orbits satisfy `σ0 ^ 3 = 1` and
`σ1 ^ 2 = 1` (at `n = 0` both sides equal `0`, as the left-hand side is infinite and
`ConnectedIsoClass 0` is empty). -/
theorem natCard_orbitRel_quotient_ofIndex_eq (n : ℕ) :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) n)) =
      ((Finset.univ : Finset (ConnectedIsoClass n)).filter
        fun c ↦ ∀ t ∈ c.orbitFinset, t.1.σ0 ^ 3 = 1 ∧ t.1.σ1 ^ 2 = 1).card := by
  rcases eq_or_ne n 0 with rfl | hn
  · have := infinite_orbitRel_quotient_ofIndex_zero
    have : IsEmpty (ConnectedIsoClass 0) :=
      ⟨fun c ↦ let ⟨t, _⟩ := ConnectedIsoClass.mk_surjective c; t.2.ne_zero rfl⟩
    rw [Nat.card_eq_zero_of_infinite, Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty]
  · have : NeZero n := ⟨hn⟩
    rw [Nat.card_congr modularIsoClassEquiv, Nat.card_congr modularConnectedIsoClassEquiv.symm,
      Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `PSL(2, ℤ)` has `1` conjugacy class of subgroups of index `1`. -/
theorem natCard_conjClasses_index_one :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 1)) =
      1 := by
  rw [natCard_orbitRel_quotient_ofIndex_eq 1]
  decide

/-- `PSL(2, ℤ)` has `1` conjugacy class of subgroups of index `2`. -/
theorem natCard_conjClasses_index_two :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 2)) =
      1 := by
  rw [natCard_orbitRel_quotient_ofIndex_eq 2]
  decide

/-- `PSL(2, ℤ)` has `2` conjugacy classes of subgroups of index `3` (one normal with monodromy `C₃`
and one non-normal `Γ₀(2)`-class with monodromy `S₃`). -/
theorem natCard_conjClasses_index_three :
    Nat.card (MulAction.orbitRel.Quotient (ConjAct PSL(2, ℤ)) (Subgroup.ofIndex PSL(2, ℤ) 3)) =
      2 := by
  rw [natCard_orbitRel_quotient_ofIndex_eq 3]
  decide +kernel

end TauCeti.ModularGroup
