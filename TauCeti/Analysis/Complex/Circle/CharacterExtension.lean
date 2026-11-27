/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Complex.Circle.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Finiteness of circle-valued character extensions

For a fixed circle-valued character on a subgroup `H`, the extensions trivial on `N` are
finite in number when `H ⊔ N` has finite index. Only the *differences* of the extensions
factor through the quotient by its normal closure, so the original character may have infinite
image, as it does for nonzero archimedean weights of Hecke characters.
-/

public section

/-- A finite group has only finitely many circle-valued homomorphisms, since each value is a
root of unity of order dividing the cardinality of the group. -/
instance Circle.instFiniteMonoidHom {G : Type*} [Group G] [Finite G] : Finite (G →* Circle) := by
  have h := Circle.finite_setOf_pow_eq_one_pi (κ := G) (n := Nat.card G) Nat.card_pos.ne'
  let f : (G →* Circle) → {g : G → Circle | g ^ Nat.card G = 1} := fun ψ ↦
    ⟨ψ, funext fun x ↦ by
      simp only [Pi.pow_apply, Pi.one_apply, ← map_pow, pow_card_eq_one', map_one]⟩
  exact @Finite.of_injective _ _ h.to_subtype f fun _ _ he ↦
    DFunLike.coe_injective (congrArg Subtype.val he)

/-- A prescribed circle-valued character on `H` has finitely many extensions trivial on `N`
if the coset space of `H ⊔ N` is finite. No continuity assumption is needed for finiteness. -/
theorem MonoidHom.finite_setOf_domRestrict_eq_of_finite_quotient {G : Type*} [Group G]
    {H N : Subgroup G} [Finite (G ⧸ (H ⊔ N))] (χ : H →* Circle) :
    {ψ : G →* Circle | ψ.domRestrict H = χ ∧ N ≤ ψ.ker}.Finite := by
  classical
  set S := {ψ : G →* Circle | ψ.domRestrict H = χ ∧ N ≤ ψ.ker}
  by_cases he : S.Nonempty
  · obtain ⟨φ, hφ⟩ := he
    let K := Subgroup.normalClosure (↑(H ⊔ N) : Set G)
    let D := domRestrictHom K Circle
    let : Finite (G ⧸ K) := Finite.of_surjective
      (Subgroup.quotientMapOfLE (show H ⊔ N ≤ K from Subgroup.le_normalClosure))
      (Quotient.ind' fun g ↦ ⟨QuotientGroup.mk g, Subgroup.quotientMapOfLE_apply_mk _ _⟩)
    have hdiff (ψ : S) : K ≤ (ψ.val / φ).ker := by
      have hle : H ⊔ N ≤ (ψ.val / φ).ker := sup_le
        (fun x hx ↦ div_eq_one.mpr (DFunLike.congr_fun (ψ.property.1.trans hφ.1.symm) ⟨x, hx⟩))
        (fun x hx ↦ div_eq_one.mpr ((ψ.property.2 hx).trans (hφ.2 hx).symm))
      exact Subgroup.normalClosure_le_normal hle
    let f : S → D.ker := fun ψ ↦ ⟨ψ.val / φ, domRestrict_eq_one_iff.mpr (hdiff ψ)⟩
    let : Finite D.ker := Finite.of_equiv _ (domRestrictHomKerEquiv Circle K).symm.toEquiv
    exact Set.finite_coe_iff.mp <| Finite.of_injective f fun ψ ψ' hh ↦
      Subtype.ext (div_left_inj.mp (congrArg Subtype.val hh))
  · rw [Set.not_nonempty_iff_eq_empty.mp he]
    exact Set.finite_empty
