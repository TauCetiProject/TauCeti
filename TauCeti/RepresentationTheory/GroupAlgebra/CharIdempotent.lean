/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.RingTheory.Idempotents.Module

/-!
# Character idempotents of a finite group algebra

Let `H` be a finite group, `O` a commutative ring and `χ : H →* Oˣ` a character of `H` with values
in `O`. The **character idempotent** of `χ` is the element

`e_χ = (#H)⁻¹ ∑_{a ∈ H} χ(a)⁻¹ a`

of the group algebra `O[H]`, here `TauCeti.charIdempotent χ`, where `(#H)⁻¹` is
`Ring.inverse (#H)`. It is meaningful when the order of `H` is a unit of `O`, which is the
hypothesis `hH` of every statement below that needs it. A typical instance is `O = ℤ_p` and
`H = μ_{p-1}`, the torsion subgroup of `ℤ_pˣ` for odd `p`: its order `p - 1` is a unit of `ℤ_p`
and its characters take values in `μ_{p-1} ⊂ ℤ_p`.

The element `e_χ` is `(#H)⁻¹` times the character sum `TauCeti.subgroupCharSum` of `χ⁻¹` over the
whole group, so left or right multiplication by a group element `h` scales it by `χ(h)`, and it
squares to itself: when `#H` is a unit by the character sum identity, and otherwise because
`e_χ = 0`. Over a domain the character idempotents of distinct
characters are orthogonal, by row orthogonality of characters (`sum_hom_units_eq_zero`); this part
does not need `#H` to be a unit. For a finite commutative group with enough roots of unity in the
domain `O`, column orthogonality (`CommGroup.sum_monoidHom_apply_eq_ite`) shows that the character
idempotents sum to `1`, so they form a complete orthogonal family of idempotents of `O[H]`.

For a module `M` over `O[H]`, the piece `e_χ M` is the **`χ`-isotypic component**: once `#H` is a
unit, it consists exactly of the vectors on which every `h ∈ H` acts by the scalar `χ(h)`. The
complete orthogonal family then decomposes every `O[H]`-module as the internal direct sum of its
isotypic components, by the Peirce decomposition `TauCeti.isInternal_smul_top`. The components
are submodules over any ring `S` whose action on `M` commutes with that of `O[H]`. For a module over
the Iwasawa algebra of `ℤ_p × H`, taking `S` to be the Iwasawa algebra of `ℤ_p` splits it into
modules over that algebra, one for each character of `H`.

The trivial character gives Mathlib's averaging idempotent `GroupAlgebra.average`. Over an
algebraically closed field, the central idempotents of arbitrary irreducible characters are
`TauCeti.Representation.primitiveCentralIdempotent`; the present file needs no field and no
algebraic closure, only a domain, because the characters here are one-dimensional.

## Main definitions

* `TauCeti.charIdempotent χ`: the character idempotent `(#H)⁻¹ ∑ χ(a)⁻¹ a` in `O[H]`.

## Main results

* `TauCeti.single_mul_charIdempotent`, `TauCeti.charIdempotent_mul_single`: a group element `h`
  acts on `e_χ` by the scalar `χ(h)` from either side.
* `TauCeti.isIdempotentElem_charIdempotent`: `e_χ` is idempotent.
* `TauCeti.charIdempotent_mul_charIdempotent_of_ne`: over a domain, `e_χ e_ψ = 0` for `χ ≠ ψ`.
* `TauCeti.charIdempotent_mul`: `e_χ e_ψ = δ_{χψ} e_χ`.
* `TauCeti.sum_charIdempotent`: for a finite commutative group with enough roots of unity, the
  character idempotents sum to `1`.
* `TauCeti.completeOrthogonalIdempotents_charIdempotent`: they form a complete orthogonal family.
* `TauCeti.mem_charIdempotent_smul_top_iff`: the eigencharacter criterion for the isotypic
  component `e_χ M`.
* `TauCeti.isInternal_charIdempotent_smul_top`: the isotypic decomposition `M = ⨁_χ e_χ M`.

## References

* J. Rodrigues Jacinto, C. Williams, *An introduction to p-adic L-functions*, Lemma 13.4 and
  Definition 13.5.
* J.-P. Serre, *Linear Representations of Finite Groups*, §2.6, Theorem 8.
-/

public section

open MonoidAlgebra
open scoped Pointwise

namespace TauCeti

variable {O H : Type*} [CommRing O]

section Group

variable [Group H] [Fintype H]

open scoped Classical in
/-- The **character idempotent** `e_χ = (#H)⁻¹ ∑_{a ∈ H} χ(a)⁻¹ a` of a character `χ : H →* Oˣ` of a
finite group, an element of the group algebra `O[H]`. The factor `(#H)⁻¹` is `Ring.inverse (#H)`,
so `e_χ` is `0` unless `#H` is a unit of `O`. It is always idempotent
(`TauCeti.isIdempotentElem_charIdempotent`).

It is `(#H)⁻¹` times the character sum `TauCeti.subgroupCharSum` of `χ⁻¹` over the whole group;
`TauCeti.charIdempotent_eq_sum` expands it as a sum over `H`. -/
noncomputable def charIdempotent (χ : H →* Oˣ) : MonoidAlgebra O H :=
  Ring.inverse (Nat.card H : O) • subgroupCharSum ((Units.coeHom O).comp χ⁻¹) ⊤

/-- The character idempotent is `(#H)⁻¹` times the `χ⁻¹`-weighted sum of the group elements. -/
theorem charIdempotent_eq_sum (χ : H →* Oˣ) :
    charIdempotent χ =
      Ring.inverse (Nat.card H : O) • ∑ a : H, (((χ a)⁻¹ : Oˣ) : O) • of O H a := by
  classical
  rw [charIdempotent, subgroupCharSum_eq_sum_of_eq_top _ _ rfl]
  simp

/-- The coefficient of `a` in the character idempotent `e_χ` is `(#H)⁻¹ χ(a)⁻¹`. -/
@[simp]
theorem coeff_charIdempotent (χ : H →* Oˣ) (a : H) :
    (charIdempotent χ).coeff a = Ring.inverse (Nat.card H : O) * (((χ a)⁻¹ : Oˣ) : O) := by
  classical
  simp [charIdempotent]

/-- **Left translation scales a character idempotent by the character**: `h e_χ = χ(h) e_χ`. -/
@[simp]
theorem single_mul_charIdempotent (χ : H →* Oˣ) (h : H) :
    single h (1 : O) * charIdempotent χ = (χ h : O) • charIdempotent χ := by
  classical
  rw [charIdempotent, mul_smul_comm,
    single_mul_subgroupCharSum _ ⊤ ⟨h, Subgroup.mem_top h⟩, smul_comm]
  simp

/-- **Right translation scales a character idempotent by the character**: `e_χ h = χ(h) e_χ`. -/
@[simp]
theorem charIdempotent_mul_single (χ : H →* Oˣ) (h : H) :
    charIdempotent χ * single h (1 : O) = (χ h : O) • charIdempotent χ := by
  classical
  rw [charIdempotent, smul_mul_assoc,
    subgroupCharSum_mul_single _ ⊤ ⟨h, Subgroup.mem_top h⟩, smul_comm]
  simp

/-- **A character idempotent is idempotent.** When the order of the group is not a unit, the
character idempotent is `0`. -/
theorem isIdempotentElem_charIdempotent (χ : H →* Oˣ) :
    IsIdempotentElem (charIdempotent χ) := by
  classical
  by_cases hH : IsUnit (Nat.card H : O)
  swap
  · rw [charIdempotent, Ring.inverse_non_unit _ hH, zero_smul]
    exact .zero
  rw [IsIdempotentElem, charIdempotent, smul_mul_smul_comm, subgroupCharSum_mul_self]
  simp only [Subgroup.card_top, ← Nat.cast_smul_eq_nsmul O, smul_smul, mul_assoc,
    Ring.inverse_mul_cancel _ hH, mul_one]

/-- **Character idempotents of distinct characters are orthogonal** over a domain:
`e_χ e_ψ = 0` for `χ ≠ ψ`. Unlike idempotence, this needs no assumption on the order of `H`. -/
theorem charIdempotent_mul_charIdempotent_of_ne [IsDomain O] {χ ψ : H →* Oˣ} (hχψ : χ ≠ ψ) :
    charIdempotent χ * charIdempotent ψ = 0 := by
  have hsum : ∑ a : H, ((χ a : Oˣ) : O) * (((ψ a)⁻¹ : Oˣ) : O) = 0 := by
    have hne : (Units.coeHom O).comp (χ / ψ) ≠ 1 := fun h ↦ hχψ <| div_eq_one.mp <|
      MonoidHom.ext fun a ↦ Units.ext <| by simpa using DFunLike.congr_fun h a
    simpa [div_eq_mul_inv] using sum_hom_units_eq_zero _ hne
  rw [charIdempotent_eq_sum ψ, mul_smul_comm, Finset.mul_sum]
  simp only [of_apply, mul_smul_comm, charIdempotent_mul_single, smul_smul, ← Finset.sum_smul]
  simp [mul_comm (((ψ _)⁻¹ : Oˣ) : O), hsum]

/-- **Multiplication table of the character idempotents** over a domain:
`e_χ e_ψ = δ_{χψ} e_χ`. -/
theorem charIdempotent_mul [IsDomain O] [DecidableEq (H →* Oˣ)] (χ ψ : H →* Oˣ) :
    charIdempotent χ * charIdempotent ψ = if χ = ψ then charIdempotent χ else 0 := by
  split_ifs with hχψ
  · subst hχψ
    exact isIdempotentElem_charIdempotent χ
  · exact charIdempotent_mul_charIdempotent_of_ne hχψ

/-- Over a domain, the character idempotents form an orthogonal family of idempotents of `O[H]`,
indexed by the characters. -/
theorem orthogonalIdempotents_charIdempotent [IsDomain O] :
    OrthogonalIdempotents (charIdempotent : (H →* Oˣ) → MonoidAlgebra O H) :=
  ⟨isIdempotentElem_charIdempotent, fun _ _ h ↦ charIdempotent_mul_charIdempotent_of_ne h⟩

/-- The character idempotent of the trivial character is Mathlib's averaging idempotent
`GroupAlgebra.average`. -/
theorem charIdempotent_one [Invertible (Fintype.card H : O)] :
    charIdempotent (1 : H →* Oˣ) = GroupAlgebra.average O H := by
  rw [charIdempotent_eq_sum, GroupAlgebra.average, Nat.card_eq_fintype_card,
    Ring.inverse_invertible]
  simp

section Module

variable {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M] [Module O M]
  [Module (MonoidAlgebra O H) M] [IsScalarTower O (MonoidAlgebra O H) M]
  [SMulCommClass (MonoidAlgebra O H) S M]

/-- **The eigencharacter criterion for an isotypic component.** When `#H` is a unit of `O`, a
vector `m` of an `O[H]`-module lies in the `χ`-isotypic component `e_χ M` exactly when every
`h ∈ H` acts on `m` by the scalar `χ(h)`. -/
theorem mem_charIdempotent_smul_top_iff (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) {m : M} :
    m ∈ charIdempotent χ • (⊤ : Submodule S M) ↔ ∀ h : H, single h (1 : O) • m = (χ h : O) • m := by
  constructor
  · intro hm h
    obtain ⟨n, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [smul_smul, single_mul_charIdempotent, smul_assoc]
  · intro hm
    rw [(isIdempotentElem_charIdempotent χ).mem_smul_top_iff_smul_eq_self,
      charIdempotent_eq_sum, smul_assoc, Finset.sum_smul]
    simp only [smul_assoc, of_apply, hm, smul_smul, Units.inv_mul, one_smul, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul O,
      Ring.inverse_mul_cancel _ hH]

end Module

end Group

section CommGroup

variable [IsDomain O] [CommGroup H] [Fintype H]
  [HasEnoughRootsOfUnity O (Monoid.exponent H)]

/-- **The character idempotents sum to `1`**: for a finite commutative group `H` and a domain `O`
with enough roots of unity in which `#H` is a unit, `∑_χ e_χ = 1`. -/
theorem sum_charIdempotent (hH : IsUnit (Nat.card H : O)) :
    ∑ χ : H →* Oˣ, charIdempotent χ = 1 := by
  classical
  -- Column orthogonality: the inverse character values at `a` sum to `#H` or `0`.
  have hcol (a : H) :
      ∑ χ : H →* Oˣ, (((χ a)⁻¹ : Oˣ) : O) = if a = 1 then (Nat.card H : O) else 0 := by
    simp [← map_inv]
  simp_rw [charIdempotent_eq_sum, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hcol, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, smul_smul, Ring.inverse_mul_cancel _ hH, one_smul, of_apply, one_def]

/-- **The character idempotents form a complete orthogonal family of idempotents** of `O[H]`,
for a finite commutative group `H` and a domain `O` with enough roots of unity in which `#H` is a
unit. -/
theorem completeOrthogonalIdempotents_charIdempotent (hH : IsUnit (Nat.card H : O)) :
    CompleteOrthogonalIdempotents (charIdempotent : (H →* Oˣ) → MonoidAlgebra O H) :=
  ⟨orthogonalIdempotents_charIdempotent, sum_charIdempotent hH⟩

/-- **The isotypic decomposition**: for a finite commutative group `H` and a domain `O` with enough
roots of unity in which `#H` is a unit, every `O[H]`-module is the internal direct sum of its
isotypic components `e_χ M`, the component of `m` at `χ` being `e_χ m`
(`TauCeti.coe_ofBijective_coeLinearMap_symm_apply_smul_top`). -/
theorem isInternal_charIdempotent_smul_top {S M : Type*} [Semiring S] [AddCommMonoid M]
    [Module S M] [Module (MonoidAlgebra O H) M] [SMulCommClass (MonoidAlgebra O H) S M]
    [DecidableEq (H →* Oˣ)] (hH : IsUnit (Nat.card H : O)) :
    DirectSum.IsInternal fun χ : H →* Oˣ ↦ charIdempotent χ • (⊤ : Submodule S M) :=
  isInternal_smul_top (completeOrthogonalIdempotents_charIdempotent hH)

end CommGroup

end TauCeti
