/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent

/-!
# Evaluation of character idempotents at characters

Let `O` be a commutative ring, `H` a finite commutative group, and `χ : H →* Oˣ` a character of `H`
with character idempotent `e_χ = (#H)⁻¹ ∑_{a ∈ H} χ(a)⁻¹ a ∈ O[H]` (`TauCeti.charIdempotent χ`).
This file computes the character evaluations `MonoidHom.charEval` of `e_χ` and of its pushforward
into `O[G]` along a subgroup inclusion `H ≤ G`:

* `MonoidHom.charEval_charIdempotent_self`: when `#H` is a unit in `O`, `χ(e_χ) = 1` over any
  commutative ring `O`.
* `MonoidHom.charEval_charIdempotent_of_ne`: over a domain `O`, `ψ(e_χ) = 0` for `χ ≠ ψ`, without
  assuming `#H` is a unit.
* `MonoidHom.charEval_charIdempotent`: over a domain in which `#H` is a unit,
  `ψ(e_χ) = δ_{χψ}`.
* `MonoidHom.charEval_mapDomainAlgHom_charIdempotent`: for a finite subgroup `H ≤ G` with `#H` a
  unit in the domain `O`, the pushed-forward idempotent `e_χ ∈ O[G]` evaluates to `1` on
  characters extending `χ` and to `0` on all other characters of `G`.
-/

public section

namespace MonoidHom

section CommRing

variable {O H G : Type*} [CommRing O] [CommGroup H] [Fintype H] [CommGroup G]

/-- When `#H` is a unit in `O`, a character `χ` evaluates to `1` on its own character idempotent
`e_χ`. No domain hypothesis on `O` is required. -/
theorem charEval_charIdempotent_self (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) :
    χ.charEval (TauCeti.charIdempotent χ) = 1 := by
  let := Fintype.ofFinite (⊤ : Subgroup H)
  rw [TauCeti.charIdempotent_eq_smul_subgroupCharSum, map_smul,
    MonoidHom.charEval_subgroupCharSum_of_le_ker χ⁻¹ χ ⊤ (fun h _ ↦ by simp [MonoidHom.mem_ker]),
    Subgroup.card_top, smul_eq_mul, Ring.inverse_mul_cancel _ hH]

/-- Over a domain, a character `ψ` vanishes on the character idempotent `e_χ` of any distinct
character `χ ≠ ψ`. No unit hypothesis on `#H` is required. -/
theorem charEval_charIdempotent_of_ne [IsDomain O] {χ ψ : H →* Oˣ} (h : χ ≠ ψ) :
    ψ.charEval (TauCeti.charIdempotent χ) = 0 := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup H)
  rw [TauCeti.charIdempotent_eq_smul_subgroupCharSum, map_smul,
    MonoidHom.charEval_subgroupCharSum_inv_top, ite_eq_right h, smul_zero]

/-- Over a domain in which `#H` is a unit, `e_χ` evaluates to the Kronecker delta at characters of
`H`. -/
theorem charEval_charIdempotent [IsDomain O] [DecidableEq (H →* Oˣ)]
    (hH : IsUnit (Nat.card H : O)) (χ ψ : H →* Oˣ) :
    ψ.charEval (TauCeti.charIdempotent χ) = if χ = ψ then 1 else 0 := by
  split_ifs with h
  · subst h
    exact charEval_charIdempotent_self hH χ
  · exact charEval_charIdempotent_of_ne h

omit [Fintype H] in
/-- For a finite subgroup `H ≤ G` whose order is a unit in the domain `O`, the embedded character
idempotent of `χ : H →* Oˣ` in `O[G]` evaluates to `1` at extensions of `χ` and to `0` at all
other characters of `G`. -/
theorem charEval_mapDomainAlgHom_charIdempotent [IsDomain O] (H : Subgroup G) [Fintype H]
    [DecidableEq (H →* Oˣ)] (hH : IsUnit (Nat.card H : O)) (χ : H →* Oˣ) (ψ : G →* Oˣ) :
    ψ.charEval (MonoidAlgebra.mapDomainAlgHom O O H.subtype (TauCeti.charIdempotent χ)) =
      if ψ.comp H.subtype = χ then 1 else 0 := by
  simp only [MonoidAlgebra.mapDomainAlgHom_apply, charEval_mapDomain,
    charEval_charIdempotent hH, eq_comm]

end CommRing

end MonoidHom
