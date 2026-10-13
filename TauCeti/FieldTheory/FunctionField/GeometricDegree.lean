/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn

/-!
# The geometric degree of an extension of function fields

Let `F' / k'` be a finite extension of an algebraic function field `F / k`, so that `k'` is the
constant field upstairs and `k` the constant field downstairs.  The two degrees `[F' : F]` and
`[k' : k]` are related through the **compositum** `F · k'`, formed inside `F'`: the tower
`F ⊆ F·k' ⊆ F'` splits `[F' : F]` as `[F·k' : F] · [F' : F·k']`, and the second factor is the
**geometric degree** `n(F'/F)`, the degree of the extension after the constants have been
absorbed.

When `F` and `k'` are linearly disjoint over `k` this reads `[F' : F] = n(F'/F) · [k' : k]`.  The
hypothesis is carried here in the degree form `[F·k' : F] = [k' : k]`; that equality is equivalent
to linear disjointness when `k' / k` is finite and `k` sits in both `F` and `k'` compatibly with
the two routes into `F'`, and without those provisos it can hold for want of content, both sides
being `0`.  In particular `[k' : k]` divides `[F' : F]`, which is what turns the cross-multiplied
degree identity `[k' : k] · deg (Con D) = [F' : F] · deg D` for the conorm into
`deg (Con D) = n(F'/F) · deg D`.

Linear disjointness is not automatic; it is what an inseparable constant field extension can
destroy.  It does hold whenever `k' / k` is separable and `k` is the exact constant field of `F`;
that is `TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn`, from which the degree
equality is derived here.
Mathlib's predicate `IntermediateField.LinearDisjoint` also supplies the degree equality, through
`TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`.

## Main definitions

* `TauCeti.constantCompositum`: the compositum `F · k'` inside `F'`.
* `TauCeti.geometricDegree`: the geometric degree `n(F'/F) = [F' : F·k']`.

## Main results

* `TauCeti.constantCompositum_eq_top_iff`: an intermediate field into which `k'` maps is generated
  over `F` by the image of `k'` exactly when it is the compositum `F · k'`.
* `TauCeti.finrank_constantCompositum_mul_geometricDegree`: the tower law
  `[F·k' : F] · n(F'/F) = [F' : F]`.
* `TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`:
  `[F' : F] = n(F'/F) · [k' : k]` when adjoining the constants to `F` costs `[k' : k]`, and
  `TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq` for the divisibility it contains.
* `TauCeti.geometricDegree_eq_finrank_of_constantCompositum_eq_bot`: the geometric degree is
  the whole degree as soon as the compositum is trivial, however that is established.
* `TauCeti.geometricDegree_eq_finrank`: the geometric degree is the whole degree when the
  constants of `F'` already lie in `F`.
* `TauCeti.geometricDegree_eq_one_of_constantCompositum_eq_top`: the geometric degree is one when
  `F'` is the compositum `F · k'`.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`: that degree equality holds for a
  separable constant field extension over an exact constant field.
* `TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn` and
  `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`: the stronger
  linear-disjointness and persistence-of-linear-independence statements from which that degree
  equality follows.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`: it also follows from
  `IntermediateField.LinearDisjoint`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6: the degree form `[F·k' : F] = [k' : k]` extracted from Proposition 3.6.1(b) (whose
  own statement, the persistence over `k'` of linear independence over `k`, is
  `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`) is
  `TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`, the geometric degree
  `[F' : F·k']` is the factor appearing in Corollary 3.6.4, and the splitting
  `[F' : F] = n(F'/F) · [k' : k]` is the companion of Proposition 3.6.6.  Section III.1
  (Corollary 3.1.14) is the cross-multiplied conorm identity this feeds, in
  `TauCeti.FieldTheory.FunctionField.Divisor.Conorm`.

-/

public section

open IntermediateField TauCeti.IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {F : Type v} {k' : Type u'} {F' : Type v'}
variable [Field F] [Field F']

section Compositum

variable [CommSemiring k'] [Algebra k' F'] [Algebra F F'] (F k' F')

/-- The **compositum** `F · k'` formed inside `F'`: the smallest intermediate field of `F' / F`
containing the image of the commutative semiring `k'` under `algebraMap k' F'`.

In the intended application `k'` is the constant field of the upper function field `F' / k'` and
`F / k` is the lower function field, so `F · k'` is `F` with the constants of `F'` adjoined. -/
def constantCompositum : IntermediateField F F' :=
  IntermediateField.adjoin F (Set.range (algebraMap k' F'))

/-- The image of every element of `k'` lies in the compositum `F · k'`. -/
@[simp]
theorem algebraMap_mem_constantCompositum (c : k') :
    algebraMap k' F' c ∈ constantCompositum F k' F' :=
  IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩

/-
Proved by `(rfl)`, not `rfl`: the body of `constantCompositum` is not `@[expose]`d, so the equation
is definitional only inside this module, and downstream consumers need this lemma to connect the
compositum to `IntermediateField.adjoin`.
-/
/-- The defining equation of the compositum `F · k'`: it is `F` with the image of `k'` in `F'`
adjoined. -/
theorem constantCompositum_def :
    constantCompositum F k' F' = IntermediateField.adjoin F (Set.range (algebraMap k' F')) :=
  (rfl)

/-- The universal property of the compositum `F · k'`: it is the least intermediate field of
`F' / F` containing the image of `k'`. -/
@[simp]
theorem constantCompositum_le_iff {K : IntermediateField F F'} :
    constantCompositum F k' F' ≤ K ↔ ∀ c : k', algebraMap k' F' c ∈ K := by
  simp [constantCompositum_def, IntermediateField.adjoin_le_iff, Set.range_subset_iff]

/-- **The compositum commutes with passing to an intermediate field**: if `k'` maps into an
intermediate field `E` of `F' / F` compatibly with `F'`, the compositum `F · k'` formed inside `E`
is carried by the inclusion `E → F'` onto the compositum formed inside `F'`. -/
theorem map_val_constantCompositum (E : IntermediateField F F') [Algebra k' E]
    [IsScalarTower k' E F'] :
    (constantCompositum F k' E).map E.val = constantCompositum F k' F' := by
  rw [constantCompositum_def, IntermediateField.adjoin_map, ← Set.range_comp,
    constantCompositum_def, IsScalarTower.algebraMap_eq k' E F']
  rfl

/-- **An intermediate field is generated by the image of `k'` exactly when it is `F · k'`**: for
an intermediate field `E` of `F' / F` into which `k'` maps compatibly with `F'`, the compositum
`F · k'` formed inside `E` is all of `E` if and only if `E` is the compositum `F · k'` formed
inside `F'`.  In particular `F · k'` is itself the compositum of `F` and `k'`. -/
theorem constantCompositum_eq_top_iff (E : IntermediateField F F') [Algebra k' E]
    [IsScalarTower k' E F'] :
    constantCompositum F k' E = ⊤ ↔ constantCompositum F k' F' = E := by
  rw [← map_val_constantCompositum F k' F' E, ← (IntermediateField.map_injective E.val).eq_iff,
    ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]

/-- The **geometric degree** `n(F'/F)`: the degree `[F' : F·k']` of `F'` over the compositum
`F · k'`, that is, what remains of `F' / F` once the image of `k'` has been adjoined to `F`.

In the intended application `F' / k'` is a finite extension of the function field `F / k` with
constant field `k'` upstairs, and `n(F'/F)` is the degree of the extension after the constants
have been absorbed.  Under linear disjointness of `F` and `k'` over `k` it is the quotient
`[F' : F] / [k' : k]`; see
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`.  It is the
factor `[F' : F·k']` by which the conorm multiplies degrees in Stichtenoth's Corollary 3.6.4. -/
noncomputable def geometricDegree : ℕ :=
  Module.finrank (constantCompositum F k' F') F'

/-
Proved by `(rfl)`, not `rfl`: the body of `geometricDegree` is not `@[expose]`d, so the equation is
definitional only inside this module, and downstream consumers need this lemma to pin the value.
-/
/-- The defining equation of the geometric degree: `n(F'/F)` is the degree of `F'` over the
compositum `F · k'`. -/
theorem geometricDegree_def :
    geometricDegree F k' F' = Module.finrank (constantCompositum F k' F') F' :=
  (rfl)

/-- The tower law for the compositum: `[F·k' : F] · n(F'/F) = [F' : F]`. -/
theorem finrank_constantCompositum_mul_geometricDegree :
    Module.finrank F (constantCompositum F k' F') * geometricDegree F k' F' =
      Module.finrank F F' := by
  rw [geometricDegree_def]
  exact Module.finrank_mul_finrank ..

/-- The geometric degree of a finite extension is positive. -/
theorem geometricDegree_pos [FiniteDimensional F F'] : 0 < geometricDegree F k' F' := by
  rw [geometricDegree_def]
  exact Module.finrank_pos

/-- **The geometric degree is the whole degree as soon as the compositum is trivial**, that is,
when adjoining the image of `k'` to `F` adds nothing.  `geometricDegree_eq_finrank` is the
special case where `k'` maps to `F'` through `F`. -/
theorem geometricDegree_eq_finrank_of_constantCompositum_eq_bot
    (h : constantCompositum F k' F' = ⊥) :
    geometricDegree F k' F' = Module.finrank F F' := by
  rw [geometricDegree_def, h, IntermediateField.finrank_bot']

/-- **The geometric degree is one when `F'` is the compositum `F · k'`**: nothing is left after
the image of `k'` has been adjoined.  This is the case of a constant field extension: combined
with the conorm degree formula `TauCeti.Divisor.degree_conorm`, it is the ingredient that makes
the conorm along a constant field extension preserve degrees. -/
@[simp]
theorem geometricDegree_eq_one_of_constantCompositum_eq_top
    (h : constantCompositum F k' F' = ⊤) : geometricDegree F k' F' = 1 := by
  rw [geometricDegree_def, h, IntermediateField.finrank_top]

/-! ### When `k'` maps to `F'` through `F` -/

section ConstantsInBase

variable [Algebra k' F] [IsScalarTower k' F F']

/-- **The compositum is `F` itself when `k'` maps to `F'` through `F`**, as when the constants
of `F'` already lie in `F`: there is nothing to adjoin. -/
@[simp]
theorem constantCompositum_eq_bot : constantCompositum F k' F' = ⊥ :=
  le_antisymm ((constantCompositum_le_iff F k' F').2 fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k' F F']
    exact IntermediateField.algebraMap_mem _ _) bot_le

/-- **The geometric degree is the whole degree** when `k'` maps to `F'` through `F`, as when the
constants of `F'` already lie in `F`: `n(F'/F) = [F' : F]`. -/
@[simp]
theorem geometricDegree_eq_finrank : geometricDegree F k' F' = Module.finrank F F' :=
  geometricDegree_eq_finrank_of_constantCompositum_eq_bot F k' F'
    (constantCompositum_eq_bot F k' F')

end ConstantsInBase

end Compositum

/-! ### Generators of the compositum -/

section GeneratedCompositum

variable [Field k] [Field k'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
variable [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] (F k' F')

/-- If a set generates `k'` over `k`, its image generates the compositum over `F`. -/
theorem constantCompositum_eq_adjoin_of_adjoin_eq_top (S : Set k')
    (hS : IntermediateField.adjoin k S = ⊤) :
    constantCompositum F k' F' =
      IntermediateField.adjoin F ((algebraMap k' F') '' S) := by
  have hrange : Set.range (algebraMap k' F') =
      (IntermediateField.adjoin k ((algebraMap k' F') '' S) : IntermediateField k F') := by
    rw [← IsScalarTower.toAlgHom_fieldRange k k' F', AlgHom.fieldRange_eq_map, ← hS,
      IntermediateField.adjoin_map, IsScalarTower.coe_toAlgHom']
  rw [constantCompositum_def, hrange, IntermediateField.adjoin_adjoin_right]

end GeneratedCompositum

/-! ### The degree of `F' / F` when `[F·k' : F]` is known -/

section DegreeForm

variable [Semiring k] [CommSemiring k'] [Module k k'] [Algebra k' F'] [Algebra F F'] (F k' F')

/-- **The degree of `F' / F` in terms of the geometric degree**: for any `k`-module structure on
`k'`, if `[F·k' : F]` equals `Module.finrank k k'`, then
`[F' : F] = n(F'/F) · Module.finrank k k'`.

When `k' / k` is a field extension compatible with `k ⊆ F` inside `F'`, the hypothesis `h` is the
degree form `[F·k' : F] = [k' : k]` of the linear-disjointness condition on `F` and `k'` over
`k`.  It is then supplied by `TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`
from `IntermediateField.LinearDisjoint`, and by
`TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable` for a separable constant field
extension over an exact constant field; it can fail for an inseparable `k' / k`.

This is the companion of Stichtenoth's Proposition 3.6.6, which splits `[F' : F]` the same way. -/
theorem finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank F F' = geometricDegree F k' F' * Module.finrank k k' := by
  rw [← finrank_constantCompositum_mul_geometricDegree F k' F', h, mul_comm]

/-- **`Module.finrank k k'` divides `[F' : F]`** when it equals `[F·k' : F]`, with the geometric
degree as quotient.  For a constant field extension `k' / k` compatible with `k ⊆ F`, the
hypothesis is the degree form of linear disjointness (see
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`), and the
conclusion says `[k' : k]` divides `[F' : F]`. -/
theorem finrank_dvd_finrank_of_finrank_constantCompositum_eq
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank k k' ∣ Module.finrank F F' :=
  ⟨geometricDegree F k' F', by
    rw [finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq F k' F' h,
      mul_comm]⟩

end DegreeForm

/-! ### Linear disjointness from the constant field -/

section LinearDisjoint

variable [Field k] [Field k'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
variable [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] (F k' F')

/-- **Mathlib's linear disjointness implies the degree hypothesis**: if the constants of `F'` and
the lower function field `F` are linearly disjoint over `k` in the sense of
`IntermediateField.LinearDisjoint`, and `k' / k` is algebraic, then adjoining the constants to `F`
costs exactly `[k' : k]`.

This is the bridge from Mathlib's predicate to the degree form `[F·k' : F] = [k' : k]` in which the
hypothesis is carried by
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`,
`TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq` and
`TauCeti.Divisor.degree_conorm`. -/
theorem finrank_constantCompositum_eq_finrank_of_linearDisjoint [Algebra.IsAlgebraic k k']
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  have e := (IsScalarTower.toAlgHom k k' F').equivFieldRange
  have halg : Algebra.IsAlgebraic k (IsScalarTower.toAlgHom k k' F').fieldRange := e.isAlgebraic
  have hrank := H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl halg)
  rw [constantCompositum_def, ← IsScalarTower.toAlgHom_fieldRange k k' F',
    e.toLinearEquiv.finrank_eq]
  exact congrArg Cardinal.toNat hrank

/-- **Adjoining a separable constant field extension to the lower function field preserves
finrank**, provided the constant field downstairs is exact: `[F·k' : F] = [k' : k]`, which for
finite `k' / k` is the degree form of linear disjointness of `F` and `k'` over `k`.

This is the degree consequence of Stichtenoth's Proposition 3.6.1(b); that proposition's own
statement — the persistence over `k'` of linear independence over `k` — is
`TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`.

The statement is over the full compatible tower: `k` embeds in `F` and in `k'`, and the two
routes `k → F → F'` and `k → k' → F'` agree. -/
theorem finrank_constantCompositum_eq_finrank_of_isSeparable (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsSeparable k k'] :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' :=
  finrank_constantCompositum_eq_finrank_of_linearDisjoint F k' F'
    (linearDisjoint_fieldRange_of_isIntegrallyClosedIn hex)

end LinearDisjoint

end TauCeti
