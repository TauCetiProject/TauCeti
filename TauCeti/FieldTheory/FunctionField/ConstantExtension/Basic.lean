/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.FunctionField.ConstantField

/-!
# Finite extensions of the constant field

A finite extension of constants yields a finite compositum over the original field, and a
separable extension of constants produces a separable compositum.  Exactness of the original
constant field is needed for neither.  The function-field theorem for arbitrary algebraic
extensions of constants is in `ConstantExtension.Algebraic`.

Under the hypotheses that make constant field extensions well behaved — the original constant
field `k` is exact in `F` and `k' / k` is separable — the compositum acquires no new separable
constants: no element of `F · k'` outside `k'` is separable over `k'`.  Perfectness of `k'` upgrades
this to exactness: when `k'` is perfect — for instance when `k` is perfect and `k' / k` is
algebraic — every algebraic element is separable over `k'`, so `k'` is the full field of constants
of `F · k'`.  Perfectness cannot simply be dropped: over an imperfect `k` an inseparable constant
field extension can enlarge the field of constants beyond `k'`.  For instance,
`k = 𝔽_p(t, u)` is exact in `F = k(x, y)` with `y ^ p = t * x ^ p + u`, but for `k' = k(t ^ (1/p))`
the element `y - t ^ (1/p) * x` of `F · k'` is a `p`-th root of `u`, and `u ^ (1/p) ∉ k'`.

Finite extensions of constants with as many elements as desired always exist, realized as
composita inside an algebraic closure of `F`.  Over a finite constant field this is how arguments
that need many constants, such as choosing a vector outside finitely many proper subspaces, are
carried out after a finite constant field extension.

## Main results

* `TauCeti.finiteDimensional_of_constantCompositum_eq_top`: a compositum with finite constants
  is finite over the original field.
* `TauCeti.finiteDimensional_base_of_constantCompositum_eq_top`: conversely, for an exact `k` and
  separable `k' / k`, a compositum finite over the original field has finite constants.
* `TauCeti.isSeparable_of_constantCompositum_eq_top`: the compositum of a separable constant
  field extension is separable over the original field.
* `TauCeti.separableClosure_eq_bot_of_constantCompositum_eq_top`: for a separable constant field
  extension of an exact constant field, `k'` is separably closed in `F · k'`.
* `TauCeti.isIntegrallyClosedIn_of_constantCompositum_eq_top`: for a separable constant field
  extension by a perfect `k'`, in particular over a perfect `k`, `k'` is the exact constant field
  of `F · k'` (Stichtenoth, Proposition 3.6.1(a)).

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Proposition 3.6.1.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A compositum with finite constants is finite over the original field. The ambient field
`F'` is assumed to be precisely the compositum of `F` and `k'`. -/
theorem finiteDimensional_of_constantCompositum_eq_top [FiniteDimensional k k']
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional F F' := by
  let : Algebra.EssFiniteType k k' := inferInstance
  obtain ⟨S, hS⟩ := IntermediateField.fg_top k k'
  have htop : IntermediateField.adjoin F ((algebraMap k' F') '' (S : Set k')) = ⊤ := by
    rw [← constantCompositum_eq_adjoin_of_adjoin_eq_top (F := F) (k' := k')
      (F' := F') S hS]
    exact h
  have hfinite : Finite ((algebraMap k' F') '' (S : Set k')) :=
    S.finite_toSet.image _
  let : Finite ((algebraMap k' F') '' (S : Set k')) := hfinite
  have hi : ∀ x ∈ (algebraMap k' F') '' (S : Set k'), IsIntegral F x := by
    rintro x ⟨c, _, rfl⟩
    exact (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  have := IntermediateField.finiteDimensional_adjoin hi
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- **Finiteness of the compositum detects finiteness of the constants**: if `k` is exact in `F`,
`k' / k` is separable and the compositum `F · k'` is finite over `F`, then `k' / k` is finite.  This
is the converse of `TauCeti.finiteDimensional_of_constantCompositum_eq_top`, by the degree identity
`[F · k' : F] = [k' : k]` of linear disjointness. -/
theorem finiteDimensional_base_of_constantCompositum_eq_top [FiniteDimensional F F']
    [Algebra.IsSeparable k k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) : FiniteDimensional k k' := by
  have hrank := finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex
  rw [h, IntermediateField.finrank_top'] at hrank
  exact Module.finite_of_finrank_pos (hrank ▸ Module.finrank_pos)

/-- A separable extension of the constant field produces a separable compositum over the
original field. -/
theorem isSeparable_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hcomp : constantCompositum F k' F' = ⊤) : Algebra.IsSeparable F F' := by
  rw [← IntermediateField.isSeparable_top]
  rw [← hcomp, constantCompositum_def,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  rintro y ⟨c, rfl⟩
  exact IsSeparable.tower_top F <|
    (Algebra.IsSeparable.isSeparable k c).map (IsScalarTower.toAlgHom k k' F')
      (algebraMap k' F').injective

/-! ### The constant field of the compositum -/

/-- **The enlarged constant field is separably closed in the compositum**: if `k` is the exact
constant field of `F` and `k' / k` is separable algebraic, then every element of `F · k'` that is
separable over `k'` is already a constant of `k'`.

This is Stichtenoth, Proposition 3.6.1(a), with perfectness of `k` replaced by the separability of
the constant in question; `TauCeti.isIntegrallyClosedIn_of_constantCompositum_eq_top` recovers the
statement of record over a perfect `k`. -/
theorem separableClosure_eq_bot_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    separableClosure k' F' = ⊥ := by
  refine eq_bot_iff.2 fun z hz ↦ IntermediateField.mem_bot.2 ?_
  refine mem_range_algebraMap_of_mem_adjoin_of_isSeparable_of_isIntegrallyClosedIn hex ?_
    (mem_separableClosure_iff.1 hz)
  rw [← constantCompositum_def, h]
  exact IntermediateField.mem_top

/-- **The constant field of a constant field extension** (Stichtenoth, Proposition 3.6.1(a)):
if `k` is the exact constant field of `F`, `k' / k` is separable and `k'` is perfect, then the
compositum `F · k'` has exact constant field `k'`.  Stichtenoth's hypotheses — `k` perfect and
`k' / k` algebraic — are the special case in which `Algebra.IsSeparable k k'` is inferred and
`PerfectField k'` is `Algebra.IsAlgebraic.perfectField k`.

Together with `TauCeti.IsFunctionField.of_constantCompositum_eq_top` from
`ConstantExtension.Algebraic`, this makes `F · k' / k'` a function field with exact constant field
for an algebraic `k' / k`, so that its genus, its places and their degrees are the ones the theory
of constant field extensions compares with those of `F / k`. -/
theorem isIntegrallyClosedIn_of_constantCompositum_eq_top [Algebra.IsSeparable k k']
    [PerfectField k'] (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) : IsIntegrallyClosedIn k' F' := by
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.2 fun z hz ↦ IntermediateField.mem_bot.1 ?_
  rw [← separableClosure_eq_bot_of_constantCompositum_eq_top hex h]
  exact PerfectField.separable_of_irreducible (minpoly.irreducible hz.isIntegral)

/-! ### Large finite extensions of constants -/

variable (k F) in
/-- **Large finite constant field extensions exist**: for every `n`, there is a finite extension
`k' / k` with more than `n` elements together with a field `F'`, intermediate between `F` and its
algebraic closure, which is the compositum `F · k'`.  The elements of `k'` are chosen among the
infinitely many elements of the algebraic closure of `k` in that of `F`. -/
theorem exists_finiteDimensional_lt_card_constantCompositum_eq_top (n : ℕ) :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ (n : ℕ∞) < ENat.card k' ∧ constantCompositum F k' F' = ⊤ := by
  classical
  let Ω := AlgebraicClosure F
  let A := algebraicClosure k Ω
  have : IsAlgClosed A := IsAlgClosure.isAlgClosed k
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq A (n + 1)
  -- adjoin the `n + 1` chosen algebraic constants `T` to `F`, and then to `k` inside `F(T)`
  let T : Set Ω := Subtype.val '' (S : Set A)
  let F' := IntermediateField.adjoin F T
  let T' : Set F' := Subtype.val ⁻¹' T
  have hT'T : Subtype.val '' T' = T :=
    Set.image_preimage_eq_of_subset fun x hx ↦ by
      simpa using IntermediateField.subset_adjoin F T hx
  have : Finite T' := (S.finite_toSet.image _).preimage Subtype.val_injective.injOn
  have hint : ∀ x ∈ T', IsIntegral k x := by
    rintro x ⟨a, -, hax⟩
    have hx : IsIntegral k (x : Ω) := by
      rw [← hax]
      exact (mem_algebraicClosure_iff.mp a.2).isIntegral
    exact (isIntegral_algHom_iff (F'.val.restrictScalars k) Subtype.val_injective).mp hx
  refine ⟨F', IntermediateField.adjoin k T', IntermediateField.finiteDimensional_adjoin hint,
    ?_, ?_⟩
  · have hT' : T'.encard = n + 1 := by
      rw [← Subtype.val_injective.injOn.encard_image, hT'T,
        Subtype.val_injective.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard, hS]
      norm_cast
    have hle : T'.encard ≤ ENat.card (IntermediateField.adjoin k T') :=
      (Set.encard_le_encard (IntermediateField.subset_adjoin k T')).trans_eq
        (ENat.card_coe_set_eq _).symm
    rw [hT'] at hle
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle
  · have htop : IntermediateField.adjoin F T' = ⊤ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_adjoin, hT'T, IntermediateField.lift_top]
    rw [eq_top_iff, ← htop, constantCompositum_def]
    refine IntermediateField.adjoin.mono _ _ _ fun x hx ↦ ?_
    exact ⟨⟨x, IntermediateField.subset_adjoin k T' hx⟩, rfl⟩

end TauCeti
