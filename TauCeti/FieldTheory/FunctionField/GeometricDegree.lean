/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.ScalarTower
public import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement
import TauCeti.FieldTheory.IntermediateField.LinearDisjoint
import TauCeti.FieldTheory.IntermediateField.Map

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
equality is derived here.  It also holds for every simple algebraic constant field extension
`k' = k(α)` over an exact constant field — in particular, for every prime-degree extension
regardless of separability — because `minpoly F α = (minpoly k α).map (algebraMap k F)`.
Mathlib's predicate `IntermediateField.LinearDisjoint` also supplies the degree equality, through
`TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`.

The name is justified by extending the constants: if `k'` is relatively algebraically closed in
`F'` and `K / k'` is separable algebraic, for instance an algebraic closure of a perfect `k'`, then
the degree of `F' · K` over `F · K` is again `n(F'/F)`. Over a perfect `k`, with `K` an algebraic
closure of `k`, this is Stichtenoth's splitting `[F' : F] = [F' · K : F · K] · [k' : k]`.

## Main definitions

* `TauCeti.constantCompositum`: the compositum `F · k'` inside `F'`.
* `TauCeti.geometricDegree`: the geometric degree `n(F'/F) = [F' : F·k']`.
* `TauCeti.constantCompositumAlgebra`: the `k'`-algebra structure on `F · k'`, with the scalar
  towers `TauCeti.isScalarTower_constantCompositum` and
  `TauCeti.isScalarTower_base_constantCompositum`.
* `TauCeti.restrictScalarsConstantCompositumEquiv`: the `F`-algebra equivalence
  `(F · L) · N ≃ₐ[F] F · (N.restrictScalars k)`.

## Main results

* `IntermediateField.constantCompositum_toSubfield`: adjoining constants to an intermediate
  field gives the same subfield as adjoining its image to the constants.
* `TauCeti.constantCompositum_adjoin_simple_toSubfield`: extending the constants of `k(t)`
  gives `K(t)` as a subfield of the ambient field.
* `TauCeti.constantCompositum_eq_top_iff`: an intermediate field into which `k'` maps is generated
  over `F` by the image of `k'` exactly when it is the compositum `F · k'`.
* `TauCeti.constantCompositum_bot`: adjoining the bottom intermediate field `⊥` over `k` gives `⊥`.
* `TauCeti.constantCompositum_eq_top_iff_of_range_eq`: the compositum `F · k'` depends only on
  the image of `F` in `F'`.
* `TauCeti.constantCompositum_eq_top_of_eq_top`: if `F' = F · k'`, then `F' = E · k'` for every
  intermediate field `E` of `F' / F`.
* `TauCeti.constantCompositum_le_of_isScalarTower` and
  `TauCeti.constantCompositum_eq_top_of_isScalarTower`: enlarging `k'` to `k''` compatibly with
  `F'` enlarges `F · k'` and preserves `constantCompositum F _ F' = ⊤`.
* `TauCeti.restrictScalars_constantCompositum_eq`,
  `TauCeti.coe_restrictScalarsConstantCompositumEquiv_apply`,
  `TauCeti.coe_restrictScalarsConstantCompositumEquiv_symm_apply`, and
  `TauCeti.restrictScalarsConstantCompositumEquiv_algebraMap`: the tower identity
  `((F · L) · N).restrictScalars F = F · (N.restrictScalars k)` for intermediate fields
  `k ⊆ L ⊆ N ⊆ k'`, together with the coercion and `algebraMap` compatibility of
  `TauCeti.restrictScalarsConstantCompositumEquiv`.
* `TauCeti.constantCompositum_tower_eq_top`: if `F' = F · k'` and `F'' = F' · k''` in a compatible
  square of extensions, then `F'' = F · k''`.
* `TauCeti.constantCompositum_eq_top_of_span_eq_top`: `F'` is the compositum `F · k'` when the
  image of `F` spans `F'` linearly over `k'`.
* `TauCeti.constantCompositum_eq_top_of_adjoin_eq_top`: `F'` is the compositum `F · k'` as soon
  as the image of `F` generates `F'` over a field `k'`.
* `TauCeti.exists_intermediateField_isIntegrallyClosedIn_constantCompositum`: pulling back
  `E · M` along `k'' → F'` produces an intermediate field `M₁` of `k'' / M` that is exact in
  `E · M` whenever `k''` is exact in `F'`.
* `TauCeti.finrank_constantCompositum_mul_geometricDegree`: the tower law
  `[F·k' : F] · n(F'/F) = [F' : F]`.
* `TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`:
  `[F' : F] = n(F'/F) · [k' : k]` when adjoining the constants to `F` costs `[k' : k]`, and
  `TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq` for the divisibility it contains.
* `TauCeti.geometricDegree_eq_finrank_of_constantCompositum_eq_bot`: the geometric degree is
  the whole degree as soon as the compositum is trivial, however that is established.
* `TauCeti.geometricDegree_eq_finrank`: the geometric degree is the whole degree when the
  constants of `F'` already lie in `F`.
* `TauCeti.geometricDegree_eq_one_iff`: the geometric degree is one exactly when `F'` is the
  compositum `F · k'`.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`: that degree equality holds for a
  separable constant field extension over an exact constant field.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_adjoin_simple_eq_top` and
  `TauCeti.finrank_constantCompositum_eq_finrank_of_finrank_prime`: the degree equality
  `[F · k' : F] = [k' : k]` holds over an exact constant field `k ⊆ F` for every simple algebraic
  extension `k' = k(α)`, and in particular for every prime-degree extension `k' / k`.
* `TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn` and
  `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`: the stronger
  linear-disjointness and persistence-of-linear-independence statements from which that degree
  equality follows.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`: it also follows from
  `IntermediateField.LinearDisjoint`, under which `F · M' ≤ F · M` forces `M' ≤ M` for
  subextensions `M`, `M'` of `k' / k`
  (`TauCeti.le_of_constantCompositum_le_of_linearDisjoint`).
* `TauCeti.geometricDegree_eq_relfinrank_adjoin`: the geometric degree is the degree
  `[F' · K : F · K]` after a separable algebraic constant field extension `K / k'`.
* `TauCeti.finrank_eq_relfinrank_adjoin_mul_finrank`: `[F' : F] = [F' · K : F · K] · [k' : k]`
  (Stichtenoth, Proposition 3.6.6).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6: the degree form `[F·k' : F] = [k' : k]` extracted from Proposition 3.6.1(b) (whose
  own statement, the persistence over `k'` of linear independence over `k`, is
  `TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn`) is
  `TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`, the geometric degree
  `[F' : F·k']` is the factor appearing in Corollary 3.6.4, the splitting
  `[F' : F] = n(F'/F) · [k' : k]` is the companion of Proposition 3.6.6, and
  `TauCeti.finrank_eq_relfinrank_adjoin_mul_finrank` is Proposition 3.6.6 itself.  Section III.1
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

/-- **The compositum depends only on the image of the lower field**: if fields `E` and `F` have
the same image in `F'`, then `E · k'` and `F · k'` are the same subfield of `F'`. -/
theorem constantCompositum_toSubfield_eq_of_range_eq {E : Type*} [Field E] [Algebra E F']
    (h : (algebraMap E F').range = (algebraMap F F').range) :
    (constantCompositum E k' F').toSubfield = (constantCompositum F k' F').toSubfield := by
  simp only [constantCompositum_def, adjoin_toSubfield, ← RingHom.coe_range, h]

/-- If fields `E` and `F` have the same image in `F'`, then `F' = E · k'` exactly when
`F' = F · k'`. -/
theorem constantCompositum_eq_top_iff_of_range_eq {E : Type*} [Field E] [Algebra E F']
    (h : (algebraMap E F').range = (algebraMap F F').range) :
    constantCompositum E k' F' = ⊤ ↔ constantCompositum F k' F' = ⊤ := by
  rw [← toSubfield_inj, ← toSubfield_inj, top_toSubfield, top_toSubfield,
    constantCompositum_toSubfield_eq_of_range_eq F k' F' h]

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

/-- **Enlarging the lower field keeps the compositum everything**: if `F' = F · k'`, then
`F' = E · k'` for every intermediate field `E` of `F' / F`, because `E · k'` contains both `F` and
the image of `k'`. -/
theorem constantCompositum_eq_top_of_eq_top (E : IntermediateField F F')
    (h : constantCompositum F k' F' = ⊤) : constantCompositum E k' F' = ⊤ := by
  have hle : constantCompositum F k' F' ≤ (constantCompositum E k' F').restrictScalars F :=
    (constantCompositum_le_iff F k' F').2 fun c ↦ algebraMap_mem_constantCompositum E k' F' c
  rw [h] at hle
  exact eq_top_iff.2 fun z _ ↦ hle IntermediateField.mem_top

variable {F k' F'} in
/-- **Enlarging the constant field enlarges the compositum**: if `k''` receives `k'` compatibly
with `F'`, then `F · k' ≤ F · k''`. -/
theorem constantCompositum_le_of_isScalarTower {k'' : Type*} [CommSemiring k''] [Algebra k' k'']
    [Algebra k'' F'] [IsScalarTower k' k'' F'] :
    constantCompositum F k' F' ≤ constantCompositum F k'' F' :=
  (constantCompositum_le_iff F k' F').2 fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k' k'' F']
    exact algebraMap_mem_constantCompositum F k'' F' (algebraMap k' k'' c)

variable {F k' F'} in
/-- **Enlarging the constant field keeps the compositum everything**: if `F' = F · k'` and `k''`
receives `k'` compatibly with `F'`, then `F' = F · k''`. -/
theorem constantCompositum_eq_top_of_isScalarTower {k'' : Type*} [CommSemiring k''] [Algebra k' k'']
    [Algebra k'' F'] [IsScalarTower k' k'' F'] (h : constantCompositum F k' F' = ⊤) :
    constantCompositum F k'' F' = ⊤ :=
  eq_top_iff.2 (h ▸ constantCompositum_le_of_isScalarTower)

variable {F k' F'} in
/-- **Transitivity of constant composita in a tower**: if `F' = F · k'` and `F'' = F' · k''` in a
compatible square of extensions, then `F'' = F · k''`. -/
theorem constantCompositum_tower_eq_top {k'' F'' : Type*} [CommSemiring k''] [Field F'']
    [Algebra k' k''] [Algebra k' F''] [Algebra k'' F''] [Algebra F F''] [Algebra F' F'']
    [IsScalarTower F F' F''] [IsScalarTower k' F' F''] [IsScalarTower k' k'' F'']
    (h₁ : constantCompositum F k' F' = ⊤) (h₂ : constantCompositum F' k'' F'' = ⊤) :
    constantCompositum F k'' F'' = ⊤ := by
  let M := constantCompositum F k'' F''
  have hF' : ∀ y : F', algebraMap F' F'' y ∈ M := by
    have hle : constantCompositum F k' F' ≤ M.comap (IsScalarTower.toAlgHom F F' F'') :=
      (constantCompositum_le_iff F k' F').mpr fun a ↦ by
        rw [IntermediateField.mem_comap, IsScalarTower.toAlgHom_apply,
          ← IsScalarTower.algebraMap_apply k' F' F'', IsScalarTower.algebraMap_apply k' k'' F'']
        exact algebraMap_mem_constantCompositum F k'' F'' (algebraMap k' k'' a)
    exact fun y ↦ hle (h₁ ▸ IntermediateField.mem_top)
  have hle₂ : constantCompositum F' k'' F'' ≤ M.toSubfield.toIntermediateField hF' :=
    (constantCompositum_le_iff F' k'' F'').mpr fun w ↦
      algebraMap_mem_constantCompositum F k'' F'' w
  rw [h₂] at hle₂
  exact eq_top_iff.mpr fun z _ ↦ hle₂ IntermediateField.mem_top

/-- **The compositum is everything when the image of `F` spans `F'` over `k'`**: if the `k'`-linear
span of the image of `F` is all of `F'`, then `F' = F · k'`, because `F · k'` is closed under
addition and multiplication and contains the images of both `F` and `k'`. -/
theorem constantCompositum_eq_top_of_span_eq_top
    (h : Submodule.span k' (Set.range (algebraMap F F')) = ⊤) :
    constantCompositum F k' F' = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span k' (Set.range (algebraMap F F')) := h ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    exact (constantCompositum F k' F').algebraMap_mem x
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a _ _ hx =>
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem_constantCompositum F k' F' a) hx

/-- The `k'`-algebra structure on the compositum `F · k'` formed inside `F'`, through which `k'`
maps into `F · k'`. It is not an instance: `F · k'` may carry another `k'`-algebra structure, for
instance one through `F` when `k'` is the original constant field. -/
abbrev constantCompositumAlgebra : Algebra k' (constantCompositum F k' F') :=
  ((algebraMap k' F').codRestrict _ (algebraMap_mem_constantCompositum F k' F')).toAlgebra

/-- Through `TauCeti.constantCompositumAlgebra`, the maps `k' → F · k' → F'` form a scalar
tower. -/
theorem isScalarTower_constantCompositum :
    letI := constantCompositumAlgebra F k' F'
    IsScalarTower k' (constantCompositum F k' F') F' :=
  letI := constantCompositumAlgebra F k' F'
  .of_algebraMap_eq fun _ ↦ rfl

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

/-- The geometric degree is positive if the extension over the constant compositum is finite. -/
theorem geometricDegree_pos [FiniteDimensional (constantCompositum F k' F') F'] :
    0 < geometricDegree F k' F' := by
  rw [geometricDegree_def]
  exact Module.finrank_pos

/-- **The geometric degree is the whole degree as soon as the compositum is trivial**, that is,
when adjoining the image of `k'` to `F` adds nothing.  `geometricDegree_eq_finrank` is the
special case where `k'` maps to `F'` through `F`. -/
theorem geometricDegree_eq_finrank_of_constantCompositum_eq_bot
    (h : constantCompositum F k' F' = ⊥) :
    geometricDegree F k' F' = Module.finrank F F' := by
  rw [geometricDegree_def, h, IntermediateField.finrank_bot']

/-- **The geometric degree is one exactly when `F'` is the compositum `F · k'`**: nothing is
left after the image of `k'` has been adjoined. For a constant field extension the compositum
is all of `F'`; combined with the conorm degree formula `TauCeti.Divisor.degree_conorm`, this
makes the conorm preserve degrees. -/
@[simp]
theorem geometricDegree_eq_one_iff :
    geometricDegree F k' F' = 1 ↔ constantCompositum F k' F' = ⊤ := by
  rw [geometricDegree_def, IntermediateField.finrank_eq_one_iff_eq_top]

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

/-- **Adjoining the trivial intermediate field `⊥ : IntermediateField k k'` gives `⊥`**: the
compositum of `F` with `⊥` inside `F'` is `F` itself. -/
@[simp]
theorem constantCompositum_bot [Field k] [Field k'] [Algebra k k'] [Algebra k F] [Algebra k F']
    [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] :
    constantCompositum F (⊥ : IntermediateField k k') F' = ⊥ := by
  refine le_antisymm ((constantCompositum_le_iff F (⊥ : IntermediateField k k') F').2 fun c ↦ ?_)
    bot_le
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 c.property
  rw [IsScalarTower.algebraMap_apply (⊥ : IntermediateField k k') k' F',
    IntermediateField.algebraMap_apply, ← ha, ← IsScalarTower.algebraMap_apply k k' F',
    IsScalarTower.algebraMap_apply k F F']
  exact IntermediateField.algebraMap_mem _ _

/-! ### The compositum of an intermediate field with the constants -/

section IntermediateFieldCompositum

open scoped IntermediateField

variable {K : Type*} [Field k] [Field K]
  [Algebra k K] [Algebra k F] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

omit [Algebra k K] [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
/-- The compositum `C · K` is the same subfield of the ambient field whether it is formed
by adjoining `K` to `C` or by adjoining the image of `C` to `K`. -/
theorem _root_.IntermediateField.constantCompositum_toSubfield (C : IntermediateField k F) :
    (constantCompositum C K F').toSubfield =
      (IntermediateField.adjoin K (Set.range (algebraMap C F'))).toSubfield := by
  rw [constantCompositum_def, IntermediateField.adjoin_toSubfield,
    IntermediateField.adjoin_toSubfield, Set.union_comm]

/-- For a simple parameter field `k(t)`, extending constants gives exactly `K(t)`
as a subfield of the ambient field. -/
theorem constantCompositum_adjoin_simple_toSubfield (x : F) :
    (constantCompositum k⟮x⟯ K F').toSubfield = K⟮algebraMap F F' x⟯.toSubfield := by
  rw [_root_.IntermediateField.constantCompositum_toSubfield,
    IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right]

end IntermediateFieldCompositum

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

/-! ### A compositum generated by the lower field -/

section CompositumOfFields

variable [Field k'] [Algebra k' F'] [Algebra F F'] (F k' F')

/-- **The compositum is everything when `F` generates `F'` over `k'`**: if the image of `F`
generates `F'` as a field over `k'`, then `F' = F · k'`, because `F · k'` is a subfield containing
the images of both `F` and `k'`. -/
theorem constantCompositum_eq_top_of_adjoin_eq_top
    (h : IntermediateField.adjoin k' (Set.range (algebraMap F F')) = ⊤) :
    constantCompositum F k' F' = ⊤ := by
  let L : IntermediateField k' F' := (constantCompositum F k' F').toSubfield.toIntermediateField
    (algebraMap_mem_constantCompositum F k' F')
  have hL : L = ⊤ := eq_top_iff.mpr <| h.symm.le.trans <| IntermediateField.adjoin_le_iff.mpr <|
    Set.range_subset_iff.mpr (constantCompositum F k' F').algebraMap_mem
  exact eq_top_iff.mpr fun x _ ↦ (hL ▸ IntermediateField.mem_top : x ∈ L)

end CompositumOfFields

section Tower

variable [Field k] [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra F F']

/-- **Tower identity for `constantCompositum`**: forming the constant compositum in two steps
`(F · L) · N` gives the same subfield of `F'` as forming `F · N` directly after restricting `N`
to an intermediate field over `k`. -/
@[simp]
theorem restrictScalars_constantCompositum_eq (L : IntermediateField k k')
    (N : IntermediateField L k') :
    (constantCompositum (constantCompositum F L F') N F').restrictScalars F =
      constantCompositum F (N.restrictScalars k) F' := by
  let FL := constantCompositum F L F'
  have hFL : FL ≤ constantCompositum F (N.restrictScalars k) F' :=
    (constantCompositum_le_iff F L F').2 fun c ↦ by
      rw [IsScalarTower.algebraMap_apply L k' F']
      exact algebraMap_mem_constantCompositum F (N.restrictScalars k) F' ⟨c.val, N.algebraMap_mem c⟩
  refine le_antisymm ((IntermediateField.le_extendScalars_iff hFL _).1
    ((constantCompositum_le_iff FL N F').2 fun c ↦ ?_))
    ((constantCompositum_le_iff F (N.restrictScalars k) F').2 fun c ↦ ?_)
  · rw [IntermediateField.mem_extendScalars, IsScalarTower.algebraMap_apply N k' F']
    exact algebraMap_mem_constantCompositum F (N.restrictScalars k) F' ⟨c.val, c.property⟩
  · rw [IntermediateField.mem_restrictScalars,
      IsScalarTower.algebraMap_apply (N.restrictScalars k) k' F']
    exact algebraMap_mem_constantCompositum FL N F' ⟨c.val, c.property⟩

section
variable (F F')

/-- The `F`-algebra equivalence `(F · L) · N ≃ₐ[F] F · (N.restrictScalars k)` behind
`TauCeti.restrictScalars_constantCompositum_eq`. -/
def restrictScalarsConstantCompositumEquiv (L : IntermediateField k k')
    (N : IntermediateField L k') :
    constantCompositum (constantCompositum F L F') N F' ≃ₐ[F]
      constantCompositum F (N.restrictScalars k) F' :=
  (IntermediateField.restrictScalarsAlgEquiv F _).symm.trans
    (IntermediateField.equivOfEq (restrictScalars_constantCompositum_eq L N))

/-- Coercion of `restrictScalarsConstantCompositumEquiv` to `F'` is the identity. -/
@[simp]
theorem coe_restrictScalarsConstantCompositumEquiv_apply (L : IntermediateField k k')
    (N : IntermediateField L k') (x : constantCompositum (constantCompositum F L F') N F') :
    (restrictScalarsConstantCompositumEquiv F F' L N x : F') = x := by
  simp [restrictScalarsConstantCompositumEquiv]

/-- Coercion of `(restrictScalarsConstantCompositumEquiv _ _ _ _).symm` to `F'` is the identity. -/
@[simp]
theorem coe_restrictScalarsConstantCompositumEquiv_symm_apply (L : IntermediateField k k')
    (N : IntermediateField L k') (x : constantCompositum F (N.restrictScalars k) F') :
    ((restrictScalarsConstantCompositumEquiv F F' L N).symm x : F') = x := by
  simp [restrictScalarsConstantCompositumEquiv]

/-- Compatibility of `restrictScalarsConstantCompositumEquiv` with the constant-field embeddings
`N → (F · L) · N` and `N.restrictScalars k → F · (N.restrictScalars k)`. -/
@[simp]
theorem restrictScalarsConstantCompositumEquiv_algebraMap (L : IntermediateField k k')
    (N : IntermediateField L k') (c : N) :
    letI := constantCompositumAlgebra F L F'
    letI := constantCompositumAlgebra (constantCompositum F L F') N F'
    letI := constantCompositumAlgebra F (N.restrictScalars k) F'
    restrictScalarsConstantCompositumEquiv F F' L N
        (algebraMap N (constantCompositum (constantCompositum F L F') N F') c) =
      algebraMap (N.restrictScalars k) (constantCompositum F (N.restrictScalars k) F')
        ((IntermediateField.restrictScalarsAlgEquiv k N).symm c) := by
  let := constantCompositumAlgebra F L F'
  let := constantCompositumAlgebra (constantCompositum F L F') N F'
  let := constantCompositumAlgebra F (N.restrictScalars k) F'
  have := isScalarTower_constantCompositum (constantCompositum F L F') N F'
  have := isScalarTower_constantCompositum F (N.restrictScalars k) F'
  apply Subtype.ext
  rw [coe_restrictScalarsConstantCompositumEquiv_apply, ← IntermediateField.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply N _ F', IsScalarTower.algebraMap_apply N k' F',
    ← IntermediateField.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply (N.restrictScalars k) _ F',
    IsScalarTower.algebraMap_apply (N.restrictScalars k) k' F',
    IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
    IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply]

end

end Tower

/-! ### The constants of the compositum over the original constants -/

section ConstantCompositumAlgebra

variable [CommSemiring k] [CommSemiring k'] [Algebra k k'] [SMul k F] [Algebra k F']
variable [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
variable (k F k' F')

/-- Through `TauCeti.constantCompositumAlgebra`, the maps `k → k' → F · k'` form a scalar
tower. -/
theorem isScalarTower_base_constantCompositum :
    letI := constantCompositumAlgebra F k' F'
    IsScalarTower k k' (constantCompositum F k' F') :=
  letI := constantCompositumAlgebra F k' F'
  .of_algebraMap_eq fun c ↦ Subtype.ext (IsScalarTower.algebraMap_apply k k' F' c)

end ConstantCompositumAlgebra

/-- Cutting out the intersection `(E · M) ∩ k''` inside `k''`: when `k''` is exact in `F'`, the
pullback `M₁` of `E · M` along `k'' → F'` sits as an intermediate field of `k'' / M`, acts
compatibly on `E · M`, and is exact in `E · M`. -/
theorem exists_intermediateField_isIntegrallyClosedIn_constantCompositum
    {E M k'' F' : Type*} [Field E] [Field M] [Field k''] [Field F']
    [Algebra M k''] [Algebra M F'] [Algebra k'' F'] [Algebra E F'] [IsScalarTower M k'' F']
    (hex'' : IsIntegrallyClosedIn k'' F') :
    let EM := constantCompositum E M F'
    letI := constantCompositumAlgebra E M F'
    ∃ (M₁ : IntermediateField M k'') (_ : Algebra M₁ EM),
      IsScalarTower M M₁ EM ∧ IsScalarTower M₁ EM F' ∧ IsIntegrallyClosedIn M₁ EM := by
  let EM := constantCompositum E M F'
  let := constantCompositumAlgebra E M F'
  have := isScalarTower_constantCompositum E M F'
  have hm_mem (m : M) : algebraMap M k'' m ∈ (EM.toSubfield).comap (algebraMap k'' F') := by
    rw [Subfield.mem_comap, ← IsScalarTower.algebraMap_apply M k'' F']
    exact algebraMap_mem_constantCompositum E M F' m
  let M₁ : IntermediateField M k'' :=
    ((EM.toSubfield).comap (algebraMap k'' F')).toIntermediateField hm_mem
  have hmEM (c : M₁) : algebraMap M₁ F' c ∈ EM := by
    rw [IsScalarTower.algebraMap_apply M₁ k'' F', IntermediateField.algebraMap_apply]
    exact c.property
  let _ : Algebra M₁ EM := ((algebraMap M₁ F').codRestrict EM hmEM).toAlgebra
  have hstEM : IsScalarTower M₁ EM F' := .of_algebraMap_eq fun c ↦ by
    rw [IntermediateField.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]
  have hstM : IsScalarTower M M₁ EM := .of_algebraMap_eq fun m ↦ (algebraMap EM F').injective <| by
    rw [← IsScalarTower.algebraMap_apply M EM F', ← IsScalarTower.algebraMap_apply M₁ EM F',
      IsScalarTower.algebraMap_apply M₁ k'' F', IntermediateField.algebraMap_apply,
      IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply M k'' F']
  refine ⟨M₁, inferInstance, hstM, hstEM,
    isIntegrallyClosedIn_iff.2 ⟨(algebraMap M₁ EM).injective, fun {y} hy ↦ ?_⟩⟩
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.1
    ((hy.map (IsScalarTower.toAlgHom M₁ EM F')).tower_top : IsIntegral k'' (y : F'))
  refine ⟨⟨c, show algebraMap k'' F' c ∈ EM from hc.symm ▸ y.property⟩, Subtype.ext ?_⟩
  rw [RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply,
    IsScalarTower.algebraMap_apply M₁ k'' F', IntermediateField.algebraMap_apply]
  exact hc

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
`IntermediateField.LinearDisjoint`, then adjoining the constants to `F` costs exactly `[k' : k]`
(both sides are `0` when `k' / k` is infinite).

This is the bridge from Mathlib's predicate to the degree form `[F·k' : F] = [k' : k]` in which the
hypothesis is carried by
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`,
`TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq` and
`TauCeti.Divisor.degree_conorm`. -/
theorem finrank_constantCompositum_eq_finrank_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  have e := (IsScalarTower.toAlgHom k k' F').equivFieldRange
  by_cases hk : Algebra.IsAlgebraic k k'
  · have halg : Algebra.IsAlgebraic k (IsScalarTower.toAlgHom k k' F').fieldRange :=
      e.isAlgebraic
    have hrank := H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl halg)
    rw [constantCompositum_def, ← IsScalarTower.toAlgHom_fieldRange k k' F',
      e.toLinearEquiv.finrank_eq]
    exact congrArg Cardinal.toNat hrank
  · have hk' : ¬ Module.Finite k k' := fun _ ↦ hk (Algebra.IsAlgebraic.of_finite k k')
    rw [Module.finrank_of_not_finite hk', Module.finrank_of_not_finite]
    intro hfin
    have h2 : Module.rank k (IsScalarTower.toAlgHom k k' F').fieldRange ≤
        Module.rank F (constantCompositum F k' F') := H.rank_left_le_adjoin_rank
    have := Module.rank_lt_aleph0_iff.mp (h2.trans_lt (Module.rank_lt_aleph0_iff.mpr hfin))
    exact hk' (Module.Finite.equiv e.symm.toLinearEquiv)

variable {F k' F'} in
/-- Under linear disjointness, a constant `c ∈ k'` lies in the compositum `F · M` of a
subextension `M` of `k' / k` exactly when it lies in `M`. -/
@[simp]
theorem algebraMap_mem_constantCompositum_iff_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    {M : IntermediateField k k'} {m : k'} :
    algebraMap k' F' m ∈ constantCompositum F M F' ↔ m ∈ M := by
  refine ⟨fun hmF ↦ by_contra fun hmM ↦ ?_,
    fun hm ↦ algebraMap_mem_constantCompositum F M F' ⟨m, hm⟩⟩
  -- `1` and `m` are independent over `M`, hence over `F · M`, which contains `m`.
  have h1m : LinearIndependent M ![(1 : k'), m] :=
    (LinearIndependent.pair_iff' one_ne_zero).2 fun a ha ↦ hmM (by
      rw [← ha, Algebra.smul_def, mul_one]
      exact a.property)
  have hli := H.symm'.linearIndependent_adjoin_algebraMap_comp M h1m
  -- The image of the pair `![1, m]` under `algebraMap k' F'`, computed entrywise.
  have hvec : algebraMap k' F' ∘ ![(1 : k'), m] = ![1, algebraMap k' F' m] := by
    ext i
    fin_cases i <;> simp
  rw [hvec, ← constantCompositum_def] at hli
  exact (LinearIndependent.pair_iff' one_ne_zero).1 hli ⟨_, hmF⟩ (by
    rw [Algebra.smul_def, mul_one]
    rfl)

variable {F k' F'} in
/-- Under linear disjointness, `F · M' ≤ F · M` forces `M' ≤ M` for subextensions `M`, `M'` of
`k' / k`. -/
theorem le_of_constantCompositum_le_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    {M M' : IntermediateField k k'}
    (hle : constantCompositum F M' F' ≤ constantCompositum F M F') : M' ≤ M := fun m hm ↦
  (algebraMap_mem_constantCompositum_iff_of_linearDisjoint H).1
    (hle (algebraMap_mem_constantCompositum F M' F' ⟨m, hm⟩))

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

open scoped IntermediateField in
/-- **Adjoining a simple algebraic constant extension to an exact constant field preserves
finrank**: if `k` is relatively algebraically closed in `F` and `k' = k⟮α⟯` for an element
`α : k'` integral over `k` (with no separability hypothesis), then `[F · k' : F] = [k' : k]`. -/
theorem finrank_constantCompositum_eq_finrank_of_adjoin_simple_eq_top
    (hex : IsIntegrallyClosedIn k F) {α : k'} (hα_int : IsIntegral k α) (hα : k⟮α⟯ = ⊤) :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  have hFα : constantCompositum F k' F' = F⟮algebraMap k' F' α⟯ := by
    rw [constantCompositum_eq_adjoin_of_adjoin_eq_top F k' F' ({α} : Set k') hα,
      Set.image_singleton]
  have hkα : k⟮algebraMap k' F' α⟯ = (IsScalarTower.toAlgHom k k' F').fieldRange := by
    rw [AlgHom.fieldRange_eq_map, ← hα, IntermediateField.adjoin_map, Set.image_singleton,
      IsScalarTower.coe_toAlgHom']
  calc Module.finrank F (constantCompositum F k' F')
      = Module.finrank F F⟮algebraMap k' F' α⟯ := by rw [hFα]
    _ = Module.finrank k k⟮algebraMap k' F' α⟯ :=
        IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn
          hex (hα_int.map (IsScalarTower.toAlgHom k k' F'))
    _ = Module.finrank k k' := by
        rw [hkα]
        exact
          (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k k' F')).symm.toLinearEquiv.finrank_eq

/-- **Adjoining a prime-degree constant extension to an exact constant field preserves finrank**:
if `k` is relatively algebraically closed in `F` and `[k' : k]` is prime (with no separability or
characteristic hypothesis), then `[F · k' : F] = [k' : k]`. -/
theorem finrank_constantCompositum_eq_finrank_of_finrank_prime
    (hex : IsIntegrallyClosedIn k F) (hp : (Module.finrank k k').Prime) :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  have : FiniteDimensional k k' := Module.finite_of_finrank_pos hp.pos
  obtain ⟨α, hα⟩ := Field.exists_adjoin_simple_eq_top_of_finrank_prime hp
  exact finrank_constantCompositum_eq_finrank_of_adjoin_simple_eq_top F k' F' hex
    (Algebra.IsIntegral.isIntegral α) hα

end LinearDisjoint

/-! ### The geometric degree after extending the constants -/

section ConstantExtension

variable [Field k'] [Algebra k' F'] [Algebra F F'] (F k' F')
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω]
variable [Algebra k' Ω] [IsScalarTower k' F' Ω]

/-- **The geometric degree survives a separable constant field extension.** Let `k'` be
relatively algebraically closed in `F'`, and let `K` be a separable algebraic extension of `k'`
inside a common overfield `Ω` of `F'` and `K`. Then the degree of `F' · K` over `F · K` is the
geometric degree `n(F'/F) = [F' : F·k']`.

For a perfect `k'` the field `K` can be an algebraic closure of `k'`, and the geometric degree is
the degree `[F' · K : F · K]` of the extension of function fields over the algebraically closed
constant field `K`. -/
theorem geometricDegree_eq_relfinrank_adjoin (hex' : IsIntegrallyClosedIn k' F')
    (K : IntermediateField k' Ω) [Algebra.IsSeparable k' K] :
    geometricDegree F k' F' = IntermediateField.relfinrank (adjoin F (K : Set Ω))
      ((adjoin F' (K : Set Ω)).restrictScalars F) := by
  let fF : F' →ₐ[F] Ω := IsScalarTower.toAlgHom F F' Ω
  let fk : F' →ₐ[k'] Ω := IsScalarTower.toAlgHom k' F' Ω
  -- the images of `F'` and of `F · k'` in `Ω`, as intermediate fields over `k'`
  let B : IntermediateField k' Ω := fk.fieldRange
  let C : IntermediateField k' Ω := adjoin k' (Set.range (algebraMap F Ω))
  have hCB : C ≤ B := adjoin_le_iff.2 <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap F F' x, (IsScalarTower.algebraMap_apply F F' Ω x).symm⟩
  have hld : K.LinearDisjoint B := by
    have h := linearDisjoint_fieldRange_of_isIntegrallyClosedIn (k' := K) (E := Ω) hex'
    have hKr : (IsScalarTower.toAlgHom k' K Ω).fieldRange = K := by
      ext x
      simp [AlgHom.mem_fieldRange]
    rw [hKr] at h
    rw [linearDisjoint_iff] at h
    rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]
    exact h
  -- both relative degrees only depend on the underlying subfields of `Ω`
  have hKS : ∀ S : Set Ω, Subfield.closure (S ∪ K) = K.toSubfield ⊔ Subfield.closure S := by
    intro S
    rw [Set.union_comm, Subfield.closure_union, ← coe_toSubfield, Subfield.closure_eq]
  have hk' : Subfield.closure (Set.range (algebraMap k' Ω)) ≤ K.toSubfield :=
    Subfield.closure_le.2 fun _ ⟨c, hc⟩ ↦ hc ▸ K.algebraMap_mem c
  have hFK : (adjoin F (K : Set Ω)).toSubfield = (K ⊔ C).toSubfield := by
    simp [C, adjoin_toSubfield, sup_toSubfield, hKS, Subfield.closure_union, ← sup_assoc, hk']
  have hF'K : ((adjoin F' (K : Set Ω)).restrictScalars F).toSubfield = (K ⊔ B).toSubfield := by
    simp [B, fk, adjoin_toSubfield, sup_toSubfield, hKS, ← RingHom.coe_fieldRange]
  have hE : ((constantCompositum F k' F').map fF).toSubfield = C.toSubfield := by
    simp [C, fF, constantCompositum_def, adjoin_map, adjoin_toSubfield, Set.union_comm,
      ← Set.range_comp, ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have htop : ((⊤ : IntermediateField F F').map fF).toSubfield = B.toSubfield := by
    simp [B, fF, fk, ← AlgHom.fieldRange_eq_map]
  rw [geometricDegree_def, ← relfinrank_top_right, ← relfinrank_map_map _ _ fF,
    relfinrank_eq_relfinrank_of_toSubfield_eq hE htop,
    ← K.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint B C hCB hld]
  exact relfinrank_eq_relfinrank_of_toSubfield_eq hFK.symm hF'K.symm

variable [Field k] [Algebra k k'] [Algebra k F] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- **The degree of an extension of function fields splits into a geometric and a constant
part** (Stichtenoth, Proposition 3.6.6): `[F' : F] = [F' · K : F · K] · [k' : k]`.

Here `k` is relatively algebraically closed in `F`, `k'` is relatively algebraically closed in
`F'`, `k' / k` is separable, and `K` is a separable algebraic extension of `k'` inside a common
overfield `Ω`. Stichtenoth takes `k` perfect and `K` an algebraic closure of `k`; over a perfect
`k'` the relative algebraic closure `algebraicClosure k' Ω` is such a `K`. -/
theorem finrank_eq_relfinrank_adjoin_mul_finrank (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsSeparable k k'] (hex' : IsIntegrallyClosedIn k' F') (K : IntermediateField k' Ω)
    [Algebra.IsSeparable k' K] :
    Module.finrank F F' = IntermediateField.relfinrank (adjoin F (K : Set Ω))
      ((adjoin F' (K : Set Ω)).restrictScalars F) * Module.finrank k k' := by
  rw [← geometricDegree_eq_relfinrank_adjoin F k' F' hex' K]
  exact finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq F k' F'
    (finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex)

end ConstantExtension

end TauCeti
