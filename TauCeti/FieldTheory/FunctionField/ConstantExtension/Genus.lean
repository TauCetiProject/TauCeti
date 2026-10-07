/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.RiemannRoch
public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.DegreeZero

/-!
# The genus under a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of an algebraic function field
`F / k` with exact constant field `k`.  The conorm `Con : Div(F) → Div(F')` preserves degrees,
and — since it also preserves the dimensions of Riemann–Roch spaces — the genus of `F' / k'` is
the genus of `F / k`.  Consequently the conorm carries the canonical class to the canonical class
and is injective on divisor classes.

Exactness of `k'` in `F'` is not needed for the degree and genus identities; it is assumed only
where the canonical class of `F' / k'` is spoken of.

## Main results

* `TauCeti.Divisor.degree_conorm_of_constantCompositum_eq_top`: `deg (Con D) = deg D`.
* `TauCeti.genus_eq_genus_of_constantCompositum_eq_top`: `g(F' / k') = g(F / k)`.
* `TauCeti.conormClassGroup_canonicalClass_of_constantCompositum_eq_top`: the conorm of the
  canonical class is the canonical class.
* `TauCeti.conormClassGroup_injective_of_constantCompositum_eq_top`: the conorm is injective on
  divisor classes.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Theorem 3.6.3(b), (c), (e) and (f).
-/

public section

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable k k']

/-- **The conorm along a constant field extension preserves degrees** (Stichtenoth,
Theorem 3.6.3(c)): for a finite separable constant field extension `F · k' / k'` of `F / k` with
exact constant field `k`, `deg (Con D) = deg D` for every divisor `D` of `F / k`.  No
function-field hypothesis on `F / k` is needed. -/
@[simp]
theorem Divisor.degree_conorm_of_constantCompositum_eq_top
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (D : Divisor k F) :
    Divisor.degree (Divisor.conorm k' F' D) = Divisor.degree D := by
  have := finiteDimensional_base_of_constantCompositum_eq_top hex h
  have := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') h
  rw [Divisor.degree_conorm_of_isSeparable k' F'
    (finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex),
    geometricDegree_eq_one_of_constantCompositum_eq_top F k' F' h, Nat.cast_one, one_mul]

/-- **The genus is unchanged by a finite separable constant field extension** (Stichtenoth,
Theorem 3.6.3(b)): if `k` is the exact constant field of `F`, then `g(F · k' / k') = g(F / k)`.
Exactness of `k'` in `F · k'` is not assumed. -/
theorem genus_eq_genus_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    genus k' F' = genus k F := by
  have := finiteDimensional_base_of_constantCompositum_eq_top hex h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  refine le_antisymm (genus_le fun D' ↦ ?_) (genus_le fun D ↦ ?_)
  · -- bound `D'` by the conorm of a divisor `D` of `F / k` and compare the two Riemann–Roch spaces
    obtain ⟨D, hD⟩ := Divisor.exists_le_conorm (k := k) (F := F) k' F' D'
    have hcomp := Divisor.dim_le_dim_add_degree_sub hF' hD
    have hRiemann := Divisor.degree_add_one_sub_dim_le_genus hF D
    rw [Divisor.dim_conorm hex h hF', Divisor.degree_conorm_of_constantCompositum_eq_top hex h]
      at hcomp
    linarith
  · have hRiemann := Divisor.degree_add_one_sub_dim_le_genus hF' (Divisor.conorm k' F' D)
    rwa [Divisor.dim_conorm hex h hF', Divisor.degree_conorm_of_constantCompositum_eq_top hex h]
      at hRiemann

/-- **The conorm of the canonical class is the canonical class** (Stichtenoth,
Theorem 3.6.3(e)): for a finite separable constant field extension `F · k' / k'` of `F / k` with
exact constant fields `k` and `k'`, the conorm on divisor classes sends the canonical class of
`F / k` to the canonical class of `F · k' / k'`. -/
@[simp]
theorem conormClassGroup_canonicalClass_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k' F')
    (h : constantCompositum F k' F' = ⊤) :
    Divisor.conormClassGroup k' F' hF (hF.of_constantCompositum_eq_top h) (canonicalClass hF hex) =
      canonicalClass (hF.of_constantCompositum_eq_top h) hex' := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  obtain ⟨W, hW⟩ := (Place.orderSystem hF).divisorClass_surjective (canonicalClass hF hex)
  have hW' := (divisorClass_eq_canonicalClass_iff hF hex W).1 hW
  rw [← hW, Divisor.conormClassGroup_divisorClass, divisorClass_eq_canonicalClass_iff hF' hex',
    Divisor.dim_conorm hex h hF', Divisor.degree_conorm_of_constantCompositum_eq_top hex h,
    genus_eq_genus_of_constantCompositum_eq_top hF hex h]
  exact hW'

/-- **The conorm is injective on divisor classes** (Stichtenoth, Theorem 3.6.3(f)): along a finite
separable constant field extension of a function field with exact constant field, two divisors
with the same conorm class lie in the same class; equivalently, a divisor whose conorm is principal
is itself principal. -/
theorem conormClassGroup_injective_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    Function.Injective (Divisor.conormClassGroup k' F' hF (hF.of_constantCompositum_eq_top h)) := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨D, rfl⟩ := (Place.orderSystem hF).divisorClass_surjective c
  rw [Divisor.conormClassGroup_divisorClass, Divisor.divisorClass_eq_zero_iff hF'] at hc
  obtain ⟨z, hz⟩ := hc
  have hdeg : Divisor.degree D = 0 := by
    rw [← Divisor.degree_conorm_of_constantCompositum_eq_top hex h, ← hz,
      Divisor.degree_principal]
  have hdim : 1 ≤ Divisor.dim D := by
    rw [← Divisor.dim_conorm hex h hF']
    exact (Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hF' (by
      rw [Divisor.degree_conorm_of_constantCompositum_eq_top hex h, hdeg])).2 ⟨z, hz⟩
  exact (Divisor.divisorClass_eq_zero_iff hF).2
    ((Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hF hdeg).1 hdim)

end TauCeti
