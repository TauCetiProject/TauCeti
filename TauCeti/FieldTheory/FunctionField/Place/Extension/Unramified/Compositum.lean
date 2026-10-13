/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
public import Mathlib.FieldTheory.Normal.Closure

/-!
# Unramified places in composita and Galois closures

Let `F' / F` be a finite separable extension of function fields and `P` a place of `F`. If `P`
is unramified in two intermediate fields `E₁` and `E₂`, meaning that every place above `P` has
ramification index one and separable residue extension, then `P` is unramified in the
compositum `E₁ E₂`. If `F' / F` is Galois, the same holds for the normal closure of an
intermediate field. This is Stichtenoth, Corollary 3.9.3.

The proof is Galois-theoretic and needs no perfectness. In a finite Galois extension, the
restriction of a place `Q` to an intermediate field `E` is unramified exactly when `E` lies in
the inertia field of `Q` (`TauCeti.Place.le_inertiaField_iff`). So `P` is unramified in `E`
exactly when `E` lies in the inertia field of every place above `P`, and this condition passes
to suprema of intermediate fields. A normal closure is the supremum of the conjugates of `E`, in
which `P` is unramified because they are isomorphic to `E` over `F`. A finite separable
extension is first embedded into a finite Galois extension.

## Main results

* `TauCeti.Place.isUnramified_restrict_sup_iff_of_isGalois`: in a finite Galois extension, the
  restriction of a place to `E₁ E₂` is unramified exactly when its restrictions to `E₁` and to
  `E₂` are.
* `TauCeti.Place.forall_isUnramified_iff_forall_le_inertiaField`: in a finite Galois extension,
  a place is unramified in an intermediate field exactly when that field lies in the inertia
  field of every place above it.
* `TauCeti.Place.forall_isUnramified_sup_iff`: **a place is unramified in a compositum exactly
  when it is unramified in both constituents**, for intermediate fields of any finite separable
  extension.
* `TauCeti.Place.forall_isUnramified_normalClosure_iff`: **a place is unramified in the normal
  closure of an intermediate field of a Galois extension exactly when it is unramified in that
  field.**

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.9.3.
-/

public section

namespace TauCeti.Place

universe u v w

variable {k : Type u} {F : Type v} {M : Type w}
variable [Field k] [Field F] [Field M] [Algebra k F] [Algebra k M] [Algebra F M]
variable [IsScalarTower k F M] [FiniteDimensional F M]

section Galois

variable [IsGalois F M]

/-- **Unramifiedness of a place in a compositum, pointwise**: in a finite Galois extension
`M / F`, the restriction of a place `Q` of `M` to the compositum `E₁ E₂` of two intermediate fields
is unramified over `F` exactly when its restrictions to `E₁` and to `E₂` are. -/
theorem isUnramified_restrict_sup_iff_of_isGalois (Q : Place k M) (E₁ E₂ : IntermediateField F M) :
    IsUnramified k F (Q.restrict k ↥(E₁ ⊔ E₂)) ↔
      IsUnramified k F (Q.restrict k E₁) ∧ IsUnramified k F (Q.restrict k E₂) := by
  simp only [← le_inertiaField_iff, sup_le_iff]

/-- **A place is unramified in an intermediate field exactly when that field lies in every inertia
field above it**: in a finite Galois extension `M / F` of function fields, every place of `E`
above `P` is unramified over `F` exactly when `E` lies in the inertia field of every place of `M`
above `P`. -/
theorem forall_isUnramified_iff_forall_le_inertiaField (hF : IsFunctionField k F)
    (P : Place k F) (E : IntermediateField F M) :
    (∀ R : Place k E, R.restrict k F = P → IsUnramified k F R) ↔
      ∀ Q : Place k M, Q.restrict k F = P → E ≤ inertiaField F Q := by
  refine ⟨fun h Q hQ ↦ (le_inertiaField_iff Q E).mpr (h _ ((restrict_restrict Q).trans hQ)),
    fun h R hR ↦ ?_⟩
  -- Every place of `E` is the restriction of a place of `M`.
  obtain ⟨Q, rfl⟩ := restrict_surjective_of_finiteDimensional
    (hF.finite_extension (E := E)) (hF.finite_extension (E := M)) R
  exact (le_inertiaField_iff Q E).mp (h Q ((restrict_restrict Q).symm.trans hR))

/-- In a finite Galois extension, a place is unramified in a compositum exactly when it is
unramified in both constituents. -/
private theorem forall_isUnramified_sup_iff_of_isGalois (hF : IsFunctionField k F)
    (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    (∀ R : Place k ↥(E₁ ⊔ E₂), R.restrict k F = P → IsUnramified k F R) ↔
      (∀ R : Place k E₁, R.restrict k F = P → IsUnramified k F R) ∧
        ∀ R : Place k E₂, R.restrict k F = P → IsUnramified k F R := by
  simp only [forall_isUnramified_iff_forall_le_inertiaField hF P, sup_le_iff, imp_and,
    forall_and]

/-- **Unramifiedness passes to normal closures** (Stichtenoth, Corollary 3.9.3): in a finite
Galois extension `M / F` of function fields, a place `P` of `F` is unramified in the normal
closure of an intermediate field `E` exactly when it is unramified in `E`. -/
theorem forall_isUnramified_normalClosure_iff (hF : IsFunctionField k F) (P : Place k F)
    (E : IntermediateField F M) :
    (∀ R : Place k (IntermediateField.normalClosure F E M), R.restrict k F = P →
        IsUnramified k F R) ↔
      ∀ R : Place k E, R.restrict k F = P → IsUnramified k F R := by
  -- `P` is unramified in each conjugate `f(E)` of `E`, since `f(E) ≅ E` over `F`.
  have hf (f : E →ₐ[F] M) := (forall_isUnramified_iff_of_algEquiv P f.equivFieldRange).trans
    (forall_isUnramified_iff_forall_le_inertiaField hF P f.fieldRange)
  rw [forall_isUnramified_iff_forall_le_inertiaField hF P]
  simp only [normalClosure_le_iff]
  exact ⟨fun h ↦ (hf E.val).mpr fun Q hQ ↦ h Q hQ E.val, fun h Q hQ f ↦ (hf f).mp h Q hQ⟩

end Galois

/-- **Unramifiedness in a compositum** (Stichtenoth, Corollary 3.9.3): for intermediate fields
`E₁` and `E₂` of a finite separable extension `M / F` of function fields, a place `P` of `F` is
unramified in the compositum `E₁ E₂` exactly when it is unramified in `E₁` and in `E₂`.

No perfectness is assumed, but unramifiedness includes separability of the residue extensions,
which cannot be weakened to ramification index one. Over `k = 𝔽_p(a)` and `F = k(t)`, the
Artin–Schreier extensions `y₁ ^ p - y₁ = a / t ^ p` and `y₂ ^ p - y₂ = a (1 + t) / t ^ p` have
ramification index one at the zero of `t`, with purely inseparable residue extension
`k(a ^ (1 / p)) / k`. Their compositum contains `y₂ - y₁`, a root of `T ^ p - T - a / t ^ (p - 1)`,
and so is ramified there. -/
theorem forall_isUnramified_sup_iff [Algebra.IsSeparable F M] (hF : IsFunctionField k F)
    (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    (∀ R : Place k ↥(E₁ ⊔ E₂), R.restrict k F = P → IsUnramified k F R) ↔
      (∀ R : Place k E₁, R.restrict k F = P → IsUnramified k F R) ∧
        ∀ R : Place k E₂, R.restrict k F = P → IsUnramified k F R := by
  -- Embed `M` in its Galois closure `N` inside a separable closure of `F`, then transport the
  -- three intermediate fields along the same embedding.
  let L := separableClosure F (AlgebraicClosure F)
  let N := IntermediateField.normalClosure F M L
  let ι : M →ₐ[F] L := IsSepClosed.lift
  let g : M →ₐ[F] N := ι.codRestrict N.toSubalgebra fun x ↦ ι.fieldRange_le_normalClosure ⟨x, rfl⟩
  rw [forall_isUnramified_iff_of_algEquiv P ((E₁ ⊔ E₂).equivMap g),
    forall_isUnramified_iff_of_algEquiv P (E₁.equivMap g),
    forall_isUnramified_iff_of_algEquiv P (E₂.equivMap g), IntermediateField.map_sup]
  exact forall_isUnramified_sup_iff_of_isGalois hF P _ _

end TauCeti.Place
