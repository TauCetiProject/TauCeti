/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.Normed.Lp.C0Ideal

/-!
# The bounded product of unital C⋆-algebras

For a family of nonzero unital C⋆-algebras `A i`, the bounded product `lp A ∞` is a unital
C⋆-algebra, `lp.inftyCStarAlgebra`. Mathlib provides the nonunital instance and the unital
commutative one; nontriviality of the factors makes the unit `(1)ᵢ` have norm one.

With the closed `c₀` ideal `lp.c0Ideal` of `TauCeti.Analysis.Normed.Lp.C0Ideal`, the quotient
`lp A ∞ ⧸ lp.c0Ideal A` is then a unital C⋆-algebra by `TwoSidedIdeal.Quotient.cstarAlgebra`.

For a concrete family, such as `A n = CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ`, instance search
does not find the C⋆-structure on `lp A ∞ ⧸ lp.c0Ideal A` within the default limits: matching
the generic quotient instances against the ring structure of `lp A ∞` requires synthesizing the
C⋆-structures of `lp A ∞` and of each `A n` as postponed subproblems, and for `CStarMatrix` over
`ℂ` these nest beyond the allowed depth. The type `lp.QuotientC0 A` is this quotient with its
unital C⋆-algebra structure `lp.QuotientC0.instCStarAlgebra` registered directly, so that instance
search only needs `CStarAlgebra (A i)` and `Nontrivial (A i)`; the structures below it, such as
the norm, the star and the `ℂ`-algebra structure, are its projections.

## Main definitions

* `lp.inftyCStarAlgebra`: the unital C⋆-algebra `lp A ∞`.
* `lp.QuotientC0`: the quotient `lp A ∞ ⧸ lp.c0Ideal A`, a unital C⋆-algebra.
* `lp.QuotientC0.mk`: the quotient map, a unital `⋆`-algebra homomorphism.
* `lp.QuotientC0.lift`: the unital `⋆`-homomorphism out of `lp.QuotientC0 A` induced by one
  vanishing on the `c₀` ideal.
* `lp.QuotientC0.norm_mk`: the quotient norm is the limit superior of the coordinate norms.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open Filter
open scoped ENNReal

namespace lp

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The bounded product `lp A ∞` of nonzero unital C⋆-algebras is a unital C⋆-algebra. -/
noncomputable instance inftyCStarAlgebra : CStarAlgebra (lp A ∞) where

end lp

namespace lp

variable {ι : Type*} (A : ι → Type*) [∀ i, CStarAlgebra (A i)]

/-- The quotient `lp A ∞ ⧸ lp.c0Ideal A` of the bounded product of a family of C⋆-algebras by its
`c₀` ideal. For nonzero unital factors it is a unital C⋆-algebra, `lp.QuotientC0.instCStarAlgebra`,
which instance search finds also for concrete families. -/
@[expose] def QuotientC0 : Type _ :=
  lp A ∞ ⧸ c0Ideal A

namespace QuotientC0

variable [∀ i, Nontrivial (A i)]

/-- The quotient of the bounded product of nonzero unital C⋆-algebras by its `c₀` ideal is a
unital C⋆-algebra. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (QuotientC0 A) :=
  TwoSidedIdeal.Quotient.cstarAlgebra (c0Ideal A)

/-- The quotient map `lp A ∞ →⋆ₐ[ℂ] lp.QuotientC0 A`. -/
noncomputable def mk : lp A ∞ →⋆ₐ[ℂ] QuotientC0 A :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (c0Ideal A)

/-- The quotient map sends `a` to its class in `lp A ∞ ⧸ c0Ideal A`. The lemmas below transfer
the quotient API to `lp.QuotientC0 A` through this equation. -/
theorem mk_apply (a : lp A ∞) :
    mk A a = (TwoSidedIdeal.Quotient.mk (c0Ideal A) a : lp A ∞ ⧸ c0Ideal A) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply (c0Ideal A) a

theorem mk_surjective : Function.Surjective (mk A) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_surjective (c0Ideal A)

variable {A}

@[simp]
theorem mk_eq_zero_iff {a : lp A ∞} : mk A a = 0 ↔ a ∈ c0Ideal A := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.eq_zero_iff_mem

theorem mk_eq_mk_iff {a b : lp A ∞} : mk A a = mk A b ↔ a - b ∈ c0Ideal A := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]

variable (A) in
@[simp]
theorem ker_mk : TwoSidedIdeal.ker (mk A) = c0Ideal A :=
  TwoSidedIdeal.Quotient.ker_mkUnitalStarAlgHom (c0Ideal A)

/-- The norm of `lp.QuotientC0 A` is the limit superior of the coordinate norms along the
cofinite filter. For a finite index type both sides are `0`. -/
theorem norm_mk (a : lp A ∞) :
    ‖mk A a‖ = limsup (fun i ↦ ‖a i‖) cofinite := by
  rw [mk_apply]
  exact norm_mk_c0Ideal a

variable {B : Type*} [CStarAlgebra B]

/-- Descend a unital `⋆`-algebra homomorphism `f : lp A ∞ →⋆ₐ[ℂ] B` vanishing on the `c₀` ideal
to `lp.QuotientC0 A →⋆ₐ[ℂ] B`. -/
noncomputable def lift (f : lp A ∞ →⋆ₐ[ℂ] B) (hf : ∀ a ∈ c0Ideal A, f a = 0) :
    QuotientC0 A →⋆ₐ[ℂ] B :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (c0Ideal A) f hf

@[simp]
theorem lift_mk (f : lp A ∞ →⋆ₐ[ℂ] B) (hf : ∀ a ∈ c0Ideal A, f a = 0) (a : lp A ∞) :
    lift f hf (mk A a) = f a := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_mk (c0Ideal A) f hf a

@[simp]
theorem lift_comp_mk (f : lp A ∞ →⋆ₐ[ℂ] B) (hf : ∀ a ∈ c0Ideal A, f a = 0) :
    (lift f hf).comp (mk A) = f :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_comp_mkUnitalStarAlgHom (c0Ideal A) f hf

/-- Two unital `⋆`-homomorphisms out of `lp.QuotientC0 A` agree when their compositions with
`lp.QuotientC0.mk A` agree. -/
@[ext 1100]
theorem hom_ext ⦃f g : QuotientC0 A →⋆ₐ[ℂ] B⦄ (h : f.comp (mk A) = g.comp (mk A)) : f = g := by
  ext x
  obtain ⟨a, rfl⟩ := mk_surjective A x
  exact DFunLike.congr_fun h a

end QuotientC0

end lp
