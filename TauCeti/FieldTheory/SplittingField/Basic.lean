/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.Solvable

/-!
# Splitting fields: subfields containing the roots and solvable automorphism groups

A splitting field `L` of `f` over `K` is generated over `K` by the roots of `f`
(Mathlib's `Polynomial.IsSplittingField.adjoin_rootSet`), so a subfield of `L` that contains the
image of `K` and all roots of `f` is all of `L`.

Mathlib states solvability of Galois groups for the chosen splitting field, through `p.Gal`. Any
other splitting field `L` of `p` is isomorphic to it over `K`, so `L ≃ₐ[K] L` is solvable as
soon as `p.Gal` is.

## Main results

* `Polynomial.IsSplittingField.subfield_eq_top`: a subfield of a splitting field containing the
  base field and the roots is everything.
* `Polynomial.IsSplittingField.ringHom_ext`: ring homomorphisms out of a splitting field are
  determined by their values on the base field and on the roots.
* `Polynomial.isSolvable_of_isSplittingField`: the automorphism group of a splitting field of `p` is
  solvable when `p.Gal` is.
-/

public section

open Polynomial

namespace Polynomial.IsSplittingField

/-- A subfield of a splitting field containing the base field and the roots is everything. -/
theorem subfield_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (f : K[X])
    [IsSplittingField K L f] {S : Subfield L} (hK : ∀ k, algebraMap K L k ∈ S)
    (hroots : f.rootSet L ⊆ S) : S = ⊤ := by
  -- `S` viewed as a `K`-subalgebra, which has the same elements as `S`.
  let T : Subalgebra K L := { S.toSubsemiring with algebraMap_mem' := hK }
  have hmem (x : L) : x ∈ T ↔ x ∈ S := by
    rw [Subalgebra.mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring]
  have hT : Algebra.adjoin K (f.rootSet L) ≤ T :=
    Algebra.adjoin_le fun x hx ↦ (hmem x).2 (hroots hx)
  rw [IsSplittingField.adjoin_rootSet] at hT
  exact eq_top_iff.2 fun x _ ↦ (hmem x).1 (hT (Algebra.mem_top (x := x)))

/-- Two ring homomorphisms out of a splitting field that agree on the base field and on the roots
are equal. -/
theorem ringHom_ext {K L M : Type*} [Field K] [Field L] [Semiring M] [Algebra K L] (f : K[X])
    [IsSplittingField K L f] {g₁ g₂ : L →+* M}
    (hK : ∀ k, g₁ (algebraMap K L k) = g₂ (algebraMap K L k))
    (hroots : ∀ x ∈ f.rootSet L, g₁ x = g₂ x) : g₁ = g₂ :=
  RingHom.eq_of_eqOn_subfield_top fun x _ ↦ RingHom.mem_eqLocusField.1 <|
    eq_top_iff.1 (subfield_eq_top f (S := g₁.eqLocusField g₂)
      (fun k ↦ RingHom.mem_eqLocusField.2 (hK k))
      (fun x hx ↦ RingHom.mem_eqLocusField.2 (hroots x hx))) (Subfield.mem_top x)

end Polynomial.IsSplittingField

namespace Polynomial

/-- The automorphism group of a splitting field of `p` is solvable if `p.Gal` is. -/
theorem isSolvable_of_isSplittingField {F L : Type*} [Field F] [Field L] [Algebra F L]
    (p : F[X]) [IsSplittingField F L p] (h : Group.IsSolvable p.Gal) :
    Group.IsSolvable (L ≃ₐ[F] L) :=
  -- `p.Gal` is by definition `p.SplittingField ≃ₐ[F] p.SplittingField`, and its derived group
  -- structure is the one of `AlgEquiv`, so `h` already has the restated type.
  have : Group.IsSolvable (p.SplittingField ≃ₐ[F] p.SplittingField) := h
  Group.isSolvable_of_surjective
    (f := (AlgEquiv.autCongr (IsSplittingField.algEquiv L p)).symm.toMonoidHom)
    (MulEquiv.surjective _)

end Polynomial
