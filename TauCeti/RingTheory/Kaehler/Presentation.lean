/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Presentation.Differentials
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Differentials of a presentation whose relations have zero differential

Let `S` be an `R`-algebra presented as a quotient of a polynomial ring `R[Xᵢ]` by relations whose
partial derivatives all vanish in `S`. Then `Ω[S⁄R]` is free on the differentials `dxᵢ` of the
generators: Mathlib's presentation `Algebra.Presentation.differentials` of `Ω[S⁄R]` has no
nonzero relation.

The main example is a quotient by `p`-th powers in characteristic `p`. For a ring `k` of
characteristic `p` and `t : σ → k`, the differentials of `S = k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)` are free on
the `dxᵢ`. For instance, over a field `k` of characteristic `p` such as `𝔽_p(t)`,
`K = k[y] ⧸ (y ^ p - t)` has `Ω[K⁄k] = K dy`, and `X' = k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)` has
`Ω[X'⁄k]` free on `dτ, dy`, so the image `dy` of the generator of `Ω[K⁄k]` does not generate
`Ω[X'⁄k]`; see `TauCeti.Examples.span_D_ne_top_powSubCQuotient`.

## Main declarations

* `Algebra.Presentation.differentialsBasis`: if the partial derivatives of every relation of a
  presentation vanish, the differentials of the generators form a basis of `Ω[S⁄R]`.
* `TauCeti.PowSubCQuotient k p t`: the quotient `k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)`.
* `TauCeti.PowSubCQuotient.nontrivial`: it is nontrivial over a nontrivial ring `k` when `p ≠ 0`.
* `TauCeti.kaehlerDifferentialBasisPowSubC`: the basis `(dxᵢ)` of its differentials in
  characteristic `p`.
-/

public section

open KaehlerDifferential MvPolynomial

namespace Algebra.Presentation

universe w t u v

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S]
  [Algebra R S] (P : Algebra.Presentation R S ι σ)

/-- If the partial derivatives of every relation of a presentation `P` of `S` vanish in `S`, the
differentials of the generators form a basis of `Ω[S⁄R]`. -/
noncomputable def differentialsBasis
    (h : ∀ r i, algebraMap P.Ring S (pderiv i (P.relation r)) = 0) :
    Module.Basis ι S Ω[S⁄R] :=
  have hrel (r : σ) : P.differentialsRelations.relation r = 0 := by
    -- Unfold the relation. Its index type `differentialsRelations.G` is `ι` only by definition,
    -- so `simp [differentialsRelations]` leaves the coordinates over `G`, where
    -- `Finsupp.mapRange_apply` and `mvPolynomialBasis_repr_apply` do not fire.
    change Finsupp.mapRange (algebraMap P.Ring S) (map_zero _)
      ((mvPolynomialBasis R ι).repr (D _ _ (P.relation r))) = (0 : ι →₀ S)
    ext i
    rw [Finsupp.mapRange_apply, mvPolynomialBasis_repr_apply]
    exact h r i
  have hP := P.differentialsSolution_isPresentation
  .ofRepr (LinearEquiv.ofBijective P.differentialsSolution.π
    ⟨by
      rw [← LinearMap.ker_eq_bot, hP.ker_π, Submodule.span_eq_bot]
      rintro _ ⟨r, rfl⟩
      exact hrel r,
    hP.surjective_π⟩).symm

/-- The basis `differentialsBasis` consists of the differentials of the generators. -/
@[simp]
theorem differentialsBasis_apply
    (h : ∀ r i, algebraMap P.Ring S (pderiv i (P.relation r)) = 0) (i : ι) :
    P.differentialsBasis h i = D R S (P.val i) :=
  -- By definition, `Basis.ofRepr e i = e.symm (Finsupp.single i 1)`, and `e.symm` is the
  -- presentation map `π`, which sends `Finsupp.single i 1` to `D R S (P.val i)`. The domain of
  -- `π` is indexed by `differentialsRelations.G`, which is `ι` only by definition, so
  -- `Basis.coe_ofRepr` and `LinearEquiv.ofBijective_apply` cannot be used with `rw` here.
  P.differentialsSolution.π_single i

/-- The coordinates of the differential of a generator in `differentialsBasis`. -/
@[simp]
theorem differentialsBasis_repr_D
    (h : ∀ r i, algebraMap P.Ring S (pderiv i (P.relation r)) = 0) (i : ι) :
    (P.differentialsBasis h).repr (D R S (P.val i)) = Finsupp.single i 1 := by
  rw [← differentialsBasis_apply P h i, Module.Basis.repr_self]

end Algebra.Presentation

namespace TauCeti

section PowSubC

variable (k : Type*) [CommRing k] (p : ℕ) {σ : Type*} (t : σ → k)

/-- The quotient `k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)` of the polynomial ring by the relations `Xᵢ ^ p = tᵢ`. -/
abbrev PowSubCQuotient : Type _ :=
  MvPolynomial σ k ⧸ Ideal.span (Set.range fun i ↦ X i ^ p - C (t i))

variable {k p t} in
/-- Over a nontrivial ring `k`, with `p ≠ 0`, the ring `k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)` is nontrivial: it
maps to an algebraic closure of a residue field of `k`, sending each `Xᵢ` to a `p`-th root of
`tᵢ`. -/
theorem PowSubCQuotient.nontrivial [Nontrivial k] (hp : p ≠ 0) :
    Nontrivial (PowSubCQuotient k p t) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal k
  let := Ideal.Quotient.field m
  let f : k →+* AlgebraicClosure (k ⧸ m) := (algebraMap _ _).comp (Ideal.Quotient.mk m)
  choose r hr using fun i ↦ IsAlgClosed.exists_pow_nat_eq (f (t i)) (Nat.pos_of_ne_zero hp)
  refine (Ideal.Quotient.lift _ (eval₂Hom f r) ?_).domain_nontrivial
  intro a ha
  refine (Ideal.span_le (I := RingHom.ker (eval₂Hom f r))).2 ?_ ha
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, eval₂Hom_X', eval₂Hom_C, hr,
    sub_self]

variable [CharP k p]

/-- The differentials of `k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)` over a ring `k` of characteristic `p` are free on
the differentials `dxᵢ` of the generators. -/
noncomputable def kaehlerDifferentialBasisPowSubC :
    Module.Basis σ (PowSubCQuotient k p t) Ω[PowSubCQuotient k p t⁄k] :=
  (Algebra.Presentation.naive (v := fun i ↦ X i ^ p - C (t i))).differentialsBasis fun r i ↦ by
    simp [CharP.cast_eq_zero]

@[simp]
theorem kaehlerDifferentialBasisPowSubC_apply (i : σ) :
    kaehlerDifferentialBasisPowSubC k p t i =
      D k (PowSubCQuotient k p t) (Ideal.Quotient.mk _ (X i)) := by
  simp [kaehlerDifferentialBasisPowSubC]

/-- The coordinates of the differential `dxᵢ` in `kaehlerDifferentialBasisPowSubC`. -/
@[simp]
theorem kaehlerDifferentialBasisPowSubC_repr_D (i : σ) :
    (kaehlerDifferentialBasisPowSubC k p t).repr
        (D k (PowSubCQuotient k p t) (Ideal.Quotient.mk _ (X i))) = Finsupp.single i 1 := by
  rw [← kaehlerDifferentialBasisPowSubC_apply, Module.Basis.repr_self]

end PowSubC

end TauCeti
