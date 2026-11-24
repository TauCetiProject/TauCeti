/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Presentation.Differentials
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPolynomial.Basic

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
`Ω[X'⁄k]`.

## Main declarations

* `Algebra.Presentation.differentialsBasis`: if the partial derivatives of every relation of a
  presentation vanish, the differentials of the generators form a basis of `Ω[S⁄R]`.
* `TauCeti.PowSubCQuotient k p t`: the quotient `k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)`.
* `TauCeti.kaehlerDifferentialBasisPowSubC`: the basis `(dxᵢ)` of its differentials in
  characteristic `p`.
* `TauCeti.span_D_ne_top_powSubCQuotient`: over a domain of characteristic `p ≠ 0`, for
  `k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)`, the single differential `dy` does not span `Ω`.
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
    P.differentialsBasis h i = D R S (P.val i) := by
  exact P.differentialsSolution.π_single i

end Algebra.Presentation

namespace TauCeti

section PowSubC

variable (k : Type*) [CommRing k] (p : ℕ) {σ : Type*} (t : σ → k)

/-- The quotient `k[Xᵢ] ⧸ (Xᵢ ^ p - tᵢ)` of the polynomial ring by the relations `Xᵢ ^ p = tᵢ`. -/
abbrev PowSubCQuotient : Type _ :=
  MvPolynomial σ k ⧸ Ideal.span (Set.range fun i ↦ X i ^ p - C (t i))

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

end PowSubC

/-- Over a domain `k`, with `p ≠ 0`, the ring `k[Xᵢ] ⧸ (Xᵢ ^ p - t)` is nontrivial: it maps to
`k[X] ⧸ (X ^ p - t)` by `Xᵢ ↦ X`. -/
private theorem nontrivial_powSubCQuotient {k : Type*} [CommRing k] [IsDomain k] {p : ℕ}
    (hp : p ≠ 0) (σ : Type*) (t : k) : Nontrivial (PowSubCQuotient k p fun _ : σ ↦ t) := by
  have hdeg : (Polynomial.X ^ p - Polynomial.C t).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact_mod_cast hp
  have := AdjoinRoot.nontrivial (Polynomial.X ^ p - Polynomial.C t) hdeg
  let f : MvPolynomial σ k →ₐ[k] AdjoinRoot (Polynomial.X ^ p - Polynomial.C t) :=
    aeval fun _ ↦ AdjoinRoot.root _
  refine (Ideal.Quotient.lift _ f.toRingHom ?_).domain_nontrivial
  intro a ha
  refine (Ideal.span_le (I := RingHom.ker f.toRingHom)).2 ?_ ha
  rintro _ ⟨i, rfl⟩
  have hroot := AdjoinRoot.eval₂_root (Polynomial.X ^ p - Polynomial.C t)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at hroot
  simpa [f, ← AdjoinRoot.algebraMap_eq] using hroot

/-- **The inseparable base change check.** Over a domain `k` of characteristic `p ≠ 0` and for
`t : k`, the differentials of `X' = k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)` are free on `dτ, dy`
(`kaehlerDifferentialBasisPowSubC`), so the single differential `dy`, the image of the generator
of `Ω[K⁄k]` for `K = k[y] ⧸ (y ^ p - t)`, does not span `Ω[X'⁄k]`. -/
theorem span_D_ne_top_powSubCQuotient {k : Type*} [CommRing k] [IsDomain k] {p : ℕ} [CharP k p]
    (hp : p ≠ 0) (t : k) :
    Submodule.span (PowSubCQuotient k p fun _ : Fin 2 ↦ t)
        {D k (PowSubCQuotient k p fun _ : Fin 2 ↦ t) (Ideal.Quotient.mk _ (X 1))} ≠ ⊤ := by
  have := nontrivial_powSubCQuotient hp (Fin 2) t
  set b := kaehlerDifferentialBasisPowSubC k p fun _ : Fin 2 ↦ t
  intro htop
  have hmem : b 0 ∈ Submodule.span (PowSubCQuotient k p fun _ : Fin 2 ↦ t) {b 1} := by
    rw [kaehlerDifferentialBasisPowSubC_apply k p _ 1]
    exact htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have := congr(b.repr $hc 0)
  simp at this

end TauCeti
