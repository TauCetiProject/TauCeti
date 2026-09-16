/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic

/-!
# The Hecke coset representatives tile a fundamental domain

`HeckeRing.GL2.heckeSlashSum` sums `f ∣[k] aᵥ` over `v : DecompQuotient Γ₂ Γ₁ δ⁻¹`, with
`aᵥ = rightCosetRep D v = δ τᵥ⁻¹`. Everything there lives in `GL (Fin 2) ℚ`, which does **not**
act on `ℍ`, so the statement is made along a homomorphism `φ` into a group that does.

This file shows that the images `φ aᵥ` of those representatives translate a fundamental domain
for `φ(Γ₂)` into one for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`.

**`φ` is a parameter, and is not assumed injective.** The theorem itself assumes only
`MulAction P ℍ`, so nothing here forces any particular element to act trivially; the hypotheses
below are what it actually rests on. Injectivity is replaced by an ambient subgroup `H` that
contains `Γ₁` and receives the conjugate `δ Γ₂ δ⁻¹`, with `ker φ ⊓ H ≤ Γ₁`. Neither `Γ₂ ≤ H` nor
stability of `H` under conjugation by `δ` is required.

Taking `H` to be the determinant-one subgroup does not by itself discharge `hker`: it reduces it to
`ker φ ⊓ H ≤ Γ₁`, which needs **both** that `φ` collapses no more of `H` than `{±1}` and that
`{±1} ≤ Γ₁`. The first is a condition on `φ` — for `ratPosToPSL2R` it is
`eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one` — and the second holds of every `Γ₀(N)`.
The other two hypotheses ask that `Γ₁ ≤ H` and that `δ Γ₂ δ⁻¹ ≤ H`. At the determinant-one
subgroup both hold as soon as `Γ₁` and `Γ₂` have determinant one, since conjugation preserves
determinants — `δ` itself need not have determinant one.

The motivation for allowing a non-injective `φ` comes from the intended instantiation rather than
from the statement. There `P` acts faithfully on `ℍ` and is a quotient of a matrix group by its
scalars, so `φ` must collapse `±1`: were `-I` to survive and act trivially,
`MeasureTheory.IsFundamentalDomain` would be unsatisfiable for any set of positive measure, since
its disjointness is `Pairwise` over group elements.

This is what turns a sum of slashes into a single integral, and the direction matters. Start from
`S`, a fundamental domain for `φ(Γ₂)`: integrating `heckeSlashSum` over `S` gives a sum of terms
`∫_S f ∣ aᵥ`, and moving each `aᵥ` onto the domain turns the sum into one integral over
`⋃ᵥ φ aᵥ • S` — which this theorem shows is a fundamental domain for the intersection
`φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`, a smaller group and hence a larger domain. That single integral is how
the Petersson pairing of a Hecke operator against a form is computed, and hence how its adjoint is
identified.

## Main results

* `HeckeRing.GL2.isFundamentalDomain_iUnion_rightCosetRep_smul`: the tiling.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/AdjointTheory/FDTransport.lean`,
<https://github.com/CBirkbeck/AINTLIB>, commit `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`,
Apache-2.0, Chris Birkbeck), where the same transport is carried out at `PSL` level.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.5.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open MeasureTheory ConjAct Matrix TauCeti UpperHalfPlane DoubleCoset

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- **The images of the Hecke coset representatives tile a fundamental domain.** If `S` is a
fundamental domain for `φ(Γ₂)`, the translates of `S` by the images of the representatives
`aᵥ = rightCosetRep D v = δ τᵥ⁻¹` tile one for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`.

Supply `H` rather than injectivity of `φ`: any subgroup containing `Γ₁`, receiving the conjugate
`δ Γ₂ δ⁻¹`, and meeting `ker φ` inside `Γ₁` — neither `Γ₂ ≤ H` nor conjugation-stability of `H` is
needed. The determinant-one subgroup serves when `φ`
collapses no more of it than `{±1}` and `{±1} ≤ Γ₁` — both hold for `ratPosToPSL2R` over any
`Γ₀(N)`, but neither follows from the statement, which constrains `φ` only through `hker`.

Why injectivity is not the alternative, for that intended instantiation: `P` there acts faithfully
and is a matrix group modulo scalars, so with `-I ∈ Γ₂` an injective `φ` would make `φ (-I)` a
non-identity element of `φ(Γ₂)` acting trivially on `ℍ`, and `hS` could then hold for no set of
positive measure — `MeasureTheory.IsFundamentalDomain` demands a.e.-disjointness over distinct
group elements. Nothing in the statement itself forces this: `MulAction P ℍ` is arbitrary here. -/
theorem isFundamentalDomain_iUnion_rightCosetRep_smul {P : Type*} [Group P] [MulAction P ℍ]
    (φ : GL (Fin 2) ℚ →* P) {H : Subgroup (GL (Fin 2) ℚ)}
    [Countable (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)] {S : Set ℍ} {μ : Measure ℍ}
    (h₂ : Γ₁ ≤ H)
    (hconj : ∀ y ∈ Γ₂, (D.out : GL (Fin 2) ℚ) * y * (D.out : GL (Fin 2) ℚ)⁻¹ ∈ H)
    (hker : φ.ker ⊓ H ≤ Γ₁) (hS : IsFundamentalDomain (Γ₂.map φ : Subgroup P) S μ)
    (hδ : Measure.QuasiMeasurePreserving (fun x : ℍ ↦ (φ (D.out : GL (Fin 2) ℚ))⁻¹ • x) μ μ)
    (hnull : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹,
      NullMeasurableSet ((φ (v.out : GL (Fin 2) ℚ))⁻¹ • S) μ) :
    IsFundamentalDomain (Γ₁.map φ ⊓ toConjAct (φ (D.out : GL (Fin 2) ℚ)) • Γ₂.map φ : Subgroup P)
      (⋃ v, φ (rightCosetRep D v) • S) μ := by
  -- `e` matches the index of Shimura's decomposition of `Γ₁δΓ₂` with that of its image, so the
  -- canonical transversal `τᵥ⁻¹` upstairs maps onto one downstairs
  set e := decompQuotientEquivMapOfKerInfLe φ Γ₂ Γ₁ H (D.out : GL (Fin 2) ℚ)⁻¹
    (map_inv φ _) h₂ (by simpa using hconj) hker with he_def
  set r : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹ → (Γ₂.map φ : Subgroup P) :=
    fun v ↦ (φ.subgroupMap Γ₂ v.out)⁻¹
  have heq : ∀ v, QuotientGroup.mk (r v)⁻¹ = e v := fun v ↦ by
    conv_rhs => rw [he_def, ← v.out_eq, decompQuotientEquivMapOfKerInfLe_mk]
    simp [r]
  simp only [rightCosetRep_def, map_mul, map_inv]
  -- `e` was built with its target supplied as `(φ δ)⁻¹` rather than `φ δ⁻¹`, so it already has
  -- the type asked for and only the underlying function needs transporting
  exact hS.iUnion_mul_smul_of_transversal (φ (D.out : GL (Fin 2) ℚ)) hδ hnull
    (funext heq ▸ e.bijective)

end HeckeRing.GL2
