/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.NumberTheory.HeckeRing.Basic

/-!
# The Hecke coset representatives tile a fundamental domain

If `S` is a fundamental domain for `φ(Γ₂)`, the translates of `S` by the images of the
representatives `aᵥ = rightCosetRep D v = δ τᵥ⁻¹` tile one for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`.

This is generic: the ambient group `G`, the acting group `P` and the space `α` acted on are all
arbitrary, and no step uses matrices, the upper half-plane, or a slash action. It sits here beside
`rightCosetRep` rather than in the modular-forms layer that consumes it, so a generic consumer need
not import the slash action to reach it.

The statement is made along a homomorphism `φ` because the double cosets frequently live in a group
that does not act on the space of interest. In the motivating instantiation `φ` is
`TauCeti.ratPosToPSL2R`, whose source is the positive-determinant subgroup `GL(2, ℚ)⁺` — that
restriction being forced for the *fractional-linear* action specifically, since a
negative-determinant matrix carries `ℍ` to the lower half-plane.

## Main results

* `DoubleCoset.isFundamentalDomain_iUnion_rightCosetRep_smul`: the tiling.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/AdjointTheory/FDTransport.lean`,
<https://github.com/CBirkbeck/AINTLIB>, commit `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`,
Apache-2.0, Chris Birkbeck). There the transport is carried out at `PSL` level with the source
group fixed at `SL(2, ℤ)`: `Gamma_p_α_FD_finite_index_decomp` (`FDTransport.lean:128`) takes
`φ : SL(2, ℤ) →* G_outer`, so it is generic in the acting group but not in the source. The
statement here is generic in the source group, the acting group and the space acted on alike.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.5.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open MeasureTheory ConjAct Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ₁ Γ₂ : Subgroup G}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- **The images of the Hecke coset representatives tile a fundamental domain.** If `S` is a
fundamental domain for `φ(Γ₂)`, the translates of `S` by the images of the representatives
`aᵥ = rightCosetRep D v = δ τᵥ⁻¹` tile one for `φ(Γ₁) ⊓ φ(δ) φ(Γ₂) φ(δ)⁻¹`.

Supply `H` rather than injectivity of `φ`: any subgroup containing `Γ₁`, receiving the conjugate
`δ Γ₂ δ⁻¹`, and meeting `ker φ` inside `Γ₁` — neither `Γ₂ ≤ H` nor conjugation-stability of `H` is
needed. The determinant-one subgroup serves when `φ` collapses no more of it than `{±1}` and
`{±1} ≤ Γ₁` — both hold for `ratPosToPSL2R` over any `Γ₀(N)`, but neither follows from the
statement, which constrains `φ` only through `hker`.

Why injectivity is not the alternative, for the intended instantiation: `P` there acts faithfully
and is a matrix group modulo scalars, so with `-I ∈ Γ₂` an injective `φ` would make `φ (-I)` a
non-identity element of `φ(Γ₂)` acting trivially, and `hS` could then hold for no set of positive
measure — `MeasureTheory.IsFundamentalDomain` demands a.e.-disjointness over distinct group
elements. Nothing in the statement itself forces this: the action is arbitrary here.

The acted-on space is an arbitrary measurable `α`, not `ℍ`: no hypothesis and no step of the proof
uses upper-half-plane structure, and the tiling lemma underneath
(`MeasureTheory.IsFundamentalDomain.iUnion_mul_smul_of_transversal`) is already stated at that
generality. `ℍ` is simply what the modular-forms consumers instantiate it at. -/
theorem isFundamentalDomain_iUnion_rightCosetRep_smul {P α : Type*} [Group P]
    [MeasurableSpace α] [MulAction P α]
    (φ : G →* P) {H : Subgroup G} [Countable (DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹)] {S : Set α}
    {μ : Measure α} (h₂ : Γ₁ ≤ H) (hconj : ∀ y ∈ Γ₂, (D.out : G) * y * (D.out : G)⁻¹ ∈ H)
    (hker : φ.ker ⊓ H ≤ Γ₁) (hS : IsFundamentalDomain (Γ₂.map φ : Subgroup P) S μ)
    (hδ : Measure.QuasiMeasurePreserving (fun x : α ↦ (φ (D.out : G))⁻¹ • x) μ μ)
    (hnull : ∀ v : DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹,
      NullMeasurableSet ((φ (v.out : G))⁻¹ • S) μ) :
    IsFundamentalDomain (Γ₁.map φ ⊓ toConjAct (φ (D.out : G)) • Γ₂.map φ : Subgroup P)
      (⋃ v, φ (rightCosetRep D v) • S) μ := by
  -- `e` matches the index of Shimura's decomposition of `Γ₁δΓ₂` with that of its image, so the
  -- canonical transversal `τᵥ⁻¹` upstairs maps onto one downstairs
  set e := decompQuotientEquivMapOfKerInfLe φ Γ₂ Γ₁ H (D.out : G)⁻¹ (map_inv φ _) h₂
    (by simpa using hconj) hker with he_def
  set r := fun v : DecompQuotient Γ₂ Γ₁ (D.out : G)⁻¹ ↦ (φ.subgroupMap Γ₂ v.out)⁻¹
  have heq : ∀ v, QuotientGroup.mk (r v)⁻¹ = e v := fun v ↦ by
    conv_rhs => rw [he_def, ← v.out_eq, decompQuotientEquivMapOfKerInfLe_mk]
    simp [r]
  simp only [rightCosetRep_def, map_mul, map_inv]
  -- `e` was built with its target supplied as `(φ δ)⁻¹` rather than `φ δ⁻¹`, so it already has
  -- the type asked for and only the underlying function needs transporting
  exact hS.iUnion_mul_smul_of_transversal (φ (D.out : G)) hδ hnull (funext heq ▸ e.bijective)

end DoubleCoset
