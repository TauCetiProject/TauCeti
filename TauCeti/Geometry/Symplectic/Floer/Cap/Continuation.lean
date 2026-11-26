/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Ring

/-!
# Continuation maps of class-indexed counts are algebra isomorphisms

Let two capped complexes be given as in `TauCeti.Geometry.Symplectic.Floer.Cap.Ring`, for
instance those of two nondegenerate Hamiltonians `H` and `H'` on the same closed symplectic
manifold: finitely many orbits with capped generators, reference caps, actions and gradings obeying
the recapping laws, and for each the counts `D`, `Q`, `E` of rigid Floer cylinders, pairs of pants
and PSS planes satisfying the identities under which `TauCeti.Floer.cohomologyGRingOfCounts` makes
the degree-wise cohomology `⨁ k, H^k` a graded algebra over the ground ring, with product induced
by the pair-of-pants product and unit the class of the PSS cycle.

Continuation cylinders from the orbits of `H` to those of `H'` are counted by generating series
`Φ`, and those in the opposite direction by `Ψ`, all in a common class group `G` mapping to the
period group by an area-preserving homomorphism `q`. The identities given by the ends of the
relevant one-dimensional moduli spaces are:

* `Φ` and `Ψ` are chain maps: `∑ₖ Φᵢₖ D'ₖₗ = ∑ₖ Dᵢₖ Φₖₗ`, and likewise for `Ψ`;
* `Ψ ∘ Φ` and `Φ ∘ Ψ` are homotopic to the identity through counts `Y` and `Y'` of the
  concatenation families, `∑ₖ Φᵢₖ Ψₖₗ - [i = l] = ∑ₘ Yᵢₘ Dₘₗ + ∑ₘ Dᵢₘ Yₘₗ` and its primed form;
* the continuation family of pairs of pants, with counts `K`, gives the homotopy
  `Φ (a ⋆ b) - Φ a ⋆' Φ b = d' K(a, b) + K(d a, b) + (-1)^e K(a, d b)` of
  `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`.

Under these identities and the index conditions of the rigid counts, the maps induced by `Φ` on
cohomology form an isomorphism of algebras over the ground ring
(`TauCeti.Floer.continuationAlgEquivOfCounts`), sending the class of a cocycle `a` to the class of
`Φ a` (`TauCeti.Floer.continuationAlgEquivOfCounts_of_mk`), with inverse induced by `Ψ`
(`TauCeti.Floer.continuationAlgEquivOfCounts_symm_of_mk`). It is the isomorphism
`TauCeti.Floer.algEquivOfCounts` of homotopy-inverse multiplicative counts, with the
multiplicativity on cocycles supplied by the continuation family of pairs of pants. No identity
relating the units is assumed: a multiplicative map onto degree-zero cohomology sends the unit to
the unit (`LinearMap.sub_mem_coboundaries_of_surjective_cohomologyMap`), so continuation sends the
class of the PSS cycle of `H` to that of `H'`.

The count identities, index conditions and potential bounds are the hypotheses that the
compactified moduli spaces are to supply; no moduli space, orientation or count is constructed
here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 12.1, on the pair-of-pants product and its
  compatibility with continuation maps.
-/

public section

noncomputable section

namespace TauCeti.Floer

open _root_.DirectSum NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  [CommRing R] {ι ι' : Type*} [Fintype ι] [Fintype ι'] {P : ι → Type*} {P' : ι' → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P i)] [∀ i', AddTorsor (PeriodGroup ω c) (P' i')]
  (r : ∀ i, P i) (r' : ∀ i', P' i') {F : (Σ i, P i) → ℝ} {F' : (Σ i', P' i') → ℝ}
  (hF : ∀ i γ (D : P i), F ⟨i, γ +ᵥ D⟩ = F ⟨i, D⟩ - (-area ω c) γ)
  (hF' : ∀ i' γ (D : P' i'), F' ⟨i', γ +ᵥ D⟩ = F' ⟨i', D⟩ - (-area ω c) γ)
  {μ : (Σ i, P i) → ℤ} {μ' : (Σ i', P' i') → ℤ}
  (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ ⟨i, D⟩)
  (hμ' : ∀ i' γ (D : P' i'), μ' ⟨i', γ +ᵥ D⟩ = degree ω c γ + μ' ⟨i', D⟩)
  (n : ℤ) (D : ι → ι → NovikovSeries R G ωG) (D' : ι' → ι' → NovikovSeries R G ωG) {C C' : ℝ}
  (hδ : ∀ p p', mapKernelOfMatrix r r (fun i k => coefficientComparison q hq (D i k)) p p' ≠ 0 →
    F p' ≤ F p + C)
  (hδ' : ∀ p p',
    mapKernelOfMatrix r' r' (fun i k => coefficientComparison q hq (D' i k)) p p' ≠ 0 →
      F' p' ≤ F' p + C')
  (Φ : ι → ι' → NovikovSeries R G ωG) (Ψ : ι' → ι → NovikovSeries R G ωG)

section CohomologyRing

variable
  (Q : ι → ι → ι → NovikovSeries R G ωG) (Q' : ι' → ι' → ι' → NovikovSeries R G ωG) {CQ CQ' : ℝ}
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r r r (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
      F p₀ ≤ F p₁ + F p₂ + CQ)
  (hnQ' : ∀ p₁ p₂ p₀,
    kernelOfMatrix r' r' r' (fun i j k => coefficientComparison q hq (Q' i j k)) p₁ p₂ p₀ ≠ 0 →
      F' p₀ ≤ F' p₁ + F' p₂ + CQ')

include hμ hμ' in
/-- **Continuation maps of class-indexed counts are multiplicative on cocycles.** If the
continuation family of pairs of pants, with counts `K` lowering the cochain degree by one, gives
the identity of `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`
between the products `Q` and `Q'` of two complexes and the continuation counts `Φ` on all three
ends, then `Φ (a ⋆ b) - Φ a ⋆' Φ b` is a coboundary for all cocycles `a` and `b`. -/
private theorem countMap_kernelProduct_sub_mem_coboundaries
    (hcont : ∃ K : ι → ι → ι' → NovikovSeries R G ωG,
      (∀ i j l, ∀ A ∈ (K i j l).support,
        μ' ⟨l, r' l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n + 1) ∧
      ∀ i j l, ∑ k, Q i j k * Φ k l - ∑ s, ∑ t, Φ i s * Φ j t * Q' s t l =
        ∑ m, K i j m * D' m l + ∑ m, D i m * K m j l +
          negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m l)
    {e f : ℤ} {a b : NovikovModule R F}
    (ha : a ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) e)
    (hb : b ∈ (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) f) :
    countMap r r' q hq hF hF' Φ (kernelProduct hnQ (kernelOfMatrix_mem hF r r r _) a b) -
        kernelProduct hnQ' (kernelOfMatrix_mem hF' r' r' r' _) (countMap r r' q hq hF hF' Φ a)
          (countMap r r' q hq hF hF' Φ b) ∈
      (kernelMap hδ' (mapKernelOfMatrix_mem hF' r' r' _)).coboundaries
        (gradeBy R F' fun p => n - μ' p) (e + f) := by
  obtain ⟨K, hK, hKid⟩ := hcont
  rw [countMap_apply, countMap_apply, countMap_apply,
    ← novikovProductOfMatrix_eq_kernelProduct hF hF hF r r r _ hnQ,
    ← novikovProductOfMatrix_eq_kernelProduct hF' hF' hF' r' r' r' _ hnQ']
  exact novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    r r r q hq r' r' r' hF hF hF hF' hF' hF' hμ Q Q' Φ Φ Φ K D D D' n hμ hμ' hK hKid hδ hδ hδ' ha
    hb

variable
  (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
    μ ⟨k, r k⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n)
  (hQ' : ∀ i j k, ∀ A ∈ (Q' i j k).support,
    μ' ⟨k, r' k⟩ - degree ω c (q A) = μ' ⟨i, r' i⟩ + μ' ⟨j, r' j⟩ - n)
  (hL : ∀ i j l, ∑ k, Q i j k * D k l =
    ∑ k, D i k * Q k j l + negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ k, D j k * Q i k l)
  (hL' : ∀ i j l, ∑ k, Q' i j k * D' k l =
    ∑ k, D' i k * Q' k j l + negOnePowCast R (n - μ' ⟨i, r' i⟩) • ∑ k, D' j k * Q' i k l)
  (E : ι → NovikovSeries R G ωG) (E' : ι' → NovikovSeries R G ωG)
  (hE : ∀ i, ∀ A ∈ (E i).support, μ ⟨i, r i⟩ - degree ω c (q A) = n)
  (hE' : ∀ i, ∀ A ∈ (E' i).support, μ' ⟨i, r' i⟩ - degree ω c (q A) = n)
  (hED : ∀ l, ∑ i, E i * D i l = 0) (hED' : ∀ l, ∑ i, E' i * D' i l = 0)
  [DecidableEq ι] [DecidableEq ι']
  (hone_mul : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ j l, ∀ A ∈ (K j l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨j, r j⟩ + 1) ∧
    ∀ j l, ∑ i, E i * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D m l + ∑ m, D j m * K m l)
  (hone_mul' : ∃ K : ι' → ι' → NovikovSeries R G ωG,
    (∀ j l, ∀ A ∈ (K j l).support, μ' ⟨l, r' l⟩ - degree ω c (q A) = μ' ⟨j, r' j⟩ + 1) ∧
    ∀ j l, ∑ i, E' i * Q' i j l - (1 : Matrix ι' ι' (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D' m l + ∑ m, D' j m * K m l)
  (hmul_one : ∃ K : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (K i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ j, E j * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D m l + ∑ m, D i m * K m l)
  (hmul_one' : ∃ K : ι' → ι' → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (K i l).support, μ' ⟨l, r' l⟩ - degree ω c (q A) = μ' ⟨i, r' i⟩ + 1) ∧
    ∀ i l, ∑ j, E' j * Q' i j l - (1 : Matrix ι' ι' (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D' m l + ∑ m, D' i m * K m l)
  (hassoc : ∃ K : ι → ι → ι → ι → NovikovSeries R G ωG,
    (∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ + μ ⟨k, r k⟩ - 2 * n + 1) ∧
    ∀ i j k l, ∑ t, Q i j t * Q t k l - ∑ u, Q j k u * Q i u l =
      ∑ m, K i j k m * D m l + ∑ m, D i m * K m j k l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m k l +
        negOnePowCast R (n - μ ⟨i, r i⟩ + (n - μ ⟨j, r j⟩)) • ∑ m, D k m * K i j m l)
  (hassoc' : ∃ K : ι' → ι' → ι' → ι' → NovikovSeries R G ωG,
    (∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ' ⟨l, r' l⟩ - degree ω c (q A) = μ' ⟨i, r' i⟩ + μ' ⟨j, r' j⟩ + μ' ⟨k, r' k⟩ - 2 * n + 1) ∧
    ∀ i j k l, ∑ t, Q' i j t * Q' t k l - ∑ u, Q' j k u * Q' i u l =
      ∑ m, K i j k m * D' m l + ∑ m, D' i m * K m j k l +
        negOnePowCast R (n - μ' ⟨i, r' i⟩) • ∑ m, D' j m * K i m k l +
        negOnePowCast R (n - μ' ⟨i, r' i⟩ + (n - μ' ⟨j, r' j⟩)) • ∑ m, D' k m * K i j m l)
  (hΦ : ∀ i i', ∀ A ∈ (Φ i i').support, μ' ⟨i', r' i'⟩ - degree ω c (q A) = μ ⟨i, r i⟩)
  (hΨ : ∀ i' i, ∀ A ∈ (Ψ i' i).support, μ ⟨i, r i⟩ - degree ω c (q A) = μ' ⟨i', r' i'⟩)
  (hΦD : ∀ i l, ∑ k, Φ i k * D' k l = ∑ k, D i k * Φ k l)
  (hΨD : ∀ i l, ∑ k, Ψ i k * D k l = ∑ k, D' i k * Ψ k l)
  (hcont : ∃ K : ι → ι → ι' → NovikovSeries R G ωG,
    (∀ i j l, ∀ A ∈ (K i j l).support,
      μ' ⟨l, r' l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + μ ⟨j, r j⟩ - n + 1) ∧
    ∀ i j l, ∑ k, Q i j k * Φ k l - ∑ s, ∑ t, Φ i s * Φ j t * Q' s t l =
      ∑ m, K i j m * D' m l + ∑ m, D i m * K m j l +
        negOnePowCast R (n - μ ⟨i, r i⟩) • ∑ m, D j m * K i m l)
  (hΨΦ : ∃ Y : ι → ι → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (Y i l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨i, r i⟩ + 1) ∧
    ∀ i l, ∑ k, Φ i k * Ψ k l - (if i = l then 1 else 0) =
      ∑ m, Y i m * D m l + ∑ m, D i m * Y m l)
  (hΦΨ : ∃ Y' : ι' → ι' → NovikovSeries R G ωG,
    (∀ i l, ∀ A ∈ (Y' i l).support, μ' ⟨l, r' l⟩ - degree ω c (q A) = μ' ⟨i, r' i⟩ + 1) ∧
    ∀ i l, ∑ k, Ψ i k * Φ k l - (if i = l then 1 else 0) =
      ∑ m, Y' i m * D' m l + ∑ m, D' i m * Y' m l)

/-- **Continuation maps of class-indexed counts are algebra isomorphisms.** Let two complexes
of class-indexed counts, for instance those of two Hamiltonians, satisfy the hypotheses of
`TauCeti.Floer.cohomologyGRingOfCounts`, so that their degree-wise cohomologies are algebras over
the ground ring. Let `Φ` and `Ψ` count rigid continuation cylinders in the two directions,
preserving the index (`hΦ`, `hΨ`), and suppose that the ends of the one-dimensional moduli spaces
give the identities saying that `Φ` and `Ψ` are chain maps (`hΦD`, `hΨD`), that `Ψ ∘ Φ` and
`Φ ∘ Ψ` are homotopic to the identities (`hΨΦ`, `hΦΨ`), and that the continuation family of pairs
of pants is a homotopy between `Φ (a ⋆ b)` and `Φ a ⋆' Φ b` (`hcont`), each homotopy counting
configurations which lower the cochain degree by one. Then the maps induced by `Φ` on cohomology
form an isomorphism of algebras over the ground ring. In particular continuation sends the unit,
the class of the PSS cycle, to the unit, although no identity relating the two PSS cycles is
assumed. -/
def continuationAlgEquivOfCounts :
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    letI := cohomologyGAlgebraOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    letI := cohomologyGRingOfCounts q hq r' hF' hμ' n D' hδ' Q' hnQ' hQ' hL' E' hE' hED' hone_mul'
      hmul_one' hassoc'
    letI := cohomologyGAlgebraOfCounts q hq r' hF' hμ' n D' hδ' Q' hnQ' hQ' hL' E' hE' hED'
      hone_mul' hmul_one' hassoc'
    (⨁ k, (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
        (gradeBy R F fun p => n - μ p) k) ≃ₐ[R]
      ⨁ k, (kernelMap hδ' (mapKernelOfMatrix_mem hF' r' r' _)).cohomology
        (gradeBy R F' fun p => n - μ' p) k :=
  algEquivOfCounts q hq r r' hF hF' hμ hμ' n D D' hδ hδ' Q Q' hnQ hnQ' hQ hQ' hL hL' E E' hE hE' hED
    hED' hone_mul hone_mul' hmul_one hmul_one' hassoc hassoc' Φ Ψ hΦ hΨ hΦD hΨD
    (fun ha hb => countMap_kernelProduct_sub_mem_coboundaries q hq r r' hF hF' hμ hμ' n D D' hδ hδ'
      Φ Q Q' hnQ hnQ' hcont ha hb)
    hΨΦ hΦΨ

/-- The continuation isomorphism sends the class of a cocycle `a` to the class of its image `Φ a`
under the map of the continuation counts. -/
theorem continuationAlgEquivOfCounts_of_mk {k : ℤ}
    (a : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) k)
    (b : (kernelMap hδ' (mapKernelOfMatrix_mem hF' r' r' _)).cocycles
      (gradeBy R F' fun p => n - μ' p) k)
    (hab : novikovMapOfMatrix hF hF' r r' (fun i i' => coefficientComparison q hq (Φ i i')) a = b) :
    continuationAlgEquivOfCounts q hq r r' hF hF' hμ hμ' n D D' hδ hδ' Φ Ψ Q Q' hnQ hnQ' hQ hQ' hL
        hL' E E' hE hE' hED hED' hone_mul hone_mul' hmul_one hmul_one' hassoc hassoc' hΦ hΨ hΦD hΨD
        hcont hΨΦ hΦΨ (of _ k (Submodule.Quotient.mk a)) =
      of (fun k => (kernelMap hδ' (mapKernelOfMatrix_mem hF' r' r' _)).cohomology
        (gradeBy R F' fun p => n - μ' p) k) k (Submodule.Quotient.mk b) :=
  algEquivOfCounts_of_mk q hq r r' hF hF' hμ hμ' n D D' hδ hδ' Q Q' hnQ hnQ' hQ hQ' hL hL' E E' hE
    hE' hED hED' hone_mul hone_mul' hmul_one hmul_one' hassoc hassoc' Φ Ψ hΦ hΨ hΦD hΨD _ hΨΦ hΦΨ a
    b hab

/-- The inverse of the continuation isomorphism is induced by the continuation counts `Ψ` in the
opposite direction: it sends the class of a cocycle `b` to the class of `Ψ b`. -/
theorem continuationAlgEquivOfCounts_symm_of_mk {k : ℤ}
    (b : (kernelMap hδ' (mapKernelOfMatrix_mem hF' r' r' _)).cocycles
      (gradeBy R F' fun p => n - μ' p) k)
    (a : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cocycles
      (gradeBy R F fun p => n - μ p) k)
    (hba : novikovMapOfMatrix hF' hF r' r (fun i' i => coefficientComparison q hq (Ψ i' i)) b = a) :
    letI := cohomologyGRingOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    letI := cohomologyGAlgebraOfCounts q hq r hF hμ n D hδ Q hnQ hQ hL E hE hED hone_mul hmul_one
      hassoc
    letI := cohomologyGRingOfCounts q hq r' hF' hμ' n D' hδ' Q' hnQ' hQ' hL' E' hE' hED' hone_mul'
      hmul_one' hassoc'
    letI := cohomologyGAlgebraOfCounts q hq r' hF' hμ' n D' hδ' Q' hnQ' hQ' hL' E' hE' hED'
      hone_mul' hmul_one' hassoc'
    (continuationAlgEquivOfCounts q hq r r' hF hF' hμ hμ' n D D' hδ hδ' Φ Ψ Q Q' hnQ hnQ' hQ hQ'
        hL hL' E E' hE hE' hED hED' hone_mul hone_mul' hmul_one hmul_one' hassoc hassoc' hΦ hΨ hΦD
        hΨD hcont hΨΦ hΦΨ).symm (of _ k (Submodule.Quotient.mk b)) =
      of (fun k => (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
        (gradeBy R F fun p => n - μ p) k) k (Submodule.Quotient.mk a) :=
  algEquivOfCounts_symm_of_mk q hq r r' hF hF' hμ hμ' n D D' hδ hδ' Q Q' hnQ hnQ' hQ hQ' hL hL' E
    E' hE hE' hED hED' hone_mul hone_mul' hmul_one hmul_one' hassoc hassoc' Φ Ψ hΦ hΨ hΦD hΨD _ hΨΦ
    hΦΨ b a hba

end CohomologyRing

end TauCeti.Floer
