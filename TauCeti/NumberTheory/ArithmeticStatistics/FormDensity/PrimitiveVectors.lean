/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.ZMod.LocalRing

import TauCeti.Data.ZMod.Count

/-!
# Primitive vectors over finite rings

A vector `v : ι → R` over a finite commutative ring is *primitive* when its coordinates generate
the unit ideal. Over `R = ZMod Q` these are the residue vectors `b` with `gcd(Q, b₀, …, bₙ) = 1`,
the points over which the local density of a form modulo `Q` counts zeros. This file defines the
finite set `FormDensity.primitiveVectors ι R` and computes it:

* membership is unimodularity in the sense of `Module.IsUnimodular`, and over a local ring it
  means that some coordinate is a unit;
* primitivity is preserved by ring homomorphisms, and over a product ring it holds exactly when it
  holds for both components, so the Chinese remainder theorem makes the count multiplicative in
  coprime moduli (`FormDensity.card_primitiveVectors_zmod_mul`);
* modulo a positive prime power there are `p ^ (r m) - p ^ ((r - 1) m)` primitive vectors of length
  `m` (`FormDensity.card_primitiveVectors_zmod_prime_pow`).

## References

* T. Browning, P. Le Boudec, W. Sawin, *The Hasse principle for random Fano hypersurfaces*,
  arXiv:2006.02356v1, §5.1 and (5.10).
-/

public section

open Finset

namespace TauCeti.FormDensity

variable {ι R S : Type*} [Fintype ι] [CommRing R] [Fintype R] [CommRing S] [Fintype S]

variable (ι R) in
/-- The primitive vectors over a finite commutative ring: the vectors whose coordinates generate
the unit ideal. -/
noncomputable def primitiveVectors : Finset (ι → R) := by
  classical
  exact univ.filter fun v ↦ Ideal.span (Set.range v) = ⊤

@[simp]
theorem mem_primitiveVectors {v : ι → R} :
    v ∈ primitiveVectors ι R ↔ Ideal.span (Set.range v) = ⊤ := by
  simp [primitiveVectors]

/-- A vector is primitive exactly when some linear combination of its coordinates is one. -/
theorem mem_primitiveVectors_iff_exists_sum {v : ι → R} :
    v ∈ primitiveVectors ι R ↔ ∃ c : ι → R, ∑ i, c i * v i = 1 := by
  rw [mem_primitiveVectors, Ideal.eq_top_iff_one, Ideal.span,
    Submodule.mem_span_range_iff_exists_fun]
  simp only [smul_eq_mul]

/-- A vector is primitive exactly when it is unimodular: some linear functional takes the value
one at it. -/
theorem mem_primitiveVectors_iff_isUnimodular {v : ι → R} :
    v ∈ primitiveVectors ι R ↔ Module.IsUnimodular R v := by
  classical
  have hrepr : ⇑((Pi.basisFun R ι).repr v) = v := funext fun i ↦ by simp
  rw [(Pi.basisFun R ι).isUnimodular_iff_span_repr_eq_top, hrepr, mem_primitiveVectors]

/-- Over a local ring, a vector is primitive exactly when one of its coordinates is a unit. For
`ZMod (p ^ r)` with `r ≠ 0` this means that some coordinate is nonzero modulo `p`. -/
theorem mem_primitiveVectors_iff_exists_isUnit [IsLocalRing R] {v : ι → R} :
    v ∈ primitiveVectors ι R ↔ ∃ i, IsUnit (v i) := by
  rw [mem_primitiveVectors]
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi⟩
  by_contra! hv
  have hle : Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr <| by
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hv i)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hle))

/-- Ring homomorphisms map primitive vectors to primitive vectors. -/
theorem comp_mem_primitiveVectors (f : R →+* S) {v : ι → R} (hv : v ∈ primitiveVectors ι R) :
    ⇑f ∘ v ∈ primitiveVectors ι S := by
  obtain ⟨c, hc⟩ := mem_primitiveVectors_iff_exists_sum.mp hv
  refine mem_primitiveVectors_iff_exists_sum.mpr ⟨⇑f ∘ c, ?_⟩
  simpa [map_sum] using congrArg f hc

/-- Ring isomorphisms identify the primitive vectors. -/
theorem comp_mem_primitiveVectors_iff (e : R ≃+* S) {v : ι → R} :
    ⇑e ∘ v ∈ primitiveVectors ι S ↔ v ∈ primitiveVectors ι R := by
  refine ⟨fun h ↦ ?_, comp_mem_primitiveVectors (e : R →+* S)⟩
  simpa [Function.comp_def] using comp_mem_primitiveVectors (e.symm : S →+* R) h

/-- A vector over a product ring is primitive exactly when both of its components are. -/
theorem mem_primitiveVectors_prod_iff {v : ι → R × S} :
    v ∈ primitiveVectors ι (R × S) ↔
      Prod.fst ∘ v ∈ primitiveVectors ι R ∧ Prod.snd ∘ v ∈ primitiveVectors ι S := by
  refine ⟨fun h ↦ ⟨comp_mem_primitiveVectors (RingHom.fst R S) h,
    comp_mem_primitiveVectors (RingHom.snd R S) h⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  obtain ⟨c₁, hc₁⟩ := mem_primitiveVectors_iff_exists_sum.mp h₁
  obtain ⟨c₂, hc₂⟩ := mem_primitiveVectors_iff_exists_sum.mp h₂
  refine mem_primitiveVectors_iff_exists_sum.mpr ⟨fun i ↦ (c₁ i, c₂ i), ?_⟩
  ext
  · simpa [Prod.fst_sum] using hc₁
  · simpa [Prod.snd_sum] using hc₂

/-- Ring isomorphisms preserve the number of primitive vectors. -/
theorem card_primitiveVectors_congr (e : R ≃+* S) :
    #(primitiveVectors ι S) = #(primitiveVectors ι R) :=
  (card_equiv (Equiv.piCongrRight fun _ ↦ e.toEquiv) fun _ ↦
    (comp_mem_primitiveVectors_iff e).symm).symm

/-- The number of primitive vectors over a product ring is the product of the numbers over the
factors. -/
theorem card_primitiveVectors_prod :
    #(primitiveVectors ι (R × S)) = #(primitiveVectors ι R) * #(primitiveVectors ι S) := by
  rw [← card_product]
  refine card_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ R) (fun _ ↦ S)) fun v ↦ ?_
  rw [Equiv.arrowProdEquivProdArrow_apply, mem_product]
  exact mem_primitiveVectors_prod_iff

/-- **Chinese remainder theorem for primitive vectors.** For coprime moduli, the number of
primitive vectors modulo `Q₁ Q₂` is the product of the numbers modulo `Q₁` and modulo `Q₂`. -/
theorem card_primitiveVectors_zmod_mul {Q₁ Q₂ : ℕ} [NeZero Q₁] [NeZero Q₂]
    (h : Q₁.Coprime Q₂) :
    #(primitiveVectors ι (ZMod (Q₁ * Q₂))) =
      #(primitiveVectors ι (ZMod Q₁)) * #(primitiveVectors ι (ZMod Q₂)) := by
  rw [← card_primitiveVectors_prod, card_primitiveVectors_congr (ZMod.chineseRemainder h)]

/-- Over the zero ring every vector is primitive, so there is exactly one primitive vector, even
for the empty index type. -/
theorem card_primitiveVectors_of_subsingleton [Subsingleton R] : #(primitiveVectors ι R) = 1 := by
  classical
  have : primitiveVectors ι R = univ :=
    eq_univ_of_forall fun v ↦ mem_primitiveVectors.mpr (Subsingleton.elim _ _)
  rw [this, card_univ, Fintype.card_eq_one_iff]
  exact ⟨0, fun _ ↦ Subsingleton.elim _ _⟩

/-- Over a finite local ring, a vector fails to be primitive exactly when all its coordinates are
nonunits, so the primitive vectors number `#R ^ #ι - #{nonunits} ^ #ι`. -/
theorem card_primitiveVectors_of_isLocalRing [IsLocalRing R] [DecidableEq R] :
    #(primitiveVectors ι R) =
      Fintype.card R ^ Fintype.card ι - #{x : R | ¬IsUnit x} ^ Fintype.card ι := by
  classical
  have hcompl : (primitiveVectors ι R)ᶜ = Fintype.piFinset fun _ : ι ↦ {x : R | ¬IsUnit x} := by
    ext v
    simp only [mem_compl, mem_primitiveVectors_iff_exists_isUnit, Fintype.mem_piFinset,
      mem_filter, mem_univ, true_and, not_exists]
  rw [← compl_compl (primitiveVectors ι R), card_compl, hcompl, Fintype.card_piFinset,
    prod_const, card_univ, Fintype.card_fun]

/-- **Counting primitive vectors modulo a prime power.** For a prime `p` and `r ≠ 0` there are
`p ^ (r m) - p ^ ((r - 1) m)` primitive vectors of length `m` modulo `p ^ r`; for `m = 0` both
sides vanish. -/
theorem card_primitiveVectors_zmod_prime_pow (p r : ℕ) [Fact p.Prime] (hr : r ≠ 0) :
    #(primitiveVectors ι (ZMod (p ^ r))) =
      p ^ (r * Fintype.card ι) - p ^ ((r - 1) * Fintype.card ι) := by
  have : NeZero r := ⟨hr⟩
  rw [card_primitiveVectors_of_isLocalRing, ZMod.card_filter_not_isUnit_prime_pow p r hr,
    ZMod.card, pow_mul, pow_mul]

end TauCeti.FormDensity
