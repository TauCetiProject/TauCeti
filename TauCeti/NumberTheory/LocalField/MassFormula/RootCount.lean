/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.FieldTheory.IntermediateField.RootCount
import TauCeti.NumberTheory.LocalField.Eisenstein.RootCount
import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Root counts of Eisenstein polynomials in the counted extensions

For a subextension `L` and a coefficient vector `a : Fin n → K`, the root count
`L.rootCount a` is the number of roots of the monic polynomial
`TauCeti.Polynomial.monicOfCoeff a` lying in `L`, counted with multiplicity. Serre's proof of the
mass formula integrates these root counts over the Eisenstein polynomials, and the identity that
makes the integration work is that, at a separable Eisenstein polynomial of degree `n`, the root
counts over all `L ∈ σ_K(n)` add up to `n`.

The reason is that an Eisenstein polynomial `f` of degree `n` is irreducible, so each of its roots
`x` in the separable closure generates a member `K⟮x⟯` of `σ_K(n)`. Conversely a root `x` lies in a
member `L` of `σ_K(n)` exactly when `K⟮x⟯ = L`, as both have degree `n`. The roots of `f` lying in
`L` are therefore the roots generating `L`, and summing over `L` counts every root of `f` exactly
once. The identification of the roots in `L` with its generators is
`IntermediateField.rootCount_eq_card_filter_adjoin_eq`, which holds for any irreducible
polynomial. When `f` is separable it has `n` roots in the separable closure. Separability is
needed: an inseparable Eisenstein polynomial, which exists in equal characteristic, is irreducible
and so has no root at all in the separable closure.

For a single `L ∈ σ_K(n)`, the root count of an Eisenstein polynomial is a finite sum of ball
indicators: if the uniformizers of `L` are covered by pairwise disjoint balls of order `r` larger
than the discriminant exponent `d(L)`, then `L.rootCount a` is the number of these balls that
contain a root. The balls do not depend on `a`, so integrating `L.rootCount` over the Eisenstein
polynomials reduces to measuring, ball by ball, the polynomials with a root in that ball.

## Main results

* `TauCeti.tsum_rootCount_eq_of_separable`: at a separable Eisenstein polynomial of degree `n`,
  the root counts over `σ_K(n)` sum to `n`.
* `IntermediateField.rootCount_eq_sum_ite_of_eisenstein`: for `L ∈ σ_K(n)`, the root count of an
  Eisenstein polynomial of degree `n` is the number of balls containing a root, in any disjoint
  cover of the uniformizers of `L` by balls of order larger than `d(L)`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §§2–3.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped IntermediateField ENNReal

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A polynomial over `𝒪[K]` with image `monicOfCoeff a` over `K`, for `a : Fin n → K`, has
degree `n`. -/
private theorem natDegree_eq_of_map_eq {n : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) : f.natDegree = n := by
  rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
    natDegree_monicOfCoeff]

/-- A root, in the separable closure, of the monic polynomial with coefficient vector
`a : Fin n → K` generates a member of `σ_K(n)` when that polynomial comes from an Eisenstein
polynomial over `𝒪[K]`. -/
private theorem adjoin_mem_totallyRamifiedOfDegree_of_mem_aroots {n : ℕ} {a : Fin n → K}
    {f : 𝒪[K][X]} (he : f.IsEisensteinAt 𝓂[K]) (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a)
    {x : SeparableClosure K} (hx : x ∈ (monicOfCoeff a).aroots (SeparableClosure K)) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n :=
  adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he (natDegree_eq_of_map_eq hf)
    (hf ▸ (mem_aroots.mp hx).2)

/-- **The root counts over `σ_K(n)` sum to `n`.** Let `f` be an Eisenstein polynomial over `𝒪[K]`
with image `monicOfCoeff a` over `K`, for `a : Fin n → K`, and assume that `monicOfCoeff a` is
separable. Then `∑_{L ∈ σ_K(n)} L.rootCount a = n`: each of the `n` roots of `monicOfCoeff a` in
the separable closure lies in exactly one member of `σ_K(n)`, the one it generates. -/
theorem tsum_rootCount_eq_of_separable {n : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (he : f.IsEisensteinAt 𝓂[K]) (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a)
    (hsep : (monicOfCoeff a).Separable) :
    ∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞) = n := by
  classical
  have hcard : ((monicOfCoeff a).aroots (SeparableClosure K)).card = n := by
    rw [aroots_def, ← (IsSepClosed.splits_codomain _ hsep).natDegree_eq_card_roots,
      natDegree_map, natDegree_monicOfCoeff]
  -- The multiset of the fields generated by the roots, each lying in `σ_K(n)`.
  set F := ((monicOfCoeff a).aroots (SeparableClosure K)).map fun x ↦ K⟮x⟯
  have hmem : ∀ L ∈ F, L ∈ totallyRamifiedOfDegree K n := by
    intro L hL
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hL
    exact adjoin_mem_totallyRamifiedOfDegree_of_mem_aroots he hf hx
  have hcount (L : totallyRamifiedOfDegree K n) : L.1.rootCount a = F.count L.1 := by
    have hL := mem_totallyRamifiedOfDegree_iff.mp L.2
    have := hL.2.finite
    -- `f` has positive degree `n = [L : K]` and is monic, so Eisenstein's criterion and Gauss's
    -- lemma make `monicOfCoeff a` irreducible over `K`.
    have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
      (hf ▸ monic_monicOfCoeff a)
    have hpos : 0 < f.natDegree := natDegree_eq_of_map_eq hf ▸ hL.1 ▸ Module.finrank_pos
    have ha : Irreducible (monicOfCoeff a) :=
      hf ▸ (hmonic.irreducible_iff_irreducible_map_fraction_map).mp
        (he.irreducible (Ideal.IsMaximal.isPrime inferInstance) hmonic.isPrimitive hpos)
    rw [L.1.rootCount_eq_card_filter_adjoin_eq ha hL.1, Multiset.count_map]
    exact congrArg _ (Multiset.filter_congr fun _ _ ↦ eq_comm)
  have hsupp : Function.support (fun L ↦ (F.count L : ℝ≥0∞)) ⊆ totallyRamifiedOfDegree K n :=
    fun L hL ↦ hmem L (Multiset.count_ne_zero.mp (by simpa using hL))
  calc ∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞)
      = ∑' L : totallyRamifiedOfDegree K n, (F.count L.1 : ℝ≥0∞) := by simp only [hcount]
    _ = ∑' L, (F.count L : ℝ≥0∞) := tsum_subtype_eq_of_support_subset hsupp
    _ = ∑ L ∈ F.toFinset, (F.count L : ℝ≥0∞) :=
      tsum_eq_sum fun L hL ↦ by simpa using hL
    _ = n := by
      rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq, Multiset.card_map, hcard]

open Classical in
/-- **The root count in a counted extension as a sum over balls.** Let `L ∈ σ_K(n)`, with its
canonical local-field structure, and let `f` be an Eisenstein polynomial over `𝒪[K]` with image
`monicOfCoeff a` over `K`, for `a : Fin n → K`. Let `C` index a family of pairwise disjoint balls
`v_L(x - c) ≥ r` covering the uniformizers of `L`, of order `r` larger than the discriminant
exponent `d(L)`. Then `L.rootCount a` is the number of these balls containing a root of `f`. -/
theorem _root_.IntermediateField.rootCount_eq_sum_ite_of_eisenstein {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ {a : Fin n → K} {f : 𝒪[K][X]}, f.IsEisensteinAt 𝓂[K] →
      f.map (algebraMap 𝒪[K] K) = monicOfCoeff a → ∀ {r : ℕ}, L.discriminantExponent < r →
      ∀ C : Finset 𝒪[L], {x : 𝒪[L] | addVal 𝒪[L] x = 1} ⊆
        ⋃ c ∈ C, {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)} →
      (C : Set 𝒪[L]).PairwiseDisjoint (fun c ↦ {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)}) →
        L.rootCount a =
          ∑ c ∈ C, if ∃ z : 𝒪[L], aeval z f = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c) then 1 else 0 := by
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := hL'.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro a f he hf r hr C hcover hdisj
  have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  -- `d(L)` is the different exponent of `L / K`, as `L / K` has inertia degree one.
  have htr := (IntermediateField.isTotallyRamified_iff L).1 hL'.2
  rw [IntermediateField.discriminantExponent_eq,
    discriminantExponent_eq_inertiaDegree_mul_differentExponent, htr.inertiaDegree_eq_one,
    one_mul] at hr
  rw [L.rootCount_def, ← hf, aroots_eq_map_roots_integerRing L hmonic, Multiset.card_map]
  exact card_roots_map_eq_sum_ite_of_eisenstein he ((natDegree_eq_of_map_eq hf).trans hL'.1.symm)
    hr C hcover hdisj

end TauCeti
