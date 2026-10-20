/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.FieldTheory.IntermediateField.Roots

/-!
# Root counts of Eisenstein polynomials in the counted extensions

A monic polynomial of degree `n` over `K` is its coefficient vector `a : Fin n → K`, through
`TauCeti.Polynomial.monicOfCoeff`. For a subextension `L`, the root count `L.rootCount a` is the
number of roots of that polynomial lying in `L`, counted with multiplicity. Serre's proof of the
mass formula integrates these root counts over the Eisenstein polynomials, and the identity that
makes the integration work is that, at a separable Eisenstein polynomial of degree `n`, the root
counts over all `L ∈ σ_K(n)` add up to `n`.

The reason is that an Eisenstein polynomial `f` of degree `n` is irreducible, so each of its roots
`x` in the separable closure generates a member `K⟮x⟯` of `σ_K(n)`. Conversely a root `x` lies in a
member `L` of `σ_K(n)` exactly when `K⟮x⟯ = L`, as both have degree `n`. The roots of `f` lying in
`L` are therefore the roots generating `L`, and summing over `L` counts every root of `f` exactly
once. When `f` is separable it has `n` roots in the separable closure. Separability is needed: an
inseparable Eisenstein polynomial, which exists in equal characteristic, is irreducible and so has
no root at all in the separable closure.

## Main definitions

* `IntermediateField.rootCount L a`: the number of roots, with multiplicity, of the monic
  polynomial with coefficient vector `a` that lie in `L`.

## Main results

* `TauCeti.rootCount_eq_card_filter_adjoin_eq`: at an Eisenstein polynomial of degree `n`, the
  roots in `L ∈ σ_K(n)` are the roots `x` in the separable closure with `K⟮x⟯ = L`.
* `TauCeti.tsum_rootCount_eq_of_separable`: at a separable Eisenstein polynomial of degree `n`,
  the root counts over `σ_K(n)` sum to `n`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2.
-/

public section
noncomputable section

open ValuativeRel Polynomial
open scoped IntermediateField ENNReal

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff natDegree_monicOfCoeff)

section General

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The root count of a coefficient vector `a : Fin n → K` in a subextension `L`: the number of
roots of the monic polynomial `monicOfCoeff a` lying in `L`, counted with multiplicity. -/
def _root_.IntermediateField.rootCount (L : IntermediateField K E) {n : ℕ} (a : Fin n → K) : ℕ :=
  ((monicOfCoeff a).aroots L).card

/-- The defining equation of `IntermediateField.rootCount`. -/
theorem _root_.IntermediateField.rootCount_def (L : IntermediateField K E) {n : ℕ}
    (a : Fin n → K) : L.rootCount a = ((monicOfCoeff a).aroots L).card := by
  rw [IntermediateField.rootCount]

end General

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A root, in the separable closure, of the monic polynomial with coefficient vector
`a : Fin n → K` generates a member of `σ_K(n)` when that polynomial comes from an Eisenstein
polynomial over `𝒪[K]`. -/
private theorem adjoin_mem_totallyRamifiedOfDegree_of_mem_aroots {n : ℕ} {a : Fin n → K}
    {f : 𝒪[K][X]} (he : f.IsEisensteinAt 𝓂[K]) (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a)
    {x : SeparableClosure K} (hx : x ∈ (monicOfCoeff a).aroots (SeparableClosure K)) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n := by
  have hfdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  exact adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hfdeg (hf ▸ (mem_aroots.mp hx).2)

open Classical in
/-- **The roots in a counted extension are its generators.** Let `f` be an Eisenstein polynomial
over `𝒪[K]` with image `monicOfCoeff a` over `K`, for `a : Fin n → K`. For `L ∈ σ_K(n)`, the
roots of `monicOfCoeff a` in `L` correspond, with multiplicities, to the roots `x` in the
separable closure with `K⟮x⟯ = L`. -/
theorem rootCount_eq_card_filter_adjoin_eq {n : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (he : f.IsEisensteinAt 𝓂[K]) (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a)
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    L.rootCount a =
      (((monicOfCoeff a).aroots (SeparableClosure K)).filter fun x ↦ K⟮x⟯ = L).card := by
  classical
  rw [mem_totallyRamifiedOfDegree_iff] at hL
  have := hL.2.finite
  rw [L.rootCount_def, ← Multiset.card_map, ← L.filter_aroots_eq_map_aroots]
  congr 1
  refine Multiset.filter_congr fun x hx ↦ ⟨fun hxL ↦ ?_, fun h ↦ h ▸ ?_⟩
  · -- `K⟮x⟯ ≤ L`, and both have degree `n`.
    have hdeg := (mem_totallyRamifiedOfDegree_iff.mp
      (adjoin_mem_totallyRamifiedOfDegree_of_mem_aroots he hf hx)).1
    exact IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr hxL) (hdeg.trans hL.1.symm)
  · exact IntermediateField.mem_adjoin_simple_self K x

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
    rw [rootCount_eq_card_filter_adjoin_eq he hf L.2, Multiset.count_map]
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

end TauCeti
