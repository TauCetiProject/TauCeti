/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Transgression

/-!
# Transgression for a minimal free pro-`p` presentation

Let `F = freeProP p X` and let `R` be a closed normal subgroup contained in its pro-`p`
Frattini subgroup. For finite abelian coefficients `M` of exponent dividing `p` with trivial
action, the restriction `H¹(F, M) → H¹(R, M)` is zero, while `H²(F, M)` vanishes. The five-term
sequence therefore makes the transgression `H¹(R, M) ^ (F ⧸ R) → H²(F ⧸ R, M ^ R)` bijective.
For a finite generating type, `R ≤ Φ(F)` characterizes minimal presentations
(`TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`). This is the first step toward
interpreting `dim H²(G, 𝔽_p)` as the number of relations of `G`.

## Main result

* `TauCeti.freeProP.transgression_bijective`: transgression is bijective for a closed normal
  subgroup `R ≤ Φ(F)` and finite abelian coefficients of exponent dividing `p` with trivial
  action.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.5).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.4.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.3.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

variable {p : ℕ} [Fact p.Prime]

namespace freeProP

variable {X : Type u} {M : Type v} [CommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [Finite M] [MulDistribMulAction (freeProP p X) M] [ContinuousSMul (freeProP p X) M]

/-- **The transgression of a minimal presentation is an isomorphism.** Let `F = freeProP p X`
and let `R` be a closed normal subgroup of `F` contained in its pro-`p` Frattini subgroup, as for
the relation subgroup of a minimal presentation. For a finite abelian group `M` of exponent
dividing `p` with trivial `F`-action, for instance `𝔽_p`, the transgression
`H¹(R, M) ^ (F ⧸ R) → H²(F ⧸ R, M ^ R)` is bijective. -/
theorem transgression_bijective (R : Subgroup (freeProP p X)) [R.Normal]
    (hRc : IsClosed (R : Set (freeProP p X))) (hR : R ≤ proPFrattini p (freeProP p X))
    (htriv : ∀ (g : freeProP p X) (m : M), g • m = m) (hexp : ∀ m : M, m ^ p = 1) :
    Function.Bijective (transgression (freeProP p X) (Additive M) R hRc) :=
  haveI := subsingleton_H2 (X := X) (IsPGroup.isProP (p := p) fun m ↦ ⟨1, by simpa using hexp m⟩)
  transgression_bijective_of_le_proPFrattini hRc hR
    (fun g m ↦ by rw [← ofMul_toMul m, ← Additive.ofMul_smul, htriv])
    (fun m ↦ by rw [← ofMul_toMul m, ← ofMul_pow, hexp, ofMul_one])

end freeProP

end TauCeti
