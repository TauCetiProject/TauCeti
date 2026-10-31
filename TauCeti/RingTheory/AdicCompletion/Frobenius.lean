/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Flat.LocalCriterion

/-!
# Frobenius on the completion of a local ring

Let `R` be a Noetherian local ring of characteristic `p` and let `R̂` be its completion at the
maximal ideal `𝔪`. If the Frobenius endomorphism `x ↦ x ^ p` of `R` is flat, then so is the
Frobenius endomorphism of `R̂` (`TauCeti.AdicCompletion.flat_frobenius`).

Frobenius commutes with the flat map `R → R̂`, so `R̂` is flat over `R` through
`R → R̂ → R̂`, the second map being Frobenius. Since `𝔪 R̂` is the maximal ideal of `R̂`, flatness
over the fibres (`RingHom.Flat.of_comp_of_map_maximalIdeal_eq`) then makes Frobenius of `R̂` flat.
No finiteness of Frobenius is needed. This is the step that lets Kunz's characterization of
regular rings by flatness of Frobenius be checked on complete local rings, where Cohen's structure
theorem applies.

The completion of a ring that is Hausdorff for the `I`-adic topology contains the ring, so it has
the same exponential characteristic (`AdicCompletion.expChar`). This applies to the completion of a
Noetherian local ring at its maximal ideal, by Krull's intersection theorem.

## Main results

* `AdicCompletion.expChar`: the `I`-adic completion of an `I`-adically Hausdorff ring has the
  exponential characteristic of the ring.
* `TauCeti.AdicCompletion.flat_frobenius`: if Frobenius of a Noetherian local ring is flat, so is
  Frobenius of its completion.

## References

* [Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP), flatness over the fibres.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), proof of Corollary 11.35.
-/

public section

open IsLocalRing

namespace AdicCompletion

/-- The completion of an `I`-adically Hausdorff ring has the exponential characteristic of the
ring, since the ring embeds into it. -/
instance expChar {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R] (p : ℕ) [ExpChar R p] :
    ExpChar (AdicCompletion I R) p :=
  expChar_of_injective_algebraMap (of_injective I R) p

end AdicCompletion

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : ℕ) [ExpChar R p]

/-- **Frobenius flatness passes to the completion.** If the Frobenius endomorphism of a
Noetherian local ring `R` is flat, so is the Frobenius endomorphism of its completion at the
maximal ideal. -/
theorem flat_frobenius (h : (frobenius R p).Flat) :
    (frobenius (AdicCompletion (maximalIdeal R) R) p).Flat := by
  have : IsLocalHom (frobenius (AdicCompletion (maximalIdeal R) R) p) :=
    ⟨fun _ ha ↦ (isUnit_pow_iff (expChar_pos R p).ne').mp ha⟩
  refine RingHom.Flat.of_comp_of_map_maximalIdeal_eq (algebraMap R _) _ ?_
    AdicCompletion.maximalIdeal_eq_map.symm
  -- Frobenius commutes with `R → R̂`, which is flat.
  have hcomm : (frobenius (AdicCompletion (maximalIdeal R) R) p).comp (algebraMap R _) =
      (algebraMap R _).comp (frobenius R p) :=
    RingHom.ext fun x ↦ ((algebraMap R _).map_frobenius p x).symm
  rw [hcomm]
  exact h.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)

end TauCeti.AdicCompletion
