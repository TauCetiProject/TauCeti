/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Algebra
import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Maps out of the henselization of a pair

The henselization of `(R, I)` is universal among henselian pairs `(S, J)` receiving a map of
pairs from `(R, I)`. This file proves the uniqueness half of that universal property, under the
weaker hypothesis that `I` generates an ideal of `S` inside its Jacobson radical: an `R`-algebra
map out of the henselization is determined by its restrictions to the étale neighbourhoods, and
each restriction is a map out of an étale algebra which is already determined modulo `IS`.

## References

* [Stacks Project, Lemma 15.12.1](https://stacks.math.columbia.edu/tag/0A02), the universal
  property of the henselization of a pair.
* The Stacks Project, Lemma 15.11.5, uniqueness of sections modulo an ideal in the Jacobson
  radical.
-/

public section

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- Two `R`-algebra maps out of the henselization of `(R, I)` agree as soon as `I` generates an
ideal of the target inside its Jacobson radical. In particular, maps of pairs from the
henselization of `(R, I)` to a henselian pair are unique. -/
theorem algHom_ext_of_map_le_jacobson {S : Type*} [CommRing S] [Algebra R S]
    (hI : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥) {f g : algebra I →ₐ[R] S} : f = g := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨B, b, rfl⟩ := exists_stage_eq I x
  obtain ⟨hEtale, hBij⟩ := (isNeighbourhood_iff I B.obj).mp B.property
  let := hEtale
  -- On a stage, both maps agree modulo `IS` because `B ⧸ IB ≅ R ⧸ I`, hence agree outright.
  have hfg : (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).comp (f.comp (stage I B)) =
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))).comp (g.comp (stage I B)) :=
    AlgHom.ext fun b ↦ by
      simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
        quotient_mk_eq_of_reducedMap_surjective I hBij.2
          (f.comp (stage I B)) (g.comp (stage I B)) b
  exact DFunLike.congr_fun
    (Algebra.FormallyUnramified.ext_of_quotient_eq R B.obj _ hI hfg) b

end TauCeti.Henselization
