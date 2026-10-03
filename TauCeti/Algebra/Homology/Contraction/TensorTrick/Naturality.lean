/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.TensorTrick

/-!
# Naturality of the tensor-trick homotopy

The tensor trick sends compatible degree-zero maps between graded special contractions to
compatible maps on reduced tensor words. The homotopy identity is the nontrivial part: each
single-slot homotopy commutes with the letterwise map, including the Koszul twists before that
slot and the inclusion-projection composite after it.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

namespace TauCeti.LinearSpecialContraction

open ReducedTensorWords

universe uR uM uN uM' uN'

variable {R : Type uR} [CommRing R]
  {M : Type uM} {N : Type uN} {M' : Type uM'} {N' : Type uN'}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  {dM : Module.End R M} {dN : Module.End R N}
  {dM' : Module.End R M'} {dN' : Module.End R N'}

/-- The reduced tensor-word homotopies commute with the letterwise map induced by a
homogeneous degree-zero map between compatible contractions. -/
theorem reducedTensorWordsHomotopy_naturality
    (c : LinearSpecialContraction dM dN) (c' : LinearSpecialContraction dM' dN')
    {G : InternalGrading R M} {G' : InternalGrading R M'}
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : LinearMap.IsHomogeneous f G.piece G'.piece 0)
    (hi : f ∘ₗ c.incl = c'.incl ∘ₗ g)
    (hp : g ∘ₗ c.proj = c'.proj ∘ₗ f)
    (hh : f ∘ₗ c.homotopy = c'.homotopy ∘ₗ f) :
    ReducedTensorWords.map (R := R) f ∘ₗ c.reducedTensorWordsHomotopy G =
      c'.reducedTensorWordsHomotopy G' ∘ₗ ReducedTensorWords.map (R := R) f := by
  have hτ : f ∘ₗ G.koszulTwist 1 = G'.koszulTwist 1 ∘ₗ f := by
    simpa using (hf.koszulTwist_comp 1).symm
  simp only [LinearMap.ext_iff, LinearMap.comp_apply] at hi hp hh hτ
  refine ReducedTensorWords.linearMap_ext R M fun n x ↦ ?_
  simp only [LinearMap.comp_apply, reducedTensorWordsHomotopy_of_tprod,
    map_sum, map_of_tprod]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  funext i
  split_ifs <;> simp [hi, hp, hh, hτ]

end TauCeti.LinearSpecialContraction
