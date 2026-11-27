/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.PairSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing

/-!
# The first differential of a filtered complex through the connecting map of a pair

For an increasing filtration `F` of a chain complex, regarded as a cochain complex `K` with
`K^{-n} = C_n`, the first differential `d¹ : E¹_{p,q} ⟶ E¹_{p-1,q}` of the homological spectral
sequence is the connecting map `H_{p+q}(F_p/F_{p-1}) ⟶ H_{p+q-1}(F_{p-1}/F_{p-2})` of the short
exact sequence of quotients `F_{p-1}/F_{p-2} ⟶ F_p/F_{p-2} ⟶ F_p/F_{p-1}`
(`CochainComplex.homologicalFiltrationSpectralSequence_first_page_d_eq`). This file factors it
through the connecting map `H_{p+q}(K/F_{p-1}) ⟶ H_{p+q-1}(F_{p-1})` of the pair `F_{p-1} ⊆ K`, the
short exact sequence `F_{p-1} ⟶ K ⟶ K/F_{p-1}` (`HomologicalComplex.pairSequence`): `d¹` is the map
`F_p/F_{p-1} ⟶ K/F_{p-1}` induced by the inclusion of `F_p`, followed by that connecting map and the
projection `F_{p-1} ⟶ F_{p-1}/F_{p-2}`
(`CochainComplex.homologicalFiltrationSpectralSequence_first_page_d_eq_δ`).

This is the case `X = F_{p-2}`, `Y = F_{p-1}`, `Z = F_p` of the factorization of the connecting
map of `Y/X ⟶ Z/X ⟶ Z/Y` through that of the pair `Y ⊆ K`
(`HomologicalComplex.δ_cokernelCompSequence_ofLE`). When `F_{p-2} = 0` and `F_p = K`, the two
outer maps are isomorphisms, and `d¹` is the connecting map of the pair itself.

## Main results

* `CochainComplex.homologicalFiltrationSpectralSequence_first_page_d_eq_δ`: the first differential
  of a filtered complex through the connecting map of the pair `F_{p-1} ⊆ K`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2.
-/

public section

noncomputable section

namespace CochainComplex

open CategoryTheory Limits HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}

variable (F : ℤ → Subobject K) (hF : Monotone F)

/-- **The first differential of a filtered complex through the connecting map of a pair.** The
differential `d¹ : E¹_{p,q} ⟶ E¹_{p-1,q}`, from `H_{p+q}(F_p/F_{p-1})` to
`H_{p+q-1}(F_{p-1}/F_{p-2})`, is the map `F_p/F_{p-1} ⟶ K/F_{p-1}` induced by the inclusion
`F_p ⊆ K`, followed by the connecting map of the pair `F_{p-1} ⊆ K` and the projection
`F_{p-1} ⟶ F_{p-1}/F_{p-2}`. -/
theorem homologicalFiltrationSpectralSequence_first_page_d_eq_δ (p q : ℤ) :
    ((homologicalFiltrationSpectralSequence F hF).page 1).d (p, q) (p - 1, q) =
      (homologicalFiltrationSpectralSequenceFirstPageXIso F hF p q).hom ≫
        (HomologicalComplex.homologyMap
          (cokernel.map (Subobject.ofLE (F (p - 1)) (F p) (hF (by lia))) (F (p - 1)).arrow (𝟙 _)
            (F p).arrow (by simp)) _ ≫
        (pairSequence_shortExact (F (p - 1))).δ (-(p + q)) (-(p - 1 + q))
          (by simp only [ComplexShape.up_Rel]; lia) ≫
        HomologicalComplex.homologyMap
          (cokernel.π (Subobject.ofLE (F (p - 1 - 1)) (F (p - 1)) (hF (by lia)))) _) ≫
        (homologicalFiltrationSpectralSequenceFirstPageXIso F hF (p - 1) q).inv := by
  rw [homologicalFiltrationSpectralSequence_first_page_d_eq, δ_cokernelCompSequence_ofLE]

end CochainComplex
