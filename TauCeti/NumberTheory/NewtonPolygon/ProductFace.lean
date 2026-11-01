/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# Finite faces of products of power series

If the Newton polygons of two power series have finite faces at a common slope, the Newton
polygon of their product has the face whose absolute endpoints are the sums of the endpoints.
Thus the face width, which counts the unit edges of that slope, adds under multiplication.
Singleton faces are allowed and contribute width zero. The endpoints include any initial
order of vanishing; they are not measured relative to the first nonzero coefficient.

The statement is algebraic: no norm, completeness or convergence hypothesis is needed once
both finite faces are given. It is the local counterpart of the global polynomial and entire
product formulas. In particular, it does not assert a global product identity for series known
only on a disc. Infinite supporting rays are excluded by the finite-face hypotheses.

The coefficient heights touch the supporting lines at both face endpoints. The coefficients of
the product at the sums of these endpoints have unique dominant terms. The product polygon lies
above the Minkowski sum, and convexity forces equality along the intervening face without
creating contacts outside it.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open TauCeti

namespace PowerSeries

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))
  {f g : R⟦X⟧} {σ : ℝ} {l u l' u' : ℕ}

/-- Finite Newton faces at a common slope add under multiplication, with both absolute
endpoints adding. This is a local product law: the polygons need not agree with their
Minkowski sum away from this face. No convergence hypothesis is required. -/
theorem isFiniteFace_newtonPolygon_mul
    (hf : IsFiniteFace (f.newtonPolygon v) σ l u)
    (hg : IsFiniteFace (g.newtonPolygon v) σ l' u') :
    IsFiniteFace ((f * g).newtonPolygon v) σ (l + l') (u + u') := by
  have hfa : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top
      (by simpa only [newtonPolygon_def] using hf.left_ne_top)
  have hga : IsAdmissible fun n => v (coeff n g) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top
      (by simpa only [newtonPolygon_def] using hg.left_ne_top)
  have hF := isLowerConvexEnvelope_newtonPolygon hfa
  have hG := isLowerConvexEnvelope_newtonPolygon hga
  obtain ⟨c, hc, hfl, hfu⟩ :=
    hF.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hf
  obtain ⟨d, hd, hgl, hgu⟩ :=
    hG.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hg
  have hcF : IsSupportingLine (f.newtonPolygon v) σ c :=
    isSupportingLine_iff_forall.mpr
      (hF.greatest (isConvexSeq_affine c σ) (isSupportingLine_iff_forall.mp hc))
  have hdG : IsSupportingLine (g.newtonPolygon v) σ d :=
    isSupportingLine_iff_forall.mpr
      (hG.greatest (isConvexSeq_affine d σ) (isSupportingLine_iff_forall.mp hd))
  have hprod : IsAdmissible fun n => v (coeff n (f * g)) :=
    (hc.minkowskiSum hd).isAdmissible.mono (minkowskiSum_le_addValuation_coeff_mul v)
  have hle := minkowskiSum_newtonPolygon_le_newtonPolygon_mul v hfa hga
  -- At either extreme split, the unique dominant coefficient makes the lower bound exact.
  have hend (i j : ℕ)
      (hi : i ∈ supportingFace (fun n => v (coeff n f)) σ c)
      (hj : j ∈ supportingFace (fun n => v (coeff n g)) σ d)
      (hij : v (coeff (i + j) (f * g)) = v (coeff i f) + v (coeff j g)) :
      (f * g).newtonPolygon v (i + j) =
        minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) (i + j) := by
    have hiF := hF.supportingFace_subset hc hi
    have hjG := hG.supportingFace_subset hd hj
    have hfi : f.newtonPolygon v i = v (coeff i f) :=
      (mem_supportingFace.mp hiF).trans (mem_supportingFace.mp hi).symm
    have hgj : g.newtonPolygon v j = v (coeff j g) :=
      (mem_supportingFace.mp hjG).trans (mem_supportingFace.mp hj).symm
    apply le_antisymm ?_ (hle (i + j))
    calc
      (f * g).newtonPolygon v (i + j) ≤ v (coeff (i + j) (f * g)) :=
        newtonPolygon_le hprod _
      _ = f.newtonPolygon v i + g.newtonPolygon v j := by rw [hij, hfi, hgj]
      _ = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) (i + j) :=
        (minkowskiSum_add_eq_of_mem_supportingFace hcF hiF hdG hjG).symm
  exact (hf.minkowskiSum hg).of_le_of_eq_endpoints
    (isConvexSeq_newtonPolygon (f * g) v) hle
    (hend l l' hfl.1 hgl.1 (addValuation_coeff_mul_eq_add_of_isLeast v hc hfl hd hgl))
    (hend u u' hfu.1 hgu.1 (addValuation_coeff_mul_eq_add_of_isGreatest v hc hfu hd hgu))

end PowerSeries
