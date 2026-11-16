/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.LinearAlgebra.Orientation.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.LinearAlgebra.Dimension.Prod
import TauCeti.Topology.Algebra.Module.Equiv.Prod

/-!
# Ordered products of local orientations of vector spaces

For a real normed space `E` of dimension `m + 1`, the integral orientation line of `E` is the
local homology group `o_E = Hₘ₊₁(E, E ∖ {0}; ℤ)`, free of rank one, and its two generators are
the local orientations of `E` at the origin. By `Orientation.localOrientationEquiv` they
correspond to the two orientations of `E`. This file defines the ordered product of a local
orientation of `E` and one of `F`, a local orientation of `E × F`
(`TauCeti.LocalOrientation.prod`): it is the local orientation selected by the product
orientation `Orientation.prod`, which lists a basis of `E` before a basis of `F`. It is the
generator-level form of the ordered identification `o_E ⊗ o_F ≅ o_{E × F}` of orientation lines.

The product has the laws of that identification.

* It is bilinear in signs: reversing either factor reverses the product
  (`TauCeti.LocalOrientation.prod_neg_left`, `TauCeti.LocalOrientation.prod_neg_right`).
* It is natural: the product of the transports along continuous linear equivalences `f` and `g`
  is the transport of the product along `f × g`
  (`TauCeti.LocalOrientation.prod_map_complZeroPairIso`).
* Exchanging the factors acts by the Koszul sign `(-1) ^ ((m + 1) * (n + 1))`
  (`TauCeti.LocalOrientation.coe_map_prodComm_prod`): transport along the exchange
  `E × F ≃ F × E` carries `z × z'` to `(-1) ^ ((m + 1) * (n + 1)) • (z' × z)`, where `m + 1` and
  `n + 1` are the dimensions of `E` and `F` (`TauCeti.LocalOrientation.map_prodComm_prod_of_even`,
  `TauCeti.LocalOrientation.map_prodComm_prod_of_odd`). For `E = F = ℝ` this is `-1`, the sign
  of the exchange of two odd lines.
* It is associative: transport along `(E × F) × G ≃ E × (F × G)` carries `(z × z') × z''` to
  `z × (z' × z'')` (`TauCeti.LocalOrientation.map_prodAssoc_prod`).

The degree of the product is written `d + 1` together with a proof of `(m + 1) + (n + 1) = d + 1`,
so that exchanged and reassociated products live in the same local homology group. The factors
have positive dimension, as `Orientation.localOrientation` requires; their finite dimensionality
follows from the dimension hypotheses.

## Main definitions

* `TauCeti.LocalOrientation.prod`: the ordered product of local orientations of `E` and `F` at
  the origin.

## Main results

* `TauCeti.LocalOrientation.prod_localOrientation`: the product of the local orientations
  selected by `ω` and `ω'` is the local orientation selected by the product orientation.
* `TauCeti.LocalOrientation.coe_map_prodComm_prod`: the exchange sign
  `(-1) ^ ((m + 1) * (n + 1))`.
* `TauCeti.LocalOrientation.map_prodAssoc_prod`: associativity.
* `TauCeti.LocalOrientation.prod_map_complZeroPairIso`: naturality.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Definition 4.1.1 and Appendix A.0
  (orientation lines and the ordering of their tensor products).
* A. Hatcher, *Algebraic Topology*, Section 3.3 (local orientations).
-/

public section

noncomputable section

open Module

universe w

namespace TauCeti.LocalOrientation

variable {E F G E' F' : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {m n p d : ℕ}

/-- **The ordered product of local orientations.** For local orientations `z` of `E` and `z'` of
`F` at the origin, their product `z × z'` is the local orientation of `E × F` at the origin
selected by the product of the orientations selecting `z` and `z'`, the first factor before the
second. Its degree is written `d + 1` with `(m + 1) + (n + 1) = d + 1`. -/
def prod (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1) (hd : m + 1 + (n + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    LocalOrientation (E × F) 0 (d + 1) :=
  haveI := FiniteDimensional.of_finrank_eq_succ hE
  haveI := FiniteDimensional.of_finrank_eq_succ hF
  (Orientation.reindex ℝ (E × F) (finCongr hd)
    (((Orientation.localOrientationEquiv hE).symm z).prod
      ((Orientation.localOrientationEquiv hF).symm z') hE hF)).localOrientation
    (finrank_prod_eq_succ hE hF hd)

/-- The product of the local orientations selected by `ω` and `ω'` is the local orientation
selected by their product orientation. -/
@[simp]
theorem prod_localOrientation (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (ω : Orientation ℝ E (Fin (m + 1)))
    (ω' : Orientation ℝ F (Fin (n + 1))) :
    prod hE hF hd (ω.localOrientation hE) (ω'.localOrientation hF) =
      haveI := FiniteDimensional.of_finrank_eq_succ hE
      haveI := FiniteDimensional.of_finrank_eq_succ hF
      (Orientation.reindex ℝ (E × F) (finCongr hd) (ω.prod ω' hE hF)).localOrientation
        (finrank_prod_eq_succ hE hF hd) := by
  rw [prod, Orientation.localOrientationEquiv_symm_localOrientation,
    Orientation.localOrientationEquiv_symm_localOrientation]

/-- Reversing the first factor reverses the product. -/
@[simp]
theorem prod_neg_left (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) : prod hE hF hd (-z) z' = -prod hE hF hd z z' := by
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hE z
  obtain ⟨ω', rfl⟩ := Orientation.localOrientation_surjective hF z'
  simp only [← Orientation.localOrientation_neg, prod_localOrientation, Orientation.prod_neg_left,
    Orientation.reindex_neg]

/-- Reversing the second factor reverses the product. -/
@[simp]
theorem prod_neg_right (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) : prod hE hF hd z (-z') = -prod hE hF hd z z' := by
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hE z
  obtain ⟨ω', rfl⟩ := Orientation.localOrientation_surjective hF z'
  simp only [← Orientation.localOrientation_neg, prod_localOrientation, Orientation.prod_neg_right,
    Orientation.reindex_neg]

/-- **Naturality of the product.** Transporting the factors along continuous linear equivalences
`f` and `g` transports the product along `f × g`. -/
theorem prod_map_complZeroPairIso (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hE' : finrank ℝ E' = m + 1) (hF' : finrank ℝ F' = n + 1) (hd : m + 1 + (n + 1) = d + 1)
    (f : E ≃L[ℝ] E') (g : F ≃L[ℝ] F') (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    prod hE' hF' hd (z.map f.complZeroPairIso) (z'.map g.complZeroPairIso) =
      (prod hE hF hd z z').map (f.prodCongr g).complZeroPairIso := by
  have := FiniteDimensional.of_finrank_eq_succ hE
  have := FiniteDimensional.of_finrank_eq_succ hF
  have := FiniteDimensional.of_finrank_eq_succ hE'
  have := FiniteDimensional.of_finrank_eq_succ hF'
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hE z
  obtain ⟨ω', rfl⟩ := Orientation.localOrientation_surjective hF z'
  simp only
  rw [← Orientation.localOrientation_map f ω hE hE', ← Orientation.localOrientation_map g ω' hF hF',
    prod_localOrientation, prod_localOrientation,
    ← Orientation.localOrientation_map _ _ (finrank_prod_eq_succ hE hF hd)
      (finrank_prod_eq_succ hE' hF' hd)]
  congr 1
  rw [Orientation.map_reindex, ContinuousLinearEquiv.prodCongr_toLinearEquiv, Orientation.map_prod]

/-- **The exchange sign.** Transport along the exchange `E × F ≃ F × E` carries the product of
local orientations `z` of `E` and `z'` of `F` to `(-1) ^ ((m + 1) * (n + 1))` times the product of
`z'` and `z`, as classes in local homology. -/
theorem coe_map_prodComm_prod (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (hd' : n + 1 + (m + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    ((prod hE hF hd z z').map (ContinuousLinearEquiv.prodComm ℝ E F).complZeroPairIso).val =
      (-1 : ℤ) ^ ((m + 1) * (n + 1)) • (prod hF hE hd' z' z).val := by
  have := FiniteDimensional.of_finrank_eq_succ hE
  have := FiniteDimensional.of_finrank_eq_succ hF
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hE z
  obtain ⟨ω', rfl⟩ := Orientation.localOrientation_surjective hF z'
  simp only
  rw [prod_localOrientation, prod_localOrientation,
    ← Orientation.localOrientation_map _ _ (finrank_prod_eq_succ hE hF hd)
      (finrank_prod_eq_succ hF hE hd'),
    Orientation.map_reindex, ContinuousLinearEquiv.prodComm_toLinearEquiv,
    Orientation.map_prodComm_prod, Orientation.reindex_units_smul,
    Orientation.reindex_finCongr_reindex_finCongr]
  rcases Nat.even_or_odd ((m + 1) * (n + 1)) with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_smul]
  · rw [h.neg_one_pow, h.neg_one_pow, Module.Ray.neg_units_smul, one_smul,
      Orientation.localOrientation_neg, coe_neg, neg_one_zsmul]

/-- If the product `(m + 1) * (n + 1)` of the dimensions is even, transport along the exchange
`E × F ≃ F × E` carries `z × z'` to `z' × z`. -/
theorem map_prodComm_prod_of_even (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (hd' : n + 1 + (m + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1))
    (h : Even ((m + 1) * (n + 1))) :
    (prod hE hF hd z z').map (ContinuousLinearEquiv.prodComm ℝ E F).complZeroPairIso =
      prod hF hE hd' z' z :=
  Subtype.ext (by rw [coe_map_prodComm_prod hE hF hd hd', h.neg_one_pow, one_zsmul])

/-- If the product `(m + 1) * (n + 1)` of the dimensions is odd, for instance for `E = F = ℝ`,
transport along the exchange `E × F ≃ F × E` carries `z × z'` to `-(z' × z)`. -/
theorem map_prodComm_prod_of_odd (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (hd' : n + 1 + (m + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1))
    (h : Odd ((m + 1) * (n + 1))) :
    (prod hE hF hd z z').map (ContinuousLinearEquiv.prodComm ℝ E F).complZeroPairIso =
      -prod hF hE hd' z' z :=
  Subtype.ext (by rw [coe_map_prodComm_prod hE hF hd hd', h.neg_one_pow, neg_one_zsmul, coe_neg])

/-- **Associativity of the product.** Transport along `(E × F) × G ≃ E × (F × G)` carries the
product `(z × z') × z''` to `z × (z' × z'')`. -/
theorem map_prodAssoc_prod {e f : ℕ} (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hG : finrank ℝ G = p + 1) (he : m + 1 + (n + 1) = e + 1) (hf : n + 1 + (p + 1) = f + 1)
    (hd : e + 1 + (p + 1) = d + 1) (he' : m + 1 + (f + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1))
    (z'' : LocalOrientation G 0 (p + 1)) :
    (prod (finrank_prod_eq_succ hE hF he) hG hd (prod hE hF he z z') z'').map
        (ContinuousLinearEquiv.prodAssoc ℝ E F G).complZeroPairIso =
      prod hE (finrank_prod_eq_succ hF hG hf) he' z (prod hF hG hf z' z'') := by
  have := FiniteDimensional.of_finrank_eq_succ hE
  have := FiniteDimensional.of_finrank_eq_succ hF
  have := FiniteDimensional.of_finrank_eq_succ hG
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hE z
  obtain ⟨ω', rfl⟩ := Orientation.localOrientation_surjective hF z'
  obtain ⟨ω'', rfl⟩ := Orientation.localOrientation_surjective hG z''
  simp only
  rw [prod_localOrientation, prod_localOrientation, prod_localOrientation, prod_localOrientation,
    ← Orientation.localOrientation_map _ _
      (finrank_prod_eq_succ (finrank_prod_eq_succ hE hF he) hG hd)
      (finrank_prod_eq_succ hE (finrank_prod_eq_succ hF hG hf) he')]
  congr 1
  rw [Orientation.prod_reindex_finCongr_left, Orientation.prod_reindex_finCongr_right,
    Orientation.map_reindex, Orientation.map_reindex, ContinuousLinearEquiv.prodAssoc_toLinearEquiv,
    Orientation.map_prodAssoc_prod]
  simp only [Orientation.reindex_finCongr_reindex_finCongr]

end TauCeti.LocalOrientation
