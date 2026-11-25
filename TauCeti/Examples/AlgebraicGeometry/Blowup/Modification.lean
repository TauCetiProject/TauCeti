/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Blowup.Modification

/-!
# Examples: the blowup of the affine plane at the origin is a modification

On `𝔸²_k = Spec k[x, y]` the ideal `(x, y)` of the origin has support a single closed point, which
is not the whole plane: the generic point `(0)` does not contain `x`. Since `𝔸²_k` is irreducible
and Noetherian, the blowup at the origin is a modification, and its centre lies in the origin.
-/

public section

open AlgebraicGeometry MvPolynomial TauCeti.AlgebraicGeometry

namespace TauCeti.BlowupModificationExample

variable (k : Type) [Field k]

/-- The ideal sheaf of the origin `(x, y)` of the affine plane `Spec k[x, y]`. -/
noncomputable def originIdealSheaf : (Spec (.of (MvPolynomial (Fin 2) k))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {X 0, X 1}).map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom)

/-- The support of the ideal sheaf of the origin is not the whole plane. -/
theorem support_originIdealSheaf_ne_top : (originIdealSheaf k).support ≠ ⊤ := by
  -- The generic point `(0)` would lie in the support, so `(0)` would contain `x`.
  intro h
  have hmem : (⊥ : PrimeSpectrum (MvPolynomial (Fin 2) k)) ∈ ((originIdealSheaf k).support :
      Set (Spec (.of (MvPolynomial (Fin 2) k)))) := h ▸ trivial
  simp only [originIdealSheaf, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Spec_zeroLocus] at hmem
  simpa using (PrimeSpectrum.mem_zeroLocus _ _).1 hmem
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_insert (X 0) {X 1})))

-- The blowup of `𝔸²_k` at the origin is a modification.
example : IsModification (originIdealSheaf k).blowupToBase :=
  Scheme.IdealSheafData.isModification_blowupToBase_of_irreducibleSpace
    (support_originIdealSheaf_ne_top k)

-- Its centre lies in the origin.
example : (originIdealSheaf k).blowupToBase.centre ⊆ (originIdealSheaf k).support :=
  Scheme.IdealSheafData.centre_blowupToBase_subset

end TauCeti.BlowupModificationExample
