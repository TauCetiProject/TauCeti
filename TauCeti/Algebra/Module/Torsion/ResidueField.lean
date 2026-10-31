/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Essential
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Ideal-power torsion in essential extensions of a residue field

Every essential extension of the residue field of a commutative Noetherian local ring is
the union of its submodules annihilated by powers of the maximal ideal. In particular this
holds for the injective hull. This lets the adic completion act through its residues, without
requiring completeness of the ring or finiteness of the residue field.

The proof applies `TauCeti.IsEssential.primaryComponent_eq_top` to the image of the residue
field. For an injective envelope, its `isEssential_range` field supplies the hypothesis;
injectivity of the ambient module is not needed.

## References

* The Stacks Project, Lemma 47.7.3, Tag 08Z4.
-/

public section

namespace TauCeti

open IsLocalRing Submodule

variable {R E : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup E] [Module R E]

/-- An essential extension of a residue field over a Noetherian local ring is
maximal-ideal-power torsion. Each element has its own annihilating power. -/
theorem IsEssential.primaryComponent_maximalIdeal_eq_top
    {ι : ResidueField R →ₗ[R] E} (hι : IsEssential (LinearMap.range ι)) :
    (maximalIdeal R).primaryComponent E = ⊤ := by
  apply hι.primaryComponent_eq_top
  rintro _ ⟨x, rfl⟩
  refine ((maximalIdeal R).primaryComponent_mem E (ι x)).mpr ⟨1, ?_⟩
  rw [mem_torsionBySet_iff]
  intro r
  have hr : residue R (r : R) = 0 := (residue_eq_zero_iff _).mpr (by simpa using r.prop)
  rw [← map_smul]
  simp [Algebra.smul_def, hr]

end TauCeti
