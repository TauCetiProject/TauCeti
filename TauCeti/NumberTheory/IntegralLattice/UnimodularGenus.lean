/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.NumberTheory.IntegralLattice.DiscriminantGenus

/-!
# The genus of unimodular lattices

Evenness is a genus invariant (`TauCeti.IntegralLattice.SameGenus.isEven_iff`), since it is
detected by the dyadic localization. For unimodular lattices it is, together with the signature,
a complete invariant of the genus: two unimodular lattices lie in one genus exactly when they have
the same signature and are both even or both odd.

This follows directly from the odd-discriminant genus classification
(`TauCeti.IntegralLattice.sameGenus_iff_of_odd_discriminant`): a unimodular lattice has
discriminant `1` (hence odd) and a trivial discriminant bilinear module, so any two unimodular
lattices have isometric discriminant bilinear modules. For instance, if `p + q ≥ 1`, the odd
unimodular lattices of signature `(p, 0, q)` form the single genus of
`I_{p,q} = ⟨1⟩ ^ p ⊕ ⟨-1⟩ ^ q`.

## Main results

* `TauCeti.IntegralLattice.sameGenus_iff_of_isUnimodular`: unimodular lattices lie in one genus
  exactly when their signatures agree and they are even together.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

/-- **The genus of a unimodular lattice.** Two unimodular lattices lie in one genus exactly when
their signatures agree and they are both even or both odd. -/
theorem sameGenus_iff_of_isUnimodular (hLu : L.IsUnimodular) (hMu : M.IsUnimodular) :
    L.SameGenus M ↔ L.signature = M.signature ∧ (L.IsEven ↔ M.IsEven) := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  have : M.IsNondegenerate := ⟨hMu.nondegenerate⟩
  have hodd : Odd L.discriminant := by
    rw [L.isUnimodular_iff_discriminant_eq_one.mp hLu]
    exact odd_one
  have : Subsingleton L.discriminantBilinearModule :=
    L.subsingleton_discriminantBilinearModule_iff.mpr
      (L.isUnimodular_iff_subsingleton_discriminantGroup.mp hLu)
  have : Subsingleton M.discriminantBilinearModule :=
    M.subsingleton_discriminantBilinearModule_iff.mpr
      (M.isUnimodular_iff_subsingleton_discriminantGroup.mp hMu)
  have hiso : FiniteBilinearModule.Isometry
      L.discriminantBilinearModule M.discriminantBilinearModule :=
    { toAddEquiv :=
        { toFun := 0
          invFun := 0
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _
          map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
      map_pairing' := fun x _ ↦ by
        rw [Subsingleton.elim x 0, FiniteBilinearModule.pairing_zero_left]
        simp }
  rw [L.sameGenus_iff_of_odd_discriminant M hodd]
  exact ⟨fun ⟨hsig, heven, _⟩ ↦ ⟨hsig, heven⟩, fun ⟨hsig, heven⟩ ↦ ⟨hsig, heven, ⟨hiso⟩⟩⟩

end TauCeti.IntegralLattice
