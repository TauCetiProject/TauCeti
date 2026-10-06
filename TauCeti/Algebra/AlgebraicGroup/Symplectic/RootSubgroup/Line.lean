/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.RootLine
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Differential

/-!
# Recognition of symplectic root-subgroup tangent images

A tangent vector belongs to the image of a represented symplectic root subgroup
exactly when its matrix vanishes outside that root's integral support. This turns
an entrywise support calculation into membership in the actual scheme-theoretic
root-subgroup differential, over arbitrary coefficient algebras.

The construction combines `RootSubgroupIndex.existsUnique_eq_tangentMatrix_iff`
with `Symplectic.range_derivationCompLieHom_rootSubgroup_eq_span`. Its normalization
is the existing `Symplectic.rootVector`, rather than a separately chosen Lie vector.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

namespace TauCeti.Symplectic

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {m : ℕ}

/-- The root-subgroup tangent image is cut out by vanishing outside the integral
root-matrix support, without any restriction on characteristic or reducedness. -/
theorem mem_range_derivationCompLieHom_rootSubgroup_iff
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B)) :
    d ∈ (derivationCompLieHom (B := B) (rootSubgroupCoordinateMap (R := R) root).hom).range ↔
      ∀ a b, root.tangentMatrix (1 : ℤ) a b = 0 →
        (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) a b = 0 := by
  rw [← LieSubalgebra.mem_toSubmodule, range_derivationCompLieHom_rootSubgroup_eq_span,
    Submodule.mem_span_singleton]
  have hscalar (c : B) :
      (tangentMatrix m (c • rootVector (R := R) (B := B) root) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) = root.tangentMatrix c := by
    rw [map_smul, SetLike.val_smul, tangentMatrix_rootVector,
      ← map_smul, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨c, rfl⟩ a b h
    rw [hscalar]
    exact root.tangentMatrix_apply_eq_zero_of_int_eq_zero c a b h
  · intro hs
    obtain ⟨c, hc, _⟩ := (root.existsUnique_eq_tangentMatrix_iff
      (tangentMatrix m d).property).mpr hs
    refine ⟨c, ?_⟩
    apply (tangentLieEquivSp (R := R) (B := B) m).injective
    apply Subtype.ext
    simpa only [LieEquiv.coe_toLieHom, tangentLieEquivSp_apply (R := R) (B := B),
      hscalar] using hc.symm

end TauCeti.Symplectic
