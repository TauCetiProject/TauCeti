/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Translation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.InvariantTheory
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Descent
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Ascent
import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.FiniteStability
import TauCeti.RingTheory.FiniteType.FaithfullyFlatPoints

/-!
# Faithful flatness over invariants of a linearly reductive subgroup

For a geometrically reduced finite-type affine group over any field, its coordinate
algebra is faithfully flat over the functions invariant under a linearly reductive closed
subgroup. The subgroup need not be normal, smooth, or connected.

Exactness of invariants gives ideal contraction and hence lifts of closed points. Ambient
left translations act transitively on these points; generic flatness therefore propagates
to the entire invariant spectrum. Linear reductivity survives extension of the ground field,
so faithful-flat descent removes the algebraic-closedness hypothesis.

The central formal inputs are `ComoduleAlgebra.comap_map_coinvariants`, Hilbert--Nagata
finite generation, and `Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7 and 12.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  (I : HopfIdeal k H)

/-- Over an algebraically closed field, ambient left translations act transitively on
closed points of a finitely generated coinvariant algebra, provided every prime
of that algebra lifts to the ambient finite-type affine group. -/
theorem exists_coinvariantsLeftTranslation_comap_eq [IsAlgClosed k]
    [Algebra.FiniteType k H] [Algebra.FiniteType k I.coinvariants]
    (hsurj : Function.Surjective (PrimeSpectrum.comap I.coinvariants.val.toRingHom))
    (y z : PrimeSpectrum I.coinvariants) (hy : IsClosed {y}) (hz : IsClosed {z}) :
    ∃ g : WithConv (H →ₐ[k] k),
      PrimeSpectrum.comap (I.coinvariantsLeftTranslation g).toAlgHom.toRingHom y = z := by
  let : Algebra.FiniteType I.coinvariants H :=
    Algebra.FiniteType.of_restrictScalars_finiteType k I.coinvariants H
  obtain ⟨b, rfl⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k) y hy
  obtain ⟨c, rfl⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k) z hz
  have hlift := _root_.AlgHom.surjective_comp_right_of_comap_surjective (K := k)
    I.coinvariants.val (RingHom.finiteType_algebraMap.mpr inferInstance)
    hsurj
  obtain ⟨p, rfl⟩ := hlift b
  obtain ⟨q, rfl⟩ := hlift c
  refine ⟨toConv q * (toConv p)⁻¹, ?_⟩
  refine (AlgHom.comap_kernelPoint (p.comp I.coinvariants.val)
    (I.coinvariantsLeftTranslation (toConv q * (toConv p)⁻¹)).toAlgHom).trans ?_
  apply congrArg AlgHom.kernelPoint
  simpa only [Algebra.ofId_self, _root_.AlgHom.mapValue_id, MonoidHom.id_apply,
    inv_mul_cancel_right, ofConv_toConv] using
    I.comp_coinvariantsLeftTranslation (toConv q * (toConv p)⁻¹) (toConv p)

/-- The coordinate algebra of a reduced finite-type affine group over an algebraically
closed field is flat over a finitely generated coinvariant algebra, provided every prime
of the coinvariants lifts to an ambient prime. -/
theorem flat_coinvariants_of_surjective_comap [IsAlgClosed k]
    [Algebra.FiniteType k H] [_root_.IsReduced H] [Algebra.FiniteType k I.coinvariants]
    (hsurj : Function.Surjective (PrimeSpectrum.comap I.coinvariants.val.toRingHom)) :
    I.coinvariants.val.toRingHom.Flat := by
  let B := I.coinvariants
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let : Algebra.FiniteType B H := Algebra.FiniteType.of_restrictScalars_finiteType k B H
  let : _root_.IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  let : JacobsonSpace (Spec (.of B)) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp
      (isJacobsonRing_of_finiteType (A := k) (B := B))
  let f : Spec (.of H) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom B.val.toRingHom)
  let : LocallyOfFiniteType f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hflat : Flat f := by
    let a (g : WithConv (H →ₐ[k] k)) : Spec (.of H) ≅ Spec (.of H) :=
      Scheme.Spec.mapIso (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv.toCommRingCatIso.op
    let b (g : WithConv (H →ₐ[k] k)) : Spec (.of B) ≅ Spec (.of B) :=
      Scheme.Spec.mapIso (I.coinvariantsLeftTranslation g).toRingEquiv.toCommRingCatIso.op
    -- `Spec.mapIso` sends the opposite ring isomorphism to the spectrum isomorphism
    -- whose forward map is `Spec.map` of the underlying ring homomorphism.
    -- The AlgEquiv projections through `toRingEquiv` and `toAlgHom` give the same ring map.
    have ha (g : WithConv (H →ₐ[k] k)) : (a g).hom =
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv.toRingHom) := rfl
    have hb (g : WithConv (H →ₐ[k] k)) : (b g).hom =
        Spec.map (CommRingCat.ofHom
          (I.coinvariantsLeftTranslation g).toAlgHom.toRingHom) := rfl
    apply f.flat_of_transitive_closedPoints_of_finiteType a b
    · intro g
      rw [ha, hb]
      dsimp only [f]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x ↦
        (I.coe_coinvariantsLeftTranslation g x).symm)
    · intro y z hy hz
      obtain ⟨g, hg⟩ := I.exists_coinvariantsLeftTranslation_comap_eq hsurj y z hy hz
      refine ⟨g, ?_⟩
      rw [hb, AlgebraicGeometry.Spec.map_apply]
      exact hg
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hflat

/-- The coordinate algebra of a geometrically reduced finite-type affine group over
any field is faithfully flat over the invariants of a linearly reductive closed subgroup.
The subgroup need not be normal, smooth, or connected. -/
theorem faithfullyFlat_coinvariants_of_isLinearlyReductive
    [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]
    (hI : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal)) :
    I.coinvariants.val.toRingHom.FaithfullyFlat := by
  let K := AlgebraicClosure k
  let J := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  apply (CommHopfAlgCat.faithfullyFlat_coinvariants_baseChange_iff (S := K) I).mp
  have hJ : Coalgebra.IsLinearlyReductive K
      (CommHopfAlgCat.baseChange (K := K) H ⧸ J.toIdeal) := by
    exact (Coalgebra.isLinearlyReductive_iff_of_coalgEquiv K
      (CommHopfAlgCat.ofIso (CommHopfAlgCat.quotientBaseChangeIso (K := K) I)).toCoalgEquiv).mpr
      (Coalgebra.IsLinearlyReductive.baseChange K hI)
  let : Algebra.FiniteType K J.coinvariants :=
    J.finiteType_coinvariants_of_isLinearlyReductive hJ
  have hsurj := J.surjective_comap_coinvariants_of_isLinearlyReductive hJ
  exact RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    ⟨J.flat_coinvariants_of_surjective_comap hsurj, hsurj⟩

end TauCeti.HopfIdeal
