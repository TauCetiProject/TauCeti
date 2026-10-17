/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Translation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.InvariantTheory
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance
import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints

/-!
# Faithful flatness over invariants of a linearly reductive subgroup

For a reduced finite-type affine group over an algebraically closed field, its coordinate
algebra is faithfully flat over the functions invariant under a linearly reductive closed
subgroup. The subgroup need not be normal, smooth, or connected.

Exactness of invariants gives ideal contraction and hence lifts of closed points. Ambient
left translations act transitively on these points; generic flatness therefore propagates
to the entire invariant spectrum. This supplies the flatness input to the affine homogeneous
quotient construction, independently of the equation identifying its fibres as subgroup cosets.

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

/-- Over an algebraically closed field, every closed point of the invariant spectrum
lifts to a rational point of the ambient group. -/
theorem exists_kernelPoint_comap_coinvariants_eq [IsAlgClosed k] [Algebra.FiniteType k H]
    (hI : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal))
    (p : PrimeSpectrum I.coinvariants) (hp : IsClosed {p}) :
    ∃ a : H →ₐ[k] k, PrimeSpectrum.comap I.coinvariants.val.toRingHom
      (AlgHom.kernelPoint a) = p := by
  have hpmax := p.isClosed_singleton_iff_isMaximal.mp hp
  have hproper : p.asIdeal.map I.coinvariants.val.toRingHom ≠ ⊤ := by
    intro heq
    have hc := I.comap_map_coinvariants_of_isLinearlyReductive hI p.asIdeal
    rw [heq, Ideal.comap_top] at hc
    exact hpmax.ne_top hc.symm
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_le_maximal _ hproper
  obtain ⟨a, ha⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k)
    ⟨Q, hQmax.isPrime⟩ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hQmax)
  refine ⟨a, ?_⟩
  rw [ha]
  exact PrimeSpectrum.ext (hpmax.eq_of_le
    (Ideal.comap_ne_top _ hQmax.ne_top) (Ideal.map_le_iff_le_comap.mp hQ)).symm

/-- The coordinate algebra of a reduced finite-type affine group over an algebraically
closed field is faithfully flat over the invariants of a linearly reductive closed subgroup. -/
theorem faithfullyFlat_coinvariants_of_isLinearlyReductive [IsAlgClosed k]
    [Algebra.FiniteType k H] [_root_.IsReduced H]
    (hI : Coalgebra.IsLinearlyReductive.{u, u, u} k (H ⧸ I.toIdeal)) :
    I.coinvariants.val.toRingHom.FaithfullyFlat := by
  let B := I.coinvariants
  let : Algebra.FiniteType k B := I.finiteType_coinvariants_of_isLinearlyReductive hI
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
    have ha (g : WithConv (H →ₐ[k] k)) : (a g).hom =
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv.toRingHom) := rfl
    have hb (g : WithConv (H →ₐ[k] k)) : (b g).hom =
        Spec.map (CommRingCat.ofHom
          (I.coinvariantsLeftTranslation g).toRingEquiv.toRingHom) := rfl
    apply f.flat_of_transitive_closedPoints_of_finiteType a b
    · intro g
      rw [ha, hb]
      dsimp only [f]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun x ↦
        (I.coe_coinvariantsLeftTranslation g x).symm)
    · intro y z hy hz
      obtain ⟨p, hp⟩ := I.exists_kernelPoint_comap_coinvariants_eq hI y hy
      obtain ⟨q, hq⟩ := I.exists_kernelPoint_comap_coinvariants_eq hI z hz
      have hp' : AlgHom.kernelPoint (p.comp I.coinvariants.val) = y :=
        (AlgHom.comap_kernelPoint p I.coinvariants.val).symm.trans hp
      have hq' : AlgHom.kernelPoint (q.comp I.coinvariants.val) = z :=
        (AlgHom.comap_kernelPoint q I.coinvariants.val).symm.trans hq
      let g := toConv q * (toConv p)⁻¹
      refine ⟨g, ?_⟩
      rw [← hp', ← hq', hb, AlgebraicGeometry.Spec.map_apply]
      refine (AlgHom.comap_kernelPoint (p.comp I.coinvariants.val)
        (I.coinvariantsLeftTranslation g).toAlgHom).trans ?_
      have h := congrArg AlgHom.kernelPoint
        (I.comp_coinvariantsLeftTranslation g (toConv p))
      -- The kernel-point API uses the scheme carrier, while Spec.map_apply uses the
      -- underlying prime spectrum; conversion aligns these presentations before simplification.
      convert! h using 1
      simp [g]
      rfl
  apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
  exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mp hflat,
    I.surjective_comap_coinvariants_of_isLinearlyReductive hI⟩

end TauCeti.HopfIdeal
