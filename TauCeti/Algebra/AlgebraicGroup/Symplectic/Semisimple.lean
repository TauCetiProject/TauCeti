/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Scalar
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive
import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Connected
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.RingTheory.FiniteType.FiniteRange
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The symplectic group is semisimple

The standard symplectic group `Sp₂ₘ` is semisimple over every field, in every rank and in every
characteristic, including characteristic two. A connected smooth normal solvable subgroup acts
by scalars on the simple standard representation. Preservation of the alternating form restricts
those scalars to square roots of one. A regular function with finite image on a reduced
connected affine scheme is constant, so the subgroup acts trivially. Faithfulness of the standard
representation identifies its defining ideal with the augmentation ideal.

The argument uses `HopfIdeal.exists_basePointsRepresentation_eq_smul`,
`eq_algebraMap_of_finite_range_eval`, and the standard symplectic comodule, following
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Semisimple` with the determinant replaced by the
alternating form. Smoothness is essential for the subgroup: this does not assert triviality of
the non-smooth connected central subgroup scheme `μ₂` in characteristic two. The rank-zero case,
where the carrier of the standard representation is a singleton, is handled separately.

## Main declarations

* `TauCeti.Symplectic.eq_augmentation_of_isNormal_of_isSolvable`: a connected reduced normal
  solvable closed subgroup of `Sp₂ₘ` over an algebraically closed field is trivial.
* `TauCeti.Symplectic.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  **`Sp₂ₘ` is semisimple over every field.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §§19.b, 21, and 24.6.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2, 2.4, and Chapter 8.

This supplies the semisimplicity half of the `Sp₂ₘ` worked example requested alongside Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti.Symplectic

open CategoryTheory WithConv
open scoped TensorProduct Matrix

universe u

noncomputable section

attribute [local instance] standardComodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every connected reduced normal solvable closed subgroup of `Sp₂ₘ` over an algebraically
closed field is trivial. Reducedness may be supplied by smoothness, but is the only subgroup
regularity needed here. -/
theorem eq_augmentation_of_isNormal_of_isSolvable
    (m : ℕ) (I : HopfIdeal k (coordinateHopfAlgebra k m)) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I)]
    [ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I →ₐ[k] k))] :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k m) := by
  let H := coordinateHopfAlgebra k m
  let Q := CommHopfAlgCat.quotient H I
  let q := (CommHopfAlgCat.mkQuotient H I).hom
  let _ : Comodule k Q (Fin (m + m) → k) := Comodule.Corestrict q.toCoalgHom
  apply Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one
    (M := Fin (m + m) → k) I (isFaithful_standardComodule k m)
  have hfixed : ∀ v : Fin (m + m) → k,
      Comodule.coact (R := k) (C := Q) v = v ⊗ₜ[k] (1 : Q) := by
    cases m with
    | zero =>
      intro v
      have hv : v = 0 := funext fun i ↦ Fin.elim0 i
      rw [hv, map_zero, TensorProduct.zero_tmul]
    | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      let _ : NeZero (n + 1 + (n + 1)) := ⟨by omega⟩
      let _ : IsReduced H := isReduced_of_smooth k H
      let _ : ConnectedSpace (PrimeSpectrum H) :=
        geometricallyConnectedCommHopfAlgProperty.connectedSpace k H
          (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k (n + 1))
      let e : Fin (n + 1 + (n + 1)) → k := Pi.single 0 1
      let φ : Module.Dual k (Fin (n + 1 + (n + 1)) → k) := LinearMap.proj 0
      let a : Q := Comodule.matrixCoefficient (R := k) (C := Q) φ e
      have hscalar (g : WithConv (Q →ₐ[k] k)) :
          ∃ c : kˣ, Comodule.basePointsRepresentation (R := k) (H := H)
            (Fin (n + 1 + (n + 1)) → k) (AlgHom.mapDomain q g) =
              (c : k) • (1 : Module.End k (Fin (n + 1 + (n + 1)) → k)) :=
        HopfIdeal.exists_basePointsRepresentation_eq_smul I hI g
      have heval (g : WithConv (Q →ₐ[k] k)) (c : kˣ)
          (hc : Comodule.basePointsRepresentation (R := k) (H := H)
            (Fin (n + 1 + (n + 1)) → k) (AlgHom.mapDomain q g) =
              (c : k) • (1 : Module.End k (Fin (n + 1 + (n + 1)) → k))) :
          g.ofConv a = (c : k) := by
        rw [Comodule.apply_matrixCoefficient, Comodule.basePointsRepresentation_corestrict q, hc]
        simp [φ, e]
      -- The scalar is a matrix coefficient; the alternating form confines its image to `±1`.
      have hfinite : (Set.range fun f : Q →ₐ[k] k ↦ f a).Finite := by
        apply (Polynomial.nthRootsFinset 2 (1 : k)).finite_toSet.subset
        rintro _ ⟨f, rfl⟩
        obtain ⟨c, hc⟩ := hscalar (toConv f)
        rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset two_pos]
        exact (congrArg (fun z : k ↦ z ^ 2) (heval (toConv f) c hc)).trans
          (scalar_sq_eq_one_of_basePointsRepresentation_eq_smul k (n + 1) (Nat.succ_ne_zero n)
            (AlgHom.mapDomain q (toConv f)) c hc)
      -- Connectedness makes the finite-image coefficient constant, with value one at the identity.
      have ha : a = algebraMap k Q (1 : k) := by
        have h := eq_algebraMap_of_finite_range_eval a hfinite (1 : WithConv (Q →ₐ[k] k)).ofConv
        have hidentity : (1 : WithConv (Q →ₐ[k] k)).ofConv a = 1 := by
          rw [Comodule.apply_matrixCoefficient, map_one]
          simp [φ, e]
        simpa only [hidentity] using h
      intro v
      apply (Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq v).mpr
      intro g
      obtain ⟨c, hc⟩ := hscalar g
      have hc1 : (c : k) = 1 := by
        rw [← heval g c hc, ha]
        simp
      rw [Comodule.basePointsRepresentation_corestrict q, hc, hc1]
      simp
  intro v
  simpa only [Comodule.corestrict_coact_apply] using hfixed v

/-- **The symplectic group is semisimple over every field and in every rank.** -/
theorem semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (m : ℕ) :
    semisimpleCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k m) := by
  have hred := reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k m
  let K := AlgebraicClosure k
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra k m)
  let G := coordinateHopfAlgebra K m
  let e : B.obj ≅ G :=
    (forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K m) ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K m)
  apply semisimpleCommHopfAlgProperty_of_geometricFiber_iso k _ G
    hred.smooth hred.geometricallyConnected e
  intro I hnormal hconnected hsmooth hsolvable
  let _ : Algebra.Smooth K (CommHopfAlgCat.quotient G I) := hsmooth
  let _ : IsReduced (CommHopfAlgCat.quotient G I) := isReduced_of_smooth K _
  let _ : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G I)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace K _ hconnected
  let _ : Group.IsSolvable
      (WithConv (CommHopfAlgCat.quotient G I →ₐ[K] AlgebraicClosure K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff K _).mp hsolvable
  let φ : K →ₐ[K] AlgebraicClosure K := Algebra.ofId K (AlgebraicClosure K)
  let _ : Group.IsSolvable (WithConv (CommHopfAlgCat.quotient G I →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (AlgHom.mapValue_injective φ.injective)
  exact eq_augmentation_of_isNormal_of_isSolvable m I hnormal

end

end TauCeti.Symplectic
