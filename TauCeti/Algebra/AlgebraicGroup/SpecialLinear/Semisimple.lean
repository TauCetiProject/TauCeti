/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Scalar
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The special linear group is semisimple

The group `SL_n` is semisimple over every field, including in characteristics dividing `n`.
A connected smooth normal solvable subgroup acts by scalars on the simple standard
representation. Determinant one restricts those scalars to the finite set of `n`th roots
of unity. A regular function with finite image on a reduced connected affine scheme is
constant, so the subgroup acts trivially. Faithfulness of the standard representation
identifies its defining ideal with the augmentation ideal.

The argument uses `HopfIdeal.exists_basePointsRepresentation_eq_smul`,
`eq_algebraMap_of_finite_range_eval`, and the standard special-linear comodule. Smoothness
is essential for the subgroup: this does not assert triviality of non-smooth connected
central subgroup schemes such as `μ_p` in `SL_p`. The zero-rank case uses the faithful
zero-dimensional representation separately.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 21.
-/

public section

namespace TauCeti.SpecialLinear

open CategoryTheory WithConv
open scoped TensorProduct Matrix

universe u

noncomputable section

attribute [local instance] standardComodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every connected reduced normal solvable closed subgroup of `SL_n` over an algebraically
closed field is trivial. Reducedness may be supplied by smoothness, but is the only subgroup
regularity needed here. -/
theorem eq_augmentation_of_isNormal_of_isSolvable
    (n : ℕ) (I : HopfIdeal k (coordinateHopfAlgebra k n)) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I →ₐ[k] k))] :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) := by
  let H := coordinateHopfAlgebra k n
  let Q := CommHopfAlgCat.quotient H I
  let q := (CommHopfAlgCat.mkQuotient H I).hom
  let _ : Comodule k Q (Fin n → k) := Comodule.Corestrict q.toCoalgHom
  apply Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one
    (M := Fin n → k) I (isFaithful_standardComodule k n)
  have hfixed : ∀ v : Fin n → k, Comodule.coact (R := k) (C := Q) v = v ⊗ₜ[k] (1 : Q) := by
    cases n with
    | zero =>
      intro v
      have hv : v = 0 := Subsingleton.elim _ _
      rw [hv, map_zero, TensorProduct.zero_tmul]
    | succ m =>
      let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      let _ : IsReduced H := isReduced_of_smooth k H
      let _ : ConnectedSpace (PrimeSpectrum H) :=
        geometricallyConnectedCommHopfAlgProperty.connectedSpace k H
          (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k (m + 1))
      let e : Fin (m + 1) → k := Pi.single 0 1
      let φ : Module.Dual k (Fin (m + 1) → k) := LinearMap.proj 0
      let a : Q := Comodule.matrixCoefficient (R := k) (C := Q) φ e
      have hscalar (g : WithConv (Q →ₐ[k] k)) :
          ∃ c : kˣ, Comodule.basePointsRepresentation (R := k) (H := H)
            (Fin (m + 1) → k) (AlgHom.mapDomain q g) =
              (c : k) • (1 : Module.End k (Fin (m + 1) → k)) :=
        HopfIdeal.exists_basePointsRepresentation_eq_smul I hI g
      have heval (g : WithConv (Q →ₐ[k] k)) (c : kˣ)
          (hc : Comodule.basePointsRepresentation (R := k) (H := H)
            (Fin (m + 1) → k) (AlgHom.mapDomain q g) =
              (c : k) • (1 : Module.End k (Fin (m + 1) → k))) :
          g.ofConv a = (c : k) := by
        rw [Comodule.apply_matrixCoefficient, Comodule.basePointsRepresentation_corestrict q, hc]
        simp [φ, e]
      -- The scalar is a matrix coefficient; determinant one confines its image to roots of unity.
      have hfinite : (Set.range fun f : Q →ₐ[k] k ↦ f a).Finite := by
        apply (Polynomial.nthRootsFinset (m + 1) (1 : k)).finite_toSet.subset
        rintro _ ⟨f, rfl⟩
        obtain ⟨c, hc⟩ := hscalar (toConv f)
        rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Nat.succ_pos m)]
        exact (congrArg (fun z : k ↦ z ^ (m + 1)) (heval (toConv f) c hc)).trans
          (scalar_pow_eq_one_of_basePointsRepresentation_eq_smul
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

/-- **The special linear group is semisimple over every field and in every rank.** -/
theorem semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    semisimpleCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  have hred := reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n
  let K := AlgebraicClosure k
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra k n)
  let G := coordinateHopfAlgebra K n
  let e : B.obj ≅ G :=
    (forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K n) ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n)
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
  exact eq_augmentation_of_isNormal_of_isSolvable n I hnormal

end

end TauCeti.SpecialLinear
