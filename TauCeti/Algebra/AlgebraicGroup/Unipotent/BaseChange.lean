/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.AlgebraicGroup.Smooth.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.Character
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Geometric unipotence under base change

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field `k`, and let
`K / k` be an arbitrary field extension. Smooth geometric unipotence of `H` is both preserved and
reflected by passing to the scalar extension `K ⊗[k] H`.

Choose a faithful finite-dimensional `H`-comodule and extend it to `K`. Its coordinate morphism
remains surjective, hence the extended comodule is faithful, while smoothness is preserved by base
change and reflected by faithfully flat scalar extension. The universal coefficient matrix of the
extended comodule is obtained from the original one along the injective inclusion
`H → K ⊗[k] H`. Its characteristic polynomial is therefore a power of `X - 1` over `K ⊗[k] H`
if and only if the original characteristic polynomial is a power of `X - 1` over `H`, and the
faithful-representation criterion detects unipotence of geometric points on both sides.

Without smoothness or finite-type assumptions, geometric-point unipotence alone is reflected by
scalar extension: choosing a `k`-embedding `AlgebraicClosure k →ₐ[k] AlgebraicClosure K`,
postcomposition and the base-change adjunction on points transfer unipotence back from `K ⊗[k] H`
via `IsUnipotentPoint.of_baseChangePointsMulEquiv`.

## Main declarations

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.of_baseChange`: geometric-point
  unipotence is reflected by arbitrary field extensions.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.baseChange`: smooth geometric unipotence is
  preserved by arbitrary field extension.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.of_baseChange`: smooth geometric unipotence is
  reflected by arbitrary field extension.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.baseChange_iff`: smooth geometric unipotence is
  invariant under arbitrary field extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.5.
* A. Borel, *Linear Algebraic Groups*, Section 15.4.
-/

public section

open CategoryTheory Module WithConv
open scoped TensorProduct

namespace TauCeti

universe u v

noncomputable section

namespace geometricallyUnipotentPointsCommHopfAlgProperty

/-- Geometric-point unipotence is reflected by arbitrary extension of the ground field, without
finite-type or reducedness assumptions. -/
theorem of_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hH ⊢
  intro g
  let ι : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  apply (HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective g ι ι.injective).mp
  exact HopfAlgebra.IsUnipotentPoint.of_baseChangePointsMulEquiv (K := K) (hH _)

end geometricallyUnipotentPointsCommHopfAlgProperty

open geometricallyUnipotentPointsCommHopfAlgProperty

namespace smoothUnipotentCommHopfAlgProperty

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- For a smooth finite-type commutative Hopf algebra `H`, unipotence of all geometric points is
equivalent before and after scalar extension along `K / k`: a faithful finite-dimensional
`H`-comodule remains faithful after base change to `K`, and its universal `(X - 1) ^ d`
characteristic-polynomial identity is preserved and reflected by
`Comodule.coefficientMatrix_baseChange_charpoly_eq_iff`. -/
private theorem forall_isUnipotentPoint_baseChange_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : Algebra.Smooth k H) :
    (∀ g : WithConv (FiniteTypeCommHopfAlgCat.baseChange (K := K) H →ₐ[K] AlgebraicClosure K),
        HopfAlgebra.IsUnipotentPoint g) ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k), HopfAlgebra.IsUnipotentPoint g := by
  let _ : Algebra.Smooth k H := hH
  let _ : IsReduced H := isReduced_of_smooth k H
  let _ : IsReduced (K ⊗[k] H) := isReduced_of_smooth K (K ⊗[k] H)
  obtain ⟨M, d, b, hb⟩ := Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom
    (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k M := Module.Free.of_basis b
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hM : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).2 hb
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let bK := b.baseChange K
  let _ : Module.Free K (K ⊗[k] M) := Module.Free.of_basis bK
  let _ : Module.Finite K (K ⊗[k] M) := Module.Finite.of_basis bK
  let p : Polynomial k := (Polynomial.X - 1) ^ Module.finrank k M
  have hpK : p.map (algebraMap k K) =
      (Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M) := by
    simp [p]
  constructor
  · intro hHK g
    have hC : (Comodule.coefficientMatrix (C := H) b).charpoly = p.map (algebraMap k H) := by
      rw [← Comodule.coefficientMatrix_baseChange_charpoly_eq_iff (A := K) b p, hpK]
      simpa only using
        (geometricallyUnipotentPointsCommHopfAlgProperty.coefficientMatrix_charpoly_eq
          ((geometricallyUnipotentPointsCommHopfAlgProperty_iff K _).mpr hHK)
          (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)) bK)
    exact (HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
      (FGComoduleCat.of (R := k) (C := H) M) hM g).2
      (Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq g b hC)
  · intro hHk g
    have hCK : (Comodule.coefficientMatrix (C := K ⊗[k] H) bK).charpoly =
        ((Polynomial.X - (1 : Polynomial K)) ^ Module.finrank K (K ⊗[k] M)).map
          (algebraMap K (K ⊗[k] H)) := by
      rw [← hpK, Comodule.coefficientMatrix_baseChange_charpoly_eq_iff (A := K) b p]
      simpa only [p] using
        (geometricallyUnipotentPointsCommHopfAlgProperty.coefficientMatrix_charpoly_eq
          ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k H.obj).mpr hHk)
          (FGComoduleCat.of (R := k) (C := H) M) b)
    exact (HopfAlgebra.isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
      (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M))
      (Comodule.IsFaithful.baseChange (K := K) hM) g).2
      (Comodule.isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq g bK hCK)

/-- Smooth geometric unipotence is preserved by arbitrary extension of the ground field. -/
theorem baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : smoothUnipotentCommHopfAlgProperty k H) :
    smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  obtain ⟨hsmooth, hunip⟩ := (smoothUnipotentCommHopfAlgProperty_iff k H).mp hH
  let _ : Algebra.Smooth k H := hsmooth
  exact (smoothUnipotentCommHopfAlgProperty_iff K _).mpr
    ⟨inferInstance, (forall_isUnipotentPoint_baseChange_iff H hsmooth).mpr hunip⟩

/-- Smooth geometric unipotence is reflected by arbitrary extension of the ground field. -/
theorem of_baseChange (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    smoothUnipotentCommHopfAlgProperty k H := by
  obtain ⟨hsmoothK, hunipK⟩ := (smoothUnipotentCommHopfAlgProperty_iff K _).mp hH
  let _ : Algebra.Smooth K (K ⊗[k] H.obj) :=
    FiniteTypeCommHopfAlgCat.smooth_baseChange_obj hsmoothK
  have hsmooth : Algebra.Smooth k H :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := k) (S := H.obj) K
  exact (smoothUnipotentCommHopfAlgProperty_iff k H).mpr
    ⟨hsmooth, (forall_isUnipotentPoint_baseChange_iff H hsmooth).mp hunipK⟩

-- The defining simp lemma `smoothUnipotentCommHopfAlgProperty_iff` already simplifies the left-hand
-- side, so adding `baseChange_iff` to the simp set would violate `simpNF`.
/-- Smooth geometric unipotence of a finite-type affine group is invariant under arbitrary
extension of the ground field. -/
theorem baseChange_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      smoothUnipotentCommHopfAlgProperty k H :=
  ⟨of_baseChange H, baseChange H⟩

end smoothUnipotentCommHopfAlgProperty

end

end TauCeti
