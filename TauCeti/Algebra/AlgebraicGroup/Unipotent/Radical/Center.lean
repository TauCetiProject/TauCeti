/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Connected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Commutative
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Center.Nilpotent
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Augmentation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup

/-!
# The centre of the unipotent radical

Let `G` be a finite-type affine group over an algebraically closed field `k`, with unipotent
radical `U = R_u(G)`, and let `N = Z(U)°_red` be the reduced connected centre of `U`, viewed as
a closed subgroup of `G` and cut out by `(unipotentRadicalDefiningIdeal G).reducedConnectedCenter`.
This file shows that `N` has the properties used to start the induction in the structure theory
of connected solvable groups:

* `N` is nontrivial as soon as `U` is: a nontrivial smooth connected unipotent group has
  nilpotent rational points, hence a nontrivial smooth connected central subgroup, which lies in
  `N` (`reducedConnectedCenter_unipotentRadicalDefiningIdeal_eq_augmentation_iff`);
* `N` is smooth and unipotent (`TauCeti.HopfIdeal.smoothUnipotent_reducedConnectedCenter`) and
  commutative (`TauCeti.HopfIdeal.isCocomm_reducedConnectedCenter`), and it is central in `U` by
  construction (`TauCeti.FiniteTypeCommHopfAlgCat.isCentral_reducedConnectedCenterDefiningIdeal`);
* when `G` is reduced, for instance in characteristic zero, `N` is normal in `G`, being
  characteristic in the normal subgroup `U` (`TauCeti.HopfIdeal.IsNormal.reducedConnectedCenter`);
* in characteristic zero, `N` is a vector group, the spectrum of the symmetric algebra on the
  primitive elements of its coordinate ring
  (`TauCeti.HopfIdeal.liftBialgHom_primitive_bijective_reducedConnectedCenter`), and `G` acts on
  it linearly by conjugation
  (`TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCenterConjLinearAut`).

The primitive elements of the coordinate ring of `N` are its additive characters, the
homomorphisms `N → 𝔾ₐ`, and a point `n` of `N` is read as the linear form `p ↦ n(p)` on them.

## Main declarations

* `TauCeti.HopfIdeal.smoothUnipotent_reducedConnectedCenter`: the reduced connected centre of a
  unipotent closed subgroup is smooth and unipotent.
* `TauCeti.HopfIdeal.liftBialgHom_primitive_bijective_reducedConnectedCenter`: in characteristic
  zero, it is a vector group.
* `reducedConnectedCenter_unipotentRadicalDefiningIdeal_eq_augmentation_iff`:
  the reduced connected centre of the unipotent radical is trivial exactly when the unipotent
  radical is.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCenterConjLinearAut`: in characteristic
  zero, the action of `G` on the reduced connected centre of its unipotent radical by
  conjugation, as linear automorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 14.21 for the nilpotence of unipotent
  groups, §14.c for commutative unipotent groups in characteristic zero, and the proof of
  Theorem 16.33, which starts from the centre of the unipotent radical.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u x

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace HopfIdeal

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The reduced connected centre of a unipotent closed subgroup is unipotent. -/
private theorem geometricallyUnipotent_reducedConnectedCenter
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter).obj :=
  geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective k
    (CommHopfAlgCat.quotientMapOfLe H.obj I.le_reducedConnectedCenter)
    (CommHopfAlgCat.quotientMapOfLe_surjective _ _) hI

/-- **The reduced connected centre of a unipotent closed subgroup is smooth and unipotent.** Over
an algebraically closed field, if every geometric point of the closed subgroup cut out by `I` is
unipotent, the reduced connected centre of that subgroup is a smooth unipotent group. -/
theorem smoothUnipotent_reducedConnectedCenter
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter) :=
  (smoothUnipotentCommHopfAlgProperty_iff k _).mpr ⟨smooth_reducedConnectedCenter I,
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mp
      (geometricallyUnipotent_reducedConnectedCenter hI)⟩

/-- **The reduced connected centre of a unipotent group is a vector group in characteristic
zero.** Over an algebraically closed field of characteristic zero, if every geometric point of
the closed subgroup cut out by `I` is unipotent, the symmetric algebra on the primitive elements
of the coordinate Hopf algebra of its reduced connected centre maps bijectively onto it. -/
theorem liftBialgHom_primitive_bijective_reducedConnectedCenter [CharZero k]
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    Function.Bijective (SymmetricAlgebra.liftBialgHom
      (Coalgebra.skewPrimitive k (1 : H ⧸ I.reducedConnectedCenter.toIdeal) 1).subtype
      fun p ↦ p.property) :=
  let _ := isCocomm_reducedConnectedCenter I
  HopfAlgebra.liftBialgHom_primitive_bijective_of_forall_isUnipotentPoint
    (geometricallyUnipotent_reducedConnectedCenter hI).forall_isUnipotentPoint

end HopfIdeal

namespace FiniteTypeCommHopfAlgCat

variable (G : FiniteTypeCommHopfAlgCat.{u, u} k)

omit [IsAlgClosed k] in
/-- The unipotent radical is unipotent. -/
private theorem geometricallyUnipotent_unipotentRadical :
    geometricallyUnipotentPointsCommHopfAlgProperty k (unipotentRadical G).obj :=
  (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr
    ((smoothUnipotentCommHopfAlgProperty_iff k _).mp (smoothUnipotent_unipotentRadical G)).2

/-- **The centre of a nontrivial unipotent radical is nontrivial.** Over an algebraically closed
field, the reduced connected centre of the unipotent radical `R_u(G)` of a finite-type affine
group `G`, as a closed subgroup of `G`, is trivial exactly when `R_u(G)` is trivial. -/
theorem reducedConnectedCenter_unipotentRadicalDefiningIdeal_eq_augmentation_iff :
    (unipotentRadicalDefiningIdeal G).reducedConnectedCenter = HopfIdeal.augmentation k G ↔
      unipotentRadicalDefiningIdeal G = HopfIdeal.augmentation k G := by
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm (HopfIdeal.le_augmentation k G _)
    (h ▸ HopfIdeal.le_reducedConnectedCenter _)⟩
  by_contra hne
  -- The unipotent radical `U` is a nontrivial smooth connected unipotent group.
  let U := unipotentRadical G
  have hsmooth : Algebra.Smooth k U :=
    ((smoothUnipotentCommHopfAlgProperty_iff k U).mp (smoothUnipotent_unipotentRadical G)).1
  have : IsReduced U := isReduced_of_smooth k U
  have : ConnectedSpace (PrimeSpectrum U) :=
    (geometricallyConnected_unipotentRadical G).connectedSpace
  have : Nontrivial (WithConv (U →ₐ[k] k)) := by
    rw [← not_subsingleton_iff_nontrivial, ← HopfIdeal.augmentation_eq_bot_iff_subsingleton,
      HopfIdeal.augmentation_quotient_eq_bot_iff]
    exact hne
  -- So `U` has a nontrivial smooth connected central subgroup, which lies in its reduced
  -- connected centre.
  obtain ⟨J, hJc, hJne, hJp⟩ :=
    HopfIdeal.exists_isCentral_isPrime_ne_augmentation_of_forall_isUnipotentPoint
      (geometricallyUnipotent_unipotentRadical G).forall_isUnipotentPoint
  have : IsDomain (U ⧸ J.toIdeal) := Ideal.Quotient.isDomain _
  have hle := reducedConnectedCenterDefiningIdeal_le_of_isCentral U hJc
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr inferInstance)
  rw [HopfIdeal.reducedConnectedCenter_eq_augmentation_iff] at h
  exact hJne (le_antisymm (HopfIdeal.le_augmentation k U J) (h ▸ hle))

variable [CharZero k]

/-- In characteristic zero, the identification of the reduced connected centre of the unipotent
radical with the vector group on the primitive elements of its coordinate Hopf algebra. -/
private noncomputable def centerVectorGroupEquiv :
    SymmetricAlgebra k (Coalgebra.skewPrimitive k
        (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1) ≃ₐc[k]
      G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal :=
  BialgEquiv.ofBijective _ (HopfIdeal.liftBialgHom_primitive_bijective_reducedConnectedCenter
    (geometricallyUnipotent_unipotentRadical G))

/-- In characteristic zero `G` is reduced, so the reduced connected centre of its unipotent
radical is normal in `G`. -/
private theorem isNormal_center_of_charZero :
    (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.IsNormal :=
  let _ := HopfAlgebra.isReduced_of_charZero k G
  (isNormal_unipotentRadicalDefiningIdeal G).reducedConnectedCenter

/-- **A group acts linearly on the centre of its unipotent radical.** Over an algebraically
closed field of characteristic zero, let `N` be the reduced connected centre of the unipotent
radical of a finite-type affine group `G`, a vector group whose points are the linear
forms on the space `P` of primitive elements of its coordinate Hopf algebra. Each point
`g ∈ G(A)` acts on these linear forms by the `A`-linear automorphism induced by conjugation
`n ↦ g * n * g⁻¹` on `N` (`unipotentRadicalCenterConjLinearAut_apply`), naturally in `A`
(`unipotentRadicalCenterConjLinearAut_mapValue`). -/
noncomputable def unipotentRadicalCenterConjLinearAut (A : Type x) [CommRing A] [Algebra k A] :
    WithConv (G →ₐ[k] A) →*
      ((Coalgebra.skewPrimitive k
          (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1 →ₗ[k] A)
        ≃ₗ[A] (Coalgebra.skewPrimitive k
          (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1 →ₗ[k] A)) :=
  (isNormal_center_of_charZero G).conjLinearAut (centerVectorGroupEquiv G) A

/-- The linear automorphism through which a point `g` of `G` acts sends the linear form
`p ↦ n(p)` of a point `n` of the centre `N` of the unipotent radical to the linear form of the
conjugate `g * n * g⁻¹`, computed by `TauCeti.HopfIdeal.IsNormal.conjPoints` for any proof `hN`
that `N` is normal in `G`. -/
theorem unipotentRadicalCenterConjLinearAut_apply
    (hN : (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.IsNormal) (A : Type x)
    [CommRing A] [Algebra k A] (g : WithConv (G →ₐ[k] A))
    (n : WithConv ((G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) →ₐ[k]
      A)) :
    unipotentRadicalCenterConjLinearAut G A g
        (n.ofConv.toLinearMap ∘ₗ (Coalgebra.skewPrimitive k
          (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1).subtype) =
      (hN.conjPoints A g n).ofConv.toLinearMap ∘ₗ (Coalgebra.skewPrimitive k
        (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1).subtype := by
  -- A point of `N`, read in the vector group, is its restriction to the primitive elements.
  have hlin (m : WithConv ((G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal)
      →ₐ[k] A)) :
      (BialgHom.mapDomain (centerVectorGroupEquiv G).toBialgHom m).ofConv.toLinearMap ∘ₗ
          SymmetricAlgebra.ι k _ =
        m.ofConv.toLinearMap ∘ₗ (Coalgebra.skewPrimitive k
        (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1).subtype := by
    ext p
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, BialgHom.mapDomain_apply_apply]
    exact congrArg m.ofConv (SymmetricAlgebra.liftBialgHom_ι (Coalgebra.skewPrimitive k
      (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1).subtype
      (fun p ↦ p.property) p)
  simp only [BialgEquiv.toBialgHom_eq_coe] at hlin
  rw [← hlin, ← hlin]
  exact hN.conjLinearAut_apply (centerVectorGroupEquiv G) A g n

/-- The linear automorphisms through which `G` acts on the centre of its unipotent radical are
natural in the value algebra. -/
theorem unipotentRadicalCenterConjLinearAut_mapValue (A B : Type x) [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (g : WithConv (G →ₐ[k] A))
    (f : Coalgebra.skewPrimitive k
      (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1 →ₗ[k] A) :
    φ.toLinearMap ∘ₗ unipotentRadicalCenterConjLinearAut G A g f =
      unipotentRadicalCenterConjLinearAut G B (AlgHom.mapValue φ g) (φ.toLinearMap ∘ₗ f) :=
  HopfIdeal.IsNormal.conjLinearAut_mapValue _ _ A B φ g f

end FiniteTypeCommHopfAlgCat

end

end TauCeti
