/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Center
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# The centre of the unipotent radical

Let `G` be a finite-type affine group over an algebraically closed field `k`, with unipotent
radical `U = R_u(G)`, and let `N = Z(U)°_red` be the reduced connected centre of `U`, viewed as
a closed subgroup of `G` and cut out by `(unipotentRadicalDefiningIdeal G).reducedConnectedCenter`.
This file shows that `N` has the properties used to start the induction in the structure theory
of connected solvable groups:

* `N` is nontrivial as soon as `U` is
  (`reducedConnectedCenter_unipotentRadicalDefiningIdeal_eq_augmentation_iff`, a special case of
  `TauCeti.HopfIdeal.reducedConnectedCenter_eq_augmentation_iff_of_geometricallyUnipotent` from
  `TauCeti.Algebra.AlgebraicGroup.Unipotent.Center`);
* `N` is smooth and unipotent (`TauCeti.HopfIdeal.smoothUnipotent_reducedConnectedCenter`) and
  commutative (`TauCeti.HopfIdeal.isCocomm_reducedConnectedCenter`), and it is central in `U` by
  construction (`TauCeti.FiniteTypeCommHopfAlgCat.isCentral_reducedConnectedCenterDefiningIdeal`);
* when `G` is reduced, for instance in characteristic zero, `N` is normal in `G`, being
  characteristic in the normal subgroup `U`
  (`isNormal_reducedConnectedCenter_unipotentRadicalDefiningIdeal`);
* in characteristic zero, `N` is a vector group, the spectrum of the symmetric algebra on the
  primitive elements of its coordinate ring
  (`TauCeti.HopfIdeal.liftBialgHom_primitive_bijective_reducedConnectedCenter`), and `G` acts on
  it linearly by conjugation
  (`TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCenterConjLinearAut`).

The primitive elements of the coordinate ring of `N` are its additive characters, the
homomorphisms `N → 𝔾ₐ`, and a point `n` of `N` is read as the linear form `p ↦ n(p)` on them.

## Main declarations

* `reducedConnectedCenter_unipotentRadicalDefiningIdeal_eq_augmentation_iff`:
  the reduced connected centre of the unipotent radical is trivial exactly when the unipotent
  radical is.
* `TauCeti.FiniteTypeCommHopfAlgCat.isNormal_reducedConnectedCenter_unipotentRadicalDefiningIdeal`:
  for reduced `G`, it is normal in `G`.
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

namespace FiniteTypeCommHopfAlgCat

variable (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **The centre of a nontrivial unipotent radical is nontrivial.** Over an algebraically closed
field, the reduced connected centre of the unipotent radical `R_u(G)` of a finite-type affine
group `G`, as a closed subgroup of `G`, is trivial exactly when `R_u(G)` is trivial. -/
theorem reducedConnectedCenter_unipotentRadicalDefiningIdeal_eq_augmentation_iff :
    (unipotentRadicalDefiningIdeal G).reducedConnectedCenter = HopfIdeal.augmentation k G ↔
      unipotentRadicalDefiningIdeal G = HopfIdeal.augmentation k G :=
  let _ : Algebra.Smooth k (unipotentRadical G) :=
    ((smoothUnipotentCommHopfAlgProperty_iff k _).mp (smoothUnipotent_unipotentRadical G)).1
  let _ : IsReduced (unipotentRadical G) := isReduced_of_smooth k _
  HopfIdeal.reducedConnectedCenter_eq_augmentation_iff_of_geometricallyUnipotent
    (geometricallyConnected_unipotentRadical G) (geometricallyUnipotent_unipotentRadical G)

/-- The reduced connected centre of the unipotent radical is normal in a reduced `G`, for
instance in characteristic zero (`TauCeti.HopfAlgebra.isReduced_of_charZero`), being
characteristic in the normal subgroup `R_u(G)`. -/
theorem isNormal_reducedConnectedCenter_unipotentRadicalDefiningIdeal [IsReduced G] :
    (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.IsNormal :=
  (isNormal_unipotentRadicalDefiningIdeal G).reducedConnectedCenter

variable [CharZero k]

/-- In characteristic zero, the identification of the reduced connected centre of the unipotent
radical with the vector group on the primitive elements of its coordinate Hopf algebra. -/
private noncomputable def centerVectorGroupEquiv :
    SymmetricAlgebra k (Coalgebra.skewPrimitive k
        (1 : G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal) 1) ≃ₐc[k]
      G ⧸ (unipotentRadicalDefiningIdeal G).reducedConnectedCenter.toIdeal :=
  BialgEquiv.ofBijective _ (HopfIdeal.liftBialgHom_primitive_bijective_reducedConnectedCenter
    (geometricallyUnipotent_unipotentRadical G))

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
  let _ := HopfAlgebra.isReduced_of_charZero k G
  (isNormal_reducedConnectedCenter_unipotentRadicalDefiningIdeal G).conjLinearAut
    (centerVectorGroupEquiv G) A

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
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, BialgHom.mapDomain_apply_apply]
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
