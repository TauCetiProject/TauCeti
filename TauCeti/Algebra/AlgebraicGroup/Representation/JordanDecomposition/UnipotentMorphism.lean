/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Commutative
public import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# The unipotent-part endomorphism of a commutative affine group

For a reduced commutative affine group of finite type over an algebraically closed field,
Jordan decomposition is regular: both factors come from endomorphisms of the group scheme.
This file constructs the unipotent projection as the convolution product of the inverse of
the semisimple projection with the identity. Its action on base-valued points is `g ↦ g_u`.

The construction uses `semisimplePartBialgHom`, which already represents `g ↦ g_s`.
The two endomorphisms are complementary idempotents. Their convolution product is the
identity over every test algebra, including nonreduced algebras. These identities allow the
semisimple and unipotent factors to be realized as closed subgroup schemes.

## References

* A. Borel, *Linear Algebraic Groups*, §4.7.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 3.1.
-/

public section

open WithConv

namespace TauCeti.HopfAlgebra.Point

universe u

variable (k H : Type u) [Field k] [IsAlgClosed k] [CommRing H]
  [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  [Coalgebra.IsCocomm k H]

/-- The endomorphism representing the unipotent part of a reduced commutative affine group
of finite type over an algebraically closed field. -/
noncomputable def unipotentPartBialgHom : H →ₐc[k] H :=
  (toConv ((semisimplePartBialgHom k H).comp
    (antipodeBialgHom (R := k) (A := H))) * toConv (BialgHom.id k H)).ofConv

/-- The unipotent projection is the convolution of the inverse semisimple projection and
the identity. -/
theorem unipotentPartBialgHom_toAlgHom :
    (unipotentPartBialgHom k H : H →ₐ[k] H) =
      ((toConv (semisimplePartBialgHom k H : H →ₐ[k] H))⁻¹ *
        toConv (AlgHom.id k H)).ofConv := by
  unfold unipotentPartBialgHom
  apply toConv_injective
  rw [BialgHom.toAlgHom_convMul, toConv_ofConv]
  congr 1
  apply ofConv_injective
  ext x
  simp [algHom_inv_apply]

/-- Over any test algebra, the two regular Jordan factors multiply to the original point. -/
theorem mapDomain_semisimplePartBialgHom_mul_mapDomain_unipotentPartBialgHom
    {A : Type*} [CommSemiring A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    BialgHom.mapDomain (semisimplePartBialgHom k H) g *
      BialgHom.mapDomain (unipotentPartBialgHom k H) g = g := by
  simp only [BialgHom.mapDomain_apply, unipotentPartBialgHom_toAlgHom]
  rw [AlgHom.comp_convMul_distrib]
  have hinv : toConv (g.ofConv.comp
      (toConv (semisimplePartBialgHom k H : H →ₐ[k] H))⁻¹.ofConv) =
      (toConv (g.ofConv.comp (semisimplePartBialgHom k H : H →ₐ[k] H)))⁻¹ := by
    simpa only [AlgHom.mapValue_apply] using
      map_inv (AlgHom.mapValue g.ofConv)
        (toConv (semisimplePartBialgHom k H : H →ₐ[k] H))
  simp [hinv]

/-- The unipotent-part endomorphism represents `g ↦ g_u` on base-valued points. -/
theorem mapDomain_unipotentPartBialgHom (g : WithConv (H →ₐ[k] k)) :
    BialgHom.mapDomain (unipotentPartBialgHom k H) g = unipotentPart k H k g := by
  apply mul_left_cancel (a := semisimplePart k H k g)
  rw [semisimplePart_mul_unipotentPart,
    ← mapDomain_semisimplePartBialgHom]
  exact mapDomain_semisimplePartBialgHom_mul_mapDomain_unipotentPartBialgHom k H g

/-- Evaluation of the regular unipotent projection at a base-valued point. -/
@[simp]
theorem apply_unipotentPartBialgHom (g : WithConv (H →ₐ[k] k)) (f : H) :
    g.ofConv (unipotentPartBialgHom k H f) = (unipotentPart k H k g).ofConv f := by
  simpa only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom] using
    congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f)
      (mapDomain_unipotentPartBialgHom k H g)

/-- Simp-normal form of the action of the unipotent projection on base-valued points. -/
@[simp]
theorem toConv_comp_unipotentPartBialgHom (g : WithConv (H →ₐ[k] k)) :
    toConv (g.ofConv.comp (unipotentPartBialgHom k H : H →ₐ[k] H)) =
      unipotentPart k H k g := by
  simpa only [BialgHom.mapDomain_apply] using mapDomain_unipotentPartBialgHom k H g

/-- The regular unipotent projection is uniquely determined by its base-valued points. -/
theorem eq_unipotentPartBialgHom_iff (φ : H →ₐc[k] H) :
    φ = unipotentPartBialgHom k H ↔
      ∀ g : WithConv (H →ₐ[k] k), BialgHom.mapDomain φ g = unipotentPart k H k g := by
  refine ⟨fun h g ↦ h ▸ mapDomain_unipotentPartBialgHom k H g, fun h ↦ ?_⟩
  ext f
  refine eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ ?_
  have hg := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f) (h (toConv g))
  rw [← apply_unipotentPartBialgHom k H (toConv g) f] at hg
  simpa [BialgHom.mapDomain_apply] using hg

/-- The unipotent projection fixes exactly the unipotent base-valued points. -/
theorem mapDomain_unipotentPartBialgHom_eq_self_iff (g : WithConv (H →ₐ[k] k)) :
    BialgHom.mapDomain (unipotentPartBialgHom k H) g = g ↔ IsUnipotentPoint g := by
  rw [mapDomain_unipotentPartBialgHom]
  exact (isUnipotentPoint_iff_unipotentPart_eq_self k H k g).symm

/-- The kernel of the unipotent projection on base-valued points consists exactly of the
semisimple points. -/
theorem mapDomain_unipotentPartBialgHom_eq_one_iff (g : WithConv (H →ₐ[k] k)) :
    BialgHom.mapDomain (unipotentPartBialgHom k H) g = 1 ↔ IsSemisimplePoint g := by
  rw [mapDomain_unipotentPartBialgHom]
  exact (isSemisimplePoint_iff_unipotentPart_eq_one g).symm

/-- The regular unipotent projection is idempotent as a group-scheme endomorphism. -/
@[simp]
theorem unipotentPartBialgHom_comp_self :
    (unipotentPartBialgHom k H).comp (unipotentPartBialgHom k H) =
      unipotentPartBialgHom k H := by
  apply (eq_unipotentPartBialgHom_iff k H _).mpr
  intro g
  rw [BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    mapDomain_unipotentPartBialgHom, mapDomain_unipotentPartBialgHom]
  exact unipotentPart_eq_self k H k
    ((isUnipotentPoint_def _).mpr (isUnipotent_pointsAction_unipotentPart k H k g))

/-- The semisimple projection after the unipotent projection is the trivial group-scheme
endomorphism (composition reverses on coordinate algebras). -/
@[simp]
theorem unipotentPartBialgHom_comp_semisimplePartBialgHom :
    (unipotentPartBialgHom k H).comp (semisimplePartBialgHom k H) =
      (Bialgebra.unitBialgHom k H).comp (Bialgebra.counitBialgHom k H) := by
  ext f
  refine eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ ?_
  have h := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f)
    (semisimplePart_eq_one_of_isUnipotent k H k
      ((isUnipotentPoint_def _).mpr
        (isUnipotent_pointsAction_unipotentPart k H k (toConv g))))
  have heval := (apply_unipotentPartBialgHom k H (toConv g)
    (semisimplePartBialgHom k H f)).trans
      ((apply_semisimplePartBialgHom (unipotentPart k H k (toConv g)) f).trans h)
  simpa [BialgHom.comp_apply, Bialgebra.unitBialgHom] using heval

/-- The unipotent projection after the semisimple projection is the trivial group-scheme
endomorphism (composition reverses on coordinate algebras). -/
@[simp]
theorem semisimplePartBialgHom_comp_unipotentPartBialgHom :
    (semisimplePartBialgHom k H).comp (unipotentPartBialgHom k H) =
      (Bialgebra.unitBialgHom k H).comp (Bialgebra.counitBialgHom k H) := by
  ext f
  refine eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ ?_
  have h := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f)
    (unipotentPart_eq_one_of_isSemisimple k H k
      (isSemisimple_pointsAction_semisimplePart k H k (toConv g)))
  have heval := (apply_semisimplePartBialgHom (toConv g)
    (unipotentPartBialgHom k H f)).trans
      ((apply_unipotentPartBialgHom k H (semisimplePart k H k (toConv g)) f).trans h)
  simpa [BialgHom.comp_apply, Bialgebra.unitBialgHom] using heval

/-- The regular unipotent projection is natural in homomorphisms of reduced commutative
affine groups. The equality is one of coordinate morphisms, so holds over every test algebra. -/
theorem unipotentPartBialgHom_comp {H' : Type u} [CommRing H']
    [_root_.HopfAlgebra k H'] [Algebra.FiniteType k H'] [IsReduced H']
    [Coalgebra.IsCocomm k H'] (φ : H →ₐc[k] H') :
    (unipotentPartBialgHom k H').comp φ = φ.comp (unipotentPartBialgHom k H) := by
  ext f
  refine eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ ?_
  have h := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f)
    (unipotentPart_mapDomain φ (toConv g))
  have hleft := apply_unipotentPartBialgHom k H' (toConv g) (φ f)
  have hright := apply_unipotentPartBialgHom k H
    (toConv (g.comp (φ : H →ₐ[k] H'))) f
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom] at h
  simpa [BialgHom.comp_apply] using hleft.trans (h.symm.trans hright.symm)

end TauCeti.HopfAlgebra.Point
