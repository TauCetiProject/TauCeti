/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import TauCeti.Algebra.Algebra.Hom
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Connected
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.RingTheory.Extension.Cotangent.Vanishing
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Smooth connected closed subgroups with equal tangent spaces

A surjective map of coordinate Hopf algebras represents a closed immersion of affine groups.
When both groups are smooth and connected, surjectivity on tangent spaces forces this closed
immersion to be an isomorphism.

The proof uses the conormal module of the surjection. Smoothness makes it finite projective over
the target. Its fibre at the identity is zero, because its split injection into the relative
cotangent space is zero there. Projective-module rank is locally constant, so connectedness of
the target makes the conormal module vanish globally. The kernel is then idempotent; connectedness
of the source and the counit condition force it to be zero.

## Main declaration

* `TauCeti.HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot`: a surjective
  Hopf map between smooth connected affine groups is injective when its conormal space vanishes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a and 10.a.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This is the global equality step for the unipotent radical. It upgrades the infinitesimal equality
supplied by the maximal-dimension construction to equality of closed subgroups.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k H K : Type u} [Field k] [CommRing H] [CommRing K]
variable [HopfAlgebra k H] [HopfAlgebra k K]

/-- A surjective Hopf map between smooth connected affine groups is injective if its conormal
space at the identity vanishes.

Equivalently, a smooth connected closed affine subgroup whose differential is surjective is the
whole ambient group. -/
theorem ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot
    (f : H →ₐc[k] K) (hf : Function.Surjective f)
    (hH_smooth : smoothCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (hH_connected : ConnectedSpace (PrimeSpectrum H))
    (hK_smooth : smoothCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k K))
    (hK_connected : ConnectedSpace (PrimeSpectrum K))
    (hconormal : conormalSubspace (HopfIdeal.ker f) = ⊥) : HopfIdeal.ker f = ⊥ := by
  let _ : Algebra H K := f.toAlgHom.toAlgebra
  let _ : IsScalarTower k H K :=
    IsScalarTower.of_algebraMap_eq' f.toAlgHom.comp_algebraMap.symm
  let P : Algebra.Extension k K :=
    { Ring := H
      σ := Function.surjInv hf
      algebraMap_σ := Function.surjInv_eq hf }
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff _).mp hH_smooth
  let _ : Algebra.Smooth k K := (smoothCommHopfAlgProperty_iff _).mp hK_smooth
  let _ : ConnectedSpace (PrimeSpectrum H) := hH_connected
  let _ : ConnectedSpace (PrimeSpectrum K) := hK_connected
  let _ : IsNoetherianRing P.Ring := by
    simpa only [P] using (Algebra.FiniteType.isNoetherianRing k H)
  have hf_algebraMap : algebraMap H K = f.toAlgHom.toRingHom := by
    ext x
    rfl
  have hPker : P.ker = (HopfIdeal.ker f).toIdeal := by
    rw [HopfIdeal.ker_toIdeal]
    exact congrArg RingHom.ker hf_algebraMap
  have _ : Module.Finite K P.Cotangent :=
    Algebra.Extension.Cotangent.finite P.ker.fg_of_isNoetherianRing
  obtain ⟨l, hl⟩ := (P.formallySmooth_iff_split_injection).mp
    (inferInstance : Algebra.FormallySmooth k K)
  let _ : Module.Projective K P.CotangentSpace := inferInstance
  let _ : Module.Projective K P.Cotangent :=
    Module.Projective.of_split P.cotangentComplex l hl
  let _ : Module.Flat K P.Cotangent := inferInstance
  let _ : Module.FinitePresentation K P.Cotangent :=
    Module.finitePresentation_of_projective K P.Cotangent
  let p : Ideal K := Bialgebra.AugmentationIdeal k K
  have _ : p.IsMaximal := _root_.AlgHom.ker_isMaximal (Bialgebra.counitAlgHom k K)
  let κ := p.ResidueField
  have hbaseChange_zero : P.cotangentComplex.lTensor κ = 0 := by
    refine P.lTensor_cotangentComplex_eq_zero fun x hx ↦ ?_
    -- `P.Ring` is `H` by definition of `P`, and `κ` is the residue field of `K` at the
    -- augmentation ideal, so the kernel of `P.Ring → κ` is the augmentation ideal of `H`.
    rw [show RingHom.ker (algebraMap P.Ring κ) = Bialgebra.AugmentationIdeal k H from
      by rw [IsScalarTower.algebraMap_eq H K κ, hf_algebraMap, ← RingHom.comap_ker,
          Ideal.ker_algebraMap_residueField]
         exact BialgHom.comap_augmentationIdeal f]
    exact (conormalSubspace_eq_bot_iff_toIdeal_le_sq_augmentationIdeal _).mp
      hconormal (hPker ▸ hx)
  have hfiber : Subsingleton (p.Fiber P.Cotangent) :=
    LinearMap.subsingleton_tensor_of_lTensor_eq_zero _ l hl hbaseChange_zero
  have hcotangent : Subsingleton P.Cotangent := p.subsingleton_of_subsingleton_fiber hfiber
  have hI_idempotent : IsIdempotentElem (HopfIdeal.ker f).toIdeal := by
    rw [← hPker]
    exact P.isIdempotentElem_ker_of_subsingleton_cotangent hcotangent
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  exact eq_bot_of_isIdempotentElem _ (HopfIdeal.ker f).toIdeal.fg_of_isNoetherianRing hI_idempotent

end HopfIdeal

end

end TauCeti
