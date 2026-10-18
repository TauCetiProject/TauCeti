/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Rigidity
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Etale
import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
import TauCeti.RingTheory.Smooth.Regular
import TauCeti.RingTheory.TensorProduct.Descent
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.RingHom.Finite

/-!
# Uniqueness of lifts through finite group homomorphisms

Over a field of characteristic zero, two homomorphisms from a geometrically connected
finite-type affine group that lift the same homomorphism through a finite group homomorphism
are equal. In particular, lifts through central isogenies are unique, as needed when comparing
simply connected covers. The covering group is required to be of finite type, but need not
be connected or semisimple, and the finite homomorphism need not be surjective or central.

The coordinate arrows reverse: for `f : H ⟶ K` and `g₁ g₂ : K ⟶ G`, equality
`f ≫ g₁ = f ≫ g₂` implies `g₁ = g₂`. This is cancellation on maps from connected groups,
rather than a categorical epimorphism assertion about `f`.

After extension to an algebraic closure, Cartier's theorem makes the finite kernel smooth,
so its Lie algebra is zero. The differential of the finite homomorphism is therefore injective.
The two lifts have equal differentials, and `CommHopfAlgCat.Hom.eq_of_derivationCompLieHom_eq`
makes them equal. Faithful scalar extension descends the equality.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 21, differentials and isogenies.
* J. E. Humphreys, *Linear Algebraic Groups*, §13, homomorphisms and their differentials.

The proof uses the equalizer rigidity theorem in `Tangent.Rigidity`, the kernel differential
criterion in `HopfIdeal.Quotient.Kernel.Etale`, and Cartier's theorem in `Smooth.CharZero`.
-/

public section

open CategoryTheory

namespace CommHopfAlgCat.Hom

open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] [CharZero k]
  {H K : CommHopfAlgCat.{u} k} [Algebra.FiniteType k K]
  {G : FiniteTypeCommHopfAlgCat.{u, u} k}

private theorem eq_of_comp_eq_of_finite_of_isAlgClosed [IsAlgClosed k]
    [ConnectedSpace (PrimeSpectrum G)] (f : H ⟶ K) (hf : f.hom.toAlgHom.Finite)
    (g₁ g₂ : K ⟶ G.obj) (h : f ≫ g₁ = f ≫ g₂) : g₁ = g₂ := by
  let Q := quotient K (kernelHopfIdeal f)
  let _ : Module.Finite k Q := moduleFinite_quotient_kernelHopfIdeal hf
  let _ : Nontrivial Q := Bialgebra.nontrivial k
  let _ : Algebra.Smooth k Q :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k Q)
  let _ : IsRegularRing Q := IsRegularRing.of_smooth (R := k)
  let _ : IsArtinianRing Q := IsArtinianRing.of_finite k Q
  have hdim : ringKrullDim Q = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hlie : Module.finrank k
      (Derivation k Q (Bialgebra.CounitAlgebra k Q k)) = 0 := by
    have heq := (TauCeti.HopfAlgebra.isRegularLocalRing_augmentationStalk_iff
      (k := k) (H := Q)).mp inferInstance
    rw [hdim] at heq
    exact_mod_cast heq
  have hker : Algebra.Etale k Q := HopfAlgebra.algebraEtale_iff_finrank_lie_eq_zero.mpr hlie
  have hinj := (algebraEtale_quotient_kernelHopfIdeal_iff f).mp hker
  apply g₁.eq_of_derivationCompLieHom_eq g₂
  apply LieHom.ext
  intro d
  apply hinj
  have hd := congrArg (fun a ↦ derivationCompLieHom (B := k) a.hom d) h
  simpa only [CommHopfAlgCat.hom_comp, derivationCompLieHom_comp, LieHom.comp_apply] using hd

/-- Homomorphism lifts from a geometrically connected finite-type affine group through a
finite group homomorphism are unique in characteristic zero. In particular this applies to
central isogenies and to comparisons of simply connected covers. The finite homomorphism
need not be surjective or central. Coordinate arrows reverse group-scheme arrows. -/
theorem eq_of_comp_eq_of_finite
    (f : H ⟶ K) (hf : f.hom.toAlgHom.Finite)
    (hG : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (g₁ g₂ : K ⟶ G.obj) (h : f ≫ g₁ = f ≫ g₂) : g₁ = g₂ := by
  let L := AlgebraicClosure k
  let extendedGroup := FiniteTypeCommHopfAlgCat.baseChange (K := L) G
  let _ : ConnectedSpace (PrimeSpectrum extendedGroup) :=
    hG.connectedSpace_algebraicClosureBaseChange
  apply baseChangeMap_injective_hom (K := L) (algebraMap k L).injective
  apply eq_of_comp_eq_of_finite_of_isAlgClosed (G := extendedGroup)
    (baseChangeMap (K := L) f)
    (by
      -- The Hopf map is L-linear, while scalar-extension stability uses a k-linear map.
      -- Their underlying ring maps agree on both tensor factors.
      have heq : (baseChangeMap (K := L) f).hom.toAlgHom.toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id k L) f.hom.toAlgHom).toRingHom := by
        apply Algebra.TensorProduct.ringHom_ext <;> ext x <;> simp
      rw [AlgHom.Finite, heq]
      exact RingHom.finite_isStableUnderBaseChange.tensorProduct_map
        (S := L) f.hom.toAlgHom hf)
    (baseChangeMap (K := L) g₁) (baseChangeMap (K := L) g₂)
  exact (baseChangeFunctor (K := L)).map_comp f g₁ |>.symm.trans
    ((congrArg (baseChangeMap (K := L)) h).trans
      ((baseChangeFunctor (K := L)).map_comp f g₂))

end CommHopfAlgCat.Hom
