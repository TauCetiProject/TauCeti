/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CanonicalMap
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tensor
public import TauCeti.RingTheory.Flat.TensorProduct

/-!
# The kernel criterion for a quotient by normal coinvariants

Let `I` be a normal Hopf ideal of a commutative Hopf algebra `H` over a field, let
`B = H^{co H/I}` be its algebra of coinvariants, and let `J` be the scheme-theoretic kernel of
the inclusion `B → H`. There are two natural maps out of `H ⊗[B] H`:

* the kernel-pair equivalence identifies it with `H ⊗ H/J`;
* the canonical map of the proposed quotient has target `H ⊗ H/I`.

This file proves that the second map is the first followed by the quotient `H/J → H/I`.
Consequently the canonical map is injective exactly when `J = I`. Since the canonical map is
always surjective, this is also exactly when it is an isomorphism. Thus the missing equality in
the Hopf ideal--Hopf subalgebra correspondence is reduced to the injectivity part of the usual
canonical-map criterion.

## References

* M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*, Manuscripta Math.
  **7** (1972), 251--270.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  {I : HopfIdeal k H}

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- The quotient from the scheme-theoretic kernel of the coinvariant projection to the proposed
normal subgroup. It is induced by the always-valid inclusion
`kernelHopfIdeal (coinvariantsι hI) ≤ I`. -/
noncomputable abbrev coinvariantsKernelQuotientMap (hI : I.IsNormal) :
    quotient H (kernelHopfIdeal (coinvariantsι hI)) ⟶ quotient H I :=
  quotientMapOfLe H (kernelHopfIdeal_coinvariantsι_le hI)

/-- Tensoring the quotient from the scheme-theoretic kernel with the ambient coordinate
algebra, regarded as a map of `H`-algebras through the left tensor factors. -/
noncomputable def coinvariantsKernelTensorMap (hI : I.IsNormal) :
    H ⊗[k] (H ⧸ (kernelHopfIdeal (coinvariantsι hI)).toIdeal) →ₐ[H]
      H ⊗[k] (H ⧸ I.toIdeal) where
  toRingHom := (Algebra.TensorProduct.map (AlgHom.id k H)
    (coinvariantsKernelQuotientMap hI).hom.toAlgHom).toRingHom
  commutes' x := by simp

/-- The tensor quotient is the tensor product of the identity with the quotient-to-quotient
map. -/
theorem coe_coinvariantsKernelTensorMap (hI : I.IsNormal) :
    ⇑(coinvariantsKernelTensorMap hI) =
      Algebra.TensorProduct.map (AlgHom.id k H)
        (coinvariantsKernelQuotientMap hI).hom.toAlgHom :=
  (rfl)

/-- The tensor quotient acts as the identity on the ambient factor and by the
quotient-to-quotient map on the kernel factor. -/
@[simp]
theorem coinvariantsKernelTensorMap_tmul (hI : I.IsNormal)
    (x : H) (y : H ⧸ (kernelHopfIdeal (coinvariantsι hI)).toIdeal) :
    coinvariantsKernelTensorMap hI (x ⊗ₜ[k] y) =
      x ⊗ₜ[k] (coinvariantsKernelQuotientMap hI).hom y := by
  simp [coe_coinvariantsKernelTensorMap]

/-- The kernel-pair equivalence for the coinvariant projection, expressed using the canonical
subalgebra action of the coinvariants on `H`. -/
noncomputable def coinvariantsKernelPairTensorEquiv (hI : I.IsNormal) :
    H ⊗[I.coinvariants] H ≃ₐ[H]
      H ⊗[k] (H ⧸ (kernelHopfIdeal (coinvariantsι hI)).toIdeal) := by
  -- The algebra structure on `H` induced by `coinvariantsι hI` is definitionally the subalgebra
  -- action of `I.coinvariants`; this is an identification of instances inside the tensor
  -- product type, so no rewriting lemma can replace it.
  exact kernelPairTensorEquiv (coinvariantsι hI)

/-- On pure tensors, the specialized kernel-pair equivalence multiplies the first factor by
the comultiplication of the second and projects its right leg to the kernel coordinates. -/
@[simp]
theorem coinvariantsKernelPairTensorEquiv_tmul (hI : I.IsNormal) (x y : H) :
    coinvariantsKernelPairTensorEquiv hI (x ⊗ₜ[I.coinvariants] y) =
      (x ⊗ₜ[k] (1 : H ⧸ (kernelHopfIdeal (coinvariantsι hI)).toIdeal)) *
        Algebra.TensorProduct.map (AlgHom.id k H)
          (Ideal.Quotient.mkₐ k (kernelHopfIdeal (coinvariantsι hI)).toIdeal)
          (Coalgebra.comul (R := k) y) := by
  -- As for `coinvariantsKernelPairTensorEquiv`, the two pure tensors differ only in the
  -- definitionally equal algebra instances of the coinvariants on `H`.
  exact kernelPairTensorEquiv_tmul (coinvariantsι hI) x y

/-- The canonical map for `I` factors as the kernel-pair equivalence of the coinvariant
projection, followed by the quotient from its scheme-theoretic kernel to `I`. -/
theorem canonicalMap_eq_tensorMap_comp_kernelPairTensorEquiv (hI : I.IsNormal) :
    I.canonicalMap = (coinvariantsKernelTensorMap hI).comp
      (coinvariantsKernelPairTensorEquiv hI).toAlgHom := by
  have hmap (t : H ⊗[k] H) : coinvariantsKernelTensorMap hI
      (Algebra.TensorProduct.map (AlgHom.id k H)
        (Ideal.Quotient.mkₐ k (kernelHopfIdeal (coinvariantsι hI)).toIdeal) t) =
      Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I.toIdeal) t := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        coinvariantsKernelTensorMap_tmul]
      exact congrArg (a ⊗ₜ[k] ·) (quotientMapOfLe_mk H (kernelHopfIdeal_coinvariantsι_le hI) b)
    | add a b ha hb => simp only [map_add, ha, hb]
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [HopfIdeal.canonicalMap_tmul, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    coinvariantsKernelPairTensorEquiv_tmul, map_mul, coinvariantsKernelTensorMap_tmul, map_one,
    hmap]

/-- The quotient from the scheme-theoretic kernel of the coinvariant projection to `I` is
injective exactly when that kernel is `I`. -/
theorem coinvariantsKernelQuotientMap_injective_iff (hI : I.IsNormal) :
    Function.Injective (coinvariantsKernelQuotientMap hI).hom ↔
      kernelHopfIdeal (coinvariantsι hI) = I :=
  quotientMapOfLe_injective_iff H (kernelHopfIdeal_coinvariantsι_le hI)

/-- **Kernel criterion for normal coinvariants.** The canonical map
`H ⊗[H^{co H/I}] H → H ⊗ H/I` is injective exactly when the scheme-theoretic kernel
of the corresponding quotient projection is the original normal subgroup `I`. -/
theorem canonicalMap_injective_iff_kernelHopfIdeal_coinvariantsι_eq (hI : I.IsNormal) :
    Function.Injective I.canonicalMap ↔ kernelHopfIdeal (coinvariantsι hI) = I := by
  let q := coinvariantsKernelQuotientMap hI
  let e := coinvariantsKernelPairTensorEquiv hI
  have hfactor := canonicalMap_eq_tensorMap_comp_kernelPairTensorEquiv hI
  let _ : Nontrivial H :=
    (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  constructor
  · intro hcan
    apply (coinvariantsKernelQuotientMap_injective_iff hI).mp
    intro x y hxy
    have htensor : Function.Injective
        (coinvariantsKernelTensorMap hI) := by
      intro a b hab
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      exact congrArg e (hcan (by rw [hfactor]; exact hab))
    apply Algebra.TensorProduct.includeRight_injective
      (A := H) (algebraMap k H).injective
    apply htensor
    simpa only [Algebra.TensorProduct.includeRight_apply,
      coinvariantsKernelTensorMap_tmul, q] using
      congrArg (fun z ↦ (1 : H) ⊗ₜ[k] z) hxy
  · intro hker
    have hq : Function.Injective q.hom :=
      (coinvariantsKernelQuotientMap_injective_iff hI).mpr hker
    have htensor : Function.Injective
        (coinvariantsKernelTensorMap hI) := by
      rw [coe_coinvariantsKernelTensorMap]
      exact Algebra.TensorProduct.map_injective_of_flat_flat
        (AlgHom.id k H) q.hom.toAlgHom Function.injective_id hq
    rw [hfactor]
    exact htensor.comp e.injective

/-- The canonical map over normal coinvariants is bijective exactly when the proposed subgroup
is the scheme-theoretic kernel of the quotient projection. Surjectivity holds for every Hopf
ideal, so only the injectivity criterion contributes to this equivalence. -/
theorem canonicalMap_bijective_iff_kernelHopfIdeal_coinvariantsι_eq (hI : I.IsNormal) :
    Function.Bijective I.canonicalMap ↔ kernelHopfIdeal (coinvariantsι hI) = I := by
  constructor
  · exact fun h ↦ (canonicalMap_injective_iff_kernelHopfIdeal_coinvariantsι_eq hI).mp h.1
  · exact fun h ↦ ⟨
      (canonicalMap_injective_iff_kernelHopfIdeal_coinvariantsι_eq hI).mpr h,
      HopfIdeal.canonicalMap_surjective I⟩

end

end TauCeti.CommHopfAlgCat
