/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic

import Mathlib.RingTheory.Nilpotent.Defs
import TauCeti.RingTheory.Flat.TensorProduct

/-!
# Kernels of Hopf algebra morphisms

This file records two conditions under which the kernel of a morphism of Hopf algebras is a
Hopf ideal. Over an arbitrary commutative base, surjectivity provides the exactness needed to
identify the kernel of the tensor-square map with `ker f ⊗ H + H ⊗ ker f`. Alternatively,
flatness of the codomain and `H / ker f` makes the tensor square of the injective factor through
`H / ker f` injective. This second construction needs no surjectivity hypothesis and applies
in particular over fields, where every module is flat.

## Main declarations

* `TauCeti.HopfIdeal.kerOfSurjective`: the Hopf ideal given by the kernel of a surjective bialgebra
  morphism.
* `TauCeti.HopfIdeal.ker`: the kernel Hopf ideal of a bialgebra morphism with flat codomain and
  flat kernel quotient.
* `TauCeti.HopfIdeal.ker_le_ker_comp`: a Hopf kernel grows under postcomposition.
* `TauCeti.HopfIdeal.kerOfSurjective_eq_ker`: comparison of the two constructions when both apply.
* `TauCeti.HopfIdeal.kerOfSurjective_toIdeal` and
  `TauCeti.HopfIdeal.mem_kerOfSurjective`: its characteristic API.
* `TauCeti.HopfIdeal.kerLiftBialgHom`: the induced bialgebra morphism from the quotient by
  the kernel of a surjective morphism.
* `TauCeti.HopfIdeal.kerLiftBialgEquiv`: the resulting bialgebra equivalence from the quotient
  by the kernel to the codomain.
* `TauCeti.HopfIdeal.isReduced_quotient_kerOfSurjective`: the kernel quotient is reduced when
  the codomain is.
* `TauCeti.HopfIdeal.kerOfSurjective_mkBialgHom`: the kernel of the quotient morphism by `I`
  is `I`.

## References

The construction is the standard kernel Hopf ideal. The tensor-kernel exactness steps use
Mathlib's `Algebra.TensorProduct.map_ker` and flatness API.

-/

public section

open scoped TensorProduct

universe u v w x

namespace TauCeti

namespace HopfIdeal

section BialgScaffolding

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommSemiring R] [Semiring H] [Semiring K]
variable [Algebra R H] [CoalgebraStruct R H]
variable [Algebra R K] [CoalgebraStruct R K]

/-- The tensor-square map sends the comultiplication of an element in the kernel of a
bialgebra morphism to zero. -/
private theorem comul_mem_tensor_map_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) :
    Coalgebra.comul (R := R) x ∈
      RingHom.ker
        (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)).toRingHom := by
  rw [RingHom.mem_ker]
  calc
    Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K) (Coalgebra.comul (R := R) x)
        = Coalgebra.comul (R := R) (f x) := CoalgHomClass.map_comp_comul_apply f x
    _ = 0 := by
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simpa using congrArg (Coalgebra.comul (R := R) (A := K)) hfx

/-- The counit vanishes on the ordinary kernel of a bialgebra morphism. -/
private theorem counit_eq_zero_of_mem_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) : Coalgebra.counit (R := R) x = 0 := by
  have h := CoalgHomClass.counit_comp_apply f x
  have hfx : f x = 0 := RingHom.mem_ker.mp hx
  simpa [hfx] using h.symm

end BialgScaffolding

section Hopf

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommRing R] [Ring H] [Ring K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- The antipode preserves the ordinary kernel of a bialgebra morphism. -/
private theorem antipode_mem_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) :
    HopfAlgebra.antipode R x ∈ RingHom.ker (f : H →ₐ[R] K) := by
  rw [RingHom.mem_ker]
  have hfx : f x = 0 := RingHom.mem_ker.mp hx
  simp [hfx]

/-- Build a Hopf ideal from the only kernel condition that is not automatic. -/
private def ofKerComul (f : H →ₐc[R] K)
    (hcomul : ∀ ⦃x : H⦄, x ∈ RingHom.ker (f : H →ₐ[R] K) →
      Coalgebra.comul (R := R) x ∈
        leftTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) ⊔
          rightTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K))) :
    HopfIdeal R H :=
  ofIdeal (RingHom.ker (f : H →ₐ[R] K)) hcomul
    (fun _ hx ↦ counit_eq_zero_of_mem_ker f hx)
    (fun _ hx ↦ antipode_mem_ker f hx)

@[simp]
private theorem ofKerComul_toIdeal (f : H →ₐc[R] K) (hcomul) :
    (ofKerComul f hcomul).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  rfl

@[simp]
private theorem mem_ofKerComul (f : H →ₐc[R] K) (hcomul) {x : H} :
    x ∈ ofKerComul f hcomul ↔ f x = 0 := by
  rw [← mem_toIdeal, ofKerComul_toIdeal, RingHom.mem_ker]
  simp only [BialgHom.coe_toAlgHom]

/-- A Hopf ideal whose underlying ideal is a morphism kernel is bottom exactly when the
morphism is injective. -/
private theorem eq_bot_iff_injective {I : HopfIdeal R H} (f : H →ₐc[R] K)
    (hI : I.toIdeal = RingHom.ker (f : H →ₐ[R] K)) :
    I = ⊥ ↔ Function.Injective f := by
  rw [← le_bot_iff, ← toIdeal_le_toIdeal, bot_toIdeal, le_bot_iff, hI,
    ← RingHom.injective_iff_ker_eq_bot]
  simp only [BialgHom.coe_toAlgHom]

/-- The kernel of a surjective bialgebra morphism, as a Hopf ideal. -/
def kerOfSurjective (f : H →ₐc[R] K) (hf : Function.Surjective f) : HopfIdeal R H :=
  ofKerComul f (by
    intro x hx
    rw [← ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal
      f.toAlgHom f.toAlgHom hf hf]
    exact comul_mem_tensor_map_ker f hx)

/-- The underlying ideal of the kernel Hopf ideal is the ring-hom kernel. -/
@[simp]
theorem kerOfSurjective_toIdeal (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerOfSurjective f hf).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  ofKerComul_toIdeal f _

/-- Membership in the kernel Hopf ideal is vanishing under the bialgebra morphism. -/
@[simp]
theorem mem_kerOfSurjective (f : H →ₐc[R] K) (hf : Function.Surjective f) {x : H} :
    x ∈ kerOfSurjective f hf ↔ f x = 0 :=
  mem_ofKerComul f _

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
@[simp]
theorem kerOfSurjective_eq_bot_iff (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    kerOfSurjective f hf = ⊥ ↔ Function.Injective f :=
  eq_bot_iff_injective f (kerOfSurjective_toIdeal f hf)

section Flat

variable [Module.Flat R K]

/-- With flat codomain and kernel quotient, comultiplication carries the ordinary kernel into
`ker f ⊗ H + H ⊗ ker f`. -/
private theorem comul_mem_left_sup_right_of_mem_ker (f : H →ₐc[R] K)
    [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) :
    Coalgebra.comul (R := R) x ∈
      leftTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) ⊔
        rightTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) := by
  let I := RingHom.ker (f : H →ₐ[R] K)
  let q : H →ₐ[R] H ⧸ I := Ideal.Quotient.mkₐ R I
  let f' : (H ⧸ I) →ₐ[R] K := Ideal.kerLiftAlg f.toAlgHom
  have hcomp : f'.comp q = f.toAlgHom := by
    ext y
    exact Ideal.kerLiftAlg_mk f.toAlgHom y
  have hzero :
      Algebra.TensorProduct.map f.toAlgHom f.toAlgHom (Coalgebra.comul (R := R) x) = 0 :=
    RingHom.mem_ker.mp (comul_mem_tensor_map_ker f hx)
  have hfactor :
      Algebra.TensorProduct.map f' f'
          (Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) x)) = 0 := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hcomp]
    exact hzero
  have hqzero :
      Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) x) = 0 :=
    Algebra.TensorProduct.map_injective_of_flat_flat f' f'
      (Ideal.kerLiftAlg_injective f.toAlgHom) (Ideal.kerLiftAlg_injective f.toAlgHom) hfactor
  have hker : RingHom.ker (Algebra.TensorProduct.map q q).toRingHom =
      leftTensorIdeal (R := R) (H := H) I ⊔ rightTensorIdeal (R := R) (H := H) I := by
    simpa only [q, AlgHom.ker_coe, AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker] using
      HopfIdeal.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal (R := R) q q
        (Ideal.Quotient.mkₐ_surjective R I) (Ideal.Quotient.mkₐ_surjective R I)
  rw [← hker, RingHom.mem_ker]
  exact hqzero

/-- The ordinary kernel of a morphism of Hopf algebras with flat codomain and flat kernel
quotient, as a Hopf ideal. In particular, these hypotheses hold over a field. -/
def ker (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] : HopfIdeal R H :=
  ofKerComul (R := R) f
    (fun x hx ↦ comul_mem_left_sup_right_of_mem_ker (R := R) f (x := x) hx)

/-- The underlying ideal of the kernel Hopf ideal is the ordinary ring-hom kernel. -/
@[simp]
theorem ker_toIdeal (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] :
    (ker f).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  ofKerComul_toIdeal f _

/-- Membership in the kernel Hopf ideal is vanishing under the morphism. -/
@[simp]
theorem mem_ker (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] {x : H} :
    x ∈ ker f ↔ f x = 0 :=
  mem_ofKerComul f _

/-- The kernel Hopf ideal of a morphism is contained in the kernel after postcomposition. -/
theorem ker_le_ker_comp {L : Type x} [Ring L] [HopfAlgebra R L]
    (f : H →ₐc[R] K) (g : K →ₐc[R] L)
    [Module.Flat R L] [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)]
    [Module.Flat R (H ⧸ RingHom.ker (g.comp f).toAlgHom)] : ker f ≤ ker (g.comp f) := by
  intro h hh
  rw [mem_ker] at hh ⊢
  rw [BialgHom.comp_apply, hh, map_zero]

/-- The surjective and flat kernel constructions agree whenever both apply. -/
@[simp]
theorem kerOfSurjective_eq_ker (f : H →ₐc[R] K)
    [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] (hf : Function.Surjective f) :
    kerOfSurjective f hf = ker f := by
  ext x
  rw [mem_kerOfSurjective, mem_ker]

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
@[simp]
theorem ker_eq_bot_iff (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] :
    ker f = ⊥ ↔ Function.Injective f :=
  eq_bot_iff_injective f (ker_toIdeal f)

/-- The kernel of the quotient bialgebra morphism by `I` is `I`. -/
@[simp]
theorem ker_mkBialgHom (I : HopfIdeal R H)
    [Module.Flat R (H ⧸ I.toIdeal)] :
    haveI : Module.Flat R
        (H ⧸ RingHom.ker (Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal).toAlgHom) := by
      rwa [Bialgebra.Quotient.mkBialgHom_toAlgHom, AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker]
    ker (Bialgebra.Quotient.mkBialgHom I.toIdeal) = I := by
  ext x
  rw [mem_ker, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_toIdeal]

end Flat

/-- The bialgebra morphism induced from a surjective morphism on the quotient by its
Hopf-ideal kernel. -/
noncomputable def kerLiftBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    H ⧸ (kerOfSurjective f hf).toIdeal →ₐc[R] K :=
  Bialgebra.Quotient.liftBialgHom (kerOfSurjective f hf).toIdeal f
    (kerOfSurjective_toIdeal f hf).le

/-- The kernel quotient lift evaluates on quotient classes as the original morphism. -/
@[simp]
theorem kerLiftBialgHom_mk (f : H →ₐc[R] K) (hf : Function.Surjective f) (h : H) :
    kerLiftBialgHom f hf (Ideal.Quotient.mk (kerOfSurjective f hf).toIdeal h) = f h :=
  Bialgebra.Quotient.liftBialgHom_mk (kerOfSurjective f hf).toIdeal f
    (kerOfSurjective_toIdeal f hf).le h

/-- The kernel quotient lift composed with the quotient map is the original morphism. -/
@[simp]
theorem kerLiftBialgHom_comp_mkBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerLiftBialgHom f hf).comp
        (Bialgebra.Quotient.mkBialgHom (kerOfSurjective f hf).toIdeal) = f :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom (kerOfSurjective f hf).toIdeal f
    (kerOfSurjective_toIdeal f hf).le

/-- The quotient by the Hopf-ideal kernel of a surjective morphism maps bijectively to the
codomain. -/
theorem kerLiftBialgHom_bijective (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    Function.Bijective (kerLiftBialgHom f hf) := by
  have hfun : (kerLiftBialgHom f hf : H ⧸ (kerOfSurjective f hf).toIdeal → K) =
      (Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[R] K)) hf :
        H ⧸ RingHom.ker (f : H →ₐ[R] K) → K) := by
    ext q
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (kerOfSurjective f hf).toIdeal q
    rw [Ideal.Quotient.mkₐ_eq_mk, kerLiftBialgHom_mk]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (f : H →ₐ[R] K)) hf h).symm
  rw [hfun]
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := (f : H →ₐ[R] K)) hf).bijective

/-- The quotient by the Hopf-ideal kernel of a surjective morphism is bialgebra-equivalent to
the codomain. -/
noncomputable def kerLiftBialgEquiv (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (H ⧸ (kerOfSurjective f hf).toIdeal) ≃ₐc[R] K :=
  BialgEquiv.ofBijective (kerLiftBialgHom f hf) (kerLiftBialgHom_bijective f hf)

/-- The kernel quotient equivalence applies as the kernel quotient lift. -/
@[simp]
theorem kerLiftBialgEquiv_apply (f : H →ₐc[R] K) (hf : Function.Surjective f)
    (q : H ⧸ (kerOfSurjective f hf).toIdeal) :
    kerLiftBialgEquiv f hf q = kerLiftBialgHom f hf q := by
  rw [kerLiftBialgEquiv, BialgEquiv.ofBijective_apply]

/-- The bialgebra morphism underlying the kernel quotient equivalence is the kernel quotient
lift. -/
@[simp]
theorem kerLiftBialgEquiv_toBialgHom (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerLiftBialgEquiv f hf : H ⧸ (kerOfSurjective f hf).toIdeal →ₐc[R] K) =
      kerLiftBialgHom f hf := by
  ext q
  exact kerLiftBialgEquiv_apply f hf q

/-- The quotient by the Hopf-ideal kernel of a surjective morphism is reduced when the codomain
is. -/
theorem isReduced_quotient_kerOfSurjective [IsReduced K] (f : H →ₐc[R] K)
    (hf : Function.Surjective f) : IsReduced (H ⧸ (kerOfSurjective f hf).toIdeal) :=
  isReduced_of_injective (kerLiftBialgEquiv f hf).toAlgEquiv.toRingEquiv.toRingHom
    (kerLiftBialgEquiv f hf).injective

/-- The Hopf-ideal kernel of the quotient morphism by `I` is `I`. -/
@[simp]
theorem kerOfSurjective_mkBialgHom (I : HopfIdeal R H) :
    kerOfSurjective (Bialgebra.Quotient.mkBialgHom I.toIdeal)
      Ideal.Quotient.mk_surjective = I := by
  ext x
  refine (mem_kerOfSurjective _ _).trans ?_
  rw [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem, mem_toIdeal]

end Hopf

end HopfIdeal

end TauCeti
