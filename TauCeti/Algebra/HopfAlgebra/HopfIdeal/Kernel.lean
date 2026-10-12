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
import TauCeti.Algebra.Bialgebra.Hom.Basic
import TauCeti.RingTheory.Flat.TensorProduct

/-!
# Kernels of Hopf algebra morphisms

A morphism of Hopf algebras over a commutative semiring has a Hopf-ideal kernel whenever
comultiplication carries its kernel into `ker f ⊗ H + H ⊗ ker f`; the counit and antipode
conditions are automatic. Over a commutative ring, this file gives two sufficient conditions
for that comultiplication property. Surjectivity provides the exactness needed to
identify the kernel of the tensor-square map with `ker f ⊗ H + H ⊗ ker f`. Alternatively,
flatness of the codomain and `H / ker f` makes the tensor square of the injective factor through
`H / ker f` injective. This second construction needs no surjectivity hypothesis and applies
in particular over fields, where every module is flat.

## Main declarations

* `BialgHom.kerOfComul`: the kernel Hopf ideal from the comultiplication condition,
  over a commutative semiring.
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

namespace BialgHom

open TauCeti HopfIdeal

section SemiringHopf

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommSemiring R] [Semiring H] [Semiring K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- The kernel of a bialgebra morphism as a Hopf ideal, assuming comultiplication carries
its kernel into `ker f ⊗ H + H ⊗ ker f`. The counit and antipode conditions follow from
preservation of the Hopf structure. This construction works over commutative semirings. -/
def kerOfComul (f : H →ₐc[R] K)
    (hcomul : ∀ ⦃x : H⦄, x ∈ RingHom.ker (f : H →ₐ[R] K) →
      Coalgebra.comul (R := R) x ∈
        leftTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K)) ⊔
          rightTensorIdeal (R := R) (H := H) (RingHom.ker (f : H →ₐ[R] K))) :
    HopfIdeal R H :=
  ofIdeal (RingHom.ker (f : H →ₐ[R] K)) hcomul
    (fun _ hx ↦ counit_eq_zero_of_mem_ker f hx)
    (fun x hx ↦ by
      rw [RingHom.mem_ker]
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simp [hfx])

/-- The underlying ideal of `kerOfComul` is the ordinary morphism kernel. -/
@[simp]
theorem kerOfComul_toIdeal (f : H →ₐc[R] K) (hcomul) :
    (kerOfComul f hcomul).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  (rfl)

/-- Membership in `kerOfComul` is vanishing under the morphism. -/
@[simp]
theorem mem_kerOfComul (f : H →ₐc[R] K) (hcomul) {x : H} :
    x ∈ kerOfComul f hcomul ↔ f x = 0 := by
  rw [← mem_toIdeal, kerOfComul_toIdeal, RingHom.mem_ker]
  simp only [BialgHom.coe_toAlgHom]

end SemiringHopf

section RingHopf

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommSemiring R] [Ring H] [Semiring K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- When the domain is a ring, the kernel Hopf ideal is bottom exactly when the morphism
is injective. -/
@[simp]
theorem kerOfComul_eq_bot_iff (f : H →ₐc[R] K) (hcomul) :
    f.kerOfComul hcomul = ⊥ ↔ Function.Injective f := by
  simpa only [SetLike.ext_iff, mem_kerOfComul, mem_bot] using
    (injective_iff_map_eq_zero' f).symm

end RingHopf

end BialgHom

namespace TauCeti.HopfIdeal

section Hopf

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommRing R] [Ring H] [Ring K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- The kernel of a surjective bialgebra morphism, as a Hopf ideal. -/
def kerOfSurjective (f : H →ₐc[R] K) (hf : Function.Surjective f) : HopfIdeal R H :=
  f.kerOfComul (by
    intro x hx
    rw [← ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal
      f.toAlgHom f.toAlgHom hf hf]
    exact f.comul_mem_ker_tensorProduct_map hx)

/-- The underlying ideal of the kernel Hopf ideal is the ring-hom kernel. -/
@[simp]
theorem kerOfSurjective_toIdeal (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (kerOfSurjective f hf).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  f.kerOfComul_toIdeal _

/-- Membership in the kernel Hopf ideal is vanishing under the bialgebra morphism. -/
@[simp]
theorem mem_kerOfSurjective (f : H →ₐc[R] K) (hf : Function.Surjective f) {x : H} :
    x ∈ kerOfSurjective f hf ↔ f x = 0 :=
  f.mem_kerOfComul _

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
@[simp]
theorem kerOfSurjective_eq_bot_iff (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    kerOfSurjective f hf = ⊥ ↔ Function.Injective f :=
  f.kerOfComul_eq_bot_iff _

section Flat

variable [Module.Flat R K]

/-- The ordinary kernel of a morphism of Hopf algebras with flat codomain and flat kernel
quotient, as a Hopf ideal. In particular, these hypotheses hold over a field. -/
def ker (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] : HopfIdeal R H :=
  f.kerOfComul (by
    intro x hx
    simpa only [Algebra.TensorProduct.map_ker_of_flat_flat, leftTensorIdeal_def,
      rightTensorIdeal_def, AlgHom.coe_ideal_map, AlgHom.toRingHom_eq_coe] using
      f.comul_mem_ker_tensorProduct_map hx)

/-- The underlying ideal of the kernel Hopf ideal is the ordinary ring-hom kernel. -/
@[simp]
theorem ker_toIdeal (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] :
    (ker f).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  f.kerOfComul_toIdeal _

/-- Membership in the kernel Hopf ideal is vanishing under the morphism. -/
@[simp]
theorem mem_ker (f : H →ₐc[R] K) [Module.Flat R (H ⧸ RingHom.ker f.toAlgHom)] {x : H} :
    x ∈ ker f ↔ f x = 0 :=
  f.mem_kerOfComul _

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
  f.kerOfComul_eq_bot_iff _

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

end TauCeti.HopfIdeal
