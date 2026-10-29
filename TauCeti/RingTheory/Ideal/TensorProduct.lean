/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.Algebra.Module.Submodule.LinearMap
public import TauCeti.LinearAlgebra.TensorProduct.Kernel
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.LinearAlgebra.TensorProduct.Torsion

/-!
# Extended ideals and annihilators under scalar extension

The scalar multiplication equivalence `S ⊗[R] R ≃ₗ[S] S` identifies the base change of
an ideal with its extension along `algebraMap R S`. This permits kernel computations
on tensor products to be read as membership statements in extended ideals.
The extension of a module annihilator is contained in its annihilator after arbitrary
scalar extension, without a flatness hypothesis. The coefficient algebra `S` need not be
commutative; extended ideals are left ideals.

For an ideal `I` and a module `M`, injectivity of `I ⊗ M → R ⊗ M` is the vanishing of
`Tor₁(R ⧸ I, M)`. `Ideal.sup_subtype_rTensor_injective` propagates it from `I` and `J` to `I ⊔ J`,
provided `I M ∩ J M = (I ⊓ J) M`.
-/

public section

open TensorProduct

namespace Ideal

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- The extended ideal is the image of its tensor base change under scalar multiplication. -/
theorem map_eq_baseChange_map_rid (I : Ideal R) :
    I.map (algebraMap R S) =
      (I.baseChange S).map (AlgebraTensorModule.rid R S S).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  simp only [LinearEquiv.coe_coe, TensorProduct.mk_apply,
    AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
  rfl

end Ideal

namespace LinearMap

variable {R S M : Type*} [CommRing R] [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Flatness tests membership in an extended scalar-source kernel on `s ⊗ₜ 1`. -/
theorem mem_map_ker_iff_of_flat [Module.Flat R S] (f : R →ₗ[R] M) (s : S) :
    s ∈ Ideal.map (algebraMap R S) (ker f) ↔ f.baseChange S (s ⊗ₜ[R] 1) = 0 := by
  rw [Ideal.map_eq_baseChange_map_rid, ← f.ker_baseChange_of_flat S,
    Submodule.mem_map_equiv, AlgebraTensorModule.rid_symm_apply, mem_ker]

end LinearMap

namespace TauCeti

section Semiring

variable {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Extension of the annihilator is contained in the annihilator after arbitrary base change. -/
theorem annihilator_map_le_baseChange :
    (Module.annihilator R M).map (algebraMap R S) ≤
      Module.annihilator S (S ⊗[R] M) := by
  refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  have h := isTorsionBy_tensorProduct_right (R := R) (M := S) (S := R)
    ((Module.isTorsionBy_iff_mem_annihilator R M).mpr hr)
  simpa only [algebraMap_smul] using h (x := x)

end Semiring

end TauCeti

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `I ⊗ M → R ⊗ M` and `J ⊗ M → R ⊗ M` are injective, that is, if
`Tor₁(R ⧸ I, M) = Tor₁(R ⧸ J, M) = 0`, and `I M ∩ J M = (I ⊓ J) M`, then `(I ⊔ J) ⊗ M → R ⊗ M` is
injective as well. -/
theorem sup_subtype_rTensor_injective {I J : Ideal R}
    (hI : Function.Injective (I.subtype.rTensor M))
    (hJ : Function.Injective (J.subtype.rTensor M))
    (hIJ : I • (⊤ : Submodule R M) ⊓ J • ⊤ ≤ (I ⊓ J) • ⊤) :
    Function.Injective ((I ⊔ J).subtype.rTensor M) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨a, b, rfl⟩ := Submodule.exists_eq_rTensor_inclusion_add I J t
  simp only [map_add, ← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion] at ht
  -- The image of `a` in `M` lies in `I M ∩ J M`, hence comes from some `s : (I ⊓ J) ⊗ M`.
  obtain ⟨s, hs⟩ : TensorProduct.lid R M (I.subtype.rTensor M a) ∈
      LinearMap.range ((TensorProduct.lid R M).comp ((I ⊓ J).subtype.rTensor M)) := by
    rw [subtype_rTensor_range]
    refine hIJ ⟨?_, ?_⟩
    · rw [← subtype_rTensor_range]
      exact ⟨a, rfl⟩
    · rw [eq_neg_of_add_eq_zero_left ht, map_neg, ← subtype_rTensor_range]
      exact neg_mem ⟨b, rfl⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (TensorProduct.lid R M).injective.eq_iff] at hs
  -- Since `I ⊗ M → R ⊗ M` and `J ⊗ M → R ⊗ M` are injective, `a` and `-b` both come from `s`.
  have ha : (Submodule.inclusion inf_le_left).rTensor M s = a := hI (by
    rw [← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion, hs])
  have hb : (Submodule.inclusion inf_le_right).rTensor M (-s) = b := hJ (by
    rw [← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion, map_neg, hs,
      eq_neg_of_add_eq_zero_right ht])
  simp only [← ha, ← hb, ← LinearMap.rTensor_comp_apply, Submodule.inclusion_comp_inclusion,
    map_neg, add_neg_cancel]

end Ideal
