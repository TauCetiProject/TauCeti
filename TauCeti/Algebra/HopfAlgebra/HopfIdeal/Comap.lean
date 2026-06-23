/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Inverse images of Hopf ideals along surjective Hopf algebra morphisms

This file records the inverse image of a Hopf ideal along a surjective bialgebra morphism.
For a surjective morphism `f : H →ₐc[R] K` and a Hopf ideal `I` of `K`, the preimage
`f ⁻¹ I` is a Hopf ideal of `H`. The construction is made by applying the existing
kernel-of-a-surjective-Hopf-map theorem to the composite `H → K → K/I`.

The surjectivity hypothesis is intentional: over a general commutative base, the tensor
exactness needed for the coideal condition is not automatic without an exactness hypothesis.

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔ closed
subgroup schemes", including kernels and pullback-style operations on closed subgroup
schemes in the affine Hopf-algebra dictionary.

## Main declarations

* `TauCeti.HopfIdeal.comap`: the inverse image of a Hopf ideal under a surjective morphism.
* `TauCeti.HopfIdeal.comap_toIdeal` and `TauCeti.HopfIdeal.mem_comap`: characteristic API.
* `TauCeti.HopfIdeal.comap_le_comap_iff`: surjective inverse image reflects containment.
* `TauCeti.HopfIdeal.comap_bot`: the kernel of a surjective morphism is the inverse image of
  the zero Hopf ideal.
* `TauCeti.HopfIdeal.comap_id` and `TauCeti.HopfIdeal.comap_comap`: identity and composition
  laws.

## References

The construction is the standard inverse image of a Hopf ideal along a surjective Hopf algebra
morphism, reduced here to the quotient-kernel construction already in
`TauCeti.Algebra.HopfAlgebra.Kernel`.
-/

public section

namespace TauCeti

universe u v w x

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : Type v} {K : Type w} {L : Type x}
variable [Ring H] [Ring K] [Ring L]
variable [HopfAlgebra R H] [HopfAlgebra R K] [HopfAlgebra R L]

/-- The inverse image of a Hopf ideal along a surjective bialgebra morphism.

It is defined as the kernel of the composite `H → K → K/I`; its underlying ideal is the
ordinary ideal comap of `I.toIdeal`. -/
noncomputable def comap (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) : HopfIdeal R H :=
  ker ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f)
    ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf)

/-- The underlying ideal of `I.comap f hf` is the ordinary ideal-theoretic inverse image. -/
@[simp]
theorem comap_toIdeal (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    (I.comap f hf).toIdeal = Ideal.comap (f : H →+* K) I.toIdeal := by
  ext h
  rw [mem_toIdeal, comap, mem_ker, Ideal.mem_comap, BialgHom.coe_comp,
    Function.comp_apply, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_toIdeal.symm

/-- Membership in the inverse-image Hopf ideal is membership after applying the morphism. -/
@[simp]
theorem mem_comap {I : HopfIdeal R K} {f : H →ₐc[R] K} {hf : Function.Surjective f}
    {h : H} : h ∈ I.comap f hf ↔ f h ∈ I := by
  rw [← mem_toIdeal, comap_toIdeal, Ideal.mem_comap]
  exact mem_toIdeal

/-- Inverse image of Hopf ideals is monotone. -/
theorem comap_mono (f : H →ₐc[R] K) (hf : Function.Surjective f) {I J : HopfIdeal R K}
    (hIJ : I ≤ J) : I.comap f hf ≤ J.comap f hf := by
  intro h hh
  exact mem_comap.mpr (hIJ (mem_comap.mp hh))

/-- For a surjective morphism, inverse image of Hopf ideals reflects containment. -/
theorem le_of_comap_le_comap (f : H →ₐc[R] K) (hf : Function.Surjective f)
    {I J : HopfIdeal R K} (hIJ : I.comap f hf ≤ J.comap f hf) : I ≤ J := by
  intro k hk
  obtain ⟨h, rfl⟩ := hf k
  exact mem_comap.mp (hIJ (mem_comap.mpr hk))

/-- For a surjective morphism, containment after inverse image is equivalent to containment
before inverse image. -/
theorem comap_le_comap_iff (f : H →ₐc[R] K) (hf : Function.Surjective f)
    {I J : HopfIdeal R K} : I.comap f hf ≤ J.comap f hf ↔ I ≤ J :=
  ⟨le_of_comap_le_comap f hf, comap_mono f hf⟩

/-- For a surjective morphism, inverse image of Hopf ideals reflects equality. -/
@[simp]
theorem comap_eq_comap_iff (f : H →ₐc[R] K) (hf : Function.Surjective f)
    {I J : HopfIdeal R K} : I.comap f hf = J.comap f hf ↔ I = J := by
  constructor
  · intro h
    apply le_antisymm
    · rw [← comap_le_comap_iff f hf, h]
    · rw [← comap_le_comap_iff f hf, h]
  · intro h
    rw [h]

/-- The inverse image of the zero Hopf ideal is the kernel Hopf ideal. -/
@[simp]
theorem comap_bot (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⊥ : HopfIdeal R K).comap f hf = ker f hf := by
  ext h
  rw [mem_comap, mem_ker, mem_bot]

/-- Pulling a Hopf ideal back along the identity morphism leaves it unchanged. -/
@[simp]
theorem comap_id (I : HopfIdeal R H) :
    I.comap (BialgHom.id R H) (fun h => ⟨h, rfl⟩) = I := by
  ext h
  rw [mem_comap, BialgHom.coe_id]
  rfl

/-- Inverse image of Hopf ideals is compatible with composition of surjective morphisms. -/
@[simp]
theorem comap_comap (I : HopfIdeal R L) (g : K →ₐc[R] L) (hg : Function.Surjective g)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (I.comap g hg).comap f hf = I.comap (g.comp f) (hg.comp hf) := by
  ext h
  rw [mem_comap, mem_comap, mem_comap, BialgHom.coe_comp]
  rfl

end HopfIdeal

end TauCeti
