/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.IsAugmentation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

import TauCeti.RingTheory.Ideal.Extended

/-!
# The kernel of an augmentation `A →ₐ[R] R`

Let `A` be an algebra, not necessarily commutative, over a commutative ring `R`, and let
`ε : A →ₐ[R] R` be an `R`-algebra map, that is, a retraction of `algebraMap R A`. Its kernel
`A₊ = ker ε` is the augmentation ideal of `A`. This file records the structure every such kernel
has, with no flatness, freeness or finiteness hypothesis:

* every `x : A` splits as the scalar `algebraMap R A (ε x)` plus the element
  `x - algebraMap R A (ε x)` of `A₊`, so `A₊` is a complement of the scalars in Mathlib's sense
  `Ideal.IsAugmentation`, and `A ≃ₗ[R] R × A₊`;
* for every ideal `I` of `R`, with extension `IA = I.map (algebraMap R A)`, the remainder
  `x - algebraMap R A (ε x)` of an element `x ∈ IA` lies in `IA * A₊`, and hence
  `IA ⊓ A₊ = IA * A₊`.

The last identity is the compatibility condition between the divided powers of an augmentation
ideal and the base ideal `I`, used for divided-power algebras and divided-power envelopes.

## Main declarations

* `AlgHom.sub_algebraMap_apply_mem_ker`: `x - algebraMap R A (ε x) ∈ ker ε`.
* `AlgHom.isAugmentation_ker`: `ker ε` is an augmentation ideal.
* `AlgHom.equivProdKer`: the `R`-linear splitting `A ≃ₗ[R] R × ker ε`,
  `x ↦ (ε x, x - algebraMap R A (ε x))`.
* `AlgHom.sub_algebraMap_apply_mem_map_mul_ker`: the remainder of `x ∈ IA` lies in `IA * ker ε`.
* `AlgHom.map_algebraMap_inf_ker_eq_mul`: `IA ⊓ ker ε = IA * ker ε`.

## References

* [Stacks: Divided power algebra, Lemma 07H5](https://stacks.math.columbia.edu/tag/07H5), whose
  proof contains the intersection identity for free modules.
* N. Roby, *Lois polynomes et lois formelles en théorie des modules*, Ann. Sci. ÉNS 80 (1963),
  III §§1–2.
-/

public section

namespace AlgHom

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (ε : A →ₐ[R] R)

/-- An element differs from the scalar given by its augmentation by an element of the kernel. -/
theorem sub_algebraMap_apply_mem_ker (x : A) : x - algebraMap R A (ε x) ∈ RingHom.ker ε := by
  simp [RingHom.mem_ker]

/-- The kernel of an `R`-algebra map `A →ₐ[R] R` is a complement of the scalars `1 : Submodule R A`,
that is, an augmentation ideal. -/
theorem isAugmentation_ker : (RingHom.ker ε).IsAugmentation R := by
  rw [Ideal.isAugmentation_iff]
  refine ⟨Submodule.disjoint_def.mpr fun x hx hxε ↦ ?_, codisjoint_iff.mpr <| eq_top_iff.mpr ?_⟩
  · obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    obtain rfl : r = 0 := by simpa using hxε
    exact map_zero _
  · intro x _
    rw [← add_sub_cancel (algebraMap R A (ε x)) x]
    exact Submodule.add_mem_sup (Submodule.mem_one.mpr ⟨_, rfl⟩)
      (ε.sub_algebraMap_apply_mem_ker x)

/-- The splitting of `A` into scalars and the kernel of `ε`, as `R`-modules:
`x ↦ (ε x, x - algebraMap R A (ε x))`, with inverse `(r, u) ↦ algebraMap R A r + u`. The
multiplication of `A` is not a product: `(algebraMap r + u) * (algebraMap s + v)` has the cross
terms `r • v + s • u`. -/
noncomputable def equivProdKer : A ≃ₗ[R] R × RingHom.ker ε where
  toFun x := (ε x, ⟨x - algebraMap R A (ε x), ε.sub_algebraMap_apply_mem_ker x⟩)
  invFun p := algebraMap R A p.1 + p.2
  map_add' x y := by
    ext
    · simp
    · simp only [map_add, Submodule.coe_add, Prod.snd_add]
      abel
  map_smul' r x := by
    ext
    · simp
    · simp [mul_sub, Algebra.smul_def]
  left_inv x := by simp
  right_inv p := by
    obtain ⟨r, u, hu⟩ := p
    rw [RingHom.mem_ker] at hu
    ext
    · simp [hu]
    · simp [hu]

@[simp]
theorem equivProdKer_apply_fst (x : A) : (ε.equivProdKer x).1 = ε x :=
  (rfl)

@[simp]
theorem coe_equivProdKer_apply_snd (x : A) :
    ((ε.equivProdKer x).2 : A) = x - algebraMap R A (ε x) :=
  (rfl)

@[simp]
theorem equivProdKer_symm_apply (p : R × RingHom.ker ε) :
    ε.equivProdKer.symm p = algebraMap R A p.1 + p.2 :=
  (rfl)

/-- **Remainder of an extended base ideal.** For an ideal `I` of `R`, the remainder
`x - algebraMap R A (ε x)` of an element `x` of the extended ideal `IA = I.map (algebraMap R A)`
lies in the product `IA * ker ε`. -/
theorem sub_algebraMap_apply_mem_map_mul_ker {I : Ideal R} {x : A}
    (hx : x ∈ I.map (algebraMap R A)) :
    x - algebraMap R A (ε x) ∈ I.map (algebraMap R A) * RingHom.ker ε := by
  rw [Ideal.mem_map_algebraMap_iff] at hx
  refine Submodule.smul_induction_on hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
  · have : r • y - algebraMap R A (ε (r • y)) = algebraMap R A r * (y - algebraMap R A (ε y)) := by
      rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
    rw [this]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hr) (ε.sub_algebraMap_apply_mem_ker y)
  · rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hy hz

/-- **Base ideal and augmentation intersection.** For an ideal `I` of `R`, the extended ideal
`IA = I.map (algebraMap R A)` meets the kernel of `ε` exactly in the product `IA * ker ε`. -/
theorem map_algebraMap_inf_ker_eq_mul (I : Ideal R) :
    I.map (algebraMap R A) ⊓ RingHom.ker ε = I.map (algebraMap R A) * RingHom.ker ε := by
  refine le_antisymm (fun x ⟨hxI, hxε⟩ ↦ ?_) Ideal.mul_le_inf
  simpa [(RingHom.mem_ker).mp hxε] using ε.sub_algebraMap_apply_mem_map_mul_ker hxI

end AlgHom
