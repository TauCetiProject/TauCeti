/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Degreewise character rescaling of graded algebras

For an `R`-algebra `A` internally graded by `𝒜 : ι → Submodule R A` over an additive monoid `ι`,
an additive character `φ : AddChar ι R` induces the degreewise rescaling endomorphism acting as
`φ i • ·` on each homogeneous piece `𝒜 i`. Because `φ` sends `0` to `1` and sums to products,
this rescaling is a graded `R`-algebra endomorphism and depends multiplicatively on `φ`.

## Main definitions

* `TauCeti.GradedAlgebra.rescale`: the monoid homomorphism `AddChar ι R →* (𝒜 →ₐᵍ[R] 𝒜)` sending
  `φ` to the graded `R`-algebra endomorphism acting by `φ i • ·` on `𝒜 i`.

## Main results

* `TauCeti.GradedAlgebra.rescale_of_mem` and `TauCeti.GradedAlgebra.rescale_coe`: on `a ∈ 𝒜 i`,
  `rescale 𝒜 φ a = φ i • a`.
* `TauCeti.GradedAlgebra.decompose_rescale`: rescaling multiplies the degree-`i` homogeneous
  component of any element by `φ i`.
* `TauCeti.GradedAlgebra.rescale_mul_apply`: rescalings compose multiplicatively.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §3.1.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.2.1.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedAlgebra

universe uR uι uA

variable {R : Type uR} {ι : Type uι} {A : Type uA}
  [CommSemiring R] [AddMonoid ι] [DecidableEq ι]
  [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

private noncomputable def rescaleAlgHom (φ : AddChar ι R) : A →ₐ[R] A :=
  (DirectSum.toAlgebra R (fun i ↦ ↥(𝒜 i)) (fun i ↦ φ i • (𝒜 i).subtype)
    (by simp [AddChar.map_zero_eq_one])
    (fun {i j} ai aj ↦ by
      simp [AddChar.map_add_eq_mul, mul_comm (φ i) (φ j), mul_smul])).comp
    (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom

private theorem rescaleAlgHom_of_mem (φ : AddChar ι R) {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    rescaleAlgHom 𝒜 φ a = φ i • a := by
  simp only [rescaleAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    DirectSum.decomposeAlgEquiv_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAlgebra_apply]
  exact DirectSum.toSemiring_of (fun j ↦ (φ j • (𝒜 j).subtype).toAddMonoidHom) _ _ i ⟨a, ha⟩

private noncomputable def rescaleGradedAlgHom (φ : AddChar ι R) : 𝒜 →ₐᵍ[R] 𝒜 where
  toAlgHom := rescaleAlgHom 𝒜 φ
  map_mem {i a} ha := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rescaleAlgHom_of_mem 𝒜 φ ha]
    exact Submodule.smul_mem (𝒜 i) (φ i) ha

/-- Degreewise rescaling of an internally graded `R`-algebra `𝒜` by additive characters
`φ : AddChar ι R`, acting as `φ i • ·` on each homogeneous piece `𝒜 i`, bundled as a monoid
homomorphism `AddChar ι R →* (𝒜 →ₐᵍ[R] 𝒜)`. -/
noncomputable def rescale : AddChar ι R →* (𝒜 →ₐᵍ[R] 𝒜) where
  toFun := rescaleGradedAlgHom 𝒜
  map_one' := by
    ext a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | homogeneous x =>
      simp [rescaleGradedAlgHom, rescaleAlgHom_of_mem 𝒜 1 x.property]
  map_mul' φ ψ := by
    ext a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | homogeneous x =>
      simp [rescaleGradedAlgHom, rescaleAlgHom_of_mem 𝒜 (φ * ψ) x.property,
        rescaleAlgHom_of_mem 𝒜 ψ x.property,
        rescaleAlgHom_of_mem 𝒜 φ (Submodule.smul_mem _ _ x.property), mul_smul]

/-- Rescaling by `φ : AddChar ι R` multiplies any homogeneous element of degree `i` by `φ i`. -/
theorem rescale_of_mem (φ : AddChar ι R) {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    rescale 𝒜 φ a = φ i • a :=
  rescaleAlgHom_of_mem 𝒜 φ ha

/-- Subtype-coercion form of `rescale_of_mem`. -/
@[simp]
theorem rescale_coe (φ : AddChar ι R) {i : ι} (a : 𝒜 i) :
    rescale 𝒜 φ a = φ i • (a : A) :=
  rescale_of_mem 𝒜 φ a.property

/-- Rescaling by `φ` multiplies the degree-`i` homogeneous component of any element by `φ i`. -/
@[simp]
theorem decompose_rescale (φ : AddChar ι R) (a : A) (i : ι) :
    DirectSum.decompose 𝒜 (rescale 𝒜 φ a) i = φ i • DirectSum.decompose 𝒜 a i :=
  Subtype.ext <| by
    rw [Submodule.coe_smul, ← map_directSumDecompose (𝒜 := 𝒜) (ℬ := 𝒜) (rescale 𝒜 φ),
      rescale_coe]

/-- Rescaling by `φ * ψ` is rescaling by `ψ` followed by rescaling by `φ`. -/
theorem rescale_mul_apply (φ ψ : AddChar ι R) (a : A) :
    rescale 𝒜 (φ * ψ) a = rescale 𝒜 φ (rescale 𝒜 ψ a) := by
  simp

end TauCeti.GradedAlgebra
