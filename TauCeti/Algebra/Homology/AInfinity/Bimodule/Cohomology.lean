/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Components
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Taylor
public import TauCeti.Algebra.Homology.GradedCochainComplex
public import TauCeti.Algebra.Homology.SquareZero

/-!
# Unary cohomology of A-infinity bimodules

The operation with no algebra inputs is a degree-one square-zero endomorphism of the
bimodule carrier. Its cohomology is the underlying module used to test bimodule
quasi-isomorphisms, independently of the higher operations.

We identify the restriction of the bar differential to the two empty words with this
unary differential, and assemble the underlying cochain complex. Total cohomology uses
`LinearMap.homology`, including its quotient, representative and descent API, rather than
a second implementation of cycles modulo boundaries.

## References

* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.AInfinityBimodule

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The unary differential of an A-infinity bimodule. -/
noncomputable def differential (MM : AInfinityBimodule AA BB M) : M →ₗ[R] M :=
  MM.taylor ∘ₗ (TensorProduct.mk R (TensorWords R A ⊗[R] M) (TensorWords R B)).flip 1 ∘ₗ
    TensorProduct.mk R (TensorWords R A) M 1

/-- The unary differential is the Taylor map on the two empty words. This is not a simp
lemma: expanding the Taylor map and restricting the bar differential recovers the differential. -/
theorem differential_apply (MM : AInfinityBimodule AA BB M) (x : M) :
    MM.differential x = MM.taylor ((1 ⊗ₜ x) ⊗ₜ 1) := (rfl)

/-- The bar differential on the two empty words is the unary differential, with empty
words on both sides of the output. -/
@[simp]
theorem barDifferential_one_tmul_tmul_one (MM : AInfinityBimodule AA BB M) (x : M) :
    MM.barDifferential ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ MM.differential x) ⊗ₜ 1 := by
  rw [MM.barDifferential_eq, gradedCoderiv_def, leftTaylor_def]
  simp [differential_apply, Comodule.leftCoactRTensor_def, Comodule.leftCofreeCoact_def,
    TensorWords.comul_eq_deconcatenation, TensorWords.deconcatenation_one]

/-- The unary differential squares to zero. -/
@[simp]
theorem differential_comp_self_eq_zero (MM : AInfinityBimodule AA BB M) :
    MM.differential ∘ₗ MM.differential = 0 := by
  have h := LinearMap.congr_fun MM.taylor_comp_barDifferential
  ext x
  simpa only [LinearMap.comp_apply, barDifferential_one_tmul_tmul_one,
    ← differential_apply, LinearMap.zero_apply] using h ((1 ⊗ₜ x) ⊗ₜ 1)

/-- The unary differential raises cohomological degree by one. -/
theorem differential_mem_piece (MM : AInfinityBimodule AA BB M) {p : ℤ} {x : M}
    (hx : x ∈ MM.grading.piece p) : MM.differential x ∈ MM.grading.piece (p + 1) := by
  rw [differential_apply, ← MM.m_zero_zero x (fun i ↦ i.elim0) (fun i ↦ i.elim0)]
  simpa only [Fin.sum_univ_zero, zero_add, add_zero, Nat.cast_zero, sub_zero] using
    MM.m_mem_piece 0 0 hx (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
      (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)

/-- The unary differential is homogeneous of degree one. -/
theorem isHomogeneous_differential (MM : AInfinityBimodule AA BB M) :
    LinearMap.IsHomogeneous MM.differential MM.grading.piece MM.grading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ MM.differential_mem_piece hx

/-- The underlying cochain complex, with the original grading and unary differential. -/
abbrev cochainComplex (MM : AInfinityBimodule AA BB M) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex MM.grading.piece MM.differential MM.isHomogeneous_differential
    fun _ x ↦ LinearMap.congr_fun MM.differential_comp_self_eq_zero x

/-- Total unary cohomology: the kernel of the unary differential modulo its image.
Use `LinearMap.homologyπ` for classes of cycles. -/
abbrev Cohomology (MM : AInfinityBimodule AA BB M) :=
  MM.differential.homology MM.differential_comp_self_eq_zero

end TauCeti.AInfinityBimodule
