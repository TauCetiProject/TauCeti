/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Coalgebra.Defs
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.LinearAlgebra.TensorAlgebra.Derivation

/-!
# The cobar construction of a differential graded coalgebra

Let `(C, Δ, d)` be a noncounital differential graded coalgebra, for instance the coaugmentation
coideal `ker ε` of a coaugmented differential graded coalgebra `R ⊕ ker ε` with its reduced
coproduct.  Its **cobar construction** is the tensor algebra

`Ω C = T(s⁻¹ C)`

on the desuspension of `C`, graded by input degree, where `s⁻¹ c` has degree `|c| + 1`.  The
underlying algebra is `TensorAlgebra R C`, whose generator `ι c` stands for `s⁻¹ c`; the
desuspension is recorded only in the grading `TauCeti.tensorAlgebraPiece (G.shift (-1))`.  Its
differential is the odd derivation (`TauCeti.tensorAlgebraDerivation`) with the values

`d_Ω (s⁻¹ c) = -s⁻¹ (d c) + ∑ (-1) ^ |c'| s⁻¹ c' * s⁻¹ c''`   for `Δ c = ∑ c' ⊗ c''`

on generators.  The first term is the internal differential of the desuspension, and the second is
the coproduct followed by `s⁻¹ ⊗ s⁻¹`, whose Koszul sign is `(-1) ^ |c'|` because `s⁻¹` has
degree one; on generators it reads `ι (τ c') * ι c''` for the Koszul twist `τ` of `C`.

The differential squares to zero
(`TauCeti.IsNonCounitalDGCoalgebra.isDGAlgebra_cobarDifferential`).  Since `d_Ω` is a derivation
for which `d_Ω ∘ d_Ω` is an unsigned derivation, it is enough to check this on a generator
`s⁻¹ c`.  There the terms quadratic in generators cancel because `d` is a
coderivation and anticommutes with `τ`, the terms cubic in generators cancel by coassociativity,
and the remaining term is `s⁻¹ (d (d c)) = 0`.

## Main definitions

* `TauCeti.cobarDifferential`: the differential of the cobar construction on `TensorAlgebra R C`.

## Main results

* `TauCeti.cobarDifferential_ι`: the differential on generators.
* `TauCeti.cobarDifferential_algebraMap` and `TauCeti.cobarDifferential_one`: the differential
  annihilates scalars.
* `TauCeti.cobarDifferential_mul`: the graded Leibniz rule.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarDifferential_cobarDifferential`: the differential squares
  to zero.
* `TauCeti.IsNonCounitalDGCoalgebra.isDGAlgebra_cobarDifferential`: **the cobar construction of
  a noncounital differential graded coalgebra is a differential graded algebra**.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the cobar construction of a coaugmented differential
  graded coalgebra.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for the bar--cobar adjunction and the enveloping differential graded algebra
  `Ω B A` of an `A∞` algebra.
-/

public section

namespace TauCeti

open TensorProduct TensorAlgebra InternalGrading

universe uR uC

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]
  (G : InternalGrading R C) (Δ : C →ₗ[R] C ⊗[R] C) (d : C →ₗ[R] C)

/-- The quadratic part `c' ⊗ c'' ↦ s⁻¹ c' * s⁻¹ c''` of the cobar differential, with the Koszul
sign `(-1) ^ |c'|` of `s⁻¹ ⊗ s⁻¹`. -/
private noncomputable def cobarQuadratic : C ⊗[R] C →ₗ[R] TensorAlgebra R C :=
  LinearMap.mul' R (TensorAlgebra R C) ∘ₗ TensorProduct.map (ι R ∘ₗ G.koszulTwist 1) (ι R)

private theorem cobarQuadratic_tmul (a b : C) :
    cobarQuadratic G (a ⊗ₜ b) = ι R (G.koszulTwist 1 a) * ι R b := by
  simp [cobarQuadratic]

/-- The product `ι a * s⁻¹ (b ⊗ c) ↦ s⁻¹ a * (s⁻¹ b * s⁻¹ c)` of three generators, with the Koszul
twist on the middle one; it is the common value of the two cubic terms of `d_Ω (d_Ω (s⁻¹ c))`. -/
private noncomputable def cobarCubic : C ⊗[R] (C ⊗[R] C) →ₗ[R] TensorAlgebra R C :=
  LinearMap.mul' R (TensorAlgebra R C) ∘ₗ TensorProduct.map (ι R) (cobarQuadratic G)

private theorem cobarCubic_tmul (a : C) (w : C ⊗[R] C) :
    cobarCubic G (a ⊗ₜ w) = ι R a * cobarQuadratic G w := by
  simp [cobarCubic]

/-- The values `-s⁻¹ (d c) + (s⁻¹ ⊗ s⁻¹) (Δ c)` of the cobar differential on generators. -/
private noncomputable def cobarGenerator : C →ₗ[R] TensorAlgebra R C :=
  cobarQuadratic G ∘ₗ Δ - ι R ∘ₗ d

private theorem cobarGenerator_apply (c : C) :
    cobarGenerator G Δ d c = cobarQuadratic G (Δ c) - ι R (d c) := (rfl)

/-- The **differential of the cobar construction** `Ω C = T(s⁻¹ C)` of a noncounital differential
graded coalgebra `(C, Δ, d)`: the odd derivation of the tensor algebra on `C`, graded by
`tensorAlgebraPiece (G.shift (-1))` so that the generator `ι c = s⁻¹ c` has degree `|c| + 1`,
which sends `s⁻¹ c` to `-s⁻¹ (d c) + ∑ (-1) ^ |c'| s⁻¹ c' * s⁻¹ c''` for `Δ c = ∑ c' ⊗ c''`
(`cobarDifferential_ι`). -/
noncomputable def cobarDifferential : TensorAlgebra R C →ₗ[R] TensorAlgebra R C :=
  tensorAlgebraDerivation (G.shift (-1)) (cobarGenerator G Δ d)

private theorem cobarDifferential_ι_eq (c : C) :
    cobarDifferential G Δ d (ι R c) = cobarQuadratic G (Δ c) - ι R (d c) := by
  rw [cobarDifferential, tensorAlgebraDerivation_ι, cobarGenerator_apply]

/-- The cobar differential on a generator `s⁻¹ c`: the desuspended coproduct, with the Koszul twist
of the first tensor factor, minus the desuspended differential. -/
@[simp]
theorem cobarDifferential_ι (c : C) :
    cobarDifferential G Δ d (ι R c) =
      LinearMap.mul' R (TensorAlgebra R C)
          (TensorProduct.map (ι R ∘ₗ G.koszulTwist 1) (ι R) (Δ c)) - ι R (d c) := by
  rw [cobarDifferential_ι_eq, cobarQuadratic, LinearMap.comp_apply]

/-- The cobar differential annihilates the image of the ground ring. -/
@[simp]
theorem cobarDifferential_algebraMap (r : R) :
    cobarDifferential G Δ d (algebraMap R (TensorAlgebra R C) r) = 0 :=
  tensorAlgebraDerivation_algebraMap _ _ r

/-- The cobar differential annihilates the unit. -/
@[simp]
theorem cobarDifferential_one : cobarDifferential G Δ d 1 = 0 :=
  tensorAlgebraDerivation_one _ _

/-- The **graded Leibniz rule** of the cobar differential, for a left factor of degree `p` in the
cobar grading. -/
theorem cobarDifferential_mul {p : ℤ} {x : TensorAlgebra R C}
    (hx : x ∈ tensorAlgebraPiece (G.shift (-1)) p) (y : TensorAlgebra R C) :
    cobarDifferential G Δ d (x * y) =
      cobarDifferential G Δ d x * y + p.negOnePow • (x * cobarDifferential G Δ d y) :=
  tensorAlgebraDerivation_mul_of_mem _ _ hx y

namespace IsNonCounitalDGCoalgebra

variable {G Δ d}

variable (h : IsNonCounitalDGCoalgebra G Δ d)
include h

/-- The generator values have degree one in the cobar grading. -/
private theorem cobarGenerator_mem {p : ℤ} {c : C} (hc : c ∈ (G.shift (-1)).piece p) :
    cobarGenerator G Δ d c ∈ tensorAlgebraPiece (G.shift (-1)) (p + 1) := by
  rw [shift_piece] at hc
  rw [cobarGenerator_apply]
  refine sub_mem ?_ (ι_mem_tensorAlgebraPiece _ ?_)
  · refine G.tensorProduct_piece_le G
      (C := (tensorAlgebraPiece (G.shift (-1)) (p + 1)).comap (cobarQuadratic G))
      (fun q a ha b hb ↦ ?_) (by simpa using h.isHomogeneous_comul.map_mem hc)
    rw [Submodule.mem_comap, cobarQuadratic_tmul]
    have ha' : G.koszulTwist 1 a ∈ (G.shift (-1)).piece (q + 1) := by
      simpa using G.koszulTwist_mem_piece ha 1
    have hb' : b ∈ (G.shift (-1)).piece (p + -1 - q + 1) := by simpa using hb
    have hdeg : q + 1 + (p + -1 - q + 1) = p + 1 := by ring
    exact hdeg ▸ SetLike.GradedMul.mul_mem (ι_mem_tensorAlgebraPiece _ ha')
      (ι_mem_tensorAlgebraPiece _ hb')
  · simpa [add_assoc] using h.map_mem hc

/-- The cobar differential of a desuspended coproduct, before the coproduct is substituted:
on any `w = ∑ a ⊗ b`, the terms of `d_Ω (s⁻¹ a * s⁻¹ b)` quadratic in generators combine with the
desuspension of `(d ⊗ 1 + τ ⊗ d) w` to leave only the two cubic terms. -/
private theorem cobarDifferential_comp_cobarQuadratic :
    cobarDifferential G Δ d ∘ₗ cobarQuadratic G -
        cobarQuadratic G ∘ₗ (d.rTensor C + TensorProduct.map (G.koszulTwist 1) d) =
      cobarCubic G ∘ₗ (TensorProduct.assoc R C C C).toLinearMap ∘ₗ Δ.rTensor C -
        cobarCubic G ∘ₗ Δ.lTensor C := by
  refine TensorProduct.ext' fun a b ↦ ?_
  have hΔ : cobarQuadratic G (Δ (G.koszulTwist 1 a)) * ι R b =
      cobarCubic G (TensorProduct.assoc R C C C (Δ a ⊗ₜ b)) := by
    rw [h.comul_koszulTwist]
    induction Δ a using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, add_mul, TensorProduct.add_tmul, hw, hw']
    | tmul x y => simp [cobarQuadratic_tmul, cobarCubic_tmul, mul_assoc]
  -- Expand `d_Ω (s⁻¹ (τ a) * s⁻¹ b)` by the Leibniz rule; the Koszul sign of `s⁻¹ (τ a)` in the
  -- desuspended grading turns it back into `-s⁻¹ a`, and `d τ = -τ d` matches the quadratic terms.
  have hσ : (G.shift (-1)).koszulTwist 1 = -G.koszulTwist 1 := by
    rw [koszulTwist_shift]
    simp
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, map_add, map_neg,
    cobarQuadratic_tmul, cobarCubic_tmul, cobarDifferential, tensorAlgebraDerivation_mul,
    tensorAlgebraDerivation_ι, cobarGenerator_apply, koszulTwistAlgEquiv_apply,
    koszulTwist_tensorAlgebraPiece_ι,
    hσ, LinearMap.neg_apply, koszulTwist_koszulTwist,
    h.koszulTwist_differential, ← hΔ, sub_mul, mul_sub, neg_mul]
  abel

/-- **The cobar differential squares to zero on generators.** -/
theorem cobarDifferential_cobarDifferential_ι (c : C) :
    cobarDifferential G Δ d (cobarDifferential G Δ d (ι R c)) = 0 := by
  have hq := LinearMap.congr_fun (cobarDifferential_comp_cobarQuadratic h) (Δ c)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h.coassoc_apply,
    sub_self, sub_eq_zero] at hq
  rw [cobarDifferential_ι_eq, map_sub, hq, cobarDifferential_ι_eq, h.sq_zero, map_zero, sub_zero,
    h.comul_differential_apply, LinearMap.add_apply, sub_self]

/-- **The cobar differential squares to zero.** -/
theorem cobarDifferential_cobarDifferential (x : TensorAlgebra R C) :
    cobarDifferential G Δ d (cobarDifferential G Δ d x) = 0 :=
  tensorAlgebraDerivation_tensorAlgebraDerivation (cobarGenerator_mem h)
    (fun c ↦ by simpa [cobarDifferential] using h.cobarDifferential_cobarDifferential_ι c) x

/-- **The cobar construction is a differential graded algebra**: the tensor algebra on a
noncounital differential graded coalgebra `C`, graded so that the generator `s⁻¹ c` has degree
`|c| + 1`, with the cobar differential. -/
theorem isDGAlgebra_cobarDifferential :
    IsDGAlgebra (tensorAlgebraPiece (G.shift (-1))) (cobarDifferential G Δ d) :=
  isDGAlgebra_tensorAlgebraDerivation (cobarGenerator_mem h)
    (fun c ↦ by simpa [cobarDifferential] using h.cobarDifferential_cobarDifferential_ι c)

end IsNonCounitalDGCoalgebra

end TauCeti
