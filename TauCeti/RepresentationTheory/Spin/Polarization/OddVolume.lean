/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.RepresentationTheory.Spin.LineSign
-- Private: orthonormal-basis orthogonality and list products of endomorphisms are used only
-- inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.End.Basic

/-!
# The odd volume element on an adapted spinor module

Let `V` be an oriented real inner product space of odd dimension `n = 2ℓ + 1` and
`Q v = -‖v‖²`. The normalized complex volume element `ω_ℂ = i ^ (ℓ + 1) c(e₁) ⋯ c(eₙ)`
(`CliffordAlgebra.complexVolume`) is central in the complexified Clifford algebra and squares to
`1`, so it acts on every irreducible module by `+1` or `-1`, and these two values label the two
irreducible modules, that is, the two factors of the odd structure theorem.

The spinor modules of `V` are the exterior algebras `⋀ W` of polarizations
`ℂ ⊗ V = W ⊕ W' ⊕ L` of `Q_ℂ` (`TauCeti.spinAction`). A vector `z` of the remainder line `L` acts
on `⋀ W` by `λ` times exterior parity, where `λ = lineCoordinate z` and `λ² = Q z`
(`TauCeti.spinAction_ι_lineOperator`). This file computes the label of `⋀ W` in terms of `λ`. Take
a positively oriented orthonormal basis `(e₁, f₁, …, e_ℓ, f_ℓ, u)` of `V` adapted to the
polarization: every `eₖ - i fₖ` lies in `W`, every `eₖ + i fₖ` lies in `W'`, and `u` lies in `L`.
This is the situation of an orthogonal complex structure `J` on `u^⊥` with `fₖ = J eₖ`, for which
`eₖ - i fₖ` is twice the `(1, 0)`-part of `eₖ`. Then

`ω_ℂ` acts on `⋀ W` by `i λ`, where `λ = lineCoordinate u`.

Since `Q u = -1`, `λ = ±i`: the coordinate `λ = -i` gives the module labelled `ω_ℂ = +1`, and
`λ = i` the module labelled `ω_ℂ = -1`. Negating the line coordinate
(`TauCeti.SpinPolarizationData.negLineCoordinate`) negates `λ` and so passes to the other label.
The odd structure isomorphism `TauCeti.SpinPolarizationData.cliffordEquivEndProd` has the actions
of `P` and of its negation as its two components, so its first factor is the one on which `ω_ℂ`
acts by `i λ` and its second the one on which it acts by `-i λ`. Reversing the orientation negates
`ω_ℂ` (`CliffordAlgebra.complexVolume_neg_orientation`) and also interchanges the labels.

## Main results

* `TauCeti.SpinPolarizationData.spinAction_complexVolume`: on an adapted spinor module, `ω_ℂ`
  acts by `i λ`.
* `TauCeti.SpinPolarizationData.spinAction_negLineCoordinate_complexVolume`: for the opposite line
  coordinate it acts by `-i λ`.
* `TauCeti.SpinPolarizationData.lineCoordinate_eq_neg_I_or_eq_I`: the line coordinate of `u` is
  `-i` or `i`.
* `TauCeti.SpinPolarizationData.spinAction_complexVolume_eq_one_iff` and
  `TauCeti.SpinPolarizationData.spinAction_complexVolume_eq_neg_one_iff`: `ω_ℂ` acts by `1`
  exactly when `λ = -i`, and by `-1` exactly when `λ = i`.

## Implementation notes

`ω_ℂ` is central, so it acts on `⋀ W` by a scalar
(`TauCeti.exists_spinAction_eq_algebraMap_of_mem_center`), which is read off on the vacuum `1`.
There `c(u)` acts by `λ`, and each pair `c(eₖ) c(fₖ)` by `-i`: writing `eₖ = x + y` and
`fₖ = i (x - y)` with `x ∈ W` and `y ∈ W'`, the vacuum goes to `i x` and then to
`i · polar Q_ℂ x y = i Q(eₖ) = -i`. Hence `ω_ℂ 1 = i ^ (ℓ + 1) (-i) ^ ℓ λ = i λ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

noncomputable section

namespace TauCeti.SpinPolarizationData

open CliffordAlgebra Module
open scoped TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  (P : SpinPolarizationData (Q.baseChange ℂ))

/-- On the vacuum, the pair `c(e) c(f)` acts by `i Q(e)` whenever `e - i f ∈ W` and
`e + i f ∈ W'`. -/
private theorem spinAction_ι_mul_ι_apply_one {e f : V}
    (hW : 1 ⊗ₜ e - Complex.I ⊗ₜ f ∈ P.W) (hW' : 1 ⊗ₜ e + Complex.I ⊗ₜ f ∈ P.W') :
    spinAction _ P (ι (Q.baseChange ℂ) (1 ⊗ₜ e) * ι (Q.baseChange ℂ) (1 ⊗ₜ f)) 1 =
      (Complex.I * Q e) • 1 := by
  -- Split `1 ⊗ e = x + y` and `1 ⊗ f = i (x - y)` along `W ⊕ W'`.
  set x : P.W := (2 : ℂ)⁻¹ • ⟨_, hW⟩
  set y : P.W' := (2 : ℂ)⁻¹ • ⟨_, hW'⟩
  have hI (v : V) : (Complex.I ⊗ₜ v : ℂ ⊗[ℝ] V) = Complex.I • (1 ⊗ₜ v) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have he : (1 ⊗ₜ e : ℂ ⊗[ℝ] V) = (x : ℂ ⊗[ℝ] V) + y := by
    simp only [x, y, Submodule.coe_smul, hI]
    module
  have hf : (1 ⊗ₜ f : ℂ ⊗[ℝ] V) = Complex.I • ((x : ℂ ⊗[ℝ] V) - y) := by
    simp only [x, y, Submodule.coe_smul, hI]
    match_scalars
    · linear_combination Complex.I_mul_I
    · ring
  have hpolar : QuadraticMap.polar (Q.baseChange ℂ) x y = Q e := by
    rw [QuadraticMap.polar, ← he, P.isotropic_W, P.isotropic_W', QuadraticForm.baseChange_tmul,
      mul_one, sub_zero, sub_zero, Complex.real_smul, mul_one]
  -- `c(f)` sends the vacuum to `i x`, and `c(e)` sends `i x` to `i · polar Q_ℂ x y`.
  rw [hf, he]
  simp only [map_smul, map_sub, map_add, mul_smul_comm, map_mul, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, spinAction_ι_wedge,
    spinAction_ι_contract, mul_one, ExteriorAlgebra.ι_sq_zero, contractLeft_ι, contractLeft_one,
    zero_add, sub_zero, P.pairingEquiv_apply, hpolar,
    Algebra.algebraMap_eq_smul_one, smul_smul]

variable [FiniteDimensional ℝ V] {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ + 1)]
  {o : Orientation ℝ V (Fin (2 * ℓ + 1))} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin (2 * ℓ + 1)) ℝ V) (hb : b.toBasis.orientation = o)
  (hbW : ∀ k : Fin ℓ,
    1 ⊗ₜ b ⟨2 * k, by omega⟩ - Complex.I ⊗ₜ b ⟨2 * k + 1, by omega⟩ ∈ P.W)
  (hbW' : ∀ k : Fin ℓ,
    1 ⊗ₜ b ⟨2 * k, by omega⟩ + Complex.I ⊗ₜ b ⟨2 * k + 1, by omega⟩ ∈ P.W')
  (hline : 1 ⊗ₜ b (Fin.last (2 * ℓ)) ∈ P.line)
include hQ hb hbW hbW'

/-- **The odd volume element on an adapted spinor module.** Let `(e₁, f₁, …, e_ℓ, f_ℓ, u)` be a
positively oriented orthonormal basis of `V` with every `eₖ - i fₖ` in `W`, every `eₖ + i fₖ` in
`W'`, and `u` in the remainder line. Then `ω_ℂ` acts on `⋀ W` by `i λ`, where `λ` is the line
coordinate of `u`, so that `u` acts by `λ` times exterior parity. -/
theorem spinAction_complexVolume :
    spinAction _ P (complexVolume Q o) =
      algebraMap ℂ (Module.End ℂ (ExteriorAlgebra ℂ P.W))
        (Complex.I * P.lineCoordinate ⟨_, hline⟩) := by
  obtain ⟨a, ha⟩ := exists_spinAction_eq_algebraMap_of_mem_center P
    (complexVolume_mem_center o (odd_two_mul_add_one ℓ))
  rw [ha]
  congr 1
  have hQb (i : Fin (2 * ℓ + 1)) : Q (b i) = -1 := by rw [hQ, b.orthonormal.1 i]; norm_num
  have hu : spinAction _ P (ι (Q.baseChange ℂ) (1 ⊗ₜ b (Fin.last (2 * ℓ)))) 1 =
      P.lineCoordinate ⟨_, hline⟩ • 1 := by
    simpa using spinAction_ι_lineOperator P ⟨_, hline⟩ 1
  have hpairs : ((List.ofFn fun k : Fin ℓ ↦
      ι (Q.baseChange ℂ) (1 ⊗ₜ b ⟨2 * k, by omega⟩) *
        ι (Q.baseChange ℂ) (1 ⊗ₜ b ⟨2 * k + 1, by omega⟩)).map (spinAction _ P)).prod 1 =
      (-Complex.I) ^ ℓ • 1 := by
    rw [Module.End.list_prod_apply_eq_pow_smul (z := -Complex.I), List.length_map,
      List.length_ofFn]
    simp only [List.mem_map, List.mem_ofFn]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [P.spinAction_ι_mul_ι_apply_one (hbW k) (hbW' k), hQb]
    simp
  -- Evaluate both sides on the vacuum: `u` gives `λ`, and each of the `ℓ` pairs gives `-i`.
  have h1 := congr($ha 1)
  rw [complexVolume_eq_prod_pairs_mul b hb (b.isOrthoᵢ_associated hQ)] at h1
  simp only [map_smul, map_mul, map_list_prod, LinearMap.smul_apply, Module.End.mul_apply, hu,
    hpairs, Module.algebraMap_end_apply, smul_smul] at h1
  have hI : Complex.I ^ ℓ * (-1) ^ ℓ * Complex.I ^ ℓ = 1 := by
    rw [mul_comm, ← mul_assoc, ← mul_pow, Complex.I_mul_I, ← mul_pow]
    simp
  rw [← smul_left_injective ℂ (one_ne_zero (α := ExteriorAlgebra ℂ P.W)) h1, pow_succ, neg_pow]
  linear_combination (Complex.I * P.lineCoordinate ⟨_, hline⟩) * hI

/-- **The opposite line coordinate gives the other label**: for the polarization with negated line
coordinate, `ω_ℂ` acts on the same adapted module `⋀ W` by `-i λ`. -/
theorem spinAction_negLineCoordinate_complexVolume :
    spinAction _ P.negLineCoordinate (complexVolume Q o) =
      algebraMap ℂ (Module.End ℂ (ExteriorAlgebra ℂ P.W))
        (-(Complex.I * P.lineCoordinate ⟨_, hline⟩)) := by
  rw [P.negLineCoordinate.spinAction_complexVolume hQ b hb hbW hbW' hline,
    lineCoordinate_negLineCoordinate, mul_neg]

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 2 * ℓ + 1)] hb hbW hbW' in
/-- The line coordinate of the last basis vector `u` is `-i` or `i`, since its square is
`Q u = -1`. -/
theorem lineCoordinate_eq_neg_I_or_eq_I :
    P.lineCoordinate ⟨_, hline⟩ = -Complex.I ∨ P.lineCoordinate ⟨_, hline⟩ = Complex.I := by
  have h := P.lineCoordinate_sq ⟨_, hline⟩
  rw [QuadraticForm.baseChange_tmul, mul_one, hQ, b.orthonormal.1] at h
  refine (mul_self_eq_mul_self_iff.1 ?_).symm
  rw [h, Complex.I_mul_I]
  norm_num

/-- **The `+1` label**: `ω_ℂ` acts on an adapted spinor module by `1` exactly when the line
coordinate of `u` is `-i`. -/
theorem spinAction_complexVolume_eq_one_iff :
    spinAction _ P (complexVolume Q o) = 1 ↔ P.lineCoordinate ⟨_, hline⟩ = -Complex.I := by
  rw [P.spinAction_complexVolume hQ b hb hbW hbW' hline,
    (algebraMap ℂ (Module.End ℂ (ExteriorAlgebra ℂ P.W))).injective.eq_iff' (map_one _)]
  constructor
  · intro h
    linear_combination -Complex.I * h + P.lineCoordinate ⟨_, hline⟩ * Complex.I_mul_I
  · intro h
    rw [h, mul_neg, Complex.I_mul_I, neg_neg]

/-- **The `-1` label**: `ω_ℂ` acts on an adapted spinor module by `-1` exactly when the line
coordinate of `u` is `i`. -/
theorem spinAction_complexVolume_eq_neg_one_iff :
    spinAction _ P (complexVolume Q o) = -1 ↔ P.lineCoordinate ⟨_, hline⟩ = Complex.I := by
  rw [P.spinAction_complexVolume hQ b hb hbW hbW' hline,
    (algebraMap ℂ (Module.End ℂ (ExteriorAlgebra ℂ P.W))).injective.eq_iff'
      (by rw [map_neg, map_one])]
  constructor
  · intro h
    linear_combination -Complex.I * h + P.lineCoordinate ⟨_, hline⟩ * Complex.I_mul_I
  · intro h
    rw [h, Complex.I_mul_I]

end TauCeti.SpinPolarizationData
