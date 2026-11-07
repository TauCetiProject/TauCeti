/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.GLSymplectic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
public import TauCeti.Topology.Algebra.Matrix.Realify
public import TauCeti.Topology.Algebra.SymplecticGroup
public import TauCeti.Topology.Circle.Degree

/-!
# The Maslov index of a loop of symplectic matrices

Every real symplectic matrix `A` has a polar decomposition `A = P U` with `P` positive definite
and `U` orthogonal, and both factors are again symplectic. An orthogonal symplectic matrix is the
realification of a unique complex unitary matrix `U_ℂ`, so `A` determines the point

`ρ(A) = det_ℂ U_ℂ`

of the unit circle (`TauCeti.GLSymplectic.maslovPhase`), with the orthogonal polar factor
`TauCeti.GLSymplectic.polarUnitary`, the realification `TauCeti.GLSymplectic.ofUnitary` and the
determinant
`Matrix.UnitaryGroup.detCircle`. It depends continuously on `A`, and on
the orthogonal symplectic matrices, the realified unitary group `U(n)`, it is the complex
determinant. The **Maslov index** `μ(Ψ)` of a loop `Ψ` of symplectic matrices
(`TauCeti.GLSymplectic.maslovIndex`) is the degree of the circle loop `t ↦ ρ(Ψ t)`.

It satisfies the axioms of McDuff and Salamon, Theorem 2.2.12:

* **homotopy:** loops homotopic through loops of symplectic matrices, with a moving base point,
  have the same Maslov index (`TauCeti.GLSymplectic.maslovIndex_eq_of_homotopy`);
* **product:** the pointwise product of two loops has the sum of their Maslov indices,
  `μ(Φ Ψ) = μ(Φ) + μ(Ψ)` (`TauCeti.GLSymplectic.maslovIndex_mul`);
* **direct sum:** the direct sum of two loops has the sum of their Maslov indices,
  `μ(Φ ⊕ Ψ) = μ(Φ) + μ(Ψ)` (`TauCeti.GLSymplectic.maslovIndex_sum`), because `ρ` is
  multiplicative under direct sums (`TauCeti.GLSymplectic.maslovPhase_sum`);
* **normalization:** on loops of realified unitary matrices it is the degree of the complex
  determinant (`TauCeti.GLSymplectic.maslovIndex_map_ofUnitary`), so the loop
  `t ↦ e^{2π i t}` of `U(1) ⊆ Sp(2)` has Maslov index `1`, and more generally the loop of scalar
  matrices `t ↦ e^{2π i t} I` in `U(n) ⊆ Sp(2n)` has Maslov index `n`
  (`TauCeti.GLSymplectic.maslovIndex_scalarRotationLoop`).

Concatenation adds Maslov indices, reversal and pointwise inversion negate them, and a loop has
the Maslov index of its loop of orthogonal polar factors.

The map `ρ` is not multiplicative on the whole symplectic group, so the product axiom is proved
by a homotopy: contracting the positive factors of both loops through symplectic matrices
(`Matrix.GeneralLinearGroup.polarDeformation`) deforms `Φ Ψ` into the product of their orthogonal
factors, on which `ρ` is the multiplicative determinant, without changing the degree.

The Maslov index of loops of symplectic matrices measures the change of symplectic
trivialization along a loop. It enters the loop law of the Conley--Zehnder index of symplectic
paths, `CZ(Φ Ψ) = CZ(Ψ) + 2 μ(Φ)` for a loop `Φ`, and the definition of the relative first Chern
number of a symplectic bundle over a surface by clutching.

## Main definitions

* `TauCeti.GLSymplectic.maslovPhase`: the map `ρ : Sp(2n, ℝ) → S¹`.
* `TauCeti.GLSymplectic.maslovIndex`: the Maslov index of a loop of symplectic matrices.
* `TauCeti.GLSymplectic.scalarRotationLoop`: the loop `t ↦ e^{2π i t} I` in `U(n)`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (the map `ρ`,
  Proposition 2.2.11 for the polar decomposition, and Theorem 2.2.12 for the Maslov index of
  loops of symplectic matrices and its axioms).
-/

public section

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixOrder unitInterval


namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The map `ρ` -/

/-- The map `ρ : Sp(2n, ℝ) → S¹` of McDuff and Salamon: for a symplectic matrix `A = P U` with
`P` positive definite and `U` orthogonal, `ρ(A)` is the complex determinant of the unitary matrix
whose realification is `U`. -/
noncomputable def maslovPhase (A : GLSymplectic n ℝ) : Circle :=
  detCircle (unitaryGroupEquivSymplecticInfOrthogonal.symm (polarUnitary A))

/-- The map `ρ` is continuous. -/
theorem continuous_maslovPhase : Continuous (maslovPhase : GLSymplectic n ℝ → Circle) :=
  continuous_detCircle.comp
    (unitaryGroupEquivSymplecticInfOrthogonal.symm.continuous.comp continuous_polarUnitary)

/-- On an orthogonal symplectic matrix, the realification of a unitary matrix `U`, the map `ρ` is
the complex determinant of `U`. -/
@[simp]
theorem maslovPhase_inclusion (U : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    maslovPhase (Subgroup.inclusion inf_le_left U) =
      detCircle (unitaryGroupEquivSymplecticInfOrthogonal.symm U) := by
  rw [maslovPhase, polarUnitary_inclusion]

/-- On realified unitary matrices `ρ` is the complex determinant. -/
@[simp]
theorem maslovPhase_ofUnitary (U : unitaryGroup n ℂ) :
    maslovPhase (ofUnitary U) = detCircle U := by
  rw [ofUnitary_apply, maslovPhase_inclusion, ContinuousMulEquiv.symm_apply_apply]

/-- `ρ` sends the identity to `1`. -/
@[simp]
theorem maslovPhase_one : maslovPhase (1 : GLSymplectic n ℝ) = 1 := by
  simpa using maslovPhase_ofUnitary (1 : unitaryGroup n ℂ)

/-- `ρ` only depends on the orthogonal polar factor. -/
theorem maslovPhase_inclusion_polarUnitary (A : GLSymplectic n ℝ) :
    maslovPhase (Subgroup.inclusion inf_le_left (polarUnitary A)) = maslovPhase A := by
  rw [maslovPhase_inclusion, maslovPhase]

/-- `ρ` is multiplicative on the orthogonal symplectic matrices. -/
theorem maslovPhase_inclusion_mul (U V : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    maslovPhase (Subgroup.inclusion inf_le_left U * Subgroup.inclusion inf_le_left V) =
      maslovPhase (Subgroup.inclusion inf_le_left U) *
        maslovPhase (Subgroup.inclusion inf_le_left V) := by
  rw [← map_mul, maslovPhase_inclusion, maslovPhase_inclusion, maslovPhase_inclusion, map_mul,
    map_mul]

/-! ### The Maslov index of a loop -/

/-- The **Maslov index** of a loop `γ` of real symplectic matrices: the degree of the circle loop
`t ↦ ρ(γ t)`, where `ρ` is `TauCeti.GLSymplectic.maslovPhase`. -/
noncomputable def maslovIndex {A : GLSymplectic n ℝ} (γ : Path A A) : ℤ :=
  Circle.degree (γ.map continuous_maslovPhase)

/-- The Maslov index is the degree of the loop `t ↦ ρ(γ t)` in the circle. -/
theorem maslovIndex_def {A : GLSymplectic n ℝ} (γ : Path A A) :
    maslovIndex γ = Circle.degree (γ.map continuous_maslovPhase) :=
  (rfl)

/-- **Homotopy invariance.** If `F` is a homotopy from the loop `γ₀` to the loop `γ₁` through
loops of symplectic matrices (`F (s, 0) = F (s, 1)` for every `s`; the base point may move), the
two loops have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopy {A B : GLSymplectic n ℝ} (γ₀ : Path A A) (γ₁ : Path B B)
    (F : C(I × I, GLSymplectic n ℝ)) (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t)
    (hF : ∀ s, F (s, 0) = F (s, 1)) :
    maslovIndex γ₀ = maslovIndex γ₁ :=
  Circle.degree_eq_of_homotopy _ _
    ((⟨maslovPhase, continuous_maslovPhase⟩ : C(GLSymplectic n ℝ, Circle)).comp F)
    (fun t ↦ by simp [h₀]) (fun t ↦ by simp [h₁]) (fun s ↦ by simp [hF])

/-- Loops of symplectic matrices that are homotopic relative to their base point have the same
Maslov index. -/
theorem maslovIndex_eq_of_homotopic {A : GLSymplectic n ℝ} {γ₀ γ₁ : Path A A}
    (h : γ₀.Homotopic γ₁) : maslovIndex γ₀ = maslovIndex γ₁ :=
  Circle.degree_eq_of_homotopic (h.map ⟨maslovPhase, continuous_maslovPhase⟩)

/-- A constant loop has Maslov index zero. -/
@[simp]
theorem maslovIndex_refl (A : GLSymplectic n ℝ) : maslovIndex (Path.refl A) = 0 :=
  (Circle.degree_congr _ (Path.refl (maslovPhase A)) fun _ ↦ by simp).trans (Circle.degree_refl _)

/-- The Maslov index is additive under concatenation of loops. -/
@[simp]
theorem maslovIndex_trans {A : GLSymplectic n ℝ} (γ₁ γ₂ : Path A A) :
    maslovIndex (γ₁.trans γ₂) = maslovIndex γ₁ + maslovIndex γ₂ := by
  rw [maslovIndex, Path.map_trans, Circle.degree_trans, maslovIndex, maslovIndex]

/-- Reversing a loop negates its Maslov index. -/
@[simp]
theorem maslovIndex_symm {A : GLSymplectic n ℝ} (γ : Path A A) :
    maslovIndex γ.symm = -maslovIndex γ := by
  rw [maslovIndex, ← Path.map_symm, Circle.degree_symm, maslovIndex]

/-- **Normalization on the unitary group.** The Maslov index of a loop of realified unitary
matrices is the degree of the loop of their complex determinants. -/
theorem maslovIndex_map_ofUnitary {U : unitaryGroup n ℂ} (γ : Path U U) :
    maslovIndex (γ.map continuous_ofUnitary) = Circle.degree (γ.map continuous_detCircle) :=
  Circle.degree_congr _ _ fun t ↦ by simp

/-- The Maslov index of a loop is that of the loop of its orthogonal polar factors. -/
theorem maslovIndex_map_polarUnitary {A : GLSymplectic n ℝ} (γ : Path A A) :
    maslovIndex (γ.map continuous_inclusion_polarUnitary) = maslovIndex γ :=
  Circle.degree_congr _ _ fun t ↦ maslovPhase_inclusion_polarUnitary (γ t)

/-- **The product axiom.** The pointwise product of two loops of symplectic matrices has the sum
of their Maslov indices. -/
theorem maslovIndex_mul {A B : GLSymplectic n ℝ} (γ₁ : Path A A) (γ₂ : Path B B) :
    maslovIndex (γ₁.mul γ₂) = maslovIndex γ₁ + maslovIndex γ₂ := by
  -- Contract the positive polar factors of both loops at once, through symplectic matrices.
  let D : GLSymplectic n ℝ × I → GLSymplectic n ℝ := fun p ↦
    ⟨polarDeformation (p.1 : GL (n ⊕ n) ℝ) p.2, polarDeformation_mem p.1.2 _⟩
  have hD : Continuous D := by
    refine Continuous.subtype_mk ?_ _
    have h := (polarHomotopy (n ⊕ n) ℝ).continuous.comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst) :
        Continuous fun p : GLSymplectic n ℝ × I ↦ (p.2, (p.1 : GL (n ⊕ n) ℝ)))
    simpa only [Function.comp_def, polarHomotopy_apply] using h
  have hD0 (A : GLSymplectic n ℝ) : D (A, 0) = A := Subtype.ext (by simp [D])
  have hD1 (A : GLSymplectic n ℝ) : D (A, 1) = Subgroup.inclusion inf_le_left (polarUnitary A) :=
    Subtype.ext (Units.ext (by simp [D]))
  let F : C(I × I, Circle) :=
    ⟨fun p ↦ maslovPhase (D (γ₁ p.2, p.1) * D (γ₂ p.2, p.1)),
      continuous_maslovPhase.comp
        ((hD.comp ((γ₁.continuous.comp continuous_snd).prodMk continuous_fst)).mul
          (hD.comp ((γ₂.continuous.comp continuous_snd).prodMk continuous_fst)))⟩
  rw [maslovIndex, maslovIndex, maslovIndex, ← Circle.degree_mul]
  refine Circle.degree_eq_of_homotopy _ _ F (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)
  · simp only [F, ContinuousMap.coe_mk, hD0, Path.map_coe, Function.comp_apply, Path.mul_apply]
  · -- After the contraction both factors are orthogonal, where `ρ` is multiplicative.
    simp only [F, ContinuousMap.coe_mk, hD1, Path.mul_apply, Path.map_coe, Function.comp_apply]
    rw [maslovPhase_inclusion_mul, maslovPhase_inclusion_polarUnitary,
      maslovPhase_inclusion_polarUnitary]
  · simp only [F, ContinuousMap.coe_mk, Path.source, Path.target]

/-- The pointwise inverse of a loop has the opposite Maslov index. -/
@[simp]
theorem maslovIndex_inv {A : GLSymplectic n ℝ} (γ : Path A A) :
    maslovIndex γ.inv = -maslovIndex γ := by
  have h := maslovIndex_mul γ.inv γ
  have h1 : maslovIndex (γ.inv.mul γ) = 0 :=
    (Circle.degree_congr _ (Path.refl 1) fun t ↦ by simp).trans (Circle.degree_refl 1)
  omega

/-! ### The loop of scalar rotations -/

/-- The loop `t ↦ e^{2π i t} I` of scalar unitary matrices, based at the identity. -/
noncomputable def scalarRotationLoop (n : Type*) [Fintype n] [DecidableEq n] :
    Path (1 : unitaryGroup n ℂ) 1 where
  toFun t := ⟨(Circle.exp (2 * Real.pi * t) : ℂ) • (1 : Matrix n n ℂ),
    Unitary.smul_mem_of_mem (Circle.exp _).coe_mem_unitary (one_mem _)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

/-- The loop of scalar rotations at time `t` is the scalar matrix `e^{2π i t} I`. -/
@[simp]
theorem coe_scalarRotationLoop_apply (t : I) :
    (scalarRotationLoop n t : Matrix n n ℂ) = (Circle.exp (2 * Real.pi * t) : ℂ) • 1 :=
  (rfl)

/-- **Normalization.** The loop of scalar rotations `t ↦ e^{2π i t} I` in `U(n) ⊆ Sp(2n, ℝ)` has
Maslov index `n`; for `n = 1` this is the loop `t ↦ e^{2π i t}` in `U(1) ⊆ Sp(2, ℝ)`, of Maslov
index `1`. -/
theorem maslovIndex_scalarRotationLoop :
    maslovIndex ((scalarRotationLoop n).map continuous_ofUnitary) = Fintype.card n := by
  rw [maslovIndex_map_ofUnitary]
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ Fintype.card n * (2 * Real.pi * t))
    (by fun_prop) (fun t ↦ ?_) (by simp only [Set.Icc.coe_one, Set.Icc.coe_zero]; push_cast; ring)
  apply Circle.ext
  simp only [Path.map_coe, Function.comp_apply, coe_detCircle, coe_scalarRotationLoop_apply,
    det_smul, det_one, mul_one, Circle.coe_exp, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-! ### Direct sums -/

section Sum

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `ρ` is multiplicative under direct sums: `ρ(A ⊕ B) = ρ(A) ρ(B)`. -/
@[simp]
theorem maslovPhase_sum (A : GLSymplectic n ℝ) (B : GLSymplectic m ℝ) :
    maslovPhase (sum (A, B)) = maslovPhase A * maslovPhase B := by
  set V := unitaryGroupEquivSymplecticInfOrthogonal.symm (polarUnitary A)
  set W := unitaryGroupEquivSymplecticInfOrthogonal.symm (polarUnitary B)
  have hV := congrArg Units.val
    (realify_toUnits_unitaryGroupEquivSymplecticInfOrthogonal_symm_apply (polarUnitary A))
  have hW := congrArg Units.val
    (realify_toUnits_unitaryGroupEquivSymplecticInfOrthogonal_symm_apply (polarUnitary B))
  rw [coe_realify, Unitary.val_toUnits_apply] at hV hW
  have key : polarUnitary (sum (A, B)) =
      unitaryGroupEquivSymplecticInfOrthogonal (UnitaryGroup.sum (V, W)) := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_polarUnitary_sum, unitaryGroupEquivSymplecticInfOrthogonal_apply, coe_realify,
      Unitary.val_toUnits_apply, UnitaryGroup.coe_sum, realify_fromBlocks_zero, hV, hW]
  rw [maslovPhase, key, ContinuousMulEquiv.symm_apply_apply, maslovPhase, maslovPhase]
  exact detCircle_sum (V, W)

/-- **The direct-sum axiom.** The direct sum of two loops of symplectic matrices has the sum of
their Maslov indices. -/
theorem maslovIndex_sum {A : GLSymplectic n ℝ} {B : GLSymplectic m ℝ} (γ₁ : Path A A)
    (γ₂ : Path B B) :
    maslovIndex ((γ₁.prod γ₂).map continuous_sum) = maslovIndex γ₁ + maslovIndex γ₂ := by
  rw [maslovIndex, maslovIndex, maslovIndex, ← Circle.degree_mul]
  exact Circle.degree_congr _ _ fun t ↦ by simp

end Sum

end TauCeti.GLSymplectic
