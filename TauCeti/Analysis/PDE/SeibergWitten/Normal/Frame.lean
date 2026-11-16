/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Clifford and self-dual frames for the normal Seiberg–Witten model

Around a complex curve in an oriented four-manifold with compatible almost complex structure `J`, a
positively oriented `J`-unitary tangent-normal frame `e` (`J e₀ = e₁`, `J e₂ = e₃`) and a unit
canonical spinor `u₀ ∈ W⁺` compare the four-dimensional gauge-fixed linearized Seiberg–Witten
operator between `Ω¹(V) × W⁺` and `ℝ × Λ⁺ V × W⁻` with the planar vortex operators `(L_x, L_x*)`
on pairs `(y, η) ∈ ℝ⁴ × ℝ⁴`.

This file completes `kahlerSelfDual` to the real orthonormal frame `(ω_u, ρ₁, ρ₂)` of `Λ⁺ V`,
builds the anti-canonical half-spinor `v₀ = c(e₀) c(e₂) u₀` completing `u₀` to an orthonormal basis
of `W⁺`, proves the cross-term polarization identity for `quadraticTwoFormPolar` on `(α u₀, β v₀)`,
and constructs the eight-real-component domain and target linear equivalences `normalDomainEquiv`
and `normalTargetEquiv` together with their weighted component norm identities.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

/-- Scoped shorthand for `ℝ⁴` equipped with its `L²` Euclidean norm. -/
scoped notation "E4" => (EuclideanSpace ℝ (Fin 4))
local notation "OneForm(" V ")" => ((V) [⋀^Fin 1]→L[ℝ] ℝ)
local notation "SD(" V ", " o ", " hkl ")" =>
  (Module.End.eigenspace (Orientation.hodgeStar (o) (hkl) : Module.End ℝ (⋀[ℝ]^2 (V))) 1)
local notation "PosSpin(" o ", " ρ ")" => (positiveHalfSpinors (o) (ρ))
local notation "NegSpin(" Q ", " o ", " ρ ")" =>
  (Module.End.eigenspace ((ρ) (chirality (Q) (o))) (-1))
local notation "cMul(" o ", " ρ ", " v ", " ψ ")" =>
  (CliffordAlgebra.halfSpinCliffordMul (o) (ρ) 1 (v)
    (LinearEquiv.ofEq _ _ (CliffordAlgebra.positiveHalfSpinors_eq_eigenspace (o) (ρ)) (ψ)))

/-! ### Orthonormal self-dual frame of `Λ⁺` -/
section SelfDualFrame
variable (o e) in
/-- The first anti-`J`-invariant unit self-dual two-vector `ρ₁ = (√2 / 2)(e₀ ∧ e₂ - e₁ ∧ e₃)`. -/
def antiInvariantSelfDual₁ (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    SD(V, o, hkl) :=
  ⟨(√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 2] - ιMulti ℝ 2 ![e 1, e 3]),
    Module.End.mem_eigenspace_iff.2 <| by
      have h13 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 3]) = -ιMulti ℝ 2 ![e 0, e 2] := by
        rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he,
          map_neg, o.hodgeStar_hodgeStar_of_even even_two hkl]
      simp only [LinearEquiv.coe_coe, map_smul, map_sub, o.hodgeStar_ιMulti_zero_two hkl he, h13,
        one_smul]; module⟩
@[simp] theorem coe_antiInvariantSelfDual₁ (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) : (antiInvariantSelfDual₁ o e hkl he : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 2] - ιMulti ℝ 2 ![e 1, e 3]) := (rfl)
variable (o e) in
/-- The second anti-`J`-invariant unit self-dual two-vector `ρ₂ = (√2 / 2)(e₀ ∧ e₃ + e₁ ∧ e₂)`. -/
def antiInvariantSelfDual₂ (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    SD(V, o, hkl) :=
  ⟨(√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 3] + ιMulti ℝ 2 ![e 1, e 2]),
    Module.End.mem_eigenspace_iff.2 <| by
      have h12 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 2]) = ιMulti ℝ 2 ![e 0, e 3] := by
        rw [← o.hodgeStar_ιMulti_zero_three hkl he, o.hodgeStar_hodgeStar_of_even even_two hkl]
      simp [o.hodgeStar_ιMulti_zero_three hkl he, h12, add_comm]⟩
@[simp] theorem coe_antiInvariantSelfDual₂ (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) : (antiInvariantSelfDual₂ o e hkl he : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 3] + ιMulti ℝ 2 ![e 1, e 2]) := (rfl)
private theorem inner_basis_ιMulti {i j k l : Fin 4} :
    ⟪ιMulti ℝ 2 ![e i, e j], ιMulti ℝ 2 ![e k, e l]⟫ =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) -
        (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  rw [inner_ιMulti_two]; simp [orthonormal_iff_ite.1 e.orthonormal]

section InnerAndNorm
variable {hkl : 2 + 2 = finrank ℝ V} {he : e.toBasis.orientation = o}
  {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3}

@[simp] theorem norm_antiInvariantSelfDual₁ : ‖antiInvariantSelfDual₁ o e hkl he‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 <| by
    rw [← real_inner_self_eq_norm_sq, Submodule.coe_inner, coe_antiInvariantSelfDual₁]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
      inner_basis_ιMulti]
    norm_num [div_eq_mul_inv]; linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
@[simp] theorem norm_antiInvariantSelfDual₂ : ‖antiInvariantSelfDual₂ o e hkl he‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 <| by
    rw [← real_inner_self_eq_norm_sq, Submodule.coe_inner, coe_antiInvariantSelfDual₂]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      inner_basis_ιMulti]
    norm_num [div_eq_mul_inv]; linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
@[simp] theorem inner_kahlerSelfDual_antiInvariantSelfDual₁ :
    ⟪kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₁ o e hkl he⟫ = 0 := by
  rw [Submodule.coe_inner, coe_kahlerSelfDual, coe_antiInvariantSelfDual₁,
    AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
    inner_basis_ιMulti]; norm_num
@[simp] theorem inner_kahlerSelfDual_antiInvariantSelfDual₂ :
    ⟪kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₂ o e hkl he⟫ = 0 := by
  rw [Submodule.coe_inner, coe_kahlerSelfDual, coe_antiInvariantSelfDual₂,
    AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    inner_basis_ιMulti]; norm_num
@[simp] theorem inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂ :
    ⟪antiInvariantSelfDual₁ o e hkl he, antiInvariantSelfDual₂ o e hkl he⟫ = 0 := by
  rw [Submodule.coe_inner, coe_antiInvariantSelfDual₁, coe_antiInvariantSelfDual₂]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_add_right,
    inner_basis_ιMulti]; norm_num
end InnerAndNorm
private theorem orthonormal_selfDualTuple (o : Orientation ℝ V (Fin 4))
    (e : OrthonormalBasis (Fin 4) ℝ V) (J : AlmostComplexStructure V)
    (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    Orthonormal ℝ ![kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₁ o e hkl he,
      antiInvariantSelfDual₂ o e hkl he] := by
  have hk := norm_kahlerSelfDual (hkl := hkl) (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
  have h1 := norm_antiInvariantSelfDual₁ (hkl := hkl) (he := he)
  have h2 := norm_antiInvariantSelfDual₂ (hkl := hkl) (he := he)
  have hk1 := inner_kahlerSelfDual_antiInvariantSelfDual₁ (hkl := hkl) (he := he) (h₀ := h₀)
    (h₂₃ := h₂₃)
  have hk2 := inner_kahlerSelfDual_antiInvariantSelfDual₂ (hkl := hkl) (he := he) (h₀ := h₀)
    (h₂₃ := h₂₃)
  have h12 := inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂ (hkl := hkl) (he := he)
  exact ⟨fun i ↦ by fin_cases i <;> assumption, fun {i j} hij ↦ by
    fin_cases i <;> fin_cases j <;>
      first | contradiction | assumption | rwa [real_inner_comm]⟩
private theorem selfDual_coords_and_norm {hkl : 2 + 2 = finrank ℝ V}
    {he : e.toBasis.orientation = o} {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3} (a b c : ℝ) :
    let sd := a • kahlerSelfDual o J hkl he h₀ h₂₃ + b • antiInvariantSelfDual₁ o e hkl he +
      c • antiInvariantSelfDual₂ o e hkl he
    ⟪kahlerSelfDual o J hkl he h₀ h₂₃, sd⟫ = a ∧ ⟪antiInvariantSelfDual₁ o e hkl he, sd⟫ = b ∧
      ⟪antiInvariantSelfDual₂ o e hkl he, sd⟫ = c ∧ ‖sd‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  have h {f : Fin 3 → SD(V, o, hkl)} (hf : Orthonormal ℝ f) :
      let sd := a • f 0 + b • f 1 + c • f 2
      ⟪f 0, sd⟫ = a ∧ ⟪f 1, sd⟫ = b ∧ ⟪f 2, sd⟫ = c ∧ ‖sd‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    intro sd; rw [← real_inner_self_eq_norm_sq]
    simp only [sd, Submodule.coe_inner, Submodule.coe_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    simp only [← Submodule.coe_inner, orthonormal_iff_ite.1 hf]; norm_num; ring
  exact h (orthonormal_selfDualTuple o e J hkl he h₀ h₂₃)
/-- **The real orthonormal basis `(ω_u, ρ₁, ρ₂)` of `Λ⁺ V`** induced by `e`. -/
def selfDualOrthonormalBasis (o : Orientation ℝ V (Fin 4)) (e : OrthonormalBasis (Fin 4) ℝ V)
    (J : AlmostComplexStructure V) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    OrthonormalBasis (Fin 3) ℝ SD(V, o, hkl) :=
  have hcard : Fintype.card (Fin 3) = finrank ℝ SD(V, o, hkl) := by
    have hsd := o.two_mul_finrank_eigenspace_hodgeStar_one even_two two_pos hkl
    rw [show Nat.choose 4 2 = 6 by decide] at hsd; rw [Fintype.card_fin]; omega
  (basisOfOrthonormalOfCardEqFinrank (orthonormal_selfDualTuple o e J hkl he h₀ h₂₃) hcard)
    |>.toOrthonormalBasis (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact
      orthonormal_selfDualTuple o e J hkl he h₀ h₂₃)
@[simp] theorem coe_selfDualOrthonormalBasis (o : Orientation ℝ V (Fin 4))
    (e : OrthonormalBasis (Fin 4) ℝ V) (J : AlmostComplexStructure V)
    (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    (selfDualOrthonormalBasis o e J hkl he h₀ h₂₃ : Fin 3 → _) =
      ![kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₁ o e hkl he,
        antiInvariantSelfDual₂ o e hkl he] := by
  rw [selfDualOrthonormalBasis, Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
/-- Orthogonal expansion of any self-dual two-vector `τ ∈ Λ⁺ V` along `(ω_u, ρ₁, ρ₂)`. -/
theorem eq_inner_kahlerSelfDual_add_antiInvariantSelfDual {hkl : 2 + 2 = finrank ℝ V}
    {he : e.toBasis.orientation = o} {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3}
    (τ : SD(V, o, hkl)) :
    τ = ⟪kahlerSelfDual o J hkl he h₀ h₂₃, τ⟫ • kahlerSelfDual o J hkl he h₀ h₂₃ +
      ⟪antiInvariantSelfDual₁ o e hkl he, τ⟫ • antiInvariantSelfDual₁ o e hkl he +
      ⟪antiInvariantSelfDual₂ o e hkl he, τ⟫ • antiInvariantSelfDual₂ o e hkl he := by
  have h := ((selfDualOrthonormalBasis o e J hkl he h₀ h₂₃).sum_repr' τ).symm
  rwa [Fin.sum_univ_three, coe_selfDualOrthonormalBasis] at h
end SelfDualFrame

/-! ### The anti-canonical spinor `v₀ = c(e₀) c(e₂) u₀` and half-spinor frames -/

section SpinorFrame
variable (o ρ e) in
/-- The **anti-canonical positive half-spinor** `v₀ = c(e₀) c(e₂) u₀` associated to `u₀ ∈ W⁺`. -/
def antiCanonicalSpinor (u₀ : PosSpin(o, ρ)) : PosSpin(o, ρ) :=
  ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀), by
    rw [mem_positiveHalfSpinors]
    have h₁ := map_ι_apply_mem_eigenspace_chirality_neg o (ε := 1)
      (Module.End.mem_eigenspace_iff.2 (by simpa using mem_positiveHalfSpinors.1 u₀.2)) (e 2)
    simpa using Module.End.mem_eigenspace_iff.1
      (map_ι_apply_mem_eigenspace_chirality_neg o (ε := -1) h₁ (e 0))⟩
/-- Scoped shorthand for the anti-canonical half-spinor `antiCanonicalSpinor o ρ e`. -/
scoped notation "antiSpin(" o ", " ρ ", " e ")" => (antiCanonicalSpinor (o) (ρ) (e))
omit [FiniteDimensional ℂ W] in @[simp] theorem coe_antiCanonicalSpinor (u₀ : PosSpin(o, ρ)) :
    (antiSpin(o, ρ, e) u₀ : W) = ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := (rfl)
section CliffordRelations
variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ
omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
private theorem ι_apply_self_basis (i : Fin 4) (w : W) : ρ (ι Q (e i)) (ρ (ι Q (e i)) w) = -w := by
  rw [map_ι_apply_map_ι_apply, hQ, e.orthonormal.1 i]; norm_num
omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
private theorem ι_apply_comm_basis {i j : Fin 4} (hij : i ≠ j) (w : W) :
    ρ (ι Q (e i)) (ρ (ι Q (e j)) w) = -ρ (ι Q (e j)) (ρ (ι Q (e i)) w) := by
  simpa only [map_mul, map_neg, mul_apply_eq_comp, LinearMap.neg_apply] using
    congrArg (fun a ↦ ρ a w) (ι_mul_ι_comm_of_isOrtho (e.isOrtho_apply hQ hij))
omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
private theorem ι_apply_conj_basis {i j : Fin 4} (hij : i ≠ j) (w : W) :
    ρ (ι Q (e i)) (ρ (ι Q (e j)) (ρ (ι Q (e i)) w)) = ρ (ι Q (e j)) w := by
  rw [ι_apply_comm_basis hQ hij.symm, map_neg, ι_apply_self_basis hQ i, neg_neg]
/-- `antiCanonicalSpinor` preserves the norm when vector Clifford action is skew-adjoint. -/
theorem norm_antiCanonicalSpinor (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (u₀ : PosSpin(o, ρ)) : ‖antiSpin(o, ρ, e) u₀‖ = ‖u₀‖ := by
  rw [← Submodule.norm_coe, coe_antiCanonicalSpinor, norm_map_ι_apply hQ hρ, norm_map_ι_apply hQ hρ,
    e.orthonormal.1 0, e.orthonormal.1 2, one_mul, one_mul, Submodule.norm_coe]
omit [FiniteDimensional ℂ W] in
/-- Clifford action of `e₀` on `v₀ = c(e₀) c(e₂) u₀`: `c(e₀) v₀ = -c(e₂) u₀`. -/
theorem ι_apply_zero_antiCanonicalSpinor (u₀ : PosSpin(o, ρ)) :
    ρ (ι Q (e 0)) (antiSpin(o, ρ, e) u₀) = -ρ (ι Q (e 2)) u₀ := by
  rw [coe_antiCanonicalSpinor, ι_apply_self_basis hQ 0]
omit [FiniteDimensional ℂ W] in
/-- Clifford action of `e₂` on `v₀ = c(e₀) c(e₂) u₀`: `c(e₂) v₀ = c(e₀) u₀`. -/
theorem ι_apply_two_antiCanonicalSpinor (u₀ : PosSpin(o, ρ)) :
    ρ (ι Q (e 2)) (antiSpin(o, ρ, e) u₀) = ρ (ι Q (e 0)) u₀ := by
  rw [coe_antiCanonicalSpinor, ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0),
    ι_apply_self_basis hQ 2, map_neg, neg_neg]

variable (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
include hkl he h₀ h₂₃

private theorem ι_apply_one_canonical {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) u₀ = I • ρ (ι Q (e 0)) u₀ :=
  h₀ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)
private theorem ι_apply_three_canonical {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 3)) u₀ = I • ρ (ι Q (e 2)) u₀ :=
  h₂₃ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
private theorem ι_one_ι_two_canonical {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 2)) u₀) = I • (antiSpin(o, ρ, e) u₀ : W) := by
  rw [ι_apply_comm_basis hQ (by decide : (1 : Fin 4) ≠ 2),
    ι_apply_one_canonical hQ hkl he h₀ h₂₃ hu₀, map_smul,
    ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0)]
  simp [coe_antiCanonicalSpinor]
private theorem ι_one_ι_three_canonical {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 3)) u₀) = -(antiSpin(o, ρ, e) u₀ : W) := by
  rw [ι_apply_three_canonical hQ hkl he h₀ h₂₃ hu₀, map_smul,
    ι_one_ι_two_canonical hQ hkl he h₀ h₂₃ hu₀]
  simp [smul_smul]
/-- The Kähler bivector acts on the anti-canonical spinor `v₀` with eigenvalue `2i`. -/
theorem bivectorExterior_kahlerForm_antiCanonicalSpinor {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (bivectorExterior Q J.kahlerForm) (antiSpin(o, ρ, e) u₀) =
      (2 * I) • (antiSpin(o, ρ, e) u₀ : W) := by
  have ha : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (antiSpin(o, ρ, e) u₀)) =
      I • (antiSpin(o, ρ, e) u₀ : W) := by
    conv_lhs => rw [coe_antiCanonicalSpinor]
    rw [ι_apply_conj_basis hQ (by decide : (0 : Fin 4) ≠ 1),
      ι_one_ι_two_canonical hQ hkl he h₀ h₂₃ hu₀]
  have hb : ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (antiSpin(o, ρ, e) u₀)) =
      I • (antiSpin(o, ρ, e) u₀ : W) := by
    conv_lhs => rw [coe_antiCanonicalSpinor, ι_apply_comm_basis hQ (by decide : (0 : Fin 4) ≠ 2)]
    simp only [map_neg]
    rw [ι_apply_conj_basis hQ (by decide : (2 : Fin 4) ≠ 3),
      ι_apply_comm_basis hQ (by decide : (3 : Fin 4) ≠ 0),
      ι_apply_three_canonical hQ hkl he h₀ h₂₃ hu₀]
    simp [coe_antiCanonicalSpinor]
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂₃]
  simp only [map_add, map_mul, LinearMap.add_apply, mul_apply_eq_comp, ha, hb]
  module
/-- The canonical Kähler Clifford projection annihilates `v₀`. -/
@[simp] theorem cliffordProjection_antiCanonicalSpinor {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ J.kahlerForm (antiSpin(o, ρ, e) u₀) = 0 :=
  cliffordProjection_apply_eq_zero_of_bivectorExterior_apply o ρ
    (bivectorExterior_kahlerForm_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀)
/-- The complementary Kähler Clifford projection fixes `v₀`. -/
@[simp] theorem cliffordProjection_neg_antiCanonicalSpinor {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ (-J.kahlerForm) (antiSpin(o, ρ, e) u₀) = antiSpin(o, ρ, e) u₀ := by
  rw [cliffordProjection_neg_apply, cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀,
    sub_zero]
/-- Clifford action of `e₁` on `v₀`: `c(e₁) v₀ = i c(e₂) u₀`. -/
theorem ι_apply_one_antiCanonicalSpinor {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (antiSpin(o, ρ, e) u₀) = I • ρ (ι Q (e 2)) u₀ := by
  rw [← h₀, ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂₃
    (cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀),
    ι_apply_zero_antiCanonicalSpinor hQ, smul_neg, neg_smul, neg_neg]
/-- Clifford action of `e₃` on `v₀`: `c(e₃) v₀ = -i c(e₀) u₀`. -/
theorem ι_apply_three_antiCanonicalSpinor {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 3)) (antiSpin(o, ρ, e) u₀) = -I • ρ (ι Q (e 0)) u₀ := by
  rw [← h₂₃, ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂₃
    (cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀),
    ι_apply_two_antiCanonicalSpinor hQ]
/-- A canonical spinor `u₀` and its anti-canonical partner `v₀` are orthogonal in `W⁺`. -/
theorem inner_antiCanonicalSpinor_eq_zero (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : PosSpin(o, ρ)} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ⟪u₀, antiSpin(o, ρ, e) u₀⟫_ℂ = 0 :=
  calc ⟪u₀, antiSpin(o, ρ, e) u₀⟫_ℂ
      = ⟪cliffordProjection o ρ J.kahlerForm u₀, antiSpin(o, ρ, e) u₀⟫_ℂ := by rw [hu₀]
    _ = ⟪u₀, cliffordProjection o ρ J.kahlerForm (antiSpin(o, ρ, e) u₀)⟫_ℂ :=
        (isSelfAdjoint_cliffordProjection o J.kahlerForm hρ).isSymmetric _ _
    _ = 0 := by rw [cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, inner_zero_right]
/-- Action of `cliffordRestriction` at `ρ₁` on a canonical spinor `u₀`: `c(ρ₁) u₀ = i √2 v₀`. -/
theorem cliffordRestriction_antiInvariantSelfDual₁_apply {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordRestriction o ρ (antiInvariantSelfDual₁ o e hkl he) u₀ =
      (I * (√2 : ℂ)) • antiSpin(o, ρ, e) u₀ := Subtype.ext <| by
  rw [coe_antiInvariantSelfDual₁, map_smul, map_sub, smul_apply, sub_apply,
    Submodule.coe_smul_of_tower, Submodule.coe_sub,
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (0 : Fin 4) ≠ 2)),
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (1 : Fin 4) ≠ 3))]
  simp only [map_mul, mul_apply_eq_comp, ι_one_ι_three_canonical hQ hkl he h₀ h₂₃ hu₀,
    ← coe_antiCanonicalSpinor, Submodule.coe_smul, ← Complex.coe_smul]
  push_cast; module
/-- Action of `cliffordRestriction` at `ρ₂` on a canonical spinor `u₀`: `c(ρ₂) u₀ = -√2 v₀`. -/
theorem cliffordRestriction_antiInvariantSelfDual₂_apply {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordRestriction o ρ (antiInvariantSelfDual₂ o e hkl he) u₀ =
      (-(√2 : ℂ)) • antiSpin(o, ρ, e) u₀ := Subtype.ext <| by
  rw [coe_antiInvariantSelfDual₂, map_smul, map_add, smul_apply, add_apply,
    Submodule.coe_smul_of_tower, Submodule.coe_add,
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (0 : Fin 4) ≠ 3)),
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (1 : Fin 4) ≠ 2))]
  simp only [map_mul, mul_apply_eq_comp, ι_apply_three_canonical hQ hkl he h₀ h₂₃ hu₀, map_smul,
    ι_one_ι_two_canonical hQ hkl he h₀ h₂₃ hu₀, ← coe_antiCanonicalSpinor, Submodule.coe_smul,
    ← Complex.coe_smul, smul_smul, I_mul_I]
  push_cast; module
/-- Orthogonal decomposition of any `ζ ∈ W⁺` along the orthonormal frame `(u₀, v₀)`. -/
theorem eq_inner_smul_add_inner_antiCanonicalSpinor_smul (h₂ : finrank ℂ PosSpin(o, ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (ζ : PosSpin(o, ρ)) :
    ζ = ⟪u₀, ζ⟫_ℂ • u₀ + ⟪antiSpin(o, ρ, e) u₀, ζ⟫_ℂ • antiSpin(o, ρ, e) u₀ := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hnegω : o.hodgeStar hkl (-J.kahlerForm) = -J.kahlerForm := by rw [map_neg, hω]
  have hv₀₁ : ‖antiSpin(o, ρ, e) u₀‖ = 1 := by rw [norm_antiCanonicalSpinor hQ hρ, hu₀₁]
  have hα := cliffordProjection_apply_eq_inner_smul o hQ hkl hω hρ h₂ hu₀ hu₀₁ ζ
  have hβ := cliffordProjection_apply_eq_inner_smul o hQ hkl hnegω hρ h₂
    (cliffordProjection_neg_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀) hv₀₁ ζ
  rw [cliffordProjection_neg_apply] at hβ; rw [← hα, ← hβ]; abel
/-- **Cross-term polarization identity**: `(√2 / 4) q'(α u₀, β v₀)` lies in the anti-`J`-invariant
plane `span(ρ₁, ρ₂)` with coefficients `(Im(conj α * β) / 4, -Re(conj α * β) / 4)`. -/
theorem smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : PosSpin(o, ρ)}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α β : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiSpin(o, ρ, e) u₀) =
      ((conj α * β).im / 4) • antiInvariantSelfDual₁ o e hkl he -
        ((conj α * β).re / 4) • antiInvariantSelfDual₂ o e hkl he := by
  have hv₀_in : ⟪antiSpin(o, ρ, e) u₀, antiSpin(o, ρ, e) u₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_antiCanonicalSpinor hQ hρ, hu₀₁]; norm_num
  have hpair (η : SD(V, o, hkl)) :
      ⟪η, quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiSpin(o, ρ, e) u₀)⟫ =
        (⟪cliffordRestriction o ρ η (α • u₀), β • antiSpin(o, ρ, e) u₀⟫_ℂ).re / 2 := by
    rw [real_inner_comm, Submodule.coe_inner, quadraticTwoFormPolar_apply, Submodule.coe_smul,
      real_inner_smul_left, ← Submodule.coe_inner,
      inner_cliffordRestrictionAdjoint_left o ρ hkl _ η,
      trace_quadraticEndPolar_mul_of_mem_traceFreeSelfAdjoint
        (cliffordRestriction_mem_traceFreeSelfAdjoint o hQ hρ η)]; simp; ring
  have hω : ⟪kahlerSelfDual o J hkl he h₀ h₂₃,
      quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiSpin(o, ρ, e) u₀)⟫ = 0 := by
    rw [real_inner_comm, Submodule.coe_inner, coe_kahlerSelfDual, real_inner_smul_right,
      inner_quadraticTwoFormPolar_of_cliffordProjection o hQ hkl
        (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) hρ
        (by rw [map_smul, hu₀])
        (by rw [map_smul, cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, smul_zero]),
      mul_zero]
  have hρ₁ : ⟪antiInvariantSelfDual₁ o e hkl he,
      quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiSpin(o, ρ, e) u₀)⟫ =
      (√2 / 2) * (conj α * β).im := by
    rw [hpair, map_smul, cliffordRestriction_antiInvariantSelfDual₁_apply hQ hkl he h₀ h₂₃ hu₀,
      smul_smul, inner_smul_left, inner_smul_right, hv₀_in]; simp; ring
  have hρ₂ : ⟪antiInvariantSelfDual₂ o e hkl he,
      quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiSpin(o, ρ, e) u₀)⟫ =
      -(√2 / 2) * (conj α * β).re := by
    rw [hpair, map_smul, cliffordRestriction_antiInvariantSelfDual₂_apply hQ hkl he h₀ h₂₃ hu₀,
      smul_smul, inner_smul_left, inner_smul_right, hv₀_in]; simp; ring
  have hs : (√2 / 4 : ℝ) * (√2 / 2) = 1 / 4 := by
    linear_combination (1 / 8 : ℝ) * Real.mul_self_sqrt zero_le_two
  conv_lhs =>
    rw [eq_inner_kahlerSelfDual_add_antiInvariantSelfDual (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
      (quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiSpin(o, ρ, e) u₀))]
  rw [hω, hρ₁, hρ₂, zero_smul, zero_add, smul_add, smul_smul, smul_smul, ← mul_assoc,
    show (√2 / 4 : ℝ) * (-(√2 / 2) * (conj α * β).re) = -((√2 / 4 * (√2 / 2)) * (conj α * β).re)
      by ring, hs]; module
end CliffordRelations
end SpinorFrame

/-! ### Eight-real-component isometric domain and target intertwiners -/

section Intertwiners
omit [Fact (finrank ℝ V = 4)] in
/-- The one-form `-η₀ e₀* + η₁ e₁* + y₀ e₂* + y₁ e₃*` for normal `y` and tangential `η`. -/
def normalFrameForm (e : OrthonormalBasis (Fin 4) ℝ V) (y η : E4) : OneForm(V) :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    ((-η 0) • innerSL ℝ (e 0) + η 1 • innerSL ℝ (e 1) +
      y 0 • innerSL ℝ (e 2) + y 1 • innerSL ℝ (e 3))
omit [Fact (finrank ℝ V = 4)] in theorem normalFrameForm_eq (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : E4) : normalFrameForm e y η = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((-η 0) • innerSL ℝ (e 0) + η 1 • innerSL ℝ (e 1) +
        y 0 • innerSL ℝ (e 2) + y 1 • innerSL ℝ (e 3)) := (rfl)
omit [Fact (finrank ℝ V = 4)] in @[simp] theorem normalFrameForm_apply
    (e : OrthonormalBasis (Fin 4) ℝ V) (y η : E4) (v : V) : normalFrameForm e y η (fun _ ↦ v) =
      -η 0 * ⟪e 0, v⟫ + η 1 * ⟪e 1, v⟫ + y 0 * ⟪e 2, v⟫ + y 1 * ⟪e 3, v⟫ := by
  simp [normalFrameForm]
omit [Fact (finrank ℝ V = 4)] in theorem normalFrameForm_add (e : OrthonormalBasis (Fin 4) ℝ V)
    (y₁ y₂ η₁ η₂ : E4) :
    normalFrameForm e (y₁ + y₂) (η₁ + η₂) = normalFrameForm e y₁ η₁ + normalFrameForm e y₂ η₂ := by
  simp only [normalFrameForm, ← map_add, PiLp.add_apply]; congr 1; module
omit [Fact (finrank ℝ V = 4)] in theorem normalFrameForm_smul (e : OrthonormalBasis (Fin 4) ℝ V)
    (r : ℝ) (y η : E4) : normalFrameForm e (r • y) (r • η) = r • normalFrameForm e y η := by
  ext v; simp [normalFrameForm]; ring
omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- The positive half-spinor `2(y₂ + i y₃) u₀ + 2(η₂ + i η₃) v₀` in `(u₀, v₀)`. -/
def normalFrameSpinor (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : PosSpin(o, ρ))
    (y η : E4) : PosSpin(o, ρ) :=
  ((2 : ℂ) * ((y 2 : ℂ) + (y 3 : ℂ) * I)) • u₀ +
    ((2 : ℂ) * ((η 2 : ℂ) + (η 3 : ℂ) * I)) • antiCanonicalSpinor o ρ e u₀
omit [FiniteDimensional ℂ W] in theorem normalFrameSpinor_eq (e : OrthonormalBasis (Fin 4) ℝ V)
    (u₀ : PosSpin(o, ρ)) (y η : E4) : normalFrameSpinor o ρ e u₀ y η =
      ((2 : ℂ) * ((y 2 : ℂ) + (y 3 : ℂ) * I)) • u₀ +
        ((2 : ℂ) * ((η 2 : ℂ) + (η 3 : ℂ) * I)) • antiCanonicalSpinor o ρ e u₀ := (rfl)

section Equivs
variable (o ρ) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
  (h₂ : finrank ℂ PosSpin(o, ρ) = 2) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : PosSpin(o, ρ)} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
include hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁

omit hkl he h₀ h₂₃ h₂ hu₀ in private theorem norm_halfSpinCliffordMul_basis (i : Fin 4) :
    ‖cMul(o, ρ, e i, u₀)‖ = 1 := by
  rw [← Submodule.norm_coe, coe_halfSpinCliffordMul_apply_apply, LinearEquiv.coe_ofEq_apply,
    norm_map_ι_apply hQ hρ, e.orthonormal.1 i, one_mul, Submodule.norm_coe, hu₀₁]
omit h₂ hu₀₁ in private theorem inner_halfSpinCliffordMul_two_zero :
    ⟪cMul(o, ρ, e 2, u₀), cMul(o, ρ, e 0, u₀)⟫_ℂ = 0 := by
  rw [← inner_conj_symm, Submodule.coe_inner, coe_halfSpinCliffordMul_apply_apply,
    coe_halfSpinCliffordMul_apply_apply, LinearEquiv.coe_ofEq_apply,
    inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hρ hu₀,
    h₂₃, e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]; simp
private theorem eq_inner_halfSpinCliffordMul (ν : NegSpin(Q, o, ρ)) :
    ν = ⟪cMul(o, ρ, e 2, u₀), ν⟫_ℂ • cMul(o, ρ, e 2, u₀) +
        ⟪cMul(o, ρ, e 0, u₀), ν⟫_ℂ • cMul(o, ρ, e 0, u₀) := by
  let φ : PosSpin(o, ρ) := ⟨-ρ (ι Q (e 0)) ν, by
    rw [mem_positiveHalfSpinors, map_neg, neg_inj]; simpa using Module.End.mem_eigenspace_iff.1
      (map_ι_apply_mem_eigenspace_chirality_neg o (ε := -1) ν.2 (e 0))⟩
  have hνφ : cMul(o, ρ, e 0, φ) = ν := Subtype.ext <| by
    rw [coe_halfSpinCliffordMul_apply_apply, LinearEquiv.coe_ofEq_apply]; dsimp [φ]
    rw [map_neg, ι_apply_self_basis hQ 0, neg_neg]
  have h0v : cMul(o, ρ, e 0, antiSpin(o, ρ, e) u₀) = -cMul(o, ρ, e 2, u₀) :=
    Subtype.ext <| by simpa using ι_apply_zero_antiCanonicalSpinor hQ u₀
  have hexp : ν = (-⟪antiSpin(o, ρ, e) u₀, φ⟫_ℂ) • cMul(o, ρ, e 2, u₀) +
      ⟪u₀, φ⟫_ℂ • cMul(o, ρ, e 0, u₀) := by
    rw [← hνφ]; conv_lhs =>
      rw [eq_inner_smul_add_inner_antiCanonicalSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ φ]
    simp only [map_add, map_smul, h0v, smul_neg, neg_smul]
    exact add_comm _ _
  have hw₂₀ := inner_halfSpinCliffordMul_two_zero o ρ hQ hkl he h₀ h₂₃ hρ hu₀
  conv_rhs => rw [hexp]
  rw [inner_smul_add_smul_of_inner_eq_zero_left
      (norm_halfSpinCliffordMul_basis o ρ hQ hρ hu₀₁ 2) hw₂₀,
    inner_smul_add_smul_of_inner_eq_zero_right
      (norm_halfSpinCliffordMul_basis o ρ hQ hρ hu₀₁ 0) hw₂₀, ← hexp]
/-- **The eight-component domain frame intertwiner** `(y, η) ≃ (b, ζ) ∈ Ω¹(V) × W⁺`. -/
def normalDomainEquiv : (E4 × E4) ≃L[ℝ] OneForm(V) × PosSpin(o, ρ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun p := (normalFrameForm e p.1 p.2, normalFrameSpinor o ρ e u₀ p.1 p.2)
      map_add' p q := Prod.ext (normalFrameForm_add e p.1 q.1 p.2 q.2) <| by
        simp only [normalFrameSpinor, Prod.fst_add, Prod.snd_add, PiLp.add_apply, ofReal_add]
        module
      map_smul' r p := Prod.ext (normalFrameForm_smul e r p.1 p.2) <| by
        simp only [normalFrameSpinor, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply,
          smul_eq_mul, ofReal_mul, RingHom.id_apply]; rw [← Complex.coe_smul]; module
      invFun q :=
        (!₂[q.1 (fun _ ↦ e 2), q.1 (fun _ ↦ e 3), (⟪u₀, q.2⟫_ℂ).re / 2, (⟪u₀, q.2⟫_ℂ).im / 2],
         !₂[-q.1 (fun _ ↦ e 0), q.1 (fun _ ↦ e 1),
            (⟪antiSpin(o, ρ, e) u₀, q.2⟫_ℂ).re / 2, (⟪antiSpin(o, ρ, e) u₀, q.2⟫_ℂ).im / 2])
      left_inv p := by
        have horth := inner_antiCanonicalSpinor_eq_zero hQ hkl he h₀ h₂₃ hρ hu₀
        have hv₀₁ : ‖antiSpin(o, ρ, e) u₀‖ = 1 := by rw [norm_antiCanonicalSpinor hQ hρ, hu₀₁]
        have huu := inner_smul_add_smul_of_inner_eq_zero_left hu₀₁ horth
          ((2 : ℂ) * (p.1 2 + p.1 3 * I)) ((2 : ℂ) * (p.2 2 + p.2 3 * I))
        have hvv := inner_smul_add_smul_of_inner_eq_zero_right hv₀₁ horth
          ((2 : ℂ) * (p.1 2 + p.1 3 * I)) ((2 : ℂ) * (p.2 2 + p.2 3 * I))
        have he_ite := orthonormal_iff_ite.1 e.orthonormal
        exact Prod.ext
          (by ext i; fin_cases i <;> simp [normalFrameForm_apply, normalFrameSpinor, he_ite, huu])
          (by ext i; fin_cases i <;> simp [normalFrameForm_apply, normalFrameSpinor, he_ite, hvv])
      right_inv q := Prod.ext
        (by apply (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.injective; ext w
            let L := (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm q.1
            have hL (v : V) : q.1 (fun _ ↦ v) = L v := by
              simp [L, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
            conv_rhs => rw [show (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm
              q.1 w = L w from rfl, ← e.sum_repr' w]
            simp [normalFrameForm, Fin.sum_univ_four, hL]; ring)
        (by conv_rhs =>
              rw [eq_inner_smul_add_inner_antiCanonicalSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ
                hu₀ hu₀₁ q.2]
            simp only [normalFrameSpinor, Matrix.cons_val_two, Matrix.cons_val_three,
              Matrix.head_cons, Matrix.tail_cons]
            congr 1 <;> congr 1 <;> (apply Complex.ext <;> simp <;> ring)) }
@[simp] theorem normalDomainEquiv_apply_fst (y η : E4) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (y, η)).1 =
      normalFrameForm e y η := (rfl)
@[simp] theorem normalDomainEquiv_apply_snd (y η : E4) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (y, η)).2 =
      normalFrameSpinor o ρ e u₀ y η := (rfl)
@[simp] theorem normalDomainEquiv_symm_apply (q : OneForm(V) × PosSpin(o, ρ)) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁).symm q =
      (!₂[q.1 (fun _ ↦ e 2), q.1 (fun _ ↦ e 3), (⟪u₀, q.2⟫_ℂ).re / 2, (⟪u₀, q.2⟫_ℂ).im / 2],
       !₂[-q.1 (fun _ ↦ e 0), q.1 (fun _ ↦ e 1), (⟪antiSpin(o, ρ, e) u₀, q.2⟫_ℂ).re / 2,
          (⟪antiSpin(o, ρ, e) u₀, q.2⟫_ℂ).im / 2]) := (rfl)
omit h₂ in
/-- Weighted component norm identity for `(normalFrameForm e y η, normalFrameSpinor o ρ e u₀ y η)`:
`‖b‖² + ‖ζ‖² / 4 = ‖y‖² + ‖η‖²`. -/
theorem alternatingFormInner_normalFrameForm_add_norm_sq_normalFrameSpinor_div_four (y η : E4) :
    alternatingFormInner V 1 (normalFrameForm e y η) (normalFrameForm e y η) +
        ‖normalFrameSpinor o ρ e u₀ y η‖ ^ 2 / 4 = ‖y‖ ^ 2 + ‖η‖ ^ 2 := by
  have horth := inner_antiCanonicalSpinor_eq_zero hQ hkl he h₀ h₂₃ hρ hu₀
  have hv₀₁ : ‖antiSpin(o, ρ, e) u₀‖ = 1 := by rw [norm_antiCanonicalSpinor hQ hρ, hu₀₁]
  have hform : alternatingFormInner V 1 (normalFrameForm e y η) (normalFrameForm e y η) =
      η 0 ^ 2 + η 1 ^ 2 + y 0 ^ 2 + y 1 ^ 2 := by
    set u : V := (-η 0) • e 0 + η 1 • e 1 + y 0 • e 2 + y 1 • e 3
    have hnf : normalFrameForm e y η = alternatingFormEquiv V 1 (ιMulti ℝ 1 ![u]) := by
      ext v
      have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
      rw [hv, alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
      simp [normalFrameForm, u, inner_add_left, real_inner_smul_left]
    rw [hnf, alternatingFormInner_alternatingFormEquiv, ← alternatingFormEquiv_apply,
      alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, u, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.1 e.orthonormal]
    norm_num; ring
  rw [hform, normalFrameSpinor, norm_smul_add_smul_sq_of_inner_eq_zero hu₀₁ hv₀₁ horth,
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq y,
    EuclideanSpace.real_norm_sq_eq η, Fin.sum_univ_four, Fin.sum_univ_four]
  simp [normSq_apply]; ring
/-- **The eight-component target frame intertwiner** `(L, A) ≃ (f, τ, ν) ∈ ℝ × Λ⁺ V × W⁻`. -/
def normalTargetEquiv : (E4 × E4) ≃L[ℝ] ℝ × SD(V, o, hkl) × NegSpin(Q, o, ρ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun p := (p.1 0,
         p.1 1 • kahlerSelfDual o J hkl he h₀ h₂₃ + p.2 0 • antiInvariantSelfDual₁ o e hkl he +
           p.2 1 • antiInvariantSelfDual₂ o e hkl he,
         ((2 : ℂ) * ((p.1 2 : ℂ) + (p.1 3 : ℂ) * I)) • cMul(o, ρ, e 2, u₀) -
           ((2 : ℂ) * ((p.2 2 : ℂ) + (p.2 3 : ℂ) * I)) • cMul(o, ρ, e 0, u₀))
      map_add' p q := Prod.ext (by simp) (Prod.ext
        (by simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply]; module)
        (by simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply, ofReal_add]; module))
      map_smul' r p := Prod.ext (by simp) (Prod.ext
        (by simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, RingHom.id_apply]; module)
        (by simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, ofReal_mul,
              RingHom.id_apply]; rw [← Complex.coe_smul]; module))
      invFun q := (!₂[q.1, ⟪kahlerSelfDual o J hkl he h₀ h₂₃, q.2.1⟫,
            (⟪cMul(o, ρ, e 2, u₀), q.2.2⟫_ℂ).re / 2, (⟪cMul(o, ρ, e 2, u₀), q.2.2⟫_ℂ).im / 2],
         !₂[⟪antiInvariantSelfDual₁ o e hkl he, q.2.1⟫, ⟪antiInvariantSelfDual₂ o e hkl he, q.2.1⟫,
            -(⟪cMul(o, ρ, e 0, u₀), q.2.2⟫_ℂ).re / 2, -(⟪cMul(o, ρ, e 0, u₀), q.2.2⟫_ℂ).im / 2])
      left_inv p := by
        dsimp only
        have hw₂₀ := inner_halfSpinCliffordMul_two_zero o ρ hQ hkl he h₀ h₂₃ hρ hu₀
        obtain ⟨hsd0, hsd1, hsd2, -⟩ := selfDual_coords_and_norm
          (hkl := hkl) (he := he) (h₀ := h₀) (h₂₃ := h₂₃) (p.1.ofLp 1) (p.2.ofLp 0) (p.2.ofLp 1)
        have hsp2 := inner_smul_add_smul_of_inner_eq_zero_left
          (norm_halfSpinCliffordMul_basis o ρ hQ hρ hu₀₁ 2) hw₂₀
          ((2 : ℂ) * (p.1.ofLp 2 + p.1.ofLp 3 * I)) (-((2 : ℂ) * (p.2.ofLp 2 + p.2.ofLp 3 * I)))
        have hsp0 := inner_smul_add_smul_of_inner_eq_zero_right
          (norm_halfSpinCliffordMul_basis o ρ hQ hρ hu₀₁ 0) hw₂₀
          ((2 : ℂ) * (p.1.ofLp 2 + p.1.ofLp 3 * I)) (-((2 : ℂ) * (p.2.ofLp 2 + p.2.ofLp 3 * I)))
        rw [neg_smul, ← sub_eq_add_neg] at hsp2 hsp0
        exact Prod.ext (by ext i; fin_cases i <;> simp [hsd0, hsp2])
          (by ext i; fin_cases i <;> simp [hsd1, hsd2, hsp0])
      right_inv q := Prod.ext (by simp) <| Prod.ext
        (by simpa using (eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
          (he := he) (h₀ := h₀) (h₂₃ := h₂₃) q.2.1).symm)
        (by conv_rhs =>
              rw [eq_inner_halfSpinCliffordMul o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ q.2.2]
            simp only [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
              Matrix.tail_cons, sub_eq_add_neg, ← neg_smul]
            congr 1 <;> congr 1 <;> (apply Complex.ext <;> simp <;> ring)) }
@[simp] theorem normalTargetEquiv_apply_fst (L A : E4) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)).1 = L 0 := (rfl)
@[simp] theorem normalTargetEquiv_apply_snd_fst (L A : E4) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)).2.1 =
      L 1 • kahlerSelfDual o J hkl he h₀ h₂₃ + A 0 • antiInvariantSelfDual₁ o e hkl he +
        A 1 • antiInvariantSelfDual₂ o e hkl he := (rfl)
@[simp] theorem normalTargetEquiv_apply_snd_snd (L A : E4) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)).2.2 =
      ((2 : ℂ) * ((L 2 : ℂ) + (L 3 : ℂ) * I)) • cMul(o, ρ, e 2, u₀) -
        ((2 : ℂ) * ((A 2 : ℂ) + (A 3 : ℂ) * I)) • cMul(o, ρ, e 0, u₀) := (rfl)
@[simp] theorem normalTargetEquiv_symm_apply (q : ℝ × SD(V, o, hkl) × NegSpin(Q, o, ρ)) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁).symm q =
      (!₂[q.1, ⟪kahlerSelfDual o J hkl he h₀ h₂₃, q.2.1⟫,
          (⟪cMul(o, ρ, e 2, u₀), q.2.2⟫_ℂ).re / 2, (⟪cMul(o, ρ, e 2, u₀), q.2.2⟫_ℂ).im / 2],
       !₂[⟪antiInvariantSelfDual₁ o e hkl he, q.2.1⟫, ⟪antiInvariantSelfDual₂ o e hkl he, q.2.1⟫,
          -(⟪cMul(o, ρ, e 0, u₀), q.2.2⟫_ℂ).re / 2,
          -(⟪cMul(o, ρ, e 0, u₀), q.2.2⟫_ℂ).im / 2]) := (rfl)
/-- Weighted component norm identity for `normalTargetEquiv`:
`f² + ‖τ‖² + ‖ν‖² / 4 = ‖L‖² + ‖A‖²`. -/
theorem sq_add_norm_sq_add_norm_sq_div_four_normalTargetEquiv (L A : E4) :
    let q := normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)
    q.1 ^ 2 + ‖q.2.1‖ ^ 2 + ‖q.2.2‖ ^ 2 / 4 = ‖L‖ ^ 2 + ‖A‖ ^ 2 := by
  intro q
  have hq2 : q.2.2 = ((2 : ℂ) * (L 2 + L 3 * I)) • cMul(o, ρ, e 2, u₀) +
      ((-2 : ℂ) * (A 2 + A 3 * I)) • cMul(o, ρ, e 0, u₀) := by
    simp only [q, normalTargetEquiv_apply_snd_snd]; module
  rw [show ‖q.2.1‖ ^ 2 = L 1 ^ 2 + A 0 ^ 2 + A 1 ^ 2 from
      (selfDual_coords_and_norm (he := he) (h₀ := h₀) (h₂₃ := h₂₃) (L 1) (A 0) (A 1)).2.2.2,
    hq2, norm_smul_add_smul_sq_of_inner_eq_zero
      (norm_halfSpinCliffordMul_basis o ρ hQ hρ hu₀₁ 2)
      (norm_halfSpinCliffordMul_basis o ρ hQ hρ hu₀₁ 0)
      (inner_halfSpinCliffordMul_two_zero o ρ hQ hkl he h₀ h₂₃ hρ hu₀),
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq L,
    EuclideanSpace.real_norm_sq_eq A, Fin.sum_univ_four, Fin.sum_univ_four]
  simp [q, normSq_apply]; ring
end Equivs
end Intertwiners
end TauCeti.SeibergWitten
