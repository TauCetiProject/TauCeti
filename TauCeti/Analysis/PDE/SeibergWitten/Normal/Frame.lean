/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Clifford and self-dual frame intertwiners for the normal Seiberg–Witten model

Let `V` be an oriented four-dimensional real inner product space equipped with an orthogonal almost
complex structure `J` and a positively oriented unitary frame `e = (e₀, e₁, e₂, e₃)` with
`J e₀ = e₁` and `J e₂ = e₃`, splitting `V` into the tangential factor `⟨e₀, e₁⟩` and the normal
factor `⟨e₂, e₃⟩`. Let `W` be a Hermitian Clifford module for `Q v = -‖v‖²` whose positive
half-spinor space `W⁺` has complex dimension two, and let `u₀ ∈ W⁺` be a unit spinor in the
canonical `-2i`-eigenline of `c₂(ω)`, where `ω` is the Kähler two-vector of `J`.

This file constructs the pointwise orthonormal frames and real-linear frame intertwiners that
decompose the eight-real-component linearized gauge-fixed Seiberg–Witten equations along the normal
plane into the four-real-component plane-vortex block and its four-real-component paired adjoint
block:

* **Self-dual two-form frame.** Alongside the unit Kähler two-vector `ω_u = (√2 / 2) ω`
  (`kahlerSelfDual`), the anti-`J`-invariant self-dual two-vectors
  `ρ₁ = (√2 / 2) (e₀ ∧ e₂ - e₁ ∧ e₃)` (`antiInvariantSelfDual₁`) and
  `ρ₂ = (√2 / 2) (e₀ ∧ e₃ + e₁ ∧ e₂)` (`antiInvariantSelfDual₂`) form a real orthonormal basis of
  the self-dual two-vectors `Λ⁺ V`.
* **Anti-canonical spinor and half-spinor frames.** `positiveHalfSpinCliffordMul` restricts odd
  Clifford multiplication `c(v)` to `W⁺ →ₗ[ℂ] W⁻`. The element `v₀ = c(e₀) c(e₂) u₀`
  (`antiCanonicalSpinor`) lies in `W⁺`, has norm `‖u₀‖`, and lies in the complementary
  `2i`-eigenline `ker P_α` of `c₂(ω)`. For unit `u₀`, `(u₀, v₀)` is a complex orthonormal basis of
  `W⁺` and `(c(e₂) u₀, c(e₀) u₀)` is a complex orthonormal basis of `W⁻`. Clifford multiplication
  by the four frame vectors sends `v₀` to `(-c(e₂) u₀, i c(e₂) u₀, c(e₀) u₀, -i c(e₀) u₀)`,
  swapping the tangential and normal directions and conjugating the complex action.
* **Cross term of the quadratic two-form.** On `u₀`, the Clifford map `C(i ·)` sends `ρ₁` to
  `i √2 v₀` and `ρ₂` to `-√2 v₀`. Consequently, for `α, β ∈ ℂ`, the polarized quadratic two-form
  `q'(α u₀, β v₀)` lies in `⟨ρ₁, ρ₂⟩` with exact formula
  `(√2 / 4) q'(α u₀, β v₀) = (Im(conj α · β) / 4) ρ₁ - (Re(conj α · β) / 4) ρ₂`.
* **Eight-component domain and target intertwiners.** `normalDomainEquiv` identifies
  `ℝ⁴ × ℝ⁴` with `(V [⋀^Fin 1]→L[ℝ] ℝ) × W⁺`, sending `(y, η)` to the one-form
  `-η₀ e₀* + η₁ e₁* + y₀ e₂* + y₁ e₃*` and spinor `2(y₂ + i y₃) u₀ + 2(η₂ + i η₃) v₀`, and
  preserving the vortex-rescaled metric `‖b‖² + ‖ζ‖² / 4`. Dually, `normalTargetEquiv` identifies
  `ℝ⁴ × ℝ⁴` with `ℝ × Λ⁺ V × W⁻`, sending `(L, A)` to
  `(L₀, L₁ ω_u + A₀ ρ₁ + A₁ ρ₂, 2(L₂ + i L₃) c(e₂) u₀ - 2(A₂ + i A₃) c(e₀) u₀)` and preserving
  `f² + ‖τ‖² + ‖ν‖² / 4`.

No differential operators are constructed here; `TauCeti.Analysis.PDE.SeibergWitten.Normal.Operator`
applies these pointwise intertwiners to the flat Seiberg–Witten equations and plane vortices.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
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

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### Orthonormal self-dual frame of `Λ⁺` -/

section SelfDualFrame

variable (o J) in
/-- The unit Kähler self-dual two-vector `ω_u = (√2 / 2) ω ∈ Λ⁺ V`. -/
def kahlerSelfDual (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  ⟨(√2 / 2 : ℝ) • J.kahlerForm, Module.End.mem_eigenspace_iff.2 <| by
    simp only [LinearEquiv.coe_coe, map_smul,
      AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he, one_smul]⟩

@[simp]
theorem coe_kahlerSelfDual (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    (kahlerSelfDual o J hkl he h₀ h₂₃ : ⋀[ℝ]^2 V) = (√2 / 2 : ℝ) • J.kahlerForm :=
  (rfl)

variable (o e) in
/-- The first anti-`J`-invariant unit self-dual two-vector
`ρ₁ = (√2 / 2) (e₀ ∧ e₂ - e₁ ∧ e₃) ∈ Λ⁺ V`. -/
def antiInvariantSelfDual₁ (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  ⟨(√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 2] - ιMulti ℝ 2 ![e 1, e 3]),
    Module.End.mem_eigenspace_iff.2 <| by
      have h13 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 3]) = -ιMulti ℝ 2 ![e 0, e 2] := by
        rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he,
          map_neg, o.hodgeStar_hodgeStar_of_even even_two hkl]
      simp only [LinearEquiv.coe_coe, map_smul, map_sub, o.hodgeStar_ιMulti_zero_two hkl he, h13,
        one_smul]
      module⟩

@[simp]
theorem coe_antiInvariantSelfDual₁ (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    (antiInvariantSelfDual₁ o e hkl he : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 2] - ιMulti ℝ 2 ![e 1, e 3]) :=
  (rfl)

variable (o e) in
/-- The second anti-`J`-invariant unit self-dual two-vector
`ρ₂ = (√2 / 2) (e₀ ∧ e₃ + e₁ ∧ e₂) ∈ Λ⁺ V`. -/
def antiInvariantSelfDual₂ (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  ⟨(√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 3] + ιMulti ℝ 2 ![e 1, e 2]),
    Module.End.mem_eigenspace_iff.2 <| by
      have h12 : o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 2]) = ιMulti ℝ 2 ![e 0, e 3] := by
        rw [← o.hodgeStar_ιMulti_zero_three hkl he,
          o.hodgeStar_hodgeStar_of_even even_two hkl]
      simp only [LinearEquiv.coe_coe, map_smul, map_add, o.hodgeStar_ιMulti_zero_three hkl he, h12,
        one_smul, add_comm]⟩

@[simp]
theorem coe_antiInvariantSelfDual₂ (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) :
    (antiInvariantSelfDual₂ o e hkl he : ⋀[ℝ]^2 V) =
      (√2 / 2 : ℝ) • (ιMulti ℝ 2 ![e 0, e 3] + ιMulti ℝ 2 ![e 1, e 2]) :=
  (rfl)

private theorem inner_basis_ιMulti {i j k l : Fin 4} :
    ⟪ιMulti ℝ 2 ![e i, e j], ιMulti ℝ 2 ![e k, e l]⟫ =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) -
        (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  rw [inner_ιMulti_two]
  simp [orthonormal_iff_ite.1 e.orthonormal]

@[simp]
theorem norm_kahlerSelfDual {hkl : 2 + 2 = finrank ℝ V} {he : e.toBasis.orientation = o}
    {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3} :
    ‖kahlerSelfDual o J hkl he h₀ h₂₃‖ = 1 := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hsq : ‖kahlerSelfDual o J hkl he h₀ h₂₃‖ ^ 2 = 1 := by
    rw [← Submodule.norm_coe, coe_kahlerSelfDual, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ, div_pow, Real.sq_sqrt zero_le_two]
    ring
  exact (sq_eq_one_iff.1 hsq).resolve_right
    (by linarith [norm_nonneg (kahlerSelfDual o J hkl he h₀ h₂₃)])

@[simp]
theorem norm_antiInvariantSelfDual₁ {hkl : 2 + 2 = finrank ℝ V} {he : e.toBasis.orientation = o} :
    ‖antiInvariantSelfDual₁ o e hkl he‖ = 1 := by
  have hsq : ‖antiInvariantSelfDual₁ o e hkl he‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, Submodule.coe_inner, coe_antiInvariantSelfDual₁]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
      inner_basis_ιMulti]
    norm_num [div_eq_mul_inv]
    linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
  exact (sq_eq_one_iff.1 hsq).resolve_right
    (by linarith [norm_nonneg (antiInvariantSelfDual₁ o e hkl he)])

@[simp]
theorem norm_antiInvariantSelfDual₂ {hkl : 2 + 2 = finrank ℝ V} {he : e.toBasis.orientation = o} :
    ‖antiInvariantSelfDual₂ o e hkl he‖ = 1 := by
  have hsq : ‖antiInvariantSelfDual₂ o e hkl he‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, Submodule.coe_inner, coe_antiInvariantSelfDual₂]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      inner_basis_ιMulti]
    norm_num [div_eq_mul_inv]
    linear_combination (2⁻¹ : ℝ) * Real.mul_self_sqrt zero_le_two
  exact (sq_eq_one_iff.1 hsq).resolve_right
    (by linarith [norm_nonneg (antiInvariantSelfDual₂ o e hkl he)])

@[simp]
theorem inner_kahlerSelfDual_antiInvariantSelfDual₁ {hkl : 2 + 2 = finrank ℝ V}
    {he : e.toBasis.orientation = o} {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3} :
    ⟪kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₁ o e hkl he⟫ = 0 := by
  rw [Submodule.coe_inner, coe_kahlerSelfDual, coe_antiInvariantSelfDual₁,
    AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃]
  simp [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
    inner_basis_ιMulti]

@[simp]
theorem inner_kahlerSelfDual_antiInvariantSelfDual₂ {hkl : 2 + 2 = finrank ℝ V}
    {he : e.toBasis.orientation = o} {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3} :
    ⟪kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₂ o e hkl he⟫ = 0 := by
  rw [Submodule.coe_inner, coe_kahlerSelfDual, coe_antiInvariantSelfDual₂,
    AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃]
  simp [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    inner_basis_ιMulti]

@[simp]
theorem inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂ {hkl : 2 + 2 = finrank ℝ V}
    {he : e.toBasis.orientation = o} :
    ⟪antiInvariantSelfDual₁ o e hkl he, antiInvariantSelfDual₂ o e hkl he⟫ = 0 := by
  rw [Submodule.coe_inner, coe_antiInvariantSelfDual₁, coe_antiInvariantSelfDual₂]
  simp [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_add_right,
    inner_basis_ιMulti]

private theorem orthonormal_selfDualTuple (o : Orientation ℝ V (Fin 4))
    (e : OrthonormalBasis (Fin 4) ℝ V) (J : AlmostComplexStructure V)
    (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    Orthonormal ℝ ![kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₁ o e hkl he,
      antiInvariantSelfDual₂ o e hkl he] := by
  refine ⟨fun i ↦ ?_, fun {i j} hij ↦ ?_⟩
  · fin_cases i
    · exact norm_kahlerSelfDual (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
    · exact norm_antiInvariantSelfDual₁ (he := he)
    · exact norm_antiInvariantSelfDual₂ (he := he)
  · fin_cases i <;> fin_cases j <;> try contradiction
    · exact inner_kahlerSelfDual_antiInvariantSelfDual₁ (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
    · exact inner_kahlerSelfDual_antiInvariantSelfDual₂ (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
    · rw [real_inner_comm]
      exact inner_kahlerSelfDual_antiInvariantSelfDual₁ (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
    · exact inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂ (he := he)
    · rw [real_inner_comm]
      exact inner_kahlerSelfDual_antiInvariantSelfDual₂ (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
    · rw [real_inner_comm]
      exact inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂ (he := he)

private theorem card_fin_three_eq_finrank_selfDual (o : Orientation ℝ V (Fin 4))
    (hkl : 2 + 2 = finrank ℝ V) :
    Fintype.card (Fin 3) =
      finrank ℝ (Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) := by
  have hsd := o.two_mul_finrank_eigenspace_hodgeStar_one even_two two_pos hkl
  have hchoose : Nat.choose 4 2 = 6 := by decide
  rw [hchoose] at hsd
  rw [Fintype.card_fin]
  omega

/-- **The real orthonormal basis `(ω_u, ρ₁, ρ₂)` of `Λ⁺ V`** induced by a positively oriented
unitary frame `e`. -/
def selfDualOrthonormalBasis (o : Orientation ℝ V (Fin 4)) (e : OrthonormalBasis (Fin 4) ℝ V)
    (J : AlmostComplexStructure V) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    OrthonormalBasis (Fin 3) ℝ
      (Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :=
  (basisOfOrthonormalOfCardEqFinrank
    (orthonormal_selfDualTuple o e J hkl he h₀ h₂₃)
    (card_fin_three_eq_finrank_selfDual o hkl)).toOrthonormalBasis
    (by
      rw [coe_basisOfOrthonormalOfCardEqFinrank]
      exact orthonormal_selfDualTuple o e J hkl he h₀ h₂₃)

@[simp]
theorem coe_selfDualOrthonormalBasis (o : Orientation ℝ V (Fin 4))
    (e : OrthonormalBasis (Fin 4) ℝ V) (J : AlmostComplexStructure V)
    (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    (selfDualOrthonormalBasis o e J hkl he h₀ h₂₃ : Fin 3 → _) =
      ![kahlerSelfDual o J hkl he h₀ h₂₃, antiInvariantSelfDual₁ o e hkl he,
        antiInvariantSelfDual₂ o e hkl he] := by
  rw [selfDualOrthonormalBasis, Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank]

/-- Every self-dual two-vector expands in the orthonormal frame `(ω_u, ρ₁, ρ₂)`. -/
theorem eq_inner_kahlerSelfDual_add_antiInvariantSelfDual {hkl : 2 + 2 = finrank ℝ V}
    {he : e.toBasis.orientation = o} {h₀ : J (e 0) = e 1} {h₂₃ : J (e 2) = e 3}
    (τ : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
    τ = ⟪kahlerSelfDual o J hkl he h₀ h₂₃, τ⟫ • kahlerSelfDual o J hkl he h₀ h₂₃ +
      ⟪antiInvariantSelfDual₁ o e hkl he, τ⟫ • antiInvariantSelfDual₁ o e hkl he +
      ⟪antiInvariantSelfDual₂ o e hkl he, τ⟫ • antiInvariantSelfDual₂ o e hkl he := by
  have h := ((selfDualOrthonormalBasis o e J hkl he h₀ h₂₃).sum_repr' τ).symm
  rwa [Fin.sum_univ_three, coe_selfDualOrthonormalBasis] at h

end SelfDualFrame

/-! ### The anti-canonical spinor `v₀ = c(e₀) c(e₂) u₀` and half-spinor frames -/

section SpinorFrame

variable (o ρ) in
/-- Odd Clifford multiplication `c(v) : W⁺ →ₗ[ℂ] W⁻` from `positiveHalfSpinors o ρ` to the
negative half-spinor eigenspace `eigenspace (ρ (chirality Q o)) (-1)` (the specialization of
`CliffordAlgebra.halfSpinCliffordMul` across the definition `positiveHalfSpinors`). -/
def positiveHalfSpinCliffordMul (v : V) :
    positiveHalfSpinors o ρ →ₗ[ℂ] Module.End.eigenspace (ρ (chirality Q o)) (-1) where
  toFun ψ := ⟨ρ (ι Q v) ψ, map_ι_apply_mem_eigenspace_chirality_neg o (ε := 1)
    (Module.End.mem_eigenspace_iff.2 (by simpa using mem_positiveHalfSpinors.1 ψ.2)) v⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

omit [FiniteDimensional ℂ W] in
@[simp]
theorem coe_positiveHalfSpinCliffordMul_apply (v : V) (ψ : positiveHalfSpinors o ρ) :
    (positiveHalfSpinCliffordMul o ρ v ψ : W) = ρ (ι Q v) ψ :=
  (rfl)

variable (o ρ e) in
/-- The **anti-canonical positive half-spinor** `v₀ = c(e₀) c(e₂) u₀` associated to a spinor
`u₀ ∈ W⁺` in the frame `e`. When `u₀` is a unit spinor in the canonical line `P_α u₀ = u₀`, `v₀`
is a unit spinor in the complementary line `ker P_α`. -/
def antiCanonicalSpinor (u₀ : positiveHalfSpinors o ρ) : positiveHalfSpinors o ρ :=
  ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀), by
    rw [mem_positiveHalfSpinors]
    have h₁ := map_ι_apply_mem_eigenspace_chirality_neg o (ε := 1)
      (Module.End.mem_eigenspace_iff.2 (by simpa using mem_positiveHalfSpinors.1 u₀.2)) (e 2)
    have h₂ := map_ι_apply_mem_eigenspace_chirality_neg o (ε := -1) h₁ (e 0)
    simpa using Module.End.mem_eigenspace_iff.1 h₂⟩

omit [FiniteDimensional ℂ W] in
@[simp]
theorem coe_antiCanonicalSpinor (u₀ : positiveHalfSpinors o ρ) :
    (antiCanonicalSpinor o ρ e u₀ : W) = ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) :=
  (rfl)

section CliffordRelations

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
private theorem ι_apply_self_basis (i : Fin 4) (w : W) :
    ρ (ι Q (e i)) (ρ (ι Q (e i)) w) = -w := by
  have h := congrArg (fun a ↦ ρ a w) (ι_sq_scalar Q (e i))
  rw [map_mul, mul_apply_eq_comp, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, one_apply_eq_self, hQ (e i), e.orthonormal.1 i, one_pow,
    neg_one_smul] at h
  exact h

omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
private theorem ι_apply_comm_basis {i j : Fin 4} (hij : i ≠ j) (w : W) :
    ρ (ι Q (e i)) (ρ (ι Q (e j)) w) = -ρ (ι Q (e j)) (ρ (ι Q (e i)) w) := by
  have h := congrArg (fun a ↦ ρ a w) (ι_mul_ι_comm_of_isOrtho (e.isOrtho_apply hQ hij))
  simpa only [map_mul, map_neg, mul_apply_eq_comp, LinearMap.neg_apply] using h

theorem norm_antiCanonicalSpinor (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (u₀ : positiveHalfSpinors o ρ) :
    ‖antiCanonicalSpinor o ρ e u₀‖ = ‖u₀‖ := by
  rw [← Submodule.norm_coe, coe_antiCanonicalSpinor, norm_map_ι_apply hQ hρ,
    norm_map_ι_apply hQ hρ, e.orthonormal.1 0, e.orthonormal.1 2, one_mul, one_mul,
    Submodule.norm_coe]

omit [FiniteDimensional ℂ W] in
/-- Clifford multiplication by `e₀` sends `v₀ = c(e₀) c(e₂) u₀` to `-c(e₂) u₀`. -/
theorem ι_apply_zero_antiCanonicalSpinor (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 0)) (antiCanonicalSpinor o ρ e u₀) = -ρ (ι Q (e 2)) u₀ := by
  rw [coe_antiCanonicalSpinor, ι_apply_self_basis hQ 0]

omit [FiniteDimensional ℂ W] in
/-- Clifford multiplication by `e₂` sends `v₀ = c(e₀) c(e₂) u₀` to `c(e₀) u₀`. -/
theorem ι_apply_two_antiCanonicalSpinor (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 2)) (antiCanonicalSpinor o ρ e u₀) = ρ (ι Q (e 0)) u₀ := by
  rw [coe_antiCanonicalSpinor, ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0),
    ι_apply_self_basis hQ 2, map_neg, neg_neg]

variable (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
include hkl he h₀ h₂₃

/-- On a canonical spinor `P_α u₀ = u₀`, the Kähler form acts on `v₀ = c(e₀) c(e₂) u₀` with
eigenvalue `2i`. -/
theorem bivectorExterior_kahlerForm_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (bivectorExterior Q J.kahlerForm) (antiCanonicalSpinor o ρ e u₀) =
      (2 * I) • (antiCanonicalSpinor o ρ e u₀ : W) := by
  have h₁ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)
  have h₃ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  rw [h₀] at h₁
  rw [h₂₃] at h₃
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂₃, map_add, map_mul, map_mul,
    LinearMap.add_apply, mul_apply_eq_comp, mul_apply_eq_comp, coe_antiCanonicalSpinor]
  have ha : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀))) =
      I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [ι_apply_comm_basis hQ (by decide : (1 : Fin 4) ≠ 0), map_neg,
      ι_apply_self_basis hQ 0, neg_neg, ι_apply_comm_basis hQ (by decide : (1 : Fin 4) ≠ 2),
      h₁, map_smul, ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0),
      smul_neg, neg_neg]
  have hb : ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀))) =
      I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [ι_apply_comm_basis hQ (by decide : (3 : Fin 4) ≠ 0), map_neg,
      ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0), neg_neg,
      ι_apply_comm_basis hQ (by decide : (3 : Fin 4) ≠ 2), map_neg,
      ι_apply_self_basis hQ 2, neg_neg, h₃, map_smul]
  rw [ha, hb]
  module

/-- The anti-canonical spinor `v₀` lies in the kernel of the canonical projection `P_α`. -/
@[simp]
theorem cliffordProjection_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ J.kahlerForm (antiCanonicalSpinor o ρ e u₀) = 0 := by
  rw [cliffordProjection_apply_eq_zero_iff]
  apply Subtype.ext
  rw [coe_cliffordRestriction_apply, Submodule.coe_smul,
    bivectorExterior_kahlerForm_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, smul_smul]
  congr 1
  linear_combination 2 * I_sq

/-- The anti-canonical spinor `v₀` is fixed by the complementary projection `P_β = P_{-ω}`. -/
@[simp]
theorem cliffordProjection_neg_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ (-J.kahlerForm) (antiCanonicalSpinor o ρ e u₀) =
      antiCanonicalSpinor o ρ e u₀ := by
  rw [cliffordProjection_neg_apply, cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀,
    sub_zero]

/-- Clifford multiplication by `e₁ = J e₀` sends `v₀` to `i c(e₂) u₀`. -/
theorem ι_apply_one_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (antiCanonicalSpinor o ρ e u₀) = I • ρ (ι Q (e 2)) u₀ := by
  rw [← h₀, ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂₃
    (cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀),
    ι_apply_zero_antiCanonicalSpinor hQ, smul_neg, neg_smul, neg_neg]

/-- Clifford multiplication by `e₃ = J e₂` sends `v₀` to `-i c(e₀) u₀`. -/
theorem ι_apply_three_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 3)) (antiCanonicalSpinor o ρ e u₀) = -I • ρ (ι Q (e 0)) u₀ := by
  rw [← h₂₃, ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂₃
    (cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀),
    ι_apply_two_antiCanonicalSpinor hQ]

/-- `u₀` and `v₀ = antiCanonicalSpinor o ρ e u₀` are orthogonal in `W⁺`. -/
theorem inner_antiCanonicalSpinor_eq_zero
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ⟪u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ = 0 := by
  calc ⟪u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ
      = ⟪cliffordProjection o ρ J.kahlerForm u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ := by rw [hu₀]
    _ = ⟪u₀, cliffordProjection o ρ J.kahlerForm (antiCanonicalSpinor o ρ e u₀)⟫_ℂ :=
        (isSelfAdjoint_cliffordProjection o J.kahlerForm hρ).isSymmetric _ _
    _ = 0 := by rw [cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, inner_zero_right]

/-- `C(i ρ₁) u₀ = (i √2) v₀` on a canonical spinor `u₀`. -/
theorem cliffordRestriction_antiInvariantSelfDual₁_apply {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordRestriction o ρ (antiInvariantSelfDual₁ o e hkl he) u₀ =
      (I * (√2 : ℂ)) • antiCanonicalSpinor o ρ e u₀ := by
  have h₁ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)
  have h₃ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  rw [h₀] at h₁
  rw [h₂₃] at h₃
  apply Subtype.ext
  rw [coe_cliffordRestriction_apply, coe_antiInvariantSelfDual₁, Submodule.coe_smul,
    coe_antiCanonicalSpinor, map_smul, map_sub, bivectorExterior_apply_ιMulti,
    bivectorExterior_apply_ιMulti,
    bivector_eq_ι_mul_ι_of_isOrtho Q (e.isOrtho_apply hQ (by decide)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (e.isOrtho_apply hQ (by decide)),
    map_smul, map_sub, map_mul, map_mul, LinearMap.smul_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, mul_apply_eq_comp]
  have h13 : ρ (ι Q (e 1)) (ρ (ι Q (e 3)) u₀) = -ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [h₃, map_smul, ι_apply_comm_basis hQ (by decide : (1 : Fin 4) ≠ 2), h₁,
      map_smul, smul_neg, smul_smul, I_mul_I, neg_one_smul, neg_neg,
      ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0)]
  rw [h13, sub_neg_eq_add, ← two_smul ℝ (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀)),
    ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- `C(i ρ₂) u₀ = -√2 v₀` on a canonical spinor `u₀`. -/
theorem cliffordRestriction_antiInvariantSelfDual₂_apply {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordRestriction o ρ (antiInvariantSelfDual₂ o e hkl he) u₀ =
      (-(√2 : ℂ)) • antiCanonicalSpinor o ρ e u₀ := by
  have h₁ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)
  have h₃ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)
  rw [h₀] at h₁
  rw [h₂₃] at h₃
  apply Subtype.ext
  rw [coe_cliffordRestriction_apply, coe_antiInvariantSelfDual₂, Submodule.coe_smul,
    coe_antiCanonicalSpinor, map_smul, map_add, bivectorExterior_apply_ιMulti,
    bivectorExterior_apply_ιMulti,
    bivector_eq_ι_mul_ι_of_isOrtho Q (e.isOrtho_apply hQ (by decide)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (e.isOrtho_apply hQ (by decide)),
    map_smul, map_add, map_mul, map_mul, LinearMap.smul_apply, LinearMap.add_apply,
    mul_apply_eq_comp, mul_apply_eq_comp]
  have h03 : ρ (ι Q (e 0)) (ρ (ι Q (e 3)) u₀) = I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [h₃, map_smul]
  have h12 : ρ (ι Q (e 1)) (ρ (ι Q (e 2)) u₀) = I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [ι_apply_comm_basis hQ (by decide : (1 : Fin 4) ≠ 2), h₁, map_smul,
      ι_apply_comm_basis hQ (by decide : (2 : Fin 4) ≠ 0), smul_neg, neg_neg]
  rw [h03, h12, ← add_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (√2 : ℂ) * I_sq

/-- **Orthonormal spinor decomposition of `W⁺`**: for a unit canonical spinor `u₀`, every
`ζ ∈ W⁺` decomposes as `ζ = ⟪u₀, ζ⟫ u₀ + ⟪v₀, ζ⟫ v₀`. -/
theorem eq_inner_smul_add_inner_antiCanonicalSpinor_smul
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    (hu₀₁ : ‖u₀‖ = 1) (ζ : positiveHalfSpinors o ρ) :
    ζ = ⟪u₀, ζ⟫_ℂ • u₀ + ⟪antiCanonicalSpinor o ρ e u₀, ζ⟫_ℂ • antiCanonicalSpinor o ρ e u₀ := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hnegω : o.hodgeStar hkl (-J.kahlerForm) = -J.kahlerForm := by rw [map_neg, hω]
  have hv₀ := cliffordProjection_neg_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀
  have hv₀₁ : ‖antiCanonicalSpinor o ρ e u₀‖ = 1 := by
    rw [norm_antiCanonicalSpinor hQ hρ, hu₀₁]
  have hα := cliffordProjection_apply_eq_inner_smul o hQ hkl hω hρ h₂ hu₀ hu₀₁ ζ
  have hβ := cliffordProjection_apply_eq_inner_smul o hQ hkl hnegω hρ h₂ hv₀ hv₀₁ ζ
  rw [cliffordProjection_neg_apply] at hβ
  rw [← hα, ← hβ]
  abel

/-! ### Cross term of `quadraticTwoFormPolar` in the self-dual frame -/

/-- **Explicit self-dual frame formula for the polarized quadratic two-form**: for a unit canonical
spinor `u₀`, `v₀ = antiCanonicalSpinor o ρ e u₀`, and `α, β ∈ ℂ`,
`(√2 / 4) q'(α u₀, β v₀) = (Im(conj α · β) / 4) ρ₁ - (Re(conj α · β) / 4) ρ₂`. -/
theorem smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    (hu₀₁ : ‖u₀‖ = 1) (α β : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀) =
      ((conj α * β).im / 4) • antiInvariantSelfDual₁ o e hkl he -
        ((conj α * β).re / 4) • antiInvariantSelfDual₂ o e hkl he := by
  set φ := α • u₀
  set ψ := β • antiCanonicalSpinor o ρ e u₀
  set qPolar := quadraticTwoFormPolar o ρ hkl φ ψ
  have hPφ : cliffordProjection o ρ J.kahlerForm φ = φ := by
    rw [map_smul, hu₀]
  have hPψ : cliffordProjection o ρ J.kahlerForm ψ = 0 := by
    rw [map_smul, cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, smul_zero]
  have hv₀_inner : ⟪antiCanonicalSpinor o ρ e u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_antiCanonicalSpinor hQ hρ, hu₀₁]
    norm_num
  -- Helper for pairing `q'(φ, ψ)` with any self-dual element `η`.
  have hpair (η : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
      ⟪η, qPolar⟫ = (⟪cliffordRestriction o ρ η φ, ψ⟫_ℂ).re / 2 := by
    dsimp only [qPolar]
    rw [real_inner_comm, Submodule.coe_inner, quadraticTwoFormPolar_apply, Submodule.coe_smul,
      real_inner_smul_left]
    have h := inner_cliffordRestrictionAdjoint_left o ρ hkl (quadraticEndPolar φ ψ) η
    rw [trace_quadraticEndPolar_mul_of_mem_traceFreeSelfAdjoint
      (cliffordRestriction_mem_traceFreeSelfAdjoint o hQ hρ η)] at h
    rw [← Submodule.coe_inner, h]
    simp only [mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
    ring
  have hω : ⟪kahlerSelfDual o J hkl he h₀ h₂₃, qPolar⟫ = 0 := by
    rw [real_inner_comm, Submodule.coe_inner, coe_kahlerSelfDual, real_inner_smul_right,
      inner_quadraticTwoFormPolar_of_cliffordProjection o hQ hkl
        (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) hρ hPφ hPψ, mul_zero]
  have hρ₁ : ⟪antiInvariantSelfDual₁ o e hkl he, qPolar⟫ = (√2 / 2) * (conj α * β).im := by
    rw [hpair]
    dsimp only [φ, ψ]
    rw [map_smul, cliffordRestriction_antiInvariantSelfDual₁_apply hQ hkl he h₀ h₂₃ hu₀,
      smul_smul, inner_smul_left, inner_smul_right, hv₀_inner, mul_one, map_mul, map_mul,
      conj_I, conj_ofReal,
      show conj α * (-I * (√2 : ℂ)) * β = -(√2 : ℂ) * ((conj α * β) * I) by ring,
      neg_mul, neg_re, re_ofReal_mul, mul_I_re]
    ring
  have hρ₂ : ⟪antiInvariantSelfDual₂ o e hkl he, qPolar⟫ = -(√2 / 2) * (conj α * β).re := by
    rw [hpair]
    dsimp only [φ, ψ]
    rw [map_smul, cliffordRestriction_antiInvariantSelfDual₂_apply hQ hkl he h₀ h₂₃ hu₀,
      smul_smul, inner_smul_left, inner_smul_right, hv₀_inner, mul_one, map_mul, map_neg,
      conj_ofReal, show conj α * -(√2 : ℂ) * β = -(√2 : ℂ) * (conj α * β) by ring,
      neg_mul, neg_re, re_ofReal_mul]
    ring
  conv_lhs =>
    rw [eq_inner_kahlerSelfDual_add_antiInvariantSelfDual (he := he) (h₀ := h₀) (h₂₃ := h₂₃) qPolar]
  rw [hω, hρ₁, hρ₂, zero_smul, zero_add, smul_add, smul_smul, smul_smul]
  have h2 : (√2 / 4 : ℝ) * (√2 / 2 * (conj α * β).im) = (conj α * β).im / 4 := by
    linear_combination ((conj α * β).im / 8) * Real.mul_self_sqrt zero_le_two
  have h3 : (√2 / 4 : ℝ) * (-(√2 / 2) * (conj α * β).re) = -((conj α * β).re / 4) := by
    linear_combination (-(conj α * β).re / 8) * Real.mul_self_sqrt zero_le_two
  rw [h2, h3, neg_smul, sub_eq_add_neg]

end CliffordRelations

end SpinorFrame

/-! ### Eight-real-component isometric domain and target intertwiners -/

section Intertwiners

omit [Fact (finrank ℝ V = 4)] in
/-- The one-form `-η₀ e₀* + η₁ e₁* + y₀ e₂* + y₁ e₃*` associated to normal connection coordinates
`(y₀, y₁)` and tangential connection coordinates `(η₀, η₁)`. When `η = 0`, this coincides
pointwise with `normalConnection`. -/
def normalFrameForm (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : EuclideanSpace ℝ (Fin 4)) : V [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    ((-η 0) • innerSL ℝ (e 0) + η 1 • innerSL ℝ (e 1) +
      y 0 • innerSL ℝ (e 2) + y 1 • innerSL ℝ (e 3))

omit [Fact (finrank ℝ V = 4)] in
theorem normalFrameForm_eq (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameForm e y η =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
        ((-η 0) • innerSL ℝ (e 0) + η 1 • innerSL ℝ (e 1) +
          y 0 • innerSL ℝ (e 2) + y 1 • innerSL ℝ (e 3)) :=
  (rfl)

omit [Fact (finrank ℝ V = 4)] in
@[simp]
theorem normalFrameForm_apply (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : EuclideanSpace ℝ (Fin 4)) (v : V) :
    normalFrameForm e y η (fun _ ↦ v) =
      -η 0 * ⟪e 0, v⟫ + η 1 * ⟪e 1, v⟫ + y 0 * ⟪e 2, v⟫ + y 1 * ⟪e 3, v⟫ := by
  simp [normalFrameForm]

omit [Fact (finrank ℝ V = 4)] in
theorem normalFrameForm_add (e : OrthonormalBasis (Fin 4) ℝ V)
    (y₁ y₂ η₁ η₂ : EuclideanSpace ℝ (Fin 4)) :
    normalFrameForm e (y₁ + y₂) (η₁ + η₂) =
      normalFrameForm e y₁ η₁ + normalFrameForm e y₂ η₂ := by
  ext v
  have hsub : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [hsub, ContinuousAlternatingMap.add_apply, normalFrameForm_apply, normalFrameForm_apply,
    normalFrameForm_apply]
  simp only [PiLp.add_apply]
  ring

omit [Fact (finrank ℝ V = 4)] in
theorem normalFrameForm_smul (e : OrthonormalBasis (Fin 4) ℝ V) (r : ℝ)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameForm e (r • y) (r • η) = r • normalFrameForm e y η := by
  ext v
  have hsub : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [hsub, ContinuousAlternatingMap.smul_apply, normalFrameForm_apply, normalFrameForm_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℂ W] in
variable (o ρ) in
/-- The positive half-spinor `2(y₂ + i y₃) u₀ + 2(η₂ + i η₃) v₀` in the canonical/anti-canonical
basis `(u₀, v₀)`. -/
def normalFrameSpinor (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (y η : EuclideanSpace ℝ (Fin 4)) : positiveHalfSpinors o ρ :=
  ((2 : ℂ) * ((y 2 : ℂ) + (y 3 : ℂ) * I)) • u₀ +
    ((2 : ℂ) * ((η 2 : ℂ) + (η 3 : ℂ) * I)) • antiCanonicalSpinor o ρ e u₀

omit [FiniteDimensional ℂ W] in
theorem normalFrameSpinor_eq (e : OrthonormalBasis (Fin 4) ℝ V)
    (u₀ : positiveHalfSpinors o ρ) (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSpinor o ρ e u₀ y η =
      ((2 : ℂ) * ((y 2 : ℂ) + (y 3 : ℂ) * I)) • u₀ +
        ((2 : ℂ) * ((η 2 : ℂ) + (η 3 : ℂ) * I)) • antiCanonicalSpinor o ρ e u₀ :=
  (rfl)

/-- **The eight-component domain frame intertwiner**, identifying `(y, η) ∈ ℝ⁴ × ℝ⁴` with
`(b, ζ) ∈ Ω¹(V) × W⁺` so that `y` parameterizes the normal connection and canonical spinor
components and `η` parameterizes the tangential connection and anti-canonical spinor components. -/
def normalDomainEquiv (o : Orientation ℝ V (Fin 4)) (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ≃L[ℝ]
      (V [⋀^Fin 1]→L[ℝ] ℝ) × positiveHalfSpinors o ρ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun p := (normalFrameForm e p.1 p.2, normalFrameSpinor o ρ e u₀ p.1 p.2)
      map_add' p q := by
        refine Prod.ext (normalFrameForm_add e p.1 q.1 p.2 q.2) ?_
        simp only [normalFrameSpinor, Prod.fst_add, Prod.snd_add, PiLp.add_apply, ofReal_add]
        module
      map_smul' r p := by
        refine Prod.ext (normalFrameForm_smul e r p.1 p.2) ?_
        simp only [normalFrameSpinor, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply,
          smul_eq_mul, ofReal_mul, RingHom.id_apply]
        rw [← Complex.coe_smul]
        module
      invFun q :=
        (!₂[q.1 (fun _ ↦ e 2), q.1 (fun _ ↦ e 3), (⟪u₀, q.2⟫_ℂ).re / 2, (⟪u₀, q.2⟫_ℂ).im / 2],
         !₂[-q.1 (fun _ ↦ e 0), q.1 (fun _ ↦ e 1),
            (⟪antiCanonicalSpinor o ρ e u₀, q.2⟫_ℂ).re / 2,
            (⟪antiCanonicalSpinor o ρ e u₀, q.2⟫_ℂ).im / 2])
      left_inv p := by
        dsimp only
        have horth := inner_antiCanonicalSpinor_eq_zero hQ hkl he h₀ h₂₃ hρ hu₀
        have horth' : ⟪antiCanonicalSpinor o ρ e u₀, u₀⟫_ℂ = 0 := by
          rw [← inner_conj_symm, horth, map_zero]
        have hu₀_in : ⟪u₀, u₀⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hu₀₁]; norm_num
        have hv₀_in : ⟪antiCanonicalSpinor o ρ e u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_antiCanonicalSpinor hQ hρ, hu₀₁]; norm_num
        have huu : ⟪u₀, normalFrameSpinor o ρ e u₀ p.1 p.2⟫_ℂ =
            (2 : ℂ) * ((p.1 2 : ℂ) + (p.1 3 : ℂ) * I) := by
          rw [normalFrameSpinor, inner_add_right, inner_smul_right, inner_smul_right,
            hu₀_in, horth, mul_one, mul_zero, add_zero]
        have hvv : ⟪antiCanonicalSpinor o ρ e u₀, normalFrameSpinor o ρ e u₀ p.1 p.2⟫_ℂ =
            (2 : ℂ) * ((p.2 2 : ℂ) + (p.2 3 : ℂ) * I) := by
          rw [normalFrameSpinor, inner_add_right, inner_smul_right, inner_smul_right,
            horth', hv₀_in, mul_zero, mul_one, zero_add]
        refine Prod.ext (by ext i; fin_cases i <;>
          simp [normalFrameForm_apply, orthonormal_iff_ite.1 e.orthonormal, huu])
          (by ext i; fin_cases i <;>
            simp [normalFrameForm_apply, orthonormal_iff_ite.1 e.orthonormal, hvv])
      right_inv q := by
        refine Prod.ext ?_ ?_
        · ext v
          let L : V →L[ℝ] ℝ :=
            (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm q.1
          have hL (w : V) : q.1 (fun _ ↦ w) = L w := by
            conv_lhs =>
              rw [← (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).apply_symm_apply q.1]
            simp [L]
          have hsub : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
          dsimp only
          rw [hsub, normalFrameForm_apply]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg, hL]
          conv_rhs => rw [← e.sum_repr' (v 0)]
          rw [map_sum, Fin.sum_univ_four]
          simp only [map_smul, smul_eq_mul]
          ring
        · have hc (z : ℂ) : (2 : ℂ) * ((z.re / 2 : ℝ) + (z.im / 2 : ℝ) * I) = z := by
            apply Complex.ext <;> simp <;> ring
          dsimp only [normalFrameSpinor]
          simp only [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
            Matrix.tail_cons, hc]
          exact (eq_inner_smul_add_inner_antiCanonicalSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ
            hu₀ hu₀₁ q.2).symm }

@[simp]
theorem normalDomainEquiv_apply_fst (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (y, η)).1 = normalFrameForm e y η :=
  (rfl)

@[simp]
theorem normalDomainEquiv_apply_snd (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (y, η)).2 =
      normalFrameSpinor o ρ e u₀ y η :=
  (rfl)

@[simp]
theorem normalDomainEquiv_symm_apply (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (q : (V [⋀^Fin 1]→L[ℝ] ℝ) × positiveHalfSpinors o ρ) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁).symm q =
      (!₂[q.1 (fun _ ↦ e 2), q.1 (fun _ ↦ e 3), (⟪u₀, q.2⟫_ℂ).re / 2, (⟪u₀, q.2⟫_ℂ).im / 2],
       !₂[-q.1 (fun _ ↦ e 0), q.1 (fun _ ↦ e 1),
          (⟪antiCanonicalSpinor o ρ e u₀, q.2⟫_ℂ).re / 2,
          (⟪antiCanonicalSpinor o ρ e u₀, q.2⟫_ℂ).im / 2]) :=
  (rfl)

/-- `normalDomainEquiv` is an isometry for the vortex-rescaled metric `‖b‖² + ‖ζ‖² / 4` on
`Ω¹(V) × W⁺` and the Euclidean metric on `ℝ⁴ × ℝ⁴`. -/
theorem norm_sq_normalDomainEquiv
    (o : Orientation ℝ V (Fin 4)) (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    alternatingFormInner V 1 (normalFrameForm e y η) (normalFrameForm e y η) +
        ‖normalFrameSpinor o ρ e u₀ y η‖ ^ 2 / 4 =
      ‖y‖ ^ 2 + ‖η‖ ^ 2 := by
  have horth := inner_antiCanonicalSpinor_eq_zero hQ hkl he h₀ h₂₃ hρ hu₀
  have hv₀₁ : ‖antiCanonicalSpinor o ρ e u₀‖ = 1 := by
    rw [norm_antiCanonicalSpinor hQ hρ, hu₀₁]
  -- Identify the 1-form with the dual of `-η₀ e₀ + η₁ e₁ + y₀ e₂ + y₁ e₃`.
  have hform : alternatingFormInner V 1 (normalFrameForm e y η) (normalFrameForm e y η) =
      η 0 ^ 2 + η 1 ^ 2 + y 0 ^ 2 + y 1 ^ 2 := by
    set u : V := -η 0 • e 0 + η 1 • e 1 + y 0 • e 2 + y 1 • e 3
    have hnf : normalFrameForm e y η = alternatingFormEquiv V 1 (ιMulti ℝ 1 ![u]) := by
      ext v
      have hsub : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
      rw [hsub, normalFrameForm_apply, alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, u, inner_add_left, real_inner_smul_left]
    rw [hnf, alternatingFormInner_alternatingFormEquiv, ← alternatingFormEquiv_apply,
      alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, u, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.1 e.orthonormal]
    norm_num
    ring
  have hspin : ‖normalFrameSpinor o ρ e u₀ y η‖ ^ 2 =
      4 * (y 2 ^ 2 + y 3 ^ 2 + η 2 ^ 2 + η 3 ^ 2) := by
    rw [normalFrameSpinor, norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, horth]
    simp only [mul_zero, RCLike.zero_re, add_zero, norm_smul, hu₀₁, hv₀₁, mul_one,
      ← normSq_eq_norm_sq, normSq_apply, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
      I_re, I_im, re_ofNat, im_ofNat]
    ring
  rw [hform, hspin, EuclideanSpace.real_norm_sq_eq y, EuclideanSpace.real_norm_sq_eq η,
    Fin.sum_univ_four, Fin.sum_univ_four]
  ring

/-- **The eight-component target frame intertwiner**, identifying `(L, A) ∈ ℝ⁴ × ℝ⁴` with
`(f, τ, ν) ∈ ℝ × Λ⁺ V × W⁻` via
`(L₀, L₁ ω_u + A₀ ρ₁ + A₁ ρ₂, 2(L₂ + i L₃) c(e₂) u₀ - 2(A₂ + i A₃) c(e₀) u₀)`. -/
def normalTargetEquiv (o : Orientation ℝ V (Fin 4)) (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ≃L[ℝ]
      ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
        Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun p :=
        (p.1 0,
         p.1 1 • kahlerSelfDual o J hkl he h₀ h₂₃ +
           p.2 0 • antiInvariantSelfDual₁ o e hkl he +
           p.2 1 • antiInvariantSelfDual₂ o e hkl he,
         ((2 : ℂ) * ((p.1 2 : ℂ) + (p.1 3 : ℂ) * I)) • positiveHalfSpinCliffordMul o ρ (e 2) u₀ -
           ((2 : ℂ) * ((p.2 2 : ℂ) + (p.2 3 : ℂ) * I)) • positiveHalfSpinCliffordMul o ρ (e 0) u₀)
      map_add' p q := by
        refine Prod.ext (by simp) (Prod.ext ?_ ?_)
        · simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply]
          module
        · simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply, ofReal_add]
          module
      map_smul' r p := by
        refine Prod.ext (by simp) (Prod.ext ?_ ?_)
        · simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, RingHom.id_apply]
          module
        · simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, ofReal_mul,
            RingHom.id_apply]
          rw [← Complex.coe_smul]
          module
      invFun q :=
        (!₂[q.1, ⟪kahlerSelfDual o J hkl he h₀ h₂₃, q.2.1⟫,
            (⟪positiveHalfSpinCliffordMul o ρ (e 2) u₀, q.2.2⟫_ℂ).re / 2,
            (⟪positiveHalfSpinCliffordMul o ρ (e 2) u₀, q.2.2⟫_ℂ).im / 2],
         !₂[⟪antiInvariantSelfDual₁ o e hkl he, q.2.1⟫,
            ⟪antiInvariantSelfDual₂ o e hkl he, q.2.1⟫,
            -(⟪positiveHalfSpinCliffordMul o ρ (e 0) u₀, q.2.2⟫_ℂ).re / 2,
            -(⟪positiveHalfSpinCliffordMul o ρ (e 0) u₀, q.2.2⟫_ℂ).im / 2])
      left_inv p := by
        dsimp only
        set w₂ := positiveHalfSpinCliffordMul o ρ (e 2) u₀
        set w₀ := positiveHalfSpinCliffordMul o ρ (e 0) u₀
        set sd := p.1 1 • kahlerSelfDual o J hkl he h₀ h₂₃ +
          p.2 0 • antiInvariantSelfDual₁ o e hkl he +
          p.2 1 • antiInvariantSelfDual₂ o e hkl he
        set sp := ((2 : ℂ) * ((p.1 2 : ℂ) + (p.1 3 : ℂ) * I)) • w₂ -
          ((2 : ℂ) * ((p.2 2 : ℂ) + (p.2 3 : ℂ) * I)) • w₀
        have hw₀₂ : ⟪w₀, w₂⟫_ℂ = 0 := by
          rw [Submodule.coe_inner, coe_positiveHalfSpinCliffordMul_apply,
            coe_positiveHalfSpinCliffordMul_apply,
            inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hρ hu₀,
            h₂₃, e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
          simp
        have hw₂₀ : ⟪w₂, w₀⟫_ℂ = 0 := by rw [← inner_conj_symm, hw₀₂, map_zero]
        have hw₂_in : ⟪w₂, w₂⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ← Submodule.norm_coe,
            coe_positiveHalfSpinCliffordMul_apply, norm_map_ι_apply hQ hρ, e.orthonormal.1 2,
            one_mul, Submodule.norm_coe, hu₀₁]
          norm_num
        have hw₀_in : ⟪w₀, w₀⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ← Submodule.norm_coe,
            coe_positiveHalfSpinCliffordMul_apply, norm_map_ι_apply hQ hρ, e.orthonormal.1 0,
            one_mul, Submodule.norm_coe, hu₀₁]
          norm_num
        have hω := real_inner_self_eq_norm_sq (kahlerSelfDual o J hkl he h₀ h₂₃)
        rw [norm_kahlerSelfDual, one_pow] at hω
        have hρ₁ := real_inner_self_eq_norm_sq (antiInvariantSelfDual₁ o e hkl he)
        rw [norm_antiInvariantSelfDual₁, one_pow] at hρ₁
        have hρ₂ := real_inner_self_eq_norm_sq (antiInvariantSelfDual₂ o e hkl he)
        rw [norm_antiInvariantSelfDual₂, one_pow] at hρ₂
        have h01 := inner_kahlerSelfDual_antiInvariantSelfDual₁ (o := o) (e := e) (J := J)
          (hkl := hkl) (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
        have h02 := inner_kahlerSelfDual_antiInvariantSelfDual₂ (o := o) (e := e) (J := J)
          (hkl := hkl) (he := he) (h₀ := h₀) (h₂₃ := h₂₃)
        have h12 := inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂ (o := o) (e := e)
          (hkl := hkl) (he := he)
        have h10 : ⟪antiInvariantSelfDual₁ o e hkl he, kahlerSelfDual o J hkl he h₀ h₂₃⟫ = 0 := by
          rw [real_inner_comm, h01]
        have h20 : ⟪antiInvariantSelfDual₂ o e hkl he, kahlerSelfDual o J hkl he h₀ h₂₃⟫ = 0 := by
          rw [real_inner_comm, h02]
        have h21 : ⟪antiInvariantSelfDual₂ o e hkl he, antiInvariantSelfDual₁ o e hkl he⟫ = 0 := by
          rw [real_inner_comm, h12]
        have hsd_in (x : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
            ⟪x, sd⟫ = p.1.ofLp 1 * ⟪x, kahlerSelfDual o J hkl he h₀ h₂₃⟫ +
              p.2.ofLp 0 * ⟪x, antiInvariantSelfDual₁ o e hkl he⟫ +
              p.2.ofLp 1 * ⟪x, antiInvariantSelfDual₂ o e hkl he⟫ := by
          dsimp only [sd]
          simp only [Submodule.coe_inner, Submodule.coe_smul, inner_add_right,
            real_inner_smul_right]
        have hsd0 : ⟪kahlerSelfDual o J hkl he h₀ h₂₃, sd⟫ = p.1.ofLp 1 := by
          rw [hsd_in, hω, h01, h02]; ring
        have hsd1 : ⟪antiInvariantSelfDual₁ o e hkl he, sd⟫ = p.2.ofLp 0 := by
          rw [hsd_in, h10, hρ₁, h12]; ring
        have hsd2 : ⟪antiInvariantSelfDual₂ o e hkl he, sd⟫ = p.2.ofLp 1 := by
          rw [hsd_in, h20, h21, hρ₂]; ring
        have hsp2 : ⟪w₂, sp⟫_ℂ = (2 : ℂ) * ((p.1.ofLp 2 : ℂ) + (p.1.ofLp 3 : ℂ) * I) := by
          dsimp only [sp]
          rw [inner_sub_right, inner_smul_right, inner_smul_right, hw₂_in, hw₂₀,
            mul_one, mul_zero, sub_zero]
        have hsp0 : ⟪w₀, sp⟫_ℂ = -((2 : ℂ) * ((p.2.ofLp 2 : ℂ) + (p.2.ofLp 3 : ℂ) * I)) := by
          dsimp only [sp]
          rw [inner_sub_right, inner_smul_right, inner_smul_right, hw₀₂, hw₀_in,
            mul_zero, mul_one, zero_sub]
        refine Prod.ext (by ext i; fin_cases i <;> simp [hsd0, hsp2])
          (by ext i; fin_cases i <;> simp [hsd1, hsd2, hsp0])
      right_inv q := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · dsimp only
          simp only [Matrix.cons_val_zero]
        · dsimp only
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact (eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
            (he := he) (h₀ := h₀) (h₂₃ := h₂₃) q.2.1).symm
        · -- Pull `q.2.2 ∈ W⁻` back to `W⁺` via `-c(e₀)`, expand in `(u₀, v₀)`, and push forward.
          dsimp only
          let φ : positiveHalfSpinors o ρ :=
            ⟨-ρ (ι Q (e 0)) q.2.2, by
              rw [mem_positiveHalfSpinors, map_neg, neg_inj]
              simpa using Module.End.mem_eigenspace_iff.1
                (map_ι_apply_mem_eigenspace_chirality_neg o (ε := -1) q.2.2.2 (e 0))⟩
          have hqφ : positiveHalfSpinCliffordMul o ρ (e 0) φ = q.2.2 := by
            apply Subtype.ext
            rw [coe_positiveHalfSpinCliffordMul_apply]
            dsimp only [φ]
            rw [map_neg, ι_apply_self_basis hQ 0, neg_neg]
          have hexp := eq_inner_smul_add_inner_antiCanonicalSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ
            hu₀ hu₀₁ φ
          have h0v : positiveHalfSpinCliffordMul o ρ (e 0) (antiCanonicalSpinor o ρ e u₀) =
              -positiveHalfSpinCliffordMul o ρ (e 2) u₀ := by
            apply Subtype.ext
            rw [coe_positiveHalfSpinCliffordMul_apply, Submodule.coe_neg,
              coe_positiveHalfSpinCliffordMul_apply, ι_apply_zero_antiCanonicalSpinor hQ]
          have hqexp : q.2.2 =
              ⟪u₀, φ⟫_ℂ • positiveHalfSpinCliffordMul o ρ (e 0) u₀ -
                ⟪antiCanonicalSpinor o ρ e u₀, φ⟫_ℂ • positiveHalfSpinCliffordMul o ρ (e 2) u₀ := by
            rw [← hqφ]
            conv_lhs => rw [hexp]
            rw [map_add, map_smul, map_smul, h0v, smul_neg, sub_eq_add_neg, add_comm]
          set w₂ := positiveHalfSpinCliffordMul o ρ (e 2) u₀
          set w₀ := positiveHalfSpinCliffordMul o ρ (e 0) u₀
          have hw₀₂ : ⟪w₀, w₂⟫_ℂ = 0 := by
            rw [Submodule.coe_inner, coe_positiveHalfSpinCliffordMul_apply,
              coe_positiveHalfSpinCliffordMul_apply,
              inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hρ hu₀,
              h₂₃, e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
            simp
          have hw₂₀ : ⟪w₂, w₀⟫_ℂ = 0 := by rw [← inner_conj_symm, hw₀₂, map_zero]
          have hw₂_in : ⟪w₂, w₂⟫_ℂ = 1 := by
            rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ← Submodule.norm_coe,
              coe_positiveHalfSpinCliffordMul_apply, norm_map_ι_apply hQ hρ, e.orthonormal.1 2,
              one_mul, Submodule.norm_coe, hu₀₁]
            norm_num
          have hw₀_in : ⟪w₀, w₀⟫_ℂ = 1 := by
            rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ← Submodule.norm_coe,
              coe_positiveHalfSpinCliffordMul_apply, norm_map_ι_apply hQ hρ, e.orthonormal.1 0,
              one_mul, Submodule.norm_coe, hu₀₁]
            norm_num
          have hc₂ : ⟪w₂, q.2.2⟫_ℂ = -⟪antiCanonicalSpinor o ρ e u₀, φ⟫_ℂ := by
            rw [hqexp, inner_sub_right, inner_smul_right, inner_smul_right, hw₂₀, hw₂_in,
              mul_zero, mul_one, zero_sub]
          have hc₀ : ⟪w₀, q.2.2⟫_ℂ = ⟪u₀, φ⟫_ℂ := by
            rw [hqexp, inner_sub_right, inner_smul_right, inner_smul_right, hw₀_in, hw₀₂,
              mul_one, mul_zero, sub_zero]
          have hc (z : ℂ) : (2 : ℂ) * ((z.re / 2 : ℝ) + (z.im / 2 : ℝ) * I) = z := by
            apply Complex.ext <;> simp <;> ring
          have hcn (z : ℂ) : (2 : ℂ) * ((-z.re / 2 : ℝ) + (-z.im / 2 : ℝ) * I) = -z := by
            apply Complex.ext <;> simp <;> ring
          simp only [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
            Matrix.tail_cons, hc, hcn]
          rw [hc₂, hc₀, hqexp]
          module }

@[simp]
theorem normalTargetEquiv_apply_fst (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (L A : EuclideanSpace ℝ (Fin 4)) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)).1 = L 0 :=
  (rfl)

@[simp]
theorem normalTargetEquiv_apply_snd_fst (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (L A : EuclideanSpace ℝ (Fin 4)) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)).2.1 =
      L 1 • kahlerSelfDual o J hkl he h₀ h₂₃ +
        A 0 • antiInvariantSelfDual₁ o e hkl he +
        A 1 • antiInvariantSelfDual₂ o e hkl he :=
  (rfl)

@[simp]
theorem normalTargetEquiv_apply_snd_snd (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (L A : EuclideanSpace ℝ (Fin 4)) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)).2.2 =
      ((2 : ℂ) * ((L 2 : ℂ) + (L 3 : ℂ) * I)) • positiveHalfSpinCliffordMul o ρ (e 2) u₀ -
        ((2 : ℂ) * ((A 2 : ℂ) + (A 3 : ℂ) * I)) • positiveHalfSpinCliffordMul o ρ (e 0) u₀ :=
  (rfl)

@[simp]
theorem normalTargetEquiv_symm_apply (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (q : ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1)) :
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁).symm q =
      (!₂[q.1, ⟪kahlerSelfDual o J hkl he h₀ h₂₃, q.2.1⟫,
          (⟪positiveHalfSpinCliffordMul o ρ (e 2) u₀, q.2.2⟫_ℂ).re / 2,
          (⟪positiveHalfSpinCliffordMul o ρ (e 2) u₀, q.2.2⟫_ℂ).im / 2],
       !₂[⟪antiInvariantSelfDual₁ o e hkl he, q.2.1⟫,
          ⟪antiInvariantSelfDual₂ o e hkl he, q.2.1⟫,
          -(⟪positiveHalfSpinCliffordMul o ρ (e 0) u₀, q.2.2⟫_ℂ).re / 2,
          -(⟪positiveHalfSpinCliffordMul o ρ (e 0) u₀, q.2.2⟫_ℂ).im / 2]) :=
  (rfl)

/-- `normalTargetEquiv` is an isometry for the target metric `f² + ‖τ‖² + ‖ν‖² / 4` on
`ℝ × Λ⁺ V × W⁻` and the Euclidean metric on `ℝ⁴ × ℝ⁴`. -/
theorem norm_sq_normalTargetEquiv (o : Orientation ℝ V (Fin 4))
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (L A : EuclideanSpace ℝ (Fin 4)) :
    let q := normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)
    q.1 ^ 2 + ‖q.2.1‖ ^ 2 + ‖q.2.2‖ ^ 2 / 4 = ‖L‖ ^ 2 + ‖A‖ ^ 2 := by
  intro q
  have hsd : ‖q.2.1‖ ^ 2 = L 1 ^ 2 + A 0 ^ 2 + A 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [q, normalTargetEquiv_apply_snd_fst, Submodule.coe_inner, Submodule.coe_smul,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [← Submodule.coe_inner, real_inner_self_eq_norm_sq, norm_kahlerSelfDual,
      norm_antiInvariantSelfDual₁, norm_antiInvariantSelfDual₂,
      inner_kahlerSelfDual_antiInvariantSelfDual₁, inner_kahlerSelfDual_antiInvariantSelfDual₂,
      inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂]
    rw [real_inner_comm (kahlerSelfDual o J hkl he h₀ h₂₃),
      inner_kahlerSelfDual_antiInvariantSelfDual₁,
      real_inner_comm (kahlerSelfDual o J hkl he h₀ h₂₃),
      inner_kahlerSelfDual_antiInvariantSelfDual₂,
      real_inner_comm (antiInvariantSelfDual₁ o e hkl he),
      inner_antiInvariantSelfDual₁_antiInvariantSelfDual₂]
    ring
  set w₂ := positiveHalfSpinCliffordMul o ρ (e 2) u₀
  set w₀ := positiveHalfSpinCliffordMul o ρ (e 0) u₀
  have hw₂₀ : ⟪w₂, w₀⟫_ℂ = 0 := by
    rw [← inner_conj_symm, Submodule.coe_inner, coe_positiveHalfSpinCliffordMul_apply,
      coe_positiveHalfSpinCliffordMul_apply,
      inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hρ hu₀,
      h₂₃, e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
    simp
  have hw₂ : ‖w₂‖ = 1 := by
    rw [← Submodule.norm_coe, coe_positiveHalfSpinCliffordMul_apply, norm_map_ι_apply hQ hρ,
      e.orthonormal.1 2, one_mul, Submodule.norm_coe, hu₀₁]
  have hw₀ : ‖w₀‖ = 1 := by
    rw [← Submodule.norm_coe, coe_positiveHalfSpinCliffordMul_apply, norm_map_ι_apply hQ hρ,
      e.orthonormal.1 0, one_mul, Submodule.norm_coe, hu₀₁]
  have hspin : ‖q.2.2‖ ^ 2 = 4 * (L 2 ^ 2 + L 3 ^ 2 + A 2 ^ 2 + A 3 ^ 2) := by
    simp only [q, normalTargetEquiv_apply_snd_snd]
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, hw₂₀]
    simp only [mul_zero, RCLike.zero_re, sub_zero, norm_smul, w₂, w₀, hw₂, hw₀, mul_one,
      ← normSq_eq_norm_sq, normSq_apply, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
      I_re, I_im, re_ofNat, im_ofNat]
    ring
  simp only [q, normalTargetEquiv_apply_fst] at hsd hspin ⊢
  rw [hsd, hspin, EuclideanSpace.real_norm_sq_eq L, EuclideanSpace.real_norm_sq_eq A,
    Fin.sum_univ_four, Fin.sum_univ_four]
  ring

end Intertwiners

end TauCeti.SeibergWitten
