/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.QuaternionicStructure
public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Charge conjugation of the Seiberg–Witten quadratic map

Charge conjugation sends a Seiberg–Witten configuration `(A, ψ)` on a `Spinᶜ` structure to the
configuration `(conj A, j ψ)` on the conjugate `Spinᶜ` structure, where `j` is the quaternionic
structure of the half-spinors: a conjugate-linear isometry with `j (j ψ) = -ψ`
(`TauCeti.stdQuaternionicStructure` on `ℂ²`). Conjugation negates the imaginary curvature form
`F_A`. The curvature equation `F_A⁺ = Q₀(ψ) + η` is therefore carried to the curvature equation
with forcing `-η`, because the quadratic map changes sign:

`Q₀(j ψ) = -Q₀(ψ)`, where `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id`.

The first part of this file proves that sign change and its consequences for the polarization
and derivative of `Q₀`, pointwise on a complex inner product space `E` of complex dimension two.
The proof uses the decomposition `ψψ* + (j ψ)(j ψ)* = ‖ψ‖² Id`
(`LinearIsometry.rankOne_self_add_rankOne_map_self`).

Any conjugate-linear isometry `j : E → F` intertwines `Q₀(ψ)` with `Q₀(j ψ)`; with the sign
change, a quaternionic structure anticommutes with every `Q₀(ψ)`.

## Clifford modules

The second part works with the quadratic term of the actual curvature equation
`F_A⁺ = q(ψ) + η`, the self-dual two-form `q(ψ) = τ(Q₀(ψ)) / 4`
(`TauCeti.SeibergWitten.quadraticTwoForm`). Let `W` and `W'` be Hermitian Clifford modules over
the same oriented four-space `V`, and let `j : W → W'` be a conjugate-linear isometric
equivalence commuting with Clifford multiplication, `j (c(v) w) = c(v) (j w)`. Such a `j`
identifies `W'` with the conjugate of `W`; for the spinors of `Spinᶜ(4)` it is multiplication by
the quaternion `j`, and `W'` is the spinor module of the conjugate `Spinᶜ` structure. Then `j`
commutes with every Clifford element (`CliffordAlgebra.comp_eq_map_comp_of_forall_ιₛₗ`), in
particular with the chirality element, so it restricts to the positive half-spinors
(`TauCeti.SeibergWitten.positiveHalfSpinorsConjEquiv`). Since `j` is conjugate-linear, it
anticommutes with the Clifford map `C(iα) = i c₂(α)`:

`C(iα) (j ψ) = -j (C(iα) ψ)`.

Since `j` conjugates traces (`LinearIsometryEquiv.trace_eq_conj_trace`), the adjoint `τ = C*`
also changes sign, and hence so does `q`:

`q(j ψ) = -q(ψ)`,  `q'(j ψ, j φ) = -q'(ψ, φ)`.

This holds for every such `j` and in any dimension of `W⁺`, without assuming `j² = -1`. Since
conjugation negates `F_A`, these are the pointwise identities by which
`(A, ψ, η) ↦ (conj A, j ψ, -η)` carries the curvature equation, and through the polarization,
which is the derivative of `q`, its linearization, to those of the conjugate `Spinᶜ` structure.
Finally `j` exchanges the two eigenlines of a self-dual form `ω` of norm `√2`, the summands of
Taubes's decomposition `ψ = α u₀ + β`: `P_α (j ψ) = j (P_β ψ)`, where `P_α = (1 + C(iω) / 2) / 2`
and `P_β` is the complementary projection.

## Main results

* `TauCeti.SeibergWitten.map_quadraticEnd_apply`: `j (Q₀(ψ) v) = Q₀(j ψ) (j v)` for every
  conjugate-linear isometry `j`.
* `TauCeti.SeibergWitten.quadraticEnd_map`: `Q₀(j ψ) = -Q₀(ψ)` in complex dimension two.
* `TauCeti.SeibergWitten.quadraticEndPolar_map_map`: the polarization, which is also the
  derivative of `Q₀`, satisfies `B(j ψ, j φ) = -B(ψ, φ)`.
* `TauCeti.SeibergWitten.map_quadraticEnd_apply_eq_neg`: `j` anticommutes with `Q₀(ψ)`.
* `TauCeti.SeibergWitten.positiveHalfSpinorsConjEquiv`: a conjugate-linear Clifford intertwiner
  restricted to the positive half-spinors.
* `TauCeti.SeibergWitten.cliffordRestriction_positiveHalfSpinorsConjEquiv`:
  `C(iα) (j ψ) = -j (C(iα) ψ)`.
* `TauCeti.SeibergWitten.cliffordRestrictionAdjoint_eq_neg`: `τ(T') = -τ(T)` when `T' j = j T`.
* `TauCeti.SeibergWitten.quadraticTwoForm_positiveHalfSpinorsConjEquiv`: `q(j ψ) = -q(ψ)`.
* `TauCeti.SeibergWitten.quadraticTwoFormPolar_positiveHalfSpinorsConjEquiv`:
  `q'(j ψ, j φ) = -q'(ψ, φ)`.
* `TauCeti.SeibergWitten.cliffordProjection_positiveHalfSpinorsConjEquiv`:
  `P_α (j ψ) = j (P_β ψ)`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

/-- A conjugate-linear isometry `j` intertwines `Q₀(ψ)` with `Q₀(j ψ)`:
`j (Q₀(ψ) v) = Q₀(j ψ) (j v)`. -/
theorem map_quadraticEnd_apply (j : E →ₗᵢ⋆[ℂ] F) (ψ v : E) :
    j (quadraticEnd ψ v) = quadraticEnd (j ψ) (j v) := by
  simp only [quadraticEnd_apply, map_sub, map_smulₛₗ, j.inner_map_map_eq_conj, j.norm_map,
    map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]

/-- A conjugate-linear isometry `j` intertwines `B(ψ, φ)` with `B(j ψ, j φ)`:
`j (B(ψ, φ) v) = B(j ψ, j φ) (j v)`. -/
theorem map_quadraticEndPolar_apply (j : E →ₗᵢ⋆[ℂ] F) (ψ φ v : E) :
    j (quadraticEndPolar ψ φ v) = quadraticEndPolar (j ψ) (j φ) (j v) := by
  simp only [quadraticEndPolar_apply_apply, map_sub, map_add, map_smulₛₗ,
    j.inner_map_map_eq_conj, Complex.conj_ofReal, Complex.conj_re]

variable {j : E →ₗᵢ⋆[ℂ] E}

/-- **Charge conjugation reverses the quadratic map**: for a quaternionic structure `j` in complex
dimension two, `Q₀(j ψ) = -Q₀(ψ)`. -/
theorem quadraticEnd_map (hj : ∀ ψ, j (j ψ) = -ψ) (h₂ : Module.finrank ℂ E = 2) (ψ : E) :
    quadraticEnd (j ψ) = -quadraticEnd ψ := by
  have h := j.rankOne_self_add_rankOne_map_self hj h₂ ψ
  rw [quadraticEnd_def, quadraticEnd_def, j.norm_map, eq_sub_of_add_eq' h]
  module

/-- For a quaternionic structure `j` in complex dimension two, the polarization of `Q₀` satisfies
`B(j ψ, j φ) = -B(ψ, φ)`. Since `B(ψ, ·)` is the derivative of `Q₀` at `ψ`, charge conjugation
also reverses the linearized curvature equation. -/
theorem quadraticEndPolar_map_map (hj : ∀ ψ, j (j ψ) = -ψ) (h₂ : Module.finrank ℂ E = 2)
    (ψ φ : E) : quadraticEndPolar (j ψ) (j φ) = -quadraticEndPolar ψ φ := by
  have h := quadraticEnd_add (j ψ) (j φ)
  rw [← map_add, quadraticEnd_map hj h₂, quadraticEnd_map hj h₂, quadraticEnd_map hj h₂,
    quadraticEnd_add] at h
  linear_combination (norm := module) -h

/-- In complex dimension two a quaternionic structure `j` anticommutes with every `Q₀(ψ)`:
`j (Q₀(ψ) v) = -Q₀(ψ) (j v)`. -/
theorem map_quadraticEnd_apply_eq_neg (hj : ∀ ψ, j (j ψ) = -ψ) (h₂ : Module.finrank ℂ E = 2)
    (ψ v : E) : j (quadraticEnd ψ v) = -quadraticEnd ψ (j v) := by
  rw [map_quadraticEnd_apply, quadraticEnd_map hj h₂, neg_apply]

/-! ### Conjugate-linear Clifford intertwiners -/

section Clifford

open CliffordAlgebra Module
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
  (ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W')
  (j : W ≃ₗᵢ⋆[ℂ] W') (hj : ∀ v w, j (ρ (ι Q v) w) = ρ' (ι Q v) (j w))

omit [Fact (finrank ℝ V = 4)] in
variable {ρ ρ' j} in
include hj in
/-- A conjugate-linear isometric equivalence commuting with the generators commutes with every
Clifford element: `j (ρ x w) = ρ' x (j w)`. -/
private theorem map_apply_of_forall_ι (x : CliffordAlgebra Q) (w : W) :
    j (ρ x w) = ρ' x (j w) := by
  have h := comp_eq_map_comp_of_forall_ιₛₗ (f := QuadraticMap.Isometry.id Q)
    (fun r ↦ Complex.conj_ofReal r) (U := j.toLinearEquiv.toLinearMap)
    (fun v ↦ LinearMap.ext (hj v)) x
  simpa [map_id] using LinearMap.congr_fun h w

variable {o ρ ρ' j} in
include hj in
/-- A conjugate-linear Clifford intertwiner maps positive half-spinors to positive half-spinors. -/
theorem map_mem_positiveHalfSpinors {w : W} (hw : w ∈ positiveHalfSpinors o ρ) :
    j w ∈ positiveHalfSpinors o ρ' := by
  rw [mem_positiveHalfSpinors] at hw ⊢
  rw [← map_apply_of_forall_ι hj, hw]

omit [Fact (finrank ℝ V = 4)] in
include hj in
/-- The inverse of a conjugate-linear Clifford intertwiner is again one. -/
private theorem symm_apply_of_forall_ι (v : V) (w : W') :
    j.symm (ρ' (ι Q v) w) = ρ (ι Q v) (j.symm w) := by
  rw [j.symm_apply_eq, hj, j.apply_symm_apply]

/-- **Charge conjugation of positive half-spinors**: a conjugate-linear isometric equivalence `j`
commuting with Clifford multiplication restricts to a conjugate-linear isometric equivalence
`W⁺ ≃ W'⁺` of the positive half-spinors. -/
def positiveHalfSpinorsConjEquiv :
    positiveHalfSpinors o ρ ≃ₗᵢ⋆[ℂ] positiveHalfSpinors o ρ' where
  toFun ψ := ⟨j ψ, map_mem_positiveHalfSpinors hj ψ.2⟩
  invFun ψ := ⟨j.symm ψ, map_mem_positiveHalfSpinors (symm_apply_of_forall_ι ρ ρ' j hj) ψ.2⟩
  map_add' ψ φ := Subtype.ext <| by simp
  map_smul' c ψ := Subtype.ext <| by simp [map_smulₛₗ]
  left_inv ψ := Subtype.ext (j.symm_apply_apply ψ)
  right_inv ψ := Subtype.ext (j.apply_symm_apply ψ)
  norm_map' ψ := j.norm_map (ψ : W)

/-- The restriction of `j` to the positive half-spinors is `j`. -/
@[simp]
theorem coe_positiveHalfSpinorsConjEquiv_apply (ψ : positiveHalfSpinors o ρ) :
    (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ : W') = j ψ :=
  (rfl)

/-- The inverse of the restriction of `j` to the positive half-spinors is `j⁻¹`. -/
@[simp]
theorem coe_positiveHalfSpinorsConjEquiv_symm_apply (ψ : positiveHalfSpinors o ρ') :
    ((positiveHalfSpinorsConjEquiv o ρ ρ' j hj).symm ψ : W) = j.symm ψ :=
  (rfl)

attribute [local instance] finiteDimensional_of_finrank_four

variable [FiniteDimensional ℂ W] [FiniteDimensional ℂ W']

/-- **Charge conjugation anticommutes with the Clifford map**: `C(iα) (j ψ) = -j (C(iα) ψ)` on
positive half-spinors, since `j` commutes with `c₂(α)` and conjugates the scalar `i`. -/
theorem cliffordRestriction_positiveHalfSpinorsConjEquiv (x : ⋀[ℝ]^2 V)
    (ψ : positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ' x (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ) =
      -positiveHalfSpinorsConjEquiv o ρ ρ' j hj (cliffordRestriction o ρ x ψ) := by
  apply Subtype.ext
  simp [map_smulₛₗ, map_apply_of_forall_ι hj]

/-- **Charge conjugation reverses the adjoint of the Clifford map**: if endomorphisms `T` of `W⁺`
and `T'` of `W'⁺` are related by `T' (j ψ) = j (T ψ)`, then `τ(T') = -τ(T)`. -/
theorem cliffordRestrictionAdjoint_eq_neg (hkl : 2 + 2 = finrank ℝ V)
    {T : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ}
    {T' : positiveHalfSpinors o ρ' →L[ℂ] positiveHalfSpinors o ρ'}
    (hT : ∀ ψ, T' (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ) =
      positiveHalfSpinorsConjEquiv o ρ ρ' j hj (T ψ)) :
    cliffordRestrictionAdjoint o ρ' hkl T' = -cliffordRestrictionAdjoint o ρ hkl T := by
  refine ext_inner_right ℝ fun β ↦ ?_
  -- `j` relates `T' C(iβ)` to `-T C(iβ)`, so their traces are conjugate.
  rw [inner_neg_left, inner_cliffordRestrictionAdjoint_left, inner_cliffordRestrictionAdjoint_left,
    ← ContinuousLinearMap.toLinearMap_mul, ← ContinuousLinearMap.toLinearMap_mul,
    LinearIsometryEquiv.trace_eq_conj_trace (positiveHalfSpinorsConjEquiv o ρ ρ' j hj)
      (T := ((-(T * cliffordRestriction o ρ β) : positiveHalfSpinors o ρ →L[ℂ] _) :
        Module.End ℂ (positiveHalfSpinors o ρ))) ?_]
  · simp
  · intro ψ
    simp [cliffordRestriction_positiveHalfSpinorsConjEquiv, hT]

/-- **Charge conjugation reverses the quadratic two-form**: `q(j ψ) = -q(ψ)`. With
`F_(conj A) = -F_A`, this turns the curvature equation `F_A⁺ = q(ψ) + η` into the curvature equation
for `(conj A, j ψ)` with forcing `-η`. -/
theorem quadraticTwoForm_positiveHalfSpinorsConjEquiv (hkl : 2 + 2 = finrank ℝ V)
    (ψ : positiveHalfSpinors o ρ) :
    quadraticTwoForm o ρ' hkl (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ) =
      -quadraticTwoForm o ρ hkl ψ := by
  rw [quadraticTwoForm_def, quadraticTwoForm_def,
    cliffordRestrictionAdjoint_eq_neg o ρ ρ' j hj hkl (T := quadraticEnd ψ)
      (T' := quadraticEnd (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ))
      fun φ ↦ (map_quadraticEnd_apply (positiveHalfSpinorsConjEquiv o ρ ρ' j hj).toLinearIsometry
        ψ φ).symm, smul_neg]

/-- **Charge conjugation reverses the polarization of `q`**, which is its real derivative:
`q'(j ψ, j φ) = -q'(ψ, φ)`, the corresponding identity for the linearized curvature equation. -/
theorem quadraticTwoFormPolar_positiveHalfSpinorsConjEquiv (hkl : 2 + 2 = finrank ℝ V)
    (ψ φ : positiveHalfSpinors o ρ) :
    quadraticTwoFormPolar o ρ' hkl (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ)
        (positiveHalfSpinorsConjEquiv o ρ ρ' j hj φ) =
      -quadraticTwoFormPolar o ρ hkl ψ φ := by
  rw [quadraticTwoFormPolar_apply, quadraticTwoFormPolar_apply,
    cliffordRestrictionAdjoint_eq_neg o ρ ρ' j hj hkl (T := quadraticEndPolar ψ φ)
      (T' := quadraticEndPolar (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ)
        (positiveHalfSpinorsConjEquiv o ρ ρ' j hj φ))
      fun χ ↦ (map_quadraticEndPolar_apply
        (positiveHalfSpinorsConjEquiv o ρ ρ' j hj).toLinearIsometry ψ φ χ).symm, smul_neg]

/-- **Charge conjugation exchanges the Clifford projections**: `P_α (j ψ) = j (P_β ψ)`, where
`P_α = (1 + C(iω) / 2) / 2` and `P_β` is the same projection for `-ω`. For self-dual `ω` with
`‖ω‖² = 2`, `j` thus maps the `-2`-eigenline of `C(iω)` on `W⁺` to the `2`-eigenline on `W'⁺`,
and the `2`-eigenline to the `-2`-eigenline. -/
theorem cliffordProjection_positiveHalfSpinorsConjEquiv (ω : ⋀[ℝ]^2 V)
    (ψ : positiveHalfSpinors o ρ) :
    cliffordProjection o ρ' ω (positiveHalfSpinorsConjEquiv o ρ ρ' j hj ψ) =
      positiveHalfSpinorsConjEquiv o ρ ρ' j hj (cliffordProjection o ρ (-ω) ψ) := by
  simp only [cliffordProjection_eq_smul, smul_apply, add_apply, one_apply_eq_self, map_neg,
    neg_apply, cliffordRestriction_positiveHalfSpinorsConjEquiv, map_smulₛₗ, map_add, smul_neg,
    map_inv₀, map_ofNat]

end Clifford

end TauCeti.SeibergWitten
