/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Exponential
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Putnam–Wintner Borel logarithms and norm-path-connectedness of `unitary (H →L[ℂ] H)`

In a general unital C⋆-algebra `A`, the principal-branch argument `Unitary.argSelfAdjoint` from
`Mathlib.Analysis.CStarAlgebra.Unitary.Connected` uses the continuous functional calculus and
recovers a unitary `u` as `exp (I • x)` only when `Complex.arg` is continuous on `spectrum ℂ u`
(for example when `‖u - 1‖ < 2`); indeed, `unitary C(S¹, ℂ)` has `ℤ`-many connected components and
the coordinate unitary `z ↦ z` admits no self-adjoint logarithm at all.

On a complex Hilbert space `H`, `H →L[ℂ] H` carries the bounded Borel functional calculus for
normal operators, and `Complex.arg : ℂ → ℝ` is Borel measurable (`Complex.measurable_arg`) and
bounded by `π`, with `Complex.exp (Complex.arg z * Complex.I) = z` for every `z` on the unit
circle. Applying `(u : H →L[ℂ] H).borelCalculus` to `Complex.arg` therefore produces, for *every*
unitary operator `u : unitary (H →L[ℂ] H)` without any spectral gap hypothesis, a canonical
self-adjoint operator `Unitary.borelArg u : selfAdjoint (H →L[ℂ] H)` satisfying `‖borelArg u‖ ≤ π`,
`-(π • 1) ≤ borelArg u ≤ π • 1`, and `selfAdjoint.expUnitary (borelArg u) = u`.

Rescaling the exponent along `t ∈ [0, 1]` via `selfAdjoint.expUnitaryPathToOne (borelArg u)` joins
`1` to `u` by an explicit norm-continuous path inside `unitary (H →L[ℂ] H)` that stays inside the
closed ball around `1` of radius `‖(u - 1 : H →L[ℂ] H)‖`, proving that `unitary (H →L[ℂ] H)` is
norm-path-connected in arbitrary Hilbert dimension (Putnam–Wintner, 1952).

## Main declarations

* `Unitary.borelArg`: canonical self-adjoint Borel argument of `u : unitary (H →L[ℂ] H)` with
  spectrum in `[-π, π]`.
* `Unitary.norm_borelArg_le_pi`, `Unitary.neg_pi_smul_one_le_borelArg`,
  `Unitary.borelArg_le_pi_smul_one`: operator-norm and Loewner order bounds on `borelArg u`.
* `Unitary.exp_I_smul_borelArg`, `Unitary.expUnitary_borelArg`: Putnam–Wintner theorem
  `exp (I • borelArg u) = u`, hence `selfAdjoint.surjective_expUnitary`.
* `Unitary.norm_borelArg`: unconditional formula
  `‖borelArg u‖ = Real.arccos (1 - ‖(u - 1 : H →L[ℂ] H)‖ ^ 2 / 2)`.
* `Unitary.borelArg_eq_argSelfAdjoint_of_continuousOn`, `Unitary.borelArg_eq_argSelfAdjoint`,
  `Unitary.borelArg_expUnitary`: agreement with `Unitary.argSelfAdjoint` whenever `Complex.arg` is
  continuous on `spectrum ℂ u` (in particular on `Metric.ball 1 2`) and left-inverse identity on
  `Metric.ball 0 π`.
* `Unitary.borelArg_one`, `Unitary.borelArg_neg_one`, `Unitary.borelArg_conj`: values at `1` and
  `-1`, and equivariance under Hilbert-space linear isometric equivalences.
* `Unitary.borelPathToOne`, `Unitary.instPathConnectedSpace`, `Unitary.isPathConnected`: explicit
  norm-continuous path from `1` to `u` and norm-path-connectedness of `unitary (H →L[ℂ] H)`.

## References

* C. R. Putnam, A. Wintner, *The connectedness of the orthogonal and unitary groups*,
  Amer. J. Math. **74** (1952), 52–70.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, 2nd ed., Springer (1998),
  Proposition 4.29.
-/

public section

noncomputable section

open MeasureTheory NormedSpace TauCeti
open scoped InnerProductSpace Real unitInterval

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real scalar multiplication on `H →L[ℂ] H` (acting on the codomain via
`ContinuousLinearMap.instSMul`) commutes with the Hilbert-space adjoint. Mathlib's
`StarModule.complexToReal` covers only `Module.complexToReal`, so this `Prop` instance unlocks
`Module ℝ` and `NormedSpace ℝ` on `selfAdjoint (H →L[ℂ] H)`. -/
instance ContinuousLinearMap.instStarModuleReal : StarModule ℝ (H →L[ℂ] H) where
  star_smul r T := by simp [← Complex.coe_smul]

namespace Unitary

/-- The real-valued bounded Borel symbol `z ↦ Complex.arg z` on `spectrum ℂ (u : H →L[ℂ] H)`. -/
def borelArgSymbol (u : unitary (H →L[ℂ] H)) :
    BoundedBorelFunction (spectrum ℂ (u : H →L[ℂ] H)) :=
  BoundedBorelFunction.ofRealFunction (fun z ↦ Complex.arg (z : ℂ))
    (Complex.measurable_arg.comp measurable_subtype_coe)
    ⟨π, Real.pi_nonneg, fun z ↦ Complex.abs_arg_le_pi (z : ℂ)⟩

/-- Evaluating `borelArgSymbol u` at a spectral value `z` gives `(Complex.arg z : ℂ)`. -/
@[simp]
theorem borelArgSymbol_apply (u : unitary (H →L[ℂ] H)) (z : spectrum ℂ (u : H →L[ℂ] H)) :
    borelArgSymbol u z = Complex.arg (z : ℂ) := by
  simp [borelArgSymbol]

/-- The **Borel argument** of a unitary operator `u : unitary (H →L[ℂ] H)`: the self-adjoint
operator obtained by applying the Borel functional calculus of `u` to the principal argument
`Complex.arg : ℂ → (-π, π]`. Unlike `Unitary.argSelfAdjoint`, this requires no continuity
hypothesis on `spectrum ℂ (u : H →L[ℂ] H)`. -/
def borelArg (u : unitary (H →L[ℂ] H)) : selfAdjoint (H →L[ℂ] H) :=
  ⟨(u : H →L[ℂ] H).borelCalculus (borelArgSymbol u),
    (u : H →L[ℂ] H).isSelfAdjoint_borelCalculus_ofRealFunction _ _ _⟩

/-- Coercing `borelArg u` to `H →L[ℂ] H` gives the Borel calculus of `u` at `borelArgSymbol u`. -/
@[simp]
theorem borelArg_coe (u : unitary (H →L[ℂ] H)) :
    (borelArg u : H →L[ℂ] H) = (u : H →L[ℂ] H).borelCalculus (borelArgSymbol u) :=
  (rfl)

/-- The operator norm of `borelArg u` is at most `π`. -/
theorem norm_borelArg_le_pi (u : unitary (H →L[ℂ] H)) : ‖borelArg u‖ ≤ π :=
  (u : H →L[ℂ] H).norm_borelCalculus_le Real.pi_nonneg fun z ↦ by
    simpa [borelArgSymbol] using Complex.abs_arg_le_pi (z : ℂ)

/-- Loewner lower bound `-(π • 1) ≤ borelArg u`. -/
theorem neg_pi_smul_one_le_borelArg (u : unitary (H →L[ℂ] H)) :
    -(π • (1 : H →L[ℂ] H)) ≤ (borelArg u : H →L[ℂ] H) := by
  rw [← neg_smul, borelArg_coe]
  exact (u : H →L[ℂ] H).smul_one_le_borelCalculus_ofRealFunction _ _
    fun z ↦ (Complex.neg_pi_lt_arg (z : ℂ)).le

/-- Loewner upper bound `borelArg u ≤ π • 1`. -/
theorem borelArg_le_pi_smul_one (u : unitary (H →L[ℂ] H)) :
    (borelArg u : H →L[ℂ] H) ≤ π • (1 : H →L[ℂ] H) :=
  (u : H →L[ℂ] H).borelCalculus_ofRealFunction_le_smul_one _ _
    fun z ↦ Complex.arg_le_pi (z : ℂ)

/-- **Putnam–Wintner unitary logarithm theorem.** Every unitary operator `u` on a complex Hilbert
space is the Banach-algebra exponential of `Complex.I • borelArg u`. -/
theorem exp_I_smul_borelArg (u : unitary (H →L[ℂ] H)) :
    NormedSpace.exp (Complex.I • (borelArg u : H →L[ℂ] H)) = (u : H →L[ℂ] H) := by
  rw [borelArg_coe, ← map_smul, ← (u : H →L[ℂ] H).borelCalculus_exp]
  have hsym : NormedSpace.exp (Complex.I • borelArgSymbol u) =
      BoundedBorelFunction.ofContinuousMap
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ (u : H →L[ℂ] H))) := by
    ext z
    have hz : ‖(z : ℂ)‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 z.2
    simp only [BoundedBorelFunction.exp_apply, BoundedBorelFunction.smul_apply,
      borelArgSymbol_apply, mul_comm Complex.I,
      BoundedBorelFunction.ofContinuousMap_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply]
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hsym, (u : H →L[ℂ] H).borelCalculus_restrict_id]

/-- Bundled unitary form of `exp_I_smul_borelArg`: `selfAdjoint.expUnitary` is a left inverse to
`borelArg` on the entire unitary group `unitary (H →L[ℂ] H)`. -/
@[simp]
theorem expUnitary_borelArg (u : unitary (H →L[ℂ] H)) :
    selfAdjoint.expUnitary (borelArg u) = u :=
  Subtype.ext (exp_I_smul_borelArg u)

/-- Every unitary operator on a complex Hilbert space has a self-adjoint logarithm of norm at most
`π`. -/
theorem exists_norm_le_pi_expUnitary_eq (u : unitary (H →L[ℂ] H)) :
    ∃ a : selfAdjoint (H →L[ℂ] H), ‖a‖ ≤ π ∧ selfAdjoint.expUnitary a = u :=
  ⟨borelArg u, norm_borelArg_le_pi u, expUnitary_borelArg u⟩

/-- Exact relation between `‖borelArg u‖` and `‖u - 1‖`, valid for *all* unitary operators on `H`
without any spectral gap hypothesis. -/
theorem two_mul_one_sub_cos_norm_borelArg (u : unitary (H →L[ℂ] H)) :
    2 * (1 - Real.cos ‖borelArg u‖) = ‖(u - 1 : H →L[ℂ] H)‖ ^ 2 := by
  conv_rhs => rw [← expUnitary_borelArg u]
  exact (selfAdjoint.norm_sq_expUnitary_sub_one (norm_borelArg_le_pi u)).symm

/-- Exact norm formula for `borelArg u`, valid unconditionally for every `u : unitary (H →L[ℂ] H)`.
-/
theorem norm_borelArg (u : unitary (H →L[ℂ] H)) :
    ‖borelArg u‖ = Real.arccos (1 - ‖(u - 1 : H →L[ℂ] H)‖ ^ 2 / 2) := by
  refine (Real.arccos_eq_of_eq_cos (norm_nonneg _) (norm_borelArg_le_pi u) ?_).symm
  linarith [two_mul_one_sub_cos_norm_borelArg u]

/-- Whenever `Complex.arg` is continuous on `spectrum ℂ (u : H →L[ℂ] H)` (for instance when `-1`
is absent or isolated in the spectrum), `borelArg u` agrees with the continuous functional calculus
logarithm `Unitary.argSelfAdjoint u`. -/
theorem borelArg_eq_argSelfAdjoint_of_continuousOn {u : unitary (H →L[ℂ] H)}
    (h : ContinuousOn Complex.arg (spectrum ℂ (u : H →L[ℂ] H))) :
    borelArg u = argSelfAdjoint u := by
  ext1
  have hcont : ContinuousOn (fun z : ℂ ↦ (Complex.arg z : ℂ)) (spectrum ℂ (u : H →L[ℂ] H)) :=
    Complex.continuous_ofReal.comp_continuousOn h
  have hsym : borelArgSymbol u = BoundedBorelFunction.ofContinuousMap
      ⟨(spectrum ℂ (u : H →L[ℂ] H)).domRestrict (fun z : ℂ ↦ (Complex.arg z : ℂ)),
        hcont.domRestrict⟩ := by
    ext z
    simp
  rw [borelArg_coe, hsym,
    (u : H →L[ℂ] H).borelCalculus_ofContinuousMap_domRestrict _ hcont, argSelfAdjoint_coe]

/-- On the open ball `‖(u - 1 : H →L[ℂ] H)‖ < 2` where the spectrum avoids `-1`, `borelArg u`
coincides with `Unitary.argSelfAdjoint u`. -/
theorem borelArg_eq_argSelfAdjoint {u : unitary (H →L[ℂ] H)}
    (hu : ‖(u - 1 : H →L[ℂ] H)‖ < 2) :
    borelArg u = argSelfAdjoint u :=
  borelArg_eq_argSelfAdjoint_of_continuousOn <|
    Complex.continuousOn_arg.mono ((spectrum_subset_slitPlane_iff_norm_lt_two u.2).2 hu)

-- Elaborate `expUnitary x` before unifying its `Monoid` projection with `borelArg`'s domain.
/-- On the open ball `‖x‖ < π` in `selfAdjoint (H →L[ℂ] H)`, `borelArg` is a left inverse to
`selfAdjoint.expUnitary`. -/
theorem borelArg_expUnitary {x : selfAdjoint (H →L[ℂ] H)} (hx : ‖x‖ < π) :
    borelArg (selfAdjoint.expUnitary x : _) = x := by
  have hcos : -1 < Real.cos ‖x‖ :=
    Real.cos_pi ▸ Real.cos_lt_cos_of_nonneg_of_le_pi (norm_nonneg x) le_rfl hx
  have hsq : ‖((selfAdjoint.expUnitary x : _) - 1 : H →L[ℂ] H)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖) :=
    selfAdjoint.norm_sq_expUnitary_sub_one hx.le
  have hu : ‖((selfAdjoint.expUnitary x : _) - 1 : H →L[ℂ] H)‖ < 2 := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (by positivity), hsq]
    linarith
  rw [borelArg_eq_argSelfAdjoint hu]
  refine (congrArg argSelfAdjoint (Subtype.ext ?_)).trans (argSelfAdjoint_expUnitary hx)
  simp only [selfAdjoint.expUnitary_coe]

/-- The Borel argument of the identity unitary `1` is `0`. -/
@[simp]
theorem borelArg_one : borelArg (1 : unitary (H →L[ℂ] H)) = 0 := by
  simpa using borelArg_expUnitary (x := (0 : selfAdjoint (H →L[ℂ] H))) (by simpa using Real.pi_pos)

/-- At the antipodal unitary `-1`, `borelArg (-1)` equals `π • 1` (since `Complex.arg (-1) = π`). -/
@[simp]
theorem borelArg_neg_one :
    borelArg (-1 : unitary (H →L[ℂ] H)) = π • (1 : selfAdjoint (H →L[ℂ] H)) := by
  ext1
  nontriviality (H →L[ℂ] H)
  have hspec : spectrum ℂ ((-1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = {-1} := by
    rw [coe_neg, OneMemClass.coe_one, ← spectrum.neg_eq, spectrum.one_eq, Set.neg_singleton]
  have hsym : borelArgSymbol (-1 : unitary (H →L[ℂ] H)) =
      algebraMap ℂ (BoundedBorelFunction (spectrum ℂ ((-1 : unitary (H →L[ℂ] H)) : H →L[ℂ] H)))
        π := by
    ext ⟨z, hz⟩
    rw [hspec, Set.mem_singleton_iff] at hz
    subst hz
    simp
  rw [borelArg_coe, hsym, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rfl

section UnitaryConj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- Conjugating a unitary operator by a Hilbert-space linear isometric equivalence `U : H ≃ₗᵢ[ℂ] H'`
conjugates its Borel argument. -/
theorem borelArg_conj (U : H ≃ₗᵢ[ℂ] H') (u : unitary (H →L[ℂ] H)) :
    (borelArg ⟨U.conjStarAlgEquiv (u : H →L[ℂ] H), Unitary.map_mem U.conjStarAlgEquiv u.2⟩ :
        H' →L[ℂ] H') =
      U.conjStarAlgEquiv (borelArg u : H →L[ℂ] H) := by
  let u' : unitary (H' →L[ℂ] H') :=
    ⟨U.conjStarAlgEquiv (u : H →L[ℂ] H), Unitary.map_mem U.conjStarAlgEquiv u.2⟩
  have hinst : @ContinuousLinearMap.borelCalculus _ _ _ _ (u' : H' →L[ℂ] H')
        (Unitary.coe_isStarNormal u') =
      @ContinuousLinearMap.borelCalculus _ _ _ _ (U.conjStarAlgEquiv (u : H →L[ℂ] H))
        (IsStarNormal.map U.conjStarAlgEquiv (u : H →L[ℂ] H)) :=
    Subsingleton.elim (Unitary.coe_isStarNormal u')
      (IsStarNormal.map U.conjStarAlgEquiv (u : H →L[ℂ] H)) ▸ rfl
  change @ContinuousLinearMap.borelCalculus _ _ _ _ (u' : H' →L[ℂ] H')
      (Unitary.coe_isStarNormal u') (borelArgSymbol u') =
    U.conjStarAlgEquiv ((u : H →L[ℂ] H).borelCalculus (borelArgSymbol u))
  rw [hinst, (u : H →L[ℂ] H).borelCalculus_conj U]
  refine congrArg U.conjStarAlgEquiv (congrArg (u : H →L[ℂ] H).borelCalculus ?_)
  ext z
  simp only [BoundedBorelFunction.compStarAlgHom'_apply, borelArgSymbol_apply]
  exact (borelArgSymbol_apply u' _).trans rfl

end UnitaryConj

/-- The canonical norm-continuous path `t ↦ expUnitary (t • borelArg u)` from `1` to `u` in
`unitary (H →L[ℂ] H)`. -/
def borelPathToOne (u : unitary (H →L[ℂ] H)) : Path 1 u where
  toFun t := selfAdjoint.expUnitary ((t : ℝ) • borelArg u)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Evaluating `borelPathToOne u` at `t` gives `selfAdjoint.expUnitary ((t : ℝ) • borelArg u)`. -/
@[simp]
theorem borelPathToOne_apply (u : unitary (H →L[ℂ] H)) (t : I) :
    borelPathToOne u t = selfAdjoint.expUnitary ((t : ℝ) • borelArg u) :=
  (rfl)

/-- Along `borelPathToOne u`, the distance from `1` never exceeds `‖(u - 1 : H →L[ℂ] H)‖`. -/
theorem norm_borelPathToOne_sub_one_le (u : unitary (H →L[ℂ] H)) (t : I) :
    ‖((borelPathToOne u t : unitary (H →L[ℂ] H)) - 1 : H →L[ℂ] H)‖ ≤
      ‖(u - 1 : H →L[ℂ] H)‖ := by
  have ht : ‖(t : ℝ) • borelArg u‖ ≤ ‖borelArg u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
    exact mul_le_of_le_one_left (norm_nonneg _) t.2.2
  have hsq : ‖(selfAdjoint.expUnitary ((t : ℝ) • borelArg u) - 1 : H →L[ℂ] H)‖ ^ 2 =
      2 * (1 - Real.cos ‖(t : ℝ) • borelArg u‖) :=
    selfAdjoint.norm_sq_expUnitary_sub_one (ht.trans (norm_borelArg_le_pi u))
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), borelPathToOne_apply, hsq,
    ← two_mul_one_sub_cos_norm_borelArg u]
  gcongr
  exact Real.cos_le_cos_of_nonneg_of_le_pi (norm_nonneg _) (norm_borelArg_le_pi u) ht

/-- Every unitary operator on a complex Hilbert space is joined to `1` in `unitary (H →L[ℂ] H)`. -/
theorem joined_one (u : unitary (H →L[ℂ] H)) : Joined 1 u :=
  ⟨borelPathToOne u⟩

/-- **Putnam–Wintner theorem.** The unitary group `unitary (H →L[ℂ] H)` of any complex Hilbert
space `H` is norm-path-connected. -/
instance instPathConnectedSpace : PathConnectedSpace (unitary (H →L[ℂ] H)) where
  nonempty := ⟨1⟩
  joined u v := (joined_one u).symm.trans (joined_one v)

/-- The path component of `1` in `unitary (H →L[ℂ] H)` is the entire unitary group. -/
@[simp]
theorem pathComponent_one_eq_univ :
    pathComponent (1 : unitary (H →L[ℂ] H)) = Set.univ :=
  Set.eq_univ_of_forall joined_one

/-- The set of unitary operators in `H →L[ℂ] H` is path-connected in the operator norm topology. -/
theorem isPathConnected :
    IsPathConnected (unitary (H →L[ℂ] H) : Set (H →L[ℂ] H)) := by
  rw [← Subtype.range_val (s := (unitary (H →L[ℂ] H) : Set (H →L[ℂ] H)))]
  exact isPathConnected_range (X := unitary (H →L[ℂ] H)) continuous_subtype_val

end Unitary

/-- The exponential map `selfAdjoint.expUnitary : selfAdjoint (H →L[ℂ] H) → unitary (H →L[ℂ] H)`
is surjective on any complex Hilbert space `H`. -/
theorem selfAdjoint.surjective_expUnitary :
    Function.Surjective (selfAdjoint.expUnitary : selfAdjoint (H →L[ℂ] H) → unitary (H →L[ℂ] H)) :=
  fun u ↦ ⟨Unitary.borelArg u, Unitary.expUnitary_borelArg u⟩

end Unitary
