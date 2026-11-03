/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.IntegrationCurrent
public import TauCeti.Analysis.Distribution.TestFunction.TopDegree
import TauCeti.Analysis.Distribution.Constancy.Basic

/-!
# The constancy theorem for top-degree currents

Let `E` be a real vector space of finite dimension `m` with an orientation `o`, and let `Ω` be a
connected open subset of `E`. A *top-degree current* on `Ω` is a continuous linear functional `T`
on the test `m`-forms `𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ)`, and its boundary is `∂T = T ∘ d`. The
**constancy theorem** says that if `∂T = 0`, then `T = c • [[Ω]]` for a unique real constant `c`,
where `[[Ω]]` is the oriented integration current `Orientation.integrationCurrent o Ω`.
Conversely `[[Ω]]` has zero boundary, so this characterizes the top-degree currents without
boundary on a connected open set. No order-zero or finite-mass assumption is made on `T`.

In degree zero the space `E` is a point, the boundary condition is vacuous (the current complex is
zero in negative degrees), and every `0`-current on the connected set `Ω = E` is a multiple of the
Dirac current `[[Ω]]`. Restricting a current without boundary to a connected open subset `U` of
an arbitrary open set `Ω` gives the local form: on each such `U`, `T` is a constant multiple of
`[[U]]`. A current on a disconnected open set may have different constants on different components.

The proof reduces to scalar distributions. Fix a basis `b` of orientation `o`, so that
`[[Ω]] ω = ∫ x, ω x b ∂b.addHaar`. The scalar distribution `g ↦ T (g • det_b)` has vanishing
derivatives when `∂T = 0` (`TestFunction.map_postcompCLM_toSpanSingleton_lineDerivOp_eq_zero`), so
it is integration against a unique constant `c`
(`Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero`). Since every top-degree
test form is `g • det_b` for the scalar test `g = ω (·) b` (`Module.Basis.testTopFormEquiv`), this
says `T = c • [[Ω]]`.

## Main declarations

* `Orientation.existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero`: a top-degree
  current with zero boundary on a connected open set is a unique constant multiple of the
  integration current.
* `Orientation.comp_extDerivCLM_eq_zero_iff`: zero boundary characterizes these multiples.
* `Orientation.existsUnique_comp_monoCLM_eq_smul_integrationCurrent`: the local form, on connected
  open subsets of an arbitrary open set.
* `Orientation.existsUnique_eq_smul_integrationCurrent_of_finrank_eq_zero`: the degree-zero case.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (constancy theorem).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, Theorem 2.1.
-/

public section

namespace Orientation

open MeasureTheory TopologicalSpace TestFunction Module LineDeriv
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω U : Opens E} {m : ℕ}

/-- For a basis `b` of orientation `o`, a top-degree current `T` is `c • [[Ω]]` exactly when the
scalar distribution `g ↦ T (g • det_b)` is integration against `c` for the Haar measure of `b`. -/
private theorem eq_smul_integrationCurrent_iff (o : Orientation ℝ E (Fin m))
    (b : Basis (Fin m) ℝ E) (hb : b.orientation = o)
    (T : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) (c : ℝ) :
    T = c • o.integrationCurrent Ω ↔
      ContinuousLinearMap.toUniformConvergenceCLM _ ℝ _
          (T ∘L (b.testTopFormEquiv.symm : 𝓓(Ω, ℝ) ≃L[ℝ] _).toContinuousLinearMap) =
        Distribution.ofFun Ω (fun _ ↦ c) b.addHaar ⊤ := by
  have hI (ω : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ)) :
      o.integrationCurrent Ω ω = ∫ x, b.testTopFormEquiv ω x ∂b.addHaar := by
    simp [integrationCurrent_apply o Ω b hb]
  have hofFun (g : 𝓓(Ω, ℝ)) :
      Distribution.ofFun Ω (fun _ ↦ c) b.addHaar ⊤ g = (∫ x, g x ∂b.addHaar) * c := by
    simp [Distribution.ofFun_apply (locallyIntegrableOn_const c), integral_mul_const]
  constructor
  · rintro rfl
    ext g
    simp [hI, hofFun, mul_comm]
  · intro h
    ext ω
    simpa [hI, hofFun, mul_comm] using DFunLike.congr_fun h (b.testTopFormEquiv ω)

/-- A top-degree current on a connected open set whose scalar coefficient distribution in a basis
`b` of orientation `o` has vanishing derivatives is a unique constant multiple of `[[Ω]]`. -/
private theorem existsUnique_eq_smul_integrationCurrent_of_basis (o : Orientation ℝ E (Fin m))
    (b : Basis (Fin m) ℝ E) (hb : b.orientation = o) (hΩ : IsConnected (Ω : Set E))
    {T : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : ∀ (v : E) (g : 𝓓(Ω, ℝ)), T (b.testTopFormEquiv.symm (∂_{v} g)) = 0) :
    ∃! c : ℝ, T = c • o.integrationCurrent Ω := by
  refine (existsUnique_congr fun c ↦ eq_smul_integrationCurrent_iff o b hb T c).2 ?_
  refine Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero _ b.addHaar hΩ
    fun v ↦ ?_
  ext g
  simp [hT]

/-- **The constancy theorem.** On a connected open subset `Ω` of an oriented real vector space of
dimension `k + 1`, a top-degree current with zero boundary, `T ∘ d = 0`, is a unique real multiple
of the oriented integration current `[[Ω]]`. -/
theorem existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero {k : ℕ}
    (o : Orientation ℝ E (Fin (k + 1))) (hE : finrank ℝ E = k + 1)
    (hΩ : IsConnected (Ω : Set E)) {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hT : T ∘L extDerivCLM = 0) :
    ∃! c : ℝ, T = c • o.integrationCurrent Ω := by
  let b := (finBasisOfFinrankEq ℝ E hE).adjustToOrientation o
  refine existsUnique_eq_smul_integrationCurrent_of_basis o b
    ((finBasisOfFinrankEq ℝ E hE).orientation_adjustToOrientation o) hΩ fun v g ↦ ?_
  -- The scalar test `g` corresponds to the top-degree test form `g • det_b`.
  have hg : b.testTopFormEquiv.symm (∂_{v} g) =
      postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ b.continuousDet) (∂_{v} g) := by
    ext x w
    simp
  rw [hg]
  exact map_postcompCLM_toSpanSingleton_lineDerivOp_eq_zero hT hE.le _ v g

/-- On a connected open subset of an oriented real vector space of dimension `k + 1`, a top-degree
current has zero boundary if and only if it is a (necessarily unique) real multiple of the oriented
integration current. -/
theorem comp_extDerivCLM_eq_zero_iff {k : ℕ} (o : Orientation ℝ E (Fin (k + 1)))
    (hE : finrank ℝ E = k + 1) (hΩ : IsConnected (Ω : Set E))
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    T ∘L extDerivCLM = 0 ↔ ∃! c : ℝ, T = c • o.integrationCurrent Ω := by
  refine ⟨existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero o hE hΩ, ?_⟩
  rintro ⟨c, rfl, -⟩
  rw [ContinuousLinearMap.smul_comp, integrationCurrent_comp_extDerivCLM, smul_zero]

/-- **The local constancy theorem.** A top-degree current with zero boundary on an arbitrary open
subset `Ω` of an oriented real vector space of dimension `k + 1` restricts, on every connected open
subset `U ⊆ Ω`, to a unique real multiple of the integration current `[[U]]`. -/
theorem existsUnique_comp_monoCLM_eq_smul_integrationCurrent {k : ℕ}
    (o : Orientation ℝ E (Fin (k + 1))) (hE : finrank ℝ E = k + 1)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : T ∘L extDerivCLM = 0) (hU : U ≤ Ω)
    (hUc : IsConnected (U : Set E)) :
    ∃! c : ℝ, T ∘L (monoCLM ℝ : 𝓓(U, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] _) =
      c • o.integrationCurrent U := by
  refine existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero o hE hUc ?_
  ext ω
  simpa [extDerivCLM_monoCLM hU] using DFunLike.congr_fun hT (monoCLM ℝ ω)

/-- **The constancy theorem in degree zero.** On a zero-dimensional oriented real vector space
every `0`-current on a connected open set, which is then the whole point, is a unique real multiple
of the integration current, the signed Dirac current at the origin. No boundary condition enters:
the boundary of a `0`-current is zero. -/
theorem existsUnique_eq_smul_integrationCurrent_of_finrank_eq_zero (o : Orientation ℝ E (Fin 0))
    (hE : finrank ℝ E = 0) (hΩ : IsConnected (Ω : Set E))
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃! c : ℝ, T = c • o.integrationCurrent Ω := by
  have : Subsingleton E := finrank_zero_iff.1 hE
  let b : Basis (Fin 0) ℝ E := Basis.empty E
  -- Every direction is zero, so the derivative hypothesis holds trivially.
  have hpos :
      ∃! c : ℝ, T = c • (positiveOrientation : Orientation ℝ E (Fin 0)).integrationCurrent Ω :=
    existsUnique_eq_smul_integrationCurrent_of_basis _ b (Basis.orientation_isEmpty b) hΩ
      fun v g ↦ by simp [Subsingleton.elim v 0]
  rcases eq_or_eq_neg_of_isEmpty o with rfl | rfl
  · exact hpos
  · exact ((Equiv.neg ℝ).existsUnique_congr fun c ↦ by simp).1 hpos

end Orientation
