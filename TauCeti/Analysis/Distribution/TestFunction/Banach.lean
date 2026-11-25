/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Frechet
public import TauCeti.Analysis.Normed.Module.Multilinear.SecondCountable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import TauCeti.Analysis.Calculus.BumpFunction.DerivativeApproximation
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homothety
import TauCeti.Analysis.Distribution.TestFunction.Convergence

/-!
# The Banach space of `C^ℓ` functions supported in a fixed compact set

For a compact set `K` in a real normed space `E`, a real normed space `F` and a finite order
`ℓ : ℕ`, the topology of the space `𝓓^{ℓ}_{K}(E, F)` of `C^ℓ` maps `E → F` vanishing outside `K`
is given by the finitely many seminorms `N_j f = sup ‖D^j f‖`, `j ≤ ℓ`, since the seminorms of
order above `ℓ` vanish. It is therefore given by the single seminorm `max_{j ≤ ℓ} N_j`, which is a
norm because `N_0` is the sup norm. This file packages this norm on the type synonym
`TauCeti.NormedContDiffMapSupportedIn E F ℓ K`, whose uniform structure is, by construction,
that of `𝓓^{ℓ}_{K}(E, F)`; the identity is a continuous linear equivalence
`TauCeti.NormedContDiffMapSupportedIn.continuousLinearEquiv` between the two. The synonym keeps the
carrier and topology of `𝓓^{ℓ}_{K}(E, F)` and only adds the norm, so that Banach-space results
apply to it.

* **Completeness.** It is complete when `F` is, since `𝓓^{ℓ}_{K}(E, F)` is
  (`ContDiffMapSupportedIn.instCompleteSpace`): uniform limits of derivatives through order `ℓ`
  are the derivatives of the limit, and the support condition passes to the limit.
* **Separability.** When `F` is second countable, so is the space. If `E` is finite-dimensional,
  the jets `f ↦ (D^j f|_K)_{j ≤ ℓ}` embed it isometrically into the finite product of the spaces
  `C(K, E [×j]→L[ℝ] F)`, which are separable; otherwise `K` has empty interior and the space is
  trivial.
* **Smooth density.** When `K` is convex and `F` is complete, the smooth maps supported in `K` are
  dense. A map is first contracted towards an interior point `x₀` of `K`, by precomposing it with
  the homothety of ratio `t > 1` about `x₀`, which moves its support to a compact subset of the
  interior of `K`; it is then mollified by bumps smaller than the distance from that support to
  the complement of `K`. Transported along the identity equivalence, this says that for all
  orders `n₂ ≤ n₁`, finite or not, the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)` has
  dense range, with approximants supported in `K` itself and not merely in a neighbourhood of `K`.

These are the properties of a space of compactly supported finite-order perturbations, for
instance of Hamiltonians, used in genericity arguments by the Sard–Smale theorem: a separable
Banach space in which the smooth perturbations are dense.

## Main definitions

* `TauCeti.NormedContDiffMapSupportedIn E F ℓ K`: the space `𝓓^{ℓ}_{K}(E, F)` with the norm
  `max_{j ≤ ℓ} sup ‖D^j f‖`.
* `TauCeti.NormedContDiffMapSupportedIn.continuousLinearEquiv`: the identity, as a continuous
  linear equivalence with `𝓓^{ℓ}_{K}(E, F)`.
* `TauCeti.NormedContDiffMapSupportedIn.jet`: the jets `(D^j f|_K)_{j ≤ ℓ}`.
* `TauCeti.NormedContDiffMapSupportedIn.jetₗᵢ`: the jet map, as a linear isometry.

## Main results

* `TauCeti.NormedContDiffMapSupportedIn.norm_def`,
  `TauCeti.NormedContDiffMapSupportedIn.norm_le_iff`: the norm is `max_{j ≤ ℓ} N_j`.
* `TauCeti.NormedContDiffMapSupportedIn.isometry_jet`: the jet map is an isometry.
* `TauCeti.NormedContDiffMapSupportedIn.instCompleteSpace`: the space is complete.
* `TauCeti.NormedContDiffMapSupportedIn.instSecondCountableTopology`: the space is second
  countable, hence separable.
* `TauCeti.NormedContDiffMapSupportedIn.dense_setOf_contDiff`: the smooth maps are dense.
* `ContDiffMapSupportedIn.denseRange_monoCLM`: for convex `K`, a Banach space `F` and `n₂ ≤ n₁`,
  the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)` has dense range.

## References

* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967,
  Chapter 13 (the spaces `C^m_c(K)`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §1.3 (regularization by convolution).
-/
public section

noncomputable section

open Filter Function Metric Set TopologicalSpace
open scoped Topology Uniformity ContDiff BoundedContinuousFunction Distributions

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (ℓ : ℕ) (K : Compacts E)

/-- The space `𝓓^{ℓ}_{K}(E, F)` of `C^ℓ` maps `E → F` vanishing outside the compact set `K`, for a
finite order `ℓ`, with the norm `‖f‖ = max_{j ≤ ℓ} sup ‖D^j f‖`. Its uniform structure is the one
of `𝓓^{ℓ}_{K}(E, F)`, and it is a Banach space when `F` is complete. -/
@[expose] def NormedContDiffMapSupportedIn : Type _ :=
  𝓓^{ℓ}_{K}(E, F)

namespace NormedContDiffMapSupportedIn

instance : AddCommGroup (NormedContDiffMapSupportedIn E F ℓ K) :=
  inferInstanceAs (AddCommGroup 𝓓^{ℓ}_{K}(E, F))

instance {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R (NormedContDiffMapSupportedIn E F ℓ K) :=
  inferInstanceAs (Module R 𝓓^{ℓ}_{K}(E, F))

instance : FunLike (NormedContDiffMapSupportedIn E F ℓ K) E F :=
  inferInstanceAs (FunLike 𝓓^{ℓ}_{K}(E, F) E F)

instance : ContDiffMapSupportedInClass (NormedContDiffMapSupportedIn E F ℓ K) E F ℓ K :=
  inferInstanceAs (ContDiffMapSupportedInClass 𝓓^{ℓ}_{K}(E, F) E F ℓ K)

variable {E F ℓ K}

/-- The underlying map of `f` in `𝓓^{ℓ}_{K}(E, F)`. -/
def toContDiffMapSupportedIn (f : NormedContDiffMapSupportedIn E F ℓ K) :
    𝓓^{ℓ}_{K}(E, F) :=
  f

/-- A map of `𝓓^{ℓ}_{K}(E, F)`, regarded in the normed space. -/
def ofContDiffMapSupportedIn (f : 𝓓^{ℓ}_{K}(E, F)) :
    NormedContDiffMapSupportedIn E F ℓ K :=
  f

@[simp]
theorem coe_toContDiffMapSupportedIn (f : NormedContDiffMapSupportedIn E F ℓ K) :
    ⇑(toContDiffMapSupportedIn f) = f :=
  (rfl)

@[simp]
theorem coe_ofContDiffMapSupportedIn (f : 𝓓^{ℓ}_{K}(E, F)) :
    ⇑(ofContDiffMapSupportedIn f) = f :=
  (rfl)

@[simp]
theorem toContDiffMapSupportedIn_ofContDiffMapSupportedIn (f : 𝓓^{ℓ}_{K}(E, F)) :
    toContDiffMapSupportedIn (ofContDiffMapSupportedIn f) = f :=
  (rfl)

@[simp]
theorem ofContDiffMapSupportedIn_toContDiffMapSupportedIn
    (f : NormedContDiffMapSupportedIn E F ℓ K) :
    ofContDiffMapSupportedIn (toContDiffMapSupportedIn f) = f :=
  (rfl)

@[ext]
theorem ext {f g : NormedContDiffMapSupportedIn E F ℓ K} (h : ∀ x, f x = g x) : f = g :=
  ContDiffMapSupportedIn.ext (f := toContDiffMapSupportedIn f) h

@[simp]
theorem coe_zero : ⇑(0 : NormedContDiffMapSupportedIn E F ℓ K) = 0 :=
  rfl

@[simp]
theorem coe_add (f g : NormedContDiffMapSupportedIn E F ℓ K) : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp]
theorem coe_neg (f : NormedContDiffMapSupportedIn E F ℓ K) : ⇑(-f) = -⇑f :=
  rfl

@[simp]
theorem coe_sub (f g : NormedContDiffMapSupportedIn E F ℓ K) : ⇑(f - g) = ⇑f - ⇑g :=
  rfl

@[simp]
theorem coe_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (f : NormedContDiffMapSupportedIn E F ℓ K) :
    ⇑(c • f) = c • ⇑f :=
  rfl

@[simp]
theorem toContDiffMapSupportedIn_add (f g : NormedContDiffMapSupportedIn E F ℓ K) :
    toContDiffMapSupportedIn (f + g) = toContDiffMapSupportedIn f + toContDiffMapSupportedIn g :=
  (rfl)

@[simp]
theorem toContDiffMapSupportedIn_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (f : NormedContDiffMapSupportedIn E F ℓ K) :
    toContDiffMapSupportedIn (c • f) = c • toContDiffMapSupportedIn f :=
  (rfl)

@[simp]
theorem toContDiffMapSupportedIn_zero :
    toContDiffMapSupportedIn (0 : NormedContDiffMapSupportedIn E F ℓ K) = 0 :=
  (rfl)

@[simp]
theorem toContDiffMapSupportedIn_neg (f : NormedContDiffMapSupportedIn E F ℓ K) :
    toContDiffMapSupportedIn (-f) = -toContDiffMapSupportedIn f :=
  (rfl)

@[simp]
theorem toContDiffMapSupportedIn_sub (f g : NormedContDiffMapSupportedIn E F ℓ K) :
    toContDiffMapSupportedIn (f - g) = toContDiffMapSupportedIn f - toContDiffMapSupportedIn g :=
  (rfl)

@[simp]
theorem ofContDiffMapSupportedIn_zero :
    ofContDiffMapSupportedIn (0 : 𝓓^{ℓ}_{K}(E, F)) = 0 :=
  (rfl)

@[simp]
theorem ofContDiffMapSupportedIn_add (f g : 𝓓^{ℓ}_{K}(E, F)) :
    ofContDiffMapSupportedIn (f + g) = ofContDiffMapSupportedIn f + ofContDiffMapSupportedIn g :=
  (rfl)

@[simp]
theorem ofContDiffMapSupportedIn_neg (f : 𝓓^{ℓ}_{K}(E, F)) :
    ofContDiffMapSupportedIn (-f) = -ofContDiffMapSupportedIn f :=
  (rfl)

@[simp]
theorem ofContDiffMapSupportedIn_sub (f g : 𝓓^{ℓ}_{K}(E, F)) :
    ofContDiffMapSupportedIn (f - g) = ofContDiffMapSupportedIn f - ofContDiffMapSupportedIn g :=
  (rfl)

@[simp]
theorem ofContDiffMapSupportedIn_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (f : 𝓓^{ℓ}_{K}(E, F)) :
    ofContDiffMapSupportedIn (c • f) = c • ofContDiffMapSupportedIn f :=
  (rfl)

/-- Every map of the normed space is `C^ℓ`. -/
protected theorem contDiff (f : NormedContDiffMapSupportedIn E F ℓ K) : ContDiff ℝ ℓ f :=
  ContDiffMapSupportedInClass.map_contDiff f

/-- Every map of the normed space vanishes outside `K`. -/
protected theorem zero_on_compl (f : NormedContDiffMapSupportedIn E F ℓ K) :
    EqOn f 0 (K : Set E)ᶜ :=
  ContDiffMapSupportedInClass.map_zero_on_compl f

/-- Every map of the normed space has compact support. -/
protected theorem hasCompactSupport (f : NormedContDiffMapSupportedIn E F ℓ K) :
    HasCompactSupport f :=
  (toContDiffMapSupportedIn f).hasCompactSupport

/-- If `E` is infinite-dimensional, the compact set `K` has empty interior and every continuous map
vanishing outside `K` is zero. -/
theorem eq_zero_of_not_finiteDimensional (hE : ¬FiniteDimensional ℝ E)
    (f : NormedContDiffMapSupportedIn E F ℓ K) : f = 0 :=
  ext <| congrFun <| (f.hasCompactSupport.eq_zero_or_finiteDimensional ℝ
    f.contDiff.continuous).resolve_right hE

instance normedAddCommGroup : NormedAddCommGroup (NormedContDiffMapSupportedIn E F ℓ K) :=
  let p : Seminorm ℝ (NormedContDiffMapSupportedIn E F ℓ K) :=
    ContDiffMapSupportedIn.supSeminorm ℝ E F ℓ K ℓ
  let _ : Norm (NormedContDiffMapSupportedIn E F ℓ K) := ⟨p⟩
  NormedAddCommGroup.ofCoreReplaceUniformity (𝕜 := ℝ)
    (U := inferInstanceAs (UniformSpace 𝓓^{ℓ}_{K}(E, F)))
    { norm_nonneg f := apply_nonneg p f
      norm_smul c f := map_smul_eq_mul p c f
      norm_triangle f g := map_add_le_add p f g
      norm_eq_zero_iff := ContDiffMapSupportedIn.supSeminorm_eq_zero_iff (𝕜 := ℝ) ℓ }
    (by
      -- The uniform structure `U` of the synonym is, by definition, the one of `𝓓^{ℓ}_{K}(E, F)`.
      change 𝓤[(ContDiffMapSupportedIn.uniformSpace : UniformSpace 𝓓^{ℓ}_{K}(E, F))] = _
      rw [ContDiffMapSupportedIn.uniformSpace_eq_supSeminorm_self]
      -- Both sides are now the uniformity of the pseudometric `dist f g = p (-f + g)`:
      -- `AddGroupSeminorm.toSeminormedAddGroup`, behind `Seminorm.toSeminormedAddCommGroup`, and
      -- `PseudoMetricSpace.ofSeminormedSpaceCore` both define the distance this way, and the norm
      -- given to the core is `p` itself.
      rfl)

/-- The norm of `f` is `max_{j ≤ ℓ} N_j f`, the largest sup norm of a derivative of order at
most `ℓ`. -/
theorem norm_def (f : NormedContDiffMapSupportedIn E F ℓ K) :
    ‖f‖ = ContDiffMapSupportedIn.supSeminorm ℝ E F ℓ K ℓ (toContDiffMapSupportedIn f) :=
  (rfl)

variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

instance : NormedSpace 𝕜 (NormedContDiffMapSupportedIn E F ℓ K) :=
  { (inferInstance : Module 𝕜 (NormedContDiffMapSupportedIn E F ℓ K)) with
    norm_smul_le c f := by
      simp only [norm_def, toContDiffMapSupportedIn_smul,
        ← ContDiffMapSupportedIn.supSeminorm_apply_eq_of_scalars (𝕜 := 𝕜)]
      exact (map_smul_eq_mul (ContDiffMapSupportedIn.supSeminorm 𝕜 E F ℓ K ℓ) c
        (toContDiffMapSupportedIn f)).le }

variable (𝕜 E F ℓ K) in
/-- The identity, as a continuous linear equivalence between the normed space and
`𝓓^{ℓ}_{K}(E, F)`. -/
def continuousLinearEquiv : NormedContDiffMapSupportedIn E F ℓ K ≃L[𝕜] 𝓓^{ℓ}_{K}(E, F) where
  toFun := toContDiffMapSupportedIn
  invFun := ofContDiffMapSupportedIn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem continuousLinearEquiv_apply (f : NormedContDiffMapSupportedIn E F ℓ K) :
    continuousLinearEquiv 𝕜 E F ℓ K f = toContDiffMapSupportedIn f :=
  (rfl)

@[simp]
theorem continuousLinearEquiv_symm_apply (f : 𝓓^{ℓ}_{K}(E, F)) :
    (continuousLinearEquiv 𝕜 E F ℓ K).symm f = ofContDiffMapSupportedIn f :=
  (rfl)

/-- **Completeness.** The `C^ℓ` maps supported in `K` with values in a Banach space form a Banach
space. -/
instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (NormedContDiffMapSupportedIn E F ℓ K) :=
  inferInstanceAs (CompleteSpace 𝓓^{ℓ}_{K}(E, F))

/-- The sup norm of the `j`-th derivative of `f`, for `j ≤ ℓ`, is at most the norm of `f`. -/
theorem norm_iteratedFDeriv_le_norm (f : NormedContDiffMapSupportedIn E F ℓ K) {j : ℕ}
    (hj : j ≤ ℓ) (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ ‖f‖ :=
  (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ
    (f := toContDiffMapSupportedIn f) (by exact_mod_cast hj)).trans
    (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hj))

/-- The norm of `f` is at most `C ≥ 0` exactly when every derivative of `f` of order at most `ℓ`
is bounded by `C` on `K`. -/
theorem norm_le_iff (f : NormedContDiffMapSupportedIn E F ℓ K) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ j ≤ ℓ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C :=
  ⟨fun h _ hj x _ ↦ (norm_iteratedFDeriv_le_norm f hj x).trans h, fun h ↦
    Seminorm.finset_sup_apply_le hC fun j hj ↦
      (ContDiffMapSupportedIn.seminorm_le_iff ℝ hC j _).2 fun _ ↦ h j (Finset.mem_Iic.1 hj)⟩

section Jet

/-- The jets of `f` on `K`: the restrictions to `K` of the derivatives `D^j f` of order `j ≤ ℓ`.
-/
def jet (f : NormedContDiffMapSupportedIn E F ℓ K) :
    (j : Fin (ℓ + 1)) → C(K, E [×j]→L[ℝ] F) := fun j ↦
  ⟨fun x ↦ iteratedFDeriv ℝ j f x,
    ((f.contDiff.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.1 j.isLt)).comp
      continuous_subtypeVal)⟩

@[simp]
theorem jet_apply (f : NormedContDiffMapSupportedIn E F ℓ K) (j : Fin (ℓ + 1)) (x : K) :
    jet f j x = iteratedFDeriv ℝ j f x :=
  (rfl)

/-- The jet map is additive. -/
@[simp]
theorem jet_add (f g : NormedContDiffMapSupportedIn E F ℓ K) : jet (f + g) = jet f + jet g := by
  funext j
  ext x : 1
  have hj : (j : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  simp only [jet_apply, Pi.add_apply, ContinuousMap.add_apply]
  exact iteratedFDeriv_add_apply (f.contDiff.contDiffAt.of_le hj)
    (g.contDiff.contDiffAt.of_le hj)

/-- The jets of the zero map vanish. -/
@[simp]
theorem jet_zero : jet (0 : NormedContDiffMapSupportedIn E F ℓ K) = 0 := by
  funext j
  ext x : 1
  simp

/-- The jet map commutes with scalar multiplication. -/
@[simp]
theorem jet_smul (c : 𝕜) (f : NormedContDiffMapSupportedIn E F ℓ K) :
    jet (c • f) = c • jet f := by
  funext j
  ext x : 1
  have hj : (j : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  simp only [jet_apply, coe_smul, Pi.smul_apply, ContinuousMap.smul_apply]
  exact iteratedFDeriv_const_smul_apply (f.contDiff.contDiffAt.of_le hj)

/-- The jet map commutes with negation. -/
@[simp]
theorem jet_neg (f : NormedContDiffMapSupportedIn E F ℓ K) : jet (-f) = -jet f := by
  rw [eq_neg_iff_add_eq_zero, ← jet_add, neg_add_cancel, jet_zero]

/-- The jet map is subtractive. -/
@[simp]
theorem jet_sub (f g : NormedContDiffMapSupportedIn E F ℓ K) : jet (f - g) = jet f - jet g := by
  rw [sub_eq_add_neg, jet_add, jet_neg, ← sub_eq_add_neg]

/-- The norm of `f` is the sup norm of its jets on `K`. -/
theorem norm_jet (f : NormedContDiffMapSupportedIn E F ℓ K) : ‖jet f‖ = ‖f‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ ?_) ?_
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦
      norm_iteratedFDeriv_le_norm f (Nat.lt_succ_iff.1 j.isLt) x
  · refine (norm_le_iff f (norm_nonneg _)).2 fun j hj x hx ↦ ?_
    calc ‖iteratedFDeriv ℝ j f x‖ = ‖jet f ⟨j, Nat.lt_succ_of_le hj⟩ ⟨x, hx⟩‖ := by
          rw [jet_apply]
      _ ≤ ‖jet f ⟨j, Nat.lt_succ_of_le hj⟩‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖jet f‖ := norm_le_pi_norm (jet f) _

variable (𝕜 E F ℓ K) in
/-- The jet map `f ↦ (D^j f|_K)_{j ≤ ℓ}`, as a linear isometry. -/
def jetₗᵢ :
    NormedContDiffMapSupportedIn E F ℓ K →ₗᵢ[𝕜] (j : Fin (ℓ + 1)) → C(K, E [×j]→L[ℝ] F) where
  toFun := jet
  map_add' := jet_add
  map_smul' := jet_smul
  norm_map' := norm_jet

@[simp]
theorem coe_jetₗᵢ : ⇑(jetₗᵢ 𝕜 E F ℓ K) = jet :=
  (rfl)

/-- The jet map is an isometry. -/
theorem isometry_jet : Isometry (jet : NormedContDiffMapSupportedIn E F ℓ K → _) :=
  (jetₗᵢ ℝ E F ℓ K).isometry

/-- **Separability.** When `F` is second countable, the `C^ℓ` maps supported in `K` form a second
countable, hence separable, space. If `E` is finite-dimensional, their jets embed them
isometrically into a finite product of separable spaces of continuous maps on the compact set `K`;
otherwise the space is trivial. -/
instance instSecondCountableTopology [SecondCountableTopology F] :
    SecondCountableTopology (NormedContDiffMapSupportedIn E F ℓ K) := by
  by_cases hE : FiniteDimensional ℝ E
  · exact isometry_jet.isEmbedding.secondCountableTopology
  · have : Subsingleton (NormedContDiffMapSupportedIn E F ℓ K) := ⟨fun f g ↦ by
      rw [eq_zero_of_not_finiteDimensional hE f, eq_zero_of_not_finiteDimensional hE g]⟩
    infer_instance

end Jet

section Density

/-- **Mollification.** A `C^ℓ` map `g` supported in `K` whose support lies in the interior of `K`
is a limit of smooth maps supported in `K`: by
`ContDiff.exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv`, it has smooth
approximants supported in the interior of `K` whose derivatives of order at most `ℓ` converge
uniformly. -/
private theorem mem_closure_setOf_contDiff_of_tsupport_subset [FiniteDimensional ℝ E]
    [CompleteSpace F] (g : NormedContDiffMapSupportedIn E F ℓ K)
    (hg : tsupport g ⊆ interior (K : Set E)) :
    g ∈ closure {f : NormedContDiffMapSupportedIn E F ℓ K | ContDiff ℝ ∞ f} := by
  obtain ⟨m, L, -, hLK, hm, hconv⟩ :=
    g.contDiff.exists_contDiff_hasCompactSupport_tendstoUniformly_iteratedFDeriv
      g.hasCompactSupport isOpen_interior hg
  let M : ℕ → NormedContDiffMapSupportedIn E F ℓ K := fun n ↦
    ofContDiffMapSupportedIn (.of_support_subset ((hm n).1.of_le (by exact_mod_cast le_top))
      ((subset_tsupport _).trans ((hm n).2.trans (hLK.trans interior_subset))))
  have hMm (n : ℕ) : ⇑(M n) = m n := funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := ((eventually_all_finset (Finset.range (ℓ + 1))).2 fun k hk ↦
    Metric.tendstoUniformly_iff.1
      (hconv k (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) _
      (half_pos hε)).exists
  refine ⟨M n, by rw [mem_ofPred_eq, hMm]; exact (hm n).1, ?_⟩
  rw [dist_eq_norm]
  refine ((norm_le_iff _ (half_pos hε).le).2 fun j hj x _ ↦ ?_).trans_lt (half_lt_self hε)
  have hj' : (j : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hj
  rw [coe_sub, iteratedFDeriv_sub_apply (g.contDiff.contDiffAt.of_le hj')
    ((M n).contDiff.contDiffAt.of_le hj'), ← dist_eq_norm, hMm]
  exact (hn j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) x).le

/-- **Contraction.** If `K` is convex and `x₀` is an interior point of `K`, every `C^ℓ` map `f`
supported in `K` is a limit of `C^ℓ` maps supported in `K` whose supports lie in the interior of
`K`: the maps `f ∘ homothety x₀ t` for `t > 1`, which tend to `f`
as `t → 1`. Their supports lie in the image of `K` under the homothety of ratio `t⁻¹` about `x₀`,
a compact subset of the interior of `K`. -/
private theorem mem_closure_setOf_tsupport_subset (hK : Convex ℝ (K : Set E)) {x₀ : E}
    (hx₀ : x₀ ∈ interior (K : Set E)) (f : NormedContDiffMapSupportedIn E F ℓ K) :
    f ∈ closure {g : NormedContDiffMapSupportedIn E F ℓ K |
      tsupport g ⊆ interior (K : Set E)} := by
  -- The homothety `h t` of ratio `max 1 t` about `x₀`, and the inverse formula for it.
  set h : ℝ → E → E := fun t ↦ AffineMap.homothety x₀ (max 1 t) with hh
  have hh' (t : ℝ) : h t = fun x ↦ max 1 t • (x - x₀) + x₀ :=
    funext fun x ↦ by simp [hh, AffineMap.homothety_apply]
  have hcont : Continuous fun p : ℝ × E ↦ h p.1 p.2 := by simp only [hh']; fun_prop
  have hinv (t : ℝ) (x : E) : x = x₀ + (max 1 t)⁻¹ • (h t x - x₀) := by
    simp [hh, AffineMap.homothety_apply, smul_smul,
      inv_mul_cancel₀ (zero_lt_one.trans_le (le_max_left 1 t)).ne']
  have hmem {t : ℝ} {x : E} (hx : f (h t x) ≠ 0) : h t x ∈ (K : Set E) :=
    not_not.1 fun hK' ↦ hx (f.zero_on_compl hK')
  have hgK (t : ℝ) : support (f ∘ h t) ⊆ K := fun x hx ↦ by
    rw [hinv t x]
    exact hK.add_smul_sub_mem (interior_subset hx₀) (hmem hx)
      ⟨inv_nonneg.2 (zero_le_one.trans (le_max_left 1 t)), inv_le_one_of_one_le₀ (le_max_left 1 t)⟩
  have hgcd (t : ℝ) : ContDiff ℝ ℓ (f ∘ h t) :=
    f.contDiff.comp (by rw [hh']; fun_prop)
  have hGg (t : ℝ) : ⇑(ContDiffMapSupportedIn.of_support_subset (hgcd t) (hgK t)) = f ∘ h t :=
    funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
  let G : ℝ → NormedContDiffMapSupportedIn E F ℓ K := fun t ↦
    ofContDiffMapSupportedIn (.of_support_subset (hgcd t) (hgK t))
  have hG : Continuous G := by
    refine (continuousLinearEquiv ℝ E F ℓ K).symm.continuous.comp
      (ContDiffMapSupportedIn.continuous_of_continuous_iteratedFDeriv
        (φ := fun t ↦ .of_support_subset (hgcd t) (hgK t)) fun k hk ↦ ?_)
    have hk' : (k : WithTop ℕ∞) ≤ ℓ := by exact_mod_cast hk
    simp only [hGg, hh, iteratedFDeriv_comp_homothety (f.contDiff.of_le hk')]
    exact ((continuous_const.max continuous_fst).pow k).smul
      ((f.contDiff.continuous_iteratedFDeriv hk').comp hcont)
  have hG1 : G 1 = f := ext fun x ↦ by simp [G, hh, AffineMap.homothety_one]
  -- For `t > 1` the support of `G t` is a compact subset of the interior of `K`.
  have hsub {t : ℝ} (ht : 1 < t) : tsupport (G t) ⊆ interior (K : Set E) := by
    refine (closure_minimal (fun x hx ↦ hmem (by simpa [G, hGg] using hx))
      (K.isCompact.isClosed.preimage (hcont.comp (Continuous.prodMk_right t)))).trans
        fun x (hx : h t x ∈ (K : Set E)) ↦ ?_
    have hx' : AffineMap.homothety x₀ t x ∈ closure (K : Set E) := by
      simpa [hh, max_eq_right ht.le, K.isCompact.isClosed.closure_eq] using hx
    obtain ⟨y, hy, hyx⟩ := hK.closure_subset_image_homothety_interior_of_one_lt hx₀ t ht hx'
    rwa [← AffineMap.homothety_injective x₀ (zero_lt_one.trans ht).ne' hyx]
  exact hG1 ▸ mem_closure_of_tendsto ((hG.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1)))
    (eventually_nhdsWithin_of_forall fun t ht ↦ hsub ht)

/-- **Smooth density.** If `K` is convex, the smooth maps supported in `K` are dense among the
`C^ℓ` maps supported in `K`. -/
theorem dense_setOf_contDiff [CompleteSpace F] (hK : Convex ℝ (K : Set E)) :
    Dense {f : NormedContDiffMapSupportedIn E F ℓ K | ContDiff ℝ ∞ f} := by
  intro f
  have hzero (h0 : (f : E → F) = 0) :
      f ∈ closure {f : NormedContDiffMapSupportedIn E F ℓ K | ContDiff ℝ ∞ f} :=
    subset_closure (by rw [mem_ofPred_eq, h0]; exact contDiff_const)
  -- A nonzero map with compact support forces `E` to be finite-dimensional, and if `K` has empty
  -- interior every map vanishing outside `K` is zero.
  rcases f.hasCompactSupport.eq_zero_or_finiteDimensional ℝ f.contDiff.continuous with h0 | hE
  · exact hzero h0
  by_cases hint : (interior (K : Set E)).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hint
    exact closure_minimal (fun g hg ↦ mem_closure_setOf_contDiff_of_tsupport_subset g hg)
      isClosed_closure (mem_closure_setOf_tsupport_subset hK hx₀ f)
  · exact hzero <| f.contDiff.continuous.ext_on
      (interior_eq_empty_iff_dense_compl.1 (not_nonempty_iff_eq_empty.1 hint)) continuous_const
      fun x hx ↦ f.zero_on_compl hx

end Density

end NormedContDiffMapSupportedIn

end TauCeti

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {K : Compacts E}

/-- **Smooth functions supported in a convex compact set are dense.** For convex `K`, a Banach
space `F` (`[CompleteSpace F]`) and `n₂ ≤ n₁`, the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)`
has dense range. For `n₁ = ∞` this says that every `C^{n₂}` function supported in `K` is a limit,
in every derivative of order at most `n₂` uniformly, of smooth functions supported in `K`. -/
theorem denseRange_monoCLM [CompleteSpace F] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {n₁ n₂ : ℕ∞} (hn : n₂ ≤ n₁)
    (hK : Convex ℝ (K : Set E)) :
    DenseRange (monoCLM 𝕜 : 𝓓^{n₁}_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F)) := by
  -- Every smooth function supported in `K` lies in the range of the inclusion.
  have hrange {g : 𝓓^{n₂}_{K}(E, F)} (hg : ContDiff ℝ ∞ g) :
      g ∈ range (monoCLM 𝕜 : 𝓓^{n₁}_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F)) :=
    ⟨.of_support_subset (hg.of_le (by exact_mod_cast le_top)) g.support_subset,
      ext fun x ↦ by simp [hn]⟩
  induction n₂ using ENat.recTopCoe with
  -- For `n₂ = ∞` every element is already smooth, so it lies in the range.
  | top => exact fun g ↦ subset_closure (hrange g.contDiff)
  -- For finite `n₂ = ℓ`, transport the density of smooth maps in the norm synonym along the
  -- identity `continuousLinearEquiv`.
  | coe ℓ =>
    exact ((TauCeti.NormedContDiffMapSupportedIn.continuousLinearEquiv ℝ E F ℓ
      K).surjective.denseRange.dense_image (ContinuousLinearEquiv.continuous _)
        (TauCeti.NormedContDiffMapSupportedIn.dense_setOf_contDiff hK)).mono
      (by rintro _ ⟨g, hg, rfl⟩; exact hrange (by simpa using hg))

end ContDiffMapSupportedIn
