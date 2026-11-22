/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Variational.BoundedSublevels
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Topology.Semicontinuity.Sequences
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm
import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.Sphere
import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
import TauCeti.Analysis.Variational.MinimizingSequence

/-!
# Compact form pairs and their constrained minima

A **compact form pair** (`TauCeti.CompactFormPair 𝕜 V H`) is the abstract setting of a
variational eigenvalue problem over `𝕜 = ℝ` or `ℂ`. It consists of

* a continuous linear map `j : V → H` between inner-product spaces, the inclusion of a form
  domain `V` into a space `H`, which is injective, compact and of dense range (it need not be a
  topological embedding);
* a bounded Hermitian sesquilinear form `a` on `V`, conjugate linear in its first argument,
  whose **energy** `q(u) = re a(u, u)` satisfies a shifted coercivity bound
  `c ‖u‖² ≤ q(u) + ω ‖j u‖²` for some `c > 0` and some real `ω`, possibly negative.

The constants `c` and `ω` are not part of the data: the bound is an existential field, so a pair
is determined by `j` and `a` (`TauCeti.CompactFormPair.ext`). For the Dirichlet form of the
Laplacian on a bounded open set, `V = H¹₀`, `H = L²`, `j` is the inclusion, `a(u, v) = ⟪∇u, ∇v⟫`,
`c = 1` and `ω = 1`.

For a submodule `W` of `H`, the **constrained sphere** `S_W = {u | j u ∈ W, ‖j u‖ = 1}`
(`TauCeti.CompactFormPair.unitConstraint`) is the admissible set of the Rayleigh minimization
behind the eigenvalues of the pair: its first eigenvalue is the minimum of `q` on `S_H`, and the
later ones are minima on the spheres of orthogonal complements of the eigenvectors already found.
This file proves that these minima exist when `V` is complete and `W` is closed
(`TauCeti.CompactFormPair.exists_isMinOn_energy_unitConstraint`). The sphere is not weakly
closed in general (`TauCeti.CompactFormPair.not_isClosed_toWeakSpace_unitConstraint_top`), so the
proof runs the sequential direct method in the reflexive space `V`:

* compactness of `j` makes `S_W` sequentially weakly closed when `W` is closed;
* the shifted coercivity bound gives `c ‖u‖² ≤ q(u) + ω` on `S_W`, so the energy has bounded
  sublevels there and is bounded below by `-ω`;
* on `S_W` the energy differs by the constant `ω` from the nonnegative Hermitian form
  `q + ω ‖j ·‖²`, which is weakly lower semicontinuous.

Minimizers also minimize the Rayleigh quotient `q(u) / ‖j u‖²` over the `u ≠ 0` with `j u ∈ W`
(`TauCeti.CompactFormPair.mul_norm_sq_le_energy_of_isMinOn`).

## References

* V. Ivrii, *Partial Differential Equations*, Chapter 13, §13.1, Theorem 4 and its proof.
* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4, §4.8 and §4.10.
-/

public section

open Bornology Filter Metric RCLike Set

namespace TauCeti

variable (𝕜 V H : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A **compact form pair**: an injective compact continuous linear map `j : V → H` of dense
range, the inclusion of a form domain, together with a bounded Hermitian sesquilinear form `a`
on `V`, conjugate linear in its first argument, satisfying the shifted coercivity bound
`c ‖u‖² ≤ re a(u, u) + ω ‖j u‖²` for some `c > 0` and some real `ω`. -/
@[ext]
structure CompactFormPair where
  /-- The form-domain inclusion `j : V → H`. -/
  inclusion : V →L[𝕜] H
  /-- The inclusion is injective. -/
  injective : Function.Injective inclusion
  /-- The inclusion has dense range. -/
  denseRange : DenseRange inclusion
  /-- The inclusion is a compact operator. -/
  isCompactOperator : IsCompactOperator inclusion
  /-- The bounded sesquilinear form `a`, conjugate linear in its first argument. -/
  form : V →L⋆[𝕜] V →L[𝕜] 𝕜
  /-- The form is Hermitian. -/
  hermitian : ∀ u v, form u v = star (form v u)
  /-- The shifted coercivity bound, for some constant `c > 0` and some shift `ω`. -/
  exists_shifted_coercive :
    ∃ c > 0, ∃ ω : ℝ, ∀ u, c * ‖u‖ ^ 2 ≤ re (form u u) + ω * ‖inclusion u‖ ^ 2

namespace CompactFormPair

variable {𝕜 V H} (P : CompactFormPair 𝕜 V H)

/-! ### The energy -/

/-- The energy `q(u) = re a(u, u)` of a compact form pair. -/
def energy (u : V) : ℝ :=
  re (P.form u u)

theorem energy_def (u : V) : P.energy u = re (P.form u u) :=
  (rfl)

/-- The shifted coercivity bound of a compact form pair, stated with its energy. -/
theorem exists_mul_norm_sq_le_energy_add :
    ∃ c > 0, ∃ ω : ℝ, ∀ u, c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2 :=
  P.exists_shifted_coercive

@[simp]
theorem energy_zero : P.energy 0 = 0 := by
  simp [energy_def]

/-- The energy is homogeneous of degree two: `q(t • u) = ‖t‖² q(u)`. -/
@[simp]
theorem energy_smul (t : 𝕜) (u : V) : P.energy (t • u) = ‖t‖ ^ 2 * P.energy u := by
  simp only [energy_def, map_smulₛₗ, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    RingHom.id_apply, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

@[simp]
theorem energy_neg (u : V) : P.energy (-u) = P.energy u := by
  simpa using P.energy_smul (-1) u

theorem continuous_energy : Continuous P.energy :=
  continuous_re.comp (P.form.continuous.clm_apply continuous_id)

/-! ### Constrained spheres -/

/-- The constrained sphere `S_W = {u | j u ∈ W, ‖j u‖ = 1}` of a submodule `W` of `H`: the
admissible set of the Rayleigh minimization in `W`. -/
def unitConstraint (W : Submodule 𝕜 H) : Set V :=
  {u | P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1}

variable {P} {W W' : Submodule 𝕜 H} {u : V}

@[simp]
theorem mem_unitConstraint : u ∈ P.unitConstraint W ↔ P.inclusion u ∈ W ∧ ‖P.inclusion u‖ = 1 :=
  Iff.rfl

variable (P W) in
theorem unitConstraint_eq_preimage :
    P.unitConstraint W = P.inclusion ⁻¹' ((W : Set H) ∩ sphere 0 1) := by
  ext u
  simp

theorem unitConstraint_mono (h : W ≤ W') : P.unitConstraint W ⊆ P.unitConstraint W' :=
  fun _ hu ↦ ⟨h hu.1, hu.2⟩

/-- A constrained sphere is invariant under multiplication by scalars of norm one, and so is the
energy (`TauCeti.CompactFormPair.energy_smul`). -/
theorem smul_mem_unitConstraint (hu : u ∈ P.unitConstraint W) {t : 𝕜} (ht : ‖t‖ = 1) :
    t • u ∈ P.unitConstraint W := by
  rw [mem_unitConstraint, map_smul, norm_smul, ht, one_mul]
  exact ⟨W.smul_mem t hu.1, hu.2⟩

/-- Normalizing a vector with nonzero image in `W` puts it on the constrained sphere `S_W`. -/
theorem inv_norm_smul_mem_unitConstraint (hu : P.inclusion u ∈ W) (hu0 : P.inclusion u ≠ 0) :
    ((‖P.inclusion u‖⁻¹ : ℝ) : 𝕜) • u ∈ P.unitConstraint W := by
  refine ⟨by simpa using W.smul_mem _ hu, ?_⟩
  rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hu0)]

/-- The constrained sphere `S_W` is nonempty exactly when some form-domain vector has a nonzero
image in `W`. A nonzero `W` does not suffice, since `W` may meet the range of `j` only in `0`. -/
theorem unitConstraint_nonempty_iff :
    (P.unitConstraint W).Nonempty ↔ ∃ u, P.inclusion u ∈ W ∧ P.inclusion u ≠ 0 := by
  constructor
  · rintro ⟨u, hu, hnorm⟩
    exact ⟨u, hu, fun h ↦ by simp [h] at hnorm⟩
  · rintro ⟨u, hu, hu0⟩
    exact ⟨_, inv_norm_smul_mem_unitConstraint hu hu0⟩

/-- The unconstrained sphere `S_H` is nonempty exactly when `H` is nontrivial, by density of the
range of the inclusion. -/
theorem unitConstraint_top_nonempty_iff : (P.unitConstraint ⊤).Nonempty ↔ Nontrivial H := by
  rw [unitConstraint_nonempty_iff]
  constructor
  · rintro ⟨u, -, hu⟩
    exact ⟨⟨_, _, hu⟩⟩
  · intro hH
    by_contra! h
    have hrange : range P.inclusion ⊆ {0} := by
      rintro _ ⟨u, rfl⟩
      exact h u Submodule.mem_top
    have huniv : (univ : Set H) ⊆ {0} := by
      rw [← P.denseRange.closure_range]
      exact closure_minimal hrange isClosed_singleton
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact hx (huniv (mem_univ x))

/-! ### Bounds on constrained spheres -/

/-- On a constrained sphere the energy is bounded below by `-ω`, for any shift `ω` in a
shifted coercivity bound with constant `c ≥ 0`. -/
theorem neg_le_energy_of_mem_unitConstraint {c ω : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, c * ‖v‖ ^ 2 ≤ P.energy v + ω * ‖P.inclusion v‖ ^ 2) (hu : u ∈ P.unitConstraint W) :
    -ω ≤ P.energy u := by
  have := h u
  rw [hu.2, one_pow, mul_one] at this
  nlinarith [sq_nonneg ‖u‖]

variable (P W)

/-- The energy is bounded below on every constrained sphere. -/
theorem bddBelow_energy_image_unitConstraint : BddBelow (P.energy '' P.unitConstraint W) := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  exact ⟨-ω, by rintro _ ⟨u, hu, rfl⟩; exact neg_le_energy_of_mem_unitConstraint hc.le h hu⟩

/-- The energy has norm-bounded sublevels on every constrained sphere: on `S_W` the shifted
coercivity bound reads `c ‖u‖² ≤ q(u) + ω`. -/
theorem hasBoundedSublevelsOn_energy_unitConstraint :
    HasBoundedSublevelsOn P.energy (P.unitConstraint W) := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_mul_norm_sq_le_energy_add
  refine hasBoundedSublevelsOn_iff.2 fun b ↦ isBounded_iff_forall_norm_le.2 ⟨1 + (b + ω) / c, ?_⟩
  rintro u ⟨hu, hub⟩
  have hcu := h u
  rw [hu.2, one_pow, mul_one] at hcu
  have hsq : ‖u‖ ^ 2 ≤ (b + ω) / c := by
    rw [le_div_iff₀ hc]
    linarith
  nlinarith [sq_nonneg (‖u‖ - 1)]

/-! ### Weak topology -/

/-- On a constrained sphere the energy is lower semicontinuous for the weak topology of `V`.
There it differs by a constant from the nonnegative Hermitian form `q + ω ‖j ·‖²`. -/
theorem lowerSemicontinuousOn_energy_unitConstraint :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ P.energy ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' P.unitConstraint W) := by
  obtain ⟨c, hc, ω, h⟩ := P.exists_shifted_coercive
  set a := ContinuousLinearMap.shiftedForm P.inclusion P.form ω
  have hlsc := a.lowerSemicontinuous_re_apply_self_comp_toWeakSpace_symm
    (ContinuousLinearMap.shiftedForm_eq_star P.inclusion P.hermitian ω)
    fun u ↦ le_trans (by positivity)
      (ContinuousLinearMap.mul_norm_sq_le_re_shiftedForm_self P.inclusion le_rfl h u)
  have hconst : LowerSemicontinuous fun _ : WeakSpace 𝕜 V ↦ -ω := lowerSemicontinuous_const
  have hlsc' := (hlsc.add hconst).lowerSemicontinuousOn (toWeakSpace 𝕜 V '' P.unitConstraint W)
  have heq : EqOn (fun w : WeakSpace 𝕜 V ↦ re (a ((toWeakSpace 𝕜 V).symm w)
      ((toWeakSpace 𝕜 V).symm w)) + -ω) (fun w ↦ P.energy ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' P.unitConstraint W) := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [LinearEquiv.symm_apply_apply, a, ContinuousLinearMap.re_shiftedForm_self, hu.2,
      one_pow, mul_one, energy_def]
    ring
  exact fun w hw ↦
    LowerSemicontinuousWithinAt.congr_of_eventuallyEq (hlsc' w hw) hw heq.eventuallyEq_nhdsWithin

/-- When `W` is closed, the constrained sphere `S_W` is sequentially closed in the weak topology
of `V`: a weakly convergent sequence has norm-convergent images under the compact map `j`. -/
theorem isSeqClosed_toWeakSpace_unitConstraint (hW : IsClosed (W : Set H)) :
    IsSeqClosed (toWeakSpace 𝕜 V '' P.unitConstraint W) := by
  rw [unitConstraint_eq_preimage]
  exact P.isCompactOperator.isSeqClosed_toWeakSpace_preimage (hW.inter isClosed_sphere)

/-- If `V` is infinite dimensional, the unconstrained sphere `S_H` is not weakly closed: `0` lies in
its weak closure. So constrained minima are found along sequences or inside bounded sets. -/
theorem not_isClosed_toWeakSpace_unitConstraint_top (hV : ¬ FiniteDimensional 𝕜 V) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' P.unitConstraint ⊤) := by
  have heq : P.unitConstraint ⊤ = {u | ‖P.inclusion u‖ = 1} := by
    ext u
    simp
  rw [heq]
  exact not_isClosed_toWeakSpace_setOf_norm_eq hV P.injective one_pos

/-- When `V` is complete and `W` is closed, the part of the constrained sphere `S_W` in any closed
ball of `V` is weakly compact, although `S_W` itself need not be weakly closed. -/
theorem isCompact_toWeakSpace_unitConstraint_inter_closedBall [CompleteSpace V]
    (hW : IsClosed (W : Set H)) (x : V) (r : ℝ) :
    IsCompact (toWeakSpace 𝕜 V '' (P.unitConstraint W ∩ closedBall x r)) := by
  have hball := isCompact_toWeakSpace_closedBall
    (surjective_inclusionInDoubleDual_of_innerProductSpace (𝕜 := 𝕜)) x r
  have hclosed := P.isCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isBounded
    isBounded_closedBall hball.isClosed (hW.inter (isClosed_sphere (x := 0) (ε := 1)))
  rw [unitConstraint_eq_preimage, inter_comm]
  exact hball.of_isClosed_subset hclosed (image_mono inter_subset_left)

/-- When `V` is complete and `W` is closed, every sublevel of the energy on the constrained sphere
`S_W` is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_unitConstraint [CompleteSpace V]
    (hW : IsClosed (W : Set H)) (b : ℝ) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ P.unitConstraint W | P.energy u ≤ b}) :=
  isCompact_toWeakSpace_sublevel_of_isSeqClosed
    surjective_inclusionInDoubleDual_of_innerProductSpace
    (P.isSeqClosed_toWeakSpace_unitConstraint W hW)
    (P.lowerSemicontinuousOn_energy_unitConstraint W).seqLowerSemicontinuousOn b
    ((P.hasBoundedSublevelsOn_energy_unitConstraint W).isBounded_sublevel b)

/-! ### Existence of constrained minima -/

/-- **Constrained Rayleigh minima.** If `V` is complete and the constrained sphere `S_W` of a
closed submodule `W` is nonempty, the energy attains its minimum on `S_W`. -/
theorem exists_isMinOn_energy_unitConstraint [CompleteSpace V] (hW : IsClosed (W : Set H))
    (hne : (P.unitConstraint W).Nonempty) :
    ∃ u ∈ P.unitConstraint W, IsMinOn P.energy (P.unitConstraint W) u :=
  exists_isMinOn_of_isSeqClosed surjective_inclusionInDoubleDual_of_innerProductSpace hne
    (P.isSeqClosed_toWeakSpace_unitConstraint W hW)
    (P.lowerSemicontinuousOn_energy_unitConstraint W).seqLowerSemicontinuousOn
    (P.hasBoundedSublevelsOn_energy_unitConstraint W)

/-- If `V` is complete and `W` is closed, the set of minimizers of the energy on the constrained
sphere `S_W` is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_unitConstraint [CompleteSpace V]
    (hW : IsClosed (W : Set H)) :
    IsCompact (toWeakSpace 𝕜 V ''
      {u ∈ P.unitConstraint W | IsMinOn P.energy (P.unitConstraint W) u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed
    surjective_inclusionInDoubleDual_of_innerProductSpace
    (P.isSeqClosed_toWeakSpace_unitConstraint W hW)
    (P.lowerSemicontinuousOn_energy_unitConstraint W).seqLowerSemicontinuousOn
    (P.hasBoundedSublevelsOn_energy_unitConstraint W)

variable {P W}

/-- **Rayleigh-quotient form of a constrained minimum.** A minimizer `u₀` of the energy on the
constrained sphere `S_W` satisfies `q(u₀) ‖j u‖² ≤ q(u)` for every `u` with `j u ∈ W`: the
minimum bounds the Rayleigh quotient `q(u) / ‖j u‖²` below on the `u ≠ 0` with `j u ∈ W`. -/
theorem mul_norm_sq_le_energy_of_isMinOn {u₀ : V}
    (hmin : IsMinOn P.energy (P.unitConstraint W) u₀) (hu : P.inclusion u ∈ W) :
    P.energy u₀ * ‖P.inclusion u‖ ^ 2 ≤ P.energy u := by
  by_cases hu0 : P.inclusion u = 0
  · rw [P.injective (hu0.trans (map_zero P.inclusion).symm)]
    simp
  have h : P.energy u₀ ≤ P.energy _ := hmin (inv_norm_smul_mem_unitConstraint hu hu0)
  rw [energy_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_pow] at h
  calc P.energy u₀ * ‖P.inclusion u‖ ^ 2
      ≤ ((‖P.inclusion u‖ ^ 2)⁻¹ * P.energy u) * ‖P.inclusion u‖ ^ 2 := by gcongr
    _ = P.energy u := by field_simp

/-- The energy at `u₀` is a lower bound for the energy on the constrained sphere `S_W` exactly
when `q(u₀) ‖j u‖² ≤ q(u)` for every `u` with `j u ∈ W`. For `u₀ ∈ S_W` this says that `q(u₀)` is
the least value of the Rayleigh quotient `q(u) / ‖j u‖²` over the `u ≠ 0` with `j u ∈ W`. -/
theorem isMinOn_energy_unitConstraint_iff {u₀ : V} :
    IsMinOn P.energy (P.unitConstraint W) u₀ ↔
      ∀ u, P.inclusion u ∈ W → P.energy u₀ * ‖P.inclusion u‖ ^ 2 ≤ P.energy u := by
  refine ⟨fun hmin _ hu ↦ mul_norm_sq_le_energy_of_isMinOn hmin hu, fun h u hu ↦ ?_⟩
  simpa [hu.2] using h u hu.1

end CompactFormPair

end TauCeti
