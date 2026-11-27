/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.Ultra
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Sup norms on the dual of a finite module

If the image of `R` in an ultrametric normed field `C` lies in the closed unit ball,
the values of a linear map from a finite `R`-module to `C` are bounded. Their supremum
is a norm, computed on any finite generating set. No norm on the source module is needed.
The construction is a real-valued function and introduces no norm instances.

## References

These norms are the setting of the bound for the cokernel of the Hodge–Tate map in
L. Alpöge's formal Lean proof of the Riemann hypothesis for Dirichlet L-functions (2026),
https://github.com/leanprover-community/riemann-hypothesis. The estimates here are elementary,
and the formalization is independent of that source.
-/

public section

namespace LinearMap

section Seminormed

variable {R E M : Type*} [Semiring R] [SeminormedAddCommGroup E] [Module R E]
  [AddCommMonoid M] [Module R M]

/-- The conditional real supremum of the norms of all values, with value zero when
these norms are unbounded. For a finite module over a ring mapping into the unit ball
of a normed field, this is a genuine, attained supremum. -/
noncomputable def supNorm (f : M →ₗ[R] E) : ℝ := ⨆ m, ‖f m‖

/-- The sup norm is the conditional real supremum over all arguments, with value zero
when the norms are unbounded. -/
theorem supNorm_def (f : M →ₗ[R] E) : f.supNorm = ⨆ m, ‖f m‖ := (rfl)

/-- The sup norm is nonnegative, including when the range is unbounded. -/
theorem supNorm_nonneg (f : M →ₗ[R] E) : 0 ≤ f.supNorm :=
  Real.iSup_nonneg fun _ ↦ norm_nonneg _

/-- The zero map has sup norm zero. -/
@[simp]
theorem supNorm_zero : (0 : M →ₗ[R] E).supNorm = 0 := by
  simp [supNorm]

/-- Negation preserves the sup norm. -/
@[simp]
theorem supNorm_neg (f : M →ₗ[R] E) : (-f).supNorm = f.supNorm := by
  simp [supNorm]

end Seminormed

variable {R C M N : Type*} [CommSemiring R] [NormedField C] [Algebra R C]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A bound on the values at generators extends to their span when scalars have norm
at most one. The bound must be nonnegative, to include the span of the empty set. -/
theorem norm_apply_le_of_mem_span (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {s : Set M} {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span R s) : ‖f m‖ ≤ r := by
  have := IsUltrametricDist.isUltrametricDist_of_forall_norm_algebraMap_le_one hR
  induction hm using Submodule.span_induction with
  | mem m hm => exact hs m hm
  | zero => simpa using hr
  | add x y hx hy hx' hy' =>
    simpa only [map_add] using (IsUltrametricDist.norm_add_le_max (f x) (f y)).trans
      (max_le hx' hy')
  | smul a x hx hx' =>
    simpa only [map_smul, Algebra.smul_def, norm_mul] using
      (mul_le_mul_of_nonneg_right (hR a) (norm_nonneg (f x))).trans (by simpa using hx')

variable [Module.Finite R M]

/-- Values of a linear map out of a finite module are bounded if the base ring maps
into the closed unit ball. -/
theorem bddAbove_range_norm (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) : BddAbove (Set.range fun m ↦ ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  apply f.norm_apply_le_of_mem_span hR (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) _
    (hs ▸ Submodule.mem_top)
  intro x hx
  exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hx

/-- Each value is bounded by the sup norm. -/
theorem norm_apply_le_supNorm (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) (m : M) : ‖f m‖ ≤ f.supNorm :=
  le_ciSup (f.bddAbove_range_norm hR) m

/-- A bound on the sup norm is equivalent to the same bound at every argument. -/
theorem supNorm_le_iff (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {r : ℝ} :
    f.supNorm ≤ r ↔ ∀ m, ‖f m‖ ≤ r :=
  ⟨fun h m ↦ (f.norm_apply_le_supNorm hR m).trans h, fun h ↦ ciSup_le h⟩

/-- The sup norm vanishes precisely on the zero map. -/
@[simp]
theorem supNorm_eq_zero_iff (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) : f.supNorm = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext m
    exact norm_eq_zero.mp (le_antisymm (h ▸ f.norm_apply_le_supNorm hR m) (norm_nonneg _))
  · rintro rfl
    exact supNorm_zero

/-- A bound may be checked on any spanning set. -/
theorem supNorm_le_iff_of_span_eq_top (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {s : Set M}
    (hs : Submodule.span R s = ⊤) {r : ℝ} (hr : 0 ≤ r) :
    f.supNorm ≤ r ↔ ∀ m ∈ s, ‖f m‖ ≤ r := by
  rw [f.supNorm_le_iff hR]
  exact ⟨fun h m _ ↦ h m, fun h m ↦
    f.norm_apply_le_of_mem_span hR hr h (hs ▸ Submodule.mem_top)⟩

omit [Module.Finite R M] in
/-- On a finite generating set the sup norm is the largest norm of a value at a generator,
with zero for an empty generating set. -/
theorem supNorm_eq_sup (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) (s : Finset M)
    (hs : Submodule.span R (s : Set M) = ⊤) :
    f.supNorm = (s.sup fun m ↦ ‖f m‖₊ : NNReal) := by
  have : Module.Finite R M := ⟨⟨s, hs⟩⟩
  apply le_antisymm
  · apply (f.supNorm_le_iff_of_span_eq_top hR hs (by positivity)).mpr
    intro m hm
    exact_mod_cast (Finset.le_sup (f := fun m ↦ ‖f m‖₊) hm)
  · have h : s.sup (fun m ↦ ‖f m‖₊) ≤ (⟨f.supNorm, f.supNorm_nonneg⟩ : NNReal) :=
      Finset.sup_le fun m _ ↦ f.norm_apply_le_supNorm hR m
    exact_mod_cast h

/-- The sup norm is attained at an element of the module, including for the zero module. -/
theorem exists_norm_eq_supNorm (f : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) : ∃ m, ‖f m‖ = f.supNorm := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have ht : Submodule.span R (↑(insert 0 s) : Set M) = ⊤ := by simpa using hs
  obtain ⟨m, _, hm⟩ := (insert 0 s).sup_mem_of_nonempty (f := fun m ↦ ‖f m‖₊)
    (Finset.insert_nonempty 0 s)
  refine ⟨m, ?_⟩
  rw [f.supNorm_eq_sup hR _ ht]
  exact congrArg (fun x : NNReal ↦ (x : ℝ)) hm

/-- The sup norm satisfies the strong triangle inequality. -/
theorem supNorm_add_le_max (f g : M →ₗ[R] C)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (f + g).supNorm ≤ max f.supNorm g.supNorm := by
  have := IsUltrametricDist.isUltrametricDist_of_forall_norm_algebraMap_le_one hR
  apply ((f + g).supNorm_le_iff hR).mpr
  intro m
  exact (IsUltrametricDist.norm_add_le_max (f m) (g m)).trans
    (max_le_max (f.norm_apply_le_supNorm hR m) (g.norm_apply_le_supNorm hR m))

omit [Module.Finite R M] in
/-- Scalar multiplication is homogeneous for the sup norm. -/
@[simp]
theorem supNorm_smul (c : C) (f : M →ₗ[R] C) :
    (c • f).supNorm = ‖c‖ * f.supNorm := by
  simp only [supNorm, coe_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

/-- Precomposition by a linear map does not increase the sup norm. -/
theorem supNorm_comp_le (f : M →ₗ[R] C) (u : N →ₗ[R] M)
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) : (f.comp u).supNorm ≤ f.supNorm := by
  exact ciSup_le fun n ↦ f.norm_apply_le_supNorm hR (u n)

end LinearMap

namespace LinearMap

variable {C M : Type*} [NormedField C] [IsUltrametricDist C] [AddCommMonoid M]
  [Module (NormedField.valuation (K := C)).valuationSubring M]
  [Module.Finite (NormedField.valuation (K := C)).valuationSubring M]

/-- Sup norm at most one means that every value belongs to the valuation ring. -/
theorem supNorm_le_one_iff (f : M →ₗ[(NormedField.valuation (K := C)).valuationSubring] C) :
    f.supNorm ≤ 1 ↔ ∀ m, f m ∈ (NormedField.valuation (K := C)).valuationSubring := by
  have hR : ∀ r : (NormedField.valuation (K := C)).valuationSubring,
      ‖algebraMap (NormedField.valuation (K := C)).valuationSubring C r‖ ≤ 1 := by
    intro r
    exact_mod_cast r.property
  rw [f.supNorm_le_iff hR]
  simp only [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnNorm]

end LinearMap
