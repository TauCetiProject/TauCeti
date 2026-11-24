/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Eigenspaces of a scalar multiple

Scaling an endomorphism `f` by a scalar `c` that acts injectively on the module (for example a
nonzero scalar on a vector space) relabels the eigenspaces of `f` by `c`: the `c μ`-eigenspace of
`c • f` is the `μ`-eigenspace of `f`, and likewise for the generalized eigenspaces of every order
(`Module.End.genEigenspace_smul`), so `c • f` has the eigenvalue `c μ` exactly when `f` has the
eigenvalue `μ` (`Module.End.hasEigenvalue_smul_iff`). Over a field, for `c ≠ 0`, every scalar `μ`
is `c (μ / c)`, so the `μ`-eigenspace of `c • f` is the `μ / c`-eigenspace of `f`
(`Module.End.eigenspace_smul_eq_div`). For example, for `κ / m ≠ 0`, the eigenspaces of the
acceleration operator `(κ / m) • H` of a spring system are those of its force matrix `H`.

Over a field, for `c ≠ 0`, it follows for powers that `1` is an eigenvalue of `(c • f) ^ m`
exactly when `(c ^ m)⁻¹` is an eigenvalue of `f ^ m`
(`Module.End.hasEigenvalue_one_pow_smul_iff`). In finite dimensions `f ^ m` has finitely many
eigenvalues, and each is `(c ^ m)⁻¹` for finitely many `c`, so for `m ≠ 0` only finitely many
rescalings `c • f` have an `m`-th power with the eigenvalue `1`
(`Module.End.finite_setOf_hasEigenvalue_one_pow_smul`), and only countably many have some
positive power with the eigenvalue `1`
(`Module.End.countable_setOf_exists_hasEigenvalue_one_pow_smul`). For the linearized return map
`f` of a periodic orbit, `f ^ m` is the linearized return map of its `m`-fold cover, and the orbit
together with all its covers is nondegenerate when no positive power of `f` has the eigenvalue
`1`. A resonant `f` such as `-1` has no eigenvalue `1` while its square does; over `ℝ`, the
rescalings `c • (-1)` with `c ≠ 1, -1` have no positive power with the eigenvalue `1`.
-/

public section

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The generalized `c μ`-eigenspace of `c • f` is the generalized `μ`-eigenspace of `f`, for `c`
acting injectively on `M`. This is the converse of Mathlib's `Module.End.genEigenspace_le_smul`,
which holds for every `c`. -/
@[simp]
theorem genEigenspace_smul (f : End R M) {c : R} (hc : IsSMulRegular M c) (μ : R) (k : ℕ∞) :
    (c • f).genEigenspace (c * μ) k = f.genEigenspace μ k := by
  refine le_antisymm (fun x hx ↦ ?_) (genEigenspace_le_smul f μ c k)
  obtain ⟨l, hlk, hl⟩ := mem_genEigenspace.1 hx
  -- `(c • f - (c * μ) • 1) ^ l = c ^ l • (f - μ • 1) ^ l`, and `c ^ l` acts injectively on `M`.
  rw [LinearMap.mem_ker, mul_smul, ← smul_sub, smul_pow, LinearMap.smul_apply] at hl
  exact mem_genEigenspace.2 ⟨l, hlk, LinearMap.mem_ker.2 ((hc.pow l).right_eq_zero_of_smul hl)⟩

/-- The `c μ`-eigenspace of `c • f` is the `μ`-eigenspace of `f`, for `c` acting injectively on
`M`. -/
theorem eigenspace_smul (f : End R M) {c : R} (hc : IsSMulRegular M c) (μ : R) :
    eigenspace (c • f) (c * μ) = eigenspace f μ :=
  genEigenspace_smul f hc μ 1

/-- For `c` acting injectively on `M`, `c • f` has the eigenvalue `c * μ` exactly when `f` has the
eigenvalue `μ`. -/
@[simp]
theorem hasEigenvalue_smul_iff (f : End R M) {c : R} (hc : IsSMulRegular M c) (μ : R) :
    (c • f).HasEigenvalue (c * μ) ↔ f.HasEigenvalue μ := by
  rw [hasEigenvalue_iff, hasEigenvalue_iff, eigenspace_smul f hc]

end Module.End

/-! ### Rescaling by a nonzero scalar over a field -/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Over a field, for `c ≠ 0`, the generalized `μ`-eigenspace of `c • f` is the generalized
`μ / c`-eigenspace of `f`. -/
theorem genEigenspace_smul_eq_div (f : End K V) {c : K} (hc : c ≠ 0) (μ : K) (k : ℕ∞) :
    (c • f).genEigenspace μ k = f.genEigenspace (μ / c) k := by
  rw [← genEigenspace_smul f (.of_ne_zero hc) (μ / c), mul_div_cancel₀ μ hc]

/-- Over a field, for `c ≠ 0`, the `μ`-eigenspace of `c • f` is the `μ / c`-eigenspace of `f`. -/
theorem eigenspace_smul_eq_div (f : End K V) {c : K} (hc : c ≠ 0) (μ : K) :
    eigenspace (c • f) μ = eigenspace f (μ / c) :=
  genEigenspace_smul_eq_div f hc μ 1

/-- Over a field, for `c ≠ 0`, `c • f` has the eigenvalue `μ` exactly when `f` has the eigenvalue
`μ / c`. -/
theorem hasEigenvalue_smul_iff_div (f : End K V) {c : K} (hc : c ≠ 0) (μ : K) :
    (c • f).HasEigenvalue μ ↔ f.HasEigenvalue (μ / c) := by
  rw [← hasEigenvalue_smul_iff f (.of_ne_zero hc) (μ / c), mul_div_cancel₀ μ hc]

/-! ### Powers of rescalings with the eigenvalue one -/

/-- For `c ≠ 0`, the `m`-th power of `c • f` has the eigenvalue `1` exactly when the `m`-th power
of `f` has the eigenvalue `(c ^ m)⁻¹`. -/
theorem hasEigenvalue_one_pow_smul_iff (f : End K V) {c : K} (hc : c ≠ 0) (m : ℕ) :
    ((c • f) ^ m).HasEigenvalue 1 ↔ (f ^ m).HasEigenvalue (c ^ m)⁻¹ := by
  rw [smul_pow, hasEigenvalue_smul_iff_div _ (pow_ne_zero m hc), one_div]

/-- For `m ≠ 0`, only finitely many rescalings `c • f` of an endomorphism `f` of a
finite-dimensional space have an `m`-th power with the eigenvalue `1`. -/
theorem finite_setOf_hasEigenvalue_one_pow_smul [FiniteDimensional K V] (f : End K V) {m : ℕ}
    (hm : m ≠ 0) : {c : K | ((c • f) ^ m).HasEigenvalue 1}.Finite := by
  -- A bad `c` is nonzero, so `(c ^ m)⁻¹` is an eigenvalue of `f ^ m`.
  have hsub : {c : K | ((c • f) ^ m).HasEigenvalue 1} ⊆
      (fun c : K ↦ (c ^ m)⁻¹) ⁻¹' {μ | (f ^ m).HasEigenvalue μ} := by
    intro c hc
    have hc₀ : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv⟩ := Set.mem_ofPred.1 hc |>.exists_hasEigenvector
      simpa [zero_pow hm, eq_comm, hv.2] using hv.apply_eq_smul
    exact Set.mem_preimage.2 ((hasEigenvalue_one_pow_smul_iff f hc₀ m).1 (Set.mem_ofPred.1 hc))
  -- Each fiber of `c ↦ (c ^ m)⁻¹` lies among the `m`-th roots of `μ⁻¹`.
  have hfiber (μ : K) : ((fun c : K ↦ (c ^ m)⁻¹) ⁻¹' {μ}).Finite := by
    refine (Polynomial.nthRootsFinset m μ⁻¹).finite_toSet.subset fun c hc ↦ ?_
    obtain rfl := Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hm), inv_inv]
  exact ((f ^ m).finite_hasEigenvalue.preimage' fun μ _ ↦ hfiber μ).subset hsub

/-- Only countably many rescalings `c • f` of an endomorphism `f` of a finite-dimensional space
have a positive power with the eigenvalue `1`. -/
theorem countable_setOf_exists_hasEigenvalue_one_pow_smul [FiniteDimensional K V] (f : End K V) :
    {c : K | ∃ m ≠ 0, ((c • f) ^ m).HasEigenvalue 1}.Countable := by
  rw [Set.ofPred_exists]
  refine Set.countable_iUnion fun m ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · exact (finite_setOf_hasEigenvalue_one_pow_smul f hm).countable.mono fun _ hc ↦ hc.2

end Module.End
