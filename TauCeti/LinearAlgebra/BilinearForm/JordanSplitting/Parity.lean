/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic

/-!
# Parity of Jordan constituents

The parity of a Jordan constituent must be measured relative to its own scale: a vector in
a constituent of scale `π ^ j` is even at that scale when its self-pairing lies in
`π ^ (j + 1) R`. In particular, at the dyadic prime a scale-two unary block is odd at its
own scale, although all its self-pairings are divisible by two.

For free constituents, the condition is that the norm ideal lies in `π` times the constituent's
own scale ideal. Zero constituents satisfy this condition, giving the even convention at an
empty scale. For symmetric forms at `π = 2`, this is the usual type II condition on dyadic
Jordan constituents: polarization gives the reverse containment in twice the scale ideal.

The condition on the `j`-th constituent is equivalent to an intrinsic condition on the form:
every vector pairing into `π ^ j R` has self-pairing in `π ^ (j + 1) R`. It follows that this
condition is independent of the Jordan splitting and is invariant under isometry. The
divisibility statements hold over any commutative ring with a non-zero-divisor `π`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 93:28--29, for invariants of dyadic Jordan
  splittings.
* Sungmun Cho, *Group schemes and local densities of quadratic lattices in residue
  characteristic 2*, [Definition 2.1(b)](https://arxiv.org/pdf/1210.7625#page=3), for parity
  relative to a modular lattice's own scale.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}
  {π : R} {N : ℕ → Submodule R M}

/-- A constituent has self-pairings divisible by one more power of `π` exactly when every vector
pairing into its scale does. This characterizes its parity without choosing a splitting. -/
theorem IsJordanSplitting.forall_pow_succ_dvd_self_iff (h : B.IsJordanSplitting π N)
    (hπ : π ∈ nonZeroDivisors R) (j : ℕ) :
    (∀ x : N j, π ^ (j + 1) ∣ B x x) ↔
      ∀ x : M, (∀ y, π ^ j ∣ B x y) → π ^ (j + 1) ∣ B x x := by
  classical
  constructor
  · intro hself x hx
    obtain ⟨f, rfl⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' N x).mp
      (h.isInternal.submodule_iSup_eq_top ▸ Submodule.mem_top)
    have hcomponent (i : ℕ) : π ^ (j + 1) ∣ B (f i) (f i) := by
      rcases lt_trichotomy i j with hi | rfl | hi
      · obtain ⟨z, hz⟩ := (h.isModular i).exists_eq_smul_of_forall_dvd
          (pow_mem hπ i) (pow_mem hπ (j - i)) (x := f i) fun y ↦ by
            rw [← pow_add, Nat.add_sub_of_le hi.le, restrict_apply, domRestrict_apply,
              ← h.apply_dfinsuppSum f i y]
            exact hx y
        obtain ⟨c, hc⟩ := (h.isModular i).dvd z z
        have hc' : B z z = π ^ i * c := by
          simpa only [restrict_apply, domRestrict_apply] using hc
        rw [hz, Submodule.coe_smul]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hc']
        have heq : π ^ (j - i) * (π ^ (j - i) * (π ^ i * c)) =
            π ^ ((j - i) + (j - i) + i) * c := by simp [pow_add, mul_assoc]
        rw [heq]
        exact dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) c
      · exact hself (f i)
      · exact (pow_dvd_pow π hi).trans ((h.isModular i).dvd (f i) (f i))
    rw [DFinsupp.sum, map_sum]
    refine Finset.dvd_sum fun i _ ↦ ?_
    rw [← DFinsupp.sum, h.apply_dfinsuppSum f i (f i)]
    exact hcomponent i
  · intro hself x
    exact hself x (h.pow_dvd_apply x.2)

/-- Whether the norm ideal lies in `π` times the constituent's own scale is independent of the
Jordan splitting. At `π = 2` this is invariance of dyadic parity type. Zero constituents satisfy
the containment. Freeness is only needed for the two constituents being compared. -/
theorem IsJordanSplitting.normIdeal_le_mul_scaleIdeal_iff
    {N' : ℕ → Submodule R M} (h : B.IsJordanSplitting π N)
    (h' : B.IsJordanSplitting π N') (hπ : π ∈ nonZeroDivisors R) (j : ℕ)
    [Module.Free R (N j)] [Module.Free R (N' j)] :
    (B.restrict (N j)).normIdeal ≤ Ideal.span {π} * (B.restrict (N j)).scaleIdeal ↔
      (B.restrict (N' j)).normIdeal ≤ Ideal.span {π} * (B.restrict (N' j)).scaleIdeal := by
  rw [(h.isModular j).normIdeal_le_mul_scaleIdeal_iff,
    (h'.isModular j).normIdeal_le_mul_scaleIdeal_iff]
  simpa only [mul_comm π, ← pow_succ, normIdeal_le_iff, Ideal.mem_span_singleton,
    restrict_apply, domRestrict_apply] using
    (h.forall_pow_succ_dvd_self_iff hπ j).trans
      (h'.forall_pow_succ_dvd_self_iff hπ j).symm

/-- Parity relative to the constituent's own scale is an isometry invariant. In particular,
Jordan splittings of isometric dyadic forms have the same type at every scale. -/
theorem IsJordanSplitting.normIdeal_le_mul_scaleIdeal_iff_of_equivalent
    {M' : Type*} [AddCommGroup M'] [Module R M'] {B' : BilinForm R M'}
    {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N) (h' : B'.IsJordanSplitting π N')
    (hB : B.Equivalent B') (hπ : π ∈ nonZeroDivisors R) (j : ℕ)
    [Module.Free R (N j)] [Module.Free R (N' j)] :
    (B.restrict (N j)).normIdeal ≤ Ideal.span {π} * (B.restrict (N j)).scaleIdeal ↔
      (B'.restrict (N' j)).normIdeal ≤ Ideal.span {π} * (B'.restrict (N' j)).scaleIdeal := by
  rw [(h.isModular j).normIdeal_le_mul_scaleIdeal_iff,
    (h'.isModular j).normIdeal_le_mul_scaleIdeal_iff]
  simp only [mul_comm π, ← pow_succ, normIdeal_le_iff, Ideal.mem_span_singleton,
    restrict_apply, domRestrict_apply]
  rw [h.forall_pow_succ_dvd_self_iff hπ j, h'.forall_pow_succ_dvd_self_iff hπ j]
  obtain ⟨e⟩ := hB
  constructor
  · intro H x hx
    obtain ⟨x, rfl⟩ := e.surjective x
    simp only [IsometryEquiv.coe_toLinearEquiv, e.map_app] at hx ⊢
    apply H x
    intro y
    simpa only [e.map_app] using hx (e y)
  · intro H x hx
    rw [← e.map_app]
    apply H (e x)
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [IsometryEquiv.coe_toLinearEquiv, e.map_app] using hx y

end LinearMap.BilinForm
