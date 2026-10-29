/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces of anticommuting endomorphisms

Let `f` and `g` be endomorphisms of a module with `f * g + g * f = 0`. Then
`(f + μ) g = -g (f - μ)`, so `g` carries the generalized `μ`-eigenspace of `f` into its
generalized `-μ`-eigenspace, for every exponent. When `g = e` is invertible, its inverse also
anticommutes with `f`, and `e` identifies the two generalized eigenspaces, which therefore have
equal `finrank`. In particular, for a finite-dimensional vector space over a field, the
eigenvalues of `f` come in pairs `±μ` with equal geometric and algebraic multiplicities, and `e`
preserves every generalized eigenspace of `f` at `0`.

The basic example is a shape operator `S` of a complex submanifold, which anticommutes with the
complex structure `J`: its principal curvatures come in pairs `±κ`.

## Main declarations

* `Module.End.genEigenspace_neg`: the generalized eigenspaces of `-f` are those of `f` at the
  negated eigenvalue.
* `Module.End.genEigenspace_smul`: over a field, the generalized eigenspaces of `t • f` for
  `t ≠ 0` are those of `f` at the rescaled eigenvalue.
* `Module.End.mapsTo_genEigenspace_neg_of_anticommute`: an endomorphism anticommuting with `f`
  maps the generalized `μ`-eigenspace of `f` into its generalized `-μ`-eigenspace.
* `Module.End.map_genEigenspace_of_anticommute`: for an invertible such endomorphism this is an
  equality of submodules.
* `Module.End.genEigenspaceEquivOfAnticommute`: the induced linear equivalence between the
  generalized `μ`- and `-μ`-eigenspaces.
* `Module.End.finrank_genEigenspace_neg_of_anticommute`: the two generalized eigenspaces have the
  same dimension.
* `Module.End.hasUnifEigenvalue_neg_iff_of_anticommute`: `-μ` is a (generalized) eigenvalue
  exactly when `μ` is.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open Set

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The generalized eigenspaces of `-f` are the generalized eigenspaces of `f` at the negated
eigenvalue. -/
@[simp]
theorem genEigenspace_neg (f : End R M) (μ : R) (k : ℕ∞) :
    (-f).genEigenspace μ k = f.genEigenspace (-μ) k :=
  le_antisymm (by simpa using genEigenspace_le_smul (-f) μ (-1) k)
    (by simpa using genEigenspace_le_smul f (-μ) (-1) k)

/-- Over a field, the generalized eigenspaces of a nonzero multiple `t • f` are the generalized
eigenspaces of `f` at the eigenvalue divided by `t`. -/
theorem genEigenspace_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (f : End K V)
    {t : K} (ht : t ≠ 0) (μ : K) (k : ℕ∞) :
    (t • f).genEigenspace μ k = f.genEigenspace (t⁻¹ * μ) k :=
  le_antisymm
    (by simpa [smul_smul, inv_mul_cancel₀ ht] using genEigenspace_le_smul (t • f) μ t⁻¹ k)
    (by simpa [mul_inv_cancel_left₀ ht] using genEigenspace_le_smul f (t⁻¹ * μ) t k)

variable {f : End R M}

/-- An endomorphism `g` anticommuting with `f` maps the generalized `μ`-eigenspace of `f` into
its generalized `-μ`-eigenspace. -/
theorem mapsTo_genEigenspace_neg_of_anticommute {g : End R M} (h : f * g + g * f = 0)
    (μ : R) (k : ℕ∞) :
    MapsTo g (f.genEigenspace μ k) (f.genEigenspace (-μ) k) := by
  have hg : (-f) ∘ₗ g = g ∘ₗ f := by
    rw [LinearMap.neg_comp, ← mul_eq_comp, eq_neg_of_add_eq_zero_left h, neg_neg, mul_eq_comp]
  rw [← genEigenspace_neg]
  exact mapsTo_genEigenspace_of_comp g hg μ k

/-- The inverse of an invertible endomorphism anticommuting with `f` also anticommutes with
`f`. -/
theorem mul_symm_add_symm_mul_eq_zero {e : M ≃ₗ[R] M} (h : f * e + e * f = 0) :
    f * e.symm + e.symm * f = 0 := by
  ext x
  simpa [add_comm] using congrArg e.symm (LinearMap.congr_fun h (e.symm x))

/-- An invertible endomorphism `e` anticommuting with `f` maps the generalized `μ`-eigenspace of
`f` onto its generalized `-μ`-eigenspace. -/
theorem map_genEigenspace_of_anticommute (e : M ≃ₗ[R] M) (h : f * e + e * f = 0) (μ : R)
    (k : ℕ∞) :
    (f.genEigenspace μ k).map (e : M →ₗ[R] M) = f.genEigenspace (-μ) k := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun x hx ↦
    mapsTo_genEigenspace_neg_of_anticommute h μ k hx) fun y hy ↦ ?_
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  simpa using mapsTo_genEigenspace_neg_of_anticommute (mul_symm_add_symm_mul_eq_zero h) (-μ) k hy

/-- An invertible endomorphism `e` anticommuting with `f` restricts to a linear equivalence
between the generalized `μ`- and `-μ`-eigenspaces of `f`. -/
def genEigenspaceEquivOfAnticommute (e : M ≃ₗ[R] M) (h : f * e + e * f = 0) (μ : R)
    (k : ℕ∞) :
    f.genEigenspace μ k ≃ₗ[R] f.genEigenspace (-μ) k :=
  e.ofSubmodules _ _ (map_genEigenspace_of_anticommute e h μ k)

@[simp]
theorem coe_genEigenspaceEquivOfAnticommute_apply (e : M ≃ₗ[R] M) (h : f * e + e * f = 0)
    (μ : R) (k : ℕ∞) (x : f.genEigenspace μ k) :
    (genEigenspaceEquivOfAnticommute e h μ k x : M) = e x := by
  rw [genEigenspaceEquivOfAnticommute, LinearEquiv.ofSubmodules_apply]

@[simp]
theorem coe_genEigenspaceEquivOfAnticommute_symm_apply (e : M ≃ₗ[R] M)
    (h : f * e + e * f = 0) (μ : R) (k : ℕ∞) (x : f.genEigenspace (-μ) k) :
    ((genEigenspaceEquivOfAnticommute e h μ k).symm x : M) = e.symm x := by
  rw [genEigenspaceEquivOfAnticommute, LinearEquiv.ofSubmodules_symm_apply]

/-- If an invertible endomorphism anticommutes with `f`, the generalized `μ`- and
`-μ`-eigenspaces of `f` have the same `finrank`. For a finite-dimensional vector space over a
field, these are the geometric multiplicities of `μ` and `-μ` when `k = 1`, and their algebraic
multiplicities when `k = ⊤`. -/
theorem finrank_genEigenspace_neg_of_anticommute (e : M ≃ₗ[R] M) (h : f * e + e * f = 0)
    (μ : R) (k : ℕ∞) :
    Module.finrank R (f.genEigenspace (-μ) k) = Module.finrank R (f.genEigenspace μ k) :=
  (genEigenspaceEquivOfAnticommute e h μ k).finrank_eq.symm

/-- If an invertible endomorphism anticommutes with `f`, then `-μ` is a generalized eigenvalue
of `f` exactly when `μ` is. -/
theorem hasUnifEigenvalue_neg_iff_of_anticommute (e : M ≃ₗ[R] M) (h : f * e + e * f = 0)
    {μ : R} {k : ℕ∞} :
    f.HasUnifEigenvalue (-μ) k ↔ f.HasUnifEigenvalue μ k := by
  rw [HasUnifEigenvalue, HasUnifEigenvalue, ← map_genEigenspace_of_anticommute e h μ k,
    Submodule.map_ne_bot_iff]

/-- If an invertible endomorphism anticommutes with `f`, then `-μ` is an eigenvalue of `f`
exactly when `μ` is. -/
theorem hasEigenvalue_neg_iff_of_anticommute (e : M ≃ₗ[R] M) (h : f * e + e * f = 0)
    {μ : R} :
    f.HasEigenvalue (-μ) ↔ f.HasEigenvalue μ :=
  hasUnifEigenvalue_neg_iff_of_anticommute e h

end Module.End
