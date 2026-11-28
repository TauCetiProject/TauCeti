/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.IsometryGroup

/-!
# The action of the orthogonal group on the quotient by the polar kernel

Let `Q` be a quadratic map on `M`, with polar bilinear map `b = polarBilin Q` and polar kernel
`K = ker b`, the vectors orthogonal to everything. The polar form descends to a bilinear map `b'` on
`M ⧸ K` (`QuadraticMap.polarQuotientBilin`) which no longer has a kernel. An orthogonal
automorphism of `Q` preserves `b`, hence maps `K` onto itself, so it induces an isometry of `b'`.
This gives a group homomorphism `O(Q) → Isom(b')`
(`QuadraticMap.orthogonalGroupToPolarQuotient`), whose kernel consists of the orthogonal
automorphisms moving every vector by an element of `K`.

In characteristic two `b'` is alternating, so `Isom(b')` is a symplectic group, while `Q` itself
need not descend to `M ⧸ K`. This is the setting of the reduction modulo two of an even lattice:
the orthogonal group of the reduced quadratic form maps to the symplectic group of the quotient by
the polar radical.

## Main definitions

* `QuadraticMap.polarQuotientBilin`: the polar form of `Q` on `M ⧸ ker (polarBilin Q)`.
* `QuadraticMap.orthogonalGroupToPolarQuotient`: the homomorphism from the orthogonal group
  of `Q` to the isometry group of `polarQuotientBilin Q`.

## Main results

* `QuadraticMap.map_add_of_mem_ker_polarBilin`: `Q` is additive along the polar kernel.
* `QuadraticMap.separatingLeft_polarQuotientBilin`: the induced form has no left kernel.
* `QuadraticMap.orthogonalGroupToPolarQuotient_apply_mk`: the induced isometry sends the
  class of `x` to the class of `g x`.
* `QuadraticMap.mem_ker_orthogonalGroupToPolarQuotient_iff`: `g` acts trivially on the
  quotient exactly when `g x - x` lies in the polar kernel for every `x`.
-/

public section

namespace QuadraticMap

open TauCeti.QuadraticMap (orthogonalGroup polar_apply_of_mem_orthogonalGroup)

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (Q : QuadraticMap R M N)

/-- A quadratic map is additive along its polar kernel: `Q (x + y) = Q x + Q y` as soon as `y` is
orthogonal to everything. -/
theorem map_add_of_mem_ker_polarBilin (x : M) {y : M} (hy : y ∈ LinearMap.ker (polarBilin Q)) :
    Q (x + y) = Q x + Q y := by
  rw [LinearMap.mem_ker] at hy
  rw [QuadraticMap.map_add (⇑Q), polar_comm, ← polarBilin_apply_apply, hy, LinearMap.zero_apply,
    add_zero]

/-- The polar form of `Q` on the quotient of `M` by the kernel of `polarBilin Q`: the class of `x`
pairs with the class of `y` to `polar Q x y`. -/
noncomputable def polarQuotientBilin :
    (M ⧸ LinearMap.ker (polarBilin Q)) →ₗ[R] (M ⧸ LinearMap.ker (polarBilin Q)) →ₗ[R] N :=
  LinearMap.IsRefl.liftQ₂ (polarBilin Q) _ (isRefl_polarBilin Q) le_rfl

/-- The induced polar form on classes. -/
@[simp]
theorem polarQuotientBilin_mk (x y : M) :
    polarQuotientBilin Q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = polar Q x y :=
  (rfl)

/-- The polar form on the quotient by the polar kernel has trivial left kernel. -/
theorem separatingLeft_polarQuotientBilin : (polarQuotientBilin Q).SeparatingLeft := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
  ext y
  simpa using hx (Submodule.Quotient.mk y)

variable {Q}

/-- An orthogonal automorphism maps the polar kernel onto itself. -/
theorem map_ker_polarBilin_of_mem_orthogonalGroup {g : M ≃ₗ[R] M} (hg : g ∈ orthogonalGroup Q) :
    (LinearMap.ker (polarBilin Q)).map (g : M →ₗ[R] M) = LinearMap.ker (polarBilin Q) := by
  have key {f : M ≃ₗ[R] M} (hf : f ∈ orthogonalGroup Q) :
      (LinearMap.ker (polarBilin Q)).map (f : M →ₗ[R] M) ≤ LinearMap.ker (polarBilin Q) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.ext_iff, polarBilin_apply_apply,
      LinearMap.zero_apply] at hx ⊢
    intro y
    rw [LinearEquiv.coe_coe, ← f.apply_symm_apply y, polar_apply_of_mem_orthogonalGroup hf]
    exact hx (f.symm y)
  refine le_antisymm (key hg) fun x hx ↦ ⟨g.symm x, ?_, by simp⟩
  have h := key (inv_mem hg) ⟨x, hx, rfl⟩
  simpa using h

variable (Q)

/-- **The action of the orthogonal group on the quotient by the polar kernel**: an orthogonal
automorphism `g` of `Q` induces the isometry `x + K ↦ g x + K` of `polarQuotientBilin Q`, where
`K` is the kernel of the polar form. -/
noncomputable def orthogonalGroupToPolarQuotient :
    orthogonalGroup Q →* (polarQuotientBilin Q).isometryGroup where
  toFun g := ⟨Submodule.Quotient.equiv _ _ (g : M ≃ₗ[R] M)
      (map_ker_polarBilin_of_mem_orthogonalGroup g.property),
    LinearMap.mem_isometryGroup_iff.mpr fun x y ↦ by
    induction x using Submodule.Quotient.induction_on with | H x => ?_
    induction y using Submodule.Quotient.induction_on with | H y => ?_
    simp [polar_apply_of_mem_orthogonalGroup g.property]⟩
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with | H x => ?_
    simp
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with | H x => ?_
    simp

/-- The induced isometry sends the class of `x` to the class of `g x`. -/
@[simp]
theorem orthogonalGroupToPolarQuotient_apply_mk (g : orthogonalGroup Q) (x : M) :
    ((orthogonalGroupToPolarQuotient Q g : (polarQuotientBilin Q).isometryGroup) :
        (M ⧸ LinearMap.ker (polarBilin Q)) ≃ₗ[R] (M ⧸ LinearMap.ker (polarBilin Q)))
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((g : M ≃ₗ[R] M) x) :=
  (rfl)

/-- An orthogonal automorphism acts trivially on the quotient by the polar kernel exactly when it
moves every vector by an element of that kernel. -/
theorem mem_ker_orthogonalGroupToPolarQuotient_iff {g : orthogonalGroup Q} :
    g ∈ (orthogonalGroupToPolarQuotient Q).ker ↔
      ∀ x, (g : M ≃ₗ[R] M) x - x ∈ LinearMap.ker (polarBilin Q) := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff, LinearEquiv.ext_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa [Submodule.Quotient.eq] using h (Submodule.Quotient.mk x)
  · induction x using Submodule.Quotient.induction_on with | H x => ?_
    simpa [Submodule.Quotient.eq] using h x

end QuadraticMap
