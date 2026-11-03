/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Lie.Basic

/-!
# The Kirillov–Kostant–Souriau form on a coadjoint tangent space

A Lie algebra `L` over a commutative ring `R` acts on its dual `L* = Module.Dual R L` by the
coadjoint action `⁅ξ, ν⁆ = -ν ∘ ad ξ` (Mathlib's `Module.Dual.instLieRingModule`). Fix `ν ∈ L*` and
let `L_ν = {ξ | ⁅ξ, ν⁆ = 0}` be its stabilizer (`TauCeti.lieAnnihilator R L ν`). Everything in this
file is linear algebra: the quotient `L ⧸ L_ν` is the **algebraic tangent model** of the coadjoint
orbit through `ν`, and the injective map `[ξ] ↦ ⁅ξ, ν⁆` from `L ⧸ L_ν` onto `L · ν ⊆ L*`
(`Module.Dual.coadjointTangentMap ν`) is its algebraic orbit derivative.

These names carry their geometric meaning only when `L` is the Lie algebra of a Lie group `G`
whose coadjoint orbit through `ν` is a smooth homogeneous space `G / G_ν` (for instance a real
finite-dimensional Lie group). In that case the coadjoint action is the derivative of
`ν ↦ ν ∘ Ad_(g⁻¹)`, the derivative at the identity of the orbit map `g ↦ g · ν` is `ξ ↦ ⁅ξ, ν⁆` on
`L` with kernel `L_ν`, the tangent space of the orbit at `ν` is `L ⧸ L_ν`, and
`coadjointTangentMap ν` is the map induced on this quotient: the derivative at the identity coset
of the map `G / G_ν → L*`, `[g] ↦ g · ν`.

The **Kirillov form** `B_ν(ξ, η) = ν ⁅ξ, η⁆` on `L` (`Module.Dual.kirillovForm ν`) is alternating,
and its kernel is exactly the stabilizer `L_ν` (`Module.Dual.ker_kirillovForm`). It therefore
descends to the **Kirillov–Kostant–Souriau form**

`ω_ν([ξ], [η]) = ν ⁅ξ, η⁆`

on `L ⧸ L_ν` (`Module.Dual.kksForm ν`), which is alternating and nondegenerate. This holds over an
arbitrary commutative ring and with no finiteness assumption, so the algebraic tangent model at
every `ν` carries a nondegenerate alternating bilinear form. With trivial coefficients the
Kirillov form is minus the Chevalley–Eilenberg coboundary of `ν` (compare Mathlib's
`LieModule.Cohomology.d₁₂`); it is stated directly here because `R` carries no trivial `L`-module
instance.

Two identities of `ω_ν` are, under the geometric hypotheses above, the pointwise content of the
facts that the coadjoint orbit is a Hamiltonian space with closed form:

* contraction of `ω_ν` with the generator `[ξ]` is evaluation at `ξ` after the orbit derivative
  (`Module.Dual.kksForm_mk_left`): this is the moment map equation `ι_(ξ_O) ω = d⟨ι, ξ⟩` at `ν`
  for the inclusion `ι` of the orbit into `L*`;
* the cyclic sum of `ω_ν([⁅ξ, η⁆], [ζ])` vanishes (`Module.Dual.kksForm_jacobi`), which is the
  Jacobi identity and gives closedness of the invariant form on the orbit.

## Main definitions

* `Module.Dual.kirillovForm ν`: the bilinear form `ν ⁅ξ, η⁆` on `L`.
* `Module.Dual.coadjointTangentMap ν`: the injection `[ξ] ↦ ⁅ξ, ν⁆` of `L ⧸ L_ν` into `L*`.
* `Module.Dual.kksForm ν`: the Kirillov–Kostant–Souriau form on `L ⧸ L_ν`.

## Main results

* `Module.Dual.ker_kirillovForm`: the kernel of the Kirillov form is the stabilizer `L_ν`.
* `Module.Dual.coadjointTangentMap_injective`: the orbit derivative is injective.
* `Module.Dual.isAlt_kksForm`, `Module.Dual.kksForm_nondegenerate`: `ω_ν` is alternating and
  nondegenerate.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.
-/

public section

open Module TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Module.Dual

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (ν : Dual R L)

/-- The **Kirillov form** `B_ν(ξ, η) = ν ⁅ξ, η⁆` of a linear functional `ν` on a Lie algebra. Its
kernel is the coadjoint stabilizer of `ν` (`Module.Dual.ker_kirillovForm`). -/
def kirillovForm : LinearMap.BilinForm R L :=
  (LieAlgebra.ad R L).toLinearMap.compr₂ ν

@[simp]
theorem kirillovForm_apply (ξ η : L) : ν.kirillovForm ξ η = ν ⁅ξ, η⁆ :=
  (rfl)

/-- The Kirillov form is alternating. -/
theorem isAlt_kirillovForm : ν.kirillovForm.IsAlt := fun ξ ↦ by
  rw [kirillovForm_apply, lie_self, map_zero]

/-- The Kirillov form of `ν` pairs `ξ` with `η` to `-⁅ξ, ν⁆ η`. -/
theorem kirillovForm_eq_neg_lie_apply (ξ η : L) : ν.kirillovForm ξ η = -(⁅ξ, ν⁆ : Dual R L) η := by
  rw [kirillovForm_apply, Dual.lie_apply, neg_neg]

/-- The kernel of the Kirillov form `ν ⁅ξ, η⁆` is the coadjoint stabilizer `L_ν` of `ν`. -/
theorem ker_kirillovForm :
    LinearMap.ker ν.kirillovForm = (lieAnnihilator R L ν).toSubmodule := by
  ext ξ
  simp only [LinearMap.mem_ker, LieSubalgebra.mem_toSubmodule, mem_lieAnnihilator,
    LinearMap.ext_iff, kirillovForm_eq_neg_lie_apply, LinearMap.zero_apply, neg_eq_zero]

/-- The algebraic orbit derivative `[ξ] ↦ ⁅ξ, ν⁆`, identifying the algebraic tangent model
`L ⧸ L_ν` with the subspace `L · ν = {⁅ξ, ν⁆}` of `L*`. When `L` integrates to a Lie group `G` whose
coadjoint orbit through `ν` is a smooth homogeneous space `G / G_ν`, this is the map induced on
`L ⧸ L_ν` by the derivative `ξ ↦ ⁅ξ, ν⁆` at the identity of the orbit map `g ↦ Ad*_g ν`, that is,
the derivative at the identity coset of the map `G / G_ν → L*`, `[g] ↦ Ad*_g ν`. -/
def coadjointTangentMap : (L ⧸ (lieAnnihilator R L ν).toSubmodule) →ₗ[R] Dual R L :=
  (lieAnnihilator R L ν).toSubmodule.liftQ
    ((LieModule.toEnd R L (Dual R L)).toLinearMap.flip ν)
    fun _ hξ ↦ (mem_lieAnnihilator R L).mp hξ

@[simp]
theorem coadjointTangentMap_mk (ξ : L) :
    ν.coadjointTangentMap (Submodule.Quotient.mk ξ) = ⁅ξ, ν⁆ :=
  (rfl)

/-- The orbit derivative `[ξ] ↦ ⁅ξ, ν⁆` is injective: the map `ξ ↦ ⁅ξ, ν⁆` on `L` has kernel the
stabilizer `L_ν`, so the induced map on `L ⧸ L_ν` is injective. -/
theorem coadjointTangentMap_injective : Function.Injective ν.coadjointTangentMap :=
  LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _
    fun _ hξ ↦ (mem_lieAnnihilator R L).mpr hξ

/-- The **Kirillov–Kostant–Souriau form** on the algebraic tangent model `L ⧸ L_ν` of the coadjoint
orbit through `ν`, the descent of the Kirillov form: `ω_ν([ξ], [η]) = ν ⁅ξ, η⁆`
(`Module.Dual.kksForm_mk`). -/
def kksForm : LinearMap.BilinForm R (L ⧸ (lieAnnihilator R L ν).toSubmodule) :=
  ν.isAlt_kirillovForm.isRefl.liftQ₂ ν.kirillovForm _ ν.ker_kirillovForm.ge

/-- The defining formula `ω_ν([ξ], [η]) = ν ⁅ξ, η⁆` of the Kirillov–Kostant–Souriau form. -/
@[simp]
theorem kksForm_mk (ξ η : L) :
    ν.kksForm (Submodule.Quotient.mk ξ) (Submodule.Quotient.mk η) = ν ⁅ξ, η⁆ :=
  (rfl)

/-- Contracting the Kirillov–Kostant–Souriau form with the generator `[ξ]` is evaluation at `ξ`
after the algebraic orbit derivative. When the coadjoint orbit through `ν` is a smooth homogeneous
space of a Lie group integrating `L`, this is the moment map equation `ι_(ξ_O) ω = d⟨ι, ξ⟩` at `ν`
for the inclusion `ι` of the orbit into `L*`, whose derivative is `coadjointTangentMap ν`. -/
theorem kksForm_mk_left (ξ : L) (y : L ⧸ (lieAnnihilator R L ν).toSubmodule) :
    ν.kksForm (Submodule.Quotient.mk ξ) y = ν.coadjointTangentMap y ξ := by
  induction y using Submodule.Quotient.induction_on with
  | H η => rw [kksForm_mk, coadjointTangentMap_mk, Dual.lie_apply, ← lie_skew, map_neg]

/-- The Kirillov–Kostant–Souriau form is alternating. -/
theorem isAlt_kksForm : ν.kksForm.IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H ξ => rw [kksForm_mk, ← kirillovForm_apply]; exact ν.isAlt_kirillovForm ξ

/-- The Kirillov–Kostant–Souriau form is nondegenerate, over any commutative ring and in any
dimension: if `ν ⁅ξ, η⁆ = 0` for every `η`, then `ξ` stabilizes `ν`. -/
theorem kksForm_nondegenerate : ν.kksForm.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft ν.isAlt_kksForm.isRefl).mpr ?_
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H ξ =>
    rw [Submodule.Quotient.mk_eq_zero, ← ker_kirillovForm, LinearMap.mem_ker]
    ext η
    rw [kirillovForm_apply, LinearMap.zero_apply, ← kksForm_mk]
    exact hx (Submodule.Quotient.mk η)

/-- The cyclic sum of the Kirillov–Kostant–Souriau form on brackets of generators vanishes. This
is the Jacobi identity, and it is the algebraic input to closedness of the invariant form on the
coadjoint orbit when that orbit is a smooth homogeneous space. -/
theorem kksForm_jacobi (ξ η ζ : L) :
    ν.kksForm (Submodule.Quotient.mk ⁅ξ, η⁆) (Submodule.Quotient.mk ζ) +
      ν.kksForm (Submodule.Quotient.mk ⁅η, ζ⁆) (Submodule.Quotient.mk ξ) +
        ν.kksForm (Submodule.Quotient.mk ⁅ζ, ξ⁆) (Submodule.Quotient.mk η) = 0 := by
  have skew (a b c : L) : ν ⁅⁅a, b⁆, c⁆ = -ν ⁅c, ⁅a, b⁆⁆ := by
    rw [← lie_skew ⁅a, b⁆ c, map_neg]
  simp only [kksForm_mk, skew]
  convert congrArg (fun x : L => -ν x) (lie_jacobi ξ η ζ) using 1 <;>
    simp only [map_add, map_zero, neg_zero]
  abel

end Module.Dual
