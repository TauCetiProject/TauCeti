/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Isotropic, coisotropic, and Lagrangian subspaces of a symplectic form

A symplectic form `ω` on a real module gives every submodule `L` a *symplectic complement*
`L^ω = {x | ∀ y ∈ L, ω(y, x) = 0}`, the orthogonal complement for the bilinear form `ω`. The three
standard size conditions on `L` relative to its complement organize the whole subject:

* `L` is **isotropic** when `L ≤ L^ω`, equivalently `ω` vanishes on `L × L`;
* `L` is **coisotropic** when `L^ω ≤ L`;
* `L` is **Lagrangian** when `L^ω = L`, i.e. isotropic and coisotropic at once.

Lagrangian subspaces are the linear model for the boundary conditions of Lagrangian Floer homology
(Lane F3 of the analytic Heegaard Floer roadmap) and for the totally real tori in `Sym^g(Σ)`
(Lane F4): the roadmap keeps *totally real* and *Lagrangian* as separate named hypotheses, so this
file builds the Lagrangian notion on the symplectic form `ω` rather than on an almost complex
structure. The two meet on the standard model `V × V`: its coordinate factors `V × {0}` and
`{0} × V` are simultaneously maximal totally real
(`TauCeti.Submodule.isMaximalTotallyReal_prod_top_bot_product` and
`TauCeti.Submodule.isMaximalTotallyReal_prod_bot_top_product`) and Lagrangian
(`TauCeti.SymplecticForm.stdSymplecticForm_isLagrangian_prod_top_bot` and
`TauCeti.SymplecticForm.stdSymplecticForm_isLagrangian_prod_bot_top`), proved in
`TauCeti.Geometry.Symplectic.StandardLagrangian`.

This is the pointwise linear-algebra layer, with no topology or smoothness bundled, built directly
on Mathlib's bilinear-form orthogonal complement
(`Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`). Mathlib has the complement and its
dimension count but no isotropic/Lagrangian vocabulary, which this file supplies.

## Main declarations

* `TauCeti.SymplecticForm.orthogonal`: the symplectic complement `L^ω`.
* `TauCeti.SymplecticForm.IsIsotropic`, `IsCoisotropic`, `IsLagrangian`: the three size predicates.
* `TauCeti.SymplecticForm.isIsotropic_iff`: isotropy is the vanishing of `ω` on `L × L`.
* `TauCeti.SymplecticForm.isLagrangian_iff`: Lagrangian is isotropic and coisotropic.
* `TauCeti.SymplecticForm.IsLagrangian.two_mul_finrank`: a Lagrangian subspace is half-dimensional,
  `2 · dim L = dim V`, and `IsIsotropic.isLagrangian_of_finrank` is the converse for an isotropic
  subspace of half the dimension.

The standard model `V × V` and the Lagrangian-ness of its coordinate factors live in the companion
file `TauCeti.Geometry.Symplectic.StandardLagrangian`, which depends on the inner-product structure
of the standard symplectic form.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.3.
-/

namespace TauCeti

namespace SymplecticForm

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {L L' : Submodule ℝ V}

/-- The symplectic complement `L^ω = {x | ∀ y ∈ L, ω(y, x) = 0}` of a submodule `L`, namely the
orthogonal complement of `L` for the bilinear form `ω`. -/
def orthogonal (ω : SymplecticForm V) (L : Submodule ℝ V) : Submodule ℝ V :=
  ω.toBilinForm.orthogonal L

lemma orthogonal_def (ω : SymplecticForm V) (L : Submodule ℝ V) :
    ω.orthogonal L = ω.toBilinForm.orthogonal L := rfl

@[simp]
lemma mem_orthogonal_iff {x : V} : x ∈ ω.orthogonal L ↔ ∀ y ∈ L, ω y x = 0 := Iff.rfl

/-- Membership in the symplectic complement, tested on the left argument of `ω`. -/
lemma mem_orthogonal_iff' {x : V} : x ∈ ω.orthogonal L ↔ ∀ y ∈ L, ω x y = 0 := by
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · have := h y hy
    linarith [ω.neg_eq x y]
  · have := h y hy
    linarith [ω.neg_eq y x]

/-- The symplectic complement is antitone: a larger subspace has a smaller complement. -/
lemma orthogonal_le (h : L ≤ L') : ω.orthogonal L' ≤ ω.orthogonal L :=
  ω.toBilinForm.orthogonal_le h

/-- A subspace is contained in the complement of its complement. -/
lemma le_orthogonal_orthogonal : L ≤ ω.orthogonal (ω.orthogonal L) :=
  ω.toBilinForm.le_orthogonal_orthogonal ω.isRefl

/-- The complement of the zero subspace is the whole space. -/
@[simp]
lemma orthogonal_bot : ω.orthogonal (⊥ : Submodule ℝ V) = ⊤ :=
  ω.toBilinForm.orthogonal_bot

/-- The complement of the whole space is the zero subspace, since `ω` is nondegenerate. -/
@[simp]
lemma orthogonal_top : ω.orthogonal (⊤ : Submodule ℝ V) = ⊥ :=
  ω.toBilinForm.orthogonal_top_eq_bot ω.nondegenerate

/-- A submodule is isotropic if it is contained in its symplectic complement, equivalently `ω`
vanishes on it. -/
def IsIsotropic (ω : SymplecticForm V) (L : Submodule ℝ V) : Prop :=
  L ≤ ω.orthogonal L

/-- A submodule is coisotropic if it contains its symplectic complement. -/
def IsCoisotropic (ω : SymplecticForm V) (L : Submodule ℝ V) : Prop :=
  ω.orthogonal L ≤ L

/-- Coisotropy unfolds to its defining containment of the symplectic complement. -/
lemma isCoisotropic_iff : ω.IsCoisotropic L ↔ ω.orthogonal L ≤ L := Iff.rfl

/-- A coisotropic subspace contains its symplectic complement. -/
lemma IsCoisotropic.orthogonal_le (h : ω.IsCoisotropic L) : ω.orthogonal L ≤ L := h

/-- A submodule is Lagrangian if it equals its own symplectic complement. -/
def IsLagrangian (ω : SymplecticForm V) (L : Submodule ℝ V) : Prop :=
  ω.orthogonal L = L

/-- Isotropy is the vanishing of the symplectic form on the subspace. -/
lemma isIsotropic_iff : ω.IsIsotropic L ↔ ∀ v ∈ L, ∀ w ∈ L, ω v w = 0 := by
  constructor
  · intro h v hv w hw
    have hwv : ω w v = 0 := (mem_orthogonal_iff.1 (h hv)) w hw
    linarith [ω.neg_eq v w]
  · intro h v hv
    rw [mem_orthogonal_iff]
    intro y hy
    exact h y hy v hv

/-- A subspace of an isotropic subspace is isotropic. -/
lemma IsIsotropic.mono (h : ω.IsIsotropic L') (hL : L ≤ L') : ω.IsIsotropic L :=
  isIsotropic_iff.2 fun v hv w hw => isIsotropic_iff.1 h v (hL hv) w (hL hw)

/-- The zero subspace is isotropic. -/
@[simp]
lemma isIsotropic_bot : ω.IsIsotropic (⊥ : Submodule ℝ V) :=
  isIsotropic_iff.2 fun v hv => by simp [(Submodule.mem_bot ℝ).1 hv]

/-- The whole space is coisotropic. -/
@[simp]
lemma isCoisotropic_top : ω.IsCoisotropic (⊤ : Submodule ℝ V) :=
  le_top

/-- A Lagrangian subspace is both isotropic and coisotropic, and conversely. -/
lemma isLagrangian_iff : ω.IsLagrangian L ↔ ω.IsIsotropic L ∧ ω.IsCoisotropic L := by
  rw [IsLagrangian, IsIsotropic, IsCoisotropic, le_antisymm_iff, and_comm]

/-- A Lagrangian subspace is isotropic. -/
lemma IsLagrangian.isIsotropic (h : ω.IsLagrangian L) : ω.IsIsotropic L :=
  (isLagrangian_iff.1 h).1

/-- A Lagrangian subspace is coisotropic. -/
lemma IsLagrangian.isCoisotropic (h : ω.IsLagrangian L) : ω.IsCoisotropic L :=
  (isLagrangian_iff.1 h).2

/-- The symplectic form vanishes on a Lagrangian subspace. -/
lemma IsLagrangian.symplecticForm_apply_eq_zero (h : ω.IsLagrangian L) {v w : V}
    (hv : v ∈ L) (hw : w ∈ L) : ω v w = 0 :=
  isIsotropic_iff.1 h.isIsotropic v hv w hw

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- The symplectic complement has complementary dimension: `dim L^ω = dim V - dim L`. -/
lemma finrank_orthogonal (ω : SymplecticForm V) (L : Submodule ℝ V) :
    finrank ℝ (ω.orthogonal L) = finrank ℝ V - finrank ℝ L :=
  ω.toBilinForm.finrank_orthogonal ω.nondegenerate L

/-- The double complement of a subspace is itself. -/
lemma orthogonal_orthogonal (ω : SymplecticForm V) (L : Submodule ℝ V) :
    ω.orthogonal (ω.orthogonal L) = L :=
  ω.toBilinForm.orthogonal_orthogonal ω.nondegenerate ω.isRefl L

/-- An isotropic subspace has at most half the dimension of the ambient space. -/
lemma IsIsotropic.two_mul_finrank_le (h : ω.IsIsotropic L) :
    2 * finrank ℝ L ≤ finrank ℝ V := by
  have hle : finrank ℝ L ≤ finrank ℝ (ω.orthogonal L) := Submodule.finrank_mono h
  rw [finrank_orthogonal] at hle
  have := L.finrank_le
  omega

/-- A Lagrangian subspace is exactly half-dimensional: `2 · dim L = dim V`. -/
lemma IsLagrangian.two_mul_finrank (h : ω.IsLagrangian L) :
    2 * finrank ℝ L = finrank ℝ V := by
  have hf : finrank ℝ (ω.orthogonal L) = finrank ℝ L := by rw [h]
  rw [finrank_orthogonal] at hf
  have := L.finrank_le
  omega

/-- An isotropic subspace of half the dimension of the ambient space is Lagrangian. -/
lemma IsIsotropic.isLagrangian_of_finrank (h : ω.IsIsotropic L)
    (hdim : 2 * finrank ℝ L = finrank ℝ V) : ω.IsLagrangian L := by
  refine (Submodule.eq_of_le_of_finrank_eq h ?_).symm
  rw [finrank_orthogonal]
  omega

end FiniteDimensional

end SymplecticForm

end TauCeti
