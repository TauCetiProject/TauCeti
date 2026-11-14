/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.LinearAlgebra.Determinant.Basic
public import TauCeti.RepresentationTheory.FDRep.Dual
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Determinant alternating forms and self-duality in rank two

For a representation `ρ : Representation R G V` of a monoid `G` on a free module with two-element
basis `b : Module.Basis (Fin 2) R V` over a commutative ring `R`, if every element of `G` acts with
determinant `1`, `b.det_comp` shows that the unimodular determinant bilinear form `b.detBilinForm`
(`TauCeti.LinearAlgebra.Determinant.Basic`) is `G`-invariant
(`Module.Basis.isInvariantForm_detBilinForm`).
When `G` is a group, `b.detBilinFormEquivDual` intertwines `ρ` with its contragredient `ρ.dual`,
yielding an explicit self-duality `Module.Basis.equivDualOfDetEqOne` over any commutative ring, and
hence `Representation.equivDualOfFinrankEqTwo` for any rank-two free representation of determinant
`1` over a commutative ring.

Combining `Representation.equivDualOfFinrankEqTwo` with
`FDRep.finrank_hom_tensor_comm_of_equiv_dual` (`TauCeti.RepresentationTheory.FDRep.Dual`) shows
that when `|G|` is invertible in a field `k`, a two-dimensional representation `V : FDRep k G` of
determinant `1` has symmetric tensor multiplicities `dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ V ⊗ X)`
(`FDRep.finrank_hom_tensor_comm_of_finrank_eq_two`).

Note that determinant `1` is genuinely required for rank-two self-duality in general: the
representation `g ↦ diag(g, 1)` of `ℂˣ` on `ℂ²` has determinant `g` and is not isomorphic to its
dual `g ↦ diag(g⁻¹, 1)`.

## Main definitions

* `Module.Basis.equivDualOfDetEqOne` and `Representation.equivDualOfFinrankEqTwo`:
  self-duality `ρ.Equiv ρ.dual` of a rank-two representation of determinant `1` over a commutative
  ring.

## Main results

* `Module.Basis.isInvariantForm_detBilinForm`: `G`-invariance of `b.detBilinForm` when
  `∀ g, LinearMap.det (ρ g) = 1`.
* `FDRep.finrank_hom_tensor_comm_of_finrank_eq_two`: symmetry of `dim_k (X ⟶ V ⊗ Y)` when `|G|` is
  invertible in `k`, `dim_k V = 2`, and `∀ g, det (V.ρ g) = 1`.
-/

public section

open CategoryTheory MonoidalCategory

universe u v w

namespace Module.Basis

section CommRing

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
  (b : Basis (Fin 2) R V)

/-- **Invariance of the determinant form.** For a monoid representation `ρ` whose elements act with
determinant `1`, `b.detBilinForm` is `G`-invariant. -/
theorem isInvariantForm_detBilinForm {G : Type w} [Monoid G] (ρ : Representation R G V)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) :
    TauCeti.Representation.IsInvariantForm ρ b.detBilinForm := by
  rw [TauCeti.Representation.isInvariantForm_iff]
  intro g x y
  have hcomp : (![ρ g x, ρ g y] : Fin 2 → V) = ρ g ∘ ![x, y] := by
    ext i
    fin_cases i <;> rfl
  rw [detBilinForm_apply, detBilinForm_apply, hcomp, b.det_comp, hdet g, one_mul]

/-- **Self-duality of a rank-two representation of determinant `1`**, constructed explicitly from a
`Fin 2`-basis over any commutative ring. -/
noncomputable def equivDualOfDetEqOne {G : Type w} [Group G] (ρ : Representation R G V)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) :
    ρ.Equiv ρ.dual :=
  .mk b.detBilinFormEquivDual fun g ↦ LinearMap.ext fun v ↦ by
    have hb : ∀ x, b.detBilinFormEquivDual x = b.detBilinForm x :=
      fun x ↦ LinearMap.ext (b.detBilinFormEquivDual_apply x)
    simpa [hb] using
      ((TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap ρ b.detBilinForm).mp
        (b.isInvariantForm_detBilinForm ρ hdet)).isIntertwining g v

@[simp]
theorem toLinearEquiv_equivDualOfDetEqOne {G : Type w} [Group G] (ρ : Representation R G V)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) :
    (b.equivDualOfDetEqOne ρ hdet).toLinearEquiv = b.detBilinFormEquivDual :=
  (rfl)

@[simp]
theorem equivDualOfDetEqOne_apply {G : Type w} [Group G] (ρ : Representation R G V)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) (x y : V) :
    b.equivDualOfDetEqOne ρ hdet x y = b.detBilinForm x y :=
  b.detBilinFormEquivDual_apply x y

@[simp]
theorem equivDualOfDetEqOne_symm_apply {G : Type w} [Group G] (ρ : Representation R G V)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) (φ : Module.Dual R V) :
    (b.equivDualOfDetEqOne ρ hdet).symm φ = φ (b 1) • b 0 - φ (b 0) • b 1 :=
  b.detBilinFormEquivDual_symm_apply φ

end CommRing

end Module.Basis

namespace Representation

/-- **Every rank-two free representation of determinant `1` over a commutative ring is
self-dual.** -/
noncomputable def equivDualOfFinrankEqTwo {R : Type u} {G : Type v} {V : Type w}
    [CommRing R] [Group G] [AddCommGroup V] [Module R V] [Module.Free R V]
    (ρ : Representation R G V) (hdim : Module.finrank R V = 2)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) :
    ρ.Equiv ρ.dual :=
  have : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with _ | hnt
    · have h1 : Module.finrank R V = 1 := Module.finrank_subsingleton
      omega
    · exact hnt
  have : Module.Finite R V := Module.finite_of_finrank_eq_succ hdim
  (Module.finBasisOfFinrankEq R V hdim).equivDualOfDetEqOne ρ hdet

end Representation

namespace FDRep

/-- **Symmetry of tensor multiplicities for a two-dimensional representation of determinant `1`.**
When `|G|` is invertible in `k`, `dim_k V = 2`, and `∀ g, det (V.ρ g) = 1`, we have
`dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ V ⊗ X)`. -/
theorem finrank_hom_tensor_comm_of_finrank_eq_two {k : Type u} {G : Type v} [Field k] [Group G]
    [Invertible (Nat.card G : k)] {V : FDRep k G} (hdim : Module.finrank k V = 2)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) (X Y : FDRep k G) :
    Module.finrank k (X ⟶ V ⊗ Y) = Module.finrank k (Y ⟶ V ⊗ X) :=
  finrank_hom_tensor_comm_of_equiv_dual
    ⟨Representation.equivDualOfFinrankEqTwo V.ρ hdim hdet⟩ X Y

end FDRep
