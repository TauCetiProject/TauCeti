/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Algebra.Category.FGModuleCat.Rigid
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.InvariantForm
import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.RepresentationTheory.Dual

/-!
# Determinant alternating forms and self-duality in rank two

Given a two-element basis `b : Module.Basis (Fin 2) R V` of a free module over a commutative ring
`R`, the determinant alternating map `b.det` in two variables defines an alternating bilinear form
`b.detBilinForm` with `b.detBilinForm x y = b.det ![x, y]`. In coordinates with respect to `b` this
is the `2 × 2` determinant `x₀ y₁ - y₀ x₁`, which is unimodular over every commutative ring:
`x ↦ b.detBilinForm x` is bijective onto `Module.Dual R V` and in particular nondegenerate.

For a representation `ρ : Representation R G V` of a monoid `G` whose elements act with determinant
`1`, `b.det_comp` shows that `b.detBilinForm` is `G`-invariant. When `G` is a group, this unimodular
invariant form intertwines `ρ` with its contragredient `ρ.dual`, yielding an explicit self-duality
`Module.Basis.equivDualOfDetEqOne` over any commutative ring, and hence
`Representation.equivDualOfFinrankEqTwo` for any two-dimensional representation of
determinant `1` over a field.

In `FDRep k G`, `FDRep.leftDualIso` identifies the categorical left dual `ᘁV` with
`FDRep.of (Representation.dual V.ρ)`. Any self-duality `V.ρ.Equiv (Representation.dual V.ρ)`
therefore induces an isomorphism `V ≅ ᘁV` and, by Frobenius reciprocity
(`TauCeti.tensorLeftHomLinearEquiv`), a `k`-linear equivalence `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)`.
Combining this with `FDRep.finrank_hom_comm` when `|G|` is invertible in `k` gives the symmetry
`dim Hom_G(X, V ⊗ Y) = dim Hom_G(Y, V ⊗ X)` of the tensor multiplicity pairing
(`FDRep.finrank_hom_tensor_comm_of_equiv_dual`, specialized to rank two in
`FDRep.finrank_hom_tensor_comm_of_finrank_eq_two`).

Note that determinant `1` is genuinely required for rank-two self-duality in general: the
representation `g ↦ diag(g, 1)` of `ℂˣ` on `ℂ²` has determinant `g` and is not isomorphic to its
dual `g ↦ diag(g⁻¹, 1)`.

## Main definitions

* `Module.Basis.detBilinForm`: the alternating bilinear form `(x, y) ↦ b.det ![x, y]` of a
  `Fin 2`-basis `b`.
* `Module.Basis.detBilinFormEquivDual`: the `R`-linear equivalence `V ≃ₗ[R] Module.Dual R V` induced
  by `b.detBilinForm`.
* `Module.Basis.equivDualOfDetEqOne` and `Representation.equivDualOfFinrankEqTwo`:
  self-duality `ρ.Equiv ρ.dual` of a rank-two representation of determinant `1`.
* `FDRep.leftDualIso`: the canonical isomorphism `ᘁV ≅ FDRep.of (Representation.dual V.ρ)` in
  `FDRep k G`.
* `FDRep.isoLeftDualOfEquivDual`: the isomorphism `V ≅ ᘁV` attached to
  `V.ρ.Equiv (Representation.dual V.ρ)`.
* `FDRep.tensorLeftHomLinearEquivOfEquivDual`: Frobenius reciprocity `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)`
  along a self-duality of `V`.

## Main results

* `Module.Basis.isAlt_detBilinForm`, `Module.Basis.bijective_detBilinForm`, and
  `Module.Basis.nondegenerate_detBilinForm`: alternation, unimodularity, and nondegeneracy of
  `b.detBilinForm`.
* `Module.Basis.isInvariantForm_detBilinForm`: `G`-invariance when `∀ g, LinearMap.det (ρ g) = 1`.
* `FDRep.finrank_hom_tensor_comm_of_equiv_dual` and
  `FDRep.finrank_hom_tensor_comm_of_finrank_eq_two`: symmetry of `dim_k (X ⟶ V ⊗ Y)` when `|G|` is
  invertible in `k`.
-/

public section

open CategoryTheory MonoidalCategory

universe u v w

namespace Module.Basis

section CommRing

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
  (b : Basis (Fin 2) R V)

/-- The alternating bilinear form `(x, y) ↦ b.det ![x, y]` attached to a two-element basis `b`. -/
noncomputable def detBilinForm : LinearMap.BilinForm R V :=
  b.det.toMultilinearMap.toBilinMap

@[simp]
theorem detBilinForm_apply (x y : V) : b.detBilinForm x y = b.det ![x, y] :=
  MultilinearMap.toBilinMap_apply b.det.toMultilinearMap x y

/-- In coordinates with respect to `b`, `b.detBilinForm x y` is `x₀ y₁ - y₀ x₁`. -/
theorem detBilinForm_eq_repr (x y : V) :
    b.detBilinForm x y = b.repr x 0 * b.repr y 1 - b.repr y 0 * b.repr x 1 := by
  rw [detBilinForm_apply, b.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]

/-- The determinant bilinear form of a `Fin 2`-basis is alternating. -/
theorem isAlt_detBilinForm : b.detBilinForm.IsAlt :=
  b.det.isAlt_toBilinMap

/-- Evaluating `b.detBilinForm` on `(b 0, b 1)` yields `1`. -/
theorem detBilinForm_basis_zero_one : b.detBilinForm (b 0) (b 1) = 1 := by
  rw [detBilinForm_eq_repr]
  simp

/-- Evaluating `b.detBilinForm` on `(b 1, b 0)` yields `-1`. -/
theorem detBilinForm_basis_one_zero : b.detBilinForm (b 1) (b 0) = -1 := by
  rw [detBilinForm_eq_repr]
  simp

/-- Pairing against `b 1` on the right reads off the `0`-th coordinate in `b`. -/
theorem detBilinForm_apply_basis_one (x : V) : b.detBilinForm x (b 1) = b.repr x 0 := by
  rw [detBilinForm_eq_repr]
  simp

/-- Pairing against `b 0` on the right reads off minus the `1`-st coordinate in `b`. -/
theorem detBilinForm_apply_basis_zero (x : V) : b.detBilinForm x (b 0) = -b.repr x 1 := by
  rw [detBilinForm_eq_repr]
  simp

/-- **Unimodularity of the `Fin 2` determinant form.** Over every commutative ring `R`,
`x ↦ b.detBilinForm x` is a bijection `V → Module.Dual R V`, with inverse
`φ ↦ φ (b 1) • b 0 - φ (b 0) • b 1`. -/
theorem bijective_detBilinForm : Function.Bijective b.detBilinForm := by
  refine ⟨fun x y hxy ↦ b.repr.injective ?_, fun φ ↦ ⟨φ (b 1) • b 0 - φ (b 0) • b 1, ?_⟩⟩
  · refine Finsupp.ext <| Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [← detBilinForm_apply_basis_one, ← detBilinForm_apply_basis_one]
      exact LinearMap.congr_fun hxy (b 1)
    · have h0 := LinearMap.congr_fun hxy (b 0)
      rw [detBilinForm_apply_basis_zero, detBilinForm_apply_basis_zero] at h0
      exact neg_inj.mp h0
  · refine b.ext <| Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [detBilinForm_apply_basis_zero]
      simp
    · rw [detBilinForm_apply_basis_one]
      simp

/-- The `R`-linear equivalence `V ≃ₗ[R] Module.Dual R V` induced by `b.detBilinForm`. -/
noncomputable def detBilinFormEquivDual : V ≃ₗ[R] Module.Dual R V :=
  LinearEquiv.ofBijective b.detBilinForm b.bijective_detBilinForm

@[simp]
theorem detBilinFormEquivDual_apply (x y : V) :
    b.detBilinFormEquivDual x y = b.detBilinForm x y :=
  (rfl)

/-- The determinant bilinear form of a `Fin 2`-basis is nondegenerate over every commutative
ring. -/
theorem nondegenerate_detBilinForm : b.detBilinForm.Nondegenerate := by
  refine ⟨fun x hx ↦ b.bijective_detBilinForm.1 ?_, fun y hy ↦ b.bijective_detBilinForm.1 ?_⟩
  · rw [map_zero]
    exact LinearMap.ext hx
  · rw [map_zero]
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.zero_apply, ← b.isAlt_detBilinForm.neg_eq x y, hy x, neg_zero]

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
  .mk b.detBilinFormEquivDual fun g ↦ LinearMap.ext fun v ↦
    ((TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap ρ b.detBilinForm).mp
      (b.isInvariantForm_detBilinForm ρ hdet)).isIntertwining g v

@[simp]
theorem equivDualOfDetEqOne_apply {G : Type w} [Group G] (ρ : Representation R G V)
    (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) (x y : V) :
    b.equivDualOfDetEqOne ρ hdet x y = b.detBilinForm x y :=
  (rfl)

end CommRing

end Module.Basis

namespace Representation

/-- **Every two-dimensional representation of determinant `1` over a field is self-dual.** -/
noncomputable def equivDualOfFinrankEqTwo {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (hdim : Module.finrank k V = 2) (hdet : ∀ g : G, LinearMap.det (ρ g) = 1) :
    ρ.Equiv ρ.dual :=
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  (Module.finBasisOfFinrankEq k V hdim).equivDualOfDetEqOne ρ hdet

end Representation

namespace FDRep

section Field

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **The categorical left dual `ᘁV` in `FDRep k G` is `FDRep.of (Representation.dual V.ρ)`.** Both
have underlying vector space `Module.Dual k V`, and the left dual action `ᘁ(V.ρ g⁻¹)` in
`FGModuleCat k` is the transpose `(V.ρ g⁻¹).dualMap` (`FGModuleCat.leftAdjointMate_hom`). -/
protected noncomputable def leftDualIso (V : FDRep k G) :
    (ᘁV : FDRep k G) ≅ FDRep.of (Representation.dual V.ρ) :=
  (LinearEquiv.refl k (Module.Dual k V)).toFDRepIso fun g φ ↦ by
    have hρ := congrArg (fun f : (ᘁV.V) ⟶ ᘁV.V ↦ f.hom.hom φ) (Action.leftDual_ρ V g)
    rw [FGModuleCat.leftAdjointMate_hom, FDRep.hom_hom_action_ρ] at hρ
    exact hρ

/-- **An equivalence `V.ρ.Equiv (Representation.dual V.ρ)` makes `V` isomorphic to its categorical
left dual `ᘁV` in `FDRep k G`.** -/
noncomputable def isoLeftDualOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) :
    V ≅ (ᘁV : FDRep k G) :=
  (e.toLinearEquiv.toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ']
      exact LinearMap.congr_fun (e.isIntertwining' g) x) ≪≫
    (FDRep.leftDualIso V).symm

/-- **Frobenius reciprocity `(V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y)` along a self-duality of `V`.** -/
noncomputable def tensorLeftHomLinearEquivOfEquivDual {V : FDRep k G}
    (e : _root_.Representation.Equiv V.ρ (Representation.dual V.ρ)) (X Y : FDRep k G) :
    (V ⊗ X ⟶ Y) ≃ₗ[k] (X ⟶ V ⊗ Y) :=
  (TauCeti.tensorLeftHomLinearEquiv k X (ᘁV) V Y).trans
    (Linear.homCongr k (Iso.refl X) (whiskerRightIso (isoLeftDualOfEquivDual e).symm Y))

/-- **Symmetry of tensor multiplicities for a self-dual representation.** When `|G|` is invertible
in `k` and `V` is self-dual, `dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ V ⊗ X)` for all `X, Y : FDRep k G`. -/
theorem finrank_hom_tensor_comm_of_equiv_dual [Invertible (Nat.card G : k)] {V : FDRep k G}
    (he : Nonempty (_root_.Representation.Equiv V.ρ (Representation.dual V.ρ)))
    (X Y : FDRep k G) :
    Module.finrank k (X ⟶ V ⊗ Y) = Module.finrank k (Y ⟶ V ⊗ X) := by
  obtain ⟨e⟩ := he
  rw [← (tensorLeftHomLinearEquivOfEquivDual e X Y).finrank_eq, FDRep.finrank_hom_comm]

/-- **Symmetry of tensor multiplicities for a two-dimensional representation of determinant `1`.**
When `|G|` is invertible in `k`, `dim_k V = 2`, and `∀ g, det (V.ρ g) = 1`, we have
`dim_k (X ⟶ V ⊗ Y) = dim_k (Y ⟶ V ⊗ X)`. -/
theorem finrank_hom_tensor_comm_of_finrank_eq_two [Invertible (Nat.card G : k)] {V : FDRep k G}
    (hdim : Module.finrank k V = 2) (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1)
    (X Y : FDRep k G) :
    Module.finrank k (X ⟶ V ⊗ Y) = Module.finrank k (Y ⟶ V ⊗ X) :=
  finrank_hom_tensor_comm_of_equiv_dual
    ⟨Representation.equivDualOfFinrankEqTwo V.ρ hdim hdet⟩ X Y

end Field

end FDRep
