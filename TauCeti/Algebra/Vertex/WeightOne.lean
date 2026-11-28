/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Graded
public import TauCeti.Algebra.Vertex.Hom
public import Mathlib.Algebra.Lie.Basic
import TauCeti.Algebra.Vertex.Borcherds.Basic
import TauCeti.Algebra.Vertex.SkewSymmetry

/-!
# The Lie algebra on the weight-one space of a graded vertex algebra

Let `A` be a graded formal vertex algebra (`TauCeti.GradedFormalVertexAxioms`) on `V`, so that
`V = ⨁_p V_p` with `V_0 = R |0⟩` and `a₍ₙ₎ b ∈ V_{p+q-n-1}` for `a ∈ V_p`, `b ∈ V_q`. The zero
product `(a, b) ↦ a₍₀₎ b` maps `V_1 × V_1` into `V_{1+1-0-1} = V_1`
(`TauCeti.GradedFormalVertexAxioms.weightOneZeroProduct`). When `V` has unique divisibility, for
instance over a `ℚ`-algebra, it is a Lie bracket on `V_1`:

* it is alternating, by skew symmetry `a₍₀₎ b = -b₍₀₎ a + T (b₍₁₎ a) - ⋯`, in which
  `b₍₁₎ a ∈ V_0 = R |0⟩` is killed by `T` and the higher terms have negative weight;
* it satisfies the Leibniz rule, the case `m = n = 0` of the Borcherds commutator formula
  `[a₍ₘ₎, b₍ₙ₎] = ∑_j (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`.

This makes `V_1` a Lie algebra over `R` with `⁅x, y⁆ = x₍₀₎ y`, on its existing additive group
and module structure. A morphism of formal vertex algebras preserving weight one restricts to a
morphism of these Lie algebras (`TauCeti.GradedFormalVertexAxioms.weightOneLieHom`). For the
affine vertex algebra `V_κ(𝔤)`, graded by conformal weight, the weight-one space is `𝔤` itself,
with its own bracket, and for a Heisenberg vertex algebra it is abelian; neither grading is
constructed here.

## Main definitions

* `TauCeti.GradedFormalVertexAxioms.weightOneZeroProduct`: the bilinear zero product on `V_1`.
* `TauCeti.GradedFormalVertexAxioms.instLieRingGradingOne`,
  `TauCeti.GradedFormalVertexAxioms.instLieAlgebraGradingOne`: the Lie algebra structure on
  `V_1`.
* `TauCeti.GradedFormalVertexAxioms.weightOneLieHom`: the Lie algebra morphism induced on weight
  one by a morphism of formal vertex algebras preserving weight one.

## Main results

* `TauCeti.GradedFormalVertexAxioms.weightOneZeroProduct_skew`: `-(y₍₀₎ x) = x₍₀₎ y` on `V_1`.
* `TauCeti.GradedFormalVertexAxioms.weightOneZeroProduct_alternating`: `x₍₀₎ x = 0` on `V_1`.
* `TauCeti.GradedFormalVertexAxioms.weightOneZeroProduct_leibniz`:
  `x₍₀₎ (y₍₀₎ z) = (x₍₀₎ y)₍₀₎ z + y₍₀₎ (x₍₀₎ z)` on `V_1`.
* `TauCeti.GradedFormalVertexAxioms.coe_lie`: `⁅x, y⁆ = x₍₀₎ y`.
* `TauCeti.GradedFormalVertexAxioms.ncoeff_one_field_apply_comm` and
  `TauCeti.GradedFormalVertexAxioms.ncoeff_one_field_apply_mem_span_vacuum`: by contrast the
  first product `a₍₁₎ b` of weight-one states is symmetric and lands in `V_0 = R |0⟩`.

## References

* V. Kac, *Introduction to vertex algebras, Poisson vertex algebras, and integrable Hamiltonian
  PDE*, in *Perspectives in Lie theory*, Springer INdAM Ser. 19 (2017), equation (3.24),
  Proposition 4.5 and Theorem 4.1(a).
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace TauCeti.GradedFormalVertexAxioms

variable {R V W U : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U]
variable (A : GradedFormalVertexAxioms R V)

/-! ### The zero product on weight one -/

/-- The zero product of two weight-one states has weight one. -/
theorem ncoeff_zero_field_apply_mem_grading_one {a b : V} (ha : a ∈ A.grading 1)
    (hb : b ∈ A.grading 1) : ((A.field a)[[0]]) b ∈ A.grading 1 :=
  A.ncoeff_field_apply_mem_grading ha hb (by norm_num)

/-- The zero product `(x, y) ↦ x₍₀₎ y` on the weight-one space `V_1`, as a bilinear map. -/
def weightOneZeroProduct : A.grading 1 →ₗ[R] A.grading 1 →ₗ[R] A.grading 1 :=
  LinearMap.mk₂ R
    (fun x y ↦ ⟨((A.field x)[[0]]) y,
      A.ncoeff_zero_field_apply_mem_grading_one x.property y.property⟩)
    (fun x x' y ↦ Subtype.ext <| by simp)
    (fun r x y ↦ Subtype.ext <| by simp)
    (fun x y y' ↦ Subtype.ext <| by simp)
    (fun r x y ↦ Subtype.ext <| by simp)

/-- The zero product on weight one, evaluated in `V`: `x₍₀₎ y`. -/
@[simp]
theorem coe_weightOneZeroProduct_apply_apply (x y : A.grading 1) :
    (A.weightOneZeroProduct x y : V) = ((A.field x)[[0]]) y := (rfl)

/-- The first product of two weight-one states is a multiple of the vacuum: `a₍₁₎ b ∈ R |0⟩`. -/
theorem ncoeff_one_field_apply_mem_span_vacuum {a b : V} (ha : a ∈ A.grading 1)
    (hb : b ∈ A.grading 1) : ((A.field a)[[1]]) b ∈ R ∙ A.vacuum :=
  A.grading_zero ▸ A.ncoeff_field_apply_mem_grading ha hb (by norm_num)

variable [HasUniqueDiv V]

/-- Skew symmetry of the zero product on weight one: `-(y₍₀₎ x) = x₍₀₎ y`. -/
theorem weightOneZeroProduct_skew (x y : A.grading 1) :
    -A.weightOneZeroProduct y x = A.weightOneZeroProduct x y := by
  -- In `x₍₀₎ y = -y₍₀₎ x + T (y₍₁₎ x) - ⋯`, the term `y₍₁₎ x` has weight zero, so it is a
  -- multiple of the vacuum and `T` kills it; the products `y₍ₖ₎ x` with `k ≥ 2` vanish.
  have hT : A.translation (((A.field y)[[1]]) x) = 0 :=
    A.translation_apply_eq_zero_of_mem_grading_zero
      (A.ncoeff_field_apply_mem_grading y.property x.property (by norm_num))
  refine Subtype.ext ?_
  rw [Submodule.coe_neg, coe_weightOneZeroProduct_apply_apply,
    coe_weightOneZeroProduct_apply_apply,
    A.ncoeff_field_apply_eq_sum_ncoeff_field_apply_vacuum x y 0 2
      (fun k hk ↦ A.ncoeff_field_apply_eq_zero y.property x.property (by push_cast at hk ⊢; omega))]
  simp [sum_range_succ, ← A.translation_apply, hT]

/-- The zero product on weight one is alternating: `x₍₀₎ x = 0`. -/
@[simp]
theorem weightOneZeroProduct_alternating (x : A.grading 1) : A.weightOneZeroProduct x x = 0 := by
  refine Subtype.ext (nsmul_right_injective two_ne_zero ?_)
  have h := congrArg Subtype.val (A.weightOneZeroProduct_skew x x)
  rw [Submodule.coe_neg, neg_eq_iff_add_eq_zero] at h
  simpa [two_nsmul] using h

/-- The Leibniz rule for the zero product on weight one:
`x₍₀₎ (y₍₀₎ z) = (x₍₀₎ y)₍₀₎ z + y₍₀₎ (x₍₀₎ z)`. -/
theorem weightOneZeroProduct_leibniz (x y z : A.grading 1) :
    A.weightOneZeroProduct x (A.weightOneZeroProduct y z) =
      A.weightOneZeroProduct (A.weightOneZeroProduct x y) z +
        A.weightOneZeroProduct y (A.weightOneZeroProduct x z) :=
  Subtype.ext <| by simpa using A.ncoeff_zero_field_ncoeff_apply x y z 0

/-! ### The first product on weight one -/

/-- The first product is symmetric on weight one: `a₍₁₎ b = b₍₁₎ a`. Unlike the zero product, it
takes values in `V_0 = R |0⟩` (`ncoeff_one_field_apply_mem_span_vacuum`). -/
theorem ncoeff_one_field_apply_comm {a b : V} (ha : a ∈ A.grading 1) (hb : b ∈ A.grading 1) :
    ((A.field a)[[1]]) b = ((A.field b)[[1]]) a := by
  rw [A.ncoeff_field_apply_eq_sum_ncoeff_field_apply_vacuum a b 1 1
    (fun k hk ↦ A.ncoeff_field_apply_eq_zero hb ha (by push_cast at hk ⊢; omega))]
  simp [Int.negOnePow_even 2 even_two]

/-! ### The Lie algebra on weight one -/

/-- The Lie ring structure on the weight-one space `V_1`, with bracket `⁅x, y⁆ = x₍₀₎ y`. -/
instance instLieRingGradingOne : LieRing (A.grading 1) where
  bracket x y := A.weightOneZeroProduct x y
  add_lie x y z := by simp
  lie_add x y z := by simp
  lie_self := A.weightOneZeroProduct_alternating
  leibniz_lie := A.weightOneZeroProduct_leibniz

/-- The bracket on weight one is `weightOneZeroProduct`. -/
theorem lie_eq_weightOneZeroProduct (x y : A.grading 1) :
    ⁅x, y⁆ = A.weightOneZeroProduct x y := (rfl)

/-- The bracket on weight one is the zero product: `⁅x, y⁆ = x₍₀₎ y`. -/
@[simp]
theorem coe_lie (x y : A.grading 1) : ((⁅x, y⁆ : A.grading 1) : V) = ((A.field x)[[0]]) y := (rfl)

/-- The Lie algebra structure on the weight-one space `V_1` over `R`. -/
instance instLieAlgebraGradingOne : LieAlgebra R (A.grading 1) where
  lie_smul r x y := by simp [lie_eq_weightOneZeroProduct]

/-! ### Morphisms -/

variable {A} [HasUniqueDiv W] [HasUniqueDiv U] {B : GradedFormalVertexAxioms R W}
  {C : GradedFormalVertexAxioms R U}

/-- A morphism of formal vertex algebras that preserves weight one restricts to a morphism of the
weight-one Lie algebras. -/
def weightOneLieHom (f : A.Hom B.toFormalVertexAxioms)
    (hf : ∀ a ∈ A.grading 1, f a ∈ B.grading 1) : A.grading 1 →ₗ⁅R⁆ B.grading 1 where
  __ := (f : V →ₗ[R] W).restrict hf
  map_lie' {x y} := Subtype.ext <| by
    simp [LinearMap.restrict_apply, f.map_ncoeff_field_apply]

/-- The Lie morphism induced on weight one is `f` itself. -/
@[simp]
theorem coe_weightOneLieHom_apply (f : A.Hom B.toFormalVertexAxioms)
    (hf : ∀ a ∈ A.grading 1, f a ∈ B.grading 1) (x : A.grading 1) :
    (weightOneLieHom f hf x : W) = f x := (rfl)

/-- The identity morphism induces the identity on weight one. -/
@[simp]
theorem weightOneLieHom_id :
    weightOneLieHom (FormalVertexAxioms.Hom.id A.toFormalVertexAxioms)
      (fun _ ha ↦ by simpa using ha) = LieHom.id :=
  LieHom.ext fun _ ↦ Subtype.ext <| by simp

/-- The Lie morphism induced on weight one by a composite is the composite of the induced ones. -/
theorem weightOneLieHom_comp (g : B.Hom C.toFormalVertexAxioms)
    (hg : ∀ b ∈ B.grading 1, g b ∈ C.grading 1) (f : A.Hom B.toFormalVertexAxioms)
    (hf : ∀ a ∈ A.grading 1, f a ∈ B.grading 1) :
    weightOneLieHom (g.comp f) (fun a ha ↦ by simpa using hg _ (hf a ha)) =
      (weightOneLieHom g hg).comp (weightOneLieHom f hf) :=
  LieHom.ext fun _ ↦ Subtype.ext <| by simp

end TauCeti.GradedFormalVertexAxioms
