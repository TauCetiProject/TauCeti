/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.Topology.PathSpace.Moore.FundamentalGroup

/-!
# The zeroth homology of the chains on the Moore loop space

For a pointed space `(B, b)`, the zeroth homology of the DG algebra `C_*(Ω_b B; R)` is the group
ring of the opposite of the fundamental group, `H₀(C_*(Ω_b B; R)) ≅ R[π₁(B, b)ᵐᵒᵖ]`, as
`R`-modules and compatibly with the product and the unit.  The class of a Moore loop `γ` is
`MooreLoopSpace.loopClass γ`; it only depends on the path component of `γ` in the Moore loop
space, and every class is hit.

Concatenation of Moore loops `γ * δ` runs through `γ` first, while the product of
`FundamentalGroup B b` is composition in the fundamental groupoid, which runs through the second
factor first.  So `loopClass` is multiplicative into the *opposite* group, and the group ring in
which `H₀` is computed is `R[π₁(B, b)ᵐᵒᵖ]`.  A right module over `R[π₁ᵐᵒᵖ]` is a left module
over `R[π₁]`, that is a representation of `π₁`.

## Main definitions

* `TauCeti.zerothClass`: the linear map from `0`-chains of the Moore loop space to
  `R[π₁(B, b)ᵐᵒᵖ]`.
* `TauCeti.zerothHomologyEquiv`: the isomorphism `C₀ / ∂C₁ ≃ₗ[R] R[π₁(B, b)ᵐᵒᵖ]`.

## Main results

* `TauCeti.zerothClass_mul`, `TauCeti.zerothClass_one`: the product and the unit.
* `TauCeti.zerothClass_eq_zero_iff`: a `0`-chain has class zero if and only if it is a boundary.
* `TauCeti.zerothClass_surjective`: every element of the group ring is a class.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

open CategoryTheory unitInterval MulOpposite

namespace TauCeti


namespace NormalizedCubicalChain

/-- Points in the same path component differ by a boundary. -/
theorem ofCube_point_sub_mem_range_boundary {X : Type*} [TopologicalSpace X] {R : Type*} [Ring R]
    {γ δ : X} (h : Joined γ δ) :
    ofCube X R (SingularCube.point γ) - ofCube X R (SingularCube.point δ) ∈
      LinearMap.range (boundary X R 0) := by
  obtain ⟨P⟩ := h
  refine ⟨ofCube X R (⟨fun t ↦ P (t 0), by fun_prop⟩ : SingularCube X 1), ?_⟩
  rw [boundary_ofCube_one]
  simp

end NormalizedCubicalChain

section Zeroth

variable (B : Type*) [TopologicalSpace B] (b : B) (R : Type*) [CommRing R]

/-- The class of `0`-cubes of the Moore loop space: the `0`-cube at `γ` goes to the class of
`γ`, in the group ring of the opposite fundamental group. -/
def zerothClassAux :
    CubicalChain (MooreLoopSpace B b) R 0 →ₗ[R] MonoidAlgebra R (FundamentalGroup B b)ᵐᵒᵖ :=
  Finsupp.linearCombination R fun c ↦
    MonoidAlgebra.single (op (MooreLoopSpace.loopClass (c fun i ↦ i.elim0))) (1 : R)

/-- The map from the `0`-chains of the Moore loop space `Ω_b B` to the group ring of the
opposite of `π₁(B, b)`: a `0`-cube at `γ` goes to the class of `γ`. -/
def zerothClass :
    NormalizedCubicalChain (MooreLoopSpace B b) R 0 →ₗ[R]
      MonoidAlgebra R (FundamentalGroup B b)ᵐᵒᵖ :=
  Submodule.liftQ _ (zerothClassAux B b R) (by rw [CubicalChain.degenerate_zero]; simp)

variable {B b R}

theorem zerothClass_ofCube_point (γ : MooreLoopSpace B b) :
    zerothClass B b R (NormalizedCubicalChain.ofCube _ R (SingularCube.point γ)) =
      MonoidAlgebra.single (op (MooreLoopSpace.loopClass γ)) 1 := by
  simp [zerothClass, zerothClassAux, NormalizedCubicalChain.ofCube_def]

/-- The two end points of a `1`-cube of the Moore loop space have the same class. -/
theorem loopClass_apply_zero_eq_loopClass_apply_one (c : SingularCube (MooreLoopSpace B b) 1) :
    MooreLoopSpace.loopClass (c fun _ ↦ 0) = MooreLoopSpace.loopClass (c fun _ ↦ 1) := by
  refine MooreLoopSpace.loopClass_eq_iff.2 ⟨{ toFun := fun t ↦ c fun _ ↦ t
                                              continuous_toFun := by fun_prop
                                              source' := rfl
                                              target' := rfl }⟩

/-- The boundary of a `1`-chain has class zero. -/
theorem zerothClassAux_boundary (f : CubicalChain (MooreLoopSpace B b) R 1) :
    zerothClassAux B b R (CubicalChain.boundary _ R 0 f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single c a =>
    have h := loopClass_apply_zero_eq_loopClass_apply_one c
    rw [CubicalChain.boundary_single, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, map_sub, zerothClassAux,
      Finsupp.linearCombination_single, SingularCube.face_zero_apply, h, sub_self]

/-- The boundary of a `1`-chain of the normalized chains has class zero. -/
theorem zerothClass_boundary (y : NormalizedCubicalChain (MooreLoopSpace B b) R 1) :
    zerothClass B b R (NormalizedCubicalChain.boundary _ R 0 y) = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H f =>
    rw [NormalizedCubicalChain.boundary_mk]
    exact zerothClassAux_boundary f

theorem range_boundary_le_ker_zerothClass :
    LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace B b) R 0) ≤
      LinearMap.ker (zerothClass B b R) := by
  rintro _ ⟨y, rfl⟩
  exact zerothClass_boundary y

variable (B b R)

/-- A section of `zerothClass` on homology: a class `g` goes to the class of a chosen Moore loop
with class `g`. -/
def zerothSection :
    MonoidAlgebra R (FundamentalGroup B b)ᵐᵒᵖ →ₗ[R]
      NormalizedCubicalChain (MooreLoopSpace B b) R 0 ⧸
        LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace B b) R 0) :=
  (Finsupp.linearCombination R fun g ↦ Submodule.Quotient.mk
    (NormalizedCubicalChain.ofCube _ R (SingularCube.point
      (Classical.choose (MooreLoopSpace.loopClass_surjective (unop g)))))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

variable {B b R}

theorem zerothSection_single (g : (FundamentalGroup B b)ᵐᵒᵖ) (r : R) :
    zerothSection B b R (MonoidAlgebra.single g r) =
      r • Submodule.Quotient.mk (NormalizedCubicalChain.ofCube _ R (SingularCube.point
        (Classical.choose (MooreLoopSpace.loopClass_surjective (unop g))))) := by
  simp [zerothSection]

/-- The class of the chosen representative. -/
theorem loopClass_choose (g : (FundamentalGroup B b)ᵐᵒᵖ) :
    op (MooreLoopSpace.loopClass
      (Classical.choose (MooreLoopSpace.loopClass_surjective (unop g)))) = g := by
  rw [Classical.choose_spec (MooreLoopSpace.loopClass_surjective (unop g))]
  rfl

variable (B b R) in
/-- **The zeroth homology of the chains on the Moore loop space is the group ring of the opposite
fundamental group**: `C₀ / ∂C₁ ≃ₗ[R] R[π₁(B, b)ᵐᵒᵖ]`. -/
def zerothHomologyEquiv :
    (NormalizedCubicalChain (MooreLoopSpace B b) R 0 ⧸
        LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace B b) R 0)) ≃ₗ[R]
      MonoidAlgebra R (FundamentalGroup B b)ᵐᵒᵖ :=
  LinearEquiv.ofLinearMap (Submodule.liftQ _ (zerothClass B b R) range_boundary_le_ker_zerothClass)
    (zerothSection B b R)
    (by
      refine LinearMap.ext fun x ↦ ?_
      induction x using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
      | single g r =>
        simp [zerothSection_single, zerothClass_ofCube_point, loopClass_choose])
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
      induction x using NormalizedCubicalChain.induction_zero with
      | zero => simp
      | add x y hx hy =>
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, map_add] at hx hy ⊢
        rw [hx, hy]
      | smul r γ =>
        have hγ : MooreLoopSpace.loopClass (Classical.choose
            (MooreLoopSpace.loopClass_surjective (unop (op (MooreLoopSpace.loopClass γ))))) =
            MooreLoopSpace.loopClass γ := by
          simpa using loopClass_choose (op (MooreLoopSpace.loopClass γ))
        have hq : (Submodule.Quotient.mk (NormalizedCubicalChain.ofCube _ R (SingularCube.point
            (Classical.choose (MooreLoopSpace.loopClass_surjective
              (unop (op (MooreLoopSpace.loopClass γ)))))))) =
            (Submodule.Quotient.mk (NormalizedCubicalChain.ofCube _ R (SingularCube.point γ)) :
              _ ⧸ LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace B b) R 0)) :=
          (Submodule.Quotient.eq _).2
            (NormalizedCubicalChain.ofCube_point_sub_mem_range_boundary
              (MooreLoopSpace.loopClass_eq_iff.1 hγ))
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, map_smul, Submodule.liftQ_apply,
          zerothClass_ofCube_point, zerothSection_single, unop_op, LinearMap.id_comp,
          one_smul]
        rw [hq])

variable (B b R) in
/-- The class of the unit is the unit. -/
theorem zerothClass_one :
    zerothClass B b R (NormalizedCubicalChain.one (MooreLoopSpace B b) R) = 1 := by
  rw [NormalizedCubicalChain.one_def, zerothClass_ofCube_point, MooreLoopSpace.loopClass_one,
    MonoidAlgebra.one_def, op_one]

/-- The product of two `0`-cubes at points is the `0`-cube at the product. -/
theorem mul_ofCube_point (γ δ : MooreLoopSpace B b) :
    NormalizedCubicalChain.mul (MooreLoopSpace B b) R 0 0
        (NormalizedCubicalChain.ofCube _ R (SingularCube.point γ))
        (NormalizedCubicalChain.ofCube _ R (SingularCube.point δ)) =
      NormalizedCubicalChain.ofCube _ R (SingularCube.point (γ * δ)) := by
  rw [NormalizedCubicalChain.mul_ofCube]
  congr 1
  exact ContinuousMap.ext fun x ↦ by
    rw [ContinuousMap.comp_apply, SingularCube.crossProduct_apply]
    simp [mulMap_apply]

/-- **The class of a product of `0`-chains is the product of the classes**: the identification of
`H₀` with the group ring of the opposite fundamental group is multiplicative. -/
theorem zerothClass_mul (a c : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    zerothClass B b R (NormalizedCubicalChain.mul _ R 0 0 a c) =
      zerothClass B b R a * zerothClass B b R c := by
  induction a using NormalizedCubicalChain.induction_zero with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_mul]
  | smul r γ =>
    induction c using NormalizedCubicalChain.induction_zero with
    | zero => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | smul s δ =>
      simp only [map_smul, LinearMap.smul_apply, mul_ofCube_point, zerothClass_ofCube_point,
        MooreLoopSpace.loopClass_mul, op_mul, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.smul_single, mul_one, mul_smul_comm]

variable (B b R) in
@[simp]
theorem zerothHomologyEquiv_mk (x : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    zerothHomologyEquiv B b R (Submodule.Quotient.mk x) = zerothClass B b R x :=
  (rfl)

/-- **A `0`-chain of the Moore loop space is a boundary if and only if its class in the group ring
of the opposite fundamental group vanishes**: the kernel of `zerothClass` is the image of the
boundary of `1`-chains. -/
theorem zerothClass_eq_zero_iff (x : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    zerothClass B b R x = 0 ↔
      x ∈ LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace B b) R 0) := by
  rw [← zerothHomologyEquiv_mk, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- The class map is surjective: every element of the group ring is the class of a `0`-chain. -/
theorem zerothClass_surjective :
    Function.Surjective (zerothClass B b R) := fun y ↦ by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ ((zerothHomologyEquiv B b R).symm y)
  exact ⟨x, by rw [← zerothHomologyEquiv_mk, hx, LinearEquiv.apply_symm_apply]⟩

end Zeroth

end TauCeti
