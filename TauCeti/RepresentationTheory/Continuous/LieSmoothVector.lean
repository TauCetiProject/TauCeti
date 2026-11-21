/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Geometry.Lie.InvariantVectorField.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Smooth vectors of a representation of a Lie group

Let `π` be a continuous representation of a real Lie group `G` on a real normed space `V`, with
coefficients in a ring `R` (for instance a complex Banach representation). A vector `v` is
*smooth* when its orbit map `g ↦ π g v` is a smooth map `G → V`. The smooth vectors form an
`R`-submodule `lieSmoothVectors I π` that every `π g` preserves.

For a left-invariant derivation `X` of `G`, the derived action
`lieDerivative π X v = d/dt|₀ π (lieExp (t • X)) v` sends smooth vectors to smooth vectors.
On a smooth vector, `π g (lieDerivative π X v)` is the derivative of the orbit map along the
left-invariant vector field of `X` at `g`. Testing against continuous linear functionals reduces
the derived action to the action of `X` on smooth scalar functions, which makes it an
`R`-linear endomorphism of the smooth vectors, linear in `X`, and compatible with brackets:
`lieDerivative π ⁅X, Y⁆` is the commutator of `lieDerivative π X` and `lieDerivative π Y` on
smooth vectors.

## Main definitions

* `ContRepresentation.IsLieSmoothVector I π v`: the orbit map of `v` is smooth.
* `ContRepresentation.lieSmoothVectors I π`: the submodule of smooth vectors.
* `ContRepresentation.lieDerivative π X v`: the derivative of `t ↦ π (lieExp (t • X)) v` at `0`.
* `ContRepresentation.lieSmoothVectorsDerivative I π X`: the derived action of `X` as an
  `R`-linear endomorphism of `lieSmoothVectors I π`.
* `ContRepresentation.lieSmoothVectorsDerivedAction I π`: the derived representation, a
  homomorphism of real Lie algebras from the left-invariant derivations of `G` to the
  `R`-linear endomorphisms of `lieSmoothVectors I π`.

## Main results

* `ContRepresentation.IsLieSmoothVector.apply`: `π g` preserves smooth vectors.
* `ContRepresentation.IsLieSmoothVector.hasDerivAt_lieDerivative`: on a smooth vector, the
  derived action is a genuine derivative.
* `ContRepresentation.IsLieSmoothVector.isLieSmoothVector_lieDerivative`: the derived action
  preserves smooth vectors.
* `ContRepresentation.IsLieSmoothVector.lieDerivative_lie`: the derived action of a bracket is
  the commutator of the derived actions.

## References

* Bernstein, Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {R : Type*} [Ring R] [Module R V] (π : ContRepresentation R G V)

/-- A vector of a continuous representation of a Lie group is *smooth* when its orbit map
`g ↦ π g v` is smooth. -/
def IsLieSmoothVector (v : V) : Prop :=
  ContMDiff I 𝓘(ℝ, V) ∞ fun g ↦ π g v

/-- Smoothness of a vector is smoothness of its orbit map. -/
theorem isLieSmoothVector_iff {v : V} :
    IsLieSmoothVector I π v ↔ ContMDiff I 𝓘(ℝ, V) ∞ fun g ↦ π g v := Iff.rfl

variable {I π} in
/-- Every operator of the representation preserves smooth vectors. -/
theorem IsLieSmoothVector.apply [ContMDiffMul I ∞ G] {v : V} (hv : IsLieSmoothVector I π v)
    (h : G) : IsLieSmoothVector I π (π h v) := by
  have hfun : (fun g ↦ π g (π h v)) = (fun g ↦ π g v) ∘ (· * h) := by
    funext g
    simp [map_mul]
  rw [isLieSmoothVector_iff, hfun]
  exact hv.comp (contMDiff_mul_right (I := I) (n := ∞))

section Submodule

variable [SMulCommClass ℝ R V] [ContinuousConstSMul R V]

/-- The submodule of smooth vectors of a continuous representation of a Lie group. -/
def lieSmoothVectors : Submodule R V where
  carrier := {v | IsLieSmoothVector I π v}
  zero_mem' := by
    simpa [Set.mem_ofPred_eq, isLieSmoothVector_iff] using
      (contMDiff_const : ContMDiff I 𝓘(ℝ, V) ∞ fun _ : G ↦ (0 : V))
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, isLieSmoothVector_iff, map_add] at hv hw ⊢
    exact hv.add hw
  smul_mem' r v hv := by
    simp only [Set.mem_ofPred_eq, isLieSmoothVector_iff, map_smul] at hv ⊢
    let L : V →L[ℝ] V :=
      { toFun := (r • ·)
        map_add' := smul_add r
        map_smul' := fun c x ↦ (smul_comm c r x).symm
        cont := continuous_const_smul r }
    exact L.contMDiff.comp hv

/-- Membership in `lieSmoothVectors` is smoothness of the vector. -/
@[simp]
theorem mem_lieSmoothVectors {v : V} : v ∈ lieSmoothVectors I π ↔ IsLieSmoothVector I π v :=
  Iff.rfl

end Submodule

section Derivative

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {I} in
/-- The derived action of a left-invariant derivation `X` on a vector `v`: the derivative at
`0` of `t ↦ π (lieExp (t • X)) v`. It is a genuine derivative on smooth vectors
(`IsLieSmoothVector.hasDerivAt_lieDerivative`). -/
def lieDerivative (X : LeftInvariantDerivation I G) (v : V) : V :=
  deriv (fun t : ℝ ↦ π (lieExp (t • X)) v) 0

variable {I} in
/-- The derived action is the derivative of the orbit along the exponential line. -/
theorem lieDerivative_def (X : LeftInvariantDerivation I G) (v : V) :
    lieDerivative π X v = deriv (fun t : ℝ ↦ π (lieExp (t • X)) v) 0 := by
  rw [lieDerivative]

variable {I π}

/-- On a smooth vector, the orbit map differentiated along the exponential line through `g` of a
left-invariant derivation is the differential of the orbit map applied to the left-invariant
vector field of that derivation at `g`. -/
theorem IsLieSmoothVector.hasDerivAt_apply_mul_lieExp_smul {v : V}
    (hv : IsLieSmoothVector I π v) (X : LeftInvariantDerivation I G) (g : G) :
    HasDerivAt (fun t : ℝ ↦ π (g * lieExp (t • X)) v)
      (mvfderiv I (fun g ↦ π g v) g (mulInvariantVectorField
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X) g)) 0 := by
  have hf : HasMFDerivAt I 𝓘(ℝ, V) (fun g ↦ π g v) g (mfderiv I 𝓘(ℝ, V) (fun g ↦ π g v) g) :=
    (hv.mdifferentiable (by simp)).mdifferentiableAt.hasMFDerivAt
  have hexp (t : ℝ) : lieExp (t • X) = mulInvariantExp (t •
      leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint X) := by
    rw [lieExp_eq_mulInvariantExp, map_smul]
  simp only [hexp]
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hf.hasDerivAt_comp_mul_mulInvariantExp_smul_zero _

/-- On a smooth vector, the derived action is the derivative of the orbit along the exponential
line. -/
theorem IsLieSmoothVector.hasDerivAt_lieDerivative {v : V} (hv : IsLieSmoothVector I π v)
    (X : LeftInvariantDerivation I G) :
    HasDerivAt (fun t : ℝ ↦ π (lieExp (t • X)) v) (lieDerivative π X v) 0 := by
  have h := hv.hasDerivAt_apply_mul_lieExp_smul X 1
  simp only [one_mul] at h
  rwa [lieDerivative_def, h.deriv]

/-- On a smooth vector, the orbit map of the derived action of `X` is the derivative of the
orbit map along the left-invariant vector field of `X`. -/
theorem IsLieSmoothVector.apply_lieDerivative {v : V} (hv : IsLieSmoothVector I π v)
    (X : LeftInvariantDerivation I G) (g : G) :
    π g (lieDerivative π X v) =
      mvfderiv I (fun g ↦ π g v) g (mulInvariantVectorField
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X) g) := by
  let L : V →L[ℝ] V := (π g).toLinearMap.toAddMonoidHom.toRealLinearMap (π g).continuous
  have h := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.hasDerivAt_lieDerivative X)
  have hfun : (L ∘ fun t : ℝ ↦ π (lieExp (t • X)) v) = fun t ↦ π (g * lieExp (t • X)) v := by
    funext t
    simp only [Function.comp_apply, map_mul]
    rfl
  rw [hfun] at h
  exact h.unique (hv.hasDerivAt_apply_mul_lieExp_smul X g)

/-- The derived action sends smooth vectors to smooth vectors. -/
theorem IsLieSmoothVector.isLieSmoothVector_lieDerivative {v : V} (hv : IsLieSmoothVector I π v)
    (X : LeftInvariantDerivation I G) : IsLieSmoothVector I π (lieDerivative π X v) := by
  rw [isLieSmoothVector_iff]
  simp only [hv.apply_lieDerivative X]
  have hf : ContMDiff I 𝓘(ℝ, V) ∞ fun g ↦ π g v := (isLieSmoothVector_iff I π).1 hv
  have hd : ContMDiff I.tangent 𝓘(ℝ, V) ∞
      (fun p : TangentBundle I G ↦ mvfderiv I (fun g ↦ π g v) p.proj p.snd) :=
    hf.contMDiff_mvfderiv_apply (by simp)
  have hX := contMDiff_mulInvariantVectorField_infty (I := I) (G := G)
    (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint X)
  exact (hd.comp hX).congr fun g ↦ rfl

/-- The smooth scalar function `g ↦ φ (π g v)` attached to a smooth vector `v` and a continuous
linear functional `φ`. -/
private def dualOrbit (φ : StrongDual ℝ V) {v : V} (hv : IsLieSmoothVector I π v) :
    C^∞⟮I, G; ℝ⟯ :=
  ⟨fun g ↦ φ (π g v), φ.contMDiff.comp hv⟩

omit [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] in
private theorem dualOrbit_apply (φ : StrongDual ℝ V) {v : V} (hv : IsLieSmoothVector I π v)
    (g : G) : dualOrbit φ hv g = φ (π g v) :=
  rfl

/-- Tested against a continuous linear functional, the orbit map of the derived action of `X`
is `X` applied to the tested orbit map. -/
private theorem dualOrbit_lieDerivative (φ : StrongDual ℝ V) {v : V}
    (hv : IsLieSmoothVector I π v) (X : LeftInvariantDerivation I G) :
    dualOrbit φ (hv.isLieSmoothVector_lieDerivative X) = X (dualOrbit φ hv) := by
  ext g
  have h1 := φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.hasDerivAt_apply_mul_lieExp_smul X g)
  have h2 := LeftInvariantDerivation.hasDerivAt_apply_mul_lieExp_smul X (dualOrbit φ hv) g 0
  simp only [zero_smul, lieExp_zero, mul_one] at h2
  rw [dualOrbit_apply, hv.apply_lieDerivative]
  exact h1.unique h2

/-- Tested against a continuous linear functional, the derived action of `X` at a smooth vector
is `X` applied to the tested orbit map, evaluated at the identity. -/
private theorem dual_lieDerivative (φ : StrongDual ℝ V) {v : V} (hv : IsLieSmoothVector I π v)
    (X : LeftInvariantDerivation I G) :
    φ (lieDerivative π X v) = X (dualOrbit φ hv) 1 := by
  rw [← dualOrbit_lieDerivative φ hv X]
  simp [dualOrbit_apply]

/-- The derived action at a smooth vector is additive in the derivation. -/
theorem IsLieSmoothVector.lieDerivative_add_left {v : V} (hv : IsLieSmoothVector I π v)
    (X Y : LeftInvariantDerivation I G) :
    lieDerivative π (X + Y) v = lieDerivative π X v + lieDerivative π Y v := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  simp [dual_lieDerivative φ hv]

/-- The derived action at a smooth vector is homogeneous in the derivation. -/
theorem IsLieSmoothVector.lieDerivative_smul_left {v : V} (hv : IsLieSmoothVector I π v) (c : ℝ)
    (X : LeftInvariantDerivation I G) :
    lieDerivative π (c • X) v = c • lieDerivative π X v := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  simp [dual_lieDerivative φ hv]

/-- **The derived action respects brackets.** At a smooth vector, the derived action of the
bracket of two left-invariant derivations is the commutator of their derived actions. -/
theorem IsLieSmoothVector.lieDerivative_lie {v : V} (hv : IsLieSmoothVector I π v)
    (X Y : LeftInvariantDerivation I G) :
    lieDerivative π ⁅X, Y⁆ v =
      lieDerivative π X (lieDerivative π Y v) - lieDerivative π Y (lieDerivative π X v) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  rw [map_sub, dual_lieDerivative φ hv, dual_lieDerivative φ (hv.isLieSmoothVector_lieDerivative Y),
    dual_lieDerivative φ (hv.isLieSmoothVector_lieDerivative X), dualOrbit_lieDerivative,
    dualOrbit_lieDerivative, LeftInvariantDerivation.commutator_apply]
  rfl

/-- The derived action is additive on smooth vectors. -/
theorem IsLieSmoothVector.lieDerivative_add_right {v w : V} (hv : IsLieSmoothVector I π v)
    (hw : IsLieSmoothVector I π w) (X : LeftInvariantDerivation I G) :
    lieDerivative π X (v + w) = lieDerivative π X v + lieDerivative π X w := by
  rw [lieDerivative_def]
  simp only [map_add]
  exact ((hv.hasDerivAt_lieDerivative X).add (hw.hasDerivAt_lieDerivative X)).deriv

/-- The derived action commutes with the coefficients on smooth vectors. -/
theorem IsLieSmoothVector.lieDerivative_smul_right [SMulCommClass ℝ R V]
    [ContinuousConstSMul R V] {v : V} (hv : IsLieSmoothVector I π v) (r : R)
    (X : LeftInvariantDerivation I G) :
    lieDerivative π X (r • v) = r • lieDerivative π X v := by
  rw [lieDerivative_def]
  simp only [map_smul]
  exact ((hv.hasDerivAt_lieDerivative X).const_smul r).deriv

section Endomorphism

variable [SMulCommClass ℝ R V] [ContinuousConstSMul R V]

variable (I π) in
/-- The derived action of a left-invariant derivation `X`, as an `R`-linear endomorphism of the
smooth vectors. -/
def lieSmoothVectorsDerivative (X : LeftInvariantDerivation I G) :
    Module.End R (lieSmoothVectors I π) where
  toFun w := ⟨lieDerivative π X w, w.property.isLieSmoothVector_lieDerivative X⟩
  map_add' v w := Subtype.ext (v.property.lieDerivative_add_right w.property X)
  map_smul' r w := Subtype.ext (w.property.lieDerivative_smul_right r X)

/-- The derived endomorphism of the smooth vectors is the derived action on the underlying
vectors. -/
@[simp]
theorem coe_lieSmoothVectorsDerivative_apply (X : LeftInvariantDerivation I G)
    (w : lieSmoothVectors I π) :
    (lieSmoothVectorsDerivative I π X w : V) = lieDerivative π X w := by
  rw [lieSmoothVectorsDerivative]
  rfl

end Endomorphism

section LieHom

attribute [local instance 100] LieRing.ofAssociativeRing

variable [Algebra ℝ R] [IsScalarTower ℝ R V] [ContinuousConstSMul R V]

variable (I π) in
/-- **The derived representation.** The derived action of left-invariant derivations on the
smooth vectors is a homomorphism of real Lie algebras into the `R`-linear endomorphisms. -/
def lieSmoothVectorsDerivedAction :
    LeftInvariantDerivation I G →ₗ⁅ℝ⁆ Module.End R (lieSmoothVectors I π) where
  toFun := lieSmoothVectorsDerivative I π
  map_add' X Y := LinearMap.ext fun w ↦ Subtype.ext (w.property.lieDerivative_add_left X Y)
  map_smul' c X := LinearMap.ext fun w ↦ Subtype.ext (w.property.lieDerivative_smul_left c X)
  map_lie' {X Y} := LinearMap.ext fun w ↦ Subtype.ext (w.property.lieDerivative_lie X Y)

/-- The derived representation of `X` is the derived endomorphism of `X`. -/
@[simp]
theorem lieSmoothVectorsDerivedAction_apply (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsDerivedAction I π X = lieSmoothVectorsDerivative I π X := by
  rw [lieSmoothVectorsDerivedAction]
  rfl

end LieHom

end Derivative

end ContRepresentation
