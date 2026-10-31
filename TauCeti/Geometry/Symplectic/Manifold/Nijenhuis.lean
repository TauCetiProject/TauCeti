/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import TauCeti.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# The Nijenhuis tensor of a smooth almost complex structure

For a smooth almost complex structure `J` on a finite-dimensional manifold, the Nijenhuis
expression on vector fields is
`N_J(X, Y) = [JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]`,
with Mathlib's Lie bracket `VectorField.mlieBracket`. It is linear over differentiable functions
in each argument, so it is a tensor: its value at `x` depends only on `X x` and `Y x`. This file
constructs that tensor as a continuous bilinear map on each tangent space, through Mathlib's
tensoriality criterion `TensorialAt.mkHom₂`, and proves its basic algebraic identities. The
construction follows Mathlib's torsion tensor `IsCovariantDerivativeOn.torsion`.

The Nijenhuis tensor is the obstruction to integrability of `J`: the Newlander–Nirenberg
theorem says that `J` comes from a complex atlas exactly when it vanishes. Its vanishing is
equivalent to involutivity of the `±i` eigenbundles of `J` in the complexified tangent bundle,
and it controls the components of the exterior derivative outside the bidegrees `(1,0)` and
`(0,1)`. The identities `N_J(Jv, w) = -J N_J(v, w)` proved here are the real form of the type
statement that `N_J` maps two `(0,1)` vectors to a `(1,0)` vector. Extended complex-bilinearly to
the complexified tangent spaces `ℂ ⊗[ℝ] T_x M`, the tensor indeed maps two vectors of type `(0,1)`
to a vector of type `(1,0)`, two vectors of type `(1,0)` to a vector of type `(0,1)`, and vanishes
on a vector of type `(1,0)` and one of type `(0,1)`; on parts of real tangent vectors,
`N_J(v^(0,1), w^(0,1)) = N_J(v, w)^(1,0)`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.nijenhuis`: the Nijenhuis tensor at a point.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_apply`: its value on differentiable vector
  fields is the Nijenhuis expression in Lie brackets.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_eq_zero_iff`: the tensor vanishes exactly
  when `[JX, JY] = [X, Y] + J[JX, Y] + J[X, JY]` for all differentiable vector fields.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_antisymm`: skew-symmetry.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_apply_left`,
  `TauCeti.SmoothAlmostComplexStructure.nijenhuis_apply_right`,
  `TauCeti.SmoothAlmostComplexStructure.nijenhuis_apply_both`: anti-commutation with `J` in each
  argument, and sign reversal under applying `J` to both arguments.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_neg`: `-J` has the same Nijenhuis tensor.
* `SmoothAlmostComplexStructure.baseChange_nijenhuis_antiholomorphicPart_antiholomorphicPart`,
  `SmoothAlmostComplexStructure.baseChange_nijenhuis_holomorphicPart_holomorphicPart`:
  `N_J(v^(0,1), w^(0,1)) = N_J(v, w)^(1,0)` and `N_J(v^(1,0), w^(1,0)) = N_J(v, w)^(0,1)` for the
  complex-bilinear extension to the complexified tangent space.
* `TauCeti.SmoothAlmostComplexStructure.baseChange_nijenhuis_mem_eigenspace_neg_of_mem_left`,
  `SmoothAlmostComplexStructure.baseChange_nijenhuis_eq_zero_of_mem_eigenspace_I_of_mem_neg_I`
  and their companions: the type identities of the complex-bilinear extension on the eigenspaces
  `T^(1,0)_x M` and `T^(0,1)_x M` of the complexified `J`.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_const`: a constant almost complex structure on
  a vector space has vanishing Nijenhuis tensor.

## Conventions

No factor `1/4` is included; some sources use `N_J / 4` instead.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public noncomputable section

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M) {x : M}

/-- The Nijenhuis expression `[JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]` on vector fields, as a bare
function. Use the tensor `SmoothAlmostComplexStructure.nijenhuis` instead. -/
private def nijenhuisAux (X Y : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  mlieBracket I (fun y ↦ J y (X y)) (fun y ↦ J y (Y y)) x - mlieBracket I X Y x -
    J x (mlieBracket I (fun y ↦ J y (X y)) Y x) - J x (mlieBracket I X (fun y ↦ J y (Y y)) x)

private lemma nijenhuisAux_swap (X Y : Π x : M, TangentSpace I x) :
    J.nijenhuisAux X Y x = -J.nijenhuisAux Y X x := by
  simp only [nijenhuisAux]
  rw [mlieBracket_swap_apply (V := fun y ↦ J y (X y)), mlieBracket_swap_apply (V := X),
    mlieBracket_swap_apply (V := fun y ↦ J y (X y)) (W := Y),
    mlieBracket_swap_apply (V := X) (W := fun y ↦ J y (Y y)), map_neg, map_neg]
  abel

/-- Replacing `X` by `J X` in the Nijenhuis expression multiplies it by `-J`. -/
private lemma nijenhuisAux_apply_left (X Y : Π x : M, TangentSpace I x) :
    J.nijenhuisAux (fun y ↦ J y (X y)) Y x = -J x (J.nijenhuisAux X Y x) := by
  -- `J (J X) = -X` pointwise; `← Pi.neg_def` folds the pointwise negation into `-X`, the form
  -- used by `mlieBracket_neg_left`.
  simp only [nijenhuisAux, apply_apply, ← Pi.neg_def, mlieBracket_neg_left, map_sub, map_neg]
  abel

/-- `J` preserves vector fields differentiable at `x`, in the form used by the Lie bracket
lemmas. -/
private lemma mdifferentiableAt_apply_field {X : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) : MDiffAt (T% (fun y ↦ J y (X y))) x :=
  J.mdifferentiableAt_apply mdifferentiableAt_id hX

section Complete

variable [CompleteSpace E]

private theorem nijenhuisAux_tensorial₁ (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (J.nijenhuisAux · Y x) x where
  smul {f X} hf hX := by
    have hJX := J.mdifferentiableAt_apply_field hX
    have hJfX : (fun y ↦ J y ((f • X) y)) = f • fun y ↦ J y (X y) := by
      ext y
      simp
    simp only [nijenhuisAux, hJfX, mlieBracket_smul_left hf hX, mlieBracket_smul_left hf hJX,
      map_add, map_smul, apply_apply]
    module
  add {X X'} hX hX' := by
    have hJX := J.mdifferentiableAt_apply_field hX
    have hJX' := J.mdifferentiableAt_apply_field hX'
    have hJXX' : (fun y ↦ J y ((X + X') y)) = (fun y ↦ J y (X y)) + fun y ↦ J y (X' y) := by
      ext y
      simp
    simp only [nijenhuisAux, hJXX', mlieBracket_add_left hX hX', mlieBracket_add_left hJX hJX',
      map_add]
    abel

private theorem nijenhuisAux_tensorial₂ (X : Π x : M, TangentSpace I x) :
    TensorialAt I E (J.nijenhuisAux X · x) x where
  smul {f Y} hf hY := by
    rw [J.nijenhuisAux_swap X, (J.nijenhuisAux_tensorial₁ X).smul hf hY,
      J.nijenhuisAux_swap Y X]
    simp
  add {Y Y'} hY hY' := by
    rw [J.nijenhuisAux_swap X, (J.nijenhuisAux_tensorial₁ X).add hY hY',
      J.nijenhuisAux_swap Y X, J.nijenhuisAux_swap Y' X]
    abel

end Complete

variable [FiniteDimensional ℝ E]

/-- The Nijenhuis tensor of a smooth almost complex structure `J` at a point `x`: the continuous
bilinear map on `T_x M` whose value on the values at `x` of differentiable vector fields `X` and
`Y` is `[JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]` at `x` (`nijenhuis_apply`). -/
def nijenhuis (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  have := FiniteDimensional.complete ℝ E
  TensorialAt.mkHom₂ (J.nijenhuisAux · · x) x
    (fun Y _ ↦ J.nijenhuisAux_tensorial₁ Y) (fun X _ ↦ J.nijenhuisAux_tensorial₂ X)

private lemma nijenhuis_apply_eq_nijenhuisAux {X Y : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    J.nijenhuis x (X x) (Y x) = J.nijenhuisAux X Y x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

/-- On vector fields differentiable at `x`, the Nijenhuis tensor is
`N_J(X, Y) = [JX, JY] - [X, Y] - J[JX, Y] - J[X, JY]`. -/
theorem nijenhuis_apply {X Y : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    J.nijenhuis x (X x) (Y x) =
      mlieBracket I (fun y ↦ J y (X y)) (fun y ↦ J y (Y y)) x - mlieBracket I X Y x -
        J x (mlieBracket I (fun y ↦ J y (X y)) Y x) -
        J x (mlieBracket I X (fun y ↦ J y (Y y)) x) :=
  J.nijenhuis_apply_eq_nijenhuisAux hX hY

/-- Tangent vectors at `x` are values at `x` of vector fields differentiable there, so statements
about the Nijenhuis tensor at `x` reduce to statements about the Nijenhuis expression. -/
private lemma nijenhuis_apply_extend (v w : TangentSpace I x) :
    J.nijenhuis x v w = J.nijenhuisAux (extend E v) (extend E w) x := by
  conv_lhs => rw [← extend_apply_self E v, ← extend_apply_self E w]
  exact J.nijenhuis_apply_eq_nijenhuisAux (mdifferentiableAt_extend ..)
    (mdifferentiableAt_extend ..)

/-- The Nijenhuis tensor vanishes everywhere exactly when
`[JX, JY] = [X, Y] + J[JX, Y] + J[X, JY]` for all vector fields differentiable at the point. -/
theorem nijenhuis_eq_zero_iff :
    J.nijenhuis = 0 ↔ ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
        mlieBracket I (fun y ↦ J y (X y)) (fun y ↦ J y (Y y)) x =
          mlieBracket I X Y x + J x (mlieBracket I (fun y ↦ J y (X y)) Y x) +
            J x (mlieBracket I X (fun y ↦ J y (Y y)) x) := by
  constructor
  · intro h X Y x hX hY
    have h' := J.nijenhuis_apply hX hY
    rw [h, Pi.zero_apply, zero_apply, zero_apply] at h'
    rw [← sub_eq_zero, ← sub_sub, ← sub_sub, ← h']
  · intro h
    ext x v w
    rw [nijenhuis_apply_extend, nijenhuisAux,
      h (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
    simp only [Pi.zero_apply, zero_apply]
    abel

/-- The Nijenhuis tensor is skew-symmetric. -/
theorem nijenhuis_antisymm (v w : TangentSpace I x) :
    J.nijenhuis x v w = -J.nijenhuis x w v := by
  rw [nijenhuis_apply_extend, nijenhuis_apply_extend, nijenhuisAux_swap]

/-- The Nijenhuis tensor vanishes on the diagonal. -/
@[simp]
theorem nijenhuis_self (v : TangentSpace I x) : J.nijenhuis x v v = 0 := by
  linear_combination (norm := module) (2⁻¹ : ℝ) • J.nijenhuis_antisymm v v

/-- The Nijenhuis tensor anti-commutes with `J` in its first argument:
`N_J(Jv, w) = -J N_J(v, w)`. -/
@[simp]
theorem nijenhuis_apply_left (v w : TangentSpace I x) :
    J.nijenhuis x (J x v) w = -J x (J.nijenhuis x v w) := by
  have := FiniteDimensional.complete ℝ E
  have hJX := J.mdifferentiableAt_apply_field (mdifferentiableAt_extend I E v)
  conv_lhs => rw [← extend_apply_self E v, ← extend_apply_self E w]
  rw [J.nijenhuis_apply_eq_nijenhuisAux hJX (mdifferentiableAt_extend ..),
    J.nijenhuisAux_apply_left, nijenhuis_apply_extend]

/-- The Nijenhuis tensor anti-commutes with `J` in its second argument:
`N_J(v, Jw) = -J N_J(v, w)`. -/
@[simp]
theorem nijenhuis_apply_right (v w : TangentSpace I x) :
    J.nijenhuis x v (J x w) = -J x (J.nijenhuis x v w) := by
  rw [nijenhuis_antisymm, nijenhuis_apply_left, J.nijenhuis_antisymm w v]
  simp

/-- Applying `J` to both arguments of the Nijenhuis tensor changes its sign:
`N_J(Jv, Jw) = -N_J(v, w)`. -/
theorem nijenhuis_apply_both (v w : TangentSpace I x) :
    J.nijenhuis x (J x v) (J x w) = -J.nijenhuis x v w := by
  rw [nijenhuis_apply_left, nijenhuis_apply_right]
  simp

/-- The almost complex structures `J` and `-J` have the same Nijenhuis tensor. -/
@[simp]
theorem nijenhuis_neg (x : M) : (-J).nijenhuis x = J.nijenhuis x := by
  ext v w
  rw [nijenhuis_apply_extend, nijenhuis_apply_extend]
  -- `(-J) X = -(J X)` pointwise; `← Pi.neg_def` folds this into `-(J X)`, the form used by
  -- `mlieBracket_neg_left` and `mlieBracket_neg_right`.
  simp only [nijenhuisAux, neg_apply, ← Pi.neg_def, mlieBracket_neg_left, mlieBracket_neg_right,
    map_neg]
  abel

/-! ### Type identities on the complexified tangent space

Extend the Nijenhuis tensor complex-bilinearly to the complexification `ℂ ⊗[ℝ] T_x M`. By its
anti-commutation with `J` in each argument, it maps two vectors of type `(0,1)` to a vector of
type `(1,0)` and two vectors of type `(1,0)` to a vector of type `(0,1)`, and it vanishes on a
vector of type `(1,0)` and one of type `(0,1)`. On the `(0,1)`- and `(1,0)`-parts of real
tangent vectors, `N_J(v^(0,1), w^(0,1)) = N_J(v, w)^(1,0)` and
`N_J(v^(1,0), w^(1,0)) = N_J(v, w)^(0,1)`. -/

section Complexification

open LinearMap (BilinMap)
open Module.End
open scoped TensorProduct

/-- `N_J(Jv, w) = -J N_J(v, w)`, in the form consumed by the complexification lemmas. -/
private lemma toLinearMap₁₂_nijenhuis_apply_left (v w : TangentSpace I x) :
    (J.nijenhuis x).toLinearMap₁₂ (J.almostComplexStructureAt x v) w =
      -J.almostComplexStructureAt x ((J.nijenhuis x).toLinearMap₁₂ v w) := by
  simp

/-- `N_J(v, Jw) = -J N_J(v, w)`, in the form consumed by the complexification lemmas. -/
private lemma toLinearMap₁₂_nijenhuis_apply_right (v w : TangentSpace I x) :
    (J.nijenhuis x).toLinearMap₁₂ v (J.almostComplexStructureAt x w) =
      -J.almostComplexStructureAt x ((J.nijenhuis x).toLinearMap₁₂ v w) := by
  simp

/-- The complex-bilinear extension of the Nijenhuis tensor maps an eigenvector of the
complexified `J` for the eigenvalue `μ` in its first argument into the eigenspace for `-μ`. In
particular it maps a vector of type `(0,1)` and any second vector to a vector of type `(1,0)`. -/
theorem baseChange_nijenhuis_mem_eigenspace_neg_of_mem_left {μ : ℂ}
    {X : ℂ ⊗[ℝ] TangentSpace I x}
    (hX : X ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) μ)
    (Y : ℂ ⊗[ℝ] TangentSpace I x) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂ X Y ∈
      eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-μ) :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_mem_eigenspace_neg_of_mem_left
    J.toLinearMap₁₂_nijenhuis_apply_left hX Y

/-- The complex-bilinear extension of the Nijenhuis tensor maps an eigenvector of the
complexified `J` for the eigenvalue `μ` in its second argument into the eigenspace for `-μ`. -/
theorem baseChange_nijenhuis_mem_eigenspace_neg_of_mem_right (X : ℂ ⊗[ℝ] TangentSpace I x)
    {μ : ℂ} {Y : ℂ ⊗[ℝ] TangentSpace I x}
    (hY : Y ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) μ) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂ X Y ∈
      eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-μ) :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_mem_eigenspace_neg_of_mem_right
    J.toLinearMap₁₂_nijenhuis_apply_right X hY

/-- The complex-bilinear extension of the Nijenhuis tensor vanishes on a vector of type `(1,0)`
and a vector of type `(0,1)`. -/
theorem baseChange_nijenhuis_eq_zero_of_mem_eigenspace_I_of_mem_neg_I
    {X Y : ℂ ⊗[ℝ] TangentSpace I x}
    (hX : X ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I)
    (hY : Y ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I)) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂ X Y = 0 :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_eq_zero_of_mem_eigenspace_I_of_mem_neg_I
    J.toLinearMap₁₂_nijenhuis_apply_left J.toLinearMap₁₂_nijenhuis_apply_right hX hY

/-- The complex-bilinear extension of the Nijenhuis tensor vanishes on a vector of type `(0,1)`
and a vector of type `(1,0)`. -/
theorem baseChange_nijenhuis_eq_zero_of_mem_eigenspace_neg_I_of_mem_I
    {X Y : ℂ ⊗[ℝ] TangentSpace I x}
    (hX : X ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I))
    (hY : Y ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂ X Y = 0 :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_eq_zero_of_mem_eigenspace_neg_I_of_mem_I
    J.toLinearMap₁₂_nijenhuis_apply_left J.toLinearMap₁₂_nijenhuis_apply_right hX hY

/-- The complex-bilinear extension of the Nijenhuis tensor vanishes on the `(1,0)`-part of `v` and
the `(0,1)`-part of `w`. -/
@[simp]
theorem baseChange_nijenhuis_holomorphicPart_antiholomorphicPart (v w : TangentSpace I x) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂
        ((J.almostComplexStructureAt x).holomorphicPart v)
        ((J.almostComplexStructureAt x).antiholomorphicPart w) = 0 :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_holomorphicPart_antiholomorphicPart
    J.toLinearMap₁₂_nijenhuis_apply_left J.toLinearMap₁₂_nijenhuis_apply_right v w

/-- The complex-bilinear extension of the Nijenhuis tensor vanishes on the `(0,1)`-part of `v` and
the `(1,0)`-part of `w`. -/
@[simp]
theorem baseChange_nijenhuis_antiholomorphicPart_holomorphicPart (v w : TangentSpace I x) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂
        ((J.almostComplexStructureAt x).antiholomorphicPart v)
        ((J.almostComplexStructureAt x).holomorphicPart w) = 0 :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_antiholomorphicPart_holomorphicPart
    J.toLinearMap₁₂_nijenhuis_apply_left J.toLinearMap₁₂_nijenhuis_apply_right v w

/-- **The type identity of the Nijenhuis tensor.** Its complex-bilinear extension maps the
`(0,1)`-parts of `v` and `w` to the `(1,0)`-part of `N_J(v, w)`:
`N_J(v^(0,1), w^(0,1)) = N_J(v, w)^(1,0)`. -/
@[simp]
theorem baseChange_nijenhuis_antiholomorphicPart_antiholomorphicPart (v w : TangentSpace I x) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂
        ((J.almostComplexStructureAt x).antiholomorphicPart v)
        ((J.almostComplexStructureAt x).antiholomorphicPart w) =
      (J.almostComplexStructureAt x).holomorphicPart (J.nijenhuis x v w) :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_antiholomorphicPart_antiholomorphicPart
    J.toLinearMap₁₂_nijenhuis_apply_left J.toLinearMap₁₂_nijenhuis_apply_right v w

/-- The conjugate type identity of the Nijenhuis tensor: its complex-bilinear extension maps the
`(1,0)`-parts of `v` and `w` to the `(0,1)`-part of `N_J(v, w)`:
`N_J(v^(1,0), w^(1,0)) = N_J(v, w)^(0,1)`. -/
@[simp]
theorem baseChange_nijenhuis_holomorphicPart_holomorphicPart (v w : TangentSpace I x) :
    BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂
        ((J.almostComplexStructureAt x).holomorphicPart v)
        ((J.almostComplexStructureAt x).holomorphicPart w) =
      (J.almostComplexStructureAt x).antiholomorphicPart (J.nijenhuis x v w) :=
  (J.almostComplexStructureAt x).bilinMap_baseChange_holomorphicPart_holomorphicPart
    J.toLinearMap₁₂_nijenhuis_apply_left J.toLinearMap₁₂_nijenhuis_apply_right v w

end Complexification

end SmoothAlmostComplexStructure

section Const

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A constant almost complex structure on a finite-dimensional real vector space has vanishing
Nijenhuis tensor. -/
@[simp]
theorem SmoothAlmostComplexStructure.nijenhuis_const (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v)
    (x : V) : (SmoothAlmostComplexStructure.const Jc hJc).nijenhuis x = 0 := by
  -- Constant vector fields have constant images under a constant `J`, and all Lie brackets of
  -- constant vector fields on a vector space vanish by `mlieBracket_const_model_space`.
  have hconst (u : V) :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt (𝕜 := ℝ) (V := fun _ ↦ u) (x := x) (n := 1)).mpr
      contDiffAt_const).mdifferentiableAt one_ne_zero
  -- The constant structure applied to a constant field is the constant map `V → V` with value
  -- `Jc u`; rewriting to this form exposes it to `mlieBracket_const_model_space`.
  have hJ (u : V) :
      (fun y ↦ SmoothAlmostComplexStructure.const Jc hJc y ((fun _ : V ↦ u) y)) =
        fun _ : V ↦ Jc u :=
    funext fun y ↦ congrArg (fun A : V →L[ℝ] V ↦ A u) (const_toEndomorphism_apply Jc hJc y)
  -- Tangent vectors of the model space are vectors of `V`, so that the constant fields below are
  -- maps `V → V`.
  have key (v w : V) : (SmoothAlmostComplexStructure.const Jc hJc).nijenhuis x v w = 0 := by
    rw [show v = (fun _ : V ↦ v) x from rfl, show w = (fun _ : V ↦ w) x from rfl,
      nijenhuis_apply _ (hconst v) (hconst w), hJ, hJ]
    simp only [mlieBracket_const_model_space]
    rw [map_zero]
    simp
  ext v w
  exact key v w

end Const

end TauCeti
