/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Algebra.Module.FunLike
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Test functions on a Lie group

A *test function* on a manifold `G` modelled on `I` is a smooth complex-valued function with
compact support. For a real Lie group `G` these are the functions `C_c^∞(G)` that act on smooth
representations by integration and serve as the archimedean factor of adelic test functions.

This file sets up the type `LieTestFunction I G` of these functions with its complex vector-space
structure, and the operations that use the group law: left and right translation, inversion
`a ↦ a (g⁻¹)`, complex conjugation and the involution `a ↦ a^*`, `a^* g = conj (a g⁻¹)`.

It is modelled on Mathlib's `TestFunction`, which treats test functions on an open subset of a
normed space; `LieTestFunction I G` uses `ContMDiff` in its place, since a Lie group is in general
not an open subset of a normed space.

## Main definitions

* `TauCeti.LieTestFunction I G`: the smooth complex functions on `G` with compact support.
* `TauCeti.LieTestFunction.toContMDiffMap`: a test function as a bundled smooth map.
* `TauCeti.LieTestFunction.leftTranslate g`: the left translation `a ↦ (x ↦ a (g⁻¹ * x))`.
* `TauCeti.LieTestFunction.rightTranslate g`: the right translation `a ↦ (x ↦ a (x * g))`.
* `TauCeti.LieTestFunction.inversion`: `a ↦ (x ↦ a x⁻¹)`.
* `TauCeti.LieTestFunction.conj`: pointwise complex conjugation, a conjugate-linear map.
* `TauCeti.LieTestFunction.involution`: `a ↦ (x ↦ conj (a x⁻¹))`, a conjugate-linear involution.

## Main results

* `TauCeti.LieTestFunction.tsupport_leftTranslate`, `tsupport_rightTranslate`,
  `tsupport_inversion`, `tsupport_conj`, `tsupport_involution`: the support closures of the
  transformed functions, in pointwise form (`g • K`, `MulOpposite.op g⁻¹ • K`, `K⁻¹`); the same
  formulas hold for the supports.

## Conventions

Right translation is `R(y) a (x) = a (x * y)` and left translation is `L(y) a (x) = a (y⁻¹ * x)`,
so that `L(x) ∘ L(y) = L(x * y)` and `R(x) ∘ R(y) = R(x * y)`.
-/

public section

open Function Set
open scoped ContDiff Manifold Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G]

/-- The test functions on a manifold `G` modelled on `I`: smooth complex-valued functions on `G`
with compact support. For a real Lie group `G` this is the space `C_c^∞(G)`. -/
structure LieTestFunction where
  /-- The underlying function. Use the coercion instead. -/
  protected toFun : G → ℂ
  protected contMDiff' : ContMDiff I 𝓘(ℝ, ℂ) ∞ toFun
  protected hasCompactSupport' : HasCompactSupport toFun

namespace LieTestFunction

variable {I G}

instance : FunLike (LieTestFunction I G) G ℂ where
  coe a := a.toFun
  coe_injective a b h := by cases a; cases b; congr

/-- A test function is smooth. -/
protected theorem contMDiff (a : LieTestFunction I G) : ContMDiff I 𝓘(ℝ, ℂ) ∞ a :=
  a.contMDiff'

/-- A test function has compact support. -/
protected theorem hasCompactSupport (a : LieTestFunction I G) : HasCompactSupport a :=
  a.hasCompactSupport'

/-- A test function is continuous. -/
@[fun_prop]
protected theorem continuous (a : LieTestFunction I G) : Continuous a :=
  a.contMDiff.continuous

@[simp]
theorem toFun_eq_coe (a : LieTestFunction I G) : a.toFun = (a : G → ℂ) :=
  (rfl)

/-- See note [custom simps projection]. -/
def Simps.coe (a : LieTestFunction I G) : G → ℂ := a

initialize_simps_projections LieTestFunction (toFun → coe, as_prefix coe)

@[ext]
theorem ext {a b : LieTestFunction I G} (h : ∀ x, a x = b x) : a = b :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk {f : G → ℂ} {hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f} {hc : HasCompactSupport f} :
    ⇑(LieTestFunction.mk f hf hc) = f :=
  (rfl)

/-- A test function as a bundled smooth map. -/
def toContMDiffMap (a : LieTestFunction I G) : C^∞⟮I, G; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨a, a.contMDiff⟩

@[simp]
theorem coe_toContMDiffMap (a : LieTestFunction I G) : ⇑a.toContMDiffMap = a :=
  (rfl)

theorem toContMDiffMap_injective :
    Injective (toContMDiffMap : LieTestFunction I G → C^∞⟮I, G; 𝓘(ℝ, ℂ), ℂ⟯) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

/-- A smooth map with compact support, as a test function. -/
def ofContMDiffMap (f : C^∞⟮I, G; 𝓘(ℝ, ℂ), ℂ⟯) (hf : HasCompactSupport f) :
    LieTestFunction I G :=
  ⟨f, f.contMDiff, hf⟩

@[simp]
theorem coe_ofContMDiffMap (f : C^∞⟮I, G; 𝓘(ℝ, ℂ), ℂ⟯) (hf : HasCompactSupport f) :
    ⇑(ofContMDiffMap f hf) = f :=
  (rfl)

section Module

instance : Zero (LieTestFunction I G) where
  zero := ⟨0, contMDiff_const, .zero⟩

instance : IsZeroApply (LieTestFunction I G) where

instance : Add (LieTestFunction I G) where
  add a b := ⟨a + b, a.contMDiff.add b.contMDiff, a.hasCompactSupport.add b.hasCompactSupport⟩

instance : IsAddApply (LieTestFunction I G) where

instance : Neg (LieTestFunction I G) where
  neg a := ⟨-a, a.contMDiff.neg, a.hasCompactSupport.neg⟩

instance : IsNegApply (LieTestFunction I G) where

instance : Sub (LieTestFunction I G) where
  sub a b := ⟨a - b, a.contMDiff.sub b.contMDiff, a.hasCompactSupport.sub b.hasCompactSupport⟩

instance : IsSubApply (LieTestFunction I G) where

instance {R : Type*} [Semiring R] [Module R ℂ] [SMulCommClass ℝ R ℂ] [ContinuousConstSMul R ℂ] :
    SMul R (LieTestFunction I G) where
  smul c a := ⟨c • ⇑a, (contDiff_const_smul c).contMDiff.comp a.contMDiff,
    a.hasCompactSupport.smul_left⟩

instance {R : Type*} [Semiring R] [Module R ℂ] [SMulCommClass ℝ R ℂ] [ContinuousConstSMul R ℂ] :
    IsSMulApply R (LieTestFunction I G) where
  smul_apply _ _ _ := rfl

instance : AddCommGroup (LieTestFunction I G) := fast_instance% FunLike.addCommGroup

instance {R : Type*} [Semiring R] [Module R ℂ] [SMulCommClass ℝ R ℂ] [ContinuousConstSMul R ℂ] :
    Module R (LieTestFunction I G) := fast_instance% FunLike.module

variable (I G) in
/-- The coercion of test functions to functions, as a `ℂ`-linear map. -/
def toFunction : LieTestFunction I G →ₗ[ℂ] G → ℂ where
  toFun a := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem toFunction_apply (a : LieTestFunction I G) : toFunction I G a = a :=
  (rfl)

theorem toFunction_injective : Injective (toFunction I G) :=
  DFunLike.coe_injective

end Module

section Conj

/-- Pointwise complex conjugation of test functions, a conjugate-linear map. -/
def conj : LieTestFunction I G →ₗ⋆[ℂ] LieTestFunction I G where
  toFun a := ⟨fun x ↦ starRingEnd ℂ (a x), Complex.conjCLE.contDiff.contMDiff.comp a.contMDiff,
    a.hasCompactSupport.comp_left (map_zero _)⟩
  map_add' a b := ext fun x ↦ map_add (starRingEnd ℂ) (a x) (b x)
  map_smul' c a := ext fun x ↦ map_mul (starRingEnd ℂ) c (a x)

@[simp]
theorem conj_apply (a : LieTestFunction I G) (x : G) : conj a x = starRingEnd ℂ (a x) :=
  (rfl)

@[simp]
theorem conj_conj (a : LieTestFunction I G) : conj (conj a) = a :=
  ext fun x ↦ by simp

@[simp]
theorem support_conj (a : LieTestFunction I G) : support (conj a) = support a := by
  ext x
  simp

@[simp]
theorem tsupport_conj (a : LieTestFunction I G) : tsupport (conj a) = tsupport a := by
  rw [tsupport, support_conj, tsupport]

end Conj

section LieGroup

variable [Group G] [LieGroup I ∞ G]

/-- Left translation of test functions by `g`: `leftTranslate g a x = a (g⁻¹ * x)`. -/
def leftTranslate (g : G) : LieTestFunction I G →ₗ[ℂ] LieTestFunction I G :=
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  { toFun a := ⟨fun x ↦ a (g⁻¹ * x), a.contMDiff.comp (contMDiff_mul_left (I := I) (n := ∞)),
      a.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem leftTranslate_apply (g : G) (a : LieTestFunction I G) (x : G) :
    leftTranslate g a x = a (g⁻¹ * x) :=
  (rfl)

@[simp]
theorem leftTranslate_one (a : LieTestFunction I G) : leftTranslate 1 a = a :=
  ext fun x ↦ by simp

theorem leftTranslate_mul (g h : G) (a : LieTestFunction I G) :
    leftTranslate (g * h) a = leftTranslate g (leftTranslate h a) :=
  ext fun x ↦ by simp [mul_assoc]

@[simp]
theorem support_leftTranslate (g : G) (a : LieTestFunction I G) :
    support (leftTranslate g a) = g • support a := by
  ext x
  simp [Set.mem_smul_set_iff_inv_smul_mem]

@[simp]
theorem tsupport_leftTranslate (g : G) (a : LieTestFunction I G) :
    tsupport (leftTranslate g a) = g • tsupport a := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [tsupport, support_leftTranslate, closure_smul, tsupport]

/-- Right translation of test functions by `g`: `rightTranslate g a x = a (x * g)`. -/
def rightTranslate (g : G) : LieTestFunction I G →ₗ[ℂ] LieTestFunction I G :=
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  { toFun a := ⟨fun x ↦ a (x * g), a.contMDiff.comp (contMDiff_mul_right (I := I) (n := ∞)),
      a.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight g)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem rightTranslate_apply (g : G) (a : LieTestFunction I G) (x : G) :
    rightTranslate g a x = a (x * g) :=
  (rfl)

@[simp]
theorem rightTranslate_one (a : LieTestFunction I G) : rightTranslate 1 a = a :=
  ext fun x ↦ by simp

theorem rightTranslate_mul (g h : G) (a : LieTestFunction I G) :
    rightTranslate (g * h) a = rightTranslate g (rightTranslate h a) :=
  ext fun x ↦ by simp [mul_assoc]

@[simp]
theorem support_rightTranslate (g : G) (a : LieTestFunction I G) :
    support (rightTranslate g a) = MulOpposite.op g⁻¹ • support a := by
  ext x
  simp [Set.mem_smul_set_iff_inv_smul_mem]

@[simp]
theorem tsupport_rightTranslate (g : G) (a : LieTestFunction I G) :
    tsupport (rightTranslate g a) = MulOpposite.op g⁻¹ • tsupport a := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [tsupport, support_rightTranslate, closure_smul, tsupport]

/-- The inversion of test functions: `inversion a x = a x⁻¹`. -/
def inversion : LieTestFunction I G →ₗ[ℂ] LieTestFunction I G :=
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  { toFun a := ⟨fun x ↦ a x⁻¹, a.contMDiff.comp (contMDiff_inv I ∞),
      a.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem inversion_apply (a : LieTestFunction I G) (x : G) : inversion a x = a x⁻¹ :=
  (rfl)

@[simp]
theorem inversion_inversion (a : LieTestFunction I G) : inversion (inversion a) = a :=
  ext fun x ↦ by simp

@[simp]
theorem support_inversion (a : LieTestFunction I G) : support (inversion a) = (support a)⁻¹ := by
  ext x
  simp

@[simp]
theorem tsupport_inversion (a : LieTestFunction I G) :
    tsupport (inversion a) = (tsupport a)⁻¹ := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [tsupport, support_inversion, ← inv_closure, tsupport]

theorem inversion_leftTranslate (g : G) (a : LieTestFunction I G) :
    inversion (leftTranslate g a) = rightTranslate g (inversion a) :=
  ext fun x ↦ by simp

theorem inversion_rightTranslate (g : G) (a : LieTestFunction I G) :
    inversion (rightTranslate g a) = leftTranslate g (inversion a) :=
  ext fun x ↦ by simp

theorem conj_inversion (a : LieTestFunction I G) : conj (inversion a) = inversion (conj a) :=
  (rfl)

/-- The involution of test functions, `involution a x = conj (a x⁻¹)`. For a unimodular group
this is the involution for which the integrated action of `involution a` in a unitary
representation is the adjoint of that of `a`. -/
def involution : LieTestFunction I G →ₗ⋆[ℂ] LieTestFunction I G :=
  conj.comp inversion

@[simp]
theorem involution_apply (a : LieTestFunction I G) (x : G) :
    involution a x = starRingEnd ℂ (a x⁻¹) :=
  (rfl)

theorem involution_eq_conj_inversion (a : LieTestFunction I G) :
    involution a = conj (inversion a) :=
  (rfl)

@[simp]
theorem involution_involution (a : LieTestFunction I G) : involution (involution a) = a :=
  ext fun x ↦ by simp

@[simp]
theorem support_involution (a : LieTestFunction I G) :
    support (involution a) = (support a)⁻¹ := by
  ext x
  simp

@[simp]
theorem tsupport_involution (a : LieTestFunction I G) :
    tsupport (involution a) = (tsupport a)⁻¹ := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [tsupport, support_involution, ← inv_closure, tsupport]

end LieGroup

end LieTestFunction

end TauCeti
