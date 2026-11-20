/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Smooth maps into trivial bundles

The trivial bundle `Bundle.Trivial B F` has the single global trivialization
`Bundle.Trivial.trivialization B F`, so a map into its total space is smooth (or differentiable at
a point) exactly when its base map and its fibre map into `F` are; in particular its constant
sections are smooth. `Bundle.Trivial.homeomorphProd` upgrades to a `C^n` diffeomorphism
`Bundle.Trivial.diffeomorphProd` between `TotalSpace F (Bundle.Trivial B F)` and `B × F`.
-/

public section

open Bundle
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}

namespace Bundle.Trivial

/-- A map into the trivial bundle is smooth at a point exactly when its base map and its fibre
map are smooth there. -/
theorem contMDiffAt_mk_iff {b : M → B} {f : M → F} {x : M} :
    ContMDiffAt J (I.prod 𝓘(𝕜, F)) n
        (fun y ↦ TotalSpace.mk' F (E := Trivial B F) (b y) (f y)) x ↔
      ContMDiffAt J I n b x ∧ ContMDiffAt J 𝓘(𝕜, F) n f x := by
  rw [Bundle.contMDiffAt_totalSpace_iff]
  simp

/-- A map into the trivial bundle is smooth exactly when its base map and its fibre map are
smooth. -/
theorem contMDiff_mk_iff {b : M → B} {f : M → F} :
    ContMDiff J (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F (E := Trivial B F) (b y) (f y)) ↔
      ContMDiff J I n b ∧ ContMDiff J 𝓘(𝕜, F) n f :=
  (forall_congr' fun _ ↦ contMDiffAt_mk_iff).trans forall_and

/-- A map into the trivial bundle is differentiable at a point exactly when its base map and its
fibre map are differentiable there. -/
theorem mdifferentiableAt_mk_iff {b : M → B} {f : M → F} {x : M} :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F))
        (fun y ↦ TotalSpace.mk' F (E := Trivial B F) (b y) (f y)) x ↔
      MDifferentiableAt J I b x ∧ MDifferentiableAt J 𝓘(𝕜, F) f x := by
  rw [mdifferentiableAt_totalSpace]
  simp

/-- A constant section of the trivial bundle is smooth. -/
theorem contMDiff_mk_const (c : F) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun y : B ↦ TotalSpace.mk' F (E := Trivial B F) y c) :=
  contMDiff_mk_iff.2 ⟨contMDiff_id, contMDiff_const⟩

/-- A constant section of the trivial bundle is differentiable. -/
theorem mdifferentiableAt_mk_const (c : F) {x : B} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y : B ↦ TotalSpace.mk' F (E := Trivial B F) y c) x :=
  mdifferentiableAt_mk_iff.2 ⟨mdifferentiableAt_id, mdifferentiableAt_const⟩

omit [TopologicalSpace B] in
/-- On the trivial line bundle, a function times the constant section `1` is the function. -/
protected theorem smul_one (σ : B → 𝕜) : (σ • (1 : B → 𝕜) : Π y : B, Trivial B 𝕜 y) = σ :=
  funext fun _ ↦ mul_one _

section Diffeomorph

variable (I B F n)

/-- `C^n` diffeomorphism between the total space of the trivial bundle and the Cartesian product,
upgrading `Bundle.Trivial.homeomorphProd`. -/
def diffeomorphProd :
    TotalSpace F (Trivial B F) ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ B × F where
  toFun p := (p.proj, p.snd)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (Bundle.contMDiff_proj (Trivial B F)).prodMk
    ((contMDiff_mk_iff (f := fun p : TotalSpace F (Trivial B F) ↦ p.snd)).mp contMDiff_id).2
  contMDiff_invFun := contMDiff_mk_iff.mpr ⟨contMDiff_fst, contMDiff_snd⟩

/-- Forward formula for `Bundle.Trivial.diffeomorphProd`. -/
@[simp]
theorem diffeomorphProd_apply (p : TotalSpace F (Trivial B F)) :
    diffeomorphProd I B F n p = (p.proj, p.snd) :=
  (rfl)

/-- Inverse formula for `Bundle.Trivial.diffeomorphProd`. -/
@[simp]
theorem diffeomorphProd_symm_apply (q : B × F) :
    (diffeomorphProd I B F n).symm q = ⟨q.1, q.2⟩ :=
  (rfl)

/-- The underlying homeomorphism of `Bundle.Trivial.diffeomorphProd` is
`Bundle.Trivial.homeomorphProd`. -/
@[simp]
theorem toHomeomorph_diffeomorphProd :
    (diffeomorphProd I B F n).toHomeomorph = homeomorphProd B F :=
  Homeomorph.ext fun p ↦ by simp

end Diffeomorph

end Bundle.Trivial
