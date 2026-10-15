/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Local rings of holomorphic germs

A germ of a holomorphic function is invertible exactly when its value at the base point
is nonzero. Consequently the stalks of the holomorphic structure sheaf are local rings,
their maximal ideals consist of the germs vanishing at the base point, and their residue
fields are canonically `ℂ` via evaluation. These are the local algebra needed for local
equations of divisors and their invertible sheaves on complex curves.

The results hold for any complex model with corners;
compactness, connectedness, and a manifold regularity assumption are unnecessary.

The unit criterion adapts Heather Macbeth's `smoothSheafCommRing.isUnit_stalk_iff` in
`Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean` to the analytic structure sheaf.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§6 and 16.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X]

/-- A holomorphic germ is a unit exactly when its value at the base point is nonzero. -/
@[simp]
theorem isUnit_stalk_iff {x : X} (f : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    IsUnit f ↔ eval I X x f ≠ 0 := by
  constructor
  · intro hf
    exact (hf.map (eval I X x)).ne_zero
  · intro hf
    let S := (holomorphicStructureSheaf I X).presheaf
    obtain ⟨U, hxU, s, rfl⟩ := S.exists_germ_eq f
    have hs : s ⟨x, hxU⟩ ≠ 0 := by
      simpa only [S, eval_germ] using hf
    let V : Opens X :=
      ⟨Subtype.val '' {y : U | s y ≠ 0},
        U.2.isOpenMap_subtype_val _ ((contMDiff s).continuous.isOpen_preimage _ isOpen_ne)⟩
    have hVU : V ≤ U := Subtype.coe_image_subset _ _
    have hxV : x ∈ V := ⟨⟨x, hxU⟩, hs, rfl⟩
    let t : (holomorphicStructureSheaf I X).obj.obj (op V) := S.map hVU.hom.op s
    have ht (y : V) : t y ≠ 0 := by
      obtain ⟨z, hz, hzy⟩ := y.2
      have hyz : Opens.inclusion hVU y = z := Subtype.ext hzy.symm
      simpa only [t, S, map_apply, hyz, Set.mem_ofPred_eq] using hz
    have hinv : ContMDiff I 𝓘(ℂ) ω (fun y : V ↦ (t y)⁻¹) := by
      intro y
      exact ((contDiffAt_inv ℂ (ht y)).contMDiffAt).comp y (contMDiff t).contMDiffAt
    let u : (holomorphicStructureSheaf I X).obj.obj (op V) :=
      ofContMDiff (fun y : V ↦ (t y)⁻¹) hinv
    have htu : t * u = 1 := by
      apply holomorphicStructureSheaf.ext
      intro y
      rw [mul_apply, one_apply]
      rw [ofContMDiff_apply (fun y : V ↦ (t y)⁻¹) hinv y]
      exact mul_inv_cancel₀ (ht y)
    have hunit : IsUnit (S.germ V x hxV t) :=
      IsUnit.of_mul_eq_one (S.germ V x hxV u) (by
        rw [← map_mul, htu, map_one])
    simpa only [t, S.germ_res_apply hVU.hom x hxV s] using hunit

/-- The nonunits of a holomorphic stalk are exactly the kernel of evaluation. -/
theorem nonunits_stalk (x : X) :
    nonunits ((holomorphicStructureSheaf I X).presheaf.stalk x) =
      RingHom.ker (eval I X x) := by
  ext f
  simp [mem_nonunits_iff]

/-- Stalks of the holomorphic structure sheaf are local rings. -/
instance instIsLocalRingStalk (x : X) :
    IsLocalRing ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [nonunits_stalk]
  exact fun f g ↦ Ideal.add_mem _

/-- The maximal ideal of a holomorphic stalk consists of the germs vanishing at its base point. -/
@[simp]
theorem maximalIdeal_stalk (x : X) :
    IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x) =
      RingHom.ker (eval I X x) := by
  exact (IsLocalRing.ker_eq_maximalIdeal (eval I X x) (eval_surjective I X x)).symm

/-- Evaluation identifies the residue field of a holomorphic stalk with `ℂ`. -/
def residueFieldEquiv (x : X) :
    IsLocalRing.ResidueField ((holomorphicStructureSheaf I X).presheaf.stalk x) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (maximalIdeal_stalk I X x)).trans
    ((eval I X x).quotientKerEquivOfSurjective (eval_surjective I X x))

/-- The residue-field comparison sends the residue of a germ to its value at the base point. -/
@[simp]
theorem residueFieldEquiv_residue (x : X)
    (f : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    residueFieldEquiv I X x (IsLocalRing.residue _ f) = eval I X x f := by
  exact (congrArg ((eval I X x).quotientKerEquivOfSurjective (eval_surjective I X x))
    (Ideal.quotEquivOfEq_mk (maximalIdeal_stalk I X x) f)).trans
      (RingHom.quotientKerEquivOfSurjective_apply_mk (eval_surjective I X x) f)

end TauCeti.holomorphicStructureSheaf
