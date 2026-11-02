/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Lifting.Relative
public import TauCeti.Topology.Homotopy.Cube.OpenBox

/-!
# Relative lifting on parameterized cube cylinders

Homotopy lifting for `A × (I × Iᴺ)` gives lifting relative to the bottom and boundary sides
of each cube cylinder, continuously in the parameter space `A`. The prescribed lift need only
be defined on that subspace. The proof applies zero-set strong-deformation-retract lifting
to the radial deformation, keeping the `A` coordinate fixed.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, relative homotopy lifting for fibrations.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
-/

public noncomputable section

open Set unitInterval

namespace TauCeti

variable {N : Type*} [Finite N] {A : Type*} [TopologicalSpace A]
variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- Homotopy lifting for a parameterized cube cylinder extends compatible lifts on its bottom
and boundary sides, continuously in an arbitrary parameter space `A`. -/
theorem HasHomotopyLiftingProperty.exists_lift_openBox
    (hp : HasHomotopyLiftingProperty p (A × (I × (N → I))))
    (f : C({y : A × (I × (N → I)) | y.2 ∈ cylinderExtensionDomain (Cube.boundary N)}, E))
    (H : C(A × (I × (N → I)), B)) (hf : ∀ x, p (f x) = H x) :
    ∃ G : C(A × (I × (N → I)), E), p ∘ G = H ∧
      ∀ x : {y : A × (I × (N → I)) | y.2 ∈ cylinderExtensionDomain (Cube.boundary N)},
        G x = f x := by
  let := Fintype.ofFinite N
  let J : Set (A × (I × (N → I))) :=
    {y | y.2 ∈ cylinderExtensionDomain (Cube.boundary N)}
  let r : C(A × (I × (N → I)), J) :=
    ⟨fun y ↦ ⟨(y.1, cubeLiftDeform 0 y.2), cubeLiftDeform_zero_mem y.2⟩,
      (continuous_fst.prodMk (continuous_cubeLiftDeform.comp
        (continuous_const.prodMk continuous_snd))).subtype_mk _⟩
  let τ : C(A × (I × (N → I)), I) :=
    ⟨fun y ↦ ⟨cubeLiftTime y.2, cubeLiftTime_mem y.2⟩,
      (continuous_cubeLiftTime.comp continuous_snd).subtype_mk _⟩
  apply hp.zeroSetSDR_liftingInclusion τ
    (fun y ↦ Subtype.ext_iff.trans (cubeLiftTime_eq_zero_iff y.2)) r ?_ f H hf
  exact ⟨{
    toFun := fun y ↦ (y.2.1, cubeLiftDeform (σ y.1) y.2.2)
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_cubeLiftDeform.comp ((continuous_symm.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd)))
    map_zero_left := fun _ ↦ by simp
    map_one_left := fun _ ↦ by simp [r]
    prop' := fun s _ hy ↦ by simp [cubeLiftDeform_of_mem (σ s) hy] }⟩

end TauCeti
