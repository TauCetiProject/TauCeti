/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.Homotopy.HurewiczFibration.RelativeLifting
public import TauCeti.Topology.Homotopy.Cube.OpenBox

/-!
# Serre lifting with prescribed cube boundaries

A Serre fibration lifts a homotopy on a finite cube with a prescribed lift on both its
initial face and its boundary cylinder. The prescribed data are continuous only on that
union; no extension of them to the whole cylinder is assumed. This is the relative lifting
needed to keep basepoint tracks fixed when constructing the fibration homotopy sequence.

The proof uses radial projection from the point at height two above the cube's centre.
A deformation runs from the bottom-and-sides subspace to each point, reaching that point
at a continuously varying time which is zero on the prescribed subspace. An ordinary
homotopy lift, evaluated at that time, therefore retains the prescribed values exactly.
In particular, no regular lifting function is required. The zero-dimensional cube is included.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, relative homotopy lifting for fibrations.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.

The radial geometry is shared with the square lifting construction in
`TauCeti.Topology.Homotopy.OpenBoxLifting` through
`TauCeti.Topology.Homotopy.Cube.OpenBox`. The final lifting step reuses
`HasHomotopyLiftingProperty.zeroSetSDR_liftingInclusion`.
-/

public noncomputable section

open Set unitInterval

namespace TauCeti

variable {N : Type*} [Finite N]
variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- A map with the homotopy lifting property for the cube cylinder lifts a homotopy on the
cube with arbitrary prescribed, compatible lifts on its bottom face and boundary cylinder. -/
theorem HasHomotopyLiftingProperty.exists_lift_openBox
    (hp : HasHomotopyLiftingProperty p (I × (N → I)))
    (f : C(cylinderExtensionDomain (Cube.boundary N), E)) (H : C(I × (N → I), B))
    (hf : ∀ x, p (f x) = H x) :
    ∃ G : C(I × (N → I), E), p ∘ G = H ∧
      ∀ x : cylinderExtensionDomain (Cube.boundary N), G x = f x := by
  let := Fintype.ofFinite N
  let r : C(I × (N → I), cylinderExtensionDomain (Cube.boundary N)) :=
    ⟨fun x ↦ ⟨cubeLiftDeform 0 x, cubeLiftDeform_zero_mem x⟩,
      (continuous_cubeLiftDeform.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let τ : C(I × (N → I), I) :=
    ⟨fun x ↦ ⟨cubeLiftTime x, cubeLiftTime_mem x⟩, continuous_cubeLiftTime.subtype_mk _⟩
  apply hp.zeroSetSDR_liftingInclusion τ
    (fun x ↦ Subtype.ext_iff.trans (cubeLiftTime_eq_zero_iff x)) r ?_ f H hf
  exact ⟨{
    toFun := fun y ↦ cubeLiftDeform (σ y.1) y.2
    continuous_toFun := continuous_cubeLiftDeform.comp
      ((continuous_symm.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := fun x ↦ by simp
    map_one_left := fun _ ↦ by simp [r]
    prop' := fun s _ hx ↦ cubeLiftDeform_of_mem (σ s) hx }⟩

namespace TopCat

open CategoryTheory

universe u

/-- **Relative cube lifting for a Serre fibration.** A continuous lift on the bottom face and
all boundary sides of `I × Iⁿ` extends to a lift of the entire homotopy. There is no
nonemptiness assumption, and `n = 0` recovers lifting with a prescribed starting point. -/
theorem exists_lift_openBox_of_mem_serreFibrations {E B : TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (n : ℕ)
    (f : C(cylinderExtensionDomain (Cube.boundary (Fin n)), E))
    (H : C(I × (Fin n → I), B)) (hf : ∀ x, p (f x) = H x) :
    ∃ G : C(I × (Fin n → I), E), p ∘ G = H ∧
      ∀ x : cylinderExtensionDomain (Cube.boundary (Fin n)), G x = f x := by
  have h := (mem_serreFibrations_iff_cube.1 hp (n + 1)).of_homeomorph
    (cubeSplitHomeomorph n).symm
  exact h.exists_lift_openBox f H hf

end TopCat

end TauCeti
