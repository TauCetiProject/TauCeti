/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.Homotopy.Lifting.OpenBox

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

namespace TopCat

open CategoryTheory

universe u

/-- **Relative cube lifting for a Serre fibration.** A continuous lift on the bottom face and
all boundary sides of `I × Iᴺ`, for any finite index type `N`, extends to a lift of the
entire homotopy. There is no nonemptiness assumption, and an empty index type recovers
lifting with a prescribed starting point. -/
theorem exists_lift_openBox_of_mem_serreFibrations {E B : TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (N : Type*) [Finite N]
    (f : C(cylinderExtensionDomain (Cube.boundary N), E))
    (H : C(I × (N → I), B)) (hf : ∀ x, p (f x) = H x) :
    ∃ G : C(I × (N → I), E), p ∘ G = H ∧
      ∀ x : cylinderExtensionDomain (Cube.boundary N), G x = f x := by
  have h := (mem_serreFibrations_iff_cube.1 hp (Nat.card N + 1)).of_homeomorph
    (cubeSplitHomeomorph (Nat.card N)).symm
  have h := h.of_homeomorph ((Homeomorph.refl I).prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ ↦ I) (Finite.equivFin N)))
  let f' : C({y : Unit × (I × (N → I)) |
      y.2 ∈ cylinderExtensionDomain (Cube.boundary N)}, E) :=
    f.comp ⟨fun y ↦ ⟨y.1.2, y.2⟩, by fun_prop⟩
  obtain ⟨G, hG, hGJ⟩ := (h.of_homeomorph (Homeomorph.uniqueProd Unit _)).exists_lift_openBox
    f' (H.comp ContinuousMap.snd) (fun y ↦ hf ⟨y.1.2, y.2⟩)
  refine ⟨G.comp ⟨fun x ↦ ((), x), by fun_prop⟩,
    funext fun x ↦ congrFun hG ((), x), fun x ↦ ?_⟩
  exact hGJ ⟨((), x.1), x.2⟩

end TopCat

end TauCeti
