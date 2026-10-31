/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.Homotopy.HurewiczFibration.RelativeLifting
public import TauCeti.Topology.Homotopy.Cube.Radius

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

The radial geometry extends the square construction in
`TauCeti.Topology.Homotopy.OpenBoxLifting`, using `cubeRadius` and `cubeScale` for the
finite-dimensional cube geometry. The final lifting step reuses
`HasHomotopyLiftingProperty.zeroSetSDR_liftingInclusion`.
-/

public noncomputable section

open Set unitInterval

namespace TauCeti

section Radial

variable {N : Type*} [Fintype N]

/-- The radial denominator for the bottom-and-sides projection. -/
private def cubeLiftDen (x : I × (N → I)) : ℝ :=
  max (2 - (x.1 : ℝ)) (2 * cubeRadius x.2)

private theorem one_le_cubeLiftDen (x : I × (N → I)) : 1 ≤ cubeLiftDen x :=
  le_max_of_le_left (by linarith [x.1.2.2])

private theorem cubeLiftDen_le_two (x : I × (N → I)) : cubeLiftDen x ≤ 2 :=
  max_le (by linarith [x.1.2.1]) (by linarith [cubeRadius_le_one x.2])

/-- Time at which the radial deformation reaches `x`. -/
private def cubeLiftTime (x : I × (N → I)) : ℝ := 2 / cubeLiftDen x - 1

private theorem cubeLiftTime_mem (x : I × (N → I)) : cubeLiftTime x ∈ I := by
  have hd : 0 < cubeLiftDen x := lt_of_lt_of_le one_pos (one_le_cubeLiftDen x)
  constructor
  · rw [cubeLiftTime, sub_nonneg, le_div_iff₀ hd]
    linarith [cubeLiftDen_le_two x]
  · rw [cubeLiftTime, sub_le_iff_le_add, div_le_iff₀ hd]
    linarith [one_le_cubeLiftDen x]

private theorem continuous_cubeLiftTime : Continuous (cubeLiftTime (N := N)) := by
  have hd : Continuous (cubeLiftDen (N := N)) :=
    (continuous_const.sub (by fun_prop)).max
      (continuous_const.mul (continuous_cubeRadius.comp continuous_snd))
  exact (continuous_const.div hd fun x ↦
    (lt_of_lt_of_le one_pos (one_le_cubeLiftDen x)).ne').sub continuous_const

private theorem cubeLiftTime_eq_zero {x : I × (N → I)}
    (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) : cubeLiftTime x = 0 := by
  have hd : cubeLiftDen x = 2 := by
    refine le_antisymm (cubeLiftDen_le_two x) ?_
    rcases mem_cylinderExtensionDomain_iff.1 hx with ht | hz
    · exact le_max_of_le_left (by simp [ht])
    · exact le_max_of_le_right (by rw [(cubeRadius_eq_one_iff x.2).2 hz]; norm_num)
  simp [cubeLiftTime, hd]

/-- Run the radial segment from the bottom and sides, stopping when it reaches `x`. -/
private def cubeLiftDeform (s : I) (x : I × (N → I)) : I × (N → I) :=
  let a := cubeLiftTime x - min (cubeLiftTime x) (s : ℝ)
  (projIcc 0 1 zero_le_one ((x.1 : ℝ) + a * (x.1 - 2)), cubeScale (1 + a) x.2)

private theorem continuous_cubeLiftDeform :
    Continuous fun y : I × (I × (N → I)) ↦ cubeLiftDeform y.1 y.2 := by
  have ht := continuous_cubeLiftTime.comp (continuous_snd :
    Continuous (Prod.snd : I × (I × (N → I)) → _))
  have ha : Continuous fun y : I × (I × (N → I)) ↦
      cubeLiftTime y.2 - min (cubeLiftTime y.2) (y.1 : ℝ) :=
    ht.sub (ht.min (by fun_prop))
  have hx : Continuous fun y : I × (I × (N → I)) ↦ (y.2.1 : ℝ) := by fun_prop
  exact (continuous_projIcc.comp (hx.add (ha.mul (hx.sub continuous_const)))).prodMk
    (continuous_cubeScale.comp ((continuous_const.add ha).prodMk (by fun_prop)))

private theorem cubeLiftDeform_time (x : I × (N → I)) :
    cubeLiftDeform ⟨cubeLiftTime x, cubeLiftTime_mem x⟩ x = x := by
  simp [cubeLiftDeform]

private theorem cubeLiftDeform_zero_mem (x : I × (N → I)) :
    cubeLiftDeform 0 x ∈ cylinderExtensionDomain (Cube.boundary N) := by
  have hd : 0 < cubeLiftDen x := lt_of_lt_of_le one_pos (one_le_cubeLiftDen x)
  have ht := (cubeLiftTime_mem x).1
  have ha : 1 + cubeLiftTime x = 2 / cubeLiftDen x := by rw [cubeLiftTime]; ring
  have hs : 0 ≤ 2 / cubeLiftDen x := by positivity
  have hr : 2 / cubeLiftDen x * cubeRadius x.2 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hd]
    exact le_max_right _ _
  simp only [cubeLiftDeform, Icc.coe_zero, min_eq_right ht, sub_zero,
    mem_cylinderExtensionDomain_iff]
  rcases max_choice (2 - (x.1 : ℝ)) (2 * cubeRadius x.2) with h | h
  · left
    have hd' : cubeLiftDen x = 2 - (x.1 : ℝ) := h
    have hne : 2 - (x.1 : ℝ) ≠ 0 := by rw [← hd']; exact hd.ne'
    have he : (x.1 : ℝ) + cubeLiftTime x * (x.1 - 2) = 0 := by
      rw [cubeLiftTime, hd']
      field_simp
      ring
    rw [he]
    exact projIcc_left zero_le_one
  · right
    rw [← cubeRadius_eq_one_iff, ha, cubeRadius_cubeScale hs hr]
    have hd' : cubeLiftDen x = 2 * cubeRadius x.2 := h
    rw [div_mul_eq_mul_div, ← hd', div_self hd.ne']

private theorem cubeLiftTime_eq_zero_iff (x : I × (N → I)) :
    cubeLiftTime x = 0 ↔ x ∈ cylinderExtensionDomain (Cube.boundary N) := by
  refine ⟨fun hx ↦ ?_, cubeLiftTime_eq_zero⟩
  have ht : (⟨cubeLiftTime x, cubeLiftTime_mem x⟩ : I) = 0 := Subtype.ext hx
  have he := cubeLiftDeform_time x
  rw [ht] at he
  exact he ▸ cubeLiftDeform_zero_mem x

end Radial

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
    map_zero_left := fun x ↦ by
      simp [cubeLiftDeform, min_eq_left (cubeLiftTime_mem x).2]
    map_one_left := fun _ ↦ by simp [r]
    prop' := fun s x hx ↦ by
      simp [cubeLiftDeform, cubeLiftTime_eq_zero hx, min_eq_left (sub_nonneg.mpr s.2.2)] }⟩

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
