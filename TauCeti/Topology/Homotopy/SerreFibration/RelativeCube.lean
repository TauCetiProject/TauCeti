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

Two maps `G₀`, `G₁ : I × Iᴺ → E` that agree with a point `x₀` on the face `{1} × Iᴺ` and on the
sides `I × ∂Iᴺ`, together with a homotopy of their projections that stays at `p x₀` there, form
exactly such data on the box `I × I^(Option N)`: the coordinate `none` is the homotopy parameter,
the time of the cube is reversed, and the prescribed values are `G₀` and `G₁` on the two ends of
the parameter and `x₀` elsewhere. So the homotopy lifts to a homotopy from `G₀` to `G₁` through
maps that agree with `x₀` there (`TauCeti.TopCat.exists_lift_homotopy_of_mem_serreFibrations`).
This compares two lifts of homotopic cubes: the boundary map of the fibration homotopy sequence
is well defined, and a Serre fibration induces injections of relative homotopy sets.

## Main results

* `TauCeti.TopCat.exists_lift_openBox_of_mem_serreFibrations`: relative cube lifting with a
  prescribed bottom and boundary cylinder.
* `TauCeti.TopCat.exists_lift_homotopy_of_mem_serreFibrations`: lifting a homotopy of cubes with
  prescribed ends, fixed on the face `{1} × Iᴺ` and on the sides.

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
    f.comp ⟨fun y ↦ ⟨y.val.2, y.property⟩, by fun_prop⟩
  obtain ⟨G, hG, hGJ⟩ := (h.of_homeomorph (Homeomorph.uniqueProd Unit _)).exists_lift_openBox
    f' (H.comp ContinuousMap.snd) (fun y ↦ hf ⟨y.val.2, y.property⟩)
  refine ⟨G.comp ⟨fun x ↦ ((), x), by fun_prop⟩,
    funext fun x ↦ congrFun hG ((), x), fun x ↦ ?_⟩
  exact hGJ ⟨((), x.val), x.property⟩

section HomotopyLift

variable {E : Type*} [TopologicalSpace E] {N : Type*} {G₀ G₁ : C(I × (N → I), E)} {x₀ : E}

/-- The values prescribed on the bottom and on the sides of the box `I × I^(Option N)` when lifting
a homotopy from `G₀` to `G₁`, with the coordinate `none` as the homotopy parameter and the time
reversed: `G₀` and `G₁` where the parameter is `0` and `1`, and `x₀` elsewhere. -/
private def boxData (G₀ G₁ : C(I × (N → I), E)) (x₀ : E) (x : I × (Option N → I)) : E :=
  if x.2 none = 0 then G₀ (σ x.1, fun k ↦ x.2 (some k))
  else if x.2 none = 1 then G₁ (σ x.1, fun k ↦ x.2 (some k)) else x₀

private theorem boxData_of_eq_zero {x : I × (Option N → I)} (hx : x.2 none = 0) :
    boxData G₀ G₁ x₀ x = G₀ (σ x.1, fun k ↦ x.2 (some k)) :=
  ite_eq_left hx

private theorem boxData_of_eq_one {x : I × (Option N → I)} (hx : x.2 none = 1) :
    boxData G₀ G₁ x₀ x = G₁ (σ x.1, fun k ↦ x.2 (some k)) := by
  rw [boxData, ite_eq_right (by rw [hx]; exact one_ne_zero), ite_eq_left hx]

private theorem boxData_eq (hG₀ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → G₀ (s, t) = x₀)
    (hG₁ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → G₁ (s, t) = x₀) {x : I × (Option N → I)}
    (hx : x.1 = 0 ∨ (fun k ↦ x.2 (some k)) ∈ Cube.boundary N) : boxData G₀ G₁ x₀ x = x₀ := by
  have h : σ x.1 = 1 ∨ (fun k ↦ x.2 (some k)) ∈ Cube.boundary N :=
    hx.imp_left fun h ↦ by rw [h, symm_zero]
  rw [boxData]
  split_ifs
  exacts [hG₀ _ _ h, hG₁ _ _ h, rfl]

/-- The prescribed values are continuous on the bottom and the sides of the box, where they agree
with `x₀`, `G₀` or `G₁` on closed pieces. -/
private theorem continuousOn_boxData [Finite N]
    (hG₀ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → G₀ (s, t) = x₀)
    (hG₁ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → G₁ (s, t) = x₀) :
    ContinuousOn (boxData G₀ G₁ x₀) (cylinderExtensionDomain (Cube.boundary (Option N))) := by
  set S := {x : I × (Option N → I) | x.1 = 0 ∨ (fun k ↦ x.2 (some k)) ∈ Cube.boundary N}
  set S₀ := {x : I × (Option N → I) | x.2 none = 0}
  set S₁ := {x : I × (Option N → I) | x.2 none = 1}
  have hsub : cylinderExtensionDomain (Cube.boundary (Option N)) ⊆ S ∪ S₀ ∪ S₁ := by
    intro x hx
    rcases mem_cylinderExtensionDomain_iff.1 hx with h | h
    · exact .inl (.inl (.inl h))
    · rcases Cube.boundary_option_iff.1 h with (h | h) | h
      exacts [.inl (.inr h), .inr h, .inl (.inl (.inr h))]
  have hS : IsClosed S := (isClosed_eq continuous_fst continuous_const).union
    (Cube.isClosed_boundary.preimage (by fun_prop))
  have hS₀ : IsClosed S₀ := isClosed_eq (by fun_prop) continuous_const
  have hS₁ : IsClosed S₁ := isClosed_eq (by fun_prop) continuous_const
  refine ContinuousOn.mono ?_ hsub
  exact ((continuousOn_const.congr fun x hx ↦ boxData_eq hG₀ hG₁ hx).union_of_isClosed
    ((G₀.continuous.comp (by fun_prop)).continuousOn.congr fun x hx ↦ boxData_of_eq_zero hx) hS
      hS₀).union_of_isClosed
    ((G₁.continuous.comp (by fun_prop)).continuousOn.congr fun x hx ↦ boxData_of_eq_one hx)
      (hS.union hS₀) hS₁

end HomotopyLift

/-- **Lifting a homotopy of cubes with prescribed ends.** Let `p` be a Serre fibration, and let
`G₀`, `G₁ : I × Iᴺ → E` take the value `x₀` on the face `{1} × Iᴺ` and on the sides `I × ∂Iᴺ`. A
homotopy `K` from `p ∘ G₀` to `p ∘ G₁` through maps taking the value `p x₀` there lifts to a
homotopy from `G₀` to `G₁` through maps taking the value `x₀` there. Only the face `{0} × Iᴺ` is
left free. -/
theorem exists_lift_homotopy_of_mem_serreFibrations {E B : TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) {N : Type*} [Finite N] {x₀ : E} {G₀ G₁ : C(I × (N → I), E)}
    (hG₀ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → G₀ (s, t) = x₀)
    (hG₁ : ∀ s t, (s = 1 ∨ t ∈ Cube.boundary N) → G₁ (s, t) = x₀)
    (K : C(I × (I × (N → I)), B)) (hK₀ : ∀ y, K (0, y) = p (G₀ y))
    (hK₁ : ∀ y, K (1, y) = p (G₁ y))
    (hK : ∀ r s t, (s = 1 ∨ t ∈ Cube.boundary N) → K (r, s, t) = p x₀) :
    ∃ L : C(I × (I × (N → I)), E), (∀ x, p (L x) = K x) ∧ (∀ y, L (0, y) = G₀ y) ∧
      (∀ y, L (1, y) = G₁ y) ∧ ∀ r s t, (s = 1 ∨ t ∈ Cube.boundary N) → L (r, s, t) = x₀ := by
  set ι := piOptionEquivProdHomeomorph fun _ : Option N ↦ I
  -- Lift on the box `I × I^(Option N)`, where the coordinate `none` is the homotopy parameter
  -- and the first coordinate is the reversed time of the cube.
  let f : C(cylinderExtensionDomain (Cube.boundary (Option N)), E) :=
    ⟨_, (continuousOn_boxData hG₀ hG₁).domRestrict⟩
  let H : C(I × (Option N → I), B) := ⟨fun x ↦ K (x.2 none, σ x.1, fun k ↦ x.2 (some k)), by
    fun_prop⟩
  have hf : ∀ x, p (f x) = H x := by
    rintro ⟨x, hx⟩
    simp only [f, H, ContinuousMap.coe_mk, domRestrict_apply]
    rcases mem_cylinderExtensionDomain_iff.1 hx with h | h
    · rw [boxData_eq hG₀ hG₁ (.inl h), hK _ _ _ (.inl (by rw [h, symm_zero]))]
    rcases Cube.boundary_option_iff.1 h with (h | h) | h
    · rw [boxData_of_eq_zero h, h, hK₀]
    · rw [boxData_of_eq_one h, h, hK₁]
    · rw [boxData_eq hG₀ hG₁ (.inr h), hK _ _ _ (.inr h)]
  obtain ⟨L, hL, hLf⟩ := exists_lift_openBox_of_mem_serreFibrations hp (Option N) f H hf
  -- Read back on `I × (I × Iᴺ)`, at the reversed time.
  have hLD {s : I} {y : Option N → I} (hy : σ s = 0 ∨ y ∈ Cube.boundary (Option N)) :
      L (σ s, y) = boxData G₀ G₁ x₀ (σ s, y) :=
    hLf ⟨(σ s, y), mem_cylinderExtensionDomain_iff.2 hy⟩
  refine ⟨⟨fun x ↦ L (σ x.2.1, ι.symm (x.1, x.2.2)), by fun_prop⟩, fun x ↦ ?_, fun y ↦ ?_,
    fun y ↦ ?_, fun r s t h ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk]
    rw [← Function.comp_apply (f := p), hL]
    simp [H, ι]
  · have hy : ι.symm (0, y.2) ∈ Cube.boundary (Option N) :=
      Cube.boundary_option_iff.2 (.inl (.inl (by simp [ι])))
    simp only [ContinuousMap.coe_mk]
    rw [hLD (.inr hy), boxData_of_eq_zero (by simp [ι])]
    simp [ι]
  · have hy : ι.symm (1, y.2) ∈ Cube.boundary (Option N) :=
      Cube.boundary_option_iff.2 (.inl (.inr (by simp [ι])))
    simp only [ContinuousMap.coe_mk]
    rw [hLD (.inr hy), boxData_of_eq_one (by simp [ι])]
    simp [ι]
  · simp only [ContinuousMap.coe_mk]
    rcases h with rfl | ht
    · rw [hLD (.inl symm_one), boxData_eq hG₀ hG₁ (.inl symm_one)]
    · have ht' : (fun k ↦ ι.symm (r, t) (some k)) ∈ Cube.boundary N := by simpa [ι] using ht
      rw [hLD (.inr (Cube.boundary_option_iff.2 (.inr ht'))), boxData_eq hG₀ hG₁ (.inr ht')]

end TopCat

end TauCeti
