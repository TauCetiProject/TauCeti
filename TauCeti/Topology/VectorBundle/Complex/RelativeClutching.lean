/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# The relative clutching number of a complex vector bundle over a square

Let `E` be a complex vector bundle over a space `X`, with finite-dimensional model fibre `F`, and
let `u : I² → X` be a map from the square. A **boundary frame** along `u` is a family of
complex-linear isomorphisms `τ y : F ≃ E (u y)` that depends continuously on `y` along the boundary
`∂I²` of the square; nothing is required of it inside. Such a `τ` is a trivialization of the
pullback `u^* E` over the boundary circle, and the obstruction to extending it over the whole
square is an integer, the **relative clutching number** `TauCeti.relativeClutchingNumber u τ`.
This is the relative first Chern number `c₁^τ(u^* E)` of the pullback bundle over the disc, relative
to the boundary trivialization `τ`, from which the index formulas for Cauchy–Riemann operators on
surfaces with boundary or cylindrical ends are written.

It is computed as follows. Along `u` the bundle has a frame `φ`, continuous on the whole square,
because the square is contractible (`TauCeti.exists_continuous_frame`). On the boundary the
transition `(φ y)⁻¹ ∘ τ y : F ≃ F` expresses the boundary frame `τ` in the frame `φ`, and the
relative clutching number is the winding number of its determinant once counterclockwise around
the boundary of the square: the degree `TauCeti.squareBoundaryDegree` of its normalized determinant
`det / |det|`. It does not depend on the frame `φ`
(`TauCeti.relativeClutchingNumber_eq_squareBoundaryDegree`), since two frames differ by a
continuous family of automorphisms over the whole square, whose determinant has degree `0`.

The relative clutching number has the laws of a relative first Chern number:

* **extension:** it vanishes when `τ` extends to a frame continuous on the whole square
  (`TauCeti.relativeClutchingNumber_eq_zero_of_continuous`);
* **change of boundary frame:** replacing `τ` by `τ ∘ g` for a continuous family `g` of
  automorphisms of `F` along the boundary adds the winding number of `det g`
  (`TauCeti.relativeClutchingNumber_trans`);
* **homotopy:** it is invariant under homotopies of the map and of the boundary frame together
  (`TauCeti.relativeClutchingNumber_eq_of_homotopy`);
* **subdivision:** cutting the square along the vertical segment `s = 1/2`, along which `τ` is also
  continuous, writes it as the sum of the relative clutching numbers of the two halves
  (`TauCeti.relativeClutchingNumber_eq_add`). This is the excision law: relative first Chern
  numbers of pieces glued along a common boundary arc with a common frame add up.

A bundle map carries boundary frames to boundary frames. If `Φ x : E x ≃ E' (f x)` is a family of
complex-linear isomorphisms covering `f : X → Y`, continuous on total spaces, then `E'` along
`f ∘ u` relative to the transported frame `Φ ∘ τ` has the same relative clutching number
(`TauCeti.relativeClutchingNumber_map_of_continuousLinearEquiv`); if the `Φ x` are conjugate
linear, the relative clutching number changes sign
(`TauCeti.relativeClutchingNumber_map_of_conjugateLinear`), because conjugating an automorphism by
a conjugate-linear isomorphism conjugates its determinant.

Finally, it is the clutching number `TauCeti.clutchingNumber` of a sphere relative to a boundary
frame. In a trivialization `e` of `E` defined over the image of the boundary, the relative clutching
number is the difference of the degrees of the clutching functions of `φ` and `τ` read in `e`
(`TauCeti.relativeClutchingNumber_eq_sub`). For a sphere `p : Ω^ (Fin 2) X x`, which sends the
boundary to `x`, this gives `c₁(p^* E) = c₁^τ(p^* E) + deg_e(τ)`
(`TauCeti.clutchingNumber_eq_relativeClutchingNumber_add`): the absolute number is recovered from
the relative one by adding the winding of the boundary frame in the trivialization near the base
point. When `τ` is the frame of the trivialization itself, the two numbers agree
(`TauCeti.clutchingNumber_eq_relativeClutchingNumber`).

## Main definitions

* `TauCeti.relativeClutchingNumber u τ`: the relative clutching number of `E` along `u : I² → X`
  relative to a boundary frame `τ`.

## Main results

* `TauCeti.relativeClutchingNumber_eq_squareBoundaryDegree`: it may be computed from any frame
  along `u`.
* `TauCeti.relativeClutchingNumber_congr`: it only depends on the boundary frame along the
  boundary.
* `TauCeti.relativeClutchingNumber_eq_zero_of_continuous`: it vanishes for a boundary frame that
  extends over the square.
* `TauCeti.relativeClutchingNumber_trans`: change of boundary frame.
* `TauCeti.relativeClutchingNumber_eq_of_homotopy`: homotopy invariance.
* `TauCeti.relativeClutchingNumber_eq_add`: subdivision.
* `TauCeti.relativeClutchingNumber_map_of_continuousLinearEquiv`,
  `TauCeti.relativeClutchingNumber_map_of_conjugateLinear`: complex-linear bundle maps preserve
  relative clutching numbers, and conjugate-linear ones reverse them.
* `TauCeti.relativeClutchingNumber_eq_sub`: the relative clutching number in a trivialization.
* `TauCeti.clutchingNumber_eq_relativeClutchingNumber_add` and
  `TauCeti.clutchingNumber_eq_relativeClutchingNumber`: comparison with the clutching number of a
  sphere.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching, and its relative
  version for a trivialization over the boundary).
* A. Hatcher, *Vector Bundles and K-Theory*, Section 1.2 (clutching functions).
-/

public section

noncomputable section

open Bundle Set
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- The **relative clutching number** of `E` along a map `u : I² → X`, relative to a boundary frame
`τ y : F ≃ E (u y)`: the degree around the boundary of the square of the normalized determinant of
the transition `(φ y)⁻¹ ∘ τ y`, for a frame `φ` of `E` along `u`. It is the relative first Chern
number of `u^* E` relative to the trivialization `τ` over the boundary, and does not depend on `φ`
(`TauCeti.relativeClutchingNumber_eq_squareBoundaryDegree`). Only the values of `τ` on the boundary
of the square matter (`TauCeti.relativeClutchingNumber_congr`), and the laws below assume that `τ`
is continuous there. -/
def relativeClutchingNumber (u : C(Fin 2 → I, X)) (τ : ∀ y, F ≃L[ℂ] E (u y)) : ℤ :=
  squareBoundaryDegree fun y ↦ ((τ y).trans
    ((exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)).choose y).symm
    ).normalizedDet

/-- **The relative clutching number from any frame.** The relative clutching number of `E` along
`u` relative to `τ` is the degree around the boundary of the square of the normalized determinant
of `(φ y)⁻¹ ∘ τ y`, for any continuous frame `φ` along `u`. -/
theorem relativeClutchingNumber_eq_squareBoundaryDegree (u : C(Fin 2 → I, X))
    (τ : ∀ y, F ≃L[ℂ] E (u y)) {φ : ∀ y, F ≃L[ℂ] E (u y)}
    (hφ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2)) :
    relativeClutchingNumber u τ =
      squareBoundaryDegree fun y ↦ ((τ y).trans (φ y).symm).normalizedDet := by
  obtain hφ₀ := (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)).choose_spec
  set φ₀ := (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)).choose
  -- The transitions to `φ` and to `φ₀` differ by a factor continuous on the whole square.
  have h : (fun y ↦ ((τ y).trans (φ y).symm).normalizedDet) =
      (fun y ↦ ((τ y).trans (φ₀ y).symm).normalizedDet) *
        fun y ↦ ((φ₀ y).trans (φ y).symm).normalizedDet :=
    funext fun y ↦
      (ContinuousLinearEquiv.normalizedDet_trans_symm_mul_trans (τ y) (φ₀ y) (φ y).symm).symm
  rw [h, squareBoundaryDegree_mul_of_continuous (continuous_normalizedDet_trans_symm hφ hφ₀),
    relativeClutchingNumber]

/-- The relative clutching number only depends on the boundary frame along the boundary of the
square. -/
theorem relativeClutchingNumber_congr (u : C(Fin 2 → I, X)) {τ τ' : ∀ y, F ≃L[ℂ] E (u y)}
    (h : ∀ y ∈ Cube.boundary (Fin 2), τ y = τ' y) :
    relativeClutchingNumber u τ = relativeClutchingNumber u τ' :=
  squareBoundaryDegree_congr fun y hy ↦ by simp only [h y hy]

/-- **Extension.** If the boundary frame `τ` is continuous on the whole square, its relative
clutching number vanishes. -/
theorem relativeClutchingNumber_eq_zero_of_continuous (u : C(Fin 2 → I, X))
    {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (τ q.1 q.2)) :
    relativeClutchingNumber u τ = 0 := by
  simp [relativeClutchingNumber_eq_squareBoundaryDegree u τ hτ]

/-- **Change of boundary frame.** Replacing the boundary frame `τ` by `τ ∘ g`, for a family `g` of
automorphisms of `F` continuous along the boundary of the square, adds the winding number of
`det g` around the boundary. -/
theorem relativeClutchingNumber_trans (u : C(Fin 2 → I, X)) {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : ContinuousOn (fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (τ q.1 q.2))
      (Cube.boundary (Fin 2) ×ˢ univ))
    {g : (Fin 2 → I) → F ≃L[ℂ] F}
    (hg : ContinuousOn (fun y ↦ (g y : F →L[ℂ] F)) (Cube.boundary (Fin 2))) :
    relativeClutchingNumber u (fun y ↦ (g y).trans (τ y)) =
      relativeClutchingNumber u τ + squareBoundaryDegree fun y ↦ (g y).normalizedDet := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)
  have h : (fun y ↦ (((g y).trans (τ y)).trans (φ y).symm).normalizedDet) =
      (fun y ↦ (g y).normalizedDet) * fun y ↦ ((τ y).trans (φ y).symm).normalizedDet :=
    -- `((g y).trans (τ y)).trans (φ y).symm` is `(g y).trans ((τ y).trans (φ y).symm)` by
    -- definition: both compose the same three maps.
    funext fun y ↦ ContinuousLinearEquiv.normalizedDet_trans (g y) ((τ y).trans (φ y).symm)
  rw [relativeClutchingNumber_eq_squareBoundaryDegree u _ hφ,
    relativeClutchingNumber_eq_squareBoundaryDegree u _ hφ, h,
    squareBoundaryDegree_mul hg.normalizedDet
      (continuousOn_normalizedDet_trans_symm hφ.continuousOn hτ),
    add_comm]

/-- **Homotopy invariance.** Let `H : I × I² → X` be a homotopy and `T` a family of frames along
`H` that is continuous over `I × ∂I²`. The relative clutching numbers of the two ends `H (0, ·)`
and `H (1, ·)`, relative to the boundary frames `T (0, ·)` and `T (1, ·)`, are equal. -/
theorem relativeClutchingNumber_eq_of_homotopy (H : C(I × (Fin 2 → I), X))
    {T : ∀ q, F ≃L[ℂ] E (H q)}
    (hT : ContinuousOn (fun q : (I × (Fin 2 → I)) × F ↦ TotalSpace.mk' F (H q.1) (T q.1 q.2))
      ((univ ×ˢ Cube.boundary (Fin 2)) ×ˢ univ)) :
    relativeClutchingNumber (H.curry 0) (fun y ↦ T (0, y)) =
      relativeClutchingNumber (H.curry 1) (fun y ↦ T (1, y)) := by
  have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  obtain ⟨Θ, hΘ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous H)
  -- At each time `t`, the frame `Θ (t, ·)` computes the relative clutching number of the slice.
  have hslice (t : I) : relativeClutchingNumber (H.curry t) (fun y ↦ T (t, y)) =
      squareBoundaryDegree fun y ↦ ((T (t, y)).trans (Θ (t, y)).symm).normalizedDet :=
    relativeClutchingNumber_eq_squareBoundaryDegree (H.curry t) _ (φ := fun y ↦ Θ (t, y))
      (hΘ.comp ((Continuous.prodMk_right t).prodMap continuous_id))
  rw [hslice, hslice]
  exact squareBoundaryDegree_eq_of_homotopy
    (continuousOn_normalizedDet_trans_symm hΘ.continuousOn hT)

/-- **Subdivision.** If the boundary frame `τ` is also continuous along the vertical segment
`s = 1/2`, the relative clutching number of `E` along `u` is the sum of those along the left and
right halves of the square, `u ∘ cubeLeftHalf 0` and `u ∘ cubeRightHalf 0`, relative to the
restrictions of `τ`. The common edge `s = 1/2` carries the same frame for both halves. -/
theorem relativeClutchingNumber_eq_add (u : C(Fin 2 → I, X)) {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : ContinuousOn (fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (τ q.1 q.2))
      ((Cube.boundary (Fin 2) ∪ {y | (y 0 : ℝ) = 1 / 2}) ×ˢ univ)) :
    relativeClutchingNumber u τ =
      relativeClutchingNumber (u.comp (cubeLeftHalf 0)) (fun y ↦ τ (cubeLeftHalf 0 y)) +
        relativeClutchingNumber (u.comp (cubeRightHalf 0)) (fun y ↦ τ (cubeRightHalf 0 y)) := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)
  -- The restrictions of `φ` to the two halves are frames along the two halves of `u`.
  have hhalf (k : C(Fin 2 → I, Fin 2 → I)) :
      Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u (k q.1)) (φ (k q.1) q.2) :=
    hφ.comp ((k.continuous.comp continuous_fst).prodMk continuous_snd)
  rw [relativeClutchingNumber_eq_squareBoundaryDegree u τ hφ,
    squareBoundaryDegree_eq_add (continuousOn_normalizedDet_trans_symm hφ.continuousOn hτ),
    relativeClutchingNumber_eq_squareBoundaryDegree _ _
      (φ := fun y ↦ φ (cubeLeftHalf 0 y)) (hhalf (cubeLeftHalf 0)),
    relativeClutchingNumber_eq_squareBoundaryDegree _ _
      (φ := fun y ↦ φ (cubeRightHalf 0 y)) (hhalf (cubeRightHalf 0))]
  -- Both sides are the same transitions, composed with the two halves (`Function.comp_apply`).
  rfl

/-- **The relative clutching number in a trivialization.** Let `e` be a trivialization of `E`
whose base set contains the image of the boundary of the square under `u`. The relative clutching
number of `E` along `u` relative to `τ` is the degree around the boundary of the clutching function
of any continuous frame `φ` along `u`, read in `e`, minus that of the boundary frame `τ`. -/
theorem relativeClutchingNumber_eq_sub (u : C(Fin 2 → I, X)) {τ φ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : ContinuousOn (fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (τ q.1 q.2))
      (Cube.boundary (Fin 2) ×ˢ univ))
    (hφ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (φ q.1 q.2))
    (e : Trivialization F (π F E)) [e.IsLinear ℂ]
    (he : ∀ y ∈ Cube.boundary (Fin 2), u y ∈ e.baseSet) :
    relativeClutchingNumber u τ =
      squareBoundaryDegree (clutchingFunction u φ e) -
        squareBoundaryDegree (clutchingFunction u τ e) := by
  have hc : ContinuousOn (clutchingFunction u φ e) (Cube.boundary (Fin 2)) :=
    (continuousOn_clutchingFunction hφ e).mono he
  have hΓ := continuousOn_normalizedDet_trans_symm hφ.continuousOn hτ
  -- On the boundary, the clutching function of `τ` is that of `φ` divided by the transition.
  have heq : EqOn (clutchingFunction u τ e)
      (clutchingFunction u φ e * (fun y ↦ ((τ y).trans (φ y).symm).normalizedDet)⁻¹)
      (Cube.boundary (Fin 2)) := fun y hy ↦
    clutchingFunction_eq_mul_normalizedDet_inv (he y hy)
  rw [squareBoundaryDegree_congr heq, squareBoundaryDegree_mul hc hΓ.inv,
    squareBoundaryDegree_inv, relativeClutchingNumber_eq_squareBoundaryDegree u τ hφ]
  ring

/-- **Comparison with the clutching number of a sphere.** For a sphere `p` based at `x` and a
boundary frame `τ` along `p`, the clutching number of `E` on `p` is the relative clutching number
relative to `τ` plus the winding number around the boundary of the square of the clutching
function of `τ` in any trivialization `e` of `E` near `x`. -/
theorem clutchingNumber_eq_relativeClutchingNumber_add {x : X} (p : Ω^ (Fin 2) X x)
    {τ : ∀ y, F ≃L[ℂ] E (p y)}
    (hτ : ContinuousOn (fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (τ q.1 q.2))
      (Cube.boundary (Fin 2) ×ˢ univ))
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] (hx : x ∈ e.baseSet) :
    clutchingNumber F E p =
      relativeClutchingNumber p.val τ + squareBoundaryDegree (clutchingFunction p τ e) := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  rw [clutchingNumber_eq_squareBoundaryDegree p e hx hφ,
    relativeClutchingNumber_eq_sub p.val hτ hφ e fun y hy ↦
      mem_of_eq_of_mem (GenLoop.boundary p y hy) hx]
  -- The coercions `⇑p` and `⇑p.val` agree by definition (`GenLoop.coe_coe`).
  exact (sub_add_cancel _ _).symm

/-- **The clutching number as a relative clutching number.** If the boundary frame `τ` along a
sphere `p` based at `x` is the frame of a trivialization `e` of `E` near `x`, that is
`e (τ y v) = (p y, v)` on the boundary of the square, then the clutching number of `E` on `p` is
the relative clutching number relative to `τ`. -/
theorem clutchingNumber_eq_relativeClutchingNumber {x : X} (p : Ω^ (Fin 2) X x)
    {τ : ∀ y, F ≃L[ℂ] E (p y)} (e : Trivialization F (π F E)) [e.IsLinear ℂ]
    (hx : x ∈ e.baseSet)
    (hτe : ∀ y ∈ Cube.boundary (Fin 2), ∀ v, (e (TotalSpace.mk' F (p y) (τ y v))).2 = v) :
    clutchingNumber F E p = relativeClutchingNumber p.val τ := by
  have hbase (y) (hy : y ∈ Cube.boundary (Fin 2)) : p y ∈ e.baseSet :=
    mem_of_eq_of_mem (GenLoop.boundary p y hy) hx
  -- On the boundary, `τ y v` is the point `e⁻¹ (x, v)` of `E` over `x`, which depends continuously
  -- on `v`.
  have hτ : ContinuousOn (fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (τ q.1 q.2))
      (Cube.boundary (Fin 2) ×ˢ univ) := by
    refine (e.toPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_const.prodMk continuous_snd) fun q ↦ e.mem_target.2 hx).continuousOn.congr ?_
    rintro ⟨y, v⟩ ⟨hy, -⟩
    exact (e.toPartialHomeomorph.eq_symm_apply (e.mem_source.2 (hbase y hy))
      (e.mem_target.2 hx)).2 <|
        Prod.ext ((e.coe_fst' (hbase y hy)).trans (GenLoop.boundary p y hy)) (hτe y hy v)
  -- The clutching function of `τ` in `e` is `1` on the boundary.
  have h1 : EqOn (clutchingFunction p τ e) (fun _ ↦ 1) (Cube.boundary (Fin 2)) := by
    intro y hy
    have hy' := hbase y hy
    have hid : (τ y).trans (e.continuousLinearEquivAt ℂ (p y) hy') =
        ContinuousLinearEquiv.refl ℂ F := by
      ext v
      simpa [Trivialization.continuousLinearEquivAt_apply] using hτe y hy v
    rw [clutchingFunction_of_mem hy', hid, ContinuousLinearEquiv.normalizedDet_refl, inv_one]
  rw [clutchingNumber_eq_relativeClutchingNumber_add p hτ e hx, squareBoundaryDegree_congr h1,
    squareBoundaryDegree_const, add_zero]

section Map

variable {Y : Type*} [TopologicalSpace Y]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {E' : Y → Type*} [∀ y, AddCommGroup (E' y)] [∀ y, Module ℂ (E' y)]
  [∀ y, TopologicalSpace (E' y)] [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E']
  [VectorBundle ℂ F' E'] [∀ y, IsTopologicalAddGroup (E' y)] [∀ y, ContinuousSMul ℂ (E' y)]

/-- **Complex-linear bundle maps preserve relative clutching numbers.** Let `Φ x : E x ≃ E' (f x)`
be complex-linear isomorphisms covering a continuous map `f : X → Y`, continuous as a map of total
spaces, and let `L : F ≃ F'` identify the model fibres. The relative clutching number of `E'` along
`f ∘ u`, relative to the boundary frame `Φ ∘ τ ∘ L⁻¹`, is that of `E` along `u` relative to `τ`. -/
theorem relativeClutchingNumber_map_of_continuousLinearEquiv (f : C(X, Y))
    (Φ : ∀ x, E x ≃L[ℂ] E' (f x))
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (L : F ≃L[ℂ] F') (u : C(Fin 2 → I, X)) (τ : ∀ y, F ≃L[ℂ] E (u y)) :
    relativeClutchingNumber (f.comp u) (fun y ↦ (L.symm.trans (τ y)).trans (Φ (u y))) =
      relativeClutchingNumber u τ := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)
  -- The frame `Φ ∘ φ ∘ L⁻¹` of `E'` along `f ∘ u`.
  have hψ : Continuous fun q : (Fin 2 → I) × F' ↦
      TotalSpace.mk' F' (f (u q.1)) ((L.symm.trans (φ q.1)).trans (Φ (u q.1)) q.2) :=
    hΦ.comp (hφ.comp (continuous_fst.prodMk (L.symm.continuous.comp continuous_snd)))
  rw [relativeClutchingNumber_eq_squareBoundaryDegree (f.comp u) _
      (φ := fun y ↦ (L.symm.trans (φ y)).trans (Φ (u y))) hψ,
    relativeClutchingNumber_eq_squareBoundaryDegree u τ hφ]
  -- The transition of the transported frames is that of `τ` and `φ`, conjugated by `L`.
  refine squareBoundaryDegree_congr fun y _ ↦ ?_
  have h : ((L.symm.trans (τ y)).trans (Φ (u y))).trans
      ((L.symm.trans (φ y)).trans (Φ (u y))).symm =
        L.symm.trans (((τ y).trans (φ y).symm).trans L) := by
    ext v
    simp
  have hL := ContinuousLinearEquiv.normalizedDet_trans_trans_symm L.symm ((τ y).trans (φ y).symm)
  rwa [ContinuousLinearEquiv.symm_symm, ← h] at hL

/-- **Conjugate-linear bundle maps reverse relative clutching numbers.** Let
`Φ x : E x ≃ E' (f x)` be conjugate-linear isomorphisms covering a continuous map `f : X → Y`,
continuous as a map of total spaces, and let `K : F ≃ F'` be a conjugate-linear isomorphism of the
model fibres. The relative clutching number of `E'` along `f ∘ u`, relative to the boundary frame
`Φ ∘ τ ∘ K⁻¹`, is the negative of that of `E` along `u` relative to `τ`. -/
theorem relativeClutchingNumber_map_of_conjugateLinear (f : C(X, Y))
    (Φ : ∀ x, E x ≃L⋆[ℂ] E' (f x))
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (K : F ≃L⋆[ℂ] F') (u : C(Fin 2 → I, X)) (τ : ∀ y, F ≃L[ℂ] E (u y)) :
    relativeClutchingNumber (f.comp u) (fun y ↦ (K.symm.trans (τ y)).trans (Φ (u y))) =
      -relativeClutchingNumber u τ := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)
  -- The frame `Φ ∘ φ ∘ K⁻¹` of `E'` along `f ∘ u`, complex linear as a composite of two
  -- conjugate-linear maps and a complex-linear one.
  have hψ : Continuous fun q : (Fin 2 → I) × F' ↦
      TotalSpace.mk' F' (f (u q.1)) ((K.symm.trans (φ q.1)).trans (Φ (u q.1)) q.2) :=
    hΦ.comp (hφ.comp (continuous_fst.prodMk (K.symm.continuous.comp continuous_snd)))
  rw [relativeClutchingNumber_eq_squareBoundaryDegree (f.comp u) _
      (φ := fun y ↦ (K.symm.trans (φ y)).trans (Φ (u y))) hψ,
    relativeClutchingNumber_eq_squareBoundaryDegree u τ hφ, ← squareBoundaryDegree_inv]
  -- The transition of the transported frames is that of `τ` and `φ`, conjugated by `K`, whose
  -- normalized determinant is the inverse one.
  refine squareBoundaryDegree_congr fun y _ ↦ ?_
  have h : ((K.symm.trans (τ y)).trans (Φ (u y))).trans
      ((K.symm.trans (φ y)).trans (Φ (u y))).symm =
        (K.symm.trans ((τ y).trans (φ y).symm)).trans K := by
    ext v
    simp
  rw [h, ContinuousLinearEquiv.normalizedDet_conjₛₗ, Pi.inv_apply]

end Map

end TauCeti
