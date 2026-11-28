/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Crossing.Functoriality
public import TauCeti.Geometry.Convex.PolyhedralComplex.AmbientSubdivision
public import TauCeti.Geometry.Convex.PolyhedralComplex.OfPolyhedron
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Worked example: crossing word of the square loop across the four coordinate half-axes in `ℝ × ℝ`

`TauCeti.FourHalfAxesExample` instantiates `Quiver.Path.crossingWord` and its functoriality laws on
the coordinate-axis arrangement `coordComplex` in `ℝ × ℝ` (built via
`FinitePolyhedralComplex.ofArrangement`):
* `halfAxisEquiv` identifies `coordComplex.walls` with the four closed coordinate half-axes
  `halfAxis : Fin 4 → Set (ℝ × ℝ)`, cooriented by `coordNormal` (`isWallCoorientation_coordNormal`),
  with `singularSupport_coordWalls` equal to `{(0, 0)}`;
* `crossingWord_squareLoop` evaluates `squareLoop.crossingWord coordNormal` on the counterclockwise
  boundary of `[-1, 1]²` to `(of w₀)⁻¹ * ((of w₃)⁻¹ * (of w₂ * of w₁))` where
  `wᵢ = halfAxisEquiv i`;
* `crossingWord_squareLoop_restrict_posX` and `crossingWord_squareLoop_restrict_posX_ne_one` verify
  that restricting along `WallComplement.restrictPrefunctor` to the subcomplex `posXComplex` of the
  positive `x`-half-axis sends the crossing word via `wallDeletion` to `(of posXWall)⁻¹ ≠ 1`;
* `crossingWord_squareLoop_xAxis` verifies `IsSubdivision.crossingWord_mapPath` on the coarsening
  `coordSubdivisionXAxis : coordComplex.IsSubdivision xAxisComplex`, merging the positive and
  negative `x`-half-axes into the single line `{p | p.2 = 0}` and killing the `y`-half-axes so the
  crossing word collapses to `1`;
* `lift_oppositeHalfAxisLabel_crossingWord_squareLoop` and
  `lift_oppositeHalfAxisLabel_crossingWord_squareLoop_ne_one` check that identifying opposite
  half-axes produces the nontrivial commutator
  `(of false)⁻¹ * ((of true)⁻¹ * (of false * of true)) ≠ 1` in `FreeGroup Bool`.

## References

* M. Kontsevich and Y. Soibelman, *Wall-crossing structures in Donaldson–Thomas invariants,
  integrable systems and Mirror Symmetry*, §2.1.
* M. Gross, *Tropical Geometry and Mirror Symmetry*, §6.2.
-/

public section

noncomputable section

open Set

namespace TauCeti.FourHalfAxesExample

/-! ### The coordinate-axis polyhedral complex in `ℝ × ℝ` -/

/-- The standard integral lattice `ℤ × ℤ →+ ℝ × ℝ`. -/
theorem isIntegralLattice_plane :
    Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)) :=
  Toric.isIntegralLattice_castAddHom.prod Toric.isIntegralLattice_castAddHom

private theorem isRationalFunctional_id :
    Toric.IsRationalFunctional Toric.isIntegralLattice_castAddHom LinearMap.id := by
  have heq : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) =
      Toric.isIntegralLattice_castAddHom.realCharacter (LinearMap.id : ℤ →ₗ[ℤ] ℤ).toAddMonoidHom :=
    Toric.isIntegralLattice_castAddHom.eq_realCharacter fun n => by simp
  rw [heq]
  exact Toric.IsRationalFunctional.realCharacter _ (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

/-- The two coordinate projections on `ℝ × ℝ` as continuous affine maps. -/
def coordRow : Bool → ((ℝ × ℝ) →ᴬ[ℝ] ℝ)
  | false => (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  | true => (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

/-- Each coordinate row has rational linear part with respect to `ℤ × ℤ ⊆ ℝ × ℝ`. -/
theorem coordRow_rational (b : Bool) :
    Toric.IsRationalFunctional isIntegralLattice_plane (coordRow b).toAffineMap.linear := by
  cases b
  · have hlin : (coordRow false).toAffineMap.linear = LinearMap.id.comp (LinearMap.fst ℝ ℝ ℝ) :=
      LinearMap.ext fun p => by
        simpa [coordRow] using (coordRow false).toAffineMap.linear_apply_vsub p 0
    rw [hlin]
    exact (Toric.IsRationalLinearMap.fst Toric.isIntegralLattice_castAddHom
      Toric.isIntegralLattice_castAddHom).map_functional isRationalFunctional_id
  · have hlin : (coordRow true).toAffineMap.linear = LinearMap.id.comp (LinearMap.snd ℝ ℝ ℝ) :=
      LinearMap.ext fun p => by
        simpa [coordRow] using (coordRow true).toAffineMap.linear_apply_vsub p 0
    rw [hlin]
    exact (Toric.IsRationalLinearMap.snd Toric.isIntegralLattice_castAddHom
      Toric.isIntegralLattice_castAddHom).map_functional isRationalFunctional_id

/-- The finite polyhedral complex in `ℝ × ℝ` cut out by `x = 0` and `y = 0`, whose cells are the
origin, the four closed coordinate half-axes, and the four closed quadrants. -/
def coordComplex : FinitePolyhedralComplex isIntegralLattice_plane :=
  FinitePolyhedralComplex.ofArrangement coordRow coordRow_rational

private theorem sign_cast_signType (s : SignType) : SignType.sign (s : ℝ) = s := by
  cases s <;> norm_num

private theorem mem_cells_coordComplex {P : Set (ℝ × ℝ)} :
    P ∈ coordComplex.cells ↔ ∃ σ : Bool → SignType, P = Convex.weakSignCell coordRow σ := by
  rw [coordComplex, FinitePolyhedralComplex.mem_cells_ofArrangement]
  constructor
  · rintro ⟨σ, hne, rfl⟩
    exact ⟨σ, Convex.closure_signCell hne⟩
  · rintro ⟨σ, rfl⟩
    have hne : (Convex.signCell coordRow σ).Nonempty :=
      ⟨((σ false : ℝ), (σ true : ℝ)), Convex.mem_signCell.mpr fun b => by
        cases b <;> simp [coordRow, sign_cast_signType]⟩
    exact ⟨σ, hne, (Convex.closure_signCell hne).symm⟩

/-- The four closed coordinate half-axes in `ℝ × ℝ`:
`0` is `{(x, 0) | 0 ≤ x}`, `1` is `{(0, y) | 0 ≤ y}`,
`2` is `{(x, 0) | x ≤ 0}`, and `3` is `{(0, y) | y ≤ 0}`. -/
def halfAxis : Fin 4 → Set (ℝ × ℝ)
  | 0 => {p | 0 ≤ p.1 ∧ p.2 = 0}
  | 1 => {p | p.1 = 0 ∧ 0 ≤ p.2}
  | 2 => {p | p.1 ≤ 0 ∧ p.2 = 0}
  | 3 => {p | p.1 = 0 ∧ p.2 ≤ 0}

@[simp] theorem halfAxis_zero : halfAxis 0 = {p | 0 ≤ p.1 ∧ p.2 = 0} := (rfl)
@[simp] theorem halfAxis_one : halfAxis 1 = {p | p.1 = 0 ∧ 0 ≤ p.2} := (rfl)
@[simp] theorem halfAxis_two : halfAxis 2 = {p | p.1 ≤ 0 ∧ p.2 = 0} := (rfl)
@[simp] theorem halfAxis_three : halfAxis 3 = {p | p.1 = 0 ∧ p.2 ≤ 0} := (rfl)

/-- Standard coorientations of the four half-axes: `dy` on horizontal half-axes (`0`, `2`) and
`dx` on vertical half-axes (`1`, `3`). -/
def halfAxisNormal : Fin 4 → (ℝ × ℝ) →ₗ[ℝ] ℝ
  | 0 => LinearMap.snd ℝ ℝ ℝ
  | 1 => LinearMap.fst ℝ ℝ ℝ
  | 2 => LinearMap.snd ℝ ℝ ℝ
  | 3 => LinearMap.fst ℝ ℝ ℝ

@[simp] theorem halfAxisNormal_zero : halfAxisNormal 0 = LinearMap.snd ℝ ℝ ℝ := (rfl)
@[simp] theorem halfAxisNormal_one : halfAxisNormal 1 = LinearMap.fst ℝ ℝ ℝ := (rfl)
@[simp] theorem halfAxisNormal_two : halfAxisNormal 2 = LinearMap.snd ℝ ℝ ℝ := (rfl)
@[simp] theorem halfAxisNormal_three : halfAxisNormal 3 = LinearMap.fst ℝ ℝ ℝ := (rfl)

private theorem halfAxisNormal_ne_zero (i : Fin 4) : halfAxisNormal i ≠ 0 := by
  intro h
  have h01 := LinearMap.congr_fun h (0, 1)
  have h10 := LinearMap.congr_fun h (1, 0)
  fin_cases i <;> simp at h01 h10

private def halfAxisUnit : Fin 4 → ℝ × ℝ
  | 0 => (1, 0) | 1 => (0, 1) | 2 => (-1, 0) | 3 => (0, -1)
private def halfAxisCoord : Fin 4 → (ℝ × ℝ) → ℝ
  | 0 => Prod.fst | 1 => Prod.snd | 2 => (- ·.1) | 3 => (- ·.2)

private theorem direction_halfAxis (i : Fin 4) :
    (affineSpan ℝ (halfAxis i)).direction = LinearMap.ker (halfAxisNormal i) := by
  refine le_antisymm ?_ ?_
  · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    fin_cases i <;> simp_all
  · intro v hv
    rw [direction_affineSpan]
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ halfAxis i := by fin_cases i <;> simp
    have he : halfAxisUnit i ∈ halfAxis i := by fin_cases i <;> norm_num [halfAxisUnit]
    have hvw : v = halfAxisCoord i v • (halfAxisUnit i -ᵥ ((0 : ℝ), (0 : ℝ))) := by
      fin_cases i <;> ext <;> simp_all [halfAxisUnit, halfAxisCoord]
    exact hvw ▸ Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ he h0)

private theorem finrank_direction_halfAxis (i : Fin 4) :
    Module.finrank ℝ (affineSpan ℝ (halfAxis i)).direction + 1 = Module.finrank ℝ (ℝ × ℝ) := by
  rw [direction_halfAxis]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero (halfAxisNormal_ne_zero i)

private def halfAxisSign : Fin 4 → Bool → SignType
  | 0 => fun b => if b then .zero else .pos
  | 1 => fun b => if b then .pos else .zero
  | 2 => fun b => if b then .zero else .neg
  | 3 => fun b => if b then .neg else .zero

private theorem weakSignCell_halfAxisSign (i : Fin 4) :
    Convex.weakSignCell coordRow (halfAxisSign i) = halfAxis i := by
  ext ⟨x, y⟩
  fin_cases i <;>
    simp [Convex.mem_weakSignCell, halfAxisSign, coordRow, Bool.forall_bool, and_comm]

private theorem direction_eq_top_of_mem_axes {S : Set (ℝ × ℝ)} (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (h0 : (0, 0) ∈ S) (hx : (a, 0) ∈ S) (hy : (0, b) ∈ S) :
    (affineSpan ℝ S).direction = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  rw [direction_affineSpan]
  have he1 : ((1 : ℝ), (0 : ℝ)) ∈ vectorSpan ℝ S := by
    simpa [inv_mul_cancel₀ ha] using Submodule.smul_mem _ a⁻¹ (vsub_mem_vectorSpan ℝ hx h0)
  have he2 : ((0 : ℝ), (1 : ℝ)) ∈ vectorSpan ℝ S := by
    simpa [inv_mul_cancel₀ hb] using Submodule.smul_mem _ b⁻¹ (vsub_mem_vectorSpan ℝ hy h0)
  have hxy : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  exact hxy ▸ add_mem (Submodule.smul_mem _ x he1) (Submodule.smul_mem _ y he2)

private theorem direction_weakSignCell_eq_top {σ : Bool → SignType}
    (hf : σ false ≠ .zero) (ht : σ true ≠ .zero) :
    (affineSpan ℝ (Convex.weakSignCell coordRow σ)).direction = ⊤ :=
  direction_eq_top_of_mem_axes (σ false : ℝ) (σ true : ℝ)
    (by cases h : σ false <;> simp [h] at hf ⊢)
    (by cases h : σ true <;> simp [h] at ht ⊢)
    (by simp [Convex.mem_weakSignCell, coordRow, Bool.forall_bool])
    (Convex.mem_weakSignCell.mpr <| Bool.forall_bool.mpr
      ⟨by cases h : σ false <;> simp [coordRow, h] at hf ⊢, by cases σ true <;> simp [coordRow]⟩)
    (Convex.mem_weakSignCell.mpr <| Bool.forall_bool.mpr
      ⟨by cases σ false <;> simp [coordRow], by cases h : σ true <;> simp [coordRow, h] at ht ⊢⟩)

/-- The walls of `coordComplex` are precisely the four closed coordinate half-axes. -/
theorem mem_walls_coordComplex {P : Set (ℝ × ℝ)} :
    P ∈ coordComplex.walls ↔ ∃ i : Fin 4, P = halfAxis i := by
  have hdim2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [FinitePolyhedralComplex.mem_cellsOfCodimension, mem_cells_coordComplex]
  constructor
  · rintro ⟨⟨σ, rfl⟩, hdim⟩
    match h0 : σ false, h1 : σ true with
    | .zero, .zero =>
      have hsing : Convex.weakSignCell coordRow σ = {((0 : ℝ), (0 : ℝ))} := by
        ext ⟨x, y⟩; simp [Convex.mem_weakSignCell, coordRow, Bool.forall_bool, h0, h1]
      rw [hsing, direction_affineSpan, vectorSpan_singleton, finrank_bot, hdim2] at hdim; omega
    | .pos, .zero =>
      exact ⟨0, (congrArg _ (by ext b; cases b <;> simp [halfAxisSign, h0, h1])).trans
        (weakSignCell_halfAxisSign 0)⟩
    | .zero, .pos =>
      exact ⟨1, (congrArg _ (by ext b; cases b <;> simp [halfAxisSign, h0, h1])).trans
        (weakSignCell_halfAxisSign 1)⟩
    | .neg, .zero =>
      exact ⟨2, (congrArg _ (by ext b; cases b <;> simp [halfAxisSign, h0, h1])).trans
        (weakSignCell_halfAxisSign 2)⟩
    | .zero, .neg =>
      exact ⟨3, (congrArg _ (by ext b; cases b <;> simp [halfAxisSign, h0, h1])).trans
        (weakSignCell_halfAxisSign 3)⟩
    | .pos, .pos | .pos, .neg | .neg, .pos | .neg, .neg =>
      rw [direction_weakSignCell_eq_top (by simp [h0]) (by simp [h1]), finrank_top, hdim2] at hdim
      omega
  · rintro ⟨i, rfl⟩
    exact ⟨⟨halfAxisSign i, (weakSignCell_halfAxisSign i).symm⟩, finrank_direction_halfAxis i⟩

private theorem halfAxis_injective : Function.Injective halfAxis := by
  intro i j hij
  have h1 := Set.ext_iff.mp hij (1, 0)
  have h2 := Set.ext_iff.mp hij (0, 1)
  have h3 := Set.ext_iff.mp hij (-1, 0)
  fin_cases i <;> fin_cases j <;> simp at h1 h2 h3 ⊢ <;> linarith

/-- The bijection `i ↦ halfAxis i` between `Fin 4` and `coordComplex.walls`. -/
def halfAxisEquiv : Fin 4 ≃ coordComplex.walls :=
  Equiv.ofBijective (fun i => ⟨halfAxis i, mem_walls_coordComplex.mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => halfAxis_injective (congrArg Subtype.val h),
      fun w => let ⟨i, hi⟩ := mem_walls_coordComplex.mp w.property; ⟨i, Subtype.ext hi.symm⟩⟩

@[simp]
theorem coe_halfAxisEquiv (i : Fin 4) : (halfAxisEquiv i : Set (ℝ × ℝ)) = halfAxis i :=
  congrArg Subtype.val (Equiv.ofBijective_apply _ _ i)

/-- Wall coorientation on `coordComplex` induced by `halfAxisNormal`. -/
def coordNormal (w : coordComplex.walls) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  halfAxisNormal (halfAxisEquiv.symm w)

@[simp]
theorem coordNormal_halfAxisEquiv (i : Fin 4) :
    coordNormal (halfAxisEquiv i) = halfAxisNormal i := by simp [coordNormal]

/-- `coordNormal` is a valid wall coorientation on `coordComplex`. -/
theorem isWallCoorientation_coordNormal : coordComplex.IsWallCoorientation coordNormal := by
  rw [FinitePolyhedralComplex.isWallCoorientation_iff]
  intro w
  obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w
  exact ⟨by simpa using halfAxisNormal_ne_zero i, by simp [direction_halfAxis]⟩

/-! ### Singular support and admissible square loop -/

private theorem origin_notMem_intrinsicInterior_zero :
    ((0 : ℝ), (0 : ℝ)) ∉ intrinsicInterior ℝ (halfAxis 0) := fun h0 =>
  one_ne_zero <| TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
    (g := (LinearMap.fst ℝ ℝ ℝ).toAffineMap) (fun _ (hp : _ ∈ halfAxis 0) => hp.1) h0 rfl
    (show ((1 : ℝ), (0 : ℝ)) ∈ halfAxis 0 from ⟨zero_le_one, rfl⟩)

private theorem halfAxisNormal_eq_zero_of_mem_affineSpan (i : Fin 4) {q : ℝ × ℝ}
    (hq : q ∈ affineSpan ℝ (halfAxis i)) : halfAxisNormal i q = 0 := by
  have h0 : (0 : ℝ × ℝ) ∈ affineSpan ℝ (halfAxis i) :=
    subset_affineSpan ℝ _ (by fin_cases i <;> simp)
  have hv : q -ᵥ (0 : ℝ × ℝ) ∈ LinearMap.ker (halfAxisNormal i) := by
    rw [← direction_halfAxis, direction_affineSpan]
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hq h0
  simpa using LinearMap.mem_ker.mp hv

private theorem mem_intrinsicInterior_halfAxis_of_ne_origin {i : Fin 4} {p : ℝ × ℝ}
    (hp : p ∈ halfAxis i) (hne : p ≠ (0, 0)) : p ∈ intrinsicInterior ℝ (halfAxis i) := by
  rw [TauCeti.mem_intrinsicInterior_iff_eventually]
  refine ⟨subset_affineSpan ℝ _ hp, ?_⟩
  fin_cases i
  · filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds
      (lt_of_le_of_ne hp.1 fun h0 => hne (Prod.ext h0.symm hp.2))] with q hq1 hqA
    exact ⟨hq1.le, halfAxisNormal_eq_zero_of_mem_affineSpan 0 hqA⟩
  · filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds
      (lt_of_le_of_ne hp.2 fun h0 => hne (Prod.ext hp.1 h0.symm))] with q hq2 hqA
    exact ⟨halfAxisNormal_eq_zero_of_mem_affineSpan 1 hqA, hq2.le⟩
  · filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds
      (lt_of_le_of_ne hp.1 fun h0 => hne (Prod.ext h0 hp.2))] with q hq1 hqA
    exact ⟨hq1.le, halfAxisNormal_eq_zero_of_mem_affineSpan 2 hqA⟩
  · filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds
      (lt_of_le_of_ne hp.2 fun h0 => hne (Prod.ext hp.1 h0))] with q hq2 hqA
    exact ⟨halfAxisNormal_eq_zero_of_mem_affineSpan 3 hqA, hq2.le⟩

/-- The singular support of `coordComplex.walls` is the origin `{(0, 0)}`. -/
@[simp]
theorem singularSupport_coordWalls :
    singularSupport (fun w : coordComplex.walls => (w : Set (ℝ × ℝ))) = {(0, 0)} := by
  refine Subset.antisymm (fun p hp => ?_) (Set.singleton_subset_iff.mpr ?_)
  · simp only [Set.mem_singleton_iff]
    by_contra hne
    rcases mem_singularSupport.mp hp with ⟨w, hfr⟩ | ⟨w₁, w₂, hdir, hi, hj⟩
    · have hcl : IsClosed (w : Set (ℝ × ℝ)) :=
        (coordComplex.isConvexPolyhedron
          (FinitePolyhedralComplex.mem_cellsOfCodimension.mp w.property).1).isClosed
      obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w
      have hp_mem : p ∈ halfAxis i := intrinsicFrontier_subset hcl hfr
      rw [← intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ)] at hfr
      exact hfr.2 (mem_intrinsicInterior_halfAxis_of_ne_origin hp_mem hne)
    · obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w₁
      obtain ⟨j, rfl⟩ := halfAxisEquiv.surjective w₂
      have hij : (halfAxisEquiv i : Set (ℝ × ℝ)) ≠ halfAxisEquiv j := fun heq => hdir (heq ▸ rfl)
      exact Set.disjoint_left.mp
        (coordComplex.disjoint_intrinsicInterior
          (FinitePolyhedralComplex.mem_cellsOfCodimension.mp (halfAxisEquiv i).property).1
          (FinitePolyhedralComplex.mem_cellsOfCodimension.mp (halfAxisEquiv j).property).1 hij)
        (mem_intrinsicInterior_halfAxis_of_ne_origin hi hne)
        (mem_intrinsicInterior_halfAxis_of_ne_origin hj hne)
  · refine mem_singularSupport.mpr (.inl ⟨halfAxisEquiv 0, ?_⟩)
    rw [← intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ)]
    exact ⟨subset_intrinsicClosure (show ((0 : ℝ), (0 : ℝ)) ∈ halfAxis 0 from ⟨le_rfl, rfl⟩),
      origin_notMem_intrinsicInterior_zero⟩

private theorem notMem_coordWalls {p : ℝ × ℝ} (hx : p.1 ≠ 0) (hy : p.2 ≠ 0)
    (w : coordComplex.walls) : p ∉ (w : Set (ℝ × ℝ)) := by
  obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w
  fin_cases i <;> simp [hx, hy]

/-- Top-right corner `(1, 1)` in `coordComplex.WallComplement`. -/
def vPP : coordComplex.WallComplement := ⟨(1, 1), notMem_coordWalls one_ne_zero one_ne_zero⟩
@[simp] theorem vPP_val : vPP.val = (1, 1) := (rfl)

/-- Top-left corner `(-1, 1)` in `coordComplex.WallComplement`. -/
def vNP : coordComplex.WallComplement := ⟨(-1, 1), notMem_coordWalls (by norm_num) one_ne_zero⟩
@[simp] theorem vNP_val : vNP.val = (-1, 1) := (rfl)

/-- Bottom-left corner `(-1, -1)` in `coordComplex.WallComplement`. -/
def vNN : coordComplex.WallComplement := ⟨(-1, -1), notMem_coordWalls (by norm_num) (by norm_num)⟩
@[simp] theorem vNN_val : vNN.val = (-1, -1) := (rfl)

/-- Bottom-right corner `(1, -1)` in `coordComplex.WallComplement`. -/
def vPN : coordComplex.WallComplement := ⟨(1, -1), notMem_coordWalls one_ne_zero (by norm_num)⟩
@[simp] theorem vPN_val : vPN.val = (1, -1) := (rfl)

private theorem crossings_eq_singleton {u v : coordComplex.WallComplement} {i₀ : Fin 4} {t₀ : ℝ}
    (honly : ∀ i t, AffineMap.lineMap u.val v.val t ∈ halfAxis i → i = i₀ ∧ t = t₀)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hi₀ : AffineMap.lineMap u.val v.val t₀ ∈ halfAxis i₀) :
    WallComplement.crossings u v = {(halfAxisEquiv i₀, t₀)} := by
  ext ⟨w, t⟩
  obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w
  simp only [WallComplement.mem_crossings, coe_halfAxisEquiv, Set.mem_singleton_iff,
    Prod.mk.injEq, halfAxisEquiv.injective.eq_iff]
  exact ⟨fun ⟨_, hi⟩ => honly i t hi, by rintro ⟨rfl, rfl⟩; exact ⟨ht₀, hi₀⟩⟩

private theorem eq_half_of_sub_two_mul_eq_zero {t a : ℝ} (ha : a ≠ 0)
    (h : (1 - 2 * t) * a = 0) : t = 1 / 2 := by
  linarith [(mul_eq_zero.mp h).resolve_right ha]

private def swapAxis : Fin 4 ≃ Fin 4 where
  toFun | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  invFun | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem swap_mem_halfAxis (p : ℝ × ℝ) (i : Fin 4) :
    p.swap ∈ halfAxis (swapAxis i) ↔ p ∈ halfAxis i := by
  fin_cases i <;> simp [swapAxis, and_comm]

private def swapEndpoint (u : coordComplex.WallComplement) : coordComplex.WallComplement :=
  ⟨u.val.swap, fun w hw => by
    obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w
    exact u.notMem (halfAxisEquiv (swapAxis.symm i))
      ((swap_mem_halfAxis u.val (swapAxis.symm i)).mp (by simpa using hw))⟩

private theorem crossings_horizontal {u v : coordComplex.WallComplement} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u.val = (a, b)) (hv : v.val = (-a, b)) :
    WallComplement.crossings u v =
      {(halfAxisEquiv (if 0 < b then 1 else 3), (1 / 2 : ℝ))} := by
  refine crossings_eq_singleton ?_ (by norm_num) ?_
  · intro i t hi
    have hpt : AffineMap.lineMap u.val v.val t = ((1 - 2 * t) * a, b) := by
      rw [AffineMap.lineMap_apply_module', hu, hv]; ext <;> dsimp <;> ring
    rw [hpt] at hi
    fin_cases i
    · exact (hb hi.2).elim
    · exact ⟨by rw [ite_eq_left (lt_of_le_of_ne hi.2 hb.symm)]; rfl,
        eq_half_of_sub_two_mul_eq_zero ha hi.1⟩
    · exact (hb hi.2).elim
    · exact ⟨by rw [ite_eq_right (not_lt.mpr hi.2)]; rfl,
        eq_half_of_sub_two_mul_eq_zero ha hi.1⟩
  · have hpt : AffineMap.lineMap u.val v.val (1 / 2 : ℝ) = (0, b) := by
      rw [AffineMap.lineMap_apply_module', hu, hv]; ext <;> dsimp <;> ring
    rw [hpt]
    split_ifs with hpos
    · exact ⟨rfl, hpos.le⟩
    · exact ⟨rfl, le_of_not_gt hpos⟩

private theorem crossings_vertical {u v : coordComplex.WallComplement} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u.val = (a, b)) (hv : v.val = (a, -b)) :
    WallComplement.crossings u v =
      {(halfAxisEquiv (if 0 < a then 0 else 2), (1 / 2 : ℝ))} := by
  have hswap := crossings_horizontal (u := swapEndpoint u) (v := swapEndpoint v) hb ha
    (by simp [swapEndpoint, hu]) (by simp [swapEndpoint, hv])
  ext ⟨w, t⟩
  obtain ⟨i, rfl⟩ := halfAxisEquiv.surjective w
  have hmem : (halfAxisEquiv i, t) ∈ WallComplement.crossings u v ↔
      (halfAxisEquiv (swapAxis i), t) ∈
        WallComplement.crossings (swapEndpoint u) (swapEndpoint v) := by
    have hline : AffineMap.lineMap (swapEndpoint u).val (swapEndpoint v).val t =
        (AffineMap.lineMap u.val v.val t).swap := by
      ext <;> simp [swapEndpoint, AffineMap.lineMap_apply_module']
    simp only [WallComplement.mem_crossings, coe_halfAxisEquiv, hline, swap_mem_halfAxis]
  rw [hmem, hswap]
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, halfAxisEquiv.injective.eq_iff,
    ← swapAxis.eq_symm_apply]
  split_ifs <;> rfl

@[simp] theorem crossings_segTop :
    WallComplement.crossings vPP vNP = {(halfAxisEquiv 1, (1 / 2 : ℝ))} := by
  simpa using crossings_horizontal (u := vPP) (v := vNP) one_ne_zero one_ne_zero rfl rfl

@[simp] theorem crossings_segLeft :
    WallComplement.crossings vNP vNN = {(halfAxisEquiv 2, (1 / 2 : ℝ))} := by
  rw [crossings_vertical (u := vNP) (v := vNN) (by norm_num) one_ne_zero rfl rfl,
    ite_eq_right (by norm_num)]

@[simp] theorem crossings_segBot :
    WallComplement.crossings vNN vPN = {(halfAxisEquiv 3, (1 / 2 : ℝ))} := by
  rw [crossings_horizontal (u := vNN) (v := vPN) (by norm_num) (by norm_num) rfl
      (by simp [vPN_val]), ite_eq_right (by norm_num)]

@[simp] theorem crossings_segRight :
    WallComplement.crossings vPN vPP = {(halfAxisEquiv 0, (1 / 2 : ℝ))} := by
  simpa using crossings_vertical (u := vPN) (v := vPP) one_ne_zero (by norm_num) rfl
    (by simp [vPP_val])

/-- Any straight segment between off-wall points missing `(0, 0)` is admissible for `coordComplex`.
-/
def mkAdmissibleEdge {u v : coordComplex.WallComplement}
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap u.val v.val t ≠ (0, 0)) : u ⟶ v :=
  ⟨(convex_segment u.val v.val).admissibleSegment_of_disjoint_singularSupport
    (by
      rw [singularSupport_coordWalls, Set.disjoint_singleton_right, segment_eq_image_lineMap]
      exact fun ⟨t, ht, heq⟩ => h0 t ht heq)
    (left_mem_segment ℝ u.val v.val) (right_mem_segment ℝ u.val v.val)⟩

/-- Top edge `(1, 1) → (-1, 1)` of the counterclockwise square loop. -/
def segTop : vPP ⟶ vNP :=
  mkAdmissibleEdge fun _ _ h => by simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.snd h

/-- Left edge `(-1, 1) → (-1, -1)` of the counterclockwise square loop. -/
def segLeft : vNP ⟶ vNN :=
  mkAdmissibleEdge fun _ _ h => by simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.fst h

/-- Bottom edge `(-1, -1) → (1, -1)` of the counterclockwise square loop. -/
def segBot : vNN ⟶ vPN :=
  mkAdmissibleEdge fun _ _ h => by simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.snd h

/-- Right edge `(1, -1) → (1, 1)` of the counterclockwise square loop. -/
def segRight : vPN ⟶ vPP :=
  mkAdmissibleEdge fun _ _ h => by simpa [AffineMap.lineMap_apply_module'] using congrArg Prod.fst h

/-- The counterclockwise boundary of `[-1, 1]²` based at `(1, 1)`. -/
def squareLoop : AdmissiblePLPath vPP vPP :=
  (((segTop.toPath.cons segLeft).cons segBot).cons segRight)

/-- Explicit edge decomposition of `squareLoop`. -/
theorem squareLoop_def :
    squareLoop = (((segTop.toPath.cons segLeft).cons segBot).cons segRight) := (rfl)

/-! ### Crossing word, wall deletion, complex subdivision, and commutator lift -/

/-- The counterclockwise square loop around `(0, 0)` crosses the positive `y`-, negative `x`-,
negative `y`-, and positive `x`-half-axes in order, producing the crossing word
`(of w₀)⁻¹ * ((of w₃)⁻¹ * (of w₂ * of w₁))` in `FreeGroup coordComplex.walls`. -/
theorem crossingWord_squareLoop :
    squareLoop.crossingWord coordNormal =
      (FreeGroup.of (halfAxisEquiv 0))⁻¹ *
        ((FreeGroup.of (halfAxisEquiv 3))⁻¹ *
          (FreeGroup.of (halfAxisEquiv 2) * FreeGroup.of (halfAxisEquiv 1))) := by
  have hTop : ¬ 0 < coordNormal (halfAxisEquiv 1) (vNP.val - vPP.val) := by norm_num
  have hLeft : ¬ 0 < coordNormal (halfAxisEquiv 2) (vNN.val - vNP.val) := by norm_num
  have hBot : 0 < coordNormal (halfAxisEquiv 3) (vPN.val - vNN.val) := by norm_num
  have hRight : 0 < coordNormal (halfAxisEquiv 0) (vPP.val - vPN.val) := by norm_num
  simp only [squareLoop_def, Quiver.Path.crossingWord_cons, Quiver.Path.crossingWord_toPath,
    coordComplex.segmentCrossingWord_of_crossings_eq_singleton coordNormal segTop crossings_segTop,
    coordComplex.segmentCrossingWord_of_crossings_eq_singleton coordNormal segLeft
      crossings_segLeft,
    coordComplex.segmentCrossingWord_of_crossings_eq_singleton coordNormal segBot crossings_segBot,
    coordComplex.segmentCrossingWord_of_crossings_eq_singleton coordNormal segRight
      crossings_segRight,
    FinitePolyhedralComplex.crossingLetter_def, ite_eq_right hTop, ite_eq_right hLeft,
    ite_eq_left hBot, ite_eq_left hRight]

/-- Lifting `squareLoop.crossingWord coordNormal` along `f : coordComplex.walls → G` multiplies the
four wall labels in counterclockwise left-action order. -/
theorem lift_crossingWord_squareLoop {G : Type*} [Group G] (f : coordComplex.walls → G) :
    FreeGroup.lift f (squareLoop.crossingWord coordNormal) =
      (f (halfAxisEquiv 0))⁻¹ *
        ((f (halfAxisEquiv 3))⁻¹ * (f (halfAxisEquiv 2) * f (halfAxisEquiv 1))) := by
  rw [crossingWord_squareLoop]; simp

private theorem halfAxis_zero_mem_cells : halfAxis 0 ∈ coordComplex.cells := by
  simpa using (FinitePolyhedralComplex.mem_cellsOfCodimension.mp (halfAxisEquiv 0).property).1

/-- The subcomplex of `coordComplex` consisting of the positive `x`-half-axis and its origin face.
-/
def posXComplex : FinitePolyhedralComplex isIntegralLattice_plane :=
  FinitePolyhedralComplex.ofPolyhedron isIntegralLattice_plane (halfAxis 0)
    (coordComplex.rational (halfAxis 0) halfAxis_zero_mem_cells)

/-- `posXComplex` is a subcomplex of `coordComplex`. -/
theorem posXComplex_isSubcomplex : posXComplex.IsSubcomplex coordComplex :=
  FinitePolyhedralComplex.isSubcomplex_ofPolyhedron coordComplex halfAxis_zero_mem_cells

/-- Every wall of `posXComplex` is a wall of `coordComplex`. -/
theorem posXComplex_walls_subset : posXComplex.walls ⊆ coordComplex.walls :=
  posXComplex_isSubcomplex.cellsOfCodimension_subset 1

/-- The unique wall `halfAxis 0` of `posXComplex`. -/
def posXWall : posXComplex.walls :=
  ⟨halfAxis 0, FinitePolyhedralComplex.mem_cellsOfCodimension.mpr
    ⟨FinitePolyhedralComplex.self_mem_cells_ofPolyhedron _ ⟨(0, 0), le_rfl, rfl⟩,
      finrank_direction_halfAxis 0⟩⟩

@[simp] theorem coe_posXWall : (posXWall : Set (ℝ × ℝ)) = halfAxis 0 := (rfl)

private theorem halfAxis_not_subset_zero {i : Fin 4} (hi : i ≠ 0) :
    ¬ halfAxis i ⊆ halfAxis 0 := fun h => by
  have hu : halfAxisUnit i ∈ halfAxis 0 := h (by fin_cases i <;> norm_num [halfAxisUnit])
  fin_cases i <;> first | contradiction | norm_num [halfAxisUnit] at hu

private theorem halfAxisEquiv_mem_posXComplex_walls_iff (i : Fin 4) :
    (halfAxisEquiv i : Set (ℝ × ℝ)) ∈ posXComplex.walls ↔ i = 0 := by
  rw [coe_halfAxisEquiv]
  refine ⟨fun hw => by_contra fun hi => ?_, fun h => h ▸ posXWall.property⟩
  have hcell := (FinitePolyhedralComplex.mem_cellsOfCodimension.mp hw).1
  exact halfAxis_not_subset_zero hi
    ((FinitePolyhedralComplex.mem_cells_ofPolyhedron _).mp hcell).isExposed.subset

/-- Restricting `squareLoop` to `posXComplex` sends its crossing word via `wallDeletion` to
`(FreeGroup.of posXWall)⁻¹`. -/
theorem crossingWord_squareLoop_restrict_posX :
    ((WallComplement.restrictPrefunctor (fun P : coordComplex.walls => (P : Set (ℝ × ℝ)))
        fun P : posXComplex.walls =>
          (⟨P.val, posXComplex_walls_subset P.property⟩ : coordComplex.walls)).mapPath
        squareLoop).crossingWord
        (fun P => coordNormal ⟨P.val, posXComplex_walls_subset P.property⟩) =
      (FreeGroup.of posXWall)⁻¹ := by
  rw [Quiver.Path.crossingWord_restrictPrefunctor squareLoop posXComplex_walls_subset coordNormal]
  have h0 : (halfAxisEquiv 0).val ∈ posXComplex.walls :=
    (halfAxisEquiv_mem_posXComplex_walls_iff 0).mpr rfl
  have h1 : (halfAxisEquiv 1).val ∉ posXComplex.walls := by
    rw [halfAxisEquiv_mem_posXComplex_walls_iff]; decide
  have h2 : (halfAxisEquiv 2).val ∉ posXComplex.walls := by
    rw [halfAxisEquiv_mem_posXComplex_walls_iff]; decide
  have h3 : (halfAxisEquiv 3).val ∉ posXComplex.walls := by
    rw [halfAxisEquiv_mem_posXComplex_walls_iff]; decide
  have hw0 : (⟨(halfAxisEquiv 0).val, h0⟩ : posXComplex.walls) = posXWall :=
    Subtype.ext (coe_halfAxisEquiv 0)
  rw [crossingWord_squareLoop]
  simp only [map_mul, map_inv, FinitePolyhedralComplex.wallDeletion_of,
    dite_eq_left h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, hw0]
  group

/-- Restricting `squareLoop` to the positive `x`-half-axis produces a nontrivial crossing word. -/
theorem crossingWord_squareLoop_restrict_posX_ne_one :
    ((WallComplement.restrictPrefunctor (fun P : coordComplex.walls => (P : Set (ℝ × ℝ)))
        fun P : posXComplex.walls =>
          (⟨P.val, posXComplex_walls_subset P.property⟩ : coordComplex.walls)).mapPath
        squareLoop).crossingWord
        (fun P => coordNormal ⟨P.val, posXComplex_walls_subset P.property⟩) ≠ 1 := by
  rw [crossingWord_squareLoop_restrict_posX]
  exact inv_ne_one.mpr (FreeGroup.of_ne_one posXWall)

/-- The coarser complex cut out by `y = 0` alone, whose single wall is the `x`-axis. -/
def xAxisComplex : FinitePolyhedralComplex isIntegralLattice_plane :=
  FinitePolyhedralComplex.ofArrangement (coordRow ∘ fun _ : Unit => true)
    (fun _ => coordRow_rational true)

/-- `coordComplex` subdivides `xAxisComplex` by splitting the `x`-axis at `(0, 0)` and introducing
the two `y`-half-axes inside the upper and lower half-planes. -/
theorem coordSubdivisionXAxis : coordComplex.IsSubdivision xAxisComplex :=
  FinitePolyhedralComplex.ofArrangement_isSubdivision_comp coordRow coordRow_rational
    (fun _ : Unit => true)

private theorem direction_snd_zero :
    (affineSpan ℝ {p : ℝ × ℝ | p.2 = 0}).direction = LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp_all
  · exact (direction_halfAxis 0).symm.trans_le
      (AffineSubspace.direction_le (affineSpan_mono ℝ fun _ hp => hp.2))

/-- The `x`-axis `{p | p.2 = 0}` as a wall of `xAxisComplex`. -/
def xAxisWall : xAxisComplex.walls :=
  ⟨{p : ℝ × ℝ | p.2 = 0}, FinitePolyhedralComplex.mem_cellsOfCodimension.mpr ⟨by
    rw [xAxisComplex, FinitePolyhedralComplex.mem_cells_ofArrangement]
    have hne : (Convex.signCell (coordRow ∘ fun _ : Unit => true) (fun _ => .zero)).Nonempty :=
      ⟨(0, 0), Convex.mem_signCell.mpr fun _ => by simp [coordRow]⟩
    refine ⟨fun _ => .zero, hne, ?_⟩
    rw [Convex.closure_signCell hne]
    ext ⟨x, y⟩
    simp [Convex.mem_weakSignCell, coordRow],
    direction_snd_zero ▸ Module.Dual.finrank_ker_add_one_of_ne_zero (halfAxisNormal_ne_zero 0)⟩⟩

@[simp]
theorem coe_xAxisWall : (xAxisWall : Set (ℝ × ℝ)) = {p : ℝ × ℝ | p.2 = 0} := (rfl)

private theorem mem_walls_xAxisComplex {P : Set (ℝ × ℝ)} :
    P ∈ xAxisComplex.walls ↔ P = {p : ℝ × ℝ | p.2 = 0} := by
  constructor
  · intro hP
    have hdim2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
    obtain ⟨hcell, hdim⟩ := FinitePolyhedralComplex.mem_cellsOfCodimension.mp hP
    rw [xAxisComplex, FinitePolyhedralComplex.mem_cells_ofArrangement] at hcell
    obtain ⟨σ, hne, rfl⟩ := hcell
    rw [Convex.closure_signCell hne] at hdim ⊢
    match hσ : σ () with
    | .zero =>
      ext ⟨x, y⟩
      simp [Convex.mem_weakSignCell, coordRow, hσ]
    | .neg | .pos =>
      have htop :
          (affineSpan ℝ (Convex.weakSignCell (coordRow ∘ fun _ : Unit => true) σ)).direction = ⊤ :=
        direction_eq_top_of_mem_axes 1 (σ () : ℝ) one_ne_zero (by simp [hσ])
          (by simp [Convex.mem_weakSignCell, coordRow])
          (by simp [Convex.mem_weakSignCell, coordRow])
          (Convex.mem_weakSignCell.mpr fun u => by cases σ u <;> simp [coordRow])
      rw [htop, finrank_top, hdim2] at hdim
      omega
  · rintro rfl
    exact xAxisWall.property

/-- Coorientation `dy` on `xAxisComplex`. -/
def xAxisNormal : xAxisComplex.walls → (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  fun _ => LinearMap.snd ℝ ℝ ℝ

/-- `xAxisNormal` is a wall coorientation on `xAxisComplex`. -/
theorem isWallCoorientation_xAxisNormal : xAxisComplex.IsWallCoorientation xAxisNormal := by
  rw [FinitePolyhedralComplex.isWallCoorientation_iff]
  intro w
  exact ⟨halfAxisNormal_ne_zero 0, by
    rw [mem_walls_xAxisComplex.mp w.property, direction_snd_zero]; rfl⟩

/-- Coarsening `coordComplex` to `xAxisComplex` merges `halfAxis 0` and `halfAxis 2` into
`xAxisWall` with opposite crossing signs and kills `halfAxis 1` and `halfAxis 3`, collapsing
`squareLoop`'s crossing word to `1`. -/
theorem crossingWord_squareLoop_xAxis :
    (coordSubdivisionXAxis.mapPath squareLoop).crossingWord xAxisNormal = 1 := by
  rw [coordSubdivisionXAxis.crossingWord_mapPath isWallCoorientation_coordNormal
      isWallCoorientation_xAxisNormal squareLoop,
    lift_crossingWord_squareLoop]
  have hw0 : coordComplex.wallWordMap xAxisComplex coordNormal xAxisNormal (halfAxisEquiv 0) =
      FreeGroup.of xAxisWall :=
    FinitePolyhedralComplex.wallWordMap_of_subset_pos
      (by rw [coe_halfAxisEquiv, coe_xAxisWall]; exact fun _ hp => hp.2)
      one_pos (by simp [xAxisNormal])
  have hw2 : coordComplex.wallWordMap xAxisComplex coordNormal xAxisNormal (halfAxisEquiv 2) =
      FreeGroup.of xAxisWall :=
    FinitePolyhedralComplex.wallWordMap_of_subset_pos
      (by rw [coe_halfAxisEquiv, coe_xAxisWall]; exact fun _ hp => hp.2)
      one_pos (by simp [xAxisNormal])
  have hw1 : coordComplex.wallWordMap xAxisComplex coordNormal xAxisNormal (halfAxisEquiv 1) = 1 :=
    FinitePolyhedralComplex.wallWordMap_of_forall_not_subset _ _ fun w hw => by
      rw [coe_halfAxisEquiv, mem_walls_xAxisComplex.mp w.property] at hw
      have h := hw (show ((0 : ℝ), (1 : ℝ)) ∈ halfAxis 1 from ⟨rfl, zero_le_one⟩)
      norm_num at h
  have hw3 : coordComplex.wallWordMap xAxisComplex coordNormal xAxisNormal (halfAxisEquiv 3) = 1 :=
    FinitePolyhedralComplex.wallWordMap_of_forall_not_subset _ _ fun w hw => by
      rw [coe_halfAxisEquiv, mem_walls_xAxisComplex.mp w.property] at hw
      have h := hw (show ((0 : ℝ), (-1 : ℝ)) ∈ halfAxis 3 from ⟨rfl, by norm_num⟩)
      norm_num at h
  rw [hw0, hw1, hw2, hw3]
  group

/-- Generator map identifying opposite coordinate half-axes into horizontal (`false`) and vertical
(`true`) labels in `FreeGroup Bool`. -/
def oppositeHalfAxisLabel : coordComplex.walls → FreeGroup Bool := fun w =>
  match halfAxisEquiv.symm w with
  | 0 => FreeGroup.of false
  | 1 => FreeGroup.of true
  | 2 => FreeGroup.of false
  | 3 => FreeGroup.of true

@[simp] theorem oppositeHalfAxisLabel_zero :
    oppositeHalfAxisLabel (halfAxisEquiv 0) = FreeGroup.of false := by simp [oppositeHalfAxisLabel]
@[simp] theorem oppositeHalfAxisLabel_one :
    oppositeHalfAxisLabel (halfAxisEquiv 1) = FreeGroup.of true := by simp [oppositeHalfAxisLabel]
@[simp] theorem oppositeHalfAxisLabel_two :
    oppositeHalfAxisLabel (halfAxisEquiv 2) = FreeGroup.of false := by simp [oppositeHalfAxisLabel]
@[simp] theorem oppositeHalfAxisLabel_three :
    oppositeHalfAxisLabel (halfAxisEquiv 3) = FreeGroup.of true := by simp [oppositeHalfAxisLabel]

/-- Identifying opposite half-axes via `oppositeHalfAxisLabel` maps the square loop's crossing word
to the commutator `(of false)⁻¹ * ((of true)⁻¹ * (of false * of true))` in `FreeGroup Bool`. -/
theorem lift_oppositeHalfAxisLabel_crossingWord_squareLoop :
    FreeGroup.lift oppositeHalfAxisLabel (squareLoop.crossingWord coordNormal) =
      (FreeGroup.of false)⁻¹ *
        ((FreeGroup.of true)⁻¹ * (FreeGroup.of false * FreeGroup.of true)) := by
  simp [lift_crossingWord_squareLoop]

/-- Under `oppositeHalfAxisLabel`, the square loop's crossing word is nontrivial in
`FreeGroup Bool`. -/
theorem lift_oppositeHalfAxisLabel_crossingWord_squareLoop_ne_one :
    FreeGroup.lift oppositeHalfAxisLabel (squareLoop.crossingWord coordNormal) ≠ 1 := by
  rw [lift_oppositeHalfAxisLabel_crossingWord_squareLoop]
  intro hcomm_eq
  have hab : FreeGroup.of false * FreeGroup.of true = FreeGroup.of true * FreeGroup.of false := by
    calc
      FreeGroup.of false * FreeGroup.of true =
          FreeGroup.of true * FreeGroup.of false *
            ((FreeGroup.of false)⁻¹ *
              ((FreeGroup.of true)⁻¹ * (FreeGroup.of false * FreeGroup.of true))) := by
        group
      _ = FreeGroup.of true * FreeGroup.of false := by rw [hcomm_eq, mul_one]
  exact Bool.false_ne_true (FreeGroup.eq_of_commute_of_of hab)

end TauCeti.FourHalfAxesExample
