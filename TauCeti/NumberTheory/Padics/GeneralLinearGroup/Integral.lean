/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `ℤ_[p]`, `ℚ_[p]` and the inclusion `PadicInt.Coe.ringHom` occur in the statements below.
public import Mathlib.NumberTheory.Padics.PadicIntegers
-- `Matrix.GeneralLinearGroup.map` and the `GL` notation occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- The topology of `GL n ℚ_[p]` as the unit group of the matrix ring occurs in the statements of
-- `TauCeti.GLPadicInt.isOpen` and `TauCeti.GLPadicInt.isCompact`.
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix
-- Non-public: the compactness of `ℤ_[p]` is used only in the compactness proof, and the
-- ultrametric determinant bound only in `TauCeti.GLPadicInt.mem_iff_inv`.
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.Analysis.Matrix.Ultra
-- Non-public: injectivity of `Matrix.GeneralLinearGroup.map` along an injective ring hom, used only
-- to build `TauCeti.GLPadicInt.mulEquiv`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# The integral subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`

The group `GLₙ(ℤ_p)` of invertible matrices over the `p`-adic integers is a subgroup of
`GLₙ(ℚ_p)` through the entrywise inclusion `ℤ_p ⊆ ℚ_p`. For `n = 2` it is the maximal compact
subgroup `K = GL₂(ℤ_p)` of `GL₂(ℚ_p)`, whose product `KZ` with the centre is the stabiliser of
the standard vertex of the Bruhat–Tits tree, and from which the representations
`c-Ind_{KZ}^G σ` of `GL₂(ℚ_p)` are compactly induced.

The subgroup is defined as the image of `Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom`; the
main result describes it intrinsically. An invertible matrix over `ℚ_p` comes from `GLₙ(ℤ_p)`
exactly when all of its entries have norm at most `1` and its determinant has norm `1`. Integrality
of the entries alone is not enough: `!![p, 0; 0, 1]` has integral entries, but its inverse does not.

## Main definitions

* `TauCeti.GLPadicInt n p`: the subgroup `GLₙ(ℤ_p)` of `GL n ℚ_[p]`.
* `TauCeti.GLPadicInt.mulEquiv`: the isomorphism `GL n ℤ_[p] ≃* GLPadicInt n p`.
* `TauCeti.castGLPadic n p`: the injective entrywise embedding `GL n ℚ →* GL n ℚ_[p]`.
* `TauCeti.padicIntEntries`: the submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible `p`-adic matrices
  with integral entries.
* `TauCeti.padicIntMatrix`: the underlying `ℤ_p`-matrix of an element of `padicIntEntries n p`,
  bundled as a monoid homomorphism.

## Main results

* `TauCeti.GLPadicInt.mem_iff`: `g ∈ GLₙ(ℤ_p)` if and only if every entry of `g` has norm at most
  `1` and `‖det g‖ = 1`.
* `TauCeti.GLPadicInt.mem_iff_inv`: `g ∈ GLₙ(ℤ_p)` if and only if `g` and `g⁻¹` have integral
  entries.
* `TauCeti.GLPadicInt.isOpen`, `TauCeti.GLPadicInt.isCompact`: `GLₙ(ℤ_p)` is open and compact.
* `TauCeti.GLPadicInt.neg_one_mem`, `TauCeti.GLPadicInt.le_padicIntEntries`,
  `TauCeti.GLPadicInt.mem_iff_mem_padicIntEntries_and_inv`: basic subgroup and integral-entry
  membership properties of `GLₙ(ℤ_p)`.
* `TauCeti.castGLPadic_injective`, `TauCeti.GLPadicInt.castGLPadic_map_intCast_mem`,
  `TauCeti.castGLPadic_mem_padicIntEntries_of_exists_int_matrix`: properties of the rational
  embedding `GL_n(ℚ) ↪ GL_n(ℚ_p)`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010), §III.1.1.
-/

public section

namespace TauCeti

open Matrix

variable (n : Type*) [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]

/-- The subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`: the image of the invertible matrices over `ℤ_p` under
the entrywise inclusion `ℤ_p ⊆ ℚ_p`. -/
noncomputable def GLPadicInt : Subgroup (GL n ℚ_[p]) :=
  (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))).range

namespace GLPadicInt

variable {n p}

/-- Membership in `GLₙ(ℤ_p)` is coming from an invertible matrix over `ℤ_p`. -/
theorem mem_iff_exists_map {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt n p ↔ ∃ γ : GL n ℤ_[p], GeneralLinearGroup.map PadicInt.Coe.ringHom γ = g :=
  Iff.rfl

/-- An invertible matrix over `ℤ_p` lies in `GLₙ(ℤ_p)`. -/
theorem map_mem (γ : GL n ℤ_[p]) :
    GeneralLinearGroup.map PadicInt.Coe.ringHom γ ∈ GLPadicInt n p :=
  ⟨γ, rfl⟩

/-- **The integral subgroup, intrinsically.** An invertible matrix over `ℚ_p` lies in `GLₙ(ℤ_p)`
exactly when all of its entries have norm at most `1` and its determinant has norm `1`. -/
theorem mem_iff {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt n p ↔
      (∀ i j, ‖(g : Matrix n n ℚ_[p]) i j‖ ≤ 1) ∧ ‖(g : Matrix n n ℚ_[p]).det‖ = 1 := by
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨fun i j ↦ ?_, ?_⟩
    · rw [GeneralLinearGroup.map_apply, PadicInt.Coe.ringHom_apply, PadicInt.norm_coe]
      exact PadicInt.norm_le_one _
    · rw [← GeneralLinearGroup.val_det_apply, GeneralLinearGroup.map_det]
      simpa [PadicInt.norm_coe] using PadicInt.isUnit_iff.mp (GeneralLinearGroup.det γ).isUnit
  · rintro ⟨h, hdet⟩
    -- The entries of `g` lift to `ℤ_p`, and the lifted matrix has a unit determinant.
    let A : Matrix n n ℤ_[p] := Matrix.of fun i j ↦ Padic.lift ((g : Matrix n n ℚ_[p]) i j) (h i j)
    have hA : PadicInt.Coe.ringHom.mapMatrix A = g := by
      ext i j
      simp [A]
    have hu : IsUnit A.det := by
      rw [PadicInt.isUnit_iff, ← PadicInt.norm_coe, ← PadicInt.Coe.ringHom_apply,
        RingHom.map_det, hA, hdet]
    refine ⟨GeneralLinearGroup.mk'' A hu, ?_⟩
    ext i j
    simp [A]

/-- **`GLₙ(ℤ_p)` is the stabiliser of the standard lattice**: an element of `GLₙ(ℚ_p)` lies in
`GLₙ(ℤ_p)` exactly when it and its inverse have integral entries. -/
theorem mem_iff_inv {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt n p ↔ (∀ i j, ‖(g : Matrix n n ℚ_[p]) i j‖ ≤ 1) ∧
      ∀ i j, ‖((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]) i j‖ ≤ 1 := by
  refine ⟨fun hg ↦ ⟨(mem_iff.mp hg).1, (mem_iff.mp (Subgroup.inv_mem _ hg)).1⟩, ?_⟩
  rintro ⟨hg, hg'⟩
  refine mem_iff.mpr ⟨hg, ?_⟩
  -- `det g * det g⁻¹ = 1` with both factors integral forces `‖det g‖ = 1`.
  have h1 : ‖(g : Matrix n n ℚ_[p]).det‖ * ‖((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]).det‖ = 1 := by
    simp [(Matrix.isUnits_det_units g).ne_zero]
  -- By the ultrametric inequality an integral matrix has integral determinant.
  have h2 : ‖(g : Matrix n n ℚ_[p]).det‖ ≤ 1 := by
    simpa using Matrix.norm_det_le_prod_of_norm_le (c := fun _ ↦ 1) hg
  have h3 : ‖((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]).det‖ ≤ 1 := by
    simpa using Matrix.norm_det_le_prod_of_norm_le (c := fun _ ↦ 1) hg'
  nlinarith [norm_nonneg ((g : Matrix n n ℚ_[p]).det),
    norm_nonneg (((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]).det)]

variable (n p) in
/-- `GLₙ(ℤ_p)` is open in `GLₙ(ℚ_p)`. -/
theorem isOpen : IsOpen (GLPadicInt n p : Set (GL n ℚ_[p])) := by
  have hball : IsOpen (Metric.closedBall (0 : ℚ_[p]) 1) :=
    IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hset : (GLPadicInt n p : Set (GL n ℚ_[p])) =
      (⋂ (i : n) (j : n), (fun g : GL n ℚ_[p] ↦
        (g : Matrix n n ℚ_[p]) i j) ⁻¹' Metric.closedBall 0 1) ∩
      ⋂ (i : n) (j : n), (fun g : GL n ℚ_[p] ↦
        ((g⁻¹ : GL n ℚ_[p]) : Matrix n n ℚ_[p]) i j) ⁻¹' Metric.closedBall 0 1 := by
    ext g
    simp [mem_iff_inv]
  rw [hset]
  refine IsOpen.inter
    (isOpen_iInter_of_finite (ι := n) fun i ↦ isOpen_iInter_of_finite (ι := n) fun j ↦
      hball.preimage ?_)
    (isOpen_iInter_of_finite (ι := n) fun i ↦ isOpen_iInter_of_finite (ι := n) fun j ↦
      hball.preimage ?_)
  · exact Units.continuous_val.matrix_elem i j
  · exact (Units.continuous_val.comp continuous_inv).matrix_elem i j

variable (n p) in
/-- `GLₙ(ℤ_p)` is compact: it is the continuous image of the compact group `GLₙ(ℤ_p)`. -/
theorem isCompact : IsCompact (GLPadicInt n p : Set (GL n ℚ_[p])) := by
  have hcont : Continuous
      (GeneralLinearGroup.map (n := n) (PadicInt.Coe.ringHom (p := p))) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_subtypeVal)
  -- `Matrix` is a type synonym for a function type, so instance search does not find its
  -- compactness, which the compactness instance of the unit group `GL n ℤ_[p]` needs.
  have : CompactSpace (Matrix n n ℤ_[p]) := inferInstanceAs (CompactSpace (n → n → ℤ_[p]))
  exact isCompact_range hcont

variable (n p) in
/-- `GLₙ(ℤ_p)` is isomorphic to its image in `GLₙ(ℚ_p)`: the entrywise inclusion `ℤ_p ⊆ ℚ_p` is
injective. -/
noncomputable def mulEquiv : GL n ℤ_[p] ≃* GLPadicInt n p :=
  MonoidHom.ofInjective (GeneralLinearGroup.map_injective (f := PadicInt.Coe.ringHom (p := p))
    Subtype.val_injective)

@[simp]
theorem coe_mulEquiv_apply (γ : GL n ℤ_[p]) :
    ((mulEquiv n p γ : GLPadicInt n p) : GL n ℚ_[p]) =
      GeneralLinearGroup.map PadicInt.Coe.ringHom γ :=
  (rfl)

variable (n p) in
/-- Defining equation for `GLPadicInt`. -/
theorem eq_range :
    GLPadicInt n p = (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))).range := (rfl)

/-- Matrix coercion of the canonical embedding `GL n ℤ_[p] →* GL n ℚ_[p]`. -/
theorem map_coe (u : GL n ℤ_[p]) :
    ((GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) u : GL n ℚ_[p]) : Matrix n n ℚ_[p]) =
      (u : Matrix n n ℤ_[p]).map (PadicInt.Coe.ringHom (p := p)) := by
  ext i j; simp

variable (n p) in
/-- The entrywise inclusion `GL n ℤ_[p] →* GL n ℚ_[p]` is injective. -/
theorem map_injective :
    Function.Injective (GeneralLinearGroup.map (n := n) (PadicInt.Coe.ringHom (p := p))) :=
  GeneralLinearGroup.map_injective Subtype.val_injective

variable (n p) in
/-- `-1` belongs to `GLₙ(ℤ_p)`. -/
theorem neg_one_mem : (-1 : GL n ℚ_[p]) ∈ GLPadicInt n p :=
  ⟨-1, by rw [GeneralLinearGroup.map_neg, map_one]⟩

end GLPadicInt

section Embedding

/-- The canonical entrywise group homomorphism `GL n ℚ →* GL n ℚ_[p]`. -/
noncomputable def castGLPadic : GL n ℚ →* GL n ℚ_[p] :=
  GeneralLinearGroup.map (Rat.castHom ℚ_[p])

/-- Defining equation for `castGLPadic`. -/
theorem castGLPadic_def :
    castGLPadic n p = GeneralLinearGroup.map (Rat.castHom ℚ_[p]) := (rfl)

/-- Matrix coercion of `castGLPadic`. -/
@[simp]
theorem castGLPadic_coe (g : GL n ℚ) :
    ((castGLPadic n p g : GL n ℚ_[p]) : Matrix n n ℚ_[p]) =
      (g : Matrix n n ℚ).map (Rat.castHom ℚ_[p]) := by
  ext i j; simp [castGLPadic]

/-- `castGLPadic` is injective because `ℚ ↪ ℚ_p` is injective. -/
theorem castGLPadic_injective : Function.Injective (castGLPadic n p) :=
  GeneralLinearGroup.map_injective (Rat.castHom ℚ_[p]).injective

/-- `castGLPadic` sends the image of `GL n ℤ` in `GL n ℚ` into `GLₙ(ℤ_p)`. -/
theorem GLPadicInt.castGLPadic_map_intCast_mem (γ : GL n ℤ) :
    castGLPadic n p (GeneralLinearGroup.map (Int.castRingHom ℚ) γ) ∈ GLPadicInt n p :=
  ⟨GeneralLinearGroup.map (Int.castRingHom ℤ_[p]) γ,
    Units.ext (by ext i j; simp [castGLPadic])⟩

end Embedding

section PadicIntEntries

/-- The submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible `p`-adic matrices with `ℤ_p`-entries. -/
def padicIntEntries : Submonoid (GL n ℚ_[p]) where
  carrier := {g | ∃ A : Matrix n n ℤ_[p],
    (g : Matrix n n ℚ_[p]) = A.map (PadicInt.Coe.ringHom (p := p))}
  one_mem' := ⟨1, (Matrix.map_one (PadicInt.Coe.ringHom (p := p)) (map_zero _) (map_one _)).symm⟩
  mul_mem' := by rintro g h ⟨A, hA⟩ ⟨B, hB⟩; exact ⟨A * B, by simp [hA, hB]⟩

/-- Membership in `padicIntEntries n p` is having a `ℤ_p`-matrix lift. -/
theorem mem_padicIntEntries_iff {g : GL n ℚ_[p]} :
    g ∈ padicIntEntries n p ↔
      ∃ A : Matrix n n ℤ_[p],
        (g : Matrix n n ℚ_[p]) = A.map (PadicInt.Coe.ringHom (p := p)) := Iff.rfl

/-- `g ∈ GL n ℚ_[p]` lies in `padicIntEntries n p` iff every entry has `p`-adic norm `≤ 1`. -/
theorem mem_padicIntEntries_iff_norm_le_one {g : GL n ℚ_[p]} :
    g ∈ padicIntEntries n p ↔ ∀ i j, ‖(g : Matrix n n ℚ_[p]) i j‖ ≤ 1 :=
  ⟨fun ⟨A, hA⟩ i j ↦ hA ▸ Matrix.map_apply.symm ▸ (A i j).property,
    fun h ↦ ⟨Matrix.of fun i j ↦ ⟨(g : Matrix n n ℚ_[p]) i j, h i j⟩, by ext i j; rfl⟩⟩

/-- Every element of `GLₙ(ℤ_p)` has `ℤ_p`-entries. -/
theorem GLPadicInt.le_padicIntEntries : (GLPadicInt n p).toSubmonoid ≤ padicIntEntries n p := by
  rintro g ⟨u, rfl⟩
  exact ⟨u, GLPadicInt.map_coe u⟩

/-- `g ∈ GLₙ(ℤ_p)` iff both `g` and `g⁻¹` lie in `padicIntEntries n p`. -/
theorem GLPadicInt.mem_iff_mem_padicIntEntries_and_inv {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt n p ↔ g ∈ padicIntEntries n p ∧ g⁻¹ ∈ padicIntEntries n p := by
  rw [GLPadicInt.mem_iff_inv, mem_padicIntEntries_iff_norm_le_one,
    mem_padicIntEntries_iff_norm_le_one]

/-- The `ℤ_p`-matrix underlying an element of `padicIntEntries n p`, as a monoid homomorphism. -/
noncomputable def padicIntMatrix : padicIntEntries n p →* Matrix n n ℤ_[p] where
  toFun g := Classical.choose g.property
  map_one' := Matrix.map_injective (f := PadicInt.Coe.ringHom (p := p)) Subtype.val_injective (by
    dsimp only; rw [(Classical.choose_spec (1 : padicIntEntries n p).property).symm,
      Matrix.map_one _ (map_zero _) (map_one _)]; rfl)
  map_mul' g h := Matrix.map_injective (f := PadicInt.Coe.ringHom (p := p)) Subtype.val_injective
    (by
      dsimp only
      rw [(Classical.choose_spec (g * h).property).symm, Matrix.map_mul,
        (Classical.choose_spec g.property).symm, (Classical.choose_spec h.property).symm]
      rfl)

/-- Casting `padicIntMatrix n p g` to `ℚ_p` recovers the matrix of `g`. -/
@[simp]
theorem map_padicIntMatrix (g : padicIntEntries n p) :
    (padicIntMatrix n p g).map (PadicInt.Coe.ringHom (p := p)) =
      ((g : GL n ℚ_[p]) : Matrix n n ℚ_[p]) :=
  (Classical.choose_spec g.property).symm

/-- `padicIntMatrix n p g = A` if and only if `A` casts to the matrix of `g`. -/
theorem padicIntMatrix_eq_iff {g : padicIntEntries n p} {A : Matrix n n ℤ_[p]} :
    padicIntMatrix n p g = A ↔
      ((g : GL n ℚ_[p]) : Matrix n n ℚ_[p]) = A.map (PadicInt.Coe.ringHom (p := p)) :=
  ⟨fun h ↦ h ▸ (map_padicIntMatrix n p g).symm,
    fun h ↦ Matrix.map_injective (f := PadicInt.Coe.ringHom (p := p)) Subtype.val_injective
      ((map_padicIntMatrix n p g).trans h)⟩

/-- The `ℤ_p`-matrix of an invertible element has nonzero determinant. -/
theorem det_padicIntMatrix_ne_zero (g : padicIntEntries n p) :
    (padicIntMatrix n p g).det ≠ 0 := by
  intro h0
  have hdet := (g : GL n ℚ_[p]).det_ne_zero
  rw [← map_padicIntMatrix n p g, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    at hdet
  exact hdet rfl

/-- If `g ∈ GL n ℚ` has integer entries, then `castGLPadic n p g` lies in `padicIntEntries n p`. -/
theorem castGLPadic_mem_padicIntEntries_of_exists_int_matrix {g : GL n ℚ}
    (h : ∃ A : Matrix n n ℤ, (g : Matrix n n ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    castGLPadic n p g ∈ padicIntEntries n p := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.map (Int.castRingHom ℤ_[p]), by rw [castGLPadic_coe, hA]; ext i j; simp⟩

end PadicIntEntries

end TauCeti
