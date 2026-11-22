/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Action
public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.FrameQuotient
public import TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The sphere bundle `SO(n) → SO(1 + n) → Sⁿ`

Evaluating a special orthogonal matrix on the first coordinate vector `e₀` gives the map
`SO(1 + n) → Sⁿ`, `A ↦ A e₀` (`TauCeti.specialOrthogonalSphereMap`), to the unit sphere of
`ℝ^(1 + n)`. Its fibre over `e₀` is the block subgroup `diag(1, SO(n))`, the image of
`Matrix.SpecialOrthogonalGroup.fromBlocksOne`. For `n ≥ 1` this map is surjective and a locally
trivial bundle with fibre `SO(n)`, and hence a Serre fibration. For `n = 0` it is not surjective:
`SO(1)` is trivial while `S⁰` has two points.

Since `Matrix.specialOrthogonalGroup` is `Matrix.specialUnitaryGroup` for the trivial star of `ℝ`,
this map is the special unitary evaluation map `TauCeti.specialUnitarySphereMap` over `ℝ`
(`TauCeti.Topology.Grassmannian.SphereBundle.SpecialUnitary`), and its continuity, fibre,
surjectivity and Serre fibration property are specializations of those statements. What is
special to `ℝ` is a chart over the whole complement of a point.

These charts come from explicit local sections. For unit vectors `b` and `y` with `y ≠ -b`, the
reflection in `b` followed by the reflection in `b + y` is a rotation taking `b` to `y`
(`TauCeti.sphereRotation`), and it depends continuously on `y`. Composing it with a fixed rotation
taking `e₀` to `b` gives a continuous section of `A ↦ A e₀` over the complement of `-b`. Through
the identification of the sphere with the orthonormal one-frames
(`TauCeti.finiteOrthonormalFrame.sphereHomeomorph`) and the homogeneous-space description
`SO(1 + n) ⧸ Stab(e₀) ≃ₜ V₁(ℝ^(1 + n))`, such a section is a local section of a subgroup quotient,
which yields the chart (`Subgroup.localSectionTrivialization`).

The coordinates are indexed by `Fin (1 + n)`, so that the block subgroup `diag(1, SO(n))` is the
image of `fromBlocksOne ℝ 1 n` without reindexing.

## Main definitions

* `TauCeti.specialOrthogonalSphereMap`: the evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`.
* `TauCeti.specialOrthogonalSphereFiberHomeomorph`: `SO(n)` is homeomorphic to the fibre of
  `A ↦ A e₀` over `e₀`, through `B ↦ diag(1, B)`.

## Main results

* `TauCeti.specialOrthogonalSphereMap_eq_specialOrthogonalSphereMap_one_iff`: the fibre over `e₀`
  is the image of `SO(n)`.
* `TauCeti.exists_trivialization_specialOrthogonalSphereMap`: a chart with fibre `SO(n)` over the
  complement of each point.
* `TauCeti.specialOrthogonalSphereMap_mem_serreFibrations`: `SO(1 + n) → Sⁿ` is a Serre fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (fiber bundles of
  orthogonal groups over spheres).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.34, where this fibration
  produces the classes of `SO(n + 1)` covering odd spheres.
-/

public section

open Matrix Metric Set Topology

noncomputable section

namespace TauCeti

/-! ### The evaluation map `SO(1 + n) → Sⁿ` -/

variable (n : ℕ)

/-- The evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`, on the first coordinate vector `e₀`: the
special unitary evaluation map over `ℝ`. -/
def specialOrthogonalSphereMap (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1 :=
  specialUnitarySphereMap n A

variable {n}

/-- In coordinates, `specialOrthogonalSphereMap n A` is the first column `A e₀` of `A`. -/
@[simp]
theorem coe_specialOrthogonalSphereMap (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    (specialOrthogonalSphereMap n A : EuclideanSpace ℝ (Fin (1 + n))) =
      WithLp.toLp 2 ((A : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ).col 0) :=
  coe_specialUnitarySphereMap A

variable (n) in
/-- The evaluation map `SO(1 + n) → Sⁿ` is continuous. -/
theorem continuous_specialOrthogonalSphereMap : Continuous (specialOrthogonalSphereMap n) :=
  continuous_specialUnitarySphereMap ℝ n

/-- The evaluation map is equivariant: `(A B) e₀ = A (B e₀)`. -/
theorem ofLp_specialOrthogonalSphereMap_mul (A B : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    WithLp.ofLp (specialOrthogonalSphereMap n (A * B) : EuclideanSpace ℝ (Fin (1 + n))) =
      (A : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ) *ᵥ
        WithLp.ofLp (specialOrthogonalSphereMap n B : EuclideanSpace ℝ (Fin (1 + n))) :=
  ofLp_specialUnitarySphereMap_mul A B

/-- The fibre of `A ↦ A e₀` over `e₀` is the block subgroup `diag(1, SO(n))`. -/
theorem specialOrthogonalSphereMap_eq_specialOrthogonalSphereMap_one_iff
    {A : specialOrthogonalGroup (Fin (1 + n)) ℝ} :
    specialOrthogonalSphereMap n A = specialOrthogonalSphereMap n 1 ↔
      A ∈ (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n).range := by
  rw [SpecialOrthogonalGroup.fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne]
  exact specialUnitarySphereMap_eq_specialUnitarySphereMap_one_iff

/-- For `n ≥ 1`, every unit vector of `ℝ^(1 + n)` is `A e₀` for some `A ∈ SO(1 + n)`. -/
theorem surjective_specialOrthogonalSphereMap [NeZero n] :
    Function.Surjective (specialOrthogonalSphereMap n) :=
  surjective_specialUnitarySphereMap

/-! ### The fibre over `e₀` -/

variable (n) in
/-- The fibre of `A ↦ A e₀` over `e₀` is `SO(n)`: the block embedding `B ↦ diag(1, B)` is a
homeomorphism of `SO(n)` onto the special orthogonal matrices fixing `e₀`. -/
def specialOrthogonalSphereFiberHomeomorph :
    specialOrthogonalGroup (Fin n) ℝ ≃ₜ
      specialOrthogonalSphereMap n ⁻¹' {specialOrthogonalSphereMap n 1} :=
  specialUnitarySphereFiberHomeomorph ℝ n

@[simp]
theorem coe_specialOrthogonalSphereFiberHomeomorph_apply (B : specialOrthogonalGroup (Fin n) ℝ) :
    (specialOrthogonalSphereFiberHomeomorph n B : specialOrthogonalGroup (Fin (1 + n)) ℝ) =
      SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n B := by
  rw [SpecialOrthogonalGroup.fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne]
  exact coe_specialUnitarySphereFiberHomeomorph_apply B

/-- A special orthogonal matrix fixing `e₀` is the block matrix `diag(1, B)` of its image `B` in
`SO(n)`. -/
@[simp]
theorem fromBlocksOne_specialOrthogonalSphereFiberHomeomorph_symm_apply
    (A : specialOrthogonalSphereMap n ⁻¹' {specialOrthogonalSphereMap n 1}) :
    SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n ((specialOrthogonalSphereFiberHomeomorph n).symm A) =
      A := by
  rw [SpecialOrthogonalGroup.fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne]
  exact fromBlocksOne_specialUnitarySphereFiberHomeomorph_symm_apply A

/-- The identity of `SO(n)` corresponds to the identity of `SO(1 + n)` in the fibre. -/
@[simp]
theorem specialOrthogonalSphereFiberHomeomorph_one :
    specialOrthogonalSphereFiberHomeomorph n 1 = ⟨1, rfl⟩ :=
  specialUnitarySphereFiberHomeomorph_one

/-! ### Local triviality -/

/-- For `n ≥ 1` and each unit vector `b`, the evaluation map `SO(1 + n) → Sⁿ` has a chart with
fibre `SO(n)` over the complement of `-b`. -/
theorem exists_trivialization_specialOrthogonalSphereMap [NeZero n]
    (b : sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1) :
    ∃ e : Bundle.Trivialization (specialOrthogonalGroup (Fin n) ℝ) (specialOrthogonalSphereMap n),
      e.baseSet = {-b}ᶜ := by
  have hn : 1 < 1 + n := Nat.lt_add_of_pos_right (Nat.pos_of_neZero n)
  let H := finiteOrthonormalFrame.specialOrthogonalStabilizer (r := 1) hn.le
  -- The sphere is the homogeneous space `SO(1 + n) ⧸ H`.
  let φ : specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1 :=
    (finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph hn).trans
      (finiteOrthonormalFrame.sphereHomeomorph ℝ (1 + n))
  have hφ (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
      φ (QuotientGroup.mk A) = specialOrthogonalSphereMap n A := by
    rw [specialOrthogonalSphereMap, specialUnitarySphereMap_eq_sphereHomeomorph,
      specialUnitaryFrameMap_eq_smul_standard, finiteOrthonormalFrame.specialUnitary_smul_def]
    exact congrArg (finiteOrthonormalFrame.sphereHomeomorph ℝ (1 + n))
      (finiteOrthonormalFrame.specialOrthogonalQuotientHomeomorph_mk hn A)
  -- A rotation `g` taking `e₀` to `b`, followed by rotations taking `b` to nearby points.
  obtain ⟨g, hg⟩ := surjective_specialOrthogonalSphereMap (n := n) b
  let U : Set (specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H) :=
    φ ⁻¹' {-b}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton.preimage φ.continuous
  let s : specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H → specialOrthogonalGroup (Fin (1 + n)) ℝ :=
    fun q ↦ sphereRotation b (φ q) * g
  have hs : ContinuousOn s U :=
    ((continuousOn_sphereRotation b).comp φ.continuous.continuousOn fun _ hq ↦ hq).mul
      continuousOn_const
  have hsec : ∀ q ∈ U, (s q : specialOrthogonalGroup (Fin (1 + n)) ℝ ⧸ H) = q := by
    intro q hq
    apply φ.injective
    rw [hφ]
    apply Subtype.ext
    apply WithLp.ofLp_injective
    rw [ofLp_specialOrthogonalSphereMap_mul, hg]
    exact sphereRotation_mulVec hq
  let e := Subgroup.localSectionTrivialization H U hU s hs hsec
  let e' := (e.homeomorphComp φ).transFiberHomeomorph
    (finiteOrthonormalFrame.specialOrthogonalStabilizerHomeomorph 1 n).symm
  have hproj : φ ∘ (QuotientGroup.mk : specialOrthogonalGroup (Fin (1 + n)) ℝ → _) =
      specialOrthogonalSphereMap n := funext hφ
  rw [← hproj]
  refine ⟨e', ?_⟩
  simp only [e', Bundle.Trivialization.transFiberHomeomorph, Bundle.Trivialization.homeomorphComp,
    e, Subgroup.localSectionTrivialization_baseSet, U]
  ext y
  simp only [Set.mem_preimage, Homeomorph.apply_symm_apply]

/-- For `n ≥ 1`, the evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`, is a Serre fibration: it is
locally trivial with fibre `SO(n)`. -/
theorem specialOrthogonalSphereMap_mem_serreFibrations [NeZero n] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialOrthogonalSphereMap n,
          continuous_specialOrthogonalSphereMap n⟩ :
        _root_.TopCat.of (specialOrthogonalGroup (Fin (1 + n)) ℝ) ⟶
          _root_.TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)) :=
  specialUnitarySphereMap_mem_serreFibrations

end TauCeti
