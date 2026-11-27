/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensorNorm
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The minimal and maximal C*-norms on `C(X) ⊙ C(Y)`

For compact Hausdorff spaces `X` and `Y`, the star homomorphism
`TauCeti.continuousMapTensorHom X Y : C(X) ⊗[ℂ] C(Y) → C(X × Y)`,
`f ⊗ g ↦ ((x, y) ↦ f x * g y)`, is isometric for both the minimal and the maximal C*-norm:

* `TauCeti.minTensorNorm_continuousMap` and `TauCeti.maxTensorNorm_continuousMap`:
  `‖z‖_min = ‖z‖_max = ‖(continuousMapTensorHom X Y) z‖_∞`;
* `TauCeti.minTensorNorm_eq_maxTensorNorm_continuousMap`: the two norms agree on
  `C(X) ⊗[ℂ] C(Y)`;
* `TauCeti.continuousMapTensorHom_injective` and `TauCeti.denseRange_continuousMapTensorHom`
  (Stone–Weierstrass): the completion of `C(X) ⊙ C(Y)` in either norm is `C(X × Y)`.

The upper bound is the content. A commuting pair of representations `π`, `ρ` of `C(X)` and `C(Y)`
on a Hilbert space `H` has commuting, star-closed ranges, so their double commutant `D` is a
closed commutative C*-subalgebra of `B(H)` containing every `(π × ρ) z`
(`TauCeti.CommutingRepresentationPair.tensorHom_mem_centralizer_centralizer`). By Gelfand
theory the norm of an element of `D` is the supremum of `|χ(·)|` over the characters `χ` of `D`.
A character `χ` restricts along `π` to a multiplicative linear functional on `C(X)`, which is
either `0` or the evaluation at a point `x`
(`ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval`), and likewise along `ρ`; so
`χ((π × ρ) z)` is `0` or the value of `(continuousMapTensorHom X Y) z` at a point `(x, y)`.
The lower bound comes from the one-dimensional representations `f ↦ f x` and `g ↦ g y`, whose
spatial tensor product sends `z` to the scalar `(continuousMapTensorHom X Y) z (x, y)`.

This is the `C(X) ⊙ C(Y)` Check of CStarAlgebras C5.1 and the norm half of the identification
`C(X) ⊗min C(Y) ≅ C(X × Y)` of C5.2.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.4.4.
-/

public section

noncomputable section

open TensorProduct ContinuousLinearMap UniformSpace
open scoped InnerProductSpace Pointwise

universe u v

/-! ### Multiplicative functionals on `C(X)` -/

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A multiplicative linear functional on `C(X, ℂ)` that need not preserve `1` is either `0` or
the evaluation at a point. -/
theorem nonUnitalAlgHom_eq_zero_or_exists_eval (ψ : C(X, ℂ) →ₙₐ[ℂ] ℂ) :
    ψ = 0 ∨ ∃ x : X, ∀ f, ψ f = f x := by
  have hidem : ψ 1 * ψ 1 = ψ 1 := by rw [← map_mul, mul_one]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h0 | h1
  · left
    ext f
    rw [← mul_one f, map_mul, h0, mul_zero, NonUnitalAlgHom.zero_apply]
  · right
    let φ : C(X, ℂ) →ₐ[ℂ] ℂ :=
      { ψ with
        map_one' := h1
        commutes' := fun c ↦ by
          simp [Algebra.algebraMap_eq_smul_one, h1] }
    obtain ⟨x, hx⟩ :=
      (WeakDual.CharacterSpace.continuousMapEval_bijective X ℂ).2
        (WeakDual.CharacterSpace.equivAlgHom.symm φ)
    refine ⟨x, fun f ↦ ?_⟩
    have := congr($hx f)
    simpa [φ] using this.symm

/-- Continuous complex functions separate the points of a compact Hausdorff space. -/
theorem exists_complex_apply_ne {x x' : X} (h : x ≠ x') : ∃ f : C(X, ℂ), f x ≠ f x' := by
  obtain ⟨f, h0, h1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed {x}) (isClosed_singleton : IsClosed {x'})
    (Set.disjoint_singleton.mpr h)
  refine ⟨(⟨fun t : ℝ ↦ (t : ℂ), Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f, ?_⟩
  simp [h0 (Set.mem_singleton x), h1 (Set.mem_singleton x')]

end ContinuousMap

namespace TauCeti

/-! ### The star homomorphism `C(X) ⊗ C(Y) → C(X × Y)` -/

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]

/-- The star homomorphism `C(X, ℂ) ⊗[ℂ] C(Y, ℂ) → C(X × Y, ℂ)`,
`f ⊗ g ↦ ((x, y) ↦ f x * g y)`. -/
def continuousMapTensorHom : C(X, ℂ) ⊗[ℂ] C(Y, ℂ) →⋆ₙₐ[ℂ] C(X × Y, ℂ) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom
    (ContinuousMap.compStarAlgHom' ℂ ℂ (ContinuousMap.fst : C(X × Y, X))).toNonUnitalStarAlgHom
    (ContinuousMap.compStarAlgHom' ℂ ℂ (ContinuousMap.snd : C(X × Y, Y))).toNonUnitalStarAlgHom
    fun _ _ ↦ Commute.all _ _

variable {X Y}

@[simp]
theorem continuousMapTensorHom_tmul_apply (f : C(X, ℂ)) (g : C(Y, ℂ)) (p : X × Y) :
    continuousMapTensorHom X Y (f ⊗ₜ g) p = f p.1 * g p.2 := by
  simp [continuousMapTensorHom]

/-! ### The upper bound: commuting pairs and Gelfand theory -/

namespace CommutingRepresentationPair

section Commutative

variable {A : Type u} {B : Type v} [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B]
variable (p : CommutingRepresentationPair A B)

/-- The union of the ranges of the two representations of a commuting pair of commutative
C*-algebras: a commuting star-closed set of operators. -/
def rangeUnion : Set (p.H →L[ℂ] p.H) :=
  Set.range p.left ∪ Set.range p.right

theorem star_rangeUnion_subset : star p.rangeUnion ⊆ p.rangeUnion := by
  rintro _ (⟨f, hf⟩ | ⟨g, hg⟩)
  · exact Or.inl ⟨star f, by rw [map_star, hf, star_star]⟩
  · exact Or.inr ⟨star g, by rw [map_star, hg, star_star]⟩

theorem rangeUnion_pairwise_commute : p.rangeUnion.Pairwise Commute := by
  have hl : ∀ f f' : A, Commute (p.left f) (p.left f') := fun f f' ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hr : ∀ g g' : B, Commute (p.right g) (p.right g') := fun g g' ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  rintro _ (⟨f, rfl⟩ | ⟨g, rfl⟩) _ (⟨f', rfl⟩ | ⟨g', rfl⟩) -
  · exact hl f f'
  · exact p.commute f g'
  · exact (p.commute f' g).symm
  · exact hr g g'

/-- The double commutant of the ranges of a commuting pair of commutative C*-algebras: a closed
commutative star subalgebra of `B(H)`. -/
def commutant : StarSubalgebra ℂ (p.H →L[ℂ] p.H) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ p.rangeUnion : Set _)

theorem coe_commutant :
    (p.commutant : Set (p.H →L[ℂ] p.H)) = p.rangeUnion.centralizer.centralizer := by
  rw [commutant, StarSubalgebra.coe_centralizer_centralizer,
    Set.union_eq_left.mpr p.star_rangeUnion_subset]

theorem isClosed_commutant : IsClosed (p.commutant : Set (p.H →L[ℂ] p.H)) := by
  rw [coe_commutant]
  exact Set.isClosed_centralizer _

theorem mul_comm_commutant (a b : p.commutant) : a * b = b * a := by
  refine Subtype.ext ?_
  have ha := a.property
  have hb := b.property
  rw [← SetLike.mem_coe, coe_commutant] at ha hb
  exact Set.centralizer_centralizer_comm_of_comm p.rangeUnion_pairwise_commute _ ha _ hb

theorem left_mem_commutant (f : A) : p.left f ∈ p.commutant := by
  rw [← SetLike.mem_coe, coe_commutant]
  exact Set.subset_centralizer_centralizer (Or.inl ⟨f, rfl⟩)

theorem right_mem_commutant (g : B) : p.right g ∈ p.commutant := by
  rw [← SetLike.mem_coe, coe_commutant]
  exact Set.subset_centralizer_centralizer (Or.inr ⟨g, rfl⟩)

theorem tensorHom_mem_commutant (z : A ⊗[ℂ] B) : p.tensorHom z ∈ p.commutant := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    rw [tensorHom_tmul]
    exact mul_mem (p.left_mem_commutant f) (p.right_mem_commutant g)
  | add z z' hz hz' => rw [map_add]; exact add_mem hz hz'

/-- The double commutant of a commuting pair of commutative C*-algebras is a commutative unital
C*-algebra. -/
@[reducible]
def commutantCommCStarAlgebra : CommCStarAlgebra p.commutant :=
  haveI := p.isClosed_commutant
  { StarSubalgebra.cstarAlgebra p.commutant with mul_comm := p.mul_comm_commutant }

/-- The restriction of the representation of `A` to a multiplicative functional, through a
character of the double commutant. -/
def leftChar (χ : p.commutant →ₙₐ[ℂ] ℂ) : A →ₙₐ[ℂ] ℂ :=
  χ.comp
    { toFun := fun f ↦ ⟨p.left f, p.left_mem_commutant f⟩
      map_smul' := fun c f ↦ Subtype.ext (map_smul p.left c f)
      map_zero' := Subtype.ext (map_zero p.left)
      map_add' := fun f f' ↦ Subtype.ext (map_add p.left f f')
      map_mul' := fun f f' ↦ Subtype.ext (map_mul p.left f f') }

/-- The restriction of the representation of `B` to a multiplicative functional, through a
character of the double commutant. -/
def rightChar (χ : p.commutant →ₙₐ[ℂ] ℂ) : B →ₙₐ[ℂ] ℂ :=
  χ.comp
    { toFun := fun g ↦ ⟨p.right g, p.right_mem_commutant g⟩
      map_smul' := fun c g ↦ Subtype.ext (map_smul p.right c g)
      map_zero' := Subtype.ext (map_zero p.right)
      map_add' := fun g g' ↦ Subtype.ext (map_add p.right g g')
      map_mul' := fun g g' ↦ Subtype.ext (map_mul p.right g g') }

/-- A character of the double commutant is multiplicative on `π a * ρ b`. -/
theorem apply_tensorHom_tmul (χ : p.commutant →ₙₐ[ℂ] ℂ) (f : A) (g : B) :
    χ ⟨p.tensorHom (f ⊗ₜ g), p.tensorHom_mem_commutant _⟩ = p.leftChar χ f * p.rightChar χ g := by
  change _ = χ ⟨p.left f, p.left_mem_commutant f⟩ * χ ⟨p.right g, p.right_mem_commutant g⟩
  rw [← map_mul]
  exact congr_arg χ (Subtype.ext (p.tensorHom_tmul f g))

/-- A character of the double commutant is additive along the integrated form. -/
theorem apply_tensorHom_add (χ : p.commutant →ₙₐ[ℂ] ℂ) (z z' : A ⊗[ℂ] B) :
    χ ⟨p.tensorHom (z + z'), p.tensorHom_mem_commutant _⟩ =
      χ ⟨p.tensorHom z, p.tensorHom_mem_commutant _⟩ +
        χ ⟨p.tensorHom z', p.tensorHom_mem_commutant _⟩ := by
  rw [← map_add]
  exact congr_arg χ (Subtype.ext (map_add p.tensorHom z z'))

end Commutative

variable [CompactSpace X] [CompactSpace Y]
variable (p : CommutingRepresentationPair C(X, ℂ) C(Y, ℂ))

/-- A character of the double commutant takes values on the integrated form of the pair that are
bounded by the supremum norm of the corresponding function on `X × Y`. -/
theorem norm_apply_tensorHom_le [T2Space X] [T2Space Y] (χ : p.commutant →ₙₐ[ℂ] ℂ)
    (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) :
    ‖χ ⟨p.tensorHom z, p.tensorHom_mem_commutant z⟩‖ ≤ ‖continuousMapTensorHom X Y z‖ := by
  rcases ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval (p.leftChar χ) with hl | ⟨x, hx⟩
  · have : χ ⟨p.tensorHom z, p.tensorHom_mem_commutant z⟩ = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul f g => rw [apply_tensorHom_tmul, hl, NonUnitalAlgHom.zero_apply, zero_mul]
      | add z z' hz hz' => rw [apply_tensorHom_add, hz, hz', add_zero]
    rw [this, norm_zero]
    exact norm_nonneg _
  rcases ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval (p.rightChar χ) with hr | ⟨y, hy⟩
  · have : χ ⟨p.tensorHom z, p.tensorHom_mem_commutant z⟩ = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul f g => rw [apply_tensorHom_tmul, hr, NonUnitalAlgHom.zero_apply, mul_zero]
      | add z z' hz hz' => rw [apply_tensorHom_add, hz, hz', add_zero]
    rw [this, norm_zero]
    exact norm_nonneg _
  have : χ ⟨p.tensorHom z, p.tensorHom_mem_commutant z⟩ = continuousMapTensorHom X Y z (x, y) := by
    induction z using TensorProduct.inductionOn with
    | tmul f g => rw [apply_tensorHom_tmul, hx, hy, continuousMapTensorHom_tmul_apply]
    | add z z' hz hz' =>
      rw [apply_tensorHom_add, hz, hz', map_add, ContinuousMap.add_apply]
  rw [this]
  exact (continuousMapTensorHom X Y z).norm_coe_le_norm (x, y)

/-- **The upper bound.** The integrated form of a commuting pair of representations of `C(X)` and
`C(Y)` is bounded by the supremum norm on `X × Y`. -/
theorem norm_tensorHom_le_norm_continuousMapTensorHom [T2Space X] [T2Space Y]
    (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) : ‖p.tensorHom z‖ ≤ ‖continuousMapTensorHom X Y z‖ := by
  let := p.commutantCommCStarAlgebra
  let T : p.commutant := ⟨p.tensorHom z, p.tensorHom_mem_commutant z⟩
  have hT : ‖p.tensorHom z‖ = ‖WeakDual.gelfandTransform ℂ p.commutant T‖ :=
    ((AddMonoidHomClass.isometry_iff_norm _).mp (gelfandTransform_isometry p.commutant) T).symm
  rw [hT, ContinuousMap.norm_le _ (norm_nonneg _)]
  intro χ
  exact p.norm_apply_tensorHom_le (WeakDual.CharacterSpace.toNonUnitalAlgHom χ) z

end CommutingRepresentationPair

/-! ### The lower bound: one-dimensional representations -/

/-- **The lower bound.** The minimal norm dominates the supremum norm on `X × Y`: the
one-dimensional representations `f ↦ f x` and `g ↦ g y` have spatial tensor product
`z ↦ (continuousMapTensorHom X Y) z (x, y)`. -/
theorem norm_continuousMapTensorHom_le_minTensorNorm [CompactSpace X] [CompactSpace Y]
    (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) :
    ‖continuousMapTensorHom X Y z‖ ≤ minTensorNorm C(X, ℂ) C(Y, ℂ) z := by
  rw [ContinuousMap.norm_le _ (minTensorNorm_nonneg z)]
  rintro ⟨x, y⟩
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let F := EuclideanSpace ℂ (ULift.{v} Unit)
  let π : C(X, ℂ) →⋆ₙₐ[ℂ] (E →L[ℂ] E) :=
    ((StarAlgHom.ofId ℂ (E →L[ℂ] E)).comp
      (ContinuousMap.evalStarAlgHom ℂ ℂ x)).toNonUnitalStarAlgHom
  let ρ : C(Y, ℂ) →⋆ₙₐ[ℂ] (F →L[ℂ] F) :=
    ((StarAlgHom.ofId ℂ (F →L[ℂ] F)).comp
      (ContinuousMap.evalStarAlgHom ℂ ℂ y)).toNonUnitalStarAlgHom
  obtain ⟨e, he⟩ : ∃ e : E, ‖e‖ = 1 := ⟨_, EuclideanSpace.orthonormal_single.1 ⟨()⟩⟩
  obtain ⟨f, hf⟩ : ∃ f : F, ‖f‖ = 1 := ⟨_, EuclideanSpace.orthonormal_single.1 ⟨()⟩⟩
  let w : Completion (E ⊗[ℂ] F) := ((e ⊗ₜ f : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F))
  have hw : ‖w‖ = 1 := by
    have : ⟪w, w⟫_ℂ = 1 := by simp [w, he, hf]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), this]
    simp
  let T := π.spatialTensorHom ρ z
  have key : ⟪w, T w⟫_ℂ = continuousMapTensorHom X Y z (x, y) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [T, w, π, ρ, NonUnitalStarAlgHom.spatialTensorHom_tmul, mapLCompletion_tmul,
        StarAlgHom.coe_toNonUnitalStarAlgHom, StarAlgHom.comp_apply, StarAlgHom.ofId_apply,
        ContinuousMap.evalStarAlgHom_apply, Algebra.algebraMap_eq_smul_one]
      simp only [smul_apply, one_apply_eq_self]
      rw [Completion.inner_coe, TensorProduct.inner_tmul, inner_smul_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, he, hf,
        continuousMapTensorHom_tmul_apply]
      simp [mul_comm]
    | add z z' hz hz' =>
      simp only [T, map_add, add_apply, inner_add_right, ContinuousMap.add_apply]
      rw [hz, hz']
  calc ‖continuousMapTensorHom X Y z (x, y)‖ = ‖⟪w, T w⟫_ℂ‖ := by rw [key]
    _ ≤ ‖w‖ * ‖T w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖T‖ * ‖w‖) := by gcongr; exact T.le_opNorm w
    _ = ‖T‖ := by rw [hw, one_mul, mul_one]
    _ ≤ minTensorNorm C(X, ℂ) C(Y, ℂ) z := norm_spatialTensorHom_le_minTensorNorm π ρ z

/-! ### The minimal and maximal norms on `C(X) ⊙ C(Y)` -/

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- **The maximal norm on `C(X) ⊙ C(Y)` is the supremum norm on `X × Y`.** -/
theorem maxTensorNorm_continuousMap (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) :
    maxTensorNorm C(X, ℂ) C(Y, ℂ) z = ‖continuousMapTensorHom X Y z‖ :=
  le_antisymm
    (maxTensorNorm_le_of_forall fun p ↦ p.norm_tensorHom_le_norm_continuousMapTensorHom z)
    ((norm_continuousMapTensorHom_le_minTensorNorm z).trans (minTensorNorm_le_maxTensorNorm z))

/-- **The minimal norm on `C(X) ⊙ C(Y)` is the supremum norm on `X × Y`.** -/
theorem minTensorNorm_continuousMap (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) :
    minTensorNorm C(X, ℂ) C(Y, ℂ) z = ‖continuousMapTensorHom X Y z‖ :=
  le_antisymm ((minTensorNorm_le_maxTensorNorm z).trans (maxTensorNorm_continuousMap z).le)
    (norm_continuousMapTensorHom_le_minTensorNorm z)

/-- **`C(X) ⊙ C(Y)` has a unique C*-norm between the minimal and the maximal one**: the two
agree. -/
theorem minTensorNorm_eq_maxTensorNorm_continuousMap (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) :
    minTensorNorm C(X, ℂ) C(Y, ℂ) z = maxTensorNorm C(X, ℂ) C(Y, ℂ) z := by
  rw [minTensorNorm_continuousMap, maxTensorNorm_continuousMap]

/-- The star homomorphism `C(X) ⊗[ℂ] C(Y) → C(X × Y)` is injective. -/
theorem continuousMapTensorHom_injective : Function.Injective (continuousMapTensorHom X Y) := by
  intro z z' h
  rw [← sub_eq_zero, ← maxTensorNorm_eq_zero_iff, maxTensorNorm_continuousMap, map_sub, h,
    sub_self, norm_zero]

/-- **Stone–Weierstrass**: the functions `(x, y) ↦ Σ fᵢ x * gᵢ y` are dense in `C(X × Y)`. -/
theorem denseRange_continuousMapTensorHom : DenseRange (continuousMapTensorHom X Y) := by
  let S : StarSubalgebra ℂ C(X × Y, ℂ) :=
    { carrier := Set.range (continuousMapTensorHom X Y)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, map_mul _ a b⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add _ a b⟩
      algebraMap_mem' := fun c ↦ ⟨c • (1 ⊗ₜ 1), by ext; simp [Algebra.algebraMap_eq_smul_one]⟩
      star_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨star a, map_star _ a⟩ }
  have hsep : S.SeparatesPoints := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hne
    by_cases hx : x = x'
    · subst hx
      obtain ⟨g, hg⟩ := ContinuousMap.exists_complex_apply_ne (fun h ↦ hne (by rw [h]) : y ≠ y')
      exact ⟨_, ⟨_, ⟨1 ⊗ₜ g, rfl⟩, rfl⟩, by simpa using hg⟩
    · obtain ⟨f, hf⟩ := ContinuousMap.exists_complex_apply_ne hx
      exact ⟨_, ⟨_, ⟨f ⊗ₜ 1, rfl⟩, rfl⟩, by simpa using hf⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  rw [DenseRange, dense_iff_closure_eq]
  have := congr_arg (fun T : StarSubalgebra ℂ C(X × Y, ℂ) ↦ (T : Set C(X × Y, ℂ))) h
  simp only [StarSubalgebra.topologicalClosure_coe, StarSubalgebra.coe_top] at this
  exact this

end TauCeti
