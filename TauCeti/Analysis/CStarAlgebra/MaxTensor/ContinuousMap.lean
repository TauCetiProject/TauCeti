/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.ProdApproximation
public import TauCeti.Analysis.CStarAlgebra.MinTensorNorm
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import TauCeti.Analysis.Normed.Algebra.Character.ContinuousMap

/-!
# The minimal and maximal C*-norms on `C(X) ⊙ C(Y)`

For compact Hausdorff spaces `X` and `Y`, the star homomorphism
`TauCeti.continuousMapTensorHom X Y : C(X) ⊗[ℂ] C(Y) → C(X × Y)`,
`f ⊗ g ↦ ((x, y) ↦ f x * g y)` (a star homomorphism version of Mathlib's linear map
`ContinuousMap.tensorHom`, see `TauCeti.coe_continuousMapTensorHom`), is isometric for both the
minimal and the maximal C*-norm:

* `TauCeti.minTensorNorm_continuousMap` and `TauCeti.maxTensorNorm_continuousMap`:
  `‖z‖_min = ‖z‖_max = ‖(continuousMapTensorHom X Y) z‖_∞`;
* `TauCeti.minTensorNorm_eq_maxTensorNorm_continuousMap`: the two norms agree on
  `C(X) ⊗[ℂ] C(Y)`;
* `TauCeti.continuousMapTensorHom_injective` and `TauCeti.denseRange_continuousMapTensorHom`
  (Stone–Weierstrass): the map is injective with dense range, from which the identification
  of the completion of `C(X) ⊙ C(Y)` in either norm with `C(X × Y)` follows once that completion
  isomorphism is constructed. Through `TauCeti.coe_continuousMapTensorHom` the density also holds
  for Mathlib's `ContinuousMap.tensorHom` (`ContinuousMap.denseRange_tensorHom_complex`).

The upper bound is the content. A commuting pair of representations `π`, `ρ` of `C(X)` and `C(Y)`
on a Hilbert space `H` has commuting, star-closed ranges, so their double commutant `D` is a
closed commutative C*-subalgebra of `B(H)` containing every `(π × ρ) z`
(`TauCeti.CommutingRepresentationPair.tensorHom_mem_doubleCommutant`). By Gelfand
theory the norm of an element of `D` is the supremum of `|χ(·)|` over the characters `χ` of `D`.
A character `χ` restricts along `π` to a multiplicative linear functional on `C(X)`, which is
either `0` or the evaluation at a point `x`
(`ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval`), and likewise along `ρ`; so
`χ((π × ρ) z)` is `0` or the value of `(continuousMapTensorHom X Y) z` at a point `(x, y)`.
The lower bound comes from the one-dimensional representations `f ↦ f x` and `g ↦ g y`, whose
spatial tensor product sends `z` to the scalar `(continuousMapTensorHom X Y) z (x, y)`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.4.4.
-/

public section

noncomputable section

open TensorProduct ContinuousLinearMap UniformSpace
open scoped InnerProductSpace Pointwise

universe u v

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

/-- `TauCeti.continuousMapTensorHom` is Mathlib's linear map `ContinuousMap.tensorHom`. -/
theorem coe_continuousMapTensorHom :
    ⇑(continuousMapTensorHom X Y) =
      ⇑(ContinuousMap.tensorHom : C(X, ℂ) ⊗[ℂ] C(Y, ℂ) →ₗ[ℂ] C(X × Y, ℂ)) := by
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul f g => ext; simp [continuousMapTensorHom]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

@[simp]
theorem continuousMapTensorHom_tmul_apply (f : C(X, ℂ)) (g : C(Y, ℂ)) (p : X × Y) :
    continuousMapTensorHom X Y (f ⊗ₜ g) p = f p.1 * g p.2 := by
  rw [coe_continuousMapTensorHom, ContinuousMap.tensorHom_tmul, ContinuousMap.prodMul_apply]

/-! ### The upper bound: commuting pairs and Gelfand theory -/

namespace CommutingRepresentationPair

section Commutative

variable {A : Type u} {B : Type v} [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B]
variable (p : CommutingRepresentationPair A B)

private theorem star_range_union_subset :
    star (Set.range p.left ∪ Set.range p.right) ⊆ Set.range p.left ∪ Set.range p.right := by
  rintro _ (⟨f, hf⟩ | ⟨g, hg⟩)
  · exact Or.inl ⟨star f, by rw [map_star, hf, star_star]⟩
  · exact Or.inr ⟨star g, by rw [map_star, hg, star_star]⟩

private theorem range_union_pairwise_commute :
    (Set.range p.left ∪ Set.range p.right).Pairwise Commute := by
  have hl : ∀ f f' : A, Commute (p.left f) (p.left f') := fun f f' ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hr : ∀ g g' : B, Commute (p.right g) (p.right g') := fun g g' ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  rintro _ (⟨f, rfl⟩ | ⟨g, rfl⟩) _ (⟨f', rfl⟩ | ⟨g', rfl⟩) -
  · exact hl f f'
  · exact p.commute f g'
  · exact (p.commute f' g).symm
  · exact hr g g'

/-- The double commutant of the union of the ranges of a commuting pair of commutative
C*-algebras: a closed commutative star subalgebra of `B(H)`. -/
def doubleCommutant : StarSubalgebra ℂ (p.H →L[ℂ] p.H) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (Set.range p.left ∪ Set.range p.right) : Set _)

theorem coe_doubleCommutant :
    (p.doubleCommutant : Set (p.H →L[ℂ] p.H)) =
      (Set.range p.left ∪ Set.range p.right).centralizer.centralizer := by
  rw [doubleCommutant, StarSubalgebra.coe_centralizer_centralizer,
    Set.union_eq_left.mpr p.star_range_union_subset]

theorem isClosed_doubleCommutant : IsClosed (p.doubleCommutant : Set (p.H →L[ℂ] p.H)) := by
  rw [coe_doubleCommutant]
  exact Set.isClosed_centralizer _

theorem mul_comm_doubleCommutant (a b : p.doubleCommutant) : a * b = b * a := by
  refine Subtype.ext ?_
  have ha := a.property
  have hb := b.property
  rw [← SetLike.mem_coe, coe_doubleCommutant] at ha hb
  exact Set.centralizer_centralizer_comm_of_comm p.range_union_pairwise_commute _ ha _ hb

theorem left_mem_doubleCommutant (f : A) : p.left f ∈ p.doubleCommutant := by
  rw [← SetLike.mem_coe, coe_doubleCommutant]
  exact Set.subset_centralizer_centralizer (Or.inl ⟨f, rfl⟩)

theorem right_mem_doubleCommutant (g : B) : p.right g ∈ p.doubleCommutant := by
  rw [← SetLike.mem_coe, coe_doubleCommutant]
  exact Set.subset_centralizer_centralizer (Or.inr ⟨g, rfl⟩)

theorem tensorHom_mem_doubleCommutant (z : A ⊗[ℂ] B) : p.tensorHom z ∈ p.doubleCommutant := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    rw [tensorHom_tmul]
    exact mul_mem (p.left_mem_doubleCommutant f) (p.right_mem_doubleCommutant g)
  | add z z' hz hz' => rw [map_add]; exact add_mem hz hz'

/-- The double commutant of a commuting pair of commutative C*-algebras is a commutative unital
C*-algebra. -/
private abbrev doubleCommutantCommCStarAlgebra : CommCStarAlgebra p.doubleCommutant :=
  haveI := p.isClosed_doubleCommutant
  { StarSubalgebra.cstarAlgebra p.doubleCommutant with mul_comm := p.mul_comm_doubleCommutant }

/-- The restriction of the representation of `A` to a multiplicative functional, through a
character of the double commutant. -/
private def leftChar (χ : p.doubleCommutant →ₙₐ[ℂ] ℂ) : A →ₙₐ[ℂ] ℂ :=
  χ.comp ((p.left : A →ₙₐ[ℂ] (p.H →L[ℂ] p.H)).codRestrict
    p.doubleCommutant.toNonUnitalSubalgebra p.left_mem_doubleCommutant)

/-- The restriction of the representation of `B` to a multiplicative functional, through a
character of the double commutant. -/
private def rightChar (χ : p.doubleCommutant →ₙₐ[ℂ] ℂ) : B →ₙₐ[ℂ] ℂ :=
  χ.comp ((p.right : B →ₙₐ[ℂ] (p.H →L[ℂ] p.H)).codRestrict
    p.doubleCommutant.toNonUnitalSubalgebra p.right_mem_doubleCommutant)

/-- The pullback of a character of the double commutant along the integrated form. -/
private def tensorChar (χ : p.doubleCommutant →ₙₐ[ℂ] ℂ) : A ⊗[ℂ] B →ₙₐ[ℂ] ℂ :=
  χ.comp ((p.tensorHom : A ⊗[ℂ] B →ₙₐ[ℂ] (p.H →L[ℂ] p.H)).codRestrict
    p.doubleCommutant.toNonUnitalSubalgebra p.tensorHom_mem_doubleCommutant)

/-- A character of the double commutant is multiplicative on `π a * ρ b`. -/
private theorem tensorChar_tmul (χ : p.doubleCommutant →ₙₐ[ℂ] ℂ) (f : A) (g : B) :
    p.tensorChar χ (f ⊗ₜ g) = p.leftChar χ f * p.rightChar χ g := by
  rw [leftChar, rightChar, NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.comp_apply, ← map_mul]
  exact congr_arg χ (Subtype.ext (p.tensorHom_tmul f g))

end Commutative

variable [CompactSpace X] [CompactSpace Y]
variable (p : CommutingRepresentationPair C(X, ℂ) C(Y, ℂ))

/-- A character of the double commutant takes values on the integrated form of the pair that are
bounded by the supremum norm of the corresponding function on `X × Y`. -/
private theorem norm_tensorChar_le [T2Space X] [T2Space Y] (χ : p.doubleCommutant →ₙₐ[ℂ] ℂ)
    (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) : ‖p.tensorChar χ z‖ ≤ ‖continuousMapTensorHom X Y z‖ := by
  by_cases h0 : ∀ f g, p.leftChar χ f * p.rightChar χ g = 0
  · have : p.tensorChar χ z = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul f g => rw [tensorChar_tmul, h0]
      | add z z' hz hz' => rw [map_add, hz, hz', add_zero]
    rw [this, norm_zero]
    exact norm_nonneg _
  push Not at h0
  obtain ⟨f₀, g₀, hfg⟩ := h0
  obtain ⟨x, hx⟩ := (ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval
    (p.leftChar χ)).resolve_left fun h ↦ hfg (by rw [h, NonUnitalAlgHom.zero_apply, zero_mul])
  obtain ⟨y, hy⟩ := (ContinuousMap.nonUnitalAlgHom_eq_zero_or_exists_eval
    (p.rightChar χ)).resolve_left fun h ↦ hfg (by rw [h, NonUnitalAlgHom.zero_apply, mul_zero])
  have : p.tensorChar χ z = continuousMapTensorHom X Y z (x, y) := by
    induction z using TensorProduct.inductionOn with
    | tmul f g => rw [tensorChar_tmul, hx, hy, continuousMapTensorHom_tmul_apply]
    | add z z' hz hz' => rw [map_add, hz, hz', map_add, ContinuousMap.add_apply]
  rw [this]
  exact (continuousMapTensorHom X Y z).norm_coe_le_norm (x, y)

/-- **The upper bound.** The integrated form of a commuting pair of representations of `C(X)` and
`C(Y)` is bounded by the supremum norm on `X × Y`. -/
theorem norm_tensorHom_le_norm_continuousMapTensorHom [T2Space X] [T2Space Y]
    (z : C(X, ℂ) ⊗[ℂ] C(Y, ℂ)) : ‖p.tensorHom z‖ ≤ ‖continuousMapTensorHom X Y z‖ := by
  let := p.doubleCommutantCommCStarAlgebra
  let T : p.doubleCommutant := ⟨p.tensorHom z, p.tensorHom_mem_doubleCommutant z⟩
  -- The double commutant carries the norm of `B(H)`, restricted to the subalgebra.
  have hT : ‖p.tensorHom z‖ = ‖T‖ := rfl
  have hG : ‖T‖ = ‖WeakDual.gelfandTransform ℂ p.doubleCommutant T‖ :=
    ((AddMonoidHomClass.isometry_iff_norm _).mp
      (gelfandTransform_isometry p.doubleCommutant) T).symm
  rw [hT, hG, ContinuousMap.norm_le _ (norm_nonneg _)]
  intro χ
  have hχ : WeakDual.gelfandTransform ℂ p.doubleCommutant T χ =
      p.tensorChar (WeakDual.CharacterSpace.toNonUnitalAlgHom χ) z := by
    rw [WeakDual.gelfandTransform_apply_apply, tensorChar, NonUnitalAlgHom.comp_apply]
    -- `T` is the corestriction of the integrated form to the double commutant, evaluated at `z`.
    rfl
  rw [hχ]
  exact p.norm_tensorChar_le (WeakDual.CharacterSpace.toNonUnitalAlgHom χ) z

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
      simp [T, w, π, ρ, Algebra.algebraMap_eq_smul_one, inner_smul_right, he, hf, mul_comm]
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

/-- **The minimal and maximal C*-norms on `C(X) ⊙ C(Y)` agree.** -/
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
      obtain ⟨g, hg, hgy⟩ :=
        separatesPoints_continuous_of_t35Space (fun h ↦ hne (by rw [h]) : y ≠ y')
      exact ⟨_, ⟨_, ⟨1 ⊗ₜ ⟨fun t ↦ (g t : ℂ), Complex.continuous_ofReal.comp hg⟩, rfl⟩, rfl⟩,
        by simpa using hgy⟩
    · obtain ⟨f, hf, hfx⟩ := separatesPoints_continuous_of_t35Space hx
      exact ⟨_, ⟨_, ⟨⟨fun t ↦ (f t : ℂ), Complex.continuous_ofReal.comp hf⟩ ⊗ₜ 1, rfl⟩, rfl⟩,
        by simpa using hfx⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  rw [DenseRange, dense_iff_closure_eq]
  have := congr_arg (fun T : StarSubalgebra ℂ C(X × Y, ℂ) ↦ (T : Set C(X × Y, ℂ))) h
  simp only [StarSubalgebra.topologicalClosure_coe, StarSubalgebra.coe_top] at this
  exact this

/-- Mathlib's linear map `ContinuousMap.tensorHom : C(X, ℂ) ⊗[ℂ] C(Y, ℂ) → C(X × Y, ℂ)` has dense
range for compact Hausdorff `X` and `Y`. -/
theorem _root_.ContinuousMap.denseRange_tensorHom_complex :
    DenseRange (ContinuousMap.tensorHom : C(X, ℂ) ⊗[ℂ] C(Y, ℂ) → C(X × Y, ℂ)) :=
  coe_continuousMapTensorHom (X := X) (Y := Y) ▸ denseRange_continuousMapTensorHom

end TauCeti
