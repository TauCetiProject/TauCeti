/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PointLattice
import Mathlib.Analysis.Normed.Field.ProperSpace
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete

/-!
# Norm-one vectors of the lattices of finite adelic points

Let `E` be a CM field, `V = (J, x)` a hermitian space with an adelic frame over `E`
(`TauCeti.FramedHermitianSpace`), and `g` a point of the finite adelic unitary group `G_f`. The
**norm-one vectors of the lattice of `g`** are the rational vectors `y ∈ E^n` with
`h_J(y, y) = y* J y = 1` whose image in `𝔸_f^n` lies in the lattice `(x_f g) Ôⁿ` of `g`
(`TauCeti.FramedHermitianSpace.finiteLattice`). For the standard space `I_n = (1_n, 1)` these are
the `y ∈ E^n` with `y* y = 1` and `g⁻¹ y ∈ Ôⁿ`.

Counting them is the vector count in the mass formulas for definite hermitian lattices, read as
a function on `G_f`. This file shows that the count is well defined and descends to the double
cosets `Γ_{V,f} \ G_f / K₀`:

* moving `g` on the right by the standard integral unitary group `K₀` does not change the set;
* moving `g` on the left by a finite rational point `x_f⁻¹ γ x_f`, `γ ∈ U(J)(E⁺)`, moves the set
  by `γ`, bijectively;
* when all signs of `V` are `+1`, so that `J` is positive definite at every infinite place, the
  set is finite: its vectors are bounded at the infinite places, as the frame carries them to
  vectors of euclidean norm one, and their finite parts lie in the compact lattice of `g`.

## Main declarations

* `TauCeti.FramedHermitianSpace.normOneVectors`: the norm-one vectors of the lattice of `g`.
* `TauCeti.FramedHermitianSpace.mem_normOneVectors_standard_iff`: the description for the
  standard space.
* `TauCeti.FramedHermitianSpace.normOneVectors_mul_of_mem_integralAdelicUnitaryGroup`:
  invariance under `K₀` on the right.
* `TauCeti.FramedHermitianSpace.normOneVectorsEquiv`,
  `TauCeti.FramedHermitianSpace.ncard_normOneVectors_mul_of_mem_finiteRationalPoints`: transport
  by the finite rational points on the left.
* `TauCeti.FramedHermitianSpace.finite_normOneVectors`: finiteness for spaces of signs
  `(1, …, 1)`.

## Attribution

The set of norm-one lattice vectors is `New.normOneLatticeVectors` in `src/Lib/SiegelWeil/Mass.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The
generalisation to spaces with an adelic frame and the invariance and finiteness statements here
are independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing ComplexConjugate

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ}
  (V : FramedHermitianSpace E s)

/-- The **norm-one vectors of the lattice of `g`**: the rational vectors `y ∈ E^n` with
`h_J(y, y) = y* J y = 1` whose image in `𝔸_f^n` lies in the lattice `(x_f g) Ôⁿ` of the finite
unitary point `g`. -/
def normOneVectors (g : finiteAdelicUnitaryGroup E ι) : Set (ι → E) :=
  {y | star y ⬝ᵥ V.gram *ᵥ y = 1 ∧ algebraMap E 𝔸ᶠ[E] ∘ y ∈ V.finiteLattice g}

/-- Membership in the norm-one vectors: `h_J(y, y) = 1`, and `y` lies in the lattice of `g`. -/
theorem mem_normOneVectors_iff {g : finiteAdelicUnitaryGroup E ι} {y : ι → E} :
    y ∈ V.normOneVectors g ↔
      star y ⬝ᵥ V.gram *ᵥ y = 1 ∧ algebraMap E 𝔸ᶠ[E] ∘ y ∈ V.finiteLattice g :=
  Iff.rfl

/-- The zero vector does not have norm one. -/
@[simp]
theorem zero_notMem_normOneVectors (g : finiteAdelicUnitaryGroup E ι) :
    (0 : ι → E) ∉ V.normOneVectors g := by
  simp [mem_normOneVectors_iff]

/-- The norm-one vectors are stable under negation. -/
@[simp]
theorem neg_mem_normOneVectors_iff {g : finiteAdelicUnitaryGroup E ι} {y : ι → E} :
    -y ∈ V.normOneVectors g ↔ y ∈ V.normOneVectors g := by
  have hneg : algebraMap E 𝔸ᶠ[E] ∘ (-y) = -(algebraMap E 𝔸ᶠ[E] ∘ y) := by
    ext i
    simp
  simp only [mem_normOneVectors_iff, star_neg, neg_dotProduct, mulVec_neg, dotProduct_neg,
    neg_neg, hneg, neg_mem_iff]

/-- At the identity point the norm-one vectors are the vectors of `h_J`-norm one in the lattice
`Λ_V` of the space. -/
theorem mem_normOneVectors_one_iff {y : ι → E} :
    y ∈ V.normOneVectors 1 ↔ star y ⬝ᵥ V.gram *ᵥ y = 1 ∧ y ∈ V.lattice := by
  rw [mem_normOneVectors_iff, mem_finiteLattice_one_iff]

/-- **The norm-one vectors of the standard space**: for `I_n = (1_n, 1)` they are the `y ∈ E^n`
with `y* y = 1` and `g⁻¹ y ∈ Ôⁿ`. -/
@[simp]
theorem mem_normOneVectors_standard_iff {g : finiteAdelicUnitaryGroup E ι} {y : ι → E} :
    y ∈ (standard E ι).normOneVectors g ↔ star y ⬝ᵥ y = 1 ∧
      ∀ i, ((↑(g : GL ι 𝔸ᶠ[E])⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (algebraMap E 𝔸ᶠ[E] ∘ y)) i ∈
        FiniteAdeleRing.integralAdeles (𝓞 E) E := by
  simp [mem_normOneVectors_iff]

/-- The standard basis vectors are norm-one vectors of the standard lattice `𝓞_Eⁿ`. -/
theorem single_one_mem_normOneVectors_standard_one (i : ι) :
    Pi.single i 1 ∈ (standard E ι).normOneVectors 1 := by
  rw [mem_normOneVectors_one_iff, mem_lattice_standard_iff]
  refine ⟨by simp [Pi.star_single], fun j ↦ ?_⟩
  by_cases hij : j = i
  · subst hij
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hij]⟩

/-! ### Invariance under the integral unitary group -/

/-- **Right invariance under `K₀`**: moving `g` by an element of the standard integral unitary
group does not change its lattice, hence its norm-one vectors. -/
theorem normOneVectors_mul_of_mem_integralAdelicUnitaryGroup (g : finiteAdelicUnitaryGroup E ι)
    {k : finiteAdelicUnitaryGroup E ι} (hk : k ∈ integralAdelicUnitaryGroup E ι) :
    V.normOneVectors (g * k) = V.normOneVectors g := by
  ext y
  rw [mem_normOneVectors_iff, mem_normOneVectors_iff,
    V.finiteLattice_mul_of_mem_integralAdelicUnitaryGroup g k hk]

/-! ### Transport by the rational points -/

/-- **Rational isometries move the norm-one vectors.** For `γ ∈ U(J)(E⁺)`, `γ y` is a norm-one
vector of the lattice of `x_f⁻¹ γ x_f g` exactly when `y` is a norm-one vector of the lattice of
`g`. -/
@[simp]
theorem mulVec_mem_normOneVectors_rationalEmbedding_mul_iff (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι) (y : ι → E) :
    (↑(γ : GL ι E) : Matrix ι ι E) *ᵥ y ∈
        V.normOneVectors (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g) ↔
      y ∈ V.normOneVectors g := by
  have hmap : algebraMap E 𝔸ᶠ[E] ∘ ((↑(γ : GL ι E) : Matrix ι ι E) *ᵥ y) =
      (↑(GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL ι E)) : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
        (algebraMap E 𝔸ᶠ[E] ∘ y) := by
    ext i
    simp [RingHom.map_mulVec]
  rw [mem_normOneVectors_iff, mem_normOneVectors_iff, hmap,
    mulVec_mem_finiteLattice_rationalEmbedding_mul_iff,
    mem_unitaryGroupOf_iff_forall_dotProduct.1 γ.property]

/-- For `γ ∈ U(J)(E⁺)`, `y` is a norm-one vector of the lattice of `x_f⁻¹ γ x_f g` exactly when
`γ⁻¹ y` is a norm-one vector of the lattice of `g`. -/
theorem mem_normOneVectors_rationalEmbedding_mul_iff (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι) (y : ι → E) :
    y ∈ V.normOneVectors (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g) ↔
      (↑(γ : GL ι E)⁻¹ : Matrix ι ι E) *ᵥ y ∈ V.normOneVectors g := by
  rw [← V.mulVec_mem_normOneVectors_rationalEmbedding_mul_iff γ g
    ((↑(γ : GL ι E)⁻¹ : Matrix ι ι E) *ᵥ y), mulVec_mulVec, Units.mul_inv, one_mulVec]

/-- The bijection `y ↦ γ y` from the norm-one vectors of the lattice of `g` to those of the
lattice of `x_f⁻¹ γ x_f g`, for `γ ∈ U(J)(E⁺)`. -/
def normOneVectorsEquiv (γ : unitaryGroupOf V.gram) (g : finiteAdelicUnitaryGroup E ι) :
    V.normOneVectors g ≃
      V.normOneVectors (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g) where
  toFun y := ⟨(↑(γ : GL ι E) : Matrix ι ι E) *ᵥ y,
    (V.mulVec_mem_normOneVectors_rationalEmbedding_mul_iff γ g y).2 y.property⟩
  invFun y := ⟨(↑(γ : GL ι E)⁻¹ : Matrix ι ι E) *ᵥ y,
    (V.mem_normOneVectors_rationalEmbedding_mul_iff γ g y).1 y.property⟩
  left_inv y := Subtype.ext (by simp [mulVec_mulVec])
  right_inv y := Subtype.ext (by simp [mulVec_mulVec])

/-- The bijection of norm-one vectors induced by `γ` is multiplication by `γ`. -/
@[simp]
theorem coe_normOneVectorsEquiv_apply (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι) (y : V.normOneVectors g) :
    (V.normOneVectorsEquiv γ g y : ι → E) = (↑(γ : GL ι E) : Matrix ι ι E) *ᵥ y :=
  (rfl)

/-- The inverse bijection of norm-one vectors induced by `γ` is multiplication by `γ⁻¹`. -/
@[simp]
theorem coe_normOneVectorsEquiv_symm_apply (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι)
    (y : V.normOneVectors (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g)) :
    ((V.normOneVectorsEquiv γ g).symm y : ι → E) = (↑(γ : GL ι E)⁻¹ : Matrix ι ι E) *ᵥ y :=
  (rfl)

/-- The norm-one vectors of the lattice of `x_f⁻¹ γ x_f g` are the images under `γ` of those of
the lattice of `g`. -/
theorem normOneVectors_rationalEmbedding_mul (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι) :
    V.normOneVectors (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g) =
      ((↑(γ : GL ι E) : Matrix ι ι E) *ᵥ ·) '' V.normOneVectors g := by
  ext y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (V.normOneVectorsEquiv γ g).surjective ⟨y, hy⟩
    exact ⟨z, z.property, congrArg Subtype.val hz⟩
  · rintro ⟨y, hy, rfl⟩
    exact (V.mulVec_mem_normOneVectors_rationalEmbedding_mul_iff γ g y).2 hy

/-- The number of norm-one vectors does not change when `g` is moved on the left by the finite
component `x_f⁻¹ γ x_f` of a rational point. -/
@[simp]
theorem ncard_normOneVectors_rationalEmbedding_mul (γ : unitaryGroupOf V.gram)
    (g : finiteAdelicUnitaryGroup E ι) :
    (V.normOneVectors (adelicUnitaryGroup.finitePart E s (V.rationalEmbedding γ) * g)).ncard =
      (V.normOneVectors g).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (V.normOneVectorsEquiv γ g)).symm

/-- **Left invariance under `Γ_{V,f}`**: the number of norm-one vectors of the lattice of `g` does
not change when `g` is moved on the left by a finite rational point. -/
theorem ncard_normOneVectors_mul_of_mem_finiteRationalPoints {h : finiteAdelicUnitaryGroup E ι}
    (hh : h ∈ V.finiteRationalPoints) (g : finiteAdelicUnitaryGroup E ι) :
    (V.normOneVectors (h * g)).ncard = (V.normOneVectors g).ncard := by
  rw [finiteRationalPoints_def] at hh
  obtain ⟨γ, rfl⟩ := hh
  exact V.ncard_normOneVectors_rationalEmbedding_mul γ g

/-! ### Finiteness for definite spaces -/

/-- **Vectors of norm one in a definite space are bounded at the infinite places.** If all signs
of `V` are `+1`, there is `B` such that every `y ∈ E^n` with `h_J(y, y) = 1` has entries of norm
at most `B` at every infinite place: the archimedean frame `x_∞` carries `x_∞⁻¹ y` to `y`, and
`x_∞⁻¹ y` is a unit vector, as `x_∞* J x_∞ = 1`. -/
theorem exists_norm_le_of_star_dotProduct_gram_mulVec_eq_one
    (V : FramedHermitianSpace E (1 : ι → ℤˣ)) :
    ∃ B : ℝ, ∀ y : ι → E, star y ⬝ᵥ V.gram *ᵥ y = 1 → ∀ i (w : InfinitePlace E),
      ‖algebraMap E (InfiniteAdeleRing E) (y i) w‖ ≤ B := by
  let x : Matrix ι ι (InfiniteAdeleRing E) := V.frame.1
  refine ⟨∑ i, ∑ j, ∑ w, ‖x i j w‖, fun y hy i w ↦ ?_⟩
  let y' : ι → InfiniteAdeleRing E := algebraMap E (InfiniteAdeleRing E) ∘ y
  -- The coordinates `u = x_∞⁻¹ y` of `y` in the archimedean frame.
  let u : ι → InfiniteAdeleRing E := (↑V.frame.1⁻¹ : Matrix ι ι (InfiniteAdeleRing E)) *ᵥ y'
  have hyu : y' = x *ᵥ u := by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hframe : xᴴ * V.gram.map (algebraMap E (InfiniteAdeleRing E)) * x = 1 := by
    simpa [← star_eq_conjTranspose] using V.star_mul_gram_mul_fst
  have hy' : star y' ⬝ᵥ V.gram.map (algebraMap E (InfiniteAdeleRing E)) *ᵥ y' = 1 := by
    -- The image of `y* J y = 1` in `E_∞`: the diagonal embedding commutes with conjugation, and
    -- with the product by `J`.
    have h := congrArg (algebraMap E (InfiniteAdeleRing E)) hy
    rw [map_one, RingHom.map_dotProduct] at h
    convert h using 2
    · ext j
      simp [y']
    · ext j
      exact (RingHom.map_mulVec _ _ _ j).symm
  have hu : star u ⬝ᵥ u = 1 := by
    rwa [hyu, ← star_dotProduct_conjTranspose_mul_mul_mulVec, hframe, one_mulVec] at hy'
  have hu1 (j : ι) : ‖u j w‖ ≤ 1 :=
    InfiniteAdeleRing.norm_apply_le_one_of_star_dotProduct_self_eq_one hu j w
  -- Evaluation at `w`, a ring homomorphism on `E_∞ = ∏_v E_v`.
  let ev : InfiniteAdeleRing E →+* w.Completion := Pi.evalRingHom _ w
  have hev (a : InfiniteAdeleRing E) : ev a = a w := Pi.evalRingHom_apply _ _ _
  calc ‖y' i w‖ = ‖ev ((x *ᵥ u) i)‖ := by rw [hev, ← hyu]
    _ = ‖∑ j, ev (x i j) * ev (u j)‖ := by
        rw [mulVec_apply_eq_sum, map_sum]
        simp only [map_mul]
    _ ≤ ∑ j, ‖x i j w‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        rw [hev, hev]
        exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hu1 j))
    _ ≤ ∑ j, ∑ w, ‖x i j w‖ := Finset.sum_le_sum fun j _ ↦
        Finset.single_le_sum (fun w _ ↦ norm_nonneg (x i j w)) (Finset.mem_univ w)
    _ ≤ ∑ i, ∑ j, ∑ w, ‖x i j w‖ :=
        Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun j _ ↦
          Finset.sum_nonneg fun w _ ↦ norm_nonneg (x i j w)) (Finset.mem_univ i)

/-- **A definite space has finitely many norm-one vectors in each point lattice.** If all signs of
`V` are `+1`, the norm-one vectors of the lattice of every `g ∈ G_f` form a finite set: they are
bounded at the infinite places, and their finite parts lie in the compact lattice of `g`. -/
theorem finite_normOneVectors (V : FramedHermitianSpace E (1 : ι → ℤˣ))
    (g : finiteAdelicUnitaryGroup E ι) : (V.normOneVectors g).Finite := by
  obtain ⟨B, hB⟩ := V.exists_norm_le_of_star_dotProduct_gram_mulVec_eq_one
  have hball (w : InfinitePlace E) : IsCompact (Metric.closedBall (0 : w.Completion) B) :=
    haveI := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    isCompact_closedBall 0 B
  -- The adelic vectors whose infinite parts are bounded by `B` at every place and whose finite
  -- parts lie in the lattice of `g`: a compact set containing every norm-one vector.
  let S : Set (ι → 𝔸[E]) :=
    (fun p : (ι → InfiniteAdeleRing E) × (ι → 𝔸ᶠ[E]) ↦ fun i ↦ ((p.1 i, p.2 i) : 𝔸[E])) ''
      ((Set.univ.pi fun _ ↦ Set.univ.pi fun w ↦ Metric.closedBall 0 B) ×ˢ V.finiteLattice g)
  have hS : IsCompact S :=
    ((isCompact_univ_pi fun _ ↦ isCompact_univ_pi hball).prod
      (V.isCompact_finiteLattice g)).image (by fun_prop)
  refine (TauCeti.GlobalNumberFields.finite_setOf_comp_mem_of_isCompact hS).subset
    fun y hy ↦ ⟨(algebraMap E (InfiniteAdeleRing E) ∘ y, algebraMap E 𝔸ᶠ[E] ∘ y),
      ⟨fun i _ w _ ↦ ?_, hy.2⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hB y hy.1 i w
  · ext i : 1
    exact Prod.ext (AdeleRing.algebraMap_fst_def (𝓞 E) E _).symm
      (AdeleRing.algebraMap_snd_def (𝓞 E) E _).symm

instance (V : FramedHermitianSpace E (1 : ι → ℤˣ)) (g : finiteAdelicUnitaryGroup E ι) :
    Finite (V.normOneVectors g) :=
  (V.finite_normOneVectors g).to_subtype

end TauCeti.FramedHermitianSpace
