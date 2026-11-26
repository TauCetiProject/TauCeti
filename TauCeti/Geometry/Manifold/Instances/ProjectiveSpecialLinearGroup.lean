/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.Projectivization
public import TauCeti.Topology.Algebra.Projectivization
import TauCeti.Analysis.Calculus.ContDiff.Matrix
import TauCeti.Geometry.Lie.RestrictScalars

/-!
# The complex Lie group `PSL(n, ℂ)`

The projective special linear group `PSL(n, ℂ) = SL(n, ℂ) ⧸ Z(SL(n, ℂ))` is an open subset of the
projective space of `n × n` matrices: the class of `A` is sent to the line of `A`, and this map
`Matrix.ProjectiveSpecialLinearGroup.toProjectivization` is an open embedding
(`Matrix.ProjectiveSpecialLinearGroup.isOpenEmbedding_toProjectivization`). For `n = 2` its image
is the complement of the determinant quadric in `ℂℙ³`. This file gives `PSL(n, ℂ)` the complex
analytic structure of this open subset and shows that it is a complex analytic Lie group.

Listing the entries of a matrix along an enumeration of `n × n`
(`Matrix.ProjectiveSpecialLinearGroup.entryEquiv`) identifies the matrices with
`ℂ^(card n * card n)` (`Matrix.ProjectiveSpecialLinearGroup.flattenEquiv`), and hence their
projective space with the standard complex projective space, which is an analytic manifold
(`Projectivization.instIsManifold`). The composite

`Matrix.ProjectiveSpecialLinearGroup.toProjectiveSpace : PSL(n, ℂ) → ℙ ℂ (Fin (N + 1) → ℂ)`,

with `N + 1 = card n * card n`, is an open embedding, and the charts of `PSL(n, ℂ)` are pulled
back along it (`Matrix.ProjectiveSpecialLinearGroup.instChartedSpace`). They are modelled on
`Matrix.SpecialLinearGroup.Model n ℂ = ℂ^(card n * card n - 1)`, the model of `SL(n, ℂ)`, and the
embedding is an analytic local diffeomorphism. So a map into `PSL(n, ℂ)` is analytic exactly when
it is continuous and its composite with the embedding is
(`Matrix.ProjectiveSpecialLinearGroup.contMDiff_iff_contMDiff_toProjectiveSpace_comp`).

The group operations are analytic. Near a pair of points, the lines of their matrices have
analytic homogeneous coordinates, normalized to `1` in a fixed standard affine chart
(`Projectivization.contMDiffOn_insertNth_affineChart`). Products and inverses can be computed on
any representing matrices
(`Matrix.ProjectiveSpecialLinearGroup.toProjectivization_mul_of_eq_mk` and
`Matrix.ProjectiveSpecialLinearGroup.toProjectivization_inv_of_eq_mk`), the inverse through the
adjugate, whose entries are polynomials. So the line of a product or an inverse has analytic
homogeneous coordinates near every point, and it depends analytically on the factors
(`Projectivization.contMDiffAt_of_eventually_eq_mk`). Hence `PSL(n, ℂ)` is a complex analytic Lie
group (`Matrix.ProjectiveSpecialLinearGroup.instLieGroup`), and so a real analytic one on the same
charts. The projection `SL(n, ℂ) → PSL(n, ℂ)` is analytic for the analytic structure of
`SL(n, ℂ)` as a level set of the determinant
(`Matrix.ProjectiveSpecialLinearGroup.contMDiff_mk`).

For `n = 2` this is the complex structure on the group of Möbius transformations of the Riemann
sphere, with respect to which their action on the sphere is holomorphic and the orbit map of an
ordered triple of distinct points is a biholomorphism.

## Main declarations

* `Matrix.ProjectiveSpecialLinearGroup.toProjectiveSpace`: the open embedding of `PSL(n, ℂ)` into
  `ℙ ℂ (Fin (N + 1) → ℂ)`.
* `Matrix.ProjectiveSpecialLinearGroup.instChartedSpace`,
  `Matrix.ProjectiveSpecialLinearGroup.instIsManifold`: the analytic manifold structure.
* `Matrix.ProjectiveSpecialLinearGroup.isLocalDiffeomorph_toProjectiveSpace`: the embedding is an
  analytic local diffeomorphism.
* `Matrix.ProjectiveSpecialLinearGroup.contMDiff_iff_contMDiff_toProjectiveSpace_comp`: maps into
  `PSL(n, ℂ)` are analytic exactly when their composites with the embedding are.
* `Matrix.ProjectiveSpecialLinearGroup.instLieGroup`,
  `Matrix.ProjectiveSpecialLinearGroup.instRealLieGroup`: the complex and real analytic Lie group
  structures.
* `Matrix.ProjectiveSpecialLinearGroup.contMDiff_mk`: the projection from `SL(n, ℂ)` is analytic.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1 (complex
  projective space and its affine charts).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the Möbius transformations of the Riemann sphere).
-/

public noncomputable section

open Set Filter Topology Projectivization
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Matrix.ProjectiveSpecialLinearGroup

variable {n : Type*} [Fintype n] [Nonempty n]

/-! ### The embedding into projective space -/

variable (n) in
/-- An enumeration of the entries of `n × n` matrices by `Fin (card n * card n - 1 + 1)`. -/
def entryEquiv : n × n ≃ Fin (Fintype.card n * Fintype.card n - 1 + 1) :=
  Fintype.equivFinOfCardEq <| by
    have : 0 < Fintype.card n * Fintype.card n := Nat.mul_pos Fintype.card_pos Fintype.card_pos
    rw [Fintype.card_prod]
    omega

variable (n) in
/-- The entries of an `n × n` complex matrix, listed along `entryEquiv n`. -/
def flattenEquiv : Matrix n n ℂ ≃L[ℂ] Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun A k ↦ A ((entryEquiv n).symm k).1 ((entryEquiv n).symm k).2
      invFun := fun v ↦ Matrix.of fun i j ↦ v (entryEquiv n (i, j))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun A ↦ by ext i j; simp
      right_inv := fun v ↦ by ext k; simp }

@[simp]
theorem flattenEquiv_apply (A : Matrix n n ℂ) (k : Fin (Fintype.card n * Fintype.card n - 1 + 1)) :
    flattenEquiv n A k = A ((entryEquiv n).symm k).1 ((entryEquiv n).symm k).2 :=
  (rfl)

@[simp]
theorem flattenEquiv_symm_apply (v : Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ) (i j : n) :
    (flattenEquiv n).symm v i j = v (entryEquiv n (i, j)) :=
  (rfl)

variable [DecidableEq n]

variable (n) in
/-- The embedding of `PSL(n, ℂ)` into the standard complex projective space of dimension
`card n * card n - 1`: the line of a representing matrix, with its entries listed along
`entryEquiv n`. -/
def toProjectiveSpace :
    ProjectiveSpecialLinearGroup n ℂ → ℙ ℂ (Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ) :=
  (flattenEquiv n).mapProjectivization ∘ toProjectivization n ℂ

@[simp]
theorem toProjectiveSpace_mk (A : SpecialLinearGroup n ℂ) :
    toProjectiveSpace n A =
      .mk ℂ (flattenEquiv n A) ((LinearEquiv.map_ne_zero_iff _).2 A.coe_ne_zero) := by
  simp [toProjectiveSpace, ContinuousLinearEquiv.mapProjectivization_mk]

/-- The embedding of `PSL(n, ℂ)` into projective space is an open embedding. -/
theorem isOpenEmbedding_toProjectiveSpace : IsOpenEmbedding (toProjectiveSpace n) :=
  (flattenEquiv n).mapProjectivization.isOpenEmbedding.comp isOpenEmbedding_toProjectivization

/-- Reading the homogeneous coordinates of `toProjectiveSpace n g` as a matrix gives homogeneous
coordinates of `toProjectivization n ℂ g`. -/
theorem toProjectivization_eq_mk_of_toProjectiveSpace_eq_mk {g : ProjectiveSpecialLinearGroup n ℂ}
    {v : Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ} {hv : v ≠ 0}
    (h : toProjectiveSpace n g = .mk ℂ v hv) :
    toProjectivization n ℂ g =
      .mk ℂ ((flattenEquiv n).symm v) ((LinearEquiv.map_ne_zero_iff _).2 hv) := by
  apply (flattenEquiv n).mapProjectivization.injective
  simp only [ContinuousLinearEquiv.mapProjectivization_mk, ContinuousLinearEquiv.apply_symm_apply]
  exact h

/-! ### The analytic structure -/

/-- The analytic charts of `PSL(n, ℂ)`, pulled back from the projective space of matrices along
the open embedding `toProjectiveSpace n`. -/
@[instance_reducible]
instance instChartedSpace :
    ChartedSpace (SpecialLinearGroup.Model n ℂ) (ProjectiveSpecialLinearGroup n ℂ) :=
  (isOpenEmbedding_toProjectiveSpace (n := n)).isLocalHomeomorph.chartedSpaceComap

/-- `PSL(n, ℂ)` is a complex analytic manifold. -/
instance instIsManifold (r : ℕ∞ω) :
    IsManifold 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) r (ProjectiveSpecialLinearGroup n ℂ) :=
  (isOpenEmbedding_toProjectiveSpace (n := n)).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The embedding of `PSL(n, ℂ)` into projective space is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorph_toProjectiveSpace (r : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) r
      (toProjectiveSpace n) :=
  (isOpenEmbedding_toProjectiveSpace (n := n)).isLocalHomeomorph
    |>.isLocalDiffeomorph_chartedSpaceComap

/-- The embedding of `PSL(n, ℂ)` into projective space is analytic. -/
theorem contMDiff_toProjectiveSpace (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) r
      (toProjectiveSpace n) :=
  (isOpenEmbedding_toProjectiveSpace (n := n)).isLocalHomeomorph.contMDiff_chartedSpaceComap

/-- A map into `PSL(n, ℂ)` is `C^r` exactly when it is continuous and its composite with the
embedding into projective space is `C^r`. -/
theorem contMDiff_iff_contMDiff_toProjectiveSpace_comp {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [TopologicalSpace M]
    [ChartedSpace H M] {r : ℕ∞ω} {f : M → ProjectiveSpecialLinearGroup n ℂ} :
    ContMDiff I 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) r f ↔
      Continuous f ∧ ContMDiff I 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) r (toProjectiveSpace n ∘ f) :=
  (isOpenEmbedding_toProjectiveSpace (n := n)).isLocalHomeomorph.contMDiff_chartedSpaceComap_iff

/-! ### The group operations are analytic -/

/-- Near a point of `PSL(n, ℂ)` whose line lies in the standard affine chart at `i`, the
homogeneous coordinates of the line normalized to `1` at `i`, read as a matrix, represent the
point and depend analytically on it. -/
private theorem exists_contMDiffAt_lift (g₀ : ProjectiveSpecialLinearGroup n ℂ) :
    ∃ L : ProjectiveSpecialLinearGroup n ℂ → Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ,
      ContMDiffAt 𝓘(ℂ, SpecialLinearGroup.Model n ℂ)
        𝓘(ℂ, Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ) ω L g₀ ∧
      ∀ᶠ g in 𝓝 g₀, ∃ hL : L g ≠ 0, toProjectiveSpace n g = .mk ℂ (L g) hL := by
  obtain ⟨i, hi⟩ := exists_mem_affineOpen (toProjectiveSpace n g₀)
  have hU : toProjectiveSpace n ⁻¹' affineOpen i ∈ 𝓝 g₀ :=
    ((isOpen_affineOpen i).preimage
      (isOpenEmbedding_toProjectiveSpace (n := n)).continuous).mem_nhds hi
  refine ⟨fun g ↦ Fin.insertNth i 1 (affineChart i (toProjectiveSpace n g)), ?_, ?_⟩
  · exact ((contMDiffOn_insertNth_affineChart i ω).contMDiffAt
      ((isOpen_affineOpen i).mem_nhds hi)).comp g₀ (contMDiff_toProjectiveSpace ω).contMDiffAt
  · filter_upwards [hU] with g hg
    refine ⟨Fin.insertNth_one_ne_zero i _, ?_⟩
    rw [← affineChart_symm_apply, (affineChart i).left_inv (by rwa [affineChart_source])]

omit [DecidableEq n] in
/-- The entries of the product of two matrices are polynomials in their entries. -/
private theorem contDiff_flattenEquiv_mul :
    ContDiff ℂ ω fun p : (Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ) ×
        (Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ) ↦
      flattenEquiv n ((flattenEquiv n).symm p.1 * (flattenEquiv n).symm p.2) := by
  refine contDiff_pi.2 fun k ↦ ?_
  simp only [flattenEquiv_apply, Matrix.mul_apply, flattenEquiv_symm_apply]
  fun_prop

/-- The entries of the adjugate of a matrix are polynomials in its entries. -/
private theorem contDiff_flattenEquiv_adjugate :
    ContDiff ℂ ω fun v : Fin (Fintype.card n * Fintype.card n - 1 + 1) → ℂ ↦
      flattenEquiv n ((flattenEquiv n).symm v).adjugate := by
  refine contDiff_pi.2 fun k ↦ ?_
  simp only [flattenEquiv_apply, adjugate_apply]
  refine ContDiff.matrix_det fun i j ↦ ?_
  simp only [updateRow_apply, flattenEquiv_symm_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_apply ℂ (fun _ ↦ ℂ) _

/-- Multiplication on `PSL(n, ℂ)` is analytic. -/
private theorem contMDiff_mul_aux :
    ContMDiff (𝓘(ℂ, SpecialLinearGroup.Model n ℂ).prod 𝓘(ℂ, SpecialLinearGroup.Model n ℂ))
      𝓘(ℂ, SpecialLinearGroup.Model n ℂ) ω
      fun p : ProjectiveSpecialLinearGroup n ℂ × ProjectiveSpecialLinearGroup n ℂ ↦ p.1 * p.2 := by
  refine contMDiff_iff_contMDiff_toProjectiveSpace_comp.2 ⟨continuous_mul, fun p ↦ ?_⟩
  obtain ⟨L₁, hL₁, hev₁⟩ := exists_contMDiffAt_lift (n := n) p.1
  obtain ⟨L₂, hL₂, hev₂⟩ := exists_contMDiffAt_lift (n := n) p.2
  refine contMDiffAt_of_eventually_eq_mk
    (F := fun q : ProjectiveSpecialLinearGroup n ℂ × ProjectiveSpecialLinearGroup n ℂ ↦
      flattenEquiv n ((flattenEquiv n).symm (L₁ q.1) * (flattenEquiv n).symm (L₂ q.2)))
    (contDiff_flattenEquiv_mul.contMDiff.contMDiffAt.comp p
      ((hL₁.comp p contMDiffAt_fst).prodMk_space (hL₂.comp p contMDiffAt_snd))) ?_
  filter_upwards [continuousAt_fst.eventually hev₁, continuousAt_snd.eventually hev₂] with q hq₁ hq₂
  obtain ⟨_, hq₁⟩ := hq₁
  obtain ⟨_, hq₂⟩ := hq₂
  obtain ⟨hAB, hmul⟩ := toProjectivization_mul_of_eq_mk
    (toProjectivization_eq_mk_of_toProjectiveSpace_eq_mk hq₁)
    (toProjectivization_eq_mk_of_toProjectiveSpace_eq_mk hq₂)
  refine ⟨(LinearEquiv.map_ne_zero_iff _).2 hAB, ?_⟩
  simp only [Function.comp_apply, toProjectiveSpace, hmul,
    ContinuousLinearEquiv.mapProjectivization_mk]

/-- Inversion on `PSL(n, ℂ)` is analytic. -/
private theorem contMDiff_inv_aux :
    ContMDiff 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) ω
      fun g : ProjectiveSpecialLinearGroup n ℂ ↦ g⁻¹ := by
  refine contMDiff_iff_contMDiff_toProjectiveSpace_comp.2 ⟨continuous_inv, fun g ↦ ?_⟩
  obtain ⟨L, hL, hev⟩ := exists_contMDiffAt_lift (n := n) g
  refine contMDiffAt_of_eventually_eq_mk
    (F := fun h ↦ flattenEquiv n ((flattenEquiv n).symm (L h)).adjugate)
    (contDiff_flattenEquiv_adjugate.contMDiff.contMDiffAt.comp g hL) ?_
  filter_upwards [hev] with h hh
  obtain ⟨_, hh⟩ := hh
  obtain ⟨hA, hinv⟩ :=
    toProjectivization_inv_of_eq_mk (toProjectivization_eq_mk_of_toProjectiveSpace_eq_mk hh)
  refine ⟨(LinearEquiv.map_ne_zero_iff _).2 hA, ?_⟩
  simp only [Function.comp_apply, toProjectiveSpace, hinv,
    ContinuousLinearEquiv.mapProjectivization_mk]

/-- `PSL(n, ℂ)` is a complex analytic Lie group. -/
instance instLieGroup :
    LieGroup 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) ω (ProjectiveSpecialLinearGroup n ℂ) where
  contMDiff_mul := contMDiff_mul_aux
  contMDiff_inv := contMDiff_inv_aux

/-- `PSL(n, ℂ)` is a real analytic Lie group on the same charts. -/
instance (priority := 100) instRealLieGroup :
    LieGroup 𝓘(ℝ, SpecialLinearGroup.Model n ℂ) ω (ProjectiveSpecialLinearGroup n ℂ) :=
  LieGroup.restrictScalars_self ℝ (𝕜 := ℂ)

/-! ### The projection from `SL(n, ℂ)` -/

open scoped Matrix.Norms.Operator in
attribute [local instance] Matrix.linftyOpTopologicalSpace in
/-- The projection `SL(n, ℂ) → PSL(n, ℂ)` is analytic, for the analytic structure of `SL(n, ℂ)` as
a level set of the determinant. -/
theorem contMDiff_mk (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) 𝓘(ℂ, SpecialLinearGroup.Model n ℂ) r
      (QuotientGroup.mk : SpecialLinearGroup n ℂ → ProjectiveSpecialLinearGroup n ℂ) := by
  refine contMDiff_iff_contMDiff_toProjectiveSpace_comp.2
    ⟨QuotientGroup.continuous_mk, fun A ↦ ?_⟩
  refine contMDiffAt_of_eventually_eq_mk (F := fun B : SpecialLinearGroup n ℂ ↦ flattenEquiv n B) ?_
    (.of_forall fun B ↦ ⟨_, toProjectiveSpace_mk B⟩)
  -- Each homogeneous coordinate is an entry of the matrix.
  refine contMDiffAt_pi_module_iff.2 fun k ↦ ?_
  exact ((entryLinearMap ℂ ℂ ((entryEquiv n).symm k).1
    ((entryEquiv n).symm k).2).toContinuousLinearMap.contMDiff.comp
      SpecialLinearGroup.contMDiff_subtypeVal).contMDiffAt

end Matrix.ProjectiveSpecialLinearGroup
