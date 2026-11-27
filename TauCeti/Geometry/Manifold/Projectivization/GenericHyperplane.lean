/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Geometry.Manifold.Measure.Differentiable
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.RegularValue.Polynomial
import TauCeti.Geometry.Manifold.Sard.Basic
import TauCeti.MeasureTheory.Measure.Haar.Differentiable

/-!
# Generic hyperplanes are transverse to a smooth projective zero locus

Let `X = complexProjectiveZeroLocus p ⊆ ℂℙⁿ` be the zero locus of a finite family `p` of homogeneous
polynomials whose cone Jacobian `J_p(L)` is onto at every point `L` of `X`, so that `X` is a smooth
complete intersection (`TauCeti.complexProjectiveZeroLocusChartedSpace`). A linear form
`ℓ : Fin (n + 1) → ℂ` cuts out the hyperplane `H_ℓ = {ℓ ⬝ᵥ v = 0}`, the zero locus of the linear
polynomial `(Matrix.replicateRow Unit ℓ).toMvPolynomial ()`, and the hyperplane section `X ∩ H_ℓ`
is the zero locus of the family `Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial`.

This file proves the hyperplane case of Bertini's theorem in the differential-topological form:
for almost every `ℓ`, this enlarged family again has onto cone Jacobian at every point of
`X ∩ H_ℓ`. So a generic hyperplane meets `X` transversally, and `X ∩ H_ℓ` is again a smooth
complete intersection: `TauCeti.complexProjectiveZeroLocusChartedSpace`, applied to the enlarged
family, makes it an embedded complex submanifold of `ℂℙⁿ` modelled on
`Fin (n - Fintype.card (ι ⊕ Unit)) → ℂ`. The exceptional linear forms are null in `ℂⁿ⁺¹` and also
in every standard affine chart of the dual projective space, and the transverse ones are dense.

The proof is a dimension count. At a point `L` of `X ∩ H_ℓ`, the enlarged Jacobian fails to be onto
exactly when `ℓ` is a combination `c ᵥ* J_p(L)` of the gradients of the equations, that is, when
`ℓ` vanishes on the kernel of `J_p(L)`, the tangent space of the affine cone over `X`
(`TauCeti.mulVec_surjective_jacobiMatrixAt_sumElim_toMvPolynomial_iff`). The bad forms therefore
lie in the union of these spaces of combinations over `L ∈ X`, the cone over the dual variety. In
the standard affine chart `i`, it is the image of the map `(a, c) ↦ c ᵥ* J_p(insertNth i 1 a)` on
the product of the affine zero locus of the dehomogenized equations, a complex manifold of
dimension `n - |ι|`, with `ℂ^ι`. This product has real dimension `2n < 2n + 2`, so its image is
null by the lower-dimensional case of Sard's theorem
(`TauCeti.isNullSet_image_of_finrank_lt_finrank`).
Transversality is invariant under rescaling `ℓ`, so reading the null set of linear forms through
the scaling map `(t, a) ↦ t • insertNth i 1 a` gives the null exceptional set in each chart.

## Main results

* `TauCeti.forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_iff`: `H_ℓ` is transverse to `X`
  exactly when `ℓ` is not a combination of the gradients of the equations at any point of
  `X ∩ H_ℓ`.
* `TauCeti.volume_setOf_exists_mem_complexProjectiveZeroLocus_mem_range_vecMul_eq_zero`: the
  linear forms that are combinations of the gradients at some point of `X` form a null set.
* `TauCeti.ae_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim`:
  almost every hyperplane is transverse to `X`.
* `TauCeti.ae_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_insertNth`:
  the same in every standard affine chart `a ↦ [insertNth i 1 a]` of the dual projective space.
* `TauCeti.dense_setOf_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim`:
  the transverse linear forms are dense.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1,
  Section 1 (Bertini's theorem).
* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  Chapter 3, for Sard's theorem when the source has smaller dimension.
-/

public section

open Function MeasureTheory MvPolynomial Set
open scoped LinearAlgebra.Projectivization Manifold ContDiff Matrix

namespace TauCeti

variable {n : ℕ} {ι : Type*} {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}

/-- In the standard affine chart `i`, the cone Jacobian of a smooth projective zero locus is onto
at the chart representative `insertNth i 1 a` of each point. -/
private theorem mulVec_surjective_jacobiMatrixAt_insertNth (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective)
    (i : Fin (n + 1)) {a : Fin n → ℂ} (ha : a ∈ affineZeroLocus fun k ↦ dehomogenize i (p k)) :
    (jacobiMatrixAt p (i.insertNth 1 a)).mulVec.Surjective := by
  have hmem : Projectivization.mk ℂ _ (Fin.insertNth_one_ne_zero i a) ∈
      complexProjectiveZeroLocus p :=
    (complexProjectiveZeroLocus_mk_insertNth_iff hp i a).2 (mem_affineZeroLocus.1 ha)
  exact (mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk hp (Projectivization.rep_ne_zero _)
    (Fin.insertNth_one_ne_zero i a) (Projectivization.mk_rep _)).1 (hrank _ hmem)

/-- The combinations `c ᵥ* J_p(insertNth i 1 a)` of the gradients depend holomorphically on the
chart coordinate `a` and the coefficients `c`. -/
private theorem differentiable_vecMul_jacobiMatrixAt_insertNth [Fintype ι]
    (p : ι → MvPolynomial (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    Differentiable ℂ fun x : (Fin n → ℂ) × (ι → ℂ) ↦
      x.2 ᵥ* jacobiMatrixAt p (i.insertNth 1 x.1) := by
  obtain ⟨G, hGdef⟩ : ∃ G : (Fin n → ℂ) → ι × Fin (n + 1) → ℂ,
      G = fun a mj ↦ eval a (dehomogenize i (pderiv mj.2 (p mj.1))) := ⟨_, rfl⟩
  have hG : Differentiable ℂ G :=
    hGdef ▸ fun a ↦ ((analyticOnNhd_eval_family _) a (mem_univ a)).differentiableAt
  have hF : (fun x : (Fin n → ℂ) × (ι → ℂ) ↦ x.2 ᵥ* jacobiMatrixAt p (i.insertNth 1 x.1)) =
      fun x j ↦ ∑ m, x.2 m * G x.1 (m, j) := by
    ext x j
    simp [hGdef, Matrix.vecMul, dotProduct, eval_dehomogenize]
  rw [hF]
  fun_prop

/-- In the standard affine chart `i`, the combinations of the gradients of the equations at the
points of `X` form a null set: they are the image of the product of the affine zero locus, of real
dimension `2 (n - |ι|)`, with `ℂ^ι`, a manifold of real dimension `2n < 2n + 2`. -/
private theorem volume_setOf_exists_vecMul_jacobiMatrixAt_insertNth_eq_zero [Fintype ι]
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective)
    (i : Fin (n + 1)) :
    volume {ℓ : Fin (n + 1) → ℂ | ∃ a ∈ affineZeroLocus fun k ↦ dehomogenize i (p k),
      ∃ c : ι → ℂ, c ᵥ* jacobiMatrixAt p (i.insertNth 1 a) = ℓ} = 0 := by
  set Z := affineZeroLocus fun k ↦ dehomogenize i (p k)
  have hsurj (a : Fin n → ℂ) (ha : a ∈ Z) :=
    mulVec_surjective_jacobiMatrixAt_insertNth hp hrank i ha
  have hZ : ∀ a ∈ Z, (jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) a).mulVec.Surjective := by
    intro a ha
    rw [Matrix.mulVec_surjective_iff_rank_eq_card,
      rank_jacobiMatrixAt_dehomogenize i hp (mem_affineZeroLocus.1 ha),
      ← Matrix.mulVec_surjective_iff_rank_eq_card]
    exact hsurj a ha
  rcases Z.eq_empty_or_nonempty with hZe | ⟨a₀, ha₀⟩
  · simp [hZe]
  -- A nonempty smooth zero locus has fewer equations than variables.
  have hcard : Fintype.card ι ≤ n := by
    have := card_lt_card_of_mulVec_surjective_jacobiMatrixAt hp (Fin.insertNth_one_ne_zero i a₀)
      (fun k ↦ by rw [← eval_dehomogenize]; exact mem_affineZeroLocus.1 ha₀ k) (hsurj a₀ ha₀)
    simpa [Nat.lt_succ_iff] using this
  let := affineZeroLocusChartedSpace hZ
  have := isManifold_affineZeroLocus hZ ∞
  have : IsManifold 𝓘(ℝ, Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ) 1 Z :=
    (isManifold_affineZeroLocus hZ 1).restrictScalars ℝ
  have hf : MDifferentiable ((𝓘(ℂ, Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ)).prod
      𝓘(ℂ, ι → ℂ)) 𝓘(ℂ, Fin (n + 1) → ℂ)
      fun x : Z × (ι → ℂ) ↦ x.2 ᵥ* jacobiMatrixAt p (i.insertNth 1 (x.1 : Fin n → ℂ)) := by
    refine (differentiable_vecMul_jacobiMatrixAt_insertNth p i).comp_mdifferentiable
      (f := fun x : Z × (ι → ℂ) ↦ ((x.1 : Fin n → ℂ), x.2)) ?_
    rw [mdifferentiable_prod_module_iff]
    exact ⟨((contMDiff_coe_affineZeroLocus hZ ∞).mdifferentiable (by simp)).comp
      mdifferentiable_fst, mdifferentiable_snd⟩
  have hfR := hf.restrictScalars ℝ
  simp only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] at hfR
  have hdim : Module.finrank ℝ ((Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ) × (ι → ℂ)) <
      Module.finrank ℝ (Fin (n + 1) → ℂ) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hnull := isNullSet_image_of_finrank_lt_finrank hdim fun x (_ : x ∈ univ) ↦ hfR x
  rw [isNullSet_modelWithCornersSelf_iff volume] at hnull
  refine measure_mono_null ?_ hnull
  rintro _ ⟨a, ha, c, rfl⟩
  exact ⟨(⟨a, ha⟩, c), mem_univ _, rfl⟩

/-- **Transversality of a hyperplane section.** On a smooth projective zero locus `X`, the
hyperplane `ℓ = 0` is transverse at every point of `X ∩ {ℓ = 0}` exactly when, at no point of `X`
on the hyperplane, `ℓ` is a combination of the gradients of the equations of `X`. -/
theorem forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_iff [Fintype ι]
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective)
    (ℓ : Fin (n + 1) → ℂ) :
    (∀ L ∈ complexProjectiveZeroLocus (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial),
      (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial)
        L.rep).mulVec.Surjective) ↔
      ∀ L ∈ complexProjectiveZeroLocus p, ℓ ⬝ᵥ L.rep = 0 →
        ℓ ∉ range (· ᵥ* jacobiMatrixAt p L.rep) := by
  simp only [complexProjectiveZeroLocus_sumElim, mem_inter_iff,
    mem_complexProjectiveZeroLocus_replicateRow_toMvPolynomial_iff, and_imp]
  exact forall₂_congr fun L hL ↦ imp_congr_right fun _ ↦
    mulVec_surjective_jacobiMatrixAt_sumElim_toMvPolynomial_iff (hrank L hL) ℓ

/-- Transversality of the hyperplane `ℓ = 0` to a smooth projective zero locus depends only on
the hyperplane, not on the nonzero multiple of `ℓ` cutting it out. -/
theorem forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff [Finite ι]
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective)
    {t : ℂ} (ht : t ≠ 0) (ℓ : Fin (n + 1) → ℂ) :
    (∀ L ∈ complexProjectiveZeroLocus
        (Sum.elim p (Matrix.replicateRow Unit (t • ℓ)).toMvPolynomial),
      (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit (t • ℓ)).toMvPolynomial)
        L.rep).mulVec.Surjective) ↔
      ∀ L ∈ complexProjectiveZeroLocus (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial),
        (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial)
          L.rep).mulVec.Surjective := by
  have := Fintype.ofFinite ι
  rw [forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_iff hrank,
    forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_iff hrank]
  refine forall₂_congr fun L _ ↦ ?_
  have hrange : t • ℓ ∈ range (· ᵥ* jacobiMatrixAt p L.rep) ↔
      ℓ ∈ range (· ᵥ* jacobiMatrixAt p L.rep) := by
    refine ⟨fun ⟨c, hc⟩ ↦ ⟨t⁻¹ • c, ?_⟩, fun ⟨c, hc⟩ ↦ ⟨t • c, ?_⟩⟩
    · simp only [Matrix.smul_vecMul, hc, smul_smul, inv_mul_cancel₀ ht, one_smul]
    · simp only [Matrix.smul_vecMul, hc]
  rw [smul_dotProduct, smul_eq_mul, mul_eq_zero, or_iff_right ht, hrange]

/-- **The cone over the dual variety is null.** For a smooth projective zero locus `X` of a family
`p` of homogeneous polynomials, the linear forms `ℓ` that are combinations of the gradients of the
equations at some point of `X`, that is, that vanish on the tangent space of the affine cone over
`X` there, form a Lebesgue-null subset of `ℂⁿ⁺¹`.

Apart from `0`, these are the linear forms whose hyperplane `ℓ = 0` is tangent to `X` somewhere. -/
theorem volume_setOf_exists_mem_complexProjectiveZeroLocus_mem_range_vecMul_eq_zero [Fintype ι]
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective) :
    volume {ℓ : Fin (n + 1) → ℂ | ∃ L ∈ complexProjectiveZeroLocus p,
      ℓ ∈ range (· ᵥ* jacobiMatrixAt p L.rep)} = 0 := by
  classical
  refine measure_mono_null (fun ℓ ⟨L, hL, c, hc⟩ ↦ ?_) (measure_iUnion_null fun i ↦
    volume_setOf_exists_vecMul_jacobiMatrixAt_insertNth_eq_zero hp hrank i)
  obtain ⟨i, hi⟩ := Projectivization.exists_mem_affineOpen L
  have hmk : Projectivization.mk ℂ L.rep L.rep_ne_zero = Projectivization.mk ℂ
      (i.insertNth 1 (Projectivization.affineChart i L)) (Fin.insertNth_one_ne_zero i _) := by
    rw [Projectivization.mk_rep, ← Projectivization.affineChart_symm_apply (K := ℂ),
      (Projectivization.affineChart i).left_inv
        ((Projectivization.affineChart_source (K := ℂ) i).symm ▸ hi)]
  -- `L.rep` is a rescaling of the chart representative, which rescales the rows of the Jacobian.
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hmk
  refine mem_iUnion.2 ⟨i, _, mem_affineZeroLocus.2
    ((mem_complexProjectiveZeroLocus_iff_eval_affineChart hp hi).1 hL),
    c ᵥ* Matrix.diagonal fun k ↦ t ^ (d k - 1), ?_⟩
  rw [← hc, ← ht, jacobiMatrixAt_smul hp, Matrix.vecMul_vecMul]

/-- **Generic hyperplanes are transverse to a smooth projective zero locus.** Let `X` be the
projective zero locus of a family `p` of homogeneous polynomials whose cone Jacobian is onto at
every point of `X`. For almost every linear form `ℓ`, the hyperplane section `X ∩ {ℓ = 0}`, cut out
by `p` together with `ℓ`, again has onto cone Jacobian at each of its points: the hyperplane meets
`X` transversally, and the section is a smooth complete intersection of one more equation. -/
theorem ae_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim [Finite ι]
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective) :
    ∀ᵐ ℓ : Fin (n + 1) → ℂ,
      ∀ L ∈ complexProjectiveZeroLocus (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial),
        (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial)
          L.rep).mulVec.Surjective := by
  have := Fintype.ofFinite ι
  rw [ae_iff]
  refine measure_mono_null (fun ℓ hℓ ↦ ?_)
    (volume_setOf_exists_mem_complexProjectiveZeroLocus_mem_range_vecMul_eq_zero hp hrank)
  rw [mem_ofPred_eq, forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_iff hrank] at hℓ
  push Not at hℓ
  obtain ⟨L, hL, -, hmem⟩ := hℓ
  exact ⟨L, hL, hmem⟩

/-- **Generic hyperplanes in a chart of the dual projective space.** In the standard affine chart
`a ↦ [insertNth i 1 a]` of the dual projective space, the hyperplanes that are not transverse to a
smooth projective zero locus form a null set of chart coordinates. -/
theorem ae_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_insertNth [Finite ι]
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective)
    (i : Fin (n + 1)) :
    ∀ᵐ a : Fin n → ℂ, ∀ L ∈ complexProjectiveZeroLocus
        (Sum.elim p (Matrix.replicateRow Unit (i.insertNth 1 a)).toMvPolynomial),
      (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit (i.insertNth 1 a)).toMvPolynomial)
        L.rep).mulVec.Surjective := by
  set P : (Fin (n + 1) → ℂ) → Prop := fun ℓ ↦
    ∀ L ∈ complexProjectiveZeroLocus (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial),
      (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial)
        L.rep).mulVec.Surjective
  have hB : volume {ℓ | ¬P ℓ} = 0 :=
    ae_iff.1 (ae_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim
      hp hrank)
  rw [ae_iff]
  -- Read off the chart coordinates and the scale of a linear form with nonzero `i`-th entry.
  let h : (Fin (n + 1) → ℂ) → ℂ × (Fin n → ℂ) := fun v ↦ (v i, fun j ↦ v (i.succAbove j) / v i)
  have hh : DifferentiableOn ℝ h {v | v i ≠ 0} := by
    refine DifferentiableOn.restrictScalars ℝ (𝕜' := ℂ) fun v (hv : v i ≠ 0) ↦ ?_
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hv)
  -- A bad chart point `a`, scaled by any `t ≠ 0`, is a bad linear form with coordinates `(t, a)`.
  have hsub : ({0}ᶜ : Set ℂ) ×ˢ {a : Fin n → ℂ | ¬P (i.insertNth 1 a)} ⊆
      h '' ({ℓ | ¬P ℓ} ∩ {v | v i ≠ 0}) := by
    rintro ⟨t, a⟩ ⟨ht, ha⟩
    refine ⟨t • i.insertNth 1 a, ⟨?_, by simpa using ht⟩, ?_⟩
    · simpa only [mem_ofPred_eq, P,
        forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff hrank ht] using ha
    · ext j <;> simp [h, mul_div_cancel_left₀ _ (show t ≠ 0 from ht)]
  have hdim : Module.finrank ℝ (Fin (n + 1) → ℂ) ≤ Module.finrank ℝ (ℂ × (Fin n → ℂ)) := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]
    omega
  have : (volume.prod volume : Measure (ℂ × (Fin n → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h0 := measure_mono_null hsub (DifferentiableOn.addHaar_image_eq_zero volume
    (volume.prod volume) hdim (hh.mono inter_subset_right)
    (measure_mono_null inter_subset_left hB))
  rw [Measure.prod_prod, mul_eq_zero] at h0
  exact h0.resolve_left (isOpen_compl_singleton.measure_ne_zero volume ⟨1, one_ne_zero⟩)

/-- The linear forms whose hyperplanes are transverse to a smooth projective zero locus are
dense. -/
theorem dense_setOf_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim [Finite ι]
    (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hrank : ∀ L ∈ complexProjectiveZeroLocus p, (jacobiMatrixAt p L.rep).mulVec.Surjective) :
    Dense {ℓ : Fin (n + 1) → ℂ | ∀ L ∈ complexProjectiveZeroLocus
        (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial),
      (jacobiMatrixAt (Sum.elim p (Matrix.replicateRow Unit ℓ).toMvPolynomial)
        L.rep).mulVec.Surjective} :=
  Measure.dense_of_ae (ae_forall_mem_mulVec_surjective_jacobiMatrixAt_sumElim hp hrank)

end TauCeti
