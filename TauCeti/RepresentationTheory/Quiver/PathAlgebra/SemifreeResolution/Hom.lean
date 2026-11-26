/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.EnvelopeAction
public import TauCeti.Algebra.Homology.DG.Bimodule.Hom.Complex
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.DGBimodule

/-!
# Cochains out of the small resolution of a DG path algebra

Let `(kQ, d)` be a differential graded path algebra, graded by an integer weight `wt` on the
arrows, whose differential kills the vertex idempotents, and let `N` be a DG `kQ`-bimodule. The
small resolution of `kQ` (`TauCeti.PathAlgebra.standardDGBimoduleResolution`) is the cone of the
boundary from the arrow term `⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ kQ` to the vertex term
`kQ ⊗_{kQ₀} kQ`. Both terms are free on explicit generators: `∑ᵥ eᵥ ⊗ eᵥ` in degree zero, and the
universal derivative `∂b` of each arrow `b` in degree `wt b`. This file computes the bimodule
cochains out of the two terms, which are the pieces of the Hom complex out of the small
resolution, and hence of the small complex computing the Hochschild cohomology of a semifree DG
path algebra such as the two-dimensional Ginzburg algebra `Π₂(Q)`.

* **The vertex term.** Evaluation at `∑ᵥ eᵥ ⊗ eᵥ` identifies the degree-`p` cochains with the
  vertex corner `⨁ᵥ eᵥ Nₚ eᵥ` (`TauCeti.PathAlgebra.vertexTensorCochainsEquiv`). Since the
  generator is a cycle, the differential of cochains becomes the differential of `N`.
* **The arrow term.** Evaluation at the `∂b` identifies the degree-`p` cochains with the
  families of elements `m_b ∈ eⱼ N eᵢ` of degree `wt b + p`
  (`TauCeti.PathAlgebra.arrowTensorCochainsEquiv`).
  The generator `∂b` is not a cycle: its differential is `∂(d b)`. Accordingly the differential of
  a cochain `f` at `b` is `d (f(∂b)) - (-1)^p f(∂(d b))`, and `f ∘ ∂` is computed from the `m_b` by
  the twisted Leibniz rule `f(∂(x y)) = (-1)^(p |x|) x f(∂y) + f(∂x) y`.
* **The boundary.** Composed with the boundary, a cochain out of the vertex term with value `m`
  at `∑ᵥ eᵥ ⊗ eᵥ` sends `∂y` to the graded commutator `(-1)^(p |y|) y m - m y`.

The sign `(-1)^(p |x|)` is that of the Koszul sign rule for bimodule cochains: the cochains
intertwine the action of the enveloping algebra with its Koszul-twisted action
`TauCeti.DGBimoduleCat.envelopeTwistAction`. Both identifications are the graded, Koszul-signed
form of the evaluation `Hom(Ae, M) ≃ eM` of `IsIdempotentElem.spanSingletonHomEquivSMulTop`.
The Hom complex out of the cone itself, and the resulting computation of Hochschild cohomology,
are not treated here.

## Main definitions

* `TauCeti.PathAlgebra.vertexTensorCochainsEquiv`: cochains out of the vertex term as elements of
  the vertex corner.
* `TauCeti.PathAlgebra.arrowTensorCochainsEquiv`: cochains out of the arrow term as families
  of elements of the arrow corners.

## Main results

* `TauCeti.PathAlgebra.coe_vertexTensorCochainsEquiv_differential` and
  `TauCeti.PathAlgebra.coe_arrowTensorCochainsEquiv_differential`: the differentials of cochains
  in these coordinates.
* `TauCeti.PathAlgebra.arrowTensor_cochain_apply_arrowTensorDerivation_mul`: the twisted Leibniz
  rule.
* `TauCeti.PathAlgebra.vertexTensor_cochain_apply_arrowTensorDifferential_arrowTensorDerivation`:
  restriction along the boundary is the graded commutator.

## References

* B. Keller, *Deformed Calabi--Yau completions*, J. Reine Angew. Math. 654 (2011), 125--180,
  Section 6, for the small resolution of a semifree DG algebra.
* J. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  [arXiv:2301.06757](https://arxiv.org/abs/2301.06757), Proposition 3.2, for the small complex
  computing the Hochschild cohomology of a two-dimensional Ginzburg algebra.
-/

public section

open CategoryTheory MulOpposite
open scoped TensorProduct

namespace TauCeti.PathAlgebra

open TauCeti.Algebra.TensorProduct
open DGBimoduleCat (envelopeTwistAction_one_tmul envelopeTwistAction_mul mem_envelopeCorner_iff
  envelopeTwistAction_tmul_one envelopeTwistAction_zero_eq_smul)

universe u v w

variable {k : Type w} [CommRing k] {Q : Type u} [Quiver.{v} Q] [Finite Q]
  {wt : ∀ {i j : Q}, (i ⟶ j) → ℤ} {d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q}
  {hd : IsDGAlgebra (gradeBy k wt) d}

local notation "𝒫" => pathAlgebra k Q
local notation "ℰ" => 𝒫 ⊗[k] 𝒫ᵐᵒᵖ
local notation "G" => InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt)
local notation "Ξ" => InternalGrading.tensorProduct (G) (InternalGrading.opposite (G))

section Corners

variable {N : DGBimoduleCat hd hd}

/-- The action of `∑ᵥ eᵥ ⊗ eᵥ`, twisted or not, is `m ↦ ∑ᵥ eᵥ m eᵥ`. -/
theorem envelopeTwistAction_vertexTensorIdempotent [Fintype Q] (p : ℤ) (m : N) :
    N.envelopeTwistAction p (vertexTensorIdempotent k Q) m =
      ∑ v : Q, vertexIdempotent k v • op (vertexIdempotent k v) • m := by
  simp only [vertexTensorIdempotent_def, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ N.envelopeTwistAction_tmul_of_mem_zero p
    (vertexIdempotent_mem_gradeBy_zero (k := k) wt v) _ m

/-- The action of `eⱼ ⊗ eᵢ`, twisted or not, is `m ↦ eⱼ m eᵢ`. -/
theorem envelopeTwistAction_arrowTensorIdempotent (p : ℤ) (b : Σ i j : Q, i ⟶ j) (m : N) :
    N.envelopeTwistAction p (arrowTensorIdempotent k Q b) m =
      vertexIdempotent k b.2.1 • op (vertexIdempotent k b.1) • m := by
  rw [arrowTensorIdempotent_def]
  exact N.envelopeTwistAction_tmul_of_mem_zero p
    (vertexIdempotent_mem_gradeBy_zero (k := k) wt _) _ m

/-- The vertex corner `⨁ᵥ eᵥ N_q eᵥ`. -/
theorem mem_envelopeCorner_vertexTensorIdempotent_iff [Fintype Q] {q : ℤ} {m : N} :
    m ∈ N.envelopeCorner (vertexTensorIdempotent k Q) q ↔
      m ∈ N.grading q ∧ ∑ v : Q, vertexIdempotent k v • op (vertexIdempotent k v) • m = m := by
  rw [mem_envelopeCorner_iff, envelopeTwistAction_vertexTensorIdempotent]

/-- The arrow corner `eⱼ N_q eᵢ` of an arrow `b : i ⟶ j`. -/
theorem mem_envelopeCorner_arrowTensorIdempotent_iff {q : ℤ} {b : Σ i j : Q, i ⟶ j} {m : N} :
    m ∈ N.envelopeCorner (arrowTensorIdempotent k Q b) q ↔
      m ∈ N.grading q ∧ vertexIdempotent k b.2.1 • op (vertexIdempotent k b.1) • m = m := by
  rw [mem_envelopeCorner_iff, envelopeTwistAction_arrowTensorIdempotent]

/-- The twisted action adds degrees, for the total-weight grading of the enveloping algebra. -/
private theorem envelopeTwistAction_mem_tensorProduct (p : ℤ) {q r : ℤ} {u : ℰ}
    (hu : u ∈ (Ξ).piece q) {m : N} (hm : m ∈ N.grading r) :
    N.envelopeTwistAction p u m ∈ N.grading (q + r) :=
  DGBimoduleCat.envelopeTwistAction_mem p (by rwa [(G).ofDecomposition_piece_eq]) hm

end Corners

section Vertex

variable [Fintype Q] (hdε : ∀ i, d (vertexIdempotent k i) = 0) (N : DGBimoduleCat hd hd)

/-- On the vertex term, the untwisted action is the action of the enveloping algebra. -/
private theorem vertexTensorDGBimodule_envelopeTwistAction_zero (u : ℰ)
    (z : vertexTensorBimodule k Q) :
    (vertexTensorDGBimodule hd hdε).envelopeTwistAction 0 u z = u • z :=
  envelopeTwistAction_zero_eq_smul (N := vertexTensorDGBimodule hd hdε)
    (instE := (inferInstance : Module ℰ ↥(vertexTensorBimodule k Q)))
    (smul_moduleLeft_smul_moduleRight (k := k) (M := ↥(vertexTensorBimodule k Q))) u z

include hdε in
/-- A cochain out of the vertex term intertwines the enveloping action with the twisted one. -/
theorem vertexTensor_cochain_apply_smul {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (vertexTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p)
    (u : ℰ) (z : vertexTensorBimodule k Q) :
    f.val.val (u • z) = N.envelopeTwistAction p u (f.val.val z) := by
  have h := dgBimoduleCochains.map_envelopeTwistAction f u z
  rwa [vertexTensorDGBimodule_envelopeTwistAction_zero] at h

/-- The twisted action on a fixed element, as a map out of the vertex term. -/
private noncomputable def vertexTensorTwistMap (p : ℤ) (m : N) :
    vertexTensorBimodule k Q →ₗ[k] N :=
  ((N.envelopeTwistAction p).flip m).comp ((vertexTensorBimodule k Q).subtype.restrictScalars k)

private theorem vertexTensorTwistMap_apply (p : ℤ) (m : N) (z : vertexTensorBimodule k Q) :
    vertexTensorTwistMap N p m z = N.envelopeTwistAction p (z : ℰ) m := (rfl)

private theorem vertexTensorTwistMap_smul (p : ℤ) (m : N) (u : ℰ)
    (z : vertexTensorBimodule k Q) :
    vertexTensorTwistMap N p m (u • z) =
      N.envelopeTwistAction p u (vertexTensorTwistMap N p m z) := by
  simp [vertexTensorTwistMap, envelopeTwistAction_mul]

/-- The cochain out of the vertex term with value `m` at the generator `∑ᵥ eᵥ ⊗ eᵥ`. -/
private noncomputable def vertexTensorCochainOfCorner {p : ℤ}
    (m : N.envelopeCorner (vertexTensorIdempotent k Q) p) :
    dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (vertexTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p :=
  dgBimoduleCochains.ofEnvelopeTwist (M := vertexTensorDGBimodule hd hdε)
    (vertexTensorTwistMap N p m)
    (LinearMap.isHomogeneous_def.2 fun q z hz ↦ by
      rw [mem_vertexTensorDGBimodule_grading_iff, mem_vertexTensorGrading_piece_iff] at hz
      rw [vertexTensorTwistMap_apply]
      exact envelopeTwistAction_mem_tensorProduct p hz (mem_envelopeCorner_iff.1 m.property).1)
    fun u z ↦ by
      rw [vertexTensorDGBimodule_envelopeTwistAction_zero]
      exact vertexTensorTwistMap_smul N p m u z

private theorem vertexTensorCochainOfCorner_apply {p : ℤ}
    (m : N.envelopeCorner (vertexTensorIdempotent k Q) p)
    (z : vertexTensorBimodule k Q) :
    (vertexTensorCochainOfCorner hdε N m).val.val z =
      N.envelopeTwistAction p (z : ℰ) m := by
  rw [vertexTensorCochainOfCorner, dgBimoduleCochains.ofEnvelopeTwist_apply,
    vertexTensorTwistMap_apply]

/-- **Cochains out of the vertex term are elements of the vertex corner.** Evaluation at the
generator `∑ᵥ eᵥ ⊗ eᵥ` identifies the degree-`p` cochains from `kQ ⊗_{kQ₀} kQ` to `N` with
`⨁ᵥ eᵥ Nₚ eᵥ`. -/
noncomputable def vertexTensorCochainsEquiv (p : ℤ) :
    dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (vertexTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p ≃ₗ[k]
      N.envelopeCorner (vertexTensorIdempotent k Q) p where
  toFun f := ⟨f.val.val (spanSingletonGenerator (vertexTensorIdempotent k Q)), by
    refine mem_envelopeCorner_vertexTensorIdempotent_iff.2 ⟨?_, ?_⟩
    · simpa only [zero_add] using
        dgBimoduleCochains.map_mem f ((mem_vertexTensorDGBimodule_grading_iff hd hdε).2
          (spanSingletonGenerator_mem_vertexTensorGrading_zero k Q wt))
    · have hfix : vertexTensorIdempotent k Q • spanSingletonGenerator (vertexTensorIdempotent k Q) =
          spanSingletonGenerator (vertexTensorIdempotent k Q) := by
        simpa using smul_spanSingletonGenerator (isIdempotentElem_vertexTensorIdempotent k Q)
          (spanSingletonGenerator (vertexTensorIdempotent k Q))
      rw [← envelopeTwistAction_vertexTensorIdempotent p, ← vertexTensor_cochain_apply_smul hdε,
        hfix]⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  invFun := vertexTensorCochainOfCorner hdε N
  left_inv f := by
    ext z
    rw [vertexTensorCochainOfCorner_apply, ← vertexTensor_cochain_apply_smul hdε,
      smul_spanSingletonGenerator (isIdempotentElem_vertexTensorIdempotent k Q)]
  right_inv m := by
    refine Subtype.ext ?_
    dsimp only
    rw [vertexTensorCochainOfCorner_apply, coe_spanSingletonGenerator,
      envelopeTwistAction_vertexTensorIdempotent,
      (mem_envelopeCorner_vertexTensorIdempotent_iff.1 m.property).2]

@[simp]
theorem coe_vertexTensorCochainsEquiv_apply {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (vertexTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p) :
    (vertexTensorCochainsEquiv hdε N p f : N) =
      f.val.val (spanSingletonGenerator (vertexTensorIdempotent k Q)) := (rfl)

@[simp]
theorem vertexTensorCochainsEquiv_symm_apply {p : ℤ}
    (m : N.envelopeCorner (vertexTensorIdempotent k Q) p)
    (z : vertexTensorBimodule k Q) :
    ((vertexTensorCochainsEquiv hdε N p).symm m).val.val z =
      N.envelopeTwistAction p (z : ℰ) m :=
  vertexTensorCochainOfCorner_apply hdε N m z

/-- **The differential of cochains out of the vertex term is the differential of `N`** on the
vertex corner. -/
theorem coe_vertexTensorCochainsEquiv_differential {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (vertexTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p) :
    (vertexTensorCochainsEquiv hdε N (p + 1)
        (dgBimoduleCochains.differential (hM := (vertexTensorDGBimodule hd hdε).isDGBimodule)
          (hN := N.isDGBimodule) p f) : N) =
      N.differential (vertexTensorCochainsEquiv hdε N p f) := by
  rw [coe_vertexTensorCochainsEquiv_apply, coe_vertexTensorCochainsEquiv_apply,
    dgBimoduleCochains.differential_apply, vertexTensorDGBimodule_differential_apply,
    vertexTensorBimoduleDifferential_spanSingletonGenerator hdε, map_zero, smul_zero, sub_zero]

end Vertex

section ArrowGenerators

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)] (N : DGBimoduleCat hd hd)

/-- The twisted action on a family of elements, one for each arrow, as a map out of the arrow
term. -/
private noncomputable def arrowTensorTwistMap (p : ℤ) (m : (Σ i j : Q, i ⟶ j) → N) :
    arrowTensorBimodule k Q →ₗ[k] N :=
  DirectSum.toModule k _ N fun b ↦ ((N.envelopeTwistAction p).flip (m b)).comp
    ((Ideal.span {arrowTensorIdempotent k Q b} : Ideal ℰ).subtype.restrictScalars k)

private theorem arrowTensorTwistMap_of (p : ℤ) (m : (Σ i j : Q, i ⟶ j) → N)
    (b : Σ i j : Q, i ⟶ j) (x : (Ideal.span {arrowTensorIdempotent k Q b} : Ideal ℰ)) :
    arrowTensorTwistMap N p m (DirectSum.of _ b x) =
      N.envelopeTwistAction p (x : ℰ) (m b) := by
  simp [arrowTensorTwistMap, ← DirectSum.lof_eq_of k]

private theorem arrowTensorTwistMap_smul (p : ℤ) (m : (Σ i j : Q, i ⟶ j) → N) (u : ℰ)
    (z : arrowTensorBimodule k Q) :
    arrowTensorTwistMap N p m (u • z) =
      N.envelopeTwistAction p u (arrowTensorTwistMap N p m z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of b x =>
    rw [← DirectSum.of_smul, arrowTensorTwistMap_of, arrowTensorTwistMap_of, Submodule.coe_smul,
      smul_eq_mul, envelopeTwistAction_mul]
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', map_add]

private theorem arrowTensorTwistMap_arrowTensorDerivation (p : ℤ)
    (m : (Σ i j : Q, i ⟶ j) → N) (b : Σ i j : Q, i ⟶ j) :
    arrowTensorTwistMap N p m (arrowTensorDerivation k Q (ofArrow b.2.2)) =
      N.envelopeTwistAction p (arrowTensorIdempotent k Q b) (m b) := by
  obtain ⟨i, j, b⟩ := b
  rw [arrowTensorDerivation_ofArrow, DirectSum.lof_eq_of, arrowTensorTwistMap_of,
    coe_spanSingletonGenerator]

private theorem arrowTensorTwistMap_arrowTensorDerivation_of_mem {p : ℤ}
    (m : ∀ b : Σ i j : Q, i ⟶ j,
      N.envelopeCorner (arrowTensorIdempotent k Q b) (wt b.2.2 + p)) (b : Σ i j : Q, i ⟶ j) :
    arrowTensorTwistMap N p (fun b ↦ m b) (arrowTensorDerivation k Q (ofArrow b.2.2)) = m b := by
  rw [arrowTensorTwistMap_arrowTensorDerivation, envelopeTwistAction_arrowTensorIdempotent,
    (mem_envelopeCorner_arrowTensorIdempotent_iff.1 (m b).property).2]

end ArrowGenerators

section Arrow

variable [Fintype Q] [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]
  (hdε : ∀ i, d (vertexIdempotent k i) = 0) (N : DGBimoduleCat hd hd)

/-- On the arrow term, the untwisted action is the action of the enveloping algebra. -/
private theorem arrowTensorDGBimodule_envelopeTwistAction_zero (u : ℰ)
    (z : arrowTensorBimodule k Q) :
    (arrowTensorDGBimodule hd hdε).envelopeTwistAction 0 u z = u • z :=
  envelopeTwistAction_zero_eq_smul (N := arrowTensorDGBimodule hd hdε)
    (instE := (inferInstance : Module ℰ (arrowTensorBimodule k Q)))
    (smul_moduleLeft_smul_moduleRight (k := k) (M := (arrowTensorBimodule k Q))) u z

include hdε in
/-- A cochain out of the arrow term intertwines the enveloping action with the twisted one. -/
theorem arrowTensor_cochain_apply_smul {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p)
    (u : ℰ) (z : arrowTensorBimodule k Q) :
    f.val.val (u • z) = N.envelopeTwistAction p u (f.val.val z) := by
  have h := dgBimoduleCochains.map_envelopeTwistAction f u z
  rwa [arrowTensorDGBimodule_envelopeTwistAction_zero] at h

include hdε in
/-- **Cochains out of the arrow term are determined by their values on the universal derivatives
of the arrows.** -/
theorem arrowTensor_cochain_ext {p : ℤ}
    {f g : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p}
    (h : ∀ b : Σ i j : Q, i ⟶ j, f.val.val (arrowTensorDerivation k Q (ofArrow b.2.2)) =
      g.val.val (arrowTensorDerivation k Q (ofArrow b.2.2))) : f = g := by
  ext z
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of b x =>
    rw [of_eq_smul_arrowTensorDerivation, arrowTensor_cochain_apply_smul hdε,
      arrowTensor_cochain_apply_smul hdε, h]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- A map out of the arrow term which intertwines the enveloping action with the twisted one, and
sends the universal derivative of each arrow `b` to degree `wt b + p`, is homogeneous of degree
`p`. -/
private theorem arrowTensor_map_mem_of_smul {p : ℤ} (g : arrowTensorBimodule k Q →ₗ[k] N)
    (hg : ∀ (u : ℰ) z, g (u • z) = N.envelopeTwistAction p u (g z))
    (hgen : ∀ b : Σ i j : Q, i ⟶ j,
      g (arrowTensorDerivation k Q (ofArrow b.2.2)) ∈ N.grading (wt b.2.2 + p))
    {q : ℤ} {z : arrowTensorBimodule k Q} (hz : z ∈ (arrowTensorGrading k Q wt).piece q) :
    g z ∈ N.grading (q + p) := by
  classical
  -- The multiples `u ∂b` with `u` homogeneous are homogeneous generators of the arrow term.
  let s : ℤ → Set (arrowTensorBimodule k Q) := fun q ↦
    {x | ∃ (b : Σ i j : Q, i ⟶ j) (u : ℰ), u ∈ (Ξ).piece (q - wt b.2.2) ∧
      x = u • arrowTensorDerivation k Q (ofArrow b.2.2)}
  let C : ℤ → Submodule k (arrowTensorBimodule k Q) := fun q ↦
    (arrowTensorGrading k Q wt).piece q ⊓ (N.grading (q + p)).comap g
  have hsC (q : ℤ) : s q ⊆ C q := by
    rintro _ ⟨b, u, hu, rfl⟩
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · simpa only [sub_add_cancel] using smul_mem_arrowTensorGrading k Q wt hu
        (arrowTensorDerivation_ofArrow_mem k Q wt b.2.2)
    · rw [Submodule.mem_comap, hg]
      simpa only [show q - wt b.2.2 + (wt b.2.2 + p) = q + p by ring] using
        envelopeTwistAction_mem_tensorProduct p hu (hgen b)
  have hspan (z : arrowTensorBimodule k Q) : z ∈ Submodule.span k
      (Set.range fun i : (Σ q : ℤ, s q) ↦ (i.2 : arrowTensorBimodule k Q)) := by
    induction z using DirectSum.induction_on with
    | zero => exact zero_mem _
    | add z z' hz hz' => exact add_mem hz hz'
    | of b x =>
      rw [of_eq_smul_arrowTensorDerivation, ← DirectSum.sum_support_decompose (Ξ).piece (x : ℰ),
        Finset.sum_smul]
      refine sum_mem fun r _ ↦ Submodule.subset_span ⟨⟨r + wt b.2.2, _, b, _, ?_, rfl⟩, rfl⟩
      simpa only [add_sub_cancel_right] using SetLike.coe_mem _
  have h := (arrowTensorGrading k Q wt).decompose_mem_of_mem_span_sigma C s hsC
    (fun _ ↦ inf_le_left) (hspan z) q
  rw [DirectSum.decompose_of_mem_same _ hz] at h
  exact h.2

include hdε in
/-- The cochain out of the arrow term with value `m b` at the universal derivative of each
arrow `b`. -/
private noncomputable def arrowTensorCochainOfCorner {p : ℤ}
    (m : ∀ b : Σ i j : Q, i ⟶ j,
      N.envelopeCorner (arrowTensorIdempotent k Q b) (wt b.2.2 + p)) :
    dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p :=
  dgBimoduleCochains.ofEnvelopeTwist (M := arrowTensorDGBimodule hd hdε)
    (arrowTensorTwistMap N p fun b ↦ m b)
    (LinearMap.isHomogeneous_def.2 fun _ _ hz ↦
      arrowTensor_map_mem_of_smul N _ (arrowTensorTwistMap_smul N p _)
        (fun b ↦ by
          rw [arrowTensorTwistMap_arrowTensorDerivation_of_mem N m]
          exact (mem_envelopeCorner_iff.1 (m b).property).1)
        ((mem_arrowTensorDGBimodule_grading_iff hd hdε).1 hz))
    fun u z ↦ by
      rw [arrowTensorDGBimodule_envelopeTwistAction_zero]
      exact arrowTensorTwistMap_smul N p _ u z

/-- The cochain built from a family `m` takes the value `m b` at the universal derivative of each
arrow `b`. -/
private theorem arrowTensorCochainOfCorner_apply_arrowTensorDerivation {p : ℤ}
    (m : ∀ b : Σ i j : Q, i ⟶ j,
      N.envelopeCorner (arrowTensorIdempotent k Q b) (wt b.2.2 + p)) (b : Σ i j : Q, i ⟶ j) :
    (arrowTensorCochainOfCorner hdε N m).val.val (arrowTensorDerivation k Q (ofArrow b.2.2)) =
      m b := by
  rw [arrowTensorCochainOfCorner, dgBimoduleCochains.ofEnvelopeTwist_apply]
  exact arrowTensorTwistMap_arrowTensorDerivation_of_mem N m b

include hdε in
/-- The value of a cochain at the universal derivative of an arrow `b` lies in the corner
`eⱼ N eᵢ`, in degree `wt b + p`. -/
theorem arrowTensor_cochain_apply_mem_envelopeCorner {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p)
    (b : Σ i j : Q, i ⟶ j) :
    f.val.val (arrowTensorDerivation k Q (ofArrow b.2.2)) ∈
      N.envelopeCorner (arrowTensorIdempotent k Q b) (wt b.2.2 + p) := by
  refine mem_envelopeCorner_arrowTensorIdempotent_iff.2 ⟨dgBimoduleCochains.map_mem f
    ((mem_arrowTensorDGBimodule_grading_iff hd hdε).2
      (arrowTensorDerivation_ofArrow_mem k Q wt b.2.2)), ?_⟩
  rw [← envelopeTwistAction_arrowTensorIdempotent p, ← arrowTensor_cochain_apply_smul hdε,
    arrowTensorIdempotent_smul_arrowTensorDerivation]

/-- **Cochains out of the arrow term are families of corner elements.** Evaluation at the
universal derivatives `∂b` of the arrows identifies the degree-`p` cochains from
`⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ kQ` to `N` with the families `(m_b)` of elements `m_b ∈ eⱼ N eᵢ` of
degree `wt b + p`. -/
noncomputable def arrowTensorCochainsEquiv (p : ℤ) :
    dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p ≃ₗ[k]
      ∀ b : Σ i j : Q, i ⟶ j, N.envelopeCorner (arrowTensorIdempotent k Q b) (wt b.2.2 + p) where
  toFun f b := ⟨_, arrowTensor_cochain_apply_mem_envelopeCorner hdε N f b⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  invFun := arrowTensorCochainOfCorner hdε N
  left_inv _ := arrowTensor_cochain_ext hdε N fun b ↦
    arrowTensorCochainOfCorner_apply_arrowTensorDerivation hdε N _ b
  right_inv m := funext fun b ↦ Subtype.ext
    (arrowTensorCochainOfCorner_apply_arrowTensorDerivation hdε N m b)

@[simp]
theorem coe_arrowTensorCochainsEquiv_apply {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p)
    (b : Σ i j : Q, i ⟶ j) :
    (arrowTensorCochainsEquiv hdε N p f b : N) =
      f.val.val (arrowTensorDerivation k Q (ofArrow b.2.2)) := (rfl)

/-- The inverse of `TauCeti.PathAlgebra.arrowTensorCochainsEquiv` takes the value `m b` at the
universal derivative of each arrow `b`. -/
theorem arrowTensorCochainsEquiv_symm_apply_arrowTensorDerivation {p : ℤ}
    (m : ∀ b : Σ i j : Q, i ⟶ j,
      N.envelopeCorner (arrowTensorIdempotent k Q b) (wt b.2.2 + p)) (b : Σ i j : Q, i ⟶ j) :
    ((arrowTensorCochainsEquiv hdε N p).symm m).val.val
        (arrowTensorDerivation k Q (ofArrow b.2.2)) = m b :=
  arrowTensorCochainOfCorner_apply_arrowTensorDerivation hdε N m b

include hdε in
/-- **The twisted Leibniz rule.** Composed with the universal derivation, a degree-`p` cochain out
of the arrow term is a derivation twisted by the Koszul sign: on homogeneous `x` of degree `r`,
`f(∂(x y)) = (-1)^(p r) x f(∂y) + f(∂x) y`. -/
theorem arrowTensor_cochain_apply_arrowTensorDerivation_mul {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p) (x y : 𝒫) :
    f.val.val (arrowTensorDerivation k Q (x * y)) =
      InternalGrading.koszulTwistAlgEquiv (gradeBy k wt) p x •
          f.val.val (arrowTensorDerivation k Q y) +
        op y • f.val.val (arrowTensorDerivation k Q x) := by
  rw [arrowTensorDerivation_mul, map_add, arrowTensor_cochain_apply_smul hdε,
    arrowTensor_cochain_apply_smul hdε, envelopeTwistAction_tmul_one, envelopeTwistAction_one_tmul]

/-- **The differential of cochains out of the arrow term.** At an arrow `b`, the differential of
a degree-`p` cochain `f` is `d (f(∂b)) - (-1)^p f(∂(d b))`, the second term coming from the twist of
the differential of the arrow term. -/
theorem coe_arrowTensorCochainsEquiv_differential {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (arrowTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p)
    (b : Σ i j : Q, i ⟶ j) :
    (arrowTensorCochainsEquiv hdε N (p + 1)
        (dgBimoduleCochains.differential (hM := (arrowTensorDGBimodule hd hdε).isDGBimodule)
          (hN := N.isDGBimodule) p f) b : N) =
      N.differential (arrowTensorCochainsEquiv hdε N p f b) -
        p.negOnePow • f.val.val (arrowTensorDerivation k Q (d (ofArrow b.2.2))) := by
  rw [coe_arrowTensorCochainsEquiv_apply, coe_arrowTensorCochainsEquiv_apply,
    dgBimoduleCochains.differential_apply, arrowTensorDGBimodule_differential_apply,
    arrowTensorBimoduleDifferential_arrowTensorDerivation hd hdε]

end Arrow

section Boundary

variable [Fintype Q] [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]
  (hdε : ∀ i, d (vertexIdempotent k i) = 0) (N : DGBimoduleCat hd hd)

include hdε in
/-- **Restriction along the boundary is the graded commutator.** A degree-`p` cochain `f` out of
the vertex term, composed with the boundary of the small resolution, takes the value
`(-1)^(p r) y m - m y` at the universal derivative `∂y` of an element `y` of degree `r`, where
`m = f(∑ᵥ eᵥ ⊗ eᵥ)`. -/
theorem vertexTensor_cochain_apply_arrowTensorDifferential_arrowTensorDerivation {p : ℤ}
    (f : dgBimoduleCochains (B := 𝒫) (𝒜 := gradeBy k wt)
      (ℳ := (vertexTensorDGBimodule hd hdε).grading) (𝒩 := N.grading) p) (y : 𝒫) :
    f.val.val (arrowTensorDifferential k Q (arrowTensorDerivation k Q y)) =
      InternalGrading.koszulTwistAlgEquiv (gradeBy k wt) p y •
          f.val.val (spanSingletonGenerator (vertexTensorIdempotent k Q)) -
        op y • f.val.val (spanSingletonGenerator (vertexTensorIdempotent k Q)) := by
  have h : arrowTensorDifferential k Q (arrowTensorDerivation k Q y) =
      (y ⊗ₜ[k] (1 : 𝒫ᵐᵒᵖ) - (1 : 𝒫) ⊗ₜ[k] op y) •
        spanSingletonGenerator (vertexTensorIdempotent k Q) :=
    Subtype.ext (by
      rw [Submodule.coe_smul, coe_spanSingletonGenerator, smul_eq_mul,
        coe_arrowTensorDifferential_arrowTensorDerivation])
  rw [h, vertexTensor_cochain_apply_smul hdε, map_sub, LinearMap.sub_apply,
    envelopeTwistAction_tmul_one, envelopeTwistAction_one_tmul]

end Boundary

end TauCeti.PathAlgebra
