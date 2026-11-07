/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BimoduleResolution.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Arrow-weight gradings of the standard bimodule resolution

An integer weight on each arrow of a finite-vertex quiver grades its standard bimodule
resolution. The vertex term inherits total degree from the enveloping algebra. The generator
of the summand indexed by an arrow `b` has degree `wt b`, not degree zero: with this convention
both the boundary and multiplication preserve degree. The universal derivation also preserves
degree. In particular, the construction applies separately to the cohomological and Adams
weights of a Ginzburg algebra.

The arrow-term grading is pulled back along the injective boundary. Exactness identifies its
image with the kernel of homogeneous multiplication, so the pulled-back pieces really form an
internal direct sum. The homogeneous pure-tensor formulas identify this grading with the usual
shifted grading on each arrow summand; it is a grading of the existing resolution, not a new
resolution on a different carrier.

## References

* D. Happel, *Hochschild cohomology of finite-dimensional algebras*, Lecture Notes in
  Mathematics 1404 (1989), Section 1, for the standard bimodule resolution.
* B. Keller, *Deformed Calabi--Yau completions*, Section 6, for the graded resolution underlying
  the small bimodule resolution of a semifree differential graded algebra.
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti.PathAlgebra

open MulOpposite

universe u v w

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q] [Fintype Q]
  (wt : ∀ {i j : Q}, (i ⟶ j) → ℤ)

local notation "A" => pathAlgebra k Q
local notation "E" => A ⊗[k] Aᵐᵒᵖ
local notation "Γ" => InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt)
local notation "Ξ" => InternalGrading.tensorProduct Γ (InternalGrading.opposite Γ)
local notation "Δ" => InternalGrading.map Γ (Bimodule.of (AlgHom.id k A))

private theorem isHomogeneous_mul_vertexTensorIdempotent :
    LinearMap.IsHomogeneous
      (LinearMap.toSpanSingleton E E (vertexTensorIdempotent k Q)) (Ξ).piece (Ξ).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (Γ).tensorProduct_piece_le (Γ).opposite
    (C := ((Ξ).piece (n + 0)).comap
      ((LinearMap.toSpanSingleton E E (vertexTensorIdempotent k Q)).restrictScalars k)) ?_ hz
  intro p x hx y hy
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, smul_eq_mul, vertexTensorIdempotent_def, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← op_unop y, ← op_mul]
  have hx' : x * vertexIdempotent k i ∈ gradeBy k wt p := by
    simpa only [add_zero] using
      SetLike.mul_mem_graded hx (vertexIdempotent_mem_gradeBy_zero (k := k) wt i)
  have hy' : vertexIdempotent k i * unop y ∈ gradeBy k wt (n - p) := by
    simpa only [zero_add] using SetLike.mul_mem_graded
      (vertexIdempotent_mem_gradeBy_zero (k := k) wt i) (((Γ).mem_opposite_piece_iff _ _).1 hy)
  have ht := (Γ).tmul_mem_tensorProduct (Γ).opposite hx'
    (((Γ).op_mem_opposite_piece_iff _ _).2 hy')
  simpa only [add_sub_cancel, add_zero] using ht

/-- The vertex term of the standard resolution is homogeneous for total arrow weight. -/
theorem isHomogeneous_vertexTensorBimodule :
    DirectSum.SetLike.IsHomogeneous (Ξ).piece (vertexTensorBimodule k Q) := by
  intro n z hz
  rw [mem_vertexTensorBimodule_iff]
  have hp := (isHomogeneous_mul_vertexTensorIdempotent k Q wt).map_decompose n z
  simp only [LinearMap.toSpanSingleton_apply, smul_eq_mul,
    mem_vertexTensorBimodule_iff.1 hz] at hp
  rw [add_zero] at hp
  exact hp

/-- The internal total-weight grading of `kQ ⊗_{kQ₀} kQ`. -/
noncomputable def vertexTensorGrading : InternalGrading k (vertexTensorBimodule k Q) :=
  (Ξ).submodule (vertexTensorBimodule k Q) (isHomogeneous_vertexTensorBimodule k Q wt)

/-- A vertex tensor is homogeneous exactly when its underlying enveloping element is. -/
@[simp]
theorem mem_vertexTensorGrading_piece_iff {n : ℤ} {z : vertexTensorBimodule k Q} :
    z ∈ (vertexTensorGrading k Q wt).piece n ↔ (z : E) ∈ (Ξ).piece n :=
  (Ξ).mem_submodule_piece _ _

/-- Cutting down a pure tensor by the vertex idempotent preserves its total degree. -/
theorem tmul_mem_vertexTensorGrading {p q : ℤ} {x y : A}
    (hx : x ∈ gradeBy k wt p) (hy : y ∈ gradeBy k wt q) (i : Q) :
    (⟨_, tmul_mem_vertexTensorBimodule i x y⟩ : vertexTensorBimodule k Q) ∈
      (vertexTensorGrading k Q wt).piece (p + q) := by
  rw [mem_vertexTensorGrading_piece_iff]
  have hx' : x * vertexIdempotent k i ∈ gradeBy k wt p := by
    simpa only [add_zero] using
      SetLike.mul_mem_graded hx (vertexIdempotent_mem_gradeBy_zero (k := k) wt i)
  have hy' : vertexIdempotent k i * y ∈ gradeBy k wt q := by
    simpa only [zero_add] using
      SetLike.mul_mem_graded (vertexIdempotent_mem_gradeBy_zero (k := k) wt i) hy
  exact (Γ).tmul_mem_tensorProduct (Γ).opposite hx'
    (((Γ).op_mem_opposite_piece_iff _ _).2 hy')

omit [Fintype Q] in
private theorem isHomogeneous_envelope_action_one [Finite Q] :
    LinearMap.IsHomogeneous
      (LinearMap.toSpanSingleton E _ (Bimodule.of (AlgHom.id k A) 1)) (Ξ).piece (Δ).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (Γ).tensorProduct_piece_le (Γ).opposite
    (C := ((Δ).piece (n + 0)).comap
      ((LinearMap.toSpanSingleton E _ (Bimodule.of (AlgHom.id k A) 1)).restrictScalars k))
    (fun p x hx y hy ↦ ?_) hz
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, Bimodule.smul_of, mul_one,
    InternalGrading.apply_mem_map_piece_iff]
  have hm := SetLike.mul_mem_graded hx (((Γ).mem_opposite_piece_iff _ _).1 hy)
  simpa only [add_sub_cancel, add_zero, AlgHom.id_apply] using hm

/-- Multiplication in the standard resolution preserves total arrow weight. The target grading
is transported through the canonical identification of the diagonal bimodule with `kQ`. -/
theorem isHomogeneous_vertexTensorMul :
    LinearMap.IsHomogeneous (vertexTensorMul k Q)
      (vertexTensorGrading k Q wt).piece (Δ).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  rw [vertexTensorMul_apply]
  exact (isHomogeneous_envelope_action_one k Q wt).map_mem
    ((mem_vertexTensorGrading_piece_iff k Q wt).1 hz)

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

/-- The internal arrow-weight grading on `⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ kQ`, with the generator
of the `b` summand in degree `wt b`. It is pulled back along the injective boundary. -/
noncomputable def arrowTensorGrading : InternalGrading k (arrowTensorBimodule k Q) where
  piece n := ((vertexTensorGrading k Q wt).piece n).comap
    ((arrowTensorDifferential k Q).restrictScalars k)
  isInternal := by
    refine DirectSum.isInternal_comap (vertexTensorGrading k Q wt).piece _
      ((arrowTensorDifferential k Q).restrictScalars k)
      (arrowTensorDifferential_injective (k := k) (Q := Q)) (fun _ _ ↦ Iff.rfl) ?_
    intro n x
    apply (exact_arrowTensorDifferential_vertexTensorMul (k := k) (Q := Q) _).mp
    exact (isHomogeneous_vertexTensorMul k Q wt).isHomogeneous_ker n
      (vertexTensorMul_arrowTensorDifferential x)

/-- The boundary detects homogeneity in the arrow term. -/
@[simp]
theorem mem_arrowTensorGrading_piece_iff {n : ℤ} {z : arrowTensorBimodule k Q} :
    z ∈ (arrowTensorGrading k Q wt).piece n ↔
      (arrowTensorDifferential k Q z : E) ∈ (Ξ).piece n := by
  rw [arrowTensorGrading, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    mem_vertexTensorGrading_piece_iff]

/-- The boundary of the standard resolution preserves arrow weight. -/
theorem isHomogeneous_arrowTensorDifferential :
    LinearMap.IsHomogeneous (arrowTensorDifferential k Q)
      (arrowTensorGrading k Q wt).piece (vertexTensorGrading k Q wt).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hz ↦ by
    simpa only [add_zero, mem_vertexTensorGrading_piece_iff] using
      (mem_arrowTensorGrading_piece_iff k Q wt).1 hz

/-- A pure tensor in the `b` arrow summand has degree `deg x + wt b + deg y`. -/
theorem lof_tmul_mem_arrowTensorGrading (b : Σ i j : Q, i ⟶ j) {p q : ℤ} {x y : A}
    (hx : x ∈ gradeBy k wt p) (hy : y ∈ gradeBy k wt q) :
    DirectSum.lof E _ _ b ⟨_, tmul_mem_span_arrowTensorIdempotent b x y⟩ ∈
      (arrowTensorGrading k Q wt).piece (p + wt b.2.2 + q) := by
  rw [mem_arrowTensorGrading_piece_iff, coe_arrowTensorDifferential_lof_tmul]
  have hx' : x * vertexIdempotent k b.2.1 ∈ gradeBy k wt p := by
    simpa only [add_zero] using
      SetLike.mul_mem_graded hx (vertexIdempotent_mem_gradeBy_zero (k := k) wt b.2.1)
  have hy' : vertexIdempotent k b.1 * y ∈ gradeBy k wt q := by
    simpa only [zero_add] using
      SetLike.mul_mem_graded (vertexIdempotent_mem_gradeBy_zero (k := k) wt b.1) hy
  have hxb := SetLike.mul_mem_graded hx (ofArrow_mem_gradeBy (k := k) wt b.2.2)
  have hby := SetLike.mul_mem_graded (ofArrow_mem_gradeBy (k := k) wt b.2.2) hy
  have hleft := (Γ).tmul_mem_tensorProduct (Γ).opposite hxb
    (((Γ).op_mem_opposite_piece_iff _ _).2 hy')
  have hright := (Γ).tmul_mem_tensorProduct (Γ).opposite hx'
    (((Γ).op_mem_opposite_piece_iff _ _).2 hby)
  exact Submodule.sub_mem _ hleft (by simpa only [add_assoc] using hright)

/-- The universal derivation relative to the vertex subalgebra preserves arrow weight. -/
theorem isHomogeneous_arrowTensorDerivation :
    LinearMap.IsHomogeneous (arrowTensorDerivation k Q)
      (gradeBy k wt) (arrowTensorGrading k Q wt).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n x hx
  rw [mem_arrowTensorGrading_piece_iff, coe_arrowTensorDifferential_arrowTensorDerivation]
  have h1 : (1 : A) ∈ gradeBy k wt 0 := SetLike.one_mem_graded _
  have hleft := (Γ).tmul_mem_tensorProduct (Γ).opposite hx
    (((Γ).op_mem_opposite_piece_iff _ _).2 h1)
  have hright := (Γ).tmul_mem_tensorProduct (Γ).opposite h1
    (((Γ).op_mem_opposite_piece_iff _ _).2 hx)
  have hd : x ⊗ₜ[k] (1 : Aᵐᵒᵖ) - 1 ⊗ₜ[k] op x ∈ (Ξ).piece n :=
    Submodule.sub_mem _ (by simpa only [add_zero, op_one] using hleft)
      (by simpa only [zero_add] using hright)
  exact (isHomogeneous_mul_vertexTensorIdempotent k Q wt).map_mem hd

/-- The canonical generator of the arrow summand has the weight of that arrow. -/
theorem arrowTensorDerivation_ofArrow_mem {i j : Q} (b : i ⟶ j) :
    arrowTensorDerivation k Q (ofArrow b) ∈ (arrowTensorGrading k Q wt).piece (wt b) := by
  simpa only [add_zero] using (isHomogeneous_arrowTensorDerivation k Q wt).map_mem
    (ofArrow_mem_gradeBy (k := k) wt b)

end TauCeti.PathAlgebra
