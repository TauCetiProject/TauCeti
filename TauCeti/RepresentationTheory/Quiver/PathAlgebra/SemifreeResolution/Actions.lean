/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BimoduleResolution.Grading

/-!
# Bimodule Leibniz rules for the small DG path resolution

The two differentials of the standard resolution of a DG path algebra obey the two-sided
Leibniz rule. If `x` and `w` are homogeneous, it reads

`d(x w y) = d(x) w y + (-1)^|x| x d(w) y + (-1)^(|x|+|w|) x w d(y)`.

Here the bimodule action is written as `(x ⊗ op y) • w`, using the existing modules over the
ordinary enveloping algebra. The generator of an arrow summand has the degree of that arrow;
the differential of this generator is the universal derivation of the arrow differential.
Thus the arrow term is a twisted free bimodule, not a direct sum with an untwisted tensor
differential. Its Leibniz rule is detected by the injective boundary into the vertex term.

These action laws are needed to regard the small resolution as a resolution by DG bimodules,
rather than just complexes of coefficient modules. They do not assert cofibrancy or construct
the resolution cone.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6, for the small bimodule resolution
  of a semifree DG algebra.
* Y. Liu and W. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  for its use in the Hochschild computation of the two-dimensional Ginzburg algebra.
-/

public section

open MulOpposite
open scoped TensorProduct

namespace TauCeti.PathAlgebra

universe u v w

variable {k : Type w} [CommRing k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  {wt : ∀ {i j : Q}, (i ⟶ j) → ℤ} {d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q}

local notation "A" => pathAlgebra k Q
local notation "E" => A ⊗[k] Aᵐᵒᵖ
local notation "σ" =>
  InternalGrading.koszulTwist (InternalGrading.ofDecomposition (gradeBy k wt)) 1

variable (hd : IsDGAlgebra (gradeBy k wt) d) (hdε : ∀ v, d (vertexIdempotent k v) = 0)

include hd hdε

/-- The vertex-term differential obeys the enveloping-action Leibniz rule on a homogeneous
module element. The degree of that element determines the differential on the acting tensor. -/
theorem vertexTensorBimoduleDifferential_smul_of_mem {q : ℤ}
    {z : vertexTensorBimodule k Q} (hz : z ∈ (vertexTensorGrading k Q wt).piece q) (u : E) :
    vertexTensorBimoduleDifferential wt d (u • z) =
      envelopeDifferential (gradeBy k wt) d q u • z +
        TensorProduct.map σ LinearMap.id u • vertexTensorBimoduleDifferential wt d z := by
  apply Subtype.ext
  simp only [coe_vertexTensorBimoduleDifferential hd hdε, Submodule.coe_smul,
    Submodule.coe_add, smul_eq_mul]
  have hΓ : InternalGrading.ofDecomposition (gradeBy k wt) =
      InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt) :=
    InternalGrading.ext fun _ => congrFun (InternalGrading.ofDecomposition_piece _) _
  have hz' := (mem_vertexTensorGrading_piece_iff k Q wt).mp hz
  rw [← hΓ] at hz'
  simpa only [zero_add] using envelopeDifferential_mul_of_mem
    hd.toIsNonUnitalDGAlgebra 0 hz' u

/-- The full two-sided Leibniz rule in the vertex term. The right factor need not be
homogeneous. -/
theorem vertexTensorBimoduleDifferential_tmul_smul {p q : ℤ} {x : A}
    (hx : x ∈ gradeBy k wt p) {z : vertexTensorBimodule k Q}
    (hz : z ∈ (vertexTensorGrading k Q wt).piece q) (y : A) :
    vertexTensorBimoduleDifferential wt d ((x ⊗ₜ[k] op y) • z) =
      (d x ⊗ₜ[k] op y) • z +
        negOnePowCast k p • ((x ⊗ₜ[k] op y) • vertexTensorBimoduleDifferential wt d z) +
          negOnePowCast k (p + q) • ((x ⊗ₜ[k] op (d y)) • z) := by
  rw [vertexTensorBimoduleDifferential_smul_of_mem hd hdε hz,
    envelopeDifferential_tmul_of_mem q hx, add_smul, smul_assoc,
    TensorProduct.map_tmul, LinearMap.id_apply,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hx, one_mul,
    ← negOnePowCast_eq_intCast, ← TensorProduct.smul_tmul', smul_assoc]
  abel

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

/-- The twisted arrow-term differential obeys the enveloping-action Leibniz rule. The twist
on arrow generators is compatible with the ordinary outer bimodule actions. -/
theorem arrowTensorBimoduleDifferential_smul_of_mem {q : ℤ}
    {z : arrowTensorBimodule k Q} (hz : z ∈ (arrowTensorGrading k Q wt).piece q) (u : E) :
    arrowTensorBimoduleDifferential wt d (u • z) =
      envelopeDifferential (gradeBy k wt) d q u • z +
        TensorProduct.map σ LinearMap.id u • arrowTensorBimoduleDifferential wt d z := by
  apply arrowTensorDifferential_injective
  have hz' : arrowTensorDifferential k Q z ∈ (vertexTensorGrading k Q wt).piece q := by
    simpa only [add_zero] using (isHomogeneous_arrowTensorDifferential k Q wt).map_mem hz
  simp only [arrowTensorDifferential_arrowTensorBimoduleDifferential hd hdε,
    (arrowTensorDifferential k Q).map_smul, map_add]
  exact vertexTensorBimoduleDifferential_smul_of_mem hd hdε hz' u

/-- The full two-sided Leibniz rule in the twisted arrow term, with the sign determined by
its actual arrow-weight grading. The right factor is arbitrary. -/
theorem arrowTensorBimoduleDifferential_tmul_smul {p q : ℤ} {x : A}
    (hx : x ∈ gradeBy k wt p) {z : arrowTensorBimodule k Q}
    (hz : z ∈ (arrowTensorGrading k Q wt).piece q) (y : A) :
    arrowTensorBimoduleDifferential wt d ((x ⊗ₜ[k] op y) • z) =
      (d x ⊗ₜ[k] op y) • z +
        negOnePowCast k p • ((x ⊗ₜ[k] op y) • arrowTensorBimoduleDifferential wt d z) +
          negOnePowCast k (p + q) • ((x ⊗ₜ[k] op (d y)) • z) := by
  rw [arrowTensorBimoduleDifferential_smul_of_mem hd hdε hz,
    envelopeDifferential_tmul_of_mem q hx, add_smul, smul_assoc,
    TensorProduct.map_tmul, LinearMap.id_apply,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hx, one_mul,
    ← negOnePowCast_eq_intCast, ← TensorProduct.smul_tmul', smul_assoc]
  abel

end TauCeti.PathAlgebra
