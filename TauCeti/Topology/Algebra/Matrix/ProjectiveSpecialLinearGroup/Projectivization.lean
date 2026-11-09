/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.Projectivization
public import TauCeti.Topology.Algebra.Projectivization
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# `PSL(n, ℂ)` as an open subset of the projective space of matrices

The map `Matrix.ProjectiveSpecialLinearGroup.toProjectivization` sends the class of a matrix `A` of
`SL(n, K)` to the line of `A` in `ℙ K (Matrix n n K)`. It is continuous for the quotient topology on
`PSL(n, K) = SL(n, K) ⧸ Z(SL(n, K))`, and the locus `{x | x.rep.det ≠ 0}` of lines of invertible
matrices is open. Over `ℂ` the map is a homeomorphism onto this locus, so `PSL(n, ℂ)` is an open
subset of the projective space of `n × n` matrices; for `n = 2`, the complement of the determinant
quadric in `ℂℙ³`.

The inverse sends the line of an invertible matrix `A` to the class of `c⁻¹ • A`, where
`c ^ n = det A`. There is no continuous `n`-th root on all of `ℂˣ`, so near a matrix `A₀` we use
the local branch `A ↦ c₀ * (det A / det A₀) ^ (1 / n)` of the principal power, which is continuous
because `det A / det A₀` stays in the slit plane near `A₀`
(`TauCeti.exists_differentiableAt_pow_eq`).
Different choices of root differ by an `n`-th root of unity, which is central in `SL(n, ℂ)`, so
they give the same element of `PSL(n, ℂ)`. This shows that the map is open.

## Main declarations

* `Matrix.ProjectiveSpecialLinearGroup.continuous_toProjectivization`: the map is continuous.
* `Matrix.isOpen_setOf_det_rep_ne_zero`: the lines of invertible matrices form an open set.
* `Matrix.ProjectiveSpecialLinearGroup.isOpenEmbedding_toProjectivization`: over `ℂ` the map is an
  open embedding.
* `Matrix.ProjectiveSpecialLinearGroup.homeomorphDetNeZero`: the homeomorphism of `PSL(n, ℂ)` with
  the locus of lines of invertible matrices.
-/

public section

open Filter Topology
open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

namespace ProjectiveSpecialLinearGroup

section Topology

variable {K : Type*} [Field K] [TopologicalSpace K]

/-- The map from `PSL(n, K)` to the projective space of matrices is continuous, for the quotient
topology of `SL(n, K) ⧸ Z(SL(n, K))`, whatever the topology of `K`. -/
@[fun_prop]
theorem continuous_toProjectivization : Continuous (toProjectivization n K) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 <|
    (Projectivization.continuous_mk
      (continuous_subtype_val : Continuous fun A : SpecialLinearGroup n K ↦ (A : Matrix n n K))
      fun A ↦ SpecialLinearGroup.coe_ne_zero A).congr fun A ↦ (toProjectivization_mk A).symm

omit [Nonempty n] in
/-- The lines of invertible matrices form an open subset of the projective space of matrices. -/
theorem _root_.Matrix.isOpen_setOf_det_rep_ne_zero [IsTopologicalRing K] [T1Space K] :
    IsOpen {x : ℙ K (Matrix n n K) | x.rep.det ≠ 0} := by
  rw [← Projectivization.isQuotientMap_mk'.isOpen_preimage]
  have : Projectivization.mk' K ⁻¹' {x : ℙ K (Matrix n n K) | x.rep.det ≠ 0} =
      {v : {v : Matrix n n K // v ≠ 0} | (v : Matrix n n K).det ≠ 0} := by
    ext v
    rw [Set.mem_preimage, Projectivization.mk'_eq_mk]
    exact det_rep_mk_ne_zero_iff v.2
  rw [this]
  exact isOpen_compl_singleton.preimage (continuous_subtype_val.matrix_det)

end Topology

section Complex

/-- The map from `PSL(n, ℂ)` to the projective space of matrices is open. -/
theorem isOpenMap_toProjectivization : IsOpenMap (toProjectivization n ℂ) := by
  -- Openness of the image is tested on nonzero representatives `v`. If the line of `v` is the
  -- line of `A ∈ SL(n, ℂ)` with class in `U`, normalizing nearby `w` to determinant one by a local
  -- branch `f` of the root of `det` gives matrices `(f w.det)⁻¹ • w` close to `A`, hence classes
  -- in `U` with the same line as `w`.
  intro U hU
  rw [← Projectivization.isQuotientMap_mk'.isOpen_preimage, isOpen_iff_mem_nhds]
  rintro ⟨v, hv⟩ ⟨g, hgU, hgv⟩
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [toProjectivization_mk, Projectivization.mk'_eq_mk] at hgv
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).1 hgv
  set k := Fintype.card n
  have hk : k ≠ 0 := Fintype.card_ne_zero
  have hdetv : v.det * (a : ℂ) ^ k = 1 := by
    rw [mul_comm, ← det_smul, ← Units.smul_def, ha, A.det_coe]
  have hv0 : v.det ≠ 0 := left_ne_zero_of_mul_eq_one hdetv
  -- A local branch `f` of the `k`-th root at `det v`, inverse to the scaling `a` at `v`.
  obtain ⟨f, hf, hfv, hfk⟩ := TauCeti.exists_differentiableAt_pow_eq hk hv0
    (by rw [inv_pow, inv_eq_of_mul_eq_one_left hdetv] : ((a : ℂ)⁻¹) ^ k = v.det)
  have hcont : Continuous fun w : Matrix n n ℂ ↦ w.det := continuous_id.matrix_det
  have hF : ContinuousAt (fun w ↦ (f w.det)⁻¹ • w) v :=
    ((hf.continuousAt.comp hcont.continuousAt).inv₀ (by simp [hfv])).smul continuousAt_id
  -- The preimage of `U` in `SL(n, ℂ)` is cut out by an open set `O` of matrices.
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 (hU.preimage QuotientGroup.continuous_mk)
  have hAO : (A : Matrix n n ℂ) ∈ O := (Set.ext_iff.1 hOU A).2 hgU
  have h₁ : ∀ᶠ w in 𝓝 v, (f w.det)⁻¹ • w ∈ O := hF.preimage_mem_nhds <| by
    rw [hfv, inv_inv, ← Units.smul_def, ha]
    exact hO.mem_nhds hAO
  filter_upwards [(continuous_subtype_val.tendsto
    (⟨v, hv⟩ : {v : Matrix n n ℂ // v ≠ 0})).eventually
      (h₁.and (hcont.continuousAt.eventually_ne hv0))] with ⟨w, hw⟩ ⟨hwO, hw0⟩
  -- Near `v`, the normalized matrix has determinant one and lies in `O`.
  obtain ⟨B, hB, hBw⟩ := exists_coe_eq_inv_smul_of_pow_eq_det hw
    (fun h ↦ hw0 (by rw [← hfk w.det, h, zero_pow hk])) (hfk w.det)
  refine ⟨B, (Set.ext_iff.1 hOU B).1 (by rwa [← hB] at hwO), ?_⟩
  rw [Projectivization.mk'_eq_mk]
  exact hBw

/-- `PSL(n, ℂ)` is an open subset of the projective space of `n × n` matrices. -/
theorem isOpenEmbedding_toProjectivization : IsOpenEmbedding (toProjectivization n ℂ) :=
  .of_continuous_injective_isOpenMap continuous_toProjectivization toProjectivization_injective
    isOpenMap_toProjectivization

variable (n) in
/-- The homeomorphism of `PSL(n, ℂ)` with the open locus of lines of invertible matrices in the
projective space of `n × n` matrices; for `n = 2` this is the complement of the determinant quadric
in `ℂℙ³`. It sends the class of `A` to the line of `A`. -/
noncomputable def homeomorphDetNeZero :
    ProjectiveSpecialLinearGroup n ℂ ≃ₜ {x : ℙ ℂ (Matrix n n ℂ) // x.rep.det ≠ 0} :=
  isOpenEmbedding_toProjectivization.toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_toProjectivization)

@[simp]
theorem coe_homeomorphDetNeZero_apply (g : ProjectiveSpecialLinearGroup n ℂ) :
    (homeomorphDetNeZero n g : ℙ ℂ (Matrix n n ℂ)) = toProjectivization n ℂ g :=
  (rfl)

/-- The inverse of `homeomorphDetNeZero` sends the line of an invertible matrix `A` to the class of
any matrix of `SL(n, ℂ)` proportional to `A`. -/
theorem homeomorphDetNeZero_symm_mk {A : Matrix n n ℂ} (hA : A ≠ 0)
    (h : (Projectivization.mk ℂ A hA).rep.det ≠ 0) (B : SpecialLinearGroup n ℂ) {c : ℂ}
    (hB : (B : Matrix n n ℂ) = c • A) :
    (homeomorphDetNeZero n).symm ⟨_, h⟩ = B := by
  rw [Homeomorph.symm_apply_eq]
  ext1
  rw [coe_homeomorphDetNeZero_apply, toProjectivization_mk]
  exact ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c, hB.symm⟩).symm

end Complex

end ProjectiveSpecialLinearGroup

end Matrix
