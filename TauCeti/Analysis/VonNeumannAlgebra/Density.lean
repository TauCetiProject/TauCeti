/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace

/-!
# The von Neumann density theorem

Let `S` be a unital star subalgebra of the bounded operators on a Hilbert space `H` over `ℝ` or
`ℂ`. Every operator `x` in the double commutant `S''` is a strong-operator limit of elements of
`S`: for finitely many vectors `v i` and every `ε > 0` there is `s ∈ S` with
`‖x (v i) - s (v i)‖ < ε` for all `i`,
`StarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`.

For a single vector `v` this is `StarSubalgebra.apply_mem_closure_of_mem_centralizer_centralizer`.
The closure `K` of the orbit `S v` is invariant under `S`, and so is its orthogonal complement
because `S` is closed under adjoints. Hence the orthogonal projection onto `K` lies in the
commutant `S'` and commutes with `x`; since `v ∈ K`, this gives `x v ∈ K`.

Finitely many vectors are handled by amplification: `S` acts diagonally on the Hilbert sum
`PiLp 2 (fun _ : ι => H)`. Every operator on this sum commuting with the diagonal copy of `S` has
matrix entries in `S'`, so the diagonal copy of `x` lies in the double commutant of the diagonal
copy of `S`, and the single-vector case applies to the sum.

Simultaneous approximation on finitely many vectors is what lets an identity between vector
functionals `y ↦ ⟪u, y v⟫`, proved for `y` in the range `π(A)` of a representation, pass to the
von Neumann algebra `π(A)''` that it generates.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.1, for the
double commutant theorem and its amplification proof.
-/

public section

open scoped InnerProductSpace

namespace StarSubalgebra

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The von Neumann density theorem for one vector.** An operator in the double commutant of a
unital star subalgebra `S` maps each vector `v` into the closure of the orbit `S v`. -/
theorem apply_mem_closure_of_mem_centralizer_centralizer [CompleteSpace H]
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer) (v : H) :
    x v ∈ closure ((fun s : H →L[𝕜] H => s v) '' S) := by
  -- the closed subspace `K` spanned by the orbit `S v`
  set K : Submodule 𝕜 H :=
    (S.toSubalgebra.toSubmodule.map
      (ContinuousLinearMap.apply 𝕜 H v).toLinearMap).topologicalClosure with hK
  have hKcoe : (K : Set H) = closure ((fun s : H →L[𝕜] H => s v) '' S) := by
    rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
    -- the carrier of the submodule underlying `S` is the carrier of `S`
    rfl
  have hKc : IsClosed (K : Set H) := Submodule.isClosed_topologicalClosure _
  -- `K` is invariant under every element of `S`
  have hinv : ∀ t ∈ S, K ∈ Module.End.invtSubmodule (t : Module.End 𝕜 H) := by
    intro t ht
    rw [Module.End.mem_invtSubmodule]
    refine Submodule.topologicalClosure_minimal _ ?_ (hKc.preimage t.continuous)
    rintro _ ⟨s, hs, rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨t * s, S.mul_mem ht hs, rfl⟩
  -- since `S` is closed under adjoints, the orthogonal projection onto `K` commutes with `S`
  have hp : K.starProjection ∈ (S : Set (H →L[𝕜] H)).centralizer := by
    intro t ht
    have hadj : K ∈ Module.End.invtSubmodule (t.adjoint : Module.End 𝕜 H) := by
      simpa [← ContinuousLinearMap.star_eq_adjoint] using hinv (star t) (star_mem ht)
    have hred : K.IsReducing (t : Module.End 𝕜 H) :=
      ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr ⟨hinv t ht, hadj⟩
    exact (Submodule.isReducing_coe_iff_commute_starProjection.mp hred).eq.symm
  have hvK : v ∈ K := Submodule.le_topologicalClosure _ ⟨1, S.one_mem, rfl⟩
  have hcomm : K.starProjection (x v) = x (K.starProjection v) := by
    simpa using DFunLike.congr_fun (hx _ hp) v
  rw [← hKcoe, SetLike.mem_coe, ← K.starProjection_eq_self_iff.mpr hvK, ← hcomm]
  exact K.starProjection_apply_mem _

section Amplification

variable {ι : Type*} [Fintype ι]

variable (𝕜 H ι) in
/-- The diagonal action of an operator on the Hilbert sum of copies of `H` indexed by `ι`. -/
private noncomputable def diagCLM (s : H →L[𝕜] H) :
    PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.piMap (fun _ => s) ∘L
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).toContinuousLinearMap

omit [Fintype ι] in
private theorem diagCLM_apply (s : H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) (i : ι) :
    diagCLM 𝕜 H ι s w i = s (w i) :=
  rfl

section Entry

variable [DecidableEq ι]

/-- The `(i, j)` matrix entry of an operator on the Hilbert sum of copies of `H`. -/
private noncomputable def entry (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) : H →L[𝕜] H :=
  PiLp.proj 2 (fun _ : ι => H) i ∘L T ∘L
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single 𝕜 (fun _ : ι => H) j

omit [Fintype ι] in
private theorem entry_apply (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) (h : H) : entry T i j h = T (PiLp.single 2 j h) i :=
  rfl

/-- An operator on the Hilbert sum acts through its matrix entries. -/
private theorem apply_eq_sum_entry (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (w : PiLp 2 (fun _ : ι => H)) (i : ι) : T w i = ∑ j, entry T i j (w j) := by
  have hw : w = ∑ j, WithLp.toLp 2 (Pi.single j (w j)) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, entry_apply]

end Entry

variable [CompleteSpace H]

variable (𝕜 H ι) in
/-- The diagonal amplification `s ↦ s ⊕ ⋯ ⊕ s` as a star algebra homomorphism. -/
private noncomputable def diag :
    (H →L[𝕜] H) →⋆ₐ[𝕜] (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  toFun := diagCLM 𝕜 H ι
  map_one' := by ext; simp [diagCLM_apply]
  map_mul' s t := by ext; simp [diagCLM_apply]
  map_zero' := by ext; simp [diagCLM_apply]
  map_add' s t := by ext; simp [diagCLM_apply]
  commutes' r := by ext; simp [diagCLM_apply, Algebra.algebraMap_eq_smul_one]
  map_star' s := by
    simp only [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro w w'
    simp [PiLp.inner_apply, diagCLM_apply, ContinuousLinearMap.adjoint_inner_left]

private theorem diag_apply (s : H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) (i : ι) :
    diag 𝕜 H ι s w i = s (w i) :=
  rfl

/-- The diagonal amplification of an operator in `S''` lies in the double commutant of the
diagonal amplification of `S`. -/
private theorem diag_mem_centralizer_centralizer
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer) :
    diag 𝕜 H ι x ∈ (S.map (diag 𝕜 H ι) : Set _).centralizer.centralizer := by
  classical
  intro T hT
  -- the matrix entries of an operator commuting with the diagonal copy of `S` lie in `S'`
  have hentry (i j : ι) : entry T i j ∈ (S : Set (H →L[𝕜] H)).centralizer := by
    intro s hs
    have hsT := hT _ (StarSubalgebra.mem_map.mpr ⟨s, hs, rfl⟩)
    ext h
    have hdiag : diag 𝕜 H ι s (PiLp.single 2 j h) = PiLp.single 2 j (s h) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [diag_apply]
      · simp [diag_apply, hk]
    have h' := congr_arg (fun w => w i) (DFunLike.congr_fun hsT (PiLp.single 2 j h))
    simp only [mul_apply_eq_comp, diag_apply, hdiag] at h'
    simpa [entry_apply, mul_apply_eq_comp] using h'
  ext w i
  simp only [mul_apply_eq_comp]
  rw [apply_eq_sum_entry, diag_apply, apply_eq_sum_entry, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply]
  simpa using DFunLike.congr_fun (hx _ (hentry i j)) (w j)

end Amplification

/-- **The von Neumann density theorem.** An operator `x` in the double commutant of a unital star
subalgebra `S` of the bounded operators on a Hilbert space is a strong-operator limit of elements
of `S`: for every finite family of vectors `v i` and every `ε > 0` there is `s ∈ S` with
`‖x (v i) - s (v i)‖ < ε` for all `i`. -/
theorem exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer [CompleteSpace H]
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) {x : H →L[𝕜] H}
    (hx : x ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer) {ι : Type*} [Finite ι]
    (v : ι → H) {ε : ℝ} (hε : 0 < ε) : ∃ s ∈ S, ∀ i, ‖x (v i) - s (v i)‖ < ε := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨_, ⟨T, hT, rfl⟩, hlt⟩ := Metric.mem_closure_iff.mp
    ((S.map (diag 𝕜 H ι)).apply_mem_closure_of_mem_centralizer_centralizer
      (diag_mem_centralizer_centralizer S hx) (WithLp.toLp 2 v)) ε hε
  obtain ⟨s, hs, rfl⟩ := StarSubalgebra.mem_map.mp hT
  refine ⟨s, hs, fun i => ?_⟩
  beta_reduce at hlt
  rw [dist_eq_norm, ← sub_apply, ← map_sub] at hlt
  calc ‖x (v i) - s (v i)‖ = ‖diag 𝕜 H ι (x - s) (WithLp.toLp 2 v) i‖ := by simp [diag_apply]
    _ ≤ ‖diag 𝕜 H ι (x - s) (WithLp.toLp 2 v)‖ := PiLp.norm_apply_le _ _
    _ < ε := hlt

end StarSubalgebra
