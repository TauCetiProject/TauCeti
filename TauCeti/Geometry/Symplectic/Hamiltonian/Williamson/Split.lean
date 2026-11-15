/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Nondegenerate

import Mathlib.LinearAlgebra.Eigenspace.Pi
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral
import TauCeti.Geometry.Symplectic.Restrict
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# Williamson's classification of split Cartan subalgebras of `sp(V, ω)`

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the Hamiltonian
endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`; these are the Hessian data
of the nondegenerate rank-zero singular points of integrable systems. Williamson's theorem sorts
such subalgebras into elliptic, hyperbolic and focus-focus blocks. This file proves the
classification in the **split** case, where every `A_{Q i}` has real spectrum (its generalized
eigenspaces span `V`): such a family spans the same space of quadratic forms as the hyperbolic
blocks `Hₖ = xₖ yₖ` (`TauCeti.SymplecticForm.hyperbolic`) of some Darboux basis
`(q₁, p₁, …, qₙ, pₙ)`
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic`).
Conversely the span of the hyperbolic blocks of a Darboux basis is nondegenerate and split, so this
characterizes the split nondegenerate families
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_span_eq_span_hyperbolic_iff`).

The linear algebra behind it is a simultaneous normal form
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint`). A pairwise
commuting family `f` of semisimple elements of `sp(V, ω)` with real spectra is diagonal in a
Darboux basis, with opposite eigenvalues on each pair:

`f i qₖ = c i k • qₖ`,  `f i pₖ = -c i k • pₖ`.

Indeed the family has a joint eigenvector `q`, with eigenvalues `χ`. Since `ω (f i u) v =
-ω u (f i v)`, the form `ω` pairs the joint eigenspaces for `χ` and `ψ` trivially unless
`ψ = -χ`; as the joint eigenspaces span `V` and `ω` is nondegenerate, some joint eigenvector `p`
for `-χ` has `ω(q, p) = 1`. The plane `span(q, p)` and its symplectic complement are invariant, so
the construction recurses on the complement. No hypothesis on the eigenvalues is needed: the zero
eigenvalue is allowed, and then `f i` vanishes on the corresponding pair.

For a nondegenerate family the members are semisimple and commute
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.isSemisimple_hamiltonianEnd`), so in such
a basis every `A_{Q i}` is `∑ₖ c i k A_{Hₖ}`, that is `Q i = ∑ₖ c i k Hₖ`. The hyperbolic blocks
Poisson-commute with these, and the span of a nondegenerate family is its own Poisson centralizer
(`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero`), so the two
spans agree. All names are in the namespace `TauCeti.SymplecticForm`.

## Main results

* `TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint`: commuting
  semisimple elements of `sp(V, ω)` with real spectra are simultaneously diagonal in a Darboux
  basis, with opposite eigenvalues on `qₖ` and `pₖ`.
* `TauCeti.SymplecticForm.IsDarbouxBasis.eq_sum_smul_hyperbolic_of_hamiltonianEnd_apply`: a form
  whose Hamiltonian endomorphism scales `qₖ` by `cₖ` and `pₖ` by `-cₖ` is `∑ₖ cₖ Hₖ`.
* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic`: a nondegenerate
  family with real spectra spans the hyperbolic blocks of a Darboux basis.
* `TauCeti.SymplecticForm.exists_isDarbouxBasis_span_eq_span_hyperbolic_iff`: a family spans the
  hyperbolic blocks of some Darboux basis exactly when it is nondegenerate with real spectra.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module

universe u

namespace TauCeti.SymplecticForm

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-! ### Simultaneous hyperbolic normal form -/

section NormalForm

/-- The basis `(q, p)` of the plane spanned by a pair with `ω(q, p) = 1`, indexed as a Darboux
basis of a plane. -/
private noncomputable def planeBasis {q p : V} (h : ω q p = 1) :
    Basis (Fin 1 × Fin 2) ℝ (Submodule.span ℝ ({q, p} : Set V)) :=
  (Basis.span ((LinearIndependent.pair_symm_iff.1
      (ω.isAlt.linearIndependent_pair_of_apply_eq_one h)).comp Prod.snd fun _ _ h ↦
        Prod.ext (Subsingleton.elim _ _) h)).map
    (LinearEquiv.ofEq _ _ (by rw [Prod.snd_surjective.range_comp, Matrix.range_cons_cons_empty]))

private theorem coe_planeBasis_apply {q p : V} (h : ω q p = 1) (k : Fin 1 × Fin 2) :
    (planeBasis h k : V) = ![q, p] k.2 := by
  simp [planeBasis, Basis.span_apply]

/-- The basis `(q, p)` of a pair with `ω(q, p) = 1` is a Darboux basis of the restriction of `ω` to
their plane. -/
private theorem isDarbouxBasis_restrict_planeBasis {q p : V} (h : ω q p = 1)
    (hcompl : IsCompl (Submodule.span ℝ {q, p}) (ω.orthogonal (Submodule.span ℝ {q, p}))) :
    (ω.restrict (Submodule.span ℝ {q, p})
      (ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl
        hcompl.disjoint)).IsDarbouxBasis (planeBasis h) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
  · simp [coe_planeBasis_apply]
  · simp [coe_planeBasis_apply]
  · obtain rfl := Subsingleton.elim i j
    simp [coe_planeBasis_apply, h]

/-- The symplectic complement of a plane spanned by a pair with nonzero pairing has smaller
dimension than the ambient space. -/
private theorem finrank_orthogonal_span_pair_lt [FiniteDimensional ℝ V] {q p : V}
    (h : ω q p ≠ 0) : finrank ℝ (ω.orthogonal (Submodule.span ℝ {q, p})) < finrank ℝ V := by
  have hq : q ≠ 0 := by rintro rfl; simp at h
  rw [ω.finrank_orthogonal]
  have hUpos : 0 < finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨q, hq⟩
  have hPpos : 0 < finrank ℝ (Submodule.span ℝ {q, p}) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨q, Submodule.subset_span (by simp)⟩, by simpa using hq⟩
  omega

/-- In a space spanned by the joint eigenspaces of a family `f` of elements of `sp(V, ω)`, a joint
eigenvector `q` with eigenvalues `χ` has a partner `p`, a joint eigenvector with the opposite
eigenvalues `-χ`, with `ω(q, p) = 1`. -/
private theorem exists_apply_eq_one_forall_apply_eq_neg_smul {ι : Type*}
    {f : ι → Module.End ℝ V} (hf : ∀ i v w, ω (f i v) w = -ω v (f i w))
    (hspan : ⨆ χ : ι → ℝ, ⨅ i, (f i).eigenspace (χ i) = ⊤) {χ : ι → ℝ} {q : V} (hq : q ≠ 0)
    (hχ : ∀ i, f i q = χ i • q) : ∃ p : V, ω q p = 1 ∧ ∀ i, f i p = -χ i • p := by
  -- Some joint eigenvector `w` pairs nontrivially with `q`, as `ω (q, ·)` is nonzero and the joint
  -- eigenspaces span.
  obtain ⟨ψ, w, hw, hqw⟩ : ∃ (ψ : ι → ℝ) (w : V),
      w ∈ ⨅ i, (f i).eigenspace (ψ i) ∧ ω q w ≠ 0 := by
    by_contra! hzero
    refine hq (ω.nondegenerate.1 q fun v ↦ ?_)
    have hv : v ∈ ⨆ ψ : ι → ℝ, ⨅ i, (f i).eigenspace (ψ i) := hspan ▸ Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun v ↦ ω.toBilinForm q v = 0) hv
      (fun ψ w hw ↦ hzero ψ w hw) (map_zero _) fun x y hx hy ↦ ?_
    rw [map_add, hx, hy, add_zero]
  have hwψ (i : ι) : f i w = ψ i • w :=
    Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 hw i)
  -- Pairing with `q` forces the eigenvalues of `w` to be opposite to those of `q`.
  have hψ (i : ι) : ψ i = -χ i := by
    have h := hf i q w
    beta_reduce at h hqw
    rw [hχ i, hwψ i, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h
    have h' : (χ i + ψ i) * ω.toBilinForm q w = 0 := by linear_combination h
    linear_combination (mul_eq_zero.1 h').resolve_right hqw
  refine ⟨(ω q w)⁻¹ • w, ?_, fun i ↦ ?_⟩
  · beta_reduce
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hqw
  · rw [map_smul, hwψ i, hψ i, smul_comm]

/-- An element of `sp(V, ω)` acting on `q` and `p` by opposite scalars preserves the symplectic
complement of their plane. -/
private theorem mapsTo_orthogonal_span_pair {A : Module.End ℝ V}
    (hA : ∀ v w, ω (A v) w = -ω v (A w)) {q p : V} {c : ℝ} (hq : A q = c • q)
    (hp : A p = -c • p) :
    ∀ x ∈ ω.orthogonal (Submodule.span ℝ {q, p}),
      A x ∈ ω.orthogonal (Submodule.span ℝ {q, p}) := by
  intro x hx
  simp only [mem_orthogonal_span_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq] at hx ⊢
  beta_reduce at hA
  refine ⟨?_, ?_⟩
  · rw [← neg_neg (ω.toBilinForm q (A x)), ← hA, hq]
    simp [hx.1]
  · rw [← neg_neg (ω.toBilinForm p (A x)), ← hA, hp]
    simp [hx.2]

/-- Splitting off a symplectic plane: if the family `f` acts on a pair `(q, p)` with
`ω(q, p) = 1` by opposite scalars `χ` and `-χ`, and is diagonal, with opposite eigenvalues on each
pair, in a Darboux basis of the symplectic complement of their plane, then it is so in a Darboux
basis of `V` starting with `(q, p)`. -/
private theorem exists_isDarbouxBasis_of_isDarbouxBasis_orthogonal {ι : Type*}
    {f : ι → Module.End ℝ V} {q p : V} (hqp : ω q p = 1)
    (hcompl : IsCompl (Submodule.span ℝ {q, p}) (ω.orthogonal (Submodule.span ℝ {q, p})))
    (hWf : ∀ i, ∀ x ∈ ω.orthogonal (Submodule.span ℝ {q, p}),
      f i x ∈ ω.orthogonal (Submodule.span ℝ {q, p}))
    {χ : ι → ℝ} (hq : ∀ i, f i q = χ i • q) (hp : ∀ i, f i p = -χ i • p) {m : ℕ}
    {bW : Basis (Fin m × Fin 2) ℝ (ω.orthogonal (Submodule.span ℝ {q, p}))}
    (hbW : (ω.restrict _ (ω.nondegenerate_restrict_orthogonal_of_isCompl hcompl)).IsDarbouxBasis bW)
    {cW : ι → Fin m → ℝ}
    (hcW : ∀ i k, (f i).restrict (hWf i) (bW (k, 0)) = cW i k • bW (k, 0) ∧
      (f i).restrict (hWf i) (bW (k, 1)) = -cW i k • bW (k, 1)) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (c : ι → Fin n → ℝ), ω.IsDarbouxBasis b ∧
      ∀ i k, f i (b (k, 0)) = c i k • b (k, 0) ∧ f i (b (k, 1)) = -c i k • b (k, 1) := by
  -- Concatenate the bases of the plane and of its complement along their direct sum.
  let σ : (Fin 1 × Fin 2) ⊕ (Fin m × Fin 2) ≃ Fin (1 + m) × Fin 2 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  let b := (((planeBasis hqp).prod bW).reindex σ).map (Submodule.prodEquivOfIsCompl _ _ hcompl)
  have hb : ω.IsDarbouxBasis b :=
    ((isDarbouxBasis_restrict_planeBasis hqp hcompl).prod hbW).map
      (ω.isSymplectomorphism_prodEquivOfIsCompl hcompl)
  have hbl (a : Fin 2) : b (Fin.castAdd m 0, a) = ![q, p] a := by
    simp [b, σ, Basis.reindex_apply, coe_planeBasis_apply]
  have hbr (j : Fin m) (a : Fin 2) : b (Fin.natAdd 1 j, a) = (bW (j, a) : V) := by
    simp [b, σ, Basis.reindex_apply]
  let c : ι → Fin (1 + m) → ℝ := fun i ↦ Fin.addCases (fun _ ↦ χ i) (cW i)
  refine ⟨1 + m, b, c, hb, fun i k ↦ ?_⟩
  induction k using Fin.addCases with
  | left k =>
    obtain rfl := Subsingleton.elim k 0
    simp only [c, Fin.addCases_left, hbl]
    exact ⟨by simpa using hq i, by simpa using hp i⟩
  | right j =>
    simp only [c, Fin.addCases_right, hbr]
    obtain ⟨h₀, h₁⟩ := hcW i j
    exact ⟨by simpa using congrArg Subtype.val h₀, by simpa using congrArg Subtype.val h₁⟩

/-- The induction on the dimension behind
`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint`: split off the
plane of a joint eigenvector and its partner, and recurse on its symplectic complement. -/
private theorem exists_isDarbouxBasis_aux {ι : Type*} (n : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
      (ω : SymplecticForm U) (f : ι → Module.End ℝ U),
      (∀ i v w, ω (f i v) w = -ω v (f i w)) → (Pairwise fun i j ↦ Commute (f i) (f j)) →
      (∀ i, (f i).IsSemisimple) → (∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) →
      finrank ℝ U ≤ n →
      ∃ (m : ℕ) (b : Basis (Fin m × Fin 2) ℝ U) (c : ι → Fin m → ℝ), ω.IsDarbouxBasis b ∧
        ∀ i k, f i (b (k, 0)) = c i k • b (k, 0) ∧ f i (b (k, 1)) = -c i k • b (k, 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ _ _ ω f hf hcomm hss hsplit hn
  rcases subsingleton_or_nontrivial U with _ | _
  · exact ⟨0, Basis.empty _, fun _ k ↦ k.elim0,
      ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩, fun _ k ↦ k.elim0⟩
  -- The family is simultaneously diagonalizable: its joint eigenspaces span `U`.
  have heq (i : ι) (μ : ℝ) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hspan : ⨆ χ : ι → ℝ, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
        hcomm hsplit
  -- A joint eigenvector `q` and its partner `p` span an invariant symplectic plane.
  obtain ⟨χ, q, hq, hqχ⟩ := exists_jointEigenvector_of_pairwise_commute f hcomm hsplit
  have hχ (i : ι) : f i q = χ i • q := Module.End.mem_eigenspace_iff.1 (hqχ i)
  obtain ⟨p, hqp, hpχ⟩ := exists_apply_eq_one_forall_apply_eq_neg_smul hf hspan hq hχ
  have hqp0 : ω q p ≠ 0 := by rw [hqp]; exact one_ne_zero
  have hcompl : IsCompl (Submodule.span ℝ {q, p}) (ω.orthogonal (Submodule.span ℝ {q, p})) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint ω.isRefl).2
      (ω.disjoint_span_pair_orthogonal hqp0)
  -- Its symplectic complement `W` is invariant, and the restricted family satisfies the same
  -- hypotheses in smaller dimension.
  have hWf (i : ι) := mapsTo_orthogonal_span_pair (hf i) (hχ i) (hpχ i)
  let ωW := ω.restrict (ω.orthogonal (Submodule.span ℝ {q, p}))
    (ω.nondegenerate_restrict_orthogonal_of_isCompl hcompl)
  let fW (i : ι) : Module.End ℝ (ω.orthogonal (Submodule.span ℝ {q, p})) :=
    (f i).restrict (hWf i)
  have hfW (i : ι) (v w : ω.orthogonal (Submodule.span ℝ {q, p})) :
      ωW (fW i v) w = -ωW v (fW i w) := by
    simpa [ωW, fW] using hf i v w
  have hcommW : Pairwise fun i j ↦ Commute (fW i) (fW j) := fun i j hij ↦
    LinearMap.restrict_commute (hcomm hij) (hWf i) (hWf j)
  have hssW (i : ι) : Module.End.IsSemisimple (fW i) :=
    (hss i).restrict (Module.End.mem_invtSubmodule _ |>.2 fun x hx ↦ hWf i x hx)
  have hsplitW (i : ι) : ⨆ μ, Module.End.maxGenEigenspace (fW i) μ = ⊤ :=
    Module.End.genEigenspace_restrict_eq_top (hWf i) (hsplit i)
  obtain ⟨m, bW, cW, hbW, hcW⟩ :=
    ih _ (lt_of_lt_of_le (finrank_orthogonal_span_pair_lt hqp0) hn) ωW fW hfW hcommW hssW
      hsplitW le_rfl
  exact exists_isDarbouxBasis_of_isDarbouxBasis_orthogonal hqp hcompl hWf hχ hpχ hbW hcW

/-- **Simultaneous hyperbolic normal form.** A pairwise commuting family `f` of semisimple
elements of `sp(V, ω)` whose spectra are real (their generalized eigenspaces span `V`) is
simultaneously diagonal in a Darboux basis `(q₁, p₁, …, qₙ, pₙ)`, with opposite eigenvalues on
each pair: `f i qₖ = c i k • qₖ` and `f i pₖ = -c i k • pₖ`. -/
theorem exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint [FiniteDimensional ℝ V]
    {ι : Type*} (f : ι → Module.End ℝ V) (hf : ∀ i, f i ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple)
    (hsplit : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (c : ι → Fin n → ℝ), ω.IsDarbouxBasis b ∧
      ∀ i k, f i (b (k, 0)) = c i k • b (k, 0) ∧ f i (b (k, 1)) = -c i k • b (k, 1) :=
  exists_isDarbouxBasis_aux _ ω f
    (fun i v w ↦ by simpa using (LinearMap.mem_skewAdjointSubmodule _).1 (hf i) v w) hcomm hss
    hsplit le_rfl

end NormalForm

/-! ### Split nondegenerate families -/

section Split

variable [FiniteDimensional ℝ V] {ι : Type*} {Q : ι → QuadraticForm ℝ V} {n : ℕ}
  {b : Basis (Fin n × Fin 2) ℝ V}

/-- A quadratic form whose Hamiltonian endomorphism, in a Darboux basis, scales each `qₖ` by `cₖ`
and each `pₖ` by `-cₖ` is the combination `∑ₖ cₖ Hₖ` of the hyperbolic blocks. -/
theorem IsDarbouxBasis.eq_sum_smul_hyperbolic_of_hamiltonianEnd_apply (hb : ω.IsDarbouxBasis b)
    {R : QuadraticForm ℝ V} {c : Fin n → ℝ}
    (hR : ∀ k, ω.hamiltonianEnd R (b (k, 0)) = c k • b (k, 0) ∧
      ω.hamiltonianEnd R (b (k, 1)) = -c k • b (k, 1)) :
    R = ∑ k, c k • hyperbolic b k := by
  refine ω.hamiltonianEnd_injective (b.ext fun ⟨k, a⟩ ↦ ?_)
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · simpa [(hR k).1] using (hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst ∅ c k).symm
  · simpa [(hR k).2] using (hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd ∅ c k).symm

/-- **Williamson's theorem for split Cartan subalgebras.** A nondegenerate family of quadratic
forms whose Hamiltonian endomorphisms have real spectra (their generalized eigenspaces span `V`)
spans the same space of quadratic forms as the hyperbolic blocks `Hₖ = xₖ yₖ` of some Darboux
basis. -/
theorem IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic
    (h : ω.IsNondegenerateQuadraticFamily Q)
    (hsplit : ∀ i, ⨆ μ, (ω.hamiltonianEnd (Q i)).maxGenEigenspace μ = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (hyperbolic b)) := by
  obtain ⟨n, b, c, hb, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_smul_of_skewAdjoint
    (fun i ↦ ω.hamiltonianEnd (Q i)) (fun i ↦ ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra _)
    (fun i j _ ↦ (quadraticPoissonBracket_eq_zero_iff (ω := ω)).1
      (h.quadraticPoissonBracket_eq_zero i j))
    (fun i ↦ h.isSemisimple_hamiltonianEnd (Submodule.subset_span ⟨i, rfl⟩)) hsplit
  -- Each `Q i` is the combination `∑ₖ c i k Hₖ` of the hyperbolic blocks.
  have hQ (i : ι) : Q i ∈ Submodule.span ℝ (Set.range (hyperbolic b)) := by
    rw [hb.eq_sum_smul_hyperbolic_of_hamiltonianEnd_apply (hc i)]
    exact Submodule.sum_mem _ fun k _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  refine ⟨n, b, hb, le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hQ))
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ ?_))⟩
  -- Conversely each `Hₖ` Poisson-commutes with the `Q i`, so it lies in their span.
  exact h.mem_span_of_forall_quadraticPoissonBracket_eq_zero fun i ↦
    hb.isNondegenerateQuadraticFamily_hyperbolic.quadraticPoissonBracket_eq_zero_of_mem_span
      (Submodule.subset_span (Set.mem_range_self k)) (hQ i)

/-- **Classification of split nondegenerate families.** A family of quadratic forms spans the same
space as the hyperbolic blocks `Hₖ = xₖ yₖ` of some Darboux basis exactly when it is nondegenerate
and the Hamiltonian endomorphisms of its members have real spectra. -/
theorem exists_isDarbouxBasis_span_eq_span_hyperbolic_iff :
    (∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (hyperbolic b))) ↔
      ω.IsNondegenerateQuadraticFamily Q ∧
        ∀ i, ⨆ μ, (ω.hamiltonianEnd (Q i)).maxGenEigenspace μ = ⊤ := by
  refine ⟨?_, fun ⟨h, hsplit⟩ ↦ h.exists_isDarbouxBasis_span_eq_span_hyperbolic hsplit⟩
  rintro ⟨n, b, hb, hspan⟩
  refine ⟨(isNondegenerateQuadraticFamily_iff_of_span_eq hspan).2
    hb.isNondegenerateQuadraticFamily_hyperbolic, fun i ↦ ?_⟩
  -- Each `Q i` is a combination `∑ₖ cₖ Hₖ` of the hyperbolic blocks, hence diagonal in `b`.
  have hQ : Q i ∈ Submodule.span ℝ (Set.range (hyperbolic b)) := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hQ
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨⟨k, a⟩, rfl⟩
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · refine Submodule.mem_iSup_of_mem (c k) (Module.End.eigenspace_le_maxGenEigenspace
      (Module.End.mem_eigenspace_iff.2 ?_))
    simpa [← hc] using hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_fst ∅ c k
  · refine Submodule.mem_iSup_of_mem (-c k) (Module.End.eigenspace_le_maxGenEigenspace
      (Module.End.mem_eigenspace_iff.2 ?_))
    simpa [← hc] using hb.hamiltonianEnd_sum_smul_ellipticHyperbolic_apply_snd ∅ c k

end Split

end TauCeti.SymplecticForm
