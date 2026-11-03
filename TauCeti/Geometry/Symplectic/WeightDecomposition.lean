/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.PolarCompatible
public import TauCeti.Geometry.Symplectic.Restrict
import TauCeti.Geometry.Symplectic.Complex.JointEigenvector
import TauCeti.Geometry.Symplectic.Complex.Module.Hom
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Weight decompositions of symplectic representations of compact abelian groups

Let `π` be a continuous linear action of a compact commutative group `G` on a finite-dimensional
real space `E` preserving a symplectic form `ω`. This file proves that `π` splits into rotations of
complex lines: there are a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` of `(E, ω)` and continuous
characters `χ₁, …, χₙ : G → S¹` such that, writing `χₖ(g) = a + b i`,

`π g qₖ = a qₖ + b pₖ`,  `π g pₖ = -b qₖ + a pₖ`

(`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq`). In the complex coordinates
`zₖ = qₖ + i pₖ` dual to this basis, `ω = Σ dqₖ ∧ dpₖ` and `g` acts by `zₖ ↦ χₖ(g) zₖ`. This is
the weight decomposition of the isotropy representation of a compact torus at a fixed point of a
symplectic action, the linear input of the local model `TauCeti.weightRotation` near such a point.

The underlying algebraic statement is available separately
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute`). Its
hypotheses are a complex structure `J` compatible with `ω` and an arbitrary pairwise commuting
family `f` of `J`-complex-linear maps preserving `ω`, with no group, topology or norm. It yields a
Darboux basis with `pₖ = J qₖ` in which each `fᵢ` rotates every line `span(qₖ, J qₖ)` by a
complex number of modulus one. For a compact abelian group,
`TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap` supplies `J`, and continuity
of `π` makes the rotation numbers continuous characters of `G`.

No inner product on `E` is assumed and the characters need not be distinct: a character may occur
several times, and a trivial character marks a fixed direction.

## Main results

* `TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute`: a
  commuting family of complex-linear symplectic maps is simultaneously diagonal, by unit complex
  numbers, in a Darboux basis adapted to `J`.
* `TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq`: the weight decomposition of a
  symplectic representation of a compact commutative group.

## References

* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2 (weights of the isotropy representation at a fixed point).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 27.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter II (complex representations of compact abelian
  groups split into characters).
-/

public section

open Module

universe u

namespace TauCeti

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

namespace SymplecticForm

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-! ### The splitting induction -/

/-- A joint eigenvector of a commuting family of complex-linear maps, normalized by
`ω(q, J q) = 1`. -/
private theorem exists_jointEigenvector_apply_eq_one [FiniteDimensional ℝ V] [Nontrivial V]
    (hJ : ω.Compatible J) {ι : Type*} (f : ι → V →ₗ[ℝ] V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hfJ : ∀ i, IsComplexLinearMap J J (f i)) :
    ∃ (c : ι → ℂ) (q : V), ω q (J q) = 1 ∧ ∀ i, f i q = (c i).re • q + (c i).im • J q := by
  obtain ⟨c, v, hv, hcv⟩ := J.exists_jointEigenvector_of_pairwise_commute f hcomm hfJ
  have hr : 0 < ω v (J v) := hJ.tames v hv
  refine ⟨c, (Real.sqrt (ω v (J v)))⁻¹ • v, ?_, fun i ↦ ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne']
  · simp only [map_smul, hcv i, smul_add, smul_comm (Real.sqrt (ω v (J v)))⁻¹]

/-- A complex-linear symplectic map rotating the line `span(q, J q)` preserves its symplectic
complement: it maps the line onto itself. -/
private theorem mapsTo_orthogonal_span_pair {f : V →ₗ[ℝ] V} (hf : ∀ x y, ω (f x) (f y) = ω x y)
    (hfJ : IsComplexLinearMap J J f) {q : V} (hq : ω q (J q) = 1) {a b : ℝ}
    (h : f q = a • q + b • J q) :
    ∀ x ∈ ω.orthogonal (Submodule.span ℝ {q, J q}),
      f x ∈ ω.orthogonal (Submodule.span ℝ {q, J q}) := by
  intro x hx
  simp only [mem_orthogonal_span_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq] at hx ⊢
  have hab := sq_add_sq_eq_one_of_apply_eq hf hfJ (by rw [hq]; exact one_ne_zero) h
  have hJq := hfJ.apply_apply_eq_of_apply_eq h
  -- `q` and `J q` are the images of `a q - b J q` and `b q + a J q`.
  have h₁ : f (a • q - b • J q) = q := by
    rw [map_sub, map_smul, map_smul, h, hJq]
    linear_combination (norm := module) hab • q
  have h₂ : f (b • q + a • J q) = J q := by
    rw [map_add, map_smul, map_smul, h, hJq]
    linear_combination (norm := module) hab • J q
  have e₁ := hf (a • q - b • J q) x
  have e₂ := hf (b • q + a • J q) x
  rw [h₁] at e₁
  rw [h₂] at e₂
  beta_reduce at e₁ e₂
  rw [e₁, e₂]
  simp [hx.1, hx.2]

/-- For a `J`-invariant form, the symplectic complement of a complex line `span(q, J q)` is
`J`-invariant. -/
private theorem mapsTo_orthogonal_span_pair_apply (hJ : ω.Invariant J) (q : V) :
    ∀ x ∈ ω.orthogonal (Submodule.span ℝ {q, J q}),
      J x ∈ ω.orthogonal (Submodule.span ℝ {q, J q}) := by
  intro x hx
  simp only [mem_orthogonal_span_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq] at hx ⊢
  have hinv := (ω.invariant_iff J).1 hJ
  beta_reduce at hinv
  refine ⟨?_, by rw [hinv]; exact hx.1⟩
  rw [← hinv q (J x), J.apply_apply]
  simp [hx.2]

/-- The complex line `span(q, J q)` of a nonzero vector, with its basis `(q, J q)` indexed by
`Fin 1 × Fin 2`. -/
private noncomputable def lineBasis (J : AlmostComplexStructure V) {q : V} (hq : q ≠ 0) :
    Basis (Fin 1 × Fin 2) ℝ (Submodule.span ℝ ({q, J q} : Set V)) :=
  (Basis.span ((J.linearIndependent_pair hq).comp Prod.snd fun _ _ h ↦
      Prod.ext (Subsingleton.elim _ _) h)).map
    (LinearEquiv.ofEq _ _ (by rw [Prod.snd_surjective.range_comp, Matrix.range_cons_cons_empty]))

private theorem coe_lineBasis_apply (J : AlmostComplexStructure V) {q : V} (hq : q ≠ 0)
    (k : Fin 1 × Fin 2) : (lineBasis J hq k : V) = ![q, J q] k.2 := by
  simp [lineBasis, Basis.span_apply]

/-- The induction on the dimension behind
`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute`: split off the
complex line of a joint eigenvector and recurse on its symplectic complement. -/
private theorem exists_isDarbouxBasis_aux {ι : Type*} (n : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
      (ω : SymplecticForm U) (J : AlmostComplexStructure U) (f : ι → U →ₗ[ℝ] U),
      ω.Compatible J → (Pairwise fun i j ↦ Commute (f i) (f j)) →
      (∀ i x y, ω (f i x) (f i y) = ω x y) → (∀ i, IsComplexLinearMap J J (f i)) →
      finrank ℝ U ≤ n →
      ∃ (m : ℕ) (b : Basis (Fin m × Fin 2) ℝ U), ω.IsDarbouxBasis b ∧
        (∀ k, b (k, 1) = J (b (k, 0))) ∧
        ∀ i k, ∃ c : ℂ, f i (b (k, 0)) = c.re • b (k, 0) + c.im • b (k, 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ _ _ ω J f hJ hcomm hf hfJ hn
  rcases subsingleton_or_nontrivial U with _ | _
  · exact ⟨0, Basis.empty _, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩,
      fun k ↦ k.elim0, fun _ k ↦ k.elim0⟩
  -- Over `ℂ` the family has a joint eigenvector `q`. Its complex line `span(q, J q)` and the
  -- symplectic complement of that line are invariant, and the complement is again a symplectic
  -- space with a compatible complex structure, of smaller dimension.
  obtain ⟨c, q, hqJq, hcq⟩ := exists_jointEigenvector_apply_eq_one hJ f hcomm hfJ
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hqJq
  -- The line `span(q, J q)` and its symplectic complement `W`, invariant under `J` and `f`.
  have hcompl : IsCompl (Submodule.span ℝ {q, J q}) (ω.orthogonal (Submodule.span ℝ {q, J q})) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint ω.isRefl).2
      (ω.disjoint_span_pair_orthogonal (by rw [hqJq]; exact one_ne_zero))
  have hWf (i : ι) := mapsTo_orthogonal_span_pair (hf i) (hfJ i) hqJq (hcq i)
  have hWJ := mapsTo_orthogonal_span_pair_apply hJ.invariant q
  let JW := J.restrict _ hWJ
  let ωW := ω.restrict (ω.orthogonal (Submodule.span ℝ {q, J q}))
    (ω.nondegenerate_restrict_orthogonal_of_isCompl hcompl)
  let fW (i : ι) := (f i).restrict (hWf i)
  have hJW : ωW.Compatible JW := hJ.restrict _ _ hWJ
  have hcommW : Pairwise fun i j ↦ Commute (fW i) (fW j) := fun i j hij ↦
    LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun (hcomm hij).eq x)
  have hfJW (i : ι) : IsComplexLinearMap JW JW (fW i) :=
    (isComplexLinearMap_iff_apply _ _ _).2 fun x ↦
      Subtype.ext (by simp [JW, fW, (isComplexLinearMap_iff_apply _ _ _).1 (hfJ i)])
  have hqP : q ∈ Submodule.span ℝ {q, J q} := Submodule.subset_span (by simp)
  have hlt : finrank ℝ (ω.orthogonal (Submodule.span ℝ {q, J q})) < finrank ℝ U := by
    rw [ω.finrank_orthogonal]
    have hUpos : 0 < finrank ℝ U := Module.finrank_pos_iff_exists_ne_zero.2 ⟨q, hq⟩
    have hPpos : 0 < finrank ℝ (Submodule.span ℝ {q, J q}) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨q, hqP⟩, by simpa using hq⟩
    omega
  obtain ⟨m, bW, hbW, hJbW, hrotW⟩ :=
    ih _ (lt_of_lt_of_le hlt hn) ωW JW fW hJW hcommW (fun i x y ↦ hf i x y) hfJW le_rfl
  -- The basis `(q, J q)` of the line is a Darboux basis of the restriction of `ω`.
  have hbP : (ω.restrict (Submodule.span ℝ {q, J q})
      (ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl
        hcompl.disjoint)).IsDarbouxBasis (lineBasis J hq) := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simp [coe_lineBasis_apply]
    · simp [coe_lineBasis_apply]
    · obtain rfl := Subsingleton.elim i j
      simp [coe_lineBasis_apply, hqJq]
  -- Concatenate the bases of the line and of `W` along their direct sum.
  let σ : (Fin 1 × Fin 2) ⊕ (Fin m × Fin 2) ≃ Fin (1 + m) × Fin 2 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  let b := (((lineBasis J hq).prod bW).reindex σ).map (Submodule.prodEquivOfIsCompl _ _ hcompl)
  have hb : ω.IsDarbouxBasis b :=
    (hbP.prod hbW).map (ω.isSymplectomorphism_prodEquivOfIsCompl hcompl)
  have hbl (a : Fin 2) : b (Fin.castAdd m 0, a) = ![q, J q] a := by
    simp [b, σ, Basis.reindex_apply, coe_lineBasis_apply]
  have hbr (j : Fin m) (a : Fin 2) : b (Fin.natAdd 1 j, a) = (bW (j, a) : U) := by
    simp [b, σ, Basis.reindex_apply]
  refine ⟨1 + m, b, hb, fun k ↦ ?_, fun i k ↦ ?_⟩
  · induction k using Fin.addCases with
    | left k =>
      obtain rfl := Subsingleton.elim k 0
      simp [hbl]
    | right j =>
      rw [hbr, hbr, hJbW j, AlmostComplexStructure.coe_restrict_apply]
  · induction k using Fin.addCases with
    | left k =>
      obtain rfl := Subsingleton.elim k 0
      exact ⟨c i, by simp [hbl, hcq i]⟩
    | right j =>
      obtain ⟨c', hc'⟩ := hrotW i j
      refine ⟨c', ?_⟩
      simpa [hbr, fW] using congrArg Subtype.val hc'

/-! ### Simultaneous diagonalization -/

/-- **Simultaneous diagonalization of commuting complex-linear symplectic maps.** Let `J` be a
complex structure compatible with a symplectic form `ω` on a finite-dimensional space, and let
`f` be a pairwise commuting family of `J`-complex-linear maps preserving `ω`. Then there is a
Darboux basis `(q₁, p₁, …, qₙ, pₙ)` with `pₖ = J qₖ` in which every `f i` rotates every line
`span(qₖ, pₖ)` by a unit complex number `c i k = a + b i`:
`f i qₖ = a qₖ + b pₖ` and `f i pₖ = -b qₖ + a pₖ`. -/
theorem exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute [FiniteDimensional ℝ V]
    (hJ : ω.Compatible J) {ι : Type*} (f : ι → V →ₗ[ℝ] V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hf : ∀ i x y, ω (f i x) (f i y) = ω x y)
    (hfJ : ∀ i, IsComplexLinearMap J J (f i)) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (c : ι → Fin n → Circle), ω.IsDarbouxBasis b ∧
      (∀ k, b (k, 1) = J (b (k, 0))) ∧ ∀ i k,
        f i (b (k, 0)) = (c i k : ℂ).re • b (k, 0) + (c i k : ℂ).im • b (k, 1) ∧
        f i (b (k, 1)) = -(c i k : ℂ).im • b (k, 0) + (c i k : ℂ).re • b (k, 1) := by
  obtain ⟨n, b, hb, hbJ, hc⟩ := exists_isDarbouxBasis_aux _ ω J f hJ hcomm hf hfJ le_rfl
  choose c hc using hc
  have hq (k : Fin n) : ω (b (k, 0)) (J (b (k, 0))) ≠ 0 := by
    rw [← hbJ, hb.apply_fst_snd]
    simp
  have hnorm (i : ι) (k : Fin n) : ‖c i k‖ = 1 := by
    have h := sq_add_sq_eq_one_of_apply_eq (hf i) (hfJ i) (hq k) (by rw [hc i k, hbJ])
    rw [Complex.norm_def, Complex.normSq_apply, ← sq, ← sq, h, Real.sqrt_one]
  let χ (i : ι) (k : Fin n) : Circle := ⟨c i k, mem_sphere_zero_iff_norm.2 (hnorm i k)⟩
  have hχ (i : ι) (k : Fin n) : (χ i k : ℂ) = c i k := rfl
  refine ⟨n, b, χ, hb, hbJ, fun i k ↦ ⟨by rw [hχ, hc i k], ?_⟩⟩
  rw [hχ, hbJ k, (hfJ i).apply_apply_eq_of_apply_eq (by rw [hc i k, hbJ]), neg_smul]

/-- **Weight decomposition of a symplectic representation of a compact abelian group.** A
continuous linear action `π` of a compact commutative group `G` on a finite-dimensional real space
preserving a symplectic form `ω` is a sum of rotations of complex lines: there are a Darboux basis
`(q₁, p₁, …, qₙ, pₙ)` of `ω` and continuous characters `χₖ : G →ₜ* Circle` with
`π g qₖ = a qₖ + b pₖ` and `π g pₖ = -b qₖ + a pₖ`, where `χₖ g = a + b i`. -/
theorem exists_isDarbouxBasis_forall_apply_eq {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (ω : SymplecticForm E)
    (π : ContRepresentation ℝ G E) (hπ : Continuous π)
    (hω : ∀ g u v, ω (π g u) (π g v) = ω u v) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ E) (χ : Fin n → G →ₜ* Circle), ω.IsDarbouxBasis b ∧
      ∀ g k, π g (b (k, 0)) = (χ k g : ℂ).re • b (k, 0) + (χ k g : ℂ).im • b (k, 1) ∧
        π g (b (k, 1)) = -(χ k g : ℂ).im • b (k, 0) + (χ k g : ℂ).re • b (k, 1) := by
  obtain ⟨J, hJ, hπJ⟩ := ω.exists_compatible_forall_isComplexLinearMap π hπ hω
  obtain ⟨n, b, c, hb, hbJ, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute hJ
    (fun g ↦ (π g : E →ₗ[ℝ] E))
    (fun g h _ ↦ ((Commute.all g h).map π).map ContinuousLinearMap.toLinearMapRingHom)
    hω hπJ
  simp only [ContinuousLinearMap.coe_coe] at hc
  -- The rotation numbers are read off by pairing with the Darboux basis.
  have hre (g : G) (k : Fin n) : (c g k : ℂ).re = ω (π g (b (k, 0))) (b (k, 1)) := by
    rw [(hc g k).1]
    simp [hb.apply_fst_snd]
  have him (g : G) (k : Fin n) : (c g k : ℂ).im = ω (b (k, 0)) (π g (b (k, 0))) := by
    rw [(hc g k).1]
    simp [hb.apply_fst_snd, hb.apply_fst_fst]
  have hcont (k : Fin n) : Continuous fun g ↦ (c g k : ℂ) := by
    have h₁ : Continuous fun g ↦ ω (π g (b (k, 0))) (b (k, 1)) :=
      (ω.toBilinForm.flip (b (k, 1))).continuous_of_finiteDimensional.comp
        ((ContinuousLinearMap.apply ℝ E (b (k, 0))).continuous.comp hπ)
    have h₂ : Continuous fun g ↦ ω (b (k, 0)) (π g (b (k, 0))) :=
      (ω.toBilinForm (b (k, 0))).continuous_of_finiteDimensional.comp
        ((ContinuousLinearMap.apply ℝ E (b (k, 0))).continuous.comp hπ)
    have h : (fun g ↦ (c g k : ℂ)) =
        fun g ↦ (ω (π g (b (k, 0))) (b (k, 1)) : ℂ) + (ω (b (k, 0)) (π g (b (k, 0))) : ℂ) *
          Complex.I := by
      funext g
      rw [← hre, ← him, Complex.re_add_im]
    rw [h]
    exact (Complex.continuous_ofReal.comp h₁).add
      ((Complex.continuous_ofReal.comp h₂).mul continuous_const)
  -- In the complex structure `J`, each `b (k, 0)` is a joint eigenvector of the `π g` with
  -- eigenvalues `c g k`, so these are multiplicative in `g`.
  let := J.complexModule
  have := J.complexModule_isScalarTower
  let ρ : G →* Module.End ℂ E :=
    { toFun := fun g ↦ (hπJ g).toComplexLinearMap
      map_one' := LinearMap.ext fun x ↦ by simp
      map_mul' := fun g h ↦ LinearMap.ext fun x ↦ by simp }
  have hmem (k : Fin n) (g : G) : b (k, 0) ∈ (ρ g).eigenspace (c g k : ℂ) := by
    rw [Module.End.mem_eigenspace_iff, J.complexModule_smul_def, ← hbJ]
    exact (hc g k).1
  let χ (k : Fin n) : G →ₜ* Circle :=
    { toFun := fun g ↦ c g k
      map_one' := Circle.ext <| ρ.eigenvalue_one_of_jointEigenvector _ _ (b.ne_zero _) (hmem k)
      map_mul' := fun g h ↦
        Circle.ext <| ρ.eigenvalue_mul_of_jointEigenvector _ _ (b.ne_zero _) (hmem k) g h
      continuous_toFun := Topology.IsInducing.subtypeVal.continuous_iff.2 (hcont k) }
  exact ⟨n, b, χ, hb, fun g k ↦ hc g k⟩

end SymplecticForm

end TauCeti
