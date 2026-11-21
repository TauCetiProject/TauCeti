/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.IsLocalHomeomorph
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local coordinates for polynomial equations

Over a complete nontrivially normed field, a square polynomial map with nonzero Jacobian
is a local homeomorphism. Applying this to the map consisting of the parameter coordinates
and the equations gives local coordinates on the ambient space `σ ⊕ ι → K` adapted to the
solution space. On the solution space, projection to the parameters is open on the locus
where the Jacobian in the remaining variables is invertible.

These statements use the coordinate topology and apply in positive characteristic as well.
They supply the local topological step in constructing charts for smooth algebraic varieties.
The inverse function theorem is Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`.
We restrict the ambient chart to the zero slice using `OpenPartialHomeomorph.subtypeCoord`.
-/

public section

open MvPolynomial Topology

namespace TauCeti

variable {K σ ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- A square polynomial map with nonzero Jacobian at `a` agrees with an open partial
homeomorphism whose source contains `a`. No characteristic-zero assumption is needed. -/
theorem exists_openPartialHomeomorph_eval_family [Fintype ι] [DecidableEq ι]
    (p : ι → MvPolynomial ι K) (a : ι → K) (ha : (jacobiMatrixAt p a).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ι → K) (ι → K),
      a ∈ e.source ∧ ∀ x, e x = fun i ↦ eval x (p i) := by
  classical
  let f := fun x : ι → K ↦ fun i ↦ eval x (p i)
  have hdet : (fderiv K f a).det ≠ 0 := by
    rwa [ContinuousLinearMap.det, fderiv_eval_family, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  let L := (fderiv K f a).toContinuousLinearEquivOfDetNeZero hdet
  have hf : HasStrictFDerivAt f (L : (ι → K) →L[K] (ι → K)) a := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (analyticOnNhd_eval_family p a (Set.mem_univ a)).hasStrictFDerivAt
  exact ⟨hf.toOpenPartialHomeomorph f, hf.mem_toOpenPartialHomeomorph_source,
    congrFun hf.toOpenPartialHomeomorph_coe⟩

section Parameters

variable [Fintype ι] [DecidableEq ι]

private theorem exists_openPartialHomeomorph_sumElim_eval_family_of_finite [Finite σ]
    (p : ι → MvPolynomial (σ ⊕ ι) K) (a : σ ⊕ ι → K)
    (ha : ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (σ ⊕ ι → K) (σ ⊕ ι → K),
      a ∈ e.source ∧ ∀ x, e x = Sum.elim (fun i ↦ x (Sum.inl i)) (fun i ↦ eval x (p i)) := by
  classical
  let := Fintype.ofFinite σ
  -- The supplemented polynomial map has an identity parameter block and a zero upper-right block.
  have hmatrix : jacobiMatrixAt (Sum.elim (fun i : σ ↦ X (Sum.inl i)) p) a =
      Matrix.fromBlocks 1 0 ((jacobiMatrixAt p a).submatrix id Sum.inl)
        ((jacobiMatrixAt p a).submatrix id Sum.inr) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, pderiv_X, Pi.single_apply, apply_ite, eq_comm]
  have hdet : (jacobiMatrixAt (Sum.elim (fun i : σ ↦ X (Sum.inl i)) p) a).det ≠ 0 := by
    simpa only [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul] using ha
  obtain ⟨e, he, hmap⟩ := exists_openPartialHomeomorph_eval_family
    (Sum.elim (fun i : σ ↦ X (Sum.inl i)) p) a hdet
  refine ⟨e, he, fun x ↦ ?_⟩
  rw [hmap]
  ext i
  cases i <;> simp

/-- At a point with invertible variable Jacobian, parameters and equations are local coordinates
on the ambient space. Only finitely many parameters occur in the equations; the remaining
coordinates are unchanged. -/
theorem exists_openPartialHomeomorph_sumElim_eval_family (p : ι → MvPolynomial (σ ⊕ ι) K)
    (a : σ ⊕ ι → K) (ha : ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (σ ⊕ ι → K) (σ ⊕ ι → K),
      a ∈ e.source ∧ ∀ x, e x = Sum.elim (fun i ↦ x (Sum.inl i)) (fun i ↦ eval x (p i)) := by
  classical
  let S := Finset.univ.biUnion fun i ↦ (p i).vars.preimage Sum.inl Sum.inl_injective.injOn
  let f : S ⊕ ι → σ ⊕ ι := Sum.map Subtype.val id
  have hf : Function.Injective f :=
    Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩
  have hf_inr (i : ι) : f (Sum.inr i) = Sum.inr i := rfl
  have hr (i : ι) : Sum.inr i ∈ Set.range f := ⟨Sum.inr i, hf_inr i⟩
  have hs (i : ι) : ↑(p i).vars ⊆ Set.range f := by
    rintro (s | j) hj
    · have hS : s ∈ S := Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_preimage.mpr hj⟩
      exact ⟨Sum.inl ⟨s, hS⟩, rfl⟩
    · exact hr j
  choose q hq using fun i ↦ exists_rename_eq_of_vars_subset_range (p i) f hf (hs i)
  have hdet : ((jacobiMatrixAt q (a ∘ f)).submatrix id Sum.inr).det ≠ 0 := by
    have hm : (jacobiMatrixAt q (a ∘ f)).submatrix id Sum.inr =
        (jacobiMatrixAt p a).submatrix id Sum.inr := by
      ext i j
      simp only [Matrix.submatrix_apply, id_eq, jacobiMatrixAt_apply]
      rw [← hq i, ← hf_inr j, pderiv_rename hf, eval_rename]
    rwa [hm]
  obtain ⟨e, he, hmap⟩ := exists_openPartialHomeomorph_sumElim_eval_family_of_finite q (a ∘ f) hdet
  -- Split off the unused coordinates and act by the identity on that factor.
  let h := (Homeomorph.piEquivPiSubtypeProd (· ∈ Set.range f) (fun _ ↦ K)).trans
    ((Homeomorph.piCongrLeft (Y := fun _ ↦ K) (Equiv.ofInjective f hf)).symm.prodCongr
      (Homeomorph.refl _))
  let E := e.prod (OpenPartialHomeomorph.refl ({i // i ∉ Set.range f} → K))
  refine ⟨(h.toOpenPartialHomeomorph.trans E).transHomeomorph h.symm, ?_, fun x ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.univ_inter, Set.mem_preimage]
    exact ⟨he, Set.mem_univ _⟩
  · let y := Sum.elim (fun i ↦ x (Sum.inl i)) (fun i ↦ eval x (p i))
    -- Evaluate the conjugate and compare the used and unused coordinates separately.
    change h.symm (E (h x)) = y
    apply h.injective
    rw [h.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · change e (x ∘ f) = y ∘ f
      rw [hmap]
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (eval_rename f x (q i)).symm.trans (congrArg (eval x) (hq i))
    · change (fun i : {i // i ∉ Set.range f} ↦ x i.val) = fun i ↦ y i.val
      funext i
      obtain ⟨(s | j), hj⟩ := i
      · rfl
      · exact (hj (hr j)).elim

/-- Projection to the parameters is open on an open part of a polynomial solution space
where the Jacobian in the other variables is invertible. This applies in particular to
principal open subsets of affine varieties. -/
theorem isOpenMap_comp_inl_eval_family_eq_zero (p : ι → MvPolynomial (σ ⊕ ι) K)
    (v : Set (σ ⊕ ι → K)) (hv : IsOpen v)
    (hp : ∀ a ∈ v, (∀ i, eval a (p i) = 0) →
      ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0) :
    IsOpenMap (fun a : {a : σ ⊕ ι → K // a ∈ v ∧ ∀ i, eval a (p i) = 0} ↦
      fun i ↦ a.val (Sum.inl i)) := by
  let s : Set (σ ⊕ ι → K) := {x | x ∈ v ∧ ∀ i, eval x (p i) = 0}
  refine (IsLocalHomeomorph.mk (fun a : s ↦ fun i ↦ a.val (Sum.inl i)) fun a ↦ ?_).isOpenMap
  obtain ⟨e, hae, he⟩ := exists_openPartialHomeomorph_sumElim_eval_family p a.val
    (hp a.val a.property.1 a.property.2)
  let e' := e.restrOpen v hv
  have he' (x : σ ⊕ ι → K) : e' x =
      Sum.elim (fun i ↦ x (Sum.inl i)) (fun i ↦ eval x (p i)) := by
    simpa only [e', OpenPartialHomeomorph.coe_restrOpen] using he x
  let j : (σ → K) → (σ ⊕ ι → K) := fun y ↦ Sum.elim y 0
  let π : (σ ⊕ ι → K) → (σ → K) := fun z i ↦ z (Sum.inl i)
  have hj : Continuous j := continuous_pi fun i ↦ by
    cases i with
    | inl i => exact continuous_apply i
    | inr i => exact continuous_const
  let chart := e'.subtypeCoord s ⟨a⟩ j π
    (fun {y} hy ↦ by
      have hmem : e'.symm (j y) ∈ (e.restrOpen v hv).source := e'.map_target hy
      rw [OpenPartialHomeomorph.restrOpen_source] at hmem
      exact ⟨hmem.2, fun i ↦ by
        simpa [he', j] using congrFun (e'.right_inv hy) (Sum.inr i)⟩)
    (fun {_} _ hx ↦ by ext i; cases i <;> simp [j, π, he', hx.2])
    (fun {_} _ ↦ rfl) hj (continuous_pi fun i ↦ continuous_apply (Sum.inl i)).continuousOn
  refine ⟨chart, ?_, ?_⟩
  · have hsource : chart.source = Subtype.val ⁻¹' e'.source :=
      OpenPartialHomeomorph.subtypeCoord_source ..
    simpa only [hsource, Set.mem_preimage, e', OpenPartialHomeomorph.restrOpen_source,
      Set.mem_inter_iff] using And.intro hae a.property.1
  · intro x _
    have hchart : chart x = π (e' x.val) := OpenPartialHomeomorph.subtypeCoord_apply ..
    rw [hchart, he']
    rfl

/-- On the locus of solutions where the variable Jacobian has nonzero determinant, projection to
the parameter coordinates is open. This formulation requires no global smoothness hypothesis. -/
theorem isOpenMap_comp_inl_det_jacobiMatrixAt_ne_zero_and_eval_family_eq_zero
    (p : ι → MvPolynomial (σ ⊕ ι) K) :
    IsOpenMap (fun a : {a : σ ⊕ ι → K //
      ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0 ∧ ∀ i, eval a (p i) = 0} ↦
      fun i ↦ a.val (Sum.inl i)) := by
  have hdet : Continuous (fun a : σ ⊕ ι → K ↦
      ((jacobiMatrixAt p a).submatrix id Sum.inr).det) :=
    Continuous.matrix_det (continuous_pi fun i ↦ continuous_pi fun j ↦ by
      simpa only [Matrix.submatrix_apply, id_eq, jacobiMatrixAt_apply] using
        MvPolynomial.continuous_eval (pderiv (Sum.inr j) (p i)))
  exact isOpenMap_comp_inl_eval_family_eq_zero p _ (isOpen_ne_fun hdet continuous_const)
    (fun _ ha _ ↦ ha)

end Parameters

end TauCeti
