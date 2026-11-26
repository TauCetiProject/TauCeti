/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import TauCeti.RingTheory.Extension.Presentation.Submersive
public import TauCeti.Topology.Algebra.PointTopology.Presentation
import TauCeti.Algebra.MvPolynomial.Sum
import TauCeti.Analysis.MvPolynomial.Implicit

/-!
# Smooth maps on affine point spaces are open

Over a complete nontrivially normed field, a standard smooth algebra over a finitely generated
algebra induces an open map on points. Lift the presentation equations to polynomials in both
the base and relative generators. The same Jacobian minor gives implicit coordinates on their
zero set. All base coordinates are among the free coordinates, so varying a base point while
holding the other free coordinates fixed lifts locally to the source.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, §4, p. 11.
-/

public section

open MvPolynomial Topology
open scoped TauCeti.PointTopology

namespace Algebra.SubmersivePresentation

open TauCeti

variable {K R S ι σ τ : Type*} [NontriviallyNormedField K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]

variable [Finite σ] (P : SubmersivePresentation R S ι σ)

/-- The relative Jacobian minor is preserved by lifting the coefficient polynomials. -/
private theorem isUnit_det_liftedRelations [Fintype σ] [DecidableEq σ]
    (q : MvPolynomial τ K →ₐ[K] R) (p : σ → MvPolynomial (ι ⊕ τ) K)
    (hp : ∀ j, MvPolynomial.map q (sumAlgEquiv K ι τ (p j)) = P.relation j)
    (x : S →ₐ[K] K) :
    IsUnit (((jacobiMatrixAt p (Sum.elim (fun i ↦ x (P.val i))
      (fun i ↦ (x.comp (IsScalarTower.toAlgHom K R S)) (q (X i))))).submatrix
        _root_.id (Sum.inl ∘ P.map)).det) := by
  let y := x.comp (IsScalarTower.toAlgHom K R S)
  let v := fun i ↦ x (P.val i)
  have h := P.isUnit_det_jacobiMatrix_solution (k := K)
    ⟨(y, v), fun j ↦ by
      rw [P.aevalTower_comp_toAlgHom_val, P.aeval_val_relation, map_zero]⟩
  convert h using 1
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [jacobiMatrixAt_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Function.comp_apply, id_eq, AlgHom.mapMatrix_apply, Matrix.map_apply,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rw [← aeval_eq_eval, ← aevalTower_map_sumAlgEquiv _ q y v,
    ← pderiv_sumAlgEquiv, ← pderiv_map, hp]

/-- The lifted polynomial coordinates embed the point space into the zero set, where the
coefficient point is recorded by its values at the base generators. -/
private theorem isEmbedding_liftedPoints (q : MvPolynomial τ K →ₐ[K] R)
    (hq : Function.Surjective q) {Z : Set ((ι ⊕ τ) → K)}
    (f : (S →ₐ[K] K) → Z)
    (hf : ∀ x, (f x).val = Sum.elim (fun i ↦ x (P.val i))
      (fun i ↦ x (algebraMap R S (q (X i))))) :
    IsEmbedding f := by
  have hbase : IsEmbedding (fun y : R →ₐ[K] K ↦ fun i ↦ y (q (X i))) := by
    have h := (PointTopology.mvPolynomialHomeomorph K K τ).isEmbedding.comp
      (PointTopology.isEmbedding_comap_of_surjective q hq (R := K))
    have heq :
        (PointTopology.mvPolynomialHomeomorph K K τ ∘ fun y : R →ₐ[K] K ↦ y.comp q) =
          fun y i ↦ y (q (X i)) := by
      funext y i
      simp only [Function.comp_apply, PointTopology.mvPolynomialHomeomorph_apply,
        AlgHom.comp_apply]
    exact heq ▸ h
  have h := Homeomorph.sumArrowHomeomorphProdArrow.symm.isEmbedding.comp
    (((IsEmbedding.id : IsEmbedding (_root_.id : (ι → K) → (ι → K))).prodMap hbase).comp
      ((Homeomorph.prodComm _ _).isEmbedding.comp
        (IsEmbedding.subtypeVal.comp P.toPresentation.pointsHomeomorph.isEmbedding)))
  apply (IsEmbedding.of_comp_iff (g := (Subtype.val : Z → (ι ⊕ τ → K)))
    IsEmbedding.subtypeVal).mp
  convert h using 1
  funext x
  rw [Function.comp_apply, hf]
  simp [Function.comp_def, Prod.map]
  -- Both sides now combine the two coordinate families using the sum eliminator.
  rfl

/-- A lifted zero whose base coordinates come from a base point recovers an original point. -/
private theorem exists_point_of_lifted_solution
    (q : MvPolynomial τ K →ₐ[K] R) (p : σ → MvPolynomial (ι ⊕ τ) K)
    (hp : ∀ j, MvPolynomial.map q (sumAlgEquiv K ι τ (p j)) = P.relation j)
    (y : R →ₐ[K] K) (v : (ι ⊕ τ) → K)
    (hv : ∀ j, eval v (p j) = 0) (hbase : ∀ i, v (.inr i) = y (q (X i))) :
    ∃ x : S →ₐ[K] K, x.comp (IsScalarTower.toAlgHom K R S) = y ∧
      Sum.elim (fun i ↦ x (P.val i)) (fun i ↦ y (q (X i))) = v := by
  have hcoord : Sum.elim (v ∘ Sum.inl) (fun i ↦ y (q (X i))) = v := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (hbase i).symm
  have hsol (j : σ) : aevalTower y (v ∘ Sum.inl) (P.relation j) = 0 := by
    rw [← hp j, aevalTower_map_sumAlgEquiv, hcoord, aeval_eq_eval, hv]
  let z : {z : (R →ₐ[K] K) × (ι → K) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0} :=
    ⟨(y, v ∘ Sum.inl), hsol⟩
  refine ⟨P.toPresentation.pointsHomeomorph.symm z,
    P.toPresentation.pointsHomeomorph_symm_comp z, ?_⟩
  rw [← hcoord]
  congr 1
  exact funext (P.toPresentation.pointsHomeomorph_symm_apply_val z)

variable [CompleteSpace K] [Finite ι]

include P in
/-- The restriction of points along a submersive presentation over a finite-type base algebra
is open for the evaluation topologies. -/
theorem isOpenMap_comap [FiniteType K R] :
    IsOpenMap (fun x : S →ₐ[K] K ↦ x.comp (IsScalarTower.toAlgHom K R S)) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  obtain ⟨τ, _, q, hq⟩ := FiniteType.iff_quotient_mvPolynomial'.mp ‹FiniteType K R›
  obtain ⟨p, hp⟩ : ∃ p : σ → MvPolynomial (ι ⊕ τ) K,
      ∀ j, MvPolynomial.map q (sumAlgEquiv K ι τ (p j)) = P.relation j :=
    Classical.axiomOfChoice fun j ↦
      ((MvPolynomial.map_surjective _ hq).comp
        (sumAlgEquiv K ι τ).surjective) (P.relation j)
  let Z := {v : (ι ⊕ τ) → K | (fun j ↦ eval v (p j)) = 0}
  let lifted : (S →ₐ[K] K) → Z := fun x ↦
    ⟨Sum.elim (fun i ↦ x (P.val i)) (fun i ↦
      (x.comp (IsScalarTower.toAlgHom K R S)) (q (X i))), by
      ext j
      rw [Pi.zero_apply, ← aeval_eq_eval,
        ← aevalTower_map_sumAlgEquiv _ q (x.comp (IsScalarTower.toAlgHom K R S)),
        hp, P.aevalTower_comp_toAlgHom_val, P.aeval_val_relation, map_zero]⟩
  have hemb := P.isEmbedding_liftedPoints q hq lifted (fun _ ↦ rfl)
  intro s hs
  obtain ⟨U, hU, rfl⟩ := hemb.isInducing.isOpen_iff.mp hs
  refine isOpen_iff_forall_mem_open.mpr fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  let m : σ → ι ⊕ τ := Sum.inl ∘ P.map
  obtain ⟨e, he, heval⟩ := exists_openPartialHomeomorph_zeroSet p
    (Sum.inl_injective.comp P.map_inj) (lifted x) (P.isUnit_det_liftedRelations q p hp x)
  let w (y' : R →ₐ[K] K) (i : ↥(Set.range m)ᶜ) :=
    Sum.elim (fun i ↦ x (P.val i)) (fun j ↦ y' (q (X j))) i.val
  have hw : Continuous w := continuous_pi fun ⟨i, _⟩ ↦ by
    cases i with
    | inl i => exact continuous_const
    | inr i => exact PointTopology.continuous_eval _
  refine ⟨w ⁻¹' (e '' (e.source ∩ U)), ?_, (e.isOpen_image_source_inter hU).preimage hw,
    ⟨lifted x, ⟨he, hx⟩, funext (heval _)⟩⟩
  rintro y' ⟨z, ⟨_, hzU⟩, hz⟩
  have hzright (i : τ) : z.val (.inr i) = y' (q (X i)) := by
    let a : ↥(Set.range m)ᶜ := ⟨.inr i, by simp [m, Set.mem_range]⟩
    exact (heval z a).symm.trans (congrFun hz a)
  obtain ⟨b, hb, hval⟩ := P.exists_point_of_lifted_solution q p hp y' z.val
    (fun j ↦ congrFun z.property j) hzright
  have hlift : lifted b = z := by
    apply Subtype.ext
    exact (congrArg (fun y : R →ₐ[K] K ↦
      Sum.elim (fun i ↦ b (P.val i)) (fun i ↦ y (q (X i)))) hb).trans hval
  exact ⟨b, Set.mem_preimage.mpr (hlift ▸ hzU), hb⟩

end Algebra.SubmersivePresentation

namespace Algebra.IsStandardSmooth

/-- A standard smooth morphism of affine schemes over a complete nontrivially normed field
induces an open map on field-valued points if the target is of finite type. -/
theorem isOpenMap_comap {K R S : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    [FiniteType K R] [IsStandardSmooth R S] :
    IsOpenMap (fun x : S →ₐ[K] K ↦ x.comp (IsScalarTower.toAlgHom K R S)) := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›.out
  exact P.isOpenMap_comap

end Algebra.IsStandardSmooth
