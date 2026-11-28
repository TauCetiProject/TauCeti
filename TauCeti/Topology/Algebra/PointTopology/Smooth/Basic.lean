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

A standard smooth algebra induces an open map on points valued in a complete nontrivially
normed field, over any commutative base ring. Lift the presentation equations to polynomials in
the finitely many relation coefficients and the relative generators. The same Jacobian minor
gives implicit coordinates on their zero set. All coefficient coordinates are among the free
coordinates, so varying a base point while holding the other free coordinates fixed lifts
locally to the source.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, §4, p. 11.
-/

public section

open MvPolynomial Topology
open scoped TauCeti.PointTopology

namespace Algebra.SubmersivePresentation

open TauCeti

universe u v

variable {k K R S τ : Type*} {ι : Type u} {σ : Type v} [CommRing k] [NontriviallyNormedField K]
  [CommRing R] [CommRing S] [Algebra k K] [Algebra k R] [Algebra k S]
  [Algebra R S] [IsScalarTower k R S]

variable [Finite σ] (P : SubmersivePresentation R S ι σ)

omit [Algebra k S] [IsScalarTower k R S] in
/-- Only finitely many coefficients are needed to lift the relative relations. -/
private theorem exists_liftedRelations :
    ∃ (τ : Type (max u v)) (_ : Fintype τ) (q : MvPolynomial τ k →ₐ[k] R)
      (p : σ → MvPolynomial (ι ⊕ τ) k),
      ∀ j, MvPolynomial.map q (sumAlgEquiv k ι τ (p j)) = P.relation j := by
  classical
  let := Fintype.ofFinite σ
  let τ := Σ j, (P.relation j).support
  let c : τ → R := fun i ↦ (P.relation i.1).coeff i.2
  let q : MvPolynomial τ k →ₐ[k] R := aeval c
  let p (j : σ) : MvPolynomial ι (MvPolynomial τ k) :=
    ∑ d : (P.relation j).support, monomial d.val (X ⟨j, d⟩)
  refine ⟨τ, inferInstance, q, fun j ↦ (sumAlgEquiv k ι τ).symm (p j), fun j ↦ ?_⟩
  simp only [AlgEquiv.apply_symm_apply, p, map_sum, map_monomial]
  simp only [AlgHom.coe_toRingHom, q, aeval_X, c]
  exact (Finset.sum_coe_sort _ (fun d ↦ monomial d ((P.relation j).coeff d))).trans
    (P.relation j).support_sum_monomial_coeff

omit [Algebra k S] [IsScalarTower k R S] in
/-- Joint evaluation of a lifted relation agrees with the original tower evaluation. -/
private theorem eval_liftedRelation
    (q : MvPolynomial τ k →ₐ[k] R) (p : σ → MvPolynomial (ι ⊕ τ) k)
    (hp : ∀ j, map q (sumAlgEquiv k ι τ (p j)) = P.relation j)
    (y : R →ₐ[k] K) (v : ι → K) (j : σ) :
    eval (Sum.elim v (fun i ↦ y (q (X i)))) (map (algebraMap k K) (p j)) =
      aevalTower y v (P.relation j) := by
  rw [← hp j, aevalTower_map_sumAlgEquiv, eval_map]
  rfl

/-- The relative Jacobian minor is preserved by lifting the coefficient polynomials. -/
private theorem isUnit_det_liftedRelations [Fintype σ] [DecidableEq σ]
    (q : MvPolynomial τ k →ₐ[k] R) (p : σ → MvPolynomial (ι ⊕ τ) k)
    (hp : ∀ j, MvPolynomial.map q (sumAlgEquiv k ι τ (p j)) = P.relation j)
    (x : S →ₐ[k] K) :
    IsUnit (((jacobiMatrixAt (fun j ↦ map (algebraMap k K) (p j)) (Sum.elim (fun i ↦ x (P.val i))
      (fun i ↦ (x.comp (IsScalarTower.toAlgHom k R S)) (q (X i))))).submatrix
        _root_.id (Sum.inl ∘ P.map)).det) := by
  let y := x.comp (IsScalarTower.toAlgHom k R S)
  let v := fun i ↦ x (P.val i)
  have h := P.isUnit_det_jacobiMatrix_solution (k := k)
    ⟨(y, v), fun j ↦ by
      rw [P.aevalTower_comp_toAlgHom_val, P.aeval_val_relation, map_zero]⟩
  convert h using 1
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [jacobiMatrixAt_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Function.comp_apply, id_eq, AlgHom.mapMatrix_apply, Matrix.map_apply,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rw [pderiv_map, eval_map]
  change aeval (Sum.elim v (fun i ↦ y (q (X i)))) _ = _
  rw [← aevalTower_map_sumAlgEquiv _ q y v, ← pderiv_sumAlgEquiv, ← pderiv_map, hp]

/-- Send a point to the zero set of the finitely parameterized relations. -/
private noncomputable def liftedPoint (q : MvPolynomial τ k →ₐ[k] R)
    (p : σ → MvPolynomial (ι ⊕ τ) k)
    (hp : ∀ j, map q (sumAlgEquiv k ι τ (p j)) = P.relation j) (x : S →ₐ[k] K) :
    {v : (ι ⊕ τ) → K | (fun j ↦ eval v (map (algebraMap k K) (p j))) = 0} :=
  ⟨Sum.elim (fun i ↦ x (P.val i))
    (fun i ↦ (x.comp (IsScalarTower.toAlgHom k R S)) (q (X i))), by
    ext j
    rw [Pi.zero_apply, P.eval_liftedRelation q p hp,
      P.aevalTower_comp_toAlgHom_val, P.aeval_val_relation, map_zero]⟩

/-- Recover a presentation point while retaining the prescribed full coefficient point. -/
private theorem exists_point_of_lifted_solution (q : MvPolynomial τ k →ₐ[k] R)
    (p : σ → MvPolynomial (ι ⊕ τ) k)
    (hp : ∀ j, map q (sumAlgEquiv k ι τ (p j)) = P.relation j)
    (y : R →ₐ[k] K) (v : (ι ⊕ τ) → K)
    (hv : ∀ j, eval v (map (algebraMap k K) (p j)) = 0)
    (hbase : ∀ i, v (.inr i) = y (q (X i)))
    (U : Set ((R →ₐ[k] K) × (ι → K))) (hU : (y, v ∘ Sum.inl) ∈ U) :
    ∃ x : S →ₐ[k] K, (P.toPresentation.pointsHomeomorph x).val ∈ U ∧
      x.comp (IsScalarTower.toAlgHom k R S) = y := by
  have hcoord : Sum.elim (v ∘ Sum.inl) (fun i ↦ y (q (X i))) = v := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (hbase i).symm
  let sol : {z : (R →ₐ[k] K) × (ι → K) //
      ∀ j, aevalTower z.1 z.2 (P.relation j) = 0} :=
    ⟨(y, v ∘ Sum.inl), fun j ↦ by rw [← P.eval_liftedRelation q p hp, hcoord, hv]⟩
  refine ⟨P.toPresentation.pointsHomeomorph.symm sol, ?_,
    P.toPresentation.pointsHomeomorph_symm_comp sol⟩
  simpa only [P.toPresentation.pointsHomeomorph.apply_symm_apply] using hU

variable [CompleteSpace K] [Finite ι]

include P in
/-- Restriction along a submersive presentation is open on points valued in a complete
nontrivially normed field, over an arbitrary commutative base ring. -/
theorem isOpenMap_comap :
    IsOpenMap (fun x : S →ₐ[k] K ↦ x.comp (IsScalarTower.toAlgHom k R S)) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  obtain ⟨τ, _, q, p, hp⟩ := P.exists_liftedRelations (k := k)
  let pK (j : σ) := map (algebraMap k K) (p j)
  let lifted := P.liftedPoint (K := K) q p hp
  let H := P.toPresentation.pointsHomeomorph (k := k) (E := K)
  intro s hs
  obtain ⟨U, hU, hUs⟩ := (IsEmbedding.subtypeVal.comp H.isEmbedding).isInducing.isOpen_iff.mp hs
  refine isOpen_iff_forall_mem_open.mpr fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  let m : σ → ι ⊕ τ := Sum.inl ∘ P.map
  obtain ⟨e, he, heval⟩ := exists_openPartialHomeomorph_zeroSet pK
    (lifted x) (P.isUnit_det_liftedRelations q p hp x)
  let w (y' : R →ₐ[k] K) (i : ↥(Set.range m)ᶜ) :=
    Sum.elim (fun i ↦ x (P.val i)) (fun j ↦ y' (q (X j))) i.val
  have hw : Continuous w := continuous_pi fun ⟨i, _⟩ ↦ by
    cases i with
    | inl i => exact continuous_const
    | inr i => exact PointTopology.continuous_eval _
  let t (y' : R →ₐ[k] K) := (y', (e.symm (w y')).val ∘ Sum.inl)
  have ht : ContinuousOn t (w ⁻¹' e.target) := continuousOn_id.prodMk <|
    continuousOn_pi.mpr fun i ↦
      ((continuous_apply (Sum.inl i)).comp continuous_subtypeVal).comp_continuousOn
        (e.symm.continuousOn.comp hw.continuousOn (fun _ h ↦ h))
  have hwx : w (x.comp (IsScalarTower.toAlgHom k R S)) = e (lifted x) :=
    (funext (heval (lifted x))).symm
  have hex : e.symm (w (x.comp (IsScalarTower.toAlgHom k R S))) = lifted x := by
    rw [hwx, e.left_inv he]
  refine ⟨w ⁻¹' e.target ∩ t ⁻¹' U, ?_,
    ht.isOpen_inter_preimage (e.open_target.preimage hw) hU, ?_⟩
  · rintro y' ⟨hy', hyt⟩
    let z := e.symm (w y')
    have hzright (i : τ) : z.val (.inr i) = y' (q (X i)) := by
      let a : ↥(Set.range m)ᶜ := ⟨.inr i, by simp [m, Set.mem_range]⟩
      exact (heval z a).symm.trans (congrFun (e.right_inv hy') a)
    obtain ⟨b, hb, hby⟩ := P.exists_point_of_lifted_solution q p hp y' z.val
      (fun j ↦ congrFun z.property j) hzright U hyt
    exact ⟨b, by rwa [← hUs], hby⟩
  · constructor
    · change w (x.comp (IsScalarTower.toAlgHom k R S)) ∈ e.target
      rw [hwx]
      exact e.map_source he
    · have hmem : (H x).val ∈ U := by rwa [← hUs] at hx
      change (x.comp (IsScalarTower.toAlgHom k R S),
        (e.symm (w (x.comp (IsScalarTower.toAlgHom k R S)))).val ∘ Sum.inl) ∈ U
      rw [hex]
      simpa only [H, Presentation.pointsHomeomorph_apply_coe, lifted, liftedPoint,
        Function.comp_def, Sum.elim_inl] using hmem

end Algebra.SubmersivePresentation

namespace TauCeti.PointTopology

/-- A standard smooth algebra induces an open restriction map on points valued in a complete
nontrivially normed field, over an arbitrary commutative base ring. -/
theorem isOpenMap_comap_of_isStandardSmooth {k K R S : Type*} [CommRing k]
    [NontriviallyNormedField K] [CompleteSpace K] [Algebra k K]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.IsStandardSmooth R S] :
    IsOpenMap (fun x : S →ₐ[k] K ↦ x.comp (IsScalarTower.toAlgHom k R S)) := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth R S›.out
  exact P.isOpenMap_comap

end TauCeti.PointTopology
