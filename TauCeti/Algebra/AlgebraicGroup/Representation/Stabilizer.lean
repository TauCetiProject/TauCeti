/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Antipode
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Submodule
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.Algebra.HopfAlgebra.Antipode
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.HopfAlgebra.Quotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Corestrict
import TauCeti.LinearAlgebra.TensorProduct.Separation
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# The stabilizer of a subspace of a representation

Let `H` be a commutative Hopf algebra over a field `k` and `M` a right `H`-comodule, that is, a
representation of the affine group `G = Spec H`. A subspace `W ≤ M` has a stabilizer: the closed
subgroup of `G` whose points carry `W` onto itself. In coordinates it is cut out by the matrix
coefficients `c(ψ ∘ q, w)` pairing vectors `w ∈ W` with functionals vanishing on `W` (here
`q : M → M ⧸ W` is the quotient map), together with their antipodes.

This file constructs that Hopf ideal and characterizes it in four ways.

* Its points with values in any commutative `k`-algebra `A` are the points whose action carries
  `A ⊗ W` onto itself. Its rational points are those carrying `W` itself onto `W`.
* It is the smallest Hopf ideal containing the coefficients `c(ψ ∘ q, w)`.
* It is zero, so the stabilizer is all of `G`, exactly when `W` is a subcomodule.
* Its Lie algebra consists of the tangent vectors whose differentiated action preserves `W`.

The last statement is the infinitesimal input to the comparison of `G`-stable and
`Lie(G)`-stable subspaces.

## Main declarations

* `Submodule.stabilizerHopfIdeal`: the Hopf ideal of the stabilizer of `W`.
* `Submodule.stabilizerHopfIdeal_le_ker_iff`: its points are the points carrying `A ⊗ W` onto
  itself.
* `Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff`: its rational points are the
  rational points carrying `W` onto itself.
* `Submodule.stabilizerHopfIdeal_le_iff`: its universal property among Hopf ideals.
* `Submodule.stabilizerHopfIdeal_eq_bot_iff`: it vanishes exactly when `W` is a subcomodule.
* `Submodule.stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict`:
  `W.stabilizerHopfIdeal H ≤ J` exactly when `W` is a subcomodule under corestriction to
  `H ⧸ J.toIdeal`.
* `Submodule.stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff`: recovering
  `W.stabilizerHopfIdeal H = I` from the point functor on all value algebras.
* `Submodule.stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff`: recovering equality of two
  stabilizer Hopf ideals from agreement on all value algebras.
* `Submodule.stabilizerHopfIdeal_map_transport`: transporting a comodule along a linear equivalence
  preserves subspace stabilizer Hopf ideals.
* `Submodule.mem_lieSubalgebra_stabilizerHopfIdeal_iff`: its Lie algebra is the stabilizer of
  `W` under the differentiated representation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open scoped TensorProduct
open TauCeti

universe u v w w₁ w₂

noncomputable section

namespace Submodule

section Hopf

variable {k : Type u} (H : Type v) {M : Type w} [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- The matrix coefficients `c(ψ ∘ q, w)` pairing vectors `w ∈ W` with functionals vanishing on
`W`, where `q : M → M ⧸ W` is the quotient map. -/
private def stabilizerCoefficients (W : Submodule k M) : Set H :=
  Set.range fun p : Module.Dual k (M ⧸ W) × W ↦
    Comodule.matrixCoefficient (R := k) (C := H) (p.1 ∘ₗ W.mkQ) p.2

/-- The generators of the stabilizer ideal: the coefficients and their antipodes. -/
private def stabilizerGenerators (W : Submodule k M) : Set H :=
  stabilizerCoefficients H W ∪ HopfAlgebra.antipode k '' stabilizerCoefficients H W

variable {H}

/-- The span of the stabilizer generators is stable under the antipode. -/
private theorem span_stabilizerGenerators_le_comap_antipode (W : Submodule k M) :
    Ideal.span (stabilizerGenerators H W) ≤
      (Ideal.span (stabilizerGenerators H W)).comap (HopfAlgebra.antipodeAlgHom k H) := by
  rw [Ideal.span_le]
  rintro y (hy | ⟨z, hz, rfl⟩)
  · exact Ideal.subset_span (Or.inr ⟨y, hy, rfl⟩)
  · rw [SetLike.mem_coe, Ideal.mem_comap, HopfAlgebra.antipodeAlgHom_apply,
      TauCeti.HopfAlgebra.antipode_antipode]
    exact Ideal.subset_span (Or.inl hz)

/-- Each coefficient `c(ψ ∘ q, w)` lies in the span of the stabilizer generators. -/
private theorem matrixCoefficient_mem_span_stabilizerGenerators (W : Submodule k M)
    (ψ : Module.Dual k (M ⧸ W)) {w : M} (hw : w ∈ W) :
    Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ W.mkQ) w ∈
      Ideal.span (stabilizerGenerators H W) :=
  Ideal.subset_span (Or.inl ⟨(ψ, ⟨w, hw⟩), rfl⟩)

/-- Modulo the stabilizer ideal, the vectors of `W` have coaction in `W ⊗ H`: their images in
`(M ⧸ W) ⊗ (H ⧸ I)` vanish. -/
private theorem map_mkQ_mkₐ_coact_eq_zero (W : Submodule k M) {w : M} (hw : w ∈ W) :
    TensorProduct.map W.mkQ
        (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W))).toLinearMap
        (Comodule.coact (R := k) (C := H) (M := M) w) = 0 := by
  set π := Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W))
  apply tensor_eq_zero_of_forall_rTensor_eq_zero (fun ψ : Module.Dual k (M ⧸ W) ↦ ψ)
    (fun x hx ↦ (Module.forall_dual_apply_eq_zero_iff k x).mp hx)
  intro ψ
  apply (TensorProduct.lid k (H ⧸ Ideal.span (stabilizerGenerators H W))).injective
  simp only [map_zero]
  have hcontract (t : M ⊗[k] H) :
      TensorProduct.lid k (H ⧸ Ideal.span (stabilizerGenerators H W))
          (ψ.rTensor _ (TensorProduct.map W.mkQ π.toLinearMap t)) =
        π (TensorProduct.lid k H (TensorProduct.map (ψ ∘ₗ W.mkQ) LinearMap.id t)) := by
    induction t with
    | tmul m h => simp [map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hcontract, ← Comodule.matrixCoefficient_def, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  exact matrixCoefficient_mem_span_stabilizerGenerators W ψ hw

/-- The comultiplication of a coefficient `c(ψ ∘ q, w)` vanishes in `(H ⧸ I) ⊗ (H ⧸ I)`. -/
private theorem map_mkₐ_comul_matrixCoefficient (W : Submodule k M)
    (ψ : Module.Dual k (M ⧸ W)) {w : M} (hw : w ∈ W) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Coalgebra.comul (R := k)
          (Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ W.mkQ) w)) = 0 := by
  set π := Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W))
  let g : M ⧸ W →ₗ[k] H ⧸ Ideal.span (stabilizerGenerators H W) :=
    W.liftQ (π.toLinearMap ∘ₗ Comodule.matrixCoefficientLinear (R := k) (C := H) (ψ ∘ₗ W.mkQ))
      fun w' hw' ↦ by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Comodule.matrixCoefficientLinear_apply,
          AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact matrixCoefficient_mem_span_stabilizerGenerators W ψ hw'
  have hfactor (t : M ⊗[k] H) :
      Algebra.TensorProduct.map π π
          (TensorProduct.map
            (Comodule.matrixCoefficientLinear (R := k) (C := H) (ψ ∘ₗ W.mkQ)) LinearMap.id t) =
        TensorProduct.map g LinearMap.id (TensorProduct.map W.mkQ π.toLinearMap t) := by
    induction t with
    | tmul m h => simp [g]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Comodule.comul_matrixCoefficient, hfactor, map_mkQ_mkₐ_coact_eq_zero W hw, map_zero]

/-- Reduction modulo the stabilizer ideal intertwines the antipode-twisted flip of `H ⊗ H` with
the induced antipode-twisted flip of the quotient. -/
private theorem map_mkₐ_map_antipode_comm (W : Submodule k M) (t : H ⊗[k] H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (TensorProduct.map (HopfAlgebra.antipode k) (HopfAlgebra.antipode k)
          (TensorProduct.comm k H H t)) =
      TensorProduct.map
        (Ideal.quotientMapₐ _ (HopfAlgebra.antipodeAlgHom k H)
          (span_stabilizerGenerators_le_comap_antipode W)).toLinearMap
        (Ideal.quotientMapₐ _ (HopfAlgebra.antipodeAlgHom k H)
          (span_stabilizerGenerators_le_comap_antipode W)).toLinearMap
        (TensorProduct.comm k _ _
          (Algebra.TensorProduct.map
            (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
            (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W))) t)) := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every stabilizer generator has comultiplication vanishing in `(H ⧸ I) ⊗ (H ⧸ I)`. -/
private theorem map_mkₐ_comul_stabilizerGenerators (W : Submodule k M) {x : H}
    (hx : x ∈ stabilizerGenerators H W) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Coalgebra.comul (R := k) x) = 0 := by
  rcases hx with ⟨⟨ψ, w⟩, rfl⟩ | ⟨_, ⟨⟨ψ, w⟩, rfl⟩, rfl⟩
  · exact map_mkₐ_comul_matrixCoefficient W ψ w.property
  · rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, map_mkₐ_map_antipode_comm,
      map_mkₐ_comul_matrixCoefficient W ψ w.property, map_zero, map_zero]

/-- The counit vanishes on the stabilizer generators. -/
private theorem counit_stabilizerGenerators (W : Submodule k M) {x : H}
    (hx : x ∈ stabilizerGenerators H W) : Coalgebra.counit (R := k) x = 0 := by
  rcases hx with ⟨⟨ψ, w⟩, rfl⟩ | ⟨_, ⟨⟨ψ, w⟩, rfl⟩, rfl⟩ <;>
  simp [Comodule.counit_matrixCoefficient, (Submodule.Quotient.mk_eq_zero W).mpr w.property]

variable (H) in
/-- The Hopf ideal of the stabilizer of a subspace `W` of a comodule `M`.

It is generated by the matrix coefficients `c(ψ ∘ q, w)`, for `w ∈ W` and functionals `ψ` on
`M ⧸ W`, together with their antipodes. Contravariantly, it cuts out the closed subgroup of
`Spec H` preserving `W`. -/
def stabilizerHopfIdeal (W : Submodule k M) : HopfIdeal k H :=
  HopfIdeal.ofSpan (stabilizerGenerators H W)
    (fun x hx ↦ by
      have hker := AlgHom.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal
        (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W)))
        (Ideal.Quotient.mkₐ_surjective _ _) (Ideal.Quotient.mkₐ_surjective _ _)
      have hI : RingHom.ker (Ideal.Quotient.mkₐ k (Ideal.span (stabilizerGenerators H W))) =
          Ideal.span (stabilizerGenerators H W) := by
        rw [← RingHom.ker_coe_toRingHom]
        exact Ideal.Quotient.mkₐ_ker k _
      rw [hI] at hker
      rw [← hker, RingHom.mem_ker]
      exact map_mkₐ_comul_stabilizerGenerators W hx)
    (fun _ hx ↦ counit_stabilizerGenerators W hx)
    (fun _ hx ↦ by
      simpa using span_stabilizerGenerators_le_comap_antipode W (Ideal.subset_span hx))

private theorem stabilizerHopfIdeal_toIdeal (W : Submodule k M) :
    (W.stabilizerHopfIdeal H).toIdeal = Ideal.span (stabilizerGenerators H W) :=
  HopfIdeal.ofSpan_toIdeal _ _ _ _

/-- A matrix coefficient pairing a vector of `W` with a functional vanishing on `W` lies in the
stabilizer Hopf ideal. -/
theorem matrixCoefficient_mem_stabilizerHopfIdeal (W : Submodule k M)
    (ψ : Module.Dual k (M ⧸ W)) {w : M} (hw : w ∈ W) :
    Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ W.mkQ) w ∈ W.stabilizerHopfIdeal H := by
  rw [← HopfIdeal.mem_toIdeal, stabilizerHopfIdeal_toIdeal]
  exact matrixCoefficient_mem_span_stabilizerGenerators W ψ hw

/-- The stabilizer Hopf ideal is the smallest Hopf ideal containing the matrix coefficients
`c(ψ ∘ q, w)`; contravariantly, the stabilizer is the largest closed subgroup on which these
coefficients vanish. -/
theorem stabilizerHopfIdeal_le_iff (W : Submodule k M) (J : HopfIdeal k H) :
    W.stabilizerHopfIdeal H ≤ J ↔
      ∀ (ψ : Module.Dual k (M ⧸ W)), ∀ w ∈ W,
        Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ W.mkQ) w ∈ J := by
  refine ⟨fun h ψ w hw ↦ h (matrixCoefficient_mem_stabilizerHopfIdeal W ψ hw), fun h ↦ ?_⟩
  rw [← HopfIdeal.toIdeal_le_toIdeal, stabilizerHopfIdeal_toIdeal, Ideal.span_le]
  rintro _ (⟨⟨ψ, w⟩, rfl⟩ | ⟨_, ⟨⟨ψ, w⟩, rfl⟩, rfl⟩)
  · exact h ψ w w.property
  · exact J.antipode_mem (h ψ w w.property)

/-- The stabilizer of `W` is the whole group exactly when `W` is a subcomodule: the coaction of
every vector of `W` lies in `W ⊗ H`. -/
theorem stabilizerHopfIdeal_eq_bot_iff (W : Submodule k M) :
    W.stabilizerHopfIdeal H = ⊥ ↔
      ∀ w ∈ W, Comodule.coact (R := k) (C := H) (M := M) w ∈
        LinearMap.range (TensorProduct.map W.subtype (LinearMap.id : H →ₗ[k] H)) := by
  simp_rw [coact_mem_range_iff_forall_matrixCoefficient_eq_zero]
  constructor
  · intro h w hw ψ
    simpa [h] using matrixCoefficient_mem_stabilizerHopfIdeal (H := H) W ψ hw
  · intro h
    refine le_antisymm ((stabilizerHopfIdeal_le_iff W ⊥).mpr fun ψ w hw ↦ ?_) bot_le
    rw [HopfIdeal.mem_bot]
    exact h w hw ψ

/-- The Lie algebra of the stabilizer of `W` consists of the tangent vectors whose
differentiated action preserves `W`. -/
theorem mem_lieSubalgebra_stabilizerHopfIdeal_iff (W : Submodule k M)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ (W.stabilizerHopfIdeal H).lieSubalgebra (B := k) ↔
      ∀ w ∈ W, Comodule.differential (R := k) (H := H) (M := M) d w ∈ W := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ (stabilizerHopfIdeal_toIdeal W)]
  have hcoeff (ψ : Module.Dual k (M ⧸ W)) (w : M) :
      d (Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ W.mkQ) w) = 0 ↔
        ψ (W.mkQ (Comodule.differential (R := k) (H := H) (M := M) d w)) = 0 := by
    rw [← EmbeddingLike.map_eq_zero_iff (f := Bialgebra.CounitAlgebra.algEquivSelf k H k),
      d.apply_matrixCoefficient, LinearMap.comp_apply]
  constructor
  · intro h w hw
    rw [← Submodule.Quotient.mk_eq_zero, ← mkQ_apply,
      ← Module.forall_dual_apply_eq_zero_iff k]
    exact fun ψ ↦ (hcoeff ψ w).mp (h _ (Or.inl ⟨(ψ, ⟨w, hw⟩), rfl⟩))
  · have hzero (ψ : Module.Dual k (M ⧸ W)) (w : W) (h : ∀ w ∈ W,
        Comodule.differential (R := k) (H := H) (M := M) d w ∈ W) :
        d (Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ W.mkQ) w) = 0 := by
      rw [hcoeff, mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr (h w w.property), map_zero]
    rintro h _ (⟨⟨ψ, w⟩, rfl⟩ | ⟨_, ⟨⟨ψ, w⟩, rfl⟩, rfl⟩)
    · exact hzero ψ w h
    · rw [Derivation.apply_antipode, hzero ψ w h, neg_zero]

/-- An algebra-valued point lies in the stabilizer of `W` exactly when its action carries the
scalar extension of `W` onto itself. -/
theorem stabilizerHopfIdeal_le_ker_iff (W : Submodule k M) {A : Type*} [CommRing A]
    [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    (W.stabilizerHopfIdeal H).toIdeal ≤ RingHom.ker g.ofConv ↔
      (W.baseChange A).map (Comodule.endOfPoint M g.ofConv) = W.baseChange A := by
  have hinv (x : H) : (g⁻¹).ofConv x = g.ofConv (HopfAlgebra.antipode k x) := by
    rw [WithConv.algHom_inv_def, WithConv.ofConv_toConv, AlgHom.antipodeComp_apply]
  rw [stabilizerHopfIdeal_toIdeal, Ideal.span_le]
  constructor
  · intro h
    apply Comodule.map_endOfPoint_eq_of_mapsTo M g g⁻¹ (mul_inv_cancel g)
    · exact (mapsTo_endOfPoint_baseChange_iff W g.ofConv).mpr fun ψ w hw ↦
        h (Or.inl ⟨(ψ, ⟨w, hw⟩), rfl⟩)
    · refine (mapsTo_endOfPoint_baseChange_iff W (g⁻¹).ofConv).mpr fun ψ w hw ↦ ?_
      rw [hinv]
      exact h (Or.inr ⟨_, ⟨(ψ, ⟨w, hw⟩), rfl⟩, rfl⟩)
  · intro h
    have hg : Set.MapsTo (Comodule.endOfPoint M g.ofConv) (W.baseChange A) (W.baseChange A) :=
      fun z hz ↦ h ▸ Submodule.mem_map_of_mem hz
    have hginv :
        Set.MapsTo (Comodule.endOfPoint M (g⁻¹).ofConv) (W.baseChange A) (W.baseChange A) := by
      intro z hz
      rw [SetLike.mem_coe, ← h] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hz'' := LinearMap.congr_fun (Comodule.endOfPoint_convMul M g⁻¹ g) z'
      rw [inv_mul_cancel, Comodule.endOfPoint_convOne, LinearMap.id_apply,
        LinearMap.comp_apply] at hz''
      rw [← hz'']
      exact hz'
    rintro _ (⟨⟨ψ, w⟩, rfl⟩ | ⟨_, ⟨⟨ψ, w⟩, rfl⟩, rfl⟩)
    · exact (mapsTo_endOfPoint_baseChange_iff W g.ofConv).mp hg ψ w w.property
    · rw [SetLike.mem_coe, RingHom.mem_ker, ← hinv]
      exact (mapsTo_endOfPoint_baseChange_iff W (g⁻¹).ofConv).mp hginv ψ w w.property

/-- A rational point lies in the stabilizer of `W` exactly when its action carries `W` onto
itself. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff (W : Submodule k M)
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (W.stabilizerHopfIdeal H) (CommAlgCat.of k k) ↔
      W.map (Comodule.basePointsRepresentation M g) = W := by
  -- Identify `k ⊗[k] M` with `M`, so that `k ⊗ W` becomes `W` and the scalar-extended action
  -- becomes the action on `M`.
  let e : M →ₗ[k] k ⊗[k] M := (TensorProduct.lid k M).symm.toLinearMap
  have hbc : W.baseChange k = W.map e := by
    have he : TensorProduct.mk k k M 1 = e := by
      ext m
      simp [e]
    rw [baseChange_eq_span, he, span_eq]
  have hcomp : Comodule.endOfPoint M g.ofConv ∘ₗ e =
      e ∘ₗ Comodule.basePointsRepresentation M g := by
    ext m
    simp only [e, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
    rw [Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker,
    W.stabilizerHopfIdeal_le_ker_iff g, hbc, ← map_comp, hcomp, map_comp]
  exact (map_injective_of_injective (TensorProduct.lid k M).symm.injective).eq_iff

/-- A subspace `W` of an `H`-comodule `M` has stabilizer Hopf ideal at most `J` if and only if `W`
is the underlying submodule of an `(H ⧸ J.toIdeal)`-subcomodule under corestriction. -/
theorem stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict
    (W : Submodule k M) (J : HopfIdeal k H) :
    W.stabilizerHopfIdeal H ≤ J ↔
      (letI : Comodule k (H ⧸ J.toIdeal) M :=
        Comodule.Corestrict
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
       ∃ N : Subcomodule k (H ⧸ J.toIdeal) M, N.toSubmodule = W) := by
  let q := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom
  let _ : Comodule k (H ⧸ J.toIdeal) M := Comodule.Corestrict q.toCoalgHom
  have hbot : W.stabilizerHopfIdeal H ≤ J ↔ W.stabilizerHopfIdeal (H ⧸ J.toIdeal) = ⊥ := by
    rw [Submodule.stabilizerHopfIdeal_le_iff, eq_bot_iff, Submodule.stabilizerHopfIdeal_le_iff]
    refine forall_congr' fun ψ ↦ forall₂_congr fun w _ ↦ ?_
    rw [CoalgHom.matrixCoefficient_corestrict, HopfIdeal.mem_bot]
    exact (CommHopfAlgCat.mkQuotient_eq_zero_iff (_root_.CommHopfAlgCat.of k H) J _).symm
  rw [hbot, Submodule.stabilizerHopfIdeal_eq_bot_iff]
  exact ⟨fun h ↦ ⟨Subcomodule.ofSubmodule W h, rfl⟩,
    by rintro ⟨N, rfl⟩ w hw; exact N.coact_mem hw⟩

/-- A subspace `W` of a comodule has stabilizer Hopf ideal `I` when every `H`-point in the universe
of `H` lies in the `I`-quotient points subgroup if and only if it stabilizes `W`. -/
theorem stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff
    (W : Submodule k M) (I : HopfIdeal k H)
    (h : ∀ (A : Type v) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
          (CommAlgCat.of k A) ↔
        (W.baseChange A).map (Comodule.endOfPoint M g.ofConv) = W.baseChange A) :
    W.stabilizerHopfIdeal H = I := by
  refine HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := _root_.CommHopfAlgCat.of k H) fun A ↦ ?_
  ext g
  have hA := h A g
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker] at hA
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker, hA,
    ← W.stabilizerHopfIdeal_le_ker_iff g]

end Hopf

section Comparison

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Two subspaces of comodules have the same stabilizer Hopf ideal when every `H`-point in the
universe of `H` stabilizes the scalar extension of one if and only if it stabilizes that of the
other. -/
theorem stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff
    {M₁ : Type w₁} {M₂ : Type w₂} [AddCommGroup M₁] [Module k M₁] [Comodule k H M₁]
    [AddCommGroup M₂] [Module k M₂] [Comodule k H M₂]
    (W₁ : Submodule k M₁) (W₂ : Submodule k M₂)
    (h : ∀ (A : Type v) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)),
      (W₁.baseChange A).map (Comodule.endOfPoint M₁ g.ofConv) = W₁.baseChange A ↔
        (W₂.baseChange A).map (Comodule.endOfPoint M₂ g.ofConv) = W₂.baseChange A) :
    W₁.stabilizerHopfIdeal H = W₂.stabilizerHopfIdeal H :=
  stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff W₁ (W₂.stabilizerHopfIdeal H)
    fun A _ _ g ↦ by
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff_toIdeal_le_ker, h A g,
        ← W₂.stabilizerHopfIdeal_le_ker_iff g]

/-- Transporting a comodule along a linear equivalence preserves subspace stabilizer Hopf ideals. -/
theorem stabilizerHopfIdeal_map_transport
    {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module k M] [Comodule k H M]
    [AddCommGroup N] [Module k N] (W : Submodule k M) (e : M ≃ₗ[k] N) :
    (letI : Comodule k H N := Comodule.Transport (R := k) (C := H) e
     (W.map e.toLinearMap).stabilizerHopfIdeal H) = W.stabilizerHopfIdeal H := by
  let _ : Comodule k H N := Comodule.Transport (R := k) (C := H) e
  refine stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff (W.map e.toLinearMap) W
    fun A _ _ g ↦ ?_
  have hcomp : Comodule.endOfPoint N g.ofConv ∘ₗ e.toLinearMap.baseChange A =
      e.toLinearMap.baseChange A ∘ₗ Comodule.endOfPoint M g.ofConv := by
    simpa only [Comodule.transportToHom_toLinearMap] using
      (Comodule.baseChange_comp_endOfPoint
        (Comodule.transportToHom (R := k) (C := H) e) g.ofConv).symm
  have hinj : Function.Injective (e.toLinearMap.baseChange A) :=
    (e.baseChange k A).injective
  rw [Submodule.baseChange_map, ← Submodule.map_comp, hcomp, Submodule.map_comp]
  exact (Submodule.map_injective_of_injective hinj).eq_iff

end Comparison

end Submodule
