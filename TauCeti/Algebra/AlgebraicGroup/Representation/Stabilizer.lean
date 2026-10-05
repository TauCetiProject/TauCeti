/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Antipode
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.Algebra.HopfAlgebra.Antipode
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# The stabilizer of a subspace of a representation

Let `H` be a commutative Hopf algebra over a field `k` and `M` a right `H`-comodule, that is, a
representation of the affine group `G = Spec H`. A subspace `W ≤ M` has a stabilizer: the closed
subgroup of `G` whose points carry `W` onto itself. In coordinates it is cut out by the matrix
coefficients `c(ψ ∘ q, w)` pairing vectors `w ∈ W` with functionals vanishing on `W` (here
`q : M → M ⧸ W` is the quotient map), together with their antipodes.

This file constructs that Hopf ideal and characterizes it in four ways.

* Its points with values in any commutative `k`-algebra `A` are the points whose action carries
  `A ⊗ W` onto itself.
* It is the smallest Hopf ideal containing the coefficients `c(ψ ∘ q, w)`.
* It is zero, so the stabilizer is all of `G`, exactly when `W` is a subcomodule.
* Its Lie algebra consists of the tangent vectors whose differentiated action preserves `W`.

The last statement is the infinitesimal input to the comparison of `G`-stable and
`Lie(G)`-stable subspaces.

## Main declarations

* `Submodule.coact_mem_range_iff_forall_matrixCoefficient_eq_zero`: over a field, the coaction
  of `m` lies in `W ⊗ C` exactly when `m` has no matrix coefficient against a functional
  vanishing on `W`.
* `Submodule.mapsTo_endOfPoint_baseChange_iff`: a point preserves `A ⊗ W` exactly when it
  kills those matrix coefficients.
* `Derivation.apply_matrixCoefficient`: a tangent vector applied to a matrix coefficient is the
  functional applied to the differentiated action.
* `Submodule.stabilizerHopfIdeal`: the Hopf ideal of the stabilizer of `W`.
* `Submodule.stabilizerHopfIdeal_le_ker_iff`: its points are the points carrying `A ⊗ W` onto
  itself.
* `Submodule.stabilizerHopfIdeal_le_iff`: its universal property among Hopf ideals.
* `Submodule.stabilizerHopfIdeal_eq_bot_iff`: it vanishes exactly when `W` is a subcomodule.
* `Submodule.mem_lieSubalgebra_stabilizerHopfIdeal_iff`: its Lie algebra is the stabilizer of
  `W` under the differentiated representation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open scoped TensorProduct
open TauCeti

universe u v w

noncomputable section

namespace Submodule

section Coalgebra

variable {k : Type u} {C : Type v} {M : Type w} [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- Over a field, the coaction of a vector lies in `W ⊗ C` exactly when every matrix coefficient
pairing it with a functional vanishing on `W` is zero. -/
theorem coact_mem_range_iff_forall_matrixCoefficient_eq_zero (W : Submodule k M) (m : M) :
    Comodule.coact (R := k) (C := C) (M := M) m ∈
        LinearMap.range (TensorProduct.map W.subtype (LinearMap.id : C →ₗ[k] C)) ↔
      ∀ ψ : Module.Dual k (M ⧸ W),
        Comodule.matrixCoefficient (R := k) (C := C) (ψ ∘ₗ W.mkQ) m = 0 := by
  have hcontract (ψ : Module.Dual k (M ⧸ W)) :
      TensorProduct.lid k C (ψ.rTensor C (W.mkQ.rTensor C
          (Comodule.coact (R := k) (C := C) (M := M) m))) =
        Comodule.matrixCoefficient (R := k) (C := C) (ψ ∘ₗ W.mkQ) m := by
    rw [Comodule.matrixCoefficient_def, ← LinearMap.rTensor_comp_apply, LinearMap.rTensor_def]
  rw [← LinearMap.rTensor_def, ← rTensor_mkQ, LinearMap.mem_ker]
  constructor
  · intro h ψ
    rw [← hcontract, h, map_zero, map_zero]
  · intro h
    apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero (fun ψ : Module.Dual k (M ⧸ W) ↦ ψ)
      (fun x hx ↦ (Module.forall_dual_apply_eq_zero_iff k x).mp hx)
    intro ψ
    rw [hcontract, h]

end Coalgebra

section Point

variable {k : Type u} {C : Type v} {M : Type w} {A : Type*} [Field k]
variable [Ring C] [Algebra k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M] [CommRing A] [Algebra k A]

/-- An algebra-valued point preserves the scalar extension of `W` exactly when it kills every
matrix coefficient pairing a vector of `W` with a functional vanishing on `W`. -/
theorem mapsTo_endOfPoint_baseChange_iff (W : Submodule k M) (g : C →ₐ[k] A) :
    Set.MapsTo (Comodule.endOfPoint M g) (W.baseChange A) (W.baseChange A) ↔
      ∀ (ψ : Module.Dual k (M ⧸ W)), ∀ w ∈ W,
        g (Comodule.matrixCoefficient (R := k) (C := C) (ψ ∘ₗ W.mkQ) w) = 0 := by
  -- Contracting the vector factor with a functional is evaluation against its base change.
  have hcomponent (φ : Module.Dual k M) (z : A ⊗[k] M) :
      LinearMap.tensorComponent φ z =
        TauCeti.Module.Dual.baseChangeEvaluation (1 ⊗ₜ[k] φ) z := by
    induction z with
    | tmul a m => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hpoint (φ : Module.Dual k M) (m : M) :
      LinearMap.tensorComponent φ (Comodule.endOfPoint M g (1 ⊗ₜ[k] m)) =
        g (Comodule.matrixCoefficient (R := k) (C := C) φ m) := by
    rw [hcomponent, Comodule.baseChangeEvaluation_endOfPoint_tmul, one_mul, one_mul]
  have hrange : (W.baseChange A : Set (A ⊗[k] M)) =
      LinearMap.ker (W.mkQ.lTensor A) := by
    ext z
    simp only [SetLike.mem_coe, lTensor_mkQ, baseChange, LinearMap.mem_range,
      LinearMap.baseChange_eq_ltensor]
  constructor
  · intro h ψ w hw
    have hz := h (tmul_mem_baseChange_of_mem (1 : A) hw)
    rw [hrange, SetLike.mem_coe, LinearMap.mem_ker] at hz
    have h0 := LinearMap.tensorComponent_map ψ (LinearMap.id : A →ₗ[k] A) W.mkQ
      (Comodule.endOfPoint M g (1 ⊗ₜ[k] w))
    rw [← LinearMap.lTensor_def, hz, map_zero, LinearMap.id_apply] at h0
    rw [← hpoint, h0]
  · intro h
    have hgen (w : M) (hw : w ∈ W) :
        Comodule.endOfPoint M g (1 ⊗ₜ[k] w) ∈ W.baseChange A := by
      rw [← SetLike.mem_coe, hrange, SetLike.mem_coe, LinearMap.mem_ker]
      apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
      intro ψ
      have h0 := LinearMap.tensorComponent_map ψ (LinearMap.id : A →ₗ[k] A) W.mkQ
        (Comodule.endOfPoint M g (1 ⊗ₜ[k] w))
      rw [← LinearMap.lTensor_def, LinearMap.id_apply] at h0
      rw [h0, map_zero, hpoint, h ψ w hw]
    intro z hz
    rw [SetLike.mem_coe, baseChange_eq_span] at hz
    rw [SetLike.mem_coe]
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hgen w hw
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

end Point

end Submodule

namespace Derivation

variable {k : Type u} {H : Type v} {M : Type w} [Field k] [CommRing H] [Bialgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- A tangent vector at the identity, applied to a matrix coefficient `c(φ, m)`, is the
functional `φ` applied to the differentiated action of the tangent vector on `m`. -/
theorem apply_matrixCoefficient (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (φ : Module.Dual k M) (m : M) :
    Bialgebra.CounitAlgebra.algEquivSelf k H k
        (d (Comodule.matrixCoefficient (R := k) (C := H) φ m)) =
      φ (Comodule.differential (R := k) (H := H) (M := M) d m) := by
  rw [Comodule.differential_apply, Comodule.matrixCoefficient_def]
  induction Comodule.coact (R := k) (C := H) (M := M) m with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n h =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul, map_smul,
      LinearMap.tensorComponent_tmul, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      Derivation.coeFn_coe]
    rw [LinearMap.map_smul_of_tower φ, smul_eq_mul, mul_comm]
    -- The scalar action on the counit synonym is that of `k` on itself; the coefficient
    -- identification is `k`-linear for it.
    exact (Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearEquiv.map_smul (φ n) (d h)

end Derivation

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
  apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero (fun ψ : Module.Dual k (M ⧸ W) ↦ ψ)
    (fun x hx ↦ (Module.forall_dual_apply_eq_zero_iff k x).mp hx)
  intro ψ
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
  · exact map_mkₐ_comul_matrixCoefficient W ψ w.2
  · rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, map_mkₐ_map_antipode_comm,
      map_mkₐ_comul_matrixCoefficient W ψ w.2, map_zero, map_zero]

/-- The counit vanishes on the stabilizer generators. -/
private theorem counit_stabilizerGenerators (W : Submodule k M) {x : H}
    (hx : x ∈ stabilizerGenerators H W) : Coalgebra.counit (R := k) x = 0 := by
  rcases hx with ⟨⟨ψ, w⟩, rfl⟩ | ⟨_, ⟨⟨ψ, w⟩, rfl⟩, rfl⟩ <;>
  simp [Comodule.counit_matrixCoefficient, (Submodule.Quotient.mk_eq_zero W).mpr w.2]

variable (H) in
/-- The Hopf ideal of the stabilizer of a subspace `W` of a comodule `M`.

It is generated by the matrix coefficients `c(ψ ∘ q, w)`, for `w ∈ W` and functionals `ψ` on
`M ⧸ W`, together with their antipodes. Contravariantly, it cuts out the closed subgroup of
`Spec H` preserving `W`. -/
def stabilizerHopfIdeal (W : Submodule k M) : HopfIdeal k H :=
  HopfIdeal.ofSpan (stabilizerGenerators H W)
    (fun x hx ↦ by
      have hker := HopfIdeal.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal
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
  · exact h ψ w w.2
  · exact J.antipode_mem (h ψ w w.2)

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
      rw [hcoeff, mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr (h w w.2), map_zero]
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
    rw [WithConv.convInv_def, WithConv.ofConv_toConv, AlgHom.antipodeComp_apply]
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
    · exact (mapsTo_endOfPoint_baseChange_iff W g.ofConv).mp hg ψ w w.2
    · rw [SetLike.mem_coe, RingHom.mem_ker, ← hinv]
      exact (mapsTo_endOfPoint_baseChange_iff W (g⁻¹).ofConv).mp hginv ψ w w.2

end Hopf

end Submodule
