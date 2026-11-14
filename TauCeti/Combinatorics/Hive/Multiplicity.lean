/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.LittlewoodRichardson
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.LittlewoodRichardson
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.Rep.DirectSum.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# Tensor-product multiplicities, Schur expansions, and invariants via integer hives

Combining the object-level hive-to-Littlewood–Richardson equivalence of
`TauCeti.Combinatorics.Hive.LittlewoodRichardson` with Stembridge's Littlewood–Richardson rule for
Schur polynomials (`TauCeti.diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau`) and the
rational Weyl-module decomposition (`TauCeti.nonempty_equiv_tprod_rationalWeylRep`), this file
identifies integer hive counts with tensor-product multiplicities and invariant dimensions of
`GL n ℂ`:

* **Schur-polynomial expansion** (`TauCeti.Hive.schur_mul_eq_finsum_hiveCount`): for polynomial
  dominant weights `λ, μ` of `GL n` and any commutative semiring `R`, the product
  `s_λ · s_μ` in `n` variables expands as the finitely supported sum
  `∑ᶠ γ : DominantWeight n, (hiveCount (productBoundary λ μ γ) : R) • s_γ`. In strictly more than
  `n` variables this fails (`TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`), since the
  rank-`n` hive model suppresses shapes with more than `n` rows.
* **Intertwiner multiplicity** (`TauCeti.Hive.finrank_hom_eq_hiveCount`): for arbitrary signed
  dominant weights `λ, μ, γ` of `GL n ℂ`, the complex dimension of the intertwiner space
  `rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n λ ⊗ rationalWeylFDRep ℂ n μ` in
  `FDRep ℂ (GL (Fin n) ℂ)` equals `hiveCount (productBoundary λ μ γ)`.
* **Input symmetry** (`TauCeti.Hive.hiveCount_comm`): `hiveCount (productBoundary λ μ γ) =
  hiveCount (productBoundary μ λ γ)`, read directly from the braiding of `FDRep ℂ (GL (Fin n) ℂ)`.
* **Trilinear invariants** (`TauCeti.Hive.finrank_invariants_eq_hiveCount`): for arbitrary signed
  dominant weights `λ, μ, ν` of `GL n ℂ`, the invariant dimension
  `dim_ℂ Hom(𝟙_, V_λ ⊗ V_μ ⊗ V_ν)` equals the cyclic hive count `hiveCount ![λ.1, μ.1, ν.1]`.

## Main results

* `TauCeti.Hive.schur_mul_eq_finsum_hiveCount`: finite-alphabet Schur-polynomial expansion with
  `hiveCount` coefficients.
* `TauCeti.Hive.finrank_hom_eq_hiveCount`: Hom-space dimension between rational Weyl modules equals
  `hiveCount (productBoundary lam μ γ)`.
* `TauCeti.Hive.hiveCount_comm`: symmetry of `hiveCount (productBoundary l m p)` in `l` and `m`.
* `TauCeti.Hive.finrank_invariants_eq_hiveCount`: dimension of `GL n ℂ`-invariants in
  `V_lam ⊗ V_μ ⊗ V_ν` equals `hiveCount ![lam.1, μ.1, ν.1]`.
* `TauCeti.Hive.finrank_hom_two_std_std`, `TauCeti.Hive.finrank_invariants_two_std_checks`,
  `TauCeti.Hive.finrank_hom_one`, `TauCeti.Hive.finrank_hom_zero`, and
  `TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`: concrete rank-`0`, rank-`1`, and
  rank-`2` representation-theoretic and sharpness checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of `GL_n(ℂ)` tensor products I: Proof of the
  saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Theorem 4 and Appendix 2.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using the
  octahedron recurrence*, Electron. J. Combin. **11** (2004), Research Paper 61, Theorem 1.
-/

public section

open CategoryTheory MonoidalCategory Matrix MvPolynomial YoungDiagram
open scoped DirectSum

namespace TauCeti.Hive

/-! ### Finite-alphabet Schur-polynomial expansion -/

/-- **The hive model of the Littlewood–Richardson rule for Schur polynomials**: for polynomial
dominant weights `λ` and `μ` of `GL n` and any commutative semiring `R`, the product `s_λ · s_μ` in
`n` variables expands over all dominant weights `γ` of `GL n` with coefficients
`hiveCount (productBoundary λ μ γ)`. Non-polynomial weights `γ` have hive count zero, and only
finitely many `γ` contribute. -/
theorem schur_mul_eq_finsum_hiveCount {n : ℕ} {R : Type*} [CommSemiring R]
    (lam μ : DominantWeight n) (hl : lam.IsPolynomial) (hm : μ.IsPolynomial) :
    diagramSchurPoly n R lam.shape * diagramSchurPoly n R μ.shape =
      ∑ᶠ γ : DominantWeight n,
        (hiveCount (productBoundary lam μ γ) : R) •
          diagramSchurPoly n R γ.shape := by
  classical
  let Sub := {ν : (lam.shape.card + μ.shape.card).Partition // (ofPartition ν).colLen 0 ≤ n}
  let emb : Sub → DominantWeight n := fun ν => weightOfShape n (ofPartition ν.1)
  have hemb_inj : Function.Injective emb := fun ν₁ ν₂ h => Subtype.ext <|
    YoungDiagram.ofPartition_injective <|
      calc ofPartition ν₁.1 = (emb ν₁).shape := (shape_weightOfShape ν₁.2).symm
        _ = (emb ν₂).shape := congrArg DominantWeight.shape h
        _ = ofPartition ν₂.1 := shape_weightOfShape ν₂.2
  have hsupp : Function.support
      (fun γ : DominantWeight n =>
        (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly n R γ.shape) ⊆
      (Finset.univ.image emb : Finset (DominantWeight n)) := by
    intro γ hγ
    rw [Function.mem_support] at hγ
    have hcnt : hiveCount (productBoundary lam μ γ) ≠ 0 := fun h0 => by
      simp [h0] at hγ
    rw [hiveCount_productBoundary_of_isPolynomial hl hm] at hcnt
    by_cases hpol : γ.IsPolynomial
    · simp only [hpol, ↓reduceIte] at hcnt
      have hne : Nonempty (LRTableau lam.shape γ.shape μ.shape) :=
        not_isEmpty_iff.mp fun _ => hcnt Nat.card_of_isEmpty
      obtain ⟨T⟩ := hne
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨⟨γ.shape.toPartition T.card_eq, by simp⟩, Finset.mem_univ _, ?_⟩)
      simp [emb, weightOfShape_shape hpol]
    · simp [hpol] at hcnt
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image fun _ _ _ _ h => hemb_inj h,
    diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun ν : (lam.shape.card + μ.shape.card).Partition => (ofPartition ν).colLen 0 ≤ n)]
  have hzero : (∑ ν ∈ Finset.univ.filter
      (fun ν : (lam.shape.card + μ.shape.card).Partition => ¬ (ofPartition ν).colLen 0 ≤ n),
      Nat.card (LRTableau lam.shape (ofPartition ν) μ.shape) •
        diagramSchurPoly n R (ofPartition ν)) = 0 := by
    refine Finset.sum_eq_zero fun ν hν => ?_
    have hlt : n < (ofPartition ν).colLen 0 := Nat.lt_of_not_le (Finset.mem_filter.mp hν).2
    rw [diagramSchurPoly_eq_zero_of_lt_colLen hlt, smul_zero]
  rw [hzero, add_zero, Finset.sum_subtype (p := fun ν => (ofPartition ν).colLen 0 ≤ n) _
    (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hsh : (emb ν).shape = ofPartition ν.1 := shape_weightOfShape ν.2
  have hpol : (emb ν).IsPolynomial := isPolynomial_weightOfShape n (ofPartition ν.1)
  rw [hiveCount_productBoundary_of_isPolynomial hl hm]
  simp only [hpol, ↓reduceIte, hsh, Nat.cast_smul_eq_nsmul]

/-! ### Hom-space multiplicities and invariants on rational Weyl modules -/

/-- Direct-sum decomposition of Hom-space dimensions in `FDRep ℂ (GL (Fin n) ℂ)` from an unbundled
`Representation.Equiv` with a finite direct sum. -/
private theorem finrank_hom_of_equiv_directSum {n : ℕ} {ι : Type*} [Fintype ι]
    (X Y : FDRep ℂ (GL (Fin n) ℂ)) (Z : ι → FDRep ℂ (GL (Fin n) ℂ))
    (e : Representation.Equiv Y.ρ (Representation.directSum fun p => (Z p).ρ)) :
    Module.finrank ℂ (X ⟶ Y) = ∑ p : ι, Module.finrank ℂ (X ⟶ Z p) := by
  let homEquiv (A B : FDRep ℂ (GL (Fin n) ℂ)) :
      (A ⟶ B) ≃ₗ[ℂ] Representation.IntertwiningMap A.ρ B.ρ :=
    (FDRep.forget₂HomLinearEquiv A B).symm ≪≫ₗ Rep.homLinearEquiv _ _
  let totalEquiv : (X ⟶ Y) ≃ₗ[ℂ] ∀ p : ι, (X ⟶ Z p) :=
    homEquiv X Y ≪≫ₗ
      Representation.Equiv.intertwiningMapCongr (.refl X.ρ) e ≪≫ₗ
      Representation.IntertwiningMap.directSumLinearEquiv X.ρ (fun p => (Z p).ρ) ≪≫ₗ
      LinearEquiv.piCongrRight fun p => (homEquiv X (Z p)).symm
  rw [totalEquiv.finrank_eq, Module.finrank_pi_fintype]

/-- Distributivity of `Representation.tprod` over `Representation.directSum` on the left. -/
private noncomputable def tprodDirectSumLeftEquiv {k G ι : Type*} [CommRing k] [Monoid G]
    [DecidableEq ι] {W : ι → Type*} [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]
    {U : Type*} [AddCommMonoid U] [Module k U]
    (τ : ∀ i, Representation k G (W i)) (σ : Representation k G U) :
    Representation.Equiv ((Representation.directSum τ).tprod σ)
      (Representation.directSum fun i => (τ i).tprod σ) :=
  .mk (TensorProduct.directSumLeft k k W U) fun g =>
    TensorProduct.ext' fun x y => DFinsupp.ext fun i => by simp [Representation.directSum_apply]

/-- For a diagram `ν` with at most `n` rows, bounded `λ`-Yamanouchi tableaux of content `ν - λ`
have the same cardinality as `LRTableau λ ν μ`. -/
private theorem card_boundedYamanouchi_eq_natCard_lrTableau {n : ℕ} {lam μ ν : YoungDiagram}
    (hν : ν.colLen 0 ≤ n) [Fintype {T : BoundedSSYT n μ //
      T.1.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + T.1.content i = ν.rowLen i}] :
    Fintype.card {T : BoundedSSYT n μ //
      T.1.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + T.1.content i = ν.rowLen i} =
      Nat.card (LRTableau lam ν μ) := by
  rw [natCard_lrTableau_eq_natCard_isYamanouchi, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr <| Equiv.subtypeSubtypeEquivSubtype
    (q := fun T : SemistandardYoungTableau μ =>
      T.IsYamanouchi lam ∧ ∀ i, lam.rowLen i + T.content i = ν.rowLen i)
    fun hT i c hc =>
      (SemistandardYoungTableau.apply_lt_colLen_zero_of_rowLen_add_content_eq hT.2 hc).trans_le hν

/-- Schur's lemma combined with highest-weight injectivity on `rationalWeylFDRep ℂ n`. -/
private theorem finrank_hom_rationalWeylFDRep {n : ℕ} (γ σ : DominantWeight n) :
    Module.finrank ℂ (rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n σ) =
      if γ = σ then 1 else 0 := by
  classical
  rw [FDRep.finrank_hom_simple_simple, if_congr (nonempty_iso_rationalWeylFDRep_iff ℂ) rfl rfl]

open scoped Classical in
/-- Partition-indexed multiplicity sum matching `hiveCount (productBoundary lam μ γ)`. -/
private theorem sum_natCard_lrTableau_shift_eq_hiveCount {n : ℕ} (lam μ γ : DominantWeight n) :
    (∑ ν : {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
        (ofPartition ν).colLen 0 ≤ n},
      if γ = (weightOfShape n (ofPartition ν.1)).shift (lam.detShift + μ.detShift) then
        Nat.card (LRTableau lam.detShiftShape (ofPartition ν.1) μ.detShiftShape)
      else 0) = hiveCount (productBoundary lam μ γ) := by
  let Sub := {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
    (ofPartition ν).colLen 0 ≤ n}
  let w (ν : Sub) : DominantWeight n :=
    (weightOfShape n (ofPartition ν.1)).shift (lam.detShift + μ.detShift)
  rw [hiveCount_productBoundary]
  split_ifs with hdet
  · set γ' := γ.shift (-(lam.detShift + μ.detShift))
    have hγ' : γ'.IsPolynomial := by
      rw [DominantWeight.isPolynomial_iff_zero_le_detShift]
      cases n with
      | zero => simp
      | succ m => rw [DominantWeight.detShift_shift]; omega
    have heq_iff (ν : Sub) : γ = w ν ↔ γ'.shape = ofPartition ν.1 :=
      ⟨fun h => by
        have h' : γ' = weightOfShape n (ofPartition ν.1) := by simp [γ', h, w]
        rw [h', shape_weightOfShape ν.2],
      fun h => by
        have h' : weightOfShape n (ofPartition ν.1) = γ' := by rw [← h, weightOfShape_shape hγ']
        simp [w, h', γ']⟩
    by_cases hcard : γ'.shape.card = lam.detShiftShape.card + μ.detShiftShape.card
    · let ν₀ : Sub := ⟨γ'.shape.toPartition hcard, by simp⟩
      rw [Finset.sum_eq_single ν₀]
      · have h0 : γ = w ν₀ := (heq_iff ν₀).mpr (YoungDiagram.ofPartition_toPartition hcard).symm
        dsimp only [w] at h0; simp only [h0, ↓reduceIte]; simp [ν₀]
      · intro ν _ hne
        have hne' : γ ≠ w ν := fun h => hne <| Subtype.ext <| YoungDiagram.ofPartition_injective <|
          by rw [← (heq_iff ν).mp h, YoungDiagram.ofPartition_toPartition]
        dsimp only [w] at hne'; simp only [hne', ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ ν₀) h
    · rw [Finset.sum_eq_zero]
      · have := isEmpty_lrTableau_of_card_ne hcard; exact Nat.card_of_isEmpty.symm
      · intro ν _
        have hne' : γ ≠ w ν := fun h => hcard <| by
          rw [(heq_iff ν).mp h, YoungDiagram.card_ofPartition]
        dsimp only [w] at hne'; simp only [hne', ↓reduceIte]
  · refine Finset.sum_eq_zero fun ν _ => ?_
    have hne' : γ ≠ w ν := fun h => hdet <| by
      cases n with
      | zero => simp
      | succ m =>
        have h0 := (DominantWeight.isPolynomial_iff_zero_le_detShift _).mp
          (isPolynomial_weightOfShape (m + 1) (ofPartition ν.1))
        rw [h, DominantWeight.detShift_shift]; omega
    dsimp only [w] at hne'; simp only [hne', ↓reduceIte]

/-- **The hive model of tensor-product multiplicities for `GL n ℂ`**: for all dominant weights
`λ, μ, γ` of `GL n ℂ`, the complex dimension of the space of intertwiners from `V_γ` to
`V_λ ⊗ V_μ` in `FDRep ℂ (GL (Fin n) ℂ)` is `hiveCount (productBoundary λ μ γ)`. -/
theorem finrank_hom_eq_hiveCount {n : ℕ} (lam μ γ : DominantWeight n) :
    Module.finrank ℂ (rationalWeylFDRep ℂ n γ ⟶
        rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) =
      hiveCount (productBoundary lam μ γ) := by
  classical
  let Sub := {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
    (ofPartition ν).colLen 0 ≤ n}
  let Fib (ν : Sub) := {T : BoundedSSYT n μ.detShiftShape //
    T.1.IsYamanouchi lam.detShiftShape ∧
      ∀ i, lam.detShiftShape.rowLen i + T.1.content i = (ofPartition ν.1).rowLen i}
  let w (ν : Sub) : DominantWeight n :=
    (weightOfShape n (ofPartition ν.1)).shift (lam.detShift + μ.detShift)
  obtain ⟨e⟩ := nonempty_equiv_tprod_rationalWeylRep n lam μ
  have he : Representation.Equiv
      (rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ).ρ
      (Representation.directSum fun p : Σ ν : Sub, Fib ν =>
        (rationalWeylFDRep ℂ n (w p.1)).ρ) :=
    (Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun _ => LinearMap.ext fun _ => rfl).trans e
  rw [finrank_hom_of_equiv_directSum _ _ _ he, Fintype.sum_sigma,
    ← sum_natCard_lrTableau_shift_eq_hiveCount lam μ γ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [finrank_hom_rationalWeylFDRep, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_boole]
  dsimp only [w, Fib]
  rw [card_boundedYamanouchi_eq_natCard_lrTableau ν.2]

/-- **Symmetry of hive counts in the two inputs**: `c^p_{l, m} = c^p_{m, l}` for all dominant
weights `l, m, p` of `GL n`. -/
theorem hiveCount_comm {n : ℕ} (l m p : DominantWeight n) :
    hiveCount (productBoundary l m p) = hiveCount (productBoundary m l p) := by
  rw [← finrank_hom_eq_hiveCount, ← finrank_hom_eq_hiveCount]
  exact (Linear.homCongr ℂ (Iso.refl _)
    (β_ (rationalWeylFDRep ℂ n l) (rationalWeylFDRep ℂ n m))).finrank_eq

/-- The tensor unit of `FDRep ℂ (GL (Fin n) ℂ)` is isomorphic to the rational Weyl module of the
zero dominant weight. -/
private theorem nonempty_iso_tensorUnit_rationalWeylFDRep_zero (n : ℕ) :
    Nonempty (𝟙_ (FDRep ℂ (GL (Fin n) ℂ)) ≅ rationalWeylFDRep ℂ n 0) := by
  let _ (l : DominantWeight n) :
      AddCommGroup (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule := inferInstance
  have h0 : (0 : DominantWeight n) = (weightOfShape n ⊥).shift 0 := by ext i; simp
  obtain ⟨e⟩ := IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (isRationalRep_detPowerRep (n := n) 0) (isRationalRep_rationalWeylRep n 0) fun t => by
      have hlhs : (detPowerRep ℂ n 0).character (diagGL t) = 1 := by
        rw [detPowerRep_zero]
        have htriv : (1 : Representation ℂ (GL (Fin n) ℂ) ℂ) =
            Representation.trivial ℂ (GL (Fin n) ℂ) ℂ :=
          MonoidHom.ext fun _ => LinearMap.ext fun _ => rfl
        rw [htriv, Representation.char_trivial, Module.finrank_self, Nat.cast_one]
      have hrhs : Representation.character
          (V := ↥(weylModuleOfShape ℂ n (0 : DominantWeight n).detShiftShape).toSubmodule)
          (rationalWeylRep ℂ n 0) (diagGL t) = 1 := by
        rw [h0, char_rationalWeylRep_shift_weightOfShape_diagonal ℂ n (by simp) 0 t,
          diagramSchurPoly_bot]
        simp
      rw [hlhs, hrhs]
  refine ⟨e.toLinearEquiv.toFDRepIso fun g x => ?_⟩
  have hunit : (𝟙_ (FDRep ℂ (GL (Fin n) ℂ))).ρ g x = detPowerRep ℂ n 0 g x := by
    rw [FDRep.tensorUnit_ρ, detPowerRep_zero]
    rfl
  rw [hunit]
  exact LinearMap.ext_iff.mp (e.toIntertwiningMap.isIntertwining' g) x

/-- Unbundled tensor-product identification for `FDRep.ρ` on `X ⊗ Y`. -/
private noncomputable def fdrepTensorEquiv {n : ℕ} (X Y : FDRep ℂ (GL (Fin n) ℂ)) :
    Representation.Equiv (X ⊗ Y).ρ (Representation.tprod X.ρ Y.ρ) :=
  .mk (LinearEquiv.refl ℂ ↥(X ⊗ Y)) fun g => LinearMap.ext fun _ => by
    rw [FDRep.tensor_ρ]
    rfl

/-- **The invariant form of the hive model for `GL n ℂ`**: for all dominant weights `λ, μ, ν` of
`GL n ℂ`, the complex dimension of the space of `GL n ℂ`-invariants
`𝟙_ (FDRep ℂ (GL (Fin n) ℂ)) ⟶ V_λ ⊗ V_μ ⊗ V_ν` equals the number of integer hives with cyclic
boundary `![λ.1, μ.1, ν.1]`. -/
theorem finrank_invariants_eq_hiveCount {n : ℕ} (lam μ ν : DominantWeight n) :
    Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin n) ℂ)) ⟶
        rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ ⊗
          rationalWeylFDRep ℂ n ν) =
      hiveCount ![lam.1, μ.1, ν.1] := by
  classical
  obtain ⟨i₀⟩ := nonempty_iso_tensorUnit_rationalWeylFDRep_zero n
  rw [(Linear.homCongr ℂ i₀ (α_ _ _ _).symm).finrank_eq]
  let Sub := {κ : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
    (ofPartition κ).colLen 0 ≤ n}
  let Fib (κ : Sub) := {T : BoundedSSYT n μ.detShiftShape //
    T.1.IsYamanouchi lam.detShiftShape ∧
      ∀ i, lam.detShiftShape.rowLen i + T.1.content i = (ofPartition κ.1).rowLen i}
  let w (p : Σ κ : Sub, Fib κ) : DominantWeight n :=
    (weightOfShape n (ofPartition p.1.1)).shift (lam.detShift + μ.detShift)
  obtain ⟨e₁₂⟩ := nonempty_equiv_tprod_rationalWeylRep n lam μ
  let eTensor₁₂ := fdrepTensorEquiv (rationalWeylFDRep ℂ n lam) (rationalWeylFDRep ℂ n μ)
  let eTensor₃ := fdrepTensorEquiv
    (rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) (rationalWeylFDRep ℂ n ν)
  let eSumTensor : Representation.Equiv
      (Representation.directSum fun p =>
        Representation.tprod (rationalWeylFDRep ℂ n (w p)).ρ (rationalWeylFDRep ℂ n ν).ρ)
      (Representation.directSum fun p =>
        (rationalWeylFDRep ℂ n (w p) ⊗ rationalWeylFDRep ℂ n ν).ρ) :=
    .mk (LinearEquiv.refl ℂ (⨁ p, ↥(rationalWeylFDRep ℂ n (w p) ⊗ rationalWeylFDRep ℂ n ν)))
      fun g => LinearMap.ext fun x => DFinsupp.ext fun p => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.directSum_apply,
          DirectSum.lmap_apply, Representation.tprod_apply]
        rw [FDRep.tensor_ρ]
        rfl
  have he₃ : Representation.Equiv
      ((rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) ⊗ rationalWeylFDRep ℂ n ν).ρ
      (Representation.directSum fun p =>
        (rationalWeylFDRep ℂ n (w p) ⊗ rationalWeylFDRep ℂ n ν).ρ) :=
    eTensor₃.trans <| ((eTensor₁₂.trans e₁₂).tprod (.refl _)).trans <|
      (tprodDirectSumLeftEquiv _ _).trans eSumTensor
  have hrot (σ : DominantWeight n) :
      hiveCount (productBoundary σ ν 0) = if ν.dual = σ then 1 else 0 := by
    have hb : productBoundary σ ν 0 = fun s => productBoundary 0 σ ν.dual (s + 1) := by
      ext s i; fin_cases s <;> simp
    rw [hb, hiveCount_rotate, hiveCount_productBoundary_zero_left]
  have hdual : productBoundary lam μ ν.dual = ![lam.1, μ.1, ν.1] := by
    ext s i; fin_cases s <;> simp
  rw [finrank_hom_of_equiv_directSum _ _ _ he₃]
  simp only [finrank_hom_eq_hiveCount, hrot, ← finrank_hom_rationalWeylFDRep]
  rw [← finrank_hom_of_equiv_directSum _ _ (fun p => rationalWeylFDRep ℂ n (w p))
      (eTensor₁₂.trans e₁₂), finrank_hom_eq_hiveCount, hdual]

/-! ### Concrete representation-theoretic and finite-alphabet checks -/

/-- Rank-`0` check: on `GL 0 ℂ`, every intertwiner space `V_γ ⟶ V_λ ⊗ V_μ` and every trilinear
invariant space `𝟙_ ⟶ V_λ ⊗ V_μ ⊗ V_ν` is one-dimensional, matching the unique empty hive. -/
theorem finrank_hom_zero (lam μ γ ν : DominantWeight 0) :
    Module.finrank ℂ (rationalWeylFDRep ℂ 0 γ ⟶
        rationalWeylFDRep ℂ 0 lam ⊗ rationalWeylFDRep ℂ 0 μ) = 1 ∧
      Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin 0) ℂ)) ⟶
        rationalWeylFDRep ℂ 0 lam ⊗ rationalWeylFDRep ℂ 0 μ ⊗
          rationalWeylFDRep ℂ 0 ν) = 1 := by
  rw [finrank_hom_eq_hiveCount, finrank_invariants_eq_hiveCount, hiveCount_rank_zero,
    hiveCount_rank_zero]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- Rank-`1` check: on `GL 1 ℂ`, `Hom(V_g, V_a ⊗ V_b)` has dimension `1` when `g = a + b` and `0`
otherwise. -/
theorem finrank_hom_one (a b g : DominantWeight 1) :
    Module.finrank ℂ (rationalWeylFDRep ℂ 1 g ⟶
        rationalWeylFDRep ℂ 1 a ⊗ rationalWeylFDRep ℂ 1 b) =
      if g = a + b then 1 else 0 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_one_productBoundary]

/-- Rank-`2` hive classification for `λ = μ = (1, 0)`: `hiveCount (productBoundary λ μ γ)` is `1`
for `γ = (2, 0)` and `γ = (1, 1)`, and `0` for every other dominant weight `γ`. -/
theorem hiveCount_two_std_std_eq (γ : DominantWeight 2) :
    hiveCount (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ γ) =
      if γ = ⟨![2, 0], by decide⟩ ∨ γ = ⟨![1, 1], by decide⟩ then 1 else 0 := by
  let std : DominantWeight 2 := ⟨![1, 0], by decide⟩
  let sym₂ : DominantWeight 2 := ⟨![2, 0], by decide⟩
  let det₂ : DominantWeight 2 := ⟨![1, 1], by decide⟩
  have hstd : std.IsPolynomial := by rw [DominantWeight.isPolynomial_def]; decide
  rcases eq_or_ne γ sym₂ with rfl | hne₂
  · dsimp only [sym₂]
    simp only [true_or, ↓reduceIte]
    rw [← card_fixedIntegerHive]
    exact Fintype.card_eq_one_iff.mpr ⟨⟨exampleTwo, boundary_exampleTwo⟩,
      fun h => Subtype.ext (boundary_injective_two (h.2.trans boundary_exampleTwo.symm))⟩
  · rcases eq_or_ne γ det₂ with rfl | hne₁
    · dsimp only [det₂]
      simp only [or_true, ↓reduceIte]
      exact hiveCount_two_std_std_det
    · dsimp only [sym₂, det₂] at hne₂ hne₁
      simp only [hne₂, hne₁, or_self, ↓reduceIte]
      refine hiveCount_eq_zero_iff.mpr ⟨fun ⟨h, hb⟩ => ?_⟩
      have hpol : γ.IsPolynomial := isPolynomial_of_productBoundary hb hstd hstd
      have h0 : 0 ≤ γ.1 1 := (DominantWeight.isPolynomial_def γ).mp hpol 1
      have hanti : γ.1 1 ≤ γ.1 0 := γ.antitone (by decide)
      have hsum := sum_eq_of_productBoundary hb
      simp only [Fin.sum_univ_two] at hsum
      change (1 : ℤ) + 0 + (1 + 0) = γ.1 0 + γ.1 1 at hsum
      rcases (by omega : (γ.1 0 = 2 ∧ γ.1 1 = 0) ∨ (γ.1 0 = 1 ∧ γ.1 1 = 1)) with
        ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · exact hne₂ (Subtype.ext (funext fun i => by fin_cases i <;> assumption))
      · exact hne₁ (Subtype.ext (funext fun i => by fin_cases i <;> assumption))

/-- Rank-`2` tensor-product check: in `FDRep ℂ (GL (Fin 2) ℂ)`, `V_{(1, 0)} ⊗ V_{(1, 0)}` contains
`V_{(2, 0)}` and `V_{(1, 1)}` each with multiplicity `1` and every other `V_γ` with multiplicity
`0`. -/
theorem finrank_hom_two_std_std (γ : DominantWeight 2) :
    Module.finrank ℂ (rationalWeylFDRep ℂ 2 γ ⟶
        rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩) =
      if γ = ⟨![2, 0], by decide⟩ ∨ γ = ⟨![1, 1], by decide⟩ then 1 else 0 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_two_std_std_eq]

/-- Rank-`2` trilinear invariant check: `dim_ℂ (V_{(1, 0)} ⊗ V_{(1, 0)} ⊗ V_{(-1, -1)})^{GL 2 ℂ} =
1` (via `det⁻¹`), whereas `dim_ℂ (V_{(1, 0)} ⊗ V_{(1, 0)} ⊗ V_{(0, 0)})^{GL 2 ℂ} = 0` (nonzero
total degree). -/
theorem finrank_invariants_two_std_checks :
    Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin 2) ℂ)) ⟶
        rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![-1, -1], by decide⟩) = 1 ∧
      Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin 2) ℂ)) ⟶
        rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![0, 0], by decide⟩) = 0 := by
  rw [finrank_invariants_eq_hiveCount, finrank_invariants_eq_hiveCount]
  constructor
  · have hb : ![(⟨![1, 0], by decide⟩ : DominantWeight 2).1,
        (⟨![1, 0], by decide⟩ : DominantWeight 2).1,
        (⟨![-1, -1], by decide⟩ : DominantWeight 2).1] =
        productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩ := by
      ext s i; fin_cases s <;> fin_cases i <;> simp
    rw [hb]
    exact hiveCount_two_std_std_det
  · refine hiveCount_eq_zero_of_sum_ne_zero ?_
    simp [Fin.sum_univ_three, Fin.sum_univ_two]

private theorem shape_eq_of_one_two (w₁ : DominantWeight 1) (w₂ : DominantWeight 2)
    (h0 : w₁.1 0 = w₂.1 0) (h1 : w₂.1 1 = 0) : w₁.shape = w₂.shape := by
  refine YoungDiagram.rowLen_injective (funext fun i => ?_)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have a := w₁.rowLen_shape 0
    have b := w₂.rowLen_shape 0
    simp only [Fin.val_zero, h0] at a b
    omega
  · rcases eq_or_ne i 1 with rfl | hi₁
    · have a := w₁.rowLen_shape_eq_zero_of_le le_rfl
      have b := w₂.rowLen_shape 1
      simp only [Fin.val_one, h1] at b
      omega
    · rw [w₁.rowLen_shape_eq_zero_of_le (by omega), w₂.rowLen_shape_eq_zero_of_le (by omega)]

/-- Sharpness of the `n`-variable alphabet in `schur_mul_eq_finsum_hiveCount`: for rank `1` weights
`λ = μ = (1)` evaluated in `2` variables, `s_{(1)}² = s_{(2)} + s_{(1, 1)}`, whereas the rank-`1`
hive sum produces only `s_{(2)}` and omits the nonzero term `s_{(1, 1)}`. -/
theorem schur_mul_two_vars_ne_finsum_hiveCount_one :
    let ω : DominantWeight 1 := ⟨![1], by decide⟩
    diagramSchurPoly 2 ℤ ω.shape * diagramSchurPoly 2 ℤ ω.shape ≠
      ∑ᶠ γ : DominantWeight 1,
        (hiveCount (productBoundary ω ω γ) : ℤ) • diagramSchurPoly 2 ℤ γ.shape := by
  intro ω heq
  let std₂ : DominantWeight 2 := ⟨![1, 0], by decide⟩
  let sym₂ : DominantWeight 2 := ⟨![2, 0], by decide⟩
  let det₂ : DominantWeight 2 := ⟨![1, 1], by decide⟩
  have hstd₂ : std₂.IsPolynomial := by rw [DominantWeight.isPolynomial_def]; decide
  have hrhs₁ : (∑ᶠ γ : DominantWeight 1,
      (hiveCount (productBoundary ω ω γ) : ℤ) • diagramSchurPoly 2 ℤ γ.shape) =
      diagramSchurPoly 2 ℤ sym₂.shape := by
    rw [finsum_eq_single _ (ω + ω)]
    · rw [shape_eq_of_one_two (ω + ω) sym₂ rfl rfl]
      simp [hiveCount_one_productBoundary]
    · intro γ hγ; simp [hiveCount_one_productBoundary, hγ]
  have hsupp₂ : Function.support
      (fun δ : DominantWeight 2 =>
        (hiveCount (productBoundary std₂ std₂ δ) : ℤ) • diagramSchurPoly 2 ℤ δ.shape) ⊆
      ({sym₂, det₂} : Finset (DominantWeight 2)) := by
    intro δ hδ
    rw [Function.mem_support] at hδ
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hnot
    dsimp only [sym₂, det₂] at hnot
    rw [hiveCount_two_std_std_eq] at hδ
    simp only [hnot, ↓reduceIte, CharP.cast_eq_zero, zero_smul] at hδ
    exact hδ rfl
  have hlhs₂ : diagramSchurPoly 2 ℤ ω.shape * diagramSchurPoly 2 ℤ ω.shape =
      diagramSchurPoly 2 ℤ sym₂.shape + diagramSchurPoly 2 ℤ det₂.shape := by
    rw [shape_eq_of_one_two ω std₂ rfl rfl, schur_mul_eq_finsum_hiveCount std₂ std₂ hstd₂ hstd₂,
      finsum_eq_sum_of_support_subset _ hsupp₂, Finset.sum_pair (by decide : sym₂ ≠ det₂),
      hiveCount_two_std_std_eq, hiveCount_two_std_std_eq]
    simp [sym₂, det₂]
  rw [hlhs₂, hrhs₁] at heq
  have heval := congrArg (MvPolynomial.eval fun _ : Fin 2 => (1 : ℤ)) (add_eq_left.mp heq)
  rw [eval_one_diagramSchurPoly_eq_card_boundedSSYT, map_zero, Int.natCast_eq_zero] at heval
  have : Nonempty (BoundedSSYT 2 det₂.shape) :=
    ⟨⟨_root_.SemistandardYoungTableau.highestWeight det₂.shape, fun i c hc => by
      rw [_root_.SemistandardYoungTableau.highestWeight_apply]
      simp only [hc, ↓reduceIte]
      exact (det₂.shape.mem_iff_lt_colLen.mp hc).trans_le
        ((det₂.shape.colLen_anti 0 c (Nat.zero_le c)).trans det₂.colLen_zero_shape_le)⟩⟩
  exact Nat.card_pos.ne' heval

end TauCeti.Hive
