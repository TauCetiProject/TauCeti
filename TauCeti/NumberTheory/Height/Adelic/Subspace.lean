/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import TauCeti.NumberTheory.Height.Adelic.Basic
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
public import TauCeti.Order.Hom.PowersetCard
import TauCeti.Data.Set.PowersetCard

/-!
# Adelic subspace heights over number fields

For a linear subspace `U ≤ (ι → L)` of dimension `k` over a finite extension `L / K` and an adelic
matrix `A : Matrix ι ι (AdeleRing (𝓞 K) K)`, `TauCeti.adelicSubspaceHeight A U` is the adelic height
of the Plücker coordinates of a basis of `U`, twisted by the `k × k` minor matrix `minorMatrix A k`
(`⋀^k A`).

## Main definitions

* `TauCeti.minorMatrix`: the matrix of `k × k` minors of a square matrix over
  `Set.powersetCard ι k`.
* `TauCeti.adelicSubspaceHeight`: the twisted adelic height of a linear subspace `U ≤ (ι → L)`.

## Main results

* `TauCeti.minorMatrix_one`, `TauCeti.minorMatrix_mul`: functoriality of `k × k` minors under
  matrix multiplication (Cauchy–Binet).
* `TauCeti.adelicSubspaceHeight_eq_adelicHeight_plucker`: independence of choice of basis for
  `A : GL ι (AdeleRing (𝓞 K) K)`.
* `TauCeti.adelicSubspaceHeight_bot`, `TauCeti.adelicSubspaceHeight_span_singleton`: zero- and
  one-dimensional evaluations.
* `TauCeti.adelicSubspaceHeight_one`: for `L = K` and `A = 1`, recovers `Submodule.subspaceHeight`.
* `TauCeti.adelicSubspaceHeight_top`: for `U = ⊤` and `A : GL`, equals
  `(ideleNorm (det A)) ^ ([K : ℚ]⁻¹)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §§2.8–2.9.
* J. Vaaler and E. Bombieri, *On Siegel's lemma*, Invent. Math. 73 (1983), 11–32.
-/

public section

open IsDedekindDomain Module NumberField Set.powersetCard TauCeti.GlobalNumberFields
open scoped NumberField NNReal

namespace TauCeti

/-- The matrix of `k × k` minors of `A : Matrix ι ι R`, indexed by `Set.powersetCard ι k` via
the increasing enumeration `Set.powersetCard.ofFinEmbEquiv.symm`. -/
@[expose]
def minorMatrix {R ι : Type*} [CommRing R] [LinearOrder ι] (A : Matrix ι ι R) (k : ℕ) :
    Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) R :=
  Matrix.of fun I J : Set.powersetCard ι k ↦
    (Matrix.of fun a b ↦ A (ofFinEmbEquiv.symm I a) (ofFinEmbEquiv.symm J b)).det

/-- Entry formula for `TauCeti.minorMatrix`. -/
@[simp]
theorem minorMatrix_apply {R ι : Type*} [CommRing R] [LinearOrder ι] (A : Matrix ι ι R) (k : ℕ)
    (I J : Set.powersetCard ι k) :
    minorMatrix A k I J =
      (Matrix.of fun a b ↦ A (ofFinEmbEquiv.symm I a) (ofFinEmbEquiv.symm J b)).det :=
  rfl

/-- The `k × k` minor matrix of the identity matrix is the identity matrix. -/
@[simp]
theorem minorMatrix_one {R ι : Type*} [CommRing R] [LinearOrder ι] (k : ℕ) :
    minorMatrix (1 : Matrix ι ι R) k = 1 := by
  ext I J
  rw [minorMatrix_apply, Matrix.one_apply]
  by_cases hIJ : I = J
  · subst hIJ
    simp only [↓reduceIte]
    have hmat : (Matrix.of fun a b : Fin k ↦
        (1 : Matrix ι ι R) (ofFinEmbEquiv.symm I a) (ofFinEmbEquiv.symm I b)) = 1 := by
      ext a b
      simp [Matrix.one_apply, (ofFinEmbEquiv.symm I).injective.eq_iff]
    rw [hmat, Matrix.det_one]
  · simp only [hIJ, ↓reduceIte]
    have hnsub : ¬ (I.val ⊆ J.val) := by
      intro hsub
      exact hIJ (Subtype.ext (Finset.eq_of_subset_of_card_le hsub
        (I.property.symm ▸ J.property.symm ▸ le_rfl)))
    obtain ⟨x, hxI, hxJ⟩ := Finset.not_subset.mp hnsub
    obtain ⟨a, ha⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem I x).2 hxI
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b ↦ ?_
    have hb : ofFinEmbEquiv.symm J b ∈ J.val :=
      (mem_range_ofFinEmbEquiv_symm_iff_mem J _).1 ⟨b, rfl⟩
    have hne : ofFinEmbEquiv.symm I a ≠ ofFinEmbEquiv.symm J b := by
      rw [ha]
      exact fun h ↦ hxJ (h ▸ hb)
    simp [Matrix.one_apply, hne]

/-- **Cauchy–Binet formula**: taking `k × k` minors commutes with matrix multiplication. -/
theorem minorMatrix_mul {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]
    (A B : Matrix ι ι R) (k : ℕ) :
    minorMatrix (A * B) k = minorMatrix A k * minorMatrix B k := by
  ext I J
  rw [minorMatrix_apply, Matrix.mul_apply]
  let X : Fin k → ι → R := fun a t ↦ A (ofFinEmbEquiv.symm I a) t
  let Y : Fin k → ι → R := fun b t ↦ B t (ofFinEmbEquiv.symm J b)
  have hmat : (Matrix.of fun a b ↦
      (A * B) (ofFinEmbEquiv.symm I a) (ofFinEmbEquiv.symm J b)) =
      Matrix.of X * (Matrix.of Y).transpose := by
    ext a b
    simp [X, Y, Matrix.mul_apply]
  rw [hmat, det_mul_transpose_eq_sum_plucker_mul X Y]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  have hX : plucker X S = minorMatrix A k I S := by
    rw [plucker_apply, minorMatrix_apply]
  have hY : plucker Y S = minorMatrix B k S J := by
    rw [plucker_apply, minorMatrix_apply, ← Matrix.det_transpose]
    rfl
  rw [hX, hY]

private theorem minorMatrix_left_inv {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]
    (A : GL ι R) (k : ℕ) :
    minorMatrix ((A⁻¹ : GL ι R) : Matrix ι ι R) k * minorMatrix (A : Matrix ι ι R) k = 1 := by
  rw [← minorMatrix_mul, ← minorMatrix_one k]
  congr 1
  simp

/-- The twisted adelic height of a linear subspace `U ≤ (ι → L)`: the adelic height of the
Plücker coordinates of `Module.finBasis L U`, twisted by the `dim U × dim U` minors of `A`. -/
@[expose]
noncomputable def adelicSubspaceHeight {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) : ℝ :=
  adelicHeight
    (Matrix.of fun I J : Set.powersetCard ι (finrank L U) ↦
      (Matrix.of fun a b ↦ A (ofFinEmbEquiv.symm I a) (ofFinEmbEquiv.symm J b)).det)
    (plucker fun i ↦ (Module.finBasis L U i : ι → L))

/-- Defining equation of `TauCeti.adelicSubspaceHeight` in terms of `TauCeti.minorMatrix`. -/
theorem adelicSubspaceHeight_def {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) :
    adelicSubspaceHeight A U =
      adelicHeight (minorMatrix A (finrank L U))
        (plucker fun i ↦ (Module.finBasis L U i : ι → L)) :=
  rfl

/-- Every adelic subspace height is nonnegative. -/
theorem adelicSubspaceHeight_nonneg {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) :
    0 ≤ adelicSubspaceHeight A U :=
  adelicHeight_nonneg _ _

private theorem plucker_coe_basis_ne_zero {L ι : Type*} [Field L] [Finite ι] [LinearOrder ι]
    {U : Submodule L (ι → L)} {p : ℕ} (b : Basis (Fin p) L U) :
    plucker (fun i ↦ (b i : ι → L)) ≠ 0 := by
  refine (plucker_ne_zero_iff _).mpr ?_
  exact b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)

/-- For an invertible adelic matrix `A : GL ι (AdeleRing (𝓞 K) K)`, `TauCeti.adelicSubspaceHeight`
is independent of the choice of basis of `U`. -/
theorem adelicSubspaceHeight_eq_adelicHeight_plucker {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {U : Submodule L (ι → L)}
    (b : Basis (Fin (finrank L U)) L U) :
    adelicSubspaceHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) U =
      adelicHeight (minorMatrix (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (finrank L U))
        (plucker fun i ↦ (b i : ι → L)) := by
  let b₀ := Module.finBasis L U
  let M : Matrix (Fin (finrank L U)) (Fin (finrank L U)) L := (b.toMatrix b₀).transpose
  have hrep : ∀ i, (b₀ i : ι → L) = ∑ j, M i j • (b j : ι → L) := by
    intro i
    calc (b₀ i : ι → L) = U.subtype (∑ j, M i j • b j) := by
          have hsum : b₀ i = ∑ j, M i j • b j := by
            simpa only [M, Matrix.transpose_apply, Basis.toMatrix_apply] using
              (b.sum_repr (b₀ i)).symm
          exact congrArg U.subtype hsum
      _ = ∑ j, M i j • (b j : ι → L) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ ↦ map_smul U.subtype _ _
  have hpl : plucker (fun i ↦ (b₀ i : ι → L)) = M.det • plucker fun i ↦ (b i : ι → L) := by
    ext s
    rw [Pi.smul_apply, smul_eq_mul, show (fun i ↦ (b₀ i : ι → L)) = fun i ↦
      ∑ j, M i j • (b j : ι → L) from funext hrep]
    exact plucker_sum_smul M (fun i ↦ (b i : ι → L)) s
  have hM : M.det ≠ 0 := by
    have hmul : (b.toMatrix b₀ * b₀.toMatrix b).det = (1 : Matrix _ _ L).det :=
      congrArg Matrix.det ((b.toMatrix_mul_toMatrix b₀ b).trans b.toMatrix_self)
    rw [Matrix.det_mul, Matrix.det_one] at hmul
    rw [Matrix.det_transpose]
    exact left_ne_zero_of_mul_eq_one hmul
  have hsupp := hasFiniteMulSupport_adelicHeight_of_left_inv (minorMatrix_left_inv A (finrank L U))
    (plucker_coe_basis_ne_zero b)
  rw [adelicSubspaceHeight_def, hpl]
  exact adelicHeight_smul_of_hasFiniteMulSupport _ _ hM hsupp

private theorem sum_eq_of_forall_eq {β α : Type*} [Fintype β] [AddCommMonoid α]
    (I₀ : β) (hI₀ : ∀ I : β, I = I₀) (g : β → α) : ∑ I, g I = g I₀ :=
  Finset.sum_eq_single I₀ (fun I _ hI ↦ (hI (hI₀ I)).elim) fun h ↦ (h (Finset.mem_univ _)).elim

/-- The adelic subspace height of the zero subspace is `1`. -/
@[simp]
theorem adelicSubspaceHeight_bot {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι (AdeleRing (𝓞 K) K)) :
    adelicSubspaceHeight A (⊥ : Submodule L (ι → L)) = 1 := by
  rw [adelicSubspaceHeight_def, adelicHeight_def]
  have hfin0 : finrank L (⊥ : Submodule L (ι → L)) = 0 := finrank_bot L (ι → L)
  let I₀ : Set.powersetCard ι (finrank L (⊥ : Submodule L (ι → L))) := ⟨∅, by simp [hfin0]⟩
  have : Nonempty (Set.powersetCard ι (finrank L (⊥ : Submodule L (ι → L)))) := ⟨I₀⟩
  have hI₀ : ∀ I : Set.powersetCard ι (finrank L (⊥ : Submodule L (ι → L))), I = I₀ := by
    intro I
    ext x
    simp [I₀, Finset.card_eq_zero.mp (I.property.trans hfin0)]
  have hm : minorMatrix A (finrank L (⊥ : Submodule L (ι → L))) I₀ I₀ = 1 := by
    rw [minorMatrix_apply, Matrix.det_eq_one_of_card_eq_zero (by simp [hfin0])]
  have hp : plucker (fun i ↦ (Module.finBasis L (⊥ : Submodule L (ι → L)) i : ι → L)) I₀ = 1 := by
    rw [plucker_apply, Matrix.det_eq_one_of_card_eq_zero (by simp [hfin0])]
  have hinf : ∀ w : InfinitePlace L,
      (∑ I, ‖∑ J, (adeleExtension (𝓞 K) K (𝓞 L) L
          (minorMatrix A (finrank L (⊥ : Submodule L (ι → L))) I J)).1 w *
            ((plucker fun i ↦ (Module.finBasis L (⊥ : Submodule L (ι → L)) i : ι → L)) J :
              w.Completion)‖ ^ 2) ^ ((w.mult : ℝ) / (2 * finrank ℚ L)) = 1 := by
    intro w
    rw [sum_eq_of_forall_eq I₀ hI₀, sum_eq_of_forall_eq I₀ hI₀, hm, hp, map_one]
    have h1w : (1 : AdeleRing (𝓞 L) L).1 w = 1 := rfl
    rw [h1w, ← InfinitePlace.Completion.algebraMap_apply_eq_coe, map_one, one_mul, norm_one]
    simp
  have hfin : ∀ v : HeightOneSpectrum (𝓞 L),
      (⨆ I, ‖∑ J, (adeleExtension (𝓞 K) K (𝓞 L) L
          (minorMatrix A (finrank L (⊥ : Submodule L (ι → L))) I J)).2 v *
            algebraMap L (v.adicCompletion L)
              ((plucker fun i ↦ (Module.finBasis L (⊥ : Submodule L (ι → L)) i : ι → L)) J)‖) ^
        ((1 : ℝ) / finrank ℚ L) = 1 := by
    intro v
    have hterm : ∀ I, ‖∑ J, (adeleExtension (𝓞 K) K (𝓞 L) L
        (minorMatrix A (finrank L (⊥ : Submodule L (ι → L))) I J)).2 v *
          algebraMap L (v.adicCompletion L)
            ((plucker fun i ↦ (Module.finBasis L (⊥ : Submodule L (ι → L)) i : ι → L)) J)‖ =
        1 := by
      intro I
      rw [hI₀ I, sum_eq_of_forall_eq I₀ hI₀, hm, hp, map_one]
      have h1v : (1 : AdeleRing (𝓞 L) L).2 v = 1 := rfl
      rw [h1v, map_one, one_mul, norm_one]
    simp_rw [hterm, ciSup_const, Real.one_rpow]
  rw [Finset.prod_eq_one fun w _ ↦ hinf w, finprod_eq_one_of_forall_eq_one hfin, mul_one]

private noncomputable def spanSingletonBasis {L ι : Type*} [Field L] {x : ι → L} (hx : x ≠ 0) :
    Basis (Fin (finrank L (Submodule.span L {x}))) L (Submodule.span L {x}) :=
  have hrank : finrank L (Submodule.span L {x}) = 1 := finrank_span_singleton hx
  let x₀ : Submodule.span L {x} := ⟨x, Submodule.subset_span (Set.mem_singleton x)⟩
  let v : Fin (finrank L (Submodule.span L {x})) → Submodule.span L {x} := fun _ ↦ x₀
  have hx₀ : x₀ ≠ 0 := fun h ↦ hx (congrArg Subtype.val h)
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi0 : Subsingleton (Fin (finrank L (Submodule.span L {x}))) := by
      rw [hrank]
      infer_instance
    have hc' : c i • x₀ = 0 := by
      simpa [Fintype.sum_eq_single i fun j hj ↦ (hj (Subsingleton.elim j i)).elim] using hc
    exact (smul_eq_zero.mp hc').resolve_right hx₀
  Basis.mk hli fun ⟨y, hy⟩ _ ↦ by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span.mpr fun S hS ↦ S.smul_mem c
      (hS ⟨⟨0, by omega⟩, rfl⟩)

/-- For an invertible adelic matrix, the adelic subspace height of a line `L ∙ x` equals the
adelic height of `x`. -/
theorem adelicSubspaceHeight_span_singleton {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} (hx : x ≠ 0) :
    adelicSubspaceHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (Submodule.span L {x}) =
      adelicHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) x := by
  let U := Submodule.span L {x}
  have hrank : finrank L U = 1 := finrank_span_singleton hx
  let b := spanSingletonBasis hx
  have hb : ∀ i : Fin (finrank L U), (b i : ι → L) = x := fun i ↦ by
    simp [b, spanSingletonBasis]
  let e : ι ≃ Set.powersetCard ι (finrank L U) :=
    ofSingleton.trans (Equiv.subtypeEquivRight fun s ↦ by rw [hrank])
  have he_val : ∀ (i : ι) (a : Fin (finrank L U)), ofFinEmbEquiv.symm (e i) a = i := by
    intro i a
    have hmem : ofFinEmbEquiv.symm (e i) a ∈ (e i).val :=
      (mem_range_ofFinEmbEquiv_symm_iff_mem (e i) _).1 ⟨a, rfl⟩
    have hsing : (e i).val = {i} := rfl
    rw [hsing, Finset.mem_singleton] at hmem
    exact hmem
  have hM : (minorMatrix (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (finrank L U)).submatrix e e =
      (A : Matrix ι ι (AdeleRing (𝓞 K) K)) := by
    ext i j
    rw [Matrix.submatrix_apply, minorMatrix_apply]
    have hi : Unique (Fin (finrank L U)) := by rw [hrank]; infer_instance
    have hconst : (Matrix.of fun a b ↦
        (A : Matrix ι ι (AdeleRing (𝓞 K) K))
          (ofFinEmbEquiv.symm (e i) a) (ofFinEmbEquiv.symm (e j) b)) =
        Matrix.of fun _ _ ↦ (A : Matrix ι ι (AdeleRing (𝓞 K) K)) i j := by
      ext a b
      simp [he_val]
    rw [hconst, Matrix.det_unique]
    rfl
  have hpl : (plucker fun k ↦ (b k : ι → L)) ∘ e = x := by
    ext i
    rw [Function.comp_apply, plucker_apply]
    have hi : Unique (Fin (finrank L U)) := by rw [hrank]; infer_instance
    have hconst : (Matrix.of fun k a ↦ (b k : ι → L) (ofFinEmbEquiv.symm (e i) a)) =
        Matrix.of fun _ _ ↦ x i := by
      ext k a
      simp [hb, he_val]
    rw [hconst, Matrix.det_unique]
    rfl
  rw [adelicSubspaceHeight_eq_adelicHeight_plucker A b, ← adelicHeight_reindex e e, hM, hpl]

/-- Over `K`, the untwisted adelic subspace height agrees with `Submodule.subspaceHeight`. -/
theorem adelicSubspaceHeight_one {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    [LinearOrder ι] (U : Submodule K (ι → K)) :
    adelicSubspaceHeight (L := K) (1 : Matrix ι ι (AdeleRing (𝓞 K) K)) U = U.subspaceHeight := by
  rw [adelicSubspaceHeight_def, minorMatrix_one, adelicHeight_one,
    Submodule.subspaceHeight_eq_height2_plucker (Module.finBasis K U)]

private def finOneGL {R : Type*} [CommRing R] (u : Rˣ) : GL (Fin 1) R :=
  ⟨Matrix.of fun _ _ ↦ (u : R), Matrix.of fun _ _ ↦ ((u⁻¹ : Rˣ) : R),
    by ext i j; rw [Matrix.mul_apply, Fintype.sum_unique]
       simp [Fin.eq_zero i, Fin.eq_zero j, Matrix.one_apply],
    by ext i j; rw [Matrix.mul_apply, Fintype.sum_unique]
       simp [Fin.eq_zero i, Fin.eq_zero j, Matrix.one_apply]⟩

private theorem det_finOneGL {R : Type*} [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (finOneGL u) = u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rfl

/-- For the full space `⊤ : Submodule L (ι → L)`, the twisted adelic subspace height equals
`(ideleNorm (det A)) ^ ([K : ℚ]⁻¹)`. -/
theorem adelicSubspaceHeight_top {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) :
    adelicSubspaceHeight (A : Matrix ι ι (AdeleRing (𝓞 K) K)) (⊤ : Submodule L (ι → L)) =
      ((GlobalNumberFields.ideleNorm (Matrix.GeneralLinearGroup.det A) : ℝ≥0) : ℝ) ^
        ((finrank ℚ K : ℝ)⁻¹) := by
  have hrank : finrank L (⊤ : Submodule L (ι → L)) = Fintype.card ι := by
    rw [finrank_top, Module.finrank_pi]
  let S₀ : Set.powersetCard ι (finrank L (⊤ : Submodule L (ι → L))) :=
    ⟨Finset.univ, by simp [hrank]⟩
  have hsub : Subsingleton (Set.powersetCard ι (finrank L (⊤ : Submodule L (ι → L)))) :=
    subsingleton_of_card_eq hrank
  let e : Fin (finrank L (⊤ : Submodule L (ι → L))) ≃ ι :=
    Equiv.ofBijective (ofFinEmbEquiv.symm S₀) <|
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(ofFinEmbEquiv.symm S₀).injective, by simp [hrank]⟩
  have hsub_eq : (Matrix.of fun a b ↦ (A : Matrix ι ι (AdeleRing (𝓞 K) K))
      (ofFinEmbEquiv.symm S₀ a) (ofFinEmbEquiv.symm S₀ b)) =
      (A : Matrix ι ι (AdeleRing (𝓞 K) K)).submatrix e e :=
    rfl
  have hminor : minorMatrix (A : Matrix ι ι (AdeleRing (𝓞 K) K))
      (finrank L (⊤ : Submodule L (ι → L))) S₀ S₀ =
      (A : Matrix ι ι (AdeleRing (𝓞 K) K)).det := by
    rw [minorMatrix_apply, hsub_eq, Matrix.det_submatrix_equiv_self]
  let e0 : Fin 1 ≃ Set.powersetCard ι (finrank L (⊤ : Submodule L (ι → L))) :=
    ⟨fun _ ↦ S₀, fun _ ↦ 0, fun i ↦ Subsingleton.elim 0 i, fun s ↦ hsub.elim S₀ s⟩
  let dGL := finOneGL (Matrix.GeneralLinearGroup.det A)
  have hsub_m : (minorMatrix (A : Matrix ι ι (AdeleRing (𝓞 K) K))
      (finrank L (⊤ : Submodule L (ι → L)))).submatrix e0 e0 =
      (dGL : Matrix (Fin 1) (Fin 1) _) := by
    ext i j
    rw [Matrix.submatrix_apply, hsub.elim (e0 i) S₀, hsub.elim (e0 j) S₀, hminor,
      ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hne :
      (plucker fun i ↦ (Module.finBasis L (⊤ : Submodule L (ι → L)) i : ι → L)) ∘ e0 ≠ 0 := by
    intro h
    apply plucker_coe_basis_ne_zero (Module.finBasis L (⊤ : Submodule L (ι → L)))
    ext s
    have hs := congrFun h 0
    simpa [hsub.elim s S₀, show e0 0 = S₀ from rfl] using hs
  rw [adelicSubspaceHeight_def, ← adelicHeight_reindex e0 e0, hsub_m,
    adelicHeight_unique dGL hne, det_finOneGL]

end TauCeti
