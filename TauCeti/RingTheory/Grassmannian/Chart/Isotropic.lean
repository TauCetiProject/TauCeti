/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Algebra.MvPolynomial.Lift
public import TauCeti.LinearAlgebra.Matrix.Symmetric
public import TauCeti.LinearAlgebra.SymplecticGroup
public import TauCeti.RingTheory.Grassmannian.Chart.Basic
public import TauCeti.RingTheory.Grassmannian.Isotropic

/-!
# The standard chart of the isotropic Grassmannian

Let `M` be a module over a commutative ring `R` with a basis `b` indexed by `ι ⊕ Fin k`. A point of
the Grassmannian chart at the last `k` basis vectors (`Module.Grassmannian.chart`) over an
`R`-algebra `A` is the graph of a matrix: it is spanned by the vectors
`1 ⊗ b (inl l) - ∑ⱼ Φ l j • (1 ⊗ b (inr j))` for a unique `Φ : Matrix ι (Fin k) A`
(`Module.Grassmannian.chartBasisEquiv`, `Module.Grassmannian.toSubmodule_chartBasisEquiv_symm`, in
`TauCeti.RingTheory.Grassmannian.Chart.Basic`). So for a bilinear form `ω` on `M`, the point is
isotropic for the base change `ω_A` exactly when `ω_A` vanishes on pairs of these vectors, which is
an explicit polynomial condition on `Φ` in terms of the Gram matrix of `ω`.

Now let `b` be a symplectic basis, indexed by `(Fin r ⊕ κ) ⊕ (Fin r ⊕ κ)` with Gram matrix the
standard alternating matrix `J`, of a module of rank `2m`, `m = r + |κ|`. The vectors
`b (inl (inl l))`, `l < r`, span an isotropic subspace `U₀` of rank `r`, and the chart at the other
basis vectors consists of the complements of their span. Split the matrix `Φ` of a chart point into
its block `S` on the dual vectors `b (inr (inl l))` of `U₀` and its block `c` on the remaining
vectors `b (inl (inr q))` and `b (inr (inr q))`. The point is isotropic exactly when
`S - Sᵀ = c J cᵀ`. The right-hand side is alternating, so this equation determines the entries of
`S` below the diagonal from those on and above it, without dividing by `2`
(`Matrix.subTransposeEqEquiv`). Hence the isotropic points of the chart are parametrized by an
arbitrary `c` and an arbitrary function on the unordered pairs `Sym2 (Fin r)`, naturally in `A`:
the chart of the Grassmannian of rank-`r` isotropic subspaces is the affine space over `R` of
dimension `2 r |κ| + r (r + 1) / 2 = r (2m - r) - r (r - 1) / 2`. This holds over every commutative
ring, including in characteristic two, and for `r = 0`, where the chart is a point.

## Main definitions

* `Module.Grassmannian.isotropicChartFunctor`: the isotropic points of a chart, as a subfunctor of
  the Grassmannian functor.
* `Module.Grassmannian.symplecticChartBasis`: a symplectic basis reordered for the standard chart.
* `Module.Grassmannian.isotropicChartEquiv`: the isotropic points of the standard chart over `A`
  are the pairs of a matrix `Matrix (Fin r) (κ ⊕ κ) A` and a function `Sym2 (Fin r) → A`.
* `Module.Grassmannian.isotropicChartCorepresentableBy`: the isotropic standard chart is
  corepresented by the polynomial ring over `R` on `Fin r × (κ ⊕ κ) ⊕ Sym2 (Fin r)`.

## Main results

* `Module.Grassmannian.isotropicLocus_chartBasisEquiv_symm_eq_bot_iff` and
  `Module.Grassmannian.baseChange_chartGraphVector`: isotropy of a chart point in terms of its
  matrix.
* `Module.Grassmannian.isotropicLocus_chartBasisEquiv_symm_eq_bot_iff_symplecticChartSym`:
  **a point of the standard chart is isotropic exactly when `S - Sᵀ = c J cᵀ`**.
* `Module.Grassmannian.map_isotropicChartEquiv_symm`: the affine coordinates are natural in `A`.
* `Module.Grassmannian.card_isotropicChart_coordinates`: **the number of coordinates is
  `r (2m - r) - r (r - 1) / 2`**.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w u'

open CategoryTheory TensorProduct

open scoped Matrix

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {ι : Type*}

section Basis

variable (b : Basis (ι ⊕ Fin k) R M) {A : Type w} [CommRing A] [Algebra R A]
  (ω : LinearMap.BilinForm R M)

/-- **Isotropy in the chart.** The point of the chart with matrix `Φ` is isotropic for the base
change of `ω` exactly when `ω_A` vanishes on every pair of its graph vectors. -/
theorem isotropicLocus_chartBasisEquiv_symm_eq_bot_iff (Φ : Matrix ι (Fin k) A) :
    ((chartBasisEquiv b A).symm Φ).1.isotropicLocus ω = ⊥ ↔
      ∀ l l', ω.baseChange A (chartGraphVector b Φ l) (chartGraphVector b Φ l') = 0 := by
  rw [isotropicLocus_def, toSubmodule_chartBasisEquiv_symm, Submodule.map₂_span_span,
    Submodule.span_eq_bot]
  simp only [Set.forall_mem_image2, Set.forall_mem_range]

/-- The values of the base change of `ω` on the graph vectors, in terms of the matrix `Φ` and the
Gram matrix of `ω` in the basis `b`. -/
theorem baseChange_chartGraphVector (Φ : Matrix ι (Fin k) A) (l l' : ι) :
    ω.baseChange A (chartGraphVector b Φ l) (chartGraphVector b Φ l') =
      algebraMap R A (ω (b (.inl l)) (b (.inl l'))) -
        ∑ j, Φ l' j * algebraMap R A (ω (b (.inl l)) (b (.inr j))) -
        ∑ j, Φ l j * algebraMap R A (ω (b (.inr j)) (b (.inl l'))) +
        ∑ j, ∑ j', Φ l j * Φ l' j' * algebraMap R A (ω (b (.inr j)) (b (.inr j'))) := by
  simp only [chartGraphVector, map_sub, map_sum, map_smul, LinearMap.sub_apply,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def, LinearMap.coe_sum,
    LinearMap.coe_smul, Finset.sum_apply, Pi.mul_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [mul_comm (Φ l' _) (Φ l _)]
  ring

end Basis

section Functor

variable (R) in
/-- The isotropic points of the chart at `x : Fin k → M` for a bilinear form `ω`, as a subfunctor
of the Grassmannian functor `A ↦ G(k, A ⊗[R] M; A)`. -/
def isotropicChartFunctor (ω : LinearMap.BilinForm R M) (x : Fin k → M) :
    Subfunctor (functor.{u, v, w} (R := R) (M := M) k) where
  obj A := {N | N ∈ chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∧ N.isotropicLocus ω = ⊥}
  map f N hN := ⟨(mem_chartFunctor_obj_iff x _ _).1
      ((chartFunctor R x).map f ((mem_chartFunctor_obj_iff x _ N).2 hN.1)),
    isotropicLocus_map_eq_bot hN.2 f.hom⟩

/-- Over `A`, the isotropic chart subfunctor consists of the isotropic points of the chart. -/
@[simp]
theorem mem_isotropicChartFunctor_obj_iff (ω : LinearMap.BilinForm R M) (x : Fin k → M)
    (A : CommAlgCat.{w} R) (N : G(k, A ⊗[R] M; A)) :
    N ∈ (isotropicChartFunctor R ω x).obj A ↔
      N ∈ chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∧ N.isotropicLocus ω = ⊥ :=
  (Iff.rfl)

end Functor

section Symplectic

variable {r : ℕ} {κ : Type u'}
  (b : Basis ((Fin r ⊕ κ) ⊕ (Fin r ⊕ κ)) R M) (e : Fin k ≃ κ ⊕ (Fin r ⊕ κ))

/-- A basis indexed by `(Fin r ⊕ κ) ⊕ (Fin r ⊕ κ)` reordered for the standard chart at the
isotropic span of the first `r` vectors: first the vectors `b (inl (inl l))`, then, in the order
given by `e`, the vectors `b (inl (inr q))` and `b (inr i)`. -/
noncomputable def symplecticChartBasis : Basis (Fin r ⊕ Fin k) R M :=
  b.reindex ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) e.symm))

/-- The first `r` vectors of `symplecticChartBasis b e` span the base point of the chart. -/
@[simp]
theorem symplecticChartBasis_inl (l : Fin r) :
    symplecticChartBasis b e (.inl l) = b (.inl (.inl l)) := by
  simp [symplecticChartBasis]

/-- The chart vectors of `symplecticChartBasis b e` at `e.symm (inl q)` are isotropic. -/
@[simp]
theorem symplecticChartBasis_inr_symm_inl (q : κ) :
    symplecticChartBasis b e (.inr (e.symm (.inl q))) = b (.inl (.inr q)) := by
  simp [symplecticChartBasis]

/-- The chart vectors of `symplecticChartBasis b e` at `e.symm (inr i)` are the dual vectors. -/
@[simp]
theorem symplecticChartBasis_inr_symm_inr (i : Fin r ⊕ κ) :
    symplecticChartBasis b e (.inr (e.symm (.inr i))) = b (.inr i) := by
  simp [symplecticChartBasis]

variable {A : Type w}

/-- The coefficients of the graph vectors of a chart point on the vectors `b (inr (inl l'))` dual
to the base point. -/
def symplecticChartSym (Φ : Matrix (Fin r) (Fin k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun l l' ↦ Φ l (e.symm (.inr (.inl l')))

/-- The coefficients of the graph vectors of a chart point on the remaining vectors
`b (inl (inr q))` and `b (inr (inr q))`. -/
def symplecticChartFree (Φ : Matrix (Fin r) (Fin k) A) : Matrix (Fin r) (κ ⊕ κ) A :=
  Matrix.of fun l t ↦ Φ l (e.symm (Sum.elim .inl (fun q ↦ .inr (.inr q)) t))

/-- The blocks of a chart matrix are compatible with applying a function to its entries. -/
@[simp]
theorem symplecticChartSym_map {B : Type*} (f : A → B)
    (Φ : Matrix (Fin r) (Fin k) A) :
    symplecticChartSym e (Φ.map f) = (symplecticChartSym e Φ).map f :=
  (rfl)

/-- The blocks of a chart matrix are compatible with applying a function to its entries. -/
@[simp]
theorem symplecticChartFree_map {B : Type*} (f : A → B)
    (Φ : Matrix (Fin r) (Fin k) A) :
    symplecticChartFree e (Φ.map f) = (symplecticChartFree e Φ).map f :=
  (rfl)

variable {e} in
/-- A chart matrix is determined by its two coordinate blocks. -/
theorem symplecticChart_ext {Φ Ψ : Matrix (Fin r) (Fin k) A}
    (h₁ : symplecticChartFree e Φ = symplecticChartFree e Ψ)
    (h₂ : symplecticChartSym e Φ = symplecticChartSym e Ψ) : Φ = Ψ := by
  ext l j
  obtain ⟨t, rfl⟩ := e.symm.surjective j
  rcases t with q | l' | q
  · simpa [symplecticChartFree] using congrFun (congrFun h₁ l) (.inl q)
  · simpa [symplecticChartSym] using congrFun (congrFun h₂ l) l'
  · simpa [symplecticChartFree] using congrFun (congrFun h₁ l) (.inr q)

/-- The splitting of a chart matrix into its two coordinate blocks. -/
private def symplecticChartSplit :
    Matrix (Fin r) (Fin k) A ≃ Matrix (Fin r) (κ ⊕ κ) A × Matrix (Fin r) (Fin r) A where
  toFun Φ := (symplecticChartFree e Φ, symplecticChartSym e Φ)
  invFun p := Matrix.of fun l j ↦
    Sum.elim (fun q ↦ p.1 l (.inl q)) (Sum.elim (fun l' ↦ p.2 l l') fun q ↦ p.1 l (.inr q)) (e j)
  left_inv Φ := symplecticChart_ext (e := e) (by ext l (q | q) <;> simp [symplecticChartFree])
    (by ext l l'; simp [symplecticChartSym])
  right_inv p := by
    ext l t
    · rcases t with q | q <;> simp [symplecticChartFree]
    · simp [symplecticChartSym]

variable [CommRing A] [Algebra R A] [Fintype κ] [DecidableEq κ]

variable {ω : LinearMap.BilinForm R M}
  (hb : LinearMap.BilinForm.toMatrix b ω = Matrix.J (Fin r ⊕ κ) R)
include hb

/-- The values of the base change of `ω` on the graph vectors of a point of the standard chart: with
`S` and `c` the two blocks of its matrix, `ω_A(vₗ, vₗ') = S l' l - S l l' + (c J cᵀ) l l'`. -/
theorem baseChange_chartGraphVector_symplecticChartBasis (Φ : Matrix (Fin r) (Fin k) A)
    (l l' : Fin r) :
    ω.baseChange A (chartGraphVector (symplecticChartBasis b e) Φ l)
        (chartGraphVector (symplecticChartBasis b e) Φ l') =
      symplecticChartSym e Φ l' l - symplecticChartSym e Φ l l' +
        (symplecticChartFree e Φ * Matrix.J κ A * (symplecticChartFree e Φ)ᵀ) l l' := by
  have hω (i j) : ω (b i) (b j) = Matrix.J (Fin r ⊕ κ) R i j := by
    rw [← LinearMap.BilinForm.toMatrix_apply, hb]
  have hsum (F : Fin k → A) : ∑ j, F j = ∑ t, F (e.symm t) := (e.symm.sum_comp F).symm
  rw [baseChange_chartGraphVector]
  simp only [hsum, Fintype.sum_sum_type, symplecticChartBasis_inl,
    symplecticChartBasis_inr_symm_inl, symplecticChartBasis_inr_symm_inr, hω]
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, symplecticChartSym,
    symplecticChartFree, Matrix.one_apply]
  ring

/-- **Isotropy in the standard chart.** A point of the standard chart is isotropic exactly when the
block `S` of its matrix on the dual vectors of the base point satisfies `S - Sᵀ = c J cᵀ`, where `c`
is the block on the remaining vectors and `J` the standard alternating matrix. -/
theorem isotropicLocus_chartBasisEquiv_symm_eq_bot_iff_symplecticChartSym
    (Φ : Matrix (Fin r) (Fin k) A) :
    ((chartBasisEquiv (symplecticChartBasis b e) A).symm Φ).1.isotropicLocus ω = ⊥ ↔
      symplecticChartSym e Φ - (symplecticChartSym e Φ)ᵀ =
        symplecticChartFree e Φ * Matrix.J κ A * (symplecticChartFree e Φ)ᵀ := by
  rw [isotropicLocus_chartBasisEquiv_symm_eq_bot_iff]
  simp only [baseChange_chartGraphVector_symplecticChartBasis b e hb]
  refine ⟨fun h ↦ Matrix.ext fun l l' ↦ ?_, fun h l l' ↦ ?_⟩
  · have := h l l'
    simp only [Matrix.sub_apply, Matrix.transpose_apply]
    linear_combination -this
  · have := congrFun (congrFun h l) l'
    simp only [Matrix.sub_apply, Matrix.transpose_apply] at this
    linear_combination -this

variable (A) in
/-- **The standard chart of the isotropic Grassmannian is an affine space.** The isotropic points
of the chart at the vectors `b (inl (inr q))` and `b (inr i)` of a symplectic basis `b` correspond
to pairs `(c, g)` of an arbitrary `r × 2|κ|` matrix `c` and an arbitrary function `g` on the
unordered pairs of `Fin r`. The block `c` of the chart matrix is `c` itself, and its block `S` on
the dual vectors of the base point is the unique solution of `S - Sᵀ = c J cᵀ` with entries `g` on
and above the diagonal. -/
noncomputable def isotropicChartEquiv :
    {N : chart A (fun j ↦ (1 : A) ⊗ₜ[R] symplecticChartBasis b e (.inr j)) //
        N.1.isotropicLocus ω = ⊥} ≃
      Matrix (Fin r) (κ ⊕ κ) A × (Sym2 (Fin r) → A) :=
  ((chartBasisEquiv (symplecticChartBasis b e) A).subtypeEquiv (q := fun Φ ↦
      symplecticChartSym e Φ - (symplecticChartSym e Φ)ᵀ =
        symplecticChartFree e Φ * Matrix.J κ A * (symplecticChartFree e Φ)ᵀ) fun N ↦ by
      rw [← isotropicLocus_chartBasisEquiv_symm_eq_bot_iff_symplecticChartSym b e hb,
        Equiv.symm_apply_apply]).trans <|
    ((symplecticChartSplit e).subtypeEquiv (q := fun p ↦ p.2 - p.2ᵀ = p.1 * Matrix.J κ A * p.1ᵀ)
      fun _ ↦ Iff.rfl).trans <|
    (Equiv.subtypeProdEquivSigmaSubtype fun c S ↦ S - Sᵀ = c * Matrix.J κ A * cᵀ).trans <|
    (Equiv.sigmaCongrRight fun c ↦ Matrix.subTransposeEqEquiv
      (Matrix.transpose_mul_J_mul_transpose c) (Matrix.mul_J_mul_transpose_apply_self c)).trans
    (Equiv.sigmaEquivProd _ _)

/-- The first coordinate of an isotropic point of the standard chart is the block `c` of its matrix
on the vectors `b (inl (inr q))` and `b (inr (inr q))`. -/
@[simp]
theorem isotropicChartEquiv_apply_fst
    (N : {N : chart A (fun j ↦ (1 : A) ⊗ₜ[R] symplecticChartBasis b e (.inr j)) //
      N.1.isotropicLocus ω = ⊥}) :
    (isotropicChartEquiv b e A hb N).1 =
      symplecticChartFree e (chartBasisEquiv (symplecticChartBasis b e) A N.1) :=
  (rfl)

private theorem isotropicChartEquiv_apply_snd
    (N : {N : chart A (fun j ↦ (1 : A) ⊗ₜ[R] symplecticChartBasis b e (.inr j)) //
      N.1.isotropicLocus ω = ⊥}) :
    (isotropicChartEquiv b e A hb N).2 =
      Matrix.subTransposeEqEquiv (Matrix.transpose_mul_J_mul_transpose _)
        (Matrix.mul_J_mul_transpose_apply_self _)
        ⟨symplecticChartSym e (chartBasisEquiv (symplecticChartBasis b e) A N.1),
          (isotropicLocus_chartBasisEquiv_symm_eq_bot_iff_symplecticChartSym b e hb _).1 <| by
            rw [Equiv.symm_apply_apply]; exact N.2⟩ :=
  (rfl)

/-- The second coordinate of an isotropic point of the standard chart records the entries on and
above the diagonal of the block `S` of its matrix on the dual vectors of the base point. -/
theorem isotropicChartEquiv_apply_snd_mk_of_le
    (N : {N : chart A (fun j ↦ (1 : A) ⊗ₜ[R] symplecticChartBasis b e (.inr j)) //
      N.1.isotropicLocus ω = ⊥}) {l l' : Fin r} (h : l ≤ l') :
    (isotropicChartEquiv b e A hb N).2 s(l, l') =
      symplecticChartSym e (chartBasisEquiv (symplecticChartBasis b e) A N.1) l l' :=
  Matrix.subTransposeEqEquiv_apply_mk_of_le _ _ _ h

/-- The block `c` of the isotropic chart point with coordinates `(c, g)` is `c`. -/
@[simp]
theorem symplecticChartFree_isotropicChartEquiv_symm_apply
    (p : Matrix (Fin r) (κ ⊕ κ) A × (Sym2 (Fin r) → A)) :
    symplecticChartFree e
        (chartBasisEquiv (symplecticChartBasis b e) A ((isotropicChartEquiv b e A hb).symm p).1) =
      p.1 := by
  rw [← isotropicChartEquiv_apply_fst b e hb, Equiv.apply_symm_apply]

/-- The block `S` of the isotropic chart point with coordinates `(c, g)` has entries `g s(l, l')`
on and above the diagonal, and `g s(l, l') + (c J cᵀ) l l'` below it. -/
theorem symplecticChartSym_isotropicChartEquiv_symm_apply
    (p : Matrix (Fin r) (κ ⊕ κ) A × (Sym2 (Fin r) → A)) (l l' : Fin r) :
    symplecticChartSym e
        (chartBasisEquiv (symplecticChartBasis b e) A ((isotropicChartEquiv b e A hb).symm p).1)
        l l' =
      p.2 s(l, l') + if l' < l then (p.1 * Matrix.J κ A * p.1ᵀ) l l' else 0 := by
  set N := (isotropicChartEquiv b e A hb).symm p
  have key : symplecticChartSym e (chartBasisEquiv (symplecticChartBasis b e) A N.1) =
      ((Matrix.subTransposeEqEquiv
        (Matrix.transpose_mul_J_mul_transpose
          (symplecticChartFree e (chartBasisEquiv (symplecticChartBasis b e) A N.1)))
        (Matrix.mul_J_mul_transpose_apply_self
          (symplecticChartFree e (chartBasisEquiv (symplecticChartBasis b e) A N.1)))).symm
          (isotropicChartEquiv b e A hb N).2).1 := by
    rw [isotropicChartEquiv_apply_snd, Equiv.symm_apply_apply]
  rw [key, Matrix.coe_subTransposeEqEquiv_symm_apply, Equiv.apply_symm_apply,
    symplecticChartFree_isotropicChartEquiv_symm_apply]

variable {B : Type w} [CommRing B] [Algebra R B]

/-- **The affine coordinates of the isotropic chart are natural**: base change along
`f : A → B` applies `f` to both coordinates. -/
theorem map_isotropicChartEquiv_symm (f : A →ₐ[R] B)
    (p : Matrix (Fin r) (κ ⊕ κ) A × (Sym2 (Fin r) → A)) :
    map f ((isotropicChartEquiv b e A hb).symm p).1.1 =
      ((isotropicChartEquiv b e B hb).symm (p.1.map f, f ∘ p.2)).1.1 := by
  rw [← Equiv.symm_apply_apply (chartBasisEquiv _ A) ((isotropicChartEquiv b e A hb).symm p).1,
    map_chartBasisEquiv_symm, ← Equiv.symm_apply_apply (chartBasisEquiv _ B)
      ((isotropicChartEquiv b e B hb).symm (p.1.map f, f ∘ p.2)).1]
  congr 2
  refine symplecticChart_ext (e := e) ?_ (Matrix.ext fun l l' ↦ ?_)
  · rw [symplecticChartFree_map, symplecticChartFree_isotropicChartEquiv_symm_apply,
      symplecticChartFree_isotropicChartEquiv_symm_apply]
  · rw [symplecticChartSym_map, Matrix.map_apply,
      symplecticChartSym_isotropicChartEquiv_symm_apply,
      symplecticChartSym_isotropicChartEquiv_symm_apply]
    have hQ : (p.1 * Matrix.J κ A * p.1ᵀ).map f = p.1.map f * Matrix.J κ B * (p.1.map f)ᵀ := by
      simp [Matrix.transpose_map]
    simp [apply_ite f, ← hQ]

variable (A) in
/-- The isotropic points of the standard chart over `A` are the `R`-algebra maps to `A` from the
polynomial ring on `Fin r × (κ ⊕ κ) ⊕ Sym2 (Fin r)`. -/
private noncomputable def isotropicChartHomEquiv :
    (MvPolynomial (Fin r × (κ ⊕ κ) ⊕ Sym2 (Fin r)) R →ₐ[R] A) ≃
      {N : chart A (fun j ↦ (1 : A) ⊗ₜ[R] symplecticChartBasis b e (.inr j)) //
        N.1.isotropicLocus ω = ⊥} :=
  (MvPolynomial.aevalEquiv _ R A).symm.trans <| (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
    (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _)).trans (isotropicChartEquiv b e A hb).symm

private theorem isotropicChartHomEquiv_comp (f : A →ₐ[R] B)
    (g : MvPolynomial (Fin r × (κ ⊕ κ) ⊕ Sym2 (Fin r)) R →ₐ[R] A) :
    (isotropicChartHomEquiv b e B hb (f.comp g)).1.1 =
      map f (isotropicChartHomEquiv b e A hb g).1.1 := by
  set p : Matrix (Fin r) (κ ⊕ κ) A × (Sym2 (Fin r) → A) :=
    Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _)
      (Equiv.sumArrowEquivProdArrow _ _ _ ((MvPolynomial.aevalEquiv _ R A).symm g))
  -- the coordinates of `f.comp g` are those of `g` followed by `f`
  have hp : Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _)
      (Equiv.sumArrowEquivProdArrow _ _ _ ((MvPolynomial.aevalEquiv _ R B).symm (f.comp g))) =
        (p.1.map f, f ∘ p.2) := by
    refine Prod.ext (Matrix.ext fun l t ↦ ?_) (funext fun z ↦ ?_) <;> simp [p, Matrix.map]
  have hA : isotropicChartHomEquiv b e A hb g = (isotropicChartEquiv b e A hb).symm p := (rfl)
  have hB : isotropicChartHomEquiv b e B hb (f.comp g) =
      (isotropicChartEquiv b e B hb).symm (p.1.map f, f ∘ p.2) := by
    rw [← hp]
    rfl
  rw [hA, hB, map_isotropicChartEquiv_symm]

/-- **The standard chart of the isotropic Grassmannian is the affine space** over `R` with
coordinates indexed by `Fin r × (κ ⊕ κ) ⊕ Sym2 (Fin r)`: its subfunctor of the Grassmannian functor
is corepresented by the polynomial ring in these variables. By
`card_isotropicChart_coordinates` there are `r (2m - r) - r (r - 1) / 2` of them, `m = r + |κ|`. -/
noncomputable def isotropicChartCorepresentableBy :
    (isotropicChartFunctor.{u, v, max u u'} R ω
        (fun j ↦ symplecticChartBasis b e (.inr j))).toFunctor.CorepresentableBy
      (CommAlgCat.of R (MvPolynomial (Fin r × (κ ⊕ κ) ⊕ Sym2 (Fin r)) R)) where
  homEquiv {A} := ConcreteCategory.homEquiv.trans <| (isotropicChartHomEquiv b e A hb).trans
    { toFun N := ⟨N.1.1, (mem_isotropicChartFunctor_obj_iff _ _ _ _).2 ⟨N.1.2, N.2⟩⟩
      invFun N := ⟨⟨N.1, ((mem_isotropicChartFunctor_obj_iff _ _ _ _).1 N.2).1⟩,
        ((mem_isotropicChartFunctor_obj_iff _ _ _ _).1 N.2).2⟩ }
  -- `(isotropicChartFunctor _ ω _).toFunctor.map f` acts on underlying points as `map f.hom`
  homEquiv_comp f g := Subtype.ext <| by exact isotropicChartHomEquiv_comp b e hb f.hom g.hom

end Symplectic

/-- **The number of coordinates of the isotropic standard chart.** The coordinates of the standard
chart of the Grassmannian of `r`-dimensional isotropic subspaces of a `2m`-dimensional symplectic
space, with `m = r + |κ|`, number `r (2m - r) - r (r - 1) / 2`. -/
theorem card_isotropicChart_coordinates (r : ℕ) (κ : Type*) [Fintype κ] :
    Fintype.card (Fin r × (κ ⊕ κ)) + Fintype.card (Sym2 (Fin r)) =
      r * (2 * (r + Fintype.card κ) - r) - r * (r - 1) / 2 := by
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Sym2.card]
  have hsucc (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by simp [Nat.choose_succ_succ]
  have h₂ : r.choose 2 + r.choose 2 + r = r * r := by
    induction r with
    | zero => simp
    | succ n ih =>
      rw [hsucc]
      linarith
  have h₃ : r * (2 * (r + Fintype.card κ) - r) = r * r + 2 * (r * Fintype.card κ) := by
    rw [show 2 * (r + Fintype.card κ) - r = r + 2 * Fintype.card κ by omega]
    ring
  rw [hsucc, ← Nat.choose_two_right, h₃, show r * (Fintype.card κ + Fintype.card κ) =
    2 * (r * Fintype.card κ) by ring]
  omega

end Module.Grassmannian
