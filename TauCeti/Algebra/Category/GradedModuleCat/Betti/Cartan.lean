/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Ext
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.PowerSeries
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Matrix

/-!
# The Cartan–Betti alternating Euler identity `C(q) · B(q, -1) = I`

Let `A` be a graded `k`-algebra with graded Cartan map `c : K₀^gr(proj A) → G₀^gr(mod A)`.
Unlike the Cartan–Ext pairing identity `C(q)ᵀ · E(q, -1) = diag(dᵢ)`, which acquires the
division-ring correction `dᵢ = dim_k(eᵢ • (Sᵢ)₀)` over a field that does not split the simple
`A`-modules, a projective resolution of `M` decomposes `[M]` *directly* in `G₀^gr(mod A)` without
passing through `Hom(-, Sᵢ)`. As a consequence, the graded Cartan matrix `C(q)` and the Betti
Poincaré matrix `B(q, t)` satisfy the **uncorrected** matrix inverse equation

`C(q) · B(q, -1) = I`

in both finite-global-dimension and infinite-global-dimension regimes:

1. **Finite projective resolutions (Laurent identity over any commutative base ring):**
   For any graded projective resolution `r` of a finite graded module `M` with finitely generated
   `A`-module terms, exactness telescopes the partial alternating sum
   `∑_{n < b} (-1)ⁿ c([Pₙ]) = [M] - (-1)^b [K_b]` in `G₀^gr(mod A)`, with no decomposition,
   field, or Noetherian assumption. When `r.X b` is a subsingleton for each basis representative
   `Mⱼ`, expanding `[Pₙ]` in any projective basis `bP` gives `C(q) · B(q, -1) = 1` in
   `Matrix I I (LaurentPolynomial ℤ)`.
2. **Unbounded minimal projective resolutions (formal power-series identity):**
   Over a finite-dimensional nonnegatively graded algebra over an arbitrary field `k`, for an
   exhaustive degree-zero simple family `S` with `gdim(eᵢ • Sᵢ) ≠ 0` and minimal resolutions
   `rⱼ` with finitely generated terms, combining `C_psᵀ * E_ps = diag(dᵢ)` with
   `diag(dᵢ) * B(q, -1) = E_psᵀ` cancels `dᵢ ≠ 0` in the integral domain `PowerSeries ℤ` to
   yield `C_ps * B(q, -1) = 1` and `B(q, -1) = C_ps⁻¹` in `Matrix I I (PowerSeries ℤ)` — with
   **no** splitting hypothesis.
3. **Linear / Koszul specialization (`C(q) · P(-q) = I`):**
   Minimal resolutions `rⱼ` of the `Sⱼ` are all linear if and only if the Maslov-graded Euler
   matrix `(bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries` inverts `C_ps`,
   specializing in the linear case to the Koszul Hilbert-series equation `C(q) · P(-q) = I`.

## Main results

* `TauCeti.GradedProjectiveResolution.sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_of` and
  `TauCeti.gradedCartanMatrix_mul_bettiAlternatingSum_eq_one`: the finite-resolution alternating
  Euler identity `C(q) · B(q, -1) = 1` in `Matrix I I (LaurentPolynomial ℤ)`.
* `TauCeti.gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one`,
  `TauCeti.eulerPowerSeries_bettiPoincareMatrix_mul_gradedCartanMatrix_trunc_eq_one`, and
  `TauCeti.eulerPowerSeries_bettiPoincareMatrix_eq_inv_gradedCartanMatrix_trunc`: the unbounded
  formal power-series identity `C_ps * B(q, -1) = 1` and `B(q, -1) = C_ps⁻¹` over any field.
* `TauCeti.forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_eq_one`
  and `TauCeti.gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one`: the Koszul
  characterization and diagonal `P(-q)` specialization.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Theorem 7.6.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *Journal of Combinatorial Theory,
  Series A* **185** (2022), Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI

/-! ### Finite resolutions: exactness telescoping in `LaurentK0` -/

section FiniteResolution

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

namespace GradedProjectiveResolution

variable (M : (gradedFiniteModules 𝒜).FullSubcategory)
  (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.obj.grading)
  [∀ n, Module.Finite A (r.X n)]

private theorem gradedFiniteModules_kernelObj_of_exact {X Y Z : GradedModuleCat.{uA} 𝒜}
    [Module.Finite A X] (d : X ⟶ Y) (f : Y ⟶ Z) (hd : Function.Exact d.hom f.hom) :
    gradedFiniteModules 𝒜 (GradedModuleCat.kernelObj f) := by
  rw [gradedFiniteModules_iff]
  change Module.Finite A ↥(LinearMap.ker f.hom)
  rw [LinearMap.exact_iff.mp hd]
  exact Module.Finite.range d.hom

private theorem subsingleton_kernelObj_of_exact {X Y Z : GradedModuleCat.{uA} 𝒜}
    [Subsingleton X] (d : X ⟶ Y) (f : Y ⟶ Z) (hd : Function.Exact d.hom f.hom) :
    Subsingleton (GradedModuleCat.kernelObj f) := by
  change Subsingleton ↥(LinearMap.ker f.hom)
  rw [LinearMap.exact_iff.mp hd]
  exact d.hom.surjective_rangeRestrict.subsingleton

/-- The `n`th syzygy of a graded projective resolution with finitely generated terms, as an object
of `(gradedFiniteModules 𝒜).FullSubcategory`: `syzygy 0 = M`, `syzygy 1 = ker π`, and
`syzygy (n + 2) = ker (d n)`. Exactness presents each positive syzygy as the image of `r.d`, so it
is finitely generated over `A` without any Noetherian hypothesis. -/
def syzygy : ℕ → (gradedFiniteModules 𝒜).FullSubcategory
  | 0 => M
  | 1 => ⟨GradedModuleCat.kernelObj r.augmentation,
      gradedFiniteModules_kernelObj_of_exact (r.differential 0) r.augmentation r.exact_d_π⟩
  | n + 2 => ⟨GradedModuleCat.kernelObj (r.differential n),
      gradedFiniteModules_kernelObj_of_exact
        (r.differential (n + 1)) (r.differential n) (r.exact_d_d n)⟩

/-- The `0`th syzygy of `r` is the resolved module `M`. -/
@[simp]
theorem syzygy_zero : r.syzygy M 0 = M := (rfl)

/-- The `1`st syzygy of `r` has underlying graded object `ker r.augmentation`. -/
@[simp]
theorem syzygy_one_obj : (r.syzygy M 1).obj = GradedModuleCat.kernelObj r.augmentation := (rfl)

/-- The `(n + 2)`nd syzygy of `r` has underlying graded object `ker (r.differential n)`. -/
@[simp]
theorem syzygy_add_two_obj (n : ℕ) :
    (r.syzygy M (n + 2)).obj = GradedModuleCat.kernelObj (r.differential n) := (rfl)

private theorem shortExact_kernelι_lift {X Y Z : GradedModuleCat.{uA} 𝒜}
    (d : X ⟶ Y) (f : Y ⟶ Z) (hd : Function.Exact d.hom f.hom) :
    ∃ (g : X ⟶ GradedModuleCat.kernelObj f) (hcomp : GradedModuleCat.kernelι d ≫ g = 0),
      (ShortComplex.mk (GradedModuleCat.kernelι d) g hcomp).ShortExact := by
  let g : X ⟶ GradedModuleCat.kernelObj f :=
    GradedModuleCat.ofHom
      (LinearMap.codRestrict (LinearMap.ker f.hom) d.hom fun x ↦
        LinearMap.mem_ker.mpr (hd.apply_apply_eq_zero x))
      (TauCeti.LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
        rw [InternalGrading.mem_ker_piece]
        exact d.isHomogeneous.map_mem hx)
  have hcomp : GradedModuleCat.kernelι d ≫ g = 0 :=
    GradedModuleCat.hom_ext (LinearMap.ext fun z ↦ Subtype.ext z.2)
  have hg_surj : Function.Surjective g.hom := fun ⟨y, hy⟩ ↦ by
    obtain ⟨x, hx⟩ := (hd y).mp (LinearMap.mem_ker.mp hy)
    exact ⟨x, Subtype.ext hx⟩
  have hexact : Function.Exact (GradedModuleCat.kernelι d).hom g.hom := fun x ↦
    ⟨fun hx ↦ ⟨⟨x, LinearMap.mem_ker.mpr (congrArg Subtype.val hx)⟩, rfl⟩,
     fun ⟨z, hz⟩ ↦ hz ▸ Subtype.ext z.2⟩
  exact ⟨g, hcomp,
    { mono_f := (GradedModuleCat.mono_iff_injective _).mpr (Submodule.injective_subtype _)
      epi_g := (GradedModuleCat.epi_iff_surjective _).mpr hg_surj
      exact := GradedModuleCat.exact_iff.mpr hexact }⟩

private theorem gradedCartanMap_finiteProjectiveTerm_eq_syzygy_add (n : ℕ) :
    gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.syzygy M (n + 1)) +
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.syzygy M n) := by
  have hterm : gradedFiniteModules 𝒜 (r.termObj n) :=
    r.finiteProjectiveTerm_obj n ▸
      gradedFiniteProjectiveModules_le_finiteModules _ (r.finiteProjectiveTerm n).property
  let X₂ : (gradedFiniteModules 𝒜).FullSubcategory := ⟨r.termObj n, hterm⟩
  have hcartan :
      gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) =
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) X₂ := by
    have h0 := gradedCartanMap_of (r.finiteProjectiveTerm n).property
    exact h0.trans (congrArg (LaurentK0.of.{uA} _)
      (ObjectProperty.FullSubcategory.ext (r.finiteProjectiveTerm_obj n)))
  rw [hcartan]
  suffices ∃ (f : (r.syzygy M (n + 1)).obj ⟶ X₂.obj) (g : X₂.obj ⟶ (r.syzygy M n).obj)
      (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact by
    obtain ⟨f, g, hfg, hse⟩ := this
    let S : ShortComplex (gradedFiniteModules 𝒜).FullSubcategory :=
      ShortComplex.mk (ObjectProperty.homMk f) (ObjectProperty.homMk g)
        (ObjectProperty.hom_ext _ hfg)
    have hconf : (gradedFiniteModulesExactStructure 𝒜).toExactStructure.Conflation S :=
      (gradedFiniteModulesExactStructure_conflation_iff S).mpr hse
    exact LaurentK0.of_conflation.{uA} (gradedFiniteModulesExactStructure 𝒜) hconf
  cases n with
  | zero =>
    exact ⟨GradedModuleCat.kernelι r.augmentation, r.augmentation,
      GradedModuleCat.kernelι_comp r.augmentation,
      { mono_f := (GradedModuleCat.mono_iff_injective _).mpr (Submodule.injective_subtype _)
        epi_g := (GradedModuleCat.epi_iff_surjective _).mpr r.surjective_π
        exact := GradedModuleCat.exact_iff.mpr (LinearMap.exact_subtype_ker_map r.π) }⟩
  | succ m =>
    cases m with
    | zero =>
      obtain ⟨g, hcomp, hse⟩ :=
        shortExact_kernelι_lift (r.differential 0) r.augmentation r.exact_d_π
      exact ⟨GradedModuleCat.kernelι (r.differential 0), g, hcomp, hse⟩
    | succ k =>
      obtain ⟨g, hcomp, hse⟩ :=
        shortExact_kernelι_lift (r.differential (k + 1)) (r.differential k) (r.exact_d_d k)
      exact ⟨GradedModuleCat.kernelι (r.differential (k + 1)), g, hcomp, hse⟩

/-- **Partial alternating Euler sum of a graded projective resolution.** In `G₀^gr(mod A)`, the
alternating sum of the first `b` terms of `r` equals `[M]` minus `(-1)^b` times the `b`th syzygy
class. -/
theorem sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_sub (b : ℕ) :
    (∑ n ∈ Finset.range b,
        (-1 : ℤ) ^ n • gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M -
        (-1 : ℤ) ^ b •
          LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (r.syzygy M b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, r.gradedCartanMap_finiteProjectiveTerm_eq_syzygy_add M b,
      smul_add, pow_succ, mul_neg, mul_one, neg_zsmul]
    abel

/-- **Alternating Euler decomposition of a finite graded projective resolution.** If the `b`th term
`r.X b` is a subsingleton, then the alternating sum of `[r.termObj n]` over `n < b` maps under
`gradedCartanMap 𝒜` to `[M]` in `G₀^gr(mod A)`. -/
theorem sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_of
    {b : ℕ} (hb : Subsingleton (r.X b)) :
    (∑ n ∈ Finset.range b,
        (-1 : ℤ) ^ n • gradedCartanMap 𝒜 (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M := by
  have hsub : Subsingleton (r.syzygy M b).obj := by
    cases b with
    | zero => exact r.surjective_π.subsingleton
    | succ m =>
      cases m with
      | zero => exact subsingleton_kernelObj_of_exact (r.differential 0) r.augmentation r.exact_d_π
      | succ k =>
        exact subsingleton_kernelObj_of_exact
          (r.differential (k + 1)) (r.differential k) (r.exact_d_d k)
  have hz : IsZero (r.syzygy M b) :=
    (IsZero.iff_id_eq_zero _).2 <| ObjectProperty.hom_ext _ <|
      GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)
  rw [r.sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_sub M b,
    ← LaurentK0.ofExactK0_exactK0_of.{uA} _ (r.syzygy M b),
    ExactK0.of_eq_zero_of_isZero.{uA} hz, map_zero, smul_zero, sub_zero]

end GradedProjectiveResolution

/-- **Finite-resolution Cartan–Betti alternating Euler identity `C(q) · B(q, -1) = 1`.** Over any
commutative ring `k` and graded `k`-algebra `A`, let `bP` be a basis of `K₀^gr(proj A)` and `bM` a
basis of `G₀^gr(mod A)` realized by objects `M j` (`bM j = [M j]`) admitting graded projective
resolutions `r j` whose `b`th terms vanish (`Subsingleton ((r j).X b)`). Then multiplying
`gradedCartanMatrix 𝒜 bP bM` on the right by the truncated alternating Betti matrix
`∑_{n < b} (-1)ⁿ [tⁿ] B(q, t)` yields `1` in `Matrix I I (LaurentPolynomial ℤ)`. -/
theorem gradedCartanMatrix_mul_bettiAlternatingSum_eq_one
    {I : Type uI} [Fintype I] [DecidableEq I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (M : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    {b : ℕ} (hb : ∀ j, Subsingleton ((r j).X b)) :
    gradedCartanMatrix 𝒜 bP bM *
      Matrix.of (fun i j ↦
        ∑ n ∈ Finset.range b,
          (-1 : LaurentPolynomial ℤ) ^ n * PowerSeries.coeff n (bettiPoincareMatrix bP r i j)) =
      1 := by
  refine Matrix.ext fun m j ↦ ?_
  have htel := congrArg (fun z ↦ bM.repr z m)
    ((r j).sum_negOnePow_gradedCartanMap_finiteProjectiveTerm_eq_of (M j) (hb j))
  rw [← hbM j, bM.repr_self, Finsupp.single_apply] at htel
  simp only [eq_comm (a := j)] at htel
  rw [Matrix.one_apply, ← htel, map_sum, Finsupp.finsetSum_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply, Finset.mul_sum, coeff_bettiPoincareMatrix, gradedCartanMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  conv_rhs => rw [← bP.sum_repr (LaurentK0.of.{uA} _ ((r j).finiteProjectiveTerm n))]
  rw [map_sum, map_zsmul, Finsupp.smul_apply, map_sum, Finsupp.finsetSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, zsmul_eq_mul, smul_eq_mul]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  ring

/-- Left-inverse companion `B(q, -1) · C(q) = 1` in `Matrix I I (LaurentPolynomial ℤ)` for finite
resolutions, deduced from `gradedCartanMatrix_mul_bettiAlternatingSum_eq_one` over the commutative
ring `LaurentPolynomial ℤ`. -/
theorem bettiAlternatingSum_mul_gradedCartanMatrix_eq_one
    {I : Type uI} [Fintype I] [DecidableEq I]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (M : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hbM : ∀ j, bM j = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (M j))
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).obj.grading)
    [∀ j n, Module.Finite A ((r j).X n)]
    {b : ℕ} (hb : ∀ j, Subsingleton ((r j).X b)) :
    Matrix.of (fun i j ↦
        ∑ n ∈ Finset.range b,
          (-1 : LaurentPolynomial ℤ) ^ n * PowerSeries.coeff n (bettiPoincareMatrix bP r i j)) *
      gradedCartanMatrix 𝒜 bP bM =
      1 :=
  mul_eq_one_comm.mp (gradedCartanMatrix_mul_bettiAlternatingSum_eq_one bP bM M hbM r hb)

end FiniteResolution

/-! ### Unbounded minimal resolutions: formal power-series identity `C_ps * B(q, -1) = 1` -/

section PowerSeries

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  (bM : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  (hbM : ∀ i, bM i = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i))

include hS hbP hbM in
/-- **The unbounded Cartan–Betti formal power-series identity `C(q) · B(q, -1) = 1`.** Over a
finite-dimensional nonnegatively graded algebra over an arbitrary field `k`, let `S` be an
exhaustive degree-zero simple family with `gdim(eᵢ • Sᵢ) ≠ 0`, and let `r` be minimal graded
projective resolutions of `S` with finitely generated terms. Then `C_ps * B_euler = 1` in
`Matrix I I (PowerSeries ℤ)`, with **no** division-endomorphism factor and **no** splitting
hypothesis. -/
theorem gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)]
    (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) :=
      fun i j ↦ by
        rw [bettiPoincareMatrix_apply]
        exact (hr j).hasEulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP (hself i)
          (fun p hp ↦ hconc j p hp.ne) (hconc i)) :
    ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) =
      1 := by
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := Module.Finite.trans A ((r i).X n)
  have hbM_eq : bM = gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS :=
    Module.Basis.eq_of_apply_eq fun i ↦
      (hbM i).trans (gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS i).symm
  subst hbM_eq
  let hExt (i j : I) :
      IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
    GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj
  let d : I → PowerSeries ℤ := fun i ↦
    PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ)
  let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
  let Cps := (gradedCartanMatrix 𝒜 bP bS).map fun p ↦ (p.trunc : PowerSeries ℤ)
  let Beul := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries (hB i j)
  let Eeul := Matrix.of fun i j ↦ Bigraded.eulerPowerSeries
    ((hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
      (fun p hp ↦ hconc i p hp.ne) (hconc j) (hExt i j))
  have hCE : Eeulᵀ * Cps = Matrix.diagonal d := by
    have htr := congrArg Matrix.transpose
      (gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
        S he he₀ hI hne hself hS bP hbP r hr hneg hconc hExt)
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose] at htr
  have hDB : Matrix.diagonal d * Beul = Eeulᵀ := by
    refine Matrix.ext fun i j ↦ ?_
    have hB' : Bigraded.HasEulerPowerSeries ((r j).bettiPoincareSeries bP i) :=
      bettiPoincareMatrix_apply bP r i j ▸ hB i j
    dsimp only [Beul, Eeul]
    rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply,
      Bigraded.eulerPowerSeries_congr (hB i j) hB' (bettiPoincareMatrix_apply bP r i j)]
    exact (hr j).C_finrank_mul_eulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP
      (hself i) (fun p hp ↦ hconc j p hp.ne) (hconc i) hB' (hExt j i)
  have hDBC : Matrix.diagonal d * (Beul * Cps) = Matrix.diagonal d * 1 := by
    rw [← Matrix.mul_assoc, hDB, hCE, mul_one]
  have hBC : Beul * Cps = 1 := by
    refine Matrix.ext fun i j ↦ ?_
    have hij := congrFun (congrFun hDBC i) j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul] at hij
    have hd_ne : d i ≠ 0 := by
      intro h0
      have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
        Int.natCast_pos.mpr
          ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) (hconc i) (hself i))
      have hc0 := congrArg PowerSeries.constantCoeff h0
      simp only [d, PowerSeries.constantCoeff_C, map_zero] at hc0
      omega
    exact mul_left_cancel₀ hd_ne hij
  exact mul_eq_one_comm.mp hBC

include hS hbP hbM in
/-- Left-inverse companion `B(q, -1) · C(q) = 1` in `Matrix I I (PowerSeries ℤ)` for unbounded
minimal resolutions. -/
theorem eulerPowerSeries_bettiPoincareMatrix_mul_gradedCartanMatrix_trunc_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)]
    (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) :=
      fun i j ↦ by
        rw [bettiPoincareMatrix_apply]
        exact (hr j).hasEulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP (hself i)
          (fun p hp ↦ hconc j p hp.ne) (hconc i)) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) *
      ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) =
      1 :=
  mul_eq_one_comm.mp
    (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
      S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB)

include hS hbP hbM in
/-- **The alternating Betti formal power-series matrix `B(q, -1)` is the inverse of the graded
Cartan matrix `C(q)`** in `Matrix I I (PowerSeries ℤ)`, over any field (splitting or not) and with
no cohomological global-dimension bound. -/
theorem eulerPowerSeries_bettiPoincareMatrix_eq_inv_gradedCartanMatrix_trunc
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)]
    (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hB : ∀ i j, Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) :=
      fun i j ↦ by
        rw [bettiPoincareMatrix_apply]
        exact (hr j).hasEulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP (hself i)
          (fun p hp ↦ hconc j p hp.ne) (hconc i)) :
    Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) =
      (((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
      S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB)).symm

include he₀ hne hself hS hbP hbM in
/-- **Koszul linearity equivalence via the Cartan–Betti identity.** Minimal resolutions `rⱼ` of
an exhaustive degree-zero simple family `S` with finitely generated terms are all linear if and
only if the Maslov-graded Euler matrix
`(bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries` inverts `C_ps`
(`C_ps * B_maslov = 1`). No splitting hypothesis or cohomological global-dimension bound is
needed. -/
theorem forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)]
    (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    (∀ j, (r j).IsLinear) ↔
      ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) *
        (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries =
        1 := by
  let hB (i j : I) : Bigraded.HasEulerPowerSeries (bettiPoincareMatrix bP r i j) := by
    rw [bettiPoincareMatrix_apply]
    exact (hr j).hasEulerPowerSeries_bettiPoincareSeries S he he₀ hI hne bP hbP (hself i)
      (fun p hp ↦ hconc j p hp.ne) (hconc i)
  have hCB := gradedCartanMatrix_trunc_mul_eulerPowerSeries_bettiPoincareMatrix_eq_one
    S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB
  have hBC := eulerPowerSeries_bettiPoincareMatrix_mul_gradedCartanMatrix_trunc_eq_one
    S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc hB
  have hiff (i j : I) :
      Bigraded.eulerPowerSeries (hB i j) =
          Bigraded.maslovEulerPowerSeries (bettiPoincareMatrix bP r i j) ↔
        ∀ (n : ℕ) (d : ℤ), (n : ℤ) ≠ d →
          (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff d = 0 :=
    Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff (hB i j)
      (fun n d ↦ by
        rw [bettiPoincareMatrix_apply]
        exact (r j).coeff_coeff_bettiPoincareSeries_nonneg S he he₀ hI hne bP hbP
          (hself i) (hconc i) n d)
      (fun n d hdn ↦ by
        rw [bettiPoincareMatrix_apply]
        exact (hr j).coeff_coeff_bettiPoincareSeries_eq_zero_of_lt S he he₀ hI hne bP hbP
          (hself i) (fun p hp ↦ hconc j p hp.ne) (hconc i) (by simpa using hdn))
  rw [forall_isLinear_iff_diagonal_bettiPoincareMatrix S he he₀ hI hne bP hbP r hr hself hS
    hconc hneg]
  constructor
  · intro hdiag
    rw [← hCB]
    congr 1
    exact Matrix.ext fun i j ↦ ((hiff i j).mpr (hdiag i j)).symm
  · intro hCM i j
    have heq : (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries =
        Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) := by
      calc (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries
          = (Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) *
              ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ))) *
              (bettiPoincareMatrix bP r).map Bigraded.maslovEulerPowerSeries := by
            rw [hBC, one_mul]
        _ = Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hB i j)) := by
            rw [Matrix.mul_assoc, hCM, mul_one]
    exact (hiff i j).mp (congrFun (congrFun heq i) j).symm

include he₀ hne hself hS hbP hbM in
/-- **The Koszul Hilbert-series equation `C(q) · P(-q) = I` for linear resolutions.** When the
resolutions `rⱼ` of `Sⱼ` are linear (with finitely generated terms), the diagonal Betti series
`P_{i, j}(q) = ∑_n β_{n, n}^i(Sⱼ) qⁿ` satisfies `C_ps * P(-q) = 1` in
`Matrix I I (PowerSeries ℤ)`. -/
theorem gradedCartanMatrix_trunc_mul_diagonalBettiPowerSeries_eq_one
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite A ((r i).X n)]
    (hlin : ∀ i, (r i).IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    ((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ)) *
      Matrix.of (fun i j ↦ PowerSeries.mk fun n ↦
        (-1 : ℤ) ^ n * (PowerSeries.coeff n (bettiPoincareMatrix bP r i j)).coeff (n : ℤ)) =
      1 := by
  have hr : ∀ i, (r i).IsMinimal := fun i ↦ (hlin i).isMinimal hneg
  have hdiag := (forall_isLinear_iff_diagonal_bettiPoincareMatrix S he he₀ hI hne bP hbP r hr
    hself hS hconc hneg).mp hlin
  have hCM :=
    (forall_isLinear_iff_gradedCartanMatrix_trunc_mul_maslovEulerPowerSeries_eq_one
      S he he₀ hI hne hself hS bP hbP bM hbM r hr hneg hconc).mp hlin
  convert hCM using 2
  refine Matrix.ext fun i j ↦ PowerSeries.ext fun n ↦ ?_
  rw [Matrix.of_apply, PowerSeries.coeff_mk, Matrix.map_apply,
    Bigraded.coeff_maslovEulerPowerSeries_of_diagonal (hdiag i j) n]

end PowerSeries

end TauCeti
