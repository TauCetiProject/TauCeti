/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.Prod
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Symplectic bases and standard planes for quadratic forms in characteristic two

Over a ring of characteristic two, the polar bilinear map `Q.polarBilin` of any quadratic map `Q`
is alternating (`QuadraticMap.isAlt_polarBilin`), and `-1 = 1` turns the standard symplectic matrix
`Matrix.J` into the symmetric pairing matrix pairing each basis vector `b (.inl i)` to `1` with its
partner `b (.inr i)` and to `0` with all other basis vectors
(`QuadraticMap.toMatrix_polarBilin_eq_J_iff`). Over a field of characteristic two, every
finite-dimensional quadratic space `(V, Q)` whose polar form is nondegenerate therefore has even
dimension `2 * m` and admits a symplectic basis
(`QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`), and every basis of a half-dimensional
`Q`-totally isotropic subspace extends to a hyperbolic symplectic basis on which `Q` vanishes
(`QuadraticMap.IsTotallyIsotropic.exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero`).

In symplectic coordinates, `Q` splits isometrically as a finite orthogonal product `QuadraticMap.pi`
of the binary forms `TauCeti.binarySymplectic R a c` (`x ↦ a x₀² + x₀ x₁ + c x₁²`) via
`QuadraticMap.isometryEquivPiBinarySymplectic`. Over `ZMod 2`, every such binary plane is isometric
to `TauCeti.binarySymplectic (ZMod 2) (a * c) (a * c)` via
`TauCeti.isometryEquivBinarySymplecticDiag`, which is either the hyperbolic plane
`QuadraticMap.proj 0 1` (`a * c = 0`) or the unique anisotropic nonsingular plane
`TauCeti.binarySymplectic (ZMod 2) 1 1` (`a = c = 1`), and the orthogonal sum of two anisotropic
planes is isometric to the orthogonal sum of two hyperbolic planes
(`TauCeti.isometryEquivProjProdBinarySymplecticOneOne`). These results underlie the Gauss-sum and
Arf-invariant classification in `TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic`.

The symplectic basis existence and Lagrangian extension steps build on
`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and
`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq_of_finrank`.

## Main definitions

* `TauCeti.binarySymplectic R a c`: the binary quadratic form
  `x ↦ a * x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2` on `Fin 2 → R`.
* `TauCeti.isometryEquivBinarySymplecticDiag`: explicit involutive plane isometry over `ZMod 2`
  between `binarySymplectic (ZMod 2) a c` and `binarySymplectic (ZMod 2) (a * c) (a * c)`.
* `TauCeti.isometryEquivProjProdBinarySymplecticOneOne`: explicit four-dimensional isometry over
  `ZMod 2` between two hyperbolic planes and two anisotropic planes.
* `QuadraticMap.isometryEquivPiBinarySymplectic`: isometric splitting of `Q` in any symplectic basis
  in characteristic two into `QuadraticMap.pi` of binary symplectic planes.

## Main results

* `QuadraticMap.isAlt_polarBilin`: in characteristic two, every polar bilinear map is alternating.
* `QuadraticMap.IsometryEquiv.polarBilin_nondegenerate_iff`,
  `QuadraticMap.polarBilin_prod_nondegenerate_iff`,
  `QuadraticMap.polarBilin_pi_nondegenerate_iff`: behavior of polar nondegeneracy under isometries
  and orthogonal sums.
* `QuadraticMap.toMatrix_polarBilin_eq_J_iff`, `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`:
  characterization and existence of symplectic bases for `Q.polarBilin` in characteristic two.
* `QuadraticMap.IsTotallyIsotropic.exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero`: over a
  field of characteristic two, a basis of a half-dimensional `Q`-totally isotropic subspace extends
  to a hyperbolic symplectic basis.
* `TauCeti.anisotropic_binarySymplectic_one_one`: `x₀² + x₀ x₁ + x₁²` over `ZMod 2` is anisotropic.
* `QuadraticMap.isTotallyIsotropic_range_inl_add_inr` and
  `QuadraticMap.orthogonal_polarBilin_range_inl_add_inr_eq`: the diagonal submodule on `Q.prod Q` is
  a `Q`-totally isotropic Lagrangian subspace in characteristic two.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* A. Pyronneau, *The Arf and Rohklin's invariant*, January 2024, §2.1, Lemmas 2.11–2.13,
  Corollary 2.14, and Theorem 2.15, pp. 4–5.
-/

public section

open Module QuadraticMap Submodule

/-! ### Polar forms, nondegeneracy, and Lagrangian subspaces in characteristic two -/

namespace QuadraticMap

section PolarNondegenerate

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P]

private theorem isRefl_polarBilin (Q : QuadraticMap R M P) : Q.polarBilin.IsRefl :=
  fun x y ↦ (polar_comm Q y x).trans

/-- Isometric equivalence between equal quadratic maps on the same module, acting as the identity on
vectors. -/
def IsometryEquiv.ofEq {S N Q₀ : Type*} [CommSemiring S] [AddCommMonoid N] [AddCommMonoid Q₀]
    [Module S N] [Module S Q₀] {Q₁ Q₂ : QuadraticMap S N Q₀} (h : Q₁ = Q₂) :
    Q₁.IsometryEquiv Q₂ where
  toLinearEquiv := LinearEquiv.refl S N
  map_app' x := by simp [h]

/-- `QuadraticMap.IsometryEquiv.ofEq` acts as the identity on vectors. -/
@[simp]
theorem IsometryEquiv.ofEq_apply {S N Q₀ : Type*} [CommSemiring S] [AddCommMonoid N]
    [AddCommMonoid Q₀] [Module S N] [Module S Q₀] {Q₁ Q₂ : QuadraticMap S N Q₀}
    (h : Q₁ = Q₂) (x : N) :
    IsometryEquiv.ofEq h x = x :=
  (rfl)

/-- In characteristic two, the polar bilinear map of any quadratic map is alternating, because
`polar Q x x = 2 • Q x = 0`. -/
theorem isAlt_polarBilin [CharP R 2] (Q : QuadraticMap R M P) : Q.polarBilin.IsAlt := fun x ↦ by
  rw [polarBilin_apply_apply, polar_self, two_nsmul, ← two_smul R (Q x),
    (CharTwo.two_eq_zero : (2 : R) = 0), zero_smul]

/-- An isometric equivalence preserves nondegeneracy of the polar bilinear form. -/
theorem IsometryEquiv.polarBilin_nondegenerate_iff {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (e : Q₁.IsometryEquiv Q₂) :
    Q₁.polarBilin.Nondegenerate ↔ Q₂.polarBilin.Nondegenerate := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft (isRefl_polarBilin Q₁),
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft (isRefl_polarBilin Q₂)]
  refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ e.injective ?_⟩
  · rw [← e.apply_symm_apply y, ← map_zero e]
    exact congrArg e (h (e.symm y) fun x ↦ by
      simpa [polarBilin_apply_apply, ← e.polar_apply] using hy (e x))
  · rw [map_zero]
    exact h (e x) fun y ↦ by
      simpa [polarBilin_apply_apply, ← e.polar_apply] using hx (e.symm y)

private theorem polarBilin_prod_eq_bilinForm_prod {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.prod Q₂).polarBilin = LinearMap.BilinForm.prod Q₁.polarBilin Q₂.polarBilin := by
  ext <;> simp

/-- The polar bilinear form of an orthogonal product is nondegenerate if and only if both factors
have nondegenerate polar bilinear forms. -/
theorem polarBilin_prod_nondegenerate_iff {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} :
    (Q₁.prod Q₂).polarBilin.Nondegenerate ↔
      Q₁.polarBilin.Nondegenerate ∧ Q₂.polarBilin.Nondegenerate := by
  rw [polarBilin_prod_eq_bilinForm_prod]
  exact LinearMap.BilinForm.nondegenerate_prod_iff

/-- The polar bilinear form of a finite orthogonal product `QuadraticMap.pi Q` is nondegenerate if
and only if each factor has nondegenerate polar bilinear form. -/
theorem polarBilin_pi_nondegenerate_iff {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {Q : ∀ i, QuadraticForm R (M i)} :
    (QuadraticMap.pi Q).polarBilin.Nondegenerate ↔ ∀ i, (Q i).polarBilin.Nondegenerate := by
  classical
  simp only [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (isRefl_polarBilin _), LinearMap.SeparatingLeft, polarBilin_apply_apply,
    QuadraticMap.Ring.polar_pi]
  refine ⟨fun h i v hv ↦ ?_, fun h x hx ↦ funext fun i ↦ h i (x i) fun v ↦ ?_⟩
  · have hsingle := h (Pi.single i v) fun y ↦ by
      rw [Fintype.sum_eq_single i]
      · simpa using hv (y i)
      · intro j hj
        simp [Pi.single_eq_of_ne hj]
    simpa using congrFun hsingle i
  · have hsingle := hx (Pi.single i v)
    rw [Fintype.sum_eq_single i] at hsingle
    · simpa using hsingle
    · intro j hj
      simp [Pi.single_eq_of_ne hj]

end PolarNondegenerate

section TotallyIsotropic

variable {R K M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Field K] [AddCommGroup V] [Module K V]

/-- A `Q`-totally isotropic submodule is contained in its own polar orthogonal complement. -/
theorem IsTotallyIsotropic.le_orthogonal_polarBilin {Q : QuadraticForm R M} {U : Submodule R M}
    (hU : Q.IsTotallyIsotropic U) :
    U ≤ LinearMap.BilinForm.orthogonal Q.polarBilin U := fun _ hv ↦
  LinearMap.BilinForm.mem_orthogonal_iff.mpr fun _ hw ↦ hU.polar_eq_zero hw hv

/-- In a finite-dimensional quadratic space whose polar bilinear form is nondegenerate, any
`Q`-totally isotropic subspace has at most half the ambient dimension. -/
theorem IsTotallyIsotropic.two_mul_finrank_le [FiniteDimensional K V] {Q : QuadraticForm K V}
    {U : Submodule K V} (hU : Q.IsTotallyIsotropic U) (hQ : Q.polarBilin.Nondegenerate) :
    2 * finrank K U ≤ finrank K V :=
  LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal hQ hU.le_orthogonal_polarBilin

/-- For a `Q`-totally isotropic subspace of a finite-dimensional space with nondegenerate polar
form, being equal to its polar orthogonal complement is equivalent to having half the ambient
dimension. -/
theorem IsTotallyIsotropic.orthogonal_polarBilin_eq_iff_two_mul_finrank_eq [FiniteDimensional K V]
    {Q : QuadraticForm K V} {U : Submodule K V} (hU : Q.IsTotallyIsotropic U)
    (hQ : Q.polarBilin.Nondegenerate) :
    LinearMap.BilinForm.orthogonal Q.polarBilin U = U ↔ 2 * finrank K U = finrank K V := by
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal (isRefl_polarBilin Q) U
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_bot_eq, finrank_bot, add_zero] at hdim
  refine ⟨fun h ↦ by rw [h] at hdim; omega, fun h ↦ ?_⟩
  exact (Submodule.eq_of_le_of_finrank_eq hU.le_orthogonal_polarBilin (by omega)).symm

/-- **Hyperbolic symplectic basis extension.** Over a field of characteristic two, every basis of a
half-dimensional `Q`-totally isotropic subspace extends to a symplectic basis of `Q.polarBilin` on
all of whose vectors `Q` vanishes, with the prescribed basis vectors in the `Sum.inl` positions. -/
theorem IsTotallyIsotropic.exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero [CharP K 2]
    [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V}
    (hU : Q.IsTotallyIsotropic U) (e : Basis ι K U)
    (hdim : Fintype.card ι + Fintype.card ι = finrank K V) :
    ∃ b : Basis (ι ⊕ ι) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι K ∧
        (∀ i, b (.inl i) = (e i : V)) ∧ ∀ x, Q (b x) = 0 := by
  -- Step 1: extend `e` to an alternating symplectic basis `b₀` of `Q.polarBilin`.
  obtain ⟨b₀, hb₀, hinl₀⟩ :=
    LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq_of_finrank (isAlt_polarBilin Q)
      hQ e hU.le_orthogonal_polarBilin hdim
  have hentry (x y : ι ⊕ ι) : polar Q (b₀ x) (b₀ y) = Matrix.J ι K x y := by
    simpa [polarBilin_apply_apply] using congrFun₂ hb₀ x y
  have heQ (i : ι) : Q (b₀ (.inl i)) = 0 := by
    rw [hinl₀]
    exact hU.apply_eq_zero (e i).2
  -- Step 2: shear each dual partner `b₀ (.inr i)` along `b₀ (.inl i)` to kill its quadratic norm
  -- while preserving the Gram matrix `Matrix.J` and hence linear independence.
  let f' (i : ι) : V := b₀ (.inr i) - Q (b₀ (.inr i)) • b₀ (.inl i)
  let d : ι ⊕ ι → V := Sum.elim (fun i ↦ b₀ (.inl i)) f'
  have hd (x y : ι ⊕ ι) : Q.polarBilin (d x) (d y) = Matrix.J ι K x y := by
    rcases x with i | i <;> rcases y with j | j
    · simpa [d] using hentry (.inl i) (.inl j)
    · have hll := hentry (.inl i) (.inl j)
      simp only [Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply] at hll
      simp [d, f', hentry (.inl i) (.inr j), hll]
    · have hll := hentry (.inl i) (.inl j)
      simp only [Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply] at hll
      simp [d, f', hentry (.inr i) (.inl j), hll]
    · rcases eq_or_ne i j with rfl | hij
      · simpa [Matrix.J] using
          LinearMap.BilinForm.IsAlt.self_eq_zero (isAlt_polarBilin Q) (d (.inr i))
      · have hrr := hentry (.inr i) (.inr j)
        have hrl := hentry (.inr i) (.inl j)
        have hlr := hentry (.inl i) (.inr j)
        have hll := hentry (.inl i) (.inl j)
        simp only [Matrix.J, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply,
          Matrix.neg_apply, Matrix.one_apply, hij, ↓reduceIte, neg_zero]
          at hrr hrl hlr hll ⊢
        simp [d, f', hrr, hrl, hlr, hll]
  have hgram : (Matrix.of fun x y ↦ Q.polarBilin (d x) (d y)) = Matrix.J ι K := Matrix.ext hd
  have hli : LinearIndependent K d := by
    apply LinearMap.BilinForm.linearIndependent_of_det_ne_zero Q.polarBilin
    rw [hgram]
    exact (Matrix.isUnit_det_J ι K).ne_zero
  have hcard : Fintype.card (ι ⊕ ι) = finrank K V := by simpa using hdim
  let b := basisOfLinearIndependentOfCardEqFinrank' d hli hcard
  have hb : ⇑b = d := coe_basisOfLinearIndependentOfCardEqFinrank' d hli hcard
  -- Step 3: check `Q (b x) = 0` on both halves of the sheared basis `b`.
  refine ⟨b, Matrix.ext fun x y ↦ by rw [LinearMap.BilinForm.toMatrix_apply, hb, hd],
    fun i ↦ by rw [hb]; exact hinl₀ i, ?_⟩
  rintro (i | i)
  · rw [hb]
    exact heQ i
  · rw [hb]
    dsimp [d, f']
    have hpair : polar Q (b₀ (.inr i)) (b₀ (.inl i)) = 1 := by
      simpa [Matrix.J] using hentry (.inr i) (.inl i)
    rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), Q.map_neg, Q.map_smul, heQ i, smul_zero,
      add_zero, polar_neg_right, polar_smul_right, hpair, smul_eq_mul, mul_one, add_neg_cancel]

/-- Variant of `exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero` phrased in terms of a
Lagrangian (`LinearMap.BilinForm.orthogonal Q.polarBilin U = U`) `Q`-totally isotropic subspace. -/
theorem IsTotallyIsotropic.exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero_of_orthogonal_eq
    [CharP K 2] [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V}
    (hU : Q.IsTotallyIsotropic U) (e : Basis ι K U)
    (horth : LinearMap.BilinForm.orthogonal Q.polarBilin U = U) :
    ∃ b : Basis (ι ⊕ ι) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι K ∧
        (∀ i, b (.inl i) = (e i : V)) ∧ ∀ x, Q (b x) = 0 := by
  have htwo := (hU.orthogonal_polarBilin_eq_iff_two_mul_finrank_eq hQ).mp horth
  rw [finrank_eq_card_basis e, two_mul] at htwo
  exact hU.exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero hQ e htwo

end TotallyIsotropic

section SymplecticCharTwo

variable {R K M V : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]
  [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

/-- **Symplectic basis characterization in characteristic two.** Since `-1 = 1` in `R`, the Gram
matrix of `Q.polarBilin` in a basis `b` indexed by `ι ⊕ ι` equals `Matrix.J ι R` if and only if
same-half polar pairings vanish and `polar Q (b (.inl i)) (b (.inr j))` is the Kronecker delta. -/
theorem toMatrix_polarBilin_eq_J_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M) :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R ↔
      (∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0) ∧
        (∀ i j, polar Q (b (.inr i)) (b (.inr j)) = 0) ∧
        ∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0 := by
  constructor
  · intro h
    have hentry (x y : ι ⊕ ι) : polar Q (b x) (b y) = Matrix.J ι R x y := by
      simpa [polarBilin_apply_apply] using congrFun₂ h x y
    refine ⟨fun i j ↦ by simpa [Matrix.J] using hentry (.inl i) (.inl j),
      fun i j ↦ by simpa [Matrix.J] using hentry (.inr i) (.inr j), fun i j ↦ ?_⟩
    rw [polar_comm]
    simpa [Matrix.J, Matrix.one_apply, eq_comm] using hentry (.inr j) (.inl i)
  · rintro ⟨hll, hrr, hlr⟩
    ext (i | i) (j | j)
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using hll i j
    · simp only [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, hlr i j, Matrix.J,
        Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.one_apply]
      split_ifs
      · exact CharTwo.neg_one_eq_one.symm
      · simp
    · rw [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_comm, hlr j i]
      simp [Matrix.J, Matrix.one_apply, eq_comm]
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using hrr i j

/-- Over a field of characteristic two, a finite-dimensional space carrying a quadratic form with
nondegenerate polar form has even dimension. -/
theorem even_finrank_of_polarBilin_nondegenerate [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) : Even (finrank K V) :=
  LinearMap.BilinForm.IsAlt.even_finrank Q.isAlt_polarBilin hQ

/-- **Existence of a quadratic symplectic basis in characteristic two.** Every finite-dimensional
quadratic space `(V, Q)` over a field of characteristic two with `Q.polarBilin.Nondegenerate` has
even dimension `2 * m` (`m = 0` included) and a basis `b : Basis (Fin m ⊕ Fin m) K V` in which
`Q.polarBilin` has matrix `Matrix.J (Fin m) K`. -/
theorem exists_basis_toMatrix_polarBilin_eq_J [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V),
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K ∧ finrank K V = 2 * m := by
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J Q.isAlt_polarBilin hQ
  refine ⟨m, b, hb, ?_⟩
  rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin, two_mul]

omit [CharP K 2] in
/-- A finite `ι ⊕ ι`-indexed basis in which `Q.polarBilin` has matrix `Matrix.J ι K` forces
`Q.polarBilin` to be nondegenerate. -/
theorem polarBilin_nondegenerate_of_toMatrix_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K V} {b : Basis (ι ⊕ ι) K V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι K) :
    Q.polarBilin.Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (B := Q.polarBilin) b).mpr <| by
    rw [hb]
    exact (Matrix.isUnit_det_J ι K).ne_zero

end SymplecticCharTwo

end QuadraticMap

/-! ### Binary symplectic quadratic forms and standard planes -/

namespace TauCeti

universe u

section BinarySymplectic

variable {R : Type u}

/-- The binary quadratic form `x ↦ a * x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2` on `Fin 2 → R`.

In characteristic two its polar bilinear form is the standard hyperbolic pairing
`(x, y) ↦ x 0 * y 1 + x 1 * y 0` independently of `a` and `c`. At `(0, 0)` it reduces to the
hyperbolic `x 0 * x 1` plane `QuadraticMap.proj 0 1`; over `ZMod 2` at `(1, 1)` it is the unique
anisotropic nonsingular plane `x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2`. -/
def binarySymplectic (R : Type u) [CommSemiring R] (a c : R) : QuadraticForm R (Fin 2 → R) :=
  a • QuadraticMap.proj 0 0 + QuadraticMap.proj 0 1 + c • QuadraticMap.proj 1 1

/-- Coordinate formula for `TauCeti.binarySymplectic`. -/
@[simp]
theorem binarySymplectic_apply [CommSemiring R] (a c : R) (x : Fin 2 → R) :
    binarySymplectic R a c x = a * x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2 := by
  simp [binarySymplectic, pow_two]

/-- At `(0, 0)`, `TauCeti.binarySymplectic` reduces to Mathlib's `QuadraticMap.proj 0 1`
(`x ↦ x 0 * x 1`). -/
@[simp]
theorem binarySymplectic_zero_zero [CommSemiring R] :
    binarySymplectic R 0 0 = QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) := by
  ext x
  simp

/-- Polarization of `QuadraticMap.proj 0 1` on `Fin 2 → R`. -/
@[simp]
theorem polar_proj_zero_one [CommRing R] (x y : Fin 2 → R) :
    polar (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) : QuadraticForm R (Fin 2 → R)) x y =
      x 0 * y 1 + x 1 * y 0 := by
  simp only [polar, proj_apply, Pi.add_apply]
  ring

/-- Polarization of `TauCeti.binarySymplectic` over a commutative ring. -/
theorem polar_binarySymplectic [CommRing R] (a c : R) (x y : Fin 2 → R) :
    polar (binarySymplectic R a c) x y =
      2 * a * (x 0 * y 0) + (x 0 * y 1 + x 1 * y 0) + 2 * c * (x 1 * y 1) := by
  simp only [polar, binarySymplectic_apply, Pi.add_apply]
  ring

/-- In characteristic two, the polarization of `TauCeti.binarySymplectic R a c` is the standard
symplectic pairing `x 0 * y 1 + x 1 * y 0`, independent of `a` and `c`. -/
@[simp]
theorem polar_binarySymplectic_charTwo [CommRing R] [CharP R 2] (a c : R) (x y : Fin 2 → R) :
    polar (binarySymplectic R a c) x y = x 0 * y 1 + x 1 * y 0 := by
  rw [polar_binarySymplectic, CharTwo.two_eq_zero]
  ring

/-- The polar bilinear form of the `x 0 * x 1` plane `QuadraticMap.proj 0 1` is nondegenerate over
every commutative ring. -/
theorem nondegenerate_polarBilin_proj_zero_one [CommRing R] :
    (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
      QuadraticForm R (Fin 2 → R)).polarBilin.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (isRefl_polarBilin _)).mpr fun x hx ↦ ?_
  have h0 : x 0 = 0 := by simpa using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- In characteristic two, the polar bilinear form of `TauCeti.binarySymplectic R a c` is
nondegenerate for all `a, c : R`. -/
theorem nondegenerate_polarBilin_binarySymplectic [CommRing R] [CharP R 2] (a c : R) :
    (binarySymplectic R a c).polarBilin.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (isRefl_polarBilin _)).mpr fun x hx ↦ ?_
  have h0 : x 0 = 0 := by simpa using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- Over `ZMod 2`, the binary plane `x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2` is anisotropic: its only zero
is the zero vector. -/
theorem anisotropic_binarySymplectic_one_one :
    (binarySymplectic (ZMod 2) 1 1).Anisotropic := by
  intro x hx
  rw [binarySymplectic_apply, one_mul, one_mul] at hx
  have h01 : x 0 = 0 ∧ x 1 = 0 :=
    (by decide : ∀ a b : ZMod 2, a ^ 2 + a * b + b ^ 2 = 0 → a = 0 ∧ b = 0) (x 0) (x 1) hx
  ext i
  fin_cases i <;> simp [h01.1, h01.2]

/-- The first coordinate axis `R ∙ ![1, 0]` is totally isotropic for the hyperbolic `x 0 * x 1`
plane `QuadraticMap.proj 0 1`. -/
theorem isTotallyIsotropic_span_proj_zero_one [CommSemiring R] :
    (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
      QuadraticForm R (Fin 2 → R)).IsTotallyIsotropic (R ∙ ![(1 : R), 0]) := by
  rw [isTotallyIsotropic_span_singleton_iff]
  simp

/-- Over any nontrivial commutative semiring, the hyperbolic `x 0 * x 1` plane is isotropic. -/
theorem not_anisotropic_proj_zero_one [CommSemiring R] [Nontrivial R] :
    ¬ (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) : QuadraticForm R (Fin 2 → R)).Anisotropic := by
  intro h
  have hzero := h ![(1 : R), 0] (by simp)
  exact one_ne_zero (congrFun hzero 0)

/-- Over `ZMod 2`, every binary symplectic plane `binarySymplectic (ZMod 2) a c` is isometric to
the diagonal-equalized plane `binarySymplectic (ZMod 2) (a * c) (a * c)` (which is
`QuadraticMap.proj 0 1` when `a * c = 0`, and `binarySymplectic (ZMod 2) 1 1` when `a * c = 1`). -/
def isometryEquivBinarySymplecticDiag (a c : ZMod 2) :
    (binarySymplectic (ZMod 2) a c).IsometryEquiv
      (binarySymplectic (ZMod 2) (a * c) (a * c)) where
  toFun v :=
    ![v 0 + (1 + a) * c * v 1, v 1 + a * (1 + c) * v 0]
  invFun v :=
    ![v 0 + (1 + a) * c * v 1, v 1 + a * (1 + c) * v 0]
  map_add' u v := by
    ext i
    fin_cases i <;> · simp; ring
  map_smul' r v := by
    ext i
    fin_cases i <;> · simp; ring
  left_inv v := by
    ext i
    fin_cases i
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (by decide : ∀ a c x y : ZMod 2,
          (x + (1 + a) * c * y) + (1 + a) * c * (y + a * (1 + c) * x) = x) a c (v 0) (v 1)
    · simpa only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (by decide : ∀ a c x y : ZMod 2,
          (y + a * (1 + c) * x) + a * (1 + c) * (x + (1 + a) * c * y) = y) a c (v 0) (v 1)
  right_inv v := by
    ext i
    fin_cases i
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (by decide : ∀ a c x y : ZMod 2,
          (x + (1 + a) * c * y) + (1 + a) * c * (y + a * (1 + c) * x) = x) a c (v 0) (v 1)
    · simpa only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] using
        (by decide : ∀ a c x y : ZMod 2,
          (y + a * (1 + c) * x) + a * (1 + c) * (x + (1 + a) * c * y) = y) a c (v 0) (v 1)
  map_app' v := by
    simpa only [binarySymplectic_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
      (by decide : ∀ a c x y : ZMod 2,
        a * c * (x + (1 + a) * c * y) ^ 2 +
          (x + (1 + a) * c * y) * (y + a * (1 + c) * x) +
          a * c * (y + a * (1 + c) * x) ^ 2 =
        a * x ^ 2 + x * y + c * y ^ 2) a c (v 0) (v 1)

/-- Forward coordinate formula for `TauCeti.isometryEquivBinarySymplecticDiag`. -/
@[simp]
theorem isometryEquivBinarySymplecticDiag_apply (a c : ZMod 2) (v : Fin 2 → ZMod 2) :
    isometryEquivBinarySymplecticDiag a c v =
      ![v 0 + (1 + a) * c * v 1, v 1 + a * (1 + c) * v 0] :=
  (rfl)

/-- Inverse coordinate formula for `TauCeti.isometryEquivBinarySymplecticDiag`. -/
@[simp]
theorem isometryEquivBinarySymplecticDiag_symm_apply (a c : ZMod 2) (v : Fin 2 → ZMod 2) :
    (isometryEquivBinarySymplecticDiag a c).symm v =
      ![v 0 + (1 + a) * c * v 1, v 1 + a * (1 + c) * v 0] :=
  (rfl)

/-- Over `ZMod 2`, if `a * c = 0`, then `binarySymplectic (ZMod 2) a c` is isometric to the
hyperbolic `x 0 * x 1` plane `QuadraticMap.proj 0 1`. -/
def isometryEquivProjOfMulEqZero {a c : ZMod 2} (h : a * c = 0) :
    (binarySymplectic (ZMod 2) a c).IsometryEquiv
       (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)) :=
  (isometryEquivBinarySymplecticDiag a c).trans <|
    IsometryEquiv.ofEq (by rw [h, binarySymplectic_zero_zero])

/-- **Two anisotropic planes over `ZMod 2` are isometric to two hyperbolic planes.**

In the standard symplectic basis `e₁, f₁, e₂, f₂` of the orthogonal sum of two copies of
`x₀² + x₀ x₁ + x₁²`, the vectors `e₁ + e₂`, `f₁ + e₂`, `e₁ + f₁ + f₂`, and `e₁ + f₁ + e₂ + f₂`
are all isotropic and form two orthogonal hyperbolic pairs. -/
def isometryEquivProjProdBinarySymplecticOneOne :
    ((QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2)).prod
      (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2))).IsometryEquiv
      ((binarySymplectic (ZMod 2) 1 1).prod (binarySymplectic (ZMod 2) 1 1)) where
  toFun p :=
    (![p.1 0 + p.2 0 + p.2 1, p.1 1 + p.2 0 + p.2 1],
      ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1])
  invFun q :=
    (![q.1 0 + q.2 1, q.1 1 + q.2 1],
      ![q.1 0 + q.1 1 + q.2 0 + q.2 1, q.1 0 + q.1 1 + q.2 0])
  map_add' p q := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    · fin_cases i <;> · simp; ring
  map_smul' r p := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    · fin_cases i <;> · simp; ring
  left_inv p := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · fin_cases i
      · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a c d : ZMod 2, (a + c + d) + (c + d) = a)
            (p.1 0) (p.2 0) (p.2 1)
      · simpa only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ b c d : ZMod 2, (b + c + d) + (c + d) = b)
            (p.1 1) (p.2 0) (p.2 1)
    · fin_cases i
      · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a b c d : ZMod 2,
            (a + c + d) + (b + c + d) + (a + b + d) + (c + d) = c)
            (p.1 0) (p.1 1) (p.2 0) (p.2 1)
      · simpa only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a b c d : ZMod 2,
            (a + c + d) + (b + c + d) + (a + b + d) = d)
            (p.1 0) (p.1 1) (p.2 0) (p.2 1)
  right_inv q := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · fin_cases i
      · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a b c d : ZMod 2,
            (a + d) + (a + b + c + d) + (a + b + c) = a)
            (q.1 0) (q.1 1) (q.2 0) (q.2 1)
      · simpa only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a b c d : ZMod 2,
            (b + d) + (a + b + c + d) + (a + b + c) = b)
            (q.1 0) (q.1 1) (q.2 0) (q.2 1)
    · fin_cases i
      · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a b c d : ZMod 2,
            (a + d) + (b + d) + (a + b + c) = c)
            (q.1 0) (q.1 1) (q.2 0) (q.2 1)
      · simpa only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] using
          (by decide : ∀ a b c d : ZMod 2,
            (a + b + c + d) + (a + b + c) = d)
            (q.1 0) (q.1 1) (q.2 0) (q.2 1)
  map_app' p := by
    simpa only [QuadraticMap.prod_apply, binarySymplectic_apply, proj_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] using
      (by decide : ∀ a b c d : ZMod 2,
        (1 * (a + c + d) ^ 2 + (a + c + d) * (b + c + d) + 1 * (b + c + d) ^ 2) +
          (1 * (a + b + d) ^ 2 + (a + b + d) * (c + d) + 1 * (c + d) ^ 2) =
        a * b + c * d) (p.1 0) (p.1 1) (p.2 0) (p.2 1)

/-- Forward coordinate formula for `TauCeti.isometryEquivProjProdBinarySymplecticOneOne`. -/
@[simp]
theorem isometryEquivProjProdBinarySymplecticOneOne_apply
    (p : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    isometryEquivProjProdBinarySymplecticOneOne p =
      (![p.1 0 + p.2 0 + p.2 1, p.1 1 + p.2 0 + p.2 1],
        ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1]) :=
  (rfl)

/-- Inverse coordinate formula for `TauCeti.isometryEquivProjProdBinarySymplecticOneOne`. -/
@[simp]
theorem isometryEquivProjProdBinarySymplecticOneOne_symm_apply
    (q : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :
    isometryEquivProjProdBinarySymplecticOneOne.symm q =
      (![q.1 0 + q.2 1, q.1 1 + q.2 1],
        ![q.1 0 + q.1 1 + q.2 0 + q.2 1, q.1 0 + q.1 1 + q.2 0]) :=
  (rfl)

end BinarySymplectic

end TauCeti

namespace QuadraticMap

section SymplecticCoordIsometry

variable {R M : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]

/-- Coordinate reindexing identifying `ι → Fin 2 → R` with `ι ⊕ ι → R` via
`x ↦ Sum.elim (fun i ↦ x i 0) (fun i ↦ x i 1)`. -/
private def piFinTwoEquivSum (R ι : Type*) [Semiring R] :
    (ι → Fin 2 → R) ≃ₗ[R] (ι ⊕ ι → R) where
  toFun x := Sum.elim (fun i ↦ x i 0) (fun i ↦ x i 1)
  invFun f i := ![f (.inl i), f (.inr i)]
  map_add' _ _ := by ext (_ | _) <;> rfl
  map_smul' _ _ := by ext (_ | _) <;> rfl
  left_inv x := funext fun i ↦ funext fun j ↦ by fin_cases j <;> rfl
  right_inv f := funext fun s ↦ by cases s <;> rfl

/-- **Symplectic coordinate splitting.** In characteristic two, any symplectic basis
`b : Basis (ι ⊕ ι) R M` for `Q.polarBilin` identifies `Q` isometrically with the orthogonal
product `QuadraticMap.pi` of the binary forms
`TauCeti.binarySymplectic R (Q (b (.inl i))) (Q (b (.inr i)))`. -/
noncomputable def isometryEquivPiBinarySymplectic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    (QuadraticMap.pi fun i ↦
      TauCeti.binarySymplectic R (Q (b (.inl i))) (Q (b (.inr i)))).IsometryEquiv Q where
  toLinearEquiv := (piFinTwoEquivSum R ι).trans b.equivFun.symm
  map_app' x := by
    obtain ⟨hll, hrr, hlr⟩ := (Q.toMatrix_polarBilin_eq_J_iff b).mp hb
    let g (i : ι) : M := x i 0 • b (.inl i) + x i 1 • b (.inr i)
    have hvec : b.equivFun.symm (piFinTwoEquivSum R ι x) = ∑ i, g i := by
      rw [Basis.equivFun_symm_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      rfl
    -- Expose the underlying linear equivalence of the structure literal to rewrite by `hvec`.
    change Q (b.equivFun.symm (piFinTwoEquivSum R ι x)) = _
    rw [hvec, Q.map_sum]
    have hcross : ∑ ij ∈ Finset.univ.sym2 with ¬ ij.IsDiag, polarSym2 Q (ij.map g) = 0 := by
      refine Finset.sum_eq_zero fun ij hij ↦ ?_
      induction ij using Sym2.ind with
      | h i j =>
        have hij' : i ≠ j := by simpa using (Finset.mem_filter.mp hij).2
        simp [g, hll i j, hrr i j, hlr i j, polar_comm (⇑Q) (b (.inr i)) (b (.inl j)),
          hlr j i, hij', hij'.symm]
    rw [hcross, add_zero, pi_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hp : polar Q (x i 0 • b (.inl i)) (x i 1 • b (.inr i)) = x i 0 * x i 1 := by
      simp only [polar_smul_left, polar_smul_right, hlr i i, ↓reduceIte, smul_eq_mul, mul_one]
      ring
    rw [TauCeti.binarySymplectic_apply]
    simp only [g, QuadraticMap.map_add (⇑Q), Q.map_smul, hp, smul_eq_mul]
    ring

/-- Symplectic coordinate splitting sends `x : ι → Fin 2 → R` to
`∑ i, (x i 0 • b (.inl i) + x i 1 • b (.inr i))`. -/
@[simp]
theorem isometryEquivPiBinarySymplectic_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (x : ι → Fin 2 → R) :
    Q.isometryEquivPiBinarySymplectic b hb x =
      ∑ i, (x i 0 • b (.inl i) + x i 1 • b (.inr i)) := by
  -- This is the unfolding lemma for `isometryEquivPiBinarySymplectic`, so no `rw` lemma applies to
  -- its LHS yet; expose its `toLinearEquiv` definition directly.
  change b.equivFun.symm (piFinTwoEquivSum R ι x) = _
  rw [Basis.equivFun_symm_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

end SymplecticCoordIsometry

section DiagonalLagrangian

/-- In characteristic two, on the orthogonal sum `Q.prod Q` of two copies of any quadratic form `Q`,
the diagonal submodule `{(x, x) | x : M}` is totally isotropic. -/
theorem isTotallyIsotropic_range_inl_add_inr {R M : Type*} [CommRing R] [CharP R 2]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) :
    (Q.prod Q).IsTotallyIsotropic
      (LinearMap.range (LinearMap.inl R M M + LinearMap.inr R M M)) := by
  rw [isTotallyIsotropic_iff]
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add, prod_apply]
  rw [← two_mul, CharTwo.two_eq_zero, zero_mul]

/-- Over a field of characteristic two, when `Q.polarBilin` is nondegenerate on a finite-dimensional
space `V`, the diagonal submodule `{(x, x) | x : V}` is a Lagrangian (`W^⊥ = W`) `(Q.prod Q)`-zero
subspace. For `Q = TauCeti.binarySymplectic (ZMod 2) 1 1`, this gives an explicit two-dimensional
`Q`-zero Lagrangian inside the orthogonal sum of two anisotropic planes. -/
theorem orthogonal_polarBilin_range_inl_add_inr_eq {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) :
    LinearMap.BilinForm.orthogonal (Q.prod Q).polarBilin
      (LinearMap.range (LinearMap.inl K V V + LinearMap.inr K V V)) =
      LinearMap.range (LinearMap.inl K V V + LinearMap.inr K V V) := by
  refine ((isTotallyIsotropic_range_inl_add_inr Q).orthogonal_polarBilin_eq_iff_two_mul_finrank_eq
    (polarBilin_prod_nondegenerate_iff.mpr ⟨hQ, hQ⟩)).mpr ?_
  rw [LinearMap.finrank_range_of_inj fun _ _ h ↦ by simpa using (Prod.mk.inj h).1,
    Module.finrank_prod, two_mul]

end DiagonalLagrangian

end QuadraticMap
