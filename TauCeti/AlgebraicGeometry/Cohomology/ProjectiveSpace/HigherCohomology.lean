/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Data.Int.Interval
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.CategoryTheory.Limits.Lattice
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.Finsupp.Supported
import TauCeti.LinearAlgebra.Matrix.Determinant.TupleSign
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Higher cohomology of the twisting sheaves on projective space

Let `M` be a free `R`-module with a basis `x₀, …, xₙ` indexed by a finite type `κ`, so that
`Proj (Sym M) = ℙⁿ_R` is projective space over an arbitrary commutative ring `R`. This file proves
that the twisting sheaves `𝒪(m)` have no cohomology in the intermediate degrees `0 < q < n`, for
every `m : ℤ`, and none at all in positive degrees when `m > -n - 1`. For `n ≥ 1` it shows that the
top cohomology `Hⁿ(ℙⁿ_R, 𝒪(m))` is isomorphic to the free `R`-module on the Laurent monomials `xᵉ`
of degree `m` all of whose exponents are negative. Together with the computation of `H⁰`
(`TauCeti.SymmetricAlgebra.free_cohomology_zero_twistingSheaf`) and the vanishing above degree `n`
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`), this computes the groups
`Hᵠ(ℙⁿ_R, 𝒪(m))` in every degree, and shows that for `n ≥ 1` they are finitely generated
`R`-modules. The duality pairing of Hartshorne, Theorem III.5.1(d), is not treated here.

The proof computes Čech cohomology for the standard affine cover by the charts `D₊(xᵢ)`, following
the Stacks Project. On the chart `D₊(x_S)` of a nonempty set `S` of coordinates, with
`x_S = ∏_{i ∈ S} xᵢ`, the sections of `𝒪(m)` are the Laurent polynomials of degree `m` whose
monomials `xᵉ` have negative exponents `eᵢ < 0` only for `i ∈ S`: every section is a fraction
`r / x_Sᵏ`, and since the coordinates are nonzerodivisors two fractions agree exactly when they do
after cross-multiplication. These identifications are compatible with restriction, so the Čech
complex of `𝒪(m)` is the Čech complex of the presheaf `S ↦ {Laurent polynomials of degree m with
negative exponents only in S}` on the finite sets of coordinates.

This presheaf is the direct sum, over the sets `T` of coordinates, of the parts spanned by the
monomials `xᵉ` whose set of negative exponents is exactly `T`. For `T` missing a coordinate `c`,
the part indexed by `T` does not change when `S` is replaced by `S ∪ {c}`; its Čech complex is
therefore that of a presheaf restricted to the chart of `c`, which is a member of the cover, and it
is exact in positive degrees (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_prod_of_hom`). The
part indexed by `T = κ` is zero on a set `S` of fewer than `n + 1` coordinates, so it contributes
nothing to the Čech complex in degrees `q < n`, and it vanishes altogether when `m > -n - 1`,
because a monomial with all exponents negative has degree at most `-n - 1`. Finally Leray's theorem
(`AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology`) identifies Čech cohomology
with the cohomology of `𝒪(m)`, the intersections of the charts being affine.

In the top degree `n` the parts indexed by `T ≠ κ` still contribute nothing, and the part indexed
by `T = κ` vanishes on every tuple of `n + 1` coordinates that is not a permutation of all of them.
Its Čech cohomology in degree `n` consists of its cocycles, which are alternating functions on the
orderings of the coordinates: the cocycle condition at a tuple repeating one entry two places later
changes the sign under an adjacent transposition. Such a cocycle is determined by its value at one
ordering, and conversely every value is attained, by the cocycle `a ↦ det(Pₐ) xᵉ`, where `Pₐ` is
the matrix of the tuple `a` whose rows are standard basis vectors. Its cocycle condition is the
expansion along the first column of a matrix whose first column is the sum of the others. The
resulting identification is linear over `R`, because sections over the charts are linear in the
Laurent coefficients.

## Main results

* `Module.Basis.subsingleton_cohomology_twistingSheaf_of_lt_card`:
  `Hᵠ(ℙⁿ_R, 𝒪(m)) = 0` for `0 < q < n` and every `m : ℤ`.
* `Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`:
  `Hᵠ(ℙⁿ_R, 𝒪(m)) = 0` for every `q > 0` when `m > -n - 1`.
* `Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf`: for `n ≥ 1`,
  `Hⁿ(ℙⁿ_R, 𝒪(m))` is isomorphic to the free `R`-module on the exponents
  `TauCeti.SymmetricAlgebra.negativeExponents κ m` of the Laurent monomials of degree `m` with all
  exponents negative.
* `Module.Basis.finite_cohomology_twistingSheaf`: for `n ≥ 1`, `Hᵠ(ℙⁿ_R, 𝒪(m))` is a finitely
  generated `R`-module for every `q` and `m`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1(b) and (c).
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS), whose proof
  decomposes the Čech complex of the standard cover by the multidegree of Laurent monomials.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open _root_.SymmetricAlgebra (ι equivMvPolynomial)

namespace TauCeti.SymmetricAlgebra

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
  {κ : Type u} (b : Module.Basis κ R M)

local notation "𝒜" => homogeneousSubmodule R M

/-! ### Laurent exponents -/

section Exponents

variable [Fintype κ] [DecidableEq κ]

/-- The coordinates in which a Laurent exponent is negative. -/
private def negSupport (e : κ → ℤ) : Finset κ := {i | e i < 0}

omit [DecidableEq κ] in
private lemma mem_negSupport {e : κ → ℤ} {i : κ} : i ∈ negSupport e ↔ e i < 0 := by
  simp [negSupport]

/-- The Laurent exponents of total degree `m` which are negative only in coordinates of `S`: the
monomials of degree `m` of the localization at the product of the coordinates in `S`. -/
private def chartExponents (m : ℤ) (S : Finset κ) : Set (κ → ℤ) :=
  {e | ∑ i, e i = m ∧ negSupport e ⊆ S}

omit [DecidableEq κ] in
private lemma chartExponents_mono {m : ℤ} {S S' : Finset κ} (h : S ⊆ S') :
    chartExponents m S ⊆ chartExponents m S' :=
  fun _ he ↦ ⟨he.1, he.2.trans h⟩

omit [DecidableEq κ] in
private lemma nonneg_of_mem_chartExponents {m : ℤ} {S : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) {i : κ} (hi : i ∉ S) : 0 ≤ e i :=
  not_lt.1 fun h ↦ hi (he.2 (mem_negSupport.2 h))

/-- The exponent of the numerator of the Laurent monomial `xᵉ` written over the denominator
`(∏_{i ∈ S} xᵢ)ʲ`. -/
private def numeratorExponent (e : κ → ℤ) (S : Finset κ) (j : ℕ) : κ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (e i + if i ∈ S then (j : ℤ) else 0).toNat

private lemma coe_numeratorExponent {m : ℤ} {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S)
    {j : ℕ} (hj : ∀ i ∈ S, 0 ≤ e i + j) (i : κ) :
    (numeratorExponent e S j i : ℤ) = e i + if i ∈ S then (j : ℤ) else 0 := by
  simp only [numeratorExponent, Finsupp.equivFunOnFinite_symm_apply_apply]
  refine Int.toNat_of_nonneg ?_
  split_ifs with hi
  · exact hj i hi
  · simpa using nonneg_of_mem_chartExponents he hi

private lemma degree_numeratorExponent {m : ℤ} {S : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) {j : ℕ} (hj : ∀ i ∈ S, 0 ≤ e i + j) :
    ((numeratorExponent e S j).degree : ℤ) = j * S.card + m := by
  rw [Finsupp.degree_eq_sum, Nat.cast_sum]
  simp_rw [coe_numeratorExponent he hj, Finset.sum_add_distrib, he.1, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

end Exponents

/-! ### Monomials in the coordinates -/

/-- The product of the coordinates indexed by `S`. -/
private def coordProd (S : Finset κ) : _root_.SymmetricAlgebra R M := ∏ i ∈ S, ι R M (b i)

private lemma coordProd_mem (S : Finset κ) : coordProd b S ∈ 𝒜 S.card := by
  simpa [coordProd] using SetLike.prod_mem_graded 𝒜 (fun _ ↦ 1) (fun i ↦ ι R M (b i)) (F := S)
    fun i _ ↦ ι_mem_homogeneousSubmodule R M (b i)

/-- The indicator exponent of `S`. -/
private def indicatorExponent (S : Finset κ) : κ →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

variable [DecidableEq κ] in
private lemma indicatorExponent_apply (S : Finset κ) (i : κ) :
    indicatorExponent S i = if i ∈ S then 1 else 0 := by
  simp [indicatorExponent, Finsupp.single_apply]

private lemma coordProd_eq_symmetricAlgebra (S : Finset κ) :
    coordProd b S = b.symmetricAlgebra (indicatorExponent S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact (equivMvPolynomial b).injective (by simp [coordProd, indicatorExponent,
      b.equivMvPolynomial_symmetricAlgebra_apply])
  | insert a S ha ih =>
    rw [coordProd, Finset.prod_insert ha, ← coordProd, ih]
    simp only [indicatorExponent, Finset.sum_insert ha, b.symmetricAlgebra_add]
    congr 1
    rw [Module.Basis.symmetricAlgebra, Module.Basis.map_apply, MvPolynomial.coe_basisMonomials]
    exact (_root_.SymmetricAlgebra.equivMvPolynomial_symm_X b a).symm

private lemma basicOpen_coordProd (S : Finset κ) :
    Proj.basicOpen 𝒜 (coordProd b S) = S.inf fun i ↦ Proj.basicOpen 𝒜 (ι R M (b i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty, coordProd, Finset.prod_empty]
    ext x
    simp only [Proj.basicOpen, ProjectiveSpectrum.basicOpen_one]
    trivial
  | insert a S ha ih =>
    rw [coordProd, Finset.prod_insert ha, ← coordProd, Proj.basicOpen_mul, ih, Finset.inf_insert]

/-! ### Laurent monomials as sections over the standard charts -/

section Chart

variable [Fintype κ] [DecidableEq κ] {m : ℤ}

private instance (S : Finset κ) : DecidablePred (· ∈ chartExponents m S) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

private lemma degree_numeratorExponent_eq_toNat {S : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) {j : ℕ} (hj : ∀ i ∈ S, 0 ≤ e i + j) :
    (numeratorExponent e S j).degree = ((j : ℤ) * S.card + m).toNat := by
  have := degree_numeratorExponent he hj
  omega

omit [Fintype κ] [DecidableEq κ] in
private lemma basicOpen_le_basicOpen_pow (S : Finset κ) (j : ℕ) :
    Proj.basicOpen 𝒜 (coordProd b S) ≤ Proj.basicOpen 𝒜 (coordProd b S ^ j) :=
  fun x hx hpow ↦ hx (x.isPrime.mem_of_pow_mem j hpow)

variable (m) in
/-- The section `c xᵉ` of `𝒪(m)` over the standard open `D₊(∏_{i ∈ S} xᵢ)`, for a Laurent
exponent `e` of degree `m` that is negative only in coordinates of `S`, written as the fraction
`c x^{e + j 1_S} / (∏_{i ∈ S} xᵢ)ʲ`. -/
private def chartSection (S : Finset κ) {e : κ → ℤ} (he : e ∈ chartExponents m S) (j : ℕ)
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (c : R) :
    Γ(Proj.twistingSheaf 𝒜 m, Proj.basicOpen 𝒜 (coordProd b S)) :=
  Proj.twistingSheaf.const (i := j * S.card) (j := ((j : ℤ) * S.card + m).toNat)
    (by have := degree_numeratorExponent he hj; push_cast; omega)
    (c • b.symmetricAlgebra (numeratorExponent e S j)) (coordProd b S ^ j)
    (Submodule.smul_mem _ c
      (degree_numeratorExponent_eq_toNat he hj ▸ b.symmetricAlgebra_mem_homogeneousSubmodule _))
    (by simpa [mul_comm] using SetLike.pow_mem_graded j (coordProd_mem b S))
    _ (basicOpen_le_basicOpen_pow b S j)

/-- The two ways of writing the Laurent monomial `xᵉ` as a fraction with denominators the powers of
coordinate products agree after cross-multiplication. -/
private lemma coordProd_pow_mul_symmetricAlgebra {S S' : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) (he' : e ∈ chartExponents m S') {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S', 0 ≤ e i + j') (c : R) :
    coordProd b S' ^ j' * (c • b.symmetricAlgebra (numeratorExponent e S j)) =
      coordProd b S ^ j * (c • b.symmetricAlgebra (numeratorExponent e S' j')) := by
  rw [coordProd_eq_symmetricAlgebra, coordProd_eq_symmetricAlgebra, b.symmetricAlgebra_pow,
    b.symmetricAlgebra_pow, mul_smul_comm, mul_smul_comm, ← b.symmetricAlgebra_add,
    ← b.symmetricAlgebra_add]
  congr 2
  ext i
  refine Nat.cast_injective (R := ℤ) ?_
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_mul, indicatorExponent_apply, coe_numeratorExponent he hj,
    coe_numeratorExponent he' hj']
  split_ifs <;> push_cast <;> ring

/-- The restriction of the Laurent monomial `c xᵉ` from one standard open to a smaller one is
the same Laurent monomial, whatever denominators are used to write it. -/
private lemma res_chartSection {S S' : Finset κ}
    (h : Proj.basicOpen 𝒜 (coordProd b S') ≤ Proj.basicOpen 𝒜 (coordProd b S)) {e : κ → ℤ}
    (he : e ∈ chartExponents m S) (he' : e ∈ chartExponents m S') {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S', 0 ≤ e i + j') (c : R) :
    (Proj.twistingSheaf 𝒜 m).presheaf.map (homOfLE h).op (chartSection b m S he j hj c) =
      chartSection b m S' he' j' hj' c := by
  rw [chartSection, Proj.twistingSheaf.res_const]
  exact Proj.twistingSheaf.const_ext (coordProd_pow_mul_symmetricAlgebra b he he' hj hj' c)

/-- The Laurent monomial `c xᵉ` does not depend on the power of the coordinate product used as
its denominator. -/
private lemma chartSection_congr {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S) {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S, 0 ≤ e i + j') (c : R) :
    chartSection b m S he j hj c = chartSection b m S he j' hj' c :=
  Proj.twistingSheaf.const_ext (coordProd_pow_mul_symmetricAlgebra b he he hj hj' c)

omit [DecidableEq κ] in
/-- A denominator exponent making every entry of `e + j 1_S` nonnegative. -/
private def exponentBound (e : κ → ℤ) : ℕ := ∑ i, (-e i).toNat

omit [DecidableEq κ] in
private lemma le_exponentBound (e : κ → ℤ) (i : κ) : 0 ≤ e i + exponentBound e := by
  have : (-e i).toNat ≤ exponentBound e :=
    Finset.single_le_sum (f := fun i ↦ (-e i).toNat) (by simp) (Finset.mem_univ i)
  omega

variable (m) in
/-- The additive map `c ↦ c xᵉ` into the sections of `𝒪(m)` over `D₊(∏_{i ∈ S} xᵢ)`, which
vanishes unless `e` is a Laurent exponent of degree `m` negative only in coordinates of `S`. -/
private def chartSectionHom (S : Finset κ) (e : κ → ℤ) :
    R →+ Γ(Proj.twistingSheaf 𝒜 m, Proj.basicOpen 𝒜 (coordProd b S)) :=
  if he : e ∈ chartExponents m S then
    { toFun := chartSection b m S he (exponentBound e) fun i _ ↦ le_exponentBound e i
      map_zero' := Proj.twistingSheaf.ext fun x ↦ by simp [chartSection]
      map_add' c c' := by
        rw [chartSection, chartSection, chartSection, Proj.twistingSheaf.const_add]
        exact Proj.twistingSheaf.const_ext (by rw [add_smul]) }
  else 0

private lemma chartSectionHom_apply {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S) {j : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (c : R) :
    chartSectionHom b m S e c = chartSection b m S he j hj c := by
  simp only [chartSectionHom, he, ↓reduceDIte, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact chartSection_congr b he _ hj c

variable (m) in
/-- The additive map from the Laurent polynomials of degree `m` whose monomials are negative only
in coordinates of `S` to the sections of `𝒪(m)` over `D₊(∏_{i ∈ S} xᵢ)`. -/
private def chartSectionsHom (S : Finset κ) :
    Finsupp.supported R R (chartExponents m S) →+
      Γ(Proj.twistingSheaf 𝒜 m, Proj.basicOpen 𝒜 (coordProd b S)) :=
  (Finsupp.liftAddHom (chartSectionHom b m S)).comp
    (Finsupp.supported R R (chartExponents m S)).subtype.toAddMonoidHom

private lemma chartSectionsHom_eq_sum {S : Finset κ}
    (f : Finsupp.supported R R (chartExponents m S)) :
    chartSectionsHom b m S f = ∑ e ∈ f.1.support, chartSectionHom b m S e (f.1 e) :=
  Finsupp.liftAddHom_apply _ _

private lemma chartSectionsHom_eq_const {S : Finset κ}
    (f : Finsupp.supported R R (chartExponents m S))
    {j : ℕ} (hj : ∀ e ∈ f.1.support, ∀ i ∈ S, 0 ≤ e i + j) (hjm : 0 ≤ (j : ℤ) * S.card + m) :
    chartSectionsHom b m S f =
      Proj.twistingSheaf.const (i := j * S.card) (j := ((j : ℤ) * S.card + m).toNat)
        (by push_cast; omega)
        (∑ e ∈ f.1.support, f.1 e • b.symmetricAlgebra (numeratorExponent e S j))
        (coordProd b S ^ j)
        (Submodule.sum_mem _ fun e he ↦ Submodule.smul_mem _ _
          (degree_numeratorExponent_eq_toNat ((Finsupp.mem_supported R f.1).1 f.2 he)
            (hj e he) ▸ b.symmetricAlgebra_mem_homogeneousSubmodule _))
        (by simpa [mul_comm] using SetLike.pow_mem_graded j (coordProd_mem b S)) _
        (basicOpen_le_basicOpen_pow b S j) := by
  refine Proj.twistingSheaf.ext fun x ↦ ?_
  rw [chartSectionsHom_eq_sum]
  refine (Proj.twistingSheaf.sum_apply _ _ x).trans <| (Finset.sum_congr rfl fun e he ↦ ?_).trans <|
    (Localization.mk_sum _ _ _).symm.trans (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).symm
  rw [chartSectionHom_apply b ((Finsupp.mem_supported R f.1).1 f.2 he) (hj e he), chartSection]
  exact Proj.twistingSheaf.const_apply _ _ _ _ _ _ x

/-- On a nonempty chart, distinct Laurent monomials give linearly independent sections: the
coordinates are nonzerodivisors, so clearing denominators loses nothing. -/
private lemma chartSectionsHom_injective {S : Finset κ} (hS : S.Nonempty) :
    Function.Injective (chartSectionsHom b m S) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  have hcard : 0 < S.card := Finset.card_pos.2 hS
  set j := (∑ e ∈ f.1.support, exponentBound e) + m.natAbs with hjdef
  have hj : ∀ e ∈ f.1.support, ∀ i ∈ S, 0 ≤ e i + j := fun e he i _ ↦ by
    have h1 := le_exponentBound e i
    have h2 : exponentBound e ≤ ∑ e ∈ f.1.support, exponentBound e :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) he
    omega
  have hjm : 0 ≤ (j : ℤ) * S.card + m := by
    have h1 : (j : ℤ) ≤ j * S.card := by exact_mod_cast Nat.le_mul_of_pos_right j hcard
    omega
  rw [chartSectionsHom_eq_const b f hj hjm, Proj.twistingSheaf.const_eq_zero_iff
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hcard (coordProd_mem b S))] at hf
  obtain ⟨N, hN⟩ := hf
  -- clear the denominators: the numerators form a polynomial killed by a power of `∏_{i ∈ S} xᵢ`
  have hP := congrArg (equivMvPolynomial b) hN
  simp only [map_mul, map_pow, map_sum, map_smul, map_zero, coordProd_eq_symmetricAlgebra,
    b.equivMvPolynomial_symmetricAlgebra_apply, MvPolynomial.monomial_pow, one_pow, Finset.mul_sum,
    mul_smul_comm, MvPolynomial.monomial_mul_monomial, mul_one] at hP
  have hmem : ∀ e ∈ f.1.support, e ∈ chartExponents m S :=
    fun e he ↦ (Finsupp.mem_supported R f.1).1 f.2 he
  refine Subtype.ext (Finsupp.ext fun e₀ ↦ ?_)
  by_cases he₀ : e₀ ∈ f.1.support
  · have hc := congrArg (fun q : MvPolynomial κ R ↦
      q.coeff (N • indicatorExponent S + numeratorExponent e₀ S j)) hP
    rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, Finset.sum_eq_single e₀] at hc
    · simpa [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial] using hc
    · intro e he hne
      have hD : N • indicatorExponent S + numeratorExponent e S j ≠
          N • indicatorExponent S + numeratorExponent e₀ S j := fun h ↦ hne <| funext fun i ↦ by
        have := congrArg (fun d : κ →₀ ℕ ↦ (d i : ℤ)) h
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Nat.cast_add, coe_numeratorExponent (hmem e he) (hj e he),
          coe_numeratorExponent (hmem e₀ he₀) (hj e₀ he₀)] at this
        omega
      simp [MvPolynomial.coeff_monomial, hD]
    · exact fun h ↦ (h he₀).elim
  · simpa using he₀

/-- The Laurent exponent `d - k 1_S` of the monomial `xᵈ / (∏_{i ∈ S} xᵢ)ᵏ`. -/
private def shiftExponent (S : Finset κ) (k : ℕ) (d : κ →₀ ℕ) : κ → ℤ :=
  fun i ↦ d i - if i ∈ S then (k : ℤ) else 0

private lemma shiftExponent_mem_chartExponents {S : Finset κ} {k : ℕ} {d : κ →₀ ℕ}
    (hd : (d.degree : ℤ) = (k * S.card : ℕ) + m) : shiftExponent S k d ∈ chartExponents m S := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [Finsupp.degree_eq_sum, Nat.cast_sum] at hd
    simp only [shiftExponent, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, hd]
    push_cast
    ring
  · by_contra hiS
    have := mem_negSupport.1 hi
    simp only [shiftExponent, hiS, ite_false, sub_zero] at this
    omega

omit [Fintype κ] in
private lemma add_shiftExponent_nonneg (S : Finset κ) (k : ℕ) (d : κ →₀ ℕ) :
    ∀ i ∈ S, 0 ≤ shiftExponent S k d i + k := fun i hi ↦ by
  simp [shiftExponent, hi]

private lemma numeratorExponent_shiftExponent {S : Finset κ} {k : ℕ} {d : κ →₀ ℕ}
    (hd : (d.degree : ℤ) = (k * S.card : ℕ) + m) :
    numeratorExponent (shiftExponent S k d) S k = d := by
  ext i
  refine Nat.cast_injective (R := ℤ) ?_
  rw [coe_numeratorExponent (shiftExponent_mem_chartExponents hd)
    (add_shiftExponent_nonneg S k d)]
  simp only [shiftExponent]
  split_ifs <;> ring

/-- On a nonempty chart, every section of `𝒪(m)` is a Laurent polynomial. -/
private lemma chartSectionsHom_surjective {S : Finset κ} (hS : S.Nonempty) :
    Function.Surjective (chartSectionsHom b m S) := by
  intro s
  obtain ⟨k, J, hJ, r, hr, rfl⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen
    (coordProd_mem b S) (Finset.card_pos.2 hS) s
  set p := equivMvPolynomial b r with hpdef
  have hp : p.IsHomogeneous J :=
    (_root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b J r).2 hr
  have hdeg (d : κ →₀ ℕ) (hd : d ∈ p.support) : (d.degree : ℤ) = (k * S.card : ℕ) + m := by
    rw [← hJ, Finsupp.degree_eq_weight_one]
    exact_mod_cast hp (MvPolynomial.mem_support_iff.1 hd)
  -- the section `r / (∏_{i ∈ S} xᵢ)ᵏ` is the sum of the Laurent monomials `xᵈ / (∏_{i ∈ S} xᵢ)ᵏ`
  let f : (κ → ℤ) →₀ R := ∑ d ∈ p.support, Finsupp.single (shiftExponent S k d) (p.coeff d)
  have hf : f ∈ Finsupp.supported R R (chartExponents m S) :=
    Submodule.sum_mem _ fun d hd ↦
      Finsupp.single_mem_supported R _ (shiftExponent_mem_chartExponents (hdeg d hd))
  refine ⟨⟨f, hf⟩, ?_⟩
  have h : chartSectionsHom b m S ⟨f, hf⟩ =
      ∑ d ∈ p.support, chartSectionHom b m S (shiftExponent S k d) (p.coeff d) := by
    simp [chartSectionsHom, f, map_sum]
  have hr' : r = ∑ d ∈ p.support, p.coeff d • b.symmetricAlgebra d := by
    refine (equivMvPolynomial b).injective ?_
    rw [← hpdef]
    simp only [map_sum, map_smul, b.equivMvPolynomial_symmetricAlgebra_apply,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact MvPolynomial.as_sum p
  refine Proj.twistingSheaf.ext fun x ↦ ?_
  rw [h]
  refine (Proj.twistingSheaf.sum_apply _ _ x).trans <| (Finset.sum_congr rfl fun d hd ↦ ?_).trans <|
    (Localization.mk_sum _ _ _).symm.trans <| (congrArg (Localization.mk · _) hr'.symm).trans
      (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).symm
  rw [chartSectionHom_apply b (shiftExponent_mem_chartExponents (hdeg d hd))
    (add_shiftExponent_nonneg S k d), chartSection]
  refine (Proj.twistingSheaf.const_apply _ _ _ _ _ _ x).trans ?_
  rw [numeratorExponent_shiftExponent (hdeg d hd)]

end Chart

/-! ### The Čech complex of the standard cover -/

section Cech

open Limits Opposite OrderDual TauCeti.CategoryTheory

variable [Fintype κ] [DecidableEq κ] (m : ℤ)

/-- The standard opens `D₊(∏_{i ∈ S} xᵢ)`, as a functor on the finite sets of coordinates ordered
by reverse inclusion; the empty set goes to the whole space. -/
private def chartFunctor : (Finset κ)ᵒᵈ ⥤ (Proj 𝒜).Opens :=
  Monotone.functor (f := fun S ↦ Proj.basicOpen 𝒜 (coordProd b (ofDual S))) fun S S' h ↦ by
    simp only [basicOpen_coordProd]
    exact Finset.inf_mono h

/-- The Laurent polynomials of degree `m` whose monomials are negative only in coordinates of `S`,
as a presheaf on the finite sets of coordinates ordered by reverse inclusion. -/
private def laurentPresheaf : ((Finset κ)ᵒᵈ)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj S := AddCommGrpCat.of (Finsupp.supported R R (chartExponents m (ofDual S.unop)))
  map f := AddCommGrpCat.ofHom (Submodule.inclusion
    (Finsupp.supported_mono (chartExponents_mono (leOfHom f.unop)))).toAddMonoidHom

/-- The sections of `𝒪(m)` as a presheaf of abelian groups. -/
private abbrev sectionsPresheaf : (Proj 𝒜).Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).obj (Proj.twistingSheaf 𝒜 m)).obj

/-- Laurent polynomials as sections of `𝒪(m)` over the standard opens. -/
private def laurentToSections :
    laurentPresheaf (R := R) (κ := κ) m ⟶
      (chartFunctor b).op ⋙ sectionsPresheaf (R := R) (M := M) m where
  app S := AddCommGrpCat.ofHom (chartSectionsHom b m (ofDual S.unop))
  naturality S S' f := by
    ext ⟨g, hg⟩
    have hmem : ∀ e ∈ g.support, e ∈ chartExponents m (ofDual S.unop) :=
      fun e he ↦ (Finsupp.mem_supported R g).1 hg he
    -- the maps of `laurentPresheaf` are inclusions, which do not change the Laurent polynomial
    let φ := ((sectionsPresheaf (R := R) (M := M) m).map ((chartFunctor b).map f.unop).op).hom
    refine (chartSectionsHom_eq_sum b (S := ofDual S'.unop) ⟨g, _⟩).trans <|
      (Finset.sum_congr rfl fun e he ↦ ?_).trans <| (map_sum φ _ _).symm.trans
        (congrArg φ (chartSectionsHom_eq_sum b ⟨g, hg⟩).symm)
    have he' : e ∈ chartExponents m (ofDual S'.unop) :=
      chartExponents_mono (leOfHom f.unop) (hmem e he)
    rw [chartSectionHom_apply b (hmem e he) (fun i _ ↦ le_exponentBound e i),
      chartSectionHom_apply b he' (fun i _ ↦ le_exponentBound e i)]
    exact (res_chartSection b (leOfHom ((chartFunctor b).map f.unop)) (hmem e he) he' _ _ _).symm

omit [Fintype κ] [DecidableEq κ] in
private lemma chartFunctor_obj (S : (Finset κ)ᵒᵈ) :
    (chartFunctor b).obj S = Proj.basicOpen 𝒜 (coordProd b (ofDual S)) :=
  rfl

omit [Fintype κ] [DecidableEq κ] in
private lemma chartFunctor_obj_singleton (i : κ) :
    (chartFunctor b).obj (toDual {i}) = Proj.basicOpen 𝒜 (ι R M (b i)) := by
  simp [chartFunctor_obj, coordProd]

omit [Fintype κ] in
/-- The product of the charts of the coordinates `a 0, …, a n` in the category of finite sets of
coordinates is the set of these coordinates, by
`CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_image_inf`. -/
private lemma ofDual_pi_toDual_singleton {n : ℕ} (a : Fin (n + 1) → κ) :
    ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) = Finset.univ.image a := by
  rw [CompleteLattice.finite_product_eq_finset_image_inf (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
    a, Finset.ofDual_inf]
  exact Finset.sup_singleton_eq_self _

omit [Fintype κ] [DecidableEq κ] in
private lemma isAffineOpen_inf_chartFunctor_obj_singleton (s : Finset κ) (hs : s.Nonempty) :
    IsAffineOpen (s.inf fun i ↦ (chartFunctor b).obj (toDual {i})) := by
  have : (s.inf fun i ↦ (chartFunctor b).obj (toDual {i})) = Proj.basicOpen 𝒜 (coordProd b s) := by
    rw [basicOpen_coordProd]
    exact Finset.inf_congr rfl fun i _ ↦ chartFunctor_obj_singleton b i
  rw [this]
  exact Proj.isAffineOpen_basicOpen 𝒜 _ (coordProd_mem b s) (Finset.card_pos.2 hs)

omit [Fintype κ] [DecidableEq κ] in
private lemma iSup_chartFunctor_obj_singleton : ⨆ i, (chartFunctor b).obj (toDual {i}) = ⊤ := by
  simp_rw [chartFunctor_obj_singleton]
  exact iSup_basicOpen_ι_eq_top R M b b.span_eq

private lemma isIso_laurentToSections_app {S : (Finset κ)ᵒᵈ} (hS : (ofDual S).Nonempty) :
    IsIso ((laurentToSections b m).app (op S)) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨chartSectionsHom_injective b hS, chartSectionsHom_surjective b hS⟩

private lemma isIso_cechComplexFunctor_map_laurentToSections :
    IsIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m)) := by
  have (n : ℕ) : IsIso (((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m)).f n) := by
    have (a : Fin (n + 1) → κ) : IsIso ((laurentToSections b m).app
        (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)))) :=
      isIso_laurentToSections_app b m
        ⟨a 0, Finset.singleton_subset_iff.1
          (leOfHom (Pi.π (fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) 0))⟩
    rw [cechComplexFunctor_map_f]
    exact Pi.map_isIso _
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### Splitting Laurent polynomials by negative support -/

/-- The projection onto the Laurent monomials with negative support exactly `T`. -/
private def negSupportProj (T : Finset κ) :
    laurentPresheaf (R := R) (κ := κ) m ⟶ laurentPresheaf (R := R) (κ := κ) m where
  app _ := AddCommGrpCat.ofHom
    (LinearMap.toAddMonoidHom (Finsupp.filterSupported (negSupport · = T) fun _ he _ ↦ he))
  -- restriction is an inclusion, so both composites filter the same Laurent polynomial
  naturality _ _ f := AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom
    ((Finsupp.filterSupported_comp_inclusion (negSupport · = T)
      (chartExponents_mono (leOfHom f.unop)) fun _ he _ ↦ he).trans
      (Finsupp.inclusion_comp_filterSupported (negSupport · = T) (fun _ he _ ↦ he)
        (chartExponents_mono (leOfHom f.unop))).symm))

omit [DecidableEq κ] in
private lemma sum_filterSupported_negSupport [DecidableEq κ] {s : Set (κ → ℤ)}
    (f : Finsupp.supported R R s) :
    ∑ T : Finset κ, Finsupp.filterSupported (negSupport · = T) (fun _ he _ ↦ he) f = f := by
  refine Subtype.ext (Finsupp.ext fun e ↦ ?_)
  simp [Finsupp.finsetSum_apply, Finsupp.filter_apply]

private lemma sum_negSupportProj :
    ∑ T : Finset κ, negSupportProj (R := R) (κ := κ) m T = 𝟙 _ := by
  refine NatTrans.ext (funext fun S ↦ ?_)
  rw [NatTrans.app_sum, NatTrans.id_app]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f ↦ ?_)
  -- a morphism of abelian groups acts through `AddCommGrpCat.homAddEquiv`, which is additive
  change AddCommGrpCat.homAddEquiv (∑ T : Finset κ, (negSupportProj (R := R) m T).app S) f = f
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact sum_filterSupported_negSupport f

/-- Restriction of Laurent polynomials to the intersection with the chart of `c`. -/
private def restrictToChart (c : κ) :
    laurentPresheaf (R := R) (κ := κ) m ⟶
      (prod.functor.obj (toDual {c})).op ⋙ laurentPresheaf (R := R) (κ := κ) m where
  app S := (laurentPresheaf m).map (prod.snd : toDual {c} ⨯ S.unop ⟶ S.unop).op
  naturality _ _ _ := rfl

/-- A Laurent monomial with negative support `T` which is negative only in coordinates of
`{c} ∪ S`, for a coordinate `c ∉ T`, is negative only in coordinates of `S`. -/
private lemma mem_chartExponents_of_subset_union {c : κ} {T : Finset κ} (hc : c ∉ T)
    {S S' : Finset κ} (h : S' ⊆ {c} ∪ S) :
    ∀ e ∈ chartExponents m S', negSupport e = T → e ∈ chartExponents m S :=
  fun e he heT ↦ ⟨he.1, fun i hi ↦ by
    have hi' := Finset.mem_union.1 (h (he.2 hi))
    rw [Finset.mem_singleton] at hi'
    exact hi'.resolve_left fun h ↦ hc (h ▸ heT ▸ hi)⟩

/-- On the monomials with negative support `T`, a Laurent polynomial on the intersection with the
chart of a coordinate `c ∉ T` is already a Laurent polynomial on the original chart. -/
private def extendFromChart {c : κ} {T : Finset κ} (hc : c ∉ T) :
    (prod.functor.obj (toDual {c})).op ⋙ laurentPresheaf (R := R) (κ := κ) m ⟶
      laurentPresheaf (R := R) (κ := κ) m where
  -- a binary product of finite sets of coordinates is their union
  app S := AddCommGrpCat.ofHom (LinearMap.toAddMonoidHom (Finsupp.filterSupported (negSupport · = T)
    (mem_chartExponents_of_subset_union m hc (CompleteLattice.prod_eq_inf (toDual {c}) S.unop).ge)))
  -- restriction is an inclusion, so both composites filter the same Laurent polynomial
  naturality X Y f := AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom
    ((Finsupp.filterSupported_comp_inclusion (negSupport · = T)
      (chartExponents_mono (leOfHom ((prod.functor.obj (toDual ({c} : Finset κ))).map f.unop)))
      (mem_chartExponents_of_subset_union m hc
        (CompleteLattice.prod_eq_inf (toDual {c}) Y.unop).ge)).trans
      (Finsupp.inclusion_comp_filterSupported (negSupport · = T)
        (mem_chartExponents_of_subset_union m hc
          (CompleteLattice.prod_eq_inf (toDual {c}) X.unop).ge)
        (chartExponents_mono (leOfHom f.unop))).symm))

private lemma restrictToChart_comp_extendFromChart {c : κ} {T : Finset κ} (hc : c ∉ T) :
    restrictToChart (R := R) (κ := κ) m c ≫ extendFromChart (R := R) m hc =
      negSupportProj (R := R) m T :=
  -- restriction is an inclusion and both sides filter the same Laurent polynomial
  NatTrans.ext (funext fun S ↦ AddCommGrpCat.hom_ext (congrArg LinearMap.toAddMonoidHom
    (Finsupp.filterSupported_comp_inclusion (negSupport · = T)
      (chartExponents_mono (leOfHom (prod.snd : toDual {c} ⨯ S.unop ⟶ S.unop)))
      (mem_chartExponents_of_subset_union m hc
        (CompleteLattice.prod_eq_inf (toDual {c}) S.unop).ge))))

/-! ### Vanishing of the Čech cohomology -/

/-- The Čech complex of Laurent polynomials for the cover of the standard charts. -/
private abbrev laurentCech : CochainComplex AddCommGrpCat.{u} ℕ :=
  (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).obj
    (laurentPresheaf (R := R) (κ := κ) m)

/-- The monomials with negative support `T ∌ c` contribute nothing to Čech cohomology in positive
degrees: they come from the chart of `c`, on which the cover has a member equal to the whole
chart. -/
private lemma homologyMap_negSupportProj_of_notMem {c : κ} {T : Finset κ} (hc : c ∉ T) (q : ℕ) :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m T)) (q + 1) = 0 := by
  have hex := ((quasiIso_cechAugmentation_iff _ isTerminalTop _).1
    (quasiIso_cechAugmentation_prod_of_hom (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
      isTerminalTop (laurentPresheaf (R := R) (κ := κ) m) (toDual {c}) (𝟙 _))).2 q
  rw [← restrictToChart_comp_extendFromChart m hc, Functor.map_comp,
    HomologicalComplex.homologyMap_comp, hex.isZero_homology.eq_of_tgt
      (HomologicalComplex.homologyMap _ _) 0, zero_comp]

/-- The monomials with all exponents negative contribute nothing to Čech cohomology in degree `q`
when `q + 1` coordinates do not suffice to cover all coordinates, or when there are no such
monomials of degree `m`. -/
private lemma homologyMap_negSupportProj_univ {q : ℕ}
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m Finset.univ)) q = 0 := by
  refine HomologicalComplex.homologyMap_eq_zero_of_f_eq_zero _ _ ?_
  rw [cechComplexFunctor_map_f]
  refine Pi.hom_ext _ _ fun a ↦ (Pi.map_π _ a).trans (Eq.trans ?_ zero_comp.symm)
  -- no Laurent monomial over a product of `q + 1` charts has all exponents negative
  have hno : ∀ e ∈ chartExponents m (ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))),
      negSupport e ≠ Finset.univ := by
    rintro e ⟨hsum, hneg⟩ huniv
    rcases h with h | h
    · have := (Finset.card_le_card (hneg.trans (ofDual_pi_toDual_singleton (n := q) a).le)).trans
        Finset.card_image_le
      rw [huniv, Finset.card_univ, Finset.card_fin] at this
      omega
    · have hlt : ∀ i, e i ≤ -1 := fun i ↦ by
        have := mem_negSupport.1 (huniv ▸ Finset.mem_univ i : i ∈ negSupport e)
        omega
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hlt i
      rw [hsum, Finset.sum_const, Finset.card_univ] at this
      simp only [nsmul_eq_mul, mul_neg, mul_one] at this
      omega
  have hzero : (negSupportProj (R := R) m Finset.univ).app
      (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))) = 0 := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f ↦ Subtype.ext ?_)
    -- the projection is the filter on the underlying Laurent polynomial
    refine (Finsupp.filterSupported_apply _ _ f).trans ?_
    exact (Finsupp.filter_eq_zero_iff _ _).2 fun e he ↦ Finsupp.notMem_support_iff.1 fun hf ↦
      hno e ((Finsupp.mem_supported R f.1).1 f.2 hf) he
  rw [hzero]
  exact comp_zero

private lemma isZero_homology_laurentCech {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    IsZero ((laurentCech (R := R) (κ := κ) m).homology q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add] at h ⊢
  have hsum : ∑ T : Finset κ, (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (negSupportProj (R := R) m T) = 𝟙 (laurentCech (R := R) (κ := κ) m) := by
    rw [← Functor.map_sum, sum_negSupportProj, CategoryTheory.Functor.map_id]
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id, ← hsum,
    ← HomologicalComplex.homologyFunctor_map, Functor.map_sum]
  refine Finset.sum_eq_zero fun T _ ↦ ?_
  rw [HomologicalComplex.homologyFunctor_map]
  by_cases hT : T = Finset.univ
  · subst hT
    exact homologyMap_negSupportProj_univ m h
  · obtain ⟨c, hc⟩ : ∃ c, c ∉ T := by
      by_contra! hall
      exact hT (Finset.eq_univ_iff_forall.2 hall)
    exact homologyMap_negSupportProj_of_notMem m hc q

end Cech

/-! ### Laurent monomials with all exponents negative -/

/-- The exponents `e : κ → ℤ` of total degree `m` whose entries are all negative. When `κ` has at
least two elements, the top cohomology of `𝒪(m)` on projective space with homogeneous coordinates
indexed by `κ` is isomorphic to the free module on the Laurent monomials `xᵉ` with these
exponents. -/
def negativeExponents (κ : Type*) [Fintype κ] (m : ℤ) : Set (κ → ℤ) :=
  {e | ∑ i, e i = m ∧ ∀ i, e i < 0}

@[simp]
theorem mem_negativeExponents {κ : Type*} [Fintype κ] {m : ℤ} {e : κ → ℤ} :
    e ∈ negativeExponents κ m ↔ ∑ i, e i = m ∧ ∀ i, e i < 0 :=
  Iff.rfl

/-- There are finitely many exponents of a given degree with all entries negative, since each
entry lies between the degree and `-1`. -/
instance (κ : Type*) [Fintype κ] (m : ℤ) : Finite (negativeExponents κ m) := by
  refine Set.Finite.to_subtype ((Set.Finite.pi (t := fun _ : κ ↦ Set.Icc m (-1))
    fun _ ↦ Set.finite_Icc _ _).subset ?_)
  classical
  rintro e ⟨hsum, hneg⟩ i -
  refine ⟨?_, by have := hneg i; omega⟩
  have : ∑ j ∈ Finset.univ.erase i, e j ≤ 0 := Finset.sum_nonpos fun j _ ↦ (hneg j).le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  omega

section TopCech

open OrderDual in
open scoped Classical in
/-- The product of the charts of the coordinates of a tuple, which is the set of its entries, is
the set of all coordinates exactly when the tuple is surjective. -/
private lemma ofDual_pi_eq_univ_iff [Fintype κ] {q : ℕ} (a : Fin (q + 1) → κ) :
    ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) = Finset.univ ↔ Function.Surjective a := by
  rw [ofDual_pi_toDual_singleton]
  refine ⟨fun h x ↦ ?_, Finset.image_univ_of_surjective⟩
  have hx : x ∈ Finset.univ.image a := h ▸ Finset.mem_univ x
  simpa using hx

open Limits Opposite OrderDual TauCeti.CategoryTheory

variable [Fintype κ] [DecidableEq κ] (m : ℤ)

omit [DecidableEq κ] in
private lemma negativeExponents_subset : negativeExponents κ m ⊆ chartExponents m Finset.univ :=
  fun _ he ↦ ⟨he.1, Finset.subset_univ _⟩

omit [DecidableEq κ] in
/-- Over a chart missing a coordinate, a Laurent monomial has a nonnegative exponent. -/
private lemma notMem_negativeExponents {S : Finset κ} (hS : S ≠ Finset.univ) {e : κ → ℤ}
    (he : e ∈ chartExponents m S) : e ∉ negativeExponents κ m := by
  rintro ⟨-, hneg⟩
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
    by_contra! h
    exact hS (Finset.eq_univ_iff_forall.2 h)
  exact hi (he.2 (mem_negSupport.2 (hneg i)))

/-- The coefficients of a Laurent polynomial at the monomials of degree `m` with all exponents
negative. -/
private abbrev negPart : ((κ → ℤ) →₀ R) →ₗ[R] negativeExponents κ m →₀ R :=
  Finsupp.lsubtypeDomain _

/-- The Laurent polynomial with given coefficients at the monomials of degree `m` with all
exponents negative. -/
private abbrev negEmb : (negativeExponents κ m →₀ R) →ₗ[R] (κ → ℤ) →₀ R :=
  Finsupp.lmapDomain R R Subtype.val

omit [DecidableEq κ] in
private lemma negPart_negEmb (f : negativeExponents κ m →₀ R) : negPart m (negEmb m f) = f := by
  ext x
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective f x

omit [DecidableEq κ] in
private lemma negEmb_mem_supported (f : negativeExponents κ m →₀ R) :
    negEmb m f ∈ Finsupp.supported R R (chartExponents m Finset.univ) := by
  refine (Finsupp.mem_supported R _).2 fun e he ↦ ?_
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support he)
  exact negativeExponents_subset m x.2

omit [DecidableEq κ] in
private lemma negPart_eq_zero {S : Finset κ} (hS : S ≠ Finset.univ) {w : (κ → ℤ) →₀ R}
    (hw : w ∈ Finsupp.supported R R (chartExponents m S)) : negPart m w = 0 := by
  ext ⟨e, he⟩
  rw [Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact Finsupp.notMem_support_iff.1 fun h ↦
    notMem_negativeExponents m hS ((Finsupp.mem_supported R w).1 hw h) he

/-- On Laurent polynomials, restricting to the monomials with all exponents negative and back is
the projection onto the monomials with negative support `univ`. -/
private lemma negEmb_negPart {S : Finset κ} {w : (κ → ℤ) →₀ R}
    (hw : w ∈ Finsupp.supported R R (chartExponents m S)) :
    negEmb m (negPart m w) = Finsupp.filter (negSupport · = Finset.univ) w := by
  ext e
  by_cases he : e ∈ negativeExponents κ m
  · rw [Finsupp.filter_apply_pos (fun x ↦ negSupport x = Finset.univ) w
      (Finset.eq_univ_iff_forall.2 fun i ↦ mem_negSupport.2 (he.2 i))]
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _
      (⟨e, he⟩ : negativeExponents κ m)
  · rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_of_notMem_range _ _ fun ⟨x, hx⟩ ↦ he (hx ▸ x.2)]
    by_cases h : negSupport e = Finset.univ
    · rw [Finsupp.filter_apply_pos (fun x ↦ negSupport x = Finset.univ) w h]
      exact (Finsupp.notMem_support_iff.1 fun hs ↦ he ⟨((Finsupp.mem_supported R w).1 hw hs).1,
        fun i ↦ mem_negSupport.1 (h ▸ Finset.mem_univ i)⟩).symm
    · rw [Finsupp.filter_apply_neg (fun x ↦ negSupport x = Finset.univ) w h]

/-- The factor indexed by `a` of a Čech cochain of Laurent polynomials. -/
private abbrev cechπ {q : ℕ} (a : Fin (q + 1) → κ) :
    (laurentCech (R := R) (κ := κ) m).X q ⟶
      (laurentPresheaf (R := R) m).obj (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))) :=
  Pi.π _ a

/-- The Čech differential of Laurent polynomials is the alternating sum of the factors indexed by
the faces, since restriction of Laurent polynomials is an inclusion. -/
private lemma val_cechπ_d (q : ℕ) (k : Fin (q + 2) → κ)
    (x : (laurentCech (R := R) (κ := κ) m).X q) :
    (cechπ m k ((laurentCech m).d q (q + 1) x)).1 =
      ∑ p : Fin (q + 2), (-1 : ℤ) ^ (p : ℕ) • (cechπ m (k ∘ p.succAbove) x).1 := by
  have h := ConcreteCategory.congr_hom (cechComplexFunctor_obj_d_comp_π
    (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)) (laurentPresheaf (R := R) m) q k) x
  refine (congrArg Subtype.val (h.trans ((DFunLike.congr_fun
    (map_sum AddCommGrpCat.homAddEquiv _ _) x).trans
      (AddMonoidHom.finsetSum_apply _ _ x)))).trans ?_
  exact (map_sum (Submodule.subtype _).toAddMonoidHom _ _).trans
    (Finset.sum_congr rfl fun p _ ↦ rfl)

end TopCech

/-! ### The top Čech cohomology of the Laurent polynomials -/

section TopDegree

open Limits Opposite OrderDual TauCeti.CategoryTheory

variable [Fintype κ] [DecidableEq κ] (m : ℤ) {n : ℕ} (e : κ ≃ Fin (n + 2))

omit [Fintype κ] [DecidableEq κ] in
include e in
/-- A tuple of fewer coordinates than there are coordinates misses one of them. -/
private lemma not_surjective_of_card (a : Fin (n + 1) → κ) : ¬Function.Surjective a := fun h ↦ by
  let : Fintype κ := Fintype.ofEquiv _ e.symm
  have := Fintype.card_le_of_surjective a h
  rw [Fintype.card_fin, Fintype.card_congr e, Fintype.card_fin] at this
  omega

/-- The factor indexed by `a` of the alternating cochain of degree `n + 1` with value `f` at the
ordering `e.symm` of the coordinates. -/
private def topCochainComponent (a : Fin (n + 2) → κ) :
    (negativeExponents κ m →₀ R) →+
      (laurentPresheaf (R := R) m).obj (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))) where
  toFun f := ⟨e.tupleSign ℤ a • negEmb m f, by
    by_cases ha : Function.Surjective a
    · -- the carrier of `laurentPresheaf` at a chart is a module of Laurent polynomials by
      -- definition, but its membership predicate is only visible after unfolding it
      change _ ∈ Finsupp.supported R R
        (chartExponents m (ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))))
      rw [(ofDual_pi_eq_univ_iff a).2 ha]
      exact Submodule.smul_of_tower_mem _ _ (negEmb_mem_supported m f)
    · rw [e.tupleSign_eq_zero_of_not_surjective ℤ ha, zero_smul]
      exact zero_mem _⟩
  -- rewriting under the subtype is blocked by the membership proof, so the equalities of
  -- underlying Laurent polynomials are stated explicitly
  map_zero' := Subtype.ext (show e.tupleSign ℤ a • negEmb m 0 = 0 by rw [map_zero, smul_zero])
  map_add' f g := Subtype.ext (show e.tupleSign ℤ a • negEmb m (f + g) =
    e.tupleSign ℤ a • negEmb m f + e.tupleSign ℤ a • negEmb m g by rw [map_add, smul_add])

/-- The alternating Čech cochain of degree `n + 1` taking the value `f` at the ordering `e.symm`
of the coordinates. -/
private def topCochain :
    AddCommGrpCat.of (negativeExponents κ m →₀ R) ⟶ (laurentCech (R := R) (κ := κ) m).X (n + 1) :=
  Pi.lift fun a ↦ AddCommGrpCat.ofHom (topCochainComponent m e a)

private lemma val_cechπ_topCochain (a : Fin (n + 2) → κ) (f : negativeExponents κ m →₀ R) :
    (cechπ m a (topCochain m e f)).1 = e.tupleSign ℤ a • negEmb m f := by
  exact congrArg Subtype.val (ConcreteCategory.congr_hom
    (Pi.lift_comp_π (fun a ↦ AddCommGrpCat.ofHom (topCochainComponent (R := R) m e a)) a) f)

/-- The coefficients at the monomials with all exponents negative of the factor of a Čech cochain
of degree `n + 1` indexed by the ordering `e.symm` of the coordinates. -/
private def topCoefficient :
    (laurentCech (R := R) (κ := κ) m).X (n + 1) ⟶ AddCommGrpCat.of (negativeExponents κ m →₀ R) :=
  cechπ m e.symm ≫ AddCommGrpCat.ofHom
    ((negPart m).toAddMonoidHom.comp (Finsupp.supported R R _).subtype.toAddMonoidHom)

private lemma topCoefficient_apply (x : (laurentCech (R := R) (κ := κ) m).X (n + 1)) :
    topCoefficient m e x = negPart m (cechπ m e.symm x).1 :=
  rfl

private lemma topCochain_comp_topCoefficient :
    topCochain (R := R) m e ≫ topCoefficient m e = 𝟙 _ := by
  refine AddCommGrpCat.ext fun f ↦ ?_
  rw [ConcreteCategory.comp_apply, topCoefficient_apply, val_cechπ_topCochain,
    Equiv.tupleSign_symm, one_smul, negPart_negEmb]
  rfl

/-- The alternating cochain is a cocycle, by the cocycle identity for signs of tuples. -/
private lemma topCochain_comp_d :
    topCochain (R := R) m e ≫ (laurentCech m).d (n + 1) (n + 2) = 0 := by
  refine Pi.hom_ext (f := fun k : Fin (n + 3) → κ ↦
    (laurentPresheaf (R := R) m).obj (op (∏ᶜ fun j ↦ (toDual {k j} : (Finset κ)ᵒᵈ)))) _ _ fun k ↦ ?_
  refine AddCommGrpCat.ext fun f ↦ Subtype.ext ?_
  -- composites of morphisms of abelian groups act by composition; this exposes the factor at `k`
  -- in the form used by `val_cechπ_d`
  change (cechπ m k ((laurentCech m).d (n + 1) (n + 2) (topCochain m e f))).1 =
    (cechπ m k 0).1
  rw [map_zero, val_cechπ_d]
  calc ∑ p : Fin (n + 3), (-1 : ℤ) ^ (p : ℕ) • (cechπ m (k ∘ p.succAbove) (topCochain m e f)).1
      = ∑ p : Fin (n + 3), ((-1 : ℤ) ^ (p : ℕ) * e.tupleSign ℤ (k ∘ p.succAbove)) • negEmb m f :=
        Finset.sum_congr rfl fun p _ ↦ by rw [val_cechπ_topCochain, smul_smul]
    _ = 0 := by rw [← Finset.sum_smul, e.sum_neg_one_pow_mul_tupleSign_comp_succAbove ℤ, zero_smul]

/-- Coboundaries have no coefficients at the monomials with all exponents negative: the faces of a
tuple of `n + 2` coordinates are tuples of `n + 1` coordinates, whose charts miss a coordinate. -/
private lemma d_comp_topCoefficient :
    (laurentCech (R := R) (κ := κ) m).d n (n + 1) ≫ topCoefficient m e = 0 := by
  refine AddCommGrpCat.ext fun x ↦ ?_
  rw [ConcreteCategory.comp_apply, topCoefficient_apply, val_cechπ_d, map_sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  rw [map_zsmul, negPart_eq_zero m (mt (ofDual_pi_eq_univ_iff _).1
    (not_surjective_of_card e _)) (cechπ m _ x).2, smul_zero]

/-! ### Cocycles of top degree are alternating -/

private lemma negPart_cechπ_eq_zero {c : Fin (n + 2) → κ} (hc : ¬Function.Surjective c)
    (z : (laurentCech (R := R) (κ := κ) m).X (n + 1)) : negPart m (cechπ m c z).1 = 0 :=
  negPart_eq_zero m (mt (ofDual_pi_eq_univ_iff c).1 hc) (cechπ m c z).2

private lemma sum_negPart_cechπ {z : (laurentCech (R := R) (κ := κ) m).X (n + 1)}
    (hz : (laurentCech m).d (n + 1) (n + 2) z = 0) (k : Fin (n + 3) → κ) :
    ∑ p : Fin (n + 3), (-1 : ℤ) ^ (p : ℕ) • negPart m (cechπ m (k ∘ p.succAbove) z).1 = 0 := by
  have h := congrArg (fun y ↦ negPart m (cechπ m k y).1) hz
  simp only [val_cechπ_d, map_sum, map_zsmul] at h
  exact h.trans (by rw [map_zero]; rfl)

include e in
/-- The coefficients of a cocycle of top degree at the monomials with all exponents negative
change sign when two adjacent entries of the tuple are swapped: this is the cocycle condition at
the tuple obtained by repeating the first of the two entries after the second. -/
private lemma negPart_cechπ_comp_swap {z : (laurentCech (R := R) (κ := κ) m).X (n + 1)}
    (hz : (laurentCech m).d (n + 1) (n + 2) z = 0) (c : Fin (n + 2) → κ) (i : Fin (n + 1)) :
    negPart m (cechπ m (c ∘ Equiv.swap i.castSucc i.succ) z).1 = -negPart m (cechπ m c z).1 := by
  let s : Fin (n + 3) → Fin (n + 2) := fun p ↦
    ⟨if (p : ℕ) = i + 2 then i else if (p : ℕ) < i + 2 then p else p - 1, by
      have := p.2; have := i.2; split_ifs <;> omega⟩
  let p₀ : Fin (n + 3) := ⟨i, by omega⟩
  let p₂ : Fin (n + 3) := ⟨i + 2, by omega⟩
  have h₀ : c ∘ s ∘ p₀.succAbove = c ∘ Equiv.swap i.castSucc i.succ := by
    funext j
    refine congrArg c (Fin.ext ?_)
    have hc : (i.castSucc : ℕ) = i := rfl
    have hs : (i.succ : ℕ) = i + 1 := rfl
    simp only [s, p₀, Function.comp_apply, Fin.val_succAbove, Equiv.swap_apply_def, Fin.ext_iff]
    split_ifs <;> omega
  have h₂ : c ∘ s ∘ p₂.succAbove = c := by
    funext j
    refine congrArg c (Fin.ext ?_)
    simp only [s, p₂, Function.comp_apply, Fin.val_succAbove]
    split_ifs <;> omega
  have hzero (p : Fin (n + 3)) (hp : p ≠ p₀ ∧ p ≠ p₂) :
      (-1 : ℤ) ^ (p : ℕ) • negPart m (cechπ m ((c ∘ s) ∘ p.succAbove) z).1 = 0 := by
    obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq hp.1.symm
    obtain ⟨j₂, hj₂⟩ := Fin.exists_succAbove_eq hp.2.symm
    rw [negPart_cechπ_eq_zero m (fun hsurj ↦ ?_) z, smul_zero]
    have hinj := (Finite.injective_iff_surjective_of_equiv e.symm).2 hsurj
    have hj : j₀ = j₂ := hinj (by
      simp only [Function.comp_apply, hj₀, hj₂]
      refine congrArg c (Fin.ext ?_)
      simp [s, p₀, p₂])
    have := congrArg Fin.val (hj₀.symm.trans (hj ▸ hj₂))
    simp [p₀, p₂] at this
  have hsum := sum_negPart_cechπ m hz (c ∘ s)
  rw [Fintype.sum_eq_add p₀ p₂ (fun h ↦ by simpa [p₀, p₂] using congrArg Fin.val h) hzero,
    Function.comp_assoc, Function.comp_assoc, h₀, h₂] at hsum
  simp only [p₀, p₂, pow_add, neg_one_sq, mul_one, ← smul_add] at hsum
  exact eq_neg_of_add_eq_zero_left (((isUnit_neg_one (α := ℤ)).pow _).smul_eq_zero.1 hsum)

/-- The coefficients of a cocycle of top degree at the monomials with all exponents negative are
alternating in the ordering of the coordinates, since adjacent transpositions generate the
symmetric group. -/
private lemma negPart_cechπ_comp_perm {z : (laurentCech (R := R) (κ := κ) m).X (n + 1)}
    (hz : (laurentCech m).d (n + 1) (n + 2) z = 0) (σ : Equiv.Perm (Fin (n + 2))) :
    negPart m (cechπ m (e.symm ∘ σ) z).1 =
      (Equiv.Perm.sign σ : ℤ) • negPart m (cechπ m e.symm z).1 := by
  induction σ using Submonoid.induction_of_closure_eq_top_right
    (Equiv.Perm.mclosure_swap_castSucc_succ (n + 1)) with
  | one =>
    rw [Equiv.Perm.sign_one, Units.val_one, one_smul]
    rfl
  | mul_right σ τ hτ ih =>
    obtain ⟨i, rfl⟩ := hτ
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, negPart_cechπ_comp_swap m e hz, ih,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
    simp

/-- A cocycle of top degree is determined, at the monomials with all exponents negative, by its
factor at the ordering `e.symm`: the factor at a tuple `c` is this one multiplied by the sign of
`c`. -/
private lemma negPart_cechπ_eq_tupleSign_smul {z : (laurentCech (R := R) (κ := κ) m).X (n + 1)}
    (hz : (laurentCech m).d (n + 1) (n + 2) z = 0) (c : Fin (n + 2) → κ) :
    negPart m (cechπ m c z).1 = e.tupleSign ℤ c • negPart m (cechπ m e.symm z).1 := by
  by_cases hc : Function.Surjective c
  · have hbij : Function.Bijective (e ∘ c) :=
      e.bijective.comp ⟨(Finite.injective_iff_surjective_of_equiv e.symm).2 hc, hc⟩
    have hσ : e.symm ∘ Equiv.ofBijective _ hbij = c := funext fun j ↦ by simp
    rw [← hσ, negPart_cechπ_comp_perm m e hz, Equiv.tupleSign_comp_perm, Equiv.tupleSign_symm,
      mul_one, Int.cast_id]
  · rw [negPart_cechπ_eq_zero m hc z, e.tupleSign_eq_zero_of_not_surjective ℤ hc, zero_smul]

/-! ### The homology in top degree -/

/-- The chain map to the complex concentrated in degree `n + 1` taking the coefficients of the
factor at the ordering `e.symm` at the monomials with all exponents negative. -/
private def toTop : laurentCech (R := R) (κ := κ) m ⟶
    (HomologicalComplex.single _ (ComplexShape.up ℕ) (n + 1)).obj
      (AddCommGrpCat.of (negativeExponents κ m →₀ R)) :=
  HomologicalComplex.mkHomToSingle (topCoefficient m e) fun i hi ↦ by
    obtain rfl : i = n := by simpa using hi
    exact d_comp_topCoefficient m e

/-- The chain map from the complex concentrated in degree `n + 1` given by the alternating
cocycles. -/
private def fromTop :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) (n + 1)).obj
      (AddCommGrpCat.of (negativeExponents κ m →₀ R)) ⟶ laurentCech (R := R) (κ := κ) m :=
  HomologicalComplex.mkHomFromSingle (topCochain m e) fun k hk ↦ by
    obtain rfl : k = n + 2 := by
      simp only [ComplexShape.up_Rel] at hk
      omega
    exact topCochain_comp_d m e

private lemma fromTop_comp_toTop : fromTop (R := R) m e ≫ toTop m e = 𝟙 _ := by
  ext : 1
  simp [toTop, fromTop, reassoc_of% topCochain_comp_topCoefficient]

/-- On cocycles of top degree, the projection onto the monomials with all exponents negative is
the alternating cocycle with the same factor at the ordering `e.symm`. -/
private lemma iCycles_comp_negSupportProj_univ :
    (laurentCech (R := R) (κ := κ) m).iCycles (n + 1) ≫
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (negSupportProj m Finset.univ)).f (n + 1) =
      (laurentCech m).iCycles (n + 1) ≫ (toTop m e ≫ fromTop m e).f (n + 1) := by
  refine Pi.hom_ext (f := fun a : Fin (n + 2) → κ ↦
    (laurentPresheaf (R := R) m).obj (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)))) _ _
    fun a ↦ AddCommGrpCat.ext fun x ↦ Subtype.ext ?_
  have hz : (laurentCech (R := R) (κ := κ) m).d (n + 1) (n + 2)
      ((laurentCech m).iCycles (n + 1) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  simp only [HomologicalComplex.comp_f, toTop, fromTop, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc]
  refine (congrArg Subtype.val (ConcreteCategory.congr_hom (cechComplexFunctor_map_f_π
    (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)) (laurentPresheaf (R := R) m)
    (negSupportProj m Finset.univ) (n + 1) a) ((laurentCech m).iCycles (n + 1) x))).trans ?_
  -- composites of morphisms of abelian groups act by composition; this states both sides in terms
  -- of the factors of the cocycle
  change ((negSupportProj (R := R) m Finset.univ).app _
      (cechπ m a ((laurentCech m).iCycles (n + 1) x))).1 =
    (cechπ m a (topCochain m e (topCoefficient m e ((laurentCech m).iCycles (n + 1) x)))).1
  rw [val_cechπ_topCochain, topCoefficient_apply, ← map_zsmul,
    ← negPart_cechπ_eq_tupleSign_smul m e hz, negEmb_negPart m (cechπ m a _).2]
  exact Finsupp.filterSupported_apply _ _ _

private lemma homologyMap_toTop_comp_fromTop :
    HomologicalComplex.homologyMap (toTop (R := R) m e ≫ fromTop m e) (n + 1) = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_eq_of_iCycles_comp (iCycles_comp_negSupportProj_univ m e)]
  have hsum : ∑ T : Finset κ, (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (negSupportProj (R := R) m T) = 𝟙 (laurentCech (R := R) (κ := κ) m) := by
    rw [← Functor.map_sum, sum_negSupportProj, CategoryTheory.Functor.map_id]
  rw [← HomologicalComplex.homologyMap_id, ← hsum, ← HomologicalComplex.homologyFunctor_map,
    ← HomologicalComplex.homologyFunctor_map, Functor.map_sum,
    Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) fun T _ hT ↦ ?_]
  obtain ⟨c, hc⟩ : ∃ c, c ∉ T := by
    by_contra! hall
    exact hT (Finset.eq_univ_iff_forall.2 hall)
  rw [HomologicalComplex.homologyFunctor_map]
  exact homologyMap_negSupportProj_of_notMem m hc n

/-- The top Čech cohomology of the Laurent polynomials is the group of Laurent polynomials whose
monomials have all exponents negative. -/
private def topHomologyIso : (laurentCech (R := R) (κ := κ) m).homology (n + 1) ≅
    AddCommGrpCat.of (negativeExponents κ m →₀ R) where
  hom := HomologicalComplex.homologyMap (toTop m e) (n + 1) ≫
    (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom
  inv := (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv ≫
    HomologicalComplex.homologyMap (fromTop m e) (n + 1)
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp,
      homologyMap_toTop_comp_fromTop]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (HomologicalComplex.homologyMap _ _),
      ← HomologicalComplex.homologyMap_comp, fromTop_comp_toTop,
      HomologicalComplex.homologyMap_id, Category.id_comp, Iso.inv_hom_id]

end TopDegree

/-! ### Comparison with the cohomology of the twisting sheaves -/

open Limits OrderDual in
open scoped Classical in
/-- The chart functor preserves the products of singletons of coordinates: the product of the
charts of the coordinates `a j` lies in the chart of their product. -/
private instance isIso_piComparison_chartFunctor {n : ℕ} (a : Fin (n + 1) → κ) :
    IsIso (piComparison (chartFunctor b) fun j ↦ toDual {a j}) := by
  refine (isIso_iff_of_thin _).2 ⟨homOfLE ?_⟩
  rw [chartFunctor_obj, basicOpen_coordProd, ofDual_pi_toDual_singleton]
  refine Finset.le_inf fun i hi ↦ ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
  exact (leOfHom (Pi.π _ j)).trans (chartFunctor_obj_singleton b (a j)).le

open _root_.AlgebraicGeometry.Scheme.Modules in
/-- Multiplication by the constant function `r` on `𝒪(m)`. -/
private abbrev twistingSheafSmul (m : ℤ) (r : R) :
    Proj.twistingSheaf 𝒜 m ⟶ Proj.twistingSheaf 𝒜 m :=
  (Proj.twistingSheaf 𝒜 m).globalSectionsSmul (baseRingToGlobalSections R (Proj 𝒜) r)

open OrderDual TauCeti.CategoryTheory in
open scoped Classical in
/-- Indexing the Čech complex by sets of coordinates instead of charts commutes with
multiplication by `r`. -/
private lemma homologyMap_smul_comp_homologyMap_cechComplexCompIso_hom (m : ℤ) (q : ℕ) (r : R) :
    HomologicalComplex.homologyMap ((cechComplexFunctor
        fun i : κ ↦ (chartFunctor b).obj (toDual {i})).map
          ((SheafOfModules.toSheaf _).map (twistingSheafSmul m r)).hom) q ≫
        HomologicalComplex.homologyMap (cechComplexCompIso (chartFunctor b)
          (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)).hom q =
      HomologicalComplex.homologyMap (cechComplexCompIso (chartFunctor b)
          (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)).hom q ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
            (Functor.whiskerLeft (chartFunctor b).op
              ((SheafOfModules.toSheaf _).map (twistingSheafSmul m r)).hom)) q := by
  rw [← HomologicalComplex.homologyMap_comp, cechComplexFunctor_map_comp_cechComplexCompIso_hom,
    HomologicalComplex.homologyMap_comp]

section Comparison

open Limits Opposite OrderDual TauCeti.CategoryTheory _root_.AlgebraicGeometry.Scheme.Modules

variable [Fintype κ] [DecidableEq κ] (m : ℤ)

/-- The cohomology of `𝒪(m)` is the Čech cohomology of the Laurent polynomials, by Leray's theorem
for the standard cover and the description of the sections over the charts. -/
private def cohomologyIsoHomologyLaurentCech (q : ℕ) :
    AddCommGrpCat.of (Cohomology (Proj.twistingSheaf 𝒜 m) q) ≅
      (laurentCech (R := R) (κ := κ) m).homology q :=
  haveI := isIso_cechComplexFunctor_map_laurentToSections b m
  (homologyCechComplexIsoCohomology (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
      (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
      (Proj.twistingSheaf 𝒜 m) q).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplexCompIso (chartFunctor b)
      (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)) q ≪≫
    (HomologicalComplex.homologyMapIso
      (asIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentToSections b m))) q).symm

/-- Multiplication by `r` on Laurent polynomials. -/
private def laurentSmul (r : R) :
    laurentPresheaf (R := R) (κ := κ) m ⟶ laurentPresheaf (R := R) m where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ r)
  naturality _ _ _ := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ ↦ rfl)

/-- The Laurent monomial `(r c) xᵉ` is the multiple of `c xᵉ` by the constant function `r`. -/
private lemma chartSectionHom_mul (S : Finset κ) (e : κ → ℤ) (r c : R) :
    chartSectionHom b m S e (r * c) =
      (Proj 𝒜).presheaf.map (Proj.basicOpen 𝒜 (coordProd b S)).leTop.op
        (baseRingToGlobalSections R (Proj 𝒜) r) • chartSectionHom b m S e c := by
  by_cases he : e ∈ chartExponents m S
  · rw [chartSectionHom_apply b he (fun i _ ↦ le_exponentBound e i),
      chartSectionHom_apply b he (fun i _ ↦ le_exponentBound e i)]
    refine Proj.twistingSheaf.ext fun x ↦ Eq.trans ?_ (Proj.twistingSheaf.smul_apply _ _ x).symm
    -- restricting a global function keeps its values, and the constant `r` is the fraction `r / 1`
    change Localization.mk _ _ =
      ((baseRingToGlobalSections R (Proj 𝒜) r).1 ⟨x.1, trivial⟩).val * Localization.mk _ _
    refine Eq.trans ?_ (congrArg (· * _)
      (val_baseRingToGlobalSections_apply (M := M) r ⟨x.1, trivial⟩)).symm
    rw [Localization.mk_mul, one_mul, mul_smul, Algebra.smul_def]
  · simp [chartSectionHom, he]

/-- Writing sections over a chart as Laurent polynomials is linear over the base ring. -/
private lemma chartSectionsHom_smul (S : Finset κ) (r : R)
    (f : Finsupp.supported R R (chartExponents m S)) :
    chartSectionsHom b m S (r • f) =
      (Proj 𝒜).presheaf.map (Proj.basicOpen 𝒜 (coordProd b S)).leTop.op
        (baseRingToGlobalSections R (Proj 𝒜) r) • chartSectionsHom b m S f := by
  simp only [chartSectionsHom, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, Submodule.coe_smul,
    Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_smul_index' fun e ↦ map_zero _, Finsupp.smul_sum]
  exact Finsupp.sum_congr fun e _ ↦ chartSectionHom_mul b m S e r _

private lemma laurentSmul_comp_laurentToSections (r : R) :
    laurentSmul m r ≫ laurentToSections b m = laurentToSections b m ≫
      Functor.whiskerLeft (chartFunctor b).op ((SheafOfModules.toSheaf _).map
        ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
          (baseRingToGlobalSections R (Proj 𝒜) r))).hom :=
  NatTrans.ext (funext fun S ↦ AddCommGrpCat.ext fun f ↦ by
    refine (chartSectionsHom_smul b m (ofDual S.unop) r f).trans ?_
    -- the whiskered morphism of sheaves of abelian groups acts on sections over a chart as the
    -- underlying morphism of sheaves of modules
    change _ = ((Proj.twistingSheaf 𝒜 m).globalSectionsSmul
      (baseRingToGlobalSections R (Proj 𝒜) r)).app _ (chartSectionsHom b m (ofDual S.unop) f)
    rw [globalSectionsSmul_app]
    rfl)

omit [Fintype κ] [DecidableEq κ] in
/-- Leray's comparison for the standard cover commutes with multiplication by `r`. -/
private lemma homologyCechComplexIsoCohomology_inv_smul [Finite κ] (q : ℕ) (r : R)
    (y : Cohomology (Proj.twistingSheaf 𝒜 m) q) :
    (homologyCechComplexIsoCohomology (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
        (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
        (Proj.twistingSheaf 𝒜 m) q).inv (r • y) =
      HomologicalComplex.homologyMap ((cechComplexFunctor
        fun i : κ ↦ (chartFunctor b).obj (toDual {i})).map
          ((SheafOfModules.toSheaf _).map (twistingSheafSmul m r)).hom) q
        ((homologyCechComplexIsoCohomology (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
          (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
          (Proj.twistingSheaf 𝒜 m) q).inv y) := by
  have h := homologyCechComplexIsoCohomology_hom_globalSectionsSmul _
    (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b) _ q
    (baseRingToGlobalSections R (Proj 𝒜) r) ((homologyCechComplexIsoCohomology
      (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
      (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
      (Proj.twistingSheaf 𝒜 m) q).inv y)
  rw [Iso.inv_hom_id_apply, ← base_smul_cohomology] at h
  rw [← h, Iso.hom_inv_id_apply]

/-- Writing sections over the charts as Laurent polynomials commutes with multiplication by
`r`. -/
private lemma homologyMap_smul_comp_homologyMapIso_laurentToSections_inv (q : ℕ) (r : R)
    [IsIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m))] :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
          (Functor.whiskerLeft (chartFunctor b).op
            ((SheafOfModules.toSheaf _).map (twistingSheafSmul m r)).hom)) q ≫
        (HomologicalComplex.homologyMapIso (asIso ((cechComplexFunctor
          fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentToSections b m))) q).inv =
      (HomologicalComplex.homologyMapIso (asIso ((cechComplexFunctor
          fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentToSections b m))) q).inv ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
            (laurentSmul m r)) q := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, HomologicalComplex.homologyMapIso_hom,
    asIso_hom, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← Functor.map_comp, ← Functor.map_comp, laurentSmul_comp_laurentToSections]

/-- The comparison of the cohomology of `𝒪(m)` with the Čech cohomology of the Laurent polynomials
is linear over the base ring. -/
private lemma cohomologyIsoHomologyLaurentCech_hom_smul (q : ℕ) (r : R)
    (x : Cohomology (Proj.twistingSheaf 𝒜 m) q) :
    (cohomologyIsoHomologyLaurentCech b m q).hom (r • x) =
      HomologicalComplex.homologyMap
        ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentSmul m r)) q
          ((cohomologyIsoHomologyLaurentCech b m q).hom x) := by
  have := isIso_cechComplexFunctor_map_laurentToSections b m
  have h := ((reassoc_of% (homologyMap_smul_comp_homologyMap_cechComplexCompIso_hom b m q r))
    _).trans (whisker_eq _ (homologyMap_smul_comp_homologyMapIso_laurentToSections_inv b m q r))
  simp only [cohomologyIsoHomologyLaurentCech, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, CategoryTheory.comp_apply]
  rw [homologyCechComplexIsoCohomology_inv_smul]
  exact ConcreteCategory.congr_hom h _

end Comparison

section TopComparison

variable [Fintype κ] [DecidableEq κ] (m : ℤ) {n : ℕ} (e : κ ≃ Fin (n + 2))

open Limits Opposite OrderDual TauCeti.CategoryTheory in
private lemma topHomologyIso_hom_smul (r : R)
    (y : (laurentCech (R := R) (κ := κ) m).homology (n + 1)) :
    (topHomologyIso m e).hom (HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentSmul m r))
        (n + 1) y) = r • (topHomologyIso m e).hom y := by
  let ρ : AddCommGrpCat.of (negativeExponents κ m →₀ R) ⟶
      AddCommGrpCat.of (negativeExponents κ m →₀ R) :=
    AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ r)
  have hco : ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentSmul m r)).f (n + 1) ≫ topCoefficient m e = topCoefficient m e ≫ ρ := by
    refine AddCommGrpCat.ext fun x ↦ ?_
    refine (congrArg (fun w ↦ negPart m (Subtype.val w)) (ConcreteCategory.congr_hom
      (cechComplexFunctor_map_f_π (fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ))
        (laurentPresheaf (R := R) (κ := κ) m) (laurentSmul (κ := κ) m r) (n + 1) e.symm)
          x)).trans ?_
    exact map_smul (negPart (R := R) (κ := κ) m) r _
  have hcomm : (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentSmul m r) ≫
      toTop m e = toTop m e ≫ (HomologicalComplex.single _ (ComplexShape.up ℕ) (n + 1)).map ρ := by
    ext : 1
    simp only [HomologicalComplex.comp_f, toTop, HomologicalComplex.mkHomToSingle_f,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
      reassoc_of% hco]
  have h : HomologicalComplex.homologyMap
      ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map (laurentSmul m r)) (n + 1) ≫
        (topHomologyIso m e).hom = (topHomologyIso m e).hom ≫ ρ := by
    simp only [topHomologyIso, ← Category.assoc, ← HomologicalComplex.homologyMap_comp, hcomm]
    simp only [HomologicalComplex.homologyMap_comp, Category.assoc,
      HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  exact ConcreteCategory.congr_hom h y

include b in
/-- The top cohomology of `𝒪(m)` as an `R`-module, for an index type in the universe of the
ring. -/
private def cohomologyTopLinearEquivAux :
    Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1) ≃ₗ[R] (negativeExponents κ m →₀ R) :=
  { (cohomologyIsoHomologyLaurentCech b m (n + 1) ≪≫
      topHomologyIso m e).addCommGroupIsoToAddEquiv with
    map_smul' := fun r x ↦ by
      -- the inherited `toFun` field must be identified with the forward map of the composite
      -- isomorphism before applying its scalar-compatibility lemmas
      change (topHomologyIso m e).hom ((cohomologyIsoHomologyLaurentCech b m (n + 1)).hom (r • x)) =
        r • (topHomologyIso m e).hom ((cohomologyIsoHomologyLaurentCech b m (n + 1)).hom x)
      rw [cohomologyIsoHomologyLaurentCech_hom_smul, topHomologyIso_hom_smul] }

end TopComparison

include b in
/-- The cohomology of `𝒪(m)` in degree `q > 0` vanishes when `q < n` or `m > -n - 1`, for an index
type in the universe of the ring. -/
private theorem subsingleton_cohomology_twistingSheaf_aux [Fintype κ] {m : ℤ} {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) := by
  classical
  exact (AddCommGrpCat.isZero_iff_subsingleton (G := AddCommGrpCat.of (Cohomology _ q))).1
    ((isZero_homology_laurentCech (R := R) (κ := κ) m hq h).of_iso
      (cohomologyIsoHomologyLaurentCech b m q))

/-! ### Main results -/

/-- The cohomology of `𝒪(m)` on projective space vanishes in degree `q > 0` when `q < n` or
`m > -n - 1`, for a basis indexed by a finite type in any universe. -/
private theorem subsingleton_cohomology_twistingSheaf_of_or {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) := by
  -- reindexing by `ULift (Fin n)` puts the index type in the universe of the ring
  let e : κ ≃ ULift.{u} (Fin (Fintype.card κ)) := (Fintype.equivFin κ).trans Equiv.ulift.symm
  exact subsingleton_cohomology_twistingSheaf_aux (b.reindex e) hq (by simpa using h)

/-- Reindexing the coordinates identifies the exponents of degree `m` with all entries
negative. -/
private def negativeExponentsCongr {κ κ' : Type*} [Fintype κ] [Fintype κ'] (e : κ ≃ κ') (m : ℤ) :
    negativeExponents κ m ≃ negativeExponents κ' m :=
  (e.arrowCongr (Equiv.refl ℤ)).subtypeEquiv fun x ↦ and_congr
    (by simp [Equiv.sum_comp e.symm x])
    ⟨fun h i ↦ h _, fun h i ↦ by simpa using h (e i)⟩

end TauCeti.SymmetricAlgebra

namespace Module.Basis

open TauCeti.SymmetricAlgebra (subsingleton_cohomology_twistingSheaf_of_or negativeExponents
  negativeExponentsCongr cohomologyTopLinearEquivAux)

universe u

variable {R : Type u} {M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

/-- **The intermediate cohomology of the twisting sheaves on projective space vanishes.** Let `M`
be a free `R`-module with a finite basis indexed by `κ`, so that `Proj (Sym M)` is projective space
of dimension `n = card κ - 1` over `R`. Then `Hᵠ(Proj (Sym M), 𝒪(m)) = 0` for `0 < q < n` and every
`m : ℤ`, over any commutative ring `R`. -/
theorem subsingleton_cohomology_twistingSheaf_of_lt_card {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {q : ℕ} (hq : 0 < q) (hqκ : q + 1 < Fintype.card κ) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) :=
  subsingleton_cohomology_twistingSheaf_of_or b m hq (.inl hqκ)

/-- **The twisting sheaves `𝒪(m)` with `m ≥ -n` on projective space have no higher cohomology.**
Let `M` be a free `R`-module with a finite basis indexed by `κ`, so that `Proj (Sym M)` is
projective space of dimension `n = card κ - 1` over `R`. If `m > -n - 1`, then
`Hᵠ(Proj (Sym M), 𝒪(m)) = 0` for every `q > 0`, over any commutative ring `R`. -/
theorem subsingleton_cohomology_twistingSheaf_of_neg_card_lt {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) {m : ℤ} (hm : -(Fintype.card κ : ℤ) < m) {q : ℕ} (hq : 0 < q) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) :=
  subsingleton_cohomology_twistingSheaf_of_or b m hq (.inr hm)

/-- **The top cohomology of the twisting sheaves on projective space.** Let `M` be a free `R`-module
with a basis `x₀, …, x_{n+1}` indexed by `κ`, so that `Proj (Sym M)` is projective space of
dimension `n + 1 ≥ 1` over `R`. Then `H^{n+1}(Proj (Sym M), 𝒪(m))` is isomorphic, as an `R`-module,
to the free `R`-module on the Laurent monomials `xᵉ` of degree `m` all of whose exponents are
negative, over any commutative ring `R`. No isomorphism is singled out: the one constructed in the
proof depends on an ordering of the coordinates. -/
theorem nonempty_linearEquiv_cohomology_top_twistingSheaf {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {n : ℕ} (hn : Fintype.card κ = n + 2) :
    Nonempty (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1) ≃ₗ[R] (negativeExponents κ m →₀ R)) :=
  -- reindexing by `ULift (Fin (card κ))` puts the index type in the universe of the ring
  let e₀ : κ ≃ ULift.{u} (Fin (Fintype.card κ)) := (Fintype.equivFin κ).trans Equiv.ulift.symm
  ⟨(cohomologyTopLinearEquivAux (b.reindex e₀) m
      (e₀.symm.trans (Fintype.equivFinOfCardEq hn))).trans
    (Finsupp.domLCongr (negativeExponentsCongr e₀.symm m))⟩

/-- The top cohomology `H^{n+1}(ℙ^{n+1}_R, 𝒪(m))` of a twisting sheaf on projective space is a
free `R`-module. -/
theorem free_cohomology_top_twistingSheaf {κ : Type*} [Fintype κ] (b : Module.Basis κ R M)
    (m : ℤ) {n : ℕ} (hn : Fintype.card κ = n + 2) :
    Module.Free R (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1)) :=
  have ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf m hn
  .of_equiv φ.symm

/-- The top cohomology `H^{n+1}(ℙ^{n+1}_R, 𝒪(m))` of a twisting sheaf on projective space is a
finitely generated `R`-module, since there are finitely many monomials of degree `m` with all
exponents negative. -/
theorem finite_cohomology_top_twistingSheaf {κ : Type*} [Fintype κ] (b : Module.Basis κ R M)
    (m : ℤ) {n : ℕ} (hn : Fintype.card κ = n + 2) :
    Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1)) :=
  have ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf m hn
  .equiv φ.symm

/-- The rank of the top cohomology `H^{n+1}(ℙ^{n+1}_R, 𝒪(m))` of a twisting sheaf on projective
space is the number of monomials of degree `m` with all exponents negative. -/
theorem finrank_cohomology_top_twistingSheaf [Nontrivial R] {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R M) (m : ℤ) {n : ℕ} (hn : Fintype.card κ = n + 2) :
    Module.finrank R (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1)) =
      Nat.card (negativeExponents κ m) := by
  have := Fintype.ofFinite (negativeExponents κ m)
  obtain ⟨φ⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf m hn
  rw [φ.finrank_eq,
    Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

/-- **The cohomology of the twisting sheaves on projective space is finitely generated.** Let `M`
be a free `R`-module with a finite basis of at least two elements, so that `Proj (Sym M)` is
projective space of positive dimension over `R`. Then `Hᵠ(Proj (Sym M), 𝒪(m))` is a finitely
generated `R`-module for every `q` and every `m : ℤ`, over any commutative ring `R`. -/
theorem finite_cohomology_twistingSheaf {κ : Type*} [Finite κ] [Nontrivial κ]
    (b : Module.Basis κ R M) (m : ℤ) (q : ℕ) :
    Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 m) q) := by
  have := Fintype.ofFinite κ
  rcases q with _ | q
  · exact TauCeti.SymmetricAlgebra.finite_cohomology_zero_twistingSheaf m b
  rcases lt_trichotomy (q + 2) (Fintype.card κ) with h | h | h
  · have := b.subsingleton_cohomology_twistingSheaf_of_lt_card m q.succ_pos h
    infer_instance
  · exact b.finite_cohomology_top_twistingSheaf m h.symm
  · have := b.subsingleton_cohomology_proj_of_card_le (Proj.twistingSheaf 𝒜 m) (q + 1) (by omega)
    infer_instance

end Module.Basis
