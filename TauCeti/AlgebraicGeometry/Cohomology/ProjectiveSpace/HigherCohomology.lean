/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.Algebra.Category.Grp.Zero
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Higher cohomology of the twisting sheaves on projective space

Let `M` be a free `R`-module with a basis `x₀, …, xₙ` indexed by a finite type `κ`, so that
`Proj (Sym M) = ℙⁿ_R` is projective space over an arbitrary commutative ring `R`. This file proves
that the twisting sheaves `𝒪(m)` have no cohomology in the intermediate degrees `0 < q < n`, for
every `m : ℤ`, and none at all in positive degrees when `m > -n - 1`. Together with the
computation of `H⁰` (`TauCeti.SymmetricAlgebra.free_cohomology_zero_twistingSheaf`) and the
vanishing above degree `n` (`Module.Basis.subsingleton_cohomology_proj_of_card_le`), this describes
`Hᵠ(ℙⁿ_R, 𝒪(m))` in every case of Hartshorne, Theorem III.5.1, except the top cohomology
`Hⁿ(ℙⁿ_R, 𝒪(m))` for `m ≤ -n - 1`, which does not vanish.

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

## Main results

* `TauCeti.SymmetricAlgebra.subsingleton_cohomology_twistingSheaf_of_lt_card`:
  `Hᵠ(ℙⁿ_R, 𝒪(m)) = 0` for `0 < q < n` and every `m : ℤ`.
* `TauCeti.SymmetricAlgebra.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`:
  `Hᵠ(ℙⁿ_R, 𝒪(m)) = 0` for every `q > 0` when `m > -n - 1`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1(b) and (d).
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

/-- The monomial `xᵈ` in the coordinates of the basis `b`. -/
private def monomial (d : κ →₀ ℕ) : _root_.SymmetricAlgebra R M :=
  (equivMvPolynomial b).symm (MvPolynomial.monomial d 1)

private lemma monomial_mem (d : κ →₀ ℕ) : monomial b d ∈ 𝒜 d.degree :=
  (_root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b _ _).1 (by
    simpa [monomial] using MvPolynomial.isHomogeneous_monomial (1 : R) rfl)

private lemma monomial_add (d d' : κ →₀ ℕ) :
    monomial b (d + d') = monomial b d * monomial b d' := by
  simp [monomial, ← map_mul, MvPolynomial.monomial_mul_monomial]

private lemma monomial_single (i : κ) : monomial b (Finsupp.single i 1) = ι R M (b i) := by
  refine (equivMvPolynomial b).injective ?_
  simp [monomial, _root_.SymmetricAlgebra.equivMvPolynomial_ι, MvPolynomial.X]

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

private lemma coordProd_eq_monomial (S : Finset κ) :
    coordProd b S = monomial b (indicatorExponent S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coordProd, indicatorExponent, monomial]
  | insert a S ha ih =>
    rw [coordProd, Finset.prod_insert ha, ← coordProd, ih]
    simp only [indicatorExponent, Finset.sum_insert ha, monomial_add, monomial_single]

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

private lemma monomial_pow (d : κ →₀ ℕ) (k : ℕ) : monomial b d ^ k = monomial b (k • d) := by
  simp [monomial, ← map_pow, MvPolynomial.monomial_pow]

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
    (c • monomial b (numeratorExponent e S j)) (coordProd b S ^ j)
    (Submodule.smul_mem _ c (degree_numeratorExponent_eq_toNat he hj ▸ monomial_mem b _))
    (by simpa [mul_comm] using SetLike.pow_mem_graded j (coordProd_mem b S))
    _ (basicOpen_le_basicOpen_pow b S j)

/-- The two ways of writing the Laurent monomial `xᵉ` as a fraction with denominators the powers of
coordinate products agree after cross-multiplication. -/
private lemma coordProd_pow_mul_monomial {S S' : Finset κ} {e : κ → ℤ}
    (he : e ∈ chartExponents m S) (he' : e ∈ chartExponents m S') {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S', 0 ≤ e i + j') (c : R) :
    coordProd b S' ^ j' * (c • monomial b (numeratorExponent e S j)) =
      coordProd b S ^ j * (c • monomial b (numeratorExponent e S' j')) := by
  rw [coordProd_eq_monomial, coordProd_eq_monomial, monomial_pow, monomial_pow, mul_smul_comm,
    mul_smul_comm, ← monomial_add, ← monomial_add]
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
  exact Proj.twistingSheaf.const_ext (coordProd_pow_mul_monomial b he he' hj hj' c)

/-- The Laurent monomial `c xᵉ` does not depend on the power of the coordinate product used as
its denominator. -/
private lemma chartSection_congr {S : Finset κ} {e : κ → ℤ} (he : e ∈ chartExponents m S) {j j' : ℕ}
    (hj : ∀ i ∈ S, 0 ≤ e i + j) (hj' : ∀ i ∈ S, 0 ≤ e i + j') (c : R) :
    chartSection b m S he j hj c = chartSection b m S he j' hj' c :=
  Proj.twistingSheaf.const_ext (coordProd_pow_mul_monomial b he he hj hj' c)

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

private lemma chartSectionsHom_eq_const {S : Finset κ}
    (f : Finsupp.supported R R (chartExponents m S))
    {j : ℕ} (hj : ∀ e ∈ f.1.support, ∀ i ∈ S, 0 ≤ e i + j) (hjm : 0 ≤ (j : ℤ) * S.card + m) :
    chartSectionsHom b m S f =
      Proj.twistingSheaf.const (i := j * S.card) (j := ((j : ℤ) * S.card + m).toNat)
        (by push_cast; omega) (∑ e ∈ f.1.support, f.1 e • monomial b (numeratorExponent e S j))
        (coordProd b S ^ j)
        (Submodule.sum_mem _ fun e he ↦ Submodule.smul_mem _ _
          (degree_numeratorExponent_eq_toNat ((Finsupp.mem_supported R f.1).1 f.2 he)
            (hj e he) ▸ monomial_mem b _))
        (by simpa [mul_comm] using SetLike.pow_mem_graded j (coordProd_mem b S)) _
        (basicOpen_le_basicOpen_pow b S j) := by
  have h : chartSectionsHom b m S f = ∑ e ∈ f.1.support, chartSectionHom b m S e (f.1 e) :=
    Finsupp.liftAddHom_apply _ _
  refine Proj.twistingSheaf.ext fun x ↦ ?_
  rw [h]
  refine (Proj.twistingSheaf.sum_apply _ _ x).trans <|
    (Finset.sum_congr rfl fun e he ↦ ?_).trans (Localization.mk_sum _ _ _).symm
  rw [chartSectionHom_apply b ((Finsupp.mem_supported R f.1).1 f.2 he) (hj e he)]
  -- the value of a fraction at `x` is that fraction in the localization at `x`, which is
  -- `Proj.twistingSheaf.const_apply`, true by `rfl`
  rfl

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
  simp only [map_mul, map_pow, map_sum, map_smul, map_zero, coordProd_eq_monomial, monomial,
    AlgEquiv.apply_symm_apply, MvPolynomial.monomial_pow, one_pow, Finset.mul_sum, mul_smul_comm,
    MvPolynomial.monomial_mul_monomial, mul_one] at hP
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
  have hr' : r = ∑ d ∈ p.support, p.coeff d • monomial b d := by
    refine (equivMvPolynomial b).injective ?_
    rw [← hpdef]
    simp only [map_sum, map_smul, monomial, AlgEquiv.apply_symm_apply, MvPolynomial.smul_monomial,
      smul_eq_mul, mul_one]
    exact MvPolynomial.as_sum p
  refine Proj.twistingSheaf.ext fun x ↦ ?_
  rw [h]
  -- the value of `r / (∏_{i ∈ S} xᵢ)ᵏ` at `x` is the fraction `r / (∏_{i ∈ S} xᵢ)ᵏ` by
  -- `Proj.twistingSheaf.const_apply`, which holds by `rfl`
  refine (Proj.twistingSheaf.sum_apply _ _ x).trans <| (Finset.sum_congr rfl fun d hd ↦ ?_).trans
    ((Localization.mk_sum _ _ _).symm.trans (by rw [← hr']; rfl))
  rw [chartSectionHom_apply b (shiftExponent_mem_chartExponents (hdeg d hd))
    (add_shiftExponent_nonneg S k d)]
  -- both sides are fractions in the localization at `x`, by `Proj.twistingSheaf.const_apply`
  change Localization.mk _ _ = Localization.mk _ _
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
    -- the maps of `laurentPresheaf` are inclusions, which do not change the Laurent polynomial
    change chartSectionsHom b m _ ⟨g, _⟩ = (Proj.twistingSheaf 𝒜 m).presheaf.map _
      (chartSectionsHom b m _ ⟨g, hg⟩)
    have hmem : ∀ e ∈ g.support, e ∈ chartExponents m (ofDual S.unop) :=
      fun e he ↦ (Finsupp.mem_supported R g).1 hg he
    rw [show chartSectionsHom b m (ofDual S.unop) ⟨g, hg⟩ =
        ∑ e ∈ g.support, chartSectionHom b m _ e (g e) from Finsupp.liftAddHom_apply _ _, map_sum,
      show chartSectionsHom b m (ofDual S'.unop) _ =
        ∑ e ∈ g.support, chartSectionHom b m _ e (g e) from Finsupp.liftAddHom_apply _ _]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he' : e ∈ chartExponents m (ofDual S'.unop) :=
      chartExponents_mono (leOfHom f.unop) (hmem e he)
    rw [chartSectionHom_apply b (hmem e he) (fun i _ ↦ le_exponentBound e i),
      chartSectionHom_apply b he' (fun i _ ↦ le_exponentBound e i)]
    exact (res_chartSection b (leOfHom ((chartFunctor b).map f.unop)) (hmem e he) he' _ _ _).symm

omit [Fintype κ] [DecidableEq κ] in
private lemma chartFunctor_obj_singleton (i : κ) :
    (chartFunctor b).obj (toDual {i}) = Proj.basicOpen 𝒜 (ι R M (b i)) := by
  simp [chartFunctor, coordProd]

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

omit [Fintype κ] in
private lemma ofDual_pi_subset_image (n : ℕ) (a : Fin (n + 1) → κ) :
    ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) ⊆ Finset.univ.image a :=
  leOfHom (Pi.lift fun j ↦ homOfLE (show toDual (Finset.univ.image a) ≤ toDual {a j} from
    Finset.singleton_subset_iff.2 (Finset.mem_image_of_mem a (Finset.mem_univ j))))

private lemma isIso_laurentToSections_app {S : (Finset κ)ᵒᵈ} (hS : (ofDual S).Nonempty) :
    IsIso ((laurentToSections b m).app (op S)) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨chartSectionsHom_injective b hS, chartSectionsHom_surjective b hS⟩

private lemma isIso_cechComplexFunctor_map_laurentToSections :
    IsIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m)) := by
  have (n : ℕ) : IsIso (((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
      (laurentToSections b m)).f n) := by
    have e : ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentToSections b m)).f n = Limits.Pi.map fun a : Fin (n + 1) → κ ↦
          (laurentToSections b m).app (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))) :=
      Pi.hom_ext _ _ fun a ↦ (cechComplexFunctor_map_f_π _ _ _ n a).trans
        (Pi.map_π (fun a : Fin (n + 1) → κ ↦ (laurentToSections b m).app
          (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)))) a).symm
    have (a : Fin (n + 1) → κ) : IsIso ((laurentToSections b m).app
        (op (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)))) :=
      isIso_laurentToSections_app b m
        ⟨a 0, Finset.singleton_subset_iff.1
          (leOfHom (Pi.π (fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ)) 0))⟩
    rw [e]
    exact Pi.map_isIso _
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### Splitting Laurent polynomials by negative support -/

omit [DecidableEq κ] in
/-- Keeping the monomials of a Laurent polynomial whose exponents satisfy `p`. -/
private def filterHom {s t : Set (κ → ℤ)} (p : (κ → ℤ) → Prop) [DecidablePred p]
    (h : ∀ e ∈ s, p e → e ∈ t) : Finsupp.supported R R s →+ Finsupp.supported R R t :=
  ((Finsupp.filterAddHom p).comp (Finsupp.supported R R s).subtype.toAddMonoidHom).codRestrict _
    fun f ↦ (Finsupp.mem_supported R _).2 fun e he ↦ by
      -- the composite of the filter with the inclusion of `supported` is the filter itself
      change e ∈ ((f.1.filter p).support : Set (κ → ℤ)) at he
      rw [Finsupp.support_filter, Finset.coe_filter] at he
      exact h e ((Finsupp.mem_supported R _).1 f.2 he.1) he.2

/-- The projection onto the Laurent monomials with negative support exactly `T`. -/
private def negSupportProj (T : Finset κ) :
    laurentPresheaf (R := R) (κ := κ) m ⟶ laurentPresheaf (R := R) (κ := κ) m where
  app _ := AddCommGrpCat.ofHom (filterHom (negSupport · = T) fun _ he _ ↦ he)
  naturality _ _ _ := rfl

omit [DecidableEq κ] in
private lemma sum_filterHom_negSupport [DecidableEq κ] {s : Set (κ → ℤ)}
    (f : Finsupp.supported R R s) :
    ∑ T : Finset κ, filterHom (negSupport · = T) (fun _ he _ ↦ he) f = f := by
  refine Subtype.ext (Finsupp.ext fun e ↦ ?_)
  rw [Submodule.coe_sum, Finsupp.finsetSum_apply]
  -- each `filterHom` is the filter on the underlying Laurent polynomial
  change ∑ T : Finset κ, (f.1.filter (negSupport · = T)) e = f.1 e
  simp [Finsupp.filter_apply]

private lemma sum_negSupportProj :
    ∑ T : Finset κ, negSupportProj (R := R) (κ := κ) m T = 𝟙 _ := by
  refine NatTrans.ext (funext fun S ↦ ?_)
  rw [NatTrans.app_sum, NatTrans.id_app]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun f ↦ ?_)
  -- a morphism of abelian groups acts through `AddCommGrpCat.homAddEquiv`, which is additive
  change AddCommGrpCat.homAddEquiv (∑ T : Finset κ, (negSupportProj (R := R) m T).app S) f = f
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact sum_filterHom_negSupport f

omit [Fintype κ] in
private lemma ofDual_prod_subset (Y S : (Finset κ)ᵒᵈ) : ofDual (Y ⨯ S) ⊆ ofDual Y ∪ ofDual S :=
  leOfHom (prod.lift (homOfLE (show toDual (ofDual Y ∪ ofDual S) ≤ Y from
    Finset.subset_union_left)) (homOfLE (show toDual (ofDual Y ∪ ofDual S) ≤ S from
    Finset.subset_union_right)))

/-- Restriction of Laurent polynomials to the intersection with the chart of `c`. -/
private def restrictToChart (c : κ) :
    laurentPresheaf (R := R) (κ := κ) m ⟶
      (prod.functor.obj (toDual {c})).op ⋙ laurentPresheaf (R := R) (κ := κ) m where
  app S := (laurentPresheaf m).map (prod.snd : toDual {c} ⨯ S.unop ⟶ S.unop).op
  naturality _ _ _ := rfl

/-- On the monomials with negative support `T`, a Laurent polynomial on the intersection with the
chart of a coordinate `c ∉ T` is already a Laurent polynomial on the original chart. -/
private def extendFromChart {c : κ} {T : Finset κ} (hc : c ∉ T) :
    (prod.functor.obj (toDual {c})).op ⋙ laurentPresheaf (R := R) (κ := κ) m ⟶
      laurentPresheaf (R := R) (κ := κ) m where
  app S := AddCommGrpCat.ofHom (filterHom (negSupport · = T) fun e he heT ↦ ⟨he.1, fun i hi ↦ by
    have hi' := ofDual_prod_subset _ _ (he.2 hi)
    rw [Finset.mem_union, ofDual_toDual, Finset.mem_singleton] at hi'
    exact hi'.resolve_left fun h ↦ hc (h ▸ heT ▸ hi)⟩)
  naturality _ _ _ := rfl

private lemma restrictToChart_comp_extendFromChart {c : κ} {T : Finset κ} (hc : c ∉ T) :
    restrictToChart (R := R) (κ := κ) m c ≫ extendFromChart (R := R) m hc =
      negSupportProj (R := R) m T :=
  -- restriction is an inclusion and both sides filter the same Laurent polynomial
  rfl

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
  refine HomologicalComplex.homologyMap_eq_zero_of_f_eq_zero _ _ (Pi.hom_ext _ _ fun a ↦
    (cechComplexFunctor_map_f_π _ _ _ q a).trans (Eq.trans ?_ zero_comp.symm))
  -- no Laurent monomial over a product of `q + 1` charts has all exponents negative
  have hno : ∀ e ∈ chartExponents m (ofDual (∏ᶜ fun j ↦ (toDual {a j} : (Finset κ)ᵒᵈ))),
      negSupport e ≠ Finset.univ := by
    rintro e ⟨hsum, hneg⟩ huniv
    rcases h with h | h
    · have := (Finset.card_le_card (hneg.trans (ofDual_pi_subset_image q a))).trans
        Finset.card_image_le
      rw [huniv, Finset.card_univ, Finset.card_univ, Fintype.card_fin] at this
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
    change f.1.filter (negSupport · = Finset.univ) = 0
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
    ext n : 1
    rw [show (∑ T : Finset κ, (cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (negSupportProj (R := R) m T)).f n = ∑ T : Finset κ,
          ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
            (negSupportProj (R := R) m T)).f n from
        map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _, HomologicalComplex.id_f]
    refine Pi.hom_ext _ _ fun a ↦ (Preadditive.sum_comp _ _ _).trans <|
      (Finset.sum_congr rfl fun T _ ↦ cechComplexFunctor_map_f_π _ _ _ n a).trans <|
        (Preadditive.comp_sum _ _ _).symm.trans ?_
    have happ (S) : ∑ T : Finset κ, (negSupportProj (R := R) m T).app S = 𝟙 _ := by
      rw [← NatTrans.app_sum, sum_negSupportProj, NatTrans.id_app]
    exact (congrArg (fun g ↦ _ ≫ g) (happ _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
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

include b in
open Limits OrderDual TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules in
/-- The cohomology of `𝒪(m)` in degree `q > 0` vanishes when `q < n` or `m > -n - 1`, for an index
type in the universe of the ring. -/
private theorem subsingleton_cohomology_twistingSheaf_aux [Fintype κ] {m : ℤ} {q : ℕ} (hq : 0 < q)
    (h : q + 1 < Fintype.card κ ∨ -(Fintype.card κ : ℤ) < m) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m) q) := by
  classical
  refine (AddCommGrpCat.isZero_iff_subsingleton (G := AddCommGrpCat.of (Cohomology _ q))).1
    ((isZero_homology_laurentCech (R := R) (κ := κ) m hq h).of_iso ?_)
  have := isIso_cechComplexFunctor_map_laurentToSections b m
  -- the product of the charts of the coordinates `a j` lies in the chart of their product
  have hG (n : ℕ) (a : Fin (n + 1) → κ) : Nonempty ((∏ᶜ fun j ↦ (chartFunctor b).obj (toDual {a j}))
      ⟶ (chartFunctor b).obj (∏ᶜ fun j ↦ toDual {a j})) := by
    refine ⟨homOfLE ?_⟩
    -- `chartFunctor` sends a set of coordinates to the basic open of their product
    change _ ≤ Proj.basicOpen 𝒜 (coordProd b _)
    rw [basicOpen_coordProd]
    refine Finset.le_inf fun i hi ↦ ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (ofDual_pi_subset_image n a hi)
    exact (leOfHom (Pi.π _ j)).trans (chartFunctor_obj_singleton b (a j)).le
  exact (AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
      (fun i : κ ↦ (chartFunctor b).obj (toDual {i}))
      (isAffineOpen_inf_chartFunctor_obj_singleton b) (iSup_chartFunctor_obj_singleton b)
      (Proj.twistingSheaf 𝒜 m) q).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplexCompIso (chartFunctor b)
      (fun i : κ ↦ toDual {i}) (sectionsPresheaf (R := R) (M := M) m)
      hG) q ≪≫
    (HomologicalComplex.homologyMapIso
      (asIso ((cechComplexFunctor fun i : κ ↦ (toDual {i} : (Finset κ)ᵒᵈ)).map
        (laurentToSections b m))) q).symm

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

end TauCeti.SymmetricAlgebra
