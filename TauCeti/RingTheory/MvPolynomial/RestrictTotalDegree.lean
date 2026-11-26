/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.Weight
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.LinearAlgebra.Basis.Pi
import TauCeti.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Algebra.MvPolynomial.Rename
import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The submodules of polynomials of bounded total degree

Mathlib's `MvPolynomial.restrictTotalDegree σ R m` is the submodule of polynomials of total degree
at most `m`. This file records that these submodules increase with `m`, that a monomial of degree
at most `m` lies in the `m`-th one, and that the `m`-th one is spanned by those monomials, so that
a linear statement about polynomials of bounded degree reduces to monomials. These monomials form
a basis whose coordinates are the coefficients, giving finite coordinates on tuples of
bounded-degree polynomials; evaluating such tuples is faithful over an infinite integral domain,
by Mathlib's `MvPolynomial.funext`. Raising the degree bound leaves the evaluation unchanged and
zero-pads the coordinates. The homogeneous polynomials of degree `d` have the analogous
coordinates, from `TauCeti.homogeneousMonomialBasis`, and evaluation, and their inclusion among
the polynomials of total degree at most `d` again zero-pads the coordinates. As a spanning family,
the monomials may be replaced by products `∏ᵢ Sₖᵢ(Xᵢ)` of the members of a polynomial sequence
`S` in the separate variables, for instance the integer-valued binomial polynomials.

## Main results

* `MvPolynomial.restrictTotalDegree_mono`: the submodules increase with the degree bound.
* `MvPolynomial.monomial_mem_restrictTotalDegree`: a monomial of degree at most `m` has total
  degree at most `m`.
* `MvPolynomial.restrictTotalDegree_eq_span`: the monomials of degree at most `m` span the
  polynomials of total degree at most `m`.
* `MvPolynomial.basisRestrictTotalDegree`: the monomial basis of the polynomials of total degree
  at most `m`, whose coordinates are the coefficients.
* `MvPolynomial.boundedCoefficientEquiv`: monomial coefficients as finite coordinates on tuples of
  bounded-degree polynomials.
* `MvPolynomial.tupleEvaluation`, `MvPolynomial.tupleEvaluation_injective`: evaluation of tuples
  of polynomials from a submodule as vector-valued functions is linear, and injective over an
  infinite integral domain, for instance for the polynomials of bounded total degree.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp_eq_extendByZero`: including a submodule of
  polynomials supported on a set of exponents of degree at most `e` among the polynomials of total
  degree at most `e` extends the coefficients by zero.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp`: raising the degree bound extends the
  finite coefficient coordinates by zero.
* `MvPolynomial.boundedCoefficientEquiv_inclusion_comp_homogeneous`: including homogeneous
  polynomials in a bounded-degree space extends their coordinates by zero.
* `MvPolynomial.mul_mem_restrictTotalDegree`: total degree bounds add under multiplication.
* `MvPolynomial.aeval_mem_restrictTotalDegree`: substituting polynomials of total degree at most
  one, such as affine linear forms, for the variables occurring in a polynomial of total degree at
  most `m` gives a polynomial of total degree at most `m`, also when the substituted polynomials
  have coefficients in an `R`-algebra.
* `MvPolynomial.killCompl_mem_restrictTotalDegree`: discarding variables outside an injective
  renaming does not raise the total degree.
* `MvPolynomial.hyperplaneSliceMap`, `MvPolynomial.hyperplaneSliceMap_surjective`: the bounded
  hyperplane slice map `(f₀, ∂f/∂X_{j₀}|_{X_{j₀}=0})` from `restrictTotalDegree σ R (d + 1)` to
  `restrictTotalDegree {j // j ≠ j₀} R (d + 1) × restrictTotalDegree {j // j ≠ j₀} R d` is
  surjective.
* `MvPolynomial.restrictTotalDegreeEquivDegreeLT`: in one variable, `restrictTotalDegree σ R d`
  is linearly equivalent to `Polynomial.degreeLT R (d + 1)`.
* `Submodule.exists_surjective_linearMap_restrictTotalDegree`: over an infinite field,
  restricting the polynomials of total degree at most `m` to a subspace `W`, in coordinates on
  `W`, is onto the polynomials of total degree at most `m` in `dim W` variables, with kernel the
  polynomials vanishing on `W`.
* `MvPolynomial.aeval_option_elim_one_X_mem_restrictTotalDegree`: setting the variable `none` to
  `1` does not raise the total degree.
* `MvPolynomial.span_prod_aeval_X_le`: products of a triangular family of one-variable polynomials
  in the separate variables lie in the span of the products of the original family.
* `Polynomial.Sequence.span_prod_aeval_X_eq_restrictTotalDegree`: the products `∏ᵢ Sₖᵢ(Xᵢ)` of
  a polynomial sequence with unit leading coefficients span the polynomials of bounded degree.
* `Module.Basis.apply_mem_of_monomial_degree_le`: a bilinear map takes values in a submodule on
  bounded-degree polynomials if it does so on basis vectors and bounded-degree monomials.
* `Module.Basis.constr_X_mul_mem_restrictTotalDegree`: multiplication by a linear form raises
  total degree by at most one.
-/

public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

variable (σ R) in
/-- The polynomials of total degree at most `m` increase with `m`. -/
theorem restrictTotalDegree_mono : Monotone (restrictTotalDegree σ R) :=
  fun _ _ h p hp ↦
    (mem_restrictTotalDegree σ _ p).2 (((mem_restrictTotalDegree σ _ p).1 hp).trans h)

/-- A polynomial of total degree at most `d` has zero coefficients at exponents of degree
above `d`. -/
theorem coeff_eq_zero_of_mem_restrictTotalDegree {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictTotalDegree σ R d) {a : σ →₀ ℕ} (ha : d < a.degree) :
    p.coeff a = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [← Finsupp.degree_apply]
  exact ((mem_restrictTotalDegree σ d p).mp hp).trans_lt ha

/-- A monomial whose exponent has degree at most `m` has total degree at most `m`. -/
theorem monomial_mem_restrictTotalDegree {s : σ →₀ ℕ} {m : ℕ} (h : s.degree ≤ m) (r : R) :
    monomial s r ∈ restrictTotalDegree σ R m :=
  (mem_restrictTotalDegree σ m _).2 <| (totalDegree_monomial_le s r).trans <| by
    simpa [Finsupp.sum, Finsupp.degree_apply] using h

variable (σ R) in
/-- The polynomials of total degree at most `m` are those supported on exponents of degree at
most `m`. -/
theorem restrictTotalDegree_eq_restrictSupport (m : ℕ) :
    restrictTotalDegree σ R m = restrictSupport R {s : σ →₀ ℕ | s.degree ≤ m} := by
  simp only [restrictTotalDegree, Finsupp.sum, Finsupp.degree_apply]

variable (σ R) in
/-- The polynomials of total degree at most `m` are spanned by the monomials of degree at most
`m`. -/
theorem restrictTotalDegree_eq_span (m : ℕ) :
    restrictTotalDegree σ R m =
      Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ m}) := by
  rw [restrictTotalDegree_eq_restrictSupport, restrictSupport_eq_span]

variable (σ R) in
/-- The monomial basis of the polynomials of total degree at most `m`, indexed by exponents of
degree at most `m`. -/
noncomputable def basisRestrictTotalDegree (m : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree ≤ m} R (restrictTotalDegree σ R m) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree ≤ m}).map
    (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m).symm)

theorem basisRestrictTotalDegree_def (m : ℕ) :
    basisRestrictTotalDegree σ R m =
      (basisRestrictSupport R {s : σ →₀ ℕ | s.degree ≤ m}).map
        (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m).symm) :=
  (rfl)

/-- The submodule of polynomials of total degree at most `m` is a free `R`-module. -/
noncomputable instance (m : ℕ) : Module.Free R (restrictTotalDegree σ R m) :=
  Module.Free.of_basis (basisRestrictTotalDegree σ R m)

/-- The coordinate of a bounded-degree polynomial in the monomial basis is its coefficient. -/
@[simp]
theorem basisRestrictTotalDegree_repr_apply (m : ℕ) (p : restrictTotalDegree σ R m)
    (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m).repr p s = (p : MvPolynomial σ R).coeff s := (rfl)

/-- A monomial basis vector of the bounded-degree polynomials is the corresponding monomial. -/
@[simp]
theorem coe_basisRestrictTotalDegree (m : ℕ) (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m s : MvPolynomial σ R) = monomial s.val 1 := by
  rw [basisRestrictTotalDegree_def, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  -- As in `basisRestrictTotalDegree`, the index `s` is read as an element of the set
  -- `{t | t.degree ≤ m}` that indexes `basisRestrictSupport`; the two subtypes agree by definition.
  exact basisRestrictSupport_apply_coe (s := {t : σ →₀ ℕ | t.degree ≤ m}) s

section Coordinates

variable {J : Type*}

variable (σ R J) in
/-- Monomial coefficients identify `J`-indexed tuples of polynomials of total degree at most `d`
with functions on the pairs of an index and an exponent of degree at most `d`. For finitely many
variables and indices this index type is finite, so these are finite coordinates. -/
noncomputable def boundedCoefficientEquiv [Finite σ] (d : ℕ) :
    (J → restrictTotalDegree σ R d) ≃ₗ[R] (J × {s : σ →₀ ℕ // s.degree ≤ d} → R) :=
  (basisRestrictTotalDegree σ R d).piEquivFun J

/-- A finite coefficient coordinate is the corresponding monomial coefficient of an entry. -/
@[simp] theorem boundedCoefficientEquiv_apply [Finite σ] {d : ℕ}
    (v : J → restrictTotalDegree σ R d) (i : J × {s : σ →₀ ℕ // s.degree ≤ d}) :
    boundedCoefficientEquiv σ R J d v i = (v i.1 : MvPolynomial σ R).coeff i.2 := by
  simp [boundedCoefficientEquiv]

/-- The tuple with prescribed finite coefficient coordinates has those monomial coefficients. -/
@[simp] theorem coeff_boundedCoefficientEquiv_symm_apply [Finite σ] {d : ℕ}
    (a : J × {s : σ →₀ ℕ // s.degree ≤ d} → R) (j : J) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    (((boundedCoefficientEquiv σ R J d).symm a j : restrictTotalDegree σ R d) :
      MvPolynomial σ R).coeff s = a (j, s) :=
  (basisRestrictTotalDegree σ R d).repr_piEquivFun_symm_apply a j s

variable (J) in
/-- Evaluation of a tuple of polynomials from a submodule `S` as a vector-valued function on
points. It is linear in the tuple. -/
noncomputable def tupleEvaluation (S : Submodule R (MvPolynomial σ R)) :
    (J → S) →ₗ[R] (σ → R) → J → R where
  toFun v x j := eval x (v j : MvPolynomial σ R)
  map_add' v w := by
    funext x j
    simp
  map_smul' a v := by
    funext x j
    simp

/-- Coordinate evaluation of a tuple of polynomials from a submodule. -/
@[simp] theorem tupleEvaluation_apply {S : Submodule R (MvPolynomial σ R)} (v : J → S)
    (x : σ → R) (j : J) :
    tupleEvaluation J S v x j = eval x (v j : MvPolynomial σ R) := (rfl)

/-- Over an infinite integral domain, tuples of polynomials from a submodule are determined by
the functions they define: the evaluation map is faithful. -/
theorem tupleEvaluation_injective {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (S : Submodule R (MvPolynomial σ R)) : Function.Injective (tupleEvaluation J S) :=
  fun _ _ h =>
    _root_.funext fun j => Subtype.ext <| MvPolynomial.funext fun x => congrFun (congrFun h x) j

/-- Including a tuple of polynomials into a larger submodule does not change the function it
defines. -/
@[simp] theorem tupleEvaluation_inclusion_comp {S T : Submodule R (MvPolynomial σ R)}
    (h : S ≤ T) (v : J → S) :
    tupleEvaluation J T (Submodule.inclusion h ∘ v) = tupleEvaluation J S v := (rfl)

/-- Let `p` be a submodule of the polynomials of total degree at most `e` whose members have zero
coefficients at the exponents outside `Q`, all exponents in `Q` having degree at most `e`.
Including a tuple from `p` among the polynomials of total degree at most `e` extends its
coefficients at the exponents in `Q` by zero. -/
theorem boundedCoefficientEquiv_inclusion_comp_eq_extendByZero [Finite σ]
    {p : Submodule R (MvPolynomial σ R)} {e : ℕ} (hp : p ≤ restrictTotalDegree σ R e)
    {Q : (σ →₀ ℕ) → Prop} (hQ : ∀ s, Q s → s.degree ≤ e)
    (h0 : ∀ x ∈ p, ∀ s, ¬Q s → x.coeff s = 0) (v : J → p) :
    boundedCoefficientEquiv σ R J e (Submodule.inclusion hp ∘ v) =
      Function.ExtendByZero.linearMap R R
        (Prod.map (id : J → J) (Subtype.impEmbedding Q (fun s => s.degree ≤ e) hQ))
        (fun i : J × Subtype Q => (v i.1 : MvPolynomial σ R).coeff i.2) := by
  have hinj : Function.Injective
      (Prod.map (id : J → J) (Subtype.impEmbedding Q (fun s => s.degree ≤ e) hQ)) :=
    Function.injective_id.prodMap (Subtype.impEmbedding _ _ _).injective
  ext ⟨j, s, hs'⟩
  rw [Function.ExtendByZero.linearMap_apply]
  by_cases hs : Q s
  · -- The index `(j, ⟨s, hs'⟩)` is the image of `(j, ⟨s, hs⟩)` by definition.
    rw [show ((j, ⟨s, hs'⟩) : J × {s : σ →₀ ℕ // s.degree ≤ e}) =
      Prod.map id (Subtype.impEmbedding Q _ hQ) (j, ⟨s, hs⟩) from rfl, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ ?_, Pi.zero_apply, boundedCoefficientEquiv_apply,
      Function.comp_apply, Submodule.coe_inclusion]
    · exact h0 _ (v j).property s hs
    · rintro ⟨⟨j', s', hs''⟩, he⟩
      exact hs (by cases he; exact hs'')

/-- Raising the degree bound from `d` to `d'` zero-pads the finite coefficient coordinates: they
are extended by zero along the inclusion of index types, so the new coordinates at exponents of
degree above `d` vanish. -/
theorem boundedCoefficientEquiv_inclusion_comp [Finite σ] {d d' : ℕ} (h : d ≤ d')
    (v : J → restrictTotalDegree σ R d) :
    boundedCoefficientEquiv σ R J d' (Submodule.inclusion (restrictTotalDegree_mono σ R h) ∘ v) =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree ≤ d) (fun s => s.degree ≤ d')
            fun _ hs => hs.trans h))
        (boundedCoefficientEquiv σ R J d v) := by
  rw [boundedCoefficientEquiv_inclusion_comp_eq_extendByZero _ (Q := fun s => s.degree ≤ d)
    (fun _ hs => hs.trans h)
    (fun _ hx _ hs => coeff_eq_zero_of_mem_restrictTotalDegree hx (not_le.1 hs)) v]
  congr 1
  ext i
  exact (boundedCoefficientEquiv_apply v i).symm

/-! ### Homogeneous coordinates

The homogeneous polynomials of degree `d` lie among those of total degree at most `d`. Their
monomial coordinates `(homogeneousMonomialBasis d).piEquivFun J` are indexed by the exponents of
degree exactly `d`, their evaluation is `tupleEvaluation`, and including them in a bounded-degree
space extends these coordinates by zero. -/

variable (σ R) in
/-- A homogeneous polynomial of degree `d` has total degree at most every `e ≥ d`. -/
theorem homogeneousSubmodule_le_restrictTotalDegree {d e : ℕ} (h : d ≤ e) :
    homogeneousSubmodule σ R d ≤ restrictTotalDegree σ R e := fun p hp =>
  (mem_restrictTotalDegree σ e p).2 <|
    ((mem_homogeneousSubmodule d p).1 hp).totalDegree_le.trans h

/-- Including homogeneous polynomials of degree `d` in the polynomials of total degree at most
`e ≥ d` extends their coefficient coordinates by zero along the inclusion of exponents of degree
`d` among those of degree at most `e`. -/
theorem boundedCoefficientEquiv_inclusion_comp_homogeneous [Finite σ] {d e : ℕ} (h : d ≤ e)
    (v : J → homogeneousSubmodule σ R d) :
    boundedCoefficientEquiv σ R J e
        (Submodule.inclusion (homogeneousSubmodule_le_restrictTotalDegree σ R h) ∘ v) =
      Function.ExtendByZero.linearMap R R (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : σ →₀ ℕ => s.degree = d) (fun s => s.degree ≤ e)
            fun _ hs => hs.le.trans h))
        ((TauCeti.homogeneousMonomialBasis d).piEquivFun J v) := by
  rw [boundedCoefficientEquiv_inclusion_comp_eq_extendByZero _ (Q := fun s => s.degree = d)
    (fun _ hs => hs.le.trans h)
    (fun x hx _ hs => ((mem_homogeneousSubmodule d x).1 hx).coeff_eq_zero hs) v]
  congr 1
  ext i
  simp

end Coordinates

/-- A product of polynomials of total degrees at most `d` and `e` has total degree at most
`d + e`. -/
theorem mul_mem_restrictTotalDegree {d e : ℕ} {f g : MvPolynomial σ R}
    (hf : f ∈ restrictTotalDegree σ R d) (hg : g ∈ restrictTotalDegree σ R e) :
    f * g ∈ restrictTotalDegree σ R (d + e) := by
  rw [mem_restrictTotalDegree] at hf hg ⊢
  exact (totalDegree_mul f g).trans (add_le_add hf hg)

/-- Substituting polynomials of total degree at most one, for instance linear forms, for the
variables of `p` does not raise the total degree, also when the substituted polynomials have
coefficients in an `R`-algebra `S`. Only the variables that occur in `p` need to be bounded. -/
theorem aeval_mem_restrictTotalDegree {τ S : Type*} [CommSemiring S] [Algebra R S]
    (p : MvPolynomial σ R) {f : σ → MvPolynomial τ S} {m : ℕ}
    (hf : ∀ i ∈ p.vars, (f i).totalDegree ≤ 1) (hp : p ∈ restrictTotalDegree σ R m) :
    aeval f p ∈ restrictTotalDegree τ S m := by
  rw [mem_restrictTotalDegree] at hp ⊢
  exact (totalDegree_aeval_le p hf).trans ((mul_one _).trans_le hp)

/-- Discarding variables outside the range of an injective renaming does not raise the total
degree. -/
theorem killCompl_mem_restrictTotalDegree {τ : Type*} {g : τ → σ} (hg : Function.Injective g)
    {m : ℕ} {f : MvPolynomial σ R} (hf : f ∈ restrictTotalDegree σ R m) :
    killCompl hg f ∈ restrictTotalDegree τ R m := by
  classical
  rw [killCompl_eq_aeval]
  refine aeval_mem_restrictTotalDegree f (fun j _ ↦ ?_) hf
  by_cases hj : j ∈ Set.range g
  · obtain ⟨i, rfl⟩ := hj
    rw [hg.extend_apply]
    exact TauCeti.totalDegree_X_le i
  · rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply, totalDegree_zero]
    exact Nat.zero_le _

/-- The bounded hyperplane slice map: restricts a polynomial of total degree at most `d + 1` and
its `j₀`-th partial derivative to the coordinate hyperplane `X j₀ = 0`, producing polynomials of
total degree at most `d + 1` and `d`, respectively, in the remaining variables. -/
noncomputable def hyperplaneSliceMap (j₀ : σ) (d : ℕ) :
    restrictTotalDegree σ R (d + 1) →ₗ[R]
      restrictTotalDegree {j : σ // j ≠ j₀} R (d + 1) ×
        restrictTotalDegree {j : σ // j ≠ j₀} R d where
  toFun f :=
    (⟨killCompl Subtype.val_injective f.val,
      killCompl_mem_restrictTotalDegree Subtype.val_injective f.property⟩,
     ⟨killCompl Subtype.val_injective (pderiv j₀ f.val),
      killCompl_mem_restrictTotalDegree Subtype.val_injective <|
        (mem_restrictTotalDegree σ d _).2 <|
          (totalDegree_pderiv_le j₀ f.val).trans <|
            Nat.sub_le_of_le_add ((mem_restrictTotalDegree σ (d + 1) _).1 f.property)⟩)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- The first component of `hyperplaneSliceMap j₀ d f` is the restriction of `f` to `X j₀ = 0`. -/
@[simp]
theorem hyperplaneSliceMap_fst_coe (j₀ : σ) (d : ℕ) (f : restrictTotalDegree σ R (d + 1)) :
    ((hyperplaneSliceMap (R := R) j₀ d f).1 : MvPolynomial {j : σ // j ≠ j₀} R) =
      killCompl Subtype.val_injective f.val := by
  simp [hyperplaneSliceMap]

/-- The second component of `hyperplaneSliceMap j₀ d f` is the restriction of `pderiv j₀ f` to
`X j₀ = 0`. -/
@[simp]
theorem hyperplaneSliceMap_snd_coe (j₀ : σ) (d : ℕ) (f : restrictTotalDegree σ R (d + 1)) :
    ((hyperplaneSliceMap (R := R) j₀ d f).2 : MvPolynomial {j : σ // j ≠ j₀} R) =
      killCompl Subtype.val_injective (pderiv j₀ f.val) := by
  simp [hyperplaneSliceMap]

/-- The bounded hyperplane slice map `hyperplaneSliceMap j₀ d` is surjective. -/
theorem hyperplaneSliceMap_surjective (j₀ : σ) (d : ℕ) :
    Function.Surjective (hyperplaneSliceMap (R := R) j₀ d) := by
  classical
  rintro ⟨g₀, g₁⟩
  let p : MvPolynomial σ R := rename Subtype.val g₀.val + X j₀ * rename Subtype.val g₁.val
  have hp : p ∈ restrictTotalDegree σ R (d + 1) := by
    rw [mem_restrictTotalDegree]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_rename_le Subtype.val g₀.val).trans
        ((mem_restrictTotalDegree {j : σ // j ≠ j₀} (d + 1) _).1 g₀.property)
    · refine (totalDegree_mul _ _).trans ?_
      have hX : (X j₀ : MvPolynomial σ R).totalDegree ≤ 1 :=
        (totalDegree_monomial_le _ _).trans_eq (by simp)
      have hg1 : (rename Subtype.val g₁.val).totalDegree ≤ d :=
        (totalDegree_rename_le Subtype.val g₁.val).trans
          ((mem_restrictTotalDegree {j : σ // j ≠ j₀} d _).1 g₁.property)
      omega
  refine ⟨⟨p, hp⟩, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · simp [p, killCompl_X_of_notMem_range]
  · simp [p, pderiv_rename_of_notMem_range]

/-- Changing coefficients along a ring map preserves the total degree bound. -/
theorem map_mem_restrictTotalDegree {S : Type*} [CommSemiring S] (φ : R →+* S)
    {m : ℕ} {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R m) :
    map φ p ∈ restrictTotalDegree σ S m := by
  rw [restrictTotalDegree_eq_restrictSupport] at hp ⊢
  exact map_mem_restrictSupport φ hp

variable (σ) in
/-- Changing the coefficients of polynomials of total degree at most `m` along a ring map
`φ : R →+* S`, as a `φ`-semilinear map. -/
noncomputable def mapRestrictTotalDegree {S : Type*} [CommSemiring S] (φ : R →+* S) (m : ℕ) :
    restrictTotalDegree σ R m →ₛₗ[φ] restrictTotalDegree σ S m :=
  (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ S m).symm).toLinearMap.comp
    ((mapRestrictSupport {s : σ →₀ ℕ | s.degree ≤ m} φ).comp
      (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m)).toLinearMap)

/-- The underlying polynomial of `mapRestrictTotalDegree σ φ m p` is `map φ p`. -/
@[simp]
theorem coe_mapRestrictTotalDegree_apply {S : Type*} [CommSemiring S] (φ : R →+* S) (m : ℕ)
    (p : restrictTotalDegree σ R m) :
    (mapRestrictTotalDegree σ φ m p : MvPolynomial σ S) = map φ p := by
  simp [mapRestrictTotalDegree, coe_mapRestrictSupport_apply]

/-- An element of `restrictTotalDegree σ R (d + 1)` lies in the kernel of `hyperplaneSliceMap j₀ d`
if and only if `X j₀ ^ 2` divides it. -/
theorem mem_ker_hyperplaneSliceMap {j₀ : σ} {d : ℕ} {f : restrictTotalDegree σ R (d + 1)} :
    f ∈ LinearMap.ker (hyperplaneSliceMap (R := R) j₀ d) ↔
      X j₀ ^ 2 ∣ (f : MvPolynomial σ R) := by
  classical
  have hrange : Set.range (Subtype.val : {j : σ // j ≠ j₀} → σ) = {j₀}ᶜ := by
    ext j
    simp
  have hX : killCompl (R := R) (Subtype.val_injective (p := (· ≠ j₀))) (X j₀) = 0 :=
    killCompl_X_of_notMem_range Subtype.val_injective (by simp)
  simp only [LinearMap.mem_ker, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Subtype.ext_iff,
    hyperplaneSliceMap_fst_coe, hyperplaneSliceMap_snd_coe, Submodule.coe_zero]
  constructor
  · rintro ⟨h0, h1⟩
    -- Vanishing on `X j₀ = 0` yields `f = X j₀ * q`; then vanishing of `∂_{j₀} f` on `X j₀ = 0`
    -- reduces to `killCompl q = 0`, giving `X j₀ ∣ q`.
    obtain ⟨q, hq⟩ := (killCompl_eq_zero_iff_X_dvd Subtype.val_injective hrange f.val).1 h0
    have hpderiv : pderiv j₀ (f : MvPolynomial σ R) = X j₀ * pderiv j₀ q + q := by
      rw [hq, Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one, add_comm]
    rw [hpderiv, map_add, map_mul, hX, zero_mul, zero_add] at h1
    obtain ⟨r, hr⟩ := (killCompl_eq_zero_iff_X_dvd Subtype.val_injective hrange q).1 h1
    exact ⟨r, by rw [hq, hr, sq, mul_assoc]⟩
  · rintro ⟨r, hr⟩
    -- Both `f` and `∂_{j₀} f` are multiples of `X j₀`, so both vanish on `X j₀ = 0`.
    refine ⟨?_, ?_⟩
    · rw [hr, map_mul, map_pow, hX, zero_pow two_ne_zero, zero_mul]
    · have hpderiv : pderiv j₀ (f : MvPolynomial σ R) =
          X j₀ * (pderiv j₀ (X j₀ * r) + r) := by
        rw [hr, sq, mul_assoc, Derivation.leibniz, pderiv_X_self]
        simp [mul_add]
      rw [hpderiv, map_mul, hX, zero_mul]

/-- In one variable, `MvPolynomial.uniqueAlgEquiv` identifies the polynomials of total degree at
most `d` with `Polynomial.degreeLT R (d + 1)`. -/
noncomputable def restrictTotalDegreeEquivDegreeLT (σ R : Type*) [CommSemiring R] [Unique σ]
    (d : ℕ) :
    restrictTotalDegree σ R d ≃ₗ[R] Polynomial.degreeLT R (d + 1) :=
  (LinearEquiv.ofEq _ _ (by
    rw [restrictTotalDegree_eq_restrictSupport]
    congr 1
    ext μ
    simp [Finsupp.degree_eq_sum])).trans <|
    ((uniqueAlgEquiv R σ).toLinearEquiv.submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (map_restrictSupport_uniqueAlgEquiv (d + 1)))

@[simp]
theorem coe_restrictTotalDegreeEquivDegreeLT_apply [Unique σ] (d : ℕ)
    (f : restrictTotalDegree σ R d) :
    (restrictTotalDegreeEquivDegreeLT σ R d f : Polynomial R) = uniqueAlgEquiv R σ f.val := by
  simp [restrictTotalDegreeEquivDegreeLT]

/-- Setting the variable `none` to `1` and keeping the variables `some j` does not raise the total
degree. -/
theorem aeval_option_elim_one_X_mem_restrictTotalDegree {d : ℕ}
    {F : MvPolynomial (Option σ) R} (hF : F ∈ restrictTotalDegree (Option σ) R d) :
    aeval (Option.elim' 1 X) F ∈ restrictTotalDegree σ R d := by
  refine aeval_mem_restrictTotalDegree F (fun v _ ↦ ?_) hF
  cases v
  · simp
  · exact TauCeti.totalDegree_X_le _

open Polynomial in
/-- If each `q k` with `k ≤ m` is a combination of the `p j` with `j ≤ k`, then the products
`∏ᵢ q_{τ i}(Xᵢ)` with `τ.degree ≤ m` lie in the span of the products `∏ᵢ p_{τ i}(Xᵢ)` with
`τ.degree ≤ m`. -/
theorem span_prod_aeval_X_le {σ R : Type*} [Fintype σ] [CommSemiring R] {p q : ℕ → R[X]} {m : ℕ}
    (h : ∀ k ≤ m, q k ∈ Submodule.span R (p '' Set.Iic k)) :
    Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i))) ''
        {τ | τ.degree ≤ m}) ≤
      Submodule.span R ((fun τ : σ →₀ ℕ ↦ ∏ i, Polynomial.aeval (X (R := R) i) (p (τ i))) ''
        {τ | τ.degree ≤ m}) := by
  classical
  rw [Submodule.span_le]
  rintro _ ⟨τ, hτ, rfl⟩
  -- Each factor lies in the span of the `p j (Xᵢ)` with `j ≤ τ i`.
  have hmem (i : σ) : Polynomial.aeval (X (R := R) i) (q (τ i)) ∈
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (h _ ((Finsupp.le_degree i τ).trans hτ))
  have hprod : ∏ i, Polynomial.aeval (X (R := R) i) (q (τ i)) ∈ ∏ i,
      Submodule.span R ((Polynomial.aeval (X (R := R) i)).toLinearMap '' (p '' Set.Iic (τ i))) := by
    induction (Finset.univ : Finset σ) using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact Submodule.one_le.1 le_rfl
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact Submodule.mul_mem_mul (hmem i) ih
  rw [Submodule.prod_span] at hprod
  refine Submodule.span_mono ?_ hprod
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hx
  simp only [Finset.mem_univ, forall_const, Set.image_image] at hg
  choose j hj hgj using fun i ↦ @hg i
  refine ⟨Finsupp.equivFunOnFinite.symm j, ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_le_sum fun i _ ↦ Set.mem_Iic.1 (hj i)).trans
      ((Finsupp.degree_eq_sum τ).symm.le.trans hτ)
  · simp [← hgj]

/-- **Restriction of polynomials to a subspace.** Over an infinite field, restricting the
polynomials of total degree at most `m` in the variables `σ` to a subspace `W` of `σ → K`, in
coordinates on `W`, is a linear map onto the polynomials of total degree at most `m` in `dim W`
variables whose kernel consists of the polynomials vanishing on `W`. -/
theorem _root_.Submodule.exists_surjective_linearMap_restrictTotalDegree [Finite σ] {K : Type*}
    [Field K] [Infinite K] (W : Submodule K (σ → K)) (m : ℕ) :
    ∃ R : restrictTotalDegree σ K m →ₗ[K] restrictTotalDegree (Fin (Module.finrank K W)) K m,
      Function.Surjective R ∧ ∀ p, R p = 0 ↔ ∀ w ∈ W, eval w (p : MvPolynomial σ K) = 0 := by
  classical
  have := Fintype.ofFinite σ
  -- Coordinates `g : Kᵈ ≃ W` on `W`, a linear left inverse `π` of `g`, and the restriction
  -- `R : p ↦ p ∘ g`, which is onto with right inverse `q ↦ q ∘ π`.
  let g : (Fin (Module.finrank K W) → K) →ₗ[K] σ → K :=
    W.subtype ∘ₗ (Module.finBasis K W).equivFun.symm.toLinearMap
  have hg : LinearMap.ker g = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp (Module.finBasis K W).equivFun.symm.injective
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective g hg
  let R : restrictTotalDegree σ K m →ₗ[K] restrictTotalDegree (Fin (Module.finrank K W)) K m :=
    (aeval (LinearMap.toMatrix' g).toMvPolynomial).toLinearMap.restrict fun p hp ↦
      aeval_mem_restrictTotalDegree p (fun i _ ↦ Matrix.toMvPolynomial_totalDegree_le _ i) hp
  have hR (p : restrictTotalDegree σ K m) (x : Fin (Module.finrank K W) → K) :
      eval x (R p : MvPolynomial _ K) = eval (g x) (p : MvPolynomial σ K) := by
    have hcoe : (R p : MvPolynomial _ K) =
        aeval (LinearMap.toMatrix' g).toMvPolynomial (p : MvPolynomial σ K) :=
      LinearMap.coe_restrict_apply _ p
    rw [hcoe, Matrix.eval_aeval_toMvPolynomial, LinearMap.toMatrix'_mulVec]
  refine ⟨R, ?_, fun p ↦ ⟨fun h w hw ↦ ?_, fun h ↦ Subtype.ext (funext fun x ↦ ?_)⟩⟩
  · rintro ⟨q, hq⟩
    refine ⟨⟨aeval (LinearMap.toMatrix' π).toMvPolynomial q, aeval_mem_restrictTotalDegree q
      (fun i _ ↦ Matrix.toMvPolynomial_totalDegree_le _ i) hq⟩, Subtype.ext (funext fun x ↦ ?_)⟩
    rw [hR, Matrix.eval_aeval_toMvPolynomial, LinearMap.toMatrix'_mulVec,
      ← LinearMap.comp_apply, hπ, LinearMap.id_apply]
  · have hw' : g ((Module.finBasis K W).equivFun ⟨w, hw⟩) = w := by simp [g]
    rw [← hw', ← hR, h, ZeroMemClass.coe_zero, map_zero]
  · rw [hR, ZeroMemClass.coe_zero, map_zero]
    exact h _ ((Module.finBasis K W).equivFun.symm x).property

end MvPolynomial

namespace Polynomial.Sequence

open Submodule

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- **Change of basis to products of a polynomial sequence.** If the leading coefficients of
`S₀, …, Sₘ` are units, then the products `∏ᵢ S_{τ i}(Xᵢ)` over the exponents `τ` of degree at
most `m` span the polynomials of total degree at most `m`, exactly as the monomials `X^τ` do. -/
theorem span_prod_aeval_X_eq_restrictTotalDegree (S : Sequence R) {m : ℕ}
    (hS : ∀ k ≤ m, IsUnit (S k).leadingCoeff) :
    span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) (S (τ i))) ''
        {τ | τ.degree ≤ m}) = MvPolynomial.restrictTotalDegree σ R m := by
  classical
  have hmon : MvPolynomial.restrictTotalDegree σ R m =
      span R ((fun τ : σ →₀ ℕ ↦ ∏ i, aeval (MvPolynomial.X (R := R) i) ((X : R[X]) ^ (τ i))) ''
        {τ | τ.degree ≤ m}) := by
    rw [MvPolynomial.restrictTotalDegree_eq_span]
    congr! with τ
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  rw [hmon]
  refine le_antisymm (MvPolynomial.span_prod_aeval_X_le fun k _ ↦ ?_)
    (MvPolynomial.span_prod_aeval_X_le fun k hk ↦ ?_)
  · have : S k ∈ degreeLE R k := mem_degreeLE.2 (S.degree_eq k).le
    rwa [degreeLE_eq_span_X_pow, Finset.coe_image, Finset.coe_range,
      Set.Iio_add_one_eq_Iic] at this
  · rw [S.span_degreeLE fun i hi ↦ hS i (hi.trans hk), mem_degreeLE]
    exact degree_X_pow_le k

end Polynomial.Sequence

namespace Module.Basis

open MvPolynomial

section Bilinear

variable {σ κ R L M : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]
  [AddCommMonoid M] [Module R M]

/-- A bilinear map out of a module and a polynomial algebra takes values in a submodule on
polynomials of total degree at most `d` if it does so on basis vectors and monomials of degree at
most `d`. -/
theorem apply_mem_of_monomial_degree_le (b : Basis κ R L)
    (Φ : L →ₗ[R] MvPolynomial σ R →ₗ[R] M) (N : Submodule R M) (d : ℕ)
    (h : ∀ (l : κ) (s : σ →₀ ℕ), s.degree ≤ d → Φ (b l) (monomial s 1) ∈ N)
    (x : L) {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R d) : Φ x p ∈ N := by
  have hle : Submodule.map₂ Φ (Submodule.span R (Set.range b))
      (Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ d})) ≤ N := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact h l s hs
  rw [b.span_eq, ← restrictTotalDegree_eq_span] at hle
  exact Submodule.map₂_le.1 hle x Submodule.mem_top p hp

end Bilinear

variable {ι R L : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- Multiplying by the linear form attached to `x` in the basis `b` raises total degree by at
most one. -/
theorem constr_X_mul_mem_restrictTotalDegree (b : Basis ι R L) {d : ℕ} (x : L)
    {p : MvPolynomial ι R} (hp : p ∈ restrictTotalDegree ι R d) :
    b.constr R X x * p ∈ restrictTotalDegree ι R (d + 1) := by
  refine b.apply_mem_of_monomial_degree_le
    ((LinearMap.mul R _).comp (b.constr R X)) _ d (fun l σ hσ ↦ ?_) x hp
  have hm : (monomial (Finsupp.single l 1 + σ) 1 : MvPolynomial ι R) ∈
      restrictTotalDegree ι R (d + 1) :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  simpa [monomial_single_add] using hm

end Module.Basis
