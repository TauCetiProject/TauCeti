/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.CharTwo
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The Arf invariant and classification of nonsingular quadratic forms over `𝔽₂`

Let `V` be a finite-dimensional vector space over `ZMod 2` equipped with a quadratic form
`Q : QuadraticForm (ZMod 2) V` whose polarization `Q.polarBilin` is nondegenerate. By
`QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`, `V` has even dimension `2 * m` and admits a
symplectic basis `b : Basis (Fin m ⊕ Fin m) (ZMod 2) V` in which `Q.polarBilin` has matrix
`Matrix.J (Fin m) (ZMod 2)`.

Cahit Arf observed in 1941 that the element
`∑ i, Q (b (inl i)) * Q (b (inr i)) : ZMod 2`
is independent of the choice of symplectic basis `b`. Over `ZMod 2`, the cleanest proof is the
Gauss-sum / voting argument: in any symplectic basis `b` indexed by `ι ⊕ ι`, `Q` decomposes
orthogonally into binary planes `symplecticPlane (Q (b (inl i))) (Q (b (inr i)))`, each plane
`[a, b]` has Gauss sum `(-1) ^ (a * b).val * 2`, and therefore
`∑ v : V, (-1 : ℤ) ^ (Q v).val = (-1) ^ (∑ i, Q (b (inl i)) * Q (b (inr i))).val * 2 ^ |ι|`.
Because the left-hand side depends only on `Q`, cancelling `2 ^ |ι|` shows that every symplectic
basis yields the same Arf sum, and simultaneously counts the isotropic vectors:
`#{v : V | Q v = 0} = 2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)` for `m ≥ 1` (and `1` when
`m = 0`). In particular, `Q.arf = 0` if and only if `Q` takes the value `0` strictly more often
than `1`.

Using the plane isometries `[a, b] ≃qᵢ [a * b, a * b]` over `ZMod 2` and
`[0, 0] ⊕ [0, 0] ≃qᵢ [1, 1] ⊕ [1, 1]`, every nonsingular quadratic space of dimension `2 * m` is
isometric to the canonical model `TauCeti.arfNormalForm m Q.arf` (all `[0, 0]` planes when
`Q.arf = 0`, and one anisotropic `[1, 1]` plane orthogonal-summed with `m - 1` split `[0, 0]`
planes when `Q.arf = 1`). Consequently two finite-dimensional `ZMod 2`-quadratic forms with
nondegenerate polar forms are isometric if and only if they have the same dimension and the same
Arf invariant (`QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`), and `Q.arf = 0` if and only
if `V` contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement, or
equivalently of half the ambient dimension.

## Main definitions

* `QuadraticMap.gaussSum`: the Gauss sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of a `ZMod 2`-quadratic
  form on a finite module.
* `TauCeti.isometryEquivSymplecticPlaneZModTwo`: over `ZMod 2`, `symplecticPlane a b` is isometric
  to `symplecticPlane (a * b) (a * b)`.
* `QuadraticMap.arf`: the Arf invariant in `ZMod 2` of a `ZMod 2`-quadratic form (`0` outside the
  finite-dimensional polar-nondegenerate regime).
* `TauCeti.arfNormalForm`: the canonical `2 * m`-dimensional nonsingular `ZMod 2`-quadratic form of
  Arf invariant `c`.
* `TauCeti.isometryEquivPiSymplecticPlaneArfNormalForm` and
  `QuadraticMap.isometryEquivArfNormalForm`: the reduction of a family of binary planes, and of any
  nonsingular `ZMod 2`-quadratic space, to `arfNormalForm`.

## Main results

* `QuadraticMap.two_mul_card_filter_apply_eq_zero`: `2 * #{v | Q v = 0} = |V| + Q.gaussSum`.
* `QuadraticMap.gaussSum_eq_of_toMatrix_polarBilin_eq_J` and
  `QuadraticMap.sum_mul_eq_of_toMatrix_polarBilin_eq_J`: Gauss-sum evaluation in a symplectic basis
  and symplectic-basis independence of the Arf sum.
* `QuadraticMap.IsometryEquiv.arf_eq`, `QuadraticMap.arf_prod`, `QuadraticMap.arf_pi`, and
  `QuadraticMap.arf_eq_add_arf_restrict_orthogonal`: invariance under isometries and additivity
  under external and internal orthogonal direct sums.
* `QuadraticMap.gaussSum_eq_of_nondegenerate_polarBilin`,
  `QuadraticMap.card_filter_apply_eq_zero_of_nondegenerate_polarBilin`, and
  `QuadraticMap.arf_eq_zero_iff_card_lt_two_mul_card_filter_apply_eq_zero`: the Gauss sum,
  zero-count formula, and majority-vote characterization of `Q.arf = 0`.
* `QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`: Arf's classification theorem over `ZMod 2`.
* `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_eq_orthogonal` and
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq`: `Q.arf = 0` if and
  only if `V` admits a `Q`-totally-isotropic polar-Lagrangian (half-dimensional) subspace.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* E. H. Brown Jr., *Generalizations of the Kervaire invariant*, Ann. of Math. (2) 95 (1972),
  368–383.
* J. Milnor, D. Husemöller, *Symmetric Bilinear Forms* (1973), Appendix 4.
* A. Pyronneau, *Invariant d'Arf et surface de genre g* (2024), §2.1, Lemmas 2.11–2.13,
  Corollary 2.14, Theorem 2.15.
-/

public section

open QuadraticMap

private def isometryEquivOfEq {R M P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid P] [Module R P] {Q₁ Q₂ : QuadraticMap R M P} (h : Q₁ = Q₂) :
    Q₁.IsometryEquiv Q₂ where
  toLinearEquiv := LinearEquiv.refl R M
  map_app' x := by simp [h]

private theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

private theorem nondegenerate_polarBilin_prod_iff
    {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} :
    (Q₁.prod Q₂).polarBilin.Nondegenerate ↔
      Q₁.polarBilin.Nondegenerate ∧ Q₂.polarBilin.Nondegenerate := by
  have heq : (Q₁.prod Q₂).polarBilin = LinearMap.BilinForm.prod Q₁.polarBilin Q₂.polarBilin :=
    LinearMap.ext fun ⟨x₁, x₂⟩ => LinearMap.ext fun ⟨y₁, y₂⟩ => by simp
  rw [heq]
  exact LinearMap.BilinForm.nondegenerate_prod_iff

private theorem nondegenerate_polarBilin_pi_iff {R ι : Type*} [CommRing R] [Fintype ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {Q : ∀ i, QuadraticForm R (M i)} :
    (QuadraticMap.pi Q).polarBilin.Nondegenerate ↔ ∀ i, (Q i).polarBilin.Nondegenerate := by
  simp only [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (QuadraticMap.pi Q).isSymm_polarBilin.isRefl,
    fun i => LinearMap.IsRefl.nondegenerate_iff_separatingLeft (Q i).isSymm_polarBilin.isRefl,
    LinearMap.SeparatingLeft, polarBilin_apply_apply]
  constructor
  · intro h i xi hxi
    classical
    have h0 : Pi.single i xi = 0 := h (Pi.single i xi) fun y => by
      rw [QuadraticMap.Ring.polar_pi, Finset.sum_eq_single i]
      · simpa using hxi (y i)
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    simpa using congrFun h0 i
  · intro h x hx
    classical
    ext i
    exact h i (x i) fun yi => by
      have hsum := hx (Pi.single i yi)
      rw [QuadraticMap.Ring.polar_pi, Finset.sum_eq_single i] at hsum
      · simpa using hsum
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp

namespace QuadraticMap

section GaussSum

private theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℤ) ^ (a + b).val = (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ b.val := by
  fin_cases a <;> fin_cases b <;> rfl

private theorem prod_neg_one_pow_val {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (∏ i ∈ s, (-1 : ℤ) ^ (f i).val) = (-1 : ℤ) ^ (∑ i ∈ s, f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert _ _ ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, neg_one_pow_val_add, ih]

private theorem eq_of_neg_one_pow_val_eq {a b : ZMod 2}
    (h : (-1 : ℤ) ^ a.val = (-1 : ℤ) ^ b.val) : a = b := by
  revert a b h
  decide

private theorem one_add_neg_one_pow_val (a : ZMod 2) :
    (1 : ℤ) + (-1 : ℤ) ^ a.val = if a = 0 then 2 else 0 := by
  fin_cases a <;> rfl

variable {V W : Type*} [AddCommMonoid V] [Module (ZMod 2) V] [AddCommMonoid W] [Module (ZMod 2) W]

/-- The Gauss sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of a quadratic form over `ZMod 2` on a finite
module `V`. -/
def gaussSum [Fintype V] (Q : QuadraticForm (ZMod 2) V) : ℤ :=
  ∑ v : V, (-1 : ℤ) ^ (Q v).val

/-- Unfolds `QuadraticMap.gaussSum`. -/
theorem gaussSum_def [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val :=
  (rfl)

/-- The Gauss sum of the zero quadratic form is the cardinality of the ambient module. -/
@[simp]
theorem gaussSum_zero [Fintype V] :
    (0 : QuadraticForm (ZMod 2) V).gaussSum = Fintype.card V := by
  simp [gaussSum_def]

/-- On a subsingleton module, every `ZMod 2`-quadratic form has Gauss sum `1`. -/
@[simp]
theorem gaussSum_of_subsingleton [Fintype V] [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = 1 := by
  have : Unique V := uniqueOfSubsingleton (0 : V)
  rw [gaussSum_def, Finset.univ_unique, Finset.sum_singleton, Subsingleton.elim default (0 : V),
    map_zero, ZMod.val_zero, pow_zero]

/-- Isometric `ZMod 2`-quadratic forms have equal Gauss sums. -/
theorem IsometryEquiv.gaussSum_eq [Fintype V] [Fintype W]
    {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.gaussSum = Q₂.gaussSum := by
  rw [gaussSum_def, gaussSum_def]
  exact Fintype.sum_equiv e.toEquiv _ _ fun v => by rw [← e.map_app]; rfl

/-- Equivalent `ZMod 2`-quadratic forms have equal Gauss sums. -/
theorem Equivalent.gaussSum_eq [Fintype V] [Fintype W]
    {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (h : Q₁.Equivalent Q₂) : Q₁.gaussSum = Q₂.gaussSum :=
  let ⟨e⟩ := h
  e.gaussSum_eq

/-- The Gauss sum of an orthogonal product is the product of the Gauss sums. -/
@[simp]
theorem gaussSum_prod [Fintype V] [Fintype W]
    (Q₁ : QuadraticForm (ZMod 2) V) (Q₂ : QuadraticForm (ZMod 2) W) :
    (Q₁.prod Q₂).gaussSum = Q₁.gaussSum * Q₂.gaussSum := by
  rw [gaussSum_def, Fintype.sum_prod_type]
  simp_rw [QuadraticMap.prod_apply, neg_one_pow_val_add, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

/-- The Gauss sum of a finite orthogonal family is the product of the component Gauss sums. -/
@[simp]
theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, Fintype (M i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (M i)) :
    (QuadraticMap.pi Q).gaussSum = ∏ i : ι, (Q i).gaussSum := by
  simp_rw [gaussSum_def]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pi_apply, ← prod_neg_one_pow_val]

/-- Twice the number of zeros of `Q : QuadraticForm (ZMod 2) V` equals `|V| + Q.gaussSum`. -/
theorem two_mul_card_filter_apply_eq_zero [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    2 * ((Finset.univ.filter fun v : V => Q v = 0).card : ℤ) =
      Fintype.card V + Q.gaussSum := by
  have hsum : ∑ v : V, ((1 : ℤ) + (-1 : ℤ) ^ (Q v).val) = Fintype.card V + Q.gaussSum := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_one, gaussSum_def]
  rw [← hsum]
  simp only [one_add_neg_one_pow_val, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

/-- Twice `Nat.card {v : V // Q v = 0}` equals `|V| + Q.gaussSum`. -/
theorem two_mul_natCard_apply_eq_zero [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    2 * (Nat.card {v : V // Q v = 0} : ℤ) = Fintype.card V + Q.gaussSum := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, two_mul_card_filter_apply_eq_zero]

/-- On `ZMod 2`, the binary plane `symplecticPlane a b` has Gauss sum `(-1) ^ (a * b).val * 2`. -/
@[simp]
theorem gaussSum_symplecticPlane (a b : ZMod 2) :
    (TauCeti.symplecticPlane a b).gaussSum = (-1 : ℤ) ^ (a * b).val * 2 := by
  rw [gaussSum_def, Fintype.sum_equiv (finTwoArrowEquiv (ZMod 2)) _
    (fun p : ZMod 2 × ZMod 2 => (-1 : ℤ) ^ (TauCeti.symplecticPlane a b ![p.1, p.2]).val)
    fun x => congrArg (fun y => (-1 : ℤ) ^ (TauCeti.symplecticPlane a b y).val)
      (funext fun i => by fin_cases i <;> rfl)]
  simp only [TauCeti.symplecticPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  revert a b
  decide

/-- On a subsingleton module, the zero locus `{v : V | Q v = 0}` has cardinality `1`. -/
@[simp]
theorem card_filter_apply_eq_zero_of_subsingleton [Fintype V] [Subsingleton V]
    (Q : QuadraticForm (ZMod 2) V) :
    (Finset.univ.filter fun v : V => Q v = 0).card = 1 := by
  have : Unique V := uniqueOfSubsingleton (0 : V)
  have h0 : Q default = 0 := by rw [Subsingleton.elim default (0 : V), map_zero]
  simp [Finset.univ_unique, Finset.filter_singleton, h0]

end GaussSum

end QuadraticMap

namespace TauCeti

/-- Over `ZMod 2`, the binary plane `symplecticPlane a b` is isometric to
`symplecticPlane (a * b) (a * b)`: it is `[0, 0]` whenever `a = 0` or `b = 0`, and `[1, 1]` when
`a = b = 1`. -/
def isometryEquivSymplecticPlaneZModTwo (a b : ZMod 2) :
    (symplecticPlane a b).IsometryEquiv (symplecticPlane (a * b) (a * b)) :=
  if ha : a = 0 then
    (isometryEquivOfEq (by rw [ha])).trans
      ((isometryEquivSymplecticPlaneZeroLeft b).trans
        (isometryEquivOfEq (by rw [ha, zero_mul])))
  else if hb : b = 0 then
    (isometryEquivOfEq (by rw [hb])).trans
      ((isometryEquivSymplecticPlaneZeroRight a).trans
        (isometryEquivOfEq (by rw [hb, mul_zero])))
  else
    isometryEquivOfEq (by
      rw [zmod_two_eq_one_of_ne_zero ha, zmod_two_eq_one_of_ne_zero hb, mul_one])

/-- Over `ZMod 2`, `symplecticPlane a b` is anisotropic if and only if `a = 1` and `b = 1`. -/
@[simp]
theorem anisotropic_symplecticPlane_iff (a b : ZMod 2) :
    (symplecticPlane a b).Anisotropic ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have ha0 : a ≠ 0 := fun ha => by
      have h0 : ![(1 : ZMod 2), 0] = 0 := h ![1, 0] (by simp [ha])
      exact one_ne_zero (congrFun h0 0)
    have hb0 : b ≠ 0 := fun hb => by
      have h0 : ![(0 : ZMod 2), 1] = 0 := h ![0, 1] (by simp [hb])
      exact one_ne_zero (congrFun h0 1)
    exact ⟨zmod_two_eq_one_of_ne_zero ha0, zmod_two_eq_one_of_ne_zero hb0⟩
  · rintro ⟨rfl, rfl⟩ x hx
    rcases eq_or_ne (x 0) 0 with h0 | h0 <;> rcases eq_or_ne (x 1) 0 with h1 | h1
    · ext i
      fin_cases i <;> simp [h0, h1]
    · rw [symplecticPlane_apply, h0, zmod_two_eq_one_of_ne_zero h1] at hx
      norm_num at hx
    · rw [symplecticPlane_apply, zmod_two_eq_one_of_ne_zero h0, h1] at hx
      norm_num at hx
    · rw [symplecticPlane_apply, zmod_two_eq_one_of_ne_zero h0,
        zmod_two_eq_one_of_ne_zero h1] at hx
      exact False.elim ((by decide : (1 * 1 ^ 2 + 1 * 1 + 1 * 1 ^ 2 : ZMod 2) ≠ 0) hx)

/-- The binary plane `symplecticPlane 1 1` (`x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2`) over `ZMod 2` is
anisotropic. -/
theorem anisotropic_symplecticPlane_one_one :
    (symplecticPlane (1 : ZMod 2) 1).Anisotropic :=
  (anisotropic_symplecticPlane_iff 1 1).mpr ⟨rfl, rfl⟩

/-- Over `ZMod 2`, the orthogonal sum `(symplecticPlane x x).prod (symplecticPlane y y)` is
isometric to `(symplecticPlane (x + y) (x + y)).prod (symplecticPlane 0 0)`. -/
def isometryEquivSymplecticPlaneProdSelf (x y : ZMod 2) :
    ((symplecticPlane x x).prod (symplecticPlane y y)).IsometryEquiv
      ((symplecticPlane (x + y) (x + y)).prod (symplecticPlane 0 0)) :=
  if hx : x = 0 then
    if hy : y = 0 then
      isometryEquivOfEq (by rw [hx, hy, add_zero])
    else
      (IsometryEquiv.prodComm _ _).trans (isometryEquivOfEq (by rw [hx, zero_add]))
  else
    if hy : y = 0 then
      isometryEquivOfEq (by rw [hy, add_zero])
    else
      have hx1 : x = 1 := zmod_two_eq_one_of_ne_zero hx
      have hy1 : y = 1 := zmod_two_eq_one_of_ne_zero hy
      (isometryEquivOfEq (by rw [hx1, hy1])).trans
        (isometryEquivSymplecticPlaneOneOneProd.symm.trans
          (isometryEquivOfEq (by
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [hx1, hy1, h11])))

end TauCeti

namespace QuadraticMap

section Arf

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- In any basis `b : Basis (ι ⊕ ι) (ZMod 2) V` in which `Q.polarBilin` has matrix
`Matrix.J ι (ZMod 2)`, the Gauss sum of `Q` is
`(-1) ^ (∑ i, Q (b (inl i)) * Q (b (inr i))).val * 2 ^ |ι|`. -/
theorem gaussSum_eq_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] (Q : QuadraticForm (ZMod 2) V) (b : Module.Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.gaussSum =
      (-1 : ℤ) ^ (∑ i : ι, Q (b (.inl i)) * Q (b (.inr i))).val * (2 : ℤ) ^ Fintype.card ι := by
  rw [(TauCeti.isometryEquivPiSymplecticPlane Q b hb).symm.gaussSum_eq, gaussSum_pi]
  simp_rw [gaussSum_symplecticPlane]
  rw [Finset.prod_mul_distrib, prod_neg_one_pow_val, Finset.prod_const, Finset.card_univ]

/-- **Symplectic-basis independence of the Arf sum**: any two symplectic bases of `Q.polarBilin`
yield the same sum `∑ i, Q (b (inl i)) * Q (b (inr i))` in `ZMod 2`. -/
theorem sum_mul_eq_of_toMatrix_polarBilin_eq_J {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Q : QuadraticForm (ZMod 2) V)
    (b : Module.Basis (ι ⊕ ι) (ZMod 2) V) (c : Module.Basis (κ ⊕ κ) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2))
    (hc : LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J κ (ZMod 2)) :
    ∑ i : ι, Q (b (.inl i)) * Q (b (.inr i)) = ∑ k : κ, Q (c (.inl k)) * Q (c (.inr k)) := by
  let _ : Fintype V := Fintype.ofEquiv (ι ⊕ ι → ZMod 2) b.equivFun.symm.toEquiv
  have hcard2 : Fintype.card (ι ⊕ ι) = Fintype.card (κ ⊕ κ) :=
    Fintype.card_congr (b.indexEquiv c)
  have hcard : Fintype.card ι = Fintype.card κ := by
    simp only [Fintype.card_sum] at hcard2
    omega
  have hg :
      (-1 : ℤ) ^ (∑ i : ι, Q (b (.inl i)) * Q (b (.inr i))).val * (2 : ℤ) ^ Fintype.card ι =
      (-1 : ℤ) ^ (∑ k : κ, Q (c (.inl k)) * Q (c (.inr k))).val * (2 : ℤ) ^ Fintype.card ι := by
    rw [← gaussSum_eq_of_toMatrix_polarBilin_eq_J Q b hb,
      gaussSum_eq_of_toMatrix_polarBilin_eq_J Q c hc, hcard]
  exact eq_of_neg_one_pow_val_eq (mul_right_cancel₀ (pow_ne_zero _ (by decide)) hg)

/-- The **Arf invariant** of a quadratic form `Q` over `ZMod 2`. When `V` is finite-dimensional
and `Q.polarBilin` is nondegenerate, `Q.arf` is `∑ i, Q (b (inl i)) * Q (b (inr i))` in any
symplectic basis `b` of `Q.polarBilin`; outside that regime `Q.arf` is `0`. -/
noncomputable def arf (Q : QuadraticForm (ZMod 2) V) : ZMod 2 :=
  open scoped Classical in
  if h : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate then
    haveI : FiniteDimensional (ZMod 2) V := h.1
    let b := (Q.exists_basis_toMatrix_polarBilin_eq_J h.2).choose_spec.2.choose
    ∑ i, Q (b (.inl i)) * Q (b (.inr i))
  else 0

/-- In any basis `b : Basis (ι ⊕ ι) (ZMod 2) V` in which `Q.polarBilin` has matrix
`Matrix.J ι (ZMod 2)`, the Arf invariant `Q.arf` equals `∑ i, Q (b (inl i)) * Q (b (inr i))`. -/
theorem arf_eq_sum_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) V) (b : Module.Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.arf = ∑ i : ι, Q (b (.inl i)) * Q (b (.inr i)) := by
  classical
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis b
  have hnd : Q.polarBilin.Nondegenerate :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr
      (hb ▸ (Matrix.isUnit_det_J ι (ZMod 2)).ne_zero)
  have hcond : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate := ⟨hfin, hnd⟩
  simp only [arf, hcond]
  exact sum_mul_eq_of_toMatrix_polarBilin_eq_J Q _ b
    (Q.exists_basis_toMatrix_polarBilin_eq_J hnd).choose_spec.2.choose_spec hb

/-- The Arf invariant of the zero quadratic form is `0`. -/
@[simp]
theorem arf_zero : (0 : QuadraticForm (ZMod 2) V).arf = 0 := by
  classical
  simp [arf]

/-- Outside finite dimension, `QuadraticMap.arf` takes its junk value `0`. -/
theorem arf_of_not_finiteDimensional (Q : QuadraticForm (ZMod 2) V)
    (h : ¬FiniteDimensional (ZMod 2) V) : Q.arf = 0 := by
  classical
  simp [arf, h]

/-- When `Q.polarBilin` is degenerate, `QuadraticMap.arf` takes its junk value `0`. -/
theorem arf_of_not_nondegenerate_polarBilin (Q : QuadraticForm (ZMod 2) V)
    (h : ¬Q.polarBilin.Nondegenerate) : Q.arf = 0 := by
  classical
  simp [arf, h]

/-- On a subsingleton module, every `ZMod 2`-quadratic form has Arf invariant `0`. -/
@[simp]
theorem arf_of_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) : Q.arf = 0 := by
  let b : Module.Basis (Empty ⊕ Empty) (ZMod 2) V :=
    (Module.Basis.empty V).reindex (Equiv.sumEmpty Empty Empty).symm
  have hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J Empty (ZMod 2) := by
    ext x
    exact x.elim Empty.elim Empty.elim
  rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J Q b hb]
  rfl

private theorem IsometryEquiv.nondegenerate_polarBilin_iff
    {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (e : Q₁.IsometryEquiv Q₂) :
    Q₁.polarBilin.Nondegenerate ↔ Q₂.polarBilin.Nondegenerate := by
  simp only [LinearMap.IsRefl.nondegenerate_iff_separatingLeft Q₁.isSymm_polarBilin.isRefl,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft Q₂.isSymm_polarBilin.isRefl,
    LinearMap.SeparatingLeft, polarBilin_apply_apply]
  constructor
  · intro h y hy
    have hx : e.symm y = 0 := h (e.symm y) fun x => by
      rw [← e.polar_apply, e.apply_symm_apply]
      exact hy (e x)
    simpa using congrArg e hx
  · intro h x hx
    have hy : e x = 0 := h (e x) fun y => by
      rw [← e.symm.polar_apply, e.symm_apply_apply]
      exact hx (e.symm y)
    simpa using congrArg e.symm hy

/-- Isometric `ZMod 2`-quadratic forms have the same Arf invariant. -/
theorem IsometryEquiv.arf_eq {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.arf = Q₂.arf := by
  classical
  have hcond : (FiniteDimensional (ZMod 2) V ∧ Q₁.polarBilin.Nondegenerate) ↔
      (FiniteDimensional (ZMod 2) W ∧ Q₂.polarBilin.Nondegenerate) :=
    ⟨fun ⟨hf, hnd⟩ =>
      have : FiniteDimensional (ZMod 2) V := hf
      ⟨Module.Finite.equiv e.toLinearEquiv, e.nondegenerate_polarBilin_iff.mp hnd⟩,
     fun ⟨hf, hnd⟩ =>
      have : FiniteDimensional (ZMod 2) W := hf
      ⟨Module.Finite.equiv e.symm.toLinearEquiv, e.nondegenerate_polarBilin_iff.mpr hnd⟩⟩
  by_cases h : FiniteDimensional (ZMod 2) V ∧ Q₁.polarBilin.Nondegenerate
  · obtain ⟨hfin, hnd⟩ := h
    obtain ⟨m, -, b, hb⟩ := Q₁.exists_basis_toMatrix_polarBilin_eq_J hnd
    let b' : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) W := b.map e.toLinearEquiv
    have hb' : LinearMap.BilinForm.toMatrix b' Q₂.polarBilin = Matrix.J (Fin m) (ZMod 2) := by
      ext x y
      simp only [b', LinearMap.BilinForm.toMatrix_apply, Module.Basis.map_apply,
        polarBilin_apply_apply]
      change polar Q₂ (e (b x)) (e (b y)) = _
      rw [e.polar_apply, ← polarBilin_apply_apply, ← LinearMap.BilinForm.toMatrix_apply, hb]
    rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J Q₁ b hb,
      arf_eq_sum_of_toMatrix_polarBilin_eq_J Q₂ b' hb']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [b', Module.Basis.map_apply]
    change _ = Q₂ (e (b (.inl i))) * Q₂ (e (b (.inr i)))
    rw [e.map_app, e.map_app]
  · have h' : ¬(FiniteDimensional (ZMod 2) W ∧ Q₂.polarBilin.Nondegenerate) := mt hcond.mpr h
    simp [arf, h, h']

/-- Equivalent `ZMod 2`-quadratic forms have the same Arf invariant. -/
theorem Equivalent.arf_eq {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (h : Q₁.Equivalent Q₂) : Q₁.arf = Q₂.arf :=
  let ⟨e⟩ := h
  e.arf_eq

/-- The Arf invariant of `TauCeti.symplecticPlane a b` over `ZMod 2` is `a * b`. -/
@[simp]
theorem arf_symplecticPlane (a b : ZMod 2) :
    (TauCeti.symplecticPlane a b).arf = a * b := by
  let σ : Fin 2 ≃ Unit ⊕ Unit :=
    { toFun := ![.inl (), .inr ()]
      invFun := Sum.elim (fun _ => 0) (fun _ => 1)
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun s => by rcases s with ⟨⟩ | ⟨⟩ <;> rfl }
  let c : Module.Basis (Unit ⊕ Unit) (ZMod 2) (Fin 2 → ZMod 2) :=
    (Pi.basisFun (ZMod 2) (Fin 2)).reindex σ
  have hc0 : c (.inl ()) = ![1, 0] := by
    ext i
    fin_cases i <;> simp [c, σ]
  have hc1 : c (.inr ()) = ![0, 1] := by
    ext i
    fin_cases i <;> simp [c, σ]
  have hc : LinearMap.BilinForm.toMatrix c (TauCeti.symplecticPlane a b).polarBilin =
      Matrix.J Unit (ZMod 2) := by
    rw [toMatrix_polarBilin_eq_J_iff]
    refine ⟨fun ⟨⟩ ⟨⟩ => polar_self_of_charTwo _ _, fun ⟨⟩ ⟨⟩ => polar_self_of_charTwo _ _,
      fun ⟨⟩ ⟨⟩ => by simp [hc0, hc1]⟩
  rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J _ c hc, Finset.univ_unique, Finset.sum_singleton]
  change TauCeti.symplecticPlane a b (c (.inl ())) *
    TauCeti.symplecticPlane a b (c (.inr ())) = a * b
  simp [hc0, hc1]

/-- The Arf invariant is additive under orthogonal product of finite-dimensional
polar-nondegenerate `ZMod 2`-quadratic spaces. -/
theorem arf_prod [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf := by
  obtain ⟨m₁, -, b₁, hb₁⟩ := Q₁.exists_basis_toMatrix_polarBilin_eq_J hQ₁
  obtain ⟨m₂, -, b₂, hb₂⟩ := Q₂.exists_basis_toMatrix_polarBilin_eq_J hQ₂
  obtain ⟨hll₁, hrr₁, hlr₁⟩ := (Q₁.toMatrix_polarBilin_eq_J_iff b₁).mp hb₁
  obtain ⟨hll₂, hrr₂, hlr₂⟩ := (Q₂.toMatrix_polarBilin_eq_J_iff b₂).mp hb₂
  let b : Module.Basis ((Fin m₁ ⊕ Fin m₂) ⊕ (Fin m₁ ⊕ Fin m₂)) (ZMod 2) (V × W) :=
    (b₁.prod b₂).reindex (Equiv.sumSumSumComm (Fin m₁) (Fin m₁) (Fin m₂) (Fin m₂))
  have hb : LinearMap.BilinForm.toMatrix b (Q₁.prod Q₂).polarBilin =
      Matrix.J (Fin m₁ ⊕ Fin m₂) (ZMod 2) := by
    rw [toMatrix_polarBilin_eq_J_iff]
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rcases i with i | i <;> rcases j with j | j <;>
        simp [b, polar_prod, hll₁, hll₂]
    · rcases i with i | i <;> rcases j with j | j <;>
        simp [b, polar_prod, hrr₁, hrr₂]
    · rcases i with i | i <;> rcases j with j | j <;>
        simp [b, polar_prod, hlr₁, hlr₂]
  rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J _ b hb, Fintype.sum_sum_type,
    arf_eq_sum_of_toMatrix_polarBilin_eq_J Q₁ b₁ hb₁,
    arf_eq_sum_of_toMatrix_polarBilin_eq_J Q₂ b₂ hb₂]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [b]

/-- The Arf invariant is additive across any finite orthogonal family of finite-dimensional
polar-nondegenerate `ZMod 2`-quadratic spaces. -/
theorem arf_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    [∀ i, FiniteDimensional (ZMod 2) (M i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i : ι, (Q i).arf := by
  have hfin : ∀ (n : ℕ) (M : Fin n → Type _) [∀ i, AddCommGroup (M i)]
      [∀ i, Module (ZMod 2) (M i)] [∀ i, FiniteDimensional (ZMod 2) (M i)]
      (Q : ∀ i, QuadraticForm (ZMod 2) (M i)),
      (∀ i, (Q i).polarBilin.Nondegenerate) →
      (QuadraticMap.pi Q).arf = ∑ i : Fin n, (Q i).arf := by
    intro n
    induction n with
    | zero =>
      intro M _ _ _ Q _
      simp
    | succ n ih =>
      intro M _ _ _ Q hQn
      rw [← (IsometryEquiv.consPi Q).arf_eq,
        arf_prod (hQn 0) (nondegenerate_polarBilin_pi_iff.mpr fun i => hQn i.succ),
        ih _ _ (fun i => hQn i.succ), Fin.sum_univ_succ]
  let e := (Fintype.equivFin ι).symm
  rw [← (IsometryEquiv.piCongrLeft Q e).arf_eq, hfin _ _ _ (fun j => hQ (e j))]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Along an internal polar-orthogonal direct-sum decomposition `V = U ⊕ U^⊥` of a
finite-dimensional nonsingular `ZMod 2`-quadratic space, the Arf invariant splits additively. -/
theorem arf_eq_add_arf_restrict_orthogonal [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (U : Submodule (ZMod 2) V)
    (hU : IsCompl U (LinearMap.BilinForm.orthogonal Q.polarBilin U)) :
    Q.arf = (Q.restrict U).arf +
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin U)).arf := by
  let e := IsometryEquiv.prodRestrictOrthogonal Q U hU
  obtain ⟨hnd₁, hnd₂⟩ := nondegenerate_polarBilin_prod_iff.mp
    (e.nondegenerate_polarBilin_iff.mpr hQ)
  rw [← e.arf_eq, arf_prod hnd₁ hnd₂]

/-- **Gauss-sum formula for the Arf invariant**: on a `2 * m`-dimensional `ZMod 2`-space with
nondegenerate polar form, `Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ m`. -/
theorem gaussSum_eq_of_nondegenerate_polarBilin [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 2 * m = Module.finrank (ZMod 2) V) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * (2 : ℤ) ^ m := by
  obtain ⟨m', hm', b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hm_eq : m' = m := by omega
  subst hm_eq
  rw [gaussSum_eq_of_toMatrix_polarBilin_eq_J Q b hb,
    arf_eq_sum_of_toMatrix_polarBilin_eq_J Q b hb, Fintype.card_fin]

/-- Dimension-free form of `QuadraticMap.gaussSum_eq_of_nondegenerate_polarBilin`:
`Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ (finrank V / 2)`. -/
theorem gaussSum_eq_arf [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * (2 : ℤ) ^ (Module.finrank (ZMod 2) V / 2) := by
  obtain ⟨m, hm⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).exists_two_nsmul
  have hm' : 2 * m = Module.finrank (ZMod 2) V := by simpa [two_mul] using hm.symm
  have hdiv : Module.finrank (ZMod 2) V / 2 = m := by omega
  rw [hdiv, gaussSum_eq_of_nondegenerate_polarBilin hQ hm']

/-- **Zero-count formula**: on a `2 * m`-dimensional `ZMod 2`-quadratic space (`1 ≤ m`) with
nondegenerate polar form,
`#{v : V | Q v = 0} = 2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)`. -/
theorem card_filter_apply_eq_zero_of_nondegenerate_polarBilin [Fintype V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {m : ℕ} (hm : 2 * m = Module.finrank (ZMod 2) V) (hm1 : 1 ≤ m) :
    ((Finset.univ.filter fun v : V => Q v = 0).card : ℤ) =
      (2 : ℤ) ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * (2 : ℤ) ^ (m - 1) := by
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  rw [two_mul_card_filter_apply_eq_zero, gaussSum_eq_of_nondegenerate_polarBilin hQ hm,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card 2, Nat.cast_pow, Nat.cast_ofNat,
    ← hm]
  have h2m : (2 : ℤ) * (2 : ℤ) ^ (2 * m - 1) = (2 : ℤ) ^ (2 * m) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hm' : (2 : ℤ) * (2 : ℤ) ^ (m - 1) = (2 : ℤ) ^ m := by
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  linear_combination -h2m - (-1 : ℤ) ^ Q.arf.val * hm'

/-- A nonsingular `ZMod 2`-quadratic form on a finite space has Arf invariant `0` if and only if
its Gauss sum is strictly positive. -/
theorem arf_eq_zero_iff_gaussSum_pos [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔ 0 < Q.gaussSum := by
  rw [gaussSum_eq_arf hQ]
  have hpow : (0 : ℤ) < (2 : ℤ) ^ (Module.finrank (ZMod 2) V / 2) := by positivity
  rcases eq_or_ne Q.arf 0 with harf | harf
  · simp [harf, hpow]
  · simp only [zmod_two_eq_one_of_ne_zero harf, one_ne_zero, ZMod.val_one, pow_one, neg_one_mul,
      Left.neg_pos_iff, false_iff, not_lt]
    exact hpow.le

/-- **Democratic (majority-vote) characterization of the Arf invariant**: a nonsingular
`ZMod 2`-quadratic form on a finite space has Arf invariant `0` if and only if strictly more than
half of the vectors in `V` are isotropic (`|V| < 2 * #{v | Q v = 0}`). -/
theorem arf_eq_zero_iff_card_lt_two_mul_card_filter_apply_eq_zero [Fintype V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔ Fintype.card V < 2 * (Finset.univ.filter fun v : V => Q v = 0).card := by
  rw [arf_eq_zero_iff_gaussSum_pos hQ, ← Int.ofNat_lt]
  push_cast
  rw [two_mul_card_filter_apply_eq_zero]
  omega

end Arf

end QuadraticMap

namespace TauCeti

/-- The canonical `2 * m`-dimensional nonsingular quadratic form over `ZMod 2` of Arf invariant `c`
(for `m ≥ 1`, and `0` when `m = 0`): `symplecticPlane c c` in coordinate `0` and
`symplecticPlane 0 0` in all remaining coordinates. -/
def arfNormalForm (m : ℕ) (c : ZMod 2) : QuadraticForm (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
  QuadraticMap.pi fun i : Fin m =>
    if (i : ℕ) = 0 then symplecticPlane c c else symplecticPlane 0 0

/-- Coordinate evaluation of `TauCeti.arfNormalForm`. -/
@[simp]
theorem arfNormalForm_apply (m : ℕ) (c : ZMod 2) (x : Fin m → Fin 2 → ZMod 2) :
    arfNormalForm m c x =
      ∑ i : Fin m, (if (i : ℕ) = 0 then symplecticPlane c c else symplecticPlane 0 0) (x i) :=
  QuadraticMap.pi_apply _ x

/-- For `c = 0`, `TauCeti.arfNormalForm m 0` is the `m`-fold orthogonal sum of split planes
`symplecticPlane 0 0`. -/
@[simp]
theorem arfNormalForm_zero (m : ℕ) :
    arfNormalForm m 0 = QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0 := by
  simp [arfNormalForm]

/-- Splitting off coordinate `0` identifies `(symplecticPlane c c).prod (arfNormalForm m 0)` with
`arfNormalForm (m + 1) c`. -/
def isometryEquivConsArfNormalForm (m : ℕ) (c : ZMod 2) :
    ((symplecticPlane c c).prod
      (QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0)).IsometryEquiv
      (arfNormalForm (m + 1) c) :=
  IsometryEquiv.consPi fun i : Fin (m + 1) =>
    if (i : ℕ) = 0 then symplecticPlane c c else symplecticPlane 0 0

/-- The polar bilinear form of `TauCeti.arfNormalForm m c` is nondegenerate. -/
theorem nondegenerate_polarBilin_arfNormalForm (m : ℕ) (c : ZMod 2) :
    (arfNormalForm m c).polarBilin.Nondegenerate :=
  nondegenerate_polarBilin_pi_iff.mpr fun i => by
    split_ifs <;> exact nondegenerate_polarBilin_symplecticPlane _ _

/-- `TauCeti.arfNormalForm m c` is nondegenerate as a quadratic form. -/
theorem nondegenerate_arfNormalForm (m : ℕ) (c : ZMod 2) :
    (arfNormalForm m c).Nondegenerate :=
  QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (nondegenerate_polarBilin_arfNormalForm m c).1)

/-- For `m + 1`, the Arf invariant of `TauCeti.arfNormalForm (m + 1) c` is `c`. -/
@[simp]
theorem arf_arfNormalForm_succ (m : ℕ) (c : ZMod 2) :
    (arfNormalForm (m + 1) c).arf = c := by
  rw [← (isometryEquivConsArfNormalForm m c).arf_eq,
    arf_prod (nondegenerate_polarBilin_symplecticPlane c c)
      (by simpa using nondegenerate_polarBilin_arfNormalForm m 0),
    arf_pi fun _ => nondegenerate_polarBilin_symplecticPlane 0 0]
  simp only [arf_symplecticPlane, mul_zero, Finset.sum_const_zero, add_zero]
  fin_cases c <;> rfl

/-- For `1 ≤ m`, the Arf invariant of `TauCeti.arfNormalForm m c` is `c`. -/
theorem arf_arfNormalForm {m : ℕ} (hm : 1 ≤ m) (c : ZMod 2) :
    (arfNormalForm m c).arf = c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact arf_arfNormalForm_succ k c

private noncomputable def isometryEquivPiDiagArfNormalForm :
    ∀ (m : ℕ) (d : Fin m → ZMod 2),
      (QuadraticMap.pi fun i : Fin m => symplecticPlane (d i) (d i)).IsometryEquiv
        (arfNormalForm m (∑ i : Fin m, d i))
  | 0, _ => isometryEquivOfEq (by
      rw [arfNormalForm]
      congr 1; ext i
      exact Fin.elim0 i)
  | 1, d => isometryEquivOfEq (by
      rw [Fin.sum_univ_one, arfNormalForm]
      congr 1; ext i
      rw [Fin.eq_zero i]
      rfl)
  | m + 2, d => by
      let tail2 : Fin m → ZMod 2 := fun i => d i.succ.succ
      let d' : Fin (m + 1) → ZMod 2 := Fin.cons (d 0 + d 1) tail2
      have hsum : ∑ i : Fin (m + 2), d i = ∑ i : Fin (m + 1), d' i := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp [d', tail2, add_assoc]
      let e1 : (QuadraticMap.pi fun i : Fin (m + 2) => symplecticPlane (d i) (d i)).IsometryEquiv
          ((symplecticPlane (d 0) (d 0)).prod
            ((symplecticPlane (d 1) (d 1)).prod
              (QuadraticMap.pi fun i : Fin m => symplecticPlane (tail2 i) (tail2 i)))) :=
        (IsometryEquiv.consPi _).symm.trans
          ((IsometryEquiv.refl _).prod (IsometryEquiv.consPi _).symm)
      let e2 : (((symplecticPlane (d 0) (d 0)).prod (symplecticPlane (d 1) (d 1))).prod
            (QuadraticMap.pi fun i : Fin m => symplecticPlane (tail2 i) (tail2 i))).IsometryEquiv
          ((symplecticPlane 0 0).prod
            ((symplecticPlane (d 0 + d 1) (d 0 + d 1)).prod
              (QuadraticMap.pi fun i : Fin m => symplecticPlane (tail2 i) (tail2 i)))) :=
        (((isometryEquivSymplecticPlaneProdSelf (d 0) (d 1)).trans
          (IsometryEquiv.prodComm _ _)).prod (IsometryEquiv.refl _)).trans
          (IsometryEquiv.prodAssoc _ _ _)
      let e3 : (QuadraticMap.pi fun i : Fin (m + 1) => symplecticPlane (d' i) (d' i)).IsometryEquiv
          ((symplecticPlane (∑ i, d i) (∑ i, d i)).prod
            (QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0)) :=
        (isometryEquivPiDiagArfNormalForm (m + 1) d').trans
          ((isometryEquivOfEq (by rw [hsum])).trans
            (isometryEquivConsArfNormalForm m (∑ i, d i)).symm)
      exact e1.trans ((IsometryEquiv.prodAssoc _ _ _).symm.trans
        (e2.trans (((IsometryEquiv.refl _).prod ((IsometryEquiv.consPi _).trans e3)).trans
          ((IsometryEquiv.prodLeftComm _ _ _).trans
            (((IsometryEquiv.refl _).prod (IsometryEquiv.consPi _)).trans
              (isometryEquivConsArfNormalForm (m + 1) (∑ i, d i)))))))

/-- Over `ZMod 2`, any `m`-fold orthogonal sum of binary planes `symplecticPlane (a i) (b i)` is
isometric to `arfNormalForm m (∑ i, a i * b i)`. -/
noncomputable def isometryEquivPiSymplecticPlaneArfNormalForm (m : ℕ) (a b : Fin m → ZMod 2) :
    (QuadraticMap.pi fun i : Fin m => symplecticPlane (a i) (b i)).IsometryEquiv
      (arfNormalForm m (∑ i : Fin m, a i * b i)) :=
  (IsometryEquiv.pi fun i => isometryEquivSymplecticPlaneZModTwo (a i) (b i)).trans
    (isometryEquivPiDiagArfNormalForm m fun i => a i * b i)

/-- The split plane `symplecticPlane 0 0` and the anisotropic plane `symplecticPlane 1 1` over
`ZMod 2` are not isometric. -/
theorem not_equivalent_symplecticPlane_zero_zero_one_one :
    ¬(symplecticPlane (0 : ZMod 2) 0).Equivalent (symplecticPlane 1 1) := fun h => by
  have harf := h.arf_eq
  simp at harf

end TauCeti

namespace QuadraticMap

section Classification

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Every `2 * m`-dimensional `ZMod 2`-quadratic space with nondegenerate polar form is isometric
to `TauCeti.arfNormalForm m Q.arf`. -/
noncomputable def isometryEquivArfNormalForm [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {m : ℕ} (hm : 2 * m = Module.finrank (ZMod 2) V) :
    Q.IsometryEquiv (TauCeti.arfNormalForm m Q.arf) := by
  let hspec := (Q.exists_basis_toMatrix_polarBilin_eq_J hQ).choose_spec
  have hm_eq : (Q.exists_basis_toMatrix_polarBilin_eq_J hQ).choose = m := by
    have := hspec.1
    omega
  let b0 := hspec.2.choose
  have hb0 := hspec.2.choose_spec
  let b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V :=
    b0.reindex ((Equiv.cast (congrArg Fin hm_eq)).sumCongr (Equiv.cast (congrArg Fin hm_eq)))
  have hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) (ZMod 2) := by
    subst hm_eq
    simpa [b] using hb0
  exact (TauCeti.isometryEquivPiSymplecticPlane Q b hb).symm.trans
    ((TauCeti.isometryEquivPiSymplecticPlaneArfNormalForm m
        (fun i => Q (b (.inl i))) (fun i => Q (b (.inr i)))).trans
      (isometryEquivOfEq (by rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J Q b hb])))

/-- Every `2 * m`-dimensional `ZMod 2`-quadratic space with nondegenerate polar form is equivalent
to `TauCeti.arfNormalForm m Q.arf`. -/
theorem equivalent_arfNormalForm [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {m : ℕ} (hm : 2 * m = Module.finrank (ZMod 2) V) :
    Q.Equivalent (TauCeti.arfNormalForm m Q.arf) :=
  ⟨isometryEquivArfNormalForm hQ hm⟩

/-- A `2 * m`-dimensional nonsingular `ZMod 2`-quadratic space is isometric to the orthogonal sum
of `m` split planes `symplecticPlane 0 0` if and only if `Q.arf = 0`. -/
theorem equivalent_pi_symplecticPlane_zero_zero_iff [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {m : ℕ} (hm : 2 * m = Module.finrank (ZMod 2) V) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m => TauCeti.symplecticPlane 0 0) ↔ Q.arf = 0 := by
  constructor
  · intro h
    rw [h.arf_eq, arf_pi fun _ => TauCeti.nondegenerate_polarBilin_symplecticPlane 0 0]
    simp
  · intro harf
    simpa [harf] using equivalent_arfNormalForm hQ hm

/-- A `2 * (m + 1)`-dimensional nonsingular `ZMod 2`-quadratic space is isometric to one
anisotropic plane `symplecticPlane 1 1` orthogonal-summed with `m` split planes
`symplecticPlane 0 0` if and only if `Q.arf = 1`. -/
theorem equivalent_symplecticPlane_one_one_prod_pi_iff [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {m : ℕ} (hm : 2 * (m + 1) = Module.finrank (ZMod 2) V) :
    Q.Equivalent ((TauCeti.symplecticPlane 1 1).prod
      (QuadraticMap.pi fun _ : Fin m => TauCeti.symplecticPlane 0 0)) ↔ Q.arf = 1 := by
  constructor
  · intro h
    rw [h.arf_eq, (TauCeti.isometryEquivConsArfNormalForm m 1).arf_eq,
      TauCeti.arf_arfNormalForm_succ]
  · intro harf
    have heq := equivalent_arfNormalForm hQ hm
    rw [harf] at heq
    exact heq.trans ⟨(TauCeti.isometryEquivConsArfNormalForm m 1).symm⟩

/-- **Arf's classification theorem** over `ZMod 2`: two finite-dimensional quadratic spaces whose
polar bilinear forms are nondegenerate are isometric if and only if they have the same dimension
and the same Arf invariant. -/
theorem equivalent_iff_finrank_eq_and_arf_eq
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.Equivalent Q₂ ↔
      Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W ∧ Q₁.arf = Q₂.arf := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv.finrank_eq, e.arf_eq⟩
  · rintro ⟨hdim, harf⟩
    obtain ⟨m, hm⟩ := (Q₁.even_finrank_of_nondegenerate_polarBilin hQ₁).exists_two_nsmul
    have hm₁ : 2 * m = Module.finrank (ZMod 2) V := by simpa [two_mul] using hm.symm
    have hm₂ : 2 * m = Module.finrank (ZMod 2) W := hm₁.trans hdim
    exact (equivalent_arfNormalForm hQ₁ hm₁).trans
      (harf ▸ (equivalent_arfNormalForm hQ₂ hm₂).symm)

end Classification

section Lagrangian

/-- Over any field, in a finite-dimensional quadratic space whose polar bilinear form is
nondegenerate, a `Q`-totally-isotropic subspace is equal to its polar orthogonal complement if and
only if its dimension is half the ambient dimension. -/
theorem isTotallyIsotropic_eq_orthogonal_iff_two_mul_finrank_eq
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V}
    (hU : Q.IsTotallyIsotropic U) :
    U = LinearMap.BilinForm.orthogonal Q.polarBilin U ↔
      2 * Module.finrank K U = Module.finrank K V := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal Q.polarBilin U := fun x hx y hy => by
    simpa [polarBilin_apply_apply] using hU.polar_eq_zero hy hx
  have hsum : Module.finrank K U +
      Module.finrank K (LinearMap.BilinForm.orthogonal Q.polarBilin U) = Module.finrank K V := by
    have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal Q.isSymm_polarBilin.isRefl U
    rwa [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_bot_eq, finrank_bot, add_zero] at h
  constructor
  · intro heq
    rw [← heq] at hsum
    omega
  · intro h2
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- If `V` contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement,
then `Q.arf = 0`. -/
theorem arf_eq_zero_of_isTotallyIsotropic_of_eq_orthogonal
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : Q.IsTotallyIsotropic U)
    (horth : U = LinearMap.BilinForm.orthogonal Q.polarBilin U) :
    Q.arf = 0 := by
  let e := Module.finBasis (ZMod 2) U
  obtain ⟨b, hb, hbinl⟩ :=
    LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq Q.isAlt_polarBilin hQ e horth
  rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J Q b hb]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hbinl i, hU.apply_eq_zero (e i).2, zero_mul]

/-- **Lagrangian criterion for the Arf invariant**: a finite-dimensional `ZMod 2`-quadratic form
with nondegenerate polar form has `Q.arf = 0` if and only if `V` contains a `Q`-totally-isotropic
subspace equal to its own polar orthogonal complement. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_eq_orthogonal
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ U = LinearMap.BilinForm.orthogonal Q.polarBilin U := by
  constructor
  · intro harf
    obtain ⟨m, hm⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).exists_two_nsmul
    have hm' : 2 * m = Module.finrank (ZMod 2) V := by simpa [two_mul] using hm.symm
    let Q₀ : QuadraticForm (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
      QuadraticMap.pi fun _ : Fin m => TauCeti.symplecticPlane 0 0
    let f : Q₀.IsometryEquiv Q :=
      (isometryEquivOfEq (by rw [harf, TauCeti.arfNormalForm_zero] :
        Q₀ = TauCeti.arfNormalForm m Q.arf)).trans (isometryEquivArfNormalForm hQ hm').symm
    let U₀ : Submodule (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
      { carrier := {x | ∀ i, x i 1 = 0}
        add_mem' := fun hx hy i => by simp [hx i, hy i]
        zero_mem' := fun _ => rfl
        smul_mem' := fun c _ hx i => by simp [hx i] }
    have hU₀_iso : Q₀.IsTotallyIsotropic U₀ := isTotallyIsotropic_iff.mpr fun x hx => by
      rw [QuadraticMap.pi_apply]
      exact Finset.sum_eq_zero fun i _ => by simp [hx i]
    have hU₀_orth : U₀ = LinearMap.BilinForm.orthogonal Q₀.polarBilin U₀ := by
      ext y
      simp only [LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply, Q₀,
        QuadraticMap.Ring.polar_pi, TauCeti.polar_symplecticPlane_of_charTwo]
      constructor
      · intro hy x hx
        exact Finset.sum_eq_zero fun i _ => by simp [hx i, hy i]
      · intro hy i
        have hsingle : (Pi.single i ![(1 : ZMod 2), 0] : Fin m → Fin 2 → ZMod 2) ∈ U₀ := fun j => by
          by_cases hji : j = i
          · subst hji; simp
          · simp [Pi.single_eq_of_ne hji]
        have hi := hy _ hsingle
        rw [Finset.sum_eq_single i] at hi
        · simpa using hi
        · intro j _ hji
          simp [Pi.single_eq_of_ne hji]
        · simp
    refine ⟨U₀.map f.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [isTotallyIsotropic_iff]
      rintro _ ⟨x, hx, rfl⟩
      change Q (f x) = 0
      rw [f.map_app]
      exact hU₀_iso.apply_eq_zero hx
    · ext v
      simp only [Submodule.mem_map, LinearMap.BilinForm.mem_orthogonal_iff,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, LinearEquiv.coe_coe,
        polarBilin_apply_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩ y hy
        change polar Q (f y) (f x) = 0
        rw [f.polar_apply]
        have hx' : x ∈ LinearMap.BilinForm.orthogonal Q₀.polarBilin U₀ := hU₀_orth ▸ hx
        exact hx' y hy
      · intro hv
        have hsymm : f.symm v ∈ LinearMap.BilinForm.orthogonal Q₀.polarBilin U₀ := fun y hy => by
          rw [polarBilin_apply_apply, ← f.polar_apply, f.apply_symm_apply]
          exact hv y hy
        exact ⟨f.symm v, hU₀_orth.symm ▸ hsymm, f.apply_symm_apply v⟩
  · rintro ⟨U, hU, horth⟩
    exact arf_eq_zero_of_isTotallyIsotropic_of_eq_orthogonal hQ hU horth

/-- **Half-dimensional isotropic criterion for the Arf invariant**: a finite-dimensional
`ZMod 2`-quadratic form with nondegenerate polar form has `Q.arf = 0` if and only if `V` contains
a `Q`-totally-isotropic subspace of half the ambient dimension. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V := by
  rw [arf_eq_zero_iff_exists_isTotallyIsotropic_eq_orthogonal hQ]
  exact exists_congr fun U => and_congr_right fun hU =>
    isTotallyIsotropic_eq_orthogonal_iff_two_mul_finrank_eq hQ hU

end Lagrangian

end QuadraticMap
