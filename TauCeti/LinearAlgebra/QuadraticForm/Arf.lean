/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
public import TauCeti.LinearAlgebra.QuadraticForm.CharTwo
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import TauCeti.Data.ZMod.Pow
import TauCeti.Data.ZMod.Two

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

Using the plane isometries `[a, b] ≅ [a * b, a * b]` over `ZMod 2` and
`[0, 0] ⊕ [0, 0] ≅ [1, 1] ⊕ [1, 1]`, every nonsingular quadratic space of dimension `2 * m` is
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
* `TauCeti.isometryEquivSymplecticPlaneMul`: over `ZMod 2`, `symplecticPlane a b` is isometric to
  `symplecticPlane (a * b) (a * b)`.
* `QuadraticMap.arf`: the Arf invariant in `ZMod 2` of a `ZMod 2`-quadratic form (`0` outside the
  finite-dimensional polar-nondegenerate regime).
* `TauCeti.arfNormalForm`: the canonical `2 * m`-dimensional nonsingular `ZMod 2`-quadratic form of
  Arf invariant `c` (for `m ≥ 1`, and `0` when `m = 0`).
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
  `QuadraticMap.gaussSum_eq_neg_one_pow_val_arf_mul_two_pow`,
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
* [A. Pyronneau, *The Arf and Rohklin's
  invariant*](https://web.ma.utexas.edu/SMC/2024/Rokhlin_s_Invariant.pdf) (January 2024), §2.1,
  Lemmas 2.11–2.13, Corollary 2.14, Theorem 2.15, pp. 4–5.
-/

public section

open QuadraticMap

namespace QuadraticMap

section GaussSum

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
  simp_rw [QuadraticMap.prod_apply, TauCeti.pow_val_add (neg_one_sq : (-1 : ℤ) ^ 2 = 1),
    ← Finset.mul_sum, ← Finset.sum_mul]
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
  rw [pi_apply, TauCeti.pow_val_sum (neg_one_sq : (-1 : ℤ) ^ 2 = 1)]

/-- Twice the number of zeros of `Q : QuadraticForm (ZMod 2) V` equals `|V| + Q.gaussSum`. -/
theorem two_mul_card_filter_apply_eq_zero [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    2 * ((Finset.univ.filter fun v : V => Q v = 0).card : ℤ) =
      Fintype.card V + Q.gaussSum := by
  have hsum : ∑ v : V, ((1 : ℤ) + (-1 : ℤ) ^ (Q v).val) = Fintype.card V + Q.gaussSum := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_one, gaussSum_def]
  rw [← hsum]
  simp only [ZMod.one_add_neg_one_pow_val, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

/-- Twice `Nat.card {v : V // Q v = 0}` equals `|V| + Q.gaussSum`. -/
theorem two_mul_natCard_apply_eq_zero [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    2 * (Nat.card {v : V // Q v = 0} : ℤ) = Fintype.card V + Q.gaussSum := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, two_mul_card_filter_apply_eq_zero]

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

/-- On `ZMod 2`, the binary plane `symplecticPlane a b` has Gauss sum `(-1) ^ (a * b).val * 2`. -/
@[simp]
theorem gaussSum_symplecticPlane (a b : ZMod 2) :
    (symplecticPlane a b).gaussSum = (-1 : ℤ) ^ (a * b).val * 2 := by
  rw [gaussSum_def, Fintype.sum_equiv (finTwoArrowEquiv (ZMod 2)) _
    (fun p : ZMod 2 × ZMod 2 => (-1 : ℤ) ^ (symplecticPlane a b ![p.1, p.2]).val)
    fun x => congrArg (fun y => (-1 : ℤ) ^ (symplecticPlane a b y).val)
      (funext fun i => by fin_cases i <;> rfl)]
  simp only [symplecticPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  revert a b
  decide

/-- Over `ZMod 2`, the binary plane `symplecticPlane a b` is isometric to
`symplecticPlane (a * b) (a * b)`: it is `[0, 0]` whenever `a = 0` or `b = 0`, and `[1, 1]` when
`a = b = 1`. -/
def isometryEquivSymplecticPlaneMul (a b : ZMod 2) :
    (symplecticPlane a b).IsometryEquiv (symplecticPlane (a * b) (a * b)) :=
  if ha : a = 0 then
    (IsometryEquiv.ofEq (by rw [ha])).trans
      ((isometryEquivSymplecticPlaneZeroLeft b).trans
        (IsometryEquiv.ofEq (by rw [ha, zero_mul])))
  else if hb : b = 0 then
    (IsometryEquiv.ofEq (by rw [hb])).trans
      ((isometryEquivSymplecticPlaneZeroRight a).trans
        (IsometryEquiv.ofEq (by rw [hb, mul_zero])))
  else
    IsometryEquiv.ofEq (by
      rw [ZMod.eq_one_of_ne_zero ha, ZMod.eq_one_of_ne_zero hb, mul_one])

/-- Evaluation of `TauCeti.isometryEquivSymplecticPlaneMul` in coordinates. -/
@[simp]
theorem isometryEquivSymplecticPlaneMul_apply (a b : ZMod 2) (x : Fin 2 → ZMod 2) :
    isometryEquivSymplecticPlaneMul a b x =
      ![x 0 + (1 + a) * b * x 1, a * (1 + b) * x 0 + x 1] := by
  rcases eq_or_ne a 0 with rfl | ha
  · ext i
    fin_cases i <;> simp [isometryEquivSymplecticPlaneMul]
  · obtain rfl := ZMod.eq_one_of_ne_zero ha
    rcases eq_or_ne b 0 with rfl | hb
    · ext i
      fin_cases i <;> simp [isometryEquivSymplecticPlaneMul, ha]
    · obtain rfl := ZMod.eq_one_of_ne_zero hb
      ext i
      fin_cases i <;> simp [isometryEquivSymplecticPlaneMul, ha, CharTwo.add_self_eq_zero]

/-- Evaluation of the inverse of `TauCeti.isometryEquivSymplecticPlaneMul` in coordinates. -/
@[simp]
theorem isometryEquivSymplecticPlaneMul_symm_apply (a b : ZMod 2) (y : Fin 2 → ZMod 2) :
    (isometryEquivSymplecticPlaneMul a b).symm y =
      ![y 0 + (1 + a) * b * y 1, a * (1 + b) * y 0 + y 1] := by
  rw [IsometryEquiv.symm_apply_eq, isometryEquivSymplecticPlaneMul_apply]
  rcases eq_or_ne a 0 with rfl | ha
  · rcases eq_or_ne b 0 with rfl | hb
    · ext i; fin_cases i <;> simp
    · obtain rfl := ZMod.eq_one_of_ne_zero hb
      ext i; fin_cases i <;> simp [add_assoc, CharTwo.add_self_eq_zero]
  · obtain rfl := ZMod.eq_one_of_ne_zero ha
    rcases eq_or_ne b 0 with rfl | hb
    · ext i; fin_cases i <;> simp [← add_assoc, CharTwo.add_self_eq_zero]
    · obtain rfl := ZMod.eq_one_of_ne_zero hb
      ext i; fin_cases i <;> simp [CharTwo.add_self_eq_zero]

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
    exact ⟨ZMod.eq_one_of_ne_zero ha0, ZMod.eq_one_of_ne_zero hb0⟩
  · rintro ⟨rfl, rfl⟩ x hx
    rcases eq_or_ne (x 0) 0 with h0 | h0 <;> rcases eq_or_ne (x 1) 0 with h1 | h1
    · ext i
      fin_cases i <;> simp [h0, h1]
    · rw [symplecticPlane_apply, h0, ZMod.eq_one_of_ne_zero h1] at hx
      norm_num at hx
    · rw [symplecticPlane_apply, ZMod.eq_one_of_ne_zero h0, h1] at hx
      norm_num at hx
    · rw [symplecticPlane_apply, ZMod.eq_one_of_ne_zero h0, ZMod.eq_one_of_ne_zero h1] at hx
      exact False.elim ((by decide : (1 * 1 ^ 2 + 1 * 1 + 1 * 1 ^ 2 : ZMod 2) ≠ 0) hx)

/-- The binary plane `symplecticPlane 1 1` (`x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2`) over `ZMod 2` is
anisotropic. -/
theorem anisotropic_symplecticPlane_one_one :
    (symplecticPlane (1 : ZMod 2) 1).Anisotropic :=
  (anisotropic_symplecticPlane_iff 1 1).mpr ⟨rfl, rfl⟩

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
  rw [(Q.isometryEquivPiSymplecticPlane b hb).symm.gaussSum_eq, gaussSum_pi]
  simp_rw [TauCeti.gaussSum_symplecticPlane]
  rw [Finset.prod_mul_distrib, ← TauCeti.pow_val_sum (neg_one_sq : (-1 : ℤ) ^ 2 = 1),
    Finset.prod_const, Finset.card_univ]

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
  exact ZMod.neg_one_pow_val_inj.mp (mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) hg)

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
theorem gaussSum_eq_neg_one_pow_val_arf_mul_two_pow [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * (2 : ℤ) ^ (Module.finrank (ZMod 2) V / 2) := by
  obtain ⟨m, hm⟩ := (Q.even_finrank_of_nondegenerate_polarBilin hQ).exists_two_nsmul
  have hm' : 2 * m = Module.finrank (ZMod 2) V := by simpa [two_mul] using hm.symm
  have hdiv : Module.finrank (ZMod 2) V / 2 = m := by omega
  rw [hdiv, gaussSum_eq_of_nondegenerate_polarBilin hQ hm']

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
  · obtain ⟨hfin₁, hnd₁⟩ := h
    obtain ⟨hfin₂, hnd₂⟩ := hcond.mp ⟨hfin₁, hnd₁⟩
    have : Finite V := Module.finite_of_finite (ZMod 2)
    have : Finite W := Module.finite_of_finite (ZMod 2)
    let _ : Fintype V := Fintype.ofFinite V
    let _ : Fintype W := Fintype.ofFinite W
    have hg := e.gaussSum_eq
    rw [gaussSum_eq_neg_one_pow_val_arf_mul_two_pow hnd₁,
      gaussSum_eq_neg_one_pow_val_arf_mul_two_pow hnd₂, e.toLinearEquiv.finrank_eq] at hg
    exact ZMod.neg_one_pow_val_inj.mp (mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) hg)
  · have h' : ¬(FiniteDimensional (ZMod 2) W ∧ Q₂.polarBilin.Nondegenerate) := mt hcond.mpr h
    simp [arf, h, h']

/-- Equivalent `ZMod 2`-quadratic forms have the same Arf invariant. -/
theorem Equivalent.arf_eq {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (h : Q₁.Equivalent Q₂) : Q₁.arf = Q₂.arf :=
  let ⟨e⟩ := h
  e.arf_eq

/-- The Arf invariant is additive under orthogonal product of finite-dimensional
polar-nondegenerate `ZMod 2`-quadratic spaces. -/
@[grind =]
theorem arf_prod [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {Q₁ : QuadraticForm (ZMod 2) V} {Q₂ : QuadraticForm (ZMod 2) W}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite W := Module.finite_of_finite (ZMod 2)
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype W := Fintype.ofFinite W
  obtain ⟨m₁, hm₁⟩ := (Q₁.even_finrank_of_nondegenerate_polarBilin hQ₁).exists_two_nsmul
  obtain ⟨m₂, hm₂⟩ := (Q₂.even_finrank_of_nondegenerate_polarBilin hQ₂).exists_two_nsmul
  have hm₁' : 2 * m₁ = Module.finrank (ZMod 2) V := by simpa [two_mul] using hm₁.symm
  have hm₂' : 2 * m₂ = Module.finrank (ZMod 2) W := by simpa [two_mul] using hm₂.symm
  have hm : 2 * (m₁ + m₂) = Module.finrank (ZMod 2) (V × W) := by
    rw [Module.finrank_prod, ← hm₁', ← hm₂', mul_add]
  have hg := gaussSum_prod Q₁ Q₂
  rw [gaussSum_eq_of_nondegenerate_polarBilin (nondegenerate_polarBilin_prod_iff.mpr ⟨hQ₁, hQ₂⟩) hm,
    gaussSum_eq_of_nondegenerate_polarBilin hQ₁ hm₁',
    gaussSum_eq_of_nondegenerate_polarBilin hQ₂ hm₂'] at hg
  have hmul :
      (-1 : ℤ) ^ (Q₁.prod Q₂).arf.val * (2 : ℤ) ^ (m₁ + m₂) =
        (-1 : ℤ) ^ (Q₁.arf + Q₂.arf).val * (2 : ℤ) ^ (m₁ + m₂) := by
    rw [hg, TauCeti.pow_val_add (neg_one_sq : (-1 : ℤ) ^ 2 = 1), pow_add]
    ring
  exact ZMod.neg_one_pow_val_inj.mp (mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) hmul)

/-- The Arf invariant is additive across any finite orthogonal family of finite-dimensional
polar-nondegenerate `ZMod 2`-quadratic spaces. -/
theorem arf_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)]
    [∀ i, FiniteDimensional (ZMod 2) (M i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i : ι, (Q i).arf := by
  classical
  have (i : ι) : Finite (M i) := Module.finite_of_finite (ZMod 2)
  let _ (i : ι) : Fintype (M i) := Fintype.ofFinite (M i)
  have hm_ex (i : ι) : ∃ m : ℕ, 2 * m = Module.finrank (ZMod 2) (M i) := by
    obtain ⟨m, hm⟩ := ((Q i).even_finrank_of_nondegenerate_polarBilin (hQ i)).exists_two_nsmul
    exact ⟨m, by simpa [two_mul] using hm.symm⟩
  choose m hm using hm_ex
  have hmpi : 2 * ∑ i, m i = Module.finrank (ZMod 2) (∀ i, M i) := by
    rw [Module.finrank_pi_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hm i
  have hg := gaussSum_pi Q
  rw [gaussSum_eq_of_nondegenerate_polarBilin (nondegenerate_polarBilin_pi_iff.mpr hQ) hmpi] at hg
  simp_rw [fun i ↦ gaussSum_eq_of_nondegenerate_polarBilin (hQ i) (hm i)] at hg
  rw [Finset.prod_mul_distrib, ← TauCeti.pow_val_sum (neg_one_sq : (-1 : ℤ) ^ 2 = 1),
    Finset.prod_pow_eq_pow_sum] at hg
  exact ZMod.neg_one_pow_val_inj.mp (mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) hg)

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
  rw [gaussSum_eq_neg_one_pow_val_arf_mul_two_pow hQ]
  have hpow : (0 : ℤ) < (2 : ℤ) ^ (Module.finrank (ZMod 2) V / 2) := by positivity
  rcases eq_or_ne Q.arf 0 with harf | harf
  · simp [harf, hpow]
  · simp only [ZMod.eq_one_of_ne_zero harf, one_ne_zero, ZMod.val_one, pow_one, neg_one_mul,
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

/-- The Arf invariant of `TauCeti.symplecticPlane a b` over `ZMod 2` is `a * b`. -/
@[simp]
theorem arf_symplecticPlane (a b : ZMod 2) :
    (symplecticPlane a b).arf = a * b := by
  have hg := gaussSum_eq_of_nondegenerate_polarBilin
    (nondegenerate_polarBilin_symplecticPlane a b) (m := 1) (by simp)
  rw [gaussSum_symplecticPlane, pow_one] at hg
  exact ZMod.neg_one_pow_val_inj.mp (mul_right_cancel₀ two_ne_zero hg.symm)

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
theorem arfNormalForm_zero (m : ℕ) :
    arfNormalForm m 0 = QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0 := by
  simp [arfNormalForm]

/-- Splitting off coordinate `0` identifies
`(symplecticPlane c c).prod (QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0)` with
`arfNormalForm (m + 1) c`. -/
def isometryEquivConsArfNormalForm (m : ℕ) (c : ZMod 2) :
    ((symplecticPlane c c).prod
      (QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0)).IsometryEquiv
      (arfNormalForm (m + 1) c) :=
  IsometryEquiv.consPi fun i : Fin (m + 1) =>
    if (i : ℕ) = 0 then symplecticPlane c c else symplecticPlane 0 0

/-- Forward evaluation of `TauCeti.isometryEquivConsArfNormalForm`. -/
@[simp]
theorem isometryEquivConsArfNormalForm_apply (m : ℕ) (c : ZMod 2)
    (p : (Fin 2 → ZMod 2) × (Fin m → Fin 2 → ZMod 2)) :
    isometryEquivConsArfNormalForm m c p = Fin.cons p.1 p.2 :=
  IsometryEquiv.consPi_apply (M := fun _ => Fin 2 → ZMod 2) _ p.1 p.2

/-- Inverse evaluation of `TauCeti.isometryEquivConsArfNormalForm`. -/
@[simp]
theorem isometryEquivConsArfNormalForm_symm_apply (m : ℕ) (c : ZMod 2)
    (x : Fin (m + 1) → Fin 2 → ZMod 2) :
    (isometryEquivConsArfNormalForm m c).symm x = (x 0, Fin.tail x) :=
  IsometryEquiv.consPi_symm_apply _ x

/-- The polar bilinear form of `TauCeti.arfNormalForm m c` is nondegenerate. -/
@[simp]
theorem nondegenerate_polarBilin_arfNormalForm (m : ℕ) (c : ZMod 2) :
    (arfNormalForm m c).polarBilin.Nondegenerate :=
  nondegenerate_polarBilin_pi_iff.mpr fun _ => by
    split_ifs <;> exact nondegenerate_polarBilin_symplecticPlane _ _

/-- `TauCeti.arfNormalForm m c` is nondegenerate as a quadratic form. -/
@[simp]
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
      (nondegenerate_polarBilin_pi_iff.mpr fun _ => nondegenerate_polarBilin_symplecticPlane 0 0),
    arf_pi fun _ => nondegenerate_polarBilin_symplecticPlane 0 0]
  simp only [arf_symplecticPlane, mul_zero, Finset.sum_const_zero, add_zero]
  fin_cases c <;> rfl

/-- For `1 ≤ m`, the Arf invariant of `TauCeti.arfNormalForm m c` is `c`. -/
theorem arf_arfNormalForm {m : ℕ} (hm : 1 ≤ m) (c : ZMod 2) :
    (arfNormalForm m c).arf = c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact arf_arfNormalForm_succ k c

private def isometryEquivSymplecticPlaneProdAddZero (x y : ZMod 2) :
    ((symplecticPlane x x).prod (symplecticPlane y y)).IsometryEquiv
      ((symplecticPlane (x + y) (x + y)).prod (symplecticPlane 0 0)) :=
  if hx : x = 0 then
    if hy : y = 0 then
      IsometryEquiv.ofEq (by rw [hx, hy, add_zero])
    else
      (IsometryEquiv.prodComm _ _).trans (IsometryEquiv.ofEq (by rw [hx, zero_add]))
  else
    if hy : y = 0 then
      IsometryEquiv.ofEq (by rw [hy, add_zero])
    else
      have hx1 : x = 1 := ZMod.eq_one_of_ne_zero hx
      have hy1 : y = 1 := ZMod.eq_one_of_ne_zero hy
      (IsometryEquiv.ofEq (by rw [hx1, hy1])).trans
        (isometryEquivSymplecticPlaneOneOneProd.symm.trans
          (IsometryEquiv.ofEq (by
            have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
            rw [hx1, hy1, h11])))

private noncomputable def isometryEquivPiDiagArfNormalForm :
    ∀ (m : ℕ) (d : Fin m → ZMod 2),
      (QuadraticMap.pi fun i : Fin m => symplecticPlane (d i) (d i)).IsometryEquiv
        (arfNormalForm m (∑ i : Fin m, d i))
  | 0, _ => IsometryEquiv.ofEq (by
      rw [arfNormalForm]
      congr 1; ext i
      exact Fin.elim0 i)
  | 1, d => IsometryEquiv.ofEq (by
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
        (((isometryEquivSymplecticPlaneProdAddZero (d 0) (d 1)).trans
          (IsometryEquiv.prodComm _ _)).prod (IsometryEquiv.refl _)).trans
          (IsometryEquiv.prodAssoc _ _ _)
      let e3 : (QuadraticMap.pi fun i : Fin (m + 1) => symplecticPlane (d' i) (d' i)).IsometryEquiv
          ((symplecticPlane (∑ i, d i) (∑ i, d i)).prod
            (QuadraticMap.pi fun _ : Fin m => symplecticPlane 0 0)) :=
        (isometryEquivPiDiagArfNormalForm (m + 1) d').trans
          ((IsometryEquiv.ofEq (by rw [hsum])).trans
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
  (IsometryEquiv.pi fun i => isometryEquivSymplecticPlaneMul (a i) (b i)).trans
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
  exact (Q.isometryEquivPiSymplecticPlane b hb).symm.trans
    ((TauCeti.isometryEquivPiSymplecticPlaneArfNormalForm m
        (fun i => Q (b (.inl i))) (fun i => Q (b (.inr i)))).trans
      (IsometryEquiv.ofEq (by rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J Q b hb])))

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
    rw [← TauCeti.arfNormalForm_zero]
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
@[grind =]
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

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- In a finite-dimensional `ZMod 2`-quadratic space whose polar bilinear form is nondegenerate, if
`V` contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement, then
`Q.arf = 0`. -/
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
      (IsometryEquiv.ofEq (by rw [harf, TauCeti.arfNormalForm_zero] :
        Q₀ = TauCeti.arfNormalForm m Q.arf)).trans (isometryEquivArfNormalForm hQ hm').symm
    let U₀ : Submodule (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
      Submodule.pi Set.univ fun _ : Fin m => ZMod 2 ∙ ![(1 : ZMod 2), 0]
    have hU₀_iso : Q₀.IsTotallyIsotropic U₀ :=
      TauCeti.isTotallyIsotropic_pi_symplecticPlane_zero_left fun _ => 0
    have hU₀_orth : LinearMap.BilinForm.orthogonal Q₀.polarBilin U₀ = U₀ :=
      TauCeti.orthogonal_polarBilin_pi_symplecticPlane_span_one_zero (fun _ => 0) (fun _ => 0)
    refine ⟨U₀.map f.toLinearMap, f.isTotallyIsotropic_map_iff.mpr hU₀_iso, ?_⟩
    rw [← f.map_orthogonal_polarBilin, hU₀_orth]
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
    hU.eq_orthogonal_iff_two_mul_finrank_eq hQ

end Lagrangian

end QuadraticMap
