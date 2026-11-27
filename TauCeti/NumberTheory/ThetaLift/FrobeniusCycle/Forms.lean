/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The twisted action of a Frobenius cycle on forms, and conditions on translates

Let `T` be a Frobenius cycle with `N` letters from a local ring `W` to a commutative ring `R`.
The group `GL_k(W)` acts on polynomials over `R` in the variables `x (b, s)`, `b : Fin k`,
`s : ZMod N`, by the `R`-algebra maps sending `x (c, s)` to `∑ b, (g_s) b c • x (b, s)`, where
`g_s = T.letterMatrix s g` is the letter matrix of `g` (`ι s` of `g` on the even letters, of its
inverse transpose on the odd ones). A form of degree `n` in each letter is a vector indexed by
the exponents `Exponent N k n`, and `letterRep n g` is the matrix of the action of `g` on such
forms. The conditions on translates cut out the forms all of whose translates by a Levi subgroup
have their coefficients at given exponents in a given ideal; the defect conditions and the deep
forms are two instances.

## Main definitions

* `TauCeti.FrobeniusCycle.twistedAction`: the twisted action of `GL_k(W)` on
  `MvPolynomial (Fin k × ZMod N) R`, as a monoid homomorphism to its algebra endomorphisms.
* `TauCeti.FrobeniusCycle.Exponent`, `TauCeti.FrobeniusCycle.formToMvPolynomial`: the exponents
  of degree `n` in each letter, and the polynomial of a form.
* `TauCeti.FrobeniusCycle.letterDegree`: the degree in each letter, as a weight with values in
  `ZMod N → ℕ`.
* `TauCeti.FrobeniusCycle.letterRep`: the matrix `ρ_n(g)` of the action on forms of degree `n`
  in each letter, as a monoid homomorphism.
* `TauCeti.FrobeniusCycle.translatesIn`, `TauCeti.FrobeniusCycle.defectConditions`,
  `TauCeti.FrobeniusCycle.deepForms`: forms all of whose Levi translates have the coefficients
  at a set of exponents in an ideal.

## Main results

* `TauCeti.FrobeniusCycle.twistedAction_X`: the action on a variable.
* `TauCeti.FrobeniusCycle.isWeightedHomogeneous_twistedAction`: the action preserves the degree
  in each letter.
* `TauCeti.FrobeniusCycle.isWeightedHomogeneous_formToMvPolynomial`,
  `TauCeti.FrobeniusCycle.eq_formToMvPolynomial_of_isWeightedHomogeneous`: the polynomials of
  forms are exactly the polynomials of degree `n` in each letter.
* `TauCeti.FrobeniusCycle.twistedAction_formToMvPolynomial`: `letterRep n g` is the matrix of
  the twisted action on forms of degree `n` in each letter.
* `TauCeti.FrobeniusCycle.letterRep_mulVec_mem_translatesIn`: the conditions on translates by
  the Levi subgroup of `τ` are stable under that subgroup.
* `TauCeti.FrobeniusCycle.translatesIn_mono`, `TauCeti.FrobeniusCycle.defectConditions_mono`,
  `TauCeti.FrobeniusCycle.deepForms_anti`: monotonicity in the ideal, the set of exponents, the
  defect bound and the depth.

## References

* The formal proof whose route the definitions of this file belong to: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `New/UpperBound/ElementaryDivisors/TwistingData.lean`; the definitions here correspond to
  `New.FrobeniusCycle.letterRep`, `New.FrobeniusCycle.translatesIn`,
  `New.FrobeniusCycle.defectConditions` and `New.FrobeniusCycle.deepForms` there.
-/

public section

open MvPolynomial Matrix TauCeti.GeneralLinear

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N : ℕ}
  (T : FrobeniusCycle W R N) {k : ℕ}

/-! ### The twisted action on polynomials -/

/-- The twisted action of `g ∈ GL_k(W)` on polynomials in the variables `x (b, s)`: the
`R`-algebra map sending `x (c, s)` to `∑ b, (g_s) b c • x (b, s)` (`twistedAction_X`), that is,
the substitution of standard vectors by the block diagonal matrix with the blocks
`g_s = T.letterMatrix s g` (`twistedAction_apply`). -/
noncomputable def twistedAction :
    GL (Fin k) W →* (MvPolynomial (Fin k × ZMod N) R →ₐ[R] MvPolynomial (Fin k × ZMod N) R) :=
  letI := T.neZero
  { toFun g := polynomialAction (blockDiagonal fun s ↦ T.letterMatrix s g)
    map_one' := by
      simp only [map_one]
      rw [← Pi.one_def, blockDiagonal_one, polynomialAction_one]
      -- `1` in the monoid of algebra endomorphisms is the identity
      rfl
    map_mul' g h := by
      simp only [map_mul]
      rw [blockDiagonal_mul, polynomialAction_mul]
      -- multiplication in the monoid of algebra endomorphisms is composition
      rfl }

/-- The twisted action is the substitution of standard vectors by the block diagonal matrix of
the letter matrices. -/
theorem twistedAction_apply [NeZero N] (g : GL (Fin k) W) :
    T.twistedAction g = polynomialAction (blockDiagonal fun s ↦ T.letterMatrix s g) :=
  (rfl)

/-- The twisted action on a variable. -/
@[simp]
theorem twistedAction_X (g : GL (Fin k) W) (c : Fin k) (s : ZMod N) :
    T.twistedAction g (X (c, s)) = ∑ b, T.letterMatrix s g b c • X (b, s) := by
  have := T.neZero
  simp [twistedAction_apply, blockDiagonal_apply, Fintype.sum_prod_type, smul_eq_C_mul,
    apply_ite C, ite_mul]

/-! ### Forms of degree `n` in each letter -/

/-- The exponents of degree `n` in each letter: the monomials `x ^ β` in the variables
`x (b, s)` with `∑ b, β (b, s) = n` for every letter `s`. -/
abbrev Exponent (N k n : ℕ) : Type := {β : Fin k × ZMod N →₀ ℕ // ∀ s, ∑ b, β (b, s) = n}

variable {n : ℕ}

/-- If there is an exponent of positive degree in each letter, there are finitely many letters:
every letter carries a variable of the finite support. -/
private theorem finite_zMod_of_exponent (hn : 0 < n) (β : Exponent N k n) : Finite (ZMod N) := by
  have h : ∀ s, ∃ b, (b, s) ∈ β.val.support := fun s ↦ by
    by_contra! h
    have h0 : ∑ b, β.val (b, s) = 0 :=
      Finset.sum_eq_zero fun b _ ↦ Finsupp.notMem_support_iff.mp (h b)
    have := β.property s
    omega
  choose b hb using h
  exact Finite.of_injective (fun s ↦ (⟨(b s, s), hb s⟩ : β.val.support))
    fun s t hst ↦ congrArg (fun x : β.val.support ↦ x.val.2) hst

instance : Finite (Exponent N k n) := by
  rcases isEmpty_or_nonempty (Exponent N k n) with h | h
  · infer_instance
  obtain ⟨β₀⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- in degree `0` the only exponent is `0`
    have : Subsingleton (Exponent N k 0) := ⟨fun β γ ↦ Subtype.ext (Finsupp.ext fun x ↦ by
      rw [(Finset.sum_eq_zero_iff.mp (β.property x.2)) x.1 (Finset.mem_univ _),
        (Finset.sum_eq_zero_iff.mp (γ.property x.2)) x.1 (Finset.mem_univ _)])⟩
    infer_instance
  have := finite_zMod_of_exponent hn β₀
  -- an exponent is determined by its values, which are at most `n`
  refine Finite.of_injective (fun (β : Exponent N k n) (x : Fin k × ZMod N) ↦
    (⟨β.val x, Nat.lt_succ_of_le ?_⟩ : Fin (n + 1)))
    fun β γ h ↦ Subtype.ext (Finsupp.ext fun x ↦ by simpa using congrFun h x)
  exact (Finset.single_le_sum (f := fun b ↦ β.val (b, x.2)) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ x.1)).trans_eq (β.property x.2)

noncomputable instance : Fintype (Exponent N k n) := Fintype.ofFinite _

/-- Two exponents with the same values are equal. -/
@[ext]
theorem Exponent.ext {β γ : Exponent N k n} (h : ∀ x, β.val x = γ.val x) : β = γ :=
  Subtype.ext (Finsupp.ext h)

/-- The degree in each letter, as a weight with values in `ZMod N → ℕ`: the variable `x (b, s)`
has the weight `Pi.single s 1`, so that a polynomial is weighted homogeneous of weight `m` for
`letterDegree` if and only if it has degree `m s` in the variables of each letter `s`
(`weight_letterDegree`). -/
def letterDegree (x : Fin k × ZMod N) : ZMod N → ℕ := Pi.single x.2 1

/-- The weight of an exponent for `letterDegree` is its family of degrees in the letters. -/
theorem weight_letterDegree (β : Fin k × ZMod N →₀ ℕ) :
    Finsupp.weight letterDegree β = fun s ↦ ∑ b, β (b, s) := by
  classical
  induction β using Finsupp.induction with
  | zero => ext; simp
  | single_add x m β _ _ ih =>
    ext s
    rw [map_add, Pi.add_apply, ih]
    simp [Finsupp.weight_single, letterDegree, Pi.single_apply, Finsupp.single_apply,
      Finset.sum_add_distrib, Prod.ext_iff, eq_comm, ite_and]

section Semiring

variable {A : Type*} [CommSemiring A]

/-- The polynomial `∑ β, F β • x ^ β` of a form of degree `n` in each letter. -/
noncomputable def formToMvPolynomial (F : Exponent N k n → A) :
    MvPolynomial (Fin k × ZMod N) A :=
  ∑ β, monomial β.val (F β)

/-- The coefficient of the polynomial of a form at an exponent is the entry of the form. -/
@[simp]
theorem coeff_formToMvPolynomial (F : Exponent N k n → A) (β : Exponent N k n) :
    (formToMvPolynomial F).coeff β.val = F β := by
  classical
  simp [formToMvPolynomial, coeff_monomial, Subtype.val_inj]

/-- The polynomial of a form has degree `n` in the variables of each letter. -/
theorem isWeightedHomogeneous_formToMvPolynomial (F : Exponent N k n → A) :
    IsWeightedHomogeneous letterDegree (formToMvPolynomial F) fun _ ↦ n :=
  IsWeightedHomogeneous.sum _ _ _ fun β _ ↦
    isWeightedHomogeneous_monomial _ _ _ (by rw [weight_letterDegree]; exact funext β.property)

/-- The polynomial of a form has no monomial outside the exponents of degree `n` in each
letter. -/
@[simp]
theorem coeff_formToMvPolynomial_eq_zero (F : Exponent N k n → A)
    {α : Fin k × ZMod N →₀ ℕ} (hα : ¬∀ s, ∑ b, α (b, s) = n) :
    (formToMvPolynomial F).coeff α = 0 :=
  (isWeightedHomogeneous_formToMvPolynomial F).coeff_eq_zero α fun h ↦
    hα fun s ↦ by simpa [weight_letterDegree] using congrFun h s

/-- A polynomial of degree `n` in the variables of each letter is the polynomial of the form of
its coefficients at the exponents. -/
theorem eq_formToMvPolynomial_of_isWeightedHomogeneous {φ : MvPolynomial (Fin k × ZMod N) A}
    (hφ : IsWeightedHomogeneous letterDegree φ fun _ ↦ n) :
    φ = formToMvPolynomial fun β : Exponent N k n ↦ φ.coeff β.val := by
  ext α
  by_cases hα : ∀ s, ∑ b, α (b, s) = n
  · exact (coeff_formToMvPolynomial (fun β : Exponent N k n ↦ φ.coeff β.val) ⟨α, hα⟩).symm
  · rw [coeff_formToMvPolynomial_eq_zero _ hα]
    exact hφ.coeff_eq_zero α fun h ↦ hα fun s ↦ by simpa [weight_letterDegree] using congrFun h s

/-- A form is determined by its polynomial. -/
theorem formToMvPolynomial_injective :
    Function.Injective (formToMvPolynomial : (Exponent N k n → A) → _) := fun F G h ↦
  funext fun β ↦ by rw [← coeff_formToMvPolynomial F β, h, coeff_formToMvPolynomial]

end Semiring

/-- The twisted action sends a variable to a linear form in the variables of the same letter. -/
private theorem isWeightedHomogeneous_twistedAction_X (g : GL (Fin k) W) (x : Fin k × ZMod N) :
    IsWeightedHomogeneous letterDegree (T.twistedAction g (X x)) (letterDegree x) := by
  rw [twistedAction_X]
  exact IsWeightedHomogeneous.sum _ _ _ fun b _ ↦ by
    rw [smul_eq_C_mul]
    exact (isWeightedHomogeneous_X R letterDegree (b, x.2)).C_mul _

/-- The twisted action sends a monomial to a polynomial of the same degree in each letter. -/
private theorem isWeightedHomogeneous_twistedAction_monomial (g : GL (Fin k) W)
    (β : Fin k × ZMod N →₀ ℕ) :
    IsWeightedHomogeneous letterDegree (T.twistedAction g (monomial β 1))
      (Finsupp.weight letterDegree β) := by
  induction β using Finsupp.induction with
  | zero => simpa using isWeightedHomogeneous_one R letterDegree
  | single_add x m β _ _ ih =>
    rw [monomial_single_add, map_mul, map_pow, map_add, Finsupp.weight_single]
    exact ((T.isWeightedHomogeneous_twistedAction_X g x).pow m).mul ih

/-- The twisted action preserves the degree in each letter: it sends a polynomial of degree
`m s` in the variables of each letter `s` to such a polynomial. -/
theorem isWeightedHomogeneous_twistedAction (g : GL (Fin k) W)
    {φ : MvPolynomial (Fin k × ZMod N) R} {m : ZMod N → ℕ}
    (hφ : IsWeightedHomogeneous letterDegree φ m) :
    IsWeightedHomogeneous letterDegree (T.twistedAction g φ) m := by
  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun β hβ ↦ ?_
  rw [← hφ (mem_support_iff.mp hβ), ← mul_one (φ.coeff β), ← smul_eq_mul, ← smul_monomial,
    map_smul, smul_eq_C_mul]
  exact (T.isWeightedHomogeneous_twistedAction_monomial g β).C_mul _

/-- The matrix of the twisted action on forms of degree `n` in each letter: its entry at
`(α, β)` is the coefficient of `x ^ α` in `g • x ^ β`. -/
private noncomputable def actionMatrix (n : ℕ) (g : GL (Fin k) W) :
    Matrix (Exponent N k n) (Exponent N k n) R :=
  Matrix.of fun α β ↦ (T.twistedAction g (monomial β.val 1)).coeff α.val

private theorem twistedAction_formToMvPolynomial_aux (g : GL (Fin k) W)
    (F : Exponent N k n → R) :
    T.twistedAction g (formToMvPolynomial F) = formToMvPolynomial (T.actionMatrix n g *ᵥ F) := by
  classical
  have := T.neZero
  ext α
  have hmono : ∀ β : Exponent N k n, monomial β.val (F β) = F β • monomial β.val (1 : R) := by
    simp [smul_monomial]
  simp only [formToMvPolynomial, map_sum, hmono, map_smul, coeff_sum, coeff_monomial]
  simp only [smul_eq_C_mul, coeff_C_mul]
  by_cases hα : ∀ s, ∑ b, α (b, s) = n
  · symm
    rw [Finset.sum_eq_single_of_mem (⟨α, hα⟩ : Exponent N k n) (Finset.mem_univ _)
      fun γ _ hγ ↦ ite_eq_right fun h ↦ hγ (Subtype.ext h), ite_eq_left rfl]
    simp only [actionMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]
  · -- `x ^ α` occurs neither in the image (wrong degree) nor in the form
    refine (Finset.sum_eq_zero fun β _ ↦ ?_).trans (Finset.sum_eq_zero fun γ _ ↦ ?_).symm
    · rw [(T.isWeightedHomogeneous_twistedAction_monomial g β.val).coeff_eq_zero, mul_zero]
      rw [weight_letterDegree, weight_letterDegree]
      exact fun h ↦ hα fun s ↦ (congrFun h s).trans (β.property s)
    · exact ite_eq_right_iff.mpr fun h ↦ (hα (h ▸ γ.property)).elim

/-- The matrix `ρ_n(g)` of the twisted action of `g` on forms of degree `n` in each letter: its
entry at `(α, β)` is the coefficient of `x ^ α` in `g • x ^ β` (`letterRep_apply`), and
`ρ_n(g) *ᵥ F` is the form of `g • F` (`twistedAction_formToMvPolynomial`). As `g` acts on the
variables of each letter `s` separately, through `g_s`, this is the Kronecker product over the
letters of the `n`-th symmetric powers of the `g_s`; that description is not used here. -/
noncomputable def letterRep (n : ℕ) :
    GL (Fin k) W →* Matrix (Exponent N k n) (Exponent N k n) R where
  toFun := T.actionMatrix n
  map_one' := by
    classical
    ext α β
    simp [actionMatrix, coeff_monomial, Matrix.one_apply, Subtype.val_inj, eq_comm]
  map_mul' g h := by
    refine Matrix.mulVec_injective (funext fun F ↦ formToMvPolynomial_injective ?_)
    rw [← mulVec_mulVec, ← T.twistedAction_formToMvPolynomial_aux g,
      ← T.twistedAction_formToMvPolynomial_aux h, ← T.twistedAction_formToMvPolynomial_aux (g * h),
      map_mul, AlgHom.mul_apply]

/-- The entry `(α, β)` of `ρ_n(g)` is the coefficient of `x ^ α` in `g • x ^ β`. -/
theorem letterRep_apply (g : GL (Fin k) W) (α β : Exponent N k n) :
    T.letterRep n g α β = (T.twistedAction g (monomial β.val 1)).coeff α.val :=
  (rfl)

/-- `letterRep n g` is the matrix of the twisted action of `g` on forms of degree `n` in each
letter. -/
theorem twistedAction_formToMvPolynomial (g : GL (Fin k) W) (F : Exponent N k n → R) :
    T.twistedAction g (formToMvPolynomial F) = formToMvPolynomial (T.letterRep n g *ᵥ F) :=
  T.twistedAction_formToMvPolynomial_aux g F

/-! ### Conditions on translates -/

/-- `translatesIn τ I B`: the forms `F` of degree `n` in each letter such that every translate
`ρ_n(g) F` by the Levi subgroup of `τ` has its coefficients at the exponents in `B` in `I`. -/
def translatesIn (τ : Fin k → ℕ) (I : Ideal R) (B : Set (Exponent N k n)) :
    Submodule R (Exponent N k n → R) where
  carrier := {F | ∀ g ∈ leviSubgroup W τ, ∀ β ∈ B, (T.letterRep n g *ᵥ F) β ∈ I}
  add_mem' hF hG g hg β hβ := by
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact I.add_mem (hF g hg β hβ) (hG g hg β hβ)
  zero_mem' g _ β _ := by simp
  smul_mem' c F hF g hg β hβ := by
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact I.mul_mem_left c (hF g hg β hβ)

/-- Unfolding `translatesIn`. -/
theorem mem_translatesIn_iff {τ : Fin k → ℕ} {I : Ideal R} {B : Set (Exponent N k n)}
    {F : Exponent N k n → R} :
    F ∈ T.translatesIn τ I B ↔ ∀ g ∈ leviSubgroup W τ, ∀ β ∈ B, (T.letterRep n g *ᵥ F) β ∈ I :=
  Iff.rfl

/-- The translate `g = 1`: a form satisfying the conditions on translates has its own
coefficients at the exponents in `B` in `I`. -/
theorem apply_mem_of_mem_translatesIn {τ : Fin k → ℕ} {I : Ideal R} {B : Set (Exponent N k n)}
    {F : Exponent N k n → R} (hF : F ∈ T.translatesIn τ I B) {β : Exponent N k n} (hβ : β ∈ B) :
    F β ∈ I := by
  simpa using hF 1 (leviSubgroup W τ).one_mem β hβ

/-- The conditions on translates by the Levi subgroup of `τ` are stable under that subgroup. -/
theorem letterRep_mulVec_mem_translatesIn {τ : Fin k → ℕ} {I : Ideal R}
    {B : Set (Exponent N k n)} {F : Exponent N k n → R} (hF : F ∈ T.translatesIn τ I B)
    {h : GL (Fin k) W} (hh : h ∈ leviSubgroup W τ) :
    T.letterRep n h *ᵥ F ∈ T.translatesIn τ I B := fun g hg β hβ ↦ by
  rw [mulVec_mulVec, ← map_mul]
  exact hF (g * h) ((leviSubgroup W τ).mul_mem hg hh) β hβ

/-- The conditions on translates are monotone in the ideal and antitone in the set of
exponents. -/
theorem translatesIn_mono {τ : Fin k → ℕ} {I J : Ideal R} {B B' : Set (Exponent N k n)}
    (hIJ : I ≤ J) (hB : B' ⊆ B) : T.translatesIn τ I B ≤ T.translatesIn τ J B' :=
  fun _ hF g hg β hβ ↦ hIJ (hF g hg β (hB hβ))

/-- No condition is imposed by the unit ideal. -/
@[simp]
theorem translatesIn_top (τ : Fin k → ℕ) (B : Set (Exponent N k n)) :
    T.translatesIn τ ⊤ B = ⊤ :=
  eq_top_iff.mpr fun _ _ _ _ _ _ ↦ Submodule.mem_top

/-- No condition is imposed at no exponent. -/
@[simp]
theorem translatesIn_empty (τ : Fin k → ℕ) (I : Ideal R) :
    T.translatesIn τ I (∅ : Set (Exponent N k n)) = ⊤ :=
  eq_top_iff.mpr fun _ _ _ _ _ hβ ↦ hβ.elim

variable (k n) in
/-- The defect conditions `DC(a, a'; I; h)`: the forms all of whose translates by the Levi
subgroup of `twoBlockLabel a'` have their coefficients in `I` at the exponents whose defect along
`(a, a')` exceeds `h` at some letter. For `a = a'` the defect weights are those of
`defectWeight` in that case (only the positive weights occur). -/
noncomputable def defectConditions (a a' : Fin k) (I : Ideal R) (h : ℝ) :
    Submodule R (Exponent N k n → R) :=
  T.translatesIn (twoBlockLabel a') I {β | ∃ i, h < T.defect a a' i β.val}

/-- Unfolding `defectConditions`. -/
theorem mem_defectConditions_iff {a a' : Fin k} {I : Ideal R} {h : ℝ}
    {F : Exponent N k n → R} :
    F ∈ T.defectConditions k n a a' I h ↔ ∀ g ∈ leviSubgroup W (twoBlockLabel a'),
      ∀ β : Exponent N k n, (∃ i, h < T.defect a a' i β.val) → (T.letterRep n g *ᵥ F) β ∈ I :=
  Iff.rfl

/-- The defect conditions are monotone in the ideal and in the bound on the defect. -/
theorem defectConditions_mono {a a' : Fin k} {I J : Ideal R} {h h' : ℝ} (hIJ : I ≤ J)
    (hh : h ≤ h') : T.defectConditions k n a a' I h ≤ T.defectConditions k n a a' J h' :=
  T.translatesIn_mono hIJ fun _ ⟨i, hi⟩ ↦ ⟨i, hh.trans_lt hi⟩

variable (k n) in
/-- The deep forms `Deep(r, d)`: the forms every translate of which by `GL_k(W)` has only
monomials of depth at least `d`. -/
noncomputable def deepForms (r d : ℕ) : Submodule R (Exponent N k n → R) :=
  T.translatesIn (fun _ ↦ 0) ⊥ {β | T.depth r β.val < d}

/-- Unfolding `deepForms`: the Levi subgroup of the constant labelling is all of `GL_k(W)`. -/
theorem mem_deepForms_iff {r d : ℕ} {F : Exponent N k n → R} :
    F ∈ T.deepForms k n r d ↔ ∀ g : GL (Fin k) W, ∀ β : Exponent N k n,
      T.depth r β.val < d → (T.letterRep n g *ᵥ F) β = 0 := by
  simp [deepForms, mem_translatesIn_iff]

/-- Every form is deep to order `0`. -/
@[simp]
theorem deepForms_zero (r : ℕ) : T.deepForms k n r 0 = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ T.mem_deepForms_iff.mpr fun _ _ h ↦ absurd h (Nat.not_lt_zero _)

/-- Deep forms of a larger depth are deep forms of a smaller depth. -/
theorem deepForms_anti (r : ℕ) {d d' : ℕ} (hd : d ≤ d') :
    T.deepForms k n r d' ≤ T.deepForms k n r d :=
  T.translatesIn_mono le_rfl fun _ hβ ↦ lt_of_lt_of_le hβ hd

end TauCeti.FrobeniusCycle
