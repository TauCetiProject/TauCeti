/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Grading
public import TauCeti.Geometry.ScatteringDiagram.SlabAlgebra.Basic
public import TauCeti.LinearAlgebra.GradedCorrespondence.Hom
public import TauCeti.LinearAlgebra.GradedCorrespondence.Multiplication

/-!
# Graded correspondences and homogeneous transfers for slab algebras

When the base ring of a slab algebra is a monoid algebra `S[Λ]` over a commutative ring `S` and an
additive commutative monoid `Λ` of tangential exponents, the adjacent Laurent polynomial chamber
algebras `(S[Λ])[T; T⁻¹]` identify canonically via `AddMonoidAlgebra.curryAlgEquiv` with the
`(ℤ × Λ)`-graded monoid algebra `ChamberAlgebra S Λ := S[ℤ × Λ]`. Here the first component of a
degree `(n, l) : ℤ × Λ` records the transverse exponent along the chamber normal and the second
records the tangential exponent in `Λ`.

For any wall factor `q : S[Λ]` and any sets `I, J ⊆ {p : ℤ × Λ | 0 ≤ p.1}` of incoming degrees
(in particular both the full nonnegative half-space `{p | 0 ≤ p.1}` and the strictly transverse
incoming locus `{p | 0 < p.1}`), sending a homogeneous chamber monomial `s z^{(a, l)}` (`a ≥ 0`) to
`s z^l X^a` on the left and to `s z^l Y^a` on the right defines sections of the two chamber maps and
packages `SlabAlgebra S[Λ] q` into a `TauCeti.GradedCorrespondence`.

Expanding `q ^ a` in the tangential basis yields the homogeneous transfer coefficients across the
slab, natural under both tangential homomorphisms `Λ →+ Λ'` (`GradedCorrespondence.Hom`) and base
ring homomorphisms `S →+* S'` such as scalar extensions and quotient truncations `S_{k+1} → S_k`.

## Main definitions

* `TauCeti.SlabAlgebra.ChamberAlgebra`: the `(ℤ × Λ)`-graded chamber algebra `S[ℤ × Λ]`.
* `TauCeti.SlabAlgebra.gradedChamberLeft`, `TauCeti.SlabAlgebra.gradedChamberRight`: the `S`-algebra
  chamber maps into `ChamberAlgebra S Λ`.
* `TauCeti.SlabAlgebra.liftGradeLeft`, `TauCeti.SlabAlgebra.liftGradeRight`: the `S`-linear lifts
  on homogeneous pieces of `ChamberAlgebra S Λ`.
* `TauCeti.SlabAlgebra.gradedCorrespondence`: the `TauCeti.GradedCorrespondence` attached to
  `q : S[Λ]` and admissible degree sets `I, J ⊆ {p | 0 ≤ p.1}`.
* `TauCeti.SlabAlgebra.gradedCorrespondenceHom`: functoriality of `gradedCorrespondence` as a
  `GradedCorrespondence.Hom` along tangential monoid homomorphisms `Λ →+ Λ'`.

## Main results

* `TauCeti.SlabAlgebra.gradedCorrespondence_injective`: joint injectivity of the graded chamber
  span.
* `TauCeti.SlabAlgebra.gradedCorrespondence_transfer_mul`: multiplicativity of homogeneous
  transfers across the slab via `GradedCorrespondence.transfer_mul`.
* `TauCeti.SlabAlgebra.coe_transfer_single` and `TauCeti.SlabAlgebra.coe_transfer_single_sub`:
  explicit homogeneous transfer coefficients in terms of `(q ^ a).coeff`.
* `TauCeti.SlabAlgebra.mapRingHom_coe_transfer`: compatibility of homogeneous transfers with
  scalar extensions and quotient truncations `S →+* S'`.
* `TauCeti.SlabAlgebra.gradedChamberRight_binomial`: for `q = t (1 + w)` in `S[ℤ]`, the incoming
  lift `w^b X^a` maps in the right chamber to `∑_{j ≤ a} t^a binom(a, j) y^{-a} w^{b + j}`.

## References

* [M. Gross and B. Siebert, *An Invitation to Toric Degenerations*][GrossSiebert2011], §2.3
  (arXiv:0808.2749).
* [M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*][GrossHackingSiebert2022], §3, Definitions 3.1–3.3 (arXiv:1601.07081).
-/

public noncomputable section

namespace TauCeti.SlabAlgebra

/-- The `(ℤ × Λ)`-graded chamber algebra `S[ℤ × Λ]`, whose first degree component is the transverse
Laurent exponent and whose second component is the tangential exponent in `Λ`. -/
abbrev ChamberAlgebra (S : Type*) [Semiring S] (Λ : Type*) : Type _ :=
  AddMonoidAlgebra S (ℤ × Λ)

section Chamber

variable {S : Type*} [CommRing S] {Λ : Type*} [AddCommMonoid Λ]

/-- Canonical `S`-algebra equivalence between `LaurentPolynomial (AddMonoidAlgebra S Λ)` and the
`(ℤ × Λ)`-graded monoid algebra `ChamberAlgebra S Λ`. -/
def chamberCurryEquiv (S : Type*) [CommRing S] (Λ : Type*) [AddCommMonoid Λ] :
    LaurentPolynomial (AddMonoidAlgebra S Λ) ≃ₐ[S] ChamberAlgebra S Λ :=
  (AddMonoidAlgebra.curryAlgEquiv S).symm

@[simp]
theorem chamberCurryEquiv_C_mul_T_single (n : ℤ) (l : Λ) (s : S) :
    chamberCurryEquiv S Λ
        (LaurentPolynomial.C (AddMonoidAlgebra.single l s) * LaurentPolynomial.T n) =
      AddMonoidAlgebra.single (n, l) s := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact AddMonoidAlgebra.curryAlgEquiv_symm_single n l s

@[simp]
theorem chamberCurryEquiv_C_single (l : Λ) (s : S) :
    chamberCurryEquiv S Λ (LaurentPolynomial.C (AddMonoidAlgebra.single l s)) =
      AddMonoidAlgebra.single (0, l) s := by
  simpa using chamberCurryEquiv_C_mul_T_single 0 l s

@[simp]
theorem chamberCurryEquiv_T (n : ℤ) :
    chamberCurryEquiv S Λ (LaurentPolynomial.T n) = AddMonoidAlgebra.single (n, 0) 1 := by
  have h1 : (1 : AddMonoidAlgebra S Λ) = AddMonoidAlgebra.single 0 1 := rfl
  rw [← one_mul (LaurentPolynomial.T n), ← map_one LaurentPolynomial.C, h1,
    chamberCurryEquiv_C_mul_T_single]

@[simp]
theorem coeff_chamberCurryEquiv (f : LaurentPolynomial (AddMonoidAlgebra S Λ)) (p : ℤ × Λ) :
    (chamberCurryEquiv S Λ f).coeff p = (f.coeff p.1).coeff p.2 := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single n g =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ =>
      rw [AddMonoidAlgebra.single_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        hg₁, hg₂, ← AddMonoidAlgebra.single_add, AddMonoidAlgebra.coeff_single,
        AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
      by_cases hn : n = p.1 <;> simp [hn]
    | single l s =>
      classical
      rw [LaurentPolynomial.single_eq_C_mul_T, chamberCurryEquiv_C_mul_T_single,
        ← LaurentPolynomial.single_eq_C_mul_T]
      rcases p with ⟨p₁, p₂⟩
      by_cases hn : n = p₁ <;> by_cases hl : l = p₂ <;>
        simp [-LaurentPolynomial.single_eq_C_mul_T, hn, hl]

/-- Left chamber `S`-algebra homomorphism `SlabAlgebra S[Λ] q →ₐ[S] ChamberAlgebra S Λ`. -/
def gradedChamberLeft (q : AddMonoidAlgebra S Λ) :
    SlabAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] ChamberAlgebra S Λ :=
  (chamberCurryEquiv S Λ).toAlgHom.comp ((chamberLeft q).restrictScalars S)

/-- Right chamber `S`-algebra homomorphism `SlabAlgebra S[Λ] q →ₐ[S] ChamberAlgebra S Λ`. -/
def gradedChamberRight (q : AddMonoidAlgebra S Λ) :
    SlabAlgebra (AddMonoidAlgebra S Λ) q →ₐ[S] ChamberAlgebra S Λ :=
  (chamberCurryEquiv S Λ).toAlgHom.comp ((chamberRight q).restrictScalars S)

theorem gradedChamberLeft_apply (q : AddMonoidAlgebra S Λ)
    (z : SlabAlgebra (AddMonoidAlgebra S Λ) q) :
    gradedChamberLeft q z = chamberCurryEquiv S Λ (chamberLeft q z) :=
  (rfl)

theorem gradedChamberRight_apply (q : AddMonoidAlgebra S Λ)
    (z : SlabAlgebra (AddMonoidAlgebra S Λ) q) :
    gradedChamberRight q z = chamberCurryEquiv S Λ (chamberRight q z) :=
  (rfl)

@[simp]
theorem gradedChamberLeft_algebraMap_single (q : AddMonoidAlgebra S Λ) (l : Λ) (s : S) :
    gradedChamberLeft q
        (algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
          (AddMonoidAlgebra.single l s)) =
      AddMonoidAlgebra.single (0, l) s := by
  rw [gradedChamberLeft_apply, AlgHom.commutes, ← LaurentPolynomial.C_eq_algebraMap,
    chamberCurryEquiv_C_single]

@[simp]
theorem gradedChamberRight_algebraMap_single (q : AddMonoidAlgebra S Λ) (l : Λ) (s : S) :
    gradedChamberRight q
        (algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
          (AddMonoidAlgebra.single l s)) =
      AddMonoidAlgebra.single (0, l) s := by
  rw [gradedChamberRight_apply, AlgHom.commutes, ← LaurentPolynomial.C_eq_algebraMap,
    chamberCurryEquiv_C_single]

@[simp]
theorem gradedChamberLeft_X_pow (q : AddMonoidAlgebra S Λ) (a : ℕ) :
    gradedChamberLeft q (X q ^ a) = AddMonoidAlgebra.single ((a : ℤ), 0) 1 := by
  rw [gradedChamberLeft_apply, chamberLeft_X_pow, chamberCurryEquiv_T]

@[simp]
theorem gradedChamberRight_Y_pow (q : AddMonoidAlgebra S Λ) (a : ℕ) :
    gradedChamberRight q (Y q ^ a) = AddMonoidAlgebra.single ((a : ℤ), 0) 1 := by
  rw [gradedChamberRight_apply, chamberRight_Y_pow, chamberCurryEquiv_T]

@[simp]
theorem gradedChamberRight_swap (q : AddMonoidAlgebra S Λ)
    (z : SlabAlgebra (AddMonoidAlgebra S Λ) q) :
    gradedChamberRight q (swap q z) = gradedChamberLeft q z := by
  rw [gradedChamberRight_apply, chamberRight_swap, gradedChamberLeft_apply]

@[simp]
theorem gradedChamberLeft_swap (q : AddMonoidAlgebra S Λ)
    (z : SlabAlgebra (AddMonoidAlgebra S Λ) q) :
    gradedChamberLeft q (swap q z) = gradedChamberRight q z := by
  rw [gradedChamberLeft_apply, chamberLeft_swap, gradedChamberRight_apply]

/-- The graded chamber homomorphisms out of `SlabAlgebra S[Λ] q` are jointly injective. -/
theorem gradedChamberLeft_prod_gradedChamberRight_injective (q : AddMonoidAlgebra S Λ) :
    Function.Injective
      ((gradedChamberLeft q).toLinearMap.prod (gradedChamberRight q).toLinearMap) := by
  intro z w h
  obtain ⟨hL, hR⟩ := Prod.mk.inj h
  exact chamberLeft_prod_chamberRight_injective q <|
    Prod.ext ((chamberCurryEquiv S Λ).injective hL) ((chamberCurryEquiv S Λ).injective hR)

/-! ### Homogeneous lifts and `GradedCorrespondence` -/

/-- `S`-linear incoming left lift on the `p`-th homogeneous piece of `ChamberAlgebra S Λ`, sending
`single p s` to `s z^{p.2} X^{p.1.toNat}`. -/
def liftGradeLeft (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ) :
    AddMonoidAlgebra.grade S p →ₗ[S] SlabAlgebra (AddMonoidAlgebra S Λ) q where
  toFun u :=
    algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
      (AddMonoidAlgebra.single p.2 (u.1.coeff p)) * X q ^ p.1.toNat
  map_add' u v := by
    simp [add_mul]
  map_smul' r u := by
    have hsmul : AddMonoidAlgebra.single p.2 (r * u.1.coeff p) =
        r • AddMonoidAlgebra.single p.2 (u.1.coeff p) := by
      rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
    have htower : algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
        (r • AddMonoidAlgebra.single p.2 (u.1.coeff p)) =
        r • algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
          (AddMonoidAlgebra.single p.2 (u.1.coeff p)) :=
      map_smul (IsScalarTower.toAlgHom S (AddMonoidAlgebra S Λ)
        (SlabAlgebra (AddMonoidAlgebra S Λ) q)) r _
    simp only [Submodule.coe_smul_of_tower, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, hsmul,
      RingHom.id_apply, htower, smul_mul_assoc]

/-- `S`-linear incoming right lift on the `p`-th homogeneous piece of `ChamberAlgebra S Λ`, sending
`single p s` to `s z^{p.2} Y^{p.1.toNat}`. -/
def liftGradeRight (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ) :
    AddMonoidAlgebra.grade S p →ₗ[S] SlabAlgebra (AddMonoidAlgebra S Λ) q where
  toFun u :=
    algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
      (AddMonoidAlgebra.single p.2 (u.1.coeff p)) * Y q ^ p.1.toNat
  map_add' u v := by
    simp [add_mul]
  map_smul' r u := by
    have hsmul : AddMonoidAlgebra.single p.2 (r * u.1.coeff p) =
        r • AddMonoidAlgebra.single p.2 (u.1.coeff p) := by
      rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
    have htower : algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
        (r • AddMonoidAlgebra.single p.2 (u.1.coeff p)) =
        r • algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
          (AddMonoidAlgebra.single p.2 (u.1.coeff p)) :=
      map_smul (IsScalarTower.toAlgHom S (AddMonoidAlgebra S Λ)
        (SlabAlgebra (AddMonoidAlgebra S Λ) q)) r _
    simp only [Submodule.coe_smul_of_tower, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, hsmul,
      RingHom.id_apply, htower, smul_mul_assoc]

theorem liftGradeLeft_apply (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (u : AddMonoidAlgebra.grade S p) :
    liftGradeLeft q p u =
      algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
        (AddMonoidAlgebra.single p.2 (u.1.coeff p)) * X q ^ p.1.toNat :=
  (rfl)

theorem liftGradeRight_apply (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (u : AddMonoidAlgebra.grade S p) :
    liftGradeRight q p u =
      algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
        (AddMonoidAlgebra.single p.2 (u.1.coeff p)) * Y q ^ p.1.toNat :=
  (rfl)

@[simp]
theorem liftGradeLeft_single (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ) (s : S) :
    liftGradeLeft q p ⟨AddMonoidAlgebra.single p s, AddMonoidAlgebra.single_mem_grade p s⟩ =
      algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
        (AddMonoidAlgebra.single p.2 s) * X q ^ p.1.toNat := by
  simp [liftGradeLeft]

@[simp]
theorem liftGradeRight_single (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ) (s : S) :
    liftGradeRight q p ⟨AddMonoidAlgebra.single p s, AddMonoidAlgebra.single_mem_grade p s⟩ =
      algebraMap (AddMonoidAlgebra S Λ) (SlabAlgebra (AddMonoidAlgebra S Λ) q)
        (AddMonoidAlgebra.single p.2 s) * Y q ^ p.1.toNat := by
  simp [liftGradeRight]

@[simp]
theorem swap_liftGradeLeft (q : AddMonoidAlgebra S Λ) (p : ℤ × Λ)
    (u : AddMonoidAlgebra.grade S p) :
    swap q (liftGradeLeft q p u) = liftGradeRight q p u := by
  simp [liftGradeLeft, liftGradeRight]

/-- On any homogeneous piece with nonnegative transverse degree `0 ≤ p.1`, `liftGradeLeft` is a
section of `gradedChamberLeft`. -/
theorem gradedChamberLeft_comp_liftGradeLeft (q : AddMonoidAlgebra S Λ) {p : ℤ × Λ}
    (hp : 0 ≤ p.1) :
    (gradedChamberLeft q).toLinearMap.comp (liftGradeLeft q p) =
      (AddMonoidAlgebra.grade S p).subtype := by
  apply LinearMap.ext
  intro u
  have hp' : (p.1.toNat : ℤ) = p.1 := Int.toNat_of_nonneg hp
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, liftGradeLeft, LinearMap.coe_mk,
    AddHom.coe_mk, map_mul, gradedChamberLeft_algebraMap_single, gradedChamberLeft_X_pow,
    AddMonoidAlgebra.single_mul_single, Prod.mk_add_mk, zero_add, add_zero, mul_one, hp',
    Submodule.coe_subtype]
  exact (AddMonoidAlgebra.eq_single_coeff_of_mem_grade u.2).symm

/-- On any homogeneous piece with nonnegative transverse degree `0 ≤ p.1`, `liftGradeRight` is a
section of `gradedChamberRight`. -/
theorem gradedChamberRight_comp_liftGradeRight (q : AddMonoidAlgebra S Λ) {p : ℤ × Λ}
    (hp : 0 ≤ p.1) :
    (gradedChamberRight q).toLinearMap.comp (liftGradeRight q p) =
      (AddMonoidAlgebra.grade S p).subtype := by
  apply LinearMap.ext
  intro u
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← swap_liftGradeLeft,
    gradedChamberRight_swap]
  exact LinearMap.congr_fun (gradedChamberLeft_comp_liftGradeLeft q hp) u

/-- Incoming left lifts preserve products of homogeneous chamber elements with nonnegative
transverse degrees. -/
theorem liftGradeLeft_mul (q : AddMonoidAlgebra S Λ) {p₁ p₂ : ℤ × Λ}
    (hp₁ : 0 ≤ p₁.1) (hp₂ : 0 ≤ p₂.1)
    (u₁ : AddMonoidAlgebra.grade S p₁) (u₂ : AddMonoidAlgebra.grade S p₂) :
    liftGradeLeft q (p₁ + p₂) ⟨u₁.1 * u₂.1, SetLike.mul_mem_graded u₁.2 u₂.2⟩ =
      liftGradeLeft q p₁ u₁ * liftGradeLeft q p₂ u₂ := by
  have hcoeff : (u₁.1 * u₂.1).coeff (p₁ + p₂) = u₁.1.coeff p₁ * u₂.1.coeff p₂ := by
    conv_lhs =>
      rw [AddMonoidAlgebra.eq_single_coeff_of_mem_grade u₁.2,
        AddMonoidAlgebra.eq_single_coeff_of_mem_grade u₂.2]
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have htoNat : (p₁ + p₂).1.toNat = p₁.1.toNat + p₂.1.toNat := by
    rw [Prod.fst_add]
    omega
  rw [liftGradeLeft_apply, liftGradeLeft_apply, liftGradeLeft_apply]
  dsimp only
  rw [hcoeff, Prod.snd_add, ← AddMonoidAlgebra.single_mul_single, map_mul, htoNat, pow_add]
  ring

/-- Incoming right lifts preserve products of homogeneous chamber elements with nonnegative
transverse degrees. -/
theorem liftGradeRight_mul (q : AddMonoidAlgebra S Λ) {p₁ p₂ : ℤ × Λ}
    (hp₁ : 0 ≤ p₁.1) (hp₂ : 0 ≤ p₂.1)
    (u₁ : AddMonoidAlgebra.grade S p₁) (u₂ : AddMonoidAlgebra.grade S p₂) :
    liftGradeRight q (p₁ + p₂) ⟨u₁.1 * u₂.1, SetLike.mul_mem_graded u₁.2 u₂.2⟩ =
      liftGradeRight q p₁ u₁ * liftGradeRight q p₂ u₂ := by
  rw [← swap_liftGradeLeft, liftGradeLeft_mul q hp₁ hp₂, map_mul, swap_liftGradeLeft,
    swap_liftGradeLeft]

/-- The `TauCeti.GradedCorrespondence` across `SlabAlgebra S[Λ] q` for any incoming admissible
degree sets `I, J ⊆ {p : ℤ × Λ | 0 ≤ p.1}`. -/
def gradedCorrespondence (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    GradedCorrespondence (B := SlabAlgebra (AddMonoidAlgebra S Λ) q)
      (AddMonoidAlgebra.grade S : (ℤ × Λ) → Submodule S (ChamberAlgebra S Λ))
      (AddMonoidAlgebra.grade S : (ℤ × Λ) → Submodule S (ChamberAlgebra S Λ)) I J where
  left := (gradedChamberLeft q).toLinearMap
  right := (gradedChamberRight q).toLinearMap
  liftLeft i := liftGradeLeft q i.1
  liftRight j := liftGradeRight q j.1
  left_liftLeft i := gradedChamberLeft_comp_liftGradeLeft q (hI i.1 i.2)
  right_liftRight j := gradedChamberRight_comp_liftGradeRight q (hJ j.1 j.2)

@[simp]
theorem gradedCorrespondence_left (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    (gradedCorrespondence q hI hJ).left = (gradedChamberLeft q).toLinearMap :=
  (rfl)

@[simp]
theorem gradedCorrespondence_right (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    (gradedCorrespondence q hI hJ).right = (gradedChamberRight q).toLinearMap :=
  (rfl)

@[simp]
theorem gradedCorrespondence_liftLeft (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) (i : I) :
    (gradedCorrespondence q hI hJ).liftLeft i = liftGradeLeft q i.1 :=
  (rfl)

@[simp]
theorem gradedCorrespondence_liftRight (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) (j : J) :
    (gradedCorrespondence q hI hJ).liftRight j = liftGradeRight q j.1 :=
  (rfl)

/-- The two legs of `gradedCorrespondence` are jointly injective. -/
theorem gradedCorrespondence_injective (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1) :
    Function.Injective
      ((gradedCorrespondence q hI hJ).left.prod (gradedCorrespondence q hI hJ).right) :=
  gradedChamberLeft_prod_gradedChamberRight_injective q

/-- Homogeneous transfer of a product across `gradedCorrespondence` equals the finite convolution
of the transfers of its factors. -/
theorem gradedCorrespondence_transfer_mul [DecidableEq Λ] (q : AddMonoidAlgebra S Λ)
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i j : I) (hij : (i : ℤ × Λ) + (j : ℤ × Λ) ∈ I)
    (a : AddMonoidAlgebra.grade S i.1) (b : AddMonoidAlgebra.grade S j.1)
    [∀ k (v : AddMonoidAlgebra.grade S (k : ℤ × Λ)), Decidable (v ≠ 0)] (k : ℤ × Λ) :
    ((gradedCorrespondence q hI hJ).transfer ⟨(i : ℤ × Λ) + (j : ℤ × Λ), hij⟩ k
      ⟨(a : ChamberAlgebra S Λ) * (b : ChamberAlgebra S Λ),
        SetLike.mul_mem_graded a.property b.property⟩ : ChamberAlgebra S Λ) =
      ∑ p ∈ (DirectSum.decompose (AddMonoidAlgebra.grade S)
          ((gradedCorrespondence q hI hJ).right
            ((gradedCorrespondence q hI hJ).liftLeft i a))).support ×ˢ
        (DirectSum.decompose (AddMonoidAlgebra.grade S)
          ((gradedCorrespondence q hI hJ).right
            ((gradedCorrespondence q hI hJ).liftLeft j b))).support
        with p.1 + p.2 = k,
          ((gradedCorrespondence q hI hJ).transfer i p.1 a : ChamberAlgebra S Λ) *
            ((gradedCorrespondence q hI hJ).transfer j p.2 b : ChamberAlgebra S Λ) := by
  refine GradedCorrespondence.transfer_mul (gradedCorrespondence q hI hJ) i j hij a b ?_ k
  simp only [gradedCorrespondence_right, gradedCorrespondence_liftLeft, AlgHom.toLinearMap_apply]
  rw [liftGradeLeft_mul q (hI i.1 i.2) (hI j.1 j.2) a b, map_mul]

private theorem mapDomain_chamberCurryEquiv_C {Λ' : Type*} [AddCommMonoid Λ']
    (φ : Λ →+ Λ') (g : AddMonoidAlgebra S Λ) :
    AddMonoidAlgebra.mapDomainAlgHom S S ((AddMonoidHom.id ℤ).prodMap φ)
        (chamberCurryEquiv S Λ (LaurentPolynomial.C g)) =
      chamberCurryEquiv S Λ'
        (LaurentPolynomial.C (AddMonoidAlgebra.mapDomainAlgHom S S φ g)) := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, map_add (AddMonoidAlgebra.mapDomainAlgHom S S φ),
      map_add LaurentPolynomial.C, map_add (chamberCurryEquiv S Λ')]
  | single l s => simp [AddMonoidHom.coe_prodMap]

/-- `gradedChamberLeft` commutes with tangential monoid homomorphisms `φ : Λ →+ Λ'`. -/
theorem mapDomain_comp_gradedChamberLeft {Λ' : Type*} [AddCommMonoid Λ']
    {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S Λ'}
    (φ : Λ →+ Λ') (hφ : AddMonoidAlgebra.mapDomainAlgHom S S φ q = q') :
    (AddMonoidAlgebra.mapDomainAlgHom S S ((AddMonoidHom.id ℤ).prodMap φ)).comp
        (gradedChamberLeft q) =
      (gradedChamberLeft q').comp (mapAlgHom (AddMonoidAlgebra.mapDomainAlgHom S S φ) hφ) := by
  apply algHom_ext_of_tower
  · intro g
    simp only [AlgHom.comp_apply, mapAlgHom_algebraMap, gradedChamberLeft_apply, AlgHom.commutes,
      ← LaurentPolynomial.C_eq_algebraMap]
    exact mapDomain_chamberCurryEquiv_C φ g
  · simp [gradedChamberLeft, AddMonoidHom.coe_prodMap]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, mapAlgHom_Y, gradedChamberLeft_apply,
      gradedChamberLeft_apply, chamberLeft_Y, chamberLeft_Y, map_mul, map_mul, map_mul,
      mapDomain_chamberCurryEquiv_C, hφ]
    simp [AddMonoidHom.coe_prodMap]

/-- `gradedChamberRight` commutes with tangential monoid homomorphisms `φ : Λ →+ Λ'`. -/
theorem mapDomain_comp_gradedChamberRight {Λ' : Type*} [AddCommMonoid Λ']
    {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S Λ'}
    (φ : Λ →+ Λ') (hφ : AddMonoidAlgebra.mapDomainAlgHom S S φ q = q') :
    (AddMonoidAlgebra.mapDomainAlgHom S S ((AddMonoidHom.id ℤ).prodMap φ)).comp
        (gradedChamberRight q) =
      (gradedChamberRight q').comp (mapAlgHom (AddMonoidAlgebra.mapDomainAlgHom S S φ) hφ) := by
  apply algHom_ext_of_tower
  · intro g
    simp only [AlgHom.comp_apply, mapAlgHom_algebraMap, gradedChamberRight_apply, AlgHom.commutes,
      ← LaurentPolynomial.C_eq_algebraMap]
    exact mapDomain_chamberCurryEquiv_C φ g
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, mapAlgHom_X, gradedChamberRight_apply,
      gradedChamberRight_apply, chamberRight_X, chamberRight_X, map_mul, map_mul, map_mul,
      mapDomain_chamberCurryEquiv_C, hφ]
    simp [AddMonoidHom.coe_prodMap]
  · simp [gradedChamberRight, AddMonoidHom.coe_prodMap]

/-- A tangential monoid homomorphism `φ : Λ →+ Λ'` sending `q` to `q'` induces a morphism of
graded correspondences (`GradedCorrespondence.Hom`) over the degree map `Prod.map id φ`. -/
def gradedCorrespondenceHom {Λ' : Type*} [AddCommMonoid Λ']
    {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S Λ'}
    (φ : Λ →+ Λ') (hφ : AddMonoidAlgebra.mapDomainAlgHom S S φ q = q')
    {I J : Set (ℤ × Λ)} {I' J' : Set (ℤ × Λ')}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (hI' : ∀ p ∈ I', 0 ≤ p.1) (hJ' : ∀ p ∈ J', 0 ≤ p.1)
    (hmapI : Set.MapsTo (Prod.map id φ) I I') (hmapJ : Set.MapsTo (Prod.map id φ) J J') :
    GradedCorrespondence.Hom (gradedCorrespondence q hI hJ) (gradedCorrespondence q' hI' hJ')
      (Prod.map id φ) (Prod.map id φ) where
  middle := (mapAlgHom (AddMonoidAlgebra.mapDomainAlgHom S S φ) hφ).toLinearMap
  left := (AddMonoidAlgebra.mapDomainAlgHom S S ((AddMonoidHom.id ℤ).prodMap φ)).toLinearMap
  right := (AddMonoidAlgebra.mapDomainAlgHom S S ((AddMonoidHom.id ℤ).prodMap φ)).toLinearMap
  left_comm := congrArg AlgHom.toLinearMap (mapDomain_comp_gradedChamberLeft φ hφ)
  right_comm := congrArg AlgHom.toLinearMap (mapDomain_comp_gradedChamberRight φ hφ)
  left_mem p u hu := by
    rw [AddMonoidAlgebra.eq_single_coeff_of_mem_grade hu]
    simp only [AlgHom.toLinearMap_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single, AddMonoidHom.coe_prodMap]
    exact AddMonoidAlgebra.single_mem_grade (Prod.map id φ p) (u.coeff p)
  right_mem p u hu := by
    rw [AddMonoidAlgebra.eq_single_coeff_of_mem_grade hu]
    simp only [AlgHom.toLinearMap_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single, AddMonoidHom.coe_prodMap]
    exact AddMonoidAlgebra.single_mem_grade (Prod.map id φ p) (u.coeff p)
  admissible_left := hmapI
  admissible_right := hmapJ
  middle_liftLeft i u := by
    obtain ⟨s, rfl⟩ : ∃ s : S, u = ⟨AddMonoidAlgebra.single i.1 s,
        AddMonoidAlgebra.single_mem_grade i.1 s⟩ :=
      ⟨u.1.coeff i.1, Subtype.ext (AddMonoidAlgebra.eq_single_coeff_of_mem_grade u.2)⟩
    rw [gradedCorrespondence_liftLeft, gradedCorrespondence_liftLeft, liftGradeLeft_single,
      liftGradeLeft_apply]
    simp [AddMonoidHom.coe_prodMap]
  middle_liftRight j u := by
    obtain ⟨s, rfl⟩ : ∃ s : S, u = ⟨AddMonoidAlgebra.single j.1 s,
        AddMonoidAlgebra.single_mem_grade j.1 s⟩ :=
      ⟨u.1.coeff j.1, Subtype.ext (AddMonoidAlgebra.eq_single_coeff_of_mem_grade u.2)⟩
    rw [gradedCorrespondence_liftRight, gradedCorrespondence_liftRight, liftGradeRight_single,
      liftGradeRight_apply]
    simp [AddMonoidHom.coe_prodMap]

/-! ### Explicit homogeneous transfer coefficients, base change, and binomial check -/

/-- Right chamber image of an incoming left monomial `s z^{(a, l)}`. -/
theorem gradedChamberRight_liftGradeLeft_single (q : AddMonoidAlgebra S Λ) (a : ℕ) (l : Λ) (s : S) :
    gradedChamberRight q
        (liftGradeLeft q ((a : ℤ), l)
          ⟨AddMonoidAlgebra.single ((a : ℤ), l) s,
            AddMonoidAlgebra.single_mem_grade ((a : ℤ), l) s⟩) =
      chamberCurryEquiv S Λ
        (LaurentPolynomial.C (AddMonoidAlgebra.single l s * q ^ a) *
          LaurentPolynomial.T (-(a : ℤ))) := by
  rw [liftGradeLeft_single, Int.toNat_natCast, map_mul, gradedChamberRight_apply,
    gradedChamberRight_apply, AlgHom.commutes, ← LaurentPolynomial.C_eq_algebraMap,
    chamberRight_X_pow, ← map_mul, ← mul_assoc, ← map_mul]

/-- Explicit homogeneous transfer of an incoming left monomial `s z^{(a, l)}` to target degree
`p' : ℤ × Λ` by expanding `q ^ a` in the tangential basis. -/
theorem coe_transfer_single [DecidableEq Λ] (q : AddMonoidAlgebra S Λ) {I J : Set (ℤ × Λ)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (a : ℕ) (l : Λ) (hi : ((a : ℤ), l) ∈ I) (s : S) (p' : ℤ × Λ) :
    ((gradedCorrespondence q hI hJ).transfer ⟨((a : ℤ), l), hi⟩ p'
        ⟨AddMonoidAlgebra.single ((a : ℤ), l) s,
          AddMonoidAlgebra.single_mem_grade ((a : ℤ), l) s⟩ : ChamberAlgebra S Λ) =
      if p'.1 = -(a : ℤ) then
        AddMonoidAlgebra.single p' ((AddMonoidAlgebra.single l s * q ^ a).coeff p'.2)
      else 0 := by
  rw [GradedCorrespondence.transfer_apply, AddMonoidAlgebra.coe_decompose_grade,
    gradedCorrespondence_right, gradedCorrespondence_liftLeft, AlgHom.toLinearMap_apply,
    gradedChamberRight_liftGradeLeft_single, coeff_chamberCurryEquiv,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  by_cases hp : p'.1 = -(a : ℤ) <;> simp [hp]

/-- Compatibility of homogeneous slab transfers with arbitrary ring homomorphisms `f : S →+* S'`
(including scalar extensions and quotient truncations `S_{k+1} → S_k`). -/
theorem mapRingHom_coe_transfer {S' : Type*} [CommRing S'] [DecidableEq Λ]
    {q : AddMonoidAlgebra S Λ} {q' : AddMonoidAlgebra S' Λ}
    (f : S →+* S') (hf : AddMonoidAlgebra.mapRingHom Λ f q = q')
    {I J : Set (ℤ × Λ)} (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (i : I) (u : AddMonoidAlgebra.grade S i.1) (p' : ℤ × Λ) :
    AddMonoidAlgebra.mapRingHom (ℤ × Λ) f
        ((gradedCorrespondence q hI hJ).transfer i p' u : ChamberAlgebra S Λ) =
      ((gradedCorrespondence q' hI hJ).transfer i p'
        ⟨AddMonoidAlgebra.mapRingHom (ℤ × Λ) f u.1,
          AddMonoidAlgebra.mapRingHom_mem_grade f u.2⟩ :
        ChamberAlgebra S' Λ) := by
  rcases i with ⟨⟨n, l⟩, hi⟩
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (hI (n, l) hi)
  obtain ⟨s, rfl⟩ : ∃ s : S, u = ⟨AddMonoidAlgebra.single ((a : ℤ), l) s,
      AddMonoidAlgebra.single_mem_grade ((a : ℤ), l) s⟩ :=
    ⟨u.1.coeff ((a : ℤ), l), Subtype.ext (AddMonoidAlgebra.eq_single_coeff_of_mem_grade u.2)⟩
  have hmap : (⟨AddMonoidAlgebra.mapRingHom (ℤ × Λ) f (AddMonoidAlgebra.single ((a : ℤ), l) s),
      AddMonoidAlgebra.mapRingHom_mem_grade f
        (AddMonoidAlgebra.single_mem_grade ((a : ℤ), l) s)⟩ :
      AddMonoidAlgebra.grade S' ((a : ℤ), l)) =
      ⟨AddMonoidAlgebra.single ((a : ℤ), l) (f s),
        AddMonoidAlgebra.single_mem_grade ((a : ℤ), l) (f s)⟩ :=
    Subtype.ext (AddMonoidAlgebra.mapRingHom_single f ((a : ℤ), l) s)
  rw [hmap, coe_transfer_single, coe_transfer_single]
  split_ifs
  · rw [AddMonoidAlgebra.mapRingHom_single, ← hf, ← map_pow,
      ← AddMonoidAlgebra.mapRingHom_single f l s, ← map_mul, AddMonoidAlgebra.coeff_mapRingHom]
  · simp

end Chamber

section Lattice

variable {S : Type*} [CommRing S]

/-- Over a tangential lattice (`AddCommGroup G`), the transferred coefficient at `(-(a : ℤ), m)` of
`s z^{(a, l)}` is `s * (q ^ a).coeff (m - l)`. -/
theorem coe_transfer_single_sub {G : Type*} [AddCommGroup G] [DecidableEq G]
    (q : AddMonoidAlgebra S G) {I J : Set (ℤ × G)}
    (hI : ∀ p ∈ I, 0 ≤ p.1) (hJ : ∀ p ∈ J, 0 ≤ p.1)
    (a : ℕ) (l m : G) (hi : ((a : ℤ), l) ∈ I) (s : S) :
    ((gradedCorrespondence q hI hJ).transfer ⟨((a : ℤ), l), hi⟩ (-(a : ℤ), m)
        ⟨AddMonoidAlgebra.single ((a : ℤ), l) s,
          AddMonoidAlgebra.single_mem_grade ((a : ℤ), l) s⟩ : ChamberAlgebra S G) =
      AddMonoidAlgebra.single (-(a : ℤ), m) (s * (q ^ a).coeff (m - l)) := by
  rw [coe_transfer_single]
  simp [AddMonoidAlgebra.coeff_single_mul_apply, neg_add_eq_sub]

/-- Binomial expansion of the right chamber image of an incoming left monomial `w^b X^a` in
`S[w, w⁻¹][X, Y] ⧸ (X Y - t (1 + w))`:
`gradedChamberRight q (w^b X^a) = ∑_{j ≤ a} t^a binom(a, j) y^{-a} w^{b + j}`. -/
theorem gradedChamberRight_binomial (t : S) (a : ℕ) (b : ℤ) :
    let q : AddMonoidAlgebra S ℤ :=
      AddMonoidAlgebra.single 0 t * (1 + AddMonoidAlgebra.single 1 1)
    gradedChamberRight q
        (algebraMap (AddMonoidAlgebra S ℤ) (SlabAlgebra (AddMonoidAlgebra S ℤ) q)
          (AddMonoidAlgebra.single b 1) * X q ^ a) =
      ∑ j ∈ Finset.range (a + 1),
        AddMonoidAlgebra.single (-(a : ℤ), b + (j : ℤ)) (t ^ a * (a.choose j : S)) := by
  intro q
  have hlift := gradedChamberRight_liftGradeLeft_single q a b 1
  rw [liftGradeLeft_single, Int.toNat_natCast] at hlift
  rw [hlift]
  have hqpow : AddMonoidAlgebra.single b (1 : S) * q ^ a =
      ∑ j ∈ Finset.range (a + 1),
        AddMonoidAlgebra.single (b + (j : ℤ)) (t ^ a * (a.choose j : S)) := by
    have h1w : (1 + AddMonoidAlgebra.single (1 : ℤ) (1 : S)) ^ a =
        ∑ j ∈ Finset.range (a + 1), AddMonoidAlgebra.single (j : ℤ) (a.choose j : S) := by
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcast : (a.choose j : AddMonoidAlgebra S ℤ) =
          AddMonoidAlgebra.single 0 (a.choose j : S) := by
        rw [← map_natCast (algebraMap S (AddMonoidAlgebra S ℤ))]
        rfl
      rw [one_pow, mul_one, AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one,
        hcast, AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
    calc
      AddMonoidAlgebra.single b (1 : S) * q ^ a
          = AddMonoidAlgebra.single b (1 : S) *
              (AddMonoidAlgebra.single 0 (t ^ a) *
                (1 + AddMonoidAlgebra.single (1 : ℤ) (1 : S)) ^ a) := by
            rw [mul_pow, AddMonoidAlgebra.single_pow, nsmul_zero]
      _ = AddMonoidAlgebra.single b (t ^ a) *
            ∑ j ∈ Finset.range (a + 1), AddMonoidAlgebra.single (j : ℤ) (a.choose j : S) := by
            rw [← mul_assoc, AddMonoidAlgebra.single_mul_single, add_zero, one_mul, h1w]
      _ = ∑ j ∈ Finset.range (a + 1),
            AddMonoidAlgebra.single (b + (j : ℤ)) (t ^ a * (a.choose j : S)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [AddMonoidAlgebra.single_mul_single]
  rw [hqpow, map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact chamberCurryEquiv_C_mul_T_single (-(a : ℤ)) (b + (j : ℤ)) (t ^ a * (a.choose j : S))

end Lattice

end TauCeti.SlabAlgebra
