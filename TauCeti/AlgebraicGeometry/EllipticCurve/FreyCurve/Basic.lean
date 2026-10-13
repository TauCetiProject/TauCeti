/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Data.Int.GCD
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable

/-!
# The Frey–Hellegouarch curve

For elements `A` and `B` of a commutative ring, the **Frey–Hellegouarch curve** is

  `y² = x (x - A) (x + B)`,

that is `a₂ = B - A`, `a₄ = -A B` and `a₁ = a₃ = a₆ = 0`. Its discriminant and `c₄` are

  `Δ = 16 A² B² (A + B)²`,  `c₄ = 16 (A² + A B + B²)`,

so over a field of characteristic not `2` it is elliptic exactly when `A`, `B` and `A + B` are
nonzero. Applied to a solution `aᵖ + bᵖ + cᵖ = 0` of Fermat's equation with `A = aᵖ` and `B = bᵖ`,
its three roots `0`, `A` and `-B` differ by `aᵖ`, `bᵖ` and `cᵖ`; this is the curve of Frey's
approach to Fermat's Last Theorem.

At `2` the equation above is not the one to reduce: `16` divides both `c₄` and `Δ`. When
`A ≡ -1 (mod 4)` and `16 ∣ B`, the substitution `x = 4 x'`, `y = 8 y' + 4 x'` divides `c₄` by `2⁴`
and `Δ` by `2¹²`, and gives the equation `freyCurveModel α β`, where `A = 4 α - 1` and `B = 16 β`:

  `y² + x y = x³ + (4 β - α) x² - (4 α - 1) β x`,

whose `c₄` is `A² + A B + B²` and whose discriminant is `(A β (A + B))² = A² B² (A + B)² / 2⁸`.
If moreover `A` and `B` are coprime, these two are coprime, so at every prime one of them is a
unit: the model is globally minimal and every reduction is good or multiplicative. Over a Dedekind
domain `O` with fraction field `F`, when the Frey curve is elliptic over `F`, it is therefore
semistable, with minimal discriminant ideal `(A² B² (A + B)² / 2⁸)`.

For Fermat's equation, the hypotheses on `A` and `B` can always be arranged. Exactly one of `a`,
`b`, `c` is even, and permuting the triple puts it in the `b` position; the other two have `p`-th
powers summing to `0` modulo `4`, so one of them has `p`-th power `≡ -1 (mod 4)`, and swapping
the odd entries if necessary puts it in the `a` position. Then `A = aᵖ ≡ -1 (mod 4)` and, for
`p ≥ 4`, `16 ∣ B = bᵖ`.

## Main definitions

* `TauCeti.freyCurve A B`: the Weierstrass curve `y² = x (x - A) (x + B)` over a commutative ring.
* `TauCeti.freyCurveModel α β`: the equation `y² + x y = x³ + (4 β - α) x² - (4 α - 1) β x`, the
  integral model at `2` of `freyCurve (4 α - 1) (16 β)`.

## Main results

* `TauCeti.freyCurve_Δ` and `TauCeti.freyCurve_c₄`: `Δ = 16 A² B² (A + B)²` and
  `c₄ = 16 (A² + A B + B²)`.
* `TauCeti.isElliptic_freyCurve_iff` and `TauCeti.isElliptic_freyCurve_iff_ne_zero`: the curve is
  elliptic exactly when `2`, `A`, `B` and `A + B` are units, respectively, over a field of
  characteristic not `2`, nonzero.
* `TauCeti.freyCurve_j`: its `j`-invariant is `256 (A² + A B + B²)³ / (A² B² (A + B)²)`.
* `TauCeti.smul_freyCurve_eq_freyCurveModel`: the change of variables `x = 4 x'`,
  `y = 8 y' + 4 x'` carries `freyCurve (4 α - 1) (16 β)` to `freyCurveModel α β`.
* `TauCeti.isGlobalMinimal_baseChange_freyCurveModel`: for coprime `A` and `B`, this model is
  globally minimal over a Dedekind domain, when it is elliptic over the fraction field.
* `TauCeti.isSemistable_freyCurve` and `TauCeti.minimalDiscriminantIdeal_freyCurve`: if `A` and
  `B` are coprime, `A ≡ -1 (mod 4)`, `16 ∣ B` and the Frey curve is elliptic over the fraction
  field, it is semistable with minimal discriminant ideal `(A² B² (A + B)² / 2⁸)`.
* `TauCeti.pow_modEq_neg_one_or_pow_modEq_neg_one`: if `xᵖ + eᵖ + yᵖ = 0` with `e` even, `x`
  coprime to `e` and `p ≥ 2`, then `xᵖ` or `yᵖ` is `-1` modulo `4`.
* `TauCeti.exists_perm_two_dvd_and_pow_modEq_neg_one`: a solution of `aᵖ + bᵖ + cᵖ = 0` with
  `a` and `b` coprime and `p ≥ 2` can be permuted so that `b` is even and `aᵖ ≡ -1 (mod 4)`.
* `TauCeti.isCoprime_of_gcd_eq_one_of_add_pow_eq_pow`: if `aⁿ + bⁿ = cⁿ` and `a`, `b`, `c` have
  no common factor, then `a` and `b` are coprime.
* `TauCeti.exists_isCoprime_and_mul_mul_add_eq_pow`: a solution of `aⁿ + bⁿ = cⁿ` with `a` and
  `b` coprime and `n ≥ 5`, of either parity, gives coprime `A ≡ -1 (mod 4)` and `B` with
  `32 ∣ B` and `A B (A + B) = (a b c)ⁿ`.
* `TauCeti.isSemistable_freyCurve_pow` and `TauCeti.minimalDiscriminantIdeal_freyCurve_pow`: for
  such a normalised solution with `p ≥ 4`, if the Frey curve of `(aᵖ, bᵖ)` is elliptic over `ℚ`,
  it is semistable over `ℤ` with minimal discriminant `(a b c)^(2 p) / 2⁸`.

## References

* G. Frey, *Links between stable elliptic curves and certain Diophantine equations*, Ann. Univ.
  Sarav. Ser. Math. 1 (1986), 1–40.
* Y. Hellegouarch, *Points d'ordre 2pʰ sur les courbes elliptiques*, Acta Arith. 26 (1975),
  253–263.
* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, in *Current Developments in
  Mathematics 1995*, International Press (1995), 1–154.
-/

public section

namespace TauCeti

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- **The Frey–Hellegouarch curve** `y² = x (x - A) (x + B)`, that is `a₂ = B - A` and
`a₄ = -A B`, the other coefficients being `0`. Its roots `0`, `A` and `-B` differ by `A`, `B` and
`A + B`. -/
def freyCurve (A B : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := B - A
  a₃ := 0
  a₄ := -(A * B)
  a₆ := 0

variable (A B : R)

@[simp] theorem freyCurve_a₁ : (freyCurve A B).a₁ = 0 := (rfl)
@[simp] theorem freyCurve_a₂ : (freyCurve A B).a₂ = B - A := (rfl)
@[simp] theorem freyCurve_a₃ : (freyCurve A B).a₃ = 0 := (rfl)
@[simp] theorem freyCurve_a₄ : (freyCurve A B).a₄ = -(A * B) := (rfl)
@[simp] theorem freyCurve_a₆ : (freyCurve A B).a₆ = 0 := (rfl)

@[simp]
theorem freyCurve_b₂ : (freyCurve A B).b₂ = 4 * (B - A) := by
  simp [b₂]

@[simp]
theorem freyCurve_b₄ : (freyCurve A B).b₄ = -2 * A * B := by
  simp [b₄]
  ring

@[simp]
theorem freyCurve_b₆ : (freyCurve A B).b₆ = 0 := by
  simp [b₆]

@[simp]
theorem freyCurve_b₈ : (freyCurve A B).b₈ = -(A ^ 2 * B ^ 2) := by
  simp [b₈]
  ring

/-- The `c₄` of the Frey curve is `16 (A² + A B + B²)`. -/
@[simp]
theorem freyCurve_c₄ : (freyCurve A B).c₄ = 16 * (A ^ 2 + A * B + B ^ 2) := by
  simp [c₄]
  ring

/-- The `c₆` of the Frey curve is `-32 (B - A) (2 A + B) (A + 2 B)`. -/
@[simp]
theorem freyCurve_c₆ : (freyCurve A B).c₆ = -32 * (B - A) * (2 * A + B) * (A + 2 * B) := by
  simp [c₆]
  ring

/-- The discriminant of the Frey curve is `16 A² B² (A + B)²`. -/
@[simp]
theorem freyCurve_Δ : (freyCurve A B).Δ = 16 * A ^ 2 * B ^ 2 * (A + B) ^ 2 := by
  simp [Δ]
  ring

/-- The image of a Frey curve under a ring homomorphism is the Frey curve of the images. -/
@[simp]
theorem map_freyCurve {S : Type*} [CommRing S] (f : R →+* S) :
    (freyCurve A B).map f = freyCurve (f A) (f B) := by
  ext <;> simp

/-- **The Frey curve is elliptic exactly when `2`, `A`, `B` and `A + B` are units.** -/
theorem isElliptic_freyCurve_iff :
    (freyCurve A B).IsElliptic ↔ IsUnit (2 : R) ∧ IsUnit A ∧ IsUnit B ∧ IsUnit (A + B) := by
  rw [isElliptic_iff, freyCurve_Δ, show (16 : R) = 2 ^ 4 by norm_num]
  simp only [IsUnit.mul_iff, isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0),
    isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0), and_assoc]

/-- The Frey curve's equation at `2`: `y² + x y = x³ + (4 β - α) x² - (4 α - 1) β x`. When
`A = 4 α - 1` and `B = 16 β`, it is obtained from `freyCurve A B` by `x = 4 x'`,
`y = 8 y' + 4 x'` (`smul_freyCurve_eq_freyCurveModel`), its `c₄` is `A² + A B + B²` and its
discriminant is `(A β (A + B))² = A² B² (A + B)² / 2⁸`. -/
def freyCurveModel (α β : R) : WeierstrassCurve R where
  a₁ := 1
  a₂ := 4 * β - α
  a₃ := 0
  a₄ := -((4 * α - 1) * β)
  a₆ := 0

variable (α β : R)

@[simp] theorem freyCurveModel_a₁ : (freyCurveModel α β).a₁ = 1 := (rfl)
@[simp] theorem freyCurveModel_a₂ : (freyCurveModel α β).a₂ = 4 * β - α := (rfl)
@[simp] theorem freyCurveModel_a₃ : (freyCurveModel α β).a₃ = 0 := (rfl)
@[simp] theorem freyCurveModel_a₄ : (freyCurveModel α β).a₄ = -((4 * α - 1) * β) := (rfl)
@[simp] theorem freyCurveModel_a₆ : (freyCurveModel α β).a₆ = 0 := (rfl)

/-- The `c₄` of `freyCurveModel α β` is `A² + A B + B²`, where `A = 4 α - 1` and `B = 16 β`;
this is the `c₄` of `freyCurve A B` divided by `2⁴`. -/
@[simp]
theorem freyCurveModel_c₄ : (freyCurveModel α β).c₄ =
    (4 * α - 1) ^ 2 + (4 * α - 1) * (16 * β) + (16 * β) ^ 2 := by
  simp [c₄, b₂, b₄]
  ring

/-- The discriminant of `freyCurveModel α β` is `(A β (A + B))²`, where `A = 4 α - 1` and
`B = 16 β`; this is the discriminant `16 A² B² (A + B)²` of `freyCurve A B` divided by `2¹²`.
-/
@[simp]
theorem freyCurveModel_Δ : (freyCurveModel α β).Δ =
    ((4 * α - 1) * β * (4 * α - 1 + 16 * β)) ^ 2 := by
  simp [Δ, b₂, b₄, b₆, b₈]
  ring

/-- The image of the model under a ring homomorphism is the model of the images. -/
@[simp]
theorem map_freyCurveModel {S : Type*} [CommRing S] (f : R →+* S) :
    (freyCurveModel α β).map f = freyCurveModel (f α) (f β) := by
  ext <;> simp [map_ofNat]

variable {α β}

/-- **For coprime `A = 4 α - 1` and `B = 16 β`, the discriminant and `c₄` of `freyCurveModel α β`
are coprime.** A prime dividing `c₄ = A² + A B + B²` and `Δ = (A β (A + B))²` divides `A`, `β` or
`A + B`, and with `c₄` it then divides both `A` and `B`. -/
theorem isCoprime_freyCurveModel_Δ_c₄ (h : IsCoprime (4 * α - 1) (16 * β)) :
    IsCoprime (freyCurveModel α β).Δ (freyCurveModel α β).c₄ := by
  set A := 4 * α - 1
  rw [freyCurveModel_Δ, freyCurveModel_c₄]
  refine IsCoprime.symm (IsCoprime.pow_right (IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_))
  · -- `c₄ ≡ B² (mod A)`
    rw [show A ^ 2 + A * (16 * β) + (16 * β) ^ 2 = (16 * β) ^ 2 + A * (A + 16 * β) by ring,
      IsCoprime.add_mul_left_left_iff]
    exact h.symm.pow_left
  · -- `c₄ ≡ A² (mod β)`
    rw [show A ^ 2 + A * (16 * β) + (16 * β) ^ 2 = A ^ 2 + β * (16 * A + 256 * β) by ring,
      IsCoprime.add_mul_left_left_iff]
    exact h.of_mul_right_right.pow_left
  · -- `c₄ ≡ -A B (mod A + B)`
    rw [show A ^ 2 + A * (16 * β) + (16 * β) ^ 2 =
        -(A * (16 * β)) + (A + 16 * β) * (A + 16 * β) by ring,
      IsCoprime.add_mul_left_left_iff, IsCoprime.neg_left_iff]
    refine IsCoprime.mul_left ?_ ?_
    · simpa [add_comm] using h.add_mul_left_right 1
    · simpa [add_comm] using h.symm.add_mul_left_right 1

end CommRing

section Field

variable {F : Type*} [Field F]

/-- **Over a field of characteristic not `2`, the Frey curve is elliptic exactly when `A`, `B`
and `A + B` are nonzero.** -/
theorem isElliptic_freyCurve_iff_ne_zero (h2 : (2 : F) ≠ 0) (A B : F) :
    (freyCurve A B).IsElliptic ↔ A ≠ 0 ∧ B ≠ 0 ∧ A + B ≠ 0 := by
  simp [isElliptic_freyCurve_iff, h2]

/-- The `j`-invariant of the Frey curve is `256 (A² + A B + B²)³ / (A² B² (A + B)²)`. -/
@[simp]
theorem freyCurve_j (A B : F) [(freyCurve A B).IsElliptic] :
    (freyCurve A B).j = 256 * (A ^ 2 + A * B + B ^ 2) ^ 3 / (A ^ 2 * B ^ 2 * (A + B) ^ 2) := by
  obtain ⟨h2, hA, hB, hAB⟩ := (isElliptic_freyCurve_iff A B).mp ‹_›
  have := h2.ne_zero
  have := hA.ne_zero
  have := hB.ne_zero
  have := hAB.ne_zero
  rw [j_eq, freyCurve_Δ, freyCurve_c₄]
  field_simp
  ring

/-- **The change of variables `x = 4 x'`, `y = 8 y' + 4 x'` carries `freyCurve (4 α - 1) (16 β)`
to `freyCurveModel α β`.** -/
theorem smul_freyCurve_eq_freyCurveModel (h2 : (2 : F) ≠ 0) (α β : F) :
    (⟨Units.mk0 2 h2, 0, 1, 0⟩ : VariableChange F) • freyCurve (4 * α - 1) (16 * β) =
      freyCurveModel α β := by
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆] <;> field_simp <;> ring

end Field

section Dedekind

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {F : Type*} [Field F] [Algebra O F]
  [IsFractionRing O F]

omit [IsDedekindDomain O] [IsFractionRing O F] in
/-- An elliptic Frey curve over the fraction field lives in characteristic not `2`. -/
private theorem two_ne_zero_of_isElliptic_baseChange {A B : O}
    [hE : ((freyCurve A B).baseChange F).IsElliptic] : (2 : F) ≠ 0 := by
  rw [baseChange, map_freyCurve, isElliptic_freyCurve_iff] at hE
  exact hE.1.ne_zero

omit [IsDedekindDomain O] [IsFractionRing O F] in
/-- The Frey curve over the fraction field is a change of variables away from the base change of
its model at `2`. -/
private theorem baseChange_freyCurveModel_eq_smul {α β : O}
    [((freyCurve (4 * α - 1) (16 * β)).baseChange F).IsElliptic] :
    ∃ C : VariableChange F,
      C • (freyCurve (4 * α - 1) (16 * β)).baseChange F = (freyCurveModel α β).baseChange F := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isElliptic_baseChange (A := 4 * α - 1) (B := 16 * β)
  refine ⟨⟨Units.mk0 2 h2, 0, 1, 0⟩, ?_⟩
  simpa [baseChange, map_ofNat] using smul_freyCurve_eq_freyCurveModel h2 _ _

/-- **For coprime `4 α - 1` and `16 β`, the model `freyCurveModel α β` is globally minimal**,
when it is elliptic over the fraction field `F`. -/
theorem isGlobalMinimal_baseChange_freyCurveModel {α β : O}
    [((freyCurveModel α β).baseChange F).IsElliptic] (h : IsCoprime (4 * α - 1) (16 * β)) :
    IsGlobalMinimal O ((freyCurveModel α β).baseChange F) :=
  isGlobalMinimal_baseChange_of_isCoprime _ (isCoprime_freyCurveModel_Δ_c₄ h)

/-- **The Frey curve is semistable** over a Dedekind domain `O` when it is elliptic over the
fraction field `F`, `A` and `B` are coprime, `A ≡ -1 (mod 4)` and `16 ∣ B`: its model at `2` has
coprime discriminant and `c₄`, so the reduction at every height-one prime is good or
multiplicative. -/
theorem isSemistable_freyCurve {A B : O} (hA : 4 ∣ A + 1) (hB : 16 ∣ B) (hAB : IsCoprime A B)
    [((freyCurve A B).baseChange F).IsElliptic] :
    IsSemistable O ((freyCurve A B).baseChange F) := by
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β, rfl⟩ := hB
  obtain rfl : A = 4 * α - 1 := eq_sub_of_add_eq hα
  obtain ⟨C, hC⟩ := baseChange_freyCurveModel_eq_smul (F := F) (α := α) (β := β)
  have : ((freyCurveModel α β).baseChange F).IsElliptic := hC ▸ inferInstance
  have hs := isSemistable_baseChange_of_isCoprime (F := F) _ (isCoprime_freyCurveModel_Δ_c₄ hAB)
  rw [← isSemistable_smul C]
  -- `hC` identifies the two curves; their ellipticity instances agree by proof irrelevance
  convert hs using 2

/-- **The minimal discriminant ideal of the Frey curve is `(A² B² (A + B)² / 2⁸)`** when it is
elliptic over the fraction field `F`, `A` and `B` are coprime, `A ≡ -1 (mod 4)` and `16 ∣ B`.
The quotient by `2⁸` is the element `d` with `2⁸ d = A² B² (A + B)²`; it is the discriminant of
the globally minimal model at `2`. -/
theorem minimalDiscriminantIdeal_freyCurve {A B d : O} (hA : 4 ∣ A + 1) (hB : 16 ∣ B)
    (hAB : IsCoprime A B) (hd : 2 ^ 8 * d = A ^ 2 * B ^ 2 * (A + B) ^ 2)
    [((freyCurve A B).baseChange F).IsElliptic] :
    minimalDiscriminantIdeal O ((freyCurve A B).baseChange F) = Ideal.span {d} := by
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β, rfl⟩ := hB
  obtain rfl : A = 4 * α - 1 := eq_sub_of_add_eq hα
  obtain ⟨C, hC⟩ := baseChange_freyCurveModel_eq_smul (F := F) (α := α) (β := β)
  have : ((freyCurveModel α β).baseChange F).IsElliptic := hC ▸ inferInstance
  have h2 : (2 : O) ≠ 0 := fun h ↦
    two_ne_zero_of_isElliptic_baseChange (F := F) (A := 4 * α - 1) (B := 16 * β)
      (by rw [← map_ofNat (algebraMap O F) 2, h, map_zero])
  -- `d` is the discriminant of the model, after cancelling `2⁸`
  have hdΔ : d = (freyCurveModel α β).Δ := by
    refine mul_left_cancel₀ (pow_ne_zero 8 h2) ?_
    rw [hd, freyCurveModel_Δ]
    ring
  rw [← minimalDiscriminantIdeal_smul O C]
  -- as above, `hC` identifies the curves and the ellipticity instances agree
  convert minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal
    (isGlobalMinimal_baseChange_freyCurveModel (F := F) hAB) (d := d)
    (by rw [hdΔ, baseChange, map_Δ]) using 2

end Dedekind

section Fermat

/-- If `x` is coprime to an even `e`, and `xᵖ + eᵖ + yᵖ = 0` with `p ≥ 2`, then `xᵖ` or `yᵖ` is
`-1` modulo `4`: both are odd and `xᵖ + yᵖ ≡ 0 (mod 4)`. -/
theorem pow_modEq_neg_one_or_pow_modEq_neg_one {p : ℕ} (hp : 2 ≤ p) {x e y : ℤ}
    (he : 2 ∣ e) (hx : IsCoprime x e) (h : x ^ p + e ^ p + y ^ p = 0) :
    x ^ p ≡ -1 [ZMOD 4] ∨ y ^ p ≡ -1 [ZMOD 4] := by
  have hxodd : Odd (x ^ p) := by
    refine Odd.pow (Int.not_even_iff_odd.mp fun hxe ↦ ?_)
    have := hx.isUnit_of_dvd' (even_iff_two_dvd.mp hxe) he
    exact absurd (Int.isUnit_iff.mp this) (by decide)
  have h4 : (4 : ℤ) ∣ e ^ p := by
    simpa using (pow_dvd_pow_of_dvd he 2).trans (pow_dvd_pow e hp)
  obtain ⟨k, hk⟩ := hxodd
  obtain ⟨m, hm⟩ := h4
  simp only [Int.ModEq]
  omega

/-- **The normalisation of a Fermat triple.** If `aᵖ + bᵖ + cᵖ = 0` with `a` and `b` coprime and
`p ≥ 2`, some permutation `a'`, `b'`, `c'` of `a`, `b`, `c` has `b'` even and
`a'ᵖ ≡ -1 (mod 4)`. The three entries are then pairwise coprime, so exactly one of them is even,
and it is put in the middle; the other two have `p`-th powers summing to `0` modulo `4`, and one
of them is chosen first. No entry needs to be negated. -/
theorem exists_perm_two_dvd_and_pow_modEq_neg_one {p : ℕ} (hp : 2 ≤ p) {a b c : ℤ}
    (hab : IsCoprime a b) (h : a ^ p + b ^ p + c ^ p = 0) :
    ∃ a' b' c' : ℤ, [a', b', c'].Perm [a, b, c] ∧ 2 ∣ b' ∧ a' ^ p ≡ -1 [ZMOD 4] := by
  -- `a` is coprime to `c`, since `cᵖ ≡ -bᵖ (mod a)`
  have hac : IsCoprime a c := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    rw [← IsCoprime.pow_right_iff k.succ_pos,
      show c ^ (k + 1) = -b ^ (k + 1) + a * -a ^ k by linear_combination h,
      IsCoprime.add_mul_left_right_iff, IsCoprime.neg_right_iff]
    exact hab.pow_right
  -- not all three entries are odd, since a sum of three odd numbers is odd
  have hodd : ¬ (Odd a ∧ Odd b ∧ Odd c) := by
    rintro ⟨ha, hb, hc⟩
    obtain ⟨i, hi⟩ := ha.pow (n := p)
    obtain ⟨j, hj⟩ := hb.pow (n := p)
    obtain ⟨k, hk⟩ := hc.pow (n := p)
    omega
  simp only [← Int.not_even_iff_odd, even_iff_two_dvd] at hodd
  by_cases hb : 2 ∣ b
  · rcases pow_modEq_neg_one_or_pow_modEq_neg_one hp hb hab h with h' | h'
    · exact ⟨a, b, c, .refl _, hb, h'⟩
    · exact ⟨c, b, a, List.reverse_perm [a, b, c], hb, h'⟩
  by_cases ha : 2 ∣ a
  · rcases pow_modEq_neg_one_or_pow_modEq_neg_one (y := c) hp ha hab.symm
      (by linear_combination h) with h' | h'
    · exact ⟨b, a, c, .swap _ _ _, ha, h'⟩
    · exact ⟨c, a, b, List.rotate_perm [a, b, c] 2, ha, h'⟩
  have hc : 2 ∣ c := by tauto
  rcases pow_modEq_neg_one_or_pow_modEq_neg_one (y := b) hp hc hac
    (by linear_combination h) with h' | h'
  · exact ⟨a, c, b, .cons _ (.swap _ _ _), hc, h'⟩
  · exact ⟨b, c, a, List.rotate_perm [a, b, c] 1, hc, h'⟩

/-- If `aⁿ + bⁿ = cⁿ` and `a`, `b`, `c` have no common factor, then `a` and `b` are coprime: a
prime dividing both divides `cⁿ`, hence `c`. This is the analogue of Mathlib's
`isCoprime_of_gcd_eq_one_of_FLT` for the form `aⁿ + bⁿ = cⁿ`, which covers even exponents. -/
theorem isCoprime_of_gcd_eq_one_of_add_pow_eq_pow {n : ℕ} {a b c : ℤ}
    (hgcd : Finset.gcd {a, b, c} id = 1) (h : a ^ n + b ^ n = c ^ n) : IsCoprime a b := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num at h
  refine isCoprime_of_prime_dvd (fun ⟨ha, hb⟩ ↦ ?_) fun p hp hpa hpb ↦ ?_
  · subst ha hb
    obtain rfl : c = 0 := by simpa [zero_pow hn, eq_comm, hn] using h
    simp at hgcd
  · have hpc : p ∣ c :=
      hp.dvd_of_dvd_pow (n := n) (h ▸ dvd_add (dvd_pow hpa hn) (dvd_pow hpb hn))
    refine hp.not_dvd_one (hgcd ▸ Finset.dvd_gcd fun x hx ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- A coprime pair `X`, `Y` with `32 ∣ Y` gives coprime `A` and `B` with `A ≡ -1 (mod 4)` and
`32 ∣ B`: either `(X, Y)` or `(-(X + Y), Y)`, depending on whether `X ≡ -1` or `X ≡ 1 (mod 4)`,
and both have `A B (A + B) = X Y (X + Y)`. -/
private theorem exists_pair_of_isCoprime {X Y : ℤ} (hXY : IsCoprime X Y) (hY : 32 ∣ Y) :
    ∃ A B : ℤ, IsCoprime A B ∧ 4 ∣ A + 1 ∧ 32 ∣ B ∧ A * B * (A + B) = X * Y * (X + Y) := by
  -- `X` is odd, being coprime to the even `Y`
  have hX : ¬ 2 ∣ X := fun h2 ↦ Int.prime_two.not_dvd_one
    (hXY.isUnit_of_dvd' h2 (dvd_trans ⟨16, by norm_num⟩ hY)).dvd
  by_cases h4 : 4 ∣ X + 1
  · exact ⟨X, Y, hXY, h4, hY, rfl⟩
  refine ⟨-(X + Y), Y, by simpa using (hXY.add_mul_left_left 1).neg_left, by omega, hY, by ring⟩

/-- **The Frey curve of a Fermat triple.** If `aⁿ + bⁿ = cⁿ` with `a` and `b` coprime and `n ≥ 5`,
there are coprime integers `A` and `B` with `A ≡ -1 (mod 4)`, `32 ∣ B` and
`A B (A + B) = (a b c)ⁿ`. Here `B` is the even one of `aⁿ`, `bⁿ`, `cⁿ`, up to sign, and `A` is
one of the other two, up to sign. -/
theorem exists_isCoprime_and_mul_mul_add_eq_pow {n : ℕ} (hn : 5 ≤ n) {a b c : ℤ}
    (hab : IsCoprime a b) (h : a ^ n + b ^ n = c ^ n) :
    ∃ A B : ℤ, IsCoprime A B ∧ 4 ∣ A + 1 ∧ 32 ∣ B ∧ A * B * (A + B) = (a * b * c) ^ n := by
  have h32 {x : ℤ} (hx : 2 ∣ x) : (32 : ℤ) ∣ x ^ n := by
    simpa using (pow_dvd_pow_of_dvd hx 5).trans (pow_dvd_pow x hn)
  have hn₀ : n ≠ 0 := by omega
  by_cases hb : 2 ∣ b
  · obtain ⟨A, B, h₁, h₂, h₃, h₄⟩ := exists_pair_of_isCoprime hab.pow (h32 hb)
    exact ⟨A, B, h₁, h₂, h₃, by rw [h₄, h]; ring⟩
  by_cases ha : 2 ∣ a
  · obtain ⟨A, B, h₁, h₂, h₃, h₄⟩ := exists_pair_of_isCoprime hab.symm.pow (h32 ha)
    exact ⟨A, B, h₁, h₂, h₃, by rw [h₄, add_comm, h]; ring⟩
  -- otherwise `a` and `b` are odd, so `cⁿ = aⁿ + bⁿ` is even, and `B = -cⁿ`
  have hc : 2 ∣ c := by
    refine Int.prime_two.dvd_of_dvd_pow (n := n) (h ▸ ?_)
    rw [← even_iff_two_dvd] at ha hb ⊢
    rw [Int.not_even_iff_odd] at ha hb
    exact (ha.pow).add_odd hb.pow
  have hac : IsCoprime (a ^ n) (-c ^ n) := by
    simpa [← h, add_comm] using (hab.pow.add_mul_left_right 1).neg_right
  obtain ⟨A, B, h₁, h₂, h₃, h₄⟩ := exists_pair_of_isCoprime hac (dvd_neg.2 (h32 hc))
  exact ⟨A, B, h₁, h₂, h₃, by rw [h₄, mul_pow, mul_pow, ← h]; ring⟩

/-- **The Frey curve of a normalised Fermat triple is semistable.** If `a` and `b` are coprime,
`b` is even, `aᵖ ≡ -1 (mod 4)`, `p ≥ 4` and `y² = x (x - aᵖ) (x + bᵖ)` is elliptic over `ℚ`, then
it is semistable over `ℤ`. -/
theorem isSemistable_freyCurve_pow {p : ℕ} (hp : 4 ≤ p) {a b : ℤ} (hab : IsCoprime a b)
    (hb : 2 ∣ b) (ha : a ^ p ≡ -1 [ZMOD 4])
    [((freyCurve (a ^ p) (b ^ p)).baseChange ℚ).IsElliptic] :
    IsSemistable ℤ ((freyCurve (a ^ p) (b ^ p)).baseChange ℚ) :=
  isSemistable_freyCurve ((Int.ModEq.dvd ha.symm).trans (by simp))
    (by simpa using (pow_dvd_pow_of_dvd hb 4).trans (pow_dvd_pow b hp)) hab.pow

/-- **The minimal discriminant of the Frey curve of a Fermat triple is `(a b c)^(2 p) / 2⁸`.** If
`aᵖ + bᵖ + cᵖ = 0` with `a` and `b` coprime, `b` even, `aᵖ ≡ -1 (mod 4)` and `p ≥ 4`, and
`y² = x (x - aᵖ) (x + bᵖ)` is elliptic over `ℚ`, its minimal discriminant ideal over `ℤ` is
generated by `(a b c)^(2 p) / 2⁸`. -/
theorem minimalDiscriminantIdeal_freyCurve_pow {p : ℕ} (hp : 4 ≤ p) {a b c : ℤ}
    (hab : IsCoprime a b) (h : a ^ p + b ^ p + c ^ p = 0) (hb : 2 ∣ b) (ha : a ^ p ≡ -1 [ZMOD 4])
    [((freyCurve (a ^ p) (b ^ p)).baseChange ℚ).IsElliptic] :
    minimalDiscriminantIdeal ℤ ((freyCurve (a ^ p) (b ^ p)).baseChange ℚ) =
      Ideal.span {(a * b * c) ^ (2 * p) / 2 ^ 8} := by
  have h16 : (16 : ℤ) ∣ b ^ p := by
    simpa using (pow_dvd_pow_of_dvd hb 4).trans (pow_dvd_pow b hp)
  refine minimalDiscriminantIdeal_freyCurve ((Int.ModEq.dvd ha.symm).trans (by simp)) h16
    hab.pow ?_
  have h256 : (2 : ℤ) ^ 8 ∣ (a * b * c) ^ (2 * p) :=
    (pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb a) c) 8).trans
      (pow_dvd_pow _ (by omega))
  rw [Int.mul_ediv_cancel' h256, show a ^ p + b ^ p = -c ^ p by linear_combination h]
  ring

end Fermat

end TauCeti
