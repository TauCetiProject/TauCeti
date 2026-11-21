/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Truncated

/-!
# δ-structures as sections of length-two Witt vectors

Let `p` be a prime. On the length-two Witt vectors `W₂(A) = TruncatedWittVector p 2 A` of any
commutative ring `A` (with no torsion hypothesis) the first coordinates of a sum and a product
are `(x + y)₁ = x₁ + y₁ + C_p(x₀, y₀)` and `(x * y)₁ = x₀ ^ p * y₁ + y₀ ^ p * x₁ + p * x₁ * y₁`,
where `C_p = DeltaRing.addCorrection p`. These are exactly the sum and product rules of a
`δ`-structure, so a `δ`-structure on `A` is the same thing as a ring homomorphism
`s : A →+* W₂(A)` with `s(x)₀ = x`, via `s(x) = (x, δ x)`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4). Under this correspondence
the Frobenius `φ x = x ^ p + p * δ x` is the first ghost component of `s(x)`. This description
of `δ`-structures by ring homomorphisms is what allows them to be extended along localizations
and to be compared with the Witt vector Frobenius.

## Main definitions and results

* `TauCeti.DeltaRing.wittSection`: the ring homomorphism `x ↦ (x, δ x)` of a `δ`-ring.
* `TauCeti.DeltaRing.ofWittSection`: the `δ`-structure of a ring homomorphism `A →+* W₂(A)`
  whose zeroth coordinate is the identity.
* `TauCeti.DeltaRing.equivWittSection`: `δ`-structures on `A` are equivalent to ring
  homomorphisms `A →+* W₂(A)` whose zeroth coordinate is the identity.
* `TauCeti.DeltaRing.wittSection_coeff_zero_pow_add_mul_coeff_one`: the Frobenius is
  `s(x)₀ ^ p + p * s(x)₁` for the Witt section `s`.
* `TauCeti.DeltaRing.ghostComponent_one_eq_frobenius`: the Frobenius is the first ghost
  component of any Witt vector lifting the Witt section.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  §2.1, Remark 2.4.
-/

public section

namespace TauCeti

namespace DeltaRing

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]

section WittSection

variable [DeltaRing p A]

variable (p A) in
/-- The ring homomorphism `x ↦ (x, δ x)` from a `δ`-ring to its length-two Witt vectors
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4). Its zeroth coordinate is the
identity (`wittSection_coeff_zero`) and its first coordinate is `δ` (`wittSection_coeff_one`). -/
noncomputable def wittSection : A →+* TruncatedWittVector p 2 A where
  toFun x := TruncatedWittVector.mk p ![x, delta p x]
  map_one' := by
    ext i
    fin_cases i <;> simp [TruncatedWittVector.coeff_mk]
  map_mul' x y := by
    ext i
    fin_cases i
    · simp [TruncatedWittVector.coeff_mk]
    · simp [TruncatedWittVector.coeff_mk, TruncatedWittVector.mul_coeff_one, delta_mul]
  map_zero' := by
    ext i
    fin_cases i <;> simp [TruncatedWittVector.coeff_mk]
  map_add' x y := by
    ext i
    fin_cases i
    · simp [TruncatedWittVector.coeff_mk]
    · simp [TruncatedWittVector.coeff_mk, TruncatedWittVector.add_coeff_one, delta_add]

/-- The Witt section sends `x` to the length-two Witt vector with coordinates `(x, δ x)`. -/
theorem wittSection_apply (x : A) :
    wittSection p A x = TruncatedWittVector.mk p ![x, delta p x] :=
  (rfl)

/-- The zeroth coordinate of the Witt section is the identity. -/
@[simp]
theorem wittSection_coeff_zero (x : A) : (wittSection p A x).coeff 0 = x := by
  simp [wittSection_apply, TruncatedWittVector.coeff_mk]

/-- The first coordinate of the Witt section is `δ`. -/
@[simp]
theorem wittSection_coeff_one (x : A) : (wittSection p A x).coeff 1 = delta p x := by
  simp [wittSection_apply, TruncatedWittVector.coeff_mk]

/-- The Frobenius is `s(x)₀ ^ p + p * s(x)₁` for the Witt section `s(x) = (x, δ x)`. -/
theorem wittSection_coeff_zero_pow_add_mul_coeff_one (x : A) :
    (wittSection p A x).coeff 0 ^ p + p * (wittSection p A x).coeff 1 = frobenius p A x := by
  rw [wittSection_coeff_zero, wittSection_coeff_one, frobenius_apply]

/-- The Frobenius `φ x = x ^ p + p * δ x` is the first ghost component of any Witt vector lifting
the Witt section `(x, δ x)`. -/
theorem ghostComponent_one_eq_frobenius {x : A} {w : WittVector p A}
    (hw : WittVector.truncate 2 w = wittSection p A x) :
    WittVector.ghostComponent 1 w = frobenius p A x := by
  rw [← wittSection_coeff_zero_pow_add_mul_coeff_one, ← hw, WittVector.coeff_truncate,
    WittVector.coeff_truncate, WittVector.ghostComponent_one]
  rfl

end WittSection

/-- The `δ`-structure `δ x = s(x)₁` of a ring homomorphism `s : A →+* W₂(A)` whose zeroth
coordinate is the identity (Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4). -/
@[instance_reducible]
def ofWittSection (s : A →+* TruncatedWittVector p 2 A) (hs : ∀ x, (s x).coeff 0 = x) :
    DeltaRing p A where
  delta x := (s x).coeff 1
  delta_zero := by simp
  delta_one := by simp
  delta_add x y := by simp [TruncatedWittVector.add_coeff_one, hs]
  delta_mul x y := by simp [TruncatedWittVector.mul_coeff_one, hs]

/-- The `δ`-operation of `ofWittSection s hs` is the first coordinate of `s`. -/
@[simp]
theorem delta_ofWittSection (s : A →+* TruncatedWittVector p 2 A)
    (hs : ∀ x, (s x).coeff 0 = x) (x : A) :
    @delta p A _ (ofWittSection s hs) x = (s x).coeff 1 :=
  (rfl)

/-- The Witt section of `ofWittSection s hs` is `s`. -/
@[simp]
theorem wittSection_ofWittSection (s : A →+* TruncatedWittVector p 2 A)
    (hs : ∀ x, (s x).coeff 0 = x) : @wittSection p _ A _ (ofWittSection s hs) = s := by
  let := ofWittSection s hs
  ext x i
  fin_cases i
  · exact (wittSection_coeff_zero x).trans (hs x).symm
  · exact wittSection_coeff_one x

/-- The `δ`-structure of the Witt section of a `δ`-ring is the given one. -/
@[simp]
theorem ofWittSection_wittSection [δ : DeltaRing p A] :
    ofWittSection (wittSection p A) wittSection_coeff_zero = δ := by
  ext x
  exact wittSection_coeff_one x

variable (p A) in
/-- `δ`-structures on `A` are equivalent to ring homomorphisms `s : A →+* W₂(A)` to the
length-two Witt vectors whose zeroth coordinate is the identity, via `s x = (x, δ x)`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4). -/
noncomputable def equivWittSection :
    DeltaRing p A ≃ {s : A →+* TruncatedWittVector p 2 A // ∀ x, (s x).coeff 0 = x} where
  toFun δ := letI := δ; ⟨wittSection p A, wittSection_coeff_zero⟩
  invFun s := ofWittSection s.1 s.2
  left_inv δ := ofWittSection_wittSection (δ := δ)
  right_inv s := Subtype.ext (wittSection_ofWittSection s.1 s.2)

@[simp]
theorem equivWittSection_apply_coe (δ : DeltaRing p A) :
    (equivWittSection p A δ : A →+* TruncatedWittVector p 2 A) = @wittSection p _ A _ δ :=
  (rfl)

@[simp]
theorem equivWittSection_symm_apply
    (s : {s : A →+* TruncatedWittVector p 2 A // ∀ x, (s x).coeff 0 = x}) :
    (equivWittSection p A).symm s = ofWittSection s.1 s.2 :=
  (rfl)

end DeltaRing

end TauCeti
