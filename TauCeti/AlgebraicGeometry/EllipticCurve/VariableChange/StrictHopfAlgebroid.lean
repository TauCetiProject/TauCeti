/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.SemidirectProduct
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The strict Weierstrass Hopf algebroid in Bauer's convention

Let `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `Γ = A[u, u⁻¹, r, s, t]` be the rings of objects and arrows of
the Weierstrass Hopf algebroid
(`TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/HopfAlgebroid.lean`). Bauer computes with
the **strict** Hopf algebroid `(A, A[r, s, t])` instead, graded by putting `aᵢ` in degree `2i` and
`r, s, t` in degrees `4, 2, 6`; the scaling coordinate `u` is replaced by the grading. This file
constructs that Hopf algebroid in the native conventions of Mathlib and Tau Ceti and gives the
dictionary between the two presentations.

The ring `A[r, s, t]` (`TauCeti.WeierstrassHopfAlgebroid.StrictArrowRing`) corepresents pairs of a
Weierstrass curve `W` and a change of variables `(1, r, s, t)`, an element of the Heisenberg
subgroup of changes of variables (`TauCeti.WeierstrassHopfAlgebroid.strictArrowEquiv`). An arrow
goes from its source `W`, classified by the left unit `η_L`, to its target `(1, r, s, t) • W`,
classified by the right unit `η_R`, which is given by Mathlib's
`WeierstrassCurve.variableChange_def` at `u = 1`:

* `η_R(a₁) = a₁ + 2s`, `η_R(a₂) = a₂ - s a₁ + 3r - s²`, `η_R(a₃) = a₃ + r a₁ + 2t`,
* `η_R(a₄) = a₄ - s a₃ + 2r a₂ - (t + rs) a₁ + 3r² - 2st`,
* `η_R(a₆) = a₆ + r a₄ + r² a₂ + r³ - t a₃ - t² - rt a₁`.

In the ring `A[r₁, s₁, t₁, r₂, s₂, t₂]` of composable pairs `W → C₁ • W → C₂ • (C₁ • W)` the first
arrow is the left factor, and the coproduct classifies the composite `C₂ * C₁`:
`Δr = r₁ + r₂`, `Δs = s₁ + s₂` and `Δt = t₁ + t₂ + s₁r₂`. The cross term `s₁r₂` pairs the first
arrow's `s` with the second arrow's `r`; in tensor notation `Δt = t ⊗ 1 + 1 ⊗ t + s ⊗ r`, and it
pins the order of composition. The counit sends `r, s, t` to `0`, and the conjugation classifying
inverse arrows sends `(r, s, t)` to `(-r, -s, -t + rs)`. We prove the counit laws, coassociativity
and the laws of the conjugation.

With the weights `1, 2, 3, 4, 6` of the coefficients and `2, 1, 3` of `r, s, t`
(`TauCeti.WeierstrassHopfAlgebroid.strictWeight`), half of Bauer's degrees, all structure maps are
graded.

**The dictionary.** Setting `u = 1` is a surjection `Γ →+* A[r, s, t]`
(`TauCeti.WeierstrassHopfAlgebroid.toStrict`) intertwining the left and right units, the counits,
the coproducts and the conjugations, with section the inclusion `A[r, s, t] →+* Γ`
(`TauCeti.WeierstrassHopfAlgebroid.ofStrict`). Conversely the scaling coordinate is recovered from
the grading: every change of variables factors as `(u, r, s, t) = (u, 0, 0, 0) (1, r, s, t)`, and
the scaling multiplies a coefficient polynomial of weight `k` by `u⁻ᵏ`, the character of the Hodge
line `ω^k` under the transformation law `φ_C^* ω_W = u⁻¹ ω_{C • W}` of the invariant differential.
So `η_R(f) = u⁻ᵏ η_R'(f)` for `f` of weight `k`, where `η_R'` is the strict right unit followed by
the inclusion `A[r, s, t] →+* Γ`
(`TauCeti.WeierstrassHopfAlgebroid.rightUnit_eq_of_isWeightedHomogeneous`). Hence the integral
modular forms of weight `k`, the `f` with `η_R(f) = u⁻ᵏ η_L(f)`, are exactly Bauer's invariants of
weight `k`: the weighted homogeneous `f` of weight `k` with `η_R(f) = η_L(f)` in `A[r, s, t]`
(`WeierstrassCurve.isIntegralModularForm_iff_strictRightUnit`). In particular `c₄`, `c₆` and `Δ`
are invariants of the strict Hopf algebroid.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.StrictArrowRing`: the ring `A[r, s, t]`.
* `TauCeti.WeierstrassHopfAlgebroid.strictLeftUnit`, `strictRightUnit`, `strictCounit`,
  `strictCoproduct`, `strictConjugation`: the structure maps of the strict Hopf algebroid.
* `TauCeti.WeierstrassHopfAlgebroid.strictWeight`: the weights of the generators of `A[r, s, t]`.
* `TauCeti.WeierstrassHopfAlgebroid.toStrict`, `toStrictPair`: the maps out of `Γ` and `Γ ⊗_A Γ`
  setting the scaling coordinates to `1`; `ofStrict`: the inclusion of `A[r, s, t]` in `Γ`.

## Main results

* `strictArrowEquiv`: homomorphisms out of `A[r, s, t]` classify strict arrows.
* `strictRightUnit_X_A₁`, …, `strictRightUnit_X_A₆` and `strictCoproduct_X_inr_zero`,
  `strictCoproduct_X_inr_one`, `strictCoproduct_X_inr_two`: the structure maps in coordinates.
* `strictCounitLeft_comp_strictCoproduct`, `strictCounitRight_comp_strictCoproduct`,
  `strictCoproduct_coassoc`: the counit laws and coassociativity.
* `isWeightedHomogeneous_strictRightUnit`, `isWeightedHomogeneous_strictCoproduct`: the structure
  maps are graded.
* `toStrict_comp_rightUnit`, `strictCounit_comp_toStrict`, `toStrictPair_comp_coproduct`,
  `toStrict_comp_conjugation`: setting `u = 1` intertwines the structure maps.
* `rightUnit_eq_of_isWeightedHomogeneous`: `η_R(f) = u⁻ᵏ η_R'(f)` for `f` of weight `k`.
* `WeierstrassCurve.isIntegralModularForm_iff_strictRightUnit`: integral modular forms of weight `k`
  are the weight-`k` invariants of the strict Hopf algebroid.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3 (the Hopf algebroid `(A, A[r, s, t])`).
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Table 3.1 (the transformation formulas).
-/

public section

noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve TauCeti.WeierstrassChange
open TauCeti.WeierstrassChange.ChangeRing
open _root_.WeierstrassCurve.VariableChange (heisenbergHom scaling)

variable {R : Type*} [CommRing R]

/-! ### The strict arrow ring `A[r, s, t]` -/

/-- The ring `A[r, s, t] = ℤ[a₁, a₂, a₃, a₄, a₆, r, s, t]` of arrows of the strict Weierstrass
Hopf algebroid, with the coefficients indexed by `Sum.inl` and the coordinates `r, s, t` by
`Sum.inr 0, 1, 2`. Its homomorphisms to `R` classify a Weierstrass curve `W` over `R` together with
a change of variables `(1, r, s, t)` over `R` (`strictArrowEquiv`). -/
abbrev StrictArrowRing : Type := MvPolynomial (Coeff ⊕ Fin 3) ℤ

/-- The **strict left unit** `η_L : A →+* A[r, s, t]`, classifying the source `W` of the universal
strict arrow `W → (1, r, s, t) • W`. -/
def strictLeftUnit : MvPolynomial Coeff ℤ →+* StrictArrowRing :=
  (rename Sum.inl).toRingHom

theorem strictLeftUnit_apply (f : MvPolynomial Coeff ℤ) :
    strictLeftUnit f = rename Sum.inl f :=
  (rfl)

@[simp]
theorem strictLeftUnit_X (i : Coeff) : strictLeftUnit (X i) = X (.inl i) :=
  rename_X _ _

/-- The universal strict change of variables `(r, s, t)` over `A[r, s, t]`, as an element of the
Heisenberg group of changes of variables `(1, r, s, t)`. -/
def strictChange : HeisenbergGroup StrictArrowRing :=
  ⟨X (.inr 0), X (.inr 1), X (.inr 2)⟩

@[simp] theorem strictChange_x : strictChange.x = X (.inr 0) := (rfl)
@[simp] theorem strictChange_y : strictChange.y = X (.inr 1) := (rfl)
@[simp] theorem strictChange_z : strictChange.z = X (.inr 2) := (rfl)

variable (R) in
/-- **Homomorphisms out of `A[r, s, t]` classify strict arrows**: `k : A[r, s, t] →+* R`
corresponds to the source curve `W` and the change of variables `(1, r, s, t)` of the arrow
`W → (1, r, s, t) • W` it classifies, recorded as an element of the Heisenberg group. -/
def strictArrowEquiv :
    (StrictArrowRing →+* R) ≃ _root_.WeierstrassCurve R × HeisenbergGroup R where
  toFun k := (WeierstrassCurve.map Universal.curve (k.comp strictLeftUnit),
    HeisenbergGroup.map k strictChange)
  invFun p := (aeval (Sum.elim (fun i ↦ p.1.specialize (X i)) ![p.2.x, p.2.y, p.2.z])).toRingHom
  left_inv k := MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simp
    · fin_cases j <;> simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · ext <;> simp
    · ext <;> simp

@[simp]
theorem strictArrowEquiv_apply (k : StrictArrowRing →+* R) :
    strictArrowEquiv R k =
      (WeierstrassCurve.map Universal.curve (k.comp strictLeftUnit),
        HeisenbergGroup.map k strictChange) :=
  (rfl)

@[simp]
theorem strictArrowEquiv_symm_apply (p : _root_.WeierstrassCurve R × HeisenbergGroup R) :
    (strictArrowEquiv R).symm p =
      (aeval (Sum.elim (fun i ↦ p.1.specialize (X i)) ![p.2.x, p.2.y, p.2.z])).toRingHom :=
  (rfl)

/-- A ring homomorphism out of `A[r, s, t]` is determined by the source curve and the strict change
of variables it classifies. -/
theorem strictArrowRing_ringHom_ext {k k' : StrictArrowRing →+* R}
    (h₁ : k.comp strictLeftUnit = k'.comp strictLeftUnit)
    (h₂ : HeisenbergGroup.map k strictChange = HeisenbergGroup.map k' strictChange) : k = k' :=
  (strictArrowEquiv R).injective (Prod.ext (by simp only [strictArrowEquiv_apply, h₁]) h₂)

/-! ### The strict right unit -/

/-- The **strict right unit** `η_R : A →+* A[r, s, t]`, classifying the target `(1, r, s, t) • W`
of the universal strict arrow. Its values on the coefficients are the formulas of Bauer, §3
(`strictRightUnit_X_A₁`, …, `strictRightUnit_X_A₆`). -/
def strictRightUnit : MvPolynomial Coeff ℤ →+* StrictArrowRing :=
  (heisenbergHom _ strictChange • WeierstrassCurve.map Universal.curve strictLeftUnit).specialize

/-- The strict right unit specializes the universal curve to the target `(1, r, s, t) • W` of the
universal strict arrow. -/
theorem map_strictRightUnit :
    WeierstrassCurve.map Universal.curve strictRightUnit =
      heisenbergHom _ strictChange • WeierstrassCurve.map Universal.curve strictLeftUnit :=
  map_specialize _

/-- If `k : A[r, s, t] →+* R` classifies the strict arrow `W → (1, r, s, t) • W`, then `k ∘ η_R`
classifies its target. -/
theorem map_comp_strictRightUnit (k : StrictArrowRing →+* R) :
    WeierstrassCurve.map Universal.curve (k.comp strictRightUnit) =
      heisenbergHom R (HeisenbergGroup.map k strictChange) •
        WeierstrassCurve.map Universal.curve (k.comp strictLeftUnit) := by
  rw [← WeierstrassCurve.map_map, map_strictRightUnit, ← map_variableChange,
    WeierstrassCurve.VariableChange.map_heisenbergHom, WeierstrassCurve.map_map]

/-- `η_R(a₁) = a₁ + 2s`. -/
theorem strictRightUnit_X_A₁ :
    strictRightUnit (X .A₁) = X (.inl .A₁) + 2 * X (.inr 1) := by
  simp [strictRightUnit, variableChange_a₁]

/-- `η_R(a₂) = a₂ - s a₁ + 3r - s²`. -/
theorem strictRightUnit_X_A₂ :
    strictRightUnit (X .A₂) =
      X (.inl .A₂) - X (.inr 1) * X (.inl .A₁) + 3 * X (.inr 0) - X (.inr 1) ^ 2 := by
  simp [strictRightUnit, variableChange_a₂]

/-- `η_R(a₃) = a₃ + r a₁ + 2t`. -/
theorem strictRightUnit_X_A₃ :
    strictRightUnit (X .A₃) = X (.inl .A₃) + X (.inr 0) * X (.inl .A₁) + 2 * X (.inr 2) := by
  simp [strictRightUnit, variableChange_a₃]

/-- `η_R(a₄) = a₄ - s a₃ + 2r a₂ - (t + rs) a₁ + 3r² - 2st`. -/
theorem strictRightUnit_X_A₄ :
    strictRightUnit (X .A₄) =
      X (.inl .A₄) - X (.inr 1) * X (.inl .A₃) + 2 * X (.inr 0) * X (.inl .A₂) -
        (X (.inr 2) + X (.inr 0) * X (.inr 1)) * X (.inl .A₁) + 3 * X (.inr 0) ^ 2 -
          2 * X (.inr 1) * X (.inr 2) := by
  simp [strictRightUnit, variableChange_a₄]

/-- `η_R(a₆) = a₆ + r a₄ + r² a₂ + r³ - t a₃ - t² - rt a₁`. -/
theorem strictRightUnit_X_A₆ :
    strictRightUnit (X .A₆) =
      X (.inl .A₆) + X (.inr 0) * X (.inl .A₄) + X (.inr 0) ^ 2 * X (.inl .A₂) + X (.inr 0) ^ 3 -
        X (.inr 2) * X (.inl .A₃) - X (.inr 2) ^ 2 - X (.inr 0) * X (.inr 2) * X (.inl .A₁) := by
  simp [strictRightUnit, variableChange_a₆]

/-! ### The strict counit -/

/-- The **strict counit** `ε : A[r, s, t] →+* A`, classifying the identity arrows: it sends
`r, s, t` to `0`. -/
def strictCounit : StrictArrowRing →+* MvPolynomial Coeff ℤ :=
  (aeval (Sum.elim X 0)).toRingHom

@[simp]
theorem strictCounit_X_inl (i : Coeff) : strictCounit (X (.inl i)) = X i := by
  simp [strictCounit]

@[simp]
theorem strictCounit_X_inr (j : Fin 3) : strictCounit (X (.inr j)) = 0 := by
  simp [strictCounit]

/-- `ε η_L = id`. -/
@[simp]
theorem strictCounit_comp_strictLeftUnit : strictCounit.comp strictLeftUnit = RingHom.id _ :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by simp

/-- The counit classifies the identity change of variables. -/
theorem heisenbergGroupMap_strictCounit_strictChange :
    HeisenbergGroup.map strictCounit strictChange = 1 := by
  ext <;> simp

/-- `ε η_R = id`: the target of an identity arrow `W → W` is `W`. -/
@[simp]
theorem strictCounit_comp_strictRightUnit : strictCounit.comp strictRightUnit = RingHom.id _ := by
  refine Universal.map_curve_injective ?_
  dsimp only
  rw [map_comp_strictRightUnit, heisenbergGroupMap_strictCounit_strictChange, map_one, one_smul,
    strictCounit_comp_strictLeftUnit]

@[simp]
theorem strictCounit_strictLeftUnit (a : MvPolynomial Coeff ℤ) :
    strictCounit (strictLeftUnit a) = a :=
  RingHom.congr_fun strictCounit_comp_strictLeftUnit a

@[simp]
theorem strictCounit_strictRightUnit (a : MvPolynomial Coeff ℤ) :
    strictCounit (strictRightUnit a) = a :=
  RingHom.congr_fun strictCounit_comp_strictRightUnit a

/-! ### Composable pairs and the strict coproduct -/

/-- The ring `A[r, s, t] ⊗_A A[r, s, t] = A[r₁, s₁, t₁, r₂, s₂, t₂]` of composable pairs of strict
arrows `W → C₁ • W → C₂ • (C₁ • W)`, the pushout of `η_R` on the left factor and `η_L` on the right
factor. The coordinates of the first arrow `C₁` are indexed by `Sum.inr (Sum.inl j)` and those of
the second arrow `C₂` by `Sum.inr (Sum.inr j)`. -/
abbrev StrictPairRing : Type := MvPolynomial (Coeff ⊕ (Fin 3 ⊕ Fin 3)) ℤ

/-- The left factor `A[r, s, t] →+* A[r, s, t] ⊗_A A[r, s, t]`, classifying the first arrow. -/
def strictLeft : StrictArrowRing →+* StrictPairRing :=
  (rename (Sum.map id Sum.inl)).toRingHom

@[simp]
theorem strictLeft_X (i : Coeff ⊕ Fin 3) :
    strictLeft (X i) = X (Sum.map id Sum.inl i) := by
  simp [strictLeft]

/-- The right factor `A[r, s, t] →+* A[r, s, t] ⊗_A A[r, s, t]`, classifying the second arrow. On
the coefficients it is the right unit of the left factor, since the source of the second arrow is
the target of the first. -/
def strictRight : StrictArrowRing →+* StrictPairRing :=
  (aeval (Sum.elim (fun i ↦ strictLeft (strictRightUnit (X i)))
    fun j ↦ X (.inr (.inr j)))).toRingHom

@[simp]
theorem strictRight_X_inl (i : Coeff) :
    strictRight (X (.inl i)) = strictLeft (strictRightUnit (X i)) := by
  simp [strictRight]

@[simp]
theorem strictRight_X_inr (j : Fin 3) : strictRight (X (.inr j)) = X (.inr (.inr j)) := by
  simp [strictRight]

/-- The pushout relation `(1 ⊗ η_L) = (η_R ⊗ 1)`: the source of the second arrow is the target of
the first. -/
theorem strictRight_comp_strictLeftUnit :
    strictRight.comp strictLeftUnit = strictLeft.comp strictRightUnit :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by simp

/-- The **strict coproduct** `Δ : A[r, s, t] →+* A[r, s, t] ⊗_A A[r, s, t]`, classifying the
composite `C₂ * C₁` of the universal composable pair `W → C₁ • W → C₂ • (C₁ • W)`. -/
def strictCoproduct : StrictArrowRing →+* StrictPairRing :=
  (strictArrowEquiv _).symm (WeierstrassCurve.map Universal.curve (strictLeft.comp strictLeftUnit),
    HeisenbergGroup.map strictRight strictChange * HeisenbergGroup.map strictLeft strictChange)

/-- `Δ η_L = (η_L ⊗ 1) η_L`: the source of a composite is the source of its first factor. -/
@[simp]
theorem strictCoproduct_comp_strictLeftUnit :
    strictCoproduct.comp strictLeftUnit = strictLeft.comp strictLeftUnit := by
  refine Universal.map_curve_injective ?_
  exact congrArg Prod.fst ((strictArrowEquiv StrictPairRing).apply_symm_apply _)

/-- The coproduct sends the universal strict change of variables to the composite `C₂ * C₁`. -/
theorem heisenbergGroupMap_strictCoproduct_strictChange :
    HeisenbergGroup.map strictCoproduct strictChange =
      HeisenbergGroup.map strictRight strictChange * HeisenbergGroup.map strictLeft strictChange :=
  congrArg Prod.snd ((strictArrowEquiv StrictPairRing).apply_symm_apply _)

/-- `Δ η_R = (1 ⊗ η_R) η_R`: the target of a composite is the target of its second factor. -/
@[simp]
theorem strictCoproduct_comp_strictRightUnit :
    strictCoproduct.comp strictRightUnit = strictRight.comp strictRightUnit := by
  refine Universal.map_curve_injective ?_
  dsimp only
  rw [map_comp_strictRightUnit, map_comp_strictRightUnit, strictRight_comp_strictLeftUnit,
    map_comp_strictRightUnit, heisenbergGroupMap_strictCoproduct_strictChange, map_mul, mul_smul,
    strictCoproduct_comp_strictLeftUnit]

@[simp]
theorem strictCoproduct_strictLeftUnit (a : MvPolynomial Coeff ℤ) :
    strictCoproduct (strictLeftUnit a) = strictLeft (strictLeftUnit a) :=
  RingHom.congr_fun strictCoproduct_comp_strictLeftUnit a

@[simp]
theorem strictCoproduct_strictRightUnit (a : MvPolynomial Coeff ℤ) :
    strictCoproduct (strictRightUnit a) = strictRight (strictRightUnit a) :=
  RingHom.congr_fun strictCoproduct_comp_strictRightUnit a

/-- `Δa = a` on the coefficients. -/
@[simp]
theorem strictCoproduct_X_inl (i : Coeff) : strictCoproduct (X (.inl i)) = X (.inl i) := by
  have := RingHom.congr_fun strictCoproduct_comp_strictLeftUnit (X i)
  simpa only [RingHom.comp_apply, strictLeftUnit_apply, rename_X, strictLeft_X, Sum.map_inl,
    id_eq] using this

/-- `Δr = r₁ + r₂`. -/
theorem strictCoproduct_X_inr_zero :
    strictCoproduct (X (.inr 0)) = X (.inr (.inl 0)) + X (.inr (.inr 0)) := by
  have := congrArg HeisenbergGroup.x heisenbergGroupMap_strictCoproduct_strictChange
  simp only [HeisenbergGroup.map_apply, HeisenbergGroup.mul_x, strictChange_x] at this
  simpa [add_comm] using this

/-- `Δs = s₁ + s₂`. -/
theorem strictCoproduct_X_inr_one :
    strictCoproduct (X (.inr 1)) = X (.inr (.inl 1)) + X (.inr (.inr 1)) := by
  have := congrArg HeisenbergGroup.y heisenbergGroupMap_strictCoproduct_strictChange
  simp only [HeisenbergGroup.map_apply, HeisenbergGroup.mul_y, strictChange_y] at this
  simpa [add_comm] using this

/-- `Δt = t₁ + t₂ + s₁r₂`: the cross term pairs the `s` of the first arrow with the `r` of the
second. -/
theorem strictCoproduct_X_inr_two :
    strictCoproduct (X (.inr 2)) =
      X (.inr (.inl 2)) + X (.inr (.inr 2)) + X (.inr (.inl 1)) * X (.inr (.inr 0)) := by
  have := congrArg HeisenbergGroup.z heisenbergGroupMap_strictCoproduct_strictChange
  simp only [HeisenbergGroup.map_apply, HeisenbergGroup.mul_z, strictChange_x, strictChange_y,
    strictChange_z] at this
  rw [this]
  simp only [strictRight_X_inr, strictLeft_X, Sum.map_inr]
  ring

/-- The map `ε ⊗ id : A[r, s, t] ⊗_A A[r, s, t] →+* A[r, s, t]`, forgetting the first arrow by
sending its coordinates to `0`. -/
def strictCounitLeft : StrictPairRing →+* StrictArrowRing :=
  (aeval (Sum.elim (fun i ↦ X (.inl i)) (Sum.elim 0 fun j ↦ X (.inr j)))).toRingHom

/-- The map `id ⊗ ε : A[r, s, t] ⊗_A A[r, s, t] →+* A[r, s, t]`, forgetting the second arrow by
sending its coordinates to `0`. -/
def strictCounitRight : StrictPairRing →+* StrictArrowRing :=
  (aeval (Sum.elim (fun i ↦ X (.inl i)) (Sum.elim (fun j ↦ X (.inr j)) 0))).toRingHom

@[simp]
theorem strictCounitLeft_X_inl (i : Coeff) : strictCounitLeft (X (.inl i)) = X (.inl i) := by
  simp [strictCounitLeft]

@[simp]
theorem strictCounitLeft_X_inr_inl (j : Fin 3) : strictCounitLeft (X (.inr (.inl j))) = 0 := by
  simp [strictCounitLeft]

@[simp]
theorem strictCounitLeft_X_inr_inr (j : Fin 3) :
    strictCounitLeft (X (.inr (.inr j))) = X (.inr j) := by
  simp [strictCounitLeft]

@[simp]
theorem strictCounitRight_X_inl (i : Coeff) : strictCounitRight (X (.inl i)) = X (.inl i) := by
  simp [strictCounitRight]

@[simp]
theorem strictCounitRight_X_inr_inl (j : Fin 3) :
    strictCounitRight (X (.inr (.inl j))) = X (.inr j) := by
  simp [strictCounitRight]

@[simp]
theorem strictCounitRight_X_inr_inr (j : Fin 3) : strictCounitRight (X (.inr (.inr j))) = 0 := by
  simp [strictCounitRight]

/-- `(ε ⊗ id)` restricts to `η_L ε` on the left factor. -/
theorem strictCounitLeft_comp_strictLeft :
    strictCounitLeft.comp strictLeft = strictLeftUnit.comp strictCounit :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j <;> simp

/-- `(ε ⊗ id)` restricts to the identity on the right factor. -/
theorem strictCounitLeft_comp_strictRight : strictCounitLeft.comp strictRight = RingHom.id _ :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simpa using RingHom.congr_fun strictCounitLeft_comp_strictLeft (strictRightUnit (X i))
    · simp

/-- `(id ⊗ ε)` restricts to the identity on the left factor. -/
theorem strictCounitRight_comp_strictLeft : strictCounitRight.comp strictLeft = RingHom.id _ :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j <;> simp

/-- `(id ⊗ ε)` restricts to `η_R ε` on the right factor. -/
theorem strictCounitRight_comp_strictRight :
    strictCounitRight.comp strictRight = strictRightUnit.comp strictCounit :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simpa using RingHom.congr_fun strictCounitRight_comp_strictLeft (strictRightUnit (X i))
    · simp

/-- **The left counit law** `(ε ⊗ id) Δ = id`. -/
theorem strictCounitLeft_comp_strictCoproduct :
    strictCounitLeft.comp strictCoproduct = RingHom.id _ :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simp
    · fin_cases j <;>
        simp [strictCoproduct_X_inr_zero, strictCoproduct_X_inr_one,
          strictCoproduct_X_inr_two]

/-- **The right counit law** `(id ⊗ ε) Δ = id`. -/
theorem strictCounitRight_comp_strictCoproduct :
    strictCounitRight.comp strictCoproduct = RingHom.id _ :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simp
    · fin_cases j <;>
        simp [strictCoproduct_X_inr_zero, strictCoproduct_X_inr_one,
          strictCoproduct_X_inr_two]

/-! ### Coassociativity -/

/-- The ring `A[r, s, t]^{⊗_A 3} = A[r₁, s₁, t₁, r₂, s₂, t₂, r₃, s₃, t₃]` of composable triples of
strict arrows. The coordinates of the three arrows are indexed by `Sum.inr (Sum.inl j)`,
`Sum.inr (Sum.inr (Sum.inl j))` and `Sum.inr (Sum.inr (Sum.inr j))`. -/
abbrev StrictTripleRing : Type := MvPolynomial (Coeff ⊕ (Fin 3 ⊕ (Fin 3 ⊕ Fin 3))) ℤ

/-- The map `Δ ⊗ id` into composable triples, composing the first two arrows: the first factor of a
composable pair goes to the composite of the first two arrows of the triple, the second factor to
the third arrow. -/
def strictCoproductLeft : StrictPairRing →+* StrictTripleRing :=
  (aeval (Sum.elim (fun i ↦ X (.inl i)) (Sum.elim
    (fun j ↦ rename (Sum.map id (Sum.map id Sum.inl)) (strictCoproduct (X (.inr j))))
    fun j ↦ X (.inr (.inr (.inr j)))))).toRingHom

/-- The map `id ⊗ Δ` into composable triples, composing the last two arrows: the first factor of a
composable pair goes to the first arrow of the triple, the second factor to the composite of the
last two arrows. -/
def strictCoproductRight : StrictPairRing →+* StrictTripleRing :=
  (aeval (Sum.elim (fun i ↦ X (.inl i)) (Sum.elim (fun j ↦ X (.inr (.inl j)))
    fun j ↦ rename (Sum.map id Sum.inr) (strictCoproduct (X (.inr j)))))).toRingHom

@[simp]
theorem strictCoproductLeft_X_inl (i : Coeff) : strictCoproductLeft (X (.inl i)) = X (.inl i) := by
  simp [strictCoproductLeft]

@[simp]
theorem strictCoproductLeft_X_inr_inl (j : Fin 3) :
    strictCoproductLeft (X (.inr (.inl j))) =
      rename (Sum.map id (Sum.map id Sum.inl)) (strictCoproduct (X (.inr j))) := by
  simp [strictCoproductLeft]

@[simp]
theorem strictCoproductLeft_X_inr_inr (j : Fin 3) :
    strictCoproductLeft (X (.inr (.inr j))) = X (.inr (.inr (.inr j))) := by
  simp [strictCoproductLeft]

@[simp]
theorem strictCoproductRight_X_inl (i : Coeff) :
    strictCoproductRight (X (.inl i)) = X (.inl i) := by
  simp [strictCoproductRight]

@[simp]
theorem strictCoproductRight_X_inr_inl (j : Fin 3) :
    strictCoproductRight (X (.inr (.inl j))) = X (.inr (.inl j)) := by
  simp [strictCoproductRight]

@[simp]
theorem strictCoproductRight_X_inr_inr (j : Fin 3) :
    strictCoproductRight (X (.inr (.inr j))) =
      rename (Sum.map id Sum.inr) (strictCoproduct (X (.inr j))) := by
  simp [strictCoproductRight]

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ`: composition of strict arrows is associative.
On `t` both sides are `t₁ + t₂ + t₃ + s₁r₂ + s₁r₃ + s₂r₃`. -/
theorem strictCoproduct_coassoc :
    strictCoproductLeft.comp strictCoproduct = strictCoproductRight.comp strictCoproduct :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    rcases i with i | j
    · simp
    · fin_cases j <;>
        simp [strictCoproduct_X_inr_zero,
          strictCoproduct_X_inr_one, strictCoproduct_X_inr_two] <;> ring

/-! ### The strict conjugation -/

/-- The **strict conjugation** `c : A[r, s, t] →+* A[r, s, t]`, classifying the inverse
`C⁻¹ : C • W → W` of the universal strict arrow. -/
def strictConjugation : StrictArrowRing →+* StrictArrowRing :=
  (strictArrowEquiv _).symm (WeierstrassCurve.map Universal.curve strictRightUnit, strictChange⁻¹)

/-- `c η_L = η_R`: the source of the inverse arrow is the target of the arrow. -/
@[simp]
theorem strictConjugation_comp_strictLeftUnit :
    strictConjugation.comp strictLeftUnit = strictRightUnit := by
  refine Universal.map_curve_injective ?_
  exact congrArg Prod.fst ((strictArrowEquiv StrictArrowRing).apply_symm_apply _)

/-- The conjugation sends the universal strict change of variables to its inverse. -/
theorem heisenbergGroupMap_strictConjugation_strictChange :
    HeisenbergGroup.map strictConjugation strictChange = strictChange⁻¹ :=
  congrArg Prod.snd ((strictArrowEquiv StrictArrowRing).apply_symm_apply _)

/-- `c η_R = η_L`: the target of the inverse arrow is the source of the arrow. -/
@[simp]
theorem strictConjugation_comp_strictRightUnit :
    strictConjugation.comp strictRightUnit = strictLeftUnit := by
  refine Universal.map_curve_injective ?_
  dsimp only
  rw [map_comp_strictRightUnit, heisenbergGroupMap_strictConjugation_strictChange,
    strictConjugation_comp_strictLeftUnit, map_strictRightUnit, map_inv, ← mul_smul,
    inv_mul_cancel, one_smul]

/-- `c c = id`: the inverse of the inverse is the original arrow. -/
@[simp]
theorem strictConjugation_comp_strictConjugation :
    strictConjugation.comp strictConjugation = RingHom.id _ := by
  refine strictArrowRing_ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, strictConjugation_comp_strictLeftUnit,
      strictConjugation_comp_strictRightUnit, RingHom.id_comp]
  · rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply,
      heisenbergGroupMap_strictConjugation_strictChange, map_inv,
      heisenbergGroupMap_strictConjugation_strictChange, inv_inv, HeisenbergGroup.map_id,
      MonoidHom.id_apply]

/-- `ε c = ε`: the inverse of an identity arrow is an identity arrow. -/
@[simp]
theorem strictCounit_comp_strictConjugation :
    strictCounit.comp strictConjugation = strictCounit := by
  refine strictArrowRing_ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, strictConjugation_comp_strictLeftUnit,
      strictCounit_comp_strictRightUnit, strictCounit_comp_strictLeftUnit]
  · rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply,
      heisenbergGroupMap_strictConjugation_strictChange, map_inv,
      heisenbergGroupMap_strictCounit_strictChange, inv_one]

@[simp]
theorem strictConjugation_strictLeftUnit (a : MvPolynomial Coeff ℤ) :
    strictConjugation (strictLeftUnit a) = strictRightUnit a :=
  RingHom.congr_fun strictConjugation_comp_strictLeftUnit a

@[simp]
theorem strictConjugation_strictRightUnit (a : MvPolynomial Coeff ℤ) :
    strictConjugation (strictRightUnit a) = strictLeftUnit a :=
  RingHom.congr_fun strictConjugation_comp_strictRightUnit a

@[simp]
theorem strictConjugation_strictConjugation (x : StrictArrowRing) :
    strictConjugation (strictConjugation x) = x :=
  RingHom.congr_fun strictConjugation_comp_strictConjugation x

@[simp]
theorem strictCounit_strictConjugation (x : StrictArrowRing) :
    strictCounit (strictConjugation x) = strictCounit x :=
  RingHom.congr_fun strictCounit_comp_strictConjugation x

/-- `c(r) = -r`. -/
theorem strictConjugation_X_inr_zero : strictConjugation (X (.inr 0)) = -X (.inr 0) := by
  simpa using congrArg HeisenbergGroup.x heisenbergGroupMap_strictConjugation_strictChange

/-- `c(s) = -s`. -/
theorem strictConjugation_X_inr_one : strictConjugation (X (.inr 1)) = -X (.inr 1) := by
  simpa using congrArg HeisenbergGroup.y heisenbergGroupMap_strictConjugation_strictChange

/-- `c(t) = -t + rs`. -/
theorem strictConjugation_X_inr_two :
    strictConjugation (X (.inr 2)) = -X (.inr 2) + X (.inr 0) * X (.inr 1) := by
  simpa using congrArg HeisenbergGroup.z heisenbergGroupMap_strictConjugation_strictChange

/-! ### The grading -/

/-- The weights of the generators of `A[r, s, t]`: `1, 2, 3, 4, 6` for `a₁, a₂, a₃, a₄, a₆` and
`2, 1, 3` for `r, s, t`. Twice the weight is the topological degree used by Bauer. -/
def strictWeight : Coeff ⊕ Fin 3 → ℕ :=
  Sum.elim coefficientWeight ![2, 1, 3]

/-- The weights of the generators of `A[r₁, s₁, t₁, r₂, s₂, t₂]`: those of `strictWeight` on each
factor. -/
def strictPairWeight : Coeff ⊕ (Fin 3 ⊕ Fin 3) → ℕ :=
  Sum.elim coefficientWeight (Sum.elim ![2, 1, 3] ![2, 1, 3])

/-- A coefficient `aᵢ` has weight `i`. -/
@[simp] theorem strictWeight_inl (i : Coeff) : strictWeight (.inl i) = coefficientWeight i := (rfl)

/-- `r` has weight `2`. -/
@[simp] theorem strictWeight_inr_zero : strictWeight (.inr 0) = 2 := (rfl)

/-- `s` has weight `1`. -/
@[simp] theorem strictWeight_inr_one : strictWeight (.inr 1) = 1 := (rfl)

/-- `t` has weight `3`. -/
@[simp] theorem strictWeight_inr_two : strictWeight (.inr 2) = 3 := (rfl)

/-- A coefficient `aᵢ` has weight `i`. -/
@[simp] theorem strictPairWeight_inl (i : Coeff) :
    strictPairWeight (.inl i) = coefficientWeight i := (rfl)

/-- On the generators `r₁, s₁, t₁` of the left factor, `strictPairWeight` is `strictWeight`. -/
@[simp] theorem strictPairWeight_inr_inl (j : Fin 3) :
    strictPairWeight (.inr (.inl j)) = strictWeight (.inr j) := (rfl)

/-- On the generators `r₂, s₂, t₂` of the right factor, `strictPairWeight` is `strictWeight`. -/
@[simp] theorem strictPairWeight_inr_inr (j : Fin 3) :
    strictPairWeight (.inr (.inr j)) = strictWeight (.inr j) := (rfl)

/-- The left unit is graded. -/
theorem isWeightedHomogeneous_strictLeftUnit {k : ℕ} {f : MvPolynomial Coeff ℤ}
    (hf : f.IsWeightedHomogeneous coefficientWeight k) :
    (strictLeftUnit f).IsWeightedHomogeneous strictWeight k := by
  rw [strictLeftUnit_apply, rename_eq_aeval]
  exact hf.aeval fun i ↦ isWeightedHomogeneous_X ℤ strictWeight (.inl i)

/-- The strict right unit of each coefficient `aᵢ` is weighted homogeneous of weight `i`. -/
theorem isWeightedHomogeneous_strictRightUnit_X (i : Coeff) :
    (strictRightUnit (X i)).IsWeightedHomogeneous strictWeight (coefficientWeight i) :=
  isWeightedHomogeneous_of_aeval_C_pow_mul_X_eq (pow_right_injective₀ two_pos (by norm_num)) <| by
    cases i <;>
      simp [strictRightUnit_X_A₁, strictRightUnit_X_A₂, strictRightUnit_X_A₃,
        strictRightUnit_X_A₄, strictRightUnit_X_A₆] <;> ring

/-- **The strict right unit is graded**: it carries a polynomial of weight `k` in the coefficients
to an element of weight `k` of `A[r, s, t]`. -/
theorem isWeightedHomogeneous_strictRightUnit {k : ℕ} {f : MvPolynomial Coeff ℤ}
    (hf : f.IsWeightedHomogeneous coefficientWeight k) :
    (strictRightUnit f).IsWeightedHomogeneous strictWeight k :=
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := ℤ) (w := strictWeight)
  (WeightedHomogeneousSubmodule.map_mem_iff coefficientWeight
    (weightedHomogeneousSubmodule ℤ strictWeight) (.id ℕ) strictRightUnit).2
      isWeightedHomogeneous_strictRightUnit_X hf

/-- The strict counit is graded. -/
theorem isWeightedHomogeneous_strictCounit {k : ℕ} {f : StrictArrowRing}
    (hf : f.IsWeightedHomogeneous strictWeight k) :
    (strictCounit f).IsWeightedHomogeneous coefficientWeight k := by
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := ℤ) (w := coefficientWeight)
  refine (WeightedHomogeneousSubmodule.map_mem_iff strictWeight
    (weightedHomogeneousSubmodule ℤ coefficientWeight) (.id ℕ) strictCounit).2 (fun i ↦ ?_) hf
  rcases i with i | j
  · simpa using isWeightedHomogeneous_X ℤ coefficientWeight i
  · simp

/-- **The strict coproduct is graded**: it carries an element of weight `k` of `A[r, s, t]` to an
element of weight `k` of `A[r₁, s₁, t₁, r₂, s₂, t₂]`. -/
theorem isWeightedHomogeneous_strictCoproduct {k : ℕ} {f : StrictArrowRing}
    (hf : f.IsWeightedHomogeneous strictWeight k) :
    (strictCoproduct f).IsWeightedHomogeneous strictPairWeight k := by
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := ℤ) (w := strictPairWeight)
  refine (WeightedHomogeneousSubmodule.map_mem_iff strictWeight
    (weightedHomogeneousSubmodule ℤ strictPairWeight) (.id ℕ) strictCoproduct).2 (fun i ↦
      isWeightedHomogeneous_of_aeval_C_pow_mul_X_eq (pow_right_injective₀ two_pos (by norm_num))
        ?_) hf
  rcases i with i | j
  · simp
  · fin_cases j <;>
      simp [strictCoproduct_X_inr_zero, strictCoproduct_X_inr_one,
        strictCoproduct_X_inr_two] <;> ring

/-- **The strict conjugation is graded.** -/
theorem isWeightedHomogeneous_strictConjugation {k : ℕ} {f : StrictArrowRing}
    (hf : f.IsWeightedHomogeneous strictWeight k) :
    (strictConjugation f).IsWeightedHomogeneous strictWeight k := by
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := ℤ) (w := strictWeight)
  refine (WeightedHomogeneousSubmodule.map_mem_iff strictWeight
    (weightedHomogeneousSubmodule ℤ strictWeight) (.id ℕ) strictConjugation).2 (fun i ↦ ?_) hf
  rcases i with i | j
  · have := strictConjugation_strictLeftUnit (X i)
    rw [strictLeftUnit_X] at this
    rw [this]
    exact isWeightedHomogeneous_strictRightUnit_X i
  · refine isWeightedHomogeneous_of_aeval_C_pow_mul_X_eq
      (pow_right_injective₀ two_pos (by norm_num)) ?_
    fin_cases j <;>
      simp [strictConjugation_X_inr_zero, strictConjugation_X_inr_one,
        strictConjugation_X_inr_two] <;> ring

/-! ### The dictionary with the Weierstrass Hopf algebroid `(A, Γ)` -/

/-- The map `Γ = A[u, u⁻¹, r, s, t] →+* A[r, s, t]` setting `u = 1`: it classifies the
inclusion of the strict changes of variables `(1, r, s, t)` among all changes of variables. -/
def toStrict : ArrowRing →+* StrictArrowRing :=
  lift (strictLeftUnit, heisenbergHom _ strictChange)

/-- `toStrict` intertwines the left units. -/
@[simp]
theorem toStrict_comp_algebraMap :
    toStrict.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) = strictLeftUnit :=
  lift_comp_algebraMap _

@[simp]
theorem toStrict_algebraMap (a : MvPolynomial Coeff ℤ) :
    toStrict (algebraMap (MvPolynomial Coeff ℤ) ArrowRing a) = strictLeftUnit a :=
  RingHom.congr_fun toStrict_comp_algebraMap a

/-- `toStrict` sends the universal change of variables `(u, r, s, t)` to `(1, r, s, t)`. -/
@[simp]
theorem universalChange_map_toStrict :
    (universalChange (MvPolynomial Coeff ℤ)).map toStrict = heisenbergHom _ strictChange :=
  map_lift _

/-- `toStrict` intertwines the right units. -/
@[simp]
theorem toStrict_comp_rightUnit : toStrict.comp rightUnit = strictRightUnit := by
  refine Universal.map_curve_injective ?_
  dsimp only
  rw [map_comp_rightUnit, universalChange_map_toStrict, toStrict_comp_algebraMap,
    map_strictRightUnit]

@[simp]
theorem toStrict_rightUnit (a : MvPolynomial Coeff ℤ) :
    toStrict (rightUnit a) = strictRightUnit a :=
  RingHom.congr_fun toStrict_comp_rightUnit a

/-- `toStrict` intertwines the counits. -/
@[simp]
theorem strictCounit_comp_toStrict : strictCounit.comp toStrict = counit := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, toStrict_comp_algebraMap, strictCounit_comp_strictLeftUnit,
      counit_comp_algebraMap]
  · rw [← VariableChange.map_map, universalChange_map_toStrict,
      WeierstrassCurve.VariableChange.map_heisenbergHom,
      heisenbergGroupMap_strictCounit_strictChange, map_one, universalChange_map_counit]

@[simp]
theorem strictCounit_toStrict (x : ArrowRing) : strictCounit (toStrict x) = counit x :=
  RingHom.congr_fun strictCounit_comp_toStrict x

/-- `toStrict` intertwines the conjugations. -/
@[simp]
theorem toStrict_comp_conjugation :
    toStrict.comp conjugation = strictConjugation.comp toStrict := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_algebraMap, toStrict_comp_rightUnit,
      RingHom.comp_assoc, toStrict_comp_algebraMap, strictConjugation_comp_strictLeftUnit]
  · rw [← VariableChange.map_map, ← VariableChange.map_map, universalChange_map_conjugation,
      VariableChange.map_inv, universalChange_map_toStrict,
      WeierstrassCurve.VariableChange.map_heisenbergHom,
      heisenbergGroupMap_strictConjugation_strictChange, map_inv]

/-- The map `Γ ⊗_A Γ →+* A[r, s, t] ⊗_A A[r, s, t]` setting `u₁ = u₂ = 1`. -/
def toStrictPair : ChangeRing ArrowRing →+* StrictPairRing :=
  lift (strictLeft.comp toStrict, heisenbergHom _ (HeisenbergGroup.map strictRight strictChange))

/-- On the left factor, `toStrictPair` is `toStrict` followed by the left factor. -/
@[simp]
theorem toStrictPair_comp_algebraMap :
    toStrictPair.comp (algebraMap ArrowRing _) = strictLeft.comp toStrict :=
  lift_comp_algebraMap _

/-- On the right factor, `toStrictPair` is `toStrict` followed by the right factor. -/
@[simp]
theorem toStrictPair_comp_map_rightUnit :
    toStrictPair.comp (ChangeRing.map rightUnit) = strictRight.comp toStrict := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, map_comp_algebraMap, ← RingHom.comp_assoc,
      toStrictPair_comp_algebraMap, RingHom.comp_assoc, toStrict_comp_rightUnit,
      RingHom.comp_assoc, toStrict_comp_algebraMap, strictRight_comp_strictLeftUnit]
  · rw [← VariableChange.map_map, universalChange_map_map, ← VariableChange.map_map,
      universalChange_map_toStrict, WeierstrassCurve.VariableChange.map_heisenbergHom, toStrictPair,
      map_lift]

/-- **`toStrict` intertwines the coproducts**: setting `u = 1` turns
`Δu = u₁u₂`, `Δr = r₁ + u₁²r₂`, `Δs = s₁ + u₁s₂` and `Δt = t₁ + u₁³t₂ + s₁u₁²r₂` into the strict
coproduct. -/
theorem toStrictPair_comp_coproduct :
    toStrictPair.comp coproduct = strictCoproduct.comp toStrict := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, coproduct_comp_algebraMap, ← RingHom.comp_assoc,
      toStrictPair_comp_algebraMap, RingHom.comp_assoc, RingHom.comp_assoc,
      toStrict_comp_algebraMap, strictCoproduct_comp_strictLeftUnit]
  · rw [← VariableChange.map_map, universalChange_map_coproduct, ← VariableChange.map_map,
      universalChange_map_toStrict, WeierstrassCurve.VariableChange.map_heisenbergHom,
      heisenbergGroupMap_strictCoproduct_strictChange, map_mul]
    have h₁ : (universalChange ArrowRing).map toStrictPair =
        heisenbergHom _ (HeisenbergGroup.map strictRight strictChange) :=
      map_lift _
    have h₂ : ((universalChange (MvPolynomial Coeff ℤ)).map (algebraMap ArrowRing _)).map
        toStrictPair = heisenbergHom _ (HeisenbergGroup.map strictLeft strictChange) := by
      rw [VariableChange.map_map, toStrictPair_comp_algebraMap, ← VariableChange.map_map,
        universalChange_map_toStrict, WeierstrassCurve.VariableChange.map_heisenbergHom]
    rw [← h₁, ← h₂]
    ext <;> simp [VariableChange.mul_def]

/-- `toStrict` sends the coordinates `u, r, s, t` of the universal change of variables to
`1, r, s, t`. -/
@[simp]
theorem toStrict_algebraMap_X (i : Fin 4) :
    toStrict (algebraMap (MvPolynomial (Fin 4) (MvPolynomial Coeff ℤ)) ArrowRing (X i)) =
      ![1, X (.inr 0), X (.inr 1), X (.inr 2)] i := by
  fin_cases i <;> simp [toStrict]

/-- `toStrict` sends the scaling coordinate `u` to `1`: the character `u⁻ᵏ` of the Hodge line
`ω^k` is invisible in `A[r, s, t]` and is recorded instead by the weight `k`. -/
theorem toStrict_universalChange_u :
    toStrict ((universalChange (MvPolynomial Coeff ℤ)).u : ArrowRing) = 1 := by
  simp

/-- `toStrict` sends `u⁻¹` to `1`. -/
@[simp]
theorem toStrict_universalChange_u_inv :
    toStrict (↑(universalChange (MvPolynomial Coeff ℤ)).u⁻¹ : ArrowRing) = 1 := by
  have h := congrArg toStrict (Units.inv_mul (universalChange (MvPolynomial Coeff ℤ)).u)
  rwa [map_mul, toStrict_universalChange_u, mul_one, map_one] at h

/-- The inclusion `A[r, s, t] →+* Γ = A[u, u⁻¹, r, s, t]` of the coordinates `a, r, s, t`. -/
def ofStrict : StrictArrowRing →+* ArrowRing :=
  (aeval (Sum.elim (fun i ↦ algebraMap (MvPolynomial Coeff ℤ) ArrowRing (X i))
    ![(universalChange (MvPolynomial Coeff ℤ)).r, (universalChange (MvPolynomial Coeff ℤ)).s,
      (universalChange (MvPolynomial Coeff ℤ)).t])).toRingHom

@[simp]
theorem ofStrict_X_inl (i : Coeff) :
    ofStrict (X (.inl i)) = algebraMap (MvPolynomial Coeff ℤ) ArrowRing (X i) := by
  simp [ofStrict]

@[simp]
theorem ofStrict_X_inr_zero :
    ofStrict (X (.inr 0)) = (universalChange (MvPolynomial Coeff ℤ)).r := by
  simp [ofStrict]

@[simp]
theorem ofStrict_X_inr_one :
    ofStrict (X (.inr 1)) = (universalChange (MvPolynomial Coeff ℤ)).s := by
  simp [ofStrict]

@[simp]
theorem ofStrict_X_inr_two :
    ofStrict (X (.inr 2)) = (universalChange (MvPolynomial Coeff ℤ)).t := by
  simp [ofStrict]

/-- `ofStrict` restricts to the left unit of `Γ` on the coefficients. -/
@[simp]
theorem ofStrict_comp_strictLeftUnit :
    ofStrict.comp strictLeftUnit = algebraMap (MvPolynomial Coeff ℤ) ArrowRing :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by simp

/-- `ofStrict` sends the universal strict change to the coordinates `(r, s, t)` of the universal
change of variables. -/
theorem heisenbergGroupMap_ofStrict_strictChange :
    HeisenbergGroup.map ofStrict strictChange =
      ⟨(universalChange (MvPolynomial Coeff ℤ)).r, (universalChange (MvPolynomial Coeff ℤ)).s,
        (universalChange (MvPolynomial Coeff ℤ)).t⟩ := by
  ext <;> simp

/-- `ofStrict` is a section of `toStrict`. -/
@[simp]
theorem toStrict_comp_ofStrict : toStrict.comp ofStrict = RingHom.id _ := by
  refine strictArrowRing_ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, ofStrict_comp_strictLeftUnit, toStrict_comp_algebraMap,
      RingHom.id_comp]
  · rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply, heisenbergGroupMap_ofStrict_strictChange,
      HeisenbergGroup.map_id, MonoidHom.id_apply]
    ext <;> simp

@[simp]
theorem toStrict_ofStrict (x : StrictArrowRing) : toStrict (ofStrict x) = x :=
  RingHom.congr_fun toStrict_comp_ofStrict x

/-- `toStrict` is surjective, with section `ofStrict` (see `toStrict_ofStrict`). -/
theorem toStrict_surjective : Function.Surjective toStrict :=
  fun x ↦ ⟨ofStrict x, toStrict_ofStrict x⟩

/-- **The right unit of `Γ` through the strict right unit.** For `f` weighted homogeneous of weight
`k`, `η_R(f) = u⁻ᵏ η_R'(f)`, where `η_R'` is the strict right unit followed by `ofStrict`. This is
the factorization `(u, r, s, t) = (u, 0, 0, 0) (1, r, s, t)`: a change of variables is a strict
change followed by a scaling, which multiplies a coefficient polynomial of weight `k` by `u⁻ᵏ`. -/
theorem rightUnit_eq_of_isWeightedHomogeneous {k : ℕ} {f : MvPolynomial Coeff ℤ}
    (hf : f.IsWeightedHomogeneous coefficientWeight k) :
    rightUnit f =
      ↑(universalChange (MvPolynomial Coeff ℤ)).u⁻¹ ^ k * ofStrict (strictRightUnit f) := by
  set C := universalChange (MvPolynomial Coeff ℤ)
  set W := WeierstrassCurve.map Universal.curve (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)
  have hC : C • W = scaling _ C.u • heisenbergHom _ ⟨C.r, C.s, C.t⟩ • W := by
    rw [← mul_smul]
    congr 1
    ext <;> simp [VariableChange.mul_def]
  -- `ofStrict ∘ η_R'` classifies the target of the strict part `(1, r, s, t)` of `C`.
  have hstrict :
      ofStrict.comp strictRightUnit = (heisenbergHom _ ⟨C.r, C.s, C.t⟩ • W).specialize := by
    refine Universal.map_curve_injective ?_
    dsimp only
    rw [map_comp_strictRightUnit, heisenbergGroupMap_ofStrict_strictChange,
      ofStrict_comp_strictLeftUnit]
    exact (map_specialize _).symm
  have hR : rightUnit = (C • W).specialize := by
    refine Universal.map_curve_injective ?_
    dsimp only
    rw [map_rightUnit]
    exact (map_specialize _).symm
  -- The scaling `(u, 0, 0, 0)` multiplies the value of `f` by `u⁻ᵏ`, over every ring; this is
  -- stated for a general ring to keep the `ℤ`-algebra structure of `MvPolynomial.aeval` canonical.
  have hscale {S : Type} [CommRing S] (W' : _root_.WeierstrassCurve S) (v : Sˣ) :
      ((⟨v, 0, 0, 0⟩ : VariableChange S) • W').specialize f = ↑v⁻¹ ^ k * W'.specialize f := by
    rw [specialize_mk_smul, hf.aeval_pow_mul, aeval_def]
    exact congrArg _ (eval₂Hom_X _ W'.specialize f)
  rw [hR, hC, WeierstrassCurve.VariableChange.scaling_apply, hscale, ← RingHom.comp_apply,
    hstrict]

end TauCeti.WeierstrassHopfAlgebroid

namespace WeierstrassCurve

open MvPolynomial TauCeti.WeierstrassHopfAlgebroid TauCeti.WeierstrassChange.ChangeRing

/-- **Integral modular forms in Bauer's convention.** A polynomial `f` in the coefficients is an
integral modular form of weight `k` exactly when it is weighted homogeneous of weight `k` and
invariant under the strict changes of variables: `η_R(f) = η_L(f)` in `A[r, s, t]`. -/
theorem isIntegralModularForm_iff_strictRightUnit {k : ℕ} {f : MvPolynomial Coeff ℤ} :
    IsIntegralModularForm k f ↔
      f.IsWeightedHomogeneous coefficientWeight k ∧ strictRightUnit f = strictLeftUnit f := by
  rw [isIntegralModularForm_iff_rightUnit]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hk, h⟩ ↦ ?_⟩
  · exact (isIntegralModularForm_iff_rightUnit.mpr h).isWeightedHomogeneous
  · have h' := congrArg toStrict h
    rw [← RingHom.comp_apply, toStrict_comp_rightUnit, map_mul, map_pow, ← RingHom.comp_apply,
      toStrict_comp_algebraMap] at h'
    rw [h', toStrict_universalChange_u_inv, one_pow, one_mul]
  · rw [rightUnit_eq_of_isWeightedHomogeneous hk, h, ← RingHom.comp_apply,
      ofStrict_comp_strictLeftUnit]

end WeierstrassCurve

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve

/-- The strict right unit fixes `c₄`. -/
theorem strictRightUnit_c₄ :
    strictRightUnit Universal.curve.c₄ = strictLeftUnit Universal.curve.c₄ :=
  (isIntegralModularForm_iff_strictRightUnit.mp isIntegralModularForm_c₄).2

/-- The strict right unit fixes `c₆`. -/
theorem strictRightUnit_c₆ :
    strictRightUnit Universal.curve.c₆ = strictLeftUnit Universal.curve.c₆ :=
  (isIntegralModularForm_iff_strictRightUnit.mp isIntegralModularForm_c₆).2

/-- The strict right unit fixes `Δ`. -/
theorem strictRightUnit_Δ : strictRightUnit Universal.curve.Δ = strictLeftUnit Universal.curve.Δ :=
  (isIntegralModularForm_iff_strictRightUnit.mp isIntegralModularForm_Δ).2

end TauCeti.WeierstrassHopfAlgebroid
