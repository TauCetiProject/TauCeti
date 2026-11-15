/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.SemidirectProduct

/-!
# The strict Weierstrass Hopf algebroid

An admissible change of variables `C = (u, r, s, t)` of Weierstrass equations is *strict* when its
scaling factor is `u = 1`. By `WeierstrassCurve.VariableChange.heisenbergEquivKer`, strict changes
of variables over a commutative ring `R` form the Heisenberg group `TauCeti.HeisenbergGroup R` with
group law

  `(r₂, s₂, t₂) * (r₁, s₁, t₁) = (r₂ + r₁, s₂ + s₁, t₂ + t₁ + r₂ * s₁)`.

Over any commutative base ring `B`, pairs of a ring homomorphism `B →+* R` and a strict change of
variables over `R` are classified by the polynomial ring
`StrictChangeRing B = B[r, s, t] = MvPolynomial (Fin 3) B` (`StrictChangeRing.lift`), whose pushout
universal property is `StrictChangeRing.pushoutLift`, and which receives the specialization map
`StrictChangeRing.fromChangeRing : B[u, u⁻¹, r, s, t] →+* B[r, s, t]` setting `u = 1`.

Taking `B = A = ℤ[a₁, a₂, a₃, a₄, a₆]` gives Bauer's cubic Hopf algebroid
`(A, A[r, s, t])` (`TauCeti.WeierstrassHopfAlgebroid.Strict`), corepresenting the groupoid of
Weierstrass curves and strict coordinate changes:
* the left unit `η_L = MvPolynomial.C` classifies the source curve `W` and the right unit
  `Strict.rightUnit` classifies the target `(1, r, s, t) • W`;
* the counit `Strict.counit` sends `r, s, t` to `0`;
* the coproduct `Strict.coproduct` into `A[r, s, t][r', s', t']` satisfies `Δr = r₁ + r₂`,
  `Δs = s₁ + s₂` and `Δt = t₁ + t₂ + s₁ r₂`, retaining the noncommutative Heisenberg cross term;
* the conjugation `Strict.conjugation` sends `(r, s, t)` to `(-r, -s, r s - t)`.

Specializing `u ↦ 1` defines a Hopf-algebroid morphism `(id_A, toStrict)` from `(A, Γ)` to
`(A, A[r, s, t])`. Conversely, using the semidirect-product decomposition
`VariableChange R ≃* HeisenbergGroup R ⋊ Rˣ`, a polynomial `f ∈ A` is an integral modular form of
weight `k` if and only if `f` is weighted homogeneous of weight `k` and primitive for the strict
right unit, `Strict.rightUnit f = MvPolynomial.C f`
(`WeierstrassCurve.isIntegralModularForm_iff_strictRightUnit`). The even homological grading on
`(A, A[r, s, t])` is constructed in
`TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Grading`.

## Main definitions

* `TauCeti.WeierstrassChange.StrictChangeRing`: the polynomial ring `B[r, s, t]` corepresenting
  strict Weierstrass changes over `B`, with `universalHeisenberg`, `universalChange`, `lift`,
  `pushoutLift` and `fromChangeRing`.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.ArrowRing`: the ring `A[r, s, t]` of strict arrows.
* `TauCeti.WeierstrassHopfAlgebroid.Strict.rightUnit`, `counit`, `coproduct`, `conjugation`: the
  Hopf-algebroid structure maps of `(A, A[r, s, t])`.
* `TauCeti.WeierstrassHopfAlgebroid.toStrict`, `toStrictTensor`: the specialization maps `u ↦ 1`
  from `(A, Γ)` and `Γ ⊗_A Γ` to `(A, A[r, s, t])` and its tensor square.

## Main results

* `Strict.coproduct_coassoc`, `Strict.pushoutLift_counit_id_comp_coproduct`,
  `Strict.pushoutLift_id_counit_comp_coproduct`,
  `Strict.pushoutLift_conjugation_id_comp_coproduct`,
  `Strict.pushoutLift_id_conjugation_comp_coproduct`: the Hopf-algebroid identities of
  `(A, A[r, s, t])`.
* `toStrict_comp_rightUnit`, `strictCounit_comp_toStrict`, `toStrictTensor_comp_coproduct`,
  `toStrict_comp_conjugation`: `(id_A, toStrict)` is a morphism of Hopf algebroids.
* `WeierstrassCurve.isIntegralModularForm_iff_strictRightUnit`: integral modular forms of weight
  `k` are the weighted-homogeneous polynomials of weight `k` fixed by `Strict.rightUnit`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.1.
-/

public section

noncomputable section

open WeierstrassCurve WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

open MvPolynomial

variable {B B' R : Type*} [CommRing B] [CommRing B'] [CommRing R]

/-! ### The ring `B[r, s, t]` of strict Weierstrass coordinate changes -/

variable (B) in
/-- The polynomial ring `B[r, s, t] = MvPolynomial (Fin 3) B`, with indices `0, 1, 2` for `r, s, t`.
Ring homomorphisms out of it classify pairs of a ring homomorphism out of `B` and an element of
`HeisenbergGroup`, i.e. a strict Weierstrass change of variables `(1, r, s, t)`. -/
abbrev StrictChangeRing : Type _ := MvPolynomial (Fin 3) B

namespace StrictChangeRing

variable (B) in
/-- The universal Heisenberg element `(r, s, t) = (X 0, X 1, X 2)` over `B[r, s, t]`. -/
def universalHeisenberg : HeisenbergGroup (StrictChangeRing B) :=
  ⟨X 0, X 1, X 2⟩

variable (B) in
@[simp]
theorem universalHeisenberg_x : (universalHeisenberg B).x = (X 0 : StrictChangeRing B) :=
  (rfl)

variable (B) in
@[simp]
theorem universalHeisenberg_y : (universalHeisenberg B).y = (X 1 : StrictChangeRing B) :=
  (rfl)

variable (B) in
@[simp]
theorem universalHeisenberg_z : (universalHeisenberg B).z = (X 2 : StrictChangeRing B) :=
  (rfl)

variable (B) in
/-- The universal strict change of variables `(1, r, s, t)` over `B[r, s, t]`. -/
def universalChange : VariableChange (StrictChangeRing B) :=
  heisenbergHom (StrictChangeRing B) (universalHeisenberg B)

variable (B) in
/-- The universal strict change of variables is the image of `universalHeisenberg B` under
`heisenbergHom`. -/
theorem universalChange_eq_heisenbergHom :
    universalChange B = heisenbergHom (StrictChangeRing B) (universalHeisenberg B) :=
  (rfl)

variable (B) in
@[simp]
theorem universalChange_u : (universalChange B).u = 1 := by
  simp [universalChange]

variable (B) in
@[simp]
theorem universalChange_r : (universalChange B).r = (X 0 : StrictChangeRing B) := by
  simp [universalChange]

variable (B) in
@[simp]
theorem universalChange_s : (universalChange B).s = (X 1 : StrictChangeRing B) := by
  simp [universalChange]

variable (B) in
@[simp]
theorem universalChange_t : (universalChange B).t = (X 2 : StrictChangeRing B) := by
  simp [universalChange]

/-- **Ring homomorphisms out of `B[r, s, t]`** classify pairs of a ring homomorphism out of `B`
and an element of `HeisenbergGroup R`, i.e. a strict change of variables `(1, r, s, t)` over `R`. -/
def lift : (B →+* R) × HeisenbergGroup R ≃ (StrictChangeRing B →+* R) where
  toFun p := eval₂Hom p.1 ![p.2.x, p.2.y, p.2.z]
  invFun k := (k.comp C, HeisenbergGroup.map k (universalHeisenberg B))
  left_inv p := by
    refine Prod.ext (RingHom.ext fun b ↦ by simp) ?_
    ext <;> simp
  right_inv k := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext fun b ↦ by simp) fun i ↦ ?_
    fin_cases i <;> simp

/-- `lift p` restricts to `p.1` along `C`. -/
@[simp]
theorem lift_comp_C (p : (B →+* R) × HeisenbergGroup R) :
    (lift p).comp C = p.1 :=
  congrArg Prod.fst (lift.left_inv p)

/-- `lift p` agrees with `p.1` on constants from `B`. -/
@[simp]
theorem lift_C (p : (B →+* R) × HeisenbergGroup R) (b : B) :
    lift p (C b) = p.1 b :=
  RingHom.congr_fun (lift_comp_C p) b

/-- `lift p` sends the generators `X 0, X 1, X 2` to the coordinates of `p.2`. -/
@[simp]
theorem lift_X (p : (B →+* R) × HeisenbergGroup R) (i : Fin 3) :
    lift p (X i) = ![p.2.x, p.2.y, p.2.z] i := by
  simp [lift]

/-- `lift p` carries `universalHeisenberg B` to `p.2`. -/
theorem map_lift_universalHeisenberg (p : (B →+* R) × HeisenbergGroup R) :
    HeisenbergGroup.map (lift p) (universalHeisenberg B) = p.2 :=
  congrArg Prod.snd (lift.left_inv p)

/-- `lift p` carries `universalChange B` to `heisenbergHom R p.2`. -/
@[simp]
theorem map_lift_universalChange (p : (B →+* R) × HeisenbergGroup R) :
    (universalChange B).map (lift p) = heisenbergHom R p.2 := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_lift_universalHeisenberg]

@[simp]
theorem lift_symm_apply (k : StrictChangeRing B →+* R) :
    lift.symm k = (k.comp C, HeisenbergGroup.map k (universalHeisenberg B)) :=
  (rfl)

/-- A ring homomorphism out of `B[r, s, t]` is determined by its restriction to `B` and the
Heisenberg element it classifies. -/
theorem ringHom_ext {k k' : StrictChangeRing B →+* R}
    (h₁ : k.comp C = k'.comp C)
    (h₂ : HeisenbergGroup.map k (universalHeisenberg B) =
      HeisenbergGroup.map k' (universalHeisenberg B)) : k = k' :=
  lift.symm.injective (Prod.ext h₁ h₂)

theorem map_universalHeisenberg (f : B →+* B') :
    HeisenbergGroup.map (MvPolynomial.map f) (universalHeisenberg B) = universalHeisenberg B' := by
  ext <;> simp

@[simp]
theorem universalChange_map_map (f : B →+* B') :
    (universalChange B).map (MvPolynomial.map f) = universalChange B' := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_universalHeisenberg,
    ← universalChange_eq_heisenbergHom]

/-- **The universal property of `B'[r, s, t]` as the pushout `B' ⊗_B B[r, s, t]`** of `f : B →+* B'`
and `C`: ring homomorphisms out of it correspond to pairs `(g, h)` of ring homomorphisms out of `B'`
and out of `B[r, s, t]` with `g ∘ f = h ∘ C`, by restriction along `C` and along
`MvPolynomial.map f`. -/
def pushoutLift (f : B →+* B') :
    {p : (B' →+* R) × (StrictChangeRing B →+* R) // p.1.comp f = p.2.comp C} ≃
      (StrictChangeRing B' →+* R) where
  toFun p := eval₂Hom p.1.1 (p.1.2 ∘ X)
  invFun k := ⟨(k.comp C, k.comp (MvPolynomial.map f)),
    RingHom.ext fun b ↦ by simp⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (RingHom.ext (eval₂Hom_C _ _)) ?_)
    refine MvPolynomial.ringHom_ext' ?_ fun i ↦ by simp
    ext b
    simpa using RingHom.congr_fun p.2 b
  right_inv k := MvPolynomial.ringHom_ext' (RingHom.ext fun b ↦ by simp) fun i ↦ by simp

@[simp]
theorem pushoutLift_symm_apply_fst (f : B →+* B') (k : StrictChangeRing B' →+* R) :
    ((pushoutLift f).symm k).1.1 = k.comp C :=
  (rfl)

@[simp]
theorem pushoutLift_symm_apply_snd (f : B →+* B') (k : StrictChangeRing B' →+* R) :
    ((pushoutLift f).symm k).1.2 = k.comp (MvPolynomial.map f) :=
  (rfl)

variable (f : B →+* B')
  (p : {p : (B' →+* R) × (StrictChangeRing B →+* R) // p.1.comp f = p.2.comp C})

@[simp]
theorem pushoutLift_comp_C : (pushoutLift f p).comp C = p.1.1 :=
  congrArg (fun q ↦ q.1.1) ((pushoutLift f).left_inv p)

@[simp]
theorem pushoutLift_comp_map : (pushoutLift f p).comp (MvPolynomial.map f) = p.1.2 :=
  congrArg (fun q ↦ q.1.2) ((pushoutLift f).left_inv p)

@[simp]
theorem pushoutLift_C (b : B') : pushoutLift f p (C b) = p.1.1 b :=
  RingHom.congr_fun (pushoutLift_comp_C f p) b

@[simp]
theorem pushoutLift_map (x : StrictChangeRing B) :
    pushoutLift f p (MvPolynomial.map f x) = p.1.2 x :=
  RingHom.congr_fun (pushoutLift_comp_map f p) x

@[simp]
theorem pushoutLift_X (i : Fin 3) : pushoutLift f p (X i) = p.1.2 (X i) := by
  simpa using pushoutLift_map f p (X i)

/-- A ring homomorphism out of `B'[r, s, t]` is determined by its restrictions along `C` and along
`MvPolynomial.map f`. -/
theorem pushout_ringHom_ext {k k' : StrictChangeRing B' →+* R}
    (h₁ : k.comp C = k'.comp C) (h₂ : k.comp (MvPolynomial.map f) = k'.comp (MvPolynomial.map f)) :
    k = k' :=
  (pushoutLift f).symm.injective (Subtype.ext (Prod.ext h₁ h₂))

variable (B) in
/-- The specialization homomorphism `B[u, u⁻¹, r, s, t] →+* B[r, s, t]` setting `u = 1` and fixing
`r, s, t`, corresponding to the inclusion of `HeisenbergGroup` into `VariableChange`. -/
def fromChangeRing : ChangeRing B →+* StrictChangeRing B :=
  ChangeRing.lift (C, universalChange B)

variable (B) in
@[simp]
theorem fromChangeRing_comp_algebraMap :
    (fromChangeRing B).comp (algebraMap B (ChangeRing B)) = C :=
  ChangeRing.lift_comp_algebraMap _

variable (B) in
@[simp]
theorem fromChangeRing_algebraMap (b : B) :
    fromChangeRing B (algebraMap B (ChangeRing B) b) = C b :=
  ChangeRing.lift_algebraMap _ b

variable (B) in
@[simp]
theorem universalChange_map_fromChangeRing :
    (ChangeRing.universalChange B).map (fromChangeRing B) = universalChange B :=
  ChangeRing.map_lift _

/-- Restricting a classifying map along `fromChangeRing` views a strict change of variables as a
general change of variables with `u = 1`. -/
@[simp]
theorem lift_comp_fromChangeRing (q : (B →+* R) × HeisenbergGroup R) :
    (lift q).comp (fromChangeRing B) = ChangeRing.lift (q.1, heisenbergHom R q.2) := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, fromChangeRing_comp_algebraMap, lift_comp_C,
      ChangeRing.lift_comp_algebraMap]
  · rw [← VariableChange.map_map, universalChange_map_fromChangeRing, map_lift_universalChange,
      ChangeRing.map_lift]

/-- `fromChangeRing` is natural in the base ring `B`. -/
theorem fromChangeRing_comp_map (g : B →+* B') :
    (fromChangeRing B').comp (ChangeRing.map g) = (MvPolynomial.map g).comp (fromChangeRing B) := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · exact RingHom.ext fun b ↦ by simp
  · rw [← VariableChange.map_map, ChangeRing.universalChange_map_map,
      universalChange_map_fromChangeRing, ← VariableChange.map_map,
      universalChange_map_fromChangeRing, universalChange_map_map]

end StrictChangeRing

end TauCeti.WeierstrassChange

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve TauCeti.WeierstrassChange
open TauCeti.WeierstrassChange.StrictChangeRing

namespace Strict

variable {R : Type*} [CommRing R]

/-! ### The strict Weierstrass Hopf algebroid `(A, A[r, s, t])` -/

/-- The ring `A[r, s, t] = ℤ[a₁, a₂, a₃, a₄, a₆][r, s, t]` of arrows of the strict Weierstrass
Hopf algebroid. Its homomorphisms to `R` classify pairs `(W, a)` of a Weierstrass curve `W` and a
strict change of variables `heisenbergHom R a = (1, r, s, t)` over `R`. -/
abbrev ArrowRing : Type := StrictChangeRing (MvPolynomial Coeff ℤ)

/-- The **right unit** `η_R : ℤ[a₁, ⋯, a₆] →+* A[r, s, t]`, classifying the target
`(1, r, s, t) • W` of the universal strict arrow; the left unit `η_L` is `MvPolynomial.C`. -/
def rightUnit : MvPolynomial Coeff ℤ →+* ArrowRing :=
  (universalChange (MvPolynomial Coeff ℤ) • WeierstrassCurve.map Universal.curve C).specialize

/-- The right unit specializes the universal curve to the target `(1, r, s, t) • W` of the
universal strict arrow. -/
@[simp]
theorem map_rightUnit :
    WeierstrassCurve.map Universal.curve rightUnit =
      universalChange (MvPolynomial Coeff ℤ) • WeierstrassCurve.map Universal.curve C :=
  map_specialize _

/-- `η_R(a₁) = a₁ + 2s`. -/
@[simp]
theorem rightUnit_A₁ : rightUnit (X .A₁) = C (X .A₁) + 2 * (X 1 : ArrowRing) := by
  simp [rightUnit, variableChange_a₁]

/-- `η_R(a₂) = a₂ - s a₁ + 3r - s²`. -/
@[simp]
theorem rightUnit_A₂ :
    rightUnit (X .A₂) = C (X .A₂) - X 1 * C (X .A₁) + 3 * X 0 - (X 1 : ArrowRing) ^ 2 := by
  simp [rightUnit, variableChange_a₂]

/-- `η_R(a₃) = a₃ + r a₁ + 2t`. -/
@[simp]
theorem rightUnit_A₃ :
    rightUnit (X .A₃) = C (X .A₃) + X 0 * C (X .A₁) + 2 * (X 2 : ArrowRing) := by
  simp [rightUnit, variableChange_a₃]

/-- `η_R(a₄) = a₄ - s a₃ + 2 r a₂ - (t + r s) a₁ + 3 r² - 2 s t`. -/
@[simp]
theorem rightUnit_A₄ :
    rightUnit (X .A₄) =
      C (X .A₄) - X 1 * C (X .A₃) + 2 * X 0 * C (X .A₂) - (X 2 + X 0 * X 1) * C (X .A₁) +
        3 * X 0 ^ 2 - 2 * X 1 * (X 2 : ArrowRing) := by
  simp [rightUnit, variableChange_a₄]

/-- `η_R(a₆) = a₆ + r a₄ + r² a₂ + r³ - t a₃ - t² - r t a₁`. -/
@[simp]
theorem rightUnit_A₆ :
    rightUnit (X .A₆) =
      C (X .A₆) + X 0 * C (X .A₄) + X 0 ^ 2 * C (X .A₂) + X 0 ^ 3 - X 2 * C (X .A₃) -
        X 2 ^ 2 - X 0 * X 2 * (C (X .A₁) : ArrowRing) := by
  simp [rightUnit, variableChange_a₆]

/-- If `k : A[r, s, t] →+* R` classifies the strict arrow `W → (1, r, s, t) • W`, then `k ∘ η_R`
classifies its target. -/
theorem map_comp_rightUnit (k : ArrowRing →+* R) :
    WeierstrassCurve.map Universal.curve (k.comp rightUnit) =
      (universalChange (MvPolynomial Coeff ℤ)).map k •
        WeierstrassCurve.map Universal.curve (k.comp C) := by
  rw [← WeierstrassCurve.map_map, map_rightUnit, ← map_variableChange, WeierstrassCurve.map_map]

/-- Equivalently to `map_comp_rightUnit`, `k ∘ η_R` is the specialization at the target of the
strict arrow classified by `k`. -/
theorem comp_rightUnit (k : ArrowRing →+* R) :
    k.comp rightUnit =
      ((universalChange (MvPolynomial Coeff ℤ)).map k •
        WeierstrassCurve.map Universal.curve (k.comp C)).specialize := by
  rw [← map_comp_rightUnit, WeierstrassCurve.specialize_map, Universal.specialize_curve,
    RingHom.comp_id]

variable (R) in
/-- **Homomorphisms out of `A[r, s, t]` classify strict arrows**: `k : A[r, s, t] →+* R`
corresponds to the source curve `W` and the Heisenberg element `a` of `W → heisenbergHom R a • W`.
-/
def arrowEquiv : (ArrowRing →+* R) ≃ WeierstrassCurve R × HeisenbergGroup R where
  toFun k := (WeierstrassCurve.map Universal.curve (k.comp C),
    HeisenbergGroup.map k (universalHeisenberg (MvPolynomial Coeff ℤ)))
  invFun p := StrictChangeRing.lift (p.1.specialize, p.2)
  left_inv k := StrictChangeRing.ringHom_ext (by simp) (by simp)
  right_inv p := by simp

@[simp]
theorem arrowEquiv_apply (k : ArrowRing →+* R) :
    arrowEquiv R k = (WeierstrassCurve.map Universal.curve (k.comp C),
      HeisenbergGroup.map k (universalHeisenberg (MvPolynomial Coeff ℤ))) :=
  (rfl)

@[simp]
theorem arrowEquiv_symm_apply (p : WeierstrassCurve R × HeisenbergGroup R) :
    (arrowEquiv R).symm p = StrictChangeRing.lift (p.1.specialize, p.2) :=
  (rfl)

/-! ### The counit -/

/-- The **counit** `ε : A[r, s, t] →+* ℤ[a₁, ⋯, a₆]`, classifying the identity strict arrows and
sending `r, s, t` to `0`. -/
def counit : ArrowRing →+* MvPolynomial Coeff ℤ :=
  StrictChangeRing.lift (RingHom.id _, 1)

@[simp]
theorem counit_X (i : Fin 3) : counit (X i) = 0 := by
  fin_cases i <;> simp [counit]

@[simp]
theorem counit_comp_C : counit.comp C = RingHom.id (MvPolynomial Coeff ℤ) :=
  StrictChangeRing.lift_comp_C _

@[simp]
theorem counit_C (a : MvPolynomial Coeff ℤ) : counit (C a) = a :=
  StrictChangeRing.lift_C _ a

theorem map_counit_universalHeisenberg :
    HeisenbergGroup.map counit (universalHeisenberg (MvPolynomial Coeff ℤ)) = 1 :=
  StrictChangeRing.map_lift_universalHeisenberg _

@[simp]
theorem universalChange_map_counit :
    (universalChange (MvPolynomial Coeff ℤ)).map counit = 1 := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_counit_universalHeisenberg,
    _root_.map_one]

@[simp]
theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id (MvPolynomial Coeff ℤ) :=
  Universal.map_curve_injective (by simp [map_comp_rightUnit])

@[simp]
theorem counit_rightUnit (a : MvPolynomial Coeff ℤ) : counit (rightUnit a) = a :=
  RingHom.congr_fun counit_comp_rightUnit a

/-! ### The coproduct -/

/-- The **coproduct** `Δ : A[r, s, t] →+* A[r, s, t][r', s', t']`, classifying the composite
`a₂ * a₁` of the universal composable pair of strict arrows: the source curve and `a₁` come from
the left factor `C`, and `a₂` comes from the right factor `MvPolynomial.map rightUnit`. -/
def coproduct : ArrowRing →+* StrictChangeRing ArrowRing :=
  StrictChangeRing.lift (C.comp C,
    HeisenbergGroup.map (MvPolynomial.map rightUnit) (universalHeisenberg (MvPolynomial Coeff ℤ)) *
      HeisenbergGroup.map C (universalHeisenberg (MvPolynomial Coeff ℤ)))

@[simp]
theorem coproduct_comp_C : coproduct.comp C = C.comp C :=
  StrictChangeRing.lift_comp_C _

@[simp]
theorem coproduct_C (a : MvPolynomial Coeff ℤ) : coproduct (C a) = C (C a) :=
  RingHom.congr_fun coproduct_comp_C a

theorem map_coproduct_universalHeisenberg :
    HeisenbergGroup.map coproduct (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      HeisenbergGroup.map (MvPolynomial.map rightUnit)
        (universalHeisenberg (MvPolynomial Coeff ℤ)) *
        HeisenbergGroup.map C (universalHeisenberg (MvPolynomial Coeff ℤ)) :=
  StrictChangeRing.map_lift_universalHeisenberg _

@[simp]
theorem universalChange_map_coproduct :
    (universalChange (MvPolynomial Coeff ℤ)).map coproduct =
      universalChange ArrowRing * (universalChange (MvPolynomial Coeff ℤ)).map C := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_coproduct_universalHeisenberg,
    _root_.map_mul, map_universalHeisenberg, ← map_heisenbergHom,
    ← universalChange_eq_heisenbergHom, ← universalChange_eq_heisenbergHom]

@[simp]
theorem coproduct_comp_rightUnit :
    coproduct.comp rightUnit = (MvPolynomial.map rightUnit).comp rightUnit := by
  refine Universal.map_curve_injective ?_
  dsimp only
  have hmap : (MvPolynomial.map (σ := Fin 3) rightUnit).comp C = C.comp rightUnit :=
    RingHom.ext (MvPolynomial.map_C rightUnit)
  rw [map_comp_rightUnit, map_comp_rightUnit, universalChange_map_coproduct, coproduct_comp_C,
    universalChange_map_map, hmap, mul_smul, ← WeierstrassCurve.map_map Universal.curve rightUnit C,
    map_rightUnit, ← map_variableChange, WeierstrassCurve.map_map]

@[simp]
theorem coproduct_rightUnit (a : MvPolynomial Coeff ℤ) :
    coproduct (rightUnit a) = MvPolynomial.map rightUnit (rightUnit a) :=
  RingHom.congr_fun coproduct_comp_rightUnit a

/-- `Δr = r₁ + r₂`. -/
@[simp]
theorem coproduct_r :
    coproduct (X 0) = C (X 0) + (X 0 : StrictChangeRing ArrowRing) := by
  simpa [coproduct] using add_comm (X 0 : StrictChangeRing ArrowRing) (C (X 0))

/-- `Δs = s₁ + s₂`. -/
@[simp]
theorem coproduct_s :
    coproduct (X 1) = C (X 1) + (X 1 : StrictChangeRing ArrowRing) := by
  simpa [coproduct] using add_comm (X 1 : StrictChangeRing ArrowRing) (C (X 1))

/-- `Δt = t₁ + t₂ + s₁ r₂`, retaining the noncommutative Heisenberg cross term. -/
@[simp]
theorem coproduct_t :
    coproduct (X 2) = C (X 2) + X 2 + C (X 1) * (X 0 : StrictChangeRing ArrowRing) := by
  simp [coproduct]
  ring

theorem map_comp_coproduct_universalHeisenberg (k : StrictChangeRing ArrowRing →+* R) :
    HeisenbergGroup.map (k.comp coproduct) (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      HeisenbergGroup.map (k.comp (MvPolynomial.map rightUnit))
        (universalHeisenberg (MvPolynomial Coeff ℤ)) *
        HeisenbergGroup.map (k.comp C) (universalHeisenberg (MvPolynomial Coeff ℤ)) := by
  rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_coproduct_universalHeisenberg,
    _root_.map_mul, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← HeisenbergGroup.map_comp,
    ← HeisenbergGroup.map_comp]

/-- **The left counit law** `(ε ⊗ id) Δ = id`. -/
theorem pushoutLift_counit_id_comp_coproduct :
    (pushoutLift rightUnit ⟨(C.comp counit, RingHom.id ArrowRing), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          coproduct =
      RingHom.id ArrowRing := by
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [map_comp_coproduct_universalHeisenberg, pushoutLift_comp_map, pushoutLift_comp_C]
  dsimp only
  rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_counit_universalHeisenberg,
    _root_.map_one, mul_one]

/-- **The right counit law** `(id ⊗ ε) Δ = id`. -/
theorem pushoutLift_id_counit_comp_coproduct :
    (pushoutLift rightUnit ⟨(RingHom.id ArrowRing, rightUnit.comp counit), by
        rw [RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]⟩).comp coproduct =
      RingHom.id ArrowRing := by
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [map_comp_coproduct_universalHeisenberg, pushoutLift_comp_map, pushoutLift_comp_C]
  dsimp only
  rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_counit_universalHeisenberg,
    _root_.map_one, one_mul]

/-- The map `Δ ⊗ id` into the triple tensor product `A[r, s, t] ⊗_A A[r, s, t] ⊗_A A[r, s, t]`. -/
def coproductLeft :
    StrictChangeRing ArrowRing →+* StrictChangeRing (StrictChangeRing ArrowRing) :=
  pushoutLift rightUnit
    ⟨(C.comp coproduct, MvPolynomial.map ((MvPolynomial.map rightUnit).comp rightUnit)),
      RingHom.ext fun a ↦ by simp⟩

@[simp]
theorem coproductLeft_comp_C :
    coproductLeft.comp C = (C : StrictChangeRing ArrowRing →+* _).comp coproduct :=
  pushoutLift_comp_C _ _

@[simp]
theorem coproductLeft_comp_map :
    coproductLeft.comp (MvPolynomial.map rightUnit) =
      MvPolynomial.map ((MvPolynomial.map rightUnit).comp rightUnit) :=
  pushoutLift_comp_map _ _

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ` of the strict Weierstrass coproduct. -/
theorem coproduct_coassoc :
    coproductLeft.comp coproduct =
      (pushoutLift rightUnit
        ⟨((C : StrictChangeRing ArrowRing →+* _).comp C,
          (MvPolynomial.map (MvPolynomial.map rightUnit)).comp coproduct),
          RingHom.ext fun a ↦ by simp⟩).comp coproduct := by
  simp only [coproductLeft]
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [map_comp_coproduct_universalHeisenberg, map_comp_coproduct_universalHeisenberg,
    pushoutLift_comp_map, pushoutLift_comp_C, pushoutLift_comp_map, pushoutLift_comp_C]
  dsimp only
  rw [map_comp_coproduct_universalHeisenberg C, map_comp_coproduct_universalHeisenberg]
  have h₁ : (MvPolynomial.map (σ := Fin 3) (MvPolynomial.map (σ := Fin 3) rightUnit)).comp C =
      C.comp (MvPolynomial.map rightUnit) :=
    RingHom.ext (MvPolynomial.map_C _)
  have h₂ : (MvPolynomial.map (MvPolynomial.map (σ := Fin 3) rightUnit)).comp
      (MvPolynomial.map (σ := Fin 3) rightUnit) =
      MvPolynomial.map ((MvPolynomial.map rightUnit).comp rightUnit) :=
    RingHom.ext fun p ↦ MvPolynomial.map_map rightUnit (MvPolynomial.map rightUnit) p
  rw [h₁, h₂, mul_assoc]

/-! ### The conjugation -/

/-- The **conjugation** `c : A[r, s, t] →+* A[r, s, t]`, classifying the inverse
`(1, -r, -s, r s - t)` of the universal strict arrow. -/
def conjugation : ArrowRing →+* ArrowRing :=
  StrictChangeRing.lift (rightUnit, (universalHeisenberg (MvPolynomial Coeff ℤ))⁻¹)

@[simp]
theorem conjugation_comp_C : conjugation.comp C = rightUnit :=
  StrictChangeRing.lift_comp_C _

@[simp]
theorem conjugation_C (a : MvPolynomial Coeff ℤ) : conjugation (C a) = rightUnit a :=
  StrictChangeRing.lift_C _ a

theorem map_conjugation_universalHeisenberg :
    HeisenbergGroup.map conjugation (universalHeisenberg (MvPolynomial Coeff ℤ)) =
      (universalHeisenberg (MvPolynomial Coeff ℤ))⁻¹ :=
  StrictChangeRing.map_lift_universalHeisenberg _

@[simp]
theorem universalChange_map_conjugation :
    (universalChange (MvPolynomial Coeff ℤ)).map conjugation =
      (universalChange (MvPolynomial Coeff ℤ))⁻¹ := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_conjugation_universalHeisenberg,
    _root_.map_inv]

@[simp]
theorem conjugation_r : conjugation (X 0) = -(X 0 : ArrowRing) := by
  simp [conjugation]

@[simp]
theorem conjugation_s : conjugation (X 1) = -(X 1 : ArrowRing) := by
  simp [conjugation]

@[simp]
theorem conjugation_t : conjugation (X 2) = X 0 * X 1 - (X 2 : ArrowRing) := by
  simp [conjugation]
  ring

@[simp]
theorem conjugation_comp_rightUnit : conjugation.comp rightUnit = C :=
  Universal.map_curve_injective (by
    dsimp only
    rw [map_comp_rightUnit, universalChange_map_conjugation, conjugation_comp_C, map_rightUnit,
      inv_smul_smul])

@[simp]
theorem conjugation_rightUnit (a : MvPolynomial Coeff ℤ) : conjugation (rightUnit a) = C a :=
  RingHom.congr_fun conjugation_comp_rightUnit a

@[simp]
theorem conjugation_comp_conjugation : conjugation.comp conjugation = RingHom.id ArrowRing := by
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_conjugation_universalHeisenberg,
    _root_.map_inv, map_conjugation_universalHeisenberg, inv_inv, HeisenbergGroup.map_id,
    MonoidHom.id_apply]

@[simp]
theorem conjugation_conjugation (x : ArrowRing) : conjugation (conjugation x) = x :=
  RingHom.congr_fun conjugation_comp_conjugation x

@[simp]
theorem counit_comp_conjugation : counit.comp conjugation = counit := by
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_conjugation_universalHeisenberg,
    _root_.map_inv, map_counit_universalHeisenberg, inv_one]

@[simp]
theorem counit_conjugation (x : ArrowRing) : counit (conjugation x) = counit x :=
  RingHom.congr_fun counit_comp_conjugation x

/-- **The left antipode equation** `μ (c ⊗ id) Δ = η_R ε`. -/
theorem pushoutLift_conjugation_id_comp_coproduct :
    (pushoutLift rightUnit ⟨(conjugation, RingHom.id ArrowRing), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp coproduct =
      rightUnit.comp counit := by
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [map_comp_coproduct_universalHeisenberg, pushoutLift_comp_map, pushoutLift_comp_C]
  dsimp only
  rw [HeisenbergGroup.map_id, MonoidHom.id_apply, map_conjugation_universalHeisenberg,
    mul_inv_cancel, HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_counit_universalHeisenberg,
    _root_.map_one]

/-- **The right antipode equation** `μ (id ⊗ c) Δ = η_L ε`. -/
theorem pushoutLift_id_conjugation_comp_coproduct :
    (pushoutLift rightUnit ⟨(RingHom.id ArrowRing, conjugation), by
        rw [conjugation_comp_C, RingHom.id_comp]⟩).comp coproduct =
      C.comp counit := by
  refine StrictChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  rw [map_comp_coproduct_universalHeisenberg, pushoutLift_comp_map, pushoutLift_comp_C]
  dsimp only
  rw [map_conjugation_universalHeisenberg, HeisenbergGroup.map_id, MonoidHom.id_apply,
    inv_mul_cancel, HeisenbergGroup.map_comp, MonoidHom.comp_apply, map_counit_universalHeisenberg,
    _root_.map_one]

end Strict

/-! ### Comparison between `(A, Γ)` and `(A, A[r, s, t])` -/

/-- The Hopf-algebroid specialization `Γ = A[u, u⁻¹, r, s, t] →+* A[r, s, t]` setting `u = 1`. -/
def toStrict : ArrowRing →+* Strict.ArrowRing :=
  fromChangeRing (MvPolynomial Coeff ℤ)

@[simp]
theorem toStrict_comp_algebraMap :
    toStrict.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) = C :=
  fromChangeRing_comp_algebraMap _

@[simp]
theorem toStrict_algebraMap (a : MvPolynomial Coeff ℤ) :
    toStrict (algebraMap (MvPolynomial Coeff ℤ) ArrowRing a) = C a :=
  fromChangeRing_algebraMap _ a

@[simp]
theorem universalChange_map_toStrict :
    (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map toStrict =
      StrictChangeRing.universalChange (MvPolynomial Coeff ℤ) :=
  universalChange_map_fromChangeRing _

theorem toStrict_u :
    toStrict ((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u : ArrowRing) = 1 := by
  simp [toStrict, fromChangeRing, ChangeRing.universalChange_u]

@[simp]
theorem toStrict_u_inv :
    toStrict ((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u⁻¹ : ArrowRingˣ) = 1 := by
  simp [toStrict, fromChangeRing]

/-- `toStrict` intertwines the right units of `(A, Γ)` and `(A, A[r, s, t])`. -/
@[simp]
theorem toStrict_comp_rightUnit : toStrict.comp rightUnit = Strict.rightUnit :=
  Universal.map_curve_injective (by simp [map_comp_rightUnit])

@[simp]
theorem toStrict_rightUnit (a : MvPolynomial Coeff ℤ) :
    toStrict (rightUnit a) = Strict.rightUnit a :=
  RingHom.congr_fun toStrict_comp_rightUnit a

/-- `toStrict` intertwines the counits of `(A, Γ)` and `(A, A[r, s, t])`. -/
@[simp]
theorem strictCounit_comp_toStrict : Strict.counit.comp toStrict = counit := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  simp [← VariableChange.map_map]

@[simp]
theorem strictCounit_toStrict (x : ArrowRing) : Strict.counit (toStrict x) = counit x :=
  RingHom.congr_fun strictCounit_comp_toStrict x

/-- The tensor-square specialization `Γ ⊗_A Γ →+* A[r, s, t] ⊗_A A[r, s, t]` induced by
`toStrict ⊗ toStrict`. -/
def toStrictTensor : ChangeRing ArrowRing →+* StrictChangeRing Strict.ArrowRing :=
  ChangeRing.pushoutLift rightUnit
    ⟨(C.comp toStrict, (MvPolynomial.map Strict.rightUnit).comp toStrict),
      RingHom.ext fun a ↦ by simp⟩

@[simp]
theorem toStrictTensor_comp_algebraMap :
    toStrictTensor.comp (algebraMap ArrowRing (ChangeRing ArrowRing)) = C.comp toStrict :=
  ChangeRing.pushoutLift_comp_algebraMap _ _

@[simp]
theorem toStrictTensor_comp_map :
    toStrictTensor.comp (ChangeRing.map rightUnit) =
      (MvPolynomial.map Strict.rightUnit).comp toStrict :=
  ChangeRing.pushoutLift_comp_map _ _

/-- `toStrict` intertwines the coproducts of `(A, Γ)` and `(A, A[r, s, t])`. -/
theorem toStrictTensor_comp_coproduct :
    toStrictTensor.comp coproduct = Strict.coproduct.comp toStrict := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp [toStrictTensor]) ?_
  rw [universalChange_map_comp_coproduct, toStrictTensor_comp_map, toStrictTensor_comp_algebraMap]
  have h₁ : (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map
      ((MvPolynomial.map Strict.rightUnit).comp toStrict) =
      StrictChangeRing.universalChange Strict.ArrowRing := by
    rw [← VariableChange.map_map, universalChange_map_toStrict,
      StrictChangeRing.universalChange_map_map]
  have h₂ : (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map
      ((C : Strict.ArrowRing →+* StrictChangeRing Strict.ArrowRing).comp toStrict) =
      (StrictChangeRing.universalChange (MvPolynomial Coeff ℤ)).map C := by
    rw [← VariableChange.map_map, universalChange_map_toStrict]
  rw [h₁, h₂, ← Strict.universalChange_map_coproduct, ← universalChange_map_toStrict,
    VariableChange.map_map]

/-- `toStrict` intertwines the conjugations of `(A, Γ)` and `(A, A[r, s, t])`. -/
@[simp]
theorem toStrict_comp_conjugation :
    toStrict.comp conjugation = Strict.conjugation.comp toStrict := by
  refine ChangeRing.ringHom_ext (RingHom.ext fun a ↦ by simp) ?_
  simp [← VariableChange.map_map]

@[simp]
theorem toStrict_conjugation (x : ArrowRing) :
    toStrict (conjugation x) = Strict.conjugation (toStrict x) :=
  RingHom.congr_fun toStrict_comp_conjugation x

end TauCeti.WeierstrassHopfAlgebroid

/-! ### Integral modular forms as primitives of `(A, A[r, s, t])` -/

namespace WeierstrassCurve

open MvPolynomial TauCeti.WeierstrassHopfAlgebroid TauCeti.WeierstrassChange

/-- **Integral modular forms via the strict Weierstrass Hopf algebroid**: a polynomial
`f ∈ ℤ[a₁, ⋯, a₆]` is an integral modular form of weight `k` if and only if `f` is weighted
homogeneous of weight `k` and is invariant under strict Weierstrass changes
(`Strict.rightUnit f = C f`). -/
theorem isIntegralModularForm_iff_strictRightUnit {k : ℕ} {f : MvPolynomial Coeff ℤ} :
    IsIntegralModularForm k f ↔
      f.IsWeightedHomogeneous coefficientWeight k ∧ Strict.rightUnit f = C f := by
  refine ⟨fun hf ↦ ⟨hf.isWeightedHomogeneous, ?_⟩, ?_⟩
  · have h := congrArg toStrict (isIntegralModularForm_iff_rightUnit.mp hf)
    simpa using h
  · rintro ⟨hdeg, hstrict⟩
    refine isIntegralModularForm_def.mpr fun R _ W C₀ ↦ ?_
    obtain ⟨⟨a, u₀⟩, rfl⟩ := (VariableChange.semidirectProductEquiv R).surjective C₀
    simp only [VariableChange.semidirectProductEquiv_apply]
    have h₁ : (VariableChange.heisenbergHom R a •
          (VariableChange.scaling R u₀ • W)).specialize f =
        (VariableChange.scaling R u₀ • W).specialize f := by
      have hk := congrArg
        (StrictChangeRing.lift ((VariableChange.scaling R u₀ • W).specialize, a)) hstrict
      rw [← RingHom.comp_apply, Strict.comp_rightUnit] at hk
      simpa using hk
    have h₂ :
        (VariableChange.scaling R u₀ • W).specialize f = ↑u₀⁻¹ ^ k * W.specialize f := by
      rw [VariableChange.scaling_apply, specialize_mk_smul, hdeg.aeval_pow_mul]
      exact congrArg _ (DFunLike.congr_fun (aeval_unique W.specialize.toIntAlgHom) f).symm
    have hu : (VariableChange.heisenbergHom R a * VariableChange.scaling R u₀).u = u₀ := by
      simp [VariableChange.mul_def]
    rw [mul_smul, h₁, h₂, hu]

end WeierstrassCurve
