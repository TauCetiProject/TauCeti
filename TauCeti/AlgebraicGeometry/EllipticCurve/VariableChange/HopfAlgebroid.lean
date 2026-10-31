/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.ModularForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic

/-!
# The Weierstrass Hopf algebroid

Let `A = ℤ[a₁, a₂, a₃, a₄, a₆]` be the ring of coefficients of the universal Weierstrass curve
and `Γ = A[u, u⁻¹, r, s, t]`. Ring homomorphisms `Γ →+* R` classify pairs `(W, C)` of a
Weierstrass curve `W` over `R` and an admissible change of variables `C` over `R`, that is,
arrows `W → C • W` of the groupoid of Weierstrass curves over `R`
(`TauCeti.WeierstrassHopfAlgebroid.arrowEquiv`). This file constructs the structure maps
classifying the groupoid operations, and proves the Hopf algebroid equations: the pair `(A, Γ)`
is a cogroupoid object in commutative rings, corepresenting the groupoid of Weierstrass curves
and their changes of variables. Its invariants of weight `k`, the `f ∈ A` with
`η_R f = u⁻ᵏ η_L f`, are the integral modular forms of weight `k`
(`WeierstrassCurve.isIntegralModularForm_iff_rightUnit`).

The **left unit** `η_L : A →+* Γ` is the inclusion `algebraMap`, classifying the source `W`, and
the **right unit** `η_R` (`rightUnit`) classifies the target `C • W`, given by Mathlib's
`WeierstrassCurve.variableChange_def`. The **counit** `ε` classifies the identity arrows.

Composable pairs `W → C₁ • W → C₂ • (C₁ • W)` are classified by the pushout `Γ ⊗_A Γ` of `η_R`
on the left factor and `η_L` on the right factor. Since `Γ` is the ring `A[u, u⁻¹, r, s, t]` over
`A` through `η_L`, this pushout is `Γ[u, u⁻¹, r, s, t]`, with left factor `algebraMap` and right
factor the coefficient extension of `η_R` (`ChangeRing.pushoutLift` is its universal property).
The **coproduct** `Δ : Γ → Γ ⊗_A Γ` classifies the composite `C₂ * C₁`; in coordinates
`Δu = u₁u₂`, `Δr = r₁ + u₁²r₂`, `Δs = s₁ + u₁s₂` and `Δt = t₁ + u₁³t₂ + s₁u₁²r₂`, where the
index `1` marks the left factor (the first arrow) and `2` the right factor (`coproduct_u`,
`coproduct_r`, `coproduct_s`, `coproduct_t`). The **conjugation** `c : Γ → Γ` classifies the
inverse `C⁻¹ : C • W → W`.

The general construction is the ring `ChangeRing B = B[u, u⁻¹, r, s, t]` over an arbitrary
commutative ring `B`, the coordinate ring of `Spec B × G` for the group scheme `G` of changes of
variables. Its homomorphisms classify pairs of a homomorphism out of `B` and a change of
variables (`ChangeRing.lift`); for `B = ℤ[a₁, ⋯, a₆]` it is `Γ`, and for `B = Γ` it is
`Γ ⊗_A Γ`, and the triple tensor product `Γ ⊗_A Γ ⊗_A Γ` is the case `B = Γ ⊗_A Γ`. For
`B = ℤ` it is the coordinate algebra `ℤ[u, r, s, t][u⁻¹]` of
`TauCeti.WeierstrassChange.Universal.CoordinateRing`.

Every equation is proved by comparing classified data: a ring homomorphism out of
`B[u, u⁻¹, r, s, t]` is determined by its restriction to `B` and by the change of variables it
classifies (`ChangeRing.ringHom_ext`), and each equation then becomes a groupoid law in the group
`WeierstrassCurve.VariableChange R` acting on Weierstrass curves. The statements and this proof
strategy follow those for the Hopf algebroid `(L, L[b₁, b₂, …])` of strict coordinate changes of
formal group laws in `TauCeti/RingTheory/FormalGroup/CoordinateChange/HopfAlgebroid.lean`.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.ChangeRing B`: the ring `B[u, u⁻¹, r, s, t]`, with its
  universal change of variables `ChangeRing.universalChange B` and the classification
  `ChangeRing.lift`.
* `TauCeti.WeierstrassHopfAlgebroid.ChangeRing.pushoutLift`: the universal property of
  `B'[u, u⁻¹, r, s, t] = B' ⊗_B B[u, u⁻¹, r, s, t]` as a pushout.
* `TauCeti.WeierstrassHopfAlgebroid.ArrowRing`: the ring `Γ = ℤ[a₁, ⋯, a₆][u, u⁻¹, r, s, t]`.
* `TauCeti.WeierstrassHopfAlgebroid.rightUnit`, `counit`, `coproduct`, `conjugation`: the
  structure maps `η_R`, `ε`, `Δ` and `c`.

## Main results

* `TauCeti.WeierstrassHopfAlgebroid.arrowEquiv`: homomorphisms `Γ →+* R` classify pairs of a
  Weierstrass curve and a change of variables over `R`; `map_comp_rightUnit` identifies the
  target classified by `η_R`.
* `counit_comp_algebraMap`, `counit_comp_rightUnit`: `ε η_L = id = ε η_R`.
* `coproduct_comp_algebraMap`, `coproduct_comp_rightUnit`: `Δ η_L = (η_L ⊗ 1) η_L` and
  `Δ η_R = (1 ⊗ η_R) η_R`.
* `pushoutLift_counit_id_comp_coproduct`, `pushoutLift_id_counit_comp_coproduct`: the counit
  laws `(ε ⊗ id) Δ = id = (id ⊗ ε) Δ`.
* `coproduct_coassoc`: coassociativity `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ`.
* `conjugation_comp_algebraMap`, `conjugation_comp_rightUnit`, `conjugation_comp_conjugation`,
  `counit_comp_conjugation`: `c η_L = η_R`, `c η_R = η_L`, `c c = id` and `ε c = ε`.
* `pushoutLift_conjugation_id_comp_coproduct`, `pushoutLift_id_conjugation_comp_coproduct`: the
  antipode equations `μ (c ⊗ id) Δ = η_R ε` and `μ (id ⊗ c) Δ = η_L ε`.
* `WeierstrassCurve.isIntegralModularForm_iff_rightUnit`: `f` is an integral modular form of
  weight `k` exactly when `η_R f = u⁻ᵏ η_L f`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3 (the Weierstrass Hopf algebroid).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.1
  (Hopf algebroids).
-/

public section

noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial WeierstrassCurve

variable {B B' R : Type*} [CommRing B] [CommRing B'] [CommRing R]

/-! ### The ring `B[u, u⁻¹, r, s, t]` -/

variable (B) in
/-- The ring `B[u, u⁻¹, r, s, t]`, the localization of `B[u, r, s, t]` away from `u`, with indices
`0, 1, 2, 3` for `u, r, s, t`. It is the coordinate ring of `Spec B × G`, for the group scheme `G`
of admissible changes of variables of Weierstrass curves. -/
abbrev ChangeRing : Type _ := Localization.Away (X 0 : MvPolynomial (Fin 4) B)

namespace ChangeRing

variable (B) in
/-- The universal change of variables `(u, r, s, t)` over `B[u, u⁻¹, r, s, t]`. -/
def universalChange : VariableChange (ChangeRing B) :=
  ⟨(IsLocalization.Away.algebraMap_isUnit (X 0 : MvPolynomial (Fin 4) B)).unit,
    algebraMap (MvPolynomial (Fin 4) B) _ (X 1), algebraMap (MvPolynomial (Fin 4) B) _ (X 2),
    algebraMap (MvPolynomial (Fin 4) B) _ (X 3)⟩

variable (B) in
@[simp]
theorem universalChange_u :
    ((universalChange B).u : ChangeRing B) = algebraMap (MvPolynomial (Fin 4) B) _ (X 0) :=
  IsUnit.unit_spec _

variable (B) in
@[simp]
theorem universalChange_r :
    (universalChange B).r = algebraMap (MvPolynomial (Fin 4) B) _ (X 1) :=
  (rfl)

variable (B) in
@[simp]
theorem universalChange_s :
    (universalChange B).s = algebraMap (MvPolynomial (Fin 4) B) _ (X 2) :=
  (rfl)

variable (B) in
@[simp]
theorem universalChange_t :
    (universalChange B).t = algebraMap (MvPolynomial (Fin 4) B) _ (X 3) :=
  (rfl)

/-- The homomorphism `B[u, r, s, t] →+* R` extending `f` and sending `u, r, s, t` to the
coefficients of `C`. -/
private def evalHom (f : B →+* R) (C : VariableChange R) : MvPolynomial (Fin 4) B →+* R :=
  eval₂Hom f ![(C.u : R), C.r, C.s, C.t]

private theorem isUnit_evalHom_X (f : B →+* R) (C : VariableChange R) :
    IsUnit (evalHom f C (X 0)) := by
  simp [evalHom]

/-- **Ring homomorphisms out of `B[u, u⁻¹, r, s, t]`** classify pairs of a ring homomorphism out
of `B` and a change of variables: a homomorphism `k` corresponds to its restriction to `B` and
to the base change of `universalChange B` along `k`. -/
def lift : (B →+* R) × VariableChange R ≃ (ChangeRing B →+* R) where
  toFun p := IsLocalization.Away.lift (X 0) (isUnit_evalHom_X p.1 p.2)
  invFun k := (k.comp (algebraMap B _), (universalChange B).map k)
  left_inv p := by
    refine Prod.ext (RingHom.ext fun b ↦ ?_) ?_
    · simp [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin 4) B) (ChangeRing B),
        evalHom]
    · ext <;> simp [evalHom]
  right_inv k := by
    refine IsLocalization.ringHom_ext (.powers (X 0 : MvPolynomial (Fin 4) B)) ?_
    refine MvPolynomial.ringHom_ext (fun b ↦ ?_) fun i ↦ ?_
    · simp [evalHom,
        IsScalarTower.algebraMap_apply B (MvPolynomial (Fin 4) B) (ChangeRing B)]
    · fin_cases i <;> simp [evalHom]

/-- `lift p` restricts to `p.1` on `B`. -/
@[simp]
theorem lift_comp_algebraMap (p : (B →+* R) × VariableChange R) :
    (lift p).comp (algebraMap B _) = p.1 :=
  congrArg Prod.fst (lift.left_inv p)

/-- `lift p` agrees with `p.1` on `B`. -/
@[simp]
theorem lift_algebraMap (p : (B →+* R) × VariableChange R) (b : B) :
    lift p (algebraMap B _ b) = p.1 b :=
  RingHom.congr_fun (lift_comp_algebraMap p) b

/-- `lift p` carries the universal change of variables to `p.2`. -/
@[simp]
theorem map_lift (p : (B →+* R) × VariableChange R) :
    (universalChange B).map (lift p) = p.2 :=
  congrArg Prod.snd (lift.left_inv p)

@[simp]
theorem lift_symm_apply (k : ChangeRing B →+* R) :
    lift.symm k = (k.comp (algebraMap B _), (universalChange B).map k) :=
  (rfl)

/-- A ring homomorphism out of `B[u, u⁻¹, r, s, t]` is determined by its restriction to `B` and
the change of variables it classifies. -/
theorem ringHom_ext {k k' : ChangeRing B →+* R}
    (h₁ : k.comp (algebraMap B _) = k'.comp (algebraMap B _))
    (h₂ : (universalChange B).map k = (universalChange B).map k') : k = k' :=
  lift.symm.injective (Prod.ext h₁ h₂)

/-! ### Coefficient extension and the pushout `B' ⊗_B B[u, u⁻¹, r, s, t]` -/

/-- The coefficient extension `B[u, u⁻¹, r, s, t] →+* B'[u, u⁻¹, r, s, t]` of `f : B →+* B'`. -/
def map (f : B →+* B') : ChangeRing B →+* ChangeRing B' :=
  lift ((algebraMap B' _).comp f, universalChange B')

@[simp]
theorem map_comp_algebraMap (f : B →+* B') :
    (map f).comp (algebraMap B _) = (algebraMap B' _).comp f :=
  lift_comp_algebraMap _

@[simp]
theorem map_algebraMap (f : B →+* B') (b : B) :
    map f (algebraMap B _ b) = algebraMap B' _ (f b) :=
  lift_algebraMap _ b

@[simp]
theorem universalChange_map_map (f : B →+* B') :
    (universalChange B).map (map f) = universalChange B' :=
  map_lift _

/-- **The universal property of `B'[u, u⁻¹, r, s, t]` as the pushout `B' ⊗_B B[u, u⁻¹, r, s, t]`**
of `f : B →+* B'` and the inclusion `algebraMap`: ring homomorphisms out of it correspond to
pairs `(g, h)` of ring homomorphisms out of `B'` and out of `B[u, u⁻¹, r, s, t]` with
`g ∘ f = h ∘ algebraMap`, by restriction along `algebraMap` and along `map f`. -/
def pushoutLift (f : B →+* B') :
    {p : (B' →+* R) × (ChangeRing B →+* R) // p.1.comp f = p.2.comp (algebraMap B _)} ≃
      (ChangeRing B' →+* R) where
  toFun p := lift (p.1.1, (universalChange B).map p.1.2)
  invFun k := ⟨(k.comp (algebraMap B' _), k.comp (map f)), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, map_comp_algebraMap]⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (lift_comp_algebraMap _) (ringHom_ext ?_ ?_))
    · rw [RingHom.comp_assoc, map_comp_algebraMap, ← RingHom.comp_assoc, lift_comp_algebraMap,
        p.2]
    · rw [← VariableChange.map_map, universalChange_map_map, map_lift]
  right_inv k := ringHom_ext (lift_comp_algebraMap _) (by
    rw [map_lift]
    dsimp only
    rw [← VariableChange.map_map, universalChange_map_map])

variable (f : B →+* B')
  (p : {p : (B' →+* R) × (ChangeRing B →+* R) // p.1.comp f = p.2.comp (algebraMap B _)})

/-- `pushoutLift f (g, h)` restricts to `g` along `algebraMap`. -/
@[simp]
theorem pushoutLift_comp_algebraMap : (pushoutLift f p).comp (algebraMap B' _) = p.1.1 :=
  congrArg (fun q ↦ q.1.1) ((pushoutLift f).left_inv p)

/-- `pushoutLift f (g, h)` restricts to `h` along `map f`. -/
@[simp]
theorem pushoutLift_comp_map : (pushoutLift f p).comp (map f) = p.1.2 :=
  congrArg (fun q ↦ q.1.2) ((pushoutLift f).left_inv p)

@[simp]
theorem pushoutLift_algebraMap (b : B') : pushoutLift f p (algebraMap B' _ b) = p.1.1 b :=
  RingHom.congr_fun (pushoutLift_comp_algebraMap f p) b

@[simp]
theorem pushoutLift_map (x : ChangeRing B) : pushoutLift f p (map f x) = p.1.2 x :=
  RingHom.congr_fun (pushoutLift_comp_map f p) x

/-- `pushoutLift f (g, h)` carries the universal change of variables over `B'` to the change
classified by `h`. -/
@[simp]
theorem universalChange_map_pushoutLift :
    (universalChange B').map (pushoutLift f p) = (universalChange B).map p.1.2 :=
  map_lift _

end ChangeRing

/-! ### The arrows of the Weierstrass Hopf algebroid -/

open ChangeRing

/-- The ring `Γ = ℤ[a₁, a₂, a₃, a₄, a₆][u, u⁻¹, r, s, t]` of arrows of the Weierstrass Hopf
algebroid. Its homomorphisms to `R` classify a Weierstrass curve `W` over `R`, the source, with
a change of variables `C` over `R` (`arrowEquiv`), the arrow `W → C • W`. -/
abbrev ArrowRing : Type := ChangeRing (MvPolynomial Coeff ℤ)

/-- The **right unit** `η_R : ℤ[a₁, ⋯, a₆] →+* Γ`, classifying the target `C • W` of the universal
arrow `W → C • W`; the left unit `η_L` is `algebraMap`, classifying its source `W`. -/
def rightUnit : MvPolynomial Coeff ℤ →+* ArrowRing :=
  (universalChange (MvPolynomial Coeff ℤ) •
    WeierstrassCurve.map Universal.curve (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)).specialize

/-- The right unit specializes the universal curve to the target `C • W` of the universal arrow:
its coefficients are given by Mathlib's `WeierstrassCurve.variableChange_def`. -/
@[simp]
theorem map_rightUnit :
    WeierstrassCurve.map Universal.curve rightUnit =
      universalChange (MvPolynomial Coeff ℤ) •
        WeierstrassCurve.map Universal.curve (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) :=
  map_specialize _

/-- If `k : Γ →+* R` classifies the arrow `W → C • W`, then `k ∘ η_R` classifies its target
`C • W`. -/
theorem map_comp_rightUnit (k : ArrowRing →+* R) :
    WeierstrassCurve.map Universal.curve (k.comp rightUnit) =
      (universalChange (MvPolynomial Coeff ℤ)).map k •
        WeierstrassCurve.map Universal.curve (k.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing))
      := by
  rw [← WeierstrassCurve.map_map, map_rightUnit, ← map_variableChange, WeierstrassCurve.map_map]

/-- Equivalently to `map_comp_rightUnit`, `k ∘ η_R` is the specialization at the target of the
arrow classified by `k`. -/
theorem comp_rightUnit (k : ArrowRing →+* R) :
    k.comp rightUnit =
      ((universalChange (MvPolynomial Coeff ℤ)).map k •
        WeierstrassCurve.map Universal.curve
          (k.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing))).specialize := by
  rw [← map_comp_rightUnit, specialize_map, Universal.specialize_curve, RingHom.comp_id]

variable (R) in
/-- **Homomorphisms out of `Γ` classify arrows**: `k : Γ →+* R` corresponds to the pair of the
source curve `W` and the change of variables `C` of the arrow `W → C • W` it classifies. -/
def arrowEquiv : (ArrowRing →+* R) ≃ WeierstrassCurve R × VariableChange R where
  toFun k := (WeierstrassCurve.map Universal.curve (k.comp (algebraMap _ ArrowRing)),
    (universalChange (MvPolynomial Coeff ℤ)).map k)
  invFun p := lift (p.1.specialize, p.2)
  left_inv k := ChangeRing.ringHom_ext (by simp) (by simp)
  right_inv p := by simp

@[simp]
theorem arrowEquiv_apply (k : ArrowRing →+* R) :
    arrowEquiv R k =
      (WeierstrassCurve.map Universal.curve (k.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)),
        (universalChange (MvPolynomial Coeff ℤ)).map k) :=
  (rfl)

@[simp]
theorem arrowEquiv_symm_apply (p : WeierstrassCurve R × VariableChange R) :
    (arrowEquiv R).symm p = lift (p.1.specialize, p.2) :=
  (rfl)

/-! ### The counit -/

/-- The **counit** `ε : Γ →+* ℤ[a₁, ⋯, a₆]`, classifying the identity arrows. -/
def counit : ArrowRing →+* MvPolynomial Coeff ℤ :=
  lift (RingHom.id _, 1)

/-- `ε η_L = id`: the source of an identity arrow `W → W` is `W`. -/
@[simp]
theorem counit_comp_algebraMap :
    counit.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) = RingHom.id _ :=
  lift_comp_algebraMap _

/-- The counit classifies the identity change of variables. -/
@[simp]
theorem universalChange_map_counit : (universalChange (MvPolynomial Coeff ℤ)).map counit = 1 :=
  map_lift _

/-- `ε η_R = id`: the target of an identity arrow `W → W` is `W`. -/
@[simp]
theorem counit_comp_rightUnit : counit.comp rightUnit = RingHom.id _ :=
  Universal.map_curve_injective (by simp [map_comp_rightUnit])

/-! ### The coproduct -/

/-- The **coproduct** `Δ : Γ →+* Γ ⊗_A Γ = Γ[u, u⁻¹, r, s, t]`, classifying the composite
`C₂ * C₁` of the universal composable pair `W → C₁ • W → C₂ • (C₁ • W)`: `W` and `C₁` come from
the left factor `algebraMap` and `C₂` from the right factor `map η_R`. -/
def coproduct : ArrowRing →+* ChangeRing ArrowRing :=
  lift ((algebraMap ArrowRing _).comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing),
    universalChange ArrowRing *
      (universalChange (MvPolynomial Coeff ℤ)).map (algebraMap ArrowRing _))

/-- `Δ η_L = (η_L ⊗ 1) η_L`: the source of a composite is the source of its first factor. -/
@[simp]
theorem coproduct_comp_algebraMap :
    coproduct.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) =
      (algebraMap ArrowRing _).comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) :=
  lift_comp_algebraMap _

/-- The coproduct sends the universal change of variables to the composite `C₂ * C₁` of the
universal changes `C₁` of the left factor and `C₂` of the right factor. -/
@[simp]
theorem universalChange_map_coproduct :
    (universalChange (MvPolynomial Coeff ℤ)).map coproduct =
      universalChange ArrowRing *
        (universalChange (MvPolynomial Coeff ℤ)).map (algebraMap ArrowRing _) :=
  map_lift _

/-- `Δ η_R = (1 ⊗ η_R) η_R`: the target of a composite is the target of its second factor. -/
@[simp]
theorem coproduct_comp_rightUnit :
    coproduct.comp rightUnit = (ChangeRing.map rightUnit).comp rightUnit := by
  refine Universal.map_curve_injective ?_
  -- Beta-reduce the goal produced by `Function.Injective`.
  dsimp only
  rw [map_comp_rightUnit, map_comp_rightUnit, universalChange_map_coproduct,
    coproduct_comp_algebraMap, universalChange_map_map, map_comp_algebraMap,
    ← WeierstrassCurve.map_map _ rightUnit, map_rightUnit, ← map_variableChange,
    WeierstrassCurve.map_map, mul_smul]

/-- The coproduct agrees with the left factor on `ℤ[a₁, ⋯, a₆]`. -/
@[simp]
theorem coproduct_algebraMap (a : MvPolynomial Coeff ℤ) :
    coproduct (algebraMap (MvPolynomial Coeff ℤ) ArrowRing a) =
      algebraMap ArrowRing _ (algebraMap (MvPolynomial Coeff ℤ) ArrowRing a) :=
  RingHom.congr_fun coproduct_comp_algebraMap a

/-- The coproduct agrees with the right factor on the image of the right unit. -/
@[simp]
theorem coproduct_rightUnit (a : MvPolynomial Coeff ℤ) :
    coproduct (rightUnit a) = ChangeRing.map rightUnit (rightUnit a) :=
  RingHom.congr_fun coproduct_comp_rightUnit a

/-! The coproduct in coordinates. Write `u, r, s, t` for the coefficients of the universal change
of variables over `Γ`, `u₁, r₁, s₁, t₁` for their images under the left factor `algebraMap` and
`u₂, r₂, s₂, t₂` for their images under the right factor `map η_R`. -/

/-- `Δu = u₁u₂`. -/
theorem coproduct_u :
    coproduct (universalChange (MvPolynomial Coeff ℤ)).u =
      algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).u *
        ChangeRing.map rightUnit (universalChange (MvPolynomial Coeff ℤ)).u := by
  have h := congrArg (fun C ↦ (C.u : ChangeRing ArrowRing)) universalChange_map_coproduct
  have h₂ := congrArg (fun C ↦ (C.u : ChangeRing ArrowRing)) (universalChange_map_map rightUnit)
  simp only [VariableChange.map_u, Units.coe_map, MonoidHom.coe_ofClass, VariableChange.mul_def,
    Units.val_mul] at h h₂
  rw [h, ← h₂, mul_comm]

/-- `Δr = r₁ + u₁²r₂`. -/
theorem coproduct_r :
    coproduct (universalChange (MvPolynomial Coeff ℤ)).r =
      algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).r +
        algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).u ^ 2 *
          ChangeRing.map rightUnit (universalChange (MvPolynomial Coeff ℤ)).r := by
  have h := congrArg VariableChange.r universalChange_map_coproduct
  have hu := congrArg (fun C ↦ (C.u : ChangeRing ArrowRing)) (universalChange_map_map rightUnit)
  have hr := congrArg VariableChange.r (universalChange_map_map rightUnit)
  simp only [VariableChange.map_r, VariableChange.map_u, Units.coe_map, MonoidHom.coe_ofClass,
    VariableChange.mul_def] at h hu hr
  rw [h, ← hr]
  ring

/-- `Δs = s₁ + u₁s₂`. -/
theorem coproduct_s :
    coproduct (universalChange (MvPolynomial Coeff ℤ)).s =
      algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).s +
        algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).u *
          ChangeRing.map rightUnit (universalChange (MvPolynomial Coeff ℤ)).s := by
  have h := congrArg VariableChange.s universalChange_map_coproduct
  have hs := congrArg VariableChange.s (universalChange_map_map rightUnit)
  simp only [VariableChange.map_s, VariableChange.map_u, Units.coe_map, MonoidHom.coe_ofClass,
    VariableChange.mul_def] at h hs
  rw [h, ← hs]
  ring

/-- `Δt = t₁ + u₁³t₂ + s₁u₁²r₂`. -/
theorem coproduct_t :
    coproduct (universalChange (MvPolynomial Coeff ℤ)).t =
      algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).t +
        algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).u ^ 3 *
          ChangeRing.map rightUnit (universalChange (MvPolynomial Coeff ℤ)).t +
        algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).s *
          algebraMap ArrowRing _ (universalChange (MvPolynomial Coeff ℤ)).u ^ 2 *
            ChangeRing.map rightUnit (universalChange (MvPolynomial Coeff ℤ)).r := by
  have h := congrArg VariableChange.t universalChange_map_coproduct
  have hr := congrArg VariableChange.r (universalChange_map_map rightUnit)
  have ht := congrArg VariableChange.t (universalChange_map_map rightUnit)
  simp only [VariableChange.map_r, VariableChange.map_t, VariableChange.map_s,
    VariableChange.map_u, Units.coe_map, MonoidHom.coe_ofClass, VariableChange.mul_def] at h hr ht
  rw [h, ← hr, ← ht]
  ring

/-- If `k : Γ ⊗_A Γ →+* R` classifies the composable pair `W → C₁ • W → C₂ • (C₁ • W)`, then
`k ∘ Δ` classifies the composite `C₂ * C₁`. -/
theorem universalChange_map_comp_coproduct (k : ChangeRing ArrowRing →+* R) :
    (universalChange (MvPolynomial Coeff ℤ)).map (k.comp coproduct) =
      (universalChange (MvPolynomial Coeff ℤ)).map (k.comp (ChangeRing.map rightUnit)) *
        (universalChange (MvPolynomial Coeff ℤ)).map (k.comp (algebraMap ArrowRing _)) := by
  rw [← VariableChange.map_map, universalChange_map_coproduct, VariableChange.map_mul,
    VariableChange.map_map, ← VariableChange.map_map _ (ChangeRing.map rightUnit),
    universalChange_map_map]

/-- The source of the composite classified by `k ∘ Δ` is the source classified by the left
factor of `k`. -/
theorem comp_coproduct_comp_algebraMap (k : ChangeRing ArrowRing →+* R) :
    (k.comp coproduct).comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) =
      (k.comp (algebraMap ArrowRing _)).comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) := by
  rw [RingHom.comp_assoc, coproduct_comp_algebraMap, RingHom.comp_assoc]

/-- **The left counit law** `(ε ⊗ id) Δ = id`: composing with an identity on the left does
nothing. Here `ε ⊗ id` is `pushoutLift (η_L ε, id)`. -/
theorem pushoutLift_counit_id_comp_coproduct :
    (pushoutLift rightUnit
        ⟨((algebraMap (MvPolynomial Coeff ℤ) ArrowRing).comp counit, RingHom.id _), by
          rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          coproduct =
      RingHom.id ArrowRing := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [comp_coproduct_comp_algebraMap, pushoutLift_comp_algebraMap, RingHom.comp_assoc,
      counit_comp_algebraMap, RingHom.comp_id, RingHom.id_comp]
  · rw [universalChange_map_comp_coproduct, pushoutLift_comp_map, pushoutLift_comp_algebraMap,
      ← VariableChange.map_map, universalChange_map_counit, VariableChange.map_one, mul_one]

/-- **The right counit law** `(id ⊗ ε) Δ = id`: composing with an identity on the right does
nothing. Here `id ⊗ ε` is `pushoutLift (id, η_R ε)`. -/
theorem pushoutLift_id_counit_comp_coproduct :
    (pushoutLift rightUnit
        ⟨(RingHom.id ArrowRing, rightUnit.comp counit), by
          rw [RingHom.comp_assoc, counit_comp_algebraMap, RingHom.comp_id, RingHom.id_comp]⟩).comp
          coproduct =
      RingHom.id ArrowRing := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [comp_coproduct_comp_algebraMap, pushoutLift_comp_algebraMap, RingHom.id_comp]
  · rw [universalChange_map_comp_coproduct, pushoutLift_comp_map, pushoutLift_comp_algebraMap,
      ← VariableChange.map_map, universalChange_map_counit, VariableChange.map_one, one_mul]

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ` of the coproduct: composition of changes of
variables is associative. Both sides take values in the triple tensor product
`Γ ⊗_A Γ ⊗_A Γ = (Γ ⊗_A Γ)[u, u⁻¹, r, s, t]`, the pushout of `Γ ⊗_A Γ` along the target
`ρ = map η_R ∘ η_R` of its universal composable pair and of `Γ` along `η_L`. In it, `Δ ⊗ id` is
`pushoutLift (algebraMap ∘ Δ, map ρ)`, and `id ⊗ Δ` is `pushoutLift (algebraMap ∘ algebraMap,
map (map η_R) ∘ Δ)`, where `map (map η_R)` is the inclusion of the last two factors. -/
theorem coproduct_coassoc :
    (pushoutLift rightUnit
        ⟨((algebraMap (ChangeRing ArrowRing) _).comp coproduct,
          ChangeRing.map ((ChangeRing.map rightUnit).comp rightUnit)), by
          dsimp only
          rw [RingHom.comp_assoc, coproduct_comp_rightUnit, map_comp_algebraMap]⟩).comp
        coproduct =
      (pushoutLift rightUnit
        ⟨((algebraMap (ChangeRing ArrowRing) _).comp (algebraMap ArrowRing _),
          (ChangeRing.map (ChangeRing.map rightUnit)).comp coproduct),
          RingHom.ext fun x ↦ by
            simp only [RingHom.comp_apply, coproduct_algebraMap, map_algebraMap]⟩).comp
        coproduct := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · exact RingHom.ext fun x ↦ by
      simp only [RingHom.comp_apply, coproduct_algebraMap, pushoutLift_algebraMap]
  · -- Both sides are the triple composite `C₃ * C₂ * C₁` of the changes of variables of the
    -- three factors.
    simp only [universalChange_map_comp_coproduct, pushoutLift_comp_map,
      pushoutLift_comp_algebraMap]
    simp only [map_comp_algebraMap, ← VariableChange.map_map, universalChange_map_map, mul_assoc]

/-! ### The conjugation -/

/-- The **conjugation** `c : Γ →+* Γ`, classifying the inverse `C⁻¹ : C • W → W` of the universal
arrow `W → C • W`. -/
def conjugation : ArrowRing →+* ArrowRing :=
  lift (rightUnit, (universalChange (MvPolynomial Coeff ℤ))⁻¹)

/-- `c η_L = η_R`: the source of the inverse is the target. -/
@[simp]
theorem conjugation_comp_algebraMap :
    conjugation.comp (algebraMap (MvPolynomial Coeff ℤ) ArrowRing) = rightUnit :=
  lift_comp_algebraMap _

/-- The conjugation agrees with the right unit on `ℤ[a₁, ⋯, a₆]`. -/
@[simp]
theorem conjugation_algebraMap (a : MvPolynomial Coeff ℤ) :
    conjugation (algebraMap (MvPolynomial Coeff ℤ) ArrowRing a) = rightUnit a :=
  lift_algebraMap _ a

/-- The conjugation sends the universal change of variables to its inverse. -/
@[simp]
theorem universalChange_map_conjugation :
    (universalChange (MvPolynomial Coeff ℤ)).map conjugation =
      (universalChange (MvPolynomial Coeff ℤ))⁻¹ :=
  map_lift _

/-- `c η_R = η_L`: the target of the inverse is the source. -/
@[simp]
theorem conjugation_comp_rightUnit :
    conjugation.comp rightUnit = algebraMap (MvPolynomial Coeff ℤ) ArrowRing :=
  Universal.map_curve_injective (by
    -- Beta-reduce the goal produced by `Function.Injective`.
    dsimp only
    rw [map_comp_rightUnit, universalChange_map_conjugation, conjugation_comp_algebraMap,
      map_rightUnit, inv_smul_smul])

/-- The conjugation agrees with the left unit on the image of the right unit. -/
@[simp]
theorem conjugation_rightUnit (a : MvPolynomial Coeff ℤ) :
    conjugation (rightUnit a) = algebraMap (MvPolynomial Coeff ℤ) ArrowRing a :=
  RingHom.congr_fun conjugation_comp_rightUnit a

/-- `c c = id`: the inverse of the inverse is the original arrow. -/
@[simp]
theorem conjugation_comp_conjugation : conjugation.comp conjugation = RingHom.id ArrowRing := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_algebraMap, conjugation_comp_rightUnit,
      RingHom.id_comp]
  · rw [← VariableChange.map_map, universalChange_map_conjugation, VariableChange.map_inv,
      universalChange_map_conjugation, inv_inv, VariableChange.map_id]

/-- The conjugation is an involution. -/
@[simp]
theorem conjugation_conjugation (x : ArrowRing) : conjugation (conjugation x) = x :=
  RingHom.congr_fun conjugation_comp_conjugation x

/-- `ε c = ε`: the inverse of an identity arrow is an identity arrow. -/
@[simp]
theorem counit_comp_conjugation : counit.comp conjugation = counit := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_algebraMap, counit_comp_rightUnit,
      counit_comp_algebraMap]
  · rw [← VariableChange.map_map, universalChange_map_conjugation, VariableChange.map_inv,
      universalChange_map_counit, inv_one]

/-- The counit is invariant under the conjugation. -/
@[simp]
theorem counit_conjugation (x : ArrowRing) : counit (conjugation x) = counit x :=
  RingHom.congr_fun counit_comp_conjugation x

/-- **The left antipode equation** `μ (c ⊗ id) Δ = η_R ε`: composing the inverse of an arrow with
it gives the identity of its target. Here `μ (c ⊗ id)` is `pushoutLift (c, id)`. -/
theorem pushoutLift_conjugation_id_comp_coproduct :
    (pushoutLift rightUnit ⟨(conjugation, RingHom.id ArrowRing), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp coproduct =
      rightUnit.comp counit := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [comp_coproduct_comp_algebraMap, pushoutLift_comp_algebraMap, conjugation_comp_algebraMap,
      RingHom.comp_assoc, counit_comp_algebraMap, RingHom.comp_id]
  · rw [universalChange_map_comp_coproduct, pushoutLift_comp_map, pushoutLift_comp_algebraMap,
      universalChange_map_conjugation, VariableChange.map_id, mul_inv_cancel,
      ← VariableChange.map_map, universalChange_map_counit, VariableChange.map_one]

/-- **The right antipode equation** `μ (id ⊗ c) Δ = η_L ε`: composing an arrow with its inverse
gives the identity of its source. Here `μ (id ⊗ c)` is `pushoutLift (id, c)`. -/
theorem pushoutLift_id_conjugation_comp_coproduct :
    (pushoutLift rightUnit ⟨(RingHom.id ArrowRing, conjugation), by
        rw [conjugation_comp_algebraMap, RingHom.id_comp]⟩).comp coproduct =
      (algebraMap (MvPolynomial Coeff ℤ) ArrowRing).comp counit := by
  refine ChangeRing.ringHom_ext ?_ ?_
  · rw [comp_coproduct_comp_algebraMap, pushoutLift_comp_algebraMap, RingHom.id_comp,
      RingHom.comp_assoc, counit_comp_algebraMap, RingHom.comp_id]
  · rw [universalChange_map_comp_coproduct, pushoutLift_comp_map, pushoutLift_comp_algebraMap,
      universalChange_map_conjugation, VariableChange.map_id, inv_mul_cancel,
      ← VariableChange.map_map, universalChange_map_counit, VariableChange.map_one]

end TauCeti.WeierstrassHopfAlgebroid

/-! ### Integral modular forms as invariants -/

namespace WeierstrassCurve

open TauCeti.WeierstrassHopfAlgebroid ChangeRing

/-- **Integral modular forms are the invariants of the Weierstrass Hopf algebroid**: `f` is an
integral modular form of weight `k` exactly when `η_R f = u⁻ᵏ η_L f` in `Γ`. -/
theorem isIntegralModularForm_iff_rightUnit {k : ℕ} {f : MvPolynomial Coeff ℤ} :
    IsIntegralModularForm k f ↔
      rightUnit f = ↑(universalChange (MvPolynomial Coeff ℤ)).u⁻¹ ^ k *
        algebraMap (MvPolynomial Coeff ℤ) ArrowRing f := by
  have hη : rightUnit = (universalChange (MvPolynomial Coeff ℤ) •
      WeierstrassCurve.map Universal.curve (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)).specialize
      := by
    simpa using comp_rightUnit (RingHom.id ArrowRing)
  refine ⟨fun hf ↦ ?_, fun h ↦ isIntegralModularForm_def.2 fun R _ W C ↦ ?_⟩
  · rw [hη, hf.specialize_smul, specialize_map, Universal.specialize_curve, RingHom.comp_id]
  · -- Specialize the identity in `Γ` along the homomorphism classifying the arrow `W → C • W`.
    have hk := congrArg (lift (W.specialize, C)) h
    have hu := congrArg (fun C : VariableChange R ↦ ((C.u⁻¹ : Rˣ) : R)) (map_lift (W.specialize, C))
    rw [← RingHom.comp_apply, comp_rightUnit] at hk
    simp only [VariableChange.map_u, Units.coe_map_inv, MonoidHom.coe_ofClass] at hu
    simpa [hu] using hk

end WeierstrassCurve
