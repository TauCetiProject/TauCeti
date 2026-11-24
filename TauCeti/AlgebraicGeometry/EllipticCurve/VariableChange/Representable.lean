/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.SemidirectProduct
import Mathlib.Algebra.CharP.Algebra

/-!
# The coordinate algebra of Weierstrass changes of variables

Over an arbitrary commutative coefficient ring `B`, the ring `ChangeRing B = B[u, u⁻¹, r, s, t]`
is the coordinate ring of `Spec B × G` for the group scheme `G` of changes of variables: its
homomorphisms classify pairs of a homomorphism out of `B` and a change of variables
(`ChangeRing.lift`, with universal change `ChangeRing.universalChange B`). The coefficient
extension `ChangeRing.map` is functorial (`ChangeRing.map_id`, `ChangeRing.map_comp`), and
`ChangeRing.pushoutLift` is the universal property of
`B'[u, u⁻¹, r, s, t] = B' ⊗_B B[u, u⁻¹, r, s, t]` as a pushout. For `B = ℤ[a₁, ⋯, a₆]` it is the
ring of arrows of the Weierstrass Hopf algebroid. Similarly, the polynomial ring
`StrictChangeRing B = B[r, s, t]` classifies strict changes `(1, r, s, t)` (`StrictChangeRing.lift`,
`StrictChangeRing.fromChangeRing`).

For `B = ℤ` it is the coordinate algebra `Universal.CoordinateRing = ℤ[u,r,s,t][u⁻¹]`, which
corepresents the group-valued functor `R ↦ WeierstrassCurve.VariableChange R`. The equivalence
here uses the native change of variables, including over rings with nilpotents and the zero ring;
it is not a classification on field points. This supplies the coordinate algebra for the group
acting on Weierstrass equations.

`WeierstrassCurve.VariableChange.specialize` classifies a change of variables, and
`ChangeRing.universalChange ℤ` is the universal one. Their two inverse laws, together with
naturality, give `pointsCorepresentableBy`.
The functor takes values in groups using Mathlib's `VariableChange.mapHom`, so its product
is the native, noncommutative product, not addition on three translation coordinates.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the
  Weierstrass coordinate-change group. The native multiplication convention is retained here.
-/

public section

noncomputable section

universe u

open WeierstrassCurve WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

open MvPolynomial

variable {B B' R : Type*} [CommRing B] [CommRing B'] [CommRing R]

/-! ### The ring `B[u, u⁻¹, r, s, t]` -/

variable (B) in
/-- The ring `B[u, u⁻¹, r, s, t]`, the localization of `B[u, r, s, t]` away from `u`, with indices
`0, 1, 2, 3` for `u, r, s, t`. It is the coordinate ring of `Spec B × G`, for the group scheme `G`
of admissible changes of variables of Weierstrass curves. -/
abbrev ChangeRing : Type _ := Localization.Away (X 0 : MvPolynomial (Fin 4) B)

namespace ChangeRing

/-- `B[u, u⁻¹, r, s, t]` is a domain when `B` is. -/
instance isDomain [IsDomain B] : IsDomain (ChangeRing B) :=
  Localization.Away.isDomain (X_ne_zero 0)

/-- The localization map `B[u, r, s, t] → B[u, u⁻¹, r, s, t]` is injective, since `u` is not a
zero divisor. -/
instance faithfulSMul_mvPolynomial : FaithfulSMul (MvPolynomial (Fin 4) B) (ChangeRing B) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <|
    IsLocalization.injective _ (Submonoid.powers_le.2 (isRegular_X (n := 0)).mem_nonZeroDivisors)

/-- The coefficient map `B → B[u, u⁻¹, r, s, t]` is injective. -/
instance faithfulSMul : FaithfulSMul B (ChangeRing B) :=
  .trans B (MvPolynomial (Fin 4) B) (ChangeRing B)

/-- `B[u, u⁻¹, r, s, t]` has characteristic `p` when `B` has. -/
instance charP (p : ℕ) [CharP B p] : CharP (ChangeRing B) p :=
  charP_of_injective_algebraMap' B p

/-- `B[u, u⁻¹, r, s, t]` has characteristic zero when `B` has. -/
instance charZero [CharZero B] : CharZero (ChangeRing B) :=
  CharP.charP_to_charZero (ChangeRing B)

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

/-- `lift p` sends the coordinates `u, r, s, t` to the coefficients of `p.2`. -/
@[simp]
theorem lift_algebraMap_X (p : (B →+* R) × VariableChange R) (i : Fin 4) :
    lift p (algebraMap (MvPolynomial (Fin 4) B) _ (X i)) =
      ![(p.2.u : R), p.2.r, p.2.s, p.2.t] i := by
  simp [lift, evalHom, IsLocalization.Away.lift_eq]

/-- `lift p` sends the inverse of the scaling coordinate `u` to the inverse of `p.2.u`. -/
@[simp]
theorem lift_universalChange_u_inv (p : (B →+* R) × VariableChange R) :
    lift p ((universalChange B).u⁻¹ : (ChangeRing B)ˣ) = ((p.2.u⁻¹ : Rˣ) : R) :=
  congrArg (fun C : VariableChange R ↦ ((C.u⁻¹ : Rˣ) : R)) (map_lift p)

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

/-- Coefficient extension fixes the coordinates `u, r, s, t`. -/
@[simp]
theorem map_algebraMap_X (f : B →+* B') (i : Fin 4) :
    map f (algebraMap (MvPolynomial (Fin 4) B) _ (X i)) =
      algebraMap (MvPolynomial (Fin 4) B') _ (X i) := by
  fin_cases i <;> simp [map]

variable (B) in
/-- Coefficient extension along the identity is the identity. -/
@[simp]
theorem map_id : map (RingHom.id B) = RingHom.id (ChangeRing B) :=
  ringHom_ext (by simp) (by simp)

/-- Coefficient extension is compatible with composition. -/
@[simp]
theorem map_comp {B'' : Type*} [CommRing B''] (g : B' →+* B'') (f : B →+* B') :
    map (g.comp f) = (map g).comp (map f) :=
  ringHom_ext (RingHom.ext fun b ↦ by simp) (by simp [← VariableChange.map_map])

/-- **The universal property of `B'[u, u⁻¹, r, s, t]` as the pushout `B' ⊗_B B[u, u⁻¹, r, s, t]`**
of `f : B →+* B'` and the inclusion `algebraMap`: ring homomorphisms out of it correspond to
pairs `(g, h)` of ring homomorphisms out of `B'` and out of `B[u, u⁻¹, r, s, t]` with
`g ∘ f = h ∘ algebraMap`, by restriction along `algebraMap` and along `map f`. -/
def pushoutLift (f : B →+* B') :
    {p : (B' →+* R) × (ChangeRing B →+* R) // p.1.comp f = p.2.comp (algebraMap B _)} ≃
      (ChangeRing B' →+* R) where
  toFun p := lift (p.val.1, (universalChange B).map p.val.2)
  invFun k := ⟨(k.comp (algebraMap B' _), k.comp (map f)), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, map_comp_algebraMap]⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (lift_comp_algebraMap _) (ringHom_ext ?_ ?_))
    · rw [RingHom.comp_assoc, map_comp_algebraMap, ← RingHom.comp_assoc, lift_comp_algebraMap,
        p.property]
    · rw [← VariableChange.map_map, universalChange_map_map, map_lift]
  right_inv k := ringHom_ext (lift_comp_algebraMap _) (by
    rw [map_lift]
    dsimp only
    rw [← VariableChange.map_map, universalChange_map_map])

/-- The first component of the pair classified by `k : B'[u, u⁻¹, r, s, t] →+* R` is its
restriction along `algebraMap`. -/
@[simp]
theorem pushoutLift_symm_apply_fst (f : B →+* B') (k : ChangeRing B' →+* R) :
    ((pushoutLift f).symm k).val.1 = k.comp (algebraMap B' _) :=
  (rfl)

/-- The second component of the pair classified by `k : B'[u, u⁻¹, r, s, t] →+* R` is its
restriction along `map f`. -/
@[simp]
theorem pushoutLift_symm_apply_snd (f : B →+* B') (k : ChangeRing B' →+* R) :
    ((pushoutLift f).symm k).val.2 = k.comp (map f) :=
  (rfl)

variable (f : B →+* B')
  (p : {p : (B' →+* R) × (ChangeRing B →+* R) // p.1.comp f = p.2.comp (algebraMap B _)})

/-- `pushoutLift f (g, h)` restricts to `g` along `algebraMap`. -/
@[simp]
theorem pushoutLift_comp_algebraMap : (pushoutLift f p).comp (algebraMap B' _) = p.val.1 :=
  congrArg (fun q ↦ q.val.1) ((pushoutLift f).left_inv p)

/-- `pushoutLift f (g, h)` restricts to `h` along `map f`. -/
@[simp]
theorem pushoutLift_comp_map : (pushoutLift f p).comp (map f) = p.val.2 :=
  congrArg (fun q ↦ q.val.2) ((pushoutLift f).left_inv p)

@[simp]
theorem pushoutLift_algebraMap (b : B') : pushoutLift f p (algebraMap B' _ b) = p.val.1 b :=
  RingHom.congr_fun (pushoutLift_comp_algebraMap f p) b

@[simp]
theorem pushoutLift_map (x : ChangeRing B) : pushoutLift f p (map f x) = p.val.2 x :=
  RingHom.congr_fun (pushoutLift_comp_map f p) x

/-- `pushoutLift f (g, h)` carries the universal change of variables over `B'` to the change
classified by `h`. -/
@[simp]
theorem universalChange_map_pushoutLift :
    (universalChange B').map (pushoutLift f p) = (universalChange B).map p.val.2 :=
  map_lift _

open CategoryTheory CategoryTheory.Limits in
/-- The coefficient-extension square is a pushout in the category of commutative rings.
This is the categorical form of `pushoutLift`, with no flatness assumption. -/
theorem isPushout {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') :
    CategoryTheory.IsPushout (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap B (ChangeRing B)))
      (CommRingCat.ofHom (algebraMap B' (ChangeRing B')))
      (CommRingCat.ofHom (map f)) := by
  have comm : CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap B' (ChangeRing B')) =
      CommRingCat.ofHom (algebraMap B (ChangeRing B)) ≫ CommRingCat.ofHom (map f) := by
    exact congrArg CommRingCat.ofHom (map_comp_algebraMap f).symm
  let desc (s : PushoutCocone (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap B (ChangeRing B)))) :=
    CommRingCat.ofHom (pushoutLift f ⟨(s.inl.hom, s.inr.hom),
      congrArg CommRingCat.Hom.hom s.condition⟩)
  refine ⟨⟨comm⟩, ⟨PushoutCocone.IsColimit.mk comm desc ?_ ?_ ?_⟩⟩
  · intro s
    exact congrArg CommRingCat.ofHom (pushoutLift_comp_algebraMap f _)
  · intro s
    exact congrArg CommRingCat.ofHom (pushoutLift_comp_map f _)
  · intro s m hm hn
    apply CommRingCat.hom_ext
    apply (pushoutLift f).symm.injective
    apply Subtype.ext
    apply Prod.ext
    · simpa only [pushoutLift_symm_apply_fst, desc, CommRingCat.hom_ofHom, CommRingCat.hom_comp,
        pushoutLift_comp_algebraMap] using congrArg CommRingCat.Hom.hom hm
    · simpa only [pushoutLift_symm_apply_snd, desc, CommRingCat.hom_ofHom, CommRingCat.hom_comp,
        pushoutLift_comp_map] using congrArg CommRingCat.Hom.hom hn

end ChangeRing

/-! ### The ring `B[r, s, t]` of strict Weierstrass coordinate changes -/

variable (B) in
/-- The polynomial ring `B[r, s, t] = MvPolynomial (Fin 3) B` classifying strict Weierstrass
changes `(1, r, s, t)` over `B`-algebras. -/
abbrev StrictChangeRing : Type _ := MvPolynomial (Fin 3) B

namespace StrictChangeRing

section
variable (B)

/-- The universal Heisenberg element `(r, s, t) = (X 0, X 1, X 2)` over `B[r, s, t]`. -/
def universalHeisenberg : HeisenbergGroup (StrictChangeRing B) := ⟨X 0, X 1, X 2⟩
@[simp] theorem universalHeisenberg_x : (universalHeisenberg B).x = X 0 := (rfl)
@[simp] theorem universalHeisenberg_y : (universalHeisenberg B).y = X 1 := (rfl)
@[simp] theorem universalHeisenberg_z : (universalHeisenberg B).z = X 2 := (rfl)

/-- The universal strict change of variables `(1, r, s, t)` over `B[r, s, t]`. -/
def universalChange : VariableChange (StrictChangeRing B) :=
  heisenbergHom (StrictChangeRing B) (universalHeisenberg B)
theorem universalChange_eq_heisenbergHom :
    universalChange B = heisenbergHom (StrictChangeRing B) (universalHeisenberg B) := (rfl)
@[simp] theorem universalChange_u : (universalChange B).u = 1 := by simp [universalChange]
@[simp] theorem universalChange_r : (universalChange B).r = X 0 := by simp [universalChange]
@[simp] theorem universalChange_s : (universalChange B).s = X 1 := by simp [universalChange]
@[simp] theorem universalChange_t : (universalChange B).t = X 2 := by simp [universalChange]
end

/-- **Ring homomorphisms out of `B[r, s, t]`** classify pairs of a ring homomorphism out of `B`
and an element of `HeisenbergGroup R`, i.e. a strict change of variables `(1, r, s, t)` over `R`. -/
def lift : (B →+* R) × HeisenbergGroup R ≃ (StrictChangeRing B →+* R) where
  toFun p := eval₂Hom p.1 ![p.2.x, p.2.y, p.2.z]
  invFun k := (k.comp C, HeisenbergGroup.map k (universalHeisenberg B))
  left_inv p := Prod.ext (RingHom.ext fun _ ↦ by simp) (by ext <;> simp)
  right_inv _ := MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by
    fin_cases i <;> simp
@[simp] theorem lift_comp_C (p : (B →+* R) × HeisenbergGroup R) : (lift p).comp C = p.1 :=
  congrArg Prod.fst (lift.left_inv p)
@[simp] theorem lift_C (p : (B →+* R) × HeisenbergGroup R) (b : B) : lift p (C b) = p.1 b :=
  RingHom.congr_fun (lift_comp_C p) b
@[simp] theorem lift_X (p : (B →+* R) × HeisenbergGroup R) (i : Fin 3) :
    lift p (X i) = ![p.2.x, p.2.y, p.2.z] i := by simp [lift]
theorem map_lift_universalHeisenberg (p : (B →+* R) × HeisenbergGroup R) :
    HeisenbergGroup.map (lift p) (universalHeisenberg B) = p.2 :=
  congrArg Prod.snd (lift.left_inv p)
@[simp] theorem map_lift_universalChange (p : (B →+* R) × HeisenbergGroup R) :
    (universalChange B).map (lift p) = heisenbergHom R p.2 := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_lift_universalHeisenberg]
@[simp] theorem lift_symm_apply (k : StrictChangeRing B →+* R) :
    lift.symm k = (k.comp C, HeisenbergGroup.map k (universalHeisenberg B)) := (rfl)

/-- A ring homomorphism out of `B[r, s, t]` is determined by its restriction to `B` and the
Heisenberg element it classifies. -/
theorem ringHom_ext {k k' : StrictChangeRing B →+* R} (h₁ : k.comp C = k'.comp C)
    (h₂ : HeisenbergGroup.map k (universalHeisenberg B) =
      HeisenbergGroup.map k' (universalHeisenberg B)) : k = k' :=
  lift.symm.injective (Prod.ext h₁ h₂)

/-- Coefficient extension `MvPolynomial.map f` carries `universalHeisenberg B` to
`universalHeisenberg B'`. -/
theorem map_map_universalHeisenberg (f : B →+* B') :
    HeisenbergGroup.map (MvPolynomial.map f) (universalHeisenberg B) = universalHeisenberg B' := by
  ext <;> simp
@[simp] theorem universalChange_map_map (f : B →+* B') :
    (universalChange B).map (MvPolynomial.map f) = universalChange B' := by
  rw [universalChange_eq_heisenbergHom, map_heisenbergHom, map_map_universalHeisenberg,
    ← universalChange_eq_heisenbergHom]

section
variable (B)

/-- The specialization homomorphism `B[u, u⁻¹, r, s, t] →+* B[r, s, t]` setting `u = 1` and fixing
`r, s, t`, corresponding to the inclusion of `HeisenbergGroup` into `VariableChange`. -/
def fromChangeRing : ChangeRing B →+* StrictChangeRing B := ChangeRing.lift (C, universalChange B)
@[simp] theorem fromChangeRing_comp_algebraMap :
    (fromChangeRing B).comp (algebraMap B (ChangeRing B)) = C := ChangeRing.lift_comp_algebraMap _
@[simp] theorem fromChangeRing_algebraMap (b : B) :
    fromChangeRing B (algebraMap B (ChangeRing B) b) = C b := ChangeRing.lift_algebraMap _ b
@[simp] theorem universalChange_map_fromChangeRing :
    (ChangeRing.universalChange B).map (fromChangeRing B) = universalChange B :=
  ChangeRing.map_lift _
@[simp] theorem fromChangeRing_algebraMap_X (i : Fin 4) :
    fromChangeRing B (algebraMap (MvPolynomial (Fin 4) B) (ChangeRing B) (X i)) =
      ![1, X 0, X 1, X 2] i := by fin_cases i <;> simp [fromChangeRing]
@[simp] theorem fromChangeRing_universalChange_u_inv :
    fromChangeRing B ((ChangeRing.universalChange B).u⁻¹ : (ChangeRing B)ˣ) = 1 := by
  simp [fromChangeRing]
end

@[simp] theorem lift_comp_fromChangeRing (q : (B →+* R) × HeisenbergGroup R) :
    (lift q).comp (fromChangeRing B) = ChangeRing.lift (q.1, heisenbergHom R q.2) :=
  ChangeRing.ringHom_ext
    (by rw [RingHom.comp_assoc, fromChangeRing_comp_algebraMap, lift_comp_C,
      ChangeRing.lift_comp_algebraMap])
    (by rw [← VariableChange.map_map, universalChange_map_fromChangeRing, map_lift_universalChange,
      ChangeRing.map_lift])
theorem fromChangeRing_comp_map (g : B →+* B') :
    (fromChangeRing B').comp (ChangeRing.map g) = (MvPolynomial.map g).comp (fromChangeRing B) :=
  ChangeRing.ringHom_ext (RingHom.ext fun _ ↦ by simp) (by simp [← VariableChange.map_map])

end StrictChangeRing

/-! ### The coordinate algebra `ℤ[u, r, s, t][u⁻¹]` -/

namespace Universal

/-- The coordinate algebra `ℤ[u,r,s,t][u⁻¹]` of the changes of variables, the case `B = ℤ` of
`ChangeRing B`. -/
abbrev CoordinateRing := ChangeRing ℤ

/-- A map from the coordinate algebra is determined by the change of variables it classifies. -/
theorem ringHom_ext {f g : CoordinateRing →+* R}
    (h : (ChangeRing.universalChange ℤ).map f = (ChangeRing.universalChange ℤ).map g) : f = g :=
  ChangeRing.ringHom_ext (RingHom.ext_int _ _) h

end Universal

end TauCeti.WeierstrassChange

namespace WeierstrassCurve.VariableChange

open TauCeti.WeierstrassChange TauCeti.WeierstrassChange.Universal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The classifying homomorphism of a change of variables: send `u,r,s,t` to its coefficients. -/
def specialize (C : VariableChange R) : CoordinateRing →+* R :=
  ChangeRing.lift (Int.castRingHom R, C)

/-- Every change of variables is the image of the universal one under its classifying map. -/
@[simp]
theorem map_specialize (C : VariableChange R) :
    (ChangeRing.universalChange ℤ).map (specialize C) = C :=
  ChangeRing.map_lift _

/-- Classifying maps commute with coefficient extension. -/
@[simp]
theorem specialize_map (C : VariableChange R) (f : R →+* S) :
    specialize (C.map f) = f.comp (specialize C) :=
  Universal.ringHom_ext (by simp [← VariableChange.map_map])

end WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

namespace Universal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The universal change is classified by the identity on its coordinate algebra. -/
@[simp]
theorem specialize_change :
    specialize (ChangeRing.universalChange ℤ) = RingHom.id CoordinateRing :=
  ringHom_ext (by simp)

/-- Ring homomorphisms from the coordinate algebra classify native changes of variables. -/
def ringHomEquiv (R : Type*) [CommRing R] : (CoordinateRing →+* R) ≃ VariableChange R where
  toFun f := (ChangeRing.universalChange ℤ).map f
  invFun := specialize
  left_inv _ := ringHom_ext (map_specialize _)
  right_inv := map_specialize

@[simp]
theorem ringHomEquiv_apply (f : CoordinateRing →+* R) :
    ringHomEquiv R f = (ChangeRing.universalChange ℤ).map f := (rfl)

@[simp]
theorem ringHomEquiv_symm_apply (C : VariableChange R) :
    (ringHomEquiv R).symm C = specialize C := (rfl)

/-- The represented point associated to a composite is obtained by mapping the original
point along the second ring homomorphism. -/
theorem ringHomEquiv_comp (f : CoordinateRing →+* R) (g : R →+* S) :
    ringHomEquiv S (g.comp f) = (ringHomEquiv R f).map g :=
  ((ChangeRing.universalChange ℤ).map_map f g).symm

end Universal

open CategoryTheory

/-- Changes of variables, with their native noncommutative group law, form a group-valued
functor of the coefficient ring. Its body is exposed so that its value types are the native
groups `VariableChange R`, without transporting points across object equalities. -/
@[expose] def pointsFunctor : CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (VariableChange R)
  map f := GrpCat.ofHom (mapHom f.hom)
  map_id _ := GrpCat.hom_ext (MonoidHom.ext fun C ↦ C.map_id)
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun C ↦ (C.map_map f.hom g.hom).symm)

/-- The points functor acts by the native coefficient map. -/
@[simp]
theorem pointsFunctor_map_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (C : VariableChange R) : pointsFunctor.map f C = C.map f.hom := (rfl)

/-- The underlying type-valued functor of Weierstrass changes of variables is corepresented
by `ℤ[u,r,s,t][u⁻¹]`. The group-scheme structure is not constructed here. -/
def pointsCorepresentableBy :
    (pointsFunctor.{u} ⋙ forget GrpCat).CorepresentableBy
      (CommRingCat.of (ULift.{u} Universal.CoordinateRing)) where
  homEquiv {R} := (ConcreteCategory.homEquiv (C := CommRingCat)).trans <|
    ({ toFun f := f.comp ULift.ringEquiv.symm.toRingHom
       invFun f := f.comp ULift.ringEquiv.toRingHom
       left_inv f := by ext x; rfl
       right_inv f := by ext x; rfl } :
      (ULift.{u} Universal.CoordinateRing →+* R) ≃ (Universal.CoordinateRing →+* R)).trans
        (Universal.ringHomEquiv R)
  homEquiv_comp g f := by
    -- Unwrap coefficient extension and use naturality of the ring-level classification.
    dsimp [ConcreteCategory.homEquiv, pointsFunctor]
    exact Universal.ringHomEquiv_comp (f.hom.comp ULift.ringEquiv.symm.toRingHom) g.hom

/-- The representing equivalence evaluates the universal change along the given ring map. -/
-- Not a simp lemma: the composite functor's object type is not in simp normal form.
theorem pointsCorepresentableBy_homEquiv {R : CommRingCat.{u}}
    (f : CommRingCat.of (ULift.{u} Universal.CoordinateRing) ⟶ R) :
    pointsCorepresentableBy.homEquiv f =
      (ChangeRing.universalChange ℤ).map (f.hom.comp ULift.ringEquiv.symm.toRingHom) := (rfl)

/-- The inverse representing equivalence is the classifying homomorphism. -/
-- As above, the composite functor's object type prevents a simp-normal-form statement.
theorem pointsCorepresentableBy_homEquiv_symm {R : CommRingCat.{u}}
    (C : VariableChange R) :
    pointsCorepresentableBy.homEquiv.symm C =
      CommRingCat.ofHom (C.specialize.comp ULift.ringEquiv.toRingHom) := (rfl)

/-- The underlying functor of changes of variables is corepresentable by its coordinate
algebra; the representing equivalence is `pointsCorepresentableBy`. -/
instance : (pointsFunctor.{u} ⋙ forget GrpCat).IsCorepresentable :=
  pointsCorepresentableBy.isCorepresentable

end TauCeti.WeierstrassChange
