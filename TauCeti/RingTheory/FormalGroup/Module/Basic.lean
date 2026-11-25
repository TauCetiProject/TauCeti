/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic

/-!
# Formal modules

Let `A` be a commutative ring and `R` a commutative `A`-algebra. A *formal `A`-module* structure
on a one-dimensional formal group law `F` over `R` (`TauCeti.FormalModule A F`) is a commutativity
proof for `F` together with an action `a ↦ [a]` of `A` by endomorphisms of `F` such that
`[1] = X`, `[a b] = [a] ∘ [b]`, `[a + b] = F([a], [b])`, and the linear coefficient of `[a]` is
the image of `a` in `R`. These are the objects of Lubin–Tate theory: the Lubin–Tate formal group
of a uniformizer `π` of a local field `K` is a formal `O_K`-module on which `π` acts by a given
Lubin–Tate series.

The tangent condition on `[a]` is not implied by the others (over `A = R = ℚ(i)`, sending `a` to
`ā X` on the additive law is a unital multiplicative additive action with the wrong linear
coefficient), and neither is additivity in `a`; both are part of the definition.

## Main definitions

* `TauCeti.FormalModule A F`: a formal `A`-module structure on `F`.
* `TauCeti.FormalModule.Hom`: homomorphisms of formal modules, the formal-group homomorphisms
  commuting with every `[a]`.
* `FormalGroup.intFormalModule`: the formal `ℤ`-module structure `[n] = FormalGroup.zsmulSeries`
  of a commutative formal group law; it is the only one.
* `TauCeti.FormalModule.𝔾ₐ`: the additive formal group law with `[a] = a X`.
* `TauCeti.FormalModule.map`: base change along a homomorphism of `A`-algebras.
* `TauCeti.FormalModule.restrictScalars`: restriction of scalars along `A → A'`.
* `TauCeti.FormalModule.conj`: transport of a formal module structure along an isomorphism of
  formal group laws, the unique structure making the isomorphism a homomorphism of formal modules.

## Main results

* `TauCeti.FormalModule.ext`: a formal module structure is determined by its action series.
* `TauCeti.FormalModule.applyPoint_act_add`: on native power-series points, `a ↦ [a](x)` is
  additive; consequently `[0] = 0` (`TauCeti.FormalModule.act_zero`), `[-a]` is the formal inverse
  of `[a]` (`TauCeti.FormalModule.act_neg`), and the integers act by integer multiplication
  (`TauCeti.FormalModule.act_intCast`).

## References

* J. Lubin and J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81
  (1965), 380–387, §1.
* E. Viehmann and K. Ziegler, *Formal moduli of formal `O_K`-modules*, Astérisque 312 (2007),
  57–66, Definition 1.1.
-/

public section

noncomputable section

open MvPowerSeries

namespace TauCeti

/-- A *formal `A`-module* structure on a formal group law `F` over an `A`-algebra `R`: `F` is
commutative, and `a ↦ [a]` is a map from `A` to the endomorphisms of `F` with `[1] = X`,
`[a b] = [a] ∘ [b]`, `[a + b] = F([a], [b])`, and linear coefficient of `[a]` equal to the image of
`a` in `R`. -/
structure FormalModule (A : Type*) [CommRing A] {R : Type*} [CommRing R] [Algebra A R]
    (F : FormalGroup R) where
  /-- The formal group law is commutative. -/
  isComm : F.IsComm
  /-- The endomorphism `[a]` of `F`. -/
  act : A → FormalGroupHom F F
  /-- The linear coefficient of `[a]` is the image of `a` in `R`. -/
  coeff_one_act (a : A) : PowerSeries.coeff 1 (act a).toPowerSeries = algebraMap A R a
  /-- `[1]` is the identity. -/
  act_one : act 1 = FormalGroupHom.id F
  /-- `[a b] = [a] ∘ [b]`. -/
  act_mul (a b : A) : act (a * b) = (act a).comp (act b)
  /-- `[a + b] = F([a], [b])`. -/
  act_add (a b : A) : (act (a + b)).toPowerSeries =
    subst ![(act a).toPowerSeries, (act b).toPowerSeries] F.toPowerSeries

namespace FormalModule

attribute [simp] coeff_one_act act_one

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] {F G H : FormalGroup R}

/-- A formal module structure is determined by its action series. -/
@[ext]
theorem ext {ρ ρ' : FormalModule A F}
    (h : ∀ a, (ρ.act a).toPowerSeries = (ρ'.act a).toPowerSeries) : ρ = ρ' := by
  obtain ⟨_, act, _⟩ := ρ
  obtain ⟨_, act', _⟩ := ρ'
  obtain rfl : act = act' := funext fun a ↦ FormalGroupHom.ext (h a)
  rfl

variable (ρ : FormalModule A F)

/-- The actions of two scalars commute. -/
theorem act_comp_act_comm (a b : A) : (ρ.act a).comp (ρ.act b) = (ρ.act b).comp (ρ.act a) := by
  rw [← ρ.act_mul, ← ρ.act_mul, mul_comm]

/-! ### The action on points -/

section Points

variable {σ : Type*}

/-- On a native power-series point `x`, `[a + b](x) = [a](x) + [b](x)`. -/
theorem applyPoint_act_add (x : F.Point σ) (a b : A) :
    (ρ.act (a + b)).applyPoint x = (ρ.act a).applyPoint x + (ρ.act b).applyPoint x := by
  apply Subtype.ext
  have hab : HasSubst ![(ρ.act a).toPowerSeries, (ρ.act b).toPowerSeries] :=
    hasSubst_finTwo (ρ.act a).hasSubst (ρ.act b).hasSubst
  rw [FormalGroupHom.applyPoint_val, ρ.act_add, FormalGroup.add_apply,
    PowerSeries.subst_def _ (subst _ _), subst_comp_subst_apply hab x.prop.const]
  congr 1
  funext i
  fin_cases i <;> simp [PowerSeries.subst_def]

/-- `a ↦ [a](x)` as an additive map from `A` to the points of `F`. -/
private def applyPointAddHom (x : F.Point σ) : A →+ F.Point σ :=
  AddMonoidHom.mk' (fun a ↦ (ρ.act a).applyPoint x) (ρ.applyPoint_act_add x)

@[simp]
theorem applyPoint_act_zero (x : F.Point σ) : (ρ.act 0).applyPoint x = 0 :=
  (ρ.applyPointAddHom x).map_zero

@[simp]
theorem applyPoint_act_neg (x : F.Point σ) (a : A) :
    (ρ.act (-a)).applyPoint x = -(ρ.act a).applyPoint x :=
  (ρ.applyPointAddHom x).map_neg a

theorem applyPoint_act_sub (x : F.Point σ) (a b : A) :
    (ρ.act (a - b)).applyPoint x = (ρ.act a).applyPoint x - (ρ.act b).applyPoint x :=
  (ρ.applyPointAddHom x).map_sub a b

/-- The integers act on points by integer multiplication. -/
@[simp]
theorem applyPoint_act_intCast (x : F.Point σ) (n : ℤ) : (ρ.act n).applyPoint x = n • x := by
  have h := map_zsmul (ρ.applyPointAddHom x) n 1
  rwa [applyPointAddHom, AddMonoidHom.mk'_apply, Int.smul_one_eq_cast,
    act_one, FormalGroupHom.id_applyPoint] at h

end Points

/-! ### Series identities -/

/-- `[0] = 0`. -/
@[simp]
theorem act_zero : (ρ.act 0).toPowerSeries = 0 := by
  have h := congrArg Subtype.val (ρ.applyPoint_act_zero F.tautologicalPoint)
  rwa [FormalGroupHom.val_applyPoint_tautologicalPoint, FormalGroup.zero_apply] at h

/-- `[-a]` is the formal inverse of `[a]`. -/
theorem act_neg (a : A) :
    (ρ.act (-a)).toPowerSeries = PowerSeries.subst (ρ.act a).toPowerSeries F.addInvX := by
  have h := congrArg Subtype.val (ρ.applyPoint_act_neg F.tautologicalPoint a)
  rwa [FormalGroupHom.val_applyPoint_tautologicalPoint, FormalGroup.neg_apply,
    FormalGroupHom.val_applyPoint_tautologicalPoint] at h

/-- The integer `n` acts by the multiplication series `[n]_F`. -/
@[simp]
theorem act_intCast (n : ℤ) : (ρ.act n).toPowerSeries = F.zsmulSeries n := by
  have h := congrArg Subtype.val (ρ.applyPoint_act_intCast F.tautologicalPoint n)
  rwa [FormalGroupHom.val_applyPoint_tautologicalPoint, ← F.subst_zsmulSeries,
    FormalGroup.val_tautologicalPoint, PowerSeries.X_subst] at h

/-- The natural number `n` acts by the multiplication series `[n]_F`. -/
@[simp]
theorem act_natCast (n : ℕ) : (ρ.act n).toPowerSeries = F.nsmulSeries n := by
  simpa using ρ.act_intCast n

/-- `[-1]` is the formal inverse. -/
@[simp]
theorem act_neg_one : (ρ.act (-1)).toPowerSeries = F.addInvX := by
  simpa using ρ.act_intCast (-1)

/-! ### Homomorphisms -/

/-- A *homomorphism of formal `A`-modules* is a homomorphism of the underlying formal group laws
commuting with the action of every `a ∈ A`. -/
@[ext]
structure Hom (ρ : FormalModule A F) (ρ' : FormalModule A G) extends FormalGroupHom F G where
  /-- `f ∘ [a] = [a] ∘ f` for every `a`. -/
  comp_act (a : A) : toFormalGroupHom.comp (ρ.act a) = (ρ'.act a).comp toFormalGroupHom

namespace Hom

variable {ρ} {ρ' : FormalModule A G} {ρ'' : FormalModule A H}

/-- The identity homomorphism of a formal module. -/
def id (ρ : FormalModule A F) : Hom ρ ρ where
  toFormalGroupHom := FormalGroupHom.id F
  comp_act a := by simp

@[simp]
theorem id_toFormalGroupHom (ρ : FormalModule A F) :
    (id ρ).toFormalGroupHom = FormalGroupHom.id F := (rfl)

/-- Composition of homomorphisms of formal modules, with the outer map first. -/
def comp (g : Hom ρ' ρ'') (f : Hom ρ ρ') : Hom ρ ρ'' where
  toFormalGroupHom := g.toFormalGroupHom.comp f.toFormalGroupHom
  comp_act a := by
    rw [FormalGroupHom.comp_assoc, f.comp_act, ← FormalGroupHom.comp_assoc, g.comp_act,
      FormalGroupHom.comp_assoc]

@[simp]
theorem comp_toFormalGroupHom (g : Hom ρ' ρ'') (f : Hom ρ ρ') :
    (g.comp f).toFormalGroupHom = g.toFormalGroupHom.comp f.toFormalGroupHom := (rfl)

@[simp]
theorem id_comp (f : Hom ρ ρ') : (id ρ').comp f = f := by
  ext : 1
  simp

@[simp]
theorem comp_id (f : Hom ρ ρ') : f.comp (id ρ) = f := by
  ext : 1
  simp

theorem comp_assoc {K : FormalGroup R} {ρ''' : FormalModule A K} (h : Hom ρ'' ρ''')
    (g : Hom ρ' ρ'') (f : Hom ρ ρ') : (h.comp g).comp f = h.comp (g.comp f) := by
  ext : 1
  simp [FormalGroupHom.comp_assoc]

end Hom

/-! ### Restriction of scalars -/

section RestrictScalars

variable (A) {A' : Type*} [CommRing A'] [Algebra A A'] [Algebra A' R] [IsScalarTower A A' R]

/-- Restriction of scalars along `A → A'`: a formal `A'`-module is a formal `A`-module on the
same law, with `[a] = [algebraMap A A' a]`. -/
def restrictScalars (ρ : FormalModule A' F) : FormalModule A F where
  isComm := ρ.isComm
  act a := ρ.act (algebraMap A A' a)
  coeff_one_act a := by rw [ρ.coeff_one_act, ← IsScalarTower.algebraMap_apply]
  act_one := by rw [map_one, ρ.act_one]
  act_mul a b := by rw [map_mul, ρ.act_mul]
  act_add a b := by rw [map_add, ρ.act_add]

@[simp]
theorem restrictScalars_act (ρ : FormalModule A' F) (a : A) :
    (ρ.restrictScalars A).act a = ρ.act (algebraMap A A' a) := (rfl)

end RestrictScalars

/-- Restricting scalars along the identity does nothing. -/
@[simp]
theorem restrictScalars_self : ρ.restrictScalars A = ρ := by
  ext
  simp

/-! ### Base change -/

section Map

variable {S T : Type*} [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]

/-- Base change of a formal `A`-module along a homomorphism `φ : R →ₐ[A] S` of `A`-algebras: the
law `F.map φ` with action series `[a]` mapped by `φ`. -/
def map (φ : R →ₐ[A] S) : FormalModule A (F.map (φ : R →+* S)) where
  isComm := haveI := ρ.isComm; inferInstance
  act a := (ρ.act a).map (φ : R →+* S)
  coeff_one_act a := by simp
  act_one := by rw [ρ.act_one, FormalGroupHom.map_id]
  act_mul a b := by rw [ρ.act_mul, FormalGroupHom.map_comp]
  act_add a b := by
    -- `PowerSeries.map` is `MvPowerSeries.map` on the unit index type.
    rw [FormalGroupHom.map_toPowerSeries, ρ.act_add, FormalGroup.map_toPowerSeries]
    refine (MvPowerSeries.map_subst
      (hasSubst_finTwo (ρ.act a).hasSubst (ρ.act b).hasSubst) _).trans ?_
    congr 1
    funext i
    -- `PowerSeries.map` is `MvPowerSeries.map` on the unit index type.
    fin_cases i <;> exact (FormalGroupHom.map_toPowerSeries _ _).symm

@[simp]
theorem map_act (φ : R →ₐ[A] S) (a : A) : (ρ.map φ).act a = (ρ.act a).map (φ : R →+* S) :=
  (rfl)

/-- Base change along the identity does nothing. The formal groups `F.map (AlgHom.id A R)` and
`F` are definitionally equal, so no transport is needed. -/
@[simp]
theorem map_id : (ρ.map (AlgHom.id A R) : FormalModule A F) = ρ := by
  ext a : 1
  simp

/-- Successive base changes agree with base change along the composite. The formal groups
`(F.map φ).map ψ` and `F.map (ψ.comp φ)` are definitionally equal, so no transport is needed. -/
@[simp]
theorem map_map (φ : R →ₐ[A] S) (ψ : S →ₐ[A] T) :
    ((ρ.map φ).map ψ : FormalModule A (F.map ((ψ.comp φ : R →ₐ[A] T) : R →+* T))) =
      ρ.map (ψ.comp φ) := by
  ext a : 1
  simp [AlgHom.comp_toRingHom]

end Map

/-! ### Transport along isomorphisms -/

section Conj

variable (e : FormalGroupIso F G)

/-- Transport of a formal module structure along an isomorphism `e : F ≅ G` of formal group
laws: `[a]_G = e ∘ [a]_F ∘ e⁻¹`. -/
def conj : FormalModule A G where
  isComm :=
    haveI := ρ.isComm
    -- `G` is the coordinate change of `F` along the series of `e`
    e.toHom.smul_eq (φ := ⟨e.toHom.toPowerSeries, e.toHom.zero_constantCoeff, e.isUnit_coeff_one⟩)
      rfl ▸ inferInstance
  act a := e.toHom.comp ((ρ.act a).comp e.invHom)
  coeff_one_act a := by
    rw [FormalGroupHom.coeff_one_comp, FormalGroupHom.coeff_one_comp, ρ.coeff_one_act,
      mul_left_comm, ← FormalGroupHom.coeff_one_comp, FormalGroupIso.toHom_comp_invHom]
    simp
  act_one := by simp
  act_mul a b := by
    rw [ρ.act_mul]
    simp only [FormalGroupHom.comp_assoc]
    rw [← FormalGroupHom.comp_assoc e.invHom e.toHom, FormalGroupIso.invHom_comp_toHom,
      FormalGroupHom.id_comp]
  act_add a b := by
    -- apply `e` to `[a + b](y) = [a](y) + [b](y)` at the point `y = e⁻¹(X)` of `F`
    have h := congrArg (fun x ↦ (e.toHom.applyPoint x).val)
      (ρ.applyPoint_act_add (e.invHom.applyPoint G.tautologicalPoint) a b)
    simp only [FormalGroupHom.applyPoint_add, ← FormalGroupHom.comp_applyPoint,
      FormalGroup.add_apply, FormalGroupHom.val_applyPoint_tautologicalPoint] at h
    exact h

@[simp]
theorem conj_act (a : A) : (ρ.conj e).act a = e.toHom.comp ((ρ.act a).comp e.invHom) := (rfl)

/-- The isomorphism `e` intertwines `ρ` and `ρ.conj e`. -/
theorem comp_act_conj (a : A) : e.toHom.comp (ρ.act a) = ((ρ.conj e).act a).comp e.toHom := by
  rw [conj_act, FormalGroupHom.comp_assoc, FormalGroupHom.comp_assoc,
    FormalGroupIso.invHom_comp_toHom, FormalGroupHom.comp_id]

/-- `ρ.conj e` is the only formal module structure on `G` for which `e` commutes with the
actions. -/
theorem eq_conj_iff (ρ' : FormalModule A G) :
    ρ' = ρ.conj e ↔ ∀ a, e.toHom.comp (ρ.act a) = (ρ'.act a).comp e.toHom := by
  refine ⟨fun h a ↦ h ▸ ρ.comp_act_conj e a, fun h ↦ ?_⟩
  ext a : 1
  rw [conj_act, ← FormalGroupHom.comp_assoc, h, FormalGroupHom.comp_assoc,
    FormalGroupIso.toHom_comp_invHom, FormalGroupHom.comp_id]

/-- The isomorphism `e` as a homomorphism of formal modules from `ρ` to `ρ.conj e`. -/
def conjHom : Hom ρ (ρ.conj e) where
  toFormalGroupHom := e.toHom
  comp_act := ρ.comp_act_conj e

@[simp]
theorem conjHom_toFormalGroupHom : (ρ.conjHom e).toFormalGroupHom = e.toHom := (rfl)

/-- The inverse of `e` as a homomorphism of formal modules from `ρ.conj e` to `ρ`. -/
def conjInvHom : Hom (ρ.conj e) ρ where
  toFormalGroupHom := e.invHom
  comp_act a := by
    rw [conj_act, ← FormalGroupHom.comp_assoc, ← FormalGroupHom.comp_assoc,
      FormalGroupIso.invHom_comp_toHom, FormalGroupHom.id_comp]

@[simp]
theorem conjInvHom_toFormalGroupHom : (ρ.conjInvHom e).toFormalGroupHom = e.invHom := (rfl)

/-- Transport along the identity isomorphism does nothing. -/
@[simp]
theorem conj_refl : ρ.conj (FormalGroupIso.refl F) = ρ := by
  ext
  simp

/-- Transport along a composite isomorphism is the composite of the transports. -/
theorem conj_trans (e' : FormalGroupIso G H) : ρ.conj (e.trans e') = (ρ.conj e).conj e' := by
  ext a : 1
  simp only [conj_act, FormalGroupIso.trans_toHom, FormalGroupIso.trans_invHom,
    FormalGroupHom.comp_assoc]

/-- Transporting along `e` and back along its inverse does nothing. -/
@[simp]
theorem conj_conj_symm : (ρ.conj e).conj e.symm = ρ := by
  rw [← conj_trans, FormalGroupIso.self_trans_symm, conj_refl]

end Conj

end FormalModule

/-! ### Examples -/

/-- The additive formal group law with `[a] = a X`. -/
def FormalModule.𝔾ₐ (A R : Type*) [CommRing A] [CommRing R] [Algebra A R] :
    FormalModule A (FormalGroup.𝔾ₐ (R := R)) where
  isComm := inferInstance
  act a := FormalGroupHom.ofHomDefectEqZero (f := algebraMap A R a • PowerSeries.X)
    (by simp) (by rw [FormalGroup.homDefect_𝔾ₐ_smul, FormalGroup.homDefect_X, sub_self, smul_zero])
  coeff_one_act a := by simp [Algebra.algebraMap_eq_smul_one]
  act_one := by
    ext : 1
    simp
  act_mul a b := by
    have hb : PowerSeries.HasSubst (b • PowerSeries.X : PowerSeries R) :=
      .of_constantCoeff_zero' (by simp)
    ext : 1
    simp [PowerSeries.subst_smul hb, PowerSeries.subst_X hb, mul_smul]
  act_add a b := by
    have hX (c : A) : PowerSeries.HasSubst (c • PowerSeries.X : PowerSeries R) :=
      .of_constantCoeff_zero' (by simp)
    have hab := hasSubst_finTwo (hX a) (hX b)
    simp [add_smul, subst_add hab, subst_X hab]

/-- The additive formal module acts by `[a] = a X`. -/
@[simp]
theorem FormalModule.𝔾ₐ_act_toPowerSeries {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (a : A) :
    ((FormalModule.𝔾ₐ A R).act a).toPowerSeries = algebraMap A R a • PowerSeries.X :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

end TauCeti

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- A formal group law has at most one formal `ℤ`-module structure. -/
instance : Subsingleton (TauCeti.FormalModule ℤ F) :=
  ⟨fun ρ ρ' ↦ TauCeti.FormalModule.ext fun n ↦ by
    simpa using (ρ.act_intCast n).trans (ρ'.act_intCast n).symm⟩

variable [F.IsComm]

/-- The formal `ℤ`-module structure of a commutative formal group law, `[n] = [n]_F`. -/
def intFormalModule : TauCeti.FormalModule ℤ F where
  isComm := ‹_›
  act := F.zsmulHom
  coeff_one_act n := by simp
  act_one := F.zsmulHom_one
  act_mul m n := TauCeti.FormalGroupHom.ext <| by
    simp only [TauCeti.FormalGroupHom.comp_toPowerSeries, zsmulHom_toPowerSeries]
    exact F.zsmulSeries_mul m n
  act_add m n := by
    simp only [zsmulHom_toPowerSeries]
    exact F.zsmulSeries_add m n

@[simp]
theorem intFormalModule_act (n : ℤ) : F.intFormalModule.act n = F.zsmulHom n := (rfl)

/-- A commutative formal group law has exactly one formal `ℤ`-module structure. -/
instance : Unique (TauCeti.FormalModule ℤ F) where
  default := F.intFormalModule
  uniq _ := Subsingleton.elim _ _

end FormalGroup
