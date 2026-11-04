/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.Naturality
public import TauCeti.RingTheory.MvPowerSeries.Symmetric
public import TauCeti.RingTheory.PowerSeries.Cartier
import Mathlib.RingTheory.Localization.Defs
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial
import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Basic
import TauCeti.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Curves on formal group laws and Cartier's operators

Let `F(X, Y)` be a one-dimensional formal group law over a commutative ring `R`. A **curve** on `F`
is a one-variable formal power series `γ(T) ∈ R⟦T⟧` with zero constant term. Curves form a group
under formal-group addition `(γ₁ + γ₂)(T) = F(γ₁(T), γ₂(T))`, abelian when `F` is commutative; the
tautological curve `γ(T) = T` is `FormalGroup.tautologicalCurve`.

Cartier introduced two families of additive endomorphisms on the group of curves, indexed by
nonzero natural numbers `n`:

* **Verschiebung** `V_n` (`FormalGroup.verschiebungCurve`), defined for any formal group law by
  `(V_n γ)(T) = γ(Tⁿ)` (`PowerSeries.expand n`).
* **Frobenius** `f_n` (`FormalGroup.frobeniusCurve`), defined for any commutative formal group law
  without adjoining `n`-th roots of unity: the formal-group sum
  `γ(T₁) +_F ⋯ +_F γ(Tₙ) ∈ R⟦T₁, …, Tₙ⟧` is symmetric in `T₁, …, Tₙ`, and evaluating its
  elementary symmetric expansion at `e₁ = ⋯ = e_{n-1} = 0` and `eₙ = (-1)^(n-1) T`
  (`MvPowerSeries.symmetricSubalgebra.evalTopEsymm`) produces `(f_n γ)(T)`.

Both operators are natural with respect to homomorphisms of formal group laws and base change of
the coefficient ring. Over a `ℚ`-algebra, the formal logarithm linearises them into
`PowerSeries.expand` and `n • PowerSeries.cartier R n 0`:

  `log_F((V_n γ)(T)) = log_F(γ(Tⁿ))`,
  `log_F((f_n γ)(T)) = ∑_{k ≥ 1} n c_{nk} Tᵏ`  where `log_F(γ(T)) = ∑_{m ≥ 1} c_m Tᵐ`.

By Lazard's theorem, every pair `(F, γ)` over an arbitrary commutative ring lifts from a pair over
a localization of a polynomial algebra over the Lazard ring, which embeds into a `ℚ`-algebra. This
yields Cartier's relations over every commutative ring:

* `f_1 = id` and `V_1 = id`,
* `f_m ∘ f_n = f_{mn}` and `V_m ∘ V_n = V_{mn}`,
* `f_n ∘ V_n = [n]_F`,
* `f_m ∘ V_n = V_n ∘ f_m` whenever `gcd(m, n) = 1`.

## Main definitions

* `FormalGroup.Curve`: curves `γ(T) ∈ R⟦T⟧` with `γ(0) = 0` on a formal group law `F`, carrying
  `AddGroup` (and `AddCommGroup` when `F` is commutative) instances.
* `FormalGroup.Curve.toPointHom` and `FormalGroup.Curve.coordPointHom`: additive homomorphisms
  embedding curves into `F.Point Unit` and into the `i`-th coordinate of `F.Point σ`.
* `FormalGroup.tautologicalCurve`: the identity curve `T` on `F`.
* `FormalGroup.Curve.map`: base change of curves along a ring homomorphism `R →+* S`.
* `TauCeti.FormalGroupHom.mapCurve` and `TauCeti.FormalGroupIso.curveEquiv`: pushforward of curves
  along homomorphisms and isomorphisms of formal group laws.
* `FormalGroup.verschiebungCurve`: Cartier's Verschiebung operator `V_n : F.Curve →+ F.Curve`.
* `FormalGroup.frobeniusCurve`: Cartier's Frobenius operator `f_n : F.Curve →+ F.Curve`.

## Main results

* `FormalGroup.toPowerSeries_frobeniusCurve`: explicit power-series formula for `(f_n γ)(T)` via
  `MvPowerSeries.symmetricSubalgebra.evalTopEsymm` and `FormalGroup.Curve.coordPointHom`.
* `FormalGroup.subst_verschiebungCurve_log` and `FormalGroup.subst_frobeniusCurve_log`: action of
  `V_n` and `f_n` on the formal logarithm over a `ℚ`-algebra.
* `FormalGroup.frobeniusCurve_one`, `FormalGroup.frobeniusCurve_frobeniusCurve`,
  `FormalGroup.frobeniusCurve_verschiebungCurve_self`, and
  `FormalGroup.frobeniusCurve_verschiebungCurve_of_coprime`: Cartier's operator identities over an
  arbitrary commutative ring.
* `FormalGroup.Curve.exists_lift_of_isUnit_natCast`: lifting of `(F, γ)` to a ring that inverts a
  specified set of nonzero natural numbers and embeds into a `ℚ`-algebra.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.1–16.2.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.19.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-! ### Curves and their group structure -/

/-- A **curve** on a formal group law `F` over `R` is a one-variable power series `γ(T) ∈ R⟦T⟧`
with zero constant coefficient. -/
@[ext]
structure Curve (F : FormalGroup R) where
  /-- The underlying power series `γ(T) ∈ R⟦T⟧`. -/
  toPowerSeries : PowerSeries R
  /-- A curve sends the origin to the origin: `γ(0) = 0`. -/
  constantCoeff_toPowerSeries : PowerSeries.constantCoeff toPowerSeries = 0

namespace Curve

variable {F : FormalGroup R}

attribute [simp] constantCoeff_toPowerSeries

@[simp]
theorem coeff_zero_toPowerSeries (γ : F.Curve) : PowerSeries.coeff 0 γ.toPowerSeries = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, γ.constantCoeff_toPowerSeries]

/-- Every curve has zero constant coefficient and therefore admits formal substitution. -/
theorem hasSubst (γ : F.Curve) : PowerSeries.HasSubst γ.toPowerSeries :=
  .of_constantCoeff_zero' γ.constantCoeff_toPowerSeries

/-- View a curve on `F` as a one-variable power-series point in `F.Point Unit`. -/
noncomputable def toPoint (γ : F.Curve) : F.Point Unit :=
  ⟨γ.toPowerSeries, γ.hasSubst⟩

@[simp]
theorem val_toPoint (γ : F.Curve) : γ.toPoint.val = γ.toPowerSeries := (rfl)

theorem toPoint_injective : Function.Injective (toPoint (F := F)) :=
  fun _ _ h ↦ Curve.ext (congrArg Subtype.val h)

noncomputable instance : Zero F.Curve where
  zero := ⟨0, map_zero _⟩

@[simp]
theorem toPowerSeries_zero : (0 : F.Curve).toPowerSeries = 0 := (rfl)

noncomputable instance : Add F.Curve where
  add γ₁ γ₂ :=
    ⟨F.toPowerSeries.subst ![γ₁.toPowerSeries, γ₂.toPowerSeries],
      constantCoeff_subst_eq_zero
        (PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries γ₂.constantCoeff_toPowerSeries)
        (fun i ↦ by
          fin_cases i
          · exact γ₁.constantCoeff_toPowerSeries
          · exact γ₂.constantCoeff_toPowerSeries) F.zero_constantCoeff⟩

@[simp]
theorem toPowerSeries_add (γ₁ γ₂ : F.Curve) :
    (γ₁ + γ₂).toPowerSeries = F.toPowerSeries.subst ![γ₁.toPowerSeries, γ₂.toPowerSeries] :=
  (rfl)

noncomputable instance : Neg F.Curve where
  neg γ :=
    ⟨PowerSeries.subst γ.toPowerSeries F.addInvX,
      PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries _
        F.constantCoeff_addInvX⟩

@[simp]
theorem toPowerSeries_neg (γ : F.Curve) :
    (-γ).toPowerSeries = PowerSeries.subst γ.toPowerSeries F.addInvX := (rfl)

noncomputable instance : Sub F.Curve where
  sub γ₁ γ₂ := γ₁ + -γ₂

theorem toPowerSeries_sub (γ₁ γ₂ : F.Curve) :
    (γ₁ - γ₂).toPowerSeries = (γ₁ + -γ₂).toPowerSeries := (rfl)

noncomputable instance : SMul ℕ F.Curve where
  smul n γ :=
    ⟨PowerSeries.subst γ.toPowerSeries (F.nsmulSeries n),
      PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries _
        (F.constantCoeff_nsmulSeries n)⟩

@[simp]
theorem toPowerSeries_nsmul (n : ℕ) (γ : F.Curve) :
    (n • γ).toPowerSeries = PowerSeries.subst γ.toPowerSeries (F.nsmulSeries n) := (rfl)

noncomputable instance : SMul ℤ F.Curve where
  smul n γ :=
    ⟨PowerSeries.subst γ.toPowerSeries (F.zsmulSeries n),
      PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries _
        (F.constantCoeff_zsmulSeries n)⟩

@[simp]
theorem toPowerSeries_zsmul (n : ℤ) (γ : F.Curve) :
    (n • γ).toPowerSeries = PowerSeries.subst γ.toPowerSeries (F.zsmulSeries n) := (rfl)

@[simp]
theorem toPoint_zero : (0 : F.Curve).toPoint = 0 :=
  Subtype.ext ((val_toPoint 0).trans (zero_apply (F := F)).symm)

@[simp]
theorem toPoint_add (γ₁ γ₂ : F.Curve) : (γ₁ + γ₂).toPoint = γ₁.toPoint + γ₂.toPoint :=
  Subtype.ext (by simp [add_apply])

@[simp]
theorem toPoint_neg (γ : F.Curve) : (-γ).toPoint = -γ.toPoint :=
  Subtype.ext (by simp [neg_apply])

noncomputable instance : AddGroup F.Curve :=
  toPoint_injective.addGroup toPoint
    toPoint_zero
    toPoint_add
    toPoint_neg
    (fun γ₁ γ₂ ↦ Subtype.ext (by simp [toPowerSeries_sub, sub_eq_add_neg, add_apply, neg_apply]))
    (fun γ n ↦ Subtype.ext <| by
      simpa only [val_toPoint, toPowerSeries_nsmul] using F.subst_nsmulSeries γ.toPoint n)
    (fun γ n ↦ Subtype.ext <| by
      simpa only [val_toPoint, toPowerSeries_zsmul] using F.subst_zsmulSeries γ.toPoint n)

noncomputable instance [F.IsComm] : AddCommGroup F.Curve :=
  { (inferInstance : AddGroup F.Curve) with
    add_comm := fun γ₁ γ₂ ↦ toPoint_injective (by rw [toPoint_add, toPoint_add, add_comm]) }

/-- Viewing a curve on `F` as a one-variable power-series point in `F.Point Unit` is an additive
homomorphism. -/
noncomputable def toPointHom (F : FormalGroup R) : F.Curve →+ F.Point Unit where
  toFun := toPoint
  map_zero' := toPoint_zero
  map_add' := toPoint_add

@[simp]
theorem toPointHom_apply (γ : F.Curve) : toPointHom F γ = γ.toPoint := (rfl)

/-- Embedding a curve in the `i`-th variable `Tᵢ` gives an additive homomorphism
`F.Curve →+ F.Point σ`. -/
noncomputable def coordPointHom (F : FormalGroup R) {σ : Type*} (i : σ) :
    F.Curve →+ F.Point σ :=
  (F.substPointHom (PowerSeries.HasSubst.X (S := R) i).const).comp (toPointHom F)

@[simp]
theorem val_coordPointHom (F : FormalGroup R) {σ : Type*} (i : σ) (γ : F.Curve) :
    (coordPointHom F i γ).val = γ.toPowerSeries.toMvPowerSeries i := by
  rw [coordPointHom, AddMonoidHom.comp_apply, val_substPointHom, toPointHom_apply, val_toPoint,
    PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.subst_def]

/-- The formal-group sum `∑ i : σ, γ(Tᵢ)` of copies of a curve `γ` in each variable of a finite
index type `σ` is a symmetric power series. -/
theorem isSymmetric_val_sum_coordPointHom [F.IsComm] {σ : Type*} [Fintype σ] (γ : F.Curve) :
    (∑ i : σ, coordPointHom F i γ).val.IsSymmetric :=
  isSymmetric_iff.mpr fun e ↦ by
    have hcoord : ∀ i : σ,
        F.substPointHom (HasSubst.X_comp e) (coordPointHom F i γ) =
          coordPointHom F (e i) γ := fun i ↦
      Subtype.ext <| by
        rw [val_substPointHom, ← rename_eq_subst, val_coordPointHom, val_coordPointHom,
          rename_toMvPowerSeries]
    have hsum :
        F.substPointHom (HasSubst.X_comp e) (∑ i : σ, coordPointHom F i γ) =
          ∑ i : σ, coordPointHom F i γ := by
      rw [map_sum]
      simp_rw [hcoord]
      exact Equiv.sum_comp e fun i ↦ coordPointHom F i γ
    rw [rename_eq_subst, ← val_substPointHom F (HasSubst.X_comp e), hsum]

/-- Adding a curve `δ` whose coefficients vanish below degree `m` leaves degrees `< m` unchanged
and adds `coeff m δ` in degree `m`. -/
theorem coeff_add_of_forall_lt_coeff_eq_zero (γ δ : F.Curve) {m k : ℕ} (hm : m ≠ 0) (hk : k ≤ m)
    (hδ : ∀ i < m, PowerSeries.coeff i δ.toPowerSeries = 0) :
    PowerSeries.coeff k (γ + δ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries +
        if k = m then PowerSeries.coeff m δ.toPowerSeries else 0 := by
  obtain ⟨r, hr⟩ := PowerSeries.X_pow_dvd_iff.mpr hδ
  have h := PowerSeries.coeff_subst_update_add_X_pow_mul F.toPowerSeries
    (PowerSeries.hasSubst_pair γ.constantCoeff_toPowerSeries (map_zero _))
    (fun s ↦ by
      fin_cases s
      · exact γ.constantCoeff_toPowerSeries
      · exact map_zero _) 1 r hm hk
  have hu : Function.update ![γ.toPowerSeries, 0] 1 (0 + PowerSeries.X ^ m * r) =
      ![γ.toPowerSeries, δ.toPowerSeries] := by
    funext i; fin_cases i <;> simp [hr]
  have h0 : F.toPowerSeries.subst ![γ.toPowerSeries, 0] = γ.toPowerSeries := by
    simpa only [toPowerSeries_add, toPowerSeries_zero] using
      congrArg Curve.toPowerSeries (_root_.add_zero γ)
  have hrm : PowerSeries.constantCoeff r = PowerSeries.coeff m δ.toPowerSeries := by
    rw [hr, PowerSeries.coeff_X_pow_mul', ite_eq_left (le_refl m), Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [toPowerSeries_add]
  simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, hu, h0, F.lin_coeff_Y, map_one, one_mul,
    hrm] using h

theorem coeff_add_eq_left_of_forall_lt_coeff_eq_zero (γ δ : F.Curve) {m k : ℕ} (hk : k < m)
    (hδ : ∀ i < m, PowerSeries.coeff i δ.toPowerSeries = 0) :
    PowerSeries.coeff k (γ + δ).toPowerSeries = PowerSeries.coeff k γ.toPowerSeries := by
  rw [coeff_add_of_forall_lt_coeff_eq_zero γ δ (by omega) hk.le hδ, ite_eq_right hk.ne,
    _root_.add_zero]

/-- Degree-`k` coefficients of formal-group sums depend only on coefficients up to degree `k`. -/
theorem coeff_add_congr {γ₁ γ₁' γ₂ γ₂' : F.Curve} {k : ℕ}
    (h₁ : ∀ i ≤ k, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₁'.toPowerSeries)
    (h₂ : ∀ i ≤ k, PowerSeries.coeff i γ₂.toPowerSeries = PowerSeries.coeff i γ₂'.toPowerSeries) :
    PowerSeries.coeff k (γ₁ + γ₂).toPowerSeries =
      PowerSeries.coeff k (γ₁' + γ₂').toPowerSeries := by
  obtain ⟨r₁, hr₁⟩ : PowerSeries.X ^ (k + 1) ∣ γ₁.toPowerSeries - γ₁'.toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i (hi : i < k + 1) ↦ by
      rw [map_sub, h₁ i (by omega), sub_self]
  obtain ⟨r₂, hr₂⟩ : PowerSeries.X ^ (k + 1) ∣ γ₂.toPowerSeries - γ₂'.toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i (hi : i < k + 1) ↦ by
      rw [map_sub, h₂ i (by omega), sub_self]
  have hstep₁ := PowerSeries.coeff_subst_update_add_X_pow_mul F.toPowerSeries
    (PowerSeries.hasSubst_pair γ₁'.constantCoeff_toPowerSeries γ₂.constantCoeff_toPowerSeries)
    (fun s ↦ by
      fin_cases s
      · exact γ₁'.constantCoeff_toPowerSeries
      · exact γ₂.constantCoeff_toPowerSeries) 0 r₁ (Nat.succ_ne_zero k) (Nat.le_succ k)
  have hu₁ : Function.update ![γ₁'.toPowerSeries, γ₂.toPowerSeries] 0
      (γ₁'.toPowerSeries + PowerSeries.X ^ (k + 1) * r₁) =
      ![γ₁.toPowerSeries, γ₂.toPowerSeries] := by
    funext i; fin_cases i <;> simp [← hr₁]
  have hstep₂ := PowerSeries.coeff_subst_update_add_X_pow_mul F.toPowerSeries
    (PowerSeries.hasSubst_pair γ₁'.constantCoeff_toPowerSeries γ₂'.constantCoeff_toPowerSeries)
    (fun s ↦ by
      fin_cases s
      · exact γ₁'.constantCoeff_toPowerSeries
      · exact γ₂'.constantCoeff_toPowerSeries) 1 r₂ (Nat.succ_ne_zero k) (Nat.le_succ k)
  have hu₂ : Function.update ![γ₁'.toPowerSeries, γ₂'.toPowerSeries] 1
      (γ₂'.toPowerSeries + PowerSeries.X ^ (k + 1) * r₂) =
      ![γ₁'.toPowerSeries, γ₂.toPowerSeries] := by
    funext i; fin_cases i <;> simp [← hr₂]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.succ_eq_add_one] at hstep₁ hstep₂
  rw [toPowerSeries_add, toPowerSeries_add, ← hu₁, hstep₁,
    ite_eq_right (Nat.ne_of_lt (Nat.lt_succ_self k)), _root_.add_zero, ← hu₂, hstep₂,
    ite_eq_right (Nat.ne_of_lt (Nat.lt_succ_self k)), _root_.add_zero]

/-- Extracting the linear coefficient `coeff 1` is an additive homomorphism `F.Curve →+ R`. -/
noncomputable def coeffOneHom (F : FormalGroup R) : F.Curve →+ R where
  toFun γ := PowerSeries.coeff 1 γ.toPowerSeries
  map_zero' := by rw [toPowerSeries_zero, map_zero]
  map_add' γ₁ γ₂ := by
    have h := coeff_add_of_forall_lt_coeff_eq_zero γ₁ γ₂ one_ne_zero (le_refl 1) fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      exact γ₂.coeff_zero_toPowerSeries
    simpa only [ite_true] using h

@[simp]
theorem coeffOneHom_apply (γ : F.Curve) :
    coeffOneHom F γ = PowerSeries.coeff 1 γ.toPowerSeries := (rfl)

@[simp high]
theorem toPowerSeries_add_𝔾ₐ (γ₁ γ₂ : (𝔾ₐ (R := R)).Curve) :
    (γ₁ + γ₂).toPowerSeries = γ₁.toPowerSeries + γ₂.toPowerSeries := by
  have ha := PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries
    γ₂.constantCoeff_toPowerSeries
  simp [toPowerSeries_add, 𝔾ₐ_toPowerSeries, subst_add ha, subst_X ha]

/-- Base change of curves along a ring homomorphism `φ : R →+* S`. -/
noncomputable def map (φ : R →+* S) : F.Curve →+ (F.map φ).Curve where
  toFun γ :=
    ⟨γ.toPowerSeries.map φ, by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        γ.coeff_zero_toPowerSeries, map_zero]⟩
  map_zero' := Curve.ext <| by simp
  map_add' γ₁ γ₂ := Curve.ext <| by
    have ha := PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries
      γ₂.constantCoeff_toPowerSeries
    simp only [toPowerSeries_add, map_toPowerSeries, PowerSeries.map, MvPowerSeries.map_subst ha]
    congr 1
    funext i
    fin_cases i <;> simp

@[simp]
theorem toPowerSeries_map (φ : R →+* S) (γ : F.Curve) :
    (Curve.map φ γ).toPowerSeries = γ.toPowerSeries.map φ := (rfl)

theorem map_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (Curve.map (F := F) φ) :=
  fun _ _ h ↦ Curve.ext <| PowerSeries.map_injective φ hφ (congrArg Curve.toPowerSeries h)

@[simp]
theorem map_id (γ : F.Curve) : (Curve.map (RingHom.id R) γ : F.Curve) = γ := by
  ext : 1
  simp

@[simp]
theorem map_map (φ : R →+* S) (ψ : S →+* T) (γ : F.Curve) :
    (Curve.map ψ (Curve.map φ γ) : (F.map (ψ.comp φ)).Curve) = Curve.map (ψ.comp φ) γ := by
  ext k
  simp [toPowerSeries_map]

end Curve

/-- The **tautological curve** `γ(T) = T` on a formal group law `F`. -/
noncomputable def tautologicalCurve (F : FormalGroup R) : F.Curve :=
  ⟨PowerSeries.X, PowerSeries.constantCoeff_X⟩

@[simp]
theorem toPowerSeries_tautologicalCurve (F : FormalGroup R) :
    F.tautologicalCurve.toPowerSeries = PowerSeries.X := (rfl)

@[simp]
theorem map_tautologicalCurve (F : FormalGroup R) (φ : R →+* S) :
    Curve.map φ F.tautologicalCurve = (F.map φ).tautologicalCurve := by
  ext : 1
  exact PowerSeries.map_X φ

end FormalGroup

namespace TauCeti

section Hom

variable {R S : Type*} [CommRing R] [CommRing S] {F G H : FormalGroup R}

namespace FormalGroupHom

/-- Push a curve forward along a homomorphism of formal group laws by formal substitution:
`(f_* γ)(T) = f(γ(T))`. -/
noncomputable def mapCurve (f : FormalGroupHom F G) : F.Curve →+ G.Curve where
  toFun γ :=
    ⟨PowerSeries.subst γ.toPowerSeries f.toPowerSeries,
      PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries _ f.zero_constantCoeff⟩
  map_zero' := FormalGroup.Curve.ext <| by
    simp [PowerSeries.subst_zero_of_constantCoeff_zero f.zero_constantCoeff]
  map_add' γ₁ γ₂ := FormalGroup.Curve.ext <| by
    simpa only [FormalGroup.Curve.toPowerSeries_add, FormalGroup.Curve.val_toPoint,
      applyPoint_val, FormalGroup.add_apply] using
      congrArg Subtype.val (f.applyPoint_add γ₁.toPoint γ₂.toPoint)

@[simp]
theorem toPowerSeries_mapCurve (f : FormalGroupHom F G) (γ : F.Curve) :
    (f.mapCurve γ).toPowerSeries = PowerSeries.subst γ.toPowerSeries f.toPowerSeries := (rfl)

@[simp]
theorem mapCurve_tautologicalCurve (f : FormalGroupHom F G) :
    f.mapCurve F.tautologicalCurve = ⟨f.toPowerSeries, f.zero_constantCoeff⟩ := by
  ext : 1
  simp [PowerSeries.X_subst]

@[simp]
theorem id_mapCurve (γ : F.Curve) : (id F).mapCurve γ = γ := by
  ext : 1
  simp [PowerSeries.subst_X γ.hasSubst]

@[simp]
theorem comp_mapCurve (g : FormalGroupHom G H) (f : FormalGroupHom F G) (γ : F.Curve) :
    (g.comp f).mapCurve γ = g.mapCurve (f.mapCurve γ) := by
  ext : 1
  simp [PowerSeries.subst_comp_subst_apply f.hasSubst γ.hasSubst]

theorem map_mapCurve (f : FormalGroupHom F G) (φ : R →+* S) (γ : F.Curve) :
    (f.map φ).mapCurve (FormalGroup.Curve.map φ γ) = FormalGroup.Curve.map φ (f.mapCurve γ) := by
  ext : 1
  rw [toPowerSeries_mapCurve, FormalGroup.Curve.toPowerSeries_map,
    FormalGroup.Curve.toPowerSeries_map, toPowerSeries_mapCurve, map_toPowerSeries]
  exact (PowerSeries.map_subst γ.hasSubst f.toPowerSeries).symm

@[simp]
theorem nsmulHom_mapCurve [F.IsComm] (n : ℕ) (γ : F.Curve) :
    (F.nsmulHom n).mapCurve γ = n • γ := by
  ext : 1
  simp

@[simp]
theorem zsmulHom_mapCurve [F.IsComm] (n : ℤ) (γ : F.Curve) :
    (F.zsmulHom n).mapCurve γ = n • γ := by
  ext : 1
  simp

end FormalGroupHom

namespace FormalGroupIso

/-- An isomorphism of formal group laws induces an isomorphism on their groups of curves. -/
noncomputable def curveEquiv (e : FormalGroupIso F G) : F.Curve ≃+ G.Curve where
  toFun := e.toHom.mapCurve
  invFun := e.invHom.mapCurve
  left_inv γ := by
    rw [← FormalGroupHom.comp_mapCurve, invHom_comp_toHom, FormalGroupHom.id_mapCurve]
  right_inv γ := by
    rw [← FormalGroupHom.comp_mapCurve, toHom_comp_invHom, FormalGroupHom.id_mapCurve]
  map_add' := map_add e.toHom.mapCurve

@[simp]
theorem curveEquiv_apply (e : FormalGroupIso F G) (γ : F.Curve) :
    e.curveEquiv γ = e.toHom.mapCurve γ := (rfl)

@[simp]
theorem curveEquiv_symm_apply (e : FormalGroupIso F G) (γ : G.Curve) :
    e.curveEquiv.symm γ = e.invHom.mapCurve γ := (rfl)

@[simp]
theorem curveEquiv_refl (F : FormalGroup R) :
    (refl F).curveEquiv = AddEquiv.refl F.Curve := by
  ext γ : 1
  simp

@[simp]
theorem curveEquiv_trans (f : FormalGroupIso F G) (g : FormalGroupIso G H) :
    (f.trans g).curveEquiv = f.curveEquiv.trans g.curveEquiv := by
  ext γ : 1
  simp [trans_toHom]

@[simp]
theorem curveEquiv_symm (f : FormalGroupIso F G) :
    f.symm.curveEquiv = f.curveEquiv.symm := by
  ext γ : 1
  simp

end FormalGroupIso

end Hom

end TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Cartier's Verschiebung operator -/

/-- **Cartier's Verschiebung operator** `V_n` on curves of a formal group law `F`, sending
`γ(T)` to `(V_n γ)(T) = γ(Tⁿ)` (`PowerSeries.expand n`). -/
noncomputable def verschiebungCurve (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) :
    F.Curve →+ F.Curve where
  toFun γ := ⟨PowerSeries.expand n hn γ.toPowerSeries, by simp⟩
  map_zero' := Curve.ext (by simp)
  map_add' γ₁ γ₂ := Curve.ext <| by
    have ha := PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries
      γ₂.constantCoeff_toPowerSeries
    simp only [Curve.toPowerSeries_add, PowerSeries.expand_apply, PowerSeries.subst_def,
      subst_comp_subst_apply ha (PowerSeries.HasSubst.X_pow hn).const]
    congr 1
    funext i
    fin_cases i <;> simp

@[simp]
theorem toPowerSeries_verschiebungCurve (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) (γ : F.Curve) :
    (F.verschiebungCurve n hn γ).toPowerSeries = PowerSeries.expand n hn γ.toPowerSeries :=
  (rfl)

@[simp]
theorem verschiebungCurve_one (F : FormalGroup R) (γ : F.Curve) :
    F.verschiebungCurve 1 one_ne_zero γ = γ := by
  ext : 1
  simp

theorem verschiebungCurve_verschiebungCurve (F : FormalGroup R) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (γ : F.Curve) :
    F.verschiebungCurve m hm (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve (m * n) (mul_ne_zero hm hn) γ := by
  ext : 1
  exact (PowerSeries.expand_mul m hm n hn γ.toPowerSeries).symm

/-- `V_n γ` has no terms of degree strictly below `n`. -/
theorem coeff_verschiebungCurve_eq_zero_of_lt (F : FormalGroup R) {n k : ℕ} (hn : n ≠ 0)
    (hk : k < n) (γ : F.Curve) :
    PowerSeries.coeff k (F.verschiebungCurve n hn γ).toPowerSeries = 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [← (F.verschiebungCurve n hn γ).constantCoeff_toPowerSeries,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · exact PowerSeries.coeff_expand_of_not_dvd n hn γ.toPowerSeries
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk)

theorem verschiebungCurve_congr (F : FormalGroup R) {m n : ℕ} (h : m = n) (hm : m ≠ 0)
    (hn : n ≠ 0) (γ : F.Curve) :
    F.verschiebungCurve m hm γ = F.verschiebungCurve n hn γ := by
  subst h
  rfl

theorem map_verschiebungCurve (F : FormalGroup R) (φ : R →+* S) (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    Curve.map φ (F.verschiebungCurve n hn γ) =
      (F.map φ).verschiebungCurve n hn (Curve.map φ γ) := by
  ext : 1
  exact PowerSeries.map_expand n hn φ γ.toPowerSeries

theorem _root_.TauCeti.FormalGroupHom.mapCurve_verschiebungCurve {F G : FormalGroup R}
    (f : TauCeti.FormalGroupHom F G) (n : ℕ) (hn : n ≠ 0) (γ : F.Curve) :
    f.mapCurve (F.verschiebungCurve n hn γ) = G.verschiebungCurve n hn (f.mapCurve γ) := by
  ext : 1
  simp only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, toPowerSeries_verschiebungCurve,
    PowerSeries.expand_apply]
  exact (PowerSeries.subst_comp_subst_apply γ.hasSubst (PowerSeries.HasSubst.X_pow hn)
    f.toPowerSeries).symm

/-- Over a `ℚ`-algebra, Verschiebung acts on the formal logarithm of a curve by expanding `T ↦ Tⁿ`:
`log_F((V_n γ)(T)) = (log_F(γ(T)))(Tⁿ)`. -/
theorem subst_verschiebungCurve_log [Algebra ℚ R] (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    PowerSeries.subst (F.verschiebungCurve n hn γ).toPowerSeries F.log =
      PowerSeries.expand n hn (PowerSeries.subst γ.toPowerSeries F.log) := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    toPowerSeries_verschiebungCurve] using
    congrArg Curve.toPowerSeries (F.logHom.mapCurve_verschiebungCurve n hn γ)

/-! ### Cartier's Frobenius operator -/

section FrobeniusSetup

private theorem constantCoeff_val_sum_coordPointHom (F : FormalGroup R) [F.IsComm] {σ : Type*}
    [Fintype σ] (γ : F.Curve) :
    constantCoeff (∑ i : σ, Curve.coordPointHom F i γ).val = 0 := by
  refine Finset.sum_induction _ (fun x : F.Point σ ↦ constantCoeff x.val = 0)
    (fun x y hx hy ↦ ?_) (by simp) (fun i _ ↦ ?_)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun j ↦ by
      fin_cases j <;> assumption) (fun j ↦ by fin_cases j <;> assumption) F.zero_constantCoeff
  · rw [Curve.val_coordPointHom, PowerSeries.toMvPowerSeries_apply, constantCoeff_rename]
    exact γ.constantCoeff_toPowerSeries

/-- **Cartier's Frobenius operator** `f_n` on curves of a commutative formal group law `F`: the
formal-group sum `γ(T₁) +_F ⋯ +_F γ(Tₙ)` is symmetric in `T₁, …, Tₙ`, and evaluating its elementary
symmetric expansion at `e₁ = ⋯ = e_{n-1} = 0` and `eₙ = (-1)^(n-1) T` produces `(f_n γ)(T)`. -/
noncomputable def frobeniusCurve (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : n ≠ 0) :
    F.Curve →+ F.Curve where
  toFun γ :=
    ⟨symmetricSubalgebra.evalTopEsymm (Fin n) R
      ⟨(∑ i : Fin n, Curve.coordPointHom F i γ).val,
        (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom γ)⟩, by
      rw [symmetricSubalgebra.constantCoeff_evalTopEsymm]
      exact constantCoeff_val_sum_coordPointHom F γ⟩
  map_zero' := Curve.ext <| by
    have h0 : (⟨(∑ i : Fin n, Curve.coordPointHom F i 0).val,
        (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom (F := F) 0)⟩ :
        symmetricSubalgebra (Fin n) R) = 0 :=
      Subtype.ext (by simp [zero_apply])
    exact (congrArg (symmetricSubalgebra.evalTopEsymm (Fin n) R) h0).trans (map_zero _)
  map_add' γ₁ γ₂ := Curve.ext <| by
    let : NeZero n := ⟨hn⟩
    let s₁ : symmetricSubalgebra (Fin n) R :=
      ⟨(∑ i : Fin n, Curve.coordPointHom F i γ₁).val,
        (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom γ₁)⟩
    let s₂ : symmetricSubalgebra (Fin n) R :=
      ⟨(∑ i : Fin n, Curve.coordPointHom F i γ₂).val,
        (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom γ₂)⟩
    let s : Fin 2 → symmetricSubalgebra (Fin n) R := ![s₁, s₂]
    have hs0 : ∀ j, constantCoeff (s j).1 = 0 := fun j ↦ by
      fin_cases j
      · exact constantCoeff_val_sum_coordPointHom F γ₁
      · exact constantCoeff_val_sum_coordPointHom F γ₂
    have hv : (∑ i : Fin n, Curve.coordPointHom F i (γ₁ + γ₂)).val =
        F.toPowerSeries.subst (fun t ↦ (s t).1) := by
      simp only [map_add, Finset.sum_add_distrib, add_apply]
      congr 1
      funext j
      fin_cases j <;> simp [s, s₁, s₂]
    have hsum : (⟨(∑ i : Fin n, Curve.coordPointHom F i (γ₁ + γ₂)).val,
        (mem_symmetricSubalgebra _).mpr
          (Curve.isSymmetric_val_sum_coordPointHom (γ₁ + γ₂))⟩ :
        symmetricSubalgebra (Fin n) R) =
        ⟨F.toPowerSeries.subst (fun t ↦ (s t).1),
          (mem_symmetricSubalgebra _).mpr <|
            IsSymmetric.subst (hasSubst_of_constantCoeff_zero hs0)
              (fun j ↦ symmetricSubalgebra.isSymmetric (s j))⟩ := Subtype.ext hv
    dsimp only [Curve.toPowerSeries_add]
    refine (congrArg (symmetricSubalgebra.evalTopEsymm (Fin n) R) hsum).trans ?_
    rw [symmetricSubalgebra.evalTopEsymm_subst F.toPowerSeries s hs0]
    congr 1
    funext j
    fin_cases j <;> simp [s, s₁, s₂]

@[simp]
theorem toPowerSeries_frobeniusCurve (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    (F.frobeniusCurve n hn γ).toPowerSeries =
      symmetricSubalgebra.evalTopEsymm (Fin n) R
        ⟨(∑ i : Fin n, Curve.coordPointHom F i γ).val,
          (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom γ)⟩ :=
  (rfl)

theorem frobeniusCurve_congr (F : FormalGroup R) [F.IsComm] {m n : ℕ} (h : m = n) (hm : m ≠ 0)
    (hn : n ≠ 0) (γ : F.Curve) :
    F.frobeniusCurve m hm γ = F.frobeniusCurve n hn γ := by
  subst h
  rfl

theorem map_frobeniusCurve (F : FormalGroup R) [F.IsComm] (φ : R →+* S) (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    Curve.map φ (F.frobeniusCurve n hn γ) =
      (F.map φ).frobeniusCurve n hn (Curve.map φ γ) := by
  ext : 1
  rw [Curve.toPowerSeries_map, toPowerSeries_frobeniusCurve, toPowerSeries_frobeniusCurve,
    symmetricSubalgebra.map_evalTopEsymm]
  have hsum_eq :
      F.mapPointHom φ (Fin n) (∑ i : Fin n, Curve.coordPointHom F i γ) =
        ∑ i : Fin n, Curve.coordPointHom (F.map φ) i (Curve.map φ γ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Subtype.ext ?_
    rw [val_mapPointHom, Curve.val_coordPointHom, Curve.val_coordPointHom, Curve.toPowerSeries_map]
    exact PowerSeries.map_toMvPowerSeries φ i γ.toPowerSeries
  have hval : MvPowerSeries.map φ (∑ i : Fin n, Curve.coordPointHom F i γ).val =
      (∑ i : Fin n, Curve.coordPointHom (F.map φ) i (Curve.map φ γ)).val :=
    (val_mapPointHom F φ (∑ i : Fin n, Curve.coordPointHom F i γ)).symm.trans
      (congrArg Subtype.val hsum_eq)
  exact congrArg (symmetricSubalgebra.evalTopEsymm (Fin n) S) (Subtype.ext hval)

theorem _root_.TauCeti.FormalGroupHom.mapCurve_frobeniusCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (n : ℕ) (hn : n ≠ 0) (γ : F.Curve) :
    f.mapCurve (F.frobeniusCurve n hn γ) = G.frobeniusCurve n hn (f.mapCurve γ) := by
  let : NeZero n := ⟨hn⟩
  ext : 1
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, toPowerSeries_frobeniusCurve,
    toPowerSeries_frobeniusCurve, PowerSeries.subst_def]
  let s : symmetricSubalgebra (Fin n) R :=
    ⟨(∑ i : Fin n, Curve.coordPointHom F i γ).val,
      (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom γ)⟩
  have hpoint : f.toAddMonoidHom (Fin n) (∑ i : Fin n, Curve.coordPointHom F i γ) =
      ∑ i : Fin n, Curve.coordPointHom G i (f.mapCurve γ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Subtype.ext ?_
    rw [TauCeti.FormalGroupHom.toAddMonoidHom_apply, TauCeti.FormalGroupHom.applyPoint_val,
      Curve.val_coordPointHom, Curve.val_coordPointHom,
      TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
      PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.toMvPowerSeries_eq_subst,
      PowerSeries.subst_comp_subst_apply γ.hasSubst (PowerSeries.HasSubst.X (S := R) i)]
  have hv : (∑ i : Fin n, Curve.coordPointHom G i (f.mapCurve γ)).val =
      MvPowerSeries.subst (fun _ : Unit ↦ s.1) f.toPowerSeries := by
    rw [← hpoint, TauCeti.FormalGroupHom.toAddMonoidHom_apply,
      TauCeti.FormalGroupHom.applyPoint_val, PowerSeries.subst_def]
  have hsub : (⟨(∑ i : Fin n, Curve.coordPointHom G i (f.mapCurve γ)).val,
      (mem_symmetricSubalgebra _).mpr
        (Curve.isSymmetric_val_sum_coordPointHom (f.mapCurve γ))⟩ :
      symmetricSubalgebra (Fin n) R) =
      ⟨MvPowerSeries.subst (fun _ : Unit ↦ s.1) f.toPowerSeries,
        (mem_symmetricSubalgebra _).mpr <|
          IsSymmetric.subst
            (hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_val_sum_coordPointHom F γ)
            (fun _ ↦ Curve.isSymmetric_val_sum_coordPointHom γ)⟩ :=
    Subtype.ext hv
  exact (symmetricSubalgebra.evalTopEsymm_subst f.toPowerSeries
    (fun _ : Unit ↦ s)
    (fun _ ↦ constantCoeff_val_sum_coordPointHom F γ)).symm.trans
    (congrArg (symmetricSubalgebra.evalTopEsymm (Fin n) R) hsub.symm)

/-- On the additive formal group law `𝔾ₐ`, Cartier's Frobenius operator `f_n` multiplies the
residue-zero Cartier component by `n`: `(f_n γ)(T) = ∑_{k ≥ 1} n γ_{nk} Tᵏ`. -/
@[simp high]
theorem toPowerSeries_frobeniusCurve_𝔾ₐ (n : ℕ) (hn : n ≠ 0) (γ : (𝔾ₐ (R := R)).Curve) :
    ((𝔾ₐ (R := R)).frobeniusCurve n hn γ).toPowerSeries =
      (n : R) • PowerSeries.cartier R n 0 γ.toPowerSeries := by
  let : NeZero n := ⟨hn⟩
  have hpt : ∀ s : Finset (Fin n),
      (∑ i ∈ s, Curve.coordPointHom (𝔾ₐ (R := R)) i γ).val =
        ∑ i ∈ s, γ.toPowerSeries.toMvPowerSeries i := fun s ↦ by
    induction s using Finset.induction_on with
    | empty => simp [zero_apply]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, 𝔾ₐ_toPowerSeries]
      have hxy : HasSubst ![(Curve.coordPointHom (𝔾ₐ (R := R)) a γ).val,
          (∑ i ∈ s, Curve.coordPointHom (𝔾ₐ (R := R)) i γ).val] :=
        hasSubst_of_constantCoeff_nilpotent fun j ↦ by
          fin_cases j
          · exact (Curve.coordPointHom (𝔾ₐ (R := R)) a γ).prop
          · exact (∑ i ∈ s, Curve.coordPointHom (𝔾ₐ (R := R)) i γ).prop
      rw [subst_add hxy, subst_X hxy, subst_X hxy]
      simp [ih]
  rw [toPowerSeries_frobeniusCurve]
  have hsub : (⟨(∑ i : Fin n, Curve.coordPointHom (𝔾ₐ (R := R)) i γ).val,
      (mem_symmetricSubalgebra _).mpr (Curve.isSymmetric_val_sum_coordPointHom γ)⟩ :
      symmetricSubalgebra (Fin n) R) =
      ⟨∑ i : Fin n, γ.toPowerSeries.toMvPowerSeries i,
        (mem_symmetricSubalgebra _).mpr (IsSymmetric.sum_toMvPowerSeries γ.toPowerSeries)⟩ :=
    Subtype.ext (hpt Finset.univ)
  refine (congrArg (symmetricSubalgebra.evalTopEsymm (Fin n) R) hsub).trans ?_
  rw [symmetricSubalgebra.evalTopEsymm_sum_toMvPowerSeries, Fintype.card_fin]

/-- Over a `ℚ`-algebra, Frobenius acts on the formal logarithm of a curve by selecting degrees
divisible by `n` and multiplying by `n`:
`log_F((f_n γ)(T)) = n • cartier R n 0 (log_F(γ(T)))`. -/
theorem subst_frobeniusCurve_log [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    PowerSeries.subst (F.frobeniusCurve n hn γ).toPowerSeries F.log =
      (n : R) • PowerSeries.cartier R n 0 (PowerSeries.subst γ.toPowerSeries F.log) := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    toPowerSeries_frobeniusCurve_𝔾ₐ] using
    congrArg Curve.toPowerSeries (F.logHom.mapCurve_frobeniusCurve n hn γ)

end FrobeniusSetup

/-! ### Lifting of curves and Cartier's operator identities -/

private theorem isUnit_map_submonoidClosure_natCast {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) {M₀ : Set ℕ} (hM₀ : ∀ n ∈ M₀, IsUnit (n : B))
    (m : Submonoid.closure ((Nat.cast : ℕ → A) '' M₀)) : IsUnit (f m) := by
  refine Submonoid.closure_induction (fun x hx ↦ ?_) (by simp)
    (fun x y _ _ hx hy ↦ by rw [map_mul]; exact hx.mul hy) m.2
  rcases hx with ⟨n, hnM, rfl⟩
  simpa only [map_natCast] using hM₀ n hnM

private theorem isLocalization_lift_injective_of_injective {A B : Type*} [CommRing A] [CommRing B]
    {M : Submonoid A} {f : A →+* B} (hf : Function.Injective f) (hM : ∀ m : M, IsUnit (f m)) :
    Function.Injective (IsLocalization.lift (M := M) (S := Localization M) hM) :=
  (IsLocalization.lift_injective_iff hM).mpr fun _ _ ↦
    ⟨IsLocalization.eq_of_eq (S := Localization M) hM,
      fun h ↦ congrArg (algebraMap A (Localization M)) (hf h)⟩

/-- **Lifting of curves**: for any commutative formal group law `F` over `R`, any curve `γ` on `F`,
and any set `S` of nonzero natural numbers whose images in `R` are units, `(F, γ)` arises by base
change along `π : A →+* R` from a pair `(F₀, γ₀)` over a commutative ring `A` in which every `n ∈ S`
is a unit and which admits an injective ring homomorphism into a `ℚ`-algebra `Q`. -/
theorem Curve.exists_lift_of_isUnit_natCast (F : FormalGroup R) [F.IsComm] (γ : F.Curve)
    (S : Set ℕ) (hS0 : ∀ n ∈ S, n ≠ 0) (hSR : ∀ n ∈ S, IsUnit (n : R)) :
    ∃ (A Q : Type) (_ : CommRing A) (_ : CommRing Q) (_ : Algebra ℚ Q)
      (j : A →+* Q) (_ : Function.Injective j) (_ : ∀ n ∈ S, IsUnit (n : A))
      (F₀ : FormalGroup A) (_ : F₀.IsComm) (γ₀ : F₀.Curve)
      (π : A →+* R) (e : TauCeti.FormalGroupIso (F₀.map π) F),
      e.toHom.mapCurve (Curve.map π γ₀) = γ := by
  -- Step 1: Adjoin polynomial curve coefficients `X₁, X₂, …` over the Lazard ring and embed the
  -- resulting ring `U` injectively into the `ℚ`-algebra `Q = ℚ[b₁, b₂, …][X₀, X₁, …]`.
  let U : Type := MvPolynomial ℕ TauCeti.LazardRing
  let Q : Type := MvPolynomial ℕ (MvPolynomial ℕ+ ℚ)
  let j₀ : TauCeti.LazardRing →+* MvPolynomial ℕ+ ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp TauCeti.LazardRing.mvPolynomialEquiv.symm.toRingHom
  have hj₀ : Function.Injective j₀ :=
    (MvPolynomial.map_injective _ Int.cast_injective).comp
      TauCeti.LazardRing.mvPolynomialEquiv.symm.injective
  let jU : U →+* Q := MvPolynomial.map j₀
  have hjU : Function.Injective jU := MvPolynomial.map_injective j₀ hj₀
  -- Step 2: Localize `U` at the submonoid `M` generated by `S` so every `n ∈ S` becomes a unit in
  -- `A = Localization M`, and lift `jU` to an injective ring homomorphism `j : A →+* Q`.
  let M : Submonoid U := Submonoid.closure ((Nat.cast : ℕ → U) '' S)
  let A : Type := Localization M
  have hjM : ∀ m : M, IsUnit (jU m) :=
    isUnit_map_submonoidClosure_natCast jU fun n hnS ↦ by
      have hq : IsUnit (n : ℚ) := Ne.isUnit (Nat.cast_ne_zero.mpr (hS0 n hnS))
      simpa only [map_natCast] using hq.map (algebraMap ℚ Q)
  let j : A →+* Q := IsLocalization.lift (M := M) (S := A) hjM
  have hj : Function.Injective j := isLocalization_lift_injective_of_injective hjU hjM
  have hSA : ∀ n ∈ S, IsUnit (n : A) := fun n hnS ↦ by
    have hm : (n : U) ∈ M := Submonoid.subset_closure ⟨n, hnS, rfl⟩
    simpa only [map_natCast] using IsLocalization.map_units A ⟨(n : U), hm⟩
  -- Step 3: Base-change Lazard's universal formal group law and the generic curve
  -- `∑_{k ≥ 1} X_k T^k` to `A`, and specialize them to `(F, γ)` along `π : A →+* R`.
  let F_U : FormalGroup U := TauCeti.LazardRing.formalGroup.map MvPolynomial.C
  let γ_U : F_U.Curve :=
    ⟨PowerSeries.mk fun k ↦ if k = 0 then 0 else MvPolynomial.X k,
      by simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]⟩
  let πU : U →+* R :=
    MvPolynomial.eval₂Hom (TauCeti.LazardRing.lift ⟨F, inferInstance⟩)
      (fun k : ℕ ↦ PowerSeries.coeff k γ.toPowerSeries)
  have hπM : ∀ m : M, IsUnit (πU m) := isUnit_map_submonoidClosure_natCast πU hSR
  let π : A →+* R := IsLocalization.lift (M := M) (S := A) hπM
  have hπ_comp : π.comp (algebraMap U A) = πU := IsLocalization.lift_comp hπM
  let F₀ : FormalGroup A := F_U.map (algebraMap U A)
  let γ₀ : F₀.Curve := Curve.map (algebraMap U A) γ_U
  have hF₀ : F₀.map π = F := by
    dsimp only [F₀, F_U]
    rw [FormalGroup.map_comp, hπ_comp, FormalGroup.map_comp]
    have hC : πU.comp MvPolynomial.C = TauCeti.LazardRing.lift ⟨F, inferInstance⟩ :=
      RingHom.ext fun r ↦ MvPolynomial.eval₂Hom_C _ _ r
    rw [hC, TauCeti.LazardRing.map_lift]
  obtain ⟨e, he⟩ : ∃ e : TauCeti.FormalGroupIso (F₀.map π) F,
      e.toHom.toPowerSeries = PowerSeries.X := hF₀ ▸ ⟨.refl _, by simp⟩
  refine ⟨A, Q, inferInstance, inferInstance, inferInstance, j, hj, hSA, F₀, inferInstance, γ₀,
    π, e, ?_⟩
  ext k
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, he,
    PowerSeries.subst_X (Curve.map π γ₀).hasSubst,
    Curve.toPowerSeries_map, Curve.toPowerSeries_map, PowerSeries.coeff_map, PowerSeries.coeff_map,
    ← RingHom.comp_apply, hπ_comp]
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [γ_U]
  · dsimp only [U, γ_U, πU]
    simp [hk0]

section CartierIdentities

/-- Transfer principle for natural curve operators: two operations on curves of commutative formal
group laws that commute with ring base change and formal-group homomorphisms and agree over every
`ℚ`-algebra agree over every commutative ring. -/
private theorem eq_of_ratAlgebra.{u} {R₀ : Type u} [CommRing R₀]
    (Φ Ψ : ∀ {B : Type u} [CommRing B] (G : FormalGroup B) [G.IsComm], G.Curve → G.Curve)
    (hQ : ∀ {B : Type u} [CommRing B] [Algebra ℚ B] (G : FormalGroup B) [G.IsComm] (δ : G.Curve),
      Φ G δ = Ψ G δ)
    (hmap : ∀ {B C : Type u} [CommRing B] [CommRing C] (G : FormalGroup B) [G.IsComm]
      (φ : B →+* C) (δ : G.Curve), Curve.map φ (Φ G δ) = Φ (G.map φ) (Curve.map φ δ))
    (hmap' : ∀ {B C : Type u} [CommRing B] [CommRing C] (G : FormalGroup B) [G.IsComm]
      (φ : B →+* C) (δ : G.Curve), Curve.map φ (Ψ G δ) = Ψ (G.map φ) (Curve.map φ δ))
    (hhom : ∀ {B : Type u} [CommRing B] {G H : FormalGroup B} [G.IsComm] [H.IsComm]
      (f : TauCeti.FormalGroupHom G H) (δ : G.Curve), f.mapCurve (Φ G δ) = Φ H (f.mapCurve δ))
    (hhom' : ∀ {B : Type u} [CommRing B] {G H : FormalGroup B} [G.IsComm] [H.IsComm]
      (f : TauCeti.FormalGroupHom G H) (δ : G.Curve), f.mapCurve (Ψ G δ) = Ψ H (f.mapCurve δ))
    (F : FormalGroup R₀) [F.IsComm] (γ : F.Curve) :
    Φ F γ = Ψ F γ := by
  obtain ⟨A, Q, _, _, _, j, hj, -, F₀, _, γ₀, π, e, rfl⟩ :=
    Curve.exists_lift_of_isUnit_natCast F γ ∅ (by simp) (by simp)
  -- Place `A` and `Q` into `Type u` as rings of functions on `PUnit.{u + 1}`.
  let A' : Type u := PUnit.{u + 1} → A
  let Q' : Type u := PUnit.{u + 1} → Q
  let upA : A →+* A' := RingHom.pi fun _ ↦ RingHom.id A
  let downA : A' →+* A := Pi.evalRingHom (fun _ ↦ A) PUnit.unit
  let j' : A' →+* Q' := RingHom.pi fun p ↦ j.comp (Pi.evalRingHom (fun _ ↦ A) p)
  have hj' : Function.Injective j' := fun _ _ h ↦ funext fun p ↦ hj (congrFun h p)
  let π' : A' →+* R₀ := π.comp downA
  have hcomp : π'.comp upA = π := RingHom.ext fun _ ↦ rfl
  let F₁ : FormalGroup A' := F₀.map upA
  let γ₁ : F₁.Curve := Curve.map upA γ₀
  have hA' : Φ F₁ γ₁ = Ψ F₁ γ₁ := by
    apply Curve.map_injective hj'
    rw [hmap F₁ j' γ₁, hmap' F₁ j' γ₁]
    exact hQ (F₁.map j') (Curve.map j' γ₁)
  have hF₁ : F₀.map π = F₁.map π' := by
    dsimp only [F₁]
    rw [FormalGroup.map_comp, hcomp]
  let f' : TauCeti.FormalGroupHom (F₁.map π') F := e.toHom.ofSourceEq hF₁
  have hγ₁ : f'.mapCurve (Curve.map π' γ₁) = e.toHom.mapCurve (Curve.map π γ₀) := by
    ext : 1
    simp only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, f',
      TauCeti.FormalGroupHom.ofSourceEq_toPowerSeries, Curve.toPowerSeries_map, γ₁]
    congr 1
  rw [← hγ₁, ← hhom f', ← hhom' f', ← hmap F₁ π' γ₁, ← hmap' F₁ π' γ₁, hA']

private theorem frobeniusCurve_one_of_ratAlgebra [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    (γ : F.Curve) : F.frobeniusCurve 1 one_ne_zero γ = γ := by
  apply F.logIso.curveEquiv.injective
  ext k
  simp [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    F.logHom.mapCurve_frobeniusCurve 1 one_ne_zero γ]

private theorem frobeniusCurve_frobeniusCurve_of_ratAlgebra [Algebra ℚ R] (F : FormalGroup R)
    [F.IsComm] {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (γ : F.Curve) :
    F.frobeniusCurve m hm (F.frobeniusCurve n hn γ) =
      F.frobeniusCurve (m * n) (mul_ne_zero hm hn) γ := by
  apply F.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    F.logHom.mapCurve_frobeniusCurve, toPowerSeries_frobeniusCurve_𝔾ₐ, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul, Nat.cast_mul]
  have hmul : n * (m * k) = m * n * k := by ring
  rw [mul_assoc, hmul]

private theorem frobeniusCurve_verschiebungCurve_self_of_ratAlgebra [Algebra ℚ R]
    (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : n ≠ 0) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.verschiebungCurve n hn γ) = n • γ := by
  apply F.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    F.logHom.mapCurve_frobeniusCurve, F.logHom.mapCurve_verschiebungCurve, map_nsmul,
    toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_verschiebungCurve, Curve.toPowerSeries_nsmul,
    nsmulSeries_𝔾ₐ]
  have hsubst : PowerSeries.subst (F.logHom.mapCurve γ).toPowerSeries
      ((n : PowerSeries R) * PowerSeries.X) =
      PowerSeries.C (n : R) * (F.logHom.mapCurve γ).toPowerSeries := by
    have hγ := (F.logHom.mapCurve γ).hasSubst
    have hC : (n : PowerSeries R) = PowerSeries.C (n : R) := map_natCast (PowerSeries.C (R := R)) n
    rw [PowerSeries.subst_mul hγ, PowerSeries.subst_X hγ, ← PowerSeries.coe_substAlgHom hγ,
      map_natCast, hC]
  rw [hsubst, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
    PowerSeries.coeff_expand_mul, PowerSeries.coeff_C_mul, smul_eq_mul]

private theorem frobeniusCurve_verschiebungCurve_of_coprime_of_ratAlgebra [Algebra ℚ R]
    (F : FormalGroup R) [F.IsComm] {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : m.Coprime n)
    (γ : F.Curve) :
    F.frobeniusCurve m hm (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.frobeniusCurve m hm γ) := by
  apply F.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    F.logHom.mapCurve_frobeniusCurve, F.logHom.mapCurve_verschiebungCurve,
    toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_verschiebungCurve, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero, PowerSeries.coeff_expand, smul_eq_mul]
  by_cases hnk : n ∣ k
  · obtain ⟨q, rfl⟩ := hnk
    have hmn : n ∣ m * (n * q) := ⟨m * q, by ring⟩
    have hcomm : m * (n * q) = n * (m * q) := by ring
    rw [ite_eq_left hmn, ite_eq_left ⟨q, rfl⟩,
      Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hn), hcomm,
      Nat.mul_div_cancel_left (m * q) (Nat.pos_of_ne_zero hn)]
  · have hmn : ¬ n ∣ m * k := fun hdvd ↦ hnk (hcop.symm.dvd_of_dvd_mul_left hdvd)
    rw [ite_eq_right hmn, ite_eq_right hnk, mul_zero]

/-- **Cartier's identity `f_1 = id`**: the first Frobenius operator is the identity on curves. -/
@[simp]
theorem frobeniusCurve_one (F : FormalGroup R) [F.IsComm] (γ : F.Curve) :
    F.frobeniusCurve 1 one_ne_zero γ = γ :=
  eq_of_ratAlgebra
    (fun G _ δ ↦ G.frobeniusCurve 1 one_ne_zero δ)
    (fun _ _ δ ↦ δ)
    (fun G _ δ ↦ frobeniusCurve_one_of_ratAlgebra G δ)
    (fun G _ φ δ ↦ G.map_frobeniusCurve φ 1 one_ne_zero δ)
    (fun _ _ _ _ ↦ rfl)
    (fun f δ ↦ f.mapCurve_frobeniusCurve 1 one_ne_zero δ)
    (fun _ _ ↦ rfl)
    F γ

/-- **Cartier's composition law `f_m ∘ f_n = f_{m n}`** on curves of a commutative formal group
law over any commutative ring. -/
theorem frobeniusCurve_frobeniusCurve (F : FormalGroup R) [F.IsComm] {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (γ : F.Curve) :
    F.frobeniusCurve m hm (F.frobeniusCurve n hn γ) =
      F.frobeniusCurve (m * n) (mul_ne_zero hm hn) γ :=
  eq_of_ratAlgebra
    (fun G _ δ ↦ G.frobeniusCurve m hm (G.frobeniusCurve n hn δ))
    (fun G _ δ ↦ G.frobeniusCurve (m * n) (mul_ne_zero hm hn) δ)
    (fun G _ δ ↦ frobeniusCurve_frobeniusCurve_of_ratAlgebra G hm hn δ)
    (fun G _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_frobeniusCurve])
    (fun G _ φ δ ↦ G.map_frobeniusCurve φ (m * n) (mul_ne_zero hm hn) δ)
    (fun f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_frobeniusCurve])
    (fun f δ ↦ f.mapCurve_frobeniusCurve (m * n) (mul_ne_zero hm hn) δ)
    F γ

/-- **Cartier's identity `f_n ∘ V_n = [n]_F`**: Frobenius after Verschiebung of the same index `n`
multiplies curves by `n` in the formal group law, over any commutative ring. -/
theorem frobeniusCurve_verschiebungCurve_self (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : n ≠ 0)
    (γ : F.Curve) :
    F.frobeniusCurve n hn (F.verschiebungCurve n hn γ) = n • γ :=
  eq_of_ratAlgebra
    (fun G _ δ ↦ G.frobeniusCurve n hn (G.verschiebungCurve n hn δ))
    (fun _ _ δ ↦ n • δ)
    (fun G _ δ ↦ frobeniusCurve_verschiebungCurve_self_of_ratAlgebra G n hn δ)
    (fun G _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_verschiebungCurve])
    (fun _ _ φ δ ↦ map_nsmul (Curve.map φ) n δ)
    (fun f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_verschiebungCurve])
    (fun f δ ↦ map_nsmul f.mapCurve n δ)
    F γ

/-- **Cartier's coprime commutation law `f_m ∘ V_n = V_n ∘ f_m`** whenever `gcd(m, n) = 1`, over
any commutative ring. -/
theorem frobeniusCurve_verschiebungCurve_of_coprime (F : FormalGroup R) [F.IsComm] {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hcop : m.Coprime n) (γ : F.Curve) :
    F.frobeniusCurve m hm (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.frobeniusCurve m hm γ) :=
  eq_of_ratAlgebra
    (fun G _ δ ↦ G.frobeniusCurve m hm (G.verschiebungCurve n hn δ))
    (fun G _ δ ↦ G.verschiebungCurve n hn (G.frobeniusCurve m hm δ))
    (fun G _ δ ↦ frobeniusCurve_verschiebungCurve_of_coprime_of_ratAlgebra G hm hn hcop δ)
    (fun G _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_verschiebungCurve])
    (fun G _ φ δ ↦ by rw [G.map_verschiebungCurve, G.map_frobeniusCurve])
    (fun f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_verschiebungCurve])
    (fun f δ ↦ by rw [f.mapCurve_verschiebungCurve, f.mapCurve_frobeniusCurve])
    F γ

end CartierIdentities

end FormalGroup
