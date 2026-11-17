/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.RingTheory.FormalGroup.ZSMul
-- Proof-only: linear topology and completeness on `K⟦X⟧` with discrete `K`.
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.PowerSeries.PiTopology
-- Proof-only: additive formal-parameter homomorphism into points over `K⸨X⸩`.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Hom
-- Proof-only: `W.a₁ ≠ 0 ∨ W.a₃ ≠ 0` for an elliptic curve in characteristic two.
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
-- Proof-only: `IsScalarTower K K⟦X⟧ K⸨X⸩`.
import TauCeti.RingTheory.LaurentSeries.Basic
-- Proof-only: `MvPowerSeries.subst_rename` for reindexing `Unit ⊕ Unit` to `Fin 2`.
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The formal series of multiplication by `n`

For an elliptic curve `W` over a field `K` and an integer `n` for which the multiplication-by-`n`
isogeny `[n] : W → W` is defined (in particular, every `n ≠ 0`), the formal power series
`[n].formalSeries ∈ K⟦X⟧` obtained by expanding `[n]*(-x / y)` in the local parameter `z = -x / y`
equals the formal-group multiplication series `(formalGroup W).zsmulSeries n`.

## Proof strategy

Equip `K` privately with the discrete uniformity and `K⟦X⟧` with the coefficientwise (`X`-adic)
topology, which is complete, Hausdorff, linearly topologised, and `(X)`-adic. For the constant
curve `E = W.map PowerSeries.C` over `K⟦X⟧`:

1. Evaluation of `E.formalAdd` on `(X) ⊂ K⟦X⟧` agrees with `MvPowerSeries.subst` into
   `(formalGroup W).toPowerSeries`, so the `n`-th multiple of the tautological parameter `X` in
   `FormalGroupPoint E (X)` has value `(formalGroup W).zsmulSeries n`.
2. Every nonzero parameter in `(X)` admits an auxiliary parameter of strictly larger `X`-adic
   order that is not fixed by the formal inverse (in characteristic two, ellipticity forces
   `a₁ ≠ 0` or `a₃ ≠ 0`), so `WeierstrassCurve.formalPointHom` yields an additive homomorphism
   `FormalGroupPoint E (X) →+ (E.baseChange K⸨X⸩).toAffine.Point`.
3. Under the identification `E.baseChange K⸨X⸩ = W.baseChange K⸨X⸩`, `formalPointHom` sends `X`
   to the Laurent expansion of the generic point of `W`. By additivity, it sends `n • X` to
   `n • genericPoint = [n]*(genericPoint)` mapped into `K⸨X⸩`. Reading `-x / y` on both sides
   identifies `(formalGroup W).zsmulSeries n` with `[n].formalSeries`.

## Main results

* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`: for any `n` with `ψₙ ≠ 0` at the generic point,
  `(mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`: the same statement for every `n ≠ 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

section PrivateHelpers

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology Topology

variable {K : Type*} [Field K] [UniformSpace K] [DiscreteUniformity K]

/-- With the discrete topology on `K`, the coefficientwise topology on `K⟦X⟧` is `(X)`-adic. -/
private theorem isAdic_span_X : IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}) := by
  rw [isAdic_iff]
  have hmem (n : ℕ) (f : K⟦X⟧) :
      f ∈ Ideal.span {(PowerSeries.X : K⟦X⟧)} ^ n ↔ ∀ k < n, PowerSeries.coeff k f = 0 := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have hset : ((Ideal.span {(PowerSeries.X : K⟦X⟧)} ^ n : Ideal K⟦X⟧) : Set K⟦X⟧) =
        ⋂ k : Fin n, PowerSeries.coeff (k : ℕ) ⁻¹' {(0 : K)} := by
      ext f
      simp [hmem, Fin.forall_iff]
    rw [hset]
    exact isOpen_iInter_of_finite fun k ↦
      (isOpen_discrete _).preimage (PowerSeries.WithPiTopology.continuous_coeff K k)
  · obtain ⟨⟨J, d⟩, -, hJd⟩ :=
      (MvPowerSeries.LinearTopology.hasBasis_nhds_zero (σ := Unit) (R := K)).mem_iff.mp hs
    refine ⟨d () + 1, fun f hf ↦ hJd ?_⟩
    rw [SetLike.mem_coe, MvPowerSeries.LinearTopology.mem_basis_iff]
    intro e he
    have hcoeff : MvPowerSeries.coeff e f = 0 := by
      have heq : e = Finsupp.single () (e ()) := by ext; simp
      rw [heq]
      exact (hmem _ f).mp hf (e ()) (Nat.lt_succ_of_le (he ()))
    rw [hcoeff]
    exact J.zero_mem

/-- Evaluating a `K`-coefficient multivariate power series mapped along `PowerSeries.C` at a family
of series with zero constant term agrees with `MvPowerSeries.subst`. -/
private theorem eval₂_id_map_C {σ : Type*} [Finite σ] {a : σ → K⟦X⟧}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ K) :
    MvPowerSeries.eval₂ (RingHom.id K⟦X⟧) a (MvPowerSeries.map PowerSeries.C f) =
      MvPowerSeries.subst a f := by
  have hI : IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}) := isAdic_span_X
  have ha_eval : MvPowerSeries.HasEval a :=
    MvPowerSeries.hasEval_of_finite_of_isTopologicallyNilpotent fun i ↦
      hI.isTopologicallyNilpotent_of_mem
        (Ideal.mem_span_singleton.mpr (PowerSeries.X_dvd_iff.mpr (ha i)))
  have hmap_cont : Continuous (MvPowerSeries.map (σ := σ) (PowerSeries.C (R := K))) :=
    continuous_pi fun d ↦
      (continuous_of_discreteTopology (f := PowerSeries.C (R := K))).comp
        (MvPowerSeries.WithPiTopology.continuous_coeff K d)
  have huniq := MvPowerSeries.eval₂_unique (φ := PowerSeries.C (R := K)) (a := a)
    continuous_of_discreteTopology ha_eval
    ((MvPowerSeries.continuous_eval₂ (φ := RingHom.id K⟦X⟧) continuous_id ha_eval).comp hmap_cont)
    (fun p ↦ by
      have hmap_p : MvPowerSeries.map PowerSeries.C (p : MvPowerSeries σ K) =
          (MvPolynomial.map PowerSeries.C p : MvPowerSeries σ K⟦X⟧) := by
        ext d
        simp [MvPolynomial.coeff_map]
      -- Unfold function composition to apply `hmap_p` before `eval₂_coe`.
      change MvPowerSeries.eval₂ (RingHom.id K⟦X⟧) a (MvPowerSeries.map PowerSeries.C p) = _
      rw [hmap_p, MvPowerSeries.eval₂_coe, MvPolynomial.eval₂_map, RingHom.id_comp])
  have heq : MvPowerSeries.eval₂ (RingHom.id K⟦X⟧) a (MvPowerSeries.map PowerSeries.C f) =
      MvPowerSeries.eval₂ (PowerSeries.C (R := K)) a f :=
    congrFun huniq f
  rw [heq, MvPowerSeries.subst_eq_eval₂]
  rfl

/-- Evaluating `(W.map PowerSeries.C).formalAdd` on two series of zero constant term computes
substitution into `(formalGroup W).toPowerSeries`. -/
private theorem formalAddEval_map_C_eq_subst (W : WeierstrassCurve K) {f g : K⟦X⟧}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    (W.map PowerSeries.C).formalAddEval f g =
      MvPowerSeries.subst ![f, g] (formalGroup W).toPowerSeries := by
  rw [WeierstrassCurve.formalAddEval_def, WeierstrassCurve.map_formalAdd,
    eval₂_id_map_C (by rintro (_ | _) <;> assumption),
    WeierstrassCurve.formalGroup_toPowerSeries,
    MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> assumption)]
  congr 1
  funext s
  rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp

/-- The `n`-th multiple of the tautological parameter `X` in `FormalGroupPoint (W.map C) (X)` has
underlying power series `(formalGroup W).zsmulSeries n`. -/
private theorem val_zsmul_X_formalGroupPoint (W : WeierstrassCurve K)
    [Fact (IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}))] (n : ℤ) :
    (n • (⟨PowerSeries.X, Ideal.subset_span rfl⟩ :
      FormalGroupPoint (W.map PowerSeries.C) (Ideal.span {(PowerSeries.X : K⟦X⟧)}))).val =
        (formalGroup W).zsmulSeries n := by
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  let φ : FormalGroupPoint (W.map PowerSeries.C) I →+ (formalGroup W).Point Unit :=
    { toFun := fun P ↦ ⟨P.val, PowerSeries.HasSubst.of_constantCoeff_zero
        (PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp P.property))⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun P Q ↦ Subtype.ext <| formalAddEval_map_C_eq_subst W
        (PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp P.property))
        (PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp Q.property)) }
  have hX : φ ⟨PowerSeries.X, Ideal.subset_span rfl⟩ = (formalGroup W).tautologicalPoint :=
    Subtype.ext (FormalGroup.val_tautologicalPoint (formalGroup W)).symm
  have hmul := congrArg Subtype.val (map_zsmul φ n ⟨PowerSeries.X, Ideal.subset_span rfl⟩)
  rw [hX, ← (formalGroup W).subst_zsmulSeries, FormalGroup.val_tautologicalPoint,
    PowerSeries.X_subst] at hmul
  exact hmul

/-- For an elliptic curve `W`, no positive power `X ^ k` is fixed by the formal inverse of
`W.map PowerSeries.C`. -/
private theorem X_pow_ne_formalInverseEval (W : WeierstrassCurve K) [W.IsElliptic]
    {k : ℕ} (hk0 : k ≠ 0) :
    (PowerSeries.X ^ k : K⟦X⟧) ≠ (W.map PowerSeries.C).formalInverseEval (PowerSeries.X ^ k) := by
  set E := W.map (PowerSeries.C (R := K))
  set u : K⟦X⟧ := PowerSeries.X ^ k
  have huI : u ∈ Ideal.span {(PowerSeries.X : K⟦X⟧)} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self _ hk0)
  have hu0 : u ≠ 0 := pow_ne_zero k PowerSeries.X_ne_zero
  have hE : PowerSeries.HasEval u := isAdic_span_X.isTopologicallyNilpotent_of_mem huI
  intro hfix
  have hmul := E.formalInverseEval_mul_formalInverseDenomEval hE
  rw [← hfix, E.formalInverseDenomEval_eq hE] at hmul
  have h2eq : (2 : K⟦X⟧) = PowerSeries.C W.a₁ * u + PowerSeries.C W.a₃ * E.formalWEval u := by
    apply mul_left_cancel₀ hu0
    rw [show E.a₁ = PowerSeries.C W.a₁ from rfl, show E.a₃ = PowerSeries.C W.a₃ from rfl] at hmul
    linear_combination hmul
  have hw_eq := E.formalWEval_eq_pow_mul_formalUEval hE
  have hw_dvd : PowerSeries.X ^ (3 * k) ∣ E.formalWEval u := by
    rw [hw_eq, show u ^ 3 = PowerSeries.X ^ (3 * k) by simp [u, ← pow_mul, mul_comm]]
    exact dvd_mul_right _ _
  have h2 : (2 : K) = 0 := by
    have h0 := congrArg (PowerSeries.coeff 0) h2eq
    have hcw0 : PowerSeries.constantCoeff (E.formalWEval u) = 0 :=
      PowerSeries.coeff_zero_eq_constantCoeff_apply (E.formalWEval u) ▸
        PowerSeries.X_pow_dvd_iff.mp hw_dvd 0 (by omega)
    simpa [u, zero_pow hk0, PowerSeries.coeff_C_mul, hcw0,
      show (2 : K⟦X⟧) = PowerSeries.C 2 from rfl] using h0
  have ha₁ : W.a₁ = 0 := by
    have hk := congrArg (PowerSeries.coeff k) h2eq
    have hckw : PowerSeries.coeff k (E.formalWEval u) = 0 :=
      PowerSeries.X_pow_dvd_iff.mp hw_dvd k (by omega)
    simpa [u, PowerSeries.coeff_C_mul, PowerSeries.coeff_C, hk0, hk0.symm, hckw,
      show (2 : K⟦X⟧) = PowerSeries.C 2 from rfl] using hk.symm
  have ha₃ : W.a₃ ≠ 0 :=
    (W.a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero_of_two_eq_zero W.isUnit_Δ.ne_zero h2).resolve_left
      (not_not.mpr ha₁)
  have h2zero : (2 : K⟦X⟧) = 0 := by
    rw [show (2 : K⟦X⟧) = PowerSeries.C 2 from rfl, h2, map_zero]
  rw [h2zero, ha₁, map_zero, zero_mul, zero_add] at h2eq
  have hwu0 : E.formalWEval u ≠ 0 := by
    rw [hw_eq]
    exact mul_ne_zero (pow_ne_zero 3 hu0) (E.isUnit_formalUEval hE).ne_zero
  exact (mul_ne_zero (by simp [ha₃]) hwu0) h2eq.symm

/-- In `FormalGroupPoint (W.map C) (X)` for an elliptic curve `W`, every parameter distinct from
its inverse admits an auxiliary parameter distinct from it, its inverse, and its own inverse. -/
private theorem exists_aux_formalGroupPoint (W : WeierstrassCurve K) [W.IsElliptic]
    [Fact (IsAdic (Ideal.span {(PowerSeries.X : K⟦X⟧)}))]
    (P : FormalGroupPoint (W.map PowerSeries.C) (Ideal.span {(PowerSeries.X : K⟦X⟧)}))
    (hP : P ≠ -P) :
    ∃ U : FormalGroupPoint (W.map PowerSeries.C) (Ideal.span {(PowerSeries.X : K⟦X⟧)}),
      U ≠ P ∧ U ≠ -P ∧ U ≠ -U := by
  let E := W.map (PowerSeries.C (R := K))
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  have hP0 : P.val ≠ 0 := fun h0 ↦ hP (by
    have hPz : P = 0 := FormalGroupPoint.ext h0
    rw [hPz, neg_zero])
  set k := P.val.order.toNat + 1
  have hk0 : k ≠ 0 := Nat.succ_ne_zero _
  set u : K⟦X⟧ := PowerSeries.X ^ k
  have huI : u ∈ I := Ideal.mem_span_singleton.mpr (dvd_pow_self _ hk0)
  have hP_lt : P.val.order < u.order := by
    rw [PowerSeries.order_X_pow k, ← ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr hP0)]
    exact Nat.cast_lt.mpr (Nat.lt_succ_self _)
  refine ⟨⟨u, huI⟩,
    fun hUP ↦ hP_lt.ne (congrArg (fun Q : FormalGroupPoint E I ↦ Q.val.order) hUP).symm,
    fun hUnP ↦ ?_,
    fun hUu ↦ X_pow_ne_formalInverseEval W hk0 (congrArg FormalGroupPoint.val hUu)⟩
  have hE : PowerSeries.HasEval P.val := P.hasEval
  have hunit_ord : (E.formalInverseDenomInvEval P.val).order = 0 :=
    not_ne_iff.mp (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.not.mpr
      (PowerSeries.isUnit_iff_constantCoeff.mp
        (E.isUnit_formalInverseDenomInvEval hE)).ne_zero)
  have hord_neg : (-P).val.order = P.val.order := by
    rw [FormalGroupPoint.coe_neg, E.formalInverseEval_eq hE, PowerSeries.order_neg,
      PowerSeries.order_mul, hunit_ord, add_zero]
  exact hP_lt.ne (hord_neg ▸ congrArg (fun Q : FormalGroupPoint E I ↦ Q.val.order) hUnP).symm

open scoped Classical in
/-- Transported along `E⁄K⸨X⸩ = W⁄K⸨X⸩`, the formal point attached to `X` is the Laurent expansion
of the generic point of `W`. -/
private theorem formalPoint_X_eq_map_genericPoint (W : WeierstrassCurve K) [W.IsElliptic]
    (hbc : (W.map PowerSeries.C).baseChange K⸨X⸩ = W.baseChange K⸨X⸩)
    [((W.map PowerSeries.C).baseChange K⸨X⸩).IsElliptic]
    [FaithfulSMul K⟦X⟧ K⸨X⸩] [@IsScalarTower K K K⸨X⸩ _ Algebra.toSMul Algebra.toSMul] :
    AddEquiv.cast (M := fun V : WeierstrassCurve K⸨X⸩ ↦ V.toAffine.Point) hbc
      ((W.map PowerSeries.C).formalPoint (K := K⸨X⸩) isAdic_span_X
        (Ideal.subset_span (rfl : (PowerSeries.X : K⟦X⟧) ∈ _))) =
      Affine.Point.map W.functionFieldLaurentExpansion W.toAffine.genericPoint := by
  let E := W.map (PowerSeries.C (R := K))
  set Q₀ := Affine.Point.map W.functionFieldLaurentExpansion W.toAffine.genericPoint
  have hy0 : W.functionFieldLaurentExpansion W.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr W.toAffine.genericY_ne_zero
  have hQ₀0 : Q₀ ≠ 0 := by
    intro h
    have hy := congrArg Affine.Point.yCoord h
    rw [Affine.Point.yCoord_map, Affine.yCoord_genericPoint, Affine.Point.yCoord_zero] at hy
    exact hy0 hy
  have hns : (W.baseChange K⸨X⸩).toAffine.Nonsingular
      (W.functionFieldLaurentExpansion W.toAffine.genericX)
      (W.functionFieldLaurentExpansion W.toAffine.genericY) := by
    simpa only [Q₀, Affine.Point.xCoord_map, Affine.Point.yCoord_map,
      Affine.xCoord_genericPoint, Affine.yCoord_genericPoint] using
        Affine.Point.nonsingular_coords hQ₀0
  have hxt : algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X *
      W.functionFieldLaurentExpansion W.toAffine.genericY =
      -W.functionFieldLaurentExpansion W.toAffine.genericX := by
    have h := W.functionFieldLaurentExpansion_neg_genericX_div_genericY
    rw [map_div₀, map_neg, ← _root_.LaurentSeries.coe_algebraMap] at h
    exact (eq_div_iff hy0).mp h.symm
  have hys : algebraMap K⟦X⟧ K⸨X⸩ W.formalW *
      W.functionFieldLaurentExpansion W.toAffine.genericY = -1 := by
    have h := W.functionFieldLaurentExpansion_neg_inv_genericY
    rw [map_neg, map_inv₀, ← _root_.LaurentSeries.coe_algebraMap] at h
    rw [← h, neg_mul, inv_mul_cancel₀ hy0]
  have hfp : E.formalPoint (K := K⸨X⸩) isAdic_span_X (Ideal.subset_span rfl) =
      Affine.Point.some (W.functionFieldLaurentExpansion W.toAffine.genericX)
        (W.functionFieldLaurentExpansion W.toAffine.genericY) (hbc.symm ▸ hns) :=
    E.formalPoint_eq_some isAdic_span_X (Ideal.subset_span rfl)
      (Ideal.mem_span_singleton.mpr (PowerSeries.X_dvd_iff.mpr W.constantCoeff_formalW))
      (hbc.symm ▸ hns) hxt hys
  rw [AddEquiv.cast_apply, hfp, Affine.Point.cast_some hbc]
  exact Affine.Point.eq_of_coords (by simp) hQ₀0
    (by simp [Q₀, Affine.xCoord_genericPoint]) (by simp [Q₀, Affine.yCoord_genericPoint])

end PrivateHelpers

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology in
/-- **The formal series of multiplication by `n` is the formal-group multiplication series**
(Silverman IV.4): for every `n` with `ψₙ` nonvanishing at the generic point of an elliptic curve
`W`, expanding `[n]*(-x / y)` in `-x / y` yields `(formalGroup W).zsmulSeries n`. -/
@[simp]
theorem formalSeries_mulByIntIsogeny [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  classical
  let _ : UniformSpace K := ⊥
  have : DiscreteUniformity K := ⟨rfl⟩
  let I : Ideal K⟦X⟧ := Ideal.span {(PowerSeries.X : K⟦X⟧)}
  have hI : IsAdic I := isAdic_span_X
  have : Fact (IsAdic I) := ⟨hI⟩
  let E := W.map (PowerSeries.C (R := K))
  have hbc : E.baseChange K⸨X⸩ = W.baseChange K⸨X⸩ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    congr 1
  have : (E.baseChange K⸨X⸩).IsElliptic := hbc ▸ inferInstance
  have : FaithfulSMul K⟦X⟧ K⸨X⸩ :=
    ⟨fun h ↦ HahnSeries.ofPowerSeries_injective <| by
      simpa [Algebra.smul_def, _root_.LaurentSeries.coe_algebraMap] using h 1⟩
  have : @IsScalarTower K K K⸨X⸩ _ Algebra.toSMul Algebra.toSMul :=
    @IsScalarTower.mk K K K⸨X⸩ _ Algebra.toSMul Algebra.toSMul fun c d f ↦ by
      simp only [smul_eq_mul, Algebra.smul_def, map_mul, mul_assoc]
  let e : (E.baseChange K⸨X⸩).toAffine.Point ≃+ (W.baseChange K⸨X⸩).toAffine.Point :=
    AddEquiv.cast (M := fun V : WeierstrassCurve K⸨X⸩ ↦ V.toAffine.Point) hbc
  let haux := exists_aux_formalGroupPoint W
  let P₀ : FormalGroupPoint E I := ⟨PowerSeries.X, Ideal.subset_span rfl⟩
  have hQ₀ : e (E.formalPointHom (S := K⸨X⸩) I haux P₀) =
      Affine.Point.map W.functionFieldLaurentExpansion W.toAffine.genericPoint := by
    rw [E.formalPointHom_apply I]
    exact formalPoint_X_eq_map_genericPoint W hbc
  have hmul : e (E.formalPointHom (S := K⸨X⸩) I haux (n • P₀)) =
      Affine.Point.map W.functionFieldLaurentExpansion
        (Affine.Point.map (mulByIntIsogeny W.toAffine hn).fieldPullback
          W.toAffine.genericPoint) := by
    rw [map_zsmul, map_zsmul, hQ₀, map_mulByIntIsogeny_genericPoint, map_zsmul]
  have hparam := congrArg (fun P : (W.baseChange K⸨X⸩).toAffine.Point ↦ -P.xCoord / P.yCoord) hmul
  rw [AddEquiv.cast_apply, Affine.Point.xCoord_cast hbc, Affine.Point.yCoord_cast hbc,
    E.formalPointHom_apply I,
    E.neg_xCoord_div_yCoord_formalPoint (K := K⸨X⸩) hI (n • P₀).property,
    val_zsmul_X_formalGroupPoint W n, Affine.Point.xCoord_map, Affine.Point.yCoord_map,
    Affine.Point.xCoord_map, Affine.Point.yCoord_map, Affine.xCoord_genericPoint,
    Affine.yCoord_genericPoint, ← map_neg, ← map_div₀, ← map_neg, ← map_div₀,
    _root_.LaurentSeries.coe_algebraMap] at hparam
  exact (formalSeries_eq_iff _ _).mpr hparam

/-- **The formal series of multiplication by `n ≠ 0` is the formal-group multiplication series**,
with the non-vanishing hypothesis discharged from ellipticity as in `mulByIntIsogenyOfNeZero`. -/
-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev`, so `simp` sees through it to
-- `formalSeries_mulByIntIsogeny`.
theorem formalSeries_mulByIntIsogenyOfNeZero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

end TauCeti.Isogeny

end
