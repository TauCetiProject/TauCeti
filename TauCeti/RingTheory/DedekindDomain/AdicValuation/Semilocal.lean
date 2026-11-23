/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension
public import TauCeti.RingTheory.Ideal.PrimesOver
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.Localization.FiniteDimensional
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.NormTrace.Pi
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# The semilocal decomposition of a finite extension of Dedekind domains

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, with `[Module.Finite R B]`, and let
`v` be a height-one prime of `R`. With no finiteness or separability hypothesis on residue fields,
scalar extension along `R → 𝒪_v` and `K → K_v` decomposes as `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w`
(`adicCompletionIntegersSemilocalEquiv`) and `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`
(`adicCompletionSemilocalEquiv`). Hence each `𝒪_w / 𝒪_v` is finite free of rank
`[L_w : K_v] = e(w ∣ v) · f(w ∣ v)`, `𝒪_w` is the integral closure of `𝒪_v` in `L_w`, `L_w / K_v`
is separable when `L / K` is separable, and norms and traces decompose locally. This complements
`AdicValuation.IntegralClosure` and `AdicValuation.LocalDegree`, which assume finite residue
fields. All `HeightOneSpectrum` declarations use `open scoped AdicCompletionExtension`, which
provides the completed algebra structures and the scoped finiteness, freeness, integral-closure,
and separability instances below.

## Main results

* `adicCompletionIntegersSemilocalHom`, `adicCompletionIntegersSemilocalEquiv`,
  `adicCompletionSemilocalHom`, `adicCompletionSemilocalEquiv`,
  `adicCompletionIntegersSemilocalToField`: semilocal maps, isomorphisms, and integral inclusion.
* `moduleFinite_adicCompletionIntegers_of_finite`, `moduleFree_adicCompletionIntegers_of_finite`,
  `isIntegralClosure_adicCompletionIntegers_of_finite`,
  `finiteDimensional_adicCompletion_of_finite`, `isSeparable_adicCompletion_of_isSeparable`.
* `finrank_adicCompletionIntegers_of_finite`, `finrank_adicCompletion_of_finite`,
  `sum_finrank_adicCompletion_of_finite`, `algebraMap_norm_eq_prod_norm_adicCompletion`,
  `algebraMap_trace_eq_sum_trace_adicCompletion`,
  `trace_adicCompletionSemilocalEquiv_symm_single_mul`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §§2–3.
-/

public section
noncomputable section

open TauCeti IsDedekindDomain TensorProduct
open scoped AdicCompletionExtension nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

variable (K B L) in
/-- The canonical `𝒪_v`-algebra map from `𝒪_v ⊗[R] B` to `∏_{w ∣ v} 𝒪_w`. -/
def adicCompletionIntegersSemilocalHom :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[v.adicCompletionIntegers K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        w.val.adicCompletionIntegers L :=
  letI : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      Algebra R (w.val.adicCompletionIntegers L) := fun w ↦
    ((algebraMap (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L)).comp
      (algebraMap R (v.adicCompletionIntegers K))).toAlgebra
  letI : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      IsScalarTower R (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L) :=
    fun _ ↦ .of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.pi fun w ↦
    { algebraMap B (w.val.adicCompletionIntegers L) with
      commutes' := fun r ↦ by
        rw [RingHom.toFun_eq_coe, IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
            (w.val.adicCompletionIntegers L), algebraMap_adicCompletionIntegersExtensionAlgebra,
          adicCompletionIntegersExtension_algebraMap] }) fun _ _ ↦ .all _ _

/-- `adicCompletionIntegersSemilocalHom` sends a pure tensor `a ⊗ b` to `(a · b)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionIntegersSemilocalHom_tmul (a : v.adicCompletionIntegers K) (b : B)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionIntegersSemilocalHom K B L (a ⊗ₜ b) w =
      algebraMap (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L) a *
        algebraMap B (w.val.adicCompletionIntegers L) b := by
  simp [adicCompletionIntegersSemilocalHom]

variable (K B L) in
/-- The canonical `K_v`-algebra map from `K_v ⊗[K] L` to `∏_{w ∣ v} L_w`. -/
def adicCompletionSemilocalHom :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}, w.val.adicCompletion L :=
  letI : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      Algebra K (w.val.adicCompletion L) := fun w ↦
    ((algebraMap (v.adicCompletion K) (w.val.adicCompletion L)).comp
      (algebraMap K (v.adicCompletion K))).toAlgebra
  letI : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun _ ↦ .of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.pi fun w ↦
    { algebraMap L (w.val.adicCompletion L) with
      commutes' := fun x ↦ by
        rw [RingHom.toFun_eq_coe,
          IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.val.adicCompletion L),
          v.algebraMap_adicCompletionExtension_algebraMap w.val] }) fun _ _ ↦ .all _ _

/-- `adicCompletionSemilocalHom` sends a pure tensor `a ⊗ x` to `(a · x)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionSemilocalHom_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionSemilocalHom K B L (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.val.adicCompletion L) a *
        algebraMap L (w.val.adicCompletion L) x := by
  simp [adicCompletionSemilocalHom]

end General

section FiniteExtension

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.Finite R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

/-- **Surjectivity of the integral semilocal map** (with arbitrary residue fields). -/
theorem adicCompletionIntegersSemilocalHom_surjective :
    Function.Surjective (v.adicCompletionIntegersSemilocalHom K B L) := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  let _ : Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  set I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  have : IsPrecomplete I (v.adicCompletionIntegers K ⊗[R] B) := .of_finite I _
  have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      IsHausdorff I (w.val.adicCompletionIntegers L) :=
    .of_map (IsLocalRing.map_maximalIdeal_le
      (algebraMap (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L)))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hI : I = Ideal.span {π} := hπ.maximalIdeal_eq
  refine surjective_of_mkQ_comp_surjective (I := I)
    (f := (v.adicCompletionIntegersSemilocalHom K B L).toLinearMap) fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  let s : Finset (HeightOneSpectrum B) :=
    (Finset.univ : Finset {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}).image (·.val)
  obtain ⟨b, hb⟩ := exists_forall_valued_sub_le (K := L) s
    (fun w ↦ if hw : w.asIdeal.LiesOver v.asIdeal then y ⟨w, hw⟩ else 0)
    (fun w ↦ w.asIdeal.ramificationIdx R)
  refine ⟨1 ⊗ₜ b, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have hsub (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      ∃ q : w.val.adicCompletionIntegers L,
        π • q = (v.adicCompletionIntegersSemilocalHom K B L (1 ⊗ₜ b) - y) w := by
    have hbw := hb w.val (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩)
    simp only [dite_eq_left w.property] at hbw
    refine (v.exists_smul_eq_adicCompletionIntegers_iff_valued_le w.val hπ).mpr ?_
    rw [Pi.sub_apply, AddSubgroupClass.coe_sub, adicCompletionIntegersSemilocalHom_tmul, map_one,
      one_mul, Valuation.map_sub_swap,
      ← ValuationSubring.algebraMap_apply (a := algebraMap B (w.val.adicCompletionIntegers L) b),
      ← algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers]
    exact hbw
  choose q hq using hsub
  exact ⟨q, Submodule.mem_top, funext hq⟩

/-- **`𝒪_w` is module-finite over `𝒪_v`** when `B` is finite over `R`. -/
theorem moduleFinite_adicCompletionIntegers_of_finite (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  .of_surjective ((LinearMap.proj (⟨w, inferInstance⟩ :
      {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})).comp
    (v.adicCompletionIntegersSemilocalHom K B L).toLinearMap)
    ((Function.surjective_eval _).comp v.adicCompletionIntegersSemilocalHom_surjective)

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.moduleFinite_adicCompletionIntegers_of_finite

/-- **`𝒪_w` is a free `𝒪_v`-module** when `B` is finite over `R`. -/
theorem moduleFree_adicCompletionIntegers_of_finite (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    Module.Free (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  Module.free_of_finite_type_torsion_free'

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.moduleFree_adicCompletionIntegers_of_finite

/-- **`L_w` is finite-dimensional over `K_v`** when `B` is finite over `R`. -/
theorem finiteDimensional_adicCompletion_of_finite (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
  TauCeti.IsFractionRing.finiteDimensional_of_finite (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L) (v.adicCompletion K) (w.adicCompletion L)

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.finiteDimensional_adicCompletion_of_finite

/-- **`𝒪_w` is the integral closure of `𝒪_v` in `L_w`** when `B` is finite over `R`. -/
theorem isIntegralClosure_adicCompletionIntegers_of_finite (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) := inferInstance

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isIntegralClosure_adicCompletionIntegers_of_finite

private def adicCompletionFieldBaseChangeEquiv :
    v.adicCompletion K ⊗[R] B ≃ₐ[v.adicCompletion K] v.adicCompletion K ⊗[K] L :=
  haveI : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  (Algebra.TensorProduct.cancelBaseChange R K (v.adicCompletion K)
    (v.adicCompletion K) B).symm.trans
    (Algebra.TensorProduct.congr .refl (Algebra.IsPushout.equiv R K B L))

omit [Module.Finite R B] in
private def adicCompletionIntegersTensorToBaseChange :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[R] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (v.adicCompletionIntegers K) _)
    (AlgHom.id R B)

variable (K B L) in
/-- The canonical inclusion `𝒪_v ⊗[R] B →ₐ[R] K_v ⊗[K] L`. -/
def adicCompletionIntegersSemilocalToField :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[K] L :=
  ((v.adicCompletionFieldBaseChangeEquiv (K := K) (B := B) (L := L)).toAlgHom.restrictScalars
    R).comp (v.adicCompletionIntegersTensorToBaseChange (K := K) (B := B))

/-- `adicCompletionIntegersSemilocalToField` sends `a ⊗ b` to `(a : K_v) ⊗ (b : L)`. -/
@[simp]
theorem adicCompletionIntegersSemilocalToField_tmul (a : v.adicCompletionIntegers K) (b : B) :
    v.adicCompletionIntegersSemilocalToField K B L (a ⊗ₜ b) =
      (a : v.adicCompletion K) ⊗ₜ algebraMap B L b := by
  simp [adicCompletionIntegersSemilocalToField, adicCompletionFieldBaseChangeEquiv,
    adicCompletionIntegersTensorToBaseChange, Algebra.IsPushout.equiv_tmul]

private theorem adicCompletionSemilocalHom_toField (z : v.adicCompletionIntegers K ⊗[R] B) :
    v.adicCompletionSemilocalHom K B L (v.adicCompletionIntegersSemilocalToField K B L z) =
      fun w ↦ (v.adicCompletionIntegersSemilocalHom K B L z w : w.val.adicCompletion L) := by
  induction z using TensorProduct.inductionOn with
  | add _ _ hx hy =>
    funext w; simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (congrFun hx w) (congrFun hy w)
  | tmul a b =>
    funext w
    rw [adicCompletionIntegersSemilocalToField_tmul, adicCompletionSemilocalHom_tmul,
      adicCompletionIntegersSemilocalHom_tmul, Subring.coe_mul,
      algebraMap_adicCompletionIntegersExtensionAlgebra, algebraMap_adicCompletionExtensionAlgebra,
      coe_adicCompletionIntegersExtension]; rfl

/-- **Surjectivity of the field semilocal map** (with arbitrary residue fields). -/
theorem adicCompletionSemilocalHom_surjective :
    Function.Surjective (v.adicCompletionSemilocalHom K B L) := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  let _ : Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  intro y
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := ZeroMemClass.coe_eq_zero.not.mpr hπ.ne_zero
  choose N hN using fun w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ↦
    v.exists_forall_pow_smul_mem_adicCompletionIntegers w.val
      ((adicCompletionIntegers.integers K v).valuation_irreducible_lt_one hπ) (y w)
  let M : ℕ := Finset.univ.sup N
  obtain ⟨t, ht⟩ := v.adicCompletionIntegersSemilocalHom_surjective (K := K) (L := L)
    fun w ↦ ⟨_, hN w M (Finset.le_sup (Finset.mem_univ w))⟩
  refine ⟨((π : v.adicCompletion K) ^ M)⁻¹ • v.adicCompletionIntegersSemilocalToField K B L t,
    funext fun w ↦ ?_⟩
  rw [map_smul, Pi.smul_apply, v.adicCompletionSemilocalHom_toField t, ht]
  exact inv_smul_smul₀ (pow_ne_zero M hπ0) (y w)

/-- **The rank of `𝒪_w` over `𝒪_v` is `e(w ∣ v) · f(w ∣ v)`** (with arbitrary residue fields). -/
theorem finrank_adicCompletionIntegers_of_finite (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  classical
  set p := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  set Q := IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hQ0 : Q ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have : NeZero p := ⟨hp0⟩
  have hp_map : p.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) ≠ ⊥ :=
    v.map_maximalIdeal_adicCompletionIntegers_eq_pow (K := K) (L := L) w ▸ pow_ne_zero _ hQ0
  have hs : p.primesOver (w.adicCompletionIntegers L) = {Q} := IsLocalRing.primesOver_eq _ hp0
  rw [← Ideal.sum_ramification_inertia_eq_finrank p (w.adicCompletionIntegers L),
    Finset.sum_eq_single ⟨Q, by rw [hs]; exact Set.mem_singleton _⟩
      (fun P _ hPQ ↦ absurd (Subtype.ext (by simpa [hs] using P.property)) hPQ) (by simp)]
  refine congrArg₂ (· * ·) ?_ (TauCeti.IsLocalRing.inertiaDeg_maximalIdeal.trans
    (v.finrank_residueField_adicCompletionIntegers (K := K) (L := L) w))
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p Q hp_map,
    v.map_maximalIdeal_adicCompletionIntegers_eq_pow (K := K) (L := L) w,
    multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hQ0 inferInstance)]

/-- **The local degree `[L_w : K_v]` is `e(w ∣ v) · f(w ∣ v)`** (with arbitrary residue fields). -/
theorem finrank_adicCompletion_of_finite (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R :=
  (IsFractionRing.finrank_eq (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletionIntegers L) (w.adicCompletion L)).trans
    (v.finrank_adicCompletionIntegers_of_finite (K := K) (L := L) w)

/-- **The sum of the local degrees above `v` equals `[L : K]`.** -/
theorem sum_finrank_adicCompletion_of_finite
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}] :
    (∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.val.adicCompletion L)) = Module.finrank K L := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  let _ : Fintype (v.asIdeal.primesOver B) := Fintype.ofEquiv _ (liesOverEquivPrimesOver B v)
  rw [Finset.sum_congr rfl fun w _ ↦ v.finrank_adicCompletion_of_finite (K := K) (L := L) w.val,
    Fintype.sum_equiv (liesOverEquivPrimesOver B v) _
      (fun P : v.asIdeal.primesOver B ↦ P.val.ramificationIdx R * P.val.inertiaDeg R)
      fun w ↦ by rw [liesOverEquivPrimesOver_apply],
    Ideal.sum_ramification_inertia_eq_finrank v.asIdeal B, IsFractionRing.finrank_eq R K B L]

/-- **Injectivity of the field semilocal map** (with arbitrary residue fields). -/
theorem adicCompletionSemilocalHom_injective :
    Function.Injective (v.adicCompletionSemilocalHom K B L) := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  let _ : Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  have := TauCeti.IsFractionRing.finiteDimensional_of_finite R B K L
  have hfin : Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) =
      Module.finrank (v.adicCompletion K)
        (∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
          w.val.adicCompletion L) := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul, Module.finrank_pi_fintype,
      v.sum_finrank_adicCompletion_of_finite (K := K) (B := B) (L := L)]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr
    (v.adicCompletionSemilocalHom_surjective (K := K) (B := B) (L := L))

variable (K B L) in
/-- **The field semilocal isomorphism** `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`. -/
def adicCompletionSemilocalEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}, w.val.adicCompletion L :=
  -- The `show Function.Bijective ...` ascription is load-bearing: `Function.Bijective` is
  -- semireducible, so without it `AlgEquiv.coe_ofBijective` and `ofBijective_apply` fail to match.
  AlgEquiv.ofBijective (v.adicCompletionSemilocalHom K B L)
    (show Function.Bijective (v.adicCompletionSemilocalHom K B L) from
      ⟨v.adicCompletionSemilocalHom_injective, v.adicCompletionSemilocalHom_surjective⟩)

/-- As a function, `adicCompletionSemilocalEquiv` is `adicCompletionSemilocalHom`. -/
theorem coe_adicCompletionSemilocalEquiv :
    ⇑(v.adicCompletionSemilocalEquiv K B L) = v.adicCompletionSemilocalHom K B L :=
  AlgEquiv.coe_ofBijective ..

/-- As an algebra homomorphism, `adicCompletionSemilocalEquiv` is `adicCompletionSemilocalHom`. -/
theorem toAlgHom_adicCompletionSemilocalEquiv :
    (v.adicCompletionSemilocalEquiv K B L).toAlgHom = v.adicCompletionSemilocalHom K B L :=
  AlgHom.ext fun x ↦ congrFun (v.coe_adicCompletionSemilocalEquiv (K := K) (B := B) (L := L)) x

/-- `adicCompletionSemilocalEquiv` sends a pure tensor `a ⊗ x` to `(a · x)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionSemilocalEquiv_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionSemilocalEquiv K B L (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.val.adicCompletion L) a *
        algebraMap L (w.val.adicCompletion L) x :=
  (congrFun (v.coe_adicCompletionSemilocalEquiv (K := K) (B := B) (L := L)) (a ⊗ₜ x) ▸
    v.adicCompletionSemilocalHom_tmul a x w)

/-- The inverse field semilocal isomorphism sends the diagonal image of `x ∈ L` to `1 ⊗ x`. -/
@[simp]
theorem adicCompletionSemilocalEquiv_symm_algebraMap (x : L) :
    (v.adicCompletionSemilocalEquiv K B L).symm
        (fun w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ↦
          algebraMap L (w.val.adicCompletion L) x) = 1 ⊗ₜ[K] x :=
  (v.adicCompletionSemilocalEquiv K B L).symm_apply_eq.mpr (funext fun w ↦ by simp)

/-- Compatibility of the integral and field semilocal maps under inclusion into the completions. -/
theorem adicCompletionIntegersSemilocalHom_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    v.adicCompletionSemilocalEquiv K B L (v.adicCompletionIntegersSemilocalToField K B L z) =
      fun w ↦ (v.adicCompletionIntegersSemilocalHom K B L z w : w.val.adicCompletion L) :=
  congrFun (v.coe_adicCompletionSemilocalEquiv (K := K) (B := B) (L := L)) _ ▸
    v.adicCompletionSemilocalHom_toField z

/-- `adicCompletionIntegersSemilocalToField` is injective when `B` is finite over `R`. -/
theorem adicCompletionIntegersSemilocalToField_injective :
    Function.Injective (v.adicCompletionIntegersSemilocalToField K B L) := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  have : Module.IsTorsionFree R (v.adicCompletion K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr <| by
      rw [IsScalarTower.algebraMap_eq R K (v.adicCompletion K), RingHom.coe_comp]
      exact (algebraMap K (v.adicCompletion K)).injective.comp (IsFractionRing.injective R K)
  exact (v.adicCompletionFieldBaseChangeEquiv (K := K) (B := B) (L := L)).injective.comp
    (TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom R (v.adicCompletionIntegers K) _).toLinearMap
      (AlgHom.id R B).toLinearMap Subtype.val_injective Function.injective_id)

/-- **Injectivity of the integral semilocal map** (with arbitrary residue fields). -/
theorem adicCompletionIntegersSemilocalHom_injective :
    Function.Injective (v.adicCompletionIntegersSemilocalHom K B L) := fun _ _ hxy ↦
  v.adicCompletionIntegersSemilocalToField_injective (K := K) (B := B) (L := L) <|
    (v.adicCompletionSemilocalEquiv K B L).injective <| by
      rw [adicCompletionIntegersSemilocalHom_fieldCompatibility,
        adicCompletionIntegersSemilocalHom_fieldCompatibility, hxy]

variable (K B L) in
/-- **The integral semilocal isomorphism** `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w`. -/
def adicCompletionIntegersSemilocalEquiv :
    v.adicCompletionIntegers K ⊗[R] B ≃ₐ[v.adicCompletionIntegers K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        w.val.adicCompletionIntegers L :=
  -- Keep `Function.Bijective` explicit so `AlgEquiv.coe_ofBijective` and `ofBijective_apply` match.
  AlgEquiv.ofBijective (v.adicCompletionIntegersSemilocalHom K B L)
    (show Function.Bijective (v.adicCompletionIntegersSemilocalHom K B L) from
      ⟨v.adicCompletionIntegersSemilocalHom_injective,
        v.adicCompletionIntegersSemilocalHom_surjective⟩)

/-- As a function, `adicCompletionIntegersSemilocalEquiv` equals the integral semilocal map. -/
theorem coe_adicCompletionIntegersSemilocalEquiv :
    ⇑(v.adicCompletionIntegersSemilocalEquiv K B L) =
      v.adicCompletionIntegersSemilocalHom K B L :=
  AlgEquiv.coe_ofBijective ..

/-- As an `AlgHom`, `adicCompletionIntegersSemilocalEquiv` equals the integral semilocal map. -/
theorem toAlgHom_adicCompletionIntegersSemilocalEquiv :
    (v.adicCompletionIntegersSemilocalEquiv K B L).toAlgHom =
      v.adicCompletionIntegersSemilocalHom K B L :=
  AlgHom.ext fun x ↦
    congrFun (v.coe_adicCompletionIntegersSemilocalEquiv (K := K) (B := B) (L := L)) x

/-- `adicCompletionIntegersSemilocalEquiv` sends a pure tensor `a ⊗ b` to `(a · b)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionIntegersSemilocalEquiv_tmul (a : v.adicCompletionIntegers K) (b : B)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionIntegersSemilocalEquiv K B L (a ⊗ₜ b) w =
      algebraMap (v.adicCompletionIntegers K) (w.val.adicCompletionIntegers L) a *
        algebraMap B (w.val.adicCompletionIntegers L) b :=
  congrFun (v.coe_adicCompletionIntegersSemilocalEquiv (K := K) (B := B) (L := L)) (a ⊗ₜ b) ▸
    v.adicCompletionIntegersSemilocalHom_tmul a b w

/-- The inverse integral semilocal isomorphism sends the diagonal image of `b ∈ B` to `1 ⊗ b`. -/
@[simp]
theorem adicCompletionIntegersSemilocalEquiv_symm_algebraMap (b : B) :
    (v.adicCompletionIntegersSemilocalEquiv K B L).symm
        (fun w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ↦
          algebraMap B (w.val.adicCompletionIntegers L) b) = 1 ⊗ₜ[R] b :=
  (v.adicCompletionIntegersSemilocalEquiv K B L).symm_apply_eq.mpr (funext fun w ↦ by simp)

/-- Compatibility of `adicCompletionIntegersSemilocalEquiv` with `adicCompletionSemilocalEquiv`. -/
theorem adicCompletionIntegersSemilocalEquiv_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    v.adicCompletionSemilocalEquiv K B L (v.adicCompletionIntegersSemilocalToField K B L z) =
      fun w ↦ (v.adicCompletionIntegersSemilocalEquiv K B L z w : w.val.adicCompletion L) :=
  v.adicCompletionIntegersSemilocalHom_fieldCompatibility z

/-- The norm of `K_v ⊗[K] L` over `K_v` is the product of the local norms of its components. -/
theorem norm_eq_prod_norm_adicCompletionSemilocalEquiv
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}]
    (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.norm (v.adicCompletion K) ξ =
      ∏ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K) (v.adicCompletionSemilocalEquiv K B L ξ w) := by
  classical
  rw [← Algebra.norm_eq_of_algEquiv (v.adicCompletionSemilocalEquiv K B L), Algebra.norm_pi]

/-- **Local-global norm formula**: `N_{L/K}(x) = ∏_{w ∣ v} N_{L_w/K_v}(x)` in `K_v`. -/
theorem algebraMap_norm_eq_prod_norm_adicCompletion
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}] (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K) (algebraMap L (w.val.adicCompletion L) x) := by
  have := TauCeti.IsFractionRing.finiteDimensional_of_finite R B K L
  rw [← Algebra.norm_baseChange_tmul (A := v.adicCompletion K) (B := L) x,
    v.norm_eq_prod_norm_adicCompletionSemilocalEquiv (B := B)]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [adicCompletionSemilocalEquiv_tmul, map_one, one_mul]

/-- The trace of a pure integral tensor paired with `d ∈ L` extends the global trace to `K_v`. -/
theorem trace_adicCompletionIntegersSemilocalToField_tmul_mul (a : v.adicCompletionIntegers K)
    (b : B) (d : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (v.adicCompletionIntegersSemilocalToField K B L (a ⊗ₜ b) * (1 ⊗ₜ d)) =
      (a : v.adicCompletion K) *
        algebraMap K (v.adicCompletion K) (Algebra.trace K L (algebraMap B L b * d)) := by
  have := TauCeti.IsFractionRing.finiteDimensional_of_finite R B K L
  rw [adicCompletionIntegersSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    ← Algebra.trace_baseChange_tmul (K := K) (A := v.adicCompletion K), ← smul_eq_mul a.val,
    ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The trace of `K_v ⊗[K] L` over `K_v` is the sum of the local traces of its components. -/
theorem trace_eq_sum_trace_adicCompletionSemilocalEquiv
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}]
    (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) ξ =
      ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L)
          (v.adicCompletionSemilocalEquiv K B L ξ w) := by
  classical
  rw [← Algebra.trace_eq_of_algEquiv (v.adicCompletionSemilocalEquiv K B L), Algebra.trace_pi]

open scoped Classical in
/-- Placing `z ∈ L_w` in the `w`-component of `K_v ⊗[K] L` preserves its trace pairing with `L`. -/
theorem trace_adicCompletionSemilocalEquiv_symm_single_mul (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (z : w.adicCompletion L) (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((v.adicCompletionSemilocalEquiv K B L).symm
          (Pi.single (⟨w, inferInstance⟩ :
            {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal}) z) * (1 ⊗ₜ x)) =
      Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) x) := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  let _ : Fintype {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  rw [v.trace_eq_sum_trace_adicCompletionSemilocalEquiv (B := B),
    Finset.sum_eq_single (⟨w, inferInstance⟩ :
      {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})
      (fun _ _ hw' ↦ by simp [Pi.single_eq_of_ne hw']) (by simp)]
  simp [adicCompletionSemilocalEquiv_tmul]

/-- **Local-global trace formula**: `Tr_{L/K}(x) = ∑_{w ∣ v} Tr_{L_w/K_v}(x)` in `K_v`. -/
theorem algebraMap_trace_eq_sum_trace_adicCompletion
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}] (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L)
          (algebraMap L (w.val.adicCompletion L) x) := by
  have := TauCeti.IsFractionRing.finiteDimensional_of_finite R B K L
  rw [← Algebra.trace_baseChange_tmul (A := v.adicCompletion K) (B := L) x,
    v.trace_eq_sum_trace_adicCompletionSemilocalEquiv (B := B)]
  exact Finset.sum_congr rfl fun w _ ↦ by rw [adicCompletionSemilocalEquiv_tmul, map_one, one_mul]

/-- **Separability passes to completions** (even when the residue extension is inseparable). -/
theorem isSeparable_adicCompletion_of_isSeparable [Algebra.IsSeparable K L]
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  let _ : Algebra K (w.adicCompletion L) :=
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L (w.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← v.algebraMap_adicCompletionExtension_algebraMap w c]
  let proj : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] w.adicCompletion L :=
    (Pi.evalAlgHom (v.adicCompletion K) _ (⟨w, inferInstance⟩ :
      {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})).comp
      (v.adicCompletionSemilocalHom K B L)
  have hsurj : Function.Surjective proj :=
    (Function.surjective_eval _).comp (v.adicCompletionSemilocalHom_surjective (K := K) (L := L))
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  rintro z -; obtain ⟨t, rfl⟩ := hsurj z
  induction t using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => exact map_add proj u₁ u₂ ▸ add_mem hu₁ hu₂
  | tmul a x =>
    have hproj : proj (a ⊗ₜ x) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) a *
          algebraMap L (w.adicCompletion L) x := by simp [proj]
    exact hproj ▸ mul_mem (algebraMap_mem _ a) (mem_separableClosure_iff.mpr <|
      ((Algebra.IsSeparable.isSeparable K x).map (IsScalarTower.toAlgHom K L (w.adicCompletion L))
        (RingHom.injective _)).tower_top (v.adicCompletion K))

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isSeparable_adicCompletion_of_isSeparable

end FiniteExtension

end IsDedekindDomain.HeightOneSpectrum

end
