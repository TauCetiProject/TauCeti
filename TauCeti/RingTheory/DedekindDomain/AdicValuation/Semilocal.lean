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
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.InertiaDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension
public import TauCeti.RingTheory.Ideal.PrimesOver
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.Localization.FiniteFree
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.NormTrace.Pi

/-!
# The semilocal decomposition of a finite extension of Dedekind domains

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, with `B` module-finite over `R`, and
let `v` be a height-one prime of `R`. Without any finiteness or separability hypothesis on the
residue fields `R ⧸ v` and `B ⧸ w`, scalar extension along `R → 𝒪_v` and `K → K_v` decomposes as
the product over the finitely many height-one primes `w` of `B` lying over `v`:

* `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w` (`adicCompletionIntegersSemilocalEquiv`),
* `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w` (`adicCompletionSemilocalEquiv`).

In particular, each completed extension `𝒪_w / 𝒪_v` is finite and free of rank
`[L_w : K_v] = e(w ∣ v) · f(w ∣ v)`, `𝒪_w` is the integral closure of `𝒪_v` in `L_w`, `L_w / K_v`
is separable whenever `L / K` is separable, and the global trace `Tr_{L/K}` decomposes as
`∑_{w ∣ v} Tr_{L_w/K_v}`. This complements
`TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegralClosure` and
`TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree`, which establish local finiteness
and `[L_w : K_v] = e · f` under `[Finite (B ⧸ w.asIdeal)]` without `[Module.Finite R B]`.

## Proof strategy

Unlike the number-field case (`TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic`), the
completed integer ring `𝒪_v` need not be compact (for instance when `K` is a function field over an
infinite or imperfect constant field). Instead, `𝒪_v ⊗[R] B` is module-finite over the complete
discrete valuation ring `𝒪_v`, hence `𝔪_v`-adically precomplete, while `∏_{w ∣ v} 𝒪_w` is
`𝔪_v`-adically Hausdorff. Simultaneous approximation
(`HeightOneSpectrum.exists_forall_valued_sub_le`) makes `B` surject modulo `𝔪_v`, and
`surjective_of_mkQ_comp_surjective` lifts this to surjectivity of `𝒪_v ⊗[R] B → ∏_{w ∣ v} 𝒪_w`.
Projecting onto a single factor yields `Module.Finite 𝒪_v 𝒪_w` and, via
`Ideal.sum_ramification_inertia_eq_finrank`, the local degree formula
`[L_w : K_v] = e(w ∣ v) · f(w ∣ v)`; comparing dimension sums then gives injectivity at both the
field and integral levels.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSemilocalHom` and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSemilocalEquiv`: the integral semilocal
  map and isomorphism `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionSemilocalHom` and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionSemilocalEquiv`: the field semilocal map and
  isomorphism `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSemilocalToField`: the injective map
  `𝒪_v ⊗[R] B →ₐ[R] K_v ⊗[K] L`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.map_maximalIdeal_adicCompletionIntegers_eq_pow` and
  `IsDedekindDomain.HeightOneSpectrum.finrank_residueField_adicCompletionIntegers`: the
  maximal-ideal extension and residue degree of `𝒪_w / 𝒪_v` agree with `e(w ∣ v)` and `f(w ∣ v)`.
* `IsDedekindDomain.HeightOneSpectrum.moduleFinite_adicCompletionIntegers_of_finite`,
  `IsDedekindDomain.HeightOneSpectrum.moduleFree_adicCompletionIntegers_of_finite`,
  `IsDedekindDomain.HeightOneSpectrum.isIntegralClosure_adicCompletionIntegers_of_finite`, and
  `IsDedekindDomain.HeightOneSpectrum.finiteDimensional_adicCompletion_of_finite`: local finiteness,
  freeness, and integral-closure properties for arbitrary residue fields.
* `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletionIntegers_of_finite` and
  `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_of_finite`:
  `finrank 𝒪_v 𝒪_w = finrank K_v L_w = e(w ∣ v) · f(w ∣ v)`.
* `IsDedekindDomain.HeightOneSpectrum.algebraMap_trace_eq_sum_trace_adicCompletion` and
  `IsDedekindDomain.HeightOneSpectrum.trace_adicCompletionSemilocalEquiv_symm_single_mul`: the
  local-global trace decomposition.
* `IsDedekindDomain.HeightOneSpectrum.isSeparable_adicCompletion_of_isSeparable`: separability of
  `L / K` passes to `L_w / K_v`.

## Provenance

The algebraic comparison between the integral and field tensor products and the componentwise trace
identities adapt the number-field development in
`TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic`,
`TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers`, and
`TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace`, replacing the compactness
argument for surjectivity by `𝔪_v`-adic completeness over an arbitrary Dedekind base.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §§2–3.
-/

public section
noncomputable section

open TauCeti IsDedekindDomain ValuativeRel WithZero TensorProduct
open scoped AdicCompletionExtension nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

/-- The maximal ideal of `𝒪_v` extends to the `e(w ∣ v)`-th power of the maximal ideal of `𝒪_w`. -/
theorem map_maximalIdeal_adicCompletionIntegers_eq_pow (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).map
        (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ w.asIdeal.ramificationIdx R := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  refine w.span_singleton_eq_maximalIdeal_pow ?_
  rw [← IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) (w.adicCompletion L),
    IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.adicCompletion L),
    algebraMap_adicCompletionExtensionAlgebra, valued_adicCompletionExtension,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ, ← exp_nsmul]
  simp

/-- The degree of the residue-field extension of completed integer rings is the global inertia
degree `w.asIdeal.inertiaDeg R` (including any inseparable factor). -/
@[simp]
theorem finrank_residueField_adicCompletionIntegers (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
        (IsLocalRing.ResidueField (w.adicCompletionIntegers L)) =
      w.asIdeal.inertiaDeg R := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv
    (v.residueFieldEquivAdicCompletionIntegers (K := K))
    (w.residueFieldEquivAdicCompletionIntegers (K := L)) (RingHom.ext fun x ↦ ?_)).symm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change algebraMap (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
      (IsLocalRing.ResidueField (w.adicCompletionIntegers L))
      (v.residueFieldEquivAdicCompletionIntegers (K := K) (Ideal.Quotient.mk v.asIdeal r)) =
    w.residueFieldEquivAdicCompletionIntegers (K := L)
      (algebraMap (R ⧸ v.asIdeal) (B ⧸ w.asIdeal) (Ideal.Quotient.mk v.asIdeal r))
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
    v.residueFieldEquivAdicCompletionIntegers_apply_mk,
    w.residueFieldEquivAdicCompletionIntegers_apply_mk]
  change algebraMap (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
      (IsLocalRing.ResidueField (w.adicCompletionIntegers L))
      (IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) r)) =
    IsLocalRing.residue (w.adicCompletionIntegers L)
      (algebraMap B (w.adicCompletionIntegers L) (algebraMap R B r))
  rw [IsLocalRing.ResidueField.algebraMap_residue,
    algebraMap_adicCompletionIntegersExtensionAlgebra, adicCompletionIntegersExtension_algebraMap]

/-- The canonical `𝒪_v`-algebra map from `𝒪_v ⊗[R] B` to the product of the completed integer rings
at the primes of `B` lying over `v`. -/
def adicCompletionIntegersSemilocalHom (v : HeightOneSpectrum R) (K B L : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [IsDedekindDomain B] [Algebra R B]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L] :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[v.adicCompletionIntegers K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        w.1.adicCompletionIntegers L :=
  letI (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      Algebra R (w.1.adicCompletionIntegers L) :=
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)).comp
      (algebraMap R (v.adicCompletionIntegers K))).toAlgebra
  letI (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      IsScalarTower R (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦
      { algebraMap B (w.1.adicCompletionIntegers L) with
        commutes' := fun r ↦ by
          change algebraMap B (w.1.adicCompletionIntegers L) (algebraMap R B r) =
            algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
              (algebraMap R (v.adicCompletionIntegers K) r)
          rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
            adicCompletionIntegersExtension_algebraMap] })
    fun _ _ ↦ .all _ _

/-- `adicCompletionIntegersSemilocalHom` sends a pure tensor `a ⊗ b` to `(a · b)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionIntegersSemilocalHom_tmul (v : HeightOneSpectrum R)
    (a : v.adicCompletionIntegers K) (b : B)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionIntegersSemilocalHom K B L (a ⊗ₜ b) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap B (w.1.adicCompletionIntegers L) b := by
  simp [adicCompletionIntegersSemilocalHom]

/-- The canonical `K_v`-algebra map from `K_v ⊗[K] L` to the product of the completions of `L` at
the primes of `B` lying over `v`. -/
def adicCompletionSemilocalHom (v : HeightOneSpectrum R) (K B L : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [IsDedekindDomain B] [Algebra R B]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L] :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        w.1.adicCompletion L :=
  letI (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      Algebra K (w.1.adicCompletion L) :=
    ((algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).comp
      (algebraMap K (v.adicCompletion K))).toAlgebra
  letI (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      IsScalarTower K (v.adicCompletion K) (w.1.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦
      { algebraMap L (w.1.adicCompletion L) with
        commutes' := fun x ↦ by
          change algebraMap L (w.1.adicCompletion L) (algebraMap K L x) =
            algebraMap (v.adicCompletion K) (w.1.adicCompletion L)
              (algebraMap K (v.adicCompletion K) x)
          rw [algebraMap_adicCompletionExtensionAlgebra, algebraMap_adicCompletion,
            algebraMap_adicCompletion, Function.comp_apply, Function.comp_apply,
            Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
          exact (adicCompletionExtension_coe K L v w.1 x).symm })
    fun _ _ ↦ .all _ _

/-- `adicCompletionSemilocalHom` sends a pure tensor `a ⊗ x` to `(a · x)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionSemilocalHom_tmul (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionSemilocalHom K B L (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) x := by
  simp [adicCompletionSemilocalHom]

end General

section FiniteExtension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.Finite R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

omit [Module.Finite R B] in
/-- An element of `𝒪_w` of valuation at most `exp (-e(w ∣ v))` is divisible by a uniformizer `π` of
`𝒪_v`. -/
private theorem exists_smul_eq_of_valued_le (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) {z : w.adicCompletionIntegers L}
    (hz : Valued.v (z : w.adicCompletion L) ≤ exp (-(w.asIdeal.ramificationIdx R : ℤ))) :
    ∃ q : w.adicCompletionIntegers L, π • q = z := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  let E : w.adicCompletion L :=
    (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π : w.adicCompletion L)
  have hEval : Valued.v E = exp (-(w.asIdeal.ramificationIdx R : ℤ)) := by
    dsimp only [E]
    rw [← ValuationSubring.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
        (w.adicCompletionIntegers L) (w.adicCompletion L),
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K)
        (w.adicCompletion L),
      algebraMap_adicCompletionExtensionAlgebra, valued_adicCompletionExtension,
      Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
      v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ, ← exp_nsmul]
    simp
  have hE0 : E ≠ 0 := fun h0 ↦ exp_ne_zero ((h0 ▸ hEval).symm.trans (map_zero _))
  have hq : (z : w.adicCompletion L) / E ∈ w.adicCompletionIntegers L := by
    rw [mem_adicCompletionIntegers, map_div₀, hEval]
    exact div_le_one_of_le₀ hz zero_le
  refine ⟨⟨(z : w.adicCompletion L) / E, hq⟩, Subtype.ext ?_⟩
  rw [Algebra.smul_def, Subring.coe_mul]
  exact mul_div_cancel₀ _ hE0

/-- **Surjectivity of the integral semilocal map**, without any residue-field finiteness
hypothesis: simultaneous approximation in `B` gives surjectivity modulo `𝔪_v`, and `𝔪_v`-adic
completeness of `𝒪_v` lifts it to `𝒪_v ⊗[R] B`. -/
theorem adicCompletionIntegersSemilocalHom_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (v.adicCompletionIntegersSemilocalHom K B L) := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Finite {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} :=
    HeightOneSpectrum.finite_liesOver B v
  let _ : Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  set I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  have : IsPrecomplete I (v.adicCompletionIntegers K ⊗[R] B) :=
    IsPrecomplete.of_finite I (v.adicCompletionIntegers K ⊗[R] B)
  have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      IsHausdorff I (w.1.adicCompletionIntegers L) :=
    IsHausdorff.of_map (IsLocalRing.map_maximalIdeal_le
      (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  refine surjective_of_mkQ_comp_surjective (I := I)
    (f := (v.adicCompletionIntegersSemilocalHom K B L).toLinearMap) fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  let s : Finset (HeightOneSpectrum B) :=
    Finset.univ.image fun w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ↦ w.1
  let x : ∀ w : HeightOneSpectrum B, w.adicCompletionIntegers L := fun w ↦
    if hw : w.asIdeal.LiesOver v.asIdeal then y ⟨w, hw⟩ else 0
  let n : HeightOneSpectrum B → ℕ := fun w ↦ w.asIdeal.ramificationIdx R
  obtain ⟨b, hb⟩ := exists_forall_valued_sub_le (K := L) s x n
  refine ⟨1 ⊗ₜ b, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    show I = Ideal.span {π} from hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  have hsub (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      ∃ q : w.1.adicCompletionIntegers L,
        π • q = (v.adicCompletionIntegersSemilocalHom K B L (1 ⊗ₜ b) - y) w := by
    have hbw := hb w.1 (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩)
    simp only [x, dite_eq_left w.2, n] at hbw
    refine exists_smul_eq_of_valued_le v w.1 hπ ?_
    rw [Pi.sub_apply, AddSubgroupClass.coe_sub, adicCompletionIntegersSemilocalHom_tmul,
      map_one, one_mul, Valuation.map_sub_swap]
    have hbcoe : (algebraMap B (w.1.adicCompletionIntegers L) b : w.1.adicCompletion L) =
        algebraMap B (w.1.adicCompletion L) b := by
      rw [← ValuationSubring.algebraMap_apply,
        ← algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers,
        IsScalarTower.algebraMap_apply B L (w.1.adicCompletion L)]
    rwa [hbcoe]
  choose q hq using hsub
  exact ⟨q, Submodule.mem_top, funext hq⟩

/-- **`𝒪_w` is module-finite over `𝒪_v`** whenever `B` is module-finite over `R`, with no
finiteness hypothesis on the residue fields. -/
theorem moduleFinite_adicCompletionIntegers_of_finite (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  let proj : (∀ u : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal},
      u.1.adicCompletionIntegers L) →ₗ[v.adicCompletionIntegers K] w.adicCompletionIntegers L :=
    LinearMap.proj (⟨w, inferInstance⟩ :
      {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})
  exact Module.Finite.of_surjective
    (proj.comp (v.adicCompletionIntegersSemilocalHom K B L).toLinearMap)
    ((Function.surjective_eval _).comp
      (v.adicCompletionIntegersSemilocalHom_surjective (K := K) (L := L)))

/-- **`𝒪_w` is a free `𝒪_v`-module** whenever `B` is module-finite over `R`. -/
theorem moduleFree_adicCompletionIntegers_of_finite (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Module.Free (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  have := v.moduleFinite_adicCompletionIntegers_of_finite (K := K) (L := L) w
  exact Module.free_of_finite_type_torsion_free'

/-- **`L_w` is finite-dimensional over `K_v`** whenever `B` is module-finite over `R`. -/
theorem finiteDimensional_adicCompletion_of_finite (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := by
  have := v.moduleFinite_adicCompletionIntegers_of_finite (K := K) (L := L) w
  have := v.moduleFree_adicCompletionIntegers_of_finite (K := K) (L := L) w
  have := (IsFractionRing.isLocalization_algebraMapSubmonoid_iff
    (v.adicCompletionIntegers K) (S := w.adicCompletionIntegers L)
    (w.adicCompletion L)).mpr inferInstance
  exact .of_basis ((Module.Free.chooseBasis (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L)).localizationLocalization (v.adicCompletion K)
      (v.adicCompletionIntegers K)⁰ (w.adicCompletion L))

/-- **`𝒪_w` is the integral closure of `𝒪_v` in `L_w`** whenever `B` is module-finite over `R`,
with no finiteness hypothesis on the residue fields. -/
theorem isIntegralClosure_adicCompletionIntegers_of_finite (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) := by
  have := v.moduleFinite_adicCompletionIntegers_of_finite (K := K) (L := L) w
  infer_instance

/-- `L` is the localization of `B` at the non-zero-divisors of `R` whenever `B` is module-finite
over `R`. -/
private theorem isLocalization_algebraMapSubmonoid_of_finite (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L] :
    IsLocalization (Algebra.algebraMapSubmonoid B R⁰) L := by
  have : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing R B K L
  exact IsIntegralClosure.isLocalization R K L B

private def adicCompletionFieldBaseChangeEquiv (v : HeightOneSpectrum R) :
    v.adicCompletion K ⊗[R] B ≃ₐ[v.adicCompletion K] v.adicCompletion K ⊗[K] L :=
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) L :=
    isLocalization_algebraMapSubmonoid_of_finite (B := B) (L := L) K
  haveI : Algebra.IsPushout R K B L :=
    (Algebra.isPushout_of_isLocalization (R := R) (A := K) R⁰ B L).symm
  (Algebra.TensorProduct.cancelBaseChange R K (v.adicCompletion K)
      (v.adicCompletion K) B).symm.trans
    (Algebra.TensorProduct.congr (.refl : v.adicCompletion K ≃ₐ[v.adicCompletion K]
      v.adicCompletion K) (Algebra.IsPushout.equiv R K B L))

@[simp]
private theorem adicCompletionFieldBaseChangeEquiv_tmul (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) (b : B) :
    v.adicCompletionFieldBaseChangeEquiv (B := B) (L := L) (a ⊗ₜ b) = a ⊗ₜ algebraMap B L b := by
  simp [adicCompletionFieldBaseChangeEquiv, Algebra.IsPushout.equiv_tmul]

omit [Module.Finite R B] in
private def adicCompletionIntegersToCompletion (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers K →ₐ[R] v.adicCompletion K :=
  { (Algebra.ofId (v.adicCompletionIntegers K) (v.adicCompletion K)).toRingHom with
    commutes' := fun r ↦ by
      change algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (algebraMap R (v.adicCompletionIntegers K) r) =
        algebraMap R (v.adicCompletion K) r
      rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]
      exact (v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers r).symm }

omit [Module.Finite R B] in
private def adicCompletionIntegersTensorToBaseChange (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[R] B :=
  { (Algebra.TensorProduct.map (v.adicCompletionIntegersToCompletion (K := K))
      (AlgHom.id R B)).toRingHom with
    commutes' := fun _ ↦ rfl }

/-- The canonical inclusion `𝒪_v ⊗[R] B →ₐ[R] K_v ⊗[K] L` from the integral tensor product into
the field tensor product. -/
def adicCompletionIntegersSemilocalToField (v : HeightOneSpectrum R) (K B L : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.Finite R B]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L] :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[K] L :=
  let eHom : v.adicCompletion K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[K] L :=
    { (v.adicCompletionFieldBaseChangeEquiv (K := K) (B := B) (L := L)).toRingEquiv.toRingHom with
      commutes' := fun r ↦ by
        change v.adicCompletionFieldBaseChangeEquiv (K := K) (B := B) (L := L)
            (algebraMap R (v.adicCompletion K) r ⊗ₜ[R] (1 : B)) =
          algebraMap R (v.adicCompletion K) r ⊗ₜ[K] (1 : L)
        rw [adicCompletionFieldBaseChangeEquiv_tmul, map_one] }
  eHom.comp (v.adicCompletionIntegersTensorToBaseChange (K := K) (B := B))

/-- `adicCompletionIntegersSemilocalToField` sends `a ⊗ b` to `(a : K_v) ⊗ (b : L)`. -/
@[simp]
theorem adicCompletionIntegersSemilocalToField_tmul (v : HeightOneSpectrum R)
    (a : v.adicCompletionIntegers K) (b : B) :
    v.adicCompletionIntegersSemilocalToField K B L (a ⊗ₜ b) =
      (a : v.adicCompletion K) ⊗ₜ algebraMap B L b := by
  change v.adicCompletionFieldBaseChangeEquiv (K := K) (B := B) (L := L)
      ((a : v.adicCompletion K) ⊗ₜ b) = _
  exact v.adicCompletionFieldBaseChangeEquiv_tmul (a : v.adicCompletion K) b

private theorem adicCompletionSemilocalHom_toField (v : HeightOneSpectrum R)
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    v.adicCompletionSemilocalHom K B L (v.adicCompletionIntegersSemilocalToField K B L z) =
      fun w ↦ (v.adicCompletionIntegersSemilocalHom K B L z w : w.1.adicCompletion L) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext w
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (congrFun hx w) (congrFun hy w)
  | tmul a b =>
    funext w
    rw [adicCompletionIntegersSemilocalToField_tmul, adicCompletionSemilocalHom_tmul,
      adicCompletionIntegersSemilocalHom_tmul, Subring.coe_mul]
    congr 1
    rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
      algebraMap_adicCompletionExtensionAlgebra, coe_adicCompletionIntegersExtension]

omit [Module.Finite R B] in
/-- Every element of `L_w` becomes integral after multiplying by a sufficiently high power of a
uniformizer of `𝒪_v`. -/
private theorem exists_pow_irreducible_mul_mem_adicCompletionIntegers (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) (z : w.adicCompletion L) :
    ∃ N : ℕ, ∀ m ≥ N,
      algebraMap (v.adicCompletion K) (w.adicCompletion L) ((π : v.adicCompletion K) ^ m) * z ∈
        w.adicCompletionIntegers L := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨0, fun _ _ ↦ by simp⟩
  have hπv : Valued.v (π : v.adicCompletion K) = exp (-1) := by
    rw [← Algebra.algebraMap_ofSubsemiring_apply
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring π]
    exact v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ
  have hzval0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  set k : ℕ := (log (Valued.v z)).natAbs
  refine ⟨k, fun m hm ↦ ?_⟩
  rw [mem_adicCompletionIntegers, map_mul, algebraMap_adicCompletionExtensionAlgebra,
    valued_adicCompletionExtension, map_pow, hπv, ← exp_nsmul, ← exp_nsmul,
    ← exp_log hzval0, ← exp_add, ← exp_zero, exp_le_exp]
  have he : 1 ≤ v.asIdeal.ramificationIdx' w.asIdeal :=
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      w.asIdeal v.ne_bot)
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  have hk : log (Valued.v z) ≤ (k : ℤ) := Int.natCast_natAbs _ ▸ le_abs_self _
  nlinarith

/-- **Surjectivity of the field semilocal map**, deduced from integral surjectivity by clearing
denominators with a power of a uniformizer of `𝒪_v`. -/
theorem adicCompletionSemilocalHom_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (v.adicCompletionSemilocalHom K B L) := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Finite {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} :=
    HeightOneSpectrum.finite_liesOver B v
  let _ : Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := Fintype.ofFinite _
  intro y
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h0
    have hπv := v.valued_algebraMap_eq_exp_neg_one_of_irreducible (K := K) hπ
    rw [Algebra.algebraMap_ofSubsemiring_apply, h0, map_zero] at hπv
    exact exp_ne_zero hπv.symm
  choose N hN using fun w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ↦
    exists_pow_irreducible_mul_mem_adicCompletionIntegers v w.1 hπ (y w)
  let M : ℕ := Finset.univ.sup N
  let yInt : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      w.1.adicCompletionIntegers L :=
    fun w ↦ ⟨_, hN w M (Finset.le_sup (Finset.mem_univ w))⟩
  obtain ⟨t, ht⟩ := v.adicCompletionIntegersSemilocalHom_surjective (K := K) (L := L) yInt
  refine ⟨((π : v.adicCompletion K) ^ M)⁻¹ • v.adicCompletionIntegersSemilocalToField K B L t,
    funext fun w ↦ ?_⟩
  rw [map_smul, Pi.smul_apply, v.adicCompletionSemilocalHom_toField t, ht, Algebra.smul_def,
    map_inv₀]
  exact inv_mul_cancel_left₀
    (map_pow (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) _ M ▸
      pow_ne_zero M ((map_ne_zero _).mpr hπ0)) (y w)

/-- **The rank of `𝒪_w` over `𝒪_v` is `e(w ∣ v) · f(w ∣ v)`**, with no finiteness or separability
hypothesis on the residue fields. -/
theorem finrank_adicCompletionIntegers_of_finite (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  classical
  have := v.moduleFinite_adicCompletionIntegers_of_finite (K := K) (L := L) w
  set p := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  set Q := IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K)
  have hQ0 : Q ≠ ⊥ := IsDiscreteValuationRing.not_a_field (w.adicCompletionIntegers L)
  have : NeZero p := ⟨hp0⟩
  rw [← Ideal.sum_ramification_inertia_eq_finrank p (w.adicCompletionIntegers L)]
  have : Q.LiesOver p := v.maximalIdeal_adicCompletionIntegers_liesOver K L w
  have hp_map : p.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) ≠ ⊥ :=
    map_maximalIdeal_adicCompletionIntegers_eq_pow (K := K) (L := L) v w ▸ pow_ne_zero _ hQ0
  have hQmem : Q ∈ p.primesOver (w.adicCompletionIntegers L) := ⟨inferInstance, inferInstance⟩
  have huniq : ∀ P ∈ p.primesOver (w.adicCompletionIntegers L), P = Q := fun P hP ↦
    have : P.LiesOver p := hP.2
    IsLocalRing.eq_maximalIdeal
      (hP.1.isMaximal (ne_bot_of_le_ne_bot hp_map (Ideal.map_le_of_le_comap (P.over_def p).le)))
  rw [Finset.sum_eq_single ⟨Q, hQmem⟩
    (fun P _ hPQ ↦ absurd (Subtype.ext (huniq P.1 P.2)) hPQ)
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  have hram : Q.ramificationIdx (v.adicCompletionIntegers K) = w.asIdeal.ramificationIdx R := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p Q hp_map,
      map_maximalIdeal_adicCompletionIntegers_eq_pow (K := K) (L := L) v w,
      multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hQ0 inferInstance)]
  have hinert : Q.inertiaDeg (v.adicCompletionIntegers K) = w.asIdeal.inertiaDeg R := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p Q,
      ← finrank_residueField_adicCompletionIntegers (K := K) (L := L) v w]
    refine Algebra.finrank_eq_of_equiv_equiv (.refl _) (.refl _) (RingHom.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (IsLocalRing.ResidueField.algebraMap_residue a).trans
      (Ideal.Quotient.algebraMap_mk_of_liesOver Q p a).symm
  exact congrArg₂ (· * ·) hram hinert

/-- **The local degree of `L_w / K_v` is `e(w ∣ v) · f(w ∣ v)`** whenever `B` is module-finite
over `R`, with no finiteness or separability hypothesis on the residue fields. -/
theorem finrank_adicCompletion_of_finite (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  rw [IsFractionRing.finrank_eq (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletionIntegers L) (w.adicCompletion L)]
  exact v.finrank_adicCompletionIntegers_of_finite (K := K) (L := L) w

/-- **The sum of the local degrees above `v` equals `[L : K]`.** -/
theorem sum_finrank_adicCompletion_of_finite (v : HeightOneSpectrum R)
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}] :
    (∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)) = Module.finrank K L := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  let _ : Fintype (v.asIdeal.primesOver B) := Fintype.ofEquiv _ (liesOverEquivPrimesOver B v)
  calc ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
          Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)
      = ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
          w.1.asIdeal.ramificationIdx R * w.1.asIdeal.inertiaDeg R :=
        Finset.sum_congr rfl fun w _ ↦ v.finrank_adicCompletion_of_finite (K := K) (L := L) w.1
    _ = ∑ Q : v.asIdeal.primesOver B,
          (Q : Ideal B).ramificationIdx R * (Q : Ideal B).inertiaDeg R :=
        Fintype.sum_equiv (liesOverEquivPrimesOver B v) _ _ fun w ↦ by
          rw [liesOverEquivPrimesOver_apply]
    _ = Module.finrank R B := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq R K B L).symm

/-- **The field semilocal isomorphism** `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`, for any finite
extension of Dedekind domains `R ⊆ B` (with arbitrary residue fields). -/
def adicCompletionSemilocalEquiv (v : HeightOneSpectrum R) (K B L : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.Finite R B]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L] :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        w.1.adicCompletion L :=
  AlgEquiv.ofBijective (v.adicCompletionSemilocalHom K B L)
    (show Function.Bijective (v.adicCompletionSemilocalHom K B L) from by
      classical
      have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
      let _ : Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} :=
        Fintype.ofFinite _
      have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
          FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) :=
        v.finiteDimensional_adicCompletion_of_finite (K := K) (L := L) w.1
      have : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) L :=
        isLocalization_algebraMapSubmonoid_of_finite (B := B) (L := L) K
      have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
      have hsurj := v.adicCompletionSemilocalHom_surjective (K := K) (B := B) (L := L)
      have hfin : Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) =
          Module.finrank (v.adicCompletion K)
            (∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
              w.1.adicCompletion L) := by
        rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
          Module.finrank_pi_fintype,
          v.sum_finrank_adicCompletion_of_finite (K := K) (B := B) (L := L)]
      exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj, hsurj⟩)

/-- `adicCompletionSemilocalEquiv` sends a pure tensor `a ⊗ x` to `(a · x)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionSemilocalEquiv_tmul (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionSemilocalEquiv K B L (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) x := by
  rw [adicCompletionSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact v.adicCompletionSemilocalHom_tmul a x w

/-- Compatibility of the integral and field semilocal maps under inclusion into the completions. -/
theorem adicCompletionIntegersSemilocalHom_fieldCompatibility (v : HeightOneSpectrum R)
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    v.adicCompletionSemilocalEquiv K B L (v.adicCompletionIntegersSemilocalToField K B L z) =
      fun w ↦ (v.adicCompletionIntegersSemilocalHom K B L z w : w.1.adicCompletion L) := by
  rw [adicCompletionSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact v.adicCompletionSemilocalHom_toField z

/-- The canonical inclusion `𝒪_v ⊗[R] B → K_v ⊗[K] L` is injective, since `B` is flat
(torsion-free) over the Dedekind domain `R`. -/
theorem adicCompletionIntegersSemilocalToField_injective (v : HeightOneSpectrum R) :
    Function.Injective (v.adicCompletionIntegersSemilocalToField K B L) := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  have : Module.IsTorsionFree R (v.adicCompletion K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr <| by
      rw [IsScalarTower.algebraMap_eq R K (v.adicCompletion K), RingHom.coe_comp]
      exact (algebraMap K (v.adicCompletion K)).injective.comp (IsFractionRing.injective R K)
  have hinj : Function.Injective (v.adicCompletionIntegersTensorToBaseChange (K := K) (B := B)) :=
    TensorProduct.map_injective_of_flat_flat
      (v.adicCompletionIntegersToCompletion (K := K)).toLinearMap (AlgHom.id R B).toLinearMap
      Subtype.val_injective Function.injective_id
  intro x y hxy
  exact hinj ((v.adicCompletionFieldBaseChangeEquiv (K := K) (B := B) (L := L)).injective hxy)

/-- **The integral semilocal isomorphism** `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w`, for any finite
extension of Dedekind domains `R ⊆ B` (with arbitrary residue fields). -/
def adicCompletionIntegersSemilocalEquiv (v : HeightOneSpectrum R) (K B L : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.Finite R B]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L] :
    v.adicCompletionIntegers K ⊗[R] B ≃ₐ[v.adicCompletionIntegers K]
      ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        w.1.adicCompletionIntegers L :=
  AlgEquiv.ofBijective (v.adicCompletionIntegersSemilocalHom K B L)
    (show Function.Bijective (v.adicCompletionIntegersSemilocalHom K B L) from
      ⟨fun x y hxy ↦
          v.adicCompletionIntegersSemilocalToField_injective (K := K) (B := B) (L := L) <|
            (v.adicCompletionSemilocalEquiv K B L).injective <| by
              rw [adicCompletionIntegersSemilocalHom_fieldCompatibility,
                adicCompletionIntegersSemilocalHom_fieldCompatibility, hxy],
        v.adicCompletionIntegersSemilocalHom_surjective (K := K) (B := B) (L := L)⟩)

/-- `adicCompletionIntegersSemilocalEquiv` sends a pure tensor `a ⊗ b` to `(a · b)_{w ∣ v}`. -/
@[simp]
theorem adicCompletionIntegersSemilocalEquiv_tmul (v : HeightOneSpectrum R)
    (a : v.adicCompletionIntegers K) (b : B)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionIntegersSemilocalEquiv K B L (a ⊗ₜ b) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap B (w.1.adicCompletionIntegers L) b := by
  rw [adicCompletionIntegersSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact v.adicCompletionIntegersSemilocalHom_tmul a b w

/-- Compatibility of `adicCompletionIntegersSemilocalEquiv` with `adicCompletionSemilocalEquiv`. -/
theorem adicCompletionIntegersSemilocalEquiv_fieldCompatibility (v : HeightOneSpectrum R)
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    v.adicCompletionSemilocalEquiv K B L (v.adicCompletionIntegersSemilocalToField K B L z) =
      fun w ↦ (v.adicCompletionIntegersSemilocalEquiv K B L z w : w.1.adicCompletion L) :=
  v.adicCompletionIntegersSemilocalHom_fieldCompatibility z

/-- The trace of a pure integral tensor paired with an element of `L` extends the global trace
pairing to `K_v`. -/
theorem trace_adicCompletionIntegersSemilocalToField_tmul_mul (v : HeightOneSpectrum R)
    (a : v.adicCompletionIntegers K) (b : B) (d : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (v.adicCompletionIntegersSemilocalToField K B L (a ⊗ₜ b) * (1 ⊗ₜ d)) =
      (a : v.adicCompletion K) *
        algebraMap K (v.adicCompletion K) (Algebra.trace K L (algebraMap B L b * d)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) L :=
    isLocalization_algebraMapSubmonoid_of_finite (B := B) (L := L) K
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have ha : (a : v.adicCompletion K) ⊗ₜ[K] (algebraMap B L b * d) =
      (a : v.adicCompletion K) • ((1 : v.adicCompletion K) ⊗ₜ[K] (algebraMap B L b * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [adicCompletionIntegersSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    ha, map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul]

/-- The trace of `K_v ⊗[K] L` over `K_v` is the sum of the local traces of its semilocal
components. -/
theorem trace_eq_sum_trace_adicCompletionSemilocalEquiv (v : HeightOneSpectrum R)
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}]
    (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) ξ =
      ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
          (v.adicCompletionSemilocalEquiv K B L ξ w) := by
  classical
  have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      Module.Finite (v.adicCompletion K) (w.1.adicCompletion L) :=
    v.finiteDimensional_adicCompletion_of_finite (K := K) (L := L) w.1
  rw [← Algebra.trace_eq_of_algEquiv (v.adicCompletionSemilocalEquiv K B L)]
  exact Algebra.trace_pi _

open scoped Classical in
/-- An element of `L_w`, placed in the `w`-component of `K_v ⊗[K] L`, has the same trace pairing
with an element of `L` as inside `L_w`. -/
theorem trace_adicCompletionSemilocalEquiv_symm_single_mul (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (z : w.adicCompletion L) (x : L) :
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
      {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})]
  · simp [adicCompletionSemilocalEquiv_tmul]
  · intro w' _ hw'
    simp [Pi.single_eq_of_ne hw']
  · simp

/-- **Local-global trace formula**: the image in `K_v` of `Tr_{L/K}(x)` is the sum of the local
traces `Tr_{L_w/K_v}(x)` over the primes `w` of `B` lying over `v`. -/
theorem algebraMap_trace_eq_sum_trace_adicCompletion (v : HeightOneSpectrum R)
    [Fintype {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}] (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
          (algebraMap L (w.1.adicCompletion L) x) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) L :=
    isLocalization_algebraMapSubmonoid_of_finite (B := B) (L := L) K
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  rw [← Algebra.trace_baseChange_tmul (A := v.adicCompletion K) (B := L) x,
    v.trace_eq_sum_trace_adicCompletionSemilocalEquiv (B := B)]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [adicCompletionSemilocalEquiv_tmul, map_one, one_mul]

/-- **Separability passes to completions**: if `L / K` is separable and `B` is module-finite over
`R`, then `L_w / K_v` is separable (even when the residue extension is inseparable). -/
theorem isSeparable_adicCompletion_of_isSeparable [Algebra.IsSeparable K L]
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  let _ : Algebra K (w.adicCompletion L) :=
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L (w.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
    .of_algebraMap_eq fun c ↦ by
      change algebraMap L (w.adicCompletion L) (algebraMap K L c) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) (algebraMap K (v.adicCompletion K) c)
      rw [algebraMap_adicCompletionExtensionAlgebra, algebraMap_adicCompletion,
        algebraMap_adicCompletion, Function.comp_apply, Function.comp_apply,
        Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply, adicCompletionExtension_coe]
  let proj : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] w.adicCompletion L :=
    (Pi.evalAlgHom (v.adicCompletion K)
      (fun u : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} ↦ u.1.adicCompletion L)
      (⟨w, inferInstance⟩ :
        {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})).comp
      (v.adicCompletionSemilocalHom K B L)
  have hsurj : Function.Surjective proj :=
    (Function.surjective_eval _).comp (v.adicCompletionSemilocalHom_surjective (K := K) (L := L))
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := hsurj z
  induction t using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => exact map_add proj u₁ u₂ ▸ add_mem hu₁ hu₂
  | tmul a x =>
    have hproj : proj (a ⊗ₜ x) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) a *
          algebraMap L (w.adicCompletion L) x := by
      simp [proj]
    rw [hproj]
    refine mul_mem (algebraMap_mem _ a) (mem_separableClosure_iff.mpr ?_)
    exact ((Algebra.IsSeparable.isSeparable K x).map
      (IsScalarTower.toAlgHom K L (w.adicCompletion L))
      (RingHom.injective _)).tower_top (v.adicCompletion K)

end FiniteExtension

end IsDedekindDomain.HeightOneSpectrum

end
