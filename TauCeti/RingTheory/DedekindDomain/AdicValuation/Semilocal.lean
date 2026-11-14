/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.RamificationInertia.Basic
public import TauCeti.RingTheory.AdicCompletion.Pi
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Multiplicity
public import TauCeti.RingTheory.Ideal.PrimesOver
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# The semilocal decomposition of an extension of Dedekind domains

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L` and `B` module-finite over `R`, and
let `v` be a height-one prime of `R`. Completing at the finitely many height-one primes `w` of `B`
lying over `v` decomposes the scalar extensions of `B` to `𝒪_v` and of `L` to `K_v` as finite
products:

```text
𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w,    K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w.
```

Neither finiteness of the residue fields nor separability of `L / K` or of the residue extensions
is assumed. Each completed integer ring `𝒪_w` is therefore a finite free `𝒪_v`-module and the
integral closure of `𝒪_v` in `L_w`, of rank `[L_w : K_v] = e(w ∣ v) · f(w ∣ v)` where `f(w ∣ v)`
is the full inertia degree including any inseparable factor. When `L / K` is separable, each local
extension `L_w / K_v` is separable as well, and the global trace decomposes as the sum of the local
traces.

## Proof outline and provenance

This file generalizes the number-field semilocal decompositions of
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Basic.lean`,
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Integers.lean`, and
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Norm/Trace.lean` to arbitrary Dedekind
domains. Over a number field, `𝒪_v` is compact because its residue field is finite, so finitely
generated `𝒪_v`-submodules of `∏_{w ∣ v} 𝒪_w` are closed and density suffices for surjectivity.
Without finite residue fields `𝒪_v` need not be compact, so the order of the argument is reversed:

1. Simultaneous approximation (`exists_forall_valued_sub_le`) shows that `B` meets every coset of
   `𝔪_v • ∏_{w ∣ v} 𝒪_w`, and Nakayama's lemma over the `𝔪_v`-adically complete ring `𝒪_v`
   (`surjective_of_mkQ_comp_surjective`) lifts this to surjectivity of
   `𝒪_v ⊗[R] B → ∏_{w ∣ v} 𝒪_w`.
2. Projecting onto each factor `w ∣ v` gives `Module.Finite 𝒪_v 𝒪_w`, hence `Module.Free 𝒪_v 𝒪_w`,
   `IsIntegralClosure 𝒪_w 𝒪_v L_w`, `FiniteDimensional K_v L_w`, and
   `[L_w : K_v] = e(w ∣ v) · f(w ∣ v)` from `Ideal.sum_ramification_inertia_eq_finrank` applied to
   the local extension `𝒪_v ⊆ 𝒪_w`.
3. Clearing denominators by powers of a uniformizer of `𝒪_v` makes `K_v ⊗[K] L → ∏_{w ∣ v} L_w`
   surjective; comparing dimensions via `∑_{w ∣ v} e(w ∣ v) · f(w ∣ v) = [L : K]` makes it an
   isomorphism, and flatness of `B` over `R` injects `𝒪_v ⊗[R] B` into `K_v ⊗[K] L`.

In contrast to `TauCeti/RingTheory/DedekindDomain/AdicValuation/IntegralClosure.lean` and
`TauCeti/RingTheory/DedekindDomain/AdicValuation/LocalDegree.lean`, which assume `[Finite (B ⧸ w)]`
so that `K_v` and `L_w` are locally compact local fields, the `_of_finite` theorems here require
only `[Module.Finite R B]` and allow arbitrary (possibly infinite or inseparable) residue fields.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSemilocalHom` and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSemilocalEquiv`: the integral
  semilocal map and `𝒪_v`-algebra equivalence `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSemilocalToField`: the canonical map
  `𝒪_v ⊗[R] B →ₐ[R] K_v ⊗[K] L`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionSemilocalHom` and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionSemilocalEquiv`: the field semilocal map and
  `K_v`-algebra equivalence `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletion_isScalarTower`: `K`, `K_v`, and `L_w` form a
  scalar tower for the canonical completion algebra.
* `IsDedekindDomain.HeightOneSpectrum.ramificationIdx_maximalIdeal_adicCompletionIntegers` and
  `IsDedekindDomain.HeightOneSpectrum.inertiaDeg_maximalIdeal_adicCompletionIntegers`: the
  ramification index and inertia degree of `𝒪_w / 𝒪_v` equal those of `w` over `R`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_moduleFinite_of_finite`,
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_moduleFree_of_finite`,
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isIntegralClosure_of_finite`, and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletion_moduleFinite_of_finite`: local finiteness,
  freeness, and integral closure for `𝒪_w / 𝒪_v` and `L_w / K_v` when `B` is finite over `R`.
* `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_of_finite` and
  `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletionIntegers_of_finite`:
  `[L_w : K_v] = finrank 𝒪_v 𝒪_w = e(w ∣ v) · f(w ∣ v)`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletion_isSeparable`: separability of `L / K` passes
  to each completed extension `L_w / K_v`.
* `IsDedekindDomain.HeightOneSpectrum.trace_adicCompletionSemilocalEquiv`,
  `IsDedekindDomain.HeightOneSpectrum.trace_adicCompletionSemilocalEquiv_symm_single_mul`, and
  `IsDedekindDomain.HeightOneSpectrum.algebraMap_trace_eq_sum_trace_adicCompletion`: the global
  trace and trace pairing decompose across the completions above `v`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3) and
  Corollary (8.4).
* [J.-P. Serre, *Local Fields*][serre1968], Chapter II, §3, Theorem 1.
-/

public section
noncomputable section

open IsDedekindDomain Module TauCeti WithZero
open scoped TensorProduct AdicCompletionExtension nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

section LocalInvariants

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- `K`, `K_v`, and `L_w` form a scalar tower for the canonical completion algebra. -/
theorem adicCompletion_isScalarTower :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_adicCompletionExtensionAlgebra]
    exact (v.adicCompletionExtension_coe K L w x).symm

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletion_isScalarTower

/-- **The ramification index of the completed integer rings is the global one**, with no finiteness
assumption on the residue fields or on `B` over `R`. -/
@[simp]
theorem ramificationIdx_maximalIdeal_adicCompletionIntegers :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers K) =
      w.asIdeal.ramificationIdx R := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have hv0 : Ideal.map (algebraMap R B) v.asIdeal ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R B)).not.mpr v.ne_bot
  have hmv0 : Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ≠ ⊥ := by
    rw [algebraMap_adicCompletionIntegersExtensionAlgebra]
    exact (Ideal.map_eq_bot_iff_of_injective
      (adicCompletionIntegersExtension_injective K L v w)).not.mpr
      (IsDiscreteValuationRing.not_a_field _)
  have hmap : Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) =
        Ideal.map (algebraMap B (w.adicCompletionIntegers L))
          (Ideal.map (algebraMap R B) v.asIdeal) := by
    rw [← v.map_asIdeal_adicCompletionIntegers (K := K), Ideal.map_map, Ideal.map_map]
    congr 1
    ext r
    simp only [RingHom.comp_apply, algebraMap_adicCompletionIntegersExtensionAlgebra,
      adicCompletionIntegersExtension_algebraMap]
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hmv0, hmap,
    w.multiplicity_map_adicCompletionIntegers _ hv0,
    ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hv0]

/-- **The inertia degree of the completed integer rings is the global one**, with no finiteness or
separability assumption on the residue fields. -/
@[simp]
theorem inertiaDeg_maximalIdeal_adicCompletionIntegers :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
        (v.adicCompletionIntegers K) =
      w.asIdeal.inertiaDeg R := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)),
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv
    (v.residueFieldEquivAdicCompletionIntegers (K := K))
    (w.residueFieldEquivAdicCompletionIntegers (K := L)) (RingHom.ext fun x ↦ ?_)).symm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.Quotient.algebraMap_mk_of_liesOver,
    w.residueFieldEquivAdicCompletionIntegers_apply_mk,
    v.residueFieldEquivAdicCompletionIntegers_apply_mk,
    algebraMap_adicCompletionIntegersExtensionAlgebra,
    adicCompletionIntegersExtension_algebraMap]

end LocalInvariants

section SemilocalDefs

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K B L : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R)

/-- The canonical `𝒪_v`-algebra map `𝒪_v ⊗[R] B →ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w` sending `a ⊗ b` to
`(a · b)_w` across the height-one primes `w` of `B` lying over `v`. -/
def adicCompletionIntegersSemilocalHom :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
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
          -- Expose the composite `R`-algebra structure installed just above so the compatibility
          -- of `adicCompletionIntegersExtension` with `R → B` applies directly.
          change algebraMap B (w.1.adicCompletionIntegers L) (algebraMap R B r) =
            algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
              (algebraMap R (v.adicCompletionIntegers K) r)
          rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
            adicCompletionIntegersExtension_algebraMap] })
    fun _ _ ↦ .all _ _

/-- The canonical `K_v`-algebra map `K_v ⊗[K] L →ₐ[K_v] ∏_{w ∣ v} L_w` sending `a ⊗ x` to
`(a · x)_w` across the height-one primes `w` of `B` lying over `v`. -/
def adicCompletionSemilocalHom :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦ IsScalarTower.toAlgHom K L (w.1.adicCompletion L))
    fun _ _ ↦ .all _ _

variable {K B L v}

/-- Value of `adicCompletionIntegersSemilocalHom` on a pure tensor. -/
@[simp]
theorem adicCompletionIntegersSemilocalHom_tmul (a : v.adicCompletionIntegers K) (b : B)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    adicCompletionIntegersSemilocalHom K B L v (a ⊗ₜ b) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap B (w.1.adicCompletionIntegers L) b := by
  simp [adicCompletionIntegersSemilocalHom]

/-- Value of `adicCompletionSemilocalHom` on a pure tensor. -/
@[simp]
theorem adicCompletionSemilocalHom_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    adicCompletionSemilocalHom K B L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) x := by
  simp [adicCompletionSemilocalHom]

end SemilocalDefs

section SinglePlaceFinite

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K B L : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  [Module.Finite R B] (v : HeightOneSpectrum R)

/-- **Surjectivity of the integral semilocal map**, proved without residue-field finiteness by
simultaneous approximation modulo `𝔪_v` and Nakayama's lemma over the complete local ring `𝒪_v`. -/
theorem adicCompletionIntegersSemilocalHom_surjective :
    Function.Surjective (adicCompletionIntegersSemilocalHom K B L v) := by
  classical
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  let mv := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      IsHausdorff mv (w.1.adicCompletionIntegers L) :=
    .of_map (IsLocalRing.map_maximalIdeal_le
      (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)))
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin' R B
  let F : (Fin m → v.adicCompletionIntegers K) →ₗ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
    (adicCompletionIntegersSemilocalHom K B L v).toLinearMap ∘ₗ
      Fintype.linearCombination (v.adicCompletionIntegers K)
        (fun i ↦ (1 : _) ⊗ₜ[R] s (Pi.single i 1))
  suffices hF : Function.Surjective F by
    intro y
    obtain ⟨x, hx⟩ := hF y
    exact ⟨_, hx⟩
  refine surjective_of_mkQ_comp_surjective (I := mv) fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπm : π ∈ mv := by
    dsimp only [mv]
    rw [Irreducible.maximalIdeal_eq hπ]
    exact Ideal.mem_span_singleton_self π
  have hπv : Valued.v (π : v.adicCompletion K) = exp (-1) :=
    v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ
  let S : Finset (HeightOneSpectrum B) :=
    ((Set.finite_coe_iff (s := {w : HeightOneSpectrum B | w.asIdeal.LiesOver v.asIdeal})).mp
      (finite_liesOver B v)).toFinset
  let yFull : ∀ w : HeightOneSpectrum B, w.adicCompletionIntegers L := fun w ↦
    if hw : w.asIdeal.LiesOver v.asIdeal then y ⟨w, hw⟩ else 0
  let n : HeightOneSpectrum B → ℕ := fun w ↦ v.asIdeal.ramificationIdx' w.asIdeal
  obtain ⟨b, hb⟩ := exists_forall_valued_sub_le (K := L) S yFull n
  obtain ⟨c, rfl⟩ := hs b
  have hsc : s c = ∑ i, c i • s (Pi.single i 1) := by
    have hc : c = ∑ i, c i • Pi.single i (1 : R) := funext fun j ↦ by simp [Pi.single_apply]
    conv_lhs => rw [hc, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ map_smul s (c i) (Pi.single i 1)
  refine ⟨fun i ↦ algebraMap R (v.adicCompletionIntegers K) (c i), ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hFc : F (fun i ↦ algebraMap R (v.adicCompletionIntegers K) (c i)) =
      fun (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) ↦
        algebraMap B (w.1.adicCompletionIntegers L) (s c) := by
    ext w
    rw [hsc]
    simp [F, Fintype.linearCombination_apply, map_sum, Algebra.smul_def,
      adicCompletionIntegersExtension_algebraMap]
  rw [hFc]
  -- At each `w ∣ v`, the image of `π` has valuation `exp (-e_w)`, matching the approximation
  -- precision `n w = e_w`; dividing the error by `π` exhibits it in `mv • ⊤`.
  have hq : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      ∃ q : w.1.adicCompletionIntegers L,
        algebraMap B (w.1.adicCompletionIntegers L) (s c) - y w = π • q := by
    intro w
    let E : w.1.adicCompletion L :=
      (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) π :
        w.1.adicCompletion L)
    have hEval : Valued.v E = exp (-(n w.1 : ℤ)) := by
      dsimp only [E]
      rw [algebraMap_adicCompletionIntegersExtensionAlgebra, coe_adicCompletionIntegersExtension,
        valued_adicCompletionExtension, hπv, ← exp_nsmul]
      simp [n]
    have hE0 : E ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hEval
      exact exp_ne_zero hEval.symm
    have hbw := hb w.1 (Set.Finite.mem_toFinset _ |>.mpr w.2)
    have hyw : yFull w.1 = y w := by simp [yFull, w.2]
    rw [hyw] at hbw
    have hdiv : (((algebraMap B (w.1.adicCompletionIntegers L) (s c) - y w :
        w.1.adicCompletionIntegers L) : w.1.adicCompletion L) / E) ∈
          w.1.adicCompletionIntegers L := by
      rw [mem_adicCompletionIntegers, map_div₀, AddSubgroupClass.coe_sub, Valuation.map_sub_swap,
        ← ValuationSubring.algebraMap_apply _
          (algebraMap B (w.1.adicCompletionIntegers L) (s c)),
        ← w.1.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (K := L),
        ← IsScalarTower.algebraMap_apply B L (w.1.adicCompletion L)]
      exact div_le_one_of_le₀ (hbw.trans_eq hEval.symm) zero_le
    refine ⟨⟨_, hdiv⟩, Subtype.ext ?_⟩
    rw [Algebra.smul_def, Subring.coe_mul, mul_div_cancel₀ _ hE0]
  choose q hq using hq
  have hsub : (fun (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) ↦
      algebraMap B (w.1.adicCompletionIntegers L) (s c)) - y = π • q := funext hq
  rw [hsub]
  exact Submodule.smul_mem_smul hπm Submodule.mem_top

variable {B} (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- **`𝒪_w` is a finite `𝒪_v`-module** whenever `B` is module-finite over `R`, with no finiteness
or separability assumption on the residue fields or on `L / K`. -/
theorem adicCompletionIntegers_moduleFinite_of_finite :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  classical
  let proj := (Pi.evalAlgHom (v.adicCompletionIntegers K)
    (fun u : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} ↦
      u.1.adicCompletionIntegers L) ⟨w, inferInstance⟩).comp
    (adicCompletionIntegersSemilocalHom K B L v)
  refine Module.Finite.of_surjective proj.toLinearMap fun y ↦ ?_
  obtain ⟨t, ht⟩ := adicCompletionIntegersSemilocalHom_surjective K B L v
    (Pi.single (⟨w, inferInstance⟩ : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal}) y)
  exact ⟨t, by simpa [proj] using congrFun ht ⟨w, inferInstance⟩⟩

/-- **`𝒪_w` is a free `𝒪_v`-module** whenever `B` is module-finite over `R`. -/
theorem adicCompletionIntegers_moduleFree_of_finite :
    Module.Free (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  have := adicCompletionIntegers_moduleFinite_of_finite K L v w
  infer_instance

/-- **`𝒪_w` is the integral closure of `𝒪_v` in `L_w`** whenever `B` is module-finite over `R`. -/
theorem adicCompletionIntegers_isIntegralClosure_of_finite :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) := by
  have := adicCompletionIntegers_moduleFinite_of_finite K L v w
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

/-- **`L_w` is a finite extension of `K_v`** whenever `B` is module-finite over `R`, with no
finiteness assumption on the residue fields. -/
theorem adicCompletion_moduleFinite_of_finite :
    Module.Finite (v.adicCompletion K) (w.adicCompletion L) := by
  have := adicCompletionIntegers_moduleFinite_of_finite K L v w
  exact Module.Finite.of_isLocalization (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)⁰

/-- **The rank of `𝒪_w` over `𝒪_v` equals the local degree `[L_w : K_v]`.** -/
@[simp]
theorem finrank_adicCompletionIntegers_of_finite :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := adicCompletionIntegers_moduleFinite_of_finite K L v w
  exact (IsFractionRing.finrank_eq (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletionIntegers L) (w.adicCompletion L)).symm

/-- **The local degree of a completion is `e(w ∣ v) · f(w ∣ v)`** whenever `B` is module-finite
over `R`, with no finiteness or separability assumption on the residue fields. -/
@[simp]
theorem finrank_adicCompletion_of_finite :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx R * w.asIdeal.inertiaDeg R := by
  have := adicCompletionIntegers_moduleFinite_of_finite K L v w
  let mv := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  let mw := IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)
  let u0 : mv.primesOver (w.adicCompletionIntegers L) := ⟨mw, inferInstance, inferInstance⟩
  let _ : Unique (mv.primesOver (w.adicCompletionIntegers L)) :=
    { default := u0
      uniq := fun ⟨Q, hQ, hQlies⟩ ↦ Subtype.ext <| by
        have hQ0 : Q ≠ ⊥ := by
          rintro rfl
          have hmv0 : mv ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
          have hbot : mv = ⊥ := by
            rw [hQlies.over, Ideal.under_def, algebraMap_adicCompletionIntegersExtensionAlgebra]
            exact Ideal.comap_bot_of_injective _ (adicCompletionIntegersExtension_injective K L v w)
          exact hmv0 hbot
        exact (hQ.isMaximal hQ0).eq_of_le (IsLocalRing.maximalIdeal.isMaximal _).ne_top
          (IsLocalRing.le_maximalIdeal hQ.ne_top) }
  have hdef : (default : mv.primesOver (w.adicCompletionIntegers L)) = u0 := rfl
  rw [← finrank_adicCompletionIntegers_of_finite K L v w,
    ← Ideal.sum_ramification_inertia_eq_finrank mv (w.adicCompletionIntegers L),
    Finset.univ_unique, Finset.sum_singleton, hdef]
  exact congrArg₂ (· * ·)
    (ramificationIdx_maximalIdeal_adicCompletionIntegers v w)
    (inertiaDeg_maximalIdeal_adicCompletionIntegers v w)

end SinglePlaceFinite

section Decomposition

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K B L : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  [Module.IsTorsionFree R B] [Module.Finite R B] (v : HeightOneSpectrum R)

attribute [local instance] Fintype.ofFinite in
/-- **The local degrees above `v` sum to the global degree `[L : K]`.** -/
theorem sum_finrank_adicCompletion_eq_finrank :
    ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      Module.finrank K L := by
  let _ : Fintype (v.asIdeal.primesOver B) :=
    Fintype.ofEquiv _ (liesOverEquivPrimesOver B v)
  calc ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
          Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)
      = ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
          w.1.asIdeal.ramificationIdx R * w.1.asIdeal.inertiaDeg R :=
        Finset.sum_congr rfl fun w _ ↦ finrank_adicCompletion_of_finite K L v w.1
    _ = ∑ Q : v.asIdeal.primesOver B,
          (Q : Ideal B).ramificationIdx R * (Q : Ideal B).inertiaDeg R :=
        Fintype.sum_equiv (liesOverEquivPrimesOver B v) _ _ fun w ↦ by
          rw [liesOverEquivPrimesOver_apply]
    _ = Module.finrank R B := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal B
    _ = Module.finrank K L := (IsFractionRing.finrank_eq R K B L).symm

private def integralFieldBaseChangeEquiv :
    v.adicCompletion K ⊗[R] B ≃ₐ[v.adicCompletion K] v.adicCompletion K ⊗[K] L :=
  (Algebra.TensorProduct.cancelBaseChange R K (v.adicCompletion K)
      (v.adicCompletion K) B).symm.trans
    (Algebra.TensorProduct.congr (.refl : v.adicCompletion K ≃ₐ[v.adicCompletion K]
      v.adicCompletion K) (Algebra.IsPushout.equiv R K B L))

@[simp]
private theorem integralFieldBaseChangeEquiv_tmul (a : v.adicCompletion K) (b : B) :
    integralFieldBaseChangeEquiv K B L v (a ⊗ₜ b) = a ⊗ₜ algebraMap B L b := by
  simp [integralFieldBaseChangeEquiv, Algebra.IsPushout.equiv_tmul]

private def integralFieldBaseChangeAlgHom :
    v.adicCompletion K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[K] L :=
  { (integralFieldBaseChangeEquiv K B L v).toRingEquiv.toRingHom with
    commutes' := fun r ↦ by
      -- The domain is an `R`-algebra via the left tensor factor, whereas
      -- `integralFieldBaseChangeEquiv` is `K_v`-linear; exposing pure tensors bridges them.
      change integralFieldBaseChangeEquiv K B L v
          (algebraMap R (v.adicCompletion K) r ⊗ₜ[R] (1 : B)) =
        algebraMap R (v.adicCompletion K) r ⊗ₜ[K] (1 : L)
      rw [integralFieldBaseChangeEquiv_tmul, map_one] }

private def adicCompletionIntegersToCompletion :
    v.adicCompletionIntegers K →ₐ[R] v.adicCompletion K :=
  IsScalarTower.toAlgHom R (v.adicCompletionIntegers K) (v.adicCompletion K)

private def integralTensorToBaseChange :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[R] B :=
  { (Algebra.TensorProduct.map (adicCompletionIntegersToCompletion K v)
      (AlgHom.id R B)).toRingHom with
    commutes' := fun _ ↦ rfl }

/-- The canonical `R`-algebra inclusion `𝒪_v ⊗[R] B →ₐ[R] K_v ⊗[K] L`. -/
def adicCompletionIntegersSemilocalToField :
    v.adicCompletionIntegers K ⊗[R] B →ₐ[R] v.adicCompletion K ⊗[K] L :=
  (integralFieldBaseChangeAlgHom K B L v).comp (integralTensorToBaseChange K B v)

variable {K B L v} in
/-- Value of `adicCompletionIntegersSemilocalToField` on a pure tensor. -/
@[simp]
theorem adicCompletionIntegersSemilocalToField_tmul (a : v.adicCompletionIntegers K) (b : B) :
    adicCompletionIntegersSemilocalToField K B L v (a ⊗ₜ b) =
      (a : v.adicCompletion K) ⊗ₜ algebraMap B L b := by
  exact integralFieldBaseChangeEquiv_tmul K B L v (a : v.adicCompletion K) b

/-- The canonical map `𝒪_v ⊗[R] B →ₐ[R] K_v ⊗[K] L` is injective. -/
theorem adicCompletionIntegersSemilocalToField_injective :
    Function.Injective (adicCompletionIntegersSemilocalToField K B L v) := by
  have : Module.IsTorsionFree R (v.adicCompletion K) := Module.IsTorsionFree.trans K
  have hinj : Function.Injective (integralTensorToBaseChange K B v) := by
    -- Expose the underlying linear tensor map; both `v.adicCompletion K` and `B` are torsion-free
    -- hence flat over Dedekind `R`.
    change Function.Injective (TensorProduct.map
      (adicCompletionIntegersToCompletion K v).toLinearMap (AlgHom.id R B).toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id
  exact (integralFieldBaseChangeEquiv K B L v).injective.comp hinj

variable {K B L v} in
/-- After inclusion into the completed fields, `adicCompletionIntegersSemilocalHom` agrees with
`adicCompletionSemilocalHom`. -/
theorem adicCompletionIntegersSemilocalHom_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    adicCompletionSemilocalHom K B L v (adicCompletionIntegersSemilocalToField K B L v z) =
      fun w ↦ (adicCompletionIntegersSemilocalHom K B L v z w : w.1.adicCompletion L) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext w
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (congrFun hx w) (congrFun hy w)
  | tmul a b =>
    funext w
    simp only [adicCompletionIntegersSemilocalToField_tmul, adicCompletionSemilocalHom_tmul,
      adicCompletionIntegersSemilocalHom_tmul]
    rw [Subring.coe_mul, ← IsScalarTower.algebraMap_apply B L (w.1.adicCompletion L),
      algebraMap_adicCompletionIntegersExtensionAlgebra,
      algebraMap_adicCompletionExtensionAlgebra, coe_adicCompletionIntegersExtension,
      algebraMap_adicCompletionIntegers_apply, algebraMap_adicCompletion, Function.comp_apply]

attribute [local instance] Fintype.ofFinite in
/-- **Surjectivity of the field semilocal map**: a uniformizer power from `𝒪_v` clears denominators
into `∏_{w ∣ v} 𝒪_w`, where `adicCompletionIntegersSemilocalHom_surjective` lifts them. -/
theorem adicCompletionSemilocalHom_surjective :
    Function.Surjective (adicCompletionSemilocalHom K B L v) := by
  classical
  intro y
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπv : Valued.v (π : v.adicCompletion K) = exp (-1) :=
    v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπv
    exact exp_ne_zero hπv.symm
  -- At each `w ∣ v`, some power of `π` multiplies `y w` into `𝒪_w`.
  have hpow : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      ∃ n : ℕ, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ((π : v.adicCompletion K) ^ n)
        * y w ∈ w.1.adicCompletionIntegers L := by
    intro w
    rcases eq_or_ne (y w) 0 with hy0 | hy0
    · exact ⟨0, by simp [hy0]⟩
    have hvy0 : Valued.v (y w) ≠ 0 := (Valued.v).ne_zero_iff.mpr hy0
    let m : ℕ := (WithZero.log (Valued.v (y w))).toNat
    refine ⟨m, ?_⟩
    rw [mem_adicCompletionIntegers, map_mul, map_pow, algebraMap_adicCompletionExtensionAlgebra,
      map_pow, valued_adicCompletionExtension, hπv, ← pow_mul, ← exp_nsmul,
      ← exp_log hvy0, ← exp_add, ← exp_zero, exp_le_exp]
    have he : 1 ≤ v.asIdeal.ramificationIdx' w.1.asIdeal := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.1.asIdeal v.ne_bot]
      exact Ideal.ramificationIdx_pos R w.1.asIdeal
    have hm : WithZero.log (Valued.v (y w)) ≤ m := by dsimp only [m]; omega
    simp only [nsmul_eq_mul, Int.natCast_mul]
    nlinarith
  choose n hn using hpow
  let N : ℕ := ∑ w, n w
  have hN : ∀ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ((π : v.adicCompletion K) ^ N)
        * y w ∈ w.1.adicCompletionIntegers L := by
    intro w
    have hle : n w ≤ N := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)
    have hsplit : N = (N - n w) + n w := (Nat.sub_add_cancel hle).symm
    rw [hsplit, pow_add, map_mul, mul_assoc]
    refine mul_mem ?_ (hn w)
    rw [algebraMap_adicCompletionExtensionAlgebra, ← SubmonoidClass.coe_pow,
      ← coe_adicCompletionIntegersExtension]
    exact (adicCompletionIntegersExtension K L v w.1 (π ^ (N - n w))).2
  obtain ⟨t, ht⟩ := adicCompletionIntegersSemilocalHom_surjective K B L v
    fun w ↦ ⟨_, hN w⟩
  refine ⟨((π : v.adicCompletion K) ^ N)⁻¹ • adicCompletionIntegersSemilocalToField K B L v t, ?_⟩
  funext w
  rw [map_smul, adicCompletionIntegersSemilocalHom_fieldCompatibility, ht, Pi.smul_apply,
    Algebra.smul_def, map_inv₀, ← mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero _).mpr (pow_ne_zero N hπ0)), one_mul]

attribute [local instance] Fintype.ofFinite in
/-- **Injectivity of the field semilocal map**, deduced from surjectivity and equality of
`K_v`-vector space dimensions. -/
theorem adicCompletionSemilocalHom_injective :
    Function.Injective (adicCompletionSemilocalHom K B L v) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) :=
    adicCompletion_moduleFinite_of_finite K L v w.1
  have hdim : Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) =
      Module.finrank (v.adicCompletion K)
        ((w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) →
          w.1.adicCompletion L) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange,
      sum_finrank_adicCompletion_eq_finrank K B L v]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (adicCompletionSemilocalHom K B L v).toLinearMap)).mpr
    (adicCompletionSemilocalHom_surjective K B L v)

/-- **The field semilocal decomposition** `K_v ⊗[K] L ≃ₐ[K_v] ∏_{w ∣ v} L_w` for an arbitrary
module-finite extension `R ⊆ B` of Dedekind domains. -/
def adicCompletionSemilocalEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  -- Keep the `Bijective` ascription explicit so `AlgEquiv.ofBijective_apply` rewrites cleanly at
  -- `instances` transparency when unfolding this equivalence on pure tensors.
  AlgEquiv.ofBijective (adicCompletionSemilocalHom K B L v)
    (show Function.Bijective (adicCompletionSemilocalHom K B L v) from
      ⟨adicCompletionSemilocalHom_injective K B L v,
        adicCompletionSemilocalHom_surjective K B L v⟩)

/-- **Injectivity of the integral semilocal map**, via inclusion into `K_v ⊗[K] L`. -/
theorem adicCompletionIntegersSemilocalHom_injective :
    Function.Injective (adicCompletionIntegersSemilocalHom K B L v) := by
  intro x y hxy
  apply adicCompletionIntegersSemilocalToField_injective K B L v
  apply adicCompletionSemilocalHom_injective K B L v
  rw [adicCompletionIntegersSemilocalHom_fieldCompatibility,
    adicCompletionIntegersSemilocalHom_fieldCompatibility, hxy]

/-- **The integral semilocal decomposition** `𝒪_v ⊗[R] B ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w` for an arbitrary
module-finite extension `R ⊆ B` of Dedekind domains. -/
def adicCompletionIntegersSemilocalEquiv :
    v.adicCompletionIntegers K ⊗[R] B ≃ₐ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
  -- Keep the `Bijective` ascription explicit for the same transparency reason as
  -- `adicCompletionSemilocalEquiv`.
  AlgEquiv.ofBijective (adicCompletionIntegersSemilocalHom K B L v)
    (show Function.Bijective (adicCompletionIntegersSemilocalHom K B L v) from
      ⟨adicCompletionIntegersSemilocalHom_injective K B L v,
        adicCompletionIntegersSemilocalHom_surjective K B L v⟩)

variable {K B L v}

/-- Value of `adicCompletionSemilocalEquiv` on a pure tensor. -/
@[simp]
theorem adicCompletionSemilocalEquiv_tmul (a : v.adicCompletion K) (x : L)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    adicCompletionSemilocalEquiv K B L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) x := by
  rw [adicCompletionSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact adicCompletionSemilocalHom_tmul a x w

/-- Value of `adicCompletionIntegersSemilocalEquiv` on a pure tensor. -/
@[simp]
theorem adicCompletionIntegersSemilocalEquiv_tmul (a : v.adicCompletionIntegers K) (b : B)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    adicCompletionIntegersSemilocalEquiv K B L v (a ⊗ₜ b) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap B (w.1.adicCompletionIntegers L) b := by
  rw [adicCompletionIntegersSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact adicCompletionIntegersSemilocalHom_tmul a b w

/-- Compatibility of the integral and field semilocal equivalences under inclusion into the
completed fields. -/
theorem adicCompletionIntegersSemilocalEquiv_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[R] B) :
    adicCompletionSemilocalEquiv K B L v
        (adicCompletionIntegersSemilocalToField K B L v z) =
      fun w ↦ (adicCompletionIntegersSemilocalEquiv K B L v z w : w.1.adicCompletion L) := by
  rw [adicCompletionSemilocalEquiv, adicCompletionIntegersSemilocalEquiv,
    AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply]
  exact adicCompletionIntegersSemilocalHom_fieldCompatibility z

variable (K B L v)

/-- **Separability passes to completions.** If `L / K` is separable and `B` is module-finite over
`R`, then each completed extension `L_w / K_v` is separable, even when the residue extension at `w`
is inseparable. -/
theorem adicCompletion_isSeparable [Algebra.IsSeparable K L]
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  classical
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  rintro z -
  obtain ⟨ξ, hξ⟩ := (adicCompletionSemilocalEquiv K B L v).surjective
    (Pi.single (⟨w, inferInstance⟩ : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal}) z)
  have hw := congrFun hξ ⟨w, inferInstance⟩
  simp only [Pi.single_eq_same] at hw
  rw [← hw]
  let proj : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] w.adicCompletion L :=
    (Pi.evalAlgHom (v.adicCompletion K)
      (fun u : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} ↦ u.1.adicCompletion L)
      ⟨w, inferInstance⟩).comp (adicCompletionSemilocalEquiv K B L v).toAlgHom
  -- View evaluation at `w` as an algebra homomorphism out of `K_v ⊗[K] L` so induction on tensors
  -- reduces to pure tensors `a ⊗ x`, whose images are products of scalars from `K_v` and images of
  -- separable elements from `L`.
  change proj ξ ∈ separableClosure (v.adicCompletion K) (w.adicCompletion L)
  clear hξ hw
  induction ξ using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | tmul a x =>
    have ha : proj (a ⊗ₜ[K] x) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) a *
          algebraMap L (w.adicCompletion L) x := by
      simp [proj]
    rw [ha]
    refine mul_mem
      ((separableClosure (v.adicCompletion K) (w.adicCompletion L)).algebraMap_mem a) ?_
    rw [mem_separableClosure_iff]
    exact IsSeparable.tower_top (v.adicCompletion K)
      ((Algebra.IsSeparable.isSeparable K x).map
        (IsScalarTower.toAlgHom K L (w.adicCompletion L))
        (algebraMap L (w.adicCompletion L)).injective)

/-- On a pure integral tensor paired with a global element, the trace in `K_v ⊗[K] L` extends the
global trace pairing. -/
theorem trace_adicCompletionIntegersSemilocalToField_tmul_mul
    (a : v.adicCompletionIntegers K) (b : B) (d : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (adicCompletionIntegersSemilocalToField K B L v (a ⊗ₜ b) * (1 ⊗ₜ d)) =
      (a : v.adicCompletion K) *
        algebraMap K (v.adicCompletion K) (Algebra.trace K L (algebraMap B L b * d)) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have ha : (a : v.adicCompletion K) ⊗ₜ[K] (algebraMap B L b * d) =
      (a : v.adicCompletion K) • ((1 : v.adicCompletion K) ⊗ₜ[K] (algebraMap B L b * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [adicCompletionIntegersSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul]

attribute [local instance] Fintype.ofFinite in
/-- **The trace of `K_v ⊗[K] L` over `K_v` is the sum of the local traces above `v`.** -/
theorem trace_adicCompletionSemilocalEquiv (ξ : v.adicCompletion K ⊗[K] L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) ξ =
      ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
          (adicCompletionSemilocalEquiv K B L v ξ w) := by
  have _ (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) :=
    adicCompletion_moduleFinite_of_finite K L v w.1
  rw [← Algebra.trace_eq_of_algEquiv (adicCompletionSemilocalEquiv K B L v)]
  exact Algebra.trace_pi _

open scoped Classical in
attribute [local instance] Fintype.ofFinite in
/-- Placing `z ∈ L_w` in the `w`-component of `K_v ⊗[K] L` identifies its trace pairing against a
global element `x ∈ L` with the local trace pairing in `L_w / K_v`. -/
theorem trace_adicCompletionSemilocalEquiv_symm_single_mul
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (z : w.adicCompletion L) (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((adicCompletionSemilocalEquiv K B L v).symm
          (Pi.single (⟨w, inferInstance⟩ :
            {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal}) z) * (1 ⊗ₜ x)) =
      Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) x) := by
  classical
  rw [trace_adicCompletionSemilocalEquiv K B L v, Finset.sum_eq_single
    (⟨w, inferInstance⟩ : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal})]
  · simp [adicCompletionSemilocalEquiv_tmul]
  · intro w' _ hw'
    simp [Pi.single_eq_of_ne hw']
  · simp

attribute [local instance] Fintype.ofFinite in
/-- **The global trace is the sum of the local traces** at the completions above `v`. -/
theorem algebraMap_trace_eq_sum_trace_adicCompletion (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
        Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
          (algebraMap L (w.1.adicCompletion L) x) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  rw [← Algebra.trace_baseChange_tmul (A := v.adicCompletion K) (B := L) x,
    trace_adicCompletionSemilocalEquiv K B L v]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp

end Decomposition

end IsDedekindDomain.HeightOneSpectrum

end
end
