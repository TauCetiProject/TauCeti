/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
public import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# The trace dual and different ideal under adic completion

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L` such that `B` is module-finite over
`R` and `L / K` is separable, and let `w` be a height-one prime of `B` lying over `v` in `R`, with
completed integer rings `𝒪_v ⊆ 𝒪_w` inside `K_v ⊆ L_w`. No finiteness or separability hypothesis is
placed on the residue fields at `v` and `w`.

Using the semilocal decomposition of `TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal`,
this file shows that the global complementary module `Submodule.traceDual R K 1` spans the local
complementary module `Submodule.traceDual 𝒪_v K_v 1` over `𝒪_w`, and hence that the global
different ideal extends to the completed different ideal:

```text
(differentIdeal R B).map (algebraMap B 𝒪_w) = differentIdeal 𝒪_v 𝒪_w.
```

Consequently:
* the multiplicity of `𝔪_w` in `differentIdeal 𝒪_v 𝒪_w` equals the multiplicity of `w` in
  `differentIdeal R B`, so `differentIdeal 𝒪_v 𝒪_w = 𝔪_w ^ multiplicity w (differentIdeal R B)`;
* the `𝒪_v`-length of the completed complementary-module quotient `Ĉ / 𝒪_w` and the `𝒪_v`-order of
  the discriminant of any `𝒪_v`-basis of `𝒪_w` both equal `d(w ∣ v) · f(w ∣ v)`, where `f(w ∣ v)`
  is the full inertia degree including its inseparable factor;
* when `R` and `B` are already local at `v` and `w`, the completed complementary-module quotient has
  the same length over `𝒪_v` as the uncompleted quotient has over `R`, and `B ⧸ differentIdeal R B`
  is canonically `B`-algebra isomorphic to `𝒪_w ⧸ differentIdeal 𝒪_v 𝒪_w`.

The file also records the monogenicity-free invariance of `Submodule.traceDual`, its quotient by the
integral elements, and `differentIdeal` under compatible ring equivalences, used to pass between
affine-model adic completions and intrinsic valuation completions when the residue extension is
inseparable and `𝒪_w` need not be monogenic over `𝒪_v`.

## Provenance

The trace-dual and different-ideal completion arguments generalize the number-field theorems of
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean` and
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Exponent.lean` (which assume finite residue
fields and use monogenicity for the valuation-ring comparison), in parallel with the localization
results of `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean`.

## Main results

* `TauCeti.mem_traceDual_one_iff_of_equiv`, `TauCeti.traceDualQuotientEquivOfEquiv`,
  `TauCeti.length_traceDual_quotient_eq_of_equiv`, and `TauCeti.map_differentIdeal_eq_of_equiv`:
  invariance of the complementary module, its quotient length, and the different ideal under
  compatible ring equivalences, without monogenicity.
* `IsDedekindDomain.HeightOneSpectrum.quotientPowAlgEquivAdicCompletionIntegers`: canonical
  `R`-algebra isomorphism `(R ⧸ v ^ n) ≃ₐ[R] (𝒪_v ⧸ 𝔪_v ^ n)`.
* `IsDedekindDomain.HeightOneSpectrum.traceDual_one_adicCompletionIntegers_eq_span`,
  `IsDedekindDomain.HeightOneSpectrum.dual_one_adicCompletionIntegers_eq_extended`, and
  `IsDedekindDomain.HeightOneSpectrum.differentIdeal_adicCompletionIntegers_eq_map`: trace duals
  and different ideals commute with adic completion.
* `IsDedekindDomain.HeightOneSpectrum.differentIdeal_adicCompletionIntegersSemilocal`: the global
  different decomposes in `∏_{u ∣ v} 𝒪_u` as the product of the local differents.
* `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_adicCompletionIntegers` and
  `IsDedekindDomain.HeightOneSpectrum.differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow`:
  invariance of the different exponent under completion.
* `IsDedekindDomain.HeightOneSpectrum.length_traceDual_quotient_adicCompletionIntegers`,
  `IsDedekindDomain.HeightOneSpectrum.ord_discr_adicCompletionIntegers`, and
  `IsDedekindDomain.HeightOneSpectrum.length_traceDual_quotient_adicCompletionIntegers_eq_length`:
  the length and discriminant formulas for the completed extension.

## References

* [J.-P. Serre, *Local Fields*][serre1968], Chapter III, §§3–4.
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, Proposition (2.2).
-/

public section
noncomputable section

open IsDedekindDomain Module TauCeti WithZero
open scoped TensorProduct AdicCompletionExtension nonZeroDivisors

namespace TauCeti

section Equiv

private theorem symm_comp_eq {R₁ S₁ R₂ S₂ : Type*} [Semiring R₁] [Semiring S₁]
    [Semiring R₂] [Semiring S₂] {f₁ : R₁ →+* S₁} {f₂ : R₂ →+* S₂}
    {e₁ : R₁ ≃+* R₂} {e₂ : S₁ ≃+* S₂}
    (h : f₂.comp (e₁ : R₁ →+* R₂) = (e₂ : S₁ →+* S₂).comp f₁) :
    f₁.comp (e₁.symm : R₂ →+* R₁) = (e₂.symm : S₂ →+* S₁).comp f₂ := by
  ext x
  apply e₂.injective
  have hx := RingHom.congr_fun h (e₁.symm x)
  simpa only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] using hx.symm

variable {A B K L A' B' K' L' : Type*}
  [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [CommRing A'] [CommRing B'] [Field K'] [Field L']
  [Algebra A' B'] [Algebra A' K'] [Algebra K' L'] [Algebra A' L'] [Algebra B' L']
  [IsScalarTower A' K' L'] [IsScalarTower A' B' L']
  {eA : A ≃+* A'} {eB : B ≃+* B'} {eK : K ≃+* K'} {eL : L ≃+* L'}

private theorem mem_traceDual_one_of_equiv
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L))
    {x : L} (hx : x ∈ Submodule.traceDual A K (1 : Submodule B L)) :
    eL x ∈ Submodule.traceDual A' K' (1 : Submodule B' L') := by
  rw [Submodule.mem_traceDual]
  intro a' ha'
  obtain ⟨b', rfl⟩ := Submodule.mem_one.mp ha'
  obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hx _ (Submodule.mem_one.mpr ⟨eB.symm b', rfl⟩)
  refine ⟨eA r, ?_⟩
  have hb' : algebraMap B' L' b' = eL (algebraMap B L (eB.symm b')) := by
    simpa only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] using
      RingHom.congr_fun hBL (eB.symm b')
  have hr' : algebraMap A' K' (eA r) = eK (algebraMap A K r) := by
    simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun hAK r
  rw [hr', hr, Algebra.traceForm_apply, Algebra.traceForm_apply, hb', ← map_mul,
    Algebra.trace_eq_of_equiv_equiv eK eL hKL, RingEquiv.apply_symm_apply]

/-- **Compatible ring equivalences preserve the complementary module**, with no monogenicity
assumption on `B / A`. -/
theorem mem_traceDual_one_iff_of_equiv
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L))
    {x : L} :
    eL x ∈ Submodule.traceDual A' K' (1 : Submodule B' L') ↔
      x ∈ Submodule.traceDual A K (1 : Submodule B L) :=
  ⟨fun hx ↦ by
      simpa only [RingEquiv.symm_apply_apply] using
        mem_traceDual_one_of_equiv (symm_comp_eq hAK) (symm_comp_eq hKL) (symm_comp_eq hBL) hx,
    mem_traceDual_one_of_equiv hAK hKL hBL⟩

private def traceDualSemilinearEquivOfEquiv
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L)) :
    haveI := RingHomInvPair.of_ringEquiv eB
    haveI := RingHomInvPair.of_ringEquiv_symm eB
    Submodule.traceDual A K (1 : Submodule B L) ≃ₛₗ[(eB : B →+* B')]
      Submodule.traceDual A' K' (1 : Submodule B' L') :=
  haveI := RingHomInvPair.of_ringEquiv eB
  haveI := RingHomInvPair.of_ringEquiv_symm eB
  { toFun := fun x ↦ ⟨eL x.1, (mem_traceDual_one_iff_of_equiv hAK hKL hBL).mpr x.2⟩
    invFun := fun x' ↦ ⟨eL.symm x'.1,
      (mem_traceDual_one_iff_of_equiv (symm_comp_eq hAK) (symm_comp_eq hKL)
        (symm_comp_eq hBL)).mpr x'.2⟩
    left_inv := fun x ↦ Subtype.ext (eL.symm_apply_apply x.1)
    right_inv := fun x' ↦ Subtype.ext (eL.apply_symm_apply x'.1)
    map_add' := fun x y ↦ Subtype.ext (map_add eL x.1 y.1)
    map_smul' := fun b x ↦ Subtype.ext <| by
      have hbL : algebraMap B' L' (eB b) = eL (algebraMap B L b) := by
        simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun hBL b
      simp only [RingHom.coe_coe, SetLike.val_smul, Algebra.smul_def, map_mul, hbL] }

/-- **Compatible ring equivalences induce a semilinear equivalence on complementary-module
quotients**, carrying `C / B` over `A` to `C' / B'` over `A'`. -/
def traceDualQuotientEquivOfEquiv
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L)) :
    haveI := RingHomInvPair.of_ringEquiv eA
    haveI := RingHomInvPair.of_ringEquiv_symm eA
    ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype)
      ≃ₛₗ[(eA : A →+* A')]
    ((Submodule.traceDual A' K' (1 : Submodule B' L')) ⧸
        (1 : Submodule B' L').comap
          (Submodule.traceDual A' K' (1 : Submodule B' L')).subtype) :=
  haveI := RingHomInvPair.of_ringEquiv eA
  haveI := RingHomInvPair.of_ringEquiv_symm eA
  haveI := RingHomInvPair.of_ringEquiv eB
  haveI := RingHomInvPair.of_ringEquiv_symm eB
  let f := traceDualSemilinearEquivOfEquiv hAK hKL hBL
  let eQ := Submodule.Quotient.equiv
    ((1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype)
    ((1 : Submodule B' L').comap (Submodule.traceDual A' K' (1 : Submodule B' L')).subtype)
    f <| by
      ext x'
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨b, hb⟩ := Submodule.mem_one.mp hx
        refine Submodule.mem_one.mpr ⟨eB b, ?_⟩
        have hb' : algebraMap B' L' (eB b) = eL (algebraMap B L b) := by
          simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun hBL b
        exact hb'.trans (congrArg eL hb)
      · intro hx'
        obtain ⟨b', hb'⟩ := Submodule.mem_one.mp hx'
        have hb : algebraMap B L (eB.symm b') = eL.symm (algebraMap B' L' b') := by
          simpa only [RingHom.comp_apply, RingHom.coe_coe] using
            RingHom.congr_fun (symm_comp_eq hBL) b'
        refine ⟨f.symm x',
          Submodule.mem_one.mpr ⟨eB.symm b', hb.trans (congrArg eL.symm hb')⟩,
          f.apply_symm_apply x'⟩
  { toFun := eQ
    invFun := eQ.symm
    left_inv := eQ.left_inv
    right_inv := eQ.right_inv
    map_add' := eQ.map_add'
    map_smul' := fun r q ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hrK : algebraMap A' K' (eA r) = eK (algebraMap A K r) := by
        simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun hAK r
      have hrL : algebraMap K' L' (eK (algebraMap A K r)) =
          eL (algebraMap K L (algebraMap A K r)) := by
        simpa only [RingHom.comp_apply, RingHom.coe_coe] using
          RingHom.congr_fun hKL (algebraMap A K r)
      have hrx : f (r • x) = eA r • f x := Subtype.ext <| by
        simp only [f, traceDualSemilinearEquivOfEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Submodule.coe_smul_of_tower, Algebra.smul_def,
          IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A' K' L',
          map_mul, hrK, hrL]
      exact (congrArg eQ (Submodule.Quotient.mk_smul _ r x)).symm.trans
        ((congrArg Submodule.Quotient.mk hrx).trans
          (Submodule.Quotient.mk_smul _ (eA r) (f x)).symm) }

/-- Value of `traceDualQuotientEquivOfEquiv` on a quotient representative. -/
@[simp]
theorem traceDualQuotientEquivOfEquiv_apply_mk
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L))
    (x : Submodule.traceDual A K (1 : Submodule B L)) :
    traceDualQuotientEquivOfEquiv hAK hKL hBL (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨eL x.1, (mem_traceDual_one_iff_of_equiv hAK hKL hBL).mpr x.2⟩ := (rfl)

/-- **Compatible ring equivalences preserve the length of the complementary-module quotient.** -/
theorem length_traceDual_quotient_eq_of_equiv
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L)) :
    Module.length A ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) =
      Module.length A' ((Submodule.traceDual A' K' (1 : Submodule B' L')) ⧸
        (1 : Submodule B' L').comap
          (Submodule.traceDual A' K' (1 : Submodule B' L')).subtype) := by
  have := RingHomInvPair.of_ringEquiv eA
  have := RingHomInvPair.of_ringEquiv_symm eA
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComap (traceDualQuotientEquivOfEquiv hAK hKL hBL))]

/-- **Compatible ring equivalences transport the different ideal**, with no monogenicity
assumption on `B / A`. -/
theorem map_differentIdeal_eq_of_equiv
    [IsDomain A] [IsDomain A'] [IsIntegrallyClosed A] [IsIntegrallyClosed A']
    [IsDedekindDomain B] [IsDedekindDomain B']
    [IsFractionRing A K] [IsFractionRing A' K']
    [IsIntegralClosure B A L] [IsIntegralClosure B' A' L']
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A' B']
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hAK : (algebraMap A' K').comp (eA : A →+* A') = (eK : K →+* K').comp (algebraMap A K))
    (hKL : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L))
    (hBL : (algebraMap B' L').comp (eB : B →+* B') = (eL : L →+* L').comp (algebraMap B L)) :
    (differentIdeal A B).map (eB : B →+* B') = differentIdeal A' B' := by
  have : Algebra.IsSeparable K' L' := Algebra.IsSeparable.of_equiv_equiv eK eL hKL
  have : FiniteDimensional K' L' := by
    let := eK.toRingHom.toAlgebra
    let : Algebra K' L := ((algebraMap K L).comp eK.symm.toRingHom).toAlgebra
    have : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq fun x ↦
      congrArg (algebraMap K L) (eK.symm_apply_apply x).symm
    have : FiniteDimensional K' L := Module.Finite.of_restrictScalars_finite K K' L
    let eKL' : L ≃ₐ[K'] L' :=
      { eL with
        commutes' := fun x ↦ by
          simpa [RingHom.algebraMap_toAlgebra] using (RingHom.congr_fun hKL (eK.symm x)).symm }
    exact Module.Finite.equiv eKL'.toLinearEquiv
  ext y'
  have hmem : y' ∈ (differentIdeal A B).map (eB : B →+* B') ↔
      eB.symm y' ∈ differentIdeal A B := by
    rw [Ideal.mem_map_iff_of_surjective (eB : B →+* B') eB.surjective]
    exact ⟨fun ⟨y, hy, hy'⟩ ↦ by subst hy'; simpa using hy,
      fun hy ↦ ⟨eB.symm y', hy, eB.apply_symm_apply y'⟩⟩
  rw [hmem, mem_differentIdeal_iff_forall_mem_traceDual (K := K) (L := L),
    mem_differentIdeal_iff_forall_mem_traceDual (K := K') (L := L')]
  have hy' : algebraMap B' L' y' = eL (algebraMap B L (eB.symm y')) := by
    simpa only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] using
      RingHom.congr_fun hBL (eB.symm y')
  constructor
  · intro h x' hx'
    have hx : eL.symm x' ∈ Submodule.traceDual A K (1 : Submodule B L) :=
      (mem_traceDual_one_iff_of_equiv (symm_comp_eq hAK) (symm_comp_eq hKL)
        (symm_comp_eq hBL)).mpr hx'
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp (h (eL.symm x') hx)
    refine Submodule.mem_one.mpr ⟨eB b, ?_⟩
    have hb' : algebraMap B' L' (eB b) = eL (algebraMap B L b) := by
      simpa only [RingHom.comp_apply, RingHom.coe_coe] using RingHom.congr_fun hBL b
    rw [hb', hb, map_mul, eL.apply_symm_apply, ← hy']
  · intro h x hx
    have hx' : eL x ∈ Submodule.traceDual A' K' (1 : Submodule B' L') :=
      (mem_traceDual_one_iff_of_equiv hAK hKL hBL).mpr hx
    obtain ⟨b', hb'⟩ := Submodule.mem_one.mp (h (eL x) hx')
    refine Submodule.mem_one.mpr ⟨eB.symm b', ?_⟩
    apply eL.injective
    have hb : eL (algebraMap B L (eB.symm b')) = algebraMap B' L' b' := by
      simpa only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] using
        (RingHom.congr_fun hBL (eB.symm b')).symm
    rw [hb, hb', hy', map_mul]

end Equiv

end TauCeti

namespace IsDedekindDomain.HeightOneSpectrum

section QuotientPow

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- The `n`-th power of the maximal ideal of `𝒪_v` contracts to `v ^ n` in `R`. -/
@[simp]
theorem under_maximalIdeal_pow_adicCompletionIntegers (n : ℕ) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n).under R = v.asIdeal ^ n := by
  ext r
  rw [Ideal.under_def, Ideal.mem_comap, v.mem_maximalIdeal_pow_iff (K := K),
    v.mem_asIdeal_pow_iff_valued_algebraMap_le (K := K),
    IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K) (v.adicCompletion K),
    ValuationSubring.algebraMap_apply]

/-- **Canonical `R`-algebra isomorphism `(R ⧸ v ^ n) ≃ₐ[R] (𝒪_v ⧸ 𝔪_v ^ n)`.** No finiteness
assumption on the residue field is needed. -/
def quotientPowAlgEquivAdicCompletionIntegers (n : ℕ) :
    (R ⧸ v.asIdeal ^ n) ≃ₐ[R]
      (v.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective
      (Ideal.quotientMap (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (algebraMap R (v.adicCompletionIntegers K))
        (le_of_eq (v.under_maximalIdeal_pow_adicCompletionIntegers (K := K) n).symm))
      ⟨Ideal.quotientMap_injective'
          (le_of_eq (v.under_maximalIdeal_pow_adicCompletionIntegers (K := K) n)),
        fun y ↦ by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
          obtain ⟨a, ha⟩ := v.exists_valued_sub_le (K := K) x n
          refine ⟨Ideal.Quotient.mk _ a, ?_⟩
          rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
          rw [v.mem_maximalIdeal_pow_iff (K := K)]
          push_cast [IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
            (v.adicCompletion K)]
          rw [Valuation.map_sub_swap]
          exact ha⟩)
    fun _ ↦ rfl

/-- Value of `quotientPowAlgEquivAdicCompletionIntegers` on a quotient representative. -/
@[simp]
theorem quotientPowAlgEquivAdicCompletionIntegers_apply_mk (n : ℕ) (r : R) :
    v.quotientPowAlgEquivAdicCompletionIntegers (K := K) n (Ideal.Quotient.mk (v.asIdeal ^ n) r) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (algebraMap R (v.adicCompletionIntegers K) r) := (rfl)

end QuotientPow

section DifferentCompletion

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  [Module.IsTorsionFree R B] [Module.Finite R B]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

include B in
private theorem trace_tmul_mul_smul (a : v.adicCompletion K) (x b y : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((a ⊗ₜ x) * (1 ⊗ₜ b)) • ((1 : v.adicCompletion K) ⊗ₜ[K] y) =
      a ⊗ₜ[K] (Algebra.trace K L (x * b) • y) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have ha : a ⊗ₜ[K] (x * b) = a • ((1 : v.adicCompletion K) ⊗ₜ[K] (x * b)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul, Algebra.trace_baseChange_tmul]
  simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
    ← Algebra.smul_def, TensorProduct.smul_tmul]

variable {K L} in
/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{L/K}(x bᵢ) yᵢ` for every
`x ∈ L`, then `z = ∑ᵢ Tr_{L_w/K_v}(z bᵢ) yᵢ` for every `z ∈ L_w`. -/
theorem sum_trace_adicCompletion_mul_smul_algebraMap_eq {ι : Type*} [Fintype ι] (b y : ι → L)
    (h : ∀ x : L, ∑ i, Algebra.trace K L (x * b i) • y i = x) (z : w.adicCompletion L) :
    ∑ i, Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) (b i)) • algebraMap L (w.adicCompletion L) (y i) =
      z := by
  classical
  let wAbove : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} := ⟨w, inferInstance⟩
  have hF (ξ : v.adicCompletion K ⊗[K] L) :
      ∑ i, Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) (ξ * (1 ⊗ₜ b i)) •
        ((1 : v.adicCompletion K) ⊗ₜ[K] y i) = ξ := by
    induction ξ using TensorProduct.inductionOn with
    | add ξ η hξ hη =>
      conv_rhs => rw [← hξ, ← hη]
      simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
    | tmul a x =>
      conv_rhs => rw [← h x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ trace_tmul_mul_smul (B := B) K L v a x (b i) (y i)
  have h' := congrArg (fun ξ ↦ v.adicCompletionSemilocalEquiv K B L ξ wAbove)
    (hF ((v.adicCompletionSemilocalEquiv K B L).symm (Pi.single wAbove z)))
  simp only [wAbove, AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, adicCompletionSemilocalEquiv_tmul, map_one, one_mul,
    trace_adicCompletionSemilocalEquiv_symm_single_mul] at h'
  exact h'

private theorem trace_adicCompletionIntegersSemilocalToField_mul_mem {d : L}
    (hd : d ∈ Submodule.traceDual R K (1 : Submodule B L))
    (t : v.adicCompletionIntegers K ⊗[R] B) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (v.adicCompletionIntegersSemilocalToField K B L t * (1 ⊗ₜ d)) ∈
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).range := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    rw [map_add, add_mul, map_add]
    exact add_mem ht hu
  | tmul a x =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
    refine ⟨a * algebraMap R (v.adicCompletionIntegers K) r, ?_⟩
    rw [v.trace_adicCompletionIntegersSemilocalToField_tmul_mul K B L a x d,
      mul_comm (algebraMap B L x), ← Algebra.traceForm_apply, ← hr]
    simp only [map_mul, ValuationSubring.algebraMap_apply, Algebra.algebraMap_self_apply,
      algebraMap_adicCompletionIntegers_apply, algebraMap_adicCompletion, Function.comp_apply]

private theorem algebraMap_mem_traceDual_adicCompletionIntegers {d : L}
    (hd : d ∈ Submodule.traceDual R K (1 : Submodule B L)) :
    algebraMap L (w.adicCompletion L) d ∈
      Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) := by
  classical
  let wAbove : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} := ⟨w, inferInstance⟩
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  obtain ⟨t, ht⟩ := (v.adicCompletionIntegersSemilocalEquiv K B L).surjective (Pi.single wAbove z)
  have hξ : v.adicCompletionIntegersSemilocalToField K B L t =
      (v.adicCompletionSemilocalEquiv K B L).symm (Pi.single wAbove
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) z)) := by
    rw [AlgEquiv.eq_symm_apply, adicCompletionIntegersSemilocalEquiv_fieldCompatibility, ht]
    funext w'
    obtain rfl | hw' := eq_or_ne w' wAbove
    · simp
    · simp [Pi.single_eq_of_ne hw']
  rw [Algebra.traceForm_apply, mul_comm,
    ← v.trace_adicCompletionSemilocalEquiv_symm_single_mul K B L w, ← hξ]
  exact trace_adicCompletionIntegersSemilocalToField_mul_mem K L v hd t

variable [Algebra.IsSeparable K L]

/-- **The completed complementary module is spanned by the global one**, with no assumption on the
residue fields at `v` and `w`. -/
theorem traceDual_one_adicCompletionIntegers_eq_span :
    Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) =
      Submodule.span (w.adicCompletionIntegers L)
        (algebraMap L (w.adicCompletion L) '' Submodule.traceDual R K (1 : Submodule B L)) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have := Module.finitePresentation_of_finite R B
  have : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨n, b, y, hy, hb⟩ := exists_sum_trace_mul_smul_eq R K (L := L) (B := B)
    rw [← v.sum_trace_adicCompletion_mul_smul_algebraMap_eq w (fun i ↦ algebraMap B L (b i))
      y hb z]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
      ⟨_, (w.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (b i)).symm⟩)
    rw [Algebra.traceForm_apply] at hc
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)
  · rintro _ ⟨d, hd, rfl⟩
    exact algebraMap_mem_traceDual_adicCompletionIntegers K L v w hd

/-- **Trace-dual fractional ideals commute with completion**, with no assumption on the residue
fields at `v` and `w`. -/
theorem dual_one_adicCompletionIntegers_eq_extended :
    haveI : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
    haveI := v.adicCompletionIntegers_isIntegralClosure_of_finite K L w
    haveI : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
      v.adicCompletion_moduleFinite_of_finite K L w
    haveI := v.adicCompletion_isSeparable K B L w
    FractionalIdeal.dual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : FractionalIdeal (w.adicCompletionIntegers L)⁰ (w.adicCompletion L)) =
      (FractionalIdeal.dual R K (1 : FractionalIdeal B⁰ L)).extended (w.adicCompletion L)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite K L w
  have : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
    v.adicCompletion_moduleFinite_of_finite K L w
  have := v.adicCompletion_isSeparable K B L w
  have hmap : IsLocalization.map (S := L) (w.adicCompletion L)
      (algebraMap B (w.adicCompletionIntegers L))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))) =
      algebraMap L (w.adicCompletion L) := by
    refine IsFractionRing.ringHom_ext (A := B) fun x ↦ ?_
    rw [IsLocalization.map_eq, w.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers]
  have hdual : ((FractionalIdeal.dual R K (1 : FractionalIdeal B⁰ L)) : Set L) =
      Submodule.traceDual R K (1 : Submodule B L) := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_dual_one,
    FractionalIdeal.coeToSubmodule_extended_eq_span, hmap, hdual]
  exact v.traceDual_one_adicCompletionIntegers_eq_span K L w

/-- **The different ideal commutes with completion**, with no assumption on the residue fields at
`v` and `w`. -/
theorem differentIdeal_adicCompletionIntegers_eq_map :
    differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      (differentIdeal R B).map (algebraMap B (w.adicCompletionIntegers L)) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite K L w
  have : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
    v.adicCompletion_moduleFinite_of_finite K L w
  have := v.adicCompletion_isSeparable K B L w
  rw [← FractionalIdeal.coeIdeal_inj (K := w.adicCompletion L),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) (w.adicCompletion L)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))),
    ← FractionalIdeal.extendedHom'_apply, coeIdeal_differentIdeal R K L B,
    coeIdeal_differentIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L)
      (w.adicCompletionIntegers L), map_inv₀, FractionalIdeal.extendedHom'_apply,
    v.dual_one_adicCompletionIntegers_eq_extended K L w]

/-- **The different of the integral semilocal algebra decomposes as the product of the local
differents above `v`.** -/
theorem differentIdeal_adicCompletionIntegersSemilocal :
    ((differentIdeal R B).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] v.adicCompletionIntegers K ⊗[R] B)).map
        (v.adicCompletionIntegersSemilocalEquiv K B L) =
      Ideal.pi fun u ↦
        differentIdeal (v.adicCompletionIntegers K) (u.1.adicCompletionIntegers L) := by
  have hmap : ((differentIdeal R B).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] v.adicCompletionIntegers K ⊗[R] B)).map
        (v.adicCompletionIntegersSemilocalEquiv K B L) = (differentIdeal R B).map
        ((v.adicCompletionIntegersSemilocalEquiv K B L).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : B →ₐ[R] _).toRingHom) :=
    Ideal.map_map (Algebra.TensorProduct.includeRight : B →ₐ[R] _).toRingHom
      (v.adicCompletionIntegersSemilocalEquiv K B L).toRingEquiv.toRingHom
  rw [hmap]
  apply Ideal.piOrderIso.injective
  funext u
  let := u.2
  simp only [Ideal.piOrderIso, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    AlgHom.toRingHom_eq_coe]
  rw [Ideal.map_evalRingHom_pi, Ideal.map_map,
    v.differentIdeal_adicCompletionIntegers_eq_map K L u.1]
  congr 1
  ext b
  simp

/-- **The exponent of the completed different at `𝔪_w` equals the global exponent at `w`**, even
when the residue extension at `w` is inseparable. -/
@[simp]
theorem multiplicity_differentIdeal_adicCompletionIntegers :
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      multiplicity w.asIdeal (differentIdeal R B) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  rw [v.differentIdeal_adicCompletionIntegers_eq_map K L w]
  exact w.multiplicity_map_adicCompletionIntegers (K := L) (differentIdeal R B)
    (differentIdeal_ne_bot_of_isSeparable (K := K) (L := L))

/-- **The completed different ideal is `𝔪_w ^ d(w ∣ v)`.** -/
theorem differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow :
    differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^
        multiplicity w.asIdeal (differentIdeal R B) := by
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite K L w
  have : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
    v.adicCompletion_moduleFinite_of_finite K L w
  have := v.adicCompletion_isSeparable K B L w
  have h0 : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) ≠ ⊥ :=
    differentIdeal_ne_bot_of_isSeparable (K := v.adicCompletion K) (L := w.adicCompletion L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (w.adicCompletionIntegers L)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  have hpow : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ n := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have hmult : multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
      (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) = n := by
    rw [hpow, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance)]
  rw [← v.multiplicity_differentIdeal_adicCompletionIntegers K L w, hmult, hpow]

omit [Module.IsTorsionFree R B] [Module.Finite R B] [Algebra.IsSeparable K L] in
private theorem finrank_residueField_adicCompletionIntegers :
    Module.finrank (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
        (IsLocalRing.ResidueField (w.adicCompletionIntegers L)) =
      w.asIdeal.inertiaDeg R :=
  (Algebra.finrank_eq_of_equiv_equiv
    (Ideal.quotEquivOfEq (rfl : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = _))
    (Ideal.quotEquivOfEq (rfl : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = _))
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))).trans <| by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)),
      v.inertiaDeg_maximalIdeal_adicCompletionIntegers w]

/-- **The complementary-module length formula on the completion**: the `𝒪_v`-length of `Ĉ / 𝒪_w`
is `d(w ∣ v) · f(w ∣ v)`, where `f(w ∣ v)` is the full inertia degree including its inseparable
factor. -/
theorem length_traceDual_quotient_adicCompletionIntegers :
    Module.length (v.adicCompletionIntegers K)
        ((Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
            (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L))) ⧸
          (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)).comap
            (Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
              (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L))).subtype) =
      (multiplicity w.asIdeal (differentIdeal R B) : ℕ∞) * w.asIdeal.inertiaDeg R := by
  have := v.adicCompletionIntegers_moduleFinite_of_finite K L w
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite K L w
  have : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
    v.adicCompletion_moduleFinite_of_finite K L w
  have := v.adicCompletion_isSeparable K B L w
  rw [TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    v.multiplicity_differentIdeal_adicCompletionIntegers K L w,
    finrank_residueField_adicCompletionIntegers K L v w]

/-- **The discriminant valuation formula on the completion**: for any `𝒪_v`-basis `b` of `𝒪_w`,
`ord_{𝒪_v}(discr_{𝒪_v}(b)) = d(w ∣ v) · f(w ∣ v)`, including the inseparable residue factor. -/
theorem ord_discr_adicCompletionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :
    Ring.ord (v.adicCompletionIntegers K) (Algebra.discr (v.adicCompletionIntegers K) b) =
      (multiplicity w.asIdeal (differentIdeal R B) : ℕ∞) * w.asIdeal.inertiaDeg R := by
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite K L w
  have := v.adicCompletion_isSeparable K B L w
  rw [TauCeti.ord_discr_eq_multiplicity_mul_finrank (v.adicCompletion K) (w.adicCompletion L) b,
    v.multiplicity_differentIdeal_adicCompletionIntegers K L w,
    finrank_residueField_adicCompletionIntegers K L v w]

/-- When `B` is already a discrete valuation ring, `B ⧸ differentIdeal R B` is canonically
`B`-algebra isomorphic to `𝒪_w ⧸ differentIdeal 𝒪_v 𝒪_w`. -/
def quotientDifferentIdealAlgEquivAdicCompletionIntegers [IsDiscreteValuationRing B] :
    (B ⧸ differentIdeal R B) ≃ₐ[B]
      (w.adicCompletionIntegers L ⧸
        differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :=
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have hw : w.asIdeal = IsLocalRing.maximalIdeal B :=
    w.isMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (IsLocalRing.le_maximalIdeal w.isMaximal.ne_top)
  have hB0 : differentIdeal R B ≠ ⊥ := differentIdeal_ne_bot_of_isSeparable (K := K) (L := L)
  have hBpow : differentIdeal R B = w.asIdeal ^ multiplicity w.asIdeal (differentIdeal R B) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hB0 hϖ
    have hpow : differentIdeal R B = w.asIdeal ^ n := by
      rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, hw]
    have hmult : multiplicity w.asIdeal (differentIdeal R B) = n := by
      rw [hpow, multiplicity_pow_self_of_prime w.prime]
    rw [hmult, hpow]
  AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq hBpow).trans
      ((w.quotientPowAlgEquivAdicCompletionIntegers (K := L)
        (multiplicity w.asIdeal (differentIdeal R B))).toRingEquiv.trans
        (Ideal.quotEquivOfEq
          (v.differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow K L w).symm)))
    fun _ ↦ rfl

/-- Value of `quotientDifferentIdealAlgEquivAdicCompletionIntegers` on a quotient representative. -/
@[simp]
theorem quotientDifferentIdealAlgEquivAdicCompletionIntegers_apply_mk
    [IsDiscreteValuationRing B] (b : B) :
    v.quotientDifferentIdealAlgEquivAdicCompletionIntegers K L w
        (Ideal.Quotient.mk (differentIdeal R B) b) =
      Ideal.Quotient.mk
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (algebraMap B (w.adicCompletionIntegers L) b) := (rfl)

/-- **Invariance of the complementary-module quotient length under completion** for a local base
`R` and discrete valuation ring `B` upstairs, with no assumption of residue-field separability. -/
theorem length_traceDual_quotient_adicCompletionIntegers_eq_length
    [IsLocalRing R] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap R B)] :
    Module.length (v.adicCompletionIntegers K)
        ((Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
            (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L))) ⧸
          (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)).comap
            (Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
              (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L))).subtype) =
      Module.length R ((Submodule.traceDual R K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual R K (1 : Submodule B L)).subtype) := by
  have : FiniteDimensional K L := Module.Finite.of_isLocalization R B R⁰
  have hv : v.asIdeal = IsLocalRing.maximalIdeal R :=
    v.isMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (IsLocalRing.le_maximalIdeal v.isMaximal.ne_top)
  have hw : w.asIdeal = IsLocalRing.maximalIdeal B :=
    w.isMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (IsLocalRing.le_maximalIdeal w.isMaximal.ne_top)
  have hfin : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) =
      w.asIdeal.inertiaDeg R :=
    (Algebra.finrank_eq_of_equiv_equiv (Ideal.quotEquivOfEq hv.symm)
      (Ideal.quotEquivOfEq hw.symm)
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))).trans
      (Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal).symm
  rw [v.length_traceDual_quotient_adicCompletionIntegers K L w,
    TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank, hfin, hw]

end DifferentCompletion

end IsDedekindDomain.HeightOneSpectrum

end
end
