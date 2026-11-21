/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Abelianization.Transfer
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.NumberField.Frobenius.Tower
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Open
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.DecompositionOrbits
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.RingTheory.Ideal.PrimesOver
import TauCeti.RingTheory.IsGaloisGroup.Dedekind

/-!
# Transfer functoriality of the global Artin map in the ground field

Let `K ⊆ E ⊆ L` be number fields with `L/K` finite Galois. Extending idele classes along
`ideleClassExtension K E : C_K →* C_E` intertwines the global Artin maps of `L/K` and of `L/E`
with the group-theoretic transfer (Verlagerung)
`Group.Abelianization.transferOfInjective : Gal(L/K)^ab →* Gal(L/E)^ab` along the inclusion
`Gal(L/E) ↪ Gal(L/K)`: for every `c ∈ C_K`,

```text
Art_{L/E} (i_{E/K} c) = Ver (Art_{L/K} c)      in Gal(L/E)^ab
```

(`globalArtinMap_ideleClassExtension`). Dual to `globalArtinMap_ideleClassNormMap` and paired with
`globalArtinMap_comp`, this completes the functoriality of `globalArtinMap` in towers of number
fields; it is the global form of the transfer diagram `ClassFormation.artinMap_groundInclusion` of
an abstract class formation.

The proof reduces to unramified uniformizers via ray-subgroup extensionality. Both sides are
homomorphisms `C_K →* Gal(L/E)^ab` whose kernels contain open preimages of idele-class norm groups
(`isOpen_range_ideleClassNormMap`, `continuous_ideleClassExtension`), so both vanish on a ray
subgroup of `C_K` whose modulus can be enlarged to include every prime in `ramifiedSupport K L`.
By `ideleClassGroup_hom_ext_of_raySubgroup_le`, it suffices to compare the two maps on the idele
class of a uniformizer `π ∈ K_vˣ` at a finite place `v` unramified in `L`.

At such a place `v`, fix a prime `Q₀` of `𝓞 L` above `v` and an arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q₀`. Extending `ofAdicCompletion v π` to `C_E` splits over the places `w` of `E`
above `v` (`ideleClassExtension_ofAdicCompletion`), and at each `w` the image of `π` in `E_w`
remains a uniformizer because `E_w / K_v` is unramified. On the Galois side, `⟨σ⟩` is the
decomposition group of `Q₀` (`Ideal.zpowers_eq_stabilizer_of_isArithFrobAt`), so the `⟨σ⟩`-orbits
on `Gal(L/K) ⧸ H` correspond to the primes `w` of `𝓞 E` above `v`
(`Ideal.orbitQuotientEquivPrimesOver`), with orbit size `f(w | v)`
(`Ideal.card_orbit_stabilizer_coset`). The transfer factor `g_q⁻¹ * σ ^ f(w | v) * g_q` is the
relative arithmetic Frobenius in `Gal(L/E)` at `g_q⁻¹ • Q₀`
(`NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg`), matching the `w`-factor on the
idele side term by term.

## Main results

* `TauCeti.ClassFieldTheory.globalArtinMap_ideleClassExtension`: the global Artin symbol over an
  intermediate field of an extended idele class is the group-theoretic transfer of its global Artin
  symbol over the ground field.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–5.
* J. Neukirch, *Algebraic Number Theory*, Chapter IV, §6 and Chapter VI, §5.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField GlobalNumberFields _root_.MulAction
open scoped AdicCompletionExtension Pointwise

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [Algebra K E]
  {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsGalois K L] [IsGalois E L]

/-- At a finite place `v` of `K` unramified in `L`, with a prime `Q₀` of `𝓞 L` above `v` and an
arithmetic Frobenius `σ ∈ Gal(L/K)` at `Q₀`, the minimal period of `σ • ·` on a coset
`c ∈ Gal(L/K) ⧸ Gal(L/E)` equals the inertia degree over `𝓞 K` of the prime of `𝓞 E` below
`c.out⁻¹ • Q₀`. -/
private lemma minimalPeriod_smul_coset_eq_inertiaDeg
    {v : HeightOneSpectrum (𝓞 K)} (hv_unram : v ∉ TauCeti.NumberField.ramifiedSupport K L)
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsMaximal] [Q₀.LiesOver v.asIdeal]
    {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ Q₀)
    (c : Gal(L/K) ⧸ (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)).range) :
    Function.minimalPeriod (σ • ·) c = ((c.out⁻¹ • Q₀).under (𝓞 E)).inertiaDeg (𝓞 K) := by
  classical
  let H : Subgroup Gal(L/K) := (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)).range
  have : IsGaloisGroup H (𝓞 E) (𝓞 L) :=
    IsGaloisGroup.of_isIntegralClosure_range_restrictScalarsHom K E L (𝓞 E) (𝓞 L)
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := 𝓞 K) (K := K) (M := L) (B := 𝓞 L)
  have : FaithfulSMul (𝓞 E) L := .trans (𝓞 E) E L
  have : FaithfulSMul (𝓞 E) (𝓞 L) := .tower_bot (𝓞 E) (𝓞 L) L
  have : Module.Finite (𝓞 K) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)
  have : Algebra.IsUnramifiedAt (𝓞 K) Q₀ :=
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v hv_unram Q₀
  have : Algebra.IsUnramifiedAt (𝓞 K) (c.out⁻¹ • Q₀) :=
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v hv_unram (c.out⁻¹ • Q₀)
  have : Algebra.IsUnramifiedAt (𝓞 K) ((c.out⁻¹ • Q₀).under (𝓞 E)) :=
    .of_liesOver (𝓞 K) ((c.out⁻¹ • Q₀).under (𝓞 E)) (c.out⁻¹ • Q₀)
  have hzpow : Subgroup.zpowers σ = stabilizer Gal(L/K) Q₀ :=
    Ideal.zpowers_eq_stabilizer_of_isArithFrobAt Q₀ hσ
  have h1 : Nat.card (orbit (Subgroup.zpowers σ) c) = Function.minimalPeriod (σ • ·) c :=
    (Nat.card_congr (orbitZPowersEquiv σ c)).trans (Nat.card_zmod _)
  have hc := Ideal.card_orbit_stabilizer_coset v.asIdeal Q₀ H (𝓞 E) c
  have hcoset :
      (Ideal.primesOverOfCoset v.asIdeal Q₀ H (𝓞 E) c).val = (c.out⁻¹ • Q₀).under (𝓞 E) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    exact Ideal.coe_primesOverOfCoset_mk v.asIdeal Q₀ H (𝓞 E) c.out
  rw [hcoset, Ideal.ramificationIdx_eq_one ((c.out⁻¹ • Q₀).under (𝓞 E)) (𝓞 K), one_mul] at hc
  have horb : (orbit (Subgroup.zpowers σ) c : Set (Gal(L/K) ⧸ H)) =
      orbit (stabilizer Gal(L/K) Q₀) c := by
    ext y
    simp only [mem_orbit_iff, Subtype.exists, Subgroup.mk_smul, hzpow]
  rw [horb, hc] at h1
  exact h1.symm

omit [NumberField K] [NumberField E] [IsGalois E L] in
/-- Given an arithmetic Frobenius `σ ∈ Gal(L/K)` at `Q₀` and a coset `c ∈ Gal(L/K) ⧸ Gal(L/E)`
whose `σ`-orbit period equals the inertia degree of `(c.out⁻¹ • Q₀).under (𝓞 E)` over `𝓞 K`, the
preimage in `Gal(L/E)` of `c.out⁻¹ * σ ^ minimalPeriod (σ • ·) c * c.out` is an arithmetic
Frobenius over `𝓞 E` at `c.out⁻¹ • Q₀`. -/
private lemma isArithFrobAt_ofInjective_symm_out_conj_pow
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsMaximal] {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ Q₀)
    (c : Gal(L/K) ⧸ (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)).range)
    [Algebra.IsUnramifiedAt (𝓞 K) (c.out⁻¹ • Q₀)]
    (hperiod : Function.minimalPeriod (σ • ·) c = ((c.out⁻¹ • Q₀).under (𝓞 E)).inertiaDeg (𝓞 K)) :
    IsArithFrobAt (𝓞 E)
      ((MonoidHom.ofInjective (AlgEquiv.restrictScalarsHom_injective K (S := E) (A := L))).symm
        ⟨c.out⁻¹ * σ ^ Function.minimalPeriod (σ • ·) c * c.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem _ σ c⟩)
      (c.out⁻¹ • Q₀) := by
  have hσ_conj : IsArithFrobAt (𝓞 K) (c.out⁻¹ * σ * c.out) (c.out⁻¹ • Q₀) := by
    simpa only [mul_assoc, inv_inv] using hσ.conj c.out⁻¹
  rw [NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg hσ_conj,
    ← AlgEquiv.restrictScalarsHom_apply,
    MonoidHom.apply_ofInjective_symm (AlgEquiv.restrictScalarsHom_injective K (S := E) (A := L)),
    ← hperiod]
  simpa [MulAut.conj_apply, mul_assoc] using
    (map_pow (MulAut.conj c.out⁻¹) σ (Function.minimalPeriod (σ • ·) c))

/-- Single-place transfer identity at a finite place `v` of `K` unramified in `L` and a uniformizer
`π ∈ K_vˣ`. -/
private lemma globalArtinMap_ideleClassExtension_ofAdicCompletion_of_isUniformizer
    (ι : L →ₐ[K] SeparableClosure K) (ι' : L →ₐ[E] SeparableClosure E)
    {v : HeightOneSpectrum (𝓞 K)} (hv_unram : v ∉ TauCeti.NumberField.ramifiedSupport K L)
    {π : (v.adicCompletion K)ˣ} (hπ : IsUniformizer (v.adicCompletion K) π) :
    (globalArtinMap E L ι' (.ofMul (ideleClassExtension K E
        (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π)))).toMul =
      Group.Abelianization.transferOfInjective
        (f := (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)))
        (AlgEquiv.restrictScalarsHom_injective K)
        (globalArtinMap K L ι (.ofMul (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π))).toMul := by
  classical
  let f : Gal(L/E) →* Gal(L/K) := AlgEquiv.restrictScalarsHom K
  have hf : Function.Injective f := AlgEquiv.restrictScalarsHom_injective K
  let H : Subgroup Gal(L/K) := f.range
  have : IsGaloisGroup H (𝓞 E) (𝓞 L) :=
    IsGaloisGroup.of_isIntegralClosure_range_restrictScalarsHom K E L (𝓞 E) (𝓞 L)
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := 𝓞 K) (K := K) (M := L) (B := 𝓞 L)
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := 𝓞 E) (K := E) (M := L) (B := 𝓞 L)
  have : FaithfulSMul (𝓞 K) E := .trans (𝓞 K) K E
  have : FaithfulSMul (𝓞 K) (𝓞 E) := .tower_bot (𝓞 K) (𝓞 E) E
  have : FaithfulSMul (𝓞 E) L := .trans (𝓞 E) E L
  have : FaithfulSMul (𝓞 E) (𝓞 L) := .tower_bot (𝓞 E) (𝓞 L) L
  have : Module.Finite (𝓞 K) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)
  obtain ⟨wL₀, hwL₀⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  let Q₀ : Ideal (𝓞 L) := wL₀.asIdeal
  have : Q₀.IsPrime := wL₀.isPrime
  have : Q₀.IsMaximal := wL₀.isMaximal
  have : Q₀.LiesOver v.asIdeal := hwL₀ ▸ inferInstance
  have : Algebra.IsUnramifiedAt (𝓞 K) Q₀ :=
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v hv_unram Q₀
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q₀ wL₀.ne_bot
  have hzpow : Subgroup.zpowers σ = stabilizer Gal(L/K) Q₀ :=
    Ideal.zpowers_eq_stabilizer_of_isArithFrobAt Q₀ hσ
  -- Bijection between `⟨σ⟩`-orbits on `Gal(L/K) ⧸ H` and finite places of `E` above `v`.
  let e₁ : Quotient (orbitRel (Subgroup.zpowers σ) (Gal(L/K) ⧸ H)) ≃
      orbitRel.Quotient (stabilizer Gal(L/K) Q₀) (Gal(L/K) ⧸ H) :=
    Quotient.congr (Equiv.refl _) fun _ _ ↦ by rw [Equiv.refl_apply, Equiv.refl_apply, hzpow]
  let e₂ : orbitRel.Quotient (stabilizer Gal(L/K) Q₀) (Gal(L/K) ⧸ H) ≃
      v.asIdeal.primesOver (𝓞 E) :=
    Ideal.orbitQuotientEquivPrimesOver v.asIdeal Q₀ H (𝓞 E)
  let e := (e₁.trans e₂).trans (HeightOneSpectrum.liesOverEquivPrimesOver (𝓞 E) v).symm
  let _ : Fintype {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofEquiv _ e
  let φ : IdeleClassGroup (𝓞 E) E →* Group.Abelianization Gal(L/E) :=
    MonoidHom.toAdditive.symm (globalArtinMap E L ι')
  have hφ : (globalArtinMap E L ι' (.ofMul (ideleClassExtension K E
      (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π)))).toMul =
      φ (ideleClassExtension K E (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π)) := by
    simp only [φ, MonoidHom.toAdditive_symm_apply_apply]
  rw [hφ, ideleClassExtension_ofAdicCompletion, finprod_eq_prod_of_fintype, map_prod,
    globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt L ι v Q₀ hσ π,
    (isUniformizer_def π).1 hπ, toAdd_ofAdd, zpow_one, toMul_ofMul,
    Group.Abelianization.transferOfInjective_eq_prod_quotient_orbitRel_zpowers_quot,
    ← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  set g_q : Gal(L/K) := q.out.out
  set Q_q : Ideal (𝓞 L) := g_q⁻¹ • Q₀
  have : Algebra.IsUnramifiedAt (𝓞 K) Q_q :=
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v hv_unram Q_q
  have hw_q_ideal : (e q).val.asIdeal = Q_q.under (𝓞 E) := by
    have hq : e₁ q = _root_.Quotient.mk'' (g_q : Gal(L/K) ⧸ H) := by
      conv_lhs => rw [← Quotient.out_eq q, ← QuotientGroup.out_eq' q.out]
      rw [Quotient.congr_mk, Equiv.refl_apply, ← Quotient.mk''_eq_mk]
    rw [Equiv.trans_apply, Equiv.trans_apply,
      HeightOneSpectrum.liesOverEquivPrimesOver_symm_apply, hq,
      Ideal.orbitQuotientEquivPrimesOver_mk, Ideal.coe_primesOverOfCoset_mk]
  have : Q_q.LiesOver (e q).val.asIdeal := ⟨hw_q_ideal⟩
  have : Algebra.IsUnramifiedAt (𝓞 K) (e q).val.asIdeal :=
    .of_liesOver (𝓞 K) (e q).val.asIdeal Q_q
  have : Algebra.IsUnramifiedAt (𝓞 E) Q_q := .of_restrictScalars (𝓞 K) Q_q
  set τ_q : Gal(L/E) := (MonoidHom.ofInjective hf).symm
    ⟨g_q⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out * g_q,
      QuotientGroup.out_conj_pow_minimalPeriod_mem H σ q.out⟩
  have hτ_q : IsArithFrobAt (𝓞 E) τ_q Q_q :=
    isArithFrobAt_ofInjective_symm_out_conj_pow Q₀ hσ q.out
      (minimalPeriod_smul_coset_eq_inertiaDeg hv_unram Q₀ hσ q.out)
  simp only [φ, MonoidHom.toAdditive_symm_apply_apply]
  rw [globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt L ι' (e q).val Q_q hτ_q,
    HeightOneSpectrum.normalizedValuation_adicCompletionExtension_of_isUnramifiedAt v (e q).val,
    (isUniformizer_def π).1 hπ, toAdd_ofAdd, zpow_one, toMul_ofMul]

/-- **Transfer functoriality of the global Artin map in the ground field.** Let `K ⊆ E ⊆ L` be
number fields with `L/K` finite Galois, embedded in separable closures of `K` and of `E` by `ι` and
`ι'`. Extending `c ∈ C_K` to `C_E` and taking its global Artin symbol in `Gal(L/E)^ab` gives the
group-theoretic transfer (Verlagerung) of the global Artin symbol of `c` in `Gal(L/K)^ab` along
`Gal(L/E) ↪ Gal(L/K)`:

```text
Art_{L/E} (i_{E/K} c) = Ver (Art_{L/K} c).
```

The instance `IsGalois E L` follows from `IsGalois K L` (`IsGalois.tower_top_of_isGalois`). -/
theorem globalArtinMap_ideleClassExtension (ι : L →ₐ[K] SeparableClosure K)
    (ι' : L →ₐ[E] SeparableClosure E) (c : IdeleClassGroup (𝓞 K) K) :
    globalArtinMap E L ι' (.ofMul (ideleClassExtension K E c)) =
      (Group.Abelianization.transferOfInjective
        (f := (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)))
        (AlgEquiv.restrictScalarsHom_injective K)).toAdditive
        (globalArtinMap K L ι (.ofMul c)) := by
  classical
  let φ : IdeleClassGroup (𝓞 E) E →* Group.Abelianization Gal(L/E) :=
    MonoidHom.toAdditive.symm (globalArtinMap E L ι')
  let F : IdeleClassGroup (𝓞 K) K →* Group.Abelianization Gal(L/E) :=
    φ.comp (ideleClassExtension K E)
  let G : IdeleClassGroup (𝓞 K) K →* Group.Abelianization Gal(L/E) :=
    (Group.Abelianization.transferOfInjective
      (f := (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)))
      (AlgEquiv.restrictScalarsHom_injective K)).comp
      (MonoidHom.toAdditive.symm (globalArtinMap K L ι))
  -- Both kernels are open in `C_K`, so both vanish on a ray subgroup whose modulus we enlarge to
  -- contain every prime of `K` that ramifies in `L`.
  have hF : IsOpen (F.ker : Set (IdeleClassGroup (𝓞 K) K)) := by
    have hker : F.ker = (ideleClassNormMap E L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range.comap
          (ideleClassExtension K E) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, ← globalArtinMap_eq_zero_iff E L ι']
      exact toMul_eq_one
    rw [hker, Subgroup.coe_comap]
    exact (isOpen_range_ideleClassNormMap E L).preimage (continuous_ideleClassExtension K E)
  have hG : IsOpen (G.ker : Set (IdeleClassGroup (𝓞 K) K)) := by
    refine Subgroup.isOpen_mono (fun x hx ↦ ?_) (isOpen_range_ideleClassNormMap K L)
    have h0 := (globalArtinMap_eq_zero_iff K L ι x).mpr hx
    rw [MonoidHom.mem_ker]
    simp [G, h0]
  obtain ⟨𝔪₀, h𝔪₀⟩ := exists_raySubgroup_le_of_isOpen (F.ker ⊓ G.ker) (by
    rw [Subgroup.coe_inf]
    exact hF.inter hG)
  let 𝔪 : Modulus K :=
    { finitePart := 𝔪₀.finitePart * ∏ v ∈ TauCeti.NumberField.ramifiedSupport K L, v.asIdeal
      finitePart_ne_bot := by
        rw [← Ideal.zero_eq_bot, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
        exact ⟨𝔪₀.finitePart_ne_zero, fun v _ ↦ by simpa using v.ne_bot⟩
      infinitePart := 𝔪₀.infinitePart }
  have h𝔪₀𝔪 : 𝔪₀ ∣ 𝔪 := Modulus.dvd_iff.mpr ⟨dvd_mul_right _ _, Finset.Subset.refl _⟩
  have h𝔪 : raySubgroup 𝔪 ≤ F.ker ⊓ G.ker := (raySubgroup_antitone h𝔪₀𝔪).trans h𝔪₀
  have hFG : F = G := ideleClassGroup_hom_ext_of_raySubgroup_le (h𝔪.trans inf_le_left)
    (h𝔪.trans inf_le_right) fun v hv π hπ ↦ by
      have hv_unram : v ∉ TauCeti.NumberField.ramifiedSupport K L := fun hram ↦
        hv ((Modulus.mem_support_iff 𝔪 v).mpr
          (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hram) _))
      simp only [F, G, φ, MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply]
      exact globalArtinMap_ideleClassExtension_ofAdicCompletion_of_isUniformizer ι ι' hv_unram hπ
  exact congrArg Additive.ofMul (DFunLike.congr_fun hFG c)

end TauCeti.ClassFieldTheory
