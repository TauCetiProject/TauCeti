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
import TauCeti.NumberTheory.NumberField.Global.Ideles.PlaceExtension
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.DecompositionOrbits
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
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

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
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
  let f : Gal(L/E) →* Gal(L/K) := AlgEquiv.restrictScalarsHom K
  have hf : Function.Injective f := AlgEquiv.restrictScalarsHom_injective K
  let H : Subgroup Gal(L/K) := f.range
  -- Both sides as multiplicative homomorphisms `C_K →* Gal(L/E)^ab`.
  let F : IdeleClassGroup (𝓞 K) K →* Group.Abelianization Gal(L/E) :=
    (MonoidHom.toAdditive.symm (globalArtinMap E L ι')).comp (ideleClassExtension K E)
  let G : IdeleClassGroup (𝓞 K) K →* Group.Abelianization Gal(L/E) :=
    (Group.Abelianization.transferOfInjective hf).comp
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
  -- Set up the ring-of-integers Galois tower `𝓞 K → 𝓞 E → 𝓞 L` for
  -- `H = range(Gal(L/E) → Gal(L/K))`.
  let _ : IsScalarTower (𝓞 K) (𝓞 E) (𝓞 L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      NumberField.RingOfIntegers.ext (IsScalarTower.algebraMap_apply K E L x)
  have : SMulCommClass H E L := ⟨fun ⟨_, τ, rfl⟩ e x ↦ by
    simp [Subgroup.mk_smul, AlgEquiv.smul_def, Algebra.smul_def, f]⟩
  have : IsGaloisGroup H E L :=
    IsGaloisGroup.of_mulEquiv_algEquiv (MonoidHom.ofInjective hf).symm fun h x ↦
      congrArg (fun k : H ↦ (k : Gal(L/K)) x)
        ((MonoidHom.ofInjective hf).apply_symm_apply h)
  have : IsGaloisGroup H (𝓞 E) (𝓞 L) := IsGaloisGroup.of_isIntegralClosure H (𝓞 E) (𝓞 L) E L
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := 𝓞 K) (K := K) (M := L) (B := 𝓞 L)
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := 𝓞 E) (K := E) (M := L) (B := 𝓞 L)
  have : FaithfulSMul (𝓞 E) L := .trans (𝓞 E) E L
  have : FaithfulSMul (𝓞 E) (𝓞 L) := .tower_bot (𝓞 E) (𝓞 L) L
  -- Compare `F` and `G` on uniformizers at finite places outside `𝔪.support`.
  have hFG : F = G := ideleClassGroup_hom_ext_of_raySubgroup_le (h𝔪.trans inf_le_left)
    (h𝔪.trans inf_le_right) fun v hv π hπ ↦ by
      have hv_unram : v ∉ TauCeti.NumberField.ramifiedSupport K L := fun hram ↦
        hv ((Modulus.mem_support_iff 𝔪 v).mpr
          (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hram) _))
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
        Quotient.congrRight fun _ _ ↦ by rw [hzpow]
      let e₂ : orbitRel.Quotient (stabilizer Gal(L/K) Q₀) (Gal(L/K) ⧸ H) ≃
          v.asIdeal.primesOver (𝓞 E) :=
        Ideal.orbitQuotientEquivPrimesOver v.asIdeal Q₀ H (𝓞 E)
      let e₃ : v.asIdeal.primesOver (𝓞 E) ≃
          {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} :=
        { toFun 𝔮 := ⟨⟨𝔮.1, 𝔮.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot 𝔮.1⟩, 𝔮.2.2⟩
          invFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
          left_inv 𝔮 := rfl
          right_inv w := Subtype.ext (HeightOneSpectrum.ext rfl) }
      let e := (e₁.trans e₂).trans e₃
      let _ : Fintype {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} :=
        Fintype.ofEquiv _ e
      -- Evaluate `G` at `(v, π)` via the orbit-product formula for `transferOfInjective`.
      have hG_apply : G (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) =
          Group.Abelianization.transferOfInjective hf (Group.Abelianization.of σ) := by
        simp only [G, MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply]
        rw [globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt L ι v Q₀ hσ π,
          (isUniformizer_def π).1 hπ, toAdd_ofAdd, zpow_one, toMul_ofMul]
      -- Evaluate `F` at `(v, π)` as the product over places of `E` above `v`.
      let φ : IdeleClassGroup (𝓞 E) E →* Group.Abelianization Gal(L/E) :=
        MonoidHom.toAdditive.symm (globalArtinMap E L ι')
      have hF_apply : F (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) =
          ∏ w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal},
            φ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w.1
              (Units.map (HeightOneSpectrum.adicCompletionExtension K E v w.1).toMonoidHom π)) := by
        change φ (ideleClassExtension K E (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π)) = _
        rw [ideleClassExtension_ofAdicCompletion, finprod_eq_prod_of_fintype, map_prod]
      rw [hF_apply, hG_apply,
        Group.Abelianization.transferOfInjective_eq_prod_quotient_orbitRel_zpowers_quot,
        ← Equiv.prod_comp e]
      refine Finset.prod_congr rfl fun q _ ↦ ?_
      -- Match the `e q`-place factor with the `q`-orbit factor.
      set g_q : Gal(L/K) := q.out.out
      set Q_q : Ideal (𝓞 L) := g_q⁻¹ • Q₀
      have hQ_q_prime : Q_q.IsPrime := inferInstance
      have hQ_q_liesK : Q_q.LiesOver v.asIdeal := inferInstance
      have hQ_q_unramK : Algebra.IsUnramifiedAt (𝓞 K) Q_q :=
        TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v hv_unram Q_q
      have hw_q_ideal : (e q).1.asIdeal = Q_q.under (𝓞 E) := by
        have hq : e₁ q = _root_.Quotient.mk'' (g_q : Gal(L/K) ⧸ H) := by
          conv_lhs => rw [← Quotient.out_eq q]
          rw [show (Quotient.out q : Gal(L/K) ⧸ H) = (g_q : Gal(L/K) ⧸ H) from
            (QuotientGroup.out_eq' q.out).symm]
          rfl
        change (e₂ (e₁ q)).1 = _
        rw [hq, Ideal.orbitQuotientEquivPrimesOver_mk, Ideal.coe_primesOverOfCoset_mk]
      have hQ_q_liesE : Q_q.LiesOver (e q).1.asIdeal := ⟨hw_q_ideal⟩
      -- Unramifiedness of `Q_q` over `𝓞 K` splits across `𝓞 K → 𝓞 E → 𝓞 L`.
      have : Module.Finite (𝓞 K) (𝓞 E) :=
        Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)
      have : Algebra.IsUnramifiedAt (𝓞 K) (e q).1.asIdeal :=
        .of_liesOver (𝓞 K) (e q).1.asIdeal Q_q
      have : Algebra.IsUnramifiedAt (𝓞 E) Q_q := .of_restrictScalars (𝓞 K) Q_q
      have hram_wK : (e q).1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
        Ideal.ramificationIdx_eq_one (e q).1.asIdeal (𝓞 K)
      -- Minimal period on `q.out` equals the residue degree `f((e q) | v)`.
      have hperiod : Function.minimalPeriod (σ • ·) q.out =
          (Q_q.under (𝓞 E)).inertiaDeg (𝓞 K) := by
        have h1 : Nat.card (orbit (Subgroup.zpowers σ) q.out) =
            Function.minimalPeriod (σ • ·) q.out :=
          (Nat.card_congr (orbitZPowersEquiv σ q.out)).trans (Nat.card_zmod _)
        have h2 : Nat.card (orbit (stabilizer Gal(L/K) Q₀) q.out) =
            (Q_q.under (𝓞 E)).inertiaDeg (𝓞 K) := by
          have hc := Ideal.card_orbit_stabilizer_coset v.asIdeal Q₀ H (𝓞 E) q.out
          have hcoset : (Ideal.primesOverOfCoset v.asIdeal Q₀ H (𝓞 E) q.out).1 =
              Q_q.under (𝓞 E) := by
            conv_lhs => rw [← QuotientGroup.out_eq' q.out]
            exact Ideal.coe_primesOverOfCoset_mk v.asIdeal Q₀ H (𝓞 E) g_q
          rw [hcoset, ← hw_q_ideal, hram_wK, one_mul, hw_q_ideal] at hc
          exact hc
        have horb : (orbit (Subgroup.zpowers σ) q.out : Set (Gal(L/K) ⧸ H)) =
            orbit (stabilizer Gal(L/K) Q₀) q.out := by
          ext y
          simp only [mem_orbit_iff, Subtype.exists, Subgroup.mk_smul, hzpow]
        rw [horb, h2] at h1
        exact h1.symm
      -- The relative Frobenius at `Q_q` restricts to `g_q⁻¹ * σ ^ m_q * g_q`.
      have hσ_conj : IsArithFrobAt (𝓞 K) (g_q⁻¹ * σ * g_q) Q_q := by
        simpa only [mul_assoc, inv_inv] using hσ.conj g_q⁻¹
      let τ_q : Gal(L/E) := (MonoidHom.ofInjective hf).symm
        ⟨g_q⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out * g_q,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H σ q.out⟩
      have hτ_q : IsArithFrobAt (𝓞 E) τ_q Q_q := by
        rw [NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg hσ_conj]
        have hfτ : f τ_q = g_q⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out * g_q :=
          congrArg Subtype.val ((MonoidHom.ofInjective hf).apply_symm_apply _)
        have hpow : (g_q⁻¹ * σ * g_q) ^ (Q_q.under (𝓞 E)).inertiaDeg (𝓞 K) =
            g_q⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out * g_q := by
          rw [← hperiod]
          simpa [MulAut.conj_apply, mul_assoc] using
            (map_pow (MulAut.conj g_q⁻¹) σ (Function.minimalPeriod (σ • ·) q.out)).symm
        exact hfτ.trans hpow.symm
      -- Since `(e q) | v` is unramified, `π` remains a uniformizer in `E_{e q}`.
      have : (e q).1.asIdeal.LiesOver v.asIdeal := (e q).2
      have hval_π : normalizedValuation ((e q).1.adicCompletion E)
          (Units.map (HeightOneSpectrum.adicCompletionExtension K E v (e q).1).toMonoidHom π) =
            Multiplicative.ofAdd 1 := by
        have : TauCeti.IsUnramified (v.adicCompletion K) ((e q).1.adicCompletion E) :=
          HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt v (e q).1
        have halg : (HeightOneSpectrum.adicCompletionExtension K E v (e q).1).toMonoidHom =
            (algebraMap (v.adicCompletion K) ((e q).1.adicCompletion E) :
              v.adicCompletion K →* (e q).1.adicCompletion E) :=
          congrArg RingHom.toMonoidHom
            (HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra K E v (e q).1).symm
        rw [halg, IsUnramified.normalizedValuation_algebraMap, (isUniformizer_def π).1 hπ]
      change (globalArtinMap E L ι' (.ofMul (IdeleClassGroup.ofAdicCompletion (𝓞 E) E (e q).1
          (Units.map (HeightOneSpectrum.adicCompletionExtension K E v (e q).1).toMonoidHom
            π)))).toMul =
        Group.Abelianization.of τ_q
      rw [globalArtinMap_ofAdicCompletion_eq_of_isArithFrobAt L ι' (e q).1 Q_q hτ_q,
        hval_π, toAdd_ofAdd, zpow_one, toMul_ofMul]
  exact congrArg Additive.ofMul (DFunLike.congr_fun hFG c)

end TauCeti.ClassFieldTheory
