/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Continuous 1-cocycles of a local field with prime-to-`p` torsion coefficients

Let `K` be a nonarchimedean local field of residue characteristic `p = ringChar 𝓀[K]`, with
absolute Galois group `G_K = Field.absoluteGaloisGroup K`, inertia subgroup `I_K`, and wild
inertia subgroup `P_K`. Let `M` be a discrete `G_K`-module killed by an integer `n` coprime to `p`
on which `P_K` acts trivially.

Because `P_K` is a pro-`p` group (`TauCeti.isProP_wildInertiaSubgroup`), every continuous
1-cocycle `c : Z1 G_K M` restricts on `P_K` to a continuous homomorphism into a discrete `n`-torsion
group, whose image is a finite `p`-group killed by `n` and therefore trivial. Hence `c` vanishes on
`P_K` and factors through the tame quotient `toTameQuotient K`. Consequently:

* If `c` vanishes on a topological generator `τ` of tame inertia, then `c` vanishes on all of
  `I_K` (`apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator`).
* For any continuous 1-cocycle `c` with `T₁` coefficients (without any torsion or wild-inertia
  hypothesis), vanishing on `I_K` and at an arithmetic Frobenius lift `σ` forces `c = 0`
  (`eq_zero_of_apply_inertiaSubgroup_eq_zero_of_isArithFrobeniusLift`).
* Combining the two, the evaluation map `c ↦ (c σ, c τ)` on `Z1 G_K M` is injective
  (`evalFrobeniusTame_injective`).
* When `I_K` acts trivially on `M`, the Iwasawa relation `σ τ σ⁻¹ = τ ^ q` in the tame quotient
  forces `σ • c τ = q • c τ`, where `q = Nat.card 𝓀[K]` (`smul_apply_of_mem_inertiaSubgroup`).

## Main results

* `TauCeti.TameCohomology.apply_eq_zero_of_mem_wildInertiaSubgroup`: a continuous 1-cocycle with
  discrete prime-to-`p` torsion coefficients and trivial `P_K`-action vanishes on `P_K`.
* `TauCeti.TameCohomology.apply_eq_of_toTameQuotient_eq`: such a cocycle depends only on the image
  in `tameQuotient K`.
* `TauCeti.TameCohomology.apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator`: vanishing on a
  tame generator forces vanishing on all of `I_K`.
* `TauCeti.TameCohomology.eq_zero_of_apply_inertiaSubgroup_eq_zero_of_isArithFrobeniusLift`:
  vanishing on `I_K` and on an arithmetic Frobenius lift forces `c = 0`.
* `TauCeti.TameCohomology.evalFrobeniusTame_injective`: a continuous 1-cocycle with prime-to-`p`
  torsion coefficients and trivial `P_K`-action is determined by its values at an arithmetic
  Frobenius lift and a tame generator.
* `TauCeti.TameCohomology.smul_apply_of_mem_inertiaSubgroup`: when `I_K` acts trivially on `M`,
  `σ • c τ = Nat.card 𝓀[K] • c τ` for any arithmetic Frobenius lift `σ` and `τ ∈ I_K`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2 (tame inertia and wild inertia).
* J. Neukirch, *Cohomology of Number Fields*, Chapter VII, §5 (tame local Galois groups).
-/

public section

open TauCeti TauCeti.ContCohomology
open scoped ValuativeRel

namespace TauCeti.TameCohomology

variable {K : Type} [Field K]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M]

private theorem z1_continuous (c : Z1 (Field.absoluteGaloisGroup K) M) :
    Continuous (c : Field.absoluteGaloisGroup K → M) :=
  (mem_Z1_iff.1 c.property).1

private theorem z1_mul (c : Z1 (Field.absoluteGaloisGroup K) M)
    (g h : Field.absoluteGaloisGroup K) :
    (c : Field.absoluteGaloisGroup K → M) (g * h) =
      g • (c : Field.absoluteGaloisGroup K → M) h + (c : Field.absoluteGaloisGroup K → M) g :=
  (mem_Z1_iff.1 c.property).2 g h

private theorem z1_one (c : Z1 (Field.absoluteGaloisGroup K) M) :
    (c : Field.absoluteGaloisGroup K → M) 1 = 0 := by
  have h := z1_mul c 1 1
  simpa using h.symm

private theorem z1_inv (c : Z1 (Field.absoluteGaloisGroup K) M)
    (g : Field.absoluteGaloisGroup K) :
    (c : Field.absoluteGaloisGroup K → M) g⁻¹ =
      -(g⁻¹ • (c : Field.absoluteGaloisGroup K → M) g) := by
  have h := z1_mul c g⁻¹ g
  rw [inv_mul_cancel, z1_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem zeroSet_isClosed [T1Space M] (c : Z1 (Field.absoluteGaloisGroup K) M) :
    IsClosed {g : Field.absoluteGaloisGroup K | (c : Field.absoluteGaloisGroup K → M) g = 0} :=
  isClosed_singleton.preimage (z1_continuous c)

private def zeroSubgroup (c : Z1 (Field.absoluteGaloisGroup K) M) :
    Subgroup (Field.absoluteGaloisGroup K) where
  carrier := {g | (c : Field.absoluteGaloisGroup K → M) g = 0}
  one_mem' := z1_one c
  mul_mem' {g h} hg hh := by
    change (c : Field.absoluteGaloisGroup K → M) (g * h) = 0
    rw [z1_mul c g h, hg, hh, smul_zero, add_zero]
  inv_mem' {g} hg := by
    change (c : Field.absoluteGaloisGroup K → M) g⁻¹ = 0
    rw [z1_inv c g, hg, smul_zero, neg_zero]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **A continuous 1-cocycle vanishing on inertia and at a Frobenius lift vanishes identically.**
No torsion or wild-inertia hypothesis is needed; only `T₁` on the coefficient module. -/
theorem eq_zero_of_apply_inertiaSubgroup_eq_zero_of_isArithFrobeniusLift [T1Space M]
    (c : Z1 (Field.absoluteGaloisGroup K) M) {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ)
    (hI : ∀ g ∈ inertiaSubgroup K, (c : Field.absoluteGaloisGroup K → M) g = 0)
    (hσ0 : (c : Field.absoluteGaloisGroup K → M) σ = 0) :
    c = 0 := by
  ext g
  let S := zeroSubgroup c
  have hS_closed : IsClosed (S : Set (Field.absoluteGaloisGroup K)) := zeroSet_isClosed c
  have hI_le : inertiaSubgroup K ≤ S := hI
  -- The image of `S` in `G_K ⧸ I_K ≃ₜ* zHat` is compact (hence closed) and contains `zHat.gen`.
  let φ : Field.absoluteGaloisGroup K →* zHat :=
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).toMonoidHom.comp <|
      (quotientInertiaSubgroupEquiv K).toMonoidHom.comp (unramifiedDegree K)
  have hφ_cont : Continuous φ :=
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).continuous.comp <|
      (quotientInertiaSubgroupEquiv K).continuous.comp (continuous_unramifiedDegree K)
  have himg_closed : IsClosed ((S.map φ) : Set zHat) :=
    (hS_closed.isCompact.image hφ_cont).isClosed
  have hgen : zHat.gen ∈ S.map φ := by
    refine ⟨σ, hσ0, ?_⟩
    simp [φ, isArithFrobeniusLift_def.1 hσ]
  have htop : (Subgroup.zpowers zHat.gen).topologicalClosure ≤ S.map φ :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.2 hgen) himg_closed
  have hmem : φ g ∈ S.map φ := by
    apply htop
    rw [zHat.topologicalClosure_zpowers_gen]
    trivial
  obtain ⟨s, hsS, hsφ⟩ := hmem
  have hker : s⁻¹ * g ∈ inertiaSubgroup K := by
    rw [← unramifiedDegree_eq_one_iff,
      ← (quotientInertiaSubgroupEquiv K).map_eq_one_iff,
      ← (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).map_eq_one_iff]
    have h1 : φ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsφ, inv_mul_cancel]
    exact h1
  have hgS : g ∈ S := by
    simpa using S.mul_mem hsS (hI_le hker)
  exact hgS

section WildTrivial

variable [DiscreteTopology M]

/-- **Wild inertia kills continuous 1-cocycles with prime-to-`p` torsion coefficients.** If `P_K`
acts trivially on the discrete `G_K`-module `M` and `M` is killed by an integer `n` coprime to
`p = ringChar 𝓀[K]`, then every continuous 1-cocycle `c : Z1 G_K M` vanishes on `P_K`. -/
theorem apply_eq_zero_of_mem_wildInertiaSubgroup
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {g : Field.absoluteGaloisGroup K}
    (hg : g ∈ wildInertiaSubgroup K) :
    (c : Field.absoluteGaloisGroup K → M) g = 0 := by
  let f : wildInertiaSubgroup K →* Multiplicative M :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((c : Field.absoluteGaloisGroup K → M) x.val)
      map_one' := by simp [z1_one]
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd ((c : Field.absoluteGaloisGroup K → M) (x.val * y.val)) = _
        rw [z1_mul c x.val y.val, hP x.val x.property, add_comm, ofAdd_add] }
  have hf_ker_open : IsOpen (f.ker : Set (wildInertiaSubgroup K)) :=
    (isOpen_discrete ({0} : Set M)).preimage ((z1_continuous c).comp continuous_subtypeVal)
  have hpro : IsProP (ringChar 𝓀[K]) (wildInertiaSubgroup K) :=
    isProP_wildInertiaSubgroup K (ringChar 𝓀[K])
  have hpg : IsPGroup (ringChar 𝓀[K]) f.range := hpro.isPGroup_range f hf_ker_open
  obtain ⟨k, hk⟩ := hpg ⟨f ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩
  have hpow_p : f ⟨g, hg⟩ ^ (ringChar 𝓀[K]) ^ k = 1 := congrArg Subtype.val hk
  have hpow_n : f ⟨g, hg⟩ ^ n = 1 := by
    change Multiplicative.ofAdd (n • (c : Field.absoluteGaloisGroup K → M) g) = 1
    rw [hM, ofAdd_zero]
  have hdvd : orderOf (f ⟨g, hg⟩) ∣ Nat.gcd n ((ringChar 𝓀[K]) ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow_n) (orderOf_dvd_of_pow_eq_one hpow_p)
  rw [(hn.pow_right k).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact Multiplicative.ofAdd.injective hdvd

/-- A continuous 1-cocycle with prime-to-`p` torsion coefficients and trivial `P_K`-action is
right-invariant under `P_K`. -/
theorem apply_mul_eq_of_mem_wildInertiaSubgroup
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) (g : Field.absoluteGaloisGroup K)
    {w : Field.absoluteGaloisGroup K} (hw : w ∈ wildInertiaSubgroup K) :
    (c : Field.absoluteGaloisGroup K → M) (g * w) = (c : Field.absoluteGaloisGroup K → M) g := by
  rw [z1_mul c g w, apply_eq_zero_of_mem_wildInertiaSubgroup hP hn hM c hw, smul_zero, zero_add]

/-- A continuous 1-cocycle with prime-to-`p` torsion coefficients and trivial `P_K`-action depends
only on the image in `tameQuotient K`. -/
theorem apply_eq_of_toTameQuotient_eq
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {g₁ g₂ : Field.absoluteGaloisGroup K}
    (h : toTameQuotient K g₁ = toTameQuotient K g₂) :
    (c : Field.absoluteGaloisGroup K → M) g₁ = (c : Field.absoluteGaloisGroup K → M) g₂ := by
  have hw : g₁⁻¹ * g₂ ∈ wildInertiaSubgroup K := by
    rw [← toTameQuotient_eq_one_iff, map_mul, map_inv, h, inv_mul_cancel]
  have h1 := apply_mul_eq_of_mem_wildInertiaSubgroup hP hn hM c g₁ hw
  simpa using h1.symm

/-- **Tame generator detection on inertia.** If `c : Z1 G_K M` has discrete prime-to-`p` torsion
coefficients with trivial `P_K`-action and vanishes on a topological generator `τ` of tame inertia,
then `c` vanishes on the entire inertia subgroup `I_K`. -/
theorem apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) (τ : inertiaSubgroup K)
    (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤)
    (hcτ : (c : Field.absoluteGaloisGroup K → M) τ = 0) {g : Field.absoluteGaloisGroup K}
    (hg : g ∈ inertiaSubgroup K) :
    (c : Field.absoluteGaloisGroup K → M) g = 0 := by
  let S := zeroSubgroup c
  have hS_closed : IsClosed (S : Set (Field.absoluteGaloisGroup K)) := zeroSet_isClosed c
  have himg_closed : IsClosed ((S.map (toTameQuotient K).toMonoidHom) : Set (tameQuotient K)) :=
    (hS_closed.isCompact.image (toTameQuotient K).continuous).isClosed
  have hτ_mem : toTameQuotient K τ ∈ S.map (toTameQuotient K).toMonoidHom := ⟨τ, hcτ, rfl⟩
  have htame_le : tameInertia K ≤ S.map (toTameQuotient K).toMonoidHom := by
    rw [← topologicalClosure_zpowers_toTameQuotient hτ]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.2 hτ_mem) himg_closed
  have hg_tame : toTameQuotient K g ∈ tameInertia K := by
    rw [← range_tameInertiaHom]
    exact ⟨inertiaTameCharacter K ⟨g, hg⟩, tameInertiaHom_inertiaTameCharacter ⟨g, hg⟩⟩
  obtain ⟨s, hsS, hsq⟩ := htame_le hg_tame
  rw [← apply_eq_of_toTameQuotient_eq hP hn hM c hsq]
  exact hsS

/-- **Frobenius and tame generator detection on `G_K`.** Under the tame hypotheses, a continuous
1-cocycle vanishing at an arithmetic Frobenius lift `σ` and at a tame generator `τ` is zero. -/
theorem eq_zero_of_apply_tameGenerator_eq_zero
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ) (τ : inertiaSubgroup K)
    (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤)
    (hcσ : (c : Field.absoluteGaloisGroup K → M) σ = 0)
    (hcτ : (c : Field.absoluteGaloisGroup K → M) τ = 0) :
    c = 0 :=
  eq_zero_of_apply_inertiaSubgroup_eq_zero_of_isArithFrobeniusLift c hσ
    (fun _ hg ↦ apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator hP hn hM c τ hτ hcτ hg) hcσ

/-- **Injectivity of evaluation at a Frobenius lift and a tame generator.** Under the tame
hypotheses, the map `c ↦ (c σ, c τ)` from `Z1 G_K M` to `M × M` is injective. -/
theorem evalFrobeniusTame_injective
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) (τ : inertiaSubgroup K)
    (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤) :
    Function.Injective (fun c : Z1 (Field.absoluteGaloisGroup K) M ↦
      ((c : Field.absoluteGaloisGroup K → M) σ, (c : Field.absoluteGaloisGroup K → M) τ)) := by
  intro c₁ c₂ h
  have hdiff : c₁ - c₂ = 0 :=
    eq_zero_of_apply_tameGenerator_eq_zero hP hn hM (c₁ - c₂) hσ τ hτ
      (sub_eq_zero.2 (congrArg Prod.fst h)) (sub_eq_zero.2 (congrArg Prod.snd h))
  exact sub_eq_zero.1 hdiff

/-- **The Iwasawa relation on cocycles with unramified action.** When `I_K` acts trivially on the
discrete prime-to-`p` torsion module `M`, every continuous 1-cocycle `c : Z1 G_K M` satisfies
`σ • c τ = q • c τ` for every arithmetic Frobenius lift `σ` and every `τ ∈ I_K`, where
`q = Nat.card 𝓀[K]`. -/
theorem smul_apply_of_mem_inertiaSubgroup
    (hI : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) (hM : ∀ m : M, n • m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ) {τ : Field.absoluteGaloisGroup K}
    (hτ : τ ∈ inertiaSubgroup K) :
    σ • (c : Field.absoluteGaloisGroup K → M) τ =
      Nat.card 𝓀[K] • (c : Field.absoluteGaloisGroup K → M) τ := by
  have hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m :=
    fun g hg ↦ hI g (wildInertiaSubgroup_le_inertiaSubgroup K hg)
  have htame : toTameQuotient K (σ * τ) = toTameQuotient K (τ ^ Nat.card 𝓀[K] * σ) := by
    have hrel := hσ.toTameQuotient_mul_toTameQuotient_mul_inv hτ
    have h1 := congrArg (· * toTameQuotient K σ) hrel
    simpa [mul_assoc, map_mul, map_pow] using h1
  have hpow (k : ℕ) : (c : Field.absoluteGaloisGroup K → M) (τ ^ k) =
      k • (c : Field.absoluteGaloisGroup K → M) τ := by
    induction k with
    | zero => simp [z1_one]
    | succ k ih =>
      rw [pow_succ, z1_mul, hI _ (pow_mem hτ k), ih, add_comm, succ_nsmul]
  have heq := apply_eq_of_toTameQuotient_eq hP hn hM c htame
  rw [z1_mul c σ τ, z1_mul c (τ ^ Nat.card 𝓀[K]) σ,
    hI _ (pow_mem hτ _), hpow, add_comm ((c : Field.absoluteGaloisGroup K → M) σ)] at heq
  exact add_right_cancel heq

end WildTrivial

end TauCeti.TameCohomology
