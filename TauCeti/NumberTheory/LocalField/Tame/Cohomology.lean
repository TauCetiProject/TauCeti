/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Cocycle

/-!
# Continuous 1-cocycles of a local field with `p`-torsion-free coefficients

Let `K` be a nonarchimedean local field of residue characteristic `p = ringChar 𝓀[K]`, with
absolute Galois group `G_K = Field.absoluteGaloisGroup K`, inertia subgroup `I_K`, and wild
inertia subgroup `P_K`. Let `M` be a discrete `p`-torsion-free `G_K`-module (i.e. `p • m = 0`
implies `m = 0`) on which `P_K` acts trivially.

Because `P_K` is a pro-`p` group (`TauCeti.isProP_wildInertiaSubgroup`), every continuous
1-cocycle `c : Z1 G_K M` vanishes on `P_K` (`TauCeti.IsProP.apply_eq_zero_of_mem_Z1`) and factors
through the tame quotient `toTameQuotient K`. Consequently:

* If `c` vanishes on a topological generator `τ` of tame inertia, then `c` vanishes on all of
  `I_K` (`apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator`).
* The evaluation map `c ↦ (c σ, c τ)` at an arithmetic Frobenius lift `σ` and a tame generator `τ`
  is injective on `Z1 G_K M` (`apply_prod_injective_of_isArithFrobeniusLift`), and in particular
  vanishing at `σ` and `τ` forces `c = 0`
  (`eq_zero_of_isArithFrobeniusLift_of_apply_tameGenerator_eq_zero`).
* When `I_K` acts trivially on `M`, the Iwasawa relation `σ τ σ⁻¹ = τ ^ q` in the tame quotient
  forces `σ • c τ = q • c τ`, where `q = Nat.card 𝓀[K]`
  (`smul_apply_eq_natCard_smul_of_isArithFrobeniusLift_of_mem_inertiaSubgroup`).

## Main results

* `TauCeti.TameCohomology.apply_eq_zero_of_mem_wildInertiaSubgroup`: a continuous 1-cocycle with
  discrete `p`-torsion-free coefficients and trivial `P_K`-action vanishes on `P_K`.
* `TauCeti.TameCohomology.apply_eq_of_toTameQuotient_eq`: such a cocycle depends only on the image
  in `tameQuotient K`.
* `TauCeti.TameCohomology.apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator`: vanishing on a
  tame generator forces vanishing on all of `I_K`.
* `TauCeti.TameCohomology.apply_prod_injective_of_isArithFrobeniusLift` and
  `TauCeti.TameCohomology.eq_zero_of_isArithFrobeniusLift_of_apply_tameGenerator_eq_zero`: a
  continuous 1-cocycle with discrete `p`-torsion-free coefficients and trivial `P_K`-action is
  determined by its values at an arithmetic Frobenius lift and a tame generator.
* `TauCeti.TameCohomology.smul_apply_eq_natCard_smul_of_isArithFrobeniusLift_of_mem_inertiaSubgroup`
  : when `I_K` acts trivially on `M`, `σ • c τ = Nat.card 𝓀[K] • c τ` for any arithmetic Frobenius
  lift `σ` and `τ ∈ I_K`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2 (tame inertia and wild inertia).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.5.2)–(7.5.3).
-/

public section

open TauCeti TauCeti.ContCohomology groupCohomology
open scoped ValuativeRel

namespace TauCeti.TameCohomology

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (Field.absoluteGaloisGroup K) M] [DiscreteTopology M]

/-- **Wild inertia kills continuous 1-cocycles with `p`-torsion-free coefficients.** If `P_K` acts
trivially on the discrete `G_K`-module `M` and `M` has no `p`-torsion (`p = ringChar 𝓀[K]`), then
every continuous 1-cocycle `c : Z1 G_K M` vanishes on `P_K`. -/
theorem apply_eq_zero_of_mem_wildInertiaSubgroup
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {g : Field.absoluteGaloisGroup K}
    (hg : g ∈ wildInertiaSubgroup K) :
    (c : Field.absoluteGaloisGroup K → M) g = 0 :=
  (isProP_wildInertiaSubgroup K (ringChar 𝓀[K])).apply_eq_zero_of_mem_Z1 hP hM c hg

/-- A continuous 1-cocycle with `p`-torsion-free coefficients and trivial `P_K`-action is
right-invariant under `P_K`. -/
theorem apply_mul_eq_of_mem_wildInertiaSubgroup
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) (g : Field.absoluteGaloisGroup K)
    {w : Field.absoluteGaloisGroup K} (hw : w ∈ wildInertiaSubgroup K) :
    (c : Field.absoluteGaloisGroup K → M) (g * w) = (c : Field.absoluteGaloisGroup K → M) g := by
  rw [(mem_Z1_iff.1 c.property).2 g w, apply_eq_zero_of_mem_wildInertiaSubgroup hP hM c hw,
    smul_zero, zero_add]

/-- A continuous 1-cocycle with `p`-torsion-free coefficients and trivial `P_K`-action depends only
on the image in `tameQuotient K`. -/
theorem apply_eq_of_toTameQuotient_eq
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {g₁ g₂ : Field.absoluteGaloisGroup K}
    (h : toTameQuotient K g₁ = toTameQuotient K g₂) :
    (c : Field.absoluteGaloisGroup K → M) g₁ = (c : Field.absoluteGaloisGroup K → M) g₂ := by
  have hw : g₁⁻¹ * g₂ ∈ wildInertiaSubgroup K := by
    rw [← toTameQuotient_eq_one_iff, map_mul, map_inv, h, inv_mul_cancel]
  have h1 := apply_mul_eq_of_mem_wildInertiaSubgroup hP hM c g₁ hw
  simpa using h1.symm

/-- **Tame generator detection on inertia.** If `c : Z1 G_K M` has discrete `p`-torsion-free
coefficients with trivial `P_K`-action and vanishes on a topological generator `τ` of tame inertia,
then `c` vanishes on the entire inertia subgroup `I_K`. -/
theorem apply_eq_zero_of_mem_inertiaSubgroup_of_tameGenerator
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) (τ : inertiaSubgroup K)
    (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤)
    (hcτ : (c : Field.absoluteGaloisGroup K → M) τ = 0) {g : Field.absoluteGaloisGroup K}
    (hg : g ∈ inertiaSubgroup K) :
    (c : Field.absoluteGaloisGroup K → M) g = 0 := by
  have hc := mem_Z1_iff.1 c.property
  have hP_le : wildInertiaSubgroup K ≤ zeroLocus hc.2 :=
    fun _ hw ↦ (mem_zeroLocus hc.2).2 (apply_eq_zero_of_mem_wildInertiaSubgroup hP hM c hw)
  have hle : (Subgroup.zpowers (τ : Field.absoluteGaloisGroup K) ⊔
      wildInertiaSubgroup K).topologicalClosure ≤ zeroLocus hc.2 :=
    Subgroup.topologicalClosure_minimal _
      (sup_le (Subgroup.zpowers_le.2 ((mem_zeroLocus hc.2).2 hcτ)) hP_le)
      (isClosed_zeroLocus hc.2 hc.1)
  rw [topologicalClosure_zpowers_sup_wildInertiaSubgroup hτ] at hle
  exact (mem_zeroLocus hc.2).1 (hle hg)

/-- **Injectivity of evaluation at a Frobenius lift and a tame generator.** Under the tame
hypotheses, the map `c ↦ (c σ, c τ)` from `Z1 G_K M` to `M × M` is injective. -/
theorem apply_prod_injective_of_isArithFrobeniusLift
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) (τ : inertiaSubgroup K)
    (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤) :
    Function.Injective (fun c : Z1 (Field.absoluteGaloisGroup K) M ↦
      ((c : Field.absoluteGaloisGroup K → M) σ, (c : Field.absoluteGaloisGroup K → M) τ)) := by
  intro c₁ c₂ h
  have htop : (Subgroup.closure ({σ, (τ : Field.absoluteGaloisGroup K)} ∪
      (wildInertiaSubgroup K : Set _))).topologicalClosure = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq]
    exact hσ.topologicalClosure_closure_sup_wildInertiaSubgroup hτ
  refine Subtype.ext (eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top
    c₁.property c₂.property htop ?_)
  rintro g ((rfl | rfl) | hg)
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h
  · rw [apply_eq_zero_of_mem_wildInertiaSubgroup hP hM c₁ hg,
      apply_eq_zero_of_mem_wildInertiaSubgroup hP hM c₂ hg]

/-- **Frobenius and tame generator detection on `G_K`.** Under the tame hypotheses, a continuous
1-cocycle vanishing at an arithmetic Frobenius lift `σ` and at a tame generator `τ` is zero. -/
theorem eq_zero_of_isArithFrobeniusLift_of_apply_tameGenerator_eq_zero
    (hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ) (τ : inertiaSubgroup K)
    (hτ : (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤)
    (hcσ : (c : Field.absoluteGaloisGroup K → M) σ = 0)
    (hcτ : (c : Field.absoluteGaloisGroup K → M) τ = 0) :
    c = 0 :=
  apply_prod_injective_of_isArithFrobeniusLift hP hM hσ τ hτ (Prod.ext hcσ hcτ)

/-- **The Iwasawa relation on cocycles with unramified action.** When `I_K` acts trivially on the
discrete `p`-torsion-free module `M`, every continuous 1-cocycle `c : Z1 G_K M` satisfies
`σ • c τ = q • c τ` for every arithmetic Frobenius lift `σ` and every `τ ∈ I_K`, where
`q = Nat.card 𝓀[K]`. -/
theorem smul_apply_eq_natCard_smul_of_isArithFrobeniusLift_of_mem_inertiaSubgroup
    (hI : ∀ g ∈ inertiaSubgroup K, ∀ m : M, g • m = m)
    (hM : ∀ m : M, ringChar 𝓀[K] • m = 0 → m = 0)
    (c : Z1 (Field.absoluteGaloisGroup K) M) {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ) {τ : Field.absoluteGaloisGroup K}
    (hτ : τ ∈ inertiaSubgroup K) :
    σ • (c : Field.absoluteGaloisGroup K → M) τ =
      Nat.card 𝓀[K] • (c : Field.absoluteGaloisGroup K → M) τ := by
  have hc := mem_Z1_iff.1 c.property
  have hP : ∀ g ∈ wildInertiaSubgroup K, ∀ m : M, g • m = m :=
    fun g hg ↦ hI g (wildInertiaSubgroup_le_inertiaSubgroup K hg)
  have htame : toTameQuotient K (σ * τ) = toTameQuotient K (τ ^ Nat.card 𝓀[K] * σ) := by
    have hrel := hσ.toTameQuotient_mul_toTameQuotient_mul_inv hτ
    have h1 := congrArg (· * toTameQuotient K σ) hrel
    simpa [mul_assoc, map_mul, map_pow] using h1
  have heq := apply_eq_of_toTameQuotient_eq hP hM c htame
  rw [hc.2 σ τ, hc.2 (τ ^ Nat.card 𝓀[K]) σ, hI _ (pow_mem hτ _),
    map_pow_of_smul_eq_self_of_mem_Z1 c.property (hI τ hτ),
    add_comm ((c : Field.absoluteGaloisGroup K → M) σ)] at heq
  exact add_right_cancel heq

end TauCeti.TameCohomology
