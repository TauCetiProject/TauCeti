/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Coinvariants
public import TauCeti.LinearAlgebra.Trace.GroupRing.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Hattori–Stallings traces for monoid extensions over `ℕ`

Let `1 → G → Γtilde → ℤ → 1` be an extension of groups with `G` finite (`ι : G →* Γtilde`
injective, `deg : Γtilde →* Multiplicative ℤ`, and `ι.range = deg.ker`), and let
`Γ = nonnegSubmonoid deg = deg⁻¹(ℕ)`. For a ring `Λ` and a left `Λ[Γ]`-module `P` that is finite
projective over `Λ[G]`, restricting `P` to `Z_γ = centralizerSubgroup ι γ.1` makes the action of
`γ ∈ Γ` `Λ[Z_γ]`-linear, giving `centralizerGroupTrace Λ ι deg hker hPG γ ∈ Λ / [Λ, Λ]` without
dividing by `|G|` or `|Z_γ|`.

## Main definitions and results

* `TauCeti.MonoidExtension.nonnegSubmonoid`, `TauCeti.MonoidExtension.conjAut`, and
  `TauCeti.MonoidExtension.centralizerSubgroup`: `Γ = deg⁻¹(ℕ)`, conjugation on `G`, and `Z_γ ≤ G`.
* `TauCeti.MonoidExtension.centralizerEnd`, `TauCeti.MonoidExtension.centralizerGroupTrace`, and
  `TauCeti.MonoidExtension.centralizerProjectiveGroupTrace`: the `Λ[Z_γ]`-linear action of `γ` and
  its trace `Tr_Λ^{Z_γ}(γ, P)`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_singleOneSMulLinearMap_eq_card_centralizer_nsmul`
  and `TauCeti.MonoidExtension.projectiveTrace_singleOneSMulLinearMap_eq_card_centralizer_mul`:
  `Tr_Λ(γ, P) = |Z_γ| • Tr_Λ^{Z_γ}(γ, P)` (Stacks Project, Section 64.15, Lemma 64.15.4).
* `TauCeti.MonoidExtension.DegreeFiber`, `TauCeti.MonoidExtension.ConjClasses`,
  `TauCeti.MonoidExtension.coinvariantEnd`, and
  `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses`:
  `Tr_Λ(γ₀, P_G) = ∑_{[γ]} Tr_Λ^{Z_γ}(γ, P)` over `G`-conjugacy classes in `deg⁻¹(d)` (Stacks
  Project, Section 64.15, Lemma 64.15.5).

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.4 and 64.15.5).
* P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
-/

public section

noncomputable section

namespace TauCeti.MonoidExtension

open _root_.MonoidAlgebra
open TauCeti.MonoidAlgebra (singleOneSMulLinearMap singleOneSMulLinearMap_apply)

/-! ### Structure of `1 → G → Γtilde → ℤ → 1` -/

section Structure

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

section Helpers

variable {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}

private theorem map_apply_eq_one (hker : ι.range = deg.ker) (g : G) : deg (ι g) = 1 :=
  MonoidHom.mem_ker.1 (hker ▸ ⟨g, rfl⟩)

private theorem mul_inv_mem_range_of_map_eq (hker : ι.range = deg.ker) {x y : Γtilde}
    (h : deg x = deg y) : x * y⁻¹ ∈ ι.range := by
  rw [hker, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

private theorem conj_mem_range (hker : ι.range = deg.ker) (γ : Γtilde) (g : G) :
    γ * ι g * γ⁻¹ ∈ ι.range := by
  rw [hker, MonoidHom.mem_ker]; simp [map_apply_eq_one hker]

private theorem map_conj_eq (x y : Γtilde) : deg (x * y * x⁻¹) = deg y := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

end Helpers

/-- The submonoid `Γ = deg⁻¹(ℕ) = { γ : Γtilde | 0 ≤ toAdd (deg γ) }` of elements of nonnegative
degree in `Γtilde`. -/
def nonnegSubmonoid (deg : Γtilde →* Multiplicative ℤ) : Submonoid Γtilde where
  carrier := { γ : Γtilde | 0 ≤ Multiplicative.toAdd (deg γ) }
  one_mem' := by simp
  mul_mem' ha hb := by simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul] at ha hb ⊢; omega

@[simp] theorem mem_nonnegSubmonoid {deg : Γtilde →* Multiplicative ℤ} {γ : Γtilde} :
    γ ∈ nonnegSubmonoid deg ↔ 0 ≤ Multiplicative.toAdd (deg γ) := by rfl

/-- The centralizer subgroup `Z_γ = { g ∈ G | ι g * γ = γ * ι g } ≤ G`. -/
def centralizerSubgroup (ι : G →* Γtilde) (γ : Γtilde) : Subgroup G :=
  (Subgroup.centralizer {γ}).comap ι

@[simp] theorem mem_centralizerSubgroup {ι : G →* Γtilde} {γ : Γtilde} {g : G} :
    g ∈ centralizerSubgroup ι γ ↔ ι g * γ = γ * ι g := Subgroup.mem_centralizer_singleton_iff

section ExtensionMaps

variable (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)

/-- Inclusion of the kernel subgroup `G` into `nonnegSubmonoid deg`. -/
def toNonnegSubmonoid (hker : ι.range = deg.ker) : G →* nonnegSubmonoid deg :=
  ι.codRestrict (nonnegSubmonoid deg) fun g ↦ by simp [map_apply_eq_one hker]

@[simp] theorem coe_toNonnegSubmonoid (hker : ι.range = deg.ker) (g : G) :
    (toNonnegSubmonoid ι deg hker g : Γtilde) = ι g := by rfl

section ConjAut

variable (hι : Function.Injective ι) (hker : ι.range = deg.ker)

/-- Conjugation by `γ : Γtilde` on `G` across `1 → G → Γtilde → ℤ`. -/
def conjAut (γ : Γtilde) : G ≃* G :=
  have : ι.range.Normal := hker ▸ deg.normal_ker
  (MonoidHom.ofInjective hι).trans <| (MulAut.conjNormal γ).trans (MonoidHom.ofInjective hι).symm

@[simp] theorem apply_conjAut (γ : Γtilde) (g : G) :
    ι (conjAut ι deg hι hker γ g) = γ * ι g * γ⁻¹ := by
  have : ι.range.Normal := hker ▸ deg.normal_ker
  simp [conjAut, MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply,
    MonoidHom.ofInjective_apply]

@[simp] theorem conjAut_one : conjAut ι deg hι hker 1 = MulEquiv.refl G := by
  ext g; exact hι (by simp)

@[simp] theorem conjAut_mul (γ₁ γ₂ : Γtilde) :
    conjAut ι deg hι hker (γ₁ * γ₂) =
      (conjAut ι deg hι hker γ₂).trans (conjAut ι deg hι hker γ₁) := by
  ext g; exact hι (by simp [mul_assoc])

@[simp] theorem conjAut_symm (γ : Γtilde) :
    (conjAut ι deg hι hker γ).symm = conjAut ι deg hι hker γ⁻¹ := by
  ext g; apply (conjAut ι deg hι hker γ).injective
  simp only [MulEquiv.apply_symm_apply]; exact hι (by simp [mul_assoc])

@[simp] theorem conjAut_map (k : G) : conjAut ι deg hι hker (ι k) = MulAut.conj k := by
  ext g; exact hι (by simp)

/-- Fixed points of `conjAut` on `G` are precisely `centralizerSubgroup ι γ`. -/
theorem eqLocus_conjAut (γ : Γtilde) :
    (conjAut ι deg hι hker γ).toMonoidHom.eqLocus (.id G) = centralizerSubgroup ι γ := by
  ext g
  rw [show g ∈ (conjAut ι deg hι hker γ).toMonoidHom.eqLocus (.id G) ↔
      conjAut ι deg hι hker γ g = g from MonoidHom.mem_eqLocusM,
    ← hι.eq_iff, apply_conjAut, mul_inv_eq_iff_eq_mul, mem_centralizerSubgroup, eq_comm]

end ConjAut

/-- Elements of `centralizerSubgroup ι γ.1` commute with `γ` inside `nonnegSubmonoid deg`. -/
theorem commute_toNonnegSubmonoid_comp_subtype (hker : ι.range = deg.ker)
    (γ : nonnegSubmonoid deg) (z : centralizerSubgroup ι γ.1) :
    Commute ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.1).subtype z) γ :=
  Subtype.ext <| by simpa using mem_centralizerSubgroup.1 z.2

/-- Conjugation of `γ : nonnegSubmonoid deg` by `k : G` preserves `nonnegSubmonoid deg`. -/
def conjNonneg (k : G) (γ : nonnegSubmonoid deg) : nonnegSubmonoid deg :=
  ⟨ι k * γ.1 * (ι k)⁻¹, by rw [mem_nonnegSubmonoid, map_conj_eq]; exact mem_nonnegSubmonoid.1 γ.2⟩

@[simp] theorem coe_conjNonneg (k : G) (γ : nonnegSubmonoid deg) :
    (conjNonneg ι deg k γ : Γtilde) = ι k * γ.1 * (ι k)⁻¹ := by rfl

/-- Conjugation by `k : G` identifies `Z_γ` with `Z_{k γ k⁻¹}`. -/
def conjCentralizerEquiv (k : G) (γ : nonnegSubmonoid deg) :
    centralizerSubgroup ι γ.1 ≃* centralizerSubgroup ι (conjNonneg ι deg k γ).1 :=
  TauCeti.Subgroup.congrOfMapEq (MulAut.conj k) <| by
    ext x; simp only [Subgroup.mem_map, mem_centralizerSubgroup, coe_conjNonneg]
    refine ⟨?_, fun hx ↦ ⟨k⁻¹ * x * k, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩⟩
    · rintro ⟨z, hz, rfl⟩
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul, map_inv]
      have h : ι k * (ι z * γ.1) * (ι k)⁻¹ = ι k * (γ.1 * ι z) * (ι k)⁻¹ := by rw [hz]
      simpa [mul_assoc] using h
    · simpa [map_mul, map_inv, mul_assoc] using congrArg (fun y ↦ (ι k)⁻¹ * y * ι k) hx

@[simp] theorem coe_conjCentralizerEquiv_apply (k : G) (γ : nonnegSubmonoid deg)
    (z : centralizerSubgroup ι γ.1) : (conjCentralizerEquiv ι deg k γ z : G) = k * z.1 * k⁻¹ := by
  simp [conjCentralizerEquiv, TauCeti.Subgroup.coe_congrOfMapEq_apply]

@[simp] theorem coe_conjCentralizerEquiv_symm_apply (k : G) (γ : nonnegSubmonoid deg)
    (z : centralizerSubgroup ι (conjNonneg ι deg k γ).1) :
    ((conjCentralizerEquiv ι deg k γ).symm z : G) = k⁻¹ * z.1 * k := by
  simp [conjCentralizerEquiv, TauCeti.Subgroup.coe_congrOfMapEq_symm_apply]

end ExtensionMaps

/-- On any `Λ[Γ]`-module `P` with compatible `Λ[G]`-action, `singleOneSMulLinearMap Λ P γ` twists
the `G`-action by `conjAut`. -/
theorem singleOneSMulLinearMap_single_smul {Λ : Type*} [Semiring Λ]
    {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) {hker : ι.range = deg.ker}
    {P : Type*} [AddCommMonoid P] [Module Λ P] [Module Λ[nonnegSubmonoid deg] P]
    [IsScalarTower Λ Λ[nonnegSubmonoid deg] P] [Module Λ[G] P]
    (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) (g : G) (p : P) :
    singleOneSMulLinearMap Λ P γ ((single g (1 : Λ) : Λ[G]) • p) =
      (single (conjAut ι deg hι hker γ.1 g) (1 : Λ) : Λ[G]) • singleOneSMulLinearMap Λ P γ p := by
  rw [singleOneSMulLinearMap_apply, singleOneSMulLinearMap_apply, hPG, hPG]
  simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
  rw [show γ * toNonnegSubmonoid ι deg hker g =
      toNonnegSubmonoid ι deg hker (conjAut ι deg hι hker γ.1 g) * γ from by ext; simp [mul_assoc]]

end Structure

/-! ### Centralizer group-ring traces and Lemma 64.15.4 -/

section CentralizerEnd

variable {Λ G Γtilde : Type*} [Semiring Λ] [Group G] [Group Γtilde]
  {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} {hker : ι.range = deg.ker}
  {P : Type*} [AddCommMonoid P] [Module Λ[nonnegSubmonoid deg] P] [Module Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
  (γ : nonnegSubmonoid deg) [Module Λ[centralizerSubgroup ι γ.1] P]
  (hPZ : ∀ (r : Λ[centralizerSubgroup ι γ.1]) (p : P),
    r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype r • p)

/-- The action of `single γ 1` as a `Λ[Z_γ]`-linear endomorphism of `P`. -/
def centralizerEnd : Module.End Λ[centralizerSubgroup ι γ.1] P :=
  ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.1).subtype).singleSMulLinearMap
    (commute_toNonnegSubmonoid_comp_subtype ι deg hker γ) P fun r p ↦ by
      rw [hPZ, hPG]; simp [mapDomainRingHom_apply, mapDomain_mapDomain]

@[simp] theorem centralizerEnd_apply (p : P) :
    centralizerEnd hPG γ hPZ p = single γ (1 : Λ) • p := by simp [centralizerEnd]

end CentralizerEnd

section CentralizerTrace

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module Λ[nonnegSubmonoid deg] P] [Module Λ[G] P]
  [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)

omit [Module Λ[nonnegSubmonoid deg] P] in
private theorem centralizer_finite_projective (γ : nonnegSubmonoid deg) :
    let _ : Module Λ[centralizerSubgroup ι γ.1] P :=
      Module.compHom P (mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype)
    Module.Finite Λ[centralizerSubgroup ι γ.1] P ∧
      Module.Projective Λ[centralizerSubgroup ι γ.1] P := by
  let Z := centralizerSubgroup ι γ.1; let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module Λ[Z] Λ[G] := φZ.toModule; let _ : Module Λ[Z] P := Module.compHom P φZ
  have h :=
    Subgroup.restrictSubgroup_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P fun _ _ ↦ rfl
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- **The centralizer group-ring trace** `Tr_Λ^{Z_γ}(γ, P) ∈ Λ / [Λ, Λ]` of `γ ∈ Γ` on `P`,
restricted to `Z_γ = centralizerSubgroup ι γ.1`. -/
def centralizerGroupTrace (γ : nonnegSubmonoid deg) : TauCeti.cyclicQuotient ℤ Λ :=
  let Z := centralizerSubgroup ι γ.1
  let _ : Module Λ[Z] P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  have h := centralizer_finite_projective Λ ι deg (P := P) γ
  have _ := h.1; have _ := h.2
  LinearMap.hattoriStallingsGroupTrace Λ Z P (centralizerEnd hPG γ fun _ _ ↦ rfl)

variable {Λ ι deg hker}

/-- Agreement of `centralizerGroupTrace` with `hattoriStallingsGroupTrace` whenever `P` already
carries a compatible `Λ[Z_γ]`-module structure. -/
theorem centralizerGroupTrace_eq_hattoriStallingsGroupTrace (γ : nonnegSubmonoid deg)
    [instZ : Module Λ[centralizerSubgroup ι γ.1] P] [Module.Finite Λ[centralizerSubgroup ι γ.1] P]
    [Module.Projective Λ[centralizerSubgroup ι γ.1] P]
    (hPZ : ∀ (r : Λ[centralizerSubgroup ι γ.1]) (p : P),
      r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype r • p)
    (u_Z : Module.End Λ[centralizerSubgroup ι γ.1] P) (huZ : ∀ p, u_Z p = single γ (1 : Λ) • p) :
    centralizerGroupTrace Λ ι deg hker hPG γ =
      LinearMap.hattoriStallingsGroupTrace Λ (centralizerSubgroup ι γ.1) P u_Z := by
  let Z := centralizerSubgroup ι γ.1; let φZ := mapDomainRingHom Λ Z.subtype
  obtain rfl : instZ = Module.compHom P φZ := Module.ext' _ _ hPZ
  let _ : Module Λ[Z] P := Module.compHom P φZ
  rw [centralizerGroupTrace]; congr 1; ext p; simp [huZ]

/-- Expanding `centralizerGroupTrace` on a `Λ[G]`-free retract `(π, i)` of `P`. -/
private theorem centralizerGroupTrace_eq_mkQ_sum_of_retract
    {r : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P) (i : P →ₗ[Λ[G]] Fin r → Λ[G]) (hπi : π ∘ₗ i = .id)
    (γ : nonnegSubmonoid deg) [Fintype (G ⧸ (centralizerSubgroup ι γ.1).subtype.range)] :
    centralizerGroupTrace Λ ι deg hker hPG γ =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ q : G ⧸ (centralizerSubgroup ι γ.1).subtype.range,
          (i (single γ (1 : Λ) •
            ((single q.out⁻¹ (1 : Λ) : Λ[G]) • π (Pi.single k 1))) k).coeff q.out⁻¹) := by
  let Z := centralizerSubgroup ι γ.1
  let _ : Module Λ[Z] P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  obtain ⟨_, _⟩ := centralizer_finite_projective Λ ι deg (P := P) γ
  let uZ := centralizerEnd hPG γ fun _ _ ↦ rfl
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uZ
      (centralizerEnd_apply hPG γ _),
    LinearMap.hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract Z (fun _ _ ↦ rfl) π i hπi uZ]
  simp only [uZ, Z, centralizerEnd_apply]

/-- **Monoid-extension trace identity** (Stacks Project, Section 64.15, Lemma 64.15.4):
`Tr_Λ(γ, P) = |Z_γ| • Tr_Λ^{Z_γ}(γ, P)`. -/
theorem hattoriStallingsTrace_singleOneSMulLinearMap_eq_card_centralizer_nsmul
    (hι : Function.Injective ι) [Module Λ P] [IsScalarTower Λ Λ[G] P]
    [IsScalarTower Λ Λ[nonnegSubmonoid deg] P] [Module.Finite Λ P] [Module.Projective Λ P]
    (γ : nonnegSubmonoid deg) :
    LinearMap.hattoriStallingsTrace Λ P (singleOneSMulLinearMap Λ P γ) =
      Nat.card (centralizerSubgroup ι γ.1) • centralizerGroupTrace Λ ι deg hker hPG γ := by
  let Z := centralizerSubgroup ι γ.1
  let _ : Module Λ[Z] P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  obtain ⟨_, _⟩ := centralizer_finite_projective Λ ι deg (P := P) γ
  let φ_Z := centralizerEnd hPG γ fun _ _ ↦ rfl
  rw [LinearMap.hattoriStallingsTrace_eq_card_nsmul_hattoriStallingsGroupTrace_of_eqLocus
      (eqLocus_conjAut ι deg hι hker γ.1).symm (fun _ _ ↦ rfl) (singleOneSMulLinearMap Λ P γ) φ_Z
      (singleOneSMulLinearMap_single_smul hι hPG γ) (fun p ↦ by simp [φ_Z]),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) φ_Z
      (centralizerEnd_apply hPG γ _)]

/-- **`G`-conjugation invariance of `centralizerGroupTrace`.** -/
theorem centralizerGroupTrace_conjNonneg (k : G) (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace Λ ι deg hker hPG (conjNonneg ι deg k γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ := by
  let γ' := conjNonneg ι deg k γ
  let Z := centralizerSubgroup ι γ.1; let Z' := centralizerSubgroup ι γ'.1
  let _ : Module Λ[Z] P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  let _ : Module Λ[Z'] P := Module.compHom P (mapDomainRingHom Λ Z'.subtype)
  obtain ⟨_, _⟩ := centralizer_finite_projective Λ ι deg (P := P) γ
  obtain ⟨_, _⟩ := centralizer_finite_projective Λ ι deg (P := P) γ'
  let uZ := centralizerEnd hPG γ fun _ _ ↦ rfl; let uZ' := centralizerEnd hPG γ' fun _ _ ↦ rfl
  let eZ : Z ≃* Z' := conjCentralizerEquiv ι deg k γ; let E := mapDomainRingEquiv Λ eZ
  let _ := RingHomInvPair.of_ringEquiv E; let _ := RingHomInvPair.of_ringEquiv_symm E
  have hE : (E : Λ[Z] →+* Λ[Z']) = mapDomainRingHom Λ eZ.toMonoidHom :=
    (RingEquiv.toRingHom_eq_coe E).symm.trans (toRingHom_mapDomainRingEquiv eZ)
  have hZ (r : Λ[Z]) (p : P) : r • p = mapDomainRingHom Λ Z.subtype r • p := rfl
  have hZ' (r : Λ[Z']) (p : P) : r • p = mapDomainRingHom Λ Z'.subtype r • p := rfl
  let j : P ≃ₛₗ[(E : Λ[Z] →+* Λ[Z'])] P :=
    { toFun := fun p ↦ (single k (1 : Λ) : Λ[G]) • p
      invFun := fun p ↦ (single k⁻¹ (1 : Λ) : Λ[G]) • p
      left_inv := fun p ↦ by simp [← mul_smul, single_mul_single, ← one_def]
      right_inv := fun p ↦ by simp [← mul_smul, single_mul_single, ← one_def]
      map_add' := smul_add _
      map_smul' := fun r p ↦ by
        induction r using induction_linear with
        | zero => simp
        | add _ _ ha hb => rw [add_smul, smul_add, _root_.map_add, add_smul, ha, hb]
        | single z c =>
          rw [hZ, hZ', hE]
          simp only [mapDomainRingHom_apply, mapDomain_single, Subgroup.coe_subtype,
            MulEquiv.coe_toMonoidHom, ← mul_smul, single_mul_single, one_mul, mul_one]
          rw [show k * (z : G) = (eZ z : G) * k from by
            dsimp only [eZ]; rw [coe_conjCentralizerEquiv_apply]; simp] }
  have hinter (p : P) : uZ' (j p) = j (uZ p) := by
    simp only [j, uZ, uZ', LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      centralizerEnd_apply]; rw [hPG, hPG]
    simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
    rw [show γ' * toNonnegSubmonoid ι deg hker k = toNonnegSubmonoid ι deg hker k * γ from by
      ext; simp [γ', mul_assoc]]
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ' (fun _ _ ↦ rfl) uZ'
      (fun _ ↦ by simp [uZ']),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uZ
      (fun _ ↦ by simp [uZ])]
  exact j.hattoriStallingsGroupTrace_eq_of_mapDomainRingHom hE hinter

end CentralizerTrace

/-! ### `G`-coinvariants and Lemma 64.15.5 -/

section DegreeFiberAndConjClasses

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

/-- The fiber `{ γ ∈ Γ | deg γ = ofAdd d }` of elements of degree `d : ℕ` in
`nonnegSubmonoid deg`. -/
@[ext]
structure DegreeFiber (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) where
  /-- Underlying element of `nonnegSubmonoid deg`. -/
  val : nonnegSubmonoid deg
  /-- Degree condition `deg val.1 = Multiplicative.ofAdd d`. -/
  deg_eq : deg val.1 = Multiplicative.ofAdd (d : ℤ)

namespace DegreeFiber

/-- Conjugation action of `ConjAct Γtilde` on `DegreeFiber deg d`. -/
instance instMulActionConjAct (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    MulAction (ConjAct Γtilde) (DegreeFiber deg d) where
  smul g γ :=
    ⟨⟨g • γ.val.1, by rw [mem_nonnegSubmonoid, ConjAct.smul_def, map_conj_eq]; exact γ.val.2⟩,
      by simp only [ConjAct.smul_def, map_conj_eq, γ.deg_eq]⟩
  one_smul γ := DegreeFiber.ext <| Subtype.ext <| one_smul (ConjAct Γtilde) γ.val.1
  mul_smul g₁ g₂ γ := DegreeFiber.ext <| Subtype.ext <| mul_smul g₁ g₂ γ.val.1

/-- Conjugation action of `G` on `DegreeFiber deg d` induced by `ι : G →* Γtilde`. -/
@[instance_reducible]
def conjAction (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    MulAction G (DegreeFiber deg d) :=
  MulAction.compHom (DegreeFiber deg d) (ConjAct.toConjAct.toMonoidHom.comp ι)

variable {deg : Γtilde →* Multiplicative ℤ} {d : ℕ}

@[simp] theorem conjAct_smul_val (g : ConjAct Γtilde) (γ : DegreeFiber deg d) :
    (g • γ).val.1 = g • γ.val.1 := by rfl

/-- Conjugation of an element of `DegreeFiber deg d` by `k : G`. -/
def conj (ι : G →* Γtilde) (k : G) (γ : DegreeFiber deg d) : DegreeFiber deg d :=
  let _ := conjAction ι deg d; k • γ

@[simp] theorem val_conj (ι : G →* Γtilde) (k : G) (γ : DegreeFiber deg d) :
    (conj ι k γ).val = conjNonneg ι deg k γ.val := by
  ext; exact ConjAct.smul_def _ _

theorem finite [Finite G] (ι : G →* Γtilde) (hker : ι.range = deg.ker) (d : ℕ) :
    Finite (DegreeFiber deg d) := by
  have : Finite deg.ker := hker ▸ Finite.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have := deg.finite_fiber (Multiplicative.ofAdd (d : ℤ))
  exact Finite.of_injective
    (fun x : DegreeFiber deg d ↦ (⟨x.val.1, x.deg_eq⟩ : { γ // deg γ = _ }))
    fun _ _ h ↦ DegreeFiber.ext <| Subtype.ext <| Subtype.mk.inj h

end DegreeFiber

section ConjClasses

variable (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ)

/-- Equivalence relation of `G`-conjugacy on `DegreeFiber deg d`. -/
def conjSetoid : Setoid (DegreeFiber deg d) :=
  let _ := DegreeFiber.conjAction ι deg d; MulAction.orbitRel G (DegreeFiber deg d)

/-- `G`-conjugacy classes of degree-`d` elements in `nonnegSubmonoid deg`. -/
abbrev ConjClasses : Type _ := Quotient (conjSetoid ι deg d)

@[simp] theorem conjSetoid_rel (γ₁ γ₂ : DegreeFiber deg d) :
    (conjSetoid ι deg d) γ₁ γ₂ ↔ ∃ k : G, γ₁.val.1 = ι k * γ₂.val.1 * (ι k)⁻¹ := by
  let _ := DegreeFiber.conjAction ι deg d
  rw [conjSetoid, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨k, hk ▸ congrArg Subtype.val (DegreeFiber.val_conj ι k γ₂)⟩,
    fun ⟨k, hk⟩ ↦ ⟨k, DegreeFiber.ext <| Subtype.ext <|
      (congrArg Subtype.val (DegreeFiber.val_conj ι k γ₂)).trans hk.symm⟩⟩

theorem conjClasses_mk_eq_iff {γ₁ γ₂ : DegreeFiber deg d} :
    (Quotient.mk (conjSetoid ι deg d) γ₁ : ConjClasses ι deg d) =
        Quotient.mk (conjSetoid ι deg d) γ₂ ↔
      ∃ k : G, γ₁.val.1 = ι k * γ₂.val.1 * (ι k)⁻¹ := by rw [Quotient.eq, conjSetoid_rel]

@[simp] theorem mk_conj (k : G) (γ : DegreeFiber deg d) :
    (Quotient.mk (conjSetoid ι deg d) (DegreeFiber.conj ι k γ) : ConjClasses ι deg d) =
      Quotient.mk (conjSetoid ι deg d) γ :=
  (conjClasses_mk_eq_iff ι deg d).2 ⟨k, by simp⟩

private theorem stabilizer_conjAction_eq (γ : DegreeFiber deg d) :
    let _ := DegreeFiber.conjAction ι deg d
    MulAction.stabilizer G γ = centralizerSubgroup ι γ.val.1 := by
  let _ := DegreeFiber.conjAction ι deg d; ext g
  have hval : (g • γ).val.1 = ι g * γ.val.1 * (ι g)⁻¹ :=
    congrArg Subtype.val (DegreeFiber.val_conj ι g γ)
  rw [MulAction.mem_stabilizer_iff, mem_centralizerSubgroup, DegreeFiber.ext_iff, Subtype.ext_iff,
    hval, mul_inv_eq_iff_eq_mul]

end ConjClasses

theorem ConjClasses.finite [Finite G] (ι : G →* Γtilde) {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (d : ℕ) : Finite (ConjClasses ι deg d) := by
  have := DegreeFiber.finite ι hker d; infer_instance

end DegreeFiberAndConjClasses

section Coinvariants

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module Λ P] [Module Λ[nonnegSubmonoid deg] P]
  [IsScalarTower Λ Λ[nonnegSubmonoid deg] P] [Module Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)

/-- The `Λ`-linear endomorphism of `Coinvariants Λ G P` induced by `γ₀ ∈ Γ`. -/
def coinvariantEnd (γ₀ : nonnegSubmonoid deg) : Module.End Λ (Coinvariants Λ G P) :=
  Coinvariants.lift ((Coinvariants.mk Λ G P).comp (singleOneSMulLinearMap Λ P γ₀)) fun g p ↦ by
    obtain ⟨g', hg'⟩ := conj_mem_range hker γ₀.1 g
    have hrel : γ₀ * toNonnegSubmonoid ι deg hker g = toNonnegSubmonoid ι deg hker g' * γ₀ := by
      ext; simp [hg', mul_assoc]
    simp only [LinearMap.comp_apply, singleOneSMulLinearMap_apply]
    rw [show single γ₀ (1 : Λ) • ((single g (1 : Λ) : Λ[G]) • p) =
        (single g' (1 : Λ) : Λ[G]) • (single γ₀ (1 : Λ) • p) by
      rw [hPG, hPG]; simp [← mul_smul, single_mul_single, hrel], Coinvariants.mk_single_one_smul]

@[simp] theorem coinvariantEnd_mk (γ₀ : nonnegSubmonoid deg) (p : P) :
    coinvariantEnd Λ ι deg hker hPG γ₀ (Coinvariants.mk Λ G P p) =
      Coinvariants.mk Λ G P (single γ₀ (1 : Λ) • p) := by simp [coinvariantEnd]

@[simp] theorem coinvariantEnd_one : coinvariantEnd Λ ι deg hker hPG 1 = LinearMap.id := by
  ext p; simp [← one_def]

@[simp] theorem coinvariantEnd_mul (γ₁ γ₂ : nonnegSubmonoid deg) :
    coinvariantEnd Λ ι deg hker hPG (γ₁ * γ₂) =
      coinvariantEnd Λ ι deg hker hPG γ₁ ∘ₗ coinvariantEnd Λ ι deg hker hPG γ₂ := by
  ext p; simp [← mul_smul]

/-- Naturality of `coinvariantEnd` with respect to `Λ[G]`-linear maps commuting with `γ₀`. -/
theorem map_coinvariantEnd [IsScalarTower Λ Λ[G] P]
    {Q : Type*} [AddCommGroup Q] [Module Λ Q] [Module Λ[nonnegSubmonoid deg] Q]
    [IsScalarTower Λ Λ[nonnegSubmonoid deg] Q] [Module Λ[G] Q] [IsScalarTower Λ Λ[G] Q]
    (hQG : ∀ (r : Λ[G]) (q : Q), r • q = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • q)
    (f : P →ₗ[Λ[G]] Q) (γ₀ : nonnegSubmonoid deg)
    (hf : ∀ p, f (single γ₀ (1 : Λ) • p) = single γ₀ (1 : Λ) • f p) :
    Coinvariants.map (Λ := Λ) f ∘ₗ coinvariantEnd Λ ι deg hker hPG γ₀ =
      coinvariantEnd Λ ι deg hker hQG γ₀ ∘ₗ Coinvariants.map (Λ := Λ) f := by ext p; simp [hf]

/-- Elements of `Γ` of the same degree induce the same endomorphism on `Coinvariants Λ G P`. -/
theorem coinvariantEnd_eq_of_map_eq {γ₁ γ₀ : nonnegSubmonoid deg} (hdeg : deg γ₁.1 = deg γ₀.1) :
    coinvariantEnd Λ ι deg hker hPG γ₁ = coinvariantEnd Λ ι deg hker hPG γ₀ := by
  ext p; simp only [coinvariantEnd_mk]
  obtain ⟨g, hg⟩ := mul_inv_mem_range_of_map_eq hker hdeg
  have hγ₁ : γ₁ = toNonnegSubmonoid ι deg hker g * γ₀ :=
    Subtype.ext (by simp [hg, inv_mul_cancel_right])
  rw [show single γ₁ (1 : Λ) • p = (single g (1 : Λ) : Λ[G]) • (single γ₀ (1 : Λ) • p) by
    rw [hPG]; simp [← mul_smul, single_mul_single, hγ₁], Coinvariants.mk_single_one_smul]

end Coinvariants

section ConjClassTrace

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module Λ[nonnegSubmonoid deg] P] [Module Λ[G] P]
  [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)

/-- The centralizer group-ring trace descended to `G`-conjugacy classes in `DegreeFiber deg d`. -/
def conjClassGroupTrace (d : ℕ) : ConjClasses ι deg d → TauCeti.cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ ↦ centralizerGroupTrace Λ ι deg hker hPG γ.val) fun a b hab ↦ by
    obtain ⟨k, hk⟩ := (conjSetoid_rel ι deg d a b).1 hab
    rw [show a.val = conjNonneg ι deg k b.val from Subtype.ext hk]
    exact centralizerGroupTrace_conjNonneg hPG k b.val

@[simp] theorem conjClassGroupTrace_mk {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassGroupTrace Λ ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ.val := by rfl

end ConjClassTrace

section OrbitBijection

variable {G Γtilde : Type*} [Group G] [Group Γtilde]
  {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}

/-- Given a basepoint `γ₀ : DegreeFiber deg d`, `DegreeFiber deg d` identifies with `G` via the
unique `g : G` satisfying `ι g * γ.val.1 = γ₀.val.1`. -/
private def degreeFiberEquivGroup (hι : Function.Injective ι) (hker : ι.range = deg.ker)
    {d : ℕ} (γ₀ : DegreeFiber deg d) : DegreeFiber deg d ≃ G where
  toFun γ := (mul_inv_mem_range_of_map_eq hker (γ₀.deg_eq.trans γ.deg_eq.symm)).choose
  invFun g := ⟨toNonnegSubmonoid ι deg hker g⁻¹ * γ₀.val, by
    simpa [map_apply_eq_one hker] using γ₀.deg_eq⟩
  left_inv γ := by
    ext1; ext1
    simp only [Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv,
      (mul_inv_mem_range_of_map_eq hker (γ₀.deg_eq.trans γ.deg_eq.symm)).choose_spec]; group
  right_inv g := hι <| by
    rw [(mul_inv_mem_range_of_map_eq hker
      (γ₀.deg_eq.trans (by simpa [map_apply_eq_one hker] using γ₀.deg_eq.symm))).choose_spec]
    simp only [Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv]; group

private theorem apply_degreeFiberEquivGroup_mul (hι : Function.Injective ι)
    (hker : ι.range = deg.ker) {d : ℕ} (γ₀ γ : DegreeFiber deg d) :
    ι (degreeFiberEquivGroup hι hker γ₀ γ) * γ.val.1 = γ₀.val.1 := by
  simp only [degreeFiberEquivGroup, Equiv.coe_fn_mk,
    (mul_inv_mem_range_of_map_eq hker (γ₀.deg_eq.trans γ.deg_eq.symm)).choose_spec,
    inv_mul_cancel_right]

private theorem conjClass_orbit_idx_eq (hι : Function.Injective ι) {hker : ι.range = deg.ker}
    {d : ℕ} (γ₀ γ : DegreeFiber deg d) (g : G) :
    degreeFiberEquivGroup hι hker γ₀ γ * conjAut ι deg hι hker γ.val.1 g * g⁻¹ =
      degreeFiberEquivGroup hι hker γ₀ (DegreeFiber.conj ι g γ) := by
  apply hι; apply mul_right_cancel (b := (DegreeFiber.conj ι g γ).val.1)
  rw [apply_degreeFiberEquivGroup_mul hι hker γ₀ (DegreeFiber.conj ι g γ)]
  simp only [DegreeFiber.val_conj, coe_conjNonneg, map_mul, map_inv, apply_conjAut]
  rw [show ι (degreeFiberEquivGroup hι hker γ₀ γ) * (γ.val.1 * ι g * γ.val.1⁻¹) * (ι g)⁻¹ *
      (ι g * γ.val.1 * (ι g)⁻¹) = ι (degreeFiberEquivGroup hι hker γ₀ γ) * γ.val.1 by group,
    apply_degreeFiberEquivGroup_mul hι hker γ₀ γ]

/-- Orbit-stabilizer decomposition of `DegreeFiber deg d` into `G`-conjugacy classes and
centralizer cosets. -/
private noncomputable def orbitStabilizerEquiv (ι : G →* Γtilde)
    (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    DegreeFiber deg d ≃
      (c : ConjClasses ι deg d) × G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range :=
  letI := DegreeFiber.conjAction ι deg d
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G (DegreeFiber deg d)).trans <|
    Equiv.sigmaCongrRight fun c : MulAction.orbitRel.Quotient G (DegreeFiber deg d) ↦
      Subgroup.quotientEquivOfEq (by rw [stabilizer_conjAction_eq, Subgroup.range_subtype]; rfl)

private theorem orbitStabilizerEquiv_symm_mk (ι : G →* Γtilde)
    (deg : Γtilde →* Multiplicative ℤ) {d : ℕ} (c : ConjClasses ι deg d) (g : G) :
    (orbitStabilizerEquiv ι deg d).symm ⟨c, QuotientGroup.mk g⟩ = DegreeFiber.conj ι g c.out := by
  let _ := DegreeFiber.conjAction ι deg d
  let c' : MulAction.orbitRel.Quotient G (DegreeFiber deg d) := c
  have hstab (x : MulAction.orbitRel.Quotient G (DegreeFiber deg d)) :
      MulAction.stabilizer G x.out = (centralizerSubgroup ι x.out.val.1).subtype.range := by
    rw [stabilizer_conjAction_eq, Subgroup.range_subtype]
  have hqeq : (Subgroup.quotientEquivOfEq (hstab c')).symm (QuotientGroup.mk g) =
      QuotientGroup.mk g :=
    (Subgroup.quotientEquivOfEq (hstab c')).symm_apply_eq.2
      (Subgroup.quotientEquivOfEq_mk (hstab c') g).symm
  exact (by
    simp only [Equiv.symm_trans_apply, Equiv.sigmaCongrRight_symm,
      Equiv.sigmaCongrRight_apply, hqeq]
    simp [MulAction.selfEquivSigmaOrbitsQuotientStabilizer,
      MulAction.selfEquivSigmaOrbitsQuotientStabilizer', MulAction.selfEquivSigmaOrbits',
      Equiv.sigmaCongrRight_symm, DegreeFiber.conj] :
    ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer G (DegreeFiber deg d)).trans
      (Equiv.sigmaCongrRight fun x ↦ Subgroup.quotientEquivOfEq (hstab x))).symm
        ⟨c', QuotientGroup.mk g⟩ = DegreeFiber.conj ι g c'.out)

end OrbitBijection

section CoinvariantTraceFormula

variable {Λ G Γtilde : Type*} [Ring Λ] [Group G] [Group Γtilde]
  {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} {hker : ι.range = deg.ker}
  {P : Type*} [AddCommGroup P] [Module Λ P] [Module Λ[nonnegSubmonoid deg] P]
  [IsScalarTower Λ Λ[nonnegSubmonoid deg] P] [Module Λ[G] P] [IsScalarTower Λ Λ[G] P]
  [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)

private theorem hattoriStallingsTrace_coinvariantEnd_of_retract
    {r : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P) (i : P →ₗ[Λ[G]] Fin r → Λ[G]) (hπi : π ∘ₗ i = .id)
    (γ₀ : nonnegSubmonoid deg) [Fintype G] :
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P) (coinvariantEnd Λ ι deg hker hPG γ₀) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ g : G, (i (single γ₀ (1 : Λ) • π (Pi.single k 1)) k).coeff g) := by
  classical
  let ePi := Coinvariants.piEquiv Λ G (Fin r)
  let i_bar := ePi.toLinearMap ∘ₗ Coinvariants.map i
  let π_bar := Coinvariants.map π ∘ₗ ePi.symm.toLinearMap
  have hπi_bar : π_bar ∘ₗ i_bar = .id := by
    simp [π_bar, i_bar, LinearMap.comp_assoc, ← Coinvariants.map_comp, hπi]
  rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin r)) i_bar π_bar hπi_bar,
    Module.Basis.hattoriStallingsTrace_apply]
  refine congrArg _ <| Finset.sum_congr rfl fun k _ ↦ ?_
  have hsingle : (fun j : Fin r ↦ single (1 : G) ((Pi.single k (1 : Λ) : Fin r → Λ) j)) =
      (Pi.single k 1 : Fin r → Λ[G]) := by
    funext j; by_cases hjk : j = k
    · subst hjk; simp [one_def]
    · simp [Pi.single_eq_of_ne hjk]
  have haug (z : Λ[G]) : augmentation Λ G z = ∑ g : G, z.coeff g := by
    conv_lhs => rw [← sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp), map_sum]; simp
  simp [i_bar, π_bar, ePi, Pi.basisFun_apply, hsingle, haug]

omit [IsScalarTower Λ Λ[G] P] in
private theorem conjClassGroupTrace_eq_mkQ_sum_cosets [Finite G] (hι : Function.Injective ι)
    {r d : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P) (i : P →ₗ[Λ[G]] Fin r → Λ[G]) (hπi : π ∘ₗ i = .id)
    (γ₀ : DegreeFiber deg d) (c : ConjClasses ι deg d)
    [Fintype (G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range)] :
    conjClassGroupTrace Λ ι deg hker hPG d c =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ q : G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range,
          (i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k).coeff
            (degreeFiberEquivGroup hι hker γ₀ (DegreeFiber.conj ι q.out c.out))) := by
  conv_lhs => rw [← Quotient.out_eq c, conjClassGroupTrace_mk]
  let γ := c.out; rw [centralizerGroupTrace_eq_mkQ_sum_of_retract hPG π i hπi γ.val]
  refine congrArg _ <| Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  let gγ := degreeFiberEquivGroup hι hker γ₀ γ
  have hγ_eq : γ.val = toNonnegSubmonoid ι deg hker gγ⁻¹ * γ₀.val :=
    Subtype.ext (by simp [gγ, eq_inv_mul_of_mul_eq (apply_degreeFiberEquivGroup_mul hι hker γ₀ γ)])
  have himg : i (single γ.val (1 : Λ) • ((single q.out⁻¹ (1 : Λ) : Λ[G]) • π (Pi.single k 1))) k =
      single (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹) (1 : Λ) *
        i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k := by
    have htwist := singleOneSMulLinearMap_single_smul hι hPG γ.val q.out⁻¹ (π (Pi.single k 1))
    simp only [singleOneSMulLinearMap_apply] at htwist
    rw [htwist, show single γ.val (1 : Λ) • π (Pi.single k 1) =
        (single gγ⁻¹ (1 : Λ) : Λ[G]) • (single γ₀.val (1 : Λ) • π (Pi.single k 1)) by
      rw [hγ_eq, hPG]; simp [← mul_smul, single_mul_single],
      ← mul_smul, single_mul_single, one_mul, congrFun (map_smul i _ _) k, Pi.smul_apply,
      smul_eq_mul]
  simp [himg, gγ, γ, conjClass_orbit_idx_eq hι γ₀ γ q.out]

/-- **Coinvariant trace over `G`-conjugacy classes** (Stacks Project, Section 64.15,
Lemma 64.15.5): `Tr_Λ(γ₀, P_G) = ∑_{[γ] ∈ deg⁻¹(d) / G} Tr_Λ^{Z_γ}(γ, P)`. -/
theorem hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses [Finite G]
    (hι : Function.Injective ι) {d : ℕ} (γ₀ : DegreeFiber deg d) :
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P)
        (coinvariantEnd Λ ι deg hker hPG γ₀.val) =
      ∑ᶠ c : ConjClasses ι deg d, conjClassGroupTrace Λ ι deg hker hPG d c := by
  classical
  have := DegreeFiber.finite ι hker d; have := ConjClasses.finite ι hker d
  let _ : Fintype G := Fintype.ofFinite G; let _ : Fintype (DegreeFiber deg d) := Fintype.ofFinite _
  let _ : Fintype (ConjClasses ι deg d) := Fintype.ofFinite _
  let _ (c : ConjClasses ι deg d) :
      Fintype (G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range) :=
    Fintype.ofFinite _
  obtain ⟨r, π, i, -, -, hπi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ[G] P
  rw [finsum_eq_sum_of_fintype, hattoriStallingsTrace_coinvariantEnd_of_retract hPG π i hπi γ₀.val]
  simp only [conjClassGroupTrace_eq_mkQ_sum_cosets hPG hι π i hπi γ₀, ← map_sum]
  congr 1; conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  let yk := i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k
  rw [← Fintype.sum_sigma (f := fun p :
      (c : ConjClasses ι deg d) × G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range ↦
    yk.coeff (degreeFiberEquivGroup hι hker γ₀ (DegreeFiber.conj ι p.2.out p.1.out)))]
  refine (Fintype.sum_equiv
    ((orbitStabilizerEquiv ι deg d).symm.trans (degreeFiberEquivGroup hι hker γ₀)) _ _ ?_).symm
  rintro ⟨c, q⟩; rw [Equiv.trans_apply]
  conv_rhs => rw [← QuotientGroup.out_eq' q, orbitStabilizerEquiv_symm_mk]

end CoinvariantTraceFormula

/-! ### Commutative coefficient rings -/

section CommRing

variable (A : Type*) [CommRing A] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module A[nonnegSubmonoid deg] P] [Module A[G] P]
  [Module.Finite A[G] P] [Module.Projective A[G] P]
  (hPG : ∀ (r : A[G]) (p : P), r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)

/-- Scalar-valued centralizer group-ring trace `Tr_A^{Z_γ}(γ, P) ∈ A`. -/
def centralizerProjectiveGroupTrace (γ : nonnegSubmonoid deg) : A :=
  TauCeti.cyclicQuotientEquivOfComm ℤ A (centralizerGroupTrace A ι deg hker hPG γ)

/-- Scalar-valued centralizer group-ring trace descended to `ConjClasses ι deg d`. -/
def conjClassProjectiveGroupTrace (d : ℕ) (c : ConjClasses ι deg d) : A :=
  TauCeti.cyclicQuotientEquivOfComm ℤ A (conjClassGroupTrace A ι deg hker hPG d c)

variable {A ι deg hker}

theorem centralizerProjectiveGroupTrace_apply (γ : nonnegSubmonoid deg) :
    centralizerProjectiveGroupTrace A ι deg hker hPG γ =
      TauCeti.cyclicQuotientEquivOfComm ℤ A (centralizerGroupTrace A ι deg hker hPG γ) := by rfl

theorem conjClassProjectiveGroupTrace_apply (d : ℕ) (c : ConjClasses ι deg d) :
    conjClassProjectiveGroupTrace A ι deg hker hPG d c =
      TauCeti.cyclicQuotientEquivOfComm ℤ A (conjClassGroupTrace A ι deg hker hPG d c) := by rfl

@[simp] theorem conjClassProjectiveGroupTrace_mk {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassProjectiveGroupTrace A ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerProjectiveGroupTrace A ι deg hker hPG γ.val := by rfl

theorem centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace A ι deg hker hPG γ =
      (TauCeti.commutatorSubmodule ℤ A).mkQ
        (centralizerProjectiveGroupTrace A ι deg hker hPG γ) := by
  simp [Submodule.mkQ_apply, centralizerProjectiveGroupTrace_apply,
    ← TauCeti.cyclicQuotientEquivOfComm_symm_apply]

theorem conjClassGroupTrace_eq_mkQ_conjClassProjectiveGroupTrace (d : ℕ)
    (c : ConjClasses ι deg d) :
    conjClassGroupTrace A ι deg hker hPG d c =
      (TauCeti.commutatorSubmodule ℤ A).mkQ
        (conjClassProjectiveGroupTrace A ι deg hker hPG d c) := by
  simp [Submodule.mkQ_apply, conjClassProjectiveGroupTrace_apply,
    ← TauCeti.cyclicQuotientEquivOfComm_symm_apply]

/-- Agreement of `centralizerProjectiveGroupTrace` with `projectiveGroupTrace` whenever `P` already
carries a compatible `A[Z_γ]`-module structure. -/
theorem centralizerProjectiveGroupTrace_eq_projectiveGroupTrace (γ : nonnegSubmonoid deg)
    [Module A[centralizerSubgroup ι γ.1] P] [Module.Finite A[centralizerSubgroup ι γ.1] P]
    [Module.Projective A[centralizerSubgroup ι γ.1] P]
    (hPZ : ∀ (r : A[centralizerSubgroup ι γ.1]) (p : P),
      r • p = mapDomainRingHom A (centralizerSubgroup ι γ.1).subtype r • p)
    (u_Z : Module.End A[centralizerSubgroup ι γ.1] P) (huZ : ∀ p, u_Z p = single γ (1 : A) • p) :
    centralizerProjectiveGroupTrace A ι deg hker hPG γ =
      LinearMap.projectiveGroupTrace A (centralizerSubgroup ι γ.1) P u_Z := by
  rw [centralizerProjectiveGroupTrace_apply, LinearMap.projectiveGroupTrace_apply,
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ hPZ u_Z huZ]

/-- **`G`-conjugation invariance of `centralizerProjectiveGroupTrace`.** -/
theorem centralizerProjectiveGroupTrace_conjNonneg (k : G) (γ : nonnegSubmonoid deg) :
    centralizerProjectiveGroupTrace A ι deg hker hPG (conjNonneg ι deg k γ) =
      centralizerProjectiveGroupTrace A ι deg hker hPG γ := by
  simp only [centralizerProjectiveGroupTrace_apply, centralizerGroupTrace_conjNonneg]

/-- Scalar-valued form of Lemma 64.15.4 over a commutative ring `A`:
`Tr_A(γ, P) = |Z_γ| * Tr_A^{Z_γ}(γ, P)`. -/
theorem projectiveTrace_singleOneSMulLinearMap_eq_card_centralizer_mul
    (hι : Function.Injective ι) [Module A P] [IsScalarTower A A[G] P]
    [IsScalarTower A A[nonnegSubmonoid deg] P] [Module.Finite A P] [Module.Projective A P]
    (γ : nonnegSubmonoid deg) :
    LinearMap.projectiveTrace A P (singleOneSMulLinearMap A P γ) =
      (Nat.card (centralizerSubgroup ι γ.1) : A) *
        centralizerProjectiveGroupTrace A ι deg hker hPG γ := by
  simpa [LinearMap.hattoriStallingsTrace_eq_projectiveTrace,
    centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace, map_nsmul, nsmul_eq_mul] using
    congrArg (TauCeti.cyclicQuotientEquivOfComm ℤ A).toAddMonoidHom
      (hattoriStallingsTrace_singleOneSMulLinearMap_eq_card_centralizer_nsmul hPG hι γ)

/-- Scalar-valued form of Lemma 64.15.5 over a commutative ring `A`:
`Tr_A(γ₀, P_G) = ∑_{[γ] ∈ deg⁻¹(d) / G} Tr_A^{Z_γ}(γ, P)`. -/
theorem projectiveTrace_coinvariantEnd_eq_sum_conjClasses
    (hι : Function.Injective ι) [Module A P] [IsScalarTower A A[G] P]
    [IsScalarTower A A[nonnegSubmonoid deg] P] {d : ℕ} (γ₀ : DegreeFiber deg d) :
    LinearMap.projectiveTrace A (Coinvariants A G P) (coinvariantEnd A ι deg hker hPG γ₀.val) =
      ∑ᶠ c : ConjClasses ι deg d, conjClassProjectiveGroupTrace A ι deg hker hPG d c := by
  have := ConjClasses.finite ι hker d; let _ : Fintype (ConjClasses ι deg d) := Fintype.ofFinite _
  have h := congrArg (TauCeti.cyclicQuotientEquivOfComm ℤ A).toAddMonoidHom
    (hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses hPG hι γ₀)
  simp only [finsum_eq_sum_of_fintype] at h ⊢
  simpa [LinearMap.hattoriStallingsTrace_eq_projectiveTrace, conjClassProjectiveGroupTrace_apply,
    map_sum] using h

end CommRing

end TauCeti.MonoidExtension

end
