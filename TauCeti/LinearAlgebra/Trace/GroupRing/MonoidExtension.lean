/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.Algebra.MonoidAlgebra.Coinvariants
public import TauCeti.LinearAlgebra.Trace.GroupRing.Basic
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.MapDomain

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
* `TauCeti.MonoidExtension.centralizerGroupTrace` and
  `TauCeti.MonoidExtension.centralizerProjectiveGroupTrace`: `Tr_Λ^{Z_γ}(γ, P)`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_elemLinearMap_eq_card_centralizer_nsmul` and
  `TauCeti.MonoidExtension.projectiveTrace_elemLinearMap_eq_card_centralizer_mul`:
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

/-! ### Structure of `1 → G → Γtilde → ℤ → 1` -/

section Structure

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

private theorem deg_ι_eq_one {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (g : G) : deg (ι g) = 1 :=
  MonoidHom.mem_ker.1 (hker ▸ ⟨g, rfl⟩)

/-- The submonoid `Γ = deg⁻¹(ℕ) = { γ : Γtilde | 0 ≤ toAdd (deg γ) }` of elements of nonnegative
degree in `Γtilde`. -/
def nonnegSubmonoid (deg : Γtilde →* Multiplicative ℤ) : Submonoid Γtilde where
  carrier := { γ : Γtilde | 0 ≤ Multiplicative.toAdd (deg γ) }
  one_mem' := by simp
  mul_mem' ha hb := by simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul] at ha hb ⊢; omega

@[simp]
theorem mem_nonnegSubmonoid {deg : Γtilde →* Multiplicative ℤ} {γ : Γtilde} :
    γ ∈ nonnegSubmonoid deg ↔ 0 ≤ Multiplicative.toAdd (deg γ) :=
  Iff.rfl

/-- Inclusion of the kernel subgroup `G` into `nonnegSubmonoid deg`. -/
def toNonnegSubmonoid (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) : G →* nonnegSubmonoid deg where
  toFun g := ⟨ι g, by simp [deg_ι_eq_one hker]⟩
  map_one' := Subtype.ext (map_one ι)
  map_mul' a b := Subtype.ext (map_mul ι a b)

@[simp]
theorem coe_toNonnegSubmonoid (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (g : G) :
    (toNonnegSubmonoid ι deg hker g : Γtilde) = ι g :=
  (rfl)

private theorem conj_mem_range (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (γ : Γtilde) (g : G) :
    γ * ι g * γ⁻¹ ∈ ι.range := by
  rw [hker, MonoidHom.mem_ker]; simp [deg_ι_eq_one hker]

/-- Conjugation by `γ : Γtilde` on `G` across `1 → G → Γtilde → ℤ`. -/
def conjAut (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) : G ≃* G where
  toFun g := (conj_mem_range ι deg hker γ g).choose
  invFun g := (conj_mem_range ι deg hker γ⁻¹ g).choose
  left_inv g := hι <| by
    rw [(conj_mem_range ι deg hker γ⁻¹ _).choose_spec,
      (conj_mem_range ι deg hker γ g).choose_spec]; group
  right_inv g := hι <| by
    rw [(conj_mem_range ι deg hker γ _).choose_spec,
      (conj_mem_range ι deg hker γ⁻¹ g).choose_spec]; group
  map_mul' a b := hι <| by
    rw [(conj_mem_range ι deg hker γ (a * b)).choose_spec, map_mul, map_mul,
      (conj_mem_range ι deg hker γ a).choose_spec,
      (conj_mem_range ι deg hker γ b).choose_spec]; group

@[simp]
theorem ι_conjAut_apply (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) (g : G) :
    ι (conjAut ι deg hι hker γ g) = γ * ι g * γ⁻¹ :=
  (conj_mem_range ι deg hker γ g).choose_spec

/-- The centralizer subgroup `Z_γ = { g ∈ G | ι g * γ = γ * ι g } ≤ G`. -/
def centralizerSubgroup (ι : G →* Γtilde) (γ : Γtilde) : Subgroup G :=
  (Subgroup.centralizer {γ}).comap ι

@[simp]
theorem mem_centralizerSubgroup {ι : G →* Γtilde} {γ : Γtilde} {g : G} :
    g ∈ centralizerSubgroup ι γ ↔ ι g * γ = γ * ι g :=
  Subgroup.mem_centralizer_singleton_iff

theorem commute_toNonnegSubmonoid_of_mem_centralizerSubgroup
    (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
    (γ : nonnegSubmonoid deg) (z : centralizerSubgroup ι γ.1) :
    Commute ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.1).subtype z) γ := by
  refine Subtype.ext ?_
  simp only [Submonoid.coe_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, coe_toNonnegSubmonoid]
  exact mem_centralizerSubgroup.1 z.2

/-- Fixed points of `conjAut` on `G` are precisely `centralizerSubgroup ι γ`. -/
theorem eqLocus_conjAut (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hι : Function.Injective ι) (hker : ι.range = deg.ker) (γ : Γtilde) :
    (conjAut ι deg hι hker γ).toMonoidHom.eqLocus (.id G) = centralizerSubgroup ι γ := by
  ext g
  change conjAut ι deg hι hker γ g = g ↔ g ∈ centralizerSubgroup ι γ
  rw [← hι.eq_iff, ι_conjAut_apply, mul_inv_eq_iff_eq_mul, mem_centralizerSubgroup, eq_comm]

/-- Conjugation of `γ : nonnegSubmonoid deg` by `k : G` preserves `nonnegSubmonoid deg`. -/
def conjNonneg (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (k : G) (γ : nonnegSubmonoid deg) : nonnegSubmonoid deg :=
  ⟨ι k * γ.1 * (ι k)⁻¹, by
    rw [mem_nonnegSubmonoid]; simpa [deg_ι_eq_one hker] using mem_nonnegSubmonoid.1 γ.2⟩

@[simp]
theorem coe_conjNonneg (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (k : G) (γ : nonnegSubmonoid deg) :
    (conjNonneg ι deg hker k γ : Γtilde) = ι k * γ.1 * (ι k)⁻¹ :=
  (rfl)

/-- Conjugation by `k : G` identifies `Z_γ` with `Z_{k γ k⁻¹}`. -/
def conjCentralizerEquiv (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    (hker : ι.range = deg.ker) (k : G) (γ : nonnegSubmonoid deg) :
    centralizerSubgroup ι γ.1 ≃* centralizerSubgroup ι (conjNonneg ι deg hker k γ).1 where
  toFun z := ⟨k * z.1 * k⁻¹, by
    have hz := mem_centralizerSubgroup.1 z.2
    rw [mem_centralizerSubgroup, coe_conjNonneg]
    calc
      ι (k * z.1 * k⁻¹) * (ι k * γ.1 * (ι k)⁻¹)
          = ι k * (ι z.1 * γ.1) * (ι k)⁻¹ := by simp [mul_assoc]
      _ = ι k * (γ.1 * ι z.1) * (ι k)⁻¹ := by rw [hz]
      _ = (ι k * γ.1 * (ι k)⁻¹) * ι (k * z.1 * k⁻¹) := by simp [mul_assoc]⟩
  invFun z' := ⟨k⁻¹ * z'.1 * k, by
    have h1 := congrArg (fun x ↦ (ι k)⁻¹ * x * ι k) (mem_centralizerSubgroup.1 z'.2)
    exact mem_centralizerSubgroup.2 (by simpa [coe_conjNonneg, mul_assoc] using h1)⟩
  left_inv z := Subtype.ext (by group)
  right_inv z' := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/-- On any `Λ[Γ]`-module `P` with compatible `Λ[G]`-action, `elemLinearMap Λ P γ` twists the
`G`-action by `conjAut`. -/
theorem elemLinearMap_single_smul {Λ : Type*} [Ring Λ]
    {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) {hker : ι.range = deg.ker}
    {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) (g : G) (p : P) :
    elemLinearMap Λ P γ ((single g (1 : Λ) : MonoidAlgebra Λ G) • p) =
      (single (conjAut ι deg hι hker γ.1 g) (1 : Λ) : MonoidAlgebra Λ G) •
        elemLinearMap Λ P γ p := by
  rw [elemLinearMap_apply, elemLinearMap_apply, hPG, hPG]
  simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
  have hrel : γ * toNonnegSubmonoid ι deg hker g =
      toNonnegSubmonoid ι deg hker (conjAut ι deg hι hker γ.1 g) * γ := by
    ext; simp [mul_assoc]
  rw [hrel]

end Structure

/-! ### Centralizer group-ring traces and Lemma 64.15.4 -/

section CentralizerTrace

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module Λ P]
  [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
  [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
  [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]

variable {Λ ι deg hker} in
private def centralizerEnd
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg)
    [Module (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    (hPZ : ∀ (r : MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) (p : P),
      r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype r • p) :
    Module.End (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P :=
  ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.1).subtype).singleSMulLinearMap
    (commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ) P fun r p ↦ by
      rw [hPZ, hPG]; simp [mapDomainRingHom_apply, mapDomain_mapDomain]

/-- **The centralizer group-ring trace** `Tr_Λ^{Z_γ}(γ, P) ∈ Λ / [Λ, Λ]` of `γ ∈ Γ` on `P`,
restricted to `Z_γ = centralizerSubgroup ι γ.1`. -/
def centralizerGroupTrace
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) : TauCeti.cyclicQuotient ℤ Λ :=
  let Z := centralizerSubgroup ι γ.1
  let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  have hsub := Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z
    (fun _ _ ↦ rfl) P (fun _ _ ↦ rfl)
  have _ := hsub.2.2.2.1; have _ := hsub.2.2.2.2
  LinearMap.hattoriStallingsGroupTrace Λ Z P (centralizerEnd hPG γ fun _ _ ↦ rfl)

variable {Λ ι deg hker}

/-- Agreement of `centralizerGroupTrace` with `hattoriStallingsGroupTrace` whenever `P` already
carries a compatible `Λ[Z_γ]`-module structure. -/
theorem centralizerGroupTrace_eq_hattoriStallingsGroupTrace
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg)
    [instZ : Module (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    [Module.Finite (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    [Module.Projective (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    (hPZ : ∀ (r : MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) (p : P),
      r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype r • p)
    (u_Z : Module.End (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P)
    (huZ : ∀ p, u_Z p = single γ (1 : Λ) • p) :
    centralizerGroupTrace Λ ι deg hker hPG γ =
      LinearMap.hattoriStallingsGroupTrace Λ (centralizerSubgroup ι γ.1) P u_Z := by
  let Z := centralizerSubgroup ι γ.1
  let φZ := mapDomainRingHom Λ Z.subtype
  have hinst : instZ = Module.compHom P φZ := Module.ext' _ _ hPZ
  subst hinst
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  rw [centralizerGroupTrace]
  congr 1
  ext p; simp [centralizerEnd, huZ]

/-- **Monoid-extension trace identity** (Stacks Project, Section 64.15, Lemma 64.15.4):
`Tr_Λ(γ, P) = |Z_γ| • Tr_Λ^{Z_γ}(γ, P)`. -/
theorem hattoriStallingsTrace_elemLinearMap_eq_card_centralizer_nsmul
    (hι : Function.Injective ι)
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    [Module.Finite Λ P] [Module.Projective Λ P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    LinearMap.hattoriStallingsTrace Λ P (elemLinearMap Λ P γ) =
      Nat.card (centralizerSubgroup ι γ.1) • centralizerGroupTrace Λ ι deg hker hPG γ := by
  let σ := conjAut ι deg hι hker γ.1
  let Z := centralizerSubgroup ι γ.1
  have hZ : Z = σ.toMonoidHom.eqLocus (.id G) := (eqLocus_conjAut ι deg hι hker γ.1).symm
  let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  have hφ := elemLinearMap_single_smul hι hPG γ
  let φ_Z := LinearMap.restrictFixedSubgroup hZ.le (fun _ _ ↦ rfl) (elemLinearMap Λ P γ) hφ
  rw [LinearMap.hattoriStallingsTrace_of_twistedSMul hZ (fun _ _ ↦ rfl)
    (elemLinearMap Λ P γ) φ_Z hφ (fun p ↦ by simp [φ_Z]),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) φ_Z
      (fun p ↦ by simp [φ_Z])]

/-- Semilinear equivalence `p ↦ single k 1 • p` intertwining the `Z_γ`- and `Z_{k γ k⁻¹}`-actions
on `P`. -/
private def conjSemilinearEquiv (k : G) (γ : nonnegSubmonoid deg)
    [Module (MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) P]
    [Module (MonoidAlgebra Λ (centralizerSubgroup ι (conjNonneg ι deg hker k γ).1)) P]
    (hZ : ∀ (r : MonoidAlgebra Λ (centralizerSubgroup ι γ.1)) (p : P),
      r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.1).subtype r • p)
    (hZ' : ∀ (r : MonoidAlgebra Λ (centralizerSubgroup ι (conjNonneg ι deg hker k γ).1)) (p : P),
      r • p = mapDomainRingHom Λ
        (centralizerSubgroup ι (conjNonneg ι deg hker k γ).1).subtype r • p)
    {σ : MonoidAlgebra Λ (centralizerSubgroup ι γ.1) →+*
      MonoidAlgebra Λ (centralizerSubgroup ι (conjNonneg ι deg hker k γ).1)}
    {σ' : MonoidAlgebra Λ (centralizerSubgroup ι (conjNonneg ι deg hker k γ).1) →+*
      MonoidAlgebra Λ (centralizerSubgroup ι γ.1)}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (hσ : σ = mapDomainRingHom Λ (conjCentralizerEquiv ι deg hker k γ).toMonoidHom) :
    P ≃ₛₗ[σ] P where
  toFun p := (single k (1 : Λ) : MonoidAlgebra Λ G) • p
  invFun p := (single k⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • p
  left_inv p := by simp [← mul_smul, single_mul_single, ← one_def]
  right_inv p := by simp [← mul_smul, single_mul_single, ← one_def]
  map_add' a b := smul_add _ a b
  map_smul' r p := by
    induction r using induction_linear with
    | zero => simp
    | add a b ha hb => rw [add_smul, smul_add, _root_.map_add, add_smul, ha, hb]
    | single z c =>
      rw [hZ, hZ', hσ]
      simp only [mapDomainRingHom_apply, mapDomain_single, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, ← mul_smul, single_mul_single, one_mul, mul_one]
      have hgrp : k * (z : G) = (conjCentralizerEquiv ι deg hker k γ z : G) * k := by
        change k * (z : G) = k * (z : G) * k⁻¹ * k; group
      rw [hgrp]

/-- **`G`-conjugation invariance of `centralizerGroupTrace`.** -/
theorem centralizerGroupTrace_conjNonneg
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (k : G) (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace Λ ι deg hker hPG (conjNonneg ι deg hker k γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ := by
  let γ' := conjNonneg ι deg hker k γ
  let Z := centralizerSubgroup ι γ.1; let Z' := centralizerSubgroup ι γ'.1
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := (mapDomainRingHom Λ Z.subtype).toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  let _ : Module (MonoidAlgebra Λ Z') (MonoidAlgebra Λ G) :=
    (mapDomainRingHom Λ Z'.subtype).toModule
  let _ : Module (MonoidAlgebra Λ Z') P := Module.compHom P (mapDomainRingHom Λ Z'.subtype)
  obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  obtain ⟨_, _, _, hfinZ', hprojZ'⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z' (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  let uZ := centralizerEnd hPG γ fun _ _ ↦ rfl
  let uZ' := centralizerEnd hPG γ' fun _ _ ↦ rfl
  let eZ : Z ≃* Z' := conjCentralizerEquiv ι deg hker k γ
  let E : MonoidAlgebra Λ Z ≃+* MonoidAlgebra Λ Z' := mapDomainRingEquiv Λ eZ
  let _ := RingHomInvPair.of_ringEquiv E; let _ := RingHomInvPair.of_ringEquiv_symm E
  have hE : (E : MonoidAlgebra Λ Z →+* MonoidAlgebra Λ Z') = mapDomainRingHom Λ eZ.toMonoidHom :=
    (RingEquiv.toRingHom_eq_coe E).symm.trans (toRingHom_mapDomainRingEquiv eZ)
  let j := conjSemilinearEquiv (Λ := Λ) (ι := ι) (hker := hker) (P := P) k γ
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (σ := E) (σ' := E.symm) hE
  have hj : ∀ p : P, j p = (single k (1 : Λ) : MonoidAlgebra Λ G) • p := fun _ ↦ rfl
  have hinter : ∀ p : P, uZ' (j p) = j (uZ p) := fun p ↦ by
    rw [hj, hj]
    simp only [uZ, uZ', centralizerEnd, MonoidHom.singleSMulLinearMap_apply]
    rw [hPG, hPG]
    simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
    have hγ : γ' * toNonnegSubmonoid ι deg hker k = toNonnegSubmonoid ι deg hker k * γ := by
      ext; simp [γ', mul_assoc]
    rw [hγ]
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ' (fun _ _ ↦ rfl) uZ'
      (fun p ↦ by simp [uZ', centralizerEnd]),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uZ
      (fun p ↦ by simp [uZ, centralizerEnd])]
  exact j.hattoriStallingsGroupTrace_eq_of_semilinear eZ hE hinter

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

/-- Conjugation of an element of `DegreeFiber deg d` by `k : G`. -/
def conj {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} (hker : ι.range = deg.ker)
    {d : ℕ} (k : G) (γ : DegreeFiber deg d) : DegreeFiber deg d :=
  ⟨conjNonneg ι deg hker k γ.val, by simpa [conjNonneg, deg_ι_eq_one hker] using γ.deg_eq⟩

@[simp]
theorem val_conj {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} (hker : ι.range = deg.ker)
    {d : ℕ} (k : G) (γ : DegreeFiber deg d) :
    (conj hker k γ).val = conjNonneg ι deg hker k γ.val :=
  (rfl)

theorem finite [Finite G] (ι : G →* Γtilde) {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (d : ℕ) : Finite (DegreeFiber deg d) := by
  by_cases hne : Nonempty (DegreeFiber deg d)
  · obtain ⟨γ₀⟩ := hne
    let f : G → DegreeFiber deg d := fun g ↦
      ⟨toNonnegSubmonoid ι deg hker g * γ₀.val, by
        simpa [deg_ι_eq_one hker] using γ₀.deg_eq⟩
    refine Finite.of_surjective f fun γ ↦ ?_
    have hmem : γ.val.1 * γ₀.val.1⁻¹ ∈ ι.range := by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ.deg_eq, γ₀.deg_eq, mul_inv_cancel]
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, DegreeFiber.ext <| Subtype.ext <| by
      rw [Submonoid.coe_mul, coe_toNonnegSubmonoid, hg, inv_mul_cancel_right]⟩
  · have : IsEmpty (DegreeFiber deg d) := not_nonempty_iff.1 hne
    infer_instance

end DegreeFiber

/-- Equivalence relation of `G`-conjugacy on `DegreeFiber deg d`. -/
def conjSetoid (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    Setoid (DegreeFiber deg d) where
  r γ₁ γ₂ := ∃ k : G, γ₁.val.1 = ι k * γ₂.val.1 * (ι k)⁻¹
  iseqv :=
    { refl := fun _ ↦ ⟨1, by simp⟩
      symm := fun ⟨k, hk⟩ ↦ ⟨k⁻¹, by rw [hk, map_inv]; group⟩
      trans := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ↦ ⟨k₁ * k₂, by rw [hk₁, hk₂]; simp [mul_assoc]⟩ }

/-- `G`-conjugacy classes of degree-`d` elements in `nonnegSubmonoid deg`. -/
abbrev ConjClasses (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) : Type _ :=
  Quotient (conjSetoid ι deg d)

theorem ConjClasses.finite [Finite G] (ι : G →* Γtilde) {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (d : ℕ) : Finite (ConjClasses ι deg d) := by
  have := DegreeFiber.finite ι hker d; infer_instance

end DegreeFiberAndConjClasses

section Coinvariants

variable (Λ : Type*) [Ring Λ] {G Γtilde : Type*} [Group G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module Λ P]
  [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P] [Module (MonoidAlgebra Λ G) P]

/-- The `Λ`-linear endomorphism of `Coinvariants Λ G P` induced by `γ₀ ∈ Γ`. -/
def coinvariantEnd [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ₀ : nonnegSubmonoid deg) :
    Module.End Λ (Coinvariants Λ G P) :=
  Coinvariants.desc ((Coinvariants.mk Λ G P).comp (elemLinearMap Λ P γ₀)) fun g p ↦ by
    obtain ⟨g', hg'⟩ := conj_mem_range ι deg hker γ₀.1 g
    have hrel : γ₀ * toNonnegSubmonoid ι deg hker g =
        toNonnegSubmonoid ι deg hker g' * γ₀ := by ext; simp [hg', mul_assoc]
    have hsmul : elemLinearMap Λ P γ₀ ((single g (1 : Λ) : MonoidAlgebra Λ G) • p) =
        (single g' (1 : Λ) : MonoidAlgebra Λ G) • elemLinearMap Λ P γ₀ p := by
      rw [elemLinearMap_apply, elemLinearMap_apply, hPG, hPG]
      simp [← mul_smul, single_mul_single, hrel]
    simp only [LinearMap.comp_apply, hsmul, Coinvariants.mk_single_one_smul]

@[simp]
theorem coinvariantEnd_mk [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (γ₀ : nonnegSubmonoid deg) (p : P) :
    coinvariantEnd Λ ι deg hker hPG γ₀ (Coinvariants.mk Λ G P p) =
      Coinvariants.mk Λ G P (single γ₀ (1 : Λ) • p) := by
  simp [coinvariantEnd]

/-- Elements of `Γ` of the same degree induce the same endomorphism on `Coinvariants Λ G P`. -/
theorem coinvariantEnd_eq_of_deg_eq [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {γ₁ γ₀ : nonnegSubmonoid deg} (hdeg : deg γ₁.1 = deg γ₀.1) :
    coinvariantEnd Λ ι deg hker hPG γ₁ = coinvariantEnd Λ ι deg hker hPG γ₀ := by
  ext p
  simp only [coinvariantEnd_mk]
  have hmem : γ₁.1 * γ₀.1⁻¹ ∈ ι.range := by
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv, hdeg, mul_inv_cancel]
  obtain ⟨g, hg⟩ := hmem
  have hγ₁ : γ₁ = toNonnegSubmonoid ι deg hker g * γ₀ := by
    ext; rw [Submonoid.coe_mul, coe_toNonnegSubmonoid, hg, inv_mul_cancel_right]
  have hsmul : single γ₁ (1 : Λ) • p =
      (single g (1 : Λ) : MonoidAlgebra Λ G) • (single γ₀ (1 : Λ) • p) := by
    rw [hPG, mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul, hγ₁]
  rw [hsmul, Coinvariants.mk_single_one_smul]

/-- The centralizer group-ring trace descended to `G`-conjugacy classes in `DegreeFiber deg d`. -/
def conjClassGroupTrace [Finite G] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    (d : ℕ) :
    ConjClasses ι deg d → TauCeti.cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ ↦ centralizerGroupTrace Λ ι deg hker hPG γ.val) fun a b ⟨k, hk⟩ ↦ by
    have ha : a.val = conjNonneg ι deg hker k b.val := Subtype.ext hk
    rw [ha]
    exact centralizerGroupTrace_conjNonneg hPG k b.val

@[simp]
theorem conjClassGroupTrace_mk [Finite G] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassGroupTrace Λ ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ.val :=
  (rfl)

end Coinvariants

section OrbitBijection

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

private theorem mul_inv_mem_range_of_deg {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) {d : ℕ} (γ₀ γ : DegreeFiber deg d) :
    γ₀.val.1 * γ.val.1⁻¹ ∈ ι.range := by
  rw [hker, MonoidHom.mem_ker, map_mul, map_inv, γ₀.deg_eq, γ.deg_eq, mul_inv_cancel]

/-- Given a basepoint `γ₀ : DegreeFiber deg d`, `DegreeFiber deg d` identifies with `G` via the
unique `g : G` satisfying `ι g * γ.val.1 = γ₀.val.1`. -/
private def degreeFiberEquivGroup {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) (hker : ι.range = deg.ker)
    {d : ℕ} (γ₀ : DegreeFiber deg d) :
    DegreeFiber deg d ≃ G where
  toFun γ := (mul_inv_mem_range_of_deg hker γ₀ γ).choose
  invFun g :=
    ⟨(toNonnegSubmonoid ι deg hker g⁻¹) * γ₀.val, by
      simpa [deg_ι_eq_one hker] using γ₀.deg_eq⟩
  left_inv γ := by
    ext1; ext1
    simp only [Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv,
      (mul_inv_mem_range_of_deg hker γ₀ γ).choose_spec]
    group
  right_inv g := hι <| by
    let γ' : DegreeFiber deg d := ⟨(toNonnegSubmonoid ι deg hker g⁻¹) * γ₀.val, by
      have hg : ι g ∈ deg.ker := hker ▸ ⟨g, rfl⟩
      rw [MonoidHom.mem_ker] at hg; simpa [hg] using γ₀.deg_eq⟩
    have hspec := (mul_inv_mem_range_of_deg hker γ₀ γ').choose_spec
    change ι (mul_inv_mem_range_of_deg hker γ₀ γ').choose = ι g
    rw [hspec]; simp only [γ', Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv]; group

private theorem ι_degreeFiberEquivGroup_mul {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hι : Function.Injective ι) (hker : ι.range = deg.ker)
    {d : ℕ} (γ₀ γ : DegreeFiber deg d) :
    ι (degreeFiberEquivGroup hι hker γ₀ γ) * γ.val.1 = γ₀.val.1 := by
  change ι (mul_inv_mem_range_of_deg hker γ₀ γ).choose * γ.val.1 = γ₀.val.1
  rw [(mul_inv_mem_range_of_deg hker γ₀ γ).choose_spec, inv_mul_cancel_right]

/-- Each `G`-conjugacy orbit fiber over `c` identifies with `G ⧸ Z_{c.out}`. -/
private def orbitCosetEquiv {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) {d : ℕ} (c : ConjClasses ι deg d) :
    G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range ≃
      { x : DegreeFiber deg d // Quotient.mk (conjSetoid ι deg d) x = c } :=
  Equiv.ofBijective
    (fun q ↦ ⟨DegreeFiber.conj hker q.out c.out,
      (@Quotient.sound _ (conjSetoid ι deg d) _ _ ⟨q.out, rfl⟩).trans (Quotient.out_eq c)⟩)
    ⟨fun q₁ q₂ h ↦ by
      have hval : ι q₁.out * c.out.val.1 * (ι q₁.out)⁻¹ =
          ι q₂.out * c.out.val.1 * (ι q₂.out)⁻¹ :=
        congrArg (fun x : DegreeFiber deg d ↦ x.val.1) (congrArg Subtype.val h)
      have hcomm : ι (q₁.out⁻¹ * q₂.out) * c.out.val.1 = c.out.val.1 * ι (q₁.out⁻¹ * q₂.out) := by
        calc
          ι (q₁.out⁻¹ * q₂.out) * c.out.val.1
              = (ι q₁.out)⁻¹ * (ι q₂.out * c.out.val.1 * (ι q₂.out)⁻¹) * ι q₂.out := by
                simp [mul_assoc]
          _ = (ι q₁.out)⁻¹ * (ι q₁.out * c.out.val.1 * (ι q₁.out)⁻¹) * ι q₂.out := by rw [← hval]
          _ = c.out.val.1 * ι (q₁.out⁻¹ * q₂.out) := by simp [mul_assoc]
      have hmem : q₁.out⁻¹ * q₂.out ∈ (centralizerSubgroup ι c.out.val.1).subtype.range :=
        ⟨⟨q₁.out⁻¹ * q₂.out, mem_centralizerSubgroup.2 hcomm⟩, rfl⟩
      simpa [Quotient.out_eq] using QuotientGroup.eq.2 hmem,
    fun ⟨x, hx⟩ ↦ by
      obtain ⟨g, hgx⟩ := Quotient.exact (hx.trans (Quotient.out_eq c).symm)
      let q : G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range := QuotientGroup.mk g
      obtain ⟨z, hz⟩ := QuotientGroup.eq.1 (Quotient.out_eq q)
      refine ⟨q, Subtype.ext <| DegreeFiber.ext <| Subtype.ext ?_⟩
      have hzc := mem_centralizerSubgroup.1 z.2
      have hg : g = q.out * (z : G) := eq_mul_of_inv_mul_eq hz.symm
      simp only [DegreeFiber.val_conj, coe_conjNonneg, hgx, hg, map_mul, mul_inv_rev]
      calc
        ι q.out * c.out.val.1 * (ι q.out)⁻¹
            = ι q.out * (c.out.val.1 * ι (z : G) * (ι (z : G))⁻¹) * (ι q.out)⁻¹ := by simp
        _ = ι q.out * (ι (z : G) * c.out.val.1 * (ι (z : G))⁻¹) * (ι q.out)⁻¹ := by rw [← hzc]
        _ = ι q.out * ι (z : G) * c.out.val.1 * ((ι (z : G))⁻¹ * (ι q.out)⁻¹) := by
              simp [mul_assoc]⟩

end OrbitBijection

section CoinvariantTraceFormula

variable {Λ G Γtilde : Type*} [Ring Λ] [Group G] [Group Γtilde]
  {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ} {hker : ι.range = deg.ker}
  {P : Type*} [AddCommGroup P] [Module Λ P]
  [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
  [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) P]
  [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
  [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]

private theorem hattoriStallingsTrace_coinvariantEnd_of_retract
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {r : ℕ} (π : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] P)
    (i : P →ₗ[MonoidAlgebra Λ G] Fin r → MonoidAlgebra Λ G) (hπi : π ∘ₗ i = .id)
    (γ₀ : nonnegSubmonoid deg) [Fintype G] :
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P)
        (coinvariantEnd Λ ι deg hker hPG γ₀) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ g : G,
          (i (single γ₀ (1 : Λ) • π (Pi.single k 1)) k).coeff g) := by
  classical
  let ePi := Coinvariants.piEquiv Λ G (Fin r)
  let i_bar : Coinvariants Λ G P →ₗ[Λ] Fin r → Λ := ePi.toLinearMap ∘ₗ Coinvariants.map i
  let π_bar : (Fin r → Λ) →ₗ[Λ] Coinvariants Λ G P := Coinvariants.map π ∘ₗ ePi.symm.toLinearMap
  have hπi_bar : π_bar ∘ₗ i_bar = .id := by
    have hassoc : π_bar ∘ₗ i_bar =
        Coinvariants.map π ∘ₗ (ePi.symm.toLinearMap ∘ₗ ePi.toLinearMap) ∘ₗ Coinvariants.map i := by
      simp [π_bar, i_bar, LinearMap.comp_assoc]
    rw [hassoc, ePi.symm_comp, LinearMap.id_comp, ← Coinvariants.map_comp, hπi, Coinvariants.map_id]
  rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin r)) i_bar π_bar hπi_bar,
    Module.Basis.hattoriStallingsTrace_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  let ek : Fin r → Λ := Pi.single k 1
  have hbasis : Pi.basisFun Λ (Fin r) k = ek := Pi.basisFun_apply Λ (Fin r) k
  have hsingle : (fun j : Fin r ↦ single (1 : G) (ek j)) =
      (Pi.single k 1 : Fin r → MonoidAlgebra Λ G) := by
    funext j; by_cases hjk : j = k; · subst hjk; simp [ek, one_def]
    · simp [ek, Pi.single_eq_of_ne hjk]
  have haug : ∀ z : MonoidAlgebra Λ G, augmentation Λ G z = ∑ g : G, z.coeff g := fun z ↦ by
    conv_lhs => rw [← sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp), map_sum]; simp
  rw [hbasis]
  simp [i_bar, π_bar, ePi, hsingle, haug]

private theorem conjClass_orbit_idx_eq (hι : Function.Injective ι) {d : ℕ}
    (γ₀ : DegreeFiber deg d) (c : ConjClasses ι deg d)
    (q : G ⧸ (centralizerSubgroup ι c.out.val.1).subtype.range) :
    degreeFiberEquivGroup hι hker γ₀ c.out * conjAut ι deg hι hker c.out.val.1 q.out * q.out⁻¹ =
      degreeFiberEquivGroup hι hker γ₀ ((orbitCosetEquiv hker c q).1) := by
  let γ := c.out; let gγ := degreeFiberEquivGroup hι hker γ₀ γ
  have hO : (orbitCosetEquiv hker c q).1 = DegreeFiber.conj hker q.out γ := rfl
  rw [hO]
  apply hι
  apply mul_right_cancel (b := (DegreeFiber.conj hker q.out γ).val.1)
  rw [ι_degreeFiberEquivGroup_mul hι hker γ₀ (DegreeFiber.conj hker q.out γ)]
  change ι (gγ * conjAut ι deg hι hker γ.val.1 q.out * q.out⁻¹) *
    (ι q.out * γ.val.1 * (ι q.out)⁻¹) = γ₀.val.1
  simp only [map_mul, map_inv, ι_conjAut_apply]
  have hgrp : ι gγ * (γ.val.1 * ι q.out * γ.val.1⁻¹) * (ι q.out)⁻¹ *
      (ι q.out * γ.val.1 * (ι q.out)⁻¹) = ι gγ * γ.val.1 := by group
  rw [hgrp, ι_degreeFiberEquivGroup_mul hι hker γ₀ γ]

private theorem conjClassGroupTrace_eq_mkQ_sum_fiber [Finite G] (hι : Function.Injective ι)
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {r d : ℕ} (π : (Fin r → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] P)
    (i : P →ₗ[MonoidAlgebra Λ G] Fin r → MonoidAlgebra Λ G) (hπi : π ∘ₗ i = .id)
    (γ₀ : DegreeFiber deg d) [Fintype (DegreeFiber deg d)] [DecidableEq (ConjClasses ι deg d)]
    (c : ConjClasses ι deg d) :
    conjClassGroupTrace Λ ι deg hker hPG d c =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ x : { x : DegreeFiber deg d // Quotient.mk (conjSetoid ι deg d) x = c },
          (i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k).coeff
            (degreeFiberEquivGroup hι hker γ₀ x.1)) := by
  classical
  conv_lhs => rw [← Quotient.out_eq c, conjClassGroupTrace_mk]
  let γ := c.out; let Z := centralizerSubgroup ι γ.val.1
  have : Finite (G ⧸ Z.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
  let _ : Fintype (G ⧸ Z.subtype.range) := Fintype.ofFinite _
  let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) := φZ.toModule
  let _ : Module (MonoidAlgebra Λ Z) P := Module.compHom P φZ
  obtain ⟨_, _, _, hfinZ, hprojZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := Λ) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  let uZ := centralizerEnd hPG γ.val fun _ _ ↦ rfl
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ.val (fun _ _ ↦ rfl) uZ
      (fun p ↦ by simp [uZ, centralizerEnd]),
    LinearMap.hattoriStallingsGroupTrace_eq_mkQ_sum_of_retract Z (fun _ _ ↦ rfl) π i hπi uZ]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← (orbitCosetEquiv hker c).sum_comp]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  let gγ := degreeFiberEquivGroup hι hker γ₀ γ
  have hγ_eq : γ.val = toNonnegSubmonoid ι deg hker gγ⁻¹ * γ₀.val :=
    Subtype.ext (by simp [gγ, eq_inv_mul_of_mul_eq (ι_degreeFiberEquivGroup_mul hι hker γ₀ γ)])
  have himg : i (uZ ((single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • π (Pi.single k 1))) k =
      single (conjAut ι deg hι hker γ.val.1 q.out⁻¹ * gγ⁻¹) (1 : Λ) *
        i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k := by
    have htwist := elemLinearMap_single_smul hι hPG γ.val q.out⁻¹ (π (Pi.single k 1))
    simp only [elemLinearMap_apply] at htwist
    have hsplit : single (toNonnegSubmonoid ι deg hker gγ⁻¹ * γ₀.val) (1 : Λ) •
        π (Pi.single k 1) =
        (single gγ⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
          (single γ₀.val (1 : Λ) • π (Pi.single k 1)) := by
      rw [hPG, mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
    simp only [uZ, centralizerEnd, MonoidHom.singleSMulLinearMap_apply, htwist]
    nth_rw 2 [hγ_eq]
    rw [hsplit, ← mul_smul, single_mul_single, one_mul, congrFun (map_smul i _ _) k,
      Pi.smul_apply, smul_eq_mul]
  simp [himg, gγ, γ, conjClass_orbit_idx_eq hι γ₀ c q]

/-- **Coinvariant trace over `G`-conjugacy classes** (Stacks Project, Section 64.15,
Lemma 64.15.5): `Tr_Λ(γ₀, P_G) = ∑_{[γ] ∈ deg⁻¹(d) / G} Tr_Λ^{Z_γ}(γ, P)`. -/
theorem hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses [Finite G]
    (hι : Function.Injective ι)
    (hPG : ∀ (r : MonoidAlgebra Λ G) (p : P),
      r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} [Fintype (ConjClasses ι deg d)] (γ₀ : DegreeFiber deg d) :
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P)
        (coinvariantEnd Λ ι deg hker hPG γ₀.val) =
      ∑ c : ConjClasses ι deg d, conjClassGroupTrace Λ ι deg hker hPG d c := by
  classical
  have := DegreeFiber.finite ι hker d
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (DegreeFiber deg d) := Fintype.ofFinite _
  obtain ⟨r, π, i, -, -, hπi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  rw [hattoriStallingsTrace_coinvariantEnd_of_retract hPG π i hπi γ₀.val]
  simp only [conjClassGroupTrace_eq_mkQ_sum_fiber hι hPG π i hπi γ₀, ← map_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  let yk := i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k
  have hpart : ∑ c : ConjClasses ι deg d,
      ∑ x : { x : DegreeFiber deg d // Quotient.mk (conjSetoid ι deg d) x = c },
        yk.coeff (degreeFiberEquivGroup hι hker γ₀ x.1) =
      ∑ x : DegreeFiber deg d, yk.coeff (degreeFiberEquivGroup hι hker γ₀ x) :=
    (Fintype.sum_sigma (f := fun p :
        (c : ConjClasses ι deg d) ×
          { x : DegreeFiber deg d // Quotient.mk (conjSetoid ι deg d) x = c } ↦
      yk.coeff (degreeFiberEquivGroup hι hker γ₀ p.2.1))).symm.trans
      ((Equiv.sigmaFiberEquiv (Quotient.mk (conjSetoid ι deg d))).sum_comp
        (fun x ↦ yk.coeff (degreeFiberEquivGroup hι hker γ₀ x)))
  rw [hpart]
  exact ((degreeFiberEquivGroup hι hker γ₀).sum_comp (fun g ↦ yk.coeff g)).symm

end CoinvariantTraceFormula

/-! ### Commutative coefficient rings -/

section CommRing

variable (A : Type*) [CommRing A] {G Γtilde : Type*} [Group G] [Finite G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)
  {P : Type*} [AddCommGroup P] [Module A P]
  [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
  [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
  [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]

/-- Scalar-valued centralizer group-ring trace `Tr_A^{Z_γ}(γ, P) ∈ A`. -/
def centralizerProjectiveGroupTrace
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) : A :=
  TauCeti.cyclicQuotientEquivOfCommRing ℤ A (centralizerGroupTrace A ι deg hker hPG γ)

/-- Scalar-valued centralizer group-ring trace descended to `ConjClasses ι deg d`. -/
def conjClassProjectiveGroupTrace
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (d : ℕ) (c : ConjClasses ι deg d) : A :=
  TauCeti.cyclicQuotientEquivOfCommRing ℤ A (conjClassGroupTrace A ι deg hker hPG d c)

variable {A ι deg hker}

@[simp]
theorem conjClassProjectiveGroupTrace_mk
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassProjectiveGroupTrace A ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerProjectiveGroupTrace A ι deg hker hPG γ.val :=
  (rfl)

theorem centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace A ι deg hker hPG γ =
      (TauCeti.commutatorSubmodule ℤ A).mkQ
        (centralizerProjectiveGroupTrace A ι deg hker hPG γ) := by
  rw [centralizerProjectiveGroupTrace, ← TauCeti.cyclicQuotientEquivOfCommRing_symm_apply]
  exact ((TauCeti.cyclicQuotientEquivOfCommRing ℤ A).symm_apply_apply _).symm

/-- Scalar-valued form of Lemma 64.15.4 over a commutative ring `A`:
`Tr_A(γ, P) = |Z_γ| * Tr_A^{Z_γ}(γ, P)`. -/
theorem projectiveTrace_elemLinearMap_eq_card_centralizer_mul
    (hι : Function.Injective ι)
    [IsScalarTower A (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module.Finite A P] [Module.Projective A P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (γ : nonnegSubmonoid deg) :
    LinearMap.projectiveTrace A P (elemLinearMap A P γ) =
      (Nat.card (centralizerSubgroup ι γ.1) : A) *
        centralizerProjectiveGroupTrace A ι deg hker hPG γ := by
  have h := congrArg (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).toAddMonoidHom
    (hattoriStallingsTrace_elemLinearMap_eq_card_centralizer_nsmul hι hPG γ)
  simpa [LinearMap.hattoriStallingsTrace_eq_projectiveTrace,
    centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace, map_nsmul, nsmul_eq_mul] using h

/-- Scalar-valued form of Lemma 64.15.5 over a commutative ring `A`:
`Tr_A(γ₀, P_G) = ∑_{[γ] ∈ deg⁻¹(d) / G} Tr_A^{Z_γ}(γ, P)`. -/
theorem projectiveTrace_coinvariantEnd_eq_sum_conjClasses
    (hι : Function.Injective ι)
    [IsScalarTower A (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} [Fintype (ConjClasses ι deg d)] (γ₀ : DegreeFiber deg d) :
    LinearMap.projectiveTrace A (Coinvariants A G P)
        (coinvariantEnd A ι deg hker hPG γ₀.val) =
      ∑ c : ConjClasses ι deg d, conjClassProjectiveGroupTrace A ι deg hker hPG d c := by
  have h := congrArg (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).toAddMonoidHom
    (hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses hι hPG γ₀)
  simpa [LinearMap.hattoriStallingsTrace_eq_projectiveTrace, conjClassProjectiveGroupTrace,
    map_sum] using h

end CommRing

end TauCeti.MonoidExtension

end
