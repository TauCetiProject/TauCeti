/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Coinvariants
public import TauCeti.GroupTheory.GroupExtension.MonoidExtension
public import TauCeti.LinearAlgebra.Trace.GroupRing.Basic
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Hattori–Stallings traces for monoid extensions over `ℕ`

Let `1 → G → Γtilde → ℤ → 1` be a group extension with `G` finite (`ι : G →* Γtilde` injective,
`deg : Γtilde →* Multiplicative ℤ`, `ι.range = deg.ker`), and `Γ = nonnegSubmonoid deg = deg⁻¹(ℕ)`
(from `TauCeti.GroupTheory.GroupExtension.MonoidExtension`). For a ring `Λ` and a left
`Λ[Γ]`-module `P` that is finite projective over `Λ[G]`, restricting `P` to
`Z_γ = centralizerSubgroup ι γ.1` makes the action of `γ ∈ Γ` `Λ[Z_γ]`-linear, giving
`centralizerGroupTrace Λ ι deg hker hPG γ ∈ Λ / [Λ, Λ]` without dividing by `|G|` or `|Z_γ|`.

## Main definitions and results

* `TauCeti.MonoidExtension.centralizerEnd`, `TauCeti.MonoidExtension.centralizerGroupTrace`,
  `TauCeti.MonoidExtension.centralizerProjectiveGroupTrace`: the `Λ[Z_γ]`-linear action of `γ` and
  its trace `Tr_Λ^{Z_γ}(γ, P)`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_singleOneSMulLinearMap_eq_card_centralizer_nsmul`,
  `TauCeti.MonoidExtension.projectiveTrace_singleOneSMulLinearMap_eq_card_centralizer_mul`:
  `Tr_Λ(γ, P) = |Z_γ| • Tr_Λ^{Z_γ}(γ, P)` (Stacks Project, Section 64.15, Lemma 64.15.4).
* `TauCeti.MonoidExtension.coinvariantEnd`, `TauCeti.MonoidExtension.conjClassGroupTrace`,
  `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses`:
  `Tr_Λ(γ₀, P_G) = ∑_{[γ]} Tr_Λ^{Z_γ}(γ, P)` over `G`-conjugacy classes in `deg⁻¹(d)` (Stacks
  Project, Section 64.15, Lemma 64.15.5).

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.4 and 64.15.5);
  P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
-/

public section
noncomputable section

namespace TauCeti.MonoidExtension

open _root_.MonoidAlgebra
open TauCeti.MonoidAlgebra (singleOneSMulLinearMap singleOneSMulLinearMap_apply)

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

section ActionAndCentralizerEnd
variable {Λ : Type*} [Semiring Λ] {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}
  {hker : ι.range = deg.ker} {P : Type*} [AddCommMonoid P] [Module Λ[nonnegSubmonoid deg] P]
  [Module Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)

include hPG in
private theorem single_toNonnegSubmonoid_mul_smul (g : G) (γ : nonnegSubmonoid deg) (p : P) :
    single (toNonnegSubmonoid ι deg hker g * γ) (1 : Λ) • p =
      (single g (1 : Λ) : Λ[G]) • (single γ (1 : Λ) • p) := by
  rw [hPG, mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
include hPG in
private theorem single_mul_toNonnegSubmonoid_smul (γ : nonnegSubmonoid deg) (g : G) (p : P) :
    single (γ * toNonnegSubmonoid ι deg hker g) (1 : Λ) • p =
      single γ (1 : Λ) • ((single g (1 : Λ) : Λ[G]) • p) := by
  rw [hPG, mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]

include hPG in
/-- On any `Λ[Γ]`-module `P` with compatible `Λ[G]`-action, `singleOneSMulLinearMap Λ P γ` twists
the `G`-action by `conjAut`. -/
theorem singleOneSMulLinearMap_single_smul [Module Λ P]
    [IsScalarTower Λ Λ[nonnegSubmonoid deg] P] (hι : Function.Injective ι)
    (γ : nonnegSubmonoid deg) (g : G) (p : P) :
    singleOneSMulLinearMap Λ P γ ((single g (1 : Λ) : Λ[G]) • p) =
      (single (conjAut ι deg hι hker γ.val g) (1 : Λ) : Λ[G]) •
        singleOneSMulLinearMap Λ P γ p := by
  rw [singleOneSMulLinearMap_apply, singleOneSMulLinearMap_apply,
    ← single_mul_toNonnegSubmonoid_smul hPG, mul_toNonnegSubmonoid ι deg hι hker,
    single_toNonnegSubmonoid_mul_smul hPG]

section CentralizerEnd
variable (γ : nonnegSubmonoid deg) [Module Λ[centralizerSubgroup ι γ.val] P]
  (hPZ : ∀ (r : Λ[centralizerSubgroup ι γ.val]) (p : P),
    r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.val).subtype r • p)

/-- The action of `single γ 1` as a `Λ[Z_γ]`-linear endomorphism of `P`. -/
def centralizerEnd : Module.End Λ[centralizerSubgroup ι γ.val] P :=
  ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.val).subtype).singleSMulLinearMap
    (commute_toNonnegSubmonoid_comp_subtype ι deg hker γ) P fun r p ↦ by
      rw [hPZ, hPG]; simp [mapDomainRingHom_apply, mapDomain_mapDomain]

@[simp] theorem centralizerEnd_apply (p : P) :
    centralizerEnd hPG γ hPZ p = single γ (1 : Λ) • p := by simp [centralizerEnd]
end CentralizerEnd
end ActionAndCentralizerEnd

section RingSection
variable (Λ : Type*) [Ring Λ] (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
  (hker : ι.range = deg.ker) {P : Type*} [AddCommGroup P] [Module Λ[nonnegSubmonoid deg] P]
  [Module Λ[G] P]
  (hPG : ∀ (r : Λ[G]) (p : P), r • p = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • p)

/-! ### Centralizer group-ring traces and Lemma 64.15.4 -/

section CentralizerTrace
variable [Finite G] [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]

omit [Module Λ[nonnegSubmonoid deg] P] in
private theorem centralizer_finite_projective (γ : nonnegSubmonoid deg) :
    let _ : Module Λ[centralizerSubgroup ι γ.val] P :=
      Module.compHom P (mapDomainRingHom Λ (centralizerSubgroup ι γ.val).subtype)
    Module.Finite Λ[centralizerSubgroup ι γ.val] P ∧
      Module.Projective Λ[centralizerSubgroup ι γ.val] P := by
  let Z := centralizerSubgroup ι γ.val; let φZ := mapDomainRingHom Λ Z.subtype
  let _ : Module Λ[Z] Λ[G] := φZ.toModule; let _ : Module Λ[Z] P := Module.compHom P φZ
  have ⟨_, _, hfin, hproj⟩ := Subgroup.restrictSubgroup_compHom_finite_projective (R := Λ) Z P
  exact ⟨hfin, hproj⟩

/-- **The centralizer group-ring trace** `Tr_Λ^{Z_γ}(γ, P) ∈ Λ / [Λ, Λ]` of `γ ∈ Γ` on `P`,
restricted to `Z_γ = centralizerSubgroup ι γ.val`. -/
def centralizerGroupTrace (γ : nonnegSubmonoid deg) : TauCeti.cyclicQuotient ℤ Λ :=
  let Z := centralizerSubgroup ι γ.val
  let _ : Module Λ[Z] P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  have h := centralizer_finite_projective Λ ι deg (P := P) γ
  have _ := h.left; have _ := h.right
  LinearMap.hattoriStallingsGroupTrace Λ Z P (centralizerEnd hPG γ fun _ _ ↦ rfl)

section Implicit
variable {Λ ι deg hker}

/-- Agreement of `centralizerGroupTrace` with `hattoriStallingsGroupTrace` whenever `P` already
carries a compatible `Λ[Z_γ]`-module structure. -/
theorem centralizerGroupTrace_eq_hattoriStallingsGroupTrace (γ : nonnegSubmonoid deg)
    [instZ : Module Λ[centralizerSubgroup ι γ.val] P]
    [Module.Finite Λ[centralizerSubgroup ι γ.val] P]
    [Module.Projective Λ[centralizerSubgroup ι γ.val] P]
    (hPZ : ∀ (r : Λ[centralizerSubgroup ι γ.val]) (p : P),
      r • p = mapDomainRingHom Λ (centralizerSubgroup ι γ.val).subtype r • p)
    (u_Z : Module.End Λ[centralizerSubgroup ι γ.val] P)
    (huZ : ∀ p, u_Z p = single γ (1 : Λ) • p) :
    centralizerGroupTrace Λ ι deg hker hPG γ =
      LinearMap.hattoriStallingsGroupTrace Λ (centralizerSubgroup ι γ.val) P u_Z := by
  let Z := centralizerSubgroup ι γ.val; let φZ := mapDomainRingHom Λ Z.subtype
  obtain rfl : instZ = Module.compHom P φZ := Module.ext' _ _ hPZ
  let _ : Module Λ[Z] P := Module.compHom P φZ
  have hu : centralizerEnd hPG γ (fun _ _ ↦ rfl) = u_Z := by ext p; simp [huZ]
  dsimp only [centralizerGroupTrace]
  rw [hu]

/-- Expanding `centralizerGroupTrace` on a `Λ[G]`-free retract `(π, i)` of `P`. -/
private theorem centralizerGroupTrace_eq_mkQ_sum_of_retract
    {r : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P) (i : P →ₗ[Λ[G]] Fin r → Λ[G]) (hπi : π ∘ₗ i = .id)
    (γ : nonnegSubmonoid deg) [Fintype (G ⧸ (centralizerSubgroup ι γ.val).subtype.range)] :
    centralizerGroupTrace Λ ι deg hker hPG γ =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ q : G ⧸ (centralizerSubgroup ι γ.val).subtype.range,
          (i (single γ (1 : Λ) •
            ((single q.out⁻¹ (1 : Λ) : Λ[G]) • π (Pi.single k 1))) k).coeff q.out⁻¹) := by
  let Z := centralizerSubgroup ι γ.val
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
      Nat.card (centralizerSubgroup ι γ.val) • centralizerGroupTrace Λ ι deg hker hPG γ := by
  let Z := centralizerSubgroup ι γ.val
  let _ : Module Λ[Z] P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  obtain ⟨_, _⟩ := centralizer_finite_projective Λ ι deg (P := P) γ
  let φ_Z := centralizerEnd hPG γ fun _ _ ↦ rfl
  rw [LinearMap.hattoriStallingsTrace_eq_card_nsmul_hattoriStallingsGroupTrace_of_eqLocus
      (eqLocus_conjAut ι deg hι hker γ.val).symm (fun _ _ ↦ rfl)
      (singleOneSMulLinearMap Λ P γ) φ_Z
      (singleOneSMulLinearMap_single_smul hPG hι γ) (fun p ↦ by simp [φ_Z]),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) φ_Z
      (centralizerEnd_apply hPG γ _)]

/-- **`G`-conjugation invariance of `centralizerGroupTrace`.** -/
theorem centralizerGroupTrace_conjNonneg (k : G) (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace Λ ι deg hker hPG (conjNonneg ι deg k γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ := by
  let γ' := conjNonneg ι deg k γ
  let Z := centralizerSubgroup ι γ.val; let Z' := centralizerSubgroup ι γ'.val
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
          have hkz : k * (z : G) = (eZ z : G) * k := by
            dsimp only [eZ]; rw [coe_conjCentralizerEquiv_apply]; simp
          rw [hZ, hZ', hE]
          simp only [mapDomainRingHom_apply, mapDomain_single, Subgroup.coe_subtype,
            MulEquiv.coe_toMonoidHom, ← mul_smul, single_mul_single, one_mul, mul_one, hkz] }
  have hinter (p : P) : uZ' (j p) = j (uZ p) := by
    simp only [j, uZ, uZ', LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      centralizerEnd_apply, ← single_mul_toNonnegSubmonoid_smul hPG,
      ← single_toNonnegSubmonoid_mul_smul hPG, γ', conjNonneg_mul_toNonnegSubmonoid]
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ' (fun _ _ ↦ rfl) uZ'
      (centralizerEnd_apply hPG γ' _),
    centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uZ
      (centralizerEnd_apply hPG γ _)]
  exact j.hattoriStallingsGroupTrace_eq_of_mapDomainRingHom hE hinter
end Implicit

/-- The centralizer group-ring trace descended to `G`-conjugacy classes in `DegreeFiber deg d`. -/
def conjClassGroupTrace (d : ℕ) : ConjClasses ι deg d → TauCeti.cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ ↦ centralizerGroupTrace Λ ι deg hker hPG γ.val) fun a b hab ↦ by
    obtain ⟨k, hk⟩ := (conjSetoid_rel ι deg d a b).1 hab
    have hval : a.val = conjNonneg ι deg k b.val := Subtype.ext (by rw [hk, coe_conjNonneg])
    rw [hval]; exact centralizerGroupTrace_conjNonneg hPG k b.val

@[simp] theorem conjClassGroupTrace_mk {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassGroupTrace Λ ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerGroupTrace Λ ι deg hker hPG γ.val := by rfl
end CentralizerTrace

/-! ### `G`-coinvariants and Lemma 64.15.5 -/

section Coinvariants
variable [Module Λ P] [IsScalarTower Λ Λ[nonnegSubmonoid deg] P]

/-- The `Λ`-linear endomorphism of `Coinvariants Λ G P` induced by `γ₀ ∈ Γ`. -/
def coinvariantEnd (γ₀ : nonnegSubmonoid deg) : Module.End Λ (Coinvariants Λ G P) :=
  Coinvariants.lift ((Coinvariants.mk Λ G P).comp (singleOneSMulLinearMap Λ P γ₀)) fun g p ↦ by
    obtain ⟨g', hg'⟩ := (hker ▸ deg.normal_ker).conj_mem (ι g) ⟨g, rfl⟩ γ₀.val
    have hrel : γ₀ * toNonnegSubmonoid ι deg hker g = toNonnegSubmonoid ι deg hker g' * γ₀ := by
      ext; simp [hg', mul_assoc]
    simp only [LinearMap.comp_apply, singleOneSMulLinearMap_apply,
      ← single_mul_toNonnegSubmonoid_smul hPG, hrel,
      single_toNonnegSubmonoid_mul_smul hPG, Coinvariants.mk_single_one_smul]

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
theorem coinvariantEnd_eq_of_map_eq {γ₁ γ₀ : nonnegSubmonoid deg} (hdeg : deg γ₁.val = deg γ₀.val) :
    coinvariantEnd Λ ι deg hker hPG γ₁ = coinvariantEnd Λ ι deg hker hPG γ₀ := by
  ext p; simp only [coinvariantEnd_mk]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (hker.symm ▸ deg.div_mem_ker_iff.2 hdeg)
  have hγ₁ : γ₁ = toNonnegSubmonoid ι deg hker g * γ₀ := Subtype.ext (by simp [hg, div_mul_cancel])
  rw [hγ₁, single_toNonnegSubmonoid_mul_smul hPG, Coinvariants.mk_single_one_smul]

section CoinvariantTraceFormula
variable {Λ ι deg hker} [IsScalarTower Λ Λ[G] P] [Module.Finite Λ[G] P] [Module.Projective Λ[G] P]

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
    funext j; by_cases hjk : j = k <;> simp [hjk, one_def]
  have haug (z : Λ[G]) : augmentation Λ G z = ∑ g : G, z.coeff g := by
    conv_lhs => rw [← sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp), map_sum]; simp
  simp [i_bar, π_bar, ePi, Pi.basisFun_apply, hsingle, haug]

omit [IsScalarTower Λ Λ[G] P] in
private theorem conjClassGroupTrace_eq_mkQ_sum_cosets [Finite G] (hι : Function.Injective ι)
    {r d : ℕ} (π : (Fin r → Λ[G]) →ₗ[Λ[G]] P) (i : P →ₗ[Λ[G]] Fin r → Λ[G]) (hπi : π ∘ₗ i = .id)
    (γ₀ : DegreeFiber deg d) (c : ConjClasses ι deg d)
    [Fintype (G ⧸ (centralizerSubgroup ι c.out.val.val).subtype.range)] :
    conjClassGroupTrace Λ ι deg hker hPG d c =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ q : G ⧸ (centralizerSubgroup ι c.out.val.val).subtype.range,
          (i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k).coeff
            (degreeFiberEquivGroup hι hker γ₀ (DegreeFiber.conj ι q.out c.out))) := by
  conv_lhs => rw [← Quotient.out_eq c, conjClassGroupTrace_mk]
  let γ := c.out; rw [centralizerGroupTrace_eq_mkQ_sum_of_retract hPG π i hπi γ.val]
  refine congrArg _ <| Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  let gγ := degreeFiberEquivGroup hι hker γ₀ γ
  have hγ_eq : γ.val = toNonnegSubmonoid ι deg hker gγ⁻¹ * γ₀.val :=
    Subtype.ext (by simp [gγ, eq_inv_mul_of_mul_eq (apply_degreeFiberEquivGroup_mul hι hker γ₀ γ)])
  have himg : i (single γ.val (1 : Λ) • ((single q.out⁻¹ (1 : Λ) : Λ[G]) • π (Pi.single k 1))) k =
      single (conjAut ι deg hι hker γ.val.val q.out⁻¹ * gγ⁻¹) (1 : Λ) *
        i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k := by
    have htwist := singleOneSMulLinearMap_single_smul hPG hι γ.val q.out⁻¹ (π (Pi.single k 1))
    simp only [singleOneSMulLinearMap_apply] at htwist
    have hγsmul : single γ.val (1 : Λ) • π (Pi.single k 1) =
        (single gγ⁻¹ (1 : Λ) : Λ[G]) • (single γ₀.val (1 : Λ) • π (Pi.single k 1)) := by
      rw [hγ_eq, single_toNonnegSubmonoid_mul_smul hPG]
    rw [htwist, hγsmul, ← mul_smul, single_mul_single, one_mul,
      congrFun (map_smul i _ _) k, Pi.smul_apply, smul_eq_mul]
  simp [himg, gγ, γ, degreeFiberEquivGroup_conj hι γ₀ γ q.out]

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
      Fintype (G ⧸ (centralizerSubgroup ι c.out.val.val).subtype.range) := Fintype.ofFinite _
  obtain ⟨r, π, i, -, -, hπi⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ[G] P
  rw [finsum_eq_sum_of_fintype, hattoriStallingsTrace_coinvariantEnd_of_retract hPG π i hπi γ₀.val]
  simp only [conjClassGroupTrace_eq_mkQ_sum_cosets hPG hι π i hπi γ₀, ← map_sum]
  congr 1; conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  let yk := i (single γ₀.val (1 : Λ) • π (Pi.single k 1)) k
  let eQ (c : ConjClasses ι deg d) :=
    Subgroup.quotientEquivOfEq (centralizerSubgroup ι c.out.val.val).range_subtype
  rw [← Fintype.sum_sigma (f := fun p :
      (c : ConjClasses ι deg d) × G ⧸ (centralizerSubgroup ι c.out.val.val).subtype.range ↦
    yk.coeff (degreeFiberEquivGroup hι hker γ₀ (DegreeFiber.conj ι p.snd.out p.fst.out)))]
  refine (Fintype.sum_equiv (((Equiv.sigmaCongrRight eQ).trans
    (orbitStabilizerEquiv ι deg d).symm).trans (degreeFiberEquivGroup hι hker γ₀)) _ _ ?_).symm
  rintro ⟨c, q⟩
  have hq : eQ c q = QuotientGroup.mk q.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]; exact Subgroup.quotientEquivOfEq_mk _ _
  simp [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, hq, yk]
end CoinvariantTraceFormula
end Coinvariants
end RingSection

/-! ### Commutative coefficient rings -/

section CommRing
variable (A : Type*) [CommRing A] [Finite G] (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
  (hker : ι.range = deg.ker) {P : Type*} [AddCommGroup P] [Module A[nonnegSubmonoid deg] P]
  [Module A[G] P] [Module.Finite A[G] P] [Module.Projective A[G] P]
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
    centralizerGroupTrace A ι deg hker hPG γ = (TauCeti.commutatorSubmodule ℤ A).mkQ
      (centralizerProjectiveGroupTrace A ι deg hker hPG γ) := by
  simp [Submodule.mkQ_apply, centralizerProjectiveGroupTrace_apply,
    ← TauCeti.cyclicQuotientEquivOfComm_symm_apply]
theorem conjClassGroupTrace_eq_mkQ_conjClassProjectiveGroupTrace (d : ℕ) (c : ConjClasses ι deg d) :
    conjClassGroupTrace A ι deg hker hPG d c = (TauCeti.commutatorSubmodule ℤ A).mkQ
      (conjClassProjectiveGroupTrace A ι deg hker hPG d c) := by
  simp [Submodule.mkQ_apply, conjClassProjectiveGroupTrace_apply,
    ← TauCeti.cyclicQuotientEquivOfComm_symm_apply]

/-- Agreement of `centralizerProjectiveGroupTrace` with `projectiveGroupTrace` whenever `P` already
carries a compatible `A[Z_γ]`-module structure. -/
theorem centralizerProjectiveGroupTrace_eq_projectiveGroupTrace (γ : nonnegSubmonoid deg)
    [Module A P] [Module A[centralizerSubgroup ι γ.val] P]
    [IsScalarTower A A[centralizerSubgroup ι γ.val] P]
    [SMulCommClass A[centralizerSubgroup ι γ.val] A P]
    [Module.Finite A[centralizerSubgroup ι γ.val] P]
    [Module.Projective A[centralizerSubgroup ι γ.val] P]
    (hPZ : ∀ (r : A[centralizerSubgroup ι γ.val]) (p : P),
      r • p = mapDomainRingHom A (centralizerSubgroup ι γ.val).subtype r • p)
    (u_Z : Module.End A[centralizerSubgroup ι γ.val] P)
    (huZ : ∀ p, u_Z p = single γ (1 : A) • p) :
    centralizerProjectiveGroupTrace A ι deg hker hPG γ =
      LinearMap.projectiveGroupTrace A (centralizerSubgroup ι γ.val) P u_Z := by
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
      (Nat.card (centralizerSubgroup ι γ.val) : A) *
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
  simpa [finsum_eq_sum_of_fintype, LinearMap.hattoriStallingsTrace_eq_projectiveTrace,
    conjClassProjectiveGroupTrace_apply, map_sum] using
    congrArg (TauCeti.cyclicQuotientEquivOfComm ℤ A).toAddMonoidHom
      (hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses hPG hι γ₀)

end CommRing
end TauCeti.MonoidExtension
end
