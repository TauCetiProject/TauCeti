/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import TauCeti.FieldTheory.Galois.FixedField

/-!
# `ℤ_p`-extensions and their layers

A **`ℤ_p`-extension** of a field `K` is a Galois extension `L / K` whose Galois group `Γ` is
isomorphic, as a topological group, to the additive group of the `p`-adic integers
(`TauCeti.ZpExtension`). Here the isomorphism `Γ ≃ₜ* Multiplicative ℤ_[p]` is part of the data.
The open subgroups of `ℤ_p` are the subgroups `pⁿ ℤ_p`, so the closed subgroups
`Γₙ = Γ ^ (pⁿ)` of finite index (`TauCeti.ZpExtension.layerSubgroup`) form a decreasing chain with
trivial intersection. Their fixed fields are the **layers**
`K = K₀ ⊂ K₁ ⊂ K₂ ⊂ ⋯ ⊂ L` (`TauCeti.ZpExtension.layer`), the finite Galois subextensions
of the tower along which Iwasawa theory follows class groups and units.

The subgroup `Γₙ` consists of the `pⁿ`-th powers in `Γ`
(`TauCeti.ZpExtension.mem_layerSubgroup_iff_exists_pow_eq`), so it does not depend on the chosen
isomorphism, and neither do the layers (`TauCeti.ZpExtension.layer_eq`). If `γ ∈ Γ` corresponds to
`1 ∈ ℤ_p`, so that it is a topological generator, then `Kₙ` is the field fixed by the single
automorphism `γ ^ (pⁿ)` (`TauCeti.ZpExtension.mem_layer_iff_apply_eq`).

The layer `Kₙ` has degree `pⁿ` over `K` and is Galois over it, the layers increase strictly,
and their union is `L`. Reduction modulo `pⁿ` identifies `Gal(Kₙ / K)` with `ℤ / pⁿ ℤ`
(`TauCeti.ZpExtension.layerGaloisEquiv`): the class of the restriction of `σ ∈ Γ` is the
reduction of the `p`-adic integer corresponding to `σ`. These identifications for different `n`
are compatible with restriction of automorphisms and reduction `ℤ / pᵐ ℤ → ℤ / pⁿ ℤ`.

## Main definitions

* `TauCeti.ZpExtension p K L`: a Galois extension `L / K` with a topological group isomorphism
  `Gal(L/K) ≃ₜ* Multiplicative ℤ_[p]`.
* `TauCeti.ZpExtension.layerSubgroup E n`: the open normal subgroup `Γ ^ (pⁿ)` of `Gal(L/K)`.
* `TauCeti.ZpExtension.layer E n`: the `n`-th layer `Kₙ`, the fixed field of `Γ ^ (pⁿ)`.
* `TauCeti.ZpExtension.layerGaloisEquiv E n`: the isomorphism `Gal(Kₙ/K) ≃* ℤ / pⁿ ℤ`.

## Main results

* `TauCeti.ZpExtension.layer_zero`, `TauCeti.ZpExtension.layer_strictMono`,
  `TauCeti.ZpExtension.finrank_layer`, `TauCeti.ZpExtension.iSup_layer`: `K₀ = K`, the layers
  increase strictly, `[Kₙ : K] = pⁿ`, and the union of the layers is `L`.
* `TauCeti.ZpExtension.fixingSubgroup_layer`: the Galois group of `L / Kₙ` is `Γ ^ (pⁿ)`.
* `TauCeti.ZpExtension.layer_eq`: the layers do not depend on the isomorphism with `ℤ_p`.
* `TauCeti.ZpExtension.mem_layer_iff_apply_eq`: `Kₙ` is the field fixed by `γ ^ (pⁿ)`.
* `TauCeti.ZpExtension.layerGaloisEquiv_restrictNormal`,
  `TauCeti.ZpExtension.castHom_layerGaloisEquiv_restrictNormal`: the identification of
  `Gal(Kₙ/K)` with `ℤ / pⁿ ℤ` on restrictions, and its compatibility between layers.

## References

* R. Sharifi, *Iwasawa theory* (lecture notes), Definition 3.1.1 and Definition 3.2.3.
* L. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §13.1.
-/

public section

open IntermediateField

namespace TauCeti

/-- A **`ℤ_p`-extension** of `K`: a Galois extension `L / K` together with a topological group
isomorphism between its Galois group and the additive group of the `p`-adic integers, written
multiplicatively. -/
@[ext]
structure ZpExtension (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L] where
  /-- The extension `L / K` is Galois. -/
  isGalois : IsGalois K L
  /-- The identification of the Galois group of `L / K` with the additive group of `ℤ_[p]`. -/
  galEquiv : Gal(L/K) ≃ₜ* Multiplicative ℤ_[p]

namespace ZpExtension

variable {p : ℕ} [Fact p.Prime] {K L : Type*} [Field K] [Field L] [Algebra K L]
  (E : ZpExtension p K L)

/-! ### The subgroups `Γ ^ (pⁿ)` -/

/-- The open normal subgroup `Γₙ = Γ ^ (pⁿ)` of the Galois group `Γ` of a `ℤ_p`-extension: the
preimage of `pⁿ ℤ_p` under the identification of `Γ` with `ℤ_p`. -/
noncomputable def layerSubgroup (n : ℕ) : OpenNormalSubgroup Gal(L/K) :=
  (padicIntLevel p n).comap E.galEquiv.toMonoidHom (by exact E.galEquiv.continuous)

/-- The underlying subgroup of `Γ ^ (pⁿ)` is the preimage of `pⁿ ℤ_p`. -/
theorem layerSubgroup_toSubgroup (n : ℕ) :
    (E.layerSubgroup n).toSubgroup =
      (padicIntLevel p n).toSubgroup.comap E.galEquiv.toMonoidHom := by
  rw [layerSubgroup]
  exact OpenNormalSubgroup.toSubgroup_comap _ _ _

/-- An automorphism lies in `Γ ^ (pⁿ)` exactly when the corresponding `p`-adic integer is
divisible by `pⁿ`. -/
theorem mem_layerSubgroup_iff {n : ℕ} {σ : Gal(L/K)} :
    σ ∈ E.layerSubgroup n ↔ (p : ℤ_[p]) ^ n ∣ (E.galEquiv σ).toAdd :=
  OpenNormalSubgroup.mem_comap.trans (mem_padicIntLevel_iff p n)

/-- **`Γ ^ (pⁿ)` consists of the `pⁿ`-th powers.** An automorphism lies in `Γ ^ (pⁿ)` exactly
when it is a `pⁿ`-th power in the Galois group. -/
theorem mem_layerSubgroup_iff_exists_pow_eq {n : ℕ} {σ : Gal(L/K)} :
    σ ∈ E.layerSubgroup n ↔ ∃ τ : Gal(L/K), τ ^ p ^ n = σ := by
  rw [mem_layerSubgroup_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨E.galEquiv.symm (Multiplicative.ofAdd z), E.galEquiv.injective ?_⟩
    rw [map_pow, ContinuousMulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    simp [hz]
  · rintro ⟨τ, rfl⟩
    exact ⟨(E.galEquiv τ).toAdd, by simp⟩

/-- The subgroups `Γ ^ (pⁿ)` do not depend on the identification of the Galois group with
`ℤ_p`. -/
theorem layerSubgroup_eq (E' : ZpExtension p K L) (n : ℕ) :
    E.layerSubgroup n = E'.layerSubgroup n :=
  SetLike.ext fun _ ↦ by
    rw [mem_layerSubgroup_iff_exists_pow_eq, mem_layerSubgroup_iff_exists_pow_eq]

/-- `Γ ^ (p⁰)` is the whole Galois group. -/
@[simp]
theorem layerSubgroup_zero : (E.layerSubgroup 0).toSubgroup = ⊤ :=
  eq_top_iff.mpr fun σ _ ↦ E.mem_layerSubgroup_iff.mpr (by simp)

/-- The subgroups `Γ ^ (pⁿ)` decrease. -/
theorem layerSubgroup_antitone : Antitone E.layerSubgroup := fun _ _ hmn _ hσ ↦
  E.mem_layerSubgroup_iff.mpr ((pow_dvd_pow _ hmn).trans (E.mem_layerSubgroup_iff.mp hσ))

/-- `Γ ^ (pⁿ)` has index `pⁿ` in the Galois group. -/
@[simp]
theorem index_layerSubgroup (n : ℕ) : (E.layerSubgroup n).toSubgroup.index = p ^ n := by
  rw [layerSubgroup_toSubgroup, Subgroup.index_comap_of_surjective _ E.galEquiv.surjective,
    index_padicIntLevel]

/-- The subgroups `Γ ^ (pⁿ)` intersect trivially: a nonzero `p`-adic integer is not divisible by
every power of `p`. -/
theorem iInf_layerSubgroup : ⨅ n, (E.layerSubgroup n).toSubgroup = ⊥ := by
  refine eq_bot_iff.mpr fun σ hσ ↦ ?_
  have hdvd (n : ℕ) : (p : ℤ_[p]) ^ n ∣ (E.galEquiv σ).toAdd :=
    E.mem_layerSubgroup_iff.mp (Subgroup.mem_iInf.mp hσ n)
  have h0 : (E.galEquiv σ).toAdd = 0 := by
    by_contra hne
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne _).mp
      (Ideal.mem_span_singleton.mpr (hdvd ((E.galEquiv σ).toAdd.valuation + 1)))
    omega
  rw [Subgroup.mem_bot, ← map_eq_one_iff E.galEquiv E.galEquiv.injective]
  exact Multiplicative.toAdd.injective h0

/-! ### The layers -/

/-- The `n`-th **layer** `Kₙ` of a `ℤ_p`-extension: the field fixed by `Γ ^ (pⁿ)`. It has degree
`pⁿ` over `K` (`finrank_layer`) and does not depend on the identification of the Galois group
with `ℤ_p` (`layer_eq`). -/
noncomputable def layer (n : ℕ) : IntermediateField K L :=
  fixedField (E.layerSubgroup n).toSubgroup

/-- An element lies in the `n`-th layer exactly when it is fixed by every automorphism whose
`p`-adic integer is divisible by `pⁿ`. -/
theorem mem_layer_iff {n : ℕ} {x : L} :
    x ∈ E.layer n ↔ ∀ σ : Gal(L/K), (p : ℤ_[p]) ^ n ∣ (E.galEquiv σ).toAdd → σ x = x := by
  simp only [layer, mem_fixedField_iff]
  exact forall_congr' fun σ ↦ imp_congr_left E.mem_layerSubgroup_iff

/-- The layers of a `ℤ_p`-extension do not depend on the identification of the Galois group with
`ℤ_p`. -/
theorem layer_eq (E' : ZpExtension p K L) : E.layer = E'.layer :=
  funext fun n ↦ by rw [layer, layer, layerSubgroup_eq E E']

/-- **The Galois group of `L` over the `n`-th layer is `Γ ^ (pⁿ)`.** -/
theorem fixingSubgroup_layer (n : ℕ) :
    (E.layer n).fixingSubgroup = (E.layerSubgroup n).toSubgroup :=
  have := E.isGalois
  fixingSubgroup_fixedField_of_isOpen (E.layerSubgroup n).isOpen

/-- The zeroth layer is the base field. -/
@[simp]
theorem layer_zero : E.layer 0 = ⊥ := by
  have := E.isGalois
  rw [layer, layerSubgroup_zero, InfiniteGalois.fixedField_bot]

/-- The layers increase. -/
theorem layer_mono : Monotone E.layer := fun _ _ hmn ↦
  fixedField_antitone (E.layerSubgroup_antitone hmn)

/-- Each layer is finite over the base field. -/
instance finiteDimensional_layer (n : ℕ) : FiniteDimensional K (E.layer n) :=
  have := E.isGalois
  finiteDimensional_fixedField_of_isOpen (E.layerSubgroup n).isOpen

/-- **The `n`-th layer has degree `pⁿ`** over the base field. -/
@[simp]
theorem finrank_layer (n : ℕ) : Module.finrank K (E.layer n) = p ^ n := by
  have := E.isGalois
  rw [layer, finrank_fixedField_of_isOpen (E.layerSubgroup n).isOpen, index_layerSubgroup]

/-- The layers increase strictly. -/
theorem layer_strictMono : StrictMono E.layer :=
  E.layer_mono.strictMono_of_injective fun m n h ↦
    Nat.pow_right_injective (Fact.out : p.Prime).two_le <| by
      simpa only [finrank_layer] using
        congrArg (fun F : IntermediateField K L ↦ Module.finrank K F) h

/-- Each layer is Galois over the base field: its Galois group over it is the quotient of the
abelian group `Γ` by `Γ ^ (pⁿ)`. -/
instance isGalois_layer (n : ℕ) : IsGalois K (E.layer n) := by
  have := E.isGalois
  refine ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (E.layer n)).mp ?_).2
  rw [fixingSubgroup_layer]
  exact ⟨(E.layerSubgroup n).isOpen, inferInstance⟩

/-- **The union of the layers is the whole `ℤ_p`-extension.** -/
theorem iSup_layer : ⨆ n, E.layer n = ⊤ := by
  have := E.isGalois
  rw [← InfiniteGalois.fixedField_fixingSubgroup (⨆ n, E.layer n), fixingSubgroup_iSup]
  simp only [fixingSubgroup_layer, iInf_layerSubgroup, fixedField_bot]

/-- **The `n`-th layer is the field fixed by `γ ^ (pⁿ)`**, where the automorphism
`γ = galEquiv⁻¹ 1` corresponds to the topological generator `1` of `ℤ_p`. -/
theorem mem_layer_iff_apply_eq {n : ℕ} {x : L} :
    x ∈ E.layer n ↔ E.galEquiv.symm (Multiplicative.ofAdd ((p : ℤ_[p]) ^ n)) x = x := by
  have := E.isGalois
  refine ⟨fun hx ↦ E.mem_layer_iff.mp hx _ (by simp), fun hx ↦ E.mem_layer_iff.mpr ?_⟩
  -- The stabilizer of `x` is open; pull it back to an open subgroup `U` of `ℤ_p`.
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hopen : IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
    have := adjoin.finiteDimensional hint
    simpa using fixingSubgroup_isOpen K⟮x⟯
  let U : OpenSubgroup (Multiplicative ℤ_[p]) :=
    OpenSubgroup.comap E.galEquiv.symm.toMonoidHom (by exact E.galEquiv.symm.continuous)
      ⟨MulAction.stabilizer Gal(L/K) x, hopen⟩
  -- Membership in a preimage and in a stabilizer unfold to this by definition.
  have hU {y : Multiplicative ℤ_[p]} : y ∈ U ↔ E.galEquiv.symm y x = x := Iff.rfl
  -- `U` contains some `pᵐ ℤ_p` and `pⁿ`, hence all of `pⁿ ℤ_p = pⁿ ℤ + pⁿ⁺ᵐ ℤ_p`.
  obtain ⟨m, hm⟩ := exists_padicIntLevel_le p U
  intro σ ⟨z, hz⟩
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec m z)
  have hσ : E.galEquiv σ = Multiplicative.ofAdd ((p : ℤ_[p]) ^ n) ^ z.appr m *
      Multiplicative.ofAdd ((p : ℤ_[p]) ^ m * ((p : ℤ_[p]) ^ n * w)) := by
    apply Multiplicative.toAdd.injective
    rw [hz, toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_eq_mul]
    linear_combination (p : ℤ_[p]) ^ n * hw
  have hmem : E.galEquiv σ ∈ U :=
    hσ ▸ U.mul_mem (U.pow_mem (hU.mpr hx) _) (hm ((mem_padicIntLevel_iff p m).mpr (by simp)))
  simpa using hU.mp hmem

/-! ### The Galois groups of the layers -/

/-- The reduction modulo `pⁿ` of the `p`-adic integer of an automorphism of a `ℤ_p`-extension, as a
homomorphism to `ℤ / pⁿ ℤ` written multiplicatively. Its kernel is `Γ ^ (pⁿ)`. -/
private noncomputable def toZModPowHom (n : ℕ) : Gal(L/K) →* Multiplicative (ZMod (p ^ n)) :=
  ((PadicInt.toZModPow n).toAddMonoidHom.toMultiplicative).comp E.galEquiv.toMonoidHom

private theorem surjective_toZModPowHom (n : ℕ) : Function.Surjective (E.toZModPowHom n) :=
  (surjective_toMultiplicative_toZModPow p n).comp E.galEquiv.surjective

private theorem layerSubgroup_eq_ker_toZModPowHom (n : ℕ) :
    (E.layerSubgroup n).toSubgroup = (E.toZModPowHom n).ker := by
  rw [toZModPowHom, ← MonoidHom.comap_ker, ← padicIntLevel_toSubgroup, layerSubgroup_toSubgroup]

private theorem layerSubgroup_eq_ker_restrictNormalHom (n : ℕ) :
    (E.layerSubgroup n).toSubgroup = (AlgEquiv.restrictNormalHom (E.layer n)).ker := by
  rw [restrictNormalHom_ker, fixingSubgroup_layer]

/-- The isomorphism `Gal(Kₙ / K) ≃* ℤ / pⁿ ℤ` of the Galois group of the `n`-th layer with the
integers modulo `pⁿ`, written multiplicatively: the restriction of `σ ∈ Γ` to `Kₙ` corresponds to
the reduction modulo `pⁿ` of the `p`-adic integer of `σ` (`layerGaloisEquiv_restrictNormal`). -/
noncomputable def layerGaloisEquiv (n : ℕ) :
    Gal(E.layer n/K) ≃* Multiplicative (ZMod (p ^ n)) :=
  letI := E.isGalois
  (QuotientGroup.liftEquiv _ (AlgEquiv.restrictNormalHom_surjective L)
      (E.layerSubgroup_eq_ker_restrictNormalHom n)).symm.trans <|
    QuotientGroup.liftEquiv _ (E.surjective_toZModPowHom n) (E.layerSubgroup_eq_ker_toZModPowHom n)

/-- **The Galois group of the `n`-th layer is `ℤ / pⁿ ℤ`**: the restriction of `σ ∈ Gal(L/K)` to
the `n`-th layer corresponds to the reduction modulo `pⁿ` of the `p`-adic integer of `σ`. -/
@[simp]
theorem layerGaloisEquiv_restrictNormal (n : ℕ) (σ : Gal(L/K)) :
    E.layerGaloisEquiv n (σ.restrictNormal (E.layer n)) =
      Multiplicative.ofAdd (PadicInt.toZModPow n (E.galEquiv σ).toAdd) := by
  have := E.isGalois
  -- `AlgEquiv.restrictNormalHom` is defined as `σ ↦ σ.restrictNormal _`.
  have h : σ.restrictNormal (E.layer n) = AlgEquiv.restrictNormalHom (E.layer n) σ := rfl
  rw [layerGaloisEquiv, MulEquiv.trans_apply, h, ← QuotientGroup.liftEquiv_mk _
    (AlgEquiv.restrictNormalHom_surjective L) (E.layerSubgroup_eq_ker_restrictNormalHom n),
    MulEquiv.symm_apply_apply, QuotientGroup.liftEquiv_mk]
  simp [toZModPowHom]

/-- The Galois group of each layer over the base field is cyclic. -/
instance isCyclic_layer (n : ℕ) : IsCyclic Gal(E.layer n/K) :=
  (E.layerGaloisEquiv n).isCyclic.mpr inferInstance

/-- **The identifications of the Galois groups of the layers are compatible with restriction**:
for `m ≤ n`, reducing modulo `pᵐ` the class in `ℤ / pⁿ ℤ` of the restriction of `σ` to the `n`-th
layer gives the class of its restriction to the `m`-th layer. -/
theorem castHom_layerGaloisEquiv_restrictNormal {m n : ℕ} (hmn : m ≤ n) (σ : Gal(L/K)) :
    ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))
        (E.layerGaloisEquiv n (σ.restrictNormal (E.layer n))).toAdd =
      (E.layerGaloisEquiv m (σ.restrictNormal (E.layer m))).toAdd := by
  simp only [layerGaloisEquiv_restrictNormal, toAdd_ofAdd, ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow m n hmn _

end ZpExtension

end TauCeti
