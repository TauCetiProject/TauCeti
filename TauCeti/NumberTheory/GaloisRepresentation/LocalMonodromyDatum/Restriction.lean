/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.LocalMonodromyDatum
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition

/-!
# Restriction of local monodromy data

Let `D` be a local monodromy datum on a profinite group `H`, with inertia `I`, tame character
`t`, Frobenius class `Fr ∈ H ⧸ I` and integer `q`. Weight–monodromy purity is read off on
subgroups of `H` that are much smaller than open ones, such as the absolute Galois group of the
`p`-power Kummer tower `k(ϖ^{1/p^∞})` inside that of a `p`-adic field `k`. Such a subgroup
inherits a local monodromy datum as soon as it still sees an open part of `H ⧸ I ≅ ℤ̂` and the
tame character does not vanish on its inertia.

Since such Galois groups are usually not literally subgroups of `G_k` but map to it, this file
restricts along a continuous homomorphism `φ : K →ₜ* H` from a profinite group `K`; restricting to
a closed subgroup is the case of its inclusion. Call `φ` *admissible* for `D`
(`LocalMonodromyDatum.IsAdmissible`) when its *residue image* `φ(K) I / I ⊆ H ⧸ I`
(`LocalMonodromyDatum.residueRange`) is open and `t ∘ φ` is not identically zero on
`φ⁻¹(I)`. The residue image is then the closure of the powers of `Fr ^ f` for a unique `f ≥ 1`,
the *residue index* (`LocalMonodromyDatum.IsAdmissible.residueIndex`). The restricted datum
`D.comap φ h` on `K` has

* inertia `φ⁻¹(I)` and tame character `t ∘ φ`;
* integer `q ^ f`;
* Frobenius coset the elements `Φ` of `K` with `φ(Φ) ∈ Fr ^ f`.

The quotient `K ⧸ φ⁻¹(I)` embeds into `H ⧸ I ≅ ℤ̂` with image the open subgroup `f ℤ̂`, which is
again isomorphic to `ℤ̂` because `ℤ̂` is torsion free; this is where the openness of the residue
image is used. Restriction is transitive, with multiplicative residue indices; restricting along
the identity changes nothing; and it commutes with rescaling the tame character and with
isomorphisms of local monodromy data, with the same constant.

## Main definitions

* `TauCeti.LocalMonodromyDatum.residueRange D φ`: the image of `K` in `H ⧸ I`.
* `TauCeti.LocalMonodromyDatum.IsAdmissible D φ`: the residue image is open and the tame
  character does not vanish on `φ⁻¹(I)`.
* `TauCeti.LocalMonodromyDatum.IsAdmissible.residueIndex`: the residue index `f`.
* `TauCeti.LocalMonodromyDatum.comap D φ h`: the restricted local monodromy datum on `K`.

## Main results

* `TauCeti.LocalMonodromyDatum.isOpen_residueRange_iff`: the residue image is open exactly when
  it contains a positive power of the Frobenius class.
* `TauCeti.LocalMonodromyDatum.IsAdmissible.of_isOpen_range`: a homomorphism with open image, such
  as the inclusion of an open subgroup, is admissible.
* `TauCeti.LocalMonodromyDatum.IsAdmissible.frobClass_pow_mem_residueRange_iff`: `Fr ^ n` lies in
  the residue image exactly when `f ∣ n`.
* `TauCeti.LocalMonodromyDatum.comap_inertia`, `comap_tame_apply`, `comap_q`,
  `mem_comap_frobenius`: the inertia, tame character, integer and Frobenius coset of the
  restricted datum; `coe_eq_comap_frobClass_pow_iff`: the classes of the powers of its Frobenius.
* `TauCeti.LocalMonodromyDatum.comap_comap`, `TauCeti.LocalMonodromyDatum.comap_id`: restriction
  is transitive, and trivial along the identity.
* `TauCeti.LocalMonodromyDatum.comap_smul`: restriction commutes with rescaling.
* `TauCeti.LocalMonodromyDatum.IsIso.comap`: an isomorphism `D → D'` with constant `c` restricts
  to an isomorphism of the restricted data with constant `c`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §9, proof of Theorem 9.6.
-/

public section

noncomputable section

namespace TauCeti

namespace LocalMonodromyDatum

universe u u' v w

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H]
  {H' : Type u'} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [CompactSpace H']
  [T2Space H'] [TotallyDisconnectedSpace H']
  {K : Type v} [Group K] [TopologicalSpace K]

section ResidueRange

variable (D : LocalMonodromyDatum ℓ H) (φ : K →ₜ* H)

/-- The **residue image** of `φ : K →ₜ* H`: the image of `K` in `H ⧸ I`. -/
def residueRange : Subgroup (H ⧸ D.inertia) :=
  ((QuotientGroup.mk' D.inertia).comp (φ : K →* H)).range

variable {D φ} in
/-- Membership in the residue image. -/
@[simp]
theorem mem_residueRange {x : H ⧸ D.inertia} :
    x ∈ D.residueRange φ ↔ ∃ k, (φ k : H ⧸ D.inertia) = x :=
  Iff.rfl

/-- `φ : K →ₜ* H` is **admissible** for restricting the local monodromy datum `D`: the image of
`K` in `H ⧸ I` is open, and the tame character does not vanish identically on `φ⁻¹(I)`. -/
structure IsAdmissible : Prop where
  isOpen_residueRange : IsOpen (D.residueRange φ : Set (H ⧸ D.inertia))
  exists_tame_ne_one : ∃ (σ : K) (hσ : φ σ ∈ D.inertia), D.tame ⟨φ σ, hσ⟩ ≠ 1

variable {D φ}

/-- **A homomorphism with open image is admissible**; for instance, the inclusion of an open
subgroup. The tame character does not vanish on the open subgroup `φ(K) ∩ I` of inertia. -/
theorem IsAdmissible.of_isOpen_range (hφ : IsOpen (Set.range φ)) : D.IsAdmissible φ where
  isOpen_residueRange := by
    have h : (D.residueRange φ : Set (H ⧸ D.inertia)) =
        (QuotientGroup.mk : H → H ⧸ D.inertia) '' Set.range φ := by
      rw [← Set.range_comp]
      exact Set.ext fun _ ↦ mem_residueRange
    rw [h]
    exact QuotientGroup.isOpenMap_coe _ hφ
  exists_tame_ne_one := by
    let V : Subgroup D.inertia := (φ : K →* H).range.subgroupOf D.inertia
    have hV : IsOpen (V : Set D.inertia) := hφ.preimage continuous_subtypeVal
    obtain ⟨⟨_, hx⟩, ⟨k, rfl⟩, hσ⟩ := D.exists_tame_ne_one_of_isOpen V hV
    exact ⟨k, hx, hσ⟩

variable (D) in
/-- The identity is admissible. -/
theorem isAdmissible_id : D.IsAdmissible (ContinuousMonoidHom.id H) :=
  .of_isOpen_range (by rw [ContinuousMonoidHom.coe_id, Set.range_id]; exact isOpen_univ)

/-- Admissibility does not see a rescaling of the tame character. -/
theorem isAdmissible_smul_iff (c : ℚ_[ℓ]ˣ) : (c • D).IsAdmissible φ ↔ D.IsAdmissible φ := by
  have key (σ : D.inertia) : (c • D).tame σ ≠ 1 ↔ D.tame σ ≠ 1 := by
    rw [Ne, Ne, ← toAdd_eq_zero, toAdd_smul_tame, mul_eq_zero, ← toAdd_eq_zero]
    simp only [Units.ne_zero, false_or]
  exact ⟨fun ⟨hU, σ, hσ, hne⟩ ↦ ⟨hU, σ, hσ, (key _).1 hne⟩,
    fun ⟨hU, σ, hσ, hne⟩ ↦ ⟨hU, σ, hσ, (key _).2 hne⟩⟩

variable [CompactSpace K]

variable (D φ) in
/-- The residue image is closed, being the image of a compact group. -/
theorem isClosed_residueRange : IsClosed (D.residueRange φ : Set (H ⧸ D.inertia)) := by
  have h : (D.residueRange φ : Set (H ⧸ D.inertia)) = Set.range fun k ↦ (φ k : H ⧸ D.inertia) :=
    Set.ext fun _ ↦ mem_residueRange
  rw [h]
  exact (isCompact_range (QuotientGroup.continuous_mk.comp φ.continuous)).isClosed

/-- The residue image is open exactly when it contains a positive power of the Frobenius class. -/
theorem isOpen_residueRange_iff :
    IsOpen (D.residueRange φ : Set (H ⧸ D.inertia)) ↔
      ∃ n ≠ 0, D.frobClass ^ n ∈ D.residueRange φ := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn, hFn⟩ ↦
    Subgroup.isOpen_of_isClosed_of_pow_mem D.denseRange_zpow_frobClass
      (D.isClosed_residueRange φ) hn hFn⟩
  have : Finite ((H ⧸ D.inertia) ⧸ D.residueRange φ) := Subgroup.quotient_finite_of_isOpen _ h
  obtain ⟨n, hn, -, hFn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (D.residueRange φ).index_ne_zero_of_finite D.frobClass
  exact ⟨n, hn.ne', hFn⟩

namespace IsAdmissible

variable (h : D.IsAdmissible φ)

include h in
/-- An admissible homomorphism reaches a positive power of the Frobenius class. -/
theorem exists_frobClass_pow_mem : ∃ n, 0 < n ∧ D.frobClass ^ n ∈ D.residueRange φ :=
  let ⟨n, hn, hFn⟩ := isOpen_residueRange_iff.1 h.isOpen_residueRange
  ⟨n, Nat.pos_of_ne_zero hn, hFn⟩

open Classical in
/-- The **residue index** `f` of an admissible homomorphism: the least positive integer with
`Fr ^ f` in the residue image. The residue image is the closure of the powers of `Fr ^ f`, and
`Fr ^ n` lies in it exactly when `f ∣ n` (`frobClass_pow_mem_residueRange_iff`). -/
def residueIndex : ℕ :=
  Nat.find h.exists_frobClass_pow_mem

open Classical in
/-- The residue index is positive. -/
theorem residueIndex_pos : 0 < h.residueIndex :=
  (Nat.find_spec h.exists_frobClass_pow_mem).1

open Classical in
/-- The `f`-th power of the Frobenius class lies in the residue image. -/
theorem frobClass_pow_residueIndex_mem : D.frobClass ^ h.residueIndex ∈ D.residueRange φ :=
  (Nat.find_spec h.exists_frobClass_pow_mem).2

/-- Some element of `K` maps into the class `Fr ^ f`. -/
theorem exists_coe_eq_frobClass_pow :
    ∃ k : K, (φ k : H ⧸ D.inertia) = D.frobClass ^ h.residueIndex :=
  h.frobClass_pow_residueIndex_mem

/-- **The powers of Frobenius in the residue image** are the multiples of the residue index:
`Fr ^ n` lies in the residue image exactly when `f ∣ n`. -/
theorem frobClass_pow_mem_residueRange_iff (n : ℕ) :
    D.frobClass ^ n ∈ D.residueRange φ ↔ h.residueIndex ∣ n := by
  refine ⟨fun hn ↦ ?_, fun ⟨m, hm⟩ ↦ hm ▸ pow_mul D.frobClass _ m ▸
    (D.residueRange φ).pow_mem h.frobClass_pow_residueIndex_mem m⟩
  -- The remainder of `n` modulo `f` is a smaller exponent with the same property, hence zero.
  have hmod : D.frobClass ^ (n % h.residueIndex) ∈ D.residueRange φ := by
    rw [← Nat.mod_add_div n h.residueIndex, pow_add, pow_mul] at hn
    exact (Subgroup.mul_mem_cancel_right _
      ((D.residueRange φ).pow_mem h.frobClass_pow_residueIndex_mem _)).1 hn
  refine Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos fun hpos ↦ ?_)
  classical
  exact Nat.find_min h.exists_frobClass_pow_mem (Nat.mod_lt n h.residueIndex_pos) ⟨hpos, hmod⟩

/-- `Fr ^ n` lies in the residue image exactly when `f ∣ n`, for integer exponents. -/
theorem frobClass_zpow_mem_residueRange_iff (n : ℤ) :
    D.frobClass ^ n ∈ D.residueRange φ ↔ (h.residueIndex : ℤ) ∣ n := by
  rcases Int.natAbs_eq n with hn | hn <;> rw [hn]
  · rw [zpow_natCast, h.frobClass_pow_mem_residueRange_iff, Int.natCast_dvd_natCast]
  · rw [zpow_neg, Subgroup.inv_mem_iff, zpow_natCast, h.frobClass_pow_mem_residueRange_iff,
      Int.dvd_neg, Int.natCast_dvd_natCast]

/-- The residue index is characterized by the powers of Frobenius in the residue image. -/
theorem residueIndex_eq_iff {f : ℕ} :
    h.residueIndex = f ↔ ∀ n : ℕ, D.frobClass ^ n ∈ D.residueRange φ ↔ f ∣ n := by
  refine ⟨fun hf ↦ hf ▸ h.frobClass_pow_mem_residueRange_iff, fun hf ↦ Nat.dvd_antisymm
    ((h.frobClass_pow_mem_residueRange_iff f).1 ((hf f).2 dvd_rfl))
    ((hf _).1 h.frobClass_pow_residueIndex_mem)⟩

/-- The residue index is `1` exactly when the Frobenius class lies in the residue image. -/
theorem residueIndex_eq_one_iff : h.residueIndex = 1 ↔ D.frobClass ∈ D.residueRange φ := by
  rw [← pow_one D.frobClass, h.frobClass_pow_mem_residueRange_iff, Nat.dvd_one]

variable [IsTopologicalGroup K] [TotallyDisconnectedSpace K]

/-- **The residue quotient of `K` is `ℤ̂`.** If `φ(k₀)` lies in the class `Fr ^ f`, then
`K ⧸ φ⁻¹(I)` is isomorphic to `ℤ̂` by an isomorphism sending the class of `k₀` to the generator. -/
theorem exists_continuousMulEquiv_zHat {k₀ : K}
    (hk₀ : (φ k₀ : H ⧸ D.inertia) = D.frobClass ^ h.residueIndex) :
    ∃ e : K ⧸ D.inertia.comap (φ : K →* H) ≃ₜ* zHat.{v}, e k₀ = zHat.gen := by
  -- `K ⧸ φ⁻¹(I)` embeds into `H ⧸ I ≅ ℤ̂` with image the open subgroup topologically generated by
  -- `Fr ^ f`, and raising to the `f`-th power is injective on the torsion-free group `ℤ̂`.
  let I' := D.inertia.comap (φ : K →* H)
  have : IsClosed (I' : Set K) := D.isClosed_inertia.preimage φ.continuous
  -- The induced embedding `ψ : K ⧸ φ⁻¹(I) → H ⧸ I`, carrying the lift of `k₀` to that of `Fr ^ f`.
  let ψ : K ⧸ I' →ₜ* H ⧸ D.inertia :=
    ⟨QuotientGroup.map I' D.inertia (φ : K →* H) le_rfl,
      (QuotientGroup.isQuotientMap_mk I').continuous_iff.2
        (QuotientGroup.continuous_mk.comp φ.continuous)⟩
  have hψ : Function.Injective ψ := (QuotientGroup.map_injective_iff _ _ _ le_rfl).2 le_rfl
  have hψk (x : zHat.{v}) :
      ψ (zHat.lift (k₀ : K ⧸ I') x) = zHat.lift (D.frobClass ^ h.residueIndex) x := by
    rw [zHat.map_lift]
    exact congrArg (fun a ↦ (zHat.lift a : zHat.{v} →ₜ* H ⧸ D.inertia) x) hk₀
  -- Injectivity: through `H ⧸ I ≅ ℤ̂`, the lift of `Fr ^ f` is the `f`-th power map.
  obtain ⟨e, he⟩ := D.exists_continuousMulEquiv_zHat
  have hinj : Function.Injective (zHat.lift (k₀ : K ⧸ I') : zHat.{v} →ₜ* K ⧸ I') := by
    intro x y hxy
    have hxy' := congrArg (fun z ↦ e (ψ z)) hxy
    simp only [hψk] at hxy'
    have he' (z : zHat.{v}) : e (zHat.lift (D.frobClass ^ h.residueIndex) z) =
        zHat.lift (zHat.gen ^ h.residueIndex) z := by
      rw [← ContinuousMonoidHom.coe_coe e, zHat.map_lift, ContinuousMonoidHom.coe_coe, map_pow,
        he]
    rw [he', he'] at hxy'
    exact zHat.lift_gen_pow_injective h.residueIndex_pos.ne' hxy'
  -- Surjectivity: the open residue image is the closure of its intersection with the dense
  -- subgroup generated by `Fr`, which consists of the powers of `Fr ^ f`.
  have hsub : (D.residueRange φ : Set (H ⧸ D.inertia)) ⊆
      Set.range (zHat.lift (D.frobClass ^ h.residueIndex) : zHat.{v} →ₜ* H ⧸ D.inertia) := by
    refine (Dense.open_subset_closure_inter D.denseRange_zpow_frobClass
      h.isOpen_residueRange).trans (closure_minimal ?_
        (isCompact_range (zHat.lift _).continuous).isClosed)
    rintro _ ⟨hx, n, rfl⟩
    obtain ⟨m, rfl⟩ := (h.frobClass_zpow_mem_residueRange_iff n).1 hx
    exact ⟨zHat.gen ^ m, by simp only [map_zpow, zHat.lift_gen, zpow_mul, zpow_natCast]⟩
  have hsurj : Function.Surjective (zHat.lift (k₀ : K ⧸ I') : zHat.{v} →ₜ* K ⧸ I') := by
    intro y
    induction y using QuotientGroup.induction_on with | H k => ?_
    obtain ⟨x, hx⟩ := hsub ⟨k, rfl⟩
    exact ⟨x, hψ ((hψk x).trans hx)⟩
  exact ⟨zHat.liftContinuousMulEquiv _ ⟨hinj, hsurj⟩, zHat.liftContinuousMulEquiv_apply_self _ _⟩

end IsAdmissible

end ResidueRange

section Comap

variable [CompactSpace K] [IsTopologicalGroup K] [T2Space K] [TotallyDisconnectedSpace K]
  {L : Type w} [Group L] [TopologicalSpace L] [CompactSpace L]

variable (D : LocalMonodromyDatum ℓ H) (φ : K →ₜ* H) (h : D.IsAdmissible φ)

/-- **The restriction of a local monodromy datum along an admissible homomorphism** `φ : K →ₜ* H`:
inertia `φ⁻¹(I)`, tame character `t ∘ φ`, integer `q ^ f` and Frobenius coset the elements of `K`
mapping into the class `Fr ^ f`, where `f` is the residue index (`mem_comap_frobenius`). Along
the inclusion of a closed subgroup `H'`, this is the restricted datum `D|_{H'}`. -/
def comap : LocalMonodromyDatum ℓ K where
  inertia := D.inertia.comap (φ : K →* H)
  isClosed_inertia := D.isClosed_inertia.preimage φ.continuous
  tame := D.tame.comp
    ⟨(φ : K →* H).subgroupComap D.inertia, (φ.continuous.comp continuous_subtypeVal).subtype_mk _⟩
  tame_ne_one hne := by
    obtain ⟨σ, hσ, hne'⟩ := h.exists_tame_ne_one
    exact hne' (DFunLike.congr_fun hne ⟨σ, hσ⟩)
  q := D.q ^ h.residueIndex
  two_le_q := D.two_le_q.trans (Nat.le_self_pow h.residueIndex_pos.ne' _)
  coprime_q := D.coprime_q.pow_left _
  frobClass := (h.exists_coe_eq_frobClass_pow.choose : K ⧸ D.inertia.comap (φ : K →* H))
  exists_continuousMulEquiv_zHat :=
    h.exists_continuousMulEquiv_zHat h.exists_coe_eq_frobClass_pow.choose_spec
  tame_conj Φ hΦ σ := by
    -- `φ(Φ)` lies in the class `Fr ^ f`, and `φ` carries conjugation by `Φ` to conjugation by
    -- `φ(Φ)`.
    have hφΦ : (φ Φ : H ⧸ D.inertia) = D.frobClass ^ h.residueIndex :=
      (congrArg (QuotientGroup.map _ D.inertia (φ : K →* H) le_rfl) hΦ).trans
        h.exists_coe_eq_frobClass_pow.choose_spec
    have hconj : (φ : K →* H).subgroupComap D.inertia (MulAut.conjNormal Φ σ) =
        MulAut.conjNormal (φ Φ) ((φ : K →* H).subgroupComap D.inertia σ) :=
      Subtype.ext <| (congrArg φ (MulAut.conjNormal_apply Φ σ)).trans <| by
        rw [map_mul, map_mul, map_inv, MulAut.conjNormal_apply]
        -- `subgroupComap` is `φ` on underlying elements; Mathlib's `subgroupComap_apply_coe` is
        -- stated for the submonoid preimage, so it does not match this subgroup preimage.
        rfl
    rw [Nat.cast_pow]
    exact (congrArg (fun x ↦ (D.tame x).toAdd) hconj).trans
      (D.tame_conj_of_coe_eq_frobClass_pow hφΦ _)

/-- The inertia of the restricted datum is the preimage of inertia. -/
@[simp]
theorem comap_inertia : (D.comap φ h).inertia = D.inertia.comap (φ : K →* H) :=
  (rfl)

/-- The tame character of the restricted datum is the composite `t ∘ φ`. -/
@[simp]
theorem comap_tame_apply (σ : K) (hσ : σ ∈ (D.comap φ h).inertia) (hσ' : φ σ ∈ D.inertia) :
    (D.comap φ h).tame ⟨σ, hσ⟩ = D.tame ⟨φ σ, hσ'⟩ :=
  (rfl)

/-- The integer of the restricted datum is `q ^ f`, for the residue index `f`. -/
@[simp]
theorem comap_q : (D.comap φ h).q = D.q ^ h.residueIndex :=
  (rfl)

/-- **The powers of Frobenius of the restricted datum.** An element `k` of `K` lies in the class
`(Fr') ^ n` of the restricted datum exactly when `φ(k)` lies in the class `Fr ^ (f * n)`. -/
theorem coe_eq_comap_frobClass_pow_iff (k : K) (n : ℕ) :
    (k : K ⧸ (D.comap φ h).inertia) = (D.comap φ h).frobClass ^ n ↔
      (φ k : H ⧸ D.inertia) = D.frobClass ^ (h.residueIndex * n) := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : K, (D.comap φ h).frobClass = k₀ ∧
      (φ k₀ : H ⧸ D.inertia) = D.frobClass ^ h.residueIndex :=
    ⟨_, rfl, h.exists_coe_eq_frobClass_pow.choose_spec⟩
  rw [hk₀.1, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq, comap_inertia, Subgroup.mem_comap,
    map_mul, map_inv, map_pow, ← QuotientGroup.eq, QuotientGroup.mk_pow,
    MonoidHom.coe_ofClass, hk₀.2, ← pow_mul, eq_comm]

/-- **The Frobenius class of the restricted datum** consists of the elements `k` of `K` with
`φ(k)` in the class `Fr ^ f`. -/
@[simp]
theorem coe_eq_comap_frobClass_iff (k : K) :
    (k : K ⧸ (D.comap φ h).inertia) = (D.comap φ h).frobClass ↔
      (φ k : H ⧸ D.inertia) = D.frobClass ^ h.residueIndex := by
  rw [← pow_one (D.comap φ h).frobClass, coe_eq_comap_frobClass_pow_iff, mul_one]

/-- **The Frobenius coset of the restricted datum**: the elements `Φ` of `K` with `φ(Φ)` in the
class `Fr ^ f`. -/
theorem mem_comap_frobenius {Φ : K} :
    Φ ∈ (D.comap φ h).frobenius ↔ (φ Φ : H ⧸ D.inertia) = D.frobClass ^ h.residueIndex := by
  rw [mem_frobenius, coe_eq_comap_frobClass_iff]

variable {D φ}

/-- A homomorphism admissible for the restricted datum, composed with `φ`, is admissible for
`D`. -/
theorem IsAdmissible.comp {ψ : L →ₜ* K} (h' : (D.comap φ h).IsAdmissible ψ) :
    D.IsAdmissible (φ.comp ψ) where
  isOpen_residueRange := isOpen_residueRange_iff.2
    ⟨h.residueIndex * h'.residueIndex, Nat.mul_ne_zero h.residueIndex_pos.ne'
      h'.residueIndex_pos.ne',
      let ⟨l, hl⟩ := h'.exists_coe_eq_frobClass_pow
      ⟨l, (coe_eq_comap_frobClass_pow_iff D φ h (ψ l) _).1 hl⟩⟩
  exists_tame_ne_one := h'.exists_tame_ne_one

/-- **Residue indices multiply** under composition. -/
theorem IsAdmissible.residueIndex_comp {ψ : L →ₜ* K} (h' : (D.comap φ h).IsAdmissible ψ) :
    (h.comp h').residueIndex = h.residueIndex * h'.residueIndex := by
  refine (h.comp h').residueIndex_eq_iff.2 fun n ↦ ⟨fun ⟨l, hl⟩ ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := (h.frobClass_pow_mem_residueRange_iff n).1 ⟨ψ l, hl⟩
    exact mul_dvd_mul_left _ ((h'.frobClass_pow_mem_residueRange_iff m).1
      ⟨l, (coe_eq_comap_frobClass_pow_iff D φ h (ψ l) m).2 hl⟩)
  · obtain ⟨l, hl⟩ := h'.exists_coe_eq_frobClass_pow
    refine ⟨l ^ m, ?_⟩
    have hlm := (coe_eq_comap_frobClass_pow_iff D φ h (ψ (l ^ m)) (h'.residueIndex * m)).1
      (by rw [map_pow, QuotientGroup.mk_pow, hl, pow_mul])
    rwa [← mul_assoc, ← hm] at hlm

/-- **Restriction is transitive**: restricting `D` along `φ` and then along `ψ` is restricting it
along `φ ∘ ψ`. -/
theorem comap_comap [IsTopologicalGroup L] [T2Space L] [TotallyDisconnectedSpace L]
    {ψ : L →ₜ* K} (h' : (D.comap φ h).IsAdmissible ψ) :
    (D.comap φ h).comap ψ h' = D.comap (φ.comp ψ) (h.comp h') := by
  refine LocalMonodromyDatum.ext rfl (fun _ _ _ ↦ rfl) (Set.ext fun Φ ↦ ?_) ?_
  · rw [mem_comap_frobenius, mem_comap_frobenius, coe_eq_comap_frobClass_pow_iff,
      h.residueIndex_comp h', ContinuousMonoidHom.coe_comp, Function.comp_apply]
  · rw [comap_q, comap_q, comap_q, h.residueIndex_comp h', pow_mul]

variable (D) in
/-- **Restriction along the identity** gives back the datum. -/
theorem comap_id : D.comap (ContinuousMonoidHom.id H) (isAdmissible_id D) = D := by
  have h1 : (isAdmissible_id D).residueIndex = 1 :=
    (isAdmissible_id D).residueIndex_eq_one_iff.2 (QuotientGroup.mk_surjective D.frobClass)
  refine LocalMonodromyDatum.ext (Subgroup.comap_id _) (fun _ _ _ ↦ rfl) (Set.ext fun Φ ↦ ?_) ?_
  · rw [mem_comap_frobenius, h1, pow_one, ContinuousMonoidHom.coe_id, id, mem_frobenius]
  · rw [comap_q, h1, pow_one]

/-- **Restriction commutes with rescaling** the tame character. -/
theorem comap_smul (c : ℚ_[ℓ]ˣ) (h : (c • D).IsAdmissible φ) :
    (c • D).comap φ h = c • D.comap φ ((isAdmissible_smul_iff c).1 h) := by
  have hf : h.residueIndex = ((isAdmissible_smul_iff c).1 h).residueIndex :=
    h.residueIndex_eq_iff.2 ((isAdmissible_smul_iff c).1 h).frobClass_pow_mem_residueRange_iff
  refine LocalMonodromyDatum.ext rfl (fun _ _ _ ↦ rfl) (Set.ext fun Φ ↦ ?_) ?_
  · rw [smul_frobenius, mem_comap_frobenius, mem_comap_frobenius, hf]
    -- `c • D` has the same inertia and Frobenius class as `D` (`smul_inertia`, `smul_frobClass`),
    -- so the two sides are the same statement in the same quotient `H ⧸ D.inertia`.
    exact Iff.rfl
  · rw [smul_q, comap_q, comap_q, hf, smul_q]

end Comap

section IsIso

variable {D : LocalMonodromyDatum ℓ H} {D' : LocalMonodromyDatum ℓ H'} {α : H ≃ₜ* H'}
  {c : ℚ_[ℓ]ˣ} {φ : K →ₜ* H} [CompactSpace K]

namespace IsIso

/-- An isomorphism of local monodromy data carries admissible homomorphisms to admissible
homomorphisms. -/
theorem isAdmissible_comp (hα : IsIso D D' α c) (h : D.IsAdmissible φ) :
    D'.IsAdmissible ((α : H →ₜ* H').comp φ) where
  isOpen_residueRange := isOpen_residueRange_iff.2
    ⟨h.residueIndex, h.residueIndex_pos.ne',
      let ⟨k, hk⟩ := h.exists_coe_eq_frobClass_pow
      ⟨k, (hα.coe_apply_eq_frobClass_pow_iff (φ k) _).2 hk⟩⟩
  exists_tame_ne_one := by
    obtain ⟨σ, hσ, hne⟩ := h.exists_tame_ne_one
    have hσ' := (hα.map_mem_inertia_iff (φ σ)).2 hσ
    refine ⟨σ, hσ', fun h1 ↦ hne (Multiplicative.toAdd.injective ?_)⟩
    have h2 := hα.toAdd_tame_map (φ σ) hσ hσ'
    rw [show D'.tame ⟨α (φ σ), hσ'⟩ = 1 from h1, toAdd_one, eq_comm, mul_eq_zero] at h2
    exact h2.resolve_left c.ne_zero

/-- An isomorphism of local monodromy data preserves residue indices. -/
theorem residueIndex_isAdmissible_comp (hα : IsIso D D' α c) (h : D.IsAdmissible φ) :
    (hα.isAdmissible_comp h).residueIndex = h.residueIndex :=
  (hα.isAdmissible_comp h).residueIndex_eq_iff.2 fun n ↦
    ⟨fun ⟨k, hk⟩ ↦ (h.frobClass_pow_mem_residueRange_iff n).1
        ⟨k, (hα.coe_apply_eq_frobClass_pow_iff (φ k) n).1 hk⟩,
      fun hn ↦ let ⟨k, hk⟩ := (h.frobClass_pow_mem_residueRange_iff n).2 hn
        ⟨k, (hα.coe_apply_eq_frobClass_pow_iff (φ k) n).2 hk⟩⟩

/-- **Isomorphisms restrict.** An isomorphism `α : D → D'` with constant `c` makes the identity of
`K` an isomorphism from the restriction of `D` along `φ` to the restriction of `D'` along
`α ∘ φ`, with the same constant `c`. For the inclusion of a closed subgroup `H₁ ⊆ H`, this is the
isomorphism `D|_{H₁} → D'|_{α(H₁)}`. -/
theorem comap [IsTopologicalGroup K] [T2Space K] [TotallyDisconnectedSpace K]
    (hα : IsIso D D' α c) (h : D.IsAdmissible φ) :
    IsIso (D.comap φ h) (D'.comap ((α : H →ₜ* H').comp φ) (hα.isAdmissible_comp h))
      (ContinuousMulEquiv.refl K) c where
  map_mem_inertia_iff k := hα.map_mem_inertia_iff (φ k)
  map_mem_frobenius_iff k := by
    rw [ContinuousMulEquiv.refl_apply, mem_comap_frobenius, mem_comap_frobenius,
      hα.residueIndex_isAdmissible_comp h]
    exact hα.coe_apply_eq_frobClass_pow_iff (φ k) _
  q_eq := by rw [comap_q, comap_q, hα.residueIndex_isAdmissible_comp h, hα.q_eq]
  toAdd_tame_map k hk hk' := hα.toAdd_tame_map (φ k) hk hk'

end IsIso

end IsIso

end LocalMonodromyDatum

end TauCeti
