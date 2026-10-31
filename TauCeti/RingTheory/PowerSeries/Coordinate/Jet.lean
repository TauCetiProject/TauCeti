/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Jet groups of formal coordinates

For `N : ℕ`, two formal coordinates over a commutative ring `R` have the same `N`-jet when they
agree modulo `X ^ (N + 1)`, that is, when their coefficients agree through degree `N`. This
congruence is compatible with composition on both sides: `f (a) ≡ f (b)` whenever `a ≡ b`, and
`f (a) ≡ g (a)` whenever `f ≡ g`, modulo `X ^ (N + 1)`. Hence the coordinates congruent to the
identity `X` form a normal subgroup `jetKernel R N`, and the quotient is the group
`Jet R N` of `N`-jets, with multiplication given by truncated composition. For `N ≤ M`
truncation is a surjective homomorphism `Jet R M →* Jet R N`.

The full coordinate group is the inverse limit of its jet groups: a compatible family of jets
comes from a unique formal coordinate, whose degree-`n` coefficient is read off from the
`n`-jet. Giving each jet group the discrete topology and the coordinate group the topology
induced by all of its jets, two coordinates are close when they agree modulo a high power of
`X`. The comparison with the closed subgroup of compatible families in the product of the jet
groups is then an isomorphism of topological groups.

## Main definitions

* `TauCeti.FormalCoordinate.jetKernel R N`: the coordinates congruent to `X` modulo
  `X ^ (N + 1)`.
* `TauCeti.FormalCoordinate.Jet R N`: the group of `N`-jets of formal coordinates.
* `TauCeti.FormalCoordinate.jet N`: the `N`-jet of a coordinate, as a homomorphism.
* `TauCeti.FormalCoordinate.Jet.truncate`: truncation `Jet R M →* Jet R N` for `N ≤ M`.
* `TauCeti.FormalCoordinate.Jet.map f N`: base change of `N`-jets along `f : R →+* S`.
* `TauCeti.FormalCoordinate.jetLimit R`: the compatible families of jets, a closed subgroup of
  the product of the jet groups.
* `TauCeti.FormalCoordinate.jetLimitEquiv R`: the isomorphism of topological groups between the
  formal coordinates and the compatible families of jets.

## Main results

* `TauCeti.FormalCoordinate.jet_eq_jet_iff`: two coordinates have the same `N`-jet if and only
  if they agree modulo `X ^ (N + 1)`.
* `TauCeti.FormalCoordinate.tendsto_iff_X_pow_dvd`: convergence of coordinates is eventual
  agreement modulo each power of `X`.
* `TauCeti.FormalCoordinate.isClosed_jetLimit`: the compatible families form a closed subgroup.
* `TauCeti.FormalCoordinate.Jet.map_jet`, `TauCeti.FormalCoordinate.Jet.truncate_map`: passing to
  jets and truncating jets are natural in the coefficients.
* `TauCeti.FormalCoordinate.continuous_map`: base change of formal coordinates is continuous.
-/

public section

open PowerSeries Filter Topology

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Composing on the left with a fixed coordinate preserves congruence modulo `X ^ n`. -/
theorem X_pow_dvd_mul_sub_mul_left (χ : FormalCoordinate R) {φ ψ : FormalCoordinate R}
    (h : X ^ n ∣ φ.toPowerSeries - ψ.toPowerSeries) :
    X ^ n ∣ (χ * φ).toPowerSeries - (χ * ψ).toPowerSeries :=
  X_pow_dvd_subst_sub_subst φ.constantCoeff_toPowerSeries ψ.constantCoeff_toPowerSeries h _

/-- Composing on the right with a fixed coordinate preserves congruence modulo `X ^ n`. -/
theorem X_pow_dvd_mul_sub_mul_right (χ : FormalCoordinate R) {φ ψ : FormalCoordinate R}
    (h : X ^ n ∣ φ.toPowerSeries - ψ.toPowerSeries) :
    X ^ n ∣ (φ * χ).toPowerSeries - (ψ * χ).toPowerSeries := by
  simpa [subst_sub χ.hasSubst] using X_pow_dvd_subst χ.constantCoeff_toPowerSeries h

variable (R) in
/-- The coordinates congruent to the identity `X` modulo `X ^ (N + 1)`: the kernel of passing
to `N`-jets. -/
def jetKernel (N : ℕ) : Subgroup (FormalCoordinate R) where
  carrier := {φ | X ^ (N + 1) ∣ φ.toPowerSeries - X}
  one_mem' := by simp
  mul_mem' {φ ψ} hφ hψ := by
    -- `φ (ψ) ≡ φ (X) = φ ≡ X`
    have h := X_pow_dvd_mul_sub_mul_left φ (ψ := 1) hψ
    rw [mul_one] at h
    simpa using dvd_add h hφ
  inv_mem' {φ} hφ := by
    -- `φ⁻¹ = X (φ⁻¹) ≡ φ (φ⁻¹) = X`
    have h := X_pow_dvd_mul_sub_mul_right φ⁻¹ (φ := 1) (dvd_sub_comm.mp hφ)
    simpa using h

theorem mem_jetKernel {N : ℕ} {φ : FormalCoordinate R} :
    φ ∈ jetKernel R N ↔ X ^ (N + 1) ∣ φ.toPowerSeries - X :=
  Iff.rfl

/-- Agreement with `X` modulo a higher power of `X` implies agreement modulo a lower one. -/
theorem jetKernel_mono {N M : ℕ} (h : N ≤ M) : jetKernel R M ≤ jetKernel R N :=
  fun _ hφ ↦ (pow_dvd_pow X (Nat.succ_le_succ h)).trans hφ

instance (N : ℕ) : (jetKernel R N).Normal where
  conj_mem φ hφ χ := by
    have h := X_pow_dvd_mul_sub_mul_right χ⁻¹
      (X_pow_dvd_mul_sub_mul_left χ (ψ := 1) hφ)
    rwa [mul_one, mul_inv_cancel, toPowerSeries_one] at h

variable (R) in
/-- The group of `N`-jets of formal coordinates: formal coordinates modulo `X ^ (N + 1)`, with
multiplication given by truncated composition. -/
def Jet (N : ℕ) : Type _ :=
  FormalCoordinate R ⧸ jetKernel R N

namespace Jet

noncomputable instance (N : ℕ) : Group (Jet R N) :=
  inferInstanceAs (Group (FormalCoordinate R ⧸ jetKernel R N))

/-- Jet groups carry the discrete topology. -/
instance (N : ℕ) : TopologicalSpace (Jet R N) := ⊥

instance (N : ℕ) : DiscreteTopology (Jet R N) := ⟨rfl⟩

end Jet

/-- The `N`-jet of a formal coordinate: its class modulo `X ^ (N + 1)`. -/
noncomputable def jet (N : ℕ) : FormalCoordinate R →* Jet R N :=
  QuotientGroup.mk' (jetKernel R N)

theorem jet_surjective (N : ℕ) : Function.Surjective (jet (R := R) N) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem ker_jet (N : ℕ) : (jet (R := R) N).ker = jetKernel R N :=
  QuotientGroup.ker_mk' _

/-- Two formal coordinates have the same `N`-jet exactly when they agree modulo `X ^ (N + 1)`. -/
theorem jet_eq_jet_iff {N : ℕ} {φ ψ : FormalCoordinate R} :
    jet N φ = jet N ψ ↔ X ^ (N + 1) ∣ φ.toPowerSeries - ψ.toPowerSeries := by
  rw [MonoidHom.eq_iff, ker_jet, mem_jetKernel]
  constructor
  · intro h
    simpa using X_pow_dvd_mul_sub_mul_left ψ (φ := ψ⁻¹ * φ) (ψ := 1) h
  · intro h
    simpa using X_pow_dvd_mul_sub_mul_left ψ⁻¹ h

/-- Two formal coordinates have the same `N`-jet exactly when their coefficients agree through
degree `N`. -/
theorem jet_eq_jet_iff_coeff {N : ℕ} {φ ψ : FormalCoordinate R} :
    jet N φ = jet N ψ ↔ ∀ m ≤ N, coeff m φ.toPowerSeries = coeff m ψ.toPowerSeries := by
  simp [jet_eq_jet_iff, X_pow_dvd_iff, sub_eq_zero]

/-- A formal coordinate has trivial `N`-jet exactly when it agrees with `X` modulo
`X ^ (N + 1)`. -/
theorem jet_eq_one_iff {N : ℕ} {φ : FormalCoordinate R} :
    jet N φ = 1 ↔ X ^ (N + 1) ∣ φ.toPowerSeries - X := by
  rw [← MonoidHom.mem_ker, ker_jet, mem_jetKernel]

namespace Jet

/-- For `N ≤ M`, the truncation of `M`-jets to `N`-jets. -/
noncomputable def truncate {N M : ℕ} (h : N ≤ M) : Jet R M →* Jet R N :=
  QuotientGroup.map _ _ (.id _) (jetKernel_mono h)

@[simp]
theorem truncate_jet {N M : ℕ} (h : N ≤ M) (φ : FormalCoordinate R) :
    truncate h (jet M φ) = jet N φ :=
  (rfl)

theorem truncate_comp_jet {N M : ℕ} (h : N ≤ M) :
    (truncate h).comp (jet M) = jet (R := R) N :=
  MonoidHom.ext (truncate_jet h)

theorem truncate_surjective {N M : ℕ} (h : N ≤ M) :
    Function.Surjective (truncate (R := R) h) := fun x ↦ by
  obtain ⟨φ, rfl⟩ := jet_surjective N x
  exact ⟨jet M φ, truncate_jet h φ⟩

@[simp]
theorem truncate_refl {N : ℕ} (x : Jet R N) : truncate le_rfl x = x := by
  obtain ⟨φ, rfl⟩ := jet_surjective N x
  exact truncate_jet le_rfl φ

@[simp]
theorem truncate_truncate {N M L : ℕ} (h₁ : N ≤ M) (h₂ : M ≤ L) (x : Jet R L) :
    truncate h₁ (truncate h₂ x) = truncate (h₁.trans h₂) x := by
  obtain ⟨φ, rfl⟩ := jet_surjective L x
  simp

end Jet

/-! ### Base change of jets -/

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

/-- Base change of coefficients preserves agreement with `X` modulo `X ^ (N + 1)`. -/
theorem jetKernel_le_comap_map (N : ℕ) : jetKernel R N ≤ (jetKernel S N).comap (map f) := by
  intro φ hφ
  rw [Subgroup.mem_comap, mem_jetKernel, toPowerSeries_map, ← PowerSeries.map_X f,
    ← map_sub, ← map_pow]
  exact _root_.map_dvd (PowerSeries.map f) hφ

namespace Jet

/-- Base change of `N`-jets along a ring homomorphism `f : R →+* S`, induced by base change of
formal coordinates. -/
noncomputable def map (N : ℕ) : Jet R N →* Jet S N :=
  QuotientGroup.map _ _ (FormalCoordinate.map f) (jetKernel_le_comap_map f N)

@[simp]
theorem map_jet (N : ℕ) (φ : FormalCoordinate R) :
    Jet.map f N (jet N φ) = jet N (FormalCoordinate.map f φ) :=
  (rfl)

theorem map_comp_jet (N : ℕ) :
    (Jet.map f N).comp (jet N) = (jet N).comp (FormalCoordinate.map f) :=
  MonoidHom.ext (map_jet f N)

/-- Jet truncation is natural in the coefficients. -/
@[simp]
theorem truncate_map {N M : ℕ} (h : N ≤ M) (x : Jet R M) :
    truncate h (Jet.map f M x) = Jet.map f N (truncate h x) := by
  obtain ⟨φ, rfl⟩ := jet_surjective M x
  simp

theorem truncate_comp_map {N M : ℕ} (h : N ≤ M) :
    (truncate h).comp (Jet.map f M) = (Jet.map f N).comp (truncate h) :=
  MonoidHom.ext (truncate_map f h)

@[simp]
theorem map_id (N : ℕ) : Jet.map (RingHom.id R) N = MonoidHom.id (Jet R N) :=
  MonoidHom.ext fun x ↦ by
    obtain ⟨φ, rfl⟩ := jet_surjective N x
    simp

@[simp]
theorem map_map {T : Type*} [CommRing T] (g : S →+* T) (N : ℕ) (x : Jet R N) :
    Jet.map g N (Jet.map f N x) = Jet.map (g.comp f) N x := by
  obtain ⟨φ, rfl⟩ := jet_surjective N x
  simp [FormalCoordinate.map_comp]

/-- Base change of jets along an injective ring homomorphism is injective. -/
theorem map_injective {f : R →+* S} (hf : Function.Injective f) (N : ℕ) :
    Function.Injective (Jet.map f N) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx ↦ ?_
  obtain ⟨φ, rfl⟩ := jet_surjective N x
  rw [map_jet, jet_eq_one_iff, X_pow_dvd_iff] at hx
  rw [jet_eq_one_iff, X_pow_dvd_iff]
  intro m hm
  apply hf
  rw [map_zero, ← coeff_map, map_sub, PowerSeries.map_X, ← toPowerSeries_map]
  exact hx m hm

end Jet

end map

/-! ### The inverse limit of the jet groups -/

variable (R) in
/-- The compatible families of jets: the inverse limit of the jet groups along truncation, as a
subgroup of their product. -/
noncomputable def jetLimit : Subgroup (∀ N, Jet R N) where
  carrier := {x | ∀ ⦃N M : ℕ⦄ (h : N ≤ M), Jet.truncate h (x M) = x N}
  mul_mem' hx hy N M h := by simp [hx h, hy h]
  one_mem' _ _ _ := map_one _
  inv_mem' hx N M h := by simp [hx h]

theorem mem_jetLimit {x : ∀ N, Jet R N} :
    x ∈ jetLimit R ↔ ∀ ⦃N M : ℕ⦄ (h : N ≤ M), Jet.truncate h (x M) = x N :=
  Iff.rfl

variable (R) in
/-- The family of all jets of a formal coordinate. -/
noncomputable def jets : FormalCoordinate R →* ∀ N, Jet R N :=
  MonoidHom.pi jet

@[simp]
theorem jets_apply (φ : FormalCoordinate R) (N : ℕ) : jets R φ N = jet N φ :=
  (rfl)

/-- A formal coordinate is determined by its jets. -/
theorem jets_injective : Function.Injective (jets R) := fun _ _ h ↦
  FormalCoordinate.ext <| PowerSeries.ext fun m ↦
    jet_eq_jet_iff_coeff.mp (congr_fun h m) m le_rfl

/-- Every compatible family of jets is the family of jets of a formal coordinate. -/
theorem range_jets : (jets R).range = jetLimit R := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨φ, rfl⟩ N M h
    simp
  choose φ hφ using fun N ↦ jet_surjective N (x N)
  -- The degree-`m` coefficient of the limit is that of any representative of the `m`-jet.
  have hcoeff {m N : ℕ} (h : m ≤ N) :
      coeff m (φ m).toPowerSeries = coeff m (φ N).toPowerSeries := by
    refine jet_eq_jet_iff_coeff.mp ?_ m le_rfl
    rw [hφ, ← hx h, ← hφ, Jet.truncate_jet]
  let ψ : FormalCoordinate R :=
    { toPowerSeries := PowerSeries.mk fun m ↦ coeff m (φ m).toPowerSeries
      constantCoeff_toPowerSeries := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, coeff_zero_eq_constantCoeff_apply,
          constantCoeff_toPowerSeries]
      isUnit_coeff_one := by simpa using (φ 1).isUnit_coeff_one }
  refine ⟨ψ, funext fun N ↦ ?_⟩
  rw [jets_apply, ← hφ, jet_eq_jet_iff_coeff]
  intro m hm
  simpa [ψ] using hcoeff hm

/-! ### The topology of agreement modulo powers of `X` -/

/-- Formal coordinates carry the topology induced by all of their jets, each jet group being
discrete: coordinates are close when they agree modulo a high power of `X`. -/
noncomputable instance : TopologicalSpace (FormalCoordinate R) :=
  .induced (jets R) inferInstance

theorem isInducing_jets : IsInducing (jets R) :=
  ⟨rfl⟩

theorem isEmbedding_jets : IsEmbedding (jets R) :=
  ⟨isInducing_jets, jets_injective⟩

instance : IsTopologicalGroup (FormalCoordinate R) :=
  isTopologicalGroup_induced (jets R)

instance : T2Space (FormalCoordinate R) :=
  isEmbedding_jets.t2Space

theorem continuous_jet (N : ℕ) : Continuous (jet (R := R) N) :=
  (continuous_apply N).comp isInducing_jets.continuous

/-- Base change of formal coordinates is continuous for the topologies of agreement modulo
powers of `X`. -/
theorem continuous_map {S : Type*} [CommRing S] (f : R →+* S) : Continuous (map f) :=
  isInducing_jets.continuous_iff.mpr <| continuous_pi fun N ↦ by
    simpa [Function.comp_def] using
      (continuous_of_discreteTopology (f := Jet.map f N)).comp (continuous_jet N)

/-- The coordinates congruent to `X` modulo `X ^ (N + 1)` form an open subgroup. -/
theorem isOpen_jetKernel (N : ℕ) : IsOpen (jetKernel R N : Set (FormalCoordinate R)) := by
  rw [← ker_jet]
  exact (isOpen_discrete {1}).preimage (continuous_jet N)

/-- A family of formal coordinates converges exactly when it eventually agrees with the limit
modulo each power of `X`. -/
theorem tendsto_iff_X_pow_dvd {ι : Type*} {l : Filter ι} (f : ι → FormalCoordinate R)
    (φ : FormalCoordinate R) :
    Tendsto f l (𝓝 φ) ↔
      ∀ N : ℕ, ∀ᶠ i in l, X ^ (N + 1) ∣ (f i).toPowerSeries - φ.toPowerSeries := by
  simp only [isInducing_jets.tendsto_nhds_iff, tendsto_pi_nhds, nhds_discrete, tendsto_pure,
    Function.comp_apply, jets_apply, jet_eq_jet_iff]

/-- The congruence classes modulo powers of `X` form a neighbourhood basis. -/
theorem hasBasis_nhds (φ : FormalCoordinate R) :
    (𝓝 φ).HasBasis (fun _ : ℕ ↦ True)
      (fun N ↦ {ψ | X ^ (N + 1) ∣ ψ.toPowerSeries - φ.toPowerSeries}) := by
  have heq : 𝓝 φ = ⨅ N : ℕ, 𝓟 {ψ | X ^ (N + 1) ∣ ψ.toPowerSeries - φ.toPowerSeries} := by
    apply le_antisymm
    · refine le_iInf fun N ↦ le_principal_iff.mpr ?_
      exact (tendsto_iff_X_pow_dvd _ φ).mp tendsto_id N
    · exact (tendsto_iff_X_pow_dvd id φ).mpr fun N ↦ mem_iInf_of_mem N (mem_principal_self _)
  rw [heq]
  refine hasBasis_iInf_principal fun N M ↦ ⟨max N M, ?_, ?_⟩ <;> intro ψ hψ <;>
    refine (pow_dvd_pow X (Nat.succ_le_succ ?_)).trans hψ
  exacts [le_max_left N M, le_max_right N M]

/-- The compatible families of jets form a closed subgroup of the product of the jet groups. -/
theorem isClosed_jetLimit : IsClosed (jetLimit R : Set (∀ N, Jet R N)) := by
  simp only [jetLimit, Subgroup.coe_set_mk, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
    Set.ofPred_forall]
  exact isClosed_iInter fun N ↦ isClosed_iInter fun M ↦ isClosed_iInter fun h ↦
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply M)) (continuous_apply N)

variable (R) in
/-- The formal coordinates are the inverse limit of their jet groups: passing to all jets is an
isomorphism of topological groups onto the compatible families of jets. -/
noncomputable def jetLimitEquiv : FormalCoordinate R ≃ₜ* jetLimit R :=
  let e : FormalCoordinate R ≃* jetLimit R :=
    .ofBijective ((jets R).codRestrict _ fun φ ↦ range_jets (R := R) ▸ ⟨φ, rfl⟩)
      ⟨fun _ _ h ↦ jets_injective (congr_arg Subtype.val h), fun x ↦ by
        obtain ⟨φ, hφ⟩ := (range_jets (R := R)).ge x.2
        exact ⟨φ, Subtype.ext hφ⟩⟩
  { e with
    continuous_toFun := isInducing_jets.continuous.subtype_mk _
    continuous_invFun := by
      refine isInducing_jets.continuous_iff.mpr ?_
      convert continuous_subtype_val using 1
      exact funext fun x ↦ congr_arg Subtype.val (e.apply_symm_apply x) }

@[simp]
theorem jetLimitEquiv_apply_coe (φ : FormalCoordinate R) (N : ℕ) :
    (jetLimitEquiv R φ : ∀ N, Jet R N) N = jet N φ :=
  (rfl)

@[simp]
theorem jets_jetLimitEquiv_symm_apply (x : jetLimit R) :
    jets R ((jetLimitEquiv R).symm x) = x :=
  congr_arg Subtype.val ((jetLimitEquiv R).apply_symm_apply x)

end TauCeti.FormalCoordinate
