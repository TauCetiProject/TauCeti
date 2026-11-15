/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.RepresentationTheory.Continuous.InvariantComplement
import Mathlib.Algebra.Order.Chebyshev

/-!
# Spectral gap of a representation

A representation has spectral gap when a finite sum of squared orbit displacements controls
squared norms on the orthogonal complement of its invariant vectors. The fixed subspace is
removed: in particular a trivial representation has spectral gap.

For a unitary monoid representation the orthogonal complement carries a unitary representation,
`IsUnitary.invariantsOrthogonal`. Spectral gap is equivalent to the absence of almost invariant
vectors in this representation. Every representation of a finite group — and more generally every
group representation with finite image — has spectral gap. Spectral gap is invariant under linear
isometric equivalences and surjective group or monoid pullbacks, passes to invariant subspaces
admitting an orthogonal projection, and for a unitary group representation may be tested on any
finite generating set.
Neither completeness nor a topology on the acting group is needed here.

## Main definitions and results

* `ContRepresentation.HasSpectralGap`: finite quadratic control of `ρ.invariantsᗮ`.
* `ContRepresentation.hasSpectralGap_iff_not_hasAlmostInvariantVectors`: equivalence with the
  absence of almost invariant vectors in `hρ.invariantsOrthogonal`.
* `ContRepresentation.hasSpectralGap_restrict_iff_of_surjective` and
  `ContRepresentation.hasSpectralGap_iff_of_linearIsometryEquiv`: invariance under surjective
  pullbacks and isometric equivalences.
* `ContRepresentation.hasSpectralGap_of_finite` and
  `ContRepresentation.hasSpectralGap_of_finite_quotient`: representations of finite groups, or
  trivial on a finite-index normal subgroup, have spectral gap.
* `ContRepresentation.HasSpectralGap.subrepresentation`: inheritance by an invariant subspace
  admitting an orthogonal projection.
* `ContRepresentation.IsUnitary.hasSpectralGap_iff_exists_of_closure_eq_top`: for a unitary group
  representation and a finite generating set `S`, spectral gap is equivalent to a spectral-gap
  inequality over `S` itself.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Definition 15.1.1 and
  Corollary 15.1.4.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

section Monoid

variable [Monoid G]

/-- A representation has spectral gap if finitely many squared orbit displacements control the
squared norm of every vector orthogonal to the invariant subspace. -/
def HasSpectralGap (ρ : ContRepresentation 𝕜 G V) : Prop :=
  ∃ (F : Finset G) (C : ℝ), 0 < C ∧
    ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2

/-- The finite quadratic inequality characterizing spectral gap. -/
theorem hasSpectralGap_def (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap ↔ ∃ (F : Finset G) (C : ℝ), 0 < C ∧
      ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
  Iff.rfl

/-- Every representation on a subsingleton space has spectral gap. -/
theorem hasSpectralGap_of_subsingleton [Subsingleton V] (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap :=
  ⟨∅, 1, zero_lt_one, fun v _ ↦ by simp [Subsingleton.elim v 0]⟩

/-- Restriction along a surjective monoid homomorphism leaves the invariant subspace unchanged. -/
theorem invariants_restrict_of_surjective {H : Type*} [Monoid H] (ρ : ContRepresentation 𝕜 G V)
    {f : H →* G} (hf : Function.Surjective f) :
    (ρ.restrict f).invariants = ρ.invariants := by
  ext v
  simp only [mem_invariants, restrict_apply_apply]
  exact ⟨fun h g ↦ by obtain ⟨x, rfl⟩ := hf g; exact h x, fun h x ↦ h (f x)⟩

/-- Restriction along a surjective monoid homomorphism preserves and reflects spectral gap. -/
theorem hasSpectralGap_restrict_iff_of_surjective {H : Type*} [Monoid H]
    (ρ : ContRepresentation 𝕜 G V) {f : H →* G} (hf : Function.Surjective f) :
    (ρ.restrict f).HasSpectralGap ↔ ρ.HasSpectralGap := by
  classical
  have hinv : (ρ.restrict f).invariants = ρ.invariants := ρ.invariants_restrict_of_surjective hf
  constructor
  · rintro ⟨F, C, hC, hF⟩
    refine ⟨F.image f, C * (F.card + 1), by positivity, fun v hv ↦ ?_⟩
    have hv' : v ∈ (ρ.restrict f).invariantsᗮ := hinv ▸ hv
    have hsum : ∑ h ∈ F, ‖ρ (f h) v - v‖ ^ 2 ≤
        (F.card + 1) * ∑ g ∈ F.image f, ‖ρ g v - v‖ ^ 2 := by
      calc ∑ h ∈ F, ‖ρ (f h) v - v‖ ^ 2
          ≤ ∑ _h ∈ F, ∑ g ∈ F.image f, ‖ρ g v - v‖ ^ 2 :=
            Finset.sum_le_sum fun h hh ↦
              Finset.single_le_sum (f := fun g ↦ ‖ρ g v - v‖ ^ 2)
                (fun _ _ ↦ sq_nonneg _) (Finset.mem_image_of_mem f hh)
        _ = F.card * ∑ g ∈ F.image f, ‖ρ g v - v‖ ^ 2 := by simp
        _ ≤ (F.card + 1) * ∑ g ∈ F.image f, ‖ρ g v - v‖ ^ 2 := by
            gcongr
            linarith
    calc ‖v‖ ^ 2 ≤ C * ∑ h ∈ F, ‖ρ (f h) v - v‖ ^ 2 := by simpa using hF v hv'
      _ ≤ C * ((F.card + 1) * ∑ g ∈ F.image f, ‖ρ g v - v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum hC.le
      _ = C * (F.card + 1) * ∑ g ∈ F.image f, ‖ρ g v - v‖ ^ 2 := (mul_assoc _ _ _).symm
  · rintro ⟨F, C, hC, hF⟩
    choose s hs using hf
    have hsinj : Function.Injective s := Function.RightInverse.injective hs
    refine ⟨F.image s, C, hC, fun v hv ↦ ?_⟩
    have hv' : v ∈ ρ.invariantsᗮ := hinv ▸ hv
    have hsum : ∑ h ∈ F.image s, ‖(ρ.restrict f) h v - v‖ ^ 2 =
        ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
      rw [Finset.sum_image fun _ _ _ _ h ↦ hsinj h]
      exact Finset.sum_congr rfl fun g _ ↦ by simp [hs g]
    rw [hsum]
    exact hF v hv'

/-- Linear isometric equivalence of representations preserves spectral gap. -/
theorem hasSpectralGap_iff_of_linearIsometryEquiv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] {ρ : ContRepresentation 𝕜 G V} {σ : ContRepresentation 𝕜 G W}
    (e : V ≃ₗᵢ[𝕜] W) (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    ρ.HasSpectralGap ↔ σ.HasSpectralGap := by
  have hinv (v : V) : e v ∈ σ.invariants ↔ v ∈ ρ.invariants := by
    simp only [mem_invariants, ← he, e.injective.eq_iff]
  have horth (v : V) : e v ∈ σ.invariantsᗮ ↔ v ∈ ρ.invariantsᗮ := by
    simp only [Submodule.mem_orthogonal]
    refine ⟨fun h u hu ↦ ?_, fun h w hw ↦ ?_⟩
    · rw [← e.inner_map_map]
      exact h (e u) ((hinv u).2 hu)
    · obtain ⟨u, rfl⟩ := e.surjective w
      rw [e.inner_map_map]
      exact h u ((hinv u).1 hw)
  have hdisp (g : G) (v : V) : ‖σ g (e v) - e v‖ = ‖ρ g v - v‖ := by
    rw [← he g v, ← map_sub, e.norm_map]
  constructor
  · rintro ⟨F, C, hC, hF⟩
    refine ⟨F, C, hC, fun w hw ↦ ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [e.norm_map, hdisp] using hF v ((horth v).1 hw)
  · rintro ⟨F, C, hC, hF⟩
    exact ⟨F, C, hC, fun v hv ↦ by
      simpa only [e.norm_map, hdisp] using hF (e v) ((horth v).2 hv)⟩

/-- Spectral gap means that the representation on the orthogonal complement of the invariant
vectors has no almost invariant vectors. Equivalently, the trivial representation is not weakly
contained in that complement. -/
theorem hasSpectralGap_iff_not_hasAlmostInvariantVectors
    (ρ : ContRepresentation 𝕜 G V) (hρ : ρ.IsUnitary) :
    ρ.HasSpectralGap ↔ ¬hρ.invariantsOrthogonal.HasAlmostInvariantVectors := by
  rw [not_hasAlmostInvariantVectors_iff]
  constructor
  · rintro ⟨F, C, hC, hF⟩
    refine ⟨F, C⁻¹, inv_pos.mpr hC, fun v ↦ ?_⟩
    have hv := hF v v.property
    calc
      C⁻¹ * ‖v‖ ^ 2 ≤ C⁻¹ * (C * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hC.le)
      _ = ∑ g ∈ F, ‖hρ.invariantsOrthogonal g v - v‖ ^ 2 := by
        simp [← Submodule.norm_coe, hC.ne']
  · rintro ⟨F, c, hc, hF⟩
    refine ⟨F, c⁻¹, inv_pos.mpr hc, fun v hv ↦ ?_⟩
    have hbound := hF ⟨v, hv⟩
    have hsum : (∑ g ∈ F, ‖hρ.invariantsOrthogonal g ⟨v, hv⟩ - ⟨v, hv⟩‖ ^ 2) =
        ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := by
      simp [← Submodule.norm_coe]
    rw [hsum] at hbound
    calc
      ‖v‖ ^ 2 = c⁻¹ * (c * ‖v‖ ^ 2) := by simp [hc.ne']
      _ ≤ c⁻¹ * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hc.le)

end Monoid

section Group

variable [Group G]

/-- Every representation of a finite group has spectral gap, without unitarity or
completeness assumptions. -/
theorem hasSpectralGap_of_finite [Finite G] (ρ : ContRepresentation 𝕜 G V) :
    ρ.HasSpectralGap := by
  classical
  let := Fintype.ofFinite G
  refine ⟨Finset.univ, 1, zero_lt_one, fun v hv ↦ ?_⟩
  rw [one_mul]
  by_contra! hbound
  have hmove (g : G) : ‖ρ g v - v‖ < ‖v‖ := by
    have hsingle := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset G)) ↦ sq_nonneg ‖ρ i v - v‖)
      (Finset.mem_univ g)
    nlinarith [norm_nonneg (ρ g v - v), norm_nonneg v]
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt hmove
  have horth := (ρ.invariants.mem_orthogonal v).mp hv w hw
  have hpyth := norm_sub_sq (𝕜 := 𝕜) w v
  rw [horth, map_zero, mul_zero, sub_zero] at hpyth
  nlinarith [sq_nonneg ‖w‖, norm_nonneg (w - v), norm_nonneg v]

/-- Any group representation that is trivial on a normal subgroup `N` with finite quotient `G ⧸ N`
has spectral gap: it factors through `G ⧸ N`. -/
theorem hasSpectralGap_of_finite_quotient (ρ : ContRepresentation 𝕜 G V)
    (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (hN : ∀ n ∈ N, ρ n = 1) :
    ρ.HasSpectralGap := by
  let π : ContRepresentation 𝕜 (G ⧸ N) V :=
    .ofMonoidHom (QuotientGroup.lift N ρ.toMonoidHom hN)
  have hres : π.restrict (QuotientGroup.mk' N) = ρ :=
    DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl
  rw [← hres, π.hasSpectralGap_restrict_iff_of_surjective (QuotientGroup.mk'_surjective N)]
  exact hasSpectralGap_of_finite π

/-- **Subrepresentation inheritance.** If a unitary group representation has spectral gap, so does
its restriction to any `G`-invariant subspace admitting an orthogonal projection, with the same
Kazhdan pair: the orthogonal projection commutes with `G`, sending ambient invariants into
subspace invariants. -/
theorem HasSpectralGap.subrepresentation {ρ : ContRepresentation 𝕜 G V}
    (hgap : ρ.HasSpectralGap) (hρ : ρ.IsUnitary) (W : Submodule 𝕜 V)
    [W.HasOrthogonalProjection] (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) :
    (ρ.subrepresentation W hW).HasSpectralGap := by
  obtain ⟨F, C, hC, hF⟩ := hgap
  refine ⟨F, C, hC, fun x hx ↦ ?_⟩
  have hx' : (x : V) ∈ ρ.invariantsᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hproj_inv : (⟨W.starProjection u, W.starProjection_apply_mem u⟩ : W) ∈
        (ρ.subrepresentation W hW).invariants := by
      rw [mem_invariants_subrepresentation]
      intro g
      rw [← hρ.starProjection_apply_comm hW g u, hu g]
    have h1 : ⟪(W.starProjection u : V), (x : V)⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx ⟨W.starProjection u, W.starProjection_apply_mem u⟩
        hproj_inv
    have h2 : ⟪u - W.starProjection u, (x : V)⟫_𝕜 = 0 :=
      inner_eq_zero_symm.mp
        ((Submodule.mem_orthogonal W _).mp (W.sub_starProjection_mem_orthogonal u) x x.2)
    calc ⟪u, (x : V)⟫_𝕜
        = ⟪(W.starProjection u : V) + (u - W.starProjection u), (x : V)⟫_𝕜 := by
            rw [add_sub_cancel]
      _ = ⟪(W.starProjection u : V), (x : V)⟫_𝕜 + ⟪u - W.starProjection u, (x : V)⟫_𝕜 :=
          inner_add_left _ _ _
      _ = 0 := by rw [h1, h2, add_zero]
  simpa only [← Submodule.norm_coe, Submodule.coe_sub, coe_subrepresentation_apply] using
    hF (x : V) hx'

/-- **1-cocycle word-length bound.** For a unitary group representation, the displacement by any
element in the subgroup generated by a finite set `S` is uniformly bounded by a multiple of the
sum of displacements over `S`. -/
theorem IsUnitary.exists_norm_sub_le_sum_of_mem_closure {ρ : ContRepresentation 𝕜 G V}
    (hρ : ρ.IsUnitary) (S : Finset G) {g : G} (hg : g ∈ Subgroup.closure (S : Set G)) :
    ∃ N : ℕ, ∀ v : V, ‖ρ g v - v‖ ≤ N * ∑ s ∈ S, ‖ρ s v - v‖ := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    refine ⟨1, fun v ↦ ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Finset.single_le_sum (f := fun t ↦ ‖ρ t v - v‖) (fun _ _ ↦ norm_nonneg _) hs
  | one =>
    exact ⟨0, fun v ↦ by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨Nx, hNx⟩ := ihx
    obtain ⟨Ny, hNy⟩ := ihy
    refine ⟨Nx + Ny, fun v ↦ ?_⟩
    have hdecomp : ρ (x * y) v - v = ρ x (ρ y v - v) + (ρ x v - v) := by
      rw [map_mul, mul_apply_eq_comp, map_sub, sub_add_sub_cancel]
    calc ‖ρ (x * y) v - v‖
        = ‖ρ x (ρ y v - v) + (ρ x v - v)‖ := by rw [hdecomp]
      _ ≤ ‖ρ x (ρ y v - v)‖ + ‖ρ x v - v‖ := norm_add_le _ _
      _ = ‖ρ y v - v‖ + ‖ρ x v - v‖ := by rw [hρ.norm_map]
      _ ≤ Ny * ∑ s ∈ S, ‖ρ s v - v‖ + Nx * ∑ s ∈ S, ‖ρ s v - v‖ :=
          add_le_add (hNy v) (hNx v)
      _ = (Nx + Ny : ℕ) * ∑ s ∈ S, ‖ρ s v - v‖ := by push_cast; ring
  | inv x _ ihx =>
    obtain ⟨Nx, hNx⟩ := ihx
    refine ⟨Nx, fun v ↦ ?_⟩
    have hinv : ρ x⁻¹ (ρ x v - v) = v - ρ x⁻¹ v := by
      rw [map_sub, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    calc ‖ρ x⁻¹ v - v‖
        = ‖v - ρ x⁻¹ v‖ := norm_sub_rev _ _
      _ = ‖ρ x⁻¹ (ρ x v - v)‖ := by rw [hinv]
      _ = ‖ρ x v - v‖ := hρ.norm_map _ _
      _ ≤ Nx * ∑ s ∈ S, ‖ρ s v - v‖ := hNx v

/-- Squared form of `IsUnitary.exists_norm_sub_le_sum_of_mem_closure`. -/
theorem IsUnitary.exists_norm_sub_sq_le_sum_of_mem_closure {ρ : ContRepresentation 𝕜 G V}
    (hρ : ρ.IsUnitary) (S : Finset G) {g : G} (hg : g ∈ Subgroup.closure (S : Set G)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V, ‖ρ g v - v‖ ^ 2 ≤ C * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 := by
  obtain ⟨N, hN⟩ := hρ.exists_norm_sub_le_sum_of_mem_closure S hg
  refine ⟨(N : ℝ) ^ 2 * S.card, by positivity, fun v ↦ ?_⟩
  calc ‖ρ g v - v‖ ^ 2
      ≤ ((N : ℝ) * ∑ s ∈ S, ‖ρ s v - v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hN v) 2
    _ = (N : ℝ) ^ 2 * (∑ s ∈ S, ‖ρ s v - v‖) ^ 2 := mul_pow _ _ 2
    _ ≤ (N : ℝ) ^ 2 * (S.card * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left sq_sum_le_card_mul_sum_sq (sq_nonneg _)
    _ = (N : ℝ) ^ 2 * S.card * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 := (mul_assoc _ _ _).symm

/-- If a unitary group representation has spectral gap and `S` is a finite generating set of `G`,
then `S` itself witnesses the spectral-gap inequality. -/
theorem HasSpectralGap.exists_of_closure_eq_top {ρ : ContRepresentation 𝕜 G V}
    (hgap : ρ.HasSpectralGap) (hρ : ρ.IsUnitary) {S : Finset G}
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 := by
  obtain ⟨F, C₀, hC₀, hF⟩ := hgap
  choose K hK0 hK using fun g : G ↦
    hρ.exists_norm_sub_sq_le_sum_of_mem_closure S (hS.ge (Subgroup.mem_top g))
  have hsumK : 0 ≤ ∑ g ∈ F, K g := Finset.sum_nonneg fun g _ ↦ hK0 g
  refine ⟨C₀ * (∑ g ∈ F, K g + 1), by positivity, fun v hv ↦ ?_⟩
  have hsum : ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 ≤
      (∑ g ∈ F, K g + 1) * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 := by
    calc ∑ g ∈ F, ‖ρ g v - v‖ ^ 2
        ≤ ∑ g ∈ F, K g * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 :=
          Finset.sum_le_sum fun g _ ↦ hK g v
      _ = (∑ g ∈ F, K g) * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ g ∈ F, K g + 1) * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith)
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  calc ‖v‖ ^ 2
      ≤ C₀ * ∑ g ∈ F, ‖ρ g v - v‖ ^ 2 := hF v hv
    _ ≤ C₀ * ((∑ g ∈ F, K g + 1) * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hC₀.le
    _ = C₀ * (∑ g ∈ F, K g + 1) * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 := (mul_assoc _ _ _).symm

/-- **Generating-set characterization of spectral gap.** For a unitary representation of a group
generated by a finite set `S`, spectral gap is equivalent to a spectral-gap inequality summed
over `S` alone. -/
theorem IsUnitary.hasSpectralGap_iff_exists_of_closure_eq_top {ρ : ContRepresentation 𝕜 G V}
    (hρ : ρ.IsUnitary) {S : Finset G} (hS : Subgroup.closure (S : Set G) = ⊤) :
    ρ.HasSpectralGap ↔
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ ρ.invariantsᗮ, ‖v‖ ^ 2 ≤ C * ∑ s ∈ S, ‖ρ s v - v‖ ^ 2 :=
  ⟨fun hgap ↦ hgap.exists_of_closure_eq_top hρ hS, fun ⟨C, hC, h⟩ ↦ ⟨S, C, hC, h⟩⟩

end Group

section Monoid

variable [Monoid G]

/-- The trivial representation has spectral gap, since its invariant complement is zero. -/
@[simp]
theorem hasSpectralGap_trivial :
    (trivial 𝕜 G V).HasSpectralGap := by
  refine ⟨∅, 1, zero_lt_one, fun v hv ↦ ?_⟩
  have hfixed : v ∈ (trivial 𝕜 G V).invariants := by simp
  have hzero : v = 0 :=
    (Submodule.disjoint_def.mp (trivial 𝕜 G V).invariants.orthogonal_disjoint) v hfixed hv
  simp [hzero]

end Monoid

end ContRepresentation
