/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Continuous.Unitary.HilbertSum
import Mathlib.Algebra.Group.Shrink
import TauCeti.RepresentationTheory.Continuous.InvariantComplement
import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite

/-!
# Kazhdan pairs and universe independence for relative property (T)

A pair `(F, δ)` of a finite set `F ⊆ Γ` and a real number `δ` is a *Kazhdan pair* for a subgroup
`Λ` of a discrete group `Γ` when every unitary representation of `Γ` with a unit vector moved by
less than `δ` by each element of `F` has a nonzero `Λ`-invariant vector. A Kazhdan pair with
`δ > 0` yields relative property (T), and conversely `Λ` has relative property (T) exactly when it
has a Kazhdan pair with `δ > 0`.

For the converse, if no Kazhdan pair exists, choose for every finite `F` and every `n` a unitary
representation with an `(F, 1 / (n + 1))`-invariant unit vector and no nonzero `Λ`-invariant
vector. Their Hilbert direct sum has almost invariant vectors, given by the chosen unit vectors
placed in single coordinates, and still has no nonzero `Λ`-invariant vector, since a vector of the
sum is invariant exactly when each of its coordinates is.

Using Mathlib's `Shrink.mulEquiv : Shrink.{u} Γ ≃* Γ` together with the GNS realization of
positive-definite matrix coefficients, whenever `Γ` is `u`-small (`[Small.{u} Γ]`), any unitary
representation in an arbitrary universe `w` with an `(F, δ)`-invariant unit vector receives an
intertwining linear isometry from a GNS Hilbert space in `Type u`; thus `IsKazhdanPair.{u}` and
`RelativePropertyT.{u}` imply `IsKazhdanPair.{w}` and `RelativePropertyT.{w}` for every universe
`w`. Since `Γ : Type v` is always `v`-small (`small_self`) and `max u v`-small (`small_max`,
which is not a typeclass instance, so the `*_max_iff` equivalences are provided explicitly),
`IsKazhdanPair.{v}` and `RelativePropertyT.{v}` coincide unconditionally with
`IsKazhdanPair.{max u v}` and `RelativePropertyT.{max u v}`. When `Γ` is small in both `u` and `w`
(for example whenever `Γ` is countable, via `Countable.toSmall`), `IsKazhdanPair` and
`RelativePropertyT` are independent of the Hilbert-space universe.

For a normal subgroup `Λ` of an arbitrary discrete group `Γ`, the subspace `H^Λ` of `Λ`-invariant
vectors is `Γ`-invariant, so restricting a unitary representation to `(H^Λ)ᗮ` turns any Kazhdan
pair `(F, δ)` with `δ > 0` into a quantitative approximation bound: every vector `ξ` moved by at
most `ε * δ` on `F` lies within `ε` of its orthogonal projection onto `H^Λ`.

## Main statements

* `Subgroup.IsKazhdanPair.relativePropertyT`: a Kazhdan pair gives relative property (T).
* `Subgroup.isKazhdanPair_of_exists_invariant_norm_sub_lt_one`: approximation by `Λ`-invariant
  vectors within distance `< 1` yields a Kazhdan pair.
* `Subgroup.isKazhdanPair_top_univ_one`: for a finite group `Γ`, `(Γ, 1)` is a Kazhdan pair
  for `⊤`.
* `Subgroup.relativePropertyT_iff_exists_isKazhdanPair`: relative property (T) is equivalent to
  the existence of a Kazhdan pair.
* `Subgroup.IsKazhdanPair.of_universe`, `Subgroup.RelativePropertyT.of_universe`: universe transfer
  from any universe `u` in which `Γ` is small (`[Small.{u} Γ]`).
* `Subgroup.isKazhdanPair_iff_isKazhdanPair`, `Subgroup.relativePropertyT_iff_relativePropertyT`:
  universe equivalence between any two universes in which `Γ` is small (in particular for countable
  `Γ`).
* `Subgroup.isKazhdanPair_max_iff`, `Subgroup.relativePropertyT_max_iff`: unconditional universe
  equivalence between `max u v` and `v`.
* `Subgroup.IsKazhdanPair.norm_sub_starProjection_invariants_le`,
  `Subgroup.IsKazhdanPair.exists_invariant_norm_sub_lt`: quantitative Kazhdan approximation for
  normal subgroups, without countability.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Chapter 1.
-/

public section

namespace Subgroup

universe u w v

open ContRepresentation
open scoped ComplexOrder InnerProductSpace

variable {Γ : Type v} [Group Γ]

/-- A pair `(F, δ)` of a finite set `F ⊆ Γ` and a real number `δ` is a Kazhdan pair for the
subgroup `Λ` when every unitary representation of `Γ` on a complex Hilbert space in universe `u`
with a unit vector moved by less than `δ` by each element of `F` has a nonzero vector fixed by
`Λ`. -/
def IsKazhdanPair (Λ : Subgroup Γ) (F : Finset Γ) (δ : ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
      (∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
        ∃ v : H, v ≠ 0 ∧ v ∈ (ρ.restrict Λ.subtype).invariants

/-- The unitary-representation criterion for Kazhdan pairs. -/
theorem isKazhdanPair_def (Λ : Subgroup Γ) (F : Finset Γ) (δ : ℝ) :
    Λ.IsKazhdanPair.{u} F δ ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
          (∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
            ∃ v : H, v ≠ 0 ∧ v ∈ (ρ.restrict Λ.subtype).invariants :=
  Iff.rfl

/-- Enlarging the finite set or shrinking the constant preserves Kazhdan pairs. -/
theorem IsKazhdanPair.mono {Λ : Subgroup Γ} {F F' : Finset Γ} {δ δ' : ℝ}
    (h : Λ.IsKazhdanPair.{u} F δ) (hF : F ⊆ F') (hδ : δ' ≤ δ) :
    Λ.IsKazhdanPair.{u} F' δ' := by
  rintro H _ _ _ ρ hρ ⟨ξ, hξ, hF'⟩
  exact h H ρ hρ ⟨ξ, hξ, fun g hg ↦ (hF' g (hF hg)).trans_le hδ⟩

/-- Passing to a smaller subgroup preserves Kazhdan pairs. -/
theorem IsKazhdanPair.mono_subgroup {Λ K : Subgroup Γ} {F : Finset Γ} {δ : ℝ}
    (h : Λ.IsKazhdanPair.{u} F δ) (hK : K ≤ Λ) :
    K.IsKazhdanPair.{u} F δ := by
  intro H _ _ _ ρ hρ hξ
  obtain ⟨v, hv0, hv⟩ := h H ρ hρ hξ
  exact ⟨v, hv0, fun g ↦ hv ⟨g, hK g.property⟩⟩

/-- Pushing forward along a group homomorphism carries Kazhdan pairs to the image subgroup. -/
theorem IsKazhdanPair.map {G' : Type w} [Group G'] [DecidableEq G'] {Λ : Subgroup Γ}
    {F : Finset Γ} {δ : ℝ} (h : Λ.IsKazhdanPair.{u} F δ) (f : Γ →* G') :
    (Λ.map f).IsKazhdanPair.{u} (F.image f) δ := by
  rintro H _ _ _ ρ hρ ⟨ξ, hξ, hF⟩
  obtain ⟨v, hv0, hv⟩ := h H (ρ.restrict f) (hρ.restrict f)
    ⟨ξ, hξ, fun g hg ↦ hF (f g) (Finset.mem_image_of_mem f hg)⟩
  refine ⟨v, hv0, fun g ↦ ?_⟩
  obtain ⟨x, hx, hfx⟩ := g.property
  simpa [hfx] using hv ⟨x, hx⟩

/-- Kazhdan pairs are preserved and reflected by group isomorphisms. -/
theorem isKazhdanPair_map_mulEquiv_iff {G' : Type w} [Group G'] {Λ : Subgroup Γ}
    {F : Finset Γ} {δ : ℝ} (e : Γ ≃* G') :
    (Λ.map e.toMonoidHom).IsKazhdanPair.{u} (F.map e.toEquiv.toEmbedding) δ ↔
      Λ.IsKazhdanPair.{u} F δ := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := h.map e.symm.toMonoidHom
    have hΛ : (Λ.map e.toMonoidHom).map e.symm.toMonoidHom = Λ := by
      rw [Subgroup.map_map]
      simp
    have hF : (F.map e.toEquiv.toEmbedding).image e.symm.toMonoidHom = F := by
      ext g
      simp only [Finset.mem_image, Finset.mem_map, Equiv.coe_toEmbedding, MulEquiv.coe_toMonoidHom]
      exact ⟨by rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; simpa using ha,
        fun hg ↦ ⟨e g, ⟨g, hg, rfl⟩, e.symm_apply_apply g⟩⟩
    rwa [hΛ, hF] at h'
  · simpa [Finset.map_eq_image] using h.map e.toMonoidHom

/-- A Kazhdan pair `(F, δ)` with `δ > 0` for `Λ` gives relative property (T) of `Λ`. -/
theorem IsKazhdanPair.relativePropertyT {Λ : Subgroup Γ} {F : Finset Γ} {δ : ℝ}
    (hΛ : Λ.IsKazhdanPair.{u} F δ) (hδ : 0 < δ) : Λ.RelativePropertyT.{u} :=
  (relativePropertyT_def Λ).mpr fun H _ _ _ ρ hu hρ ↦
    hΛ H ρ hu ((hasAlmostInvariantVectors_def ρ).mp hρ F δ hδ)

/-- If every `(F, δ)`-invariant unit vector of a unitary representation in universe `u` lies at
distance strictly less than `1` from a `Λ`-invariant vector, then `(F, δ)` is a Kazhdan pair for
`Λ`. -/
theorem isKazhdanPair_of_exists_invariant_norm_sub_lt_one {Λ : Subgroup Γ} {F : Finset Γ}
    {δ : ℝ}
    (h : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
        ∀ ξ : H, ‖ξ‖ = 1 → (∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
          ∃ v ∈ (ρ.restrict Λ.subtype).invariants, ‖v - ξ‖ < 1) :
    Λ.IsKazhdanPair.{u} F δ := by
  rintro H _ _ _ ρ hρ ⟨ξ, hξ, hξF⟩
  obtain ⟨v, hv, hvξ⟩ := h H ρ hρ ξ hξ hξF
  exact ⟨v, fun hv0 ↦ by simp [hv0, hξ] at hvξ, hv⟩

/-- In a finite group `Γ`, the pair `(Γ, 1)` is a Kazhdan pair for `⊤`: averaging a unit vector
moved by less than `1` by every element gives an invariant vector within distance less than `1`
of it, which therefore cannot vanish. -/
theorem isKazhdanPair_top_univ_one [Fintype Γ] :
    (⊤ : Subgroup Γ).IsKazhdanPair.{u} Finset.univ 1 := by
  rintro H _ _ _ ρ - ⟨ξ, hξ, hF⟩
  obtain ⟨w, hw, hclose⟩ := ρ.exists_invariant_norm_sub_lt fun g ↦ hF g (Finset.mem_univ g)
  refine ⟨w, fun hw0 ↦ ?_, fun g ↦ hw g⟩
  simp [hw0, hξ] at hclose

/-- **Kazhdan pairs.** A subgroup `Λ` of a discrete group `Γ` has relative property (T) exactly
when there are a finite set `F ⊆ Γ` and a `δ > 0` forming a Kazhdan pair for `Λ`. -/
theorem relativePropertyT_iff_exists_isKazhdanPair (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{max u v} ↔
      ∃ (F : Finset Γ) (δ : ℝ), 0 < δ ∧ Λ.IsKazhdanPair.{max u v} F δ := by
  classical
  refine ⟨fun hΛ ↦ ?_, fun ⟨F, δ, hδ, h⟩ ↦ h.relativePropertyT hδ⟩
  by_contra hne
  -- For each finite set `F` and each `n`, choose a unitary representation with an
  -- `(F, 1 / (n + 1))`-invariant unit vector and no nonzero `Λ`-invariant vector.
  have key (i : Finset Γ × ℕ) : ¬ Λ.IsKazhdanPair.{max u v} i.1 (1 / (i.2 + 1)) :=
    fun hi ↦ hne ⟨i.1, _, Nat.one_div_pos_of_nat, hi⟩
  simp only [isKazhdanPair_def, not_forall, not_exists, not_and] at key
  choose H _ _ _ ρ hu hξ hinv using key
  -- Their Hilbert direct sum has almost invariant vectors, so it has a nonzero `Λ`-invariant
  -- vector, whose coordinates are `Λ`-invariant and hence all zero.
  obtain ⟨x, hx0, hx⟩ :=
    (relativePropertyT_def Λ).mp hΛ (lp H 2) (hilbertSum ρ hu) (isUnitary_hilbertSum ρ hu) <|
      (hasAlmostInvariantVectors_def _).mpr fun F ε hε ↦ by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨ξ, hξ1, hξF⟩ := hξ (F, n)
        refine ⟨lp.single 2 (F, n) ξ, by rw [lp.norm_single (by norm_num), hξ1], fun g hg ↦ ?_⟩
        rw [hilbertSum_apply_single, ← lp.single_sub, lp.norm_single (by norm_num)]
        exact (hξF g hg).trans hn
  rw [restrict_hilbertSum, mem_invariants_hilbertSum_iff] at hx
  exact hx0 (lp.ext (funext fun i ↦ not_not.mp fun h ↦ hinv i (x i) h (hx i)))

/-- A Kazhdan pair in a universe `u` in which the ambient group `Γ` is small is a Kazhdan pair in
every Hilbert-space universe `w`. -/
theorem IsKazhdanPair.of_universe [Small.{u} Γ] {Λ : Subgroup Γ} {F : Finset Γ} {δ : ℝ}
    (h : Λ.IsKazhdanPair.{u} F δ) : Λ.IsKazhdanPair.{w} F δ := by
  rintro H _ _ _ ρ hρ ⟨ξ, hξ, hF⟩
  let e : Shrink.{u} Γ ≃* Γ := Shrink.mulEquiv
  let ρ₀ : ContRepresentation ℂ (Shrink.{u} Γ) H := ρ.restrict e.toMonoidHom
  have hρ₀ : ρ₀.IsUnitary := hρ.restrict e.toMonoidHom
  let φ : Shrink.{u} Γ → ℂ := fun g ↦ ⟪ξ, ρ₀ g ξ⟫_ℂ
  have hφ : (Matrix.of fun g h : Shrink.{u} Γ ↦ φ (g⁻¹ * h)).PosSemidef :=
    hρ₀.posSemidef_inner_map_inv_mul ξ
  let T := hφ.gnsIsometry hρ₀ (fun _ ↦ rfl)
  let σ : ContRepresentation ℂ Γ hφ.gnsSpace := hφ.gnsRepresentation.restrict e.symm.toMonoidHom
  have hσ : σ.IsUnitary := hφ.isUnitary_gnsRepresentation.restrict e.symm.toMonoidHom
  let ξ₀ := hφ.gnsVector 1
  have hTξ₀ : T ξ₀ = ξ := by simp [T, ξ₀]
  have hξ₀_norm : ‖ξ₀‖ = 1 := by rw [← T.norm_map, hTξ₀, hξ]
  have hTσ (g : Γ) (x : hφ.gnsSpace) : T (σ g x) = ρ g (T x) := by
    simpa [σ, ρ₀, e, T] using
      hφ.gnsIsometry_gnsRepresentation hρ₀ (fun _ ↦ rfl) (e.symm g) x
  have hξ₀_F (g : Γ) (hg : g ∈ F) : ‖σ g ξ₀ - ξ₀‖ < δ := by
    rw [← T.norm_map, map_sub, hTσ, hTξ₀]
    exact hF g hg
  obtain ⟨v₀, hv₀, hv₀Λ⟩ := h hφ.gnsSpace σ hσ ⟨ξ₀, hξ₀_norm, hξ₀_F⟩
  refine ⟨T v₀, fun h0 ↦ hv₀ (T.injective (by simpa using h0)), fun k ↦ ?_⟩
  rw [restrict_apply_apply, ← hTσ]
  exact congrArg T (hv₀Λ k)

/-- **Universe independence of Kazhdan pairs.** When the ambient group `Γ` is small in both `u` and
`w` (for example whenever `Γ` is countable), whether `(F, δ)` is a Kazhdan pair for `Λ` is
equivalent in universes `u` and `w`. -/
theorem isKazhdanPair_iff_isKazhdanPair [Small.{u} Γ] [Small.{w} Γ] (Λ : Subgroup Γ)
    (F : Finset Γ) (δ : ℝ) :
    Λ.IsKazhdanPair.{u} F δ ↔ Λ.IsKazhdanPair.{w} F δ :=
  ⟨IsKazhdanPair.of_universe, IsKazhdanPair.of_universe⟩

/-- Being a Kazhdan pair in universe `max u v` is equivalent to being a Kazhdan pair in the
universe `v` of the group. -/
theorem isKazhdanPair_max_iff (Λ : Subgroup Γ) (F : Finset Γ) (δ : ℝ) :
    Λ.IsKazhdanPair.{max u v} F δ ↔ Λ.IsKazhdanPair.{v} F δ :=
  ⟨fun h ↦ have : Small.{max u v} Γ := small_max Γ; h.of_universe, IsKazhdanPair.of_universe⟩

/-- Relative property (T) in a universe `u` in which the ambient group `Γ` is small implies
relative property (T) in every Hilbert-space universe `w`. -/
theorem RelativePropertyT.of_universe [Small.{u} Γ] {Λ : Subgroup Γ}
    (h : Λ.RelativePropertyT.{u}) : Λ.RelativePropertyT.{w} := by
  let e : Shrink.{u} Γ ≃* Γ := Shrink.mulEquiv
  let Λ₀ : Subgroup (Shrink.{u} Γ) := Λ.comap e.toMonoidHom
  have hΛ₀_map : Λ₀.map e.toMonoidHom = Λ :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective Λ
  have hΛ₀ : Λ₀.RelativePropertyT.{u} :=
    (relativePropertyT_map_mulEquiv_iff e).mp (hΛ₀_map.symm ▸ h)
  obtain ⟨F₀, δ, hδ, hK₀⟩ := Λ₀.relativePropertyT_iff_exists_isKazhdanPair.{u, u}.mp hΛ₀
  have hK : Λ.IsKazhdanPair.{u} (F₀.map e.toEquiv.toEmbedding) δ := by
    rw [← hΛ₀_map]
    exact (isKazhdanPair_map_mulEquiv_iff e).mpr hK₀
  exact hK.of_universe.relativePropertyT hδ

/-- **Universe independence of relative property (T).** When the ambient group `Γ` is small in both
`u` and `w` (for example whenever `Γ` is countable), relative property (T) of `Λ` is equivalent in
universes `u` and `w`. -/
theorem relativePropertyT_iff_relativePropertyT [Small.{u} Γ] [Small.{w} Γ] (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{u} ↔ Λ.RelativePropertyT.{w} :=
  ⟨RelativePropertyT.of_universe, RelativePropertyT.of_universe⟩

/-- Relative property (T) in universe `max u v` is equivalent to relative property (T) in the
universe `v` of the group. -/
theorem relativePropertyT_max_iff (Λ : Subgroup Γ) :
    Λ.RelativePropertyT.{max u v} ↔ Λ.RelativePropertyT.{v} :=
  ⟨fun h ↦ have : Small.{max u v} Γ := small_max Γ; h.of_universe, RelativePropertyT.of_universe⟩

section Normal

/-- **Quantitative Kazhdan approximation for normal subgroups.** If `(F, δ)` with `δ > 0` is a
Kazhdan pair for a normal subgroup `Λ` in the universe of `Γ`, then in any unitary representation
`ρ` of `Γ` on a Hilbert space (in any universe) every vector `ξ` moved by at most `ε * δ` on `F`
lies within `ε` of its orthogonal projection onto `H^Λ`. -/
theorem IsKazhdanPair.norm_sub_starProjection_invariants_le {Λ : Subgroup Γ} [Λ.Normal]
    {F : Finset Γ} {δ : ℝ} (hK : Λ.IsKazhdanPair.{v} F δ) (hδ : 0 < δ)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : ContRepresentation ℂ Γ H} (hρ : ρ.IsUnitary) {ε : ℝ} (hε : 0 ≤ ε) (ξ : H)
    (hF : ∀ g ∈ F, ‖ρ g ξ - ξ‖ ≤ ε * δ) :
    ‖ξ - (ρ.restrict Λ.subtype).invariants.starProjection ξ‖ ≤ ε := by
  let W := (ρ.restrict Λ.subtype).invariants
  have hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W := apply_mem_invariants_restrict ρ Λ
  let η : H := ξ - W.starProjection ξ
  by_cases hη0 : η = 0
  · dsimp only [η] at hη0
    rw [hη0, norm_zero]
    exact hε
  have hηpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
  -- Restrict `ρ` to `Wᗮ`, which is `Γ`-invariant since `Λ` is normal and `ρ` is unitary, and has
  -- no nonzero `Λ`-invariant vectors.
  let σ := ρ.subrepresentation Wᗮ (hρ.apply_mem_orthogonal hW)
  have hσ : σ.IsUnitary := hρ.subrepresentation (hρ.apply_mem_orthogonal hW)
  let η₀ : Wᗮ := ⟨(‖η‖⁻¹ : ℂ) • η, Wᗮ.smul_mem _ (W.sub_starProjection_mem_orthogonal ξ)⟩
  have hη₀_norm : ‖η₀‖ = 1 := by
    rw [← Submodule.norm_coe]
    exact norm_smul_inv_norm hη0
  have hno_inv : ¬ ∃ v : Wᗮ, v ≠ 0 ∧ v ∈ (σ.restrict Λ.subtype).invariants := by
    rintro ⟨v, hv0, hv⟩
    have hvW : (v : H) ∈ W := fun k ↦ by
      simpa only [σ, restrict_apply_apply, coe_subrepresentation_apply] using
        congrArg Subtype.val (hv k)
    exact hv0 (Subtype.ext ((Submodule.disjoint_def.mp W.orthogonal_disjoint) v hvW v.property))
  have hnotF : ¬ ∀ g ∈ F, ‖σ g η₀ - η₀‖ < δ := fun hlt ↦
    hno_inv ((isKazhdanPair_def Λ F δ).mp hK.of_universe Wᗮ σ hσ ⟨η₀, hη₀_norm, hlt⟩)
  push Not at hnotF
  obtain ⟨g, hgF, hgδ⟩ := hnotF
  have hcomm : ρ g η - η = Wᗮ.starProjection (ρ g ξ - ξ) := by
    dsimp only [η]
    rw [Submodule.starProjection_orthogonal_val, map_sub, map_sub,
      hρ.starProjection_apply_comm hW g ξ]
    abel
  have hproj_le : ‖ρ g η - η‖ ≤ ‖ρ g ξ - ξ‖ := by
    rw [hcomm]
    exact Wᗮ.norm_starProjection_apply_le _
  have hscale : ‖σ g η₀ - η₀‖ = ‖η‖⁻¹ * ‖ρ g η - η‖ := by
    rw [← Submodule.norm_coe, Submodule.coe_sub, coe_subrepresentation_apply, map_smul, ← smul_sub,
      norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  rw [hscale, le_inv_mul_iff₀' hηpos] at hgδ
  have hle : δ * ‖η‖ ≤ δ * ε := by linarith [hproj_le, hF g hgF]
  exact le_of_mul_le_mul_left hle hδ

/-- For a Kazhdan pair `(F, δ)` (`δ > 0`) of a normal subgroup `Λ` in the universe `v` of `Γ`,
any vector in a unitary representation on a Hilbert space (in any universe) moved by strictly less
than `ε * δ` on `F` (`ε > 0`) is strictly within `ε` of a `Λ`-invariant vector. -/
theorem IsKazhdanPair.exists_invariant_norm_sub_lt {Λ : Subgroup Γ} [Λ.Normal]
    {F : Finset Γ} {δ : ℝ} (hK : Λ.IsKazhdanPair.{v} F δ) (hδ : 0 < δ)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : ContRepresentation ℂ Γ H} (hρ : ρ.IsUnitary) {ε : ℝ} (hε : 0 < ε) (ξ : H)
    (hF : ∀ g ∈ F, ‖ρ g ξ - ξ‖ < ε * δ) :
    ∃ v ∈ (ρ.restrict Λ.subtype).invariants, ‖v - ξ‖ < ε := by
  refine ⟨(ρ.restrict Λ.subtype).invariants.starProjection ξ,
    Submodule.starProjection_apply_mem _ ξ, ?_⟩
  rw [norm_sub_rev]
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · exact (hK.norm_sub_starProjection_invariants_le hδ hρ le_rfl ξ (by simp)).trans_lt hε
  · let m : ℝ := (F.sup' hFne fun g ↦ ‖ρ g ξ - ξ‖) / δ
    have hm_nonneg : 0 ≤ m := by
      obtain ⟨g₀, hg₀⟩ := hFne
      exact div_nonneg ((norm_nonneg _).trans (F.le_sup' (fun g ↦ ‖ρ g ξ - ξ‖) hg₀)) hδ.le
    have hm_lt : m < ε := by
      rw [div_lt_iff₀ hδ, Finset.sup'_lt_iff]
      exact hF
    refine (hK.norm_sub_starProjection_invariants_le hδ hρ hm_nonneg ξ fun g hg ↦ ?_).trans_lt hm_lt
    rw [div_mul_cancel₀ _ hδ.ne']
    exact F.le_sup' (fun g ↦ ‖ρ g ξ - ξ‖) hg

end Normal

end Subgroup
