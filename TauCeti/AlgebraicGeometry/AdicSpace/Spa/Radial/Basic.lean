/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
import TauCeti.AlgebraicGeometry.AdicSpace.Cont.DominatingUnit
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Closed and strict radial regions in the adic spectrum

For a commutative ring `A` with a topology, a subring `A⁺`, a coordinate `T ∈ A` and radius
representatives `a, b ∈ A`, this file defines the radial subsets of `Spa (A, A⁺)` cut out by
valuative comparisons of `T` with `a` and `b`:

* `closedDisc A⁺ T b = {v ∈ Spa (A, A⁺) | v(T) ≤ v(b)}`, the closed disc `𝔻(A⁺, T, b)`;
* `puncturedClosedDisc A⁺ T b`, the closed disc with the support locus `{v | v(T) = 0}` of `T`
  removed;
* `closedAnnulus A⁺ T a b = {v ∈ Spa (A, A⁺) | v(a) ≤ v(T) ≤ v(b), v(T) ≠ 0}`;
* `strictAnnulus A⁺ T a b = {v ∈ Spa (A, A⁺) | v(a) < v(T) < v(b)}`.

The comparisons are taken at points of every rank, through the valuative relation of the point,
so no real-valued representative is chosen. For `A = C⟨T⟩` over a complete nontrivially valued
field these are the discs `B(ε)`, punctured discs `B(ε)*` and annuli `B(a, b)` of Ito and the
regions `E(0, r)` and `A(r, R)` of Berkovich on rank-one points. The words *closed* and *strict*
follow the classical radial convention `r ≤ |T| ≤ R` versus `r < |T| < R`; they are not
statements about the adic topology. Indeed a weak inequality `v(T) ≤ v(b)` with `b` a unit gives
the rational subset `R(T / b)`, which is open in `Spa (A, A⁺)` (`isOpen_val_preimage_closedDisc`),
whereas strict inequalities do not in general give an open subset.

## Main results

* `TauCeti.ValuationSpectrum.closedDisc_eq_rationalSubset`: for a unit radius, the closed disc is
  the rational subset `R({T} / b)`.
* `TauCeti.ValuationSpectrum.comap_preimage_closedDisc_inter_spa` and its analogues for the
  other regions: the radial regions are compatible with pulling back along continuous
  plus-preserving ring maps.
* `TauCeti.ValuationSpectrum.closedDisc_mul_right`: rescaling the coordinate and the radius by
  the same unit does not change the disc.
* `TauCeti.ValuationSpectrum.closedAnnulus_eq_inter_rationalSubset`: for arbitrary radii, the
  closed annulus is `R({T} / b) ∩ R({a} / T)`; no unit hypothesis is needed.
* `TauCeti.ValuationSpectrum.iUnion_closedAnnulus_pow` and
  `TauCeti.ValuationSpectrum.monotone_closedAnnulus_pow`: for a topologically nilpotent `ϖ`, the
  annuli `ϖⁿ ≤ |T| ≤ b` increase with `n` and exhaust the punctured disc.
* `TauCeti.ValuationSpectrum.strictAnnulus_subset_closedAnnulus` and
  `TauCeti.ValuationSpectrum.strictAnnulus_self`: the strict annulus lies in the closed one, and
  equal radii give the empty strict annulus but the weak circle as closed annulus.

## References

* K. Ito, *Uniform local constancy of étale cohomology of rigid analytic varieties*, §6.1, p. 31,
  and §6.2, pp. 35–37.
* V. G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, §6.3,
  Remarks 6.3.4 and Corollary 6.3.6.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### Closed discs -/

/-- **The closed disc `𝔻(A⁺, T, b)`**: the points `v` of `Spa (A, A⁺)` with `v(T) ≤ v(b)`. For a
unit `b` this is the rational subset `R({T} / b)` (`closedDisc_eq_rationalSubset`); over
`C⟨T / c⟩` for a complete nontrivially valued field `C` and a radius `0 < |b| ≤ |c|` it is the
closed disc of radius `|b|`. -/
def closedDisc (Aplus : Subring A) (T b : A) : Set (Spv A) :=
  spa Aplus ∩ {v | v.toValuativeRel.vle T b}

/-- The set-level characterization of the closed disc. -/
theorem closedDisc_def (Aplus : Subring A) (T b : A) :
    closedDisc Aplus T b = spa Aplus ∩ {v | v.toValuativeRel.vle T b} := (rfl)

/-- Membership in `𝔻(A⁺, T, b)` is membership in `Spa (A, A⁺)` together with `v(T) ≤ v(b)`. -/
@[simp]
theorem mem_closedDisc_iff (Aplus : Subring A) (T b : A) (v : Spv A) :
    v ∈ closedDisc Aplus T b ↔ v ∈ spa Aplus ∧ v.toValuativeRel.vle T b := Iff.rfl

/-- Every closed disc lies in the adic spectrum. -/
theorem closedDisc_subset_spa (Aplus : Subring A) (T b : A) : closedDisc Aplus T b ⊆ spa Aplus :=
  Set.inter_subset_left

/-- **For a unit radius the closed disc is a rational subset**: `𝔻(A⁺, T, b) = R({T} / b)`. The
nonvanishing condition `v(b) ≠ 0` of the rational subset is automatic for a unit. -/
theorem closedDisc_eq_rationalSubset (Aplus : Subring A) (T : A) {b : A} (hb : IsUnit b) :
    closedDisc Aplus T b = rationalSubset Aplus {T} b := by
  ext v
  simp only [mem_closedDisc_iff, mem_rationalSubset_iff, Finset.mem_singleton, forall_eq]
  exact ⟨fun h ↦ ⟨h.1, h.2,
    @TauCeti.ValuativeRel.not_vle_zero_of_isUnit _ _ v.toValuativeRel _ hb⟩,
    fun h ↦ ⟨h.1, h.2.1⟩⟩

/-- The closed disc of radius `1` is the rational subset `R({T} / 1)`. -/
theorem closedDisc_one_right (Aplus : Subring A) (T : A) :
    closedDisc Aplus T 1 = rationalSubset Aplus {T} 1 :=
  closedDisc_eq_rationalSubset Aplus T isUnit_one

/-- **A closed disc of unit radius is relatively open** in `Spa (A, A⁺)`. -/
theorem isOpen_val_preimage_closedDisc (Aplus : Subring A) (T : A) {b : A} (hb : IsUnit b) :
    IsOpen (Subtype.val ⁻¹' closedDisc Aplus T b : Set (spa Aplus)) := by
  rw [closedDisc_eq_rationalSubset Aplus T hb]
  exact isOpen_val_preimage_rationalSubset Aplus {T} b

/-- **Pulling back a closed disc.** For a continuous ring map `φ : A → B` carrying `A⁺` into
`B⁺`, the points of `Spa (B, B⁺)` whose pullback lies in `𝔻(A⁺, T, b)` form `𝔻(B⁺, φ T, φ b)`. -/
theorem comap_preimage_closedDisc_inter_spa {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T b : A) :
    comap φ ⁻¹' closedDisc Aplus T b ∩ spa Bplus = closedDisc Bplus (φ T) (φ b) := by
  simp only [closedDisc_def, comap_preimage_spa_inter_inter_spa hφ hplus, Set.preimage_ofPred_eq,
    comap_vle]

/-- **Concentric closed discs are nested**: if `v(b) ≤ v(b')` at every point of `Spa (A, A⁺)`,
then `𝔻(A⁺, T, b) ⊆ 𝔻(A⁺, T, b')`. -/
theorem closedDisc_subset_closedDisc (Aplus : Subring A) (T : A) {b b' : A}
    (h : ∀ v ∈ spa Aplus, v.toValuativeRel.vle b b') :
    closedDisc Aplus T b ⊆ closedDisc Aplus T b' :=
  fun v hv ↦ ⟨hv.1, v.toValuativeRel.vle_trans hv.2 (h v hv.1)⟩

/-- **Rescaling by a unit**: multiplying the coordinate and the radius by the same unit `u`
leaves the closed disc unchanged, `𝔻(A⁺, T u, b u) = 𝔻(A⁺, T, b)`. -/
@[simp]
theorem closedDisc_mul_right (Aplus : Subring A) (T b : A) {u : A} (hu : IsUnit u) :
    closedDisc Aplus (T * u) (b * u) = closedDisc Aplus T b := by
  ext v
  let := v.toValuativeRel
  have hu0 : (0 : A) <ᵥ u :=
    ValuativeRel.not_vle.mp (TauCeti.ValuativeRel.not_vle_zero_of_isUnit hu)
  simp only [mem_closedDisc_iff, ValuativeRel.mul_vle_mul_iff_left hu0]

/-- The closed disc with coordinate `0` is the whole adic spectrum, whatever the radius. -/
@[simp]
theorem closedDisc_zero_left (Aplus : Subring A) (b : A) : closedDisc Aplus 0 b = spa Aplus := by
  ext v
  let := v.toValuativeRel
  simp

/-- The closed disc whose radius is its own coordinate is the whole adic spectrum. -/
@[simp]
theorem closedDisc_self (Aplus : Subring A) (T : A) : closedDisc Aplus T T = spa Aplus := by
  ext v
  let := v.toValuativeRel
  simp

/-! ### Punctured closed discs -/

/-- **The punctured closed disc `𝔻^×(A⁺, T, b)`**: the points of the closed disc `𝔻(A⁺, T, b)`
off the support locus of `T`, that is with `v(T) ≠ 0`. For the unit disc over a complete
nontrivially valued field it is the complement of the classical point `T = 0`. -/
def puncturedClosedDisc (Aplus : Subring A) (T b : A) : Set (Spv A) :=
  closedDisc Aplus T b ∩ {v | ¬ v.toValuativeRel.vle T 0}

/-- The set-level characterization of the punctured closed disc. -/
theorem puncturedClosedDisc_def (Aplus : Subring A) (T b : A) :
    puncturedClosedDisc Aplus T b = closedDisc Aplus T b ∩ {v | ¬ v.toValuativeRel.vle T 0} :=
  (rfl)

/-- Membership in `𝔻^×(A⁺, T, b)` is closed-disc membership with `T` outside the support. -/
@[simp]
theorem mem_puncturedClosedDisc_iff (Aplus : Subring A) (T b : A) (v : Spv A) :
    v ∈ puncturedClosedDisc Aplus T b ↔
      v ∈ spa Aplus ∧ v.toValuativeRel.vle T b ∧ ¬ v.toValuativeRel.vle T 0 :=
  and_assoc

/-- The punctured closed disc lies in its closed disc. -/
theorem puncturedClosedDisc_subset_closedDisc (Aplus : Subring A) (T b : A) :
    puncturedClosedDisc Aplus T b ⊆ closedDisc Aplus T b :=
  Set.inter_subset_left

/-- The punctured closed disc is the closed disc minus the support locus `{v | v(T) = 0}`. -/
theorem puncturedClosedDisc_eq_diff (Aplus : Subring A) (T b : A) :
    puncturedClosedDisc Aplus T b = closedDisc Aplus T b \ {v | v.toValuativeRel.vle T 0} := by
  rw [puncturedClosedDisc_def, Set.sdiff_eq, Set.compl_ofPred]

/-- **Pulling back a punctured closed disc.** For a continuous ring map `φ : A → B` carrying
`A⁺` into `B⁺`, the points of `Spa (B, B⁺)` whose pullback lies in `𝔻^×(A⁺, T, b)` form
`𝔻^×(B⁺, φ T, φ b)`. -/
theorem comap_preimage_puncturedClosedDisc_inter_spa {B : Type*} [CommRing B]
    [TopologicalSpace B] {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T b : A) :
    comap φ ⁻¹' puncturedClosedDisc Aplus T b ∩ spa Bplus =
      puncturedClosedDisc Bplus (φ T) (φ b) := by
  rw [puncturedClosedDisc_def, Set.preimage_inter, Set.inter_right_comm,
    comap_preimage_closedDisc_inter_spa hφ hplus, puncturedClosedDisc_def]
  simp only [Set.preimage_ofPred_eq, comap_vle, map_zero]

/-- The punctured closed disc with coordinate `0` is empty, whatever the radius. -/
@[simp]
theorem puncturedClosedDisc_zero_left (Aplus : Subring A) (b : A) :
    puncturedClosedDisc Aplus 0 b = ∅ := by
  ext v
  simp

/-- The punctured closed disc with coordinate and radius `1` is the whole adic spectrum. -/
@[simp]
theorem puncturedClosedDisc_one_one (Aplus : Subring A) :
    puncturedClosedDisc Aplus 1 1 = spa Aplus := by
  ext v
  simp [v.toValuativeRel.not_vle_one_zero]

/-- With radius `0` the punctured closed disc is empty: `v(T) ≤ v(0)` puts `T` in the
support. -/
@[simp]
theorem puncturedClosedDisc_zero_right (Aplus : Subring A) (T : A) :
    puncturedClosedDisc Aplus T 0 = ∅ := by
  ext v
  simp

/-! ### Closed annuli -/

/-- **The closed annulus `𝔸(A⁺, T, a, b)`**: the points `v` of `Spa (A, A⁺)` with
`v(a) ≤ v(T) ≤ v(b)` and `v(T) ≠ 0`. For arbitrary `a, b` it is the intersection
`R({T} / b) ∩ R({a} / T)` of two rational subsets (`closedAnnulus_eq_inter_rationalSubset`).
Equal radii give the weak circle `v(T) = v(a)`. -/
def closedAnnulus (Aplus : Subring A) (T a b : A) : Set (Spv A) :=
  spa Aplus ∩ {v | v.toValuativeRel.vle a T ∧ v.toValuativeRel.vle T b ∧
    ¬ v.toValuativeRel.vle T 0}

/-- The set-level characterization of the closed annulus. -/
theorem closedAnnulus_def (Aplus : Subring A) (T a b : A) :
    closedAnnulus Aplus T a b = spa Aplus ∩ {v | v.toValuativeRel.vle a T ∧
      v.toValuativeRel.vle T b ∧ ¬ v.toValuativeRel.vle T 0} := (rfl)

/-- Membership in `𝔸(A⁺, T, a, b)`: `Spa` membership, both weak inequalities, and `T` outside
the support. -/
@[simp]
theorem mem_closedAnnulus_iff (Aplus : Subring A) (T a b : A) (v : Spv A) :
    v ∈ closedAnnulus Aplus T a b ↔ v ∈ spa Aplus ∧ v.toValuativeRel.vle a T ∧
      v.toValuativeRel.vle T b ∧ ¬ v.toValuativeRel.vle T 0 := Iff.rfl

/-- Every closed annulus lies in the adic spectrum. -/
theorem closedAnnulus_subset_spa (Aplus : Subring A) (T a b : A) :
    closedAnnulus Aplus T a b ⊆ spa Aplus :=
  Set.inter_subset_left

/-- **The closed annulus is an intersection of two rational subsets**:
`𝔸(A⁺, T, a, b) = R({T} / b) ∩ R({a} / T)`, for all `a` and `b`. No unit hypothesis is needed:
`v(T) ≤ v(b)` and `v(T) ≠ 0` force `v(b) ≠ 0`. -/
theorem closedAnnulus_eq_inter_rationalSubset (Aplus : Subring A) (T a b : A) :
    closedAnnulus Aplus T a b = rationalSubset Aplus {T} b ∩ rationalSubset Aplus {a} T := by
  ext v
  simp only [mem_closedAnnulus_iff, Set.mem_inter_iff, mem_rationalSubset_iff,
    Finset.mem_singleton, forall_eq]
  exact ⟨fun ⟨hv, haT, hTb, hT⟩ ↦
      ⟨⟨hv, hTb, fun hb ↦ hT (v.toValuativeRel.vle_trans hTb hb)⟩, hv, haT, hT⟩,
    fun ⟨⟨hv, hTb, _⟩, _, haT, hT⟩ ↦ ⟨hv, haT, hTb, hT⟩⟩

/-- **Closed annuli are relatively open** in `Spa (A, A⁺)`, for arbitrary radii: each is an
intersection of two rational subsets. -/
theorem isOpen_val_preimage_closedAnnulus (Aplus : Subring A) (T a b : A) :
    IsOpen (Subtype.val ⁻¹' closedAnnulus Aplus T a b : Set (spa Aplus)) := by
  rw [closedAnnulus_eq_inter_rationalSubset, Set.preimage_inter]
  exact (isOpen_val_preimage_rationalSubset Aplus {T} b).inter
    (isOpen_val_preimage_rationalSubset Aplus {a} T)

/-- **Pulling back a closed annulus.** For a continuous ring map `φ : A → B` carrying `A⁺` into
`B⁺`, the points of `Spa (B, B⁺)` whose pullback lies in `𝔸(A⁺, T, a, b)` form
`𝔸(B⁺, φ T, φ a, φ b)`. -/
theorem comap_preimage_closedAnnulus_inter_spa {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T a b : A) :
    comap φ ⁻¹' closedAnnulus Aplus T a b ∩ spa Bplus =
      closedAnnulus Bplus (φ T) (φ a) (φ b) := by
  simp only [closedAnnulus_def, comap_preimage_spa_inter_inter_spa hφ hplus,
    Set.preimage_ofPred_eq, comap_vle, map_zero]

/-- Every point of a closed annulus lies in the punctured outer disc. -/
theorem closedAnnulus_subset_puncturedClosedDisc (Aplus : Subring A) (T a b : A) :
    closedAnnulus Aplus T a b ⊆ puncturedClosedDisc Aplus T b :=
  fun v ⟨hv, _, hTb, hT⟩ ↦ (mem_puncturedClosedDisc_iff Aplus T b v).mpr ⟨hv, hTb, hT⟩

/-- **Concentric closed annuli are nested**: if `v(a') ≤ v(a)` and `v(b) ≤ v(b')` at every point
of `Spa (A, A⁺)`, then `𝔸(A⁺, T, a, b) ⊆ 𝔸(A⁺, T, a', b')`. -/
theorem closedAnnulus_subset_closedAnnulus (Aplus : Subring A) (T : A) {a a' b b' : A}
    (ha : ∀ v ∈ spa Aplus, v.toValuativeRel.vle a' a)
    (hb : ∀ v ∈ spa Aplus, v.toValuativeRel.vle b b') :
    closedAnnulus Aplus T a b ⊆ closedAnnulus Aplus T a' b' :=
  fun v ⟨hv, haT, hTb, hT⟩ ↦ ⟨hv, v.toValuativeRel.vle_trans (ha v hv) haT,
    v.toValuativeRel.vle_trans hTb (hb v hv), hT⟩

/-- **The annular exhaustion of the punctured disc.** For a topologically nilpotent `ϖ`, the
closed annuli `v(ϖⁿ) ≤ v(T) ≤ v(b)` exhaust `𝔻^×(A⁺, T, b)`: at a continuous point with
`v(T) ≠ 0`, some power of `ϖ` is dominated by `T`. -/
theorem iUnion_closedAnnulus_pow (Aplus : Subring A) (T b : A) {ϖ : A}
    (hϖ : IsTopologicallyNilpotent ϖ) :
    ⋃ n : ℕ, closedAnnulus Aplus T (ϖ ^ n) b = puncturedClosedDisc Aplus T b := by
  refine Set.Subset.antisymm
    (Set.iUnion_subset fun n ↦ closedAnnulus_subset_puncturedClosedDisc Aplus T _ b) ?_
  intro v hv
  obtain ⟨hspa, hTb, hT⟩ := (mem_puncturedClosedDisc_iff Aplus T b v).mp hv
  obtain ⟨n, hn⟩ := ((mem_spa_iff Aplus v).mp hspa).1.exists_pow_vlt_of_isTopologicallyNilpotent
    hϖ (by rwa [mem_supp_iff])
  let := v.toValuativeRel
  exact Set.mem_iUnion.mpr ⟨n, hspa, hn.vle, hTb, hT⟩

/-- **The exhaustion annuli increase**: for a topologically nilpotent `ϖ`, every point of
`Spa (A, A⁺)` is continuous, so `v(ϖ) ≤ 1` and `v(ϖᵐ) ≤ v(ϖⁿ)` for `n ≤ m`; hence
`𝔸(A⁺, T, ϖⁿ, b) ⊆ 𝔸(A⁺, T, ϖᵐ, b)`. -/
theorem monotone_closedAnnulus_pow (Aplus : Subring A) (T b : A) {ϖ : A}
    (hϖ : IsTopologicallyNilpotent ϖ) : Monotone fun n : ℕ ↦ closedAnnulus Aplus T (ϖ ^ n) b :=
  fun _ _ hnm ↦ closedAnnulus_subset_closedAnnulus Aplus T
    (fun v hv ↦ by
      let := v.toValuativeRel
      refine ValuativeRel.pow_vle_pow_of_vle_one ((valuation_le_iff v ϖ 1).mp ?_) hnm
      rw [map_one]
      exact ((isContinuous_def v).mp ((mem_spa_iff Aplus v).mp hv).1
        |>.lt_one_of_isTopologicallyNilpotent hϖ).le)
    (fun v _ ↦ v.toValuativeRel.vle_refl b)

/-- **A closed annulus with inner radius `0` is the punctured closed disc**: `v(0) ≤ v(T)` always
holds. -/
@[simp]
theorem closedAnnulus_zero_middle (Aplus : Subring A) (T b : A) :
    closedAnnulus Aplus T 0 b = puncturedClosedDisc Aplus T b := by
  ext v
  let := v.toValuativeRel
  simp

/-- The closed annulus with coordinate `0` is empty. -/
@[simp]
theorem closedAnnulus_zero_left (Aplus : Subring A) (a b : A) : closedAnnulus Aplus 0 a b = ∅ := by
  ext v
  simp

/-- The closed annulus with coordinate and both radii `1` is the whole adic spectrum. -/
@[simp]
theorem closedAnnulus_one_one_one (Aplus : Subring A) : closedAnnulus Aplus 1 1 1 = spa Aplus := by
  ext v
  simp [v.toValuativeRel.not_vle_one_zero]

/-! ### Strict annuli -/

/-- **The strict annulus `𝔸^<(A⁺, T, a, b)`**: the points `v` of `Spa (A, A⁺)` with
`v(a) < v(T) < v(b)`, the strict comparison being the negation of the reverse weak one. The
strict inequality `v(a) < v(T)` already puts `T` outside the support
(`not_vle_zero_of_mem_strictAnnulus`). This locus is not asserted to be open in `Spa (A, A⁺)`:
radial regions called *open* in Berkovich's or rigid terminology are the unions of closed
annuli of `TauCeti.ValuationSpectrum.openAnnulus`. For radius families with `v(a) < v(aⱼ)` and
`v(bⱼ) < v(b)` such a union lies in the strict annulus, and is in general a proper subset of it
because of Ito's rank-two point `η(R)`. -/
def strictAnnulus (Aplus : Subring A) (T a b : A) : Set (Spv A) :=
  spa Aplus ∩ {v | v.toValuativeRel.vlt a T ∧ v.toValuativeRel.vlt T b}

/-- The set-level characterization of the strict annulus. -/
theorem strictAnnulus_def (Aplus : Subring A) (T a b : A) :
    strictAnnulus Aplus T a b =
      spa Aplus ∩ {v | v.toValuativeRel.vlt a T ∧ v.toValuativeRel.vlt T b} := (rfl)

/-- Membership in `𝔸^<(A⁺, T, a, b)`: `Spa` membership and both strict comparisons. -/
@[simp]
theorem mem_strictAnnulus_iff (Aplus : Subring A) (T a b : A) (v : Spv A) :
    v ∈ strictAnnulus Aplus T a b ↔
      v ∈ spa Aplus ∧ v.toValuativeRel.vlt a T ∧ v.toValuativeRel.vlt T b := Iff.rfl

/-- Every strict annulus lies in the adic spectrum. -/
theorem strictAnnulus_subset_spa (Aplus : Subring A) (T a b : A) :
    strictAnnulus Aplus T a b ⊆ spa Aplus :=
  Set.inter_subset_left

/-- At a point of a strict annulus the coordinate is outside the support. -/
theorem not_vle_zero_of_mem_strictAnnulus {Aplus : Subring A} {T a b : A} {v : Spv A}
    (hv : v ∈ strictAnnulus Aplus T a b) : ¬ v.toValuativeRel.vle T 0 := by
  let := v.toValuativeRel
  exact fun hT ↦ hv.2.1 (ValuativeRel.vle_trans hT (ValuativeRel.zero_vle a))

/-- **Pulling back a strict annulus.** For a continuous ring map `φ : A → B` carrying `A⁺` into
`B⁺`, the points of `Spa (B, B⁺)` whose pullback lies in `𝔸^<(A⁺, T, a, b)` form
`𝔸^<(B⁺, φ T, φ a, φ b)`. -/
theorem comap_preimage_strictAnnulus_inter_spa {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T a b : A) :
    comap φ ⁻¹' strictAnnulus Aplus T a b ∩ spa Bplus =
      strictAnnulus Bplus (φ T) (φ a) (φ b) := by
  simp only [strictAnnulus_def, comap_preimage_spa_inter_inter_spa hφ hplus,
    Set.preimage_ofPred_eq, comap_vlt]

/-- **The strict annulus lies in the closed annulus** with the same radii. -/
theorem strictAnnulus_subset_closedAnnulus (Aplus : Subring A) (T a b : A) :
    strictAnnulus Aplus T a b ⊆ closedAnnulus Aplus T a b := by
  intro v hv
  let := v.toValuativeRel
  exact ⟨hv.1, hv.2.1.vle, hv.2.2.vle, not_vle_zero_of_mem_strictAnnulus hv⟩

/-- **Equal radii give the empty strict annulus**, unlike the closed annulus, which is then the
weak circle. -/
@[simp]
theorem strictAnnulus_self (Aplus : Subring A) (T a : A) : strictAnnulus Aplus T a a = ∅ := by
  ext v
  let := v.toValuativeRel
  simp only [mem_strictAnnulus_iff, Set.mem_empty_iff_false, iff_false]
  exact fun ⟨_, haT, hTa⟩ ↦ haT hTa.vle

/-- The strict annulus with coordinate `0` is empty. -/
@[simp]
theorem strictAnnulus_zero_left (Aplus : Subring A) (a b : A) : strictAnnulus Aplus 0 a b = ∅ := by
  ext v
  let := v.toValuativeRel
  simp

end TauCeti.ValuationSpectrum
