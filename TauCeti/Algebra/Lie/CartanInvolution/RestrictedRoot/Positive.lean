/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Decomposition
public import Mathlib.Algebra.Lie.Engel

/-!
# The positive restricted root space `𝔫`

Let `𝔞` be a submodule of a Lie algebra `L` over an ordered ring and `H₀ ∈ 𝔞`. The restricted
roots `λ` with `λ(H₀) > 0` form the positive system `Σ⁺` cut out by `H₀`, and the sum of their
restricted root spaces is

`𝔫 = ⊕_{λ ∈ Σ⁺} 𝔤_λ` (`Submodule.positiveRestrictedRootSpace 𝔞 H₀`).

Since `[𝔤_λ, 𝔤_μ] ⊆ 𝔤_{λ + μ}` and `λ(H₀) > 0`, `μ(H₀) ≥ 0` give `(λ + μ)(H₀) > 0`, the space `𝔫` is
a Lie subalgebra (`Submodule.positiveRestrictedRootSubalgebra`), normalized by `𝔞` and by the
centralizer `𝔤_0` of `𝔞`. If the restricted root spaces span `L` and `L` is Noetherian, each
`ad x`, `x ∈ 𝔫`, is nilpotent on `L`: it strictly raises the value at `H₀` of the restricted roots
involved, which takes finitely many values. By Engel's theorem `𝔫` acts nilpotently on `L` and is a
nilpotent Lie algebra. For an automorphism `θ` with `𝔞 ⊆ 𝔭`, `θ` maps `𝔫` onto the negative
counterpart `𝔫⁻ = positiveRestrictedRootSpace 𝔞 (-H₀)`, and `𝔤_0 + 𝔫` meets `𝔫⁻` trivially.

For a Cartan involution of a real Lie algebra and an abelian `𝔞 ⊆ 𝔭` these hypotheses hold. For
`𝔞` maximal abelian and `H₀` regular, `𝔫` is the Lie algebra of the nilpotent factor `N` of the
Iwasawa decomposition `G = KAN` of a real semisimple Lie group, and an ideal of the minimal
parabolic subalgebra `𝔤_0 ⊕ 𝔫 = 𝔪 ⊕ 𝔞 ⊕ 𝔫`. The Lie algebra decompositions `𝔤₀ = 𝔫⁻ ⊕ 𝔤_0 ⊕ 𝔫`
and `𝔤₀ = 𝔨 ⊕ 𝔞 ⊕ 𝔫` are in `TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Iwasawa`.

## Main definitions

* `Submodule.positiveRestrictedRootSpace`: the sum `𝔫` of the restricted root spaces of the
  restricted roots positive at `H₀`.
* `Submodule.positiveRestrictedRootSubalgebra`: `𝔫` as a Lie subalgebra.

## Main results

* `Submodule.positiveRestrictedRootSpace_le_iff`: `𝔫 ≤ N` exactly when `𝔤_λ ≤ N` for every `λ`
  with `λ(H₀) > 0`; `Submodule.apply_mem_of_mem_positiveRestrictedRootSpace` is its form for the
  image of `𝔫` under a linear map.
* `Submodule.lie_mem_positiveRestrictedRootSpace`: `[𝔫, 𝔫] ⊆ 𝔫`.
* `Submodule.lie_mem_positiveRestrictedRootSpace_of_mem_restrictedRootSpace`: `[𝔤_μ, 𝔫] ⊆ 𝔫` for
  `μ(H₀) ≥ 0`, in particular for `μ = 0`.
* `Submodule.lie_mem_positiveRestrictedRootSpace_of_mem`: `[𝔞, 𝔫] ⊆ 𝔫`.
* `Submodule.disjoint_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace`: `𝔤_0 + 𝔫` and
  `𝔫⁻` are independent; `Submodule.disjoint_restrictedRootSpace_zero_positiveRestrictedRootSpace`
  and `Submodule.disjoint_positiveRestrictedRootSpace`: `𝔤_0 ∩ 𝔫 = 0`, and `𝔞 ∩ 𝔫 = 0` for abelian
  `𝔞`.
* `LieEquiv.map_positiveRestrictedRootSpace`: `θ 𝔫 = 𝔫⁻` for `𝔞 ⊆ 𝔭`.
* `Submodule.isNilpotent_ad_of_mem_positiveRestrictedRootSpace`,
  `Submodule.lieModule_isNilpotent_positiveRestrictedRootSubalgebra`,
  `Submodule.lieRing_isNilpotent_positiveRestrictedRootSubalgebra`: if the restricted root spaces
  span a torsion-free Noetherian `L` over a linearly ordered commutative ring, `ad x` is nilpotent
  for `x ∈ 𝔫`, `𝔫` acts nilpotently on `L`, and `𝔫` is a nilpotent Lie algebra.
* `LieEquiv.IsCartanInvolution.lieModule_isNilpotent_positiveRestrictedRootSubalgebra`,
  `LieEquiv.IsCartanInvolution.lieRing_isNilpotent_positiveRestrictedRootSubalgebra`: the same for
  a Cartan involution of a real Lie algebra and an abelian `𝔞 ⊆ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.40 and
  the definition of `𝔫` before Proposition 6.43.
-/

public section

open LieAlgebra Module

namespace Submodule

section Preorder

variable {R L : Type*} [CommRing R] [Preorder R] [LieRing L] [LieAlgebra R L]
  {𝔞 : Submodule R L} {H₀ : 𝔞} {μ : Dual R 𝔞} {x y : L}

/-- The positive restricted root space `𝔫 = ⊕_{λ ∈ Σ⁺} 𝔤_λ` of a submodule `𝔞` and `H₀ ∈ 𝔞`: the
sum of the restricted root spaces `𝔤_λ` of the restricted roots `λ` with `λ(H₀) > 0`. -/
def positiveRestrictedRootSpace (𝔞 : Submodule R L) (H₀ : 𝔞) : Submodule R L :=
  ⨆ (μ ∈ 𝔞.restrictedRoots) (_ : 0 < μ H₀), 𝔞.restrictedRootSpace μ

/-- `𝔫` is the sum of the restricted root spaces of all functionals positive at `H₀`: those that
are not restricted roots contribute `0`. -/
theorem positiveRestrictedRootSpace_eq_iSup :
    𝔞.positiveRestrictedRootSpace H₀ =
      ⨆ (μ : Dual R 𝔞) (_ : 0 < μ H₀), 𝔞.restrictedRootSpace μ := by
  refine le_antisymm (iSup₂_le fun μ _ ↦ iSup_le fun h ↦ le_iSup₂_of_le μ h le_rfl)
    (iSup₂_le fun μ h ↦ ?_)
  by_cases hbot : 𝔞.restrictedRootSpace μ = ⊥
  · exact hbot.le.trans bot_le
  have hμ : μ ≠ 0 := by
    rintro rfl
    exact lt_irrefl _ h
  exact le_iSup₂_of_le μ (mem_restrictedRoots.mpr ⟨hμ, hbot⟩) (le_iSup_of_le h le_rfl)

/-- `𝔫` contains the restricted root space of every functional positive at `H₀`. -/
theorem restrictedRootSpace_le_positiveRestrictedRootSpace (h : 0 < μ H₀) :
    𝔞.restrictedRootSpace μ ≤ 𝔞.positiveRestrictedRootSpace H₀ := by
  rw [positiveRestrictedRootSpace_eq_iSup]
  exact le_iSup₂_of_le μ h le_rfl

/-- `𝔫` lies in a submodule `N` exactly when `N` contains the restricted root space of every
functional positive at `H₀`. -/
theorem positiveRestrictedRootSpace_le_iff {N : Submodule R L} :
    𝔞.positiveRestrictedRootSpace H₀ ≤ N ↔
      ∀ μ : Dual R 𝔞, 0 < μ H₀ → 𝔞.restrictedRootSpace μ ≤ N := by
  rw [positiveRestrictedRootSpace_eq_iSup]
  exact iSup₂_le_iff

/-- A linear map sends `𝔫` into a submodule `N` when it sends the restricted root space of every
functional positive at `H₀` into `N`. -/
theorem apply_mem_of_mem_positiveRestrictedRootSpace {M : Type*} [AddCommGroup M] [Module R M]
    {N : Submodule R M} (f : L →ₗ[R] M)
    (hf : ∀ μ : Dual R 𝔞, 0 < μ H₀ → ∀ z ∈ 𝔞.restrictedRootSpace μ, f z ∈ N)
    (hy : y ∈ 𝔞.positiveRestrictedRootSpace H₀) : f y ∈ N :=
  mem_comap.mp <| positiveRestrictedRootSpace_le_iff.mpr
    (fun μ hμ z hz ↦ mem_comap.mpr (hf μ hμ z hz)) hy

/-- **`𝔞` normalizes `𝔫`**: `[x, y] ∈ 𝔫` for `x ∈ 𝔞` and `y ∈ 𝔫`. -/
theorem lie_mem_positiveRestrictedRootSpace_of_mem (hx : x ∈ 𝔞)
    (hy : y ∈ 𝔞.positiveRestrictedRootSpace H₀) :
    ⁅x, y⁆ ∈ 𝔞.positiveRestrictedRootSpace H₀ := by
  rw [← ad_apply R]
  refine apply_mem_of_mem_positiveRestrictedRootSpace _ (fun μ hμ z hz ↦ ?_) hy
  rw [ad_apply, mem_restrictedRootSpace.mp hz ⟨x, hx⟩]
  exact smul_mem _ _ (restrictedRootSpace_le_positiveRestrictedRootSpace hμ hz)

/-- The zero subspace has `𝔫 = 0`: it has no restricted roots. -/
@[simp]
theorem positiveRestrictedRootSpace_bot (H₀ : (⊥ : Submodule R L)) :
    (⊥ : Submodule R L).positiveRestrictedRootSpace H₀ = ⊥ := by
  simp [positiveRestrictedRootSpace]

/-- `𝔤_0` and `𝔫` are independent. -/
theorem disjoint_restrictedRootSpace_zero_positiveRestrictedRootSpace [IsDomain R]
    [IsTorsionFree R L] :
    Disjoint (𝔞.restrictedRootSpace 0) (𝔞.positiveRestrictedRootSpace H₀) := by
  refine (iSupIndep_restrictedRootSpace.disjoint_biSup (y := {μ | 0 < μ H₀})
    (by simp)).mono_right ?_
  exact positiveRestrictedRootSpace_le_iff.mpr fun μ hμ ↦ le_biSup _ hμ

/-- An abelian submodule `𝔞` and `𝔫` are independent. -/
theorem disjoint_positiveRestrictedRootSpace [IsDomain R] [IsTorsionFree R L]
    (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : Disjoint 𝔞 (𝔞.positiveRestrictedRootSpace H₀) :=
  disjoint_restrictedRootSpace_zero_positiveRestrictedRootSpace.mono_left
    (le_restrictedRootSpace_zero hab)

end Preorder

section OrderedRing

variable {R L : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [LieRing L]
  [LieAlgebra R L] {𝔞 : Submodule R L} {H₀ : 𝔞} {μ : Dual R 𝔞} {x y : L}

/-- **`[𝔤_μ, 𝔫] ⊆ 𝔫` for `μ(H₀) ≥ 0`**: the bracket raises the value at `H₀`. -/
theorem lie_mem_positiveRestrictedRootSpace_of_mem_restrictedRootSpace (hμ : 0 ≤ μ H₀)
    (hx : x ∈ 𝔞.restrictedRootSpace μ) (hy : y ∈ 𝔞.positiveRestrictedRootSpace H₀) :
    ⁅x, y⁆ ∈ 𝔞.positiveRestrictedRootSpace H₀ := by
  rw [← ad_apply R]
  refine apply_mem_of_mem_positiveRestrictedRootSpace _ (fun ν hν z hz ↦ ?_) hy
  rw [ad_apply]
  refine restrictedRootSpace_le_positiveRestrictedRootSpace ?_ (lie_mem_restrictedRootSpace hx hz)
  rw [LinearMap.add_apply]
  exact add_pos_of_nonneg_of_pos hμ hν

/-- **The centralizer `𝔤_0` of `𝔞` normalizes `𝔫`.** -/
theorem lie_mem_positiveRestrictedRootSpace_of_mem_restrictedRootSpace_zero
    (hx : x ∈ 𝔞.restrictedRootSpace 0) (hy : y ∈ 𝔞.positiveRestrictedRootSpace H₀) :
    ⁅x, y⁆ ∈ 𝔞.positiveRestrictedRootSpace H₀ :=
  lie_mem_positiveRestrictedRootSpace_of_mem_restrictedRootSpace le_rfl hx hy

/-- **`𝔫` is closed under the bracket.** -/
theorem lie_mem_positiveRestrictedRootSpace (hx : x ∈ 𝔞.positiveRestrictedRootSpace H₀)
    (hy : y ∈ 𝔞.positiveRestrictedRootSpace H₀) : ⁅x, y⁆ ∈ 𝔞.positiveRestrictedRootSpace H₀ := by
  rw [← lie_skew, neg_mem_iff, ← ad_apply R]
  refine apply_mem_of_mem_positiveRestrictedRootSpace _ (fun μ hμ z hz ↦ ?_) hx
  rw [ad_apply, ← lie_skew, neg_mem_iff]
  exact lie_mem_positiveRestrictedRootSpace_of_mem_restrictedRootSpace hμ.le hz hy

variable (𝔞 H₀) in
/-- The positive restricted root space `𝔫 = ⊕_{λ ∈ Σ⁺} 𝔤_λ` as a Lie subalgebra. -/
def positiveRestrictedRootSubalgebra : LieSubalgebra R L where
  toSubmodule := 𝔞.positiveRestrictedRootSpace H₀
  lie_mem' := lie_mem_positiveRestrictedRootSpace

@[simp]
theorem toSubmodule_positiveRestrictedRootSubalgebra :
    (𝔞.positiveRestrictedRootSubalgebra H₀).toSubmodule = 𝔞.positiveRestrictedRootSpace H₀ :=
  SetLike.ext fun _ ↦ Iff.rfl

@[simp]
theorem mem_positiveRestrictedRootSubalgebra :
    x ∈ 𝔞.positiveRestrictedRootSubalgebra H₀ ↔ x ∈ 𝔞.positiveRestrictedRootSpace H₀ :=
  Iff.rfl

/-- `𝔫⁻ = positiveRestrictedRootSpace 𝔞 (-H₀)` is the sum of the restricted root spaces of the
functionals negative at `H₀`. -/
theorem positiveRestrictedRootSpace_neg_le_iff {N : Submodule R L} :
    𝔞.positiveRestrictedRootSpace (-H₀) ≤ N ↔
      ∀ μ : Dual R 𝔞, μ H₀ < 0 → 𝔞.restrictedRootSpace μ ≤ N := by
  simp only [positiveRestrictedRootSpace_le_iff, map_neg, neg_pos]

/-- **`𝔤_0 + 𝔫` and `𝔫⁻` are independent**: the restricted root spaces of functionals with
`λ(H₀) ≥ 0` and with `λ(H₀) < 0` are independent. -/
theorem disjoint_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace [IsDomain R]
    [IsTorsionFree R L] :
    Disjoint (𝔞.restrictedRootSpace 0 ⊔ 𝔞.positiveRestrictedRootSpace H₀)
      (𝔞.positiveRestrictedRootSpace (-H₀)) := by
  refine (iSupIndep_restrictedRootSpace.disjoint_biSup_biSup
    (s := {μ | 0 ≤ μ H₀}) (t := {μ | μ H₀ < 0})
    (Set.disjoint_left.mpr fun μ h h' ↦ not_lt_of_ge h h')).mono
    (sup_le (le_biSup _ (by simp))
      (positiveRestrictedRootSpace_le_iff.mpr fun μ hμ ↦ le_biSup _ hμ.le))
    (positiveRestrictedRootSpace_neg_le_iff.mpr fun μ hμ ↦ le_biSup _ hμ)

end OrderedRing

/-! ### Nilpotence of `𝔫` -/

section LinearOrderedRing

variable {K L : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {𝔞 : Submodule K L} {H₀ : 𝔞} {ν : Dual K 𝔞} {x z : L}

/-- `ad x`, `x ∈ 𝔫`, carries `𝔤_ν` into the sum of the restricted root spaces of the functionals
whose value at `H₀` exceeds `ν(H₀)`. -/
private theorem lie_mem_iSup_lt_of_mem_positiveRestrictedRootSpace
    (hx : x ∈ 𝔞.positiveRestrictedRootSpace H₀) (hz : z ∈ 𝔞.restrictedRootSpace ν) :
    ⁅x, z⁆ ∈ ⨆ (μ : Dual K 𝔞) (_ : ν H₀ < μ H₀), 𝔞.restrictedRootSpace μ := by
  rw [← lie_skew, neg_mem_iff, ← ad_apply K]
  refine apply_mem_of_mem_positiveRestrictedRootSpace _ (fun μ hμ y hy ↦ ?_) hx
  have hlt : ν H₀ < (ν + μ) H₀ := by
    rw [LinearMap.add_apply]
    exact lt_add_of_pos_right _ hμ
  rw [ad_apply]
  exact mem_iSup_of_mem (ν + μ) (mem_iSup_of_mem hlt (lie_mem_restrictedRootSpace hz hy))

/-- **`ad x` is nilpotent for `x ∈ 𝔫`.** If the restricted root spaces of `𝔞` span a torsion-free
Noetherian Lie algebra `L` over a linearly ordered commutative ring, then `ad x` is nilpotent for
every `x` in the positive restricted root space `𝔫`. -/
theorem isNilpotent_ad_of_mem_positiveRestrictedRootSpace [IsTorsionFree K L] [IsNoetherian K L]
    (hspan : ⨆ μ : Dual K 𝔞, 𝔞.restrictedRootSpace μ = ⊤)
    (hx : x ∈ 𝔞.positiveRestrictedRootSpace H₀) : IsNilpotent (ad K L x) := by
  have hfin : {μ : Dual K 𝔞 | 𝔞.restrictedRootSpace μ ≠ ⊥}.Finite :=
    finite_ne_bot_of_iSupIndep iSupIndep_restrictedRootSpace
  set F := hfin.toFinset
  -- By induction on the number of nonzero restricted root spaces with value `> t` at `H₀`, a power
  -- of `ad x` bounded by that number kills their sum.
  have key (n : ℕ) : ∀ t : K, (F.filter (t < · H₀)).card ≤ n →
      ⨆ (μ : Dual K 𝔞) (_ : t < μ H₀), 𝔞.restrictedRootSpace μ ≤
        LinearMap.ker ((ad K L x) ^ n) := by
    induction n with
    | zero =>
      intro t ht
      refine iSup₂_le fun μ hμ ↦ ?_
      by_contra hbot
      have hmem : μ ∈ F.filter (t < · H₀) := by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, F]
        exact ⟨fun h ↦ hbot (h.le.trans bot_le), hμ⟩
      exact (Finset.card_pos.mpr ⟨μ, hmem⟩).ne' (Nat.le_zero.mp ht)
    | succ n ih =>
      intro t ht
      refine iSup₂_le fun μ hμ ↦ ?_
      by_cases hbot : 𝔞.restrictedRootSpace μ = ⊥
      · exact hbot.le.trans bot_le
      intro z hz
      have hsub : F.filter (μ H₀ < · H₀) ⊂ F.filter (t < · H₀) := by
        refine (Finset.ssubset_iff_of_subset fun ν h ↦ ?_).mpr ⟨μ, ?_, ?_⟩
        · simp only [Finset.mem_filter] at h ⊢
          exact ⟨h.1, hμ.trans h.2⟩
        · simp only [Finset.mem_filter, Set.Finite.mem_toFinset, F]
          exact ⟨hbot, hμ⟩
        · simp
      have hz' := ih (μ H₀) (by have := Finset.card_lt_card hsub; omega)
        (lie_mem_iSup_lt_of_mem_positiveRestrictedRootSpace hx hz)
      rw [LinearMap.mem_ker, pow_succ, mul_apply_eq_comp, ad_apply]
      exact LinearMap.mem_ker.mp hz'
  -- Take `t` below the value at `H₀` of every functional with nonzero restricted root space.
  obtain ⟨b, hb⟩ := (hfin.image fun μ ↦ μ H₀).bddBelow
  refine ⟨(F.filter ((b - 1) < · H₀)).card, LinearMap.ext fun y ↦ ?_⟩
  rw [LinearMap.zero_apply, ← LinearMap.mem_ker]
  refine key _ (b - 1) le_rfl ?_
  refine (hspan.symm.le.trans (iSup_le fun μ ↦ ?_)) mem_top
  by_cases hbot : 𝔞.restrictedRootSpace μ = ⊥
  · exact hbot.le.trans bot_le
  exact le_iSup₂_of_le μ ((sub_one_lt b).trans_le (hb ⟨μ, hbot, rfl⟩)) le_rfl

/-- **`𝔫` acts nilpotently on `L`.** If the restricted root spaces of `𝔞` span a torsion-free
Noetherian Lie algebra `L` over a linearly ordered commutative ring, the positive restricted root
subalgebra acts nilpotently on `L` by Engel's theorem. -/
theorem lieModule_isNilpotent_positiveRestrictedRootSubalgebra [IsTorsionFree K L]
    [IsNoetherian K L] (hspan : ⨆ μ : Dual K 𝔞, 𝔞.restrictedRootSpace μ = ⊤) :
    LieModule.IsNilpotent (𝔞.positiveRestrictedRootSubalgebra H₀) L := by
  refine (LieModule.isNilpotent_iff_forall' (R := K)).mpr fun x ↦ ?_
  convert isNilpotent_ad_of_mem_positiveRestrictedRootSpace (K := K) hspan x.property using 1
  ext y
  simp

/-- **`𝔫` is a nilpotent Lie algebra.** If the restricted root spaces of `𝔞` span a torsion-free
Noetherian Lie algebra `L` over a linearly ordered commutative ring, the positive restricted root
subalgebra is nilpotent. -/
theorem lieRing_isNilpotent_positiveRestrictedRootSubalgebra [IsTorsionFree K L] [IsNoetherian K L]
    (hspan : ⨆ μ : Dual K 𝔞, 𝔞.restrictedRootSpace μ = ⊤) :
    LieRing.IsNilpotent (𝔞.positiveRestrictedRootSubalgebra H₀) :=
  LieAlgebra.isNilpotent_iff_forall.mpr fun x ↦
    LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad _
      (isNilpotent_ad_of_mem_positiveRestrictedRootSpace hspan x.property)

end LinearOrderedRing

end Submodule

namespace LieEquiv

open Submodule

variable {R L : Type*} [CommRing R] [Preorder R] [LieRing L] [LieAlgebra R L] {θ : L ≃ₗ⁅R⁆ L}
  {𝔞 : Submodule R L}

/-- **`θ 𝔫 = 𝔫⁻`.** For `𝔞 ⊆ 𝔭`, an automorphism `θ` maps the positive restricted root space of
`H₀` onto that of `-H₀`, the sum of the restricted root spaces of the functionals negative at
`H₀`. -/
theorem map_positiveRestrictedRootSpace (h𝔞 : 𝔞 ≤ θ.cartanP) (H₀ : 𝔞) :
    (𝔞.positiveRestrictedRootSpace H₀).map (θ : L →ₗ[R] L) =
      𝔞.positiveRestrictedRootSpace (-H₀) := by
  simp only [positiveRestrictedRootSpace_eq_iSup, Submodule.map_iSup, map_restrictedRootSpace h𝔞]
  refine le_antisymm (iSup₂_le fun μ h ↦ le_iSup₂_of_le (-μ) (by simpa using h) le_rfl)
    (iSup₂_le fun μ h ↦ le_iSup₂_of_le (-μ) (by simpa using h) (by rw [neg_neg]))

end LieEquiv

namespace LieEquiv.IsCartanInvolution

open Submodule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- **`𝔫` acts nilpotently.** For a Cartan involution `θ` of a real Lie algebra and an abelian
subspace `𝔞` of `𝔭`, the positive restricted root subalgebra of any `H₀ ∈ 𝔞` acts nilpotently on
the Lie algebra. -/
theorem lieModule_isNilpotent_positiveRestrictedRootSubalgebra (hθ : θ.IsCartanInvolution)
    (h𝔞 : 𝔞 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) (H₀ : 𝔞) :
    LieModule.IsNilpotent (𝔞.positiveRestrictedRootSubalgebra H₀) L :=
  have := hθ.finiteDimensional
  Submodule.lieModule_isNilpotent_positiveRestrictedRootSubalgebra
    (hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab)

/-- **`𝔫` is a nilpotent Lie algebra.** For a Cartan involution `θ` of a real Lie algebra and an
abelian subspace `𝔞` of `𝔭`, the positive restricted root subalgebra of any `H₀ ∈ 𝔞` is
nilpotent. -/
theorem lieRing_isNilpotent_positiveRestrictedRootSubalgebra (hθ : θ.IsCartanInvolution)
    (h𝔞 : 𝔞 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) (H₀ : 𝔞) :
    LieRing.IsNilpotent (𝔞.positiveRestrictedRootSubalgebra H₀) :=
  have := hθ.finiteDimensional
  Submodule.lieRing_isNilpotent_positiveRestrictedRootSubalgebra
    (hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab)

end LieEquiv.IsCartanInvolution
