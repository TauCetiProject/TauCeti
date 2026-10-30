/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.FiniteCover
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Modules.Tilde
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Uniform vanishing of quasi-coherent cohomology on quasi-compact quasi-separated schemes

On a quasi-compact and quasi-separated scheme `X` there is a bound `N`, depending only on `X`,
such that `Hⁿ(X, F) = 0` for every quasi-coherent `F` and every `n ≥ N`. Consequently, for a
quasi-compact and quasi-separated morphism `f : X ⟶ S` to an affine scheme, the cohomology of
quasi-coherent modules on `X` vanishes in a range depending only on `f`, and the higher direct
images `Rⁿ f_* F` of quasi-coherent modules vanish in such a range when `S` is quasi-compact.
Over a base that is not quasi-compact no uniform bound need exist. For an affine open `U` of an
arbitrary base, the preimage `f⁻¹ U` is a quasi-compact quasi-separated open
(`Scheme.Hom.isCompact_preimage`, `Scheme.Hom.isQuasiSeparated_preimage`), so
`Scheme.Modules.exists_subsingleton_cohomologyOn_of_isCompact` bounds the cohomology there.

The proof follows the Stacks Project. A quasi-compact open `W` of an affine open `U` is a finite
union of `r` basic opens of `U`; their finite intersections are again basic opens, hence affine,
so Serre's vanishing theorem and the bound for finite Leray covers give `Hⁿ(W, F) = 0` for
`n ≥ r`. A quasi-compact open of a quasi-separated scheme is a finite union of affine opens. If
`Hⁿ(W, F)` vanishes for `n ≥ N₁` and `Hⁿ(W ⊓ U, F)` for `n ≥ N₂`, where `U` is an affine open,
then the Mayer–Vietoris sequence makes `Hⁿ(W ⊔ U, F)` vanish for `n ≥ max N₁ (N₂ + 1)`.
Quasi-separation makes `W ⊓ U` a quasi-compact open of the affine open `U`, which is the first
case. Both steps survive intersecting with the basic open `D(g)` of a section `g` over an open
containing `W`, so the bounds hold uniformly on `W ⊓ D(g)`. The preimage of a basic open of an
affine open `U` of the base is such a basic open of `f⁻¹ U`, and when the base is quasi-compact
finitely many affine opens `U` suffice for their basic opens to form a basis, so this uniformity
makes the higher direct images vanish.

## Main declarations

* `Scheme.Modules.exists_subsingleton_cohomologyOn_inf_basicOpen_of_le_isAffineOpen`:
  a uniform vanishing bound for quasi-coherent cohomology on `W ⊓ D(g)`, for `W` a quasi-compact
  open contained in an affine open and `g` a section over an open containing `W`;
* `Scheme.Modules.exists_subsingleton_cohomologyOn_inf_basicOpen_of_isCompact`:
  a uniform vanishing bound on `W ⊓ D(g)`, for `W` a quasi-compact and quasi-separated open, and
  its case `g = 1`, `Scheme.Modules.exists_subsingleton_cohomologyOn_of_isCompact`;
* `Scheme.Modules.exists_subsingleton_cohomology`: a uniform vanishing bound on a quasi-compact
  quasi-separated scheme;
* `Scheme.Hom.exists_subsingleton_cohomology_of_isAffine`: the bound for the source of a
  quasi-compact quasi-separated morphism to an affine scheme;
* `Scheme.Hom.exists_isZero_higherDirectImage`: the higher direct images along a quasi-compact
  quasi-separated morphism to a quasi-compact scheme vanish in a range depending only on the
  morphism.

## References

* The Stacks Project, Lemmas 30.4.2–30.4.6 (tag 01XH).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Uniform vanishing on a quasi-compact open of an affine open.** Let `W` be a quasi-compact
open contained in an affine open `U` of a scheme `X`. Then there is a bound `N`, independent of
the coefficients and of the section `g` over an open `V ⊇ W`, such that `Hⁿ(W ∩ D(g), M) = 0` for
every quasi-coherent `M` and every `n ≥ N`. Stacks, Lemma 30.4.2 (01XD). -/
theorem exists_subsingleton_cohomologyOn_inf_basicOpen_of_le_isAffineOpen {U W : X.Opens}
    (hU : IsAffineOpen U) (hW : IsCompact (W : Set X)) (hWU : W ≤ U) :
    ∃ N : ℕ, ∀ (V : X.Opens), W ≤ V → ∀ (g : Γ(X, V)) (M : X.Modules) [M.IsQuasicoherent]
      (n : ℕ), N ≤ n → Subsingleton (cohomologyOn M n (W ⊓ X.basicOpen g)) := by
  classical
  -- Cover `W` by finitely many basic opens of `U` contained in `W`.
  let ι := {f : Γ(X, U) // X.basicOpen f ≤ W}
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover (fun i : ι ↦ (X.basicOpen i.1 : Set X))
    (fun i ↦ (X.basicOpen i.1).isOpen) fun x hx ↦ by
      obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩
  have hsW : s.sup (fun i : ι ↦ X.basicOpen i.1) = W := by
    refine le_antisymm (Finset.sup_le fun i _ ↦ i.2) fun x hx ↦ ?_
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (Finset.le_sup (f := fun i : ι ↦ X.basicOpen i.1) hi) hxi
  rcases s.eq_empty_or_nonempty with rfl | hne
  · -- The empty open is affine.
    refine ⟨1, fun V _ g M _ n hn ↦ ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hsW, Finset.sup_empty, bot_inf_eq]
    exact subsingleton_cohomologyOn_succ_of_isAffineOpen M (isAffineOpen_bot X) m
  refine ⟨s.card, fun V hWV g M _ n hn ↦ ?_⟩
  have hsW' : s.sup (fun i : ι ↦ X.basicOpen i.1 ⊓ X.basicOpen g) = W ⊓ X.basicOpen g := by
    rw [← Finset.sup_inf_distrib_right, hsW]
  rw [← hsW']
  refine subsingleton_cohomologyOn_sup_of_card_le M hne _ (fun t _ ht i ↦ ?_) n hn
  -- A nonempty finite intersection of basic opens of `U` is a basic open `D(f)` of `U`, and
  -- `D(f) ⊓ D(g)` is the basic open of the affine open `D(f) ⊆ V` cut out by `g`.
  obtain ⟨f, hf⟩ : t.inf (fun i : ι ↦ X.basicOpen i.1) ∈
      Set.range fun f : Γ(X, U) ↦ X.basicOpen f := by
    rw [← Finset.inf'_eq_inf ht]
    exact Finset.inf'_mem _ Scheme.inf_mem_range_basicOpen _ ht _ fun i _ ↦ ⟨i.1, rfl⟩
  obtain ⟨j, hj⟩ := ht
  have hfV : X.basicOpen f ≤ V := by
    rw [show X.basicOpen f = _ from hf]
    exact (Finset.inf_le hj).trans (j.2.trans hWV)
  have hinf : t.inf (fun i : ι ↦ X.basicOpen i.1 ⊓ X.basicOpen g) =
      t.inf (fun i : ι ↦ X.basicOpen i.1) ⊓ X.basicOpen g :=
    (Finset.inf_inf (f := fun i : ι ↦ X.basicOpen i.1) (g := fun _ ↦ X.basicOpen g)).trans
      (congrArg _ (Finset.inf_const ⟨j, hj⟩ _))
  rw [hinf, ← show X.basicOpen f = _ from hf, ← Scheme.basicOpen_res X g (homOfLE hfV).op]
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M ((hU.basicOpen f).basicOpen _) i

/-- **Uniform vanishing on a quasi-compact quasi-separated open.** If `W` is a quasi-compact and
quasi-separated open of a scheme `X`, there is a bound `N`, independent of the coefficients and
of the section `g` over an open `V ⊇ W`, such that `Hⁿ(W ∩ D(g), M) = 0` for every
quasi-coherent `M` and every `n ≥ N`. Stacks, Section 30.4 (01XH). -/
theorem exists_subsingleton_cohomologyOn_inf_basicOpen_of_isCompact {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) :
    ∃ N : ℕ, ∀ (V : X.Opens), W ≤ V → ∀ (g : Γ(X, V)) (M : X.Modules) [M.IsQuasicoherent]
      (n : ℕ), N ≤ n → Subsingleton (cohomologyOn M n (W ⊓ X.basicOpen g)) := by
  revert hW'
  refine compact_open_induction_on (P := fun W ↦ IsQuasiSeparated (W : Set X) → ∃ N : ℕ,
    ∀ (V : X.Opens), W ≤ V → ∀ (g : Γ(X, V)) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ),
      N ≤ n → Subsingleton (cohomologyOn M n (W ⊓ X.basicOpen g))) W hW
    (fun _ ↦ exists_subsingleton_cohomologyOn_inf_basicOpen_of_le_isAffineOpen
      (isAffineOpen_bot X) isCompact_empty le_rfl) fun W hW U ih hWU' ↦ ?_
  obtain ⟨N₁, hN₁⟩ := ih (hWU'.of_subset Set.subset_union_left)
  -- By quasi-separation, `W ⊓ U` is a quasi-compact open of the affine open `U`.
  obtain ⟨N₂, hN₂⟩ := exists_subsingleton_cohomologyOn_inf_basicOpen_of_le_isAffineOpen U.2
    (hWU' _ _ Set.subset_union_left W.isOpen hW Set.subset_union_right U.1.isOpen U.2.isCompact)
    (inf_le_right : W ⊓ U.1 ≤ U.1)
  refine ⟨max N₁ (N₂ + 1), fun V hV g M _ n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- `U ⊓ D(g)` is a basic open of the affine open `U`.
  have hUg : IsAffineOpen (U.1 ⊓ X.basicOpen g) := by
    rw [← Scheme.basicOpen_res X g (homOfLE (le_sup_right.trans hV)).op]
    exact U.2.basicOpen _
  rw [inf_sup_right]
  refine subsingleton_cohomologyOn_sup_succ M m ?_
    (hN₁ V (le_sup_left.trans hV) g M (m + 1) (by omega))
    (subsingleton_cohomologyOn_succ_of_isAffineOpen M hUg m)
  rw [inf_inf_inf_comm, inf_idem]
  exact hN₂ V (inf_le_left.trans (le_sup_left.trans hV)) g M m (by omega)

/-- **Uniform vanishing on a quasi-compact quasi-separated open.** If `W` is a quasi-compact and
quasi-separated open of a scheme `X`, there is a bound `N`, independent of the coefficients, such
that `Hⁿ(W, M) = 0` for every quasi-coherent `M` and every `n ≥ N`. Stacks, Section 30.4
(01XH). -/
theorem exists_subsingleton_cohomologyOn_of_isCompact {W : X.Opens} (hW : IsCompact (W : Set X))
    (hW' : IsQuasiSeparated (W : Set X)) :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (cohomologyOn M n W) := by
  obtain ⟨N, hN⟩ := exists_subsingleton_cohomologyOn_inf_basicOpen_of_isCompact hW hW'
  exact ⟨N, fun M _ n hn ↦ by
    simpa only [Scheme.basicOpen_one, inf_top_eq] using hN ⊤ le_top 1 M n hn⟩

/-- **Uniform vanishing on a quasi-compact quasi-separated scheme.** On a quasi-compact and
quasi-separated scheme `X` there is a bound `N` such that `Hⁿ(X, M) = 0` for every quasi-coherent
`M` and every `n ≥ N`. Stacks, Section 30.4 (01XH). -/
theorem exists_subsingleton_cohomology (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), N ≤ n →
      Subsingleton (Cohomology M n) := by
  obtain ⟨N, hN⟩ := exists_subsingleton_cohomologyOn_of_isCompact (X := X) (W := ⊤)
    isCompact_univ (.of_quasiSeparatedSpace _)
  exact ⟨N, fun M _ n hn ↦ have := hN M n hn
    (cohomologyOnTopIso M n).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

/-- **Uniform vanishing over an affine base.** For a quasi-compact and quasi-separated morphism
`f : X ⟶ S` to an affine scheme, the cohomology of quasi-coherent modules on `X` vanishes in a
range depending only on `f`. Stacks, Lemmas 30.4.1–30.4.6 (01XH). -/
theorem exists_subsingleton_cohomology_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      Subsingleton (Cohomology F p) := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := quasiSeparatedSpace_of_quasiSeparated f
  exact Modules.exists_subsingleton_cohomology X

/-- **Uniform vanishing of higher direct images over a quasi-compact base.** For a quasi-compact
and quasi-separated morphism `f : X ⟶ S` to a quasi-compact scheme, the higher direct images
`Rᵖ f_* F` of quasi-coherent modules vanish in a range depending only on `f`. Stacks, Section 30.4
(01XH). -/
theorem exists_isZero_higherDirectImage {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (p : ℕ), N ≤ p →
      IsZero ((f.higherDirectImage p).obj F) := by
  obtain ⟨s, hs, hsS⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens (X := S) (U := ⊤).mp isCompact_univ
  -- A bound on the basic opens of the preimage of each affine open of `S`.
  choose N hN using fun U : S.affineOpens ↦
    Modules.exists_subsingleton_cohomologyOn_inf_basicOpen_of_isCompact (X := X) (W := f ⁻¹ᵁ U.1)
      (f.isCompact_preimage U.2.isCompact) (f.isQuasiSeparated_preimage U.2.isQuasiSeparated)
  obtain ⟨M, hM⟩ := (hs.image N).bddAbove
  refine ⟨max M 1, fun F _ p hp ↦ ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  -- The basic opens of the affine opens in `s` form a basis of `S`.
  have hB : Opens.IsBasis {V : S.Opens | ∃ U ∈ s, ∃ r : Γ(S, U.1), S.basicOpen r = V} := by
    refine Opens.isBasis_iff_nbhd.mpr fun {O x} hx ↦ ?_
    obtain ⟨U, hU, hxU⟩ : ∃ U ∈ s, x ∈ U.1 := by
      have : x ∈ (⊤ : S.Opens) := trivial
      rw [hsS] at this
      simpa using this
    obtain ⟨r, hr, hxr⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
    exact ⟨_, ⟨U, hU, r, rfl⟩, hxr, hr⟩
  refine f.isZero_higherDirectImage_succ_of_isBasis F q hB ?_
  -- The preimage of `D(r)` is the basic open `D(f^* r)` of `f⁻¹ U`, where the bound holds.
  rintro _ ⟨U, hU, r, rfl⟩
  rw [Scheme.preimage_basicOpen, ← inf_eq_right.mpr (X.basicOpen_le (f.app U.1 r))]
  exact hN U _ le_rfl _ F (q + 1) (by have := hM ⟨U, hU, rfl⟩; omega)

end AlgebraicGeometry.Scheme.Hom
