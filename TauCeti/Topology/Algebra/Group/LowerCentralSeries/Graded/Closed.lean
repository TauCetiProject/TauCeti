/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Closed
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# The graded bracket of the closed lower central series

The successive quotients of the closed lower central series are the case `p = 0` of Tau Ceti's
graded pieces for the lower `p`-series. This file gives that specialization its consumer-facing
names; its commutator formula is `gradedBracket_gradedMk`.

For a pro-`p` group, taking a `p`-adic power in either argument of a commutator acts on its class
by the same `p`-adic exponent. Thus the canonical `ℤ_p`-module structures on the graded pieces
make the bracket `ℤ_p`-bilinear.

## Main definitions

* `TauCeti.lcsGradedPiece`: the successive quotient `γ_n(G) / γ_{n+1}(G)`, written additively.
* `TauCeti.lcsGradedMk`: the class of an element of `γ_n(G)`.
* `TauCeti.lcsBracket`: the bracket induced by the group commutator.

## Main results

* `TauCeti.lcsGradedMk_conj`: conjugation is trivial on each graded piece.
* `TauCeti.lcsBracket_natural`: the bracket is natural in continuous homomorphisms.
* `TauCeti.IsProP.lcsGradedMk_padicPow`: a `p`-adic power becomes scalar multiplication on a
  graded piece.
* `TauCeti.lcsBracket_padicPow_left`, `TauCeti.lcsBracket_padicPow_right`: a `p`-adic power in
  either argument becomes the same power of the bracket class.
* `TauCeti.IsProP.lcsBracket_smul_left`, `TauCeti.IsProP.lcsBracket_smul_right`: the bracket is
  `ℤ_p`-linear in each variable.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `n`-th graded piece of the closed lower central series, written additively. -/
abbrev lcsGradedPiece (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Type u :=
  gradedPiece 0 G n

/-- The class in `γ_n(G) / γ_{n+1}(G)` of an element of `γ_n(G)`. -/
abbrev lcsGradedMk (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (x : closedLowerCentralSeries G n) : lcsGradedPiece G n :=
  gradedMk 0 G n ⟨x, by rw [← closedLowerCentralSeries_def]; exact x.2⟩

/-- Conjugation acts trivially on every graded piece of the closed lower central series. -/
@[simp]
theorem lcsGradedMk_conj (n : ℕ) (g : G) (x : closedLowerCentralSeries G n) :
    lcsGradedMk G n
        ⟨g * x * g⁻¹, (closedLowerCentralSeries_normal (G := G) n).conj_mem x x.2 g⟩ =
      lcsGradedMk G n x := by
  rw [gradedMk_eq_gradedMk_iff]
  exact mk_conj_of_mem_pLowerCentralSeries
    (closedLowerCentralSeries_def G n ▸ x.2) g

/-- The bracket on the graded pieces of the closed lower central series. Its degree is
`j + k + 1` because the series is indexed from zero. -/
abbrev lcsBracket (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (j k : ℕ) (x : lcsGradedPiece G j) (y : lcsGradedPiece G k) :
    lcsGradedPiece G (j + k + 1) :=
  gradedBracket 0 G j k x y

/-- The closed-series bracket on classes is represented by the group commutator. -/
theorem lcsBracket_mk {j k : ℕ} (x : closedLowerCentralSeries G j)
    (y : closedLowerCentralSeries G k) :
    lcsBracket G j k (lcsGradedMk G j x) (lcsGradedMk G k y) =
      lcsGradedMk G (j + k + 1)
        ⟨⁅(x : G), (y : G)⁆,
          (commutator_closedLowerCentralSeries_le j k)
            (Subgroup.commutator_mem_commutator x.2 y.2)⟩ := by
  rw [lcsBracket, lcsGradedMk, lcsGradedMk, gradedBracket_gradedMk]

/-- The closed-series bracket is additive in its first argument. -/
@[simp]
theorem lcsBracket_add_left {j k : ℕ} (x x' : lcsGradedPiece G j)
    (y : lcsGradedPiece G k) :
    lcsBracket G j k (x + x') y = lcsBracket G j k x y + lcsBracket G j k x' y := by
  simp only [lcsBracket, map_add, AddMonoidHom.add_apply]

/-- The closed-series bracket is additive in its second argument. -/
@[simp]
theorem lcsBracket_add_right {j k : ℕ} (x : lcsGradedPiece G j)
    (y y' : lcsGradedPiece G k) :
    lcsBracket G j k x (y + y') = lcsBracket G j k x y + lcsBracket G j k x y' := by
  simp only [lcsBracket, map_add]

/-- **Naturality of the closed-series bracket**: the graded maps induced by a continuous
homomorphism commute with the bracket. -/
theorem lcsBracket_natural {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) {j k : ℕ} (x : lcsGradedPiece G j)
    (y : lcsGradedPiece G k) :
    gradedMap 0 f hf (j + k + 1) (lcsBracket G j k x y) =
      lcsBracket H j k (gradedMap 0 f hf j x) (gradedMap 0 f hf k y) :=
  gradedMap_gradedBracket f hf x y

section PadicPow

variable {p : ℕ} [Fact p.Prime] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The canonical `ℤ_p`-module structure on a graded piece of the closed lower central series
of a pro-`p` group. It is the module structure on the abelian pro-`p` quotient
`γ_n(G) / γ_{n+1}(G)`. -/
@[instance_reducible]
noncomputable def IsProP.lcsGradedPieceModule (hG : IsProP p G) (n : ℕ) :
    Module ℤ_[p] (lcsGradedPiece G n) := by
  let R := pLowerCentralSeries 0 G n
  let N := (pLowerCentralSeries 0 G (n + 1)).subgroupOf R
  let _ : IsClosed (R : Set G) := isClosed_pLowerCentralSeries n
  let _ : IsClosed (N : Set R) := by
    rw [isClosed_induced_iff]
    exact ⟨pLowerCentralSeries 0 G (n + 1), isClosed_pLowerCentralSeries (n + 1), rfl⟩
  exact ((hG.subgroup R).quotient N).module

/-- In a pro-`p` group, the class of a `p`-adic power in a closed-series graded piece is the
corresponding `ℤ_p`-scalar multiple. -/
@[simp]
theorem IsProP.lcsGradedMk_padicPow (hG : IsProP p G) {n : ℕ}
    (x : closedLowerCentralSeries G n) (u : ℤ_[p]) :
    letI := hG.lcsGradedPieceModule n
    lcsGradedMk G n
        ⟨hG.padicPow (x : G) u,
          hG.padicPow_mem (isClosed_closedLowerCentralSeries n) x.2 u⟩ =
      u • lcsGradedMk G n x := by
  let R := pLowerCentralSeries 0 G n
  let N := (pLowerCentralSeries 0 G (n + 1)).subgroupOf R
  let _ : IsClosed (R : Set G) := isClosed_pLowerCentralSeries n
  let _ : IsClosed (N : Set R) := by
    rw [isClosed_induced_iff]
    exact ⟨pLowerCentralSeries 0 G (n + 1), isClosed_pLowerCentralSeries (n + 1), rfl⟩
  let hR : IsProP p R := hG.subgroup R
  let xR : R := ⟨x, by
    -- `R` is the lower-`p` spelling of the sealed closed-series term.
    change (x : G) ∈ pLowerCentralSeries 0 G n
    rw [← closedLowerCentralSeries_def]
    exact x.2⟩
  let xuR : R := ⟨hG.padicPow (x : G) u,
    by
      -- `R` is the lower-`p` spelling of the sealed closed-series term.
      change hG.padicPow (x : G) u ∈ pLowerCentralSeries 0 G n
      rw [← closedLowerCentralSeries_def]
      exact hG.padicPow_mem (isClosed_closedLowerCentralSeries n) x.2 u⟩
  have hpow : hR.padicPow xR u = xuR := by
    apply Subtype.ext
    exact hR.map_padicPow hG R.subtype continuous_subtype_val xR u
  let _ : Module ℤ_[p] (lcsGradedPiece G n) := hG.lcsGradedPieceModule n
  rw [lcsGradedMk, gradedMk_def, lcsGradedMk, gradedMk_def]
  -- Expose the subgroup quotient underlying the sealed graded class map.
  change Additive.ofMul (QuotientGroup.mk xuR : R ⧸ N) =
    u • Additive.ofMul (QuotientGroup.mk xR : R ⧸ N)
  rw [← hpow]
  exact hR.ofMul_mk_padicPow_quotient N xR u

/-- Modulo `γ_{j+k+2}`, taking a `p`-adic power in the left input of a commutator is the same
as taking that power of the commutator. -/
theorem IsProP.mk_commutatorElement_padicPow_left (hG : IsProP p G) {j k : ℕ}
    (x : closedLowerCentralSeries G j) (y : closedLowerCentralSeries G k) (u : ℤ_[p]) :
    ((⁅hG.padicPow (x : G) u, (y : G)⁆ : G) :
        G ⧸ pLowerCentralSeries 0 G (j + k + 1 + 1)) =
      ((hG.padicPow ⁅(x : G), (y : G)⁆ u : G) :
        G ⧸ pLowerCentralSeries 0 G (j + k + 1 + 1)) := by
  let N := pLowerCentralSeries 0 G (j + k + 1 + 1)
  let _ : IsClosed (N : Set G) := isClosed_pLowerCentralSeries _
  have hpow (z : G) : Continuous fun a : ℤ_[p] ↦ hG.padicPow z a :=
    hG.continuous_padicPow.comp (continuous_id.prodMk continuous_const)
  have hleft : Continuous fun a : ℤ_[p] ↦
      ((⁅hG.padicPow (x : G) a, (y : G)⁆ : G) : G ⧸ N) := by
    apply QuotientGroup.continuous_mk.comp
    have hxy : Continuous fun a : ℤ_[p] ↦ hG.padicPow (x : G) a * (y : G) :=
      (hpow x).mul continuous_const
    have hxyx : Continuous fun a : ℤ_[p] ↦
        hG.padicPow (x : G) a * (y : G) * (hG.padicPow (x : G) a)⁻¹ :=
      hxy.mul (hpow x).inv
    exact (hxyx.mul continuous_const).congr fun _ ↦ rfl
  have hright : Continuous fun a : ℤ_[p] ↦
      ((hG.padicPow ⁅(x : G), (y : G)⁆ a : G) : G ⧸ N) := by
    exact QuotientGroup.continuous_mk.comp (hpow _)
  apply congrFun (PadicInt.denseRange_natCast.equalizer hleft hright ?_) u
  funext n
  simp only [Function.comp_apply, hG.padicPow_natCast]
  have hx : (x : G) ∈ pLowerCentralSeries 0 G j := by
    rw [← closedLowerCentralSeries_def]
    exact x.2
  have hy : (y : G) ∈ pLowerCentralSeries 0 G k := by
    rw [← closedLowerCentralSeries_def]
    exact y.2
  have hcomm : Commute ((x : G) : G ⧸ N)
      ⁅((x : G) : G ⧸ N), ((y : G) : G ⧸ N)⁆ := by
    simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries hx hy) (x : G)
  -- Restate coercions as the quotient homomorphism so its map lemmas apply.
  change QuotientGroup.mk' N ⁅(x : G) ^ n, (y : G)⁆ =
    QuotientGroup.mk' N (⁅(x : G), (y : G)⁆ ^ n)
  rw [map_pow, map_commutatorElement]
  exact (hcomm.commutatorElement_pow_left n).symm

/-- Modulo `γ_{j+k+2}`, taking a `p`-adic power in the right input of a commutator is the same
as taking that power of the commutator. -/
theorem IsProP.mk_commutatorElement_padicPow_right (hG : IsProP p G) {j k : ℕ}
    (x : closedLowerCentralSeries G j) (y : closedLowerCentralSeries G k) (u : ℤ_[p]) :
    ((⁅(x : G), hG.padicPow (y : G) u⁆ : G) :
        G ⧸ pLowerCentralSeries 0 G (j + k + 1 + 1)) =
      ((hG.padicPow ⁅(x : G), (y : G)⁆ u : G) :
        G ⧸ pLowerCentralSeries 0 G (j + k + 1 + 1)) := by
  let N := pLowerCentralSeries 0 G (j + k + 1 + 1)
  let _ : IsClosed (N : Set G) := isClosed_pLowerCentralSeries _
  have hpow (z : G) : Continuous fun a : ℤ_[p] ↦ hG.padicPow z a :=
    hG.continuous_padicPow.comp (continuous_id.prodMk continuous_const)
  have hleft : Continuous fun a : ℤ_[p] ↦
      ((⁅(x : G), hG.padicPow (y : G) a⁆ : G) : G ⧸ N) := by
    apply QuotientGroup.continuous_mk.comp
    have hxy : Continuous fun a : ℤ_[p] ↦ (x : G) * hG.padicPow (y : G) a :=
      continuous_const.mul (hpow y)
    have hxyx : Continuous fun a : ℤ_[p] ↦
        (x : G) * hG.padicPow (y : G) a * (x : G)⁻¹ :=
      hxy.mul continuous_const
    exact (hxyx.mul (hpow y).inv).congr fun _ ↦ rfl
  have hright : Continuous fun a : ℤ_[p] ↦
      ((hG.padicPow ⁅(x : G), (y : G)⁆ a : G) : G ⧸ N) := by
    exact QuotientGroup.continuous_mk.comp (hpow _)
  apply congrFun (PadicInt.denseRange_natCast.equalizer hleft hright ?_) u
  funext n
  simp only [Function.comp_apply, hG.padicPow_natCast]
  have hx : (x : G) ∈ pLowerCentralSeries 0 G j := by
    rw [← closedLowerCentralSeries_def]
    exact x.2
  have hy : (y : G) ∈ pLowerCentralSeries 0 G k := by
    rw [← closedLowerCentralSeries_def]
    exact y.2
  have hcomm : Commute ((y : G) : G ⧸ N)
      ⁅((x : G) : G ⧸ N), ((y : G) : G ⧸ N)⁆ := by
    simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries hx hy) (y : G)
  -- Restate coercions as the quotient homomorphism so its map lemmas apply.
  change QuotientGroup.mk' N ⁅(x : G), (y : G) ^ n⁆ =
    QuotientGroup.mk' N (⁅(x : G), (y : G)⁆ ^ n)
  rw [map_pow, map_commutatorElement]
  exact (hcomm.commutatorElement_pow_right n).symm

/-- Taking a `p`-adic power in the first argument of the closed-series bracket takes the same
power of the bracket class. This is `ℤ_p`-linearity in the first variable on representatives. -/
theorem lcsBracket_padicPow_left (hG : IsProP p G) {j k : ℕ}
    (x : closedLowerCentralSeries G j) (y : closedLowerCentralSeries G k) (u : ℤ_[p]) :
    ∃ hx : hG.padicPow (x : G) u ∈ closedLowerCentralSeries G j,
    ∃ hxy : hG.padicPow ⁅(x : G), (y : G)⁆ u ∈ closedLowerCentralSeries G (j + k + 1),
      lcsBracket G j k (lcsGradedMk G j ⟨_, hx⟩) (lcsGradedMk G k y) =
        lcsGradedMk G (j + k + 1) ⟨_, hxy⟩ := by
  refine ⟨hG.padicPow_mem (isClosed_closedLowerCentralSeries j) x.2 u,
    hG.padicPow_mem (isClosed_closedLowerCentralSeries (j + k + 1))
      ((commutator_closedLowerCentralSeries_le j k)
        (Subgroup.commutator_mem_commutator x.2 y.2)) u, ?_⟩
  rw [lcsBracket, lcsGradedMk, gradedBracket_gradedMk, gradedMk_eq_gradedMk_iff]
  exact hG.mk_commutatorElement_padicPow_left x y u

/-- Taking a `p`-adic power in the second argument of the closed-series bracket takes the same
power of the bracket class. This is `ℤ_p`-linearity in the second variable on representatives. -/
theorem lcsBracket_padicPow_right (hG : IsProP p G) {j k : ℕ}
    (x : closedLowerCentralSeries G j) (y : closedLowerCentralSeries G k) (u : ℤ_[p]) :
    ∃ hy : hG.padicPow (y : G) u ∈ closedLowerCentralSeries G k,
    ∃ hxy : hG.padicPow ⁅(x : G), (y : G)⁆ u ∈ closedLowerCentralSeries G (j + k + 1),
      lcsBracket G j k (lcsGradedMk G j x) (lcsGradedMk G k ⟨_, hy⟩) =
        lcsGradedMk G (j + k + 1) ⟨_, hxy⟩ := by
  refine ⟨hG.padicPow_mem (isClosed_closedLowerCentralSeries k) y.2 u,
    hG.padicPow_mem (isClosed_closedLowerCentralSeries (j + k + 1))
      ((commutator_closedLowerCentralSeries_le j k)
        (Subgroup.commutator_mem_commutator x.2 y.2)) u, ?_⟩
  rw [lcsBracket, lcsGradedMk, gradedBracket_gradedMk, gradedMk_eq_gradedMk_iff]
  exact hG.mk_commutatorElement_padicPow_right x y u

/-- The closed-series bracket of a pro-`p` group is `ℤ_p`-linear in its first argument. -/
theorem IsProP.lcsBracket_smul_left (hG : IsProP p G) {j k : ℕ} (u : ℤ_[p])
    (x : lcsGradedPiece G j) (y : lcsGradedPiece G k) :
    letI := hG.lcsGradedPieceModule j
    letI := hG.lcsGradedPieceModule k
    letI := hG.lcsGradedPieceModule (j + k + 1)
    lcsBracket G j k (u • x) y = u • lcsBracket G j k x y := by
  let _ : Module ℤ_[p] (lcsGradedPiece G j) := hG.lcsGradedPieceModule j
  let _ : Module ℤ_[p] (lcsGradedPiece G k) := hG.lcsGradedPieceModule k
  let _ : Module ℤ_[p] (lcsGradedPiece G (j + k + 1)) :=
    hG.lcsGradedPieceModule (j + k + 1)
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  let xc : closedLowerCentralSeries G j := ⟨x, by
    rw [closedLowerCentralSeries_def]
    exact x.2⟩
  let yc : closedLowerCentralSeries G k := ⟨y, by
    rw [closedLowerCentralSeries_def]
    exact y.2⟩
  -- Replace the generic surjective representatives by the closed-series class map.
  change lcsBracket G j k (u • lcsGradedMk G j xc) (lcsGradedMk G k yc) =
    u • lcsBracket G j k (lcsGradedMk G j xc) (lcsGradedMk G k yc)
  rw [← hG.lcsGradedMk_padicPow xc u]
  obtain ⟨_, _, hbracket⟩ := lcsBracket_padicPow_left hG xc yc u
  rw [hbracket]
  let c : closedLowerCentralSeries G (j + k + 1) :=
    ⟨⁅(xc : G), (yc : G)⁆,
      (commutator_closedLowerCentralSeries_le j k)
        (Subgroup.commutator_mem_commutator xc.2 yc.2)⟩
  rw [lcsBracket, lcsGradedMk, gradedBracket_gradedMk]
  simpa only [c] using hG.lcsGradedMk_padicPow c u

/-- The closed-series bracket of a pro-`p` group is `ℤ_p`-linear in its second argument. -/
theorem IsProP.lcsBracket_smul_right (hG : IsProP p G) {j k : ℕ} (u : ℤ_[p])
    (x : lcsGradedPiece G j) (y : lcsGradedPiece G k) :
    letI := hG.lcsGradedPieceModule j
    letI := hG.lcsGradedPieceModule k
    letI := hG.lcsGradedPieceModule (j + k + 1)
    lcsBracket G j k x (u • y) = u • lcsBracket G j k x y := by
  let _ : Module ℤ_[p] (lcsGradedPiece G j) := hG.lcsGradedPieceModule j
  let _ : Module ℤ_[p] (lcsGradedPiece G k) := hG.lcsGradedPieceModule k
  let _ : Module ℤ_[p] (lcsGradedPiece G (j + k + 1)) :=
    hG.lcsGradedPieceModule (j + k + 1)
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  let xc : closedLowerCentralSeries G j := ⟨x, by
    rw [closedLowerCentralSeries_def]
    exact x.2⟩
  let yc : closedLowerCentralSeries G k := ⟨y, by
    rw [closedLowerCentralSeries_def]
    exact y.2⟩
  -- Replace the generic surjective representatives by the closed-series class map.
  change lcsBracket G j k (lcsGradedMk G j xc) (u • lcsGradedMk G k yc) =
    u • lcsBracket G j k (lcsGradedMk G j xc) (lcsGradedMk G k yc)
  rw [← hG.lcsGradedMk_padicPow yc u]
  obtain ⟨_, _, hbracket⟩ := lcsBracket_padicPow_right hG xc yc u
  rw [hbracket]
  let c : closedLowerCentralSeries G (j + k + 1) :=
    ⟨⁅(xc : G), (yc : G)⁆,
      (commutator_closedLowerCentralSeries_le j k)
        (Subgroup.commutator_mem_commutator xc.2 yc.2)⟩
  rw [lcsBracket, lcsGradedMk, gradedBracket_gradedMk]
  simpa only [c] using hG.lcsGradedMk_padicPow c u

end PadicPow

end TauCeti
