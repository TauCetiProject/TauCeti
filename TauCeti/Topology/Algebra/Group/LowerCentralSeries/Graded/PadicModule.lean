/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# The `ℤ_p`-bilinear graded bracket of a pro-`p` group

Let `G` be a pro-`p` group and `λ_n` the lower `q`-series of `G`, for any `q`. Each graded piece
`λ_n / λ_{n+1}` is an abelian pro-`p` group, hence carries a canonical `ℤ_p`-module structure.
Taking a `p`-adic power in either argument of a commutator acts on its class by the same `p`-adic
exponent, so the graded bracket is `ℤ_p`-bilinear.

## Main definitions

* `TauCeti.IsProP.gradedPieceModule`: the canonical `ℤ_p`-module structure on a graded piece.

## Main results

* `TauCeti.IsProP.gradedMk_padicPow`: a `p`-adic power becomes scalar multiplication on a graded
  piece.
* `TauCeti.IsProP.mk_commutatorElement_padicPow_left`,
  `TauCeti.IsProP.mk_commutatorElement_padicPow_right`: modulo `λ_{j+k+2}`, a `p`-adic power in
  either input of a commutator is the same power of the commutator.
* `TauCeti.IsProP.gradedBracket_padicPow_left`, `TauCeti.IsProP.gradedBracket_padicPow_right`:
  the same statements for classes in the graded pieces.
* `TauCeti.IsProP.gradedBracket_smul_left`, `TauCeti.IsProP.gradedBracket_smul_right`: the graded
  bracket is `ℤ_p`-linear in each variable.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The canonical `ℤ_p`-module structure on a graded piece of the lower `q`-series of a pro-`p`
group. It is the module structure on the abelian pro-`p` quotient `λ_n / λ_{n+1}`. -/
@[instance_reducible]
noncomputable def IsProP.gradedPieceModule (hG : IsProP p G) (q n : ℕ) :
    Module ℤ_[p] (gradedPiece q G n) := by
  let R := pLowerCentralSeries q G n
  let N := (pLowerCentralSeries q G (n + 1)).subgroupOf R
  let _ : IsClosed (R : Set G) := isClosed_pLowerCentralSeries n
  let _ : IsClosed (N : Set R) := by
    rw [isClosed_induced_iff]
    exact ⟨pLowerCentralSeries q G (n + 1), isClosed_pLowerCentralSeries (n + 1), rfl⟩
  exact ((hG.subgroup R).quotient N).module

/-- In a pro-`p` group, the class of a `p`-adic power in a graded piece of the lower `q`-series is
the corresponding `ℤ_p`-scalar multiple. -/
@[simp]
theorem IsProP.gradedMk_padicPow (hG : IsProP p G) {q n : ℕ}
    (x : pLowerCentralSeries q G n) (u : ℤ_[p]) :
    letI := hG.gradedPieceModule q n
    gradedMk q G n
        ⟨hG.padicPow (x : G) u, hG.padicPow_mem (isClosed_pLowerCentralSeries n) x.2 u⟩ =
      u • gradedMk q G n x := by
  let R := pLowerCentralSeries q G n
  let N := (pLowerCentralSeries q G (n + 1)).subgroupOf R
  let _ : IsClosed (R : Set G) := isClosed_pLowerCentralSeries n
  let _ : IsClosed (N : Set R) := by
    rw [isClosed_induced_iff]
    exact ⟨pLowerCentralSeries q G (n + 1), isClosed_pLowerCentralSeries (n + 1), rfl⟩
  let hR : IsProP p R := hG.subgroup R
  let xuR : R := ⟨hG.padicPow (x : G) u, hG.padicPow_mem (isClosed_pLowerCentralSeries n) x.2 u⟩
  have hpow : hR.padicPow x u = xuR := by
    apply Subtype.ext
    exact hR.map_padicPow hG R.subtype continuous_subtype_val x u
  let _ : Module ℤ_[p] (gradedPiece q G n) := hG.gradedPieceModule q n
  rw [gradedMk_def, gradedMk_def]
  -- Expose the subgroup quotient underlying the sealed graded class map.
  change Additive.ofMul (QuotientGroup.mk xuR : R ⧸ N) =
    u • Additive.ofMul (QuotientGroup.mk x : R ⧸ N)
  rw [← hpow]
  exact hR.ofMul_mk_padicPow_quotient N x u

/-- Modulo `λ_{j+k+2}`, taking a `p`-adic power in the left input of a commutator is the same
as taking that power of the commutator. -/
theorem IsProP.mk_commutatorElement_padicPow_left (hG : IsProP p G) {q j k : ℕ}
    (x : pLowerCentralSeries q G j) (y : pLowerCentralSeries q G k) (u : ℤ_[p]) :
    ((⁅hG.padicPow (x : G) u, (y : G)⁆ : G) :
        G ⧸ pLowerCentralSeries q G (j + k + 1 + 1)) =
      ((hG.padicPow ⁅(x : G), (y : G)⁆ u : G) :
        G ⧸ pLowerCentralSeries q G (j + k + 1 + 1)) := by
  let N := pLowerCentralSeries q G (j + k + 1 + 1)
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
  rw [hG.mk_padicPow_quotient N]
  refine (hG.quotient N).eq_padicPow_of_continuous hleft (fun n ↦ ?_) u
  rw [hG.padicPow_natCast]
  have hcomm : Commute ((x : G) : G ⧸ N)
      ⁅((x : G) : G ⧸ N), ((y : G) : G ⧸ N)⁆ := by
    simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries x.2 y.2) (x : G)
  -- Restate coercions as the quotient homomorphism so its map lemmas apply.
  change QuotientGroup.mk' N ⁅(x : G) ^ n, (y : G)⁆ =
    QuotientGroup.mk' N ⁅(x : G), (y : G)⁆ ^ n
  rw [map_commutatorElement, map_pow]
  exact (hcomm.commutatorElement_pow_left n).symm

/-- Modulo `λ_{j+k+2}`, taking a `p`-adic power in the right input of a commutator is the same
as taking that power of the commutator. -/
theorem IsProP.mk_commutatorElement_padicPow_right (hG : IsProP p G) {q j k : ℕ}
    (x : pLowerCentralSeries q G j) (y : pLowerCentralSeries q G k) (u : ℤ_[p]) :
    ((⁅(x : G), hG.padicPow (y : G) u⁆ : G) :
        G ⧸ pLowerCentralSeries q G (j + k + 1 + 1)) =
      ((hG.padicPow ⁅(x : G), (y : G)⁆ u : G) :
        G ⧸ pLowerCentralSeries q G (j + k + 1 + 1)) := by
  let N := pLowerCentralSeries q G (j + k + 1 + 1)
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
  rw [hG.mk_padicPow_quotient N]
  refine (hG.quotient N).eq_padicPow_of_continuous hleft (fun n ↦ ?_) u
  rw [hG.padicPow_natCast]
  have hcomm : Commute ((y : G) : G ⧸ N)
      ⁅((x : G) : G ⧸ N), ((y : G) : G ⧸ N)⁆ := by
    simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries x.2 y.2) (y : G)
  -- Restate coercions as the quotient homomorphism so its map lemmas apply.
  change QuotientGroup.mk' N ⁅(x : G), (y : G) ^ n⁆ =
    QuotientGroup.mk' N ⁅(x : G), (y : G)⁆ ^ n
  rw [map_commutatorElement, map_pow]
  exact (hcomm.commutatorElement_pow_right n).symm

/-- Taking a `p`-adic power in the first argument of the graded bracket takes the same power of
the bracket class. This is `ℤ_p`-linearity in the first variable on representatives. -/
theorem IsProP.gradedBracket_padicPow_left (hG : IsProP p G) {q j k : ℕ}
    (x : pLowerCentralSeries q G j) (y : pLowerCentralSeries q G k) (u : ℤ_[p]) :
    gradedBracket q G j k
        (gradedMk q G j
          ⟨hG.padicPow (x : G) u, hG.padicPow_mem (isClosed_pLowerCentralSeries j) x.2 u⟩)
        (gradedMk q G k y) =
      gradedMk q G (j + k + 1)
        ⟨hG.padicPow ⁅(x : G), (y : G)⁆ u, hG.padicPow_mem (isClosed_pLowerCentralSeries _)
          (commutator_mem_pLowerCentralSeries x.2 y.2) u⟩ := by
  rw [gradedBracket_gradedMk, gradedMk_eq_gradedMk_iff]
  exact hG.mk_commutatorElement_padicPow_left x y u

/-- Taking a `p`-adic power in the second argument of the graded bracket takes the same power of
the bracket class. This is `ℤ_p`-linearity in the second variable on representatives. -/
theorem IsProP.gradedBracket_padicPow_right (hG : IsProP p G) {q j k : ℕ}
    (x : pLowerCentralSeries q G j) (y : pLowerCentralSeries q G k) (u : ℤ_[p]) :
    gradedBracket q G j k (gradedMk q G j x)
        (gradedMk q G k
          ⟨hG.padicPow (y : G) u, hG.padicPow_mem (isClosed_pLowerCentralSeries k) y.2 u⟩) =
      gradedMk q G (j + k + 1)
        ⟨hG.padicPow ⁅(x : G), (y : G)⁆ u, hG.padicPow_mem (isClosed_pLowerCentralSeries _)
          (commutator_mem_pLowerCentralSeries x.2 y.2) u⟩ := by
  rw [gradedBracket_gradedMk, gradedMk_eq_gradedMk_iff]
  exact hG.mk_commutatorElement_padicPow_right x y u

/-- The graded bracket of a pro-`p` group is `ℤ_p`-linear in its first argument. -/
theorem IsProP.gradedBracket_smul_left (hG : IsProP p G) {q j k : ℕ} (u : ℤ_[p])
    (x : gradedPiece q G j) (y : gradedPiece q G k) :
    letI := hG.gradedPieceModule q j
    letI := hG.gradedPieceModule q k
    letI := hG.gradedPieceModule q (j + k + 1)
    gradedBracket q G j k (u • x) y = u • gradedBracket q G j k x y := by
  let _ : Module ℤ_[p] (gradedPiece q G j) := hG.gradedPieceModule q j
  let _ : Module ℤ_[p] (gradedPiece q G k) := hG.gradedPieceModule q k
  let _ : Module ℤ_[p] (gradedPiece q G (j + k + 1)) := hG.gradedPieceModule q (j + k + 1)
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [← hG.gradedMk_padicPow x u, hG.gradedBracket_padicPow_left x y u,
    gradedBracket_gradedMk]
  exact hG.gradedMk_padicPow ⟨_, commutator_mem_pLowerCentralSeries x.2 y.2⟩ u

/-- The graded bracket of a pro-`p` group is `ℤ_p`-linear in its second argument. -/
theorem IsProP.gradedBracket_smul_right (hG : IsProP p G) {q j k : ℕ} (u : ℤ_[p])
    (x : gradedPiece q G j) (y : gradedPiece q G k) :
    letI := hG.gradedPieceModule q j
    letI := hG.gradedPieceModule q k
    letI := hG.gradedPieceModule q (j + k + 1)
    gradedBracket q G j k x (u • y) = u • gradedBracket q G j k x y := by
  let _ : Module ℤ_[p] (gradedPiece q G j) := hG.gradedPieceModule q j
  let _ : Module ℤ_[p] (gradedPiece q G k) := hG.gradedPieceModule q k
  let _ : Module ℤ_[p] (gradedPiece q G (j + k + 1)) := hG.gradedPieceModule q (j + k + 1)
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [← hG.gradedMk_padicPow y u, hG.gradedBracket_padicPow_right x y u,
    gradedBracket_gradedMk]
  exact hG.gradedMk_padicPow ⟨_, commutator_mem_pLowerCentralSeries x.2 y.2⟩ u

end TauCeti
