/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector
-- Private: the orthogonal-basis and volume-element computations are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Chirality and self-duality in the Clifford algebra of an oriented four-space

Let `V` be an oriented real inner product space of dimension four and `Q` a quadratic form on `V`
with `Q v = -‖v‖²`, so that in `CliffordAlgebra Q` the generators satisfy the Clifford relation
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫` of the spinor representations of the Seiberg–Witten equations.

The **chirality element** is `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` for a positively oriented orthonormal
basis `e`. It is defined here without a frame, as minus the image of the unit volume element of
`⋀⁴ V` under the quantization map `CliffordAlgebra.equivExterior`, and `chirality_eq` recovers
the displayed formula for *every* positively oriented orthonormal basis; this is the frame
independence of `Γ`. Moreover `Γ² = 1`, `Γ` anticommutes with every generator, and `Γ` is fixed
by reversal and by the grade involution. The first fact splits every Clifford module over `ℝ` into
the `±1` eigenspaces `W⁺` and `W⁻` of `Γ`, the second makes the generators exchange them, and the
last is the algebraic input for `Γ` to act self-adjointly on a Hermitian Clifford module; that
Hermitian statement is not made here.

Two-forms act through the Clifford bivector map
`c₂ = CliffordAlgebra.bivectorExterior Q : ⋀² V → CliffordAlgebra Q`, which sends `eᵢ ∧ eⱼ` to
`c(eᵢ) c(eⱼ)` for `i ≠ j`. The central identity of this file is the **self-duality relation**

  `c₂(⋆α) = Γ c₂(α)`,

where `⋆` is the Hodge star of the oriented space (`Orientation.hodgeStar`). As `c₂(α)` commutes
with `Γ`, anti-self-dual two-forms (`⋆α = -α`) act by zero on `W⁺` and self-dual ones act by zero
on `W⁻`: on `W⁺` only `Λ⁺` survives, which is what lets the curvature equation of the
Seiberg–Witten equations be written as an equation between self-dual two-forms and trace-free
endomorphisms of `W⁺`.

## Main definitions

* `TauCeti.SeibergWitten.chirality Q o`: the chirality element `Γ` of `CliffordAlgebra Q`.

## Main results

* `TauCeti.SeibergWitten.chirality_eq`: `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` for every positively
  oriented orthonormal basis `e`.
* `TauCeti.SeibergWitten.chirality_mul_self`: `Γ² = 1`.
* `TauCeti.SeibergWitten.chirality_mul_ι`: `Γ c(v) = -c(v) Γ`.
* `TauCeti.SeibergWitten.reverse_chirality`, `TauCeti.SeibergWitten.involute_chirality`: `Γ` is
  fixed by reversal and by the grade involution.
* `TauCeti.SeibergWitten.commute_chirality_bivectorExterior`: two-forms commute with `Γ`.
* `TauCeti.SeibergWitten.bivectorExterior_hodgeStar`: the self-duality relation
  `c₂(⋆α) = Γ c₂(α)`.
* `TauCeti.SeibergWitten.bivectorExterior_smul_eq_zero_of_hodgeStar_eq_neg` and
  `TauCeti.SeibergWitten.bivectorExterior_smul_eq_zero_of_hodgeStar_eq_self`: anti-self-dual
  two-forms annihilate `W⁺`, and self-dual two-forms annihilate `W⁻`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Chapter IV, §1.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–§4.1.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open Module CliffordAlgebra exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

section Orthonormal

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- For `Q v = -‖v‖²`, orthogonality for `Q` is orthogonality for the inner product. -/
private theorem isOrtho_iff {x y : V} : Q.IsOrtho x y ↔ ⟪x, y⟫ = 0 := by
  rw [QuadraticMap.isOrtho_def, hQ, hQ, hQ, norm_add_sq_real]
  constructor <;> intro h <;> linarith

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- An orthonormal basis is orthogonal for the polar form of `Q`. -/
private theorem isOrthoᵢ_associated : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis :=
  fun _ _ hij ↦
    QuadraticMap.associated_isOrtho.2 ((isOrtho_iff hQ).2 (by simpa using b.orthonormal.2 hij))

/-- The members of a list of distinct orthonormal basis vectors are pairwise orthogonal for `Q`. -/
private theorem pairwise_isOrtho_map {l : List ι} (hl : l.Nodup) : (l.map b).Pairwise Q.IsOrtho :=
  List.pairwise_map.mpr <| hl.imp fun hij ↦ (isOrtho_iff hQ).2 (b.orthonormal.2 hij)

/-- `Q` takes the value `-1` at every member of a list of orthonormal basis vectors. -/
private theorem prod_map_map_eq (l : List ι) : ((l.map b).map Q).prod = (-1) ^ l.length := by
  have h : (l.map b).map Q = List.replicate l.length (-1) := by
    refine List.eq_replicate_iff.2 ⟨by simp, fun x hx ↦ ?_⟩
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp [hQ, b.orthonormal.1 i]
  rw [h, List.prod_replicate]

/-- The square of the Clifford product of two distinct orthonormal basis vectors is `-1`. -/
private theorem basis_mul_self_of_card_eq_two [LinearOrder ι] (s : powersetCard ι 2) :
    basis Q b.toBasis s * basis Q b.toBasis s = -1 := by
  rw [basis_eq_prod_map_sort (isOrthoᵢ_associated hQ b), OrthonormalBasis.coe_toBasis,
    prod_map_ι_sq_scalar (pairwise_isOrtho_map hQ _ (Finset.sort_nodup _ _)), prod_map_map_eq hQ]
  have hlen : ((s : Finset ι).sort (· ≤ ·)).length = 2 := by
    rw [Finset.length_sort]
    exact powersetCard.mem_iff.1 s.2
  simp [hlen]

end Orthonormal

variable [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)]

variable (Q) (o : Orientation ℝ V (Fin 4))

/-- The chirality element `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` of the Clifford algebra of an oriented
four-dimensional real inner product space, for any positively oriented orthonormal basis `e`
(`TauCeti.SeibergWitten.chirality_eq`). It is defined frame-free, as minus the quantization of the
unit volume element of `⋀⁴ V`. -/
def chirality : CliffordAlgebra Q :=
  -(equivExterior Q).symm (o.volumeEquiv.symm 1 : ExteriorAlgebra ℝ V)

/-- Unfolding lemma for `TauCeti.SeibergWitten.chirality`. -/
theorem chirality_def :
    chirality Q o = -(equivExterior Q).symm (o.volumeEquiv.symm 1 : ExteriorAlgebra ℝ V) :=
  (rfl)

variable {Q}

/-- In terms of the Clifford basis of a positively oriented orthonormal basis `e`, the chirality
element is minus the basis vector indexed by all of `Fin 4`. -/
private theorem chirality_eq_neg_basis_univ (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) :
    chirality Q o = -basis Q b.toBasis Finset.univ := by
  have h : o.volumeEquiv.symm 1 = b.toBasis.topVector := by
    rw [LinearEquiv.symm_apply_eq, o.volumeEquiv_topVector b hb]
  rw [chirality_def, h, Basis.coe_topVector, CliffordAlgebra.basis_apply]

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- The chirality element is minus the ordered product of the generators of a positively oriented
orthonormal basis, written as a list. -/
private theorem chirality_eq_neg_prod (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) :
    chirality Q o = -(((List.finRange 4).map b).map (ι Q)).prod := by
  rw [chirality_eq_neg_basis_univ o b hb, basis_eq_prod_map_sort (isOrthoᵢ_associated hQ b),
    Fin.sort_univ, OrthonormalBasis.coe_toBasis]

/-- **Frame independence of the chirality element**: `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` for every
positively oriented orthonormal basis `e`. -/
theorem chirality_eq (b : OrthonormalBasis (Fin 4) ℝ V) (hb : b.toBasis.orientation = o) :
    chirality Q o = -(ι Q (b 0) * ι Q (b 1) * ι Q (b 2) * ι Q (b 3)) := by
  rw [chirality_eq_neg_prod o hQ b hb]
  simp [List.finRange_succ, mul_assoc]

/-- A positively oriented orthonormal basis of the oriented four-space. -/
private abbrev frame : OrthonormalBasis (Fin 4) ℝ V :=
  o.finOrthonormalBasis (by norm_num) Fact.out

omit [FiniteDimensional ℝ V] hQ in
private theorem frame_orientation : (frame o).toBasis.orientation = o :=
  o.finOrthonormalBasis_orientation _ _

/-- **The chirality element is an involution**: `Γ² = 1`. -/
@[simp]
theorem chirality_mul_self : chirality Q o * chirality Q o = 1 := by
  rw [chirality_eq_neg_prod o hQ (frame o) (frame_orientation o), neg_mul_neg,
    prod_map_ι_sq_scalar (pairwise_isOrtho_map hQ _ (List.nodup_finRange 4)),
    prod_map_map_eq hQ]
  norm_num [Nat.choose_two_right]

/-- **The chirality element anticommutes with every generator**: `Γ c(v) = -c(v) Γ`. -/
theorem chirality_mul_ι (v : V) : chirality Q o * ι Q v = -(ι Q v * chirality Q o) := by
  have hspan : v ∈ Submodule.span ℝ {x : V | x ∈ (List.finRange 4).map (frame o)} := by
    have h : {x : V | x ∈ (List.finRange 4).map (frame o)} = Set.range (frame o) := by
      ext; simp
    rw [h, ← OrthonormalBasis.coe_toBasis, (frame o).toBasis.span_eq]
    exact Submodule.mem_top
  rw [chirality_eq_neg_prod o hQ (frame o) (frame_orientation o), neg_mul, mul_neg,
    prod_map_ι_mul_ι_of_even_length (pairwise_isOrtho_map hQ _ (List.nodup_finRange 4))
      (by simp [Nat.even_iff]) hspan]

/-- The chirality element is fixed by reversal. Together with `involute_chirality`, it is fixed by
the Clifford conjugation `involute ∘ reverse`. -/
@[simp]
theorem reverse_chirality : reverse (chirality Q o) = chirality Q o := by
  rw [chirality_eq_neg_prod o hQ (frame o) (frame_orientation o), map_neg,
    reverse_prod_map_ι_of_pairwise_isOrtho (pairwise_isOrtho_map hQ _ (List.nodup_finRange 4))]
  norm_num [Nat.choose_two_right]

omit hQ in
/-- The chirality element is even: it is fixed by the grade involution. -/
@[simp]
theorem involute_chirality : involute (chirality Q o) = chirality Q o := by
  have h : involute (basis Q (frame o).toBasis Finset.univ) =
      basis Q (frame o).toBasis Finset.univ := by
    apply (equivExterior Q).injective
    rw [equivExterior_involute, CliffordAlgebra.basis_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.exteriorAlgebra_eq_prod_map_sort, involute_prod_map_ι]
    norm_num
  rw [chirality_eq_neg_basis_univ o (frame o) (frame_orientation o), map_neg, h]

/-- **Two-forms commute with the chirality element**, since `Γ` anticommutes with each of the two
generators in a bivector. -/
theorem commute_chirality_bivectorExterior (x : ⋀[ℝ]^2 V) :
    Commute (chirality Q o) (bivectorExterior Q x) := by
  have hι : ∀ a b : V, chirality Q o * (ι Q a * ι Q b) = ι Q a * ι Q b * chirality Q o := by
    intro a b
    rw [← mul_assoc, chirality_mul_ι o hQ, neg_mul, mul_assoc, chirality_mul_ι o hQ, mul_neg,
      neg_neg, mul_assoc]
  have hmem : bivectorExterior Q x ∈ Subalgebra.toSubmodule
      (Subalgebra.centralizer ℝ {chirality Q o}) := by
    refine bivectorExterior_range_le_of_bivector_mem Q _ (fun a b ↦ ?_)
      (LinearMap.mem_range_self _ x)
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    rw [bivector_def, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hι, hι]
  exact (Subalgebra.mem_centralizer_iff ℝ).1 hmem _ rfl

/-- **The self-duality relation**: the Clifford action of the Hodge dual of a two-form is the
chirality element times the action of the two-form, `c₂(⋆α) = Γ c₂(α)`. -/
theorem bivectorExterior_hodgeStar (hkl : 2 + 2 = finrank ℝ V) (x : ⋀[ℝ]^2 V) :
    bivectorExterior Q (o.hodgeStar hkl x) = chirality Q o * bivectorExterior Q x := by
  set b := frame o
  have hbiv : ∀ y : ⋀[ℝ]^2 V, bivectorExterior Q y = (equivExterior Q).symm y := fun y ↦
    LinearEquiv.eq_symm_apply _ |>.2 (equivExterior_bivectorExterior Q y)
  have hcard : 2 + 2 = Fintype.card (Fin 4) := rfl
  -- Compare both sides as linear maps on the orthonormal basis `e_s` of `⋀² V`.
  refine LinearMap.congr_fun ((b.toBasis.exteriorPower 2).ext
    (f₁ := (bivectorExterior Q).comp (o.hodgeStar hkl).toLinearMap)
    (f₂ := (LinearMap.mulLeft ℝ (chirality Q o)).comp (bivectorExterior Q)) fun s ↦ ?_) x
  set t := powersetCard.compl hcard s
  have hst : Disjoint s.val t.val :=
    (powersetCard.disjoint_iff_eq_compl hcard).2
      ((powersetCard.compl hcard).symm_apply_apply s).symm
  have hunion : (powersetCard.disjUnion hst : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ <| by
      rw [powersetCard.coe_disjUnion, Finset.card_disjUnion, powersetCard.mem_iff.1 s.2,
        powersetCard.mem_iff.1 t.2]
      exact hcard
  -- With `A = e_s`, `C = e_t` and `ε` the shuffle sign, `A C = -ε Γ` and `A² = -1`.
  set A := basis Q b.toBasis s
  set C := basis Q b.toBasis t
  set ε := powersetCard.sign s
  have hAC : A * C = ε • -chirality Q o := by
    rw [basis_mul_basis_of_disjoint (isOrthoᵢ_associated hQ b) hst,
      ← powersetCard.sign_eq_permOfDisjoint_sign hcard s t hst, hunion,
      chirality_eq_neg_basis_univ o b (frame_orientation o), neg_neg]
  have hAA : A * A = -1 := basis_mul_self_of_card_eq_two hQ b s
  have hA : bivectorExterior Q (b.toBasis.exteriorPower 2 s) = A := by
    rw [hbiv, ← ExteriorAlgebra.basis_eq_coe_basis, ← CliffordAlgebra.basis_apply]
  have hC : bivectorExterior Q (b.toBasis.exteriorPower 2 t) = C := by
    rw [hbiv, ← ExteriorAlgebra.basis_eq_coe_basis, ← CliffordAlgebra.basis_apply]
  have hcomm : A * chirality Q o = chirality Q o * A := by
    rw [← hA]
    exact ((commute_chirality_bivectorExterior o hQ _).eq).symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply]
  rw [o.hodgeStar_basis b (frame_orientation o) hkl s, map_zsmul_unit, hA]
  -- `C = -(A A) C = -A (A C) = ε A Γ`, and `ε² = 1`.
  calc ε • bivectorExterior Q (b.toBasis.exteriorPower 2 _) = ε • C := by rw [← hC]
    _ = ε • (-(A * A) * C) := by rw [hAA, neg_neg, one_mul]
    _ = (ε * ε) • (A * chirality Q o) := by
      rw [neg_mul, mul_assoc, hAC, mul_smul_comm, mul_neg]
      simp only [smul_neg, neg_neg, smul_smul]
    _ = chirality Q o * A := by rw [Int.units_mul_self, one_smul, hcomm]

/-- An anti-self-dual two-form `α`, `⋆α = -α`, satisfies `c₂(α) Γ = -c₂(α)`. -/
theorem bivectorExterior_mul_chirality_of_hodgeStar_eq_neg (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) :
    bivectorExterior Q x * chirality Q o = -bivectorExterior Q x := by
  rw [← (commute_chirality_bivectorExterior o hQ x).eq, ← bivectorExterior_hodgeStar o hQ hkl,
    hx, map_neg]

/-- A self-dual two-form `α`, `⋆α = α`, satisfies `c₂(α) Γ = c₂(α)`. -/
theorem bivectorExterior_mul_chirality_of_hodgeStar_eq_self (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) :
    bivectorExterior Q x * chirality Q o = bivectorExterior Q x := by
  rw [← (commute_chirality_bivectorExterior o hQ x).eq, ← bivectorExterior_hodgeStar o hQ hkl, hx]

variable {S : Type*} [AddCommGroup S] [Module (CliffordAlgebra Q) S] [Module ℝ S]

/-- **Anti-self-dual two-forms annihilate positive spinors**: if `Γ ψ = ψ` and `⋆α = -α`, then
`c₂(α) ψ = 0`. -/
theorem bivectorExterior_smul_eq_zero_of_hodgeStar_eq_neg (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) {ψ : S} (hψ : chirality Q o • ψ = ψ) :
    bivectorExterior Q x • ψ = 0 := by
  have h : bivectorExterior Q x • ψ = -(bivectorExterior Q x • ψ) := by
    conv_lhs => rw [← hψ, smul_smul, bivectorExterior_mul_chirality_of_hodgeStar_eq_neg o hQ hkl hx]
    rw [neg_smul]
  -- A vector of a real vector space equal to its negative is zero.
  have h2 : (2 : ℝ) • (bivectorExterior Q x • ψ) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  simpa using h2

/-- **Self-dual two-forms annihilate negative spinors**: if `Γ ψ = -ψ` and `⋆α = α`, then
`c₂(α) ψ = 0`. -/
theorem bivectorExterior_smul_eq_zero_of_hodgeStar_eq_self (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) {ψ : S} (hψ : chirality Q o • ψ = -ψ) :
    bivectorExterior Q x • ψ = 0 := by
  have h : bivectorExterior Q x • ψ = -(bivectorExterior Q x • ψ) := by
    conv_lhs => rw [← bivectorExterior_mul_chirality_of_hodgeStar_eq_self o hQ hkl hx, ← smul_smul,
      hψ, smul_neg]
  -- A vector of a real vector space equal to its negative is zero.
  have h2 : (2 : ℝ) • (bivectorExterior Q x • ψ) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  simpa using h2

end Form

end TauCeti.SeibergWitten
