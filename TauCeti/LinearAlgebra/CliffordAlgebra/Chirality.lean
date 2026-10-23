/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Oriented
-- Private: the orthogonal-basis and volume-element computations are used only inside proofs.
import TauCeti.Algebra.CharP.Invertible
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic
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

The quantitative form of this identification is the **anticommutator formula**

  `c₂(α) c₂(β) + c₂(β) c₂(α) = -2 ⟪α, β⟫ - 2 ⟪⋆α, β⟫ Γ`,

for the inner product of `⋀² V` induced by that of `V`. For self-dual `α` the right-hand side is
`-2 ⟪α, β⟫ (1 + Γ)`, so on `W⁺` the two-forms anticommute up to `-4 ⟪α, β⟫` and a self-dual
`α` squares to `-2 ‖α‖²`. In particular self-dual two-forms act faithfully on every nonzero
positive spinor. Taking traces over a positive half-spinor space of complex dimension two, this is
the normalization `⟪C(iα), C(iβ)⟫ = 4 ⟪α, β⟫` of the Clifford map `C` from imaginary self-dual
two-forms to trace-free endomorphisms of `W⁺`; that trace statement is not made here.

## Main definitions

* `CliffordAlgebra.chirality Q o`: the chirality element `Γ` of `CliffordAlgebra Q`.

## Main results

* `CliffordAlgebra.chirality_eq_neg_volumeElement`: `Γ` is minus the volume element
  `CliffordAlgebra.volumeElement Q o` of the oriented four-space.
* `CliffordAlgebra.chirality_eq`: `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` for every positively
  oriented orthonormal basis `e`.
* `CliffordAlgebra.chirality_mul_self`: `Γ² = 1`.
* `CliffordAlgebra.chirality_mul_ι`: `Γ c(v) = -c(v) Γ`.
* `CliffordAlgebra.reverse_chirality`, `CliffordAlgebra.involute_chirality`: `Γ` is
  fixed by reversal and by the grade involution.
* `CliffordAlgebra.commute_chirality_bivectorExterior`: two-forms commute with `Γ`.
* `CliffordAlgebra.bivectorExterior_hodgeStar`: the self-duality relation
  `c₂(⋆α) = Γ c₂(α)`.
* `CliffordAlgebra.bivectorExterior_smul_eq_zero_of_hodgeStar_eq_neg` and
  `CliffordAlgebra.bivectorExterior_smul_eq_zero_of_hodgeStar_eq_self`: anti-self-dual
  two-forms annihilate `W⁺`, and self-dual two-forms annihilate `W⁻`.
* `CliffordAlgebra.bivectorExterior_mul_bivectorExterior_add_swap`: the anticommutator formula
  `c₂(α) c₂(β) + c₂(β) c₂(α) = -2 ⟪α, β⟫ - 2 ⟪⋆α, β⟫ Γ`, and
  `CliffordAlgebra.bivectorExterior_mul_self`: `c₂(α)² = -‖α‖² - ⟪⋆α, α⟫ Γ`.
* `CliffordAlgebra.bivectorExterior_mul_bivectorExterior_add_swap_of_hodgeStar_eq_self` and
  `CliffordAlgebra.bivectorExterior_mul_bivectorExterior_add_swap_of_hodgeStar_eq_neg`: the
  anticommutator of a self-dual (anti-self-dual) two-form is `-2 ⟪α, β⟫ (1 ± Γ)`.
* `CliffordAlgebra.bivectorExterior_smul_bivectorExterior_smul_add_swap_of_hodgeStar_eq_self` and
  `CliffordAlgebra.bivectorExterior_smul_bivectorExterior_smul_self_of_hodgeStar_eq_self`: on
  positive spinors a self-dual `α` satisfies `c₂(α) c₂(β) + c₂(β) c₂(α) = -4 ⟪α, β⟫` and
  `c₂(α)² = -2 ‖α‖²`; the `_of_hodgeStar_eq_neg` versions are the same on negative spinors for
  anti-self-dual `α`.
* `CliffordAlgebra.bivectorExterior_smul_eq_zero_iff_of_hodgeStar_eq_self` and
  `CliffordAlgebra.bivectorExterior_smul_eq_zero_iff_of_hodgeStar_eq_neg`: self-dual two-forms
  act faithfully on nonzero positive spinors, and anti-self-dual ones on nonzero negative spinors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Chapter IV, §1.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1–§4.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

variable [Fact (finrank ℝ V = 4)]

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

variable (Q) (o : Orientation ℝ V (Fin 4))

/-- The chirality element `Γ` of the Clifford algebra of an oriented four-dimensional real inner
product space: minus the quantization of the unit volume element of `⋀⁴ V`. When
`Q v = -‖v‖²`, it equals `-c(e₁) c(e₂) c(e₃) c(e₄)` for every positively oriented orthonormal
basis `e` (`CliffordAlgebra.chirality_eq`). -/
def chirality : CliffordAlgebra Q :=
  -(equivExterior Q).symm (o.volumeEquiv.symm 1 : ExteriorAlgebra ℝ V)

/-- Unfolding lemma for `CliffordAlgebra.chirality`. -/
theorem chirality_def :
    chirality Q o = -(equivExterior Q).symm (o.volumeEquiv.symm 1 : ExteriorAlgebra ℝ V) :=
  (rfl)

/-- The chirality element is minus the volume element `CliffordAlgebra.volumeElement Q o` of the
oriented four-space. -/
theorem chirality_eq_neg_volumeElement : chirality Q o = -volumeElement Q o := by
  rw [chirality_def, volumeElement_def]

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
  rw [chirality_eq_neg_basis_univ o b hb, basis_eq_prod_map_sort (b.isOrthoᵢ_associated hQ),
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

omit hQ in
private theorem frame_orientation : (frame o).toBasis.orientation = o :=
  o.finOrthonormalBasis_orientation _ _

/-- **The chirality element is an involution**: `Γ² = 1`. -/
@[simp]
theorem chirality_mul_self : chirality Q o * chirality Q o = 1 := by
  rw [chirality_eq_neg_basis_univ o (frame o) (frame_orientation o), neg_mul_neg,
    basis_mul_self_of_orthonormal hQ]
  norm_num [Nat.choose_two_right]

/-- **The chirality element anticommutes with every generator**: `Γ c(v) = -c(v) Γ`. -/
theorem chirality_mul_ι (v : V) : chirality Q o * ι Q v = -(ι Q v * chirality Q o) := by
  have hspan : v ∈ Submodule.span ℝ {x : V | x ∈ (List.finRange 4).map (frame o)} := by
    have h : {x : V | x ∈ (List.finRange 4).map (frame o)} = Set.range (frame o) := by
      ext; simp
    rw [h, ← OrthonormalBasis.coe_toBasis, (frame o).toBasis.span_eq]
    exact Submodule.mem_top
  rw [chirality_eq_neg_prod o hQ (frame o) (frame_orientation o), neg_mul, mul_neg,
    prod_map_ι_mul_ι_of_even_length ((frame o).pairwise_isOrtho_map hQ (List.nodup_finRange 4))
      (by simp [Nat.even_iff]) hspan]

omit hQ in
/-- The chirality element is fixed by reversal. Together with `involute_chirality`, it is fixed by
the Clifford conjugation `involute ∘ reverse`. -/
@[simp]
theorem reverse_chirality : reverse (chirality Q o) = chirality Q o := by
  simp [chirality_eq_neg_volumeElement]

omit hQ in
/-- The chirality element is even: it is fixed by the grade involution. -/
@[simp]
theorem involute_chirality : involute (chirality Q o) = chirality Q o := by
  norm_num [chirality_eq_neg_volumeElement]

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

/-- For a two-element set `s` of frame indices, `e_s e_{sᶜ} = -ε Γ`, where `ε` is the shuffle
sign of `s`. -/
private theorem basis_mul_basis_compl (hcard : 2 + 2 = Fintype.card (Fin 4))
    (s : powersetCard (Fin 4) 2) :
    basis Q (frame o).toBasis s * basis Q (frame o).toBasis (powersetCard.compl hcard s) =
      powersetCard.sign s • -chirality Q o := by
  set t := powersetCard.compl hcard s
  have hst : Disjoint s.val t.val :=
    (powersetCard.disjoint_iff_eq_compl hcard).2
      ((powersetCard.compl hcard).symm_apply_apply s).symm
  have hunion : (powersetCard.disjUnion hst : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ <| by
      rw [powersetCard.coe_disjUnion, Finset.card_disjUnion, powersetCard.mem_iff.1 s.2,
        powersetCard.mem_iff.1 t.2]
      exact hcard
  rw [basis_mul_basis_of_disjoint ((frame o).isOrthoᵢ_associated hQ) hst,
    ← powersetCard.sign_eq_permOfDisjoint_sign hcard s t hst, hunion,
    chirality_eq_neg_basis_univ o (frame o) (frame_orientation o), neg_neg]

/-- **The self-duality relation**: the Clifford action of the Hodge dual of a two-form is the
chirality element times the action of the two-form, `c₂(⋆α) = Γ c₂(α)`. -/
theorem bivectorExterior_hodgeStar (hkl : 2 + 2 = finrank ℝ V) (x : ⋀[ℝ]^2 V) :
    bivectorExterior Q (o.hodgeStar hkl x) = chirality Q o * bivectorExterior Q x := by
  set b := frame o
  have hcard : 2 + 2 = Fintype.card (Fin 4) := rfl
  -- Compare both sides as linear maps on the orthonormal basis `e_s` of `⋀² V`.
  refine LinearMap.congr_fun ((b.toBasis.exteriorPower 2).ext
    (f₁ := (bivectorExterior Q).comp (o.hodgeStar hkl).toLinearMap)
    (f₂ := (LinearMap.mulLeft ℝ (chirality Q o)).comp (bivectorExterior Q)) fun s ↦ ?_) x
  -- With `A = e_s`, `C = e_t` and `ε` the shuffle sign, `A C = -ε Γ` and `A² = -1`.
  set A := basis Q b.toBasis s
  set C := basis Q b.toBasis (powersetCard.compl hcard s)
  set ε := powersetCard.sign s
  have hAC : A * C = ε • -chirality Q o := basis_mul_basis_compl o hQ hcard s
  have hAA : A * A = -1 := by
    rw [basis_mul_self_of_orthonormal hQ, powersetCard.mem_iff.1 s.2]
    norm_num
  have hcomm : A * chirality Q o = chirality Q o * A := by
    have h := (commute_chirality_bivectorExterior o hQ (b.toBasis.exteriorPower 2 s)).eq.symm
    rwa [bivectorExterior_exteriorPower_basis] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply]
  rw [o.hodgeStar_basis b (frame_orientation o) hkl s, map_zsmul_unit,
    bivectorExterior_exteriorPower_basis, bivectorExterior_exteriorPower_basis]
  -- `C = -(A A) C = -A (A C) = ε A Γ`, and `ε² = 1`.
  calc ε • C = ε • (-(A * A) * C) := by rw [hAA, neg_neg, one_mul]
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

/-! ### The anticommutator of two two-forms -/

/-- The anticommutator formula on the orthonormal basis `e_s` of `⋀² V` induced by the frame. -/
private theorem bivectorExterior_basis_mul_add_swap (hkl : 2 + 2 = finrank ℝ V)
    (s t : powersetCard (Fin 4) 2) :
    bivectorExterior Q ((frame o).toBasis.exteriorPower 2 s) *
        bivectorExterior Q ((frame o).toBasis.exteriorPower 2 t) +
      bivectorExterior Q ((frame o).toBasis.exteriorPower 2 t) *
        bivectorExterior Q ((frame o).toBasis.exteriorPower 2 s) =
      algebraMap ℝ (CliffordAlgebra Q)
          (-2 * ⟪(frame o).toBasis.exteriorPower 2 s, (frame o).toBasis.exteriorPower 2 t⟫) -
        (2 * ⟪o.hodgeStar hkl ((frame o).toBasis.exteriorPower 2 s),
          (frame o).toBasis.exteriorPower 2 t⟫) • chirality Q o := by
  have hcard : 2 + 2 = Fintype.card (Fin 4) := rfl
  -- The basis `e_s` is orthonormal, and `⋆ e_s = ε e_{sᶜ}`.
  have hinner : ∀ u v : powersetCard (Fin 4) 2,
      ⟪(frame o).toBasis.exteriorPower 2 u, (frame o).toBasis.exteriorPower 2 v⟫ =
        if u = v then 1 else 0 := fun u v ↦ by
    rw [← OrthonormalBasis.toBasis_exteriorPower, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.inner_eq_ite]
  rw [o.hodgeStar_basis (frame o) (frame_orientation o) hkl s, Units.smul_def,
    ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hinner, hinner,
    bivectorExterior_exteriorPower_basis, bivectorExterior_exteriorPower_basis]
  -- Write `e_t = c(e_k) c(e_l)`, where `t = {k, l}`.
  obtain ⟨k, l, hsort⟩ := List.length_eq_two.1
    (by rw [Finset.length_sort, powersetCard.mem_iff.1 t.2] :
      ((t : Finset (Fin 4)).sort (· ≤ ·)).length = 2)
  have hmem : ∀ i, i ∈ t.val ↔ i = k ∨ i = l := fun i ↦ by
    rw [← Finset.mem_sort (· ≤ ·), hsort]
    simp
  have ht : basis Q (frame o).toBasis t = ι Q (frame o k) * ι Q (frame o l) := by
    rw [basis_eq_prod_map_sort ((frame o).isOrthoᵢ_associated hQ), hsort]
    simp
  -- `e_s` anticommutes with the generators it contains and commutes with the others.
  have hb := (frame o).isOrthoᵢ_associated hQ
  have hmem_s : ∀ {i}, i ∈ s.val → basis Q (frame o).toBasis s * ι Q (frame o i) =
      -(ι Q (frame o i) * basis Q (frame o).toBasis s) := fun hi ↦ by
    rw [← OrthonormalBasis.coe_toBasis, basis_mul_ι_of_mem hb hi, powersetCard.mem_iff.1 s.2]
    simp
  have hnotMem_s : ∀ {i}, i ∉ s.val → basis Q (frame o).toBasis s * ι Q (frame o i) =
      ι Q (frame o i) * basis Q (frame o).toBasis s := fun hi ↦ by
    rw [← OrthonormalBasis.coe_toBasis, basis_mul_ι_of_notMem hb hi, powersetCard.mem_iff.1 s.2]
    simp
  set A := basis Q (frame o).toBasis s
  by_cases hts : t.val ⊆ s.val
  · -- `t ⊆ s`, so `t = s` and `e_s² = -1`.
    have hts : t = s := Subtype.ext <| Finset.eq_of_subset_of_card_le hts
      (by rw [powersetCard.mem_iff.1 s.2, powersetCard.mem_iff.1 t.2])
    subst hts
    have hk : k ∈ t.val := (hmem k).2 (Or.inl rfl)
    have hne : powersetCard.compl hcard t ≠ t := fun h ↦ by
      have hk' : k ∈ powersetCard.compl hcard t := by rw [h]; exact hk
      exact powersetCard.mem_compl.1 hk' hk
    have hAA : A * A = -1 := by
      rw [basis_mul_self_of_orthonormal hQ, powersetCard.mem_iff.1 t.2]
      norm_num
    rw [ite_eq_left rfl, ite_eq_right hne, hAA, Algebra.algebraMap_eq_smul_one]
    module
  by_cases hdisj : Disjoint s.val t.val
  · -- `t` is disjoint from `s`, so `t = sᶜ`, and `e_s` commutes with `e_t`.
    have hk : k ∉ s.val := Finset.disjoint_right.1 hdisj ((hmem k).2 (Or.inl rfl))
    have hl : l ∉ s.val := Finset.disjoint_right.1 hdisj ((hmem l).2 (Or.inr rfl))
    have hst : s ≠ t := fun h ↦ hk (h ▸ (hmem k).2 (Or.inl rfl))
    have hct : t = powersetCard.compl hcard s :=
      (powersetCard.disjoint_iff_eq_compl hcard).1 hdisj.symm
    have h : basis Q (frame o).toBasis t * A = A * basis Q (frame o).toBasis t := by
      rw [ht, mul_assoc, ← hnotMem_s hl, ← mul_assoc,
        ← hnotMem_s hk, mul_assoc]
    rw [ite_eq_right hst, ite_eq_left hct.symm, h, hct, basis_mul_basis_compl o hQ hcard s,
      Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
    simp only [mul_zero, map_zero, zero_sub, mul_one, smul_neg]
    module
  -- `t` shares exactly one index `i` with `s`; let `j` be the other one. Then `e_s` anticommutes
  -- with `c(e_i)` and commutes with `c(e_j)`, so it anticommutes with `e_t`.
  obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.1 hts
  obtain ⟨i, his, hit⟩ := Finset.not_disjoint_iff.1 hdisj
  have hst : s ≠ t := fun h ↦ hjs (h ▸ hjt)
  have hct : powersetCard.compl hcard s ≠ t := fun h ↦
    powersetCard.mem_compl.1 (h ▸ hit : i ∈ powersetCard.compl hcard s) his
  have hi : SemiconjBy A (ι Q (frame o i)) (-ι Q (frame o i)) := by
    rw [SemiconjBy, hmem_s his, neg_mul]
  have hj : SemiconjBy A (ι Q (frame o j)) (ι Q (frame o j)) := hnotMem_s hjs
  have h : A * basis Q (frame o).toBasis t = -(basis Q (frame o).toBasis t * A) := by
    rw [ht]
    rcases (hmem i).1 hit with rfl | rfl <;> rcases (hmem j).1 hjt with rfl | rfl
    · exact absurd his hjs
    · rw [(hi.mul_right hj).eq, neg_mul, neg_mul]
    · rw [(hj.mul_right hi).eq, mul_neg, neg_mul]
    · exact absurd his hjs
  rw [ite_eq_right hst, ite_eq_right hct, h]
  simp

/-- **The anticommutator of two two-forms** in the Clifford algebra of an oriented four-space:
`c₂(α) c₂(β) + c₂(β) c₂(α) = -2 ⟪α, β⟫ - 2 ⟪⋆α, β⟫ Γ`. Since `α ∧ β = ⟪⋆α, β⟫ vol`, the
coefficient of `Γ` is minus twice the volume of `α ∧ β`. -/
theorem bivectorExterior_mul_bivectorExterior_add_swap (hkl : 2 + 2 = finrank ℝ V)
    (x y : ⋀[ℝ]^2 V) :
    bivectorExterior Q x * bivectorExterior Q y + bivectorExterior Q y * bivectorExterior Q x =
      algebraMap ℝ (CliffordAlgebra Q) (-2 * ⟪x, y⟫) -
        (2 * ⟪o.hodgeStar hkl x, y⟫) • chirality Q o := by
  -- Both sides are bilinear in `(α, β)`; compare them on the orthonormal basis of `⋀² V`.
  let B : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] CliffordAlgebra Q := LinearMap.mk₂ ℝ
    (fun x y ↦ bivectorExterior Q x * bivectorExterior Q y +
      bivectorExterior Q y * bivectorExterior Q x -
      ((-2 * ⟪x, y⟫) • 1 - (2 * ⟪o.hodgeStar hkl x, y⟫) • chirality Q o))
    (fun x x' y ↦ by
      simp only [map_add, add_mul, mul_add, inner_add_left]
      module)
    (fun r x y ↦ by
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, real_inner_smul_left]
      module)
    (fun x y y' ↦ by
      simp only [map_add, add_mul, mul_add, inner_add_right]
      module)
    (fun r x y ↦ by
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, real_inner_smul_right]
      module)
  have hB : B = 0 := LinearMap.ext_basis ((frame o).toBasis.exteriorPower 2)
    ((frame o).toBasis.exteriorPower 2) fun s t ↦ by
      simp only [B, LinearMap.mk₂_apply, LinearMap.zero_apply, sub_eq_zero,
        bivectorExterior_basis_mul_add_swap o hQ hkl s t, Algebra.algebraMap_eq_smul_one]
  have h := LinearMap.congr_fun₂ hB x y
  simp only [B, LinearMap.mk₂_apply, LinearMap.zero_apply, sub_eq_zero] at h
  rw [h, Algebra.algebraMap_eq_smul_one]

/-- **The square of a two-form**: `c₂(α)² = -‖α‖² - ⟪⋆α, α⟫ Γ`. -/
theorem bivectorExterior_mul_self (hkl : 2 + 2 = finrank ℝ V) (x : ⋀[ℝ]^2 V) :
    bivectorExterior Q x * bivectorExterior Q x =
      algebraMap ℝ (CliffordAlgebra Q) (-‖x‖ ^ 2) - ⟪o.hodgeStar hkl x, x⟫ • chirality Q o := by
  have h := bivectorExterior_mul_bivectorExterior_add_swap o hQ hkl x x
  rw [real_inner_self_eq_norm_sq, Algebra.algebraMap_eq_smul_one] at h
  rw [Algebra.algebraMap_eq_smul_one]
  refine smul_right_injective _ (two_ne_zero : (2 : ℝ) ≠ 0) ?_
  simp only [two_smul, h]
  module

/-- For a self-dual two-form `α`, `⋆α = α`, the anticommutator is
`c₂(α) c₂(β) + c₂(β) c₂(α) = -2 ⟪α, β⟫ (1 + Γ)`. -/
theorem bivectorExterior_mul_bivectorExterior_add_swap_of_hodgeStar_eq_self
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) (y : ⋀[ℝ]^2 V) :
    bivectorExterior Q x * bivectorExterior Q y + bivectorExterior Q y * bivectorExterior Q x =
      (-2 * ⟪x, y⟫) • (1 + chirality Q o) := by
  rw [bivectorExterior_mul_bivectorExterior_add_swap o hQ hkl, hx, Algebra.algebraMap_eq_smul_one]
  module

/-- For an anti-self-dual two-form `α`, `⋆α = -α`, the anticommutator is
`c₂(α) c₂(β) + c₂(β) c₂(α) = -2 ⟪α, β⟫ (1 - Γ)`. -/
theorem bivectorExterior_mul_bivectorExterior_add_swap_of_hodgeStar_eq_neg
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) (y : ⋀[ℝ]^2 V) :
    bivectorExterior Q x * bivectorExterior Q y + bivectorExterior Q y * bivectorExterior Q x =
      (-2 * ⟪x, y⟫) • (1 - chirality Q o) := by
  rw [bivectorExterior_mul_bivectorExterior_add_swap o hQ hkl, hx, inner_neg_left,
    Algebra.algebraMap_eq_smul_one]
  module

variable {S : Type*} [AddCommGroup S] [Module (CliffordAlgebra Q) S]

/-- **Anti-self-dual two-forms annihilate positive spinors**: if `Γ ψ = ψ` and `⋆α = -α`, then
`c₂(α) ψ = 0`. -/
theorem bivectorExterior_smul_eq_zero_of_hodgeStar_eq_neg (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) {ψ : S} (hψ : chirality Q o • ψ = ψ) :
    bivectorExterior Q x • ψ = 0 := by
  -- `2` is invertible in the real Clifford algebra, so a spinor equal to its negative is zero.
  let : Invertible (2 : CliffordAlgebra Q) :=
    (Invertible.map (algebraMap ℝ (CliffordAlgebra Q)) 2).copy 2 (map_ofNat _ 2).symm
  refine TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := CliffordAlgebra Q) ?_
  conv_lhs => rw [← hψ, smul_smul, bivectorExterior_mul_chirality_of_hodgeStar_eq_neg o hQ hkl hx]
  rw [neg_smul]

/-- **Self-dual two-forms annihilate negative spinors**: if `Γ ψ = -ψ` and `⋆α = α`, then
`c₂(α) ψ = 0`. -/
theorem bivectorExterior_smul_eq_zero_of_hodgeStar_eq_self (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) {ψ : S} (hψ : chirality Q o • ψ = -ψ) :
    bivectorExterior Q x • ψ = 0 := by
  -- `2` is invertible in the real Clifford algebra, so a spinor equal to its negative is zero.
  let : Invertible (2 : CliffordAlgebra Q) :=
    (Invertible.map (algebraMap ℝ (CliffordAlgebra Q)) 2).copy 2 (map_ofNat _ 2).symm
  refine TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := CliffordAlgebra Q) ?_
  conv_lhs => rw [← bivectorExterior_mul_chirality_of_hodgeStar_eq_self o hQ hkl hx, ← smul_smul,
    hψ, smul_neg]

section RealModule

variable [Module ℝ S] [IsScalarTower ℝ (CliffordAlgebra Q) S]

/-- **Self-dual two-forms anticommute on positive spinors up to their inner product**: if
`Γ ψ = ψ` and `⋆α = α`, then `c₂(α) c₂(β) ψ + c₂(β) c₂(α) ψ = -4 ⟪α, β⟫ ψ`. -/
theorem bivectorExterior_smul_bivectorExterior_smul_add_swap_of_hodgeStar_eq_self
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) (y : ⋀[ℝ]^2 V)
    {ψ : S} (hψ : chirality Q o • ψ = ψ) :
    bivectorExterior Q x • bivectorExterior Q y • ψ +
        bivectorExterior Q y • bivectorExterior Q x • ψ =
      (-4 * ⟪x, y⟫) • ψ := by
  rw [smul_smul, smul_smul, ← add_smul,
    bivectorExterior_mul_bivectorExterior_add_swap_of_hodgeStar_eq_self o hQ hkl hx, smul_assoc,
    add_smul, one_smul, hψ, ← two_smul ℝ ψ, smul_smul]
  ring_nf

/-- **Anti-self-dual two-forms anticommute on negative spinors up to their inner product**: if
`Γ ψ = -ψ` and `⋆α = -α`, then `c₂(α) c₂(β) ψ + c₂(β) c₂(α) ψ = -4 ⟪α, β⟫ ψ`. -/
theorem bivectorExterior_smul_bivectorExterior_smul_add_swap_of_hodgeStar_eq_neg
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) (y : ⋀[ℝ]^2 V)
    {ψ : S} (hψ : chirality Q o • ψ = -ψ) :
    bivectorExterior Q x • bivectorExterior Q y • ψ +
        bivectorExterior Q y • bivectorExterior Q x • ψ =
      (-4 * ⟪x, y⟫) • ψ := by
  rw [smul_smul, smul_smul, ← add_smul,
    bivectorExterior_mul_bivectorExterior_add_swap_of_hodgeStar_eq_neg o hQ hkl hx, smul_assoc,
    sub_smul, one_smul, hψ, sub_neg_eq_add, ← two_smul ℝ ψ, smul_smul]
  ring_nf

/-- A self-dual two-form squares to `-2 ‖α‖²` on positive spinors: if `Γ ψ = ψ` and `⋆α = α`,
then `c₂(α) c₂(α) ψ = -2 ‖α‖² ψ`. -/
theorem bivectorExterior_smul_bivectorExterior_smul_self_of_hodgeStar_eq_self
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) {ψ : S}
    (hψ : chirality Q o • ψ = ψ) :
    bivectorExterior Q x • bivectorExterior Q x • ψ = (-2 * ‖x‖ ^ 2) • ψ := by
  rw [smul_smul, bivectorExterior_mul_self o hQ hkl, hx, real_inner_self_eq_norm_sq, sub_smul,
    smul_assoc, hψ, algebraMap_smul]
  module

/-- An anti-self-dual two-form squares to `-2 ‖α‖²` on negative spinors: if `Γ ψ = -ψ` and
`⋆α = -α`, then `c₂(α) c₂(α) ψ = -2 ‖α‖² ψ`. -/
theorem bivectorExterior_smul_bivectorExterior_smul_self_of_hodgeStar_eq_neg
    (hkl : 2 + 2 = finrank ℝ V) {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) {ψ : S}
    (hψ : chirality Q o • ψ = -ψ) :
    bivectorExterior Q x • bivectorExterior Q x • ψ = (-2 * ‖x‖ ^ 2) • ψ := by
  rw [smul_smul, bivectorExterior_mul_self o hQ hkl, hx, inner_neg_left,
    real_inner_self_eq_norm_sq, sub_smul, smul_assoc, hψ, algebraMap_smul]
  module

/-- **Self-dual two-forms act faithfully on every nonzero positive spinor**: if `Γ ψ = ψ`,
`ψ ≠ 0` and `⋆α = α`, then `c₂(α) ψ = 0` only for `α = 0`. -/
theorem bivectorExterior_smul_eq_zero_iff_of_hodgeStar_eq_self (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = x) {ψ : S} (hψ : chirality Q o • ψ = ψ)
    (hψ₀ : ψ ≠ 0) :
    bivectorExterior Q x • ψ = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero, zero_smul]⟩
  have hsq := bivectorExterior_smul_bivectorExterior_smul_self_of_hodgeStar_eq_self o hQ hkl hx hψ
  rw [h, smul_zero, eq_comm, smul_eq_zero] at hsq
  simpa [hψ₀] using hsq

/-- **Anti-self-dual two-forms act faithfully on every nonzero negative spinor**: if
`Γ ψ = -ψ`, `ψ ≠ 0` and `⋆α = -α`, then `c₂(α) ψ = 0` only for `α = 0`. -/
theorem bivectorExterior_smul_eq_zero_iff_of_hodgeStar_eq_neg (hkl : 2 + 2 = finrank ℝ V)
    {x : ⋀[ℝ]^2 V} (hx : o.hodgeStar hkl x = -x) {ψ : S} (hψ : chirality Q o • ψ = -ψ)
    (hψ₀ : ψ ≠ 0) :
    bivectorExterior Q x • ψ = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero, zero_smul]⟩
  have hsq := bivectorExterior_smul_bivectorExterior_smul_self_of_hodgeStar_eq_neg o hQ hkl hx hψ
  rw [h, smul_zero, eq_comm, smul_eq_zero] at hsq
  simpa [hψ₀] using hsq

end RealModule

end Form

end CliffordAlgebra
