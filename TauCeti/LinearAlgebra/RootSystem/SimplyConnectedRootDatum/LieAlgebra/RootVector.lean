/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.RootSystem

/-!
# The Chevalley system of the pinned rational Lie algebra

`TauCeti.DynkinType.exists_isChevalleySystem` shows that the pinned rational Lie algebra
`TauCeti.DynkinType.lieAlgebra` has a Chevalley system for its signed Chevalley involution `ω`
whose root vectors at `±αᵢ` are the Bourbaki-numbered generators `eᵢ` and `fᵢ`. Those conditions
fix such a system only up to signs at the non-simple roots. This file names one,
`TauCeti.DynkinType.chevalleySystem`, indexed by the root numbers `Fin t.numRoots` of
`TauCeti.DynkinType.simplyConnectedRootDatum` and written down from Geck's generators, by
recursion on the height of a root:

* at a simple root `αᵢ` it is `eᵢ`;
* at a positive root `γ` that is not simple, let `i` be the least Bourbaki node for which
  `γ - αᵢ` is a root `β`; then it is `(r + 1)⁻¹ • ⁅eᵢ, e_β⁆`, where `r` is the largest integer
  with `β - r αᵢ` a root;
* at a negative root `-γ` it is `-ω (e_γ)`.

Compared step by step with any Chevalley system pinned to the generators, through the root-string
normalization `TauCeti.IsChevalleySystem.inv_smul_lie_eq_or_eq_neg`, the named family agrees with
it up to a sign that is the same at `γ` and at `-γ`. It is therefore itself a Chevalley system for
`ω`, so its structure constants are the integers `±(r + 1)` of
`TauCeti.IsChevalleySystem.intStructureConstant`, and it names a root vector for every root, as the
Kostant `ℤ`-form and the root subgroups of non-simple roots require.

## Main definitions

* `TauCeti.DynkinType.chevalleySystem`: the root vector attached to each root number.

## Main results

* `TauCeti.DynkinType.chevalleySystem_simpleIndex` and
  `TauCeti.DynkinType.chevalleySystem_reflectionPerm_simpleIndex`: the root vectors at `αᵢ` and
  `-αᵢ` are the numbered generators `eᵢ` and `fᵢ`.
* `TauCeti.DynkinType.exists_chevalleySystem_eq_inv_smul_lie`: the recursion at a positive root
  that is not simple.
* `TauCeti.DynkinType.chevalleyInvolution_chevalleySystem`: the Chevalley involution sends the
  root vector of `γ` to minus that of `-γ`.
* `TauCeti.DynkinType.isChevalleySystem_chevalleySystem`: the family is a Chevalley system for the
  signed Chevalley involution.
* `TauCeti.DynkinType.chevalleySystem_mem_rootSpace` and
  `TauCeti.DynkinType.lie_chevalleySystem_reflectionPerm_self`: each root vector lies in its root
  space, and the root vectors of `γ` and `-γ` bracket to the coroot of `γ`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads
-- them; the module defining `TauCeti.DynkinType.lieAlgebra` activates the same instance locally.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-! ## Removing a simple root from a positive root -/

/-- Root `γ` of the rational root system is the simple root `αᵢ` plus a root. -/
private abbrev IsSimpleSummand (γ : Fin t.numRoots) (i : Fin t.rank) : Prop :=
  ∃ β, (t.rationalRootSystem ht).root γ =
    (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β

variable {t ht}

private theorem simpleIndex_mem_support (i : Fin t.rank) :
    t.simpleIndex ht i ∈ (t.rationalBase ht).support := by
  rw [← coe_simpleSupportEquiv]
  exact (t.simpleSupportEquiv ht i).2

/-- A positive root that is not simple is a simple root plus a root. -/
private theorem exists_isSimpleSummand {γ : Fin t.numRoots} (hγ : (t.rationalBase ht).IsPos γ)
    (hs : γ ∉ (t.rationalBase ht).support) : ∃ i, t.IsSimpleSummand ht γ i := by
  obtain ⟨j, hj, hpos⟩ := hγ.exists_mem_support_pos_pairingIn
  rw [RootPairing.zero_lt_pairingIn_iff'] at hpos
  obtain ⟨β, hβ⟩ := (t.rationalRootSystem ht).root_sub_root_mem_of_pairingIn_pos hpos
    fun h => hs (h ▸ hj)
  refine ⟨(t.simpleSupportEquiv ht).symm ⟨j, hj⟩, β, ?_⟩
  rw [← coe_simpleSupportEquiv, Equiv.apply_symm_apply, hβ]
  abel

/-- The least Bourbaki node `i` for which `γ - αᵢ` is a root. -/
private def peelNode {γ : Fin t.numRoots} (h : ∃ i, t.IsSimpleSummand ht γ i) : Fin t.rank :=
  Fin.find _ h

/-- The root `γ - αᵢ`, for `i` the node `TauCeti.DynkinType.peelNode`. -/
private def peelRoot {γ : Fin t.numRoots} (h : ∃ i, t.IsSimpleSummand ht γ i) : Fin t.numRoots :=
  Fin.find _ (Fin.find_spec h)

private theorem root_eq_add_peelRoot {γ : Fin t.numRoots} (h : ∃ i, t.IsSimpleSummand ht γ i) :
    (t.rationalRootSystem ht).root γ =
      (t.rationalRootSystem ht).root (t.simpleIndex ht (peelNode h)) +
        (t.rationalRootSystem ht).root (peelRoot h) :=
  Fin.find_spec (Fin.find_spec h)

private theorem height_peelRoot {γ : Fin t.numRoots} (h : ∃ i, t.IsSimpleSummand ht γ i) :
    (t.rationalBase ht).height (peelRoot h) = (t.rationalBase ht).height γ - 1 := by
  rw [(t.rationalBase ht).height_sub (k := peelRoot h) (i := γ)
      (j := t.simpleIndex ht (peelNode h)) (by rw [root_eq_add_peelRoot h]; abel),
    RootPairing.Base.height_one_of_mem_support (simpleIndex_mem_support _)]

private theorem isPos_peelRoot {γ : Fin t.numRoots} (hγ : (t.rationalBase ht).IsPos γ)
    (h : ∃ i, t.IsSimpleSummand ht γ i) : (t.rationalBase ht).IsPos (peelRoot h) :=
  hγ.sub (simpleIndex_mem_support _) (by rw [root_eq_add_peelRoot h]; abel)

private theorem isPos_reflectionPerm_self {γ : Fin t.numRoots}
    (hγ : ¬(t.rationalBase ht).IsPos γ) :
    (t.rationalBase ht).IsPos ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) := by
  rw [← reflectionPerm_rationalRootSystem]
  exact (RootPairing.Base.IsPos.or_neg (t.rationalBase ht) γ).resolve_left hγ

private theorem height_reflectionPerm_self (γ : Fin t.numRoots) :
    (t.rationalBase ht).height ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) =
      -(t.rationalBase ht).height γ := by
  rw [← reflectionPerm_rationalRootSystem]
  exact (t.rationalBase ht).height_reflectionPerm_self γ

private theorem reflectionPerm_reflectionPerm_self (γ : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).reflectionPerm
        ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)
        ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) = γ :=
  letI := (t.simplyConnectedRootDatum ht).indexNeg
  neg_neg γ

variable (t ht)

/-! ## The named Chevalley system -/

/-- **The Chevalley system of the pinned rational Lie algebra.** The root vector attached to the
root numbered `γ`: the generator `eᵢ` at a simple root `αᵢ`; at a positive root `γ` that is not
simple, `(r + 1)⁻¹ • ⁅eᵢ, e_β⁆` for `i` the least Bourbaki node with `γ - αᵢ` a root `β` and `r`
the largest integer with `β - r αᵢ` a root; and `-ω (e_{-γ})` at a negative root `γ`, for `ω` the
signed Chevalley involution. -/
def chevalleySystem (γ : Fin t.numRoots) : t.lieAlgebra ht :=
  if hs : γ ∈ (t.rationalBase ht).support then
    (t.lieBasis ht).e ((t.simpleSupportEquiv ht).symm ⟨γ, hs⟩)
  else if hγ : 0 < (t.rationalBase ht).height γ then
    ((chainBotCoeff
        (t.rootEquiv ht (t.simpleIndex ht (peelNode (exists_isSimpleSummand hγ hs))) :
          Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))
        (t.rootEquiv ht (peelRoot (exists_isSimpleSummand hγ hs)) :
          Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) + 1 : ℕ) : ℚ)⁻¹ •
      ⁅(t.lieBasis ht).e (peelNode (exists_isSimpleSummand hγ hs)),
        chevalleySystem (peelRoot (exists_isSimpleSummand hγ hs))⁆
  else
    -t.chevalleyInvolution ht
      (chevalleySystem ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ))
termination_by 2 * ((t.rationalBase ht).height γ).natAbs +
  if 0 < (t.rationalBase ht).height γ then 0 else 1
decreasing_by
  · have h₁ := height_peelRoot (exists_isSimpleSummand hγ hs)
    have h₂ := isPos_peelRoot hγ (exists_isSimpleSummand hγ hs)
    rw [RootPairing.Base.isPos_iff] at h₂
    simp only [h₂, hγ, ↓reduceIte]
    omega
  · have h₁ := height_reflectionPerm_self (ht := ht) γ
    have h₂ := isPos_reflectionPerm_self (ht := ht) (γ := γ) hγ
    rw [RootPairing.Base.isPos_iff] at h₂
    simp only [h₂, hγ, ↓reduceIte]
    omega

variable {t ht}

private theorem chevalleySystem_of_mem_support {γ : Fin t.numRoots}
    (hs : γ ∈ (t.rationalBase ht).support) :
    t.chevalleySystem ht γ = (t.lieBasis ht).e ((t.simpleSupportEquiv ht).symm ⟨γ, hs⟩) := by
  rw [chevalleySystem]
  simp only [hs, ↓reduceDIte]

private theorem chevalleySystem_of_height_nonpos {γ : Fin t.numRoots}
    (hγ : ¬0 < (t.rationalBase ht).height γ) :
    t.chevalleySystem ht γ = -t.chevalleyInvolution ht
      (t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)) := by
  have hs : γ ∉ (t.rationalBase ht).support := fun hs =>
    hγ ((RootPairing.Base.isPos_iff _).1 (RootPairing.Base.isPos_of_mem_support hs))
  rw [chevalleySystem]
  simp only [hs, hγ, ↓reduceDIte]

private theorem coe_rootEquiv_reflectionPerm_self (γ : Fin t.numRoots) :
    (t.rootEquiv ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) :
        Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) =
      -(t.rootEquiv ht γ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) := by
  rw [rootEquiv_reflectionPerm_self, LieAlgebra.IsKilling.val_neg_root]

/-- **The recursion at a positive root that is not simple.** Such a root `γ` is `αᵢ + β` for a
Bourbaki node `i` and a root `β`, and its root vector is `(r + 1)⁻¹ • ⁅eᵢ, e_β⁆`, where `r` is the
largest integer with `β - r αᵢ` a root. -/
theorem exists_chevalleySystem_eq_inv_smul_lie {γ : Fin t.numRoots}
    (hγ : (t.rationalBase ht).IsPos γ) (hs : γ ∉ (t.rationalBase ht).support) :
    ∃ i β, (t.rationalRootSystem ht).root γ =
        (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β ∧
      t.chevalleySystem ht γ =
        ((chainBotCoeff (t.rootEquiv ht (t.simpleIndex ht i) :
            Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))
          (t.rootEquiv ht β : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) + 1 : ℕ) :
            ℚ)⁻¹ •
          ⁅(t.lieBasis ht).e i, t.chevalleySystem ht β⁆ := by
  have hγ' : 0 < (t.rationalBase ht).height γ := (RootPairing.Base.isPos_iff _).1 hγ
  refine ⟨peelNode (exists_isSimpleSummand hγ hs), peelRoot (exists_isSimpleSummand hγ hs),
    root_eq_add_peelRoot _, ?_⟩
  rw [chevalleySystem]
  simp only [hs, hγ', ↓reduceDIte]

variable (t ht)

/-- **The root vector at a simple root `αᵢ` is the numbered generator `eᵢ`.** -/
@[simp] theorem chevalleySystem_simpleIndex (i : Fin t.rank) :
    t.chevalleySystem ht (t.simpleIndex ht i) = (t.lieBasis ht).e i := by
  rw [chevalleySystem_of_mem_support (simpleIndex_mem_support i)]
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (coe_simpleSupportEquiv t ht i).symm

/-- **The Chevalley involution exchanges opposite root vectors**: it sends the root vector of `γ`
to minus that of `-γ`. -/
theorem chevalleyInvolution_chevalleySystem (γ : Fin t.numRoots) :
    t.chevalleyInvolution ht (t.chevalleySystem ht γ) =
      -t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) := by
  by_cases hγ : 0 < (t.rationalBase ht).height γ
  · have hneg : ¬0 < (t.rationalBase ht).height
        ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) := by
      rw [height_reflectionPerm_self]
      omega
    rw [chevalleySystem_of_height_nonpos hneg, reflectionPerm_reflectionPerm_self, neg_neg]
  · have hinv := (t.chevalleyInvolution ht).symm_apply_apply
      (t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ))
    rw [chevalleyInvolution_symm] at hinv
    rw [chevalleySystem_of_height_nonpos hγ, map_neg, hinv]

/-- **The root vector at a negative simple root `-αᵢ` is the numbered generator `fᵢ`.** -/
@[simp] theorem chevalleySystem_reflectionPerm_simpleIndex (i : Fin t.rank) :
    t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
      (t.simpleIndex ht i)) = (t.lieBasis ht).f i := by
  have h := t.chevalleyInvolution_chevalleySystem ht (t.simpleIndex ht i)
  rw [chevalleySystem_simpleIndex, chevalleyInvolution_lieBasis_e, neg_inj] at h
  exact h.symm

variable {t ht}

/-! ## Comparison with a pinned Chevalley system

The sign comparison is carried out for any root-indexed family satisfying the defining equations
of `TauCeti.DynkinType.chevalleySystem`, against the root-indexed family `X` of a pinned Chevalley
system, with the root-string coefficient left abstract. -/

/-- At a positive root, a family `y` satisfying the simple-root and recursion equations is a sign
times a family `X` that has the same simple root vectors and whose recursion step holds up to
sign. -/
private theorem exists_eq_smul_of_height_pos {X y : Fin t.numRoots → t.lieAlgebra ht}
    {c : Fin t.rank → Fin t.numRoots → ℚ}
    (hX : ∀ γ i β, (t.rationalRootSystem ht).root γ =
        (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β →
      c i β • ⁅X (t.simpleIndex ht i), X β⁆ = X γ ∨
        c i β • ⁅X (t.simpleIndex ht i), X β⁆ = -X γ)
    (hXs : ∀ i, X (t.simpleIndex ht i) = (t.lieBasis ht).e i)
    (hys : ∀ i, y (t.simpleIndex ht i) = (t.lieBasis ht).e i)
    (hystep : ∀ γ, (t.rationalBase ht).IsPos γ → γ ∉ (t.rationalBase ht).support →
      ∃ i β, (t.rationalRootSystem ht).root γ =
          (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β ∧
        y γ = c i β • ⁅(t.lieBasis ht).e i, y β⁆)
    (n : ℕ) (γ : Fin t.numRoots) (hn : ((t.rationalBase ht).height γ).toNat = n)
    (hγ : 0 < (t.rationalBase ht).height γ) :
    ∃ s : ℚ, s * s = 1 ∧ y γ = s • X γ := by
  induction n using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
  by_cases hs : γ ∈ (t.rationalBase ht).support
  · obtain ⟨i, rfl⟩ : ∃ i, t.simpleIndex ht i = γ :=
      ⟨(t.simpleSupportEquiv ht).symm ⟨γ, hs⟩, by
        rw [← coe_simpleSupportEquiv, Equiv.apply_symm_apply]⟩
    exact ⟨1, one_mul 1, by rw [hys, hXs, one_smul]⟩
  · obtain ⟨i, β, hroot, hy⟩ := hystep γ ((RootPairing.Base.isPos_iff _).2 hγ) hs
    have hroot' : (t.rationalRootSystem ht).root β =
        (t.rationalRootSystem ht).root γ - (t.rationalRootSystem ht).root (t.simpleIndex ht i) := by
      rw [hroot]
      abel
    have hβ : (t.rationalBase ht).height β = (t.rationalBase ht).height γ - 1 := by
      rw [(t.rationalBase ht).height_sub hroot',
        RootPairing.Base.height_one_of_mem_support (simpleIndex_mem_support _)]
    have hβpos : 0 < (t.rationalBase ht).height β :=
      (RootPairing.Base.isPos_iff _).1 (((RootPairing.Base.isPos_iff _).2 hγ).sub
        (simpleIndex_mem_support i) hroot')
    obtain ⟨s, hs₂, hsβ⟩ := ih ((t.rationalBase ht).height β).toNat (by omega) β rfl hβpos
    rw [hy, hsβ, lie_smul, smul_comm]
    rcases hX γ i β hroot with h | h <;> rw [hXs] at h
    · exact ⟨s, hs₂, by rw [h]⟩
    · exact ⟨-s, by rw [neg_mul_neg, hs₂], by rw [h, smul_neg, neg_smul]⟩

/-- At every root `γ`, a family `y` satisfying the defining equations agrees with `X` at `γ` and at
`-γ` up to one common sign, when both are exchanged with a sign by the Chevalley involution. -/
private theorem exists_eq_smul {X y : Fin t.numRoots → t.lieAlgebra ht}
    {c : Fin t.rank → Fin t.numRoots → ℚ}
    (hX : ∀ γ i β, (t.rationalRootSystem ht).root γ =
        (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β →
      c i β • ⁅X (t.simpleIndex ht i), X β⁆ = X γ ∨
        c i β • ⁅X (t.simpleIndex ht i), X β⁆ = -X γ)
    (hXs : ∀ i, X (t.simpleIndex ht i) = (t.lieBasis ht).e i)
    (hXω : ∀ γ, t.chevalleyInvolution ht (X γ) =
      -X ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ))
    (hys : ∀ i, y (t.simpleIndex ht i) = (t.lieBasis ht).e i)
    (hystep : ∀ γ, (t.rationalBase ht).IsPos γ → γ ∉ (t.rationalBase ht).support →
      ∃ i β, (t.rationalRootSystem ht).root γ =
          (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β ∧
        y γ = c i β • ⁅(t.lieBasis ht).e i, y β⁆)
    (hyω : ∀ γ, t.chevalleyInvolution ht (y γ) =
      -y ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ))
    (γ : Fin t.numRoots) :
    ∃ s : ℚ, s * s = 1 ∧ y γ = s • X γ ∧
      y ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) =
        s • X ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) := by
  have hpos : ∀ γ, 0 < (t.rationalBase ht).height γ → ∃ s : ℚ, s * s = 1 ∧ y γ = s • X γ ∧
      y ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) =
        s • X ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) := by
    intro γ hγ
    obtain ⟨s, hs, hy⟩ := exists_eq_smul_of_height_pos hX hXs hys hystep _ γ rfl hγ
    have h := hyω γ
    rw [hy, map_smul, hXω, smul_neg, neg_inj] at h
    exact ⟨s, hs, hy, h.symm⟩
  by_cases hγ : 0 < (t.rationalBase ht).height γ
  · exact hpos γ hγ
  · have hne := (t.rationalBase ht).height_ne_zero γ
    obtain ⟨s, hs, h₁, h₂⟩ := hpos ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)
      (by rw [height_reflectionPerm_self]; omega)
    exact ⟨s, hs, reflectionPerm_reflectionPerm_self γ ▸ h₂, h₁⟩

/-- A pinned Chevalley system, read in the root numbering: its root vectors at the simple roots are
the generators `eᵢ`. -/
private theorem exists_isChevalleySystem_rootEquiv_simpleIndex :
    ∃ x : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht,
      IsChevalleySystem (t.chevalleyInvolution ht) x ∧
        ∀ i, x (t.rootEquiv ht (t.simpleIndex ht i)) = (t.lieBasis ht).e i := by
  obtain ⟨x, hx, hxe⟩ := t.exists_isChevalleySystem ht
  refine ⟨x, hx, fun i => ?_⟩
  rw [rootEquiv_simpleIndex]
  exact (hxe i).1

/-- A Chevalley system for the Chevalley involution, read in the root numbering, exchanges the root
vectors of `γ` and `-γ` with a sign. -/
private theorem map_root_rootEquiv
    {x : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht}
    (hx : IsChevalleySystem (t.chevalleyInvolution ht) x) (γ : Fin t.numRoots) :
    t.chevalleyInvolution ht (x (t.rootEquiv ht γ)) =
      -x (t.rootEquiv ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)) := by
  rw [hx.map_root, coe_rootEquiv_reflectionPerm_self]

/-- A family that agrees with a Chevalley system up to sign lies in the root spaces. -/
private theorem mem_rootSpace_of_eq_smul
    {x : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht}
    (hx : IsChevalleySystem (t.chevalleyInvolution ht) x) {y : Fin t.numRoots → t.lieAlgebra ht}
    {γ : Fin t.numRoots} {s : ℚ} (h : y γ = s • x (t.rootEquiv ht γ)) :
    y γ ∈ rootSpace (t.cartanSubalgebra ht)
      (t.rootEquiv ht γ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) := by
  rw [h]
  exact Submodule.smul_mem _ s (hx.toIsSl2System.mem_rootSpace _)

/-- A family that agrees with a Chevalley system up to signs, equal at `γ` and `-γ`, brackets its
vectors at `γ` and `-γ` to the coroot of `γ`. -/
private theorem lie_eq_coroot_of_eq_smul
    {x : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht) → t.lieAlgebra ht}
    (hx : IsChevalleySystem (t.chevalleyInvolution ht) x) {y : Fin t.numRoots → t.lieAlgebra ht}
    {γ : Fin t.numRoots} {s : ℚ} (hs : s * s = 1) (h₁ : y γ = s • x (t.rootEquiv ht γ))
    (h₂ : y ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) =
      s • x (t.rootEquiv ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ))) :
    ⁅y γ, y ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)⁆ =
      ((coroot (t.rootEquiv ht γ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) :
        t.cartanSubalgebra ht) : t.lieAlgebra ht) := by
  rw [coe_rootEquiv_reflectionPerm_self] at h₂
  -- Rewriting the goal with `h₂` would compare `γ` with `-γ` by unfolding the root tables, so the
  -- two equations are applied by congruence instead.
  have hss (a b : t.lieAlgebra ht) : ⁅s • a, s • b⁆ = ⁅a, b⁆ := by
    rw [smul_lie, lie_smul, smul_smul, hs, one_smul]
  exact (congrArg₂ (fun a b => ⁅a, b⁆) h₁ h₂).trans ((hss _ _).trans
    (hx.toIsSl2System.lie_neg _ (LieSubalgebra.isNonZero_coe_root _)))

/-- A family satisfying the defining equations of `TauCeti.DynkinType.chevalleySystem`, extended
by `0` at the zero weight, is a Chevalley system for the Chevalley involution: it agrees with the
root vectors of a pinned Chevalley system up to signs that are equal at opposite roots. -/
private theorem isChevalleySystem_extendRootFamily_of_recursion
    {y : Fin t.numRoots → t.lieAlgebra ht}
    (hys : ∀ i, y (t.simpleIndex ht i) = (t.lieBasis ht).e i)
    (hystep : ∀ γ, (t.rationalBase ht).IsPos γ → γ ∉ (t.rationalBase ht).support →
      ∃ i β, (t.rationalRootSystem ht).root γ =
          (t.rationalRootSystem ht).root (t.simpleIndex ht i) + (t.rationalRootSystem ht).root β ∧
        y γ = ((chainBotCoeff (t.rootEquiv ht (t.simpleIndex ht i) :
              Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))
            (t.rootEquiv ht β : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) + 1 : ℕ) :
              ℚ)⁻¹ • ⁅(t.lieBasis ht).e i, y β⁆)
    (hyω : ∀ γ, t.chevalleyInvolution ht (y γ) =
      -y ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)) :
    IsChevalleySystem (t.chevalleyInvolution ht) (extendRootFamily y) := by
  obtain ⟨x, hx, hXs⟩ := exists_isChevalleySystem_rootEquiv_simpleIndex (ht := ht)
  have hsign := exists_eq_smul (X := fun γ => x (t.rootEquiv ht γ))
    (fun _ _ _ hroot => hx.inv_smul_lie_eq_or_eq_neg _ _ _ (LieSubalgebra.isNonZero_coe_root _)
      (LieSubalgebra.isNonZero_coe_root _) (LieSubalgebra.isNonZero_coe_root _)
      (t.coe_rootEquiv_eq_add ht hroot))
    hXs (map_root_rootEquiv hx) hys hystep hyω
  rw [isChevalleySystem_extendRootFamily_iff, isSl2System_extendRootFamily_iff]
  refine ⟨⟨fun γ => ?_, fun γ => ?_⟩, hyω⟩
  · obtain ⟨s, -, h, -⟩ := hsign γ
    exact mem_rootSpace_of_eq_smul hx h
  · obtain ⟨s, hs, h₁, h₂⟩ := hsign γ
    exact lie_eq_coroot_of_eq_smul hx hs h₁ h₂

variable (t ht)

/-- **The named family is a Chevalley system.** Extended by `0` at the zero weight, the root
vectors `TauCeti.DynkinType.chevalleySystem` form a Chevalley system for the signed Chevalley
involution of the pinned rational Lie algebra. -/
theorem isChevalleySystem_chevalleySystem :
    IsChevalleySystem (t.chevalleyInvolution ht) (extendRootFamily (t.chevalleySystem ht)) :=
  isChevalleySystem_extendRootFamily_of_recursion (t.chevalleySystem_simpleIndex ht)
    (fun _ hγ hs => exists_chevalleySystem_eq_inv_smul_lie hγ hs)
    (t.chevalleyInvolution_chevalleySystem ht)

/-- Each named root vector lies in the root space of its root. -/
theorem chevalleySystem_mem_rootSpace (γ : Fin t.numRoots) :
    t.chevalleySystem ht γ ∈ rootSpace (t.cartanSubalgebra ht)
      (t.rootEquiv ht γ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) :=
  ((isSl2System_extendRootFamily_iff _).1
    (t.isChevalleySystem_chevalleySystem ht).toIsSl2System).1 γ

/-- The named root vectors of `γ` and `-γ` bracket to the coroot of `γ`. -/
theorem lie_chevalleySystem_reflectionPerm_self (γ : Fin t.numRoots) :
    ⁅t.chevalleySystem ht γ,
        t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)⁆ =
      ((coroot (t.rootEquiv ht γ : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht)) :
        t.cartanSubalgebra ht) : t.lieAlgebra ht) :=
  ((isSl2System_extendRootFamily_iff _).1
    (t.isChevalleySystem_chevalleySystem ht).toIsSl2System).2 γ

end

end TauCeti.DynkinType
