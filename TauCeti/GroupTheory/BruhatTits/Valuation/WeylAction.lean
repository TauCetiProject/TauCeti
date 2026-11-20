/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BruhatTits.Valuation.Basic
public import TauCeti.GroupTheory.BruhatTits.WeylGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.GroupTheory.Commutator
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice

/-!
# Discrete valuations and the action of the Weyl normalizer on valuations

Defines `Valuation.IsDiscrete`, `MulAction D.weylNormalizer (Valuation D)`,
`Valuation.smul_reflection` (Bruhat–Tits I, Proposition 6.2.7), and
`Valuation.existsUnique_mem_corootSpan_smul_eq_shift` (§§6.2.5–6.2.21).
-/

public section

open scoped Pointwise commutatorElement

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {G : Type*} [Group G]

section Discrete
variable {R : Type*} [Field R] [LinearOrder R] [Module R M] [Module R N]
  {P : RootPairing ι R M N} {D : RootDatum P G}
namespace Valuation
/-- A valuation is *discrete* if each `Γ a ∩ [r, s]` is finite (Bruhat–Tits I, 6.2.21). -/
def IsDiscrete (φ : Valuation D) : Prop := ∀ (i : ι) (r s : ℝ), (φ.valueSet i ∩ Set.Icc r s).Finite
theorem isDiscrete_iff (φ : Valuation D) :
    φ.IsDiscrete ↔ ∀ (i : ι) (r s : ℝ), (φ.valueSet i ∩ Set.Icc r s).Finite := Iff.rfl
theorem IsDiscrete.finite_inter_Icc {φ : Valuation D} (h : φ.IsDiscrete) (i : ι) (r s : ℝ) :
    (φ.valueSet i ∩ Set.Icc r s).Finite := h i r s
@[simp] theorem isDiscrete_of_isEmpty [IsEmpty ι] (φ : Valuation D) : φ.IsDiscrete := isEmptyElim
private theorem apply_congr (φ : Valuation D) {i j : ι} (hij : i = j) {u : D.U i} {v : D.U j}
    (huv : (u : G) = v) : φ i u = φ j v := by subst hij; exact congrArg (φ i) (Subtype.ext huv)
private theorem ext_filtration {φ ψ : Valuation D}
    (h : ∀ i k, φ.filtration i k = ψ.filtration i k) : φ = ψ :=
  ext fun i u ↦ WithTop.eq_of_forall_coe_le_iff fun k ↦ by
    rw [← φ.coe_mem_filtration_iff, h i k, ψ.coe_mem_filtration_iff]
private theorem exists_apply_eq_coe_of_index (φ : Valuation D) (i : ι) :
    ∃ (k : ℝ) (u : D.U i), φ i u = k :=
  let ⟨k, hk⟩ := (φ.valueSet_nontrivial i).nonempty; ⟨k, φ.mem_valueSet_iff.mp hk⟩
end Valuation
end Discrete

section WeylNormalizer
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Module R M] [Module R N] {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]
namespace RootDatum
variable (D : RootDatum P G)
theorem inv_mul_mul_mem_U_weylNormalizer (n : D.weylNormalizer) {i : ι} {u : G} (hu : u ∈ D.U i) :
    (n : G)⁻¹ * u * n ∈ D.U (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) := by
  rw [← Subgroup.mem_conjAct_smul_iff, D.weylGroupHom_conj, ← Equiv.Perm.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Equiv.Perm.one_apply]; exact hu
theorem inv_mul_mul_mem_reflectionCoset_weylNormalizer (n : D.weylNormalizer) {i : ι} {m : G}
    (hm : m ∈ D.reflectionCoset i) :
    (n : G)⁻¹ * m * n ∈ D.reflectionCoset (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) := by
  set j := P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i
  obtain ⟨m', hm'⟩ := D.reflectionCoset_nonempty j
  let nm : D.weylNormalizer := ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩
  let nm' : D.weylNormalizer := ⟨m', D.reflectionCoset_subset_weylNormalizer j hm'⟩
  have hker : n⁻¹ * nm * n * nm'⁻¹ ∈ D.weylGroupHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      D.weylGroupHom_reflection hm, D.weylGroupHom_reflection hm']
    have hconj := RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj P (D.weylGroupHom n)⁻¹ i
    rw [inv_inv] at hconj; rw [← hconj, mul_inv_cancel]
  rw [D.ker_weylGroupHom, Subgroup.mem_subgroupOf] at hker
  exact (D.mem_reflectionCoset_iff_mul_inv_mem_T hm').mpr hker
end RootDatum

namespace Valuation
variable {D : RootDatum P G}
theorem ext_of_isIndivisible {φ ψ : Valuation D}
    (h : ∀ i : ι, P.IsIndivisible i → ∀ u : D.U i, φ i u = ψ i u) : φ = ψ := by
  ext j u; rcases P.isIndivisible_or_exists_root_eq_two_smul j with hj | ⟨i, hi, hij⟩
  · exact h j hj u
  · rw [φ.apply_eq_two_smul i j hij u, ψ.apply_eq_two_smul i j hij u, h i hi]
private noncomputable abbrev permInv (n : D.weylNormalizer) (i : ι) : ι :=
  P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i
private noncomputable def conjU (n : D.weylNormalizer) {i : ι} (u : D.U i) : D.U (permInv n i) :=
  ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
private theorem mem_U_of_mem_permInv (n : D.weylNormalizer) {i : ι} {g : G}
    (hg : g ∈ D.U (permInv n i)) : (n : G) * g * (n : G)⁻¹ ∈ D.U i := by
  have hp : permInv n⁻¹ (permInv n i) = i := by
    rw [permInv, permInv, D.weylGroupHom.map_inv n, inv_inv, ← Equiv.Perm.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have h : ((n⁻¹ : D.weylNormalizer) : G)⁻¹ * g * (n⁻¹ : D.weylNormalizer) ∈ D.U i :=
    hp ▸ D.inv_mul_mul_mem_U_weylNormalizer n⁻¹ hg
  simpa only [Subgroup.coe_inv, inv_inv] using h
private theorem smul_three_le_encard_range (n : D.weylNormalizer) (φ : Valuation D) (i : ι) :
    3 ≤ (Set.range fun u : D.U i ↦ φ (permInv n i) (conjU n u)).encard := by
  suffices (Set.range fun u : D.U i ↦ φ (permInv n i) (conjU n u)) =
      Set.range (φ (permInv n i)) from this ▸ φ.three_le_encard_range _
  refine Set.Subset.antisymm (Set.range_comp_subset_range _ _) fun _ ⟨v, hv⟩ ↦
    ⟨⟨_, mem_U_of_mem_permInv n v.2⟩, (φ.apply_congr rfl (by dsimp [conjU]; group)).trans hv⟩
private theorem smul_exists_apply_eq_apply_conj_add (n : D.weylNormalizer) (φ : Valuation D)
    (i : ι) (m : G) (hm : m ∈ D.reflectionCoset i) :
    ∃ c : ℝ, ∀ u : D.U (P.reflectionPerm i i), u ≠ 1 →
      φ (permInv n (P.reflectionPerm i i)) (conjU n u) =
        φ (permInv n i)
          (conjU n ⟨m * u * m⁻¹, D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm u.2⟩) + c := by
  have hneg : permInv n (P.reflectionPerm i i) = P.reflectionPerm (permInv n i) (permInv n i) :=
    P.weylGroupToPerm_neg (D.weylGroupHom n)⁻¹ i
  obtain ⟨c, hc⟩ := φ.exists_apply_eq_apply_conj_add (permInv n i) ((n : G)⁻¹ * m * n)
    (D.inv_mul_mul_mem_reflectionCoset_weylNormalizer n hm)
  refine ⟨c, fun u hu ↦ ?_⟩
  let u' : D.U (P.reflectionPerm (permInv n i) (permInv n i)) :=
    ⟨(n : G)⁻¹ * u * n, hneg ▸ D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
  have hu' : u' ≠ 1 := fun h ↦ hu <| Subtype.ext <|
    (conj_eq_one_iff (a := (n : G)⁻¹) (b := (u : G))).mp
      (by simpa only [u', inv_inv, Subgroup.coe_one] using congrArg Subtype.val h)
  exact (φ.apply_congr hneg (v := u') rfl).trans ((hc u' hu').trans
    (congrArg (· + (c : WithTop ℝ)) (φ.apply_congr rfl (by dsimp [u', conjU]; group))))
private theorem smul_commutator_mem (n : D.weylNormalizer) (φ : Valuation D) (i j : ι)
    (hij : ∀ c : R, 0 < c → P.root j ≠ -(c • P.root i)) (k l : ℝ) (u : D.U i) (v : D.U j)
    (hu : (k : WithTop ℝ) ≤ φ (permInv n i) (conjU n u))
    (hv : (l : WithTop ℝ) ≤ φ (permInv n j) (conjU n v)) :
    ⁅(u : G), (v : G)⁆ ∈ Subgroup.closure {g | ∃ (m : ι) (p q : ℕ), 0 < p ∧ 0 < q ∧
      P.root m = p • P.root i + q • P.root j ∧
      ∃ hg : g ∈ D.U m, ((p * k + q * l : ℝ) : WithTop ℝ) ≤ φ (permInv n m) (conjU n ⟨g, hg⟩)} := by
  let e := (D.weylGroupHom n : P.Aut).weightEquiv
  have hr (b : ι) : e (P.root (permInv n b)) = P.root b :=
    (P.weylGroup_apply_root (D.weylGroupHom n) (permInv n b)).trans <| by
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have hij' : ∀ c : R, 0 < c → P.root (permInv n j) ≠ -(c • P.root (permInv n i)) :=
    fun c hc h0 ↦ hij c hc <| by have h1 := congrArg e h0; rwa [map_neg, map_smul, hr i, hr j] at h1
  have hcm := φ.commutator_mem _ _ hij' k l (conjU n u) (conjU n v) hu hv
  have hcomm_eq : ⁅(conjU n u : G), (conjU n v : G)⁆ = (n : G)⁻¹ * ⁅(u : G), (v : G)⁆ * n := by
    simp only [conjU, commutatorElement_def]; group
  rw [hcomm_eq] at hcm
  have hconj_comm :
      (n : G) * ((n : G)⁻¹ * ⁅(u : G), (v : G)⁆ * n) * (n : G)⁻¹ = ⁅(u : G), (v : G)⁆ := by group
  rw [← hconj_comm]
  generalize (n : G)⁻¹ * ⁅(u : G), (v : G)⁆ * n = z at hcm ⊢
  induction hcm using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m', p, q, hp, hq, hm', hyU, hval⟩ := hy
    set m := P.weylGroupToPerm (D.weylGroupHom n) m'
    have hwm : permInv n m = m' := by simp [permInv, m, ← Equiv.Perm.mul_apply]
    have hrm : P.root m = p • P.root i + q • P.root j := by
      have h1 := congrArg e hm'; rw [map_add, map_nsmul, map_nsmul, hr i, hr j] at h1
      exact (P.weylGroup_apply_root (D.weylGroupHom n) m').symm.trans h1
    have hgU : (n : G) * y * (n : G)⁻¹ ∈ D.U m := by
      rw [← D.weylGroupHom_conj n m', ← ConjAct.toConjAct_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hyU
    exact Subgroup.subset_closure ⟨m, p, q, hp, hq, hrm, hgU,
      hval.trans_eq (φ.apply_congr hwm.symm (by dsimp [conjU]; group))⟩
  | one => simp
  | mul x y _ _ ihx ihy => exact (by group : (n : G) * (x * y) * (n : G)⁻¹ =
      ((n : G) * x * (n : G)⁻¹) * ((n : G) * y * (n : G)⁻¹)) ▸ mul_mem ihx ihy
  | inv x _ ih =>
    exact (by group : (n : G) * x⁻¹ * (n : G)⁻¹ = ((n : G) * x * (n : G)⁻¹)⁻¹) ▸ inv_mem ih
private theorem smul_apply_reflectionPerm_left (n : D.weylNormalizer) (φ : Valuation D) (i : ι)
    (u : D.U i) (u' u'' : D.U (P.reflectionPerm i i))
    (h : (u' : G) * u * u'' ∈ D.reflectionCoset i) :
    φ (permInv n (P.reflectionPerm i i)) (conjU n u') = -φ (permInv n i) (conjU n u) := by
  have hneg : permInv n (P.reflectionPerm i i) = P.reflectionPerm (permInv n i) (permInv n i) :=
    P.weylGroupToPerm_neg (D.weylGroupHom n)⁻¹ i
  have hm' : ((n : G)⁻¹ * u' * n) * ((n : G)⁻¹ * u * n) * ((n : G)⁻¹ * u'' * n) ∈
      D.reflectionCoset (permInv n i) :=
    (by group : (n : G)⁻¹ * ((u' : G) * u * u'') * n =
      ((n : G)⁻¹ * u' * n) * ((n : G)⁻¹ * u * n) * ((n : G)⁻¹ * u'' * n)) ▸
      D.inv_mul_mul_mem_reflectionCoset_weylNormalizer n h
  let v' : D.U (P.reflectionPerm (permInv n i) (permInv n i)) :=
    ⟨(n : G)⁻¹ * u' * n, hneg ▸ D.inv_mul_mul_mem_U_weylNormalizer n u'.2⟩
  let v'' : D.U (P.reflectionPerm (permInv n i) (permInv n i)) :=
    ⟨(n : G)⁻¹ * u'' * n, hneg ▸ D.inv_mul_mul_mem_U_weylNormalizer n u''.2⟩
  exact (φ.apply_congr hneg (v := v') rfl).trans
    (φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset _ (conjU n u) v' v'' hm')
/-- `D.weylNormalizer` acts on `Valuation D` by `(n • φ) a (u) = φ (w⁻¹ a) (n⁻¹ u n)`
(Bruhat–Tits I, 6.2.5). -/
noncomputable instance : SMul D.weylNormalizer (Valuation D) where
  smul n φ := {
    toFun i u := φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
      ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩
    three_le_encard_range i := by exact smul_three_le_encard_range n φ i
    min_le_apply_mul i u v := by
      exact (φ.min_le_apply_mul _ _ _).trans_eq
        (φ.apply_congr rfl (by simp only [Subgroup.coe_mul]; group))
    apply_le_apply_inv i u := by
      exact (φ.apply_le_apply_inv _ _).trans_eq
        (φ.apply_congr rfl (by simp only [Subgroup.coe_inv]; group))
    apply_eq_top_iff i u := by
      rw [φ.apply_eq_top_iff, ← Subtype.coe_inj, ← Subtype.coe_inj]
      simpa only [inv_inv, Subgroup.coe_one] using conj_eq_one_iff (a := (n : G)⁻¹) (b := (u : G))
    exists_apply_eq_apply_conj_add i m hm := by exact smul_exists_apply_eq_apply_conj_add n φ i m hm
    commutator_mem i j hij k l u v hu hv := by exact smul_commutator_mem n φ i j hij k l u v hu hv
    apply_eq_two_smul i j h u := by
      have h' : P.root (permInv n j) = (2 : R) • P.root (permInv n i) := by
        rw [← P.weylGroup_apply_root, ← P.weylGroup_apply_root, h]
        exact LinearEquiv.map_smul ((D.weylGroupHom n)⁻¹ : P.Aut).weightEquiv (2 : R) (P.root i)
      exact φ.apply_eq_two_smul _ _ h' (conjU n u)
    apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' h := by
      exact smul_apply_reflectionPerm_left n φ i u u' u'' h }
@[simp] theorem smul_apply (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (u : D.U i) :
    (n • φ) i u = φ (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i)
      ⟨(n : G)⁻¹ * u * n, D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩ := (rfl)
theorem smul_apply_weylGroupEquiv (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (u : D.U i) :
    (n • φ) i u = φ (P.weylGroupToPerm (D.weylGroupEquiv (QuotientGroup.mk n))⁻¹ i)
      ⟨(n : G)⁻¹ * u * n, D.weylGroupEquiv_mk n ▸ D.inv_mul_mul_mem_U_weylNormalizer n u.2⟩ :=
  (smul_apply n φ i u).trans (φ.apply_congr (by rw [D.weylGroupEquiv_mk]) rfl)
noncomputable instance : MulAction D.weylNormalizer (Valuation D) where
  one_smul φ := by ext _ _; exact (smul_apply _ _ _ _).trans (φ.apply_congr (by simp) (by simp))
  mul_smul n₁ n₂ φ := by
    ext i u; simp only [smul_apply]
    exact φ.apply_congr (by simp [mul_inv_rev]) (by simp only [Subgroup.coe_mul]; group)
@[simp] theorem filtration_smul (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (k : ℝ) :
    (n • φ).filtration i k =
      ConjAct.toConjAct (n : G) • φ.filtration (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) k := by
  ext g; rw [Subgroup.mem_conjAct_smul_iff, mem_filtration_iff, mem_filtration_iff]
  refine ⟨fun ⟨hg, hk⟩ ↦ ⟨D.inv_mul_mul_mem_U_weylNormalizer n hg, by rwa [smul_apply] at hk⟩,
    fun ⟨hg', hk⟩ ↦ ⟨?_, by rwa [smul_apply]⟩⟩
  exact (by group : (n : G) * ((n : G)⁻¹ * g * n) * (n : G)⁻¹ = g) ▸ mem_U_of_mem_permInv n hg'
theorem conj_filtration (n : D.weylNormalizer) (φ : Valuation D) (i : ι) (k : ℝ) :
    ConjAct.toConjAct (n : G) • φ.filtration i k =
      (n • φ).filtration (P.weylGroupToPerm (D.weylGroupHom n) i) k := by
  rw [filtration_smul, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Equiv.Perm.one_apply]
@[simp] theorem valueSet_smul (n : D.weylNormalizer) (φ : Valuation D) (i : ι) :
    (n • φ).valueSet i = φ.valueSet (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ i) := by
  ext k; simp only [mem_valueSet_iff, smul_apply]
  exact ⟨fun ⟨u, hu⟩ ↦ ⟨conjU n u, hu⟩, fun ⟨v, hv⟩ ↦
    ⟨⟨_, mem_U_of_mem_permInv n v.2⟩, (φ.apply_congr rfl (by dsimp [conjU]; group)).trans hv⟩⟩
@[simp] theorem isDiscrete_smul_iff (n : D.weylNormalizer) (φ : Valuation D) :
    (n • φ).IsDiscrete ↔ φ.IsDiscrete := by
  refine ⟨fun h i r s ↦ ?_, fun h i r s ↦ by rw [valueSet_smul]; exact h _ r s⟩
  have h' := h (P.weylGroupToPerm (D.weylGroupHom n) i) r s
  rwa [valueSet_smul, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Equiv.Perm.one_apply] at h'
end Valuation
end WeylNormalizer

namespace Valuation
variable [Module ℝ M] [Module ℝ N] {P : RootPairing ι ℝ M N} {D : RootDatum P G} (φ : Valuation D)
@[simp] theorem isDiscrete_shift_iff (v : N) : (φ.shift v).IsDiscrete ↔ φ.IsDiscrete := by
  have hshift {ψ : Valuation D} (h : ψ.IsDiscrete) (w : N) : (ψ.shift w).IsDiscrete :=
    fun i r s ↦ ((h i (r - P.root' i w) (s - P.root' i w)).image (· + P.root' i w)).subset
      fun x ⟨hx, hrx, hxs⟩ ↦ let ⟨y, hy, hxy⟩ := (ψ.valueSet_shift w) ▸ hx
        ⟨y, ⟨hy, by linarith, by linarith⟩, hxy⟩
  exact ⟨fun h ↦ by simpa using hshift h (-v), fun h ↦ hshift h v⟩
variable {φ} in
theorem Equipollent.isDiscrete_iff {ψ : Valuation D} (h : φ.Equipollent ψ) :
    φ.IsDiscrete ↔ ψ.IsDiscrete := by
  obtain ⟨v, hv⟩ := φ.equipollent_iff.mp h
  rw [ext fun i u ↦ (hv i u).trans (φ.shift_apply v u).symm]; exact (φ.isDiscrete_shift_iff v).symm
theorem shift_eq_shift_iff_of_mem_corootSpan [Finite ι] {v w : N}
    (hv : v ∈ P.corootSpan ℝ) (hw : w ∈ P.corootSpan ℝ) :
    φ.shift v = φ.shift w ↔ v = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have := Fintype.ofFinite ι
  have hker : v - w ∈ LinearMap.ker P.toDualRootSpan := by
    rw [LinearMap.mem_ker]; ext ⟨x, hx⟩; rw [RootPairing.toDualRootSpan_apply, LinearMap.zero_apply]
    refine Submodule.span_induction (fun y hy ↦ ?_) (by simp)
      (fun _ _ _ _ ih₁ ih₂ ↦ by simp [ih₁, ih₂]) (fun _ _ _ ih ↦ by simp [ih]) hx
    obtain ⟨i, rfl⟩ := hy; obtain ⟨k, u, hu⟩ := φ.exists_apply_eq_coe_of_index i
    have heq : (φ.shift v) i u = (φ.shift w) i u := congr($h i u)
    rw [shift_apply, shift_apply, hu] at heq; norm_cast at heq
    simpa [RootPairing.root', map_sub] using (by linarith : P.root' i v - P.root' i w = 0)
  exact sub_eq_zero.mp
    (Submodule.disjoint_def.mp P.disjoint_corootSpan_ker_toDualRootSpan _ (sub_mem hv hw) hker)
theorem isCompatible_iff_smul [Finite ι] [P.IsCrystallographic] {ν : D.T → N} :
    φ.IsCompatible ν ↔
      ∀ z : D.T, (⟨z, D.T_le_weylNormalizer z.2⟩ : D.weylNormalizer) • φ = φ.shift (ν z) := by
  rw [φ.isCompatible_iff_filtration, forall_comm]
  refine forall_congr' fun z ↦ ⟨fun h ↦ ext_filtration fun i k ↦ ?_, fun h i k ↦ ?_⟩
  · rw [filtration_smul, D.weylGroupHom_torus z.2, inv_one, map_one, Equiv.Perm.one_apply,
      filtration_shift, h i k]
  · have h' := congrArg (fun ψ : Valuation D ↦ ψ.filtration i k) h
    rwa [filtration_smul, D.weylGroupHom_torus z.2, inv_one, map_one, Equiv.Perm.one_apply,
      filtration_shift] at h'
private theorem shift_neg_smul_coroot (c : ℝ) (i j : ι) (x : D.U j) :
    (φ.shift (-(c • P.coroot i))) j x = φ j x + ((-(P.pairing j i * c) : ℝ) : WithTop ℝ) := by
  rw [shift_apply]; congr 2; simp [mul_comm]
private theorem exists_root'_eq_zero_and_eq_one {i j : ι}
    (hli : LinearIndependent ℝ ![P.root i, P.root j]) :
    ∃ y : N, P.root' i y = 0 ∧ P.root' j y = 1 := by
  have hnotMem : P.root j ∉ Submodule.span ℝ {P.root i} := fun hmem ↦ by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    linarith [(LinearIndependent.pair_iff.mp hli c (-1) (by simp [hc])).2]
  obtain ⟨g, hgi, hgj⟩ :=
    LinearMap.exists_extend_of_notMem (0 : Submodule.span ℝ {P.root i} →ₗ[ℝ] ℝ) hnotMem (1 : ℝ)
  exact ⟨P.flip.toPerfPair.symm g,
    by simpa [RootPairing.root'] using congr($hgi ⟨P.root i, Submodule.mem_span_singleton_self _⟩),
    by simpa [RootPairing.root'] using hgj⟩
private theorem ne_one_right_of_mul_mul_mem_reflectionCoset {i : ι} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)}
    (h : (u' : G) * u * u'' ∈ D.reflectionCoset i) : u'' ≠ 1 := by
  rintro rfl; have h1 := D.reflection_conjugates i ((u' : G) * u) (by simpa using h) i
  rw [ConjAct.toConjAct_mul, mul_smul,
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer u.2)] at h1
  have h2 : D.U i = D.U (P.reflectionPerm i i) := by
    rw [← inv_smul_eq_iff.mpr h1.symm, ← ConjAct.toConjAct_inv,
      Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer (inv_mem u'.2))]
  exact D.U_ne_of_root_eq_neg (by simp) h2.symm
private theorem inv_mul_mul_mem_U_reflectionCoset {i j : ι} {m : G}
    (hm : m ∈ D.reflectionCoset i) {x : G} (hx : x ∈ D.U j) :
    m⁻¹ * x * m ∈ D.U (P.reflectionPerm i j) := by
  rwa [← Subgroup.mem_conjAct_smul_iff, D.reflection_conjugates i m hm, P.reflectionPerm_self]
private def reflCone (P : RootPairing ι ℝ M N) (i j : ι) (y₀ y₁ : N) (b : ι) : Prop :=
  0 < P.root' b y₀ ∧ P.root b = P.root' b y₀ • P.root j + P.root' b y₁ • P.root i
private noncomputable def reflConeSubgroup (φ : Valuation D) (i j : ι) (y₀ y₁ : N) (k l : ℝ)
    (b : ι) : Subgroup G := open Classical in
  if reflCone P i j y₀ y₁ b then φ.filtration b (P.root' b y₀ * l + P.root' b y₁ * k) else ⊥
private def IsDualPair (P : RootPairing ι ℝ M N) (i j : ι) (y₀ y₁ : N) : Prop :=
  P.root' i y₀ = 0 ∧ P.root' j y₀ = 1 ∧ P.root' j y₁ = 0 ∧ P.root' i y₁ = 1
private theorem reflConeSubgroup_eq_of_root_eq {i j : ι} {y₀ y₁ : N} (hy : IsDualPair P i j y₀ y₁)
    (k l : ℝ) {b : ι} {c d : ℝ} (hc : 0 < c) (hb : P.root b = c • P.root j + d • P.root i) :
    φ.reflConeSubgroup i j y₀ y₁ k l b = φ.filtration b (c * l + d * k) := by
  obtain ⟨hy₀i, hy₀j, hy₁j, hy₁i⟩ := hy
  have hc₀ : P.root' b y₀ = c := by simp [RootPairing.root', hb, hy₀i, hy₀j]
  have hd₁ : P.root' b y₁ = d := by simp [RootPairing.root', hb, hy₁i, hy₁j]
  have hcone : reflCone P i j y₀ y₁ b := ⟨hc₀ ▸ hc, by rwa [hc₀, hd₁]⟩
  simp [reflConeSubgroup, hcone, hc₀, hd₁]
private theorem reflConeSubgroup_le_of_two_smul (i j : ι) (y₀ y₁ : N) (k l : ℝ) {b₁ b₂ : ι}
    (h2 : P.root b₂ = (2 : ℝ) • P.root b₁) :
    φ.reflConeSubgroup i j y₀ y₁ k l b₂ ≤ φ.reflConeSubgroup i j y₀ y₁ k l b₁ := by
  classical dsimp only [reflConeSubgroup]
  have h0 : P.root' b₂ y₀ = 2 * P.root' b₁ y₀ := by simp [RootPairing.root', h2]
  have h1 : P.root' b₂ y₁ = 2 * P.root' b₁ y₁ := by simp [RootPairing.root', h2]
  split_ifs with hb₂ hb₁
  · intro g hg_mem; obtain ⟨hg, hval⟩ := φ.mem_filtration_iff.mp hg_mem
    have hg₁ : g ∈ D.U b₁ := D.le_of_root_eq_two_smul b₁ b₂ h2 hg
    refine φ.mem_filtration_iff.mpr ⟨hg₁, ?_⟩
    rw [φ.apply_eq_two_smul b₁ b₂ h2 ⟨g, hg⟩, h0, h1] at hval
    cases h : φ b₁ ⟨g, hg₁⟩ with
    | top => exact le_top
    | coe r => rw [h, two_nsmul, ← WithTop.coe_add] at hval; norm_cast at hval ⊢; linarith
  · refine (hb₁ ⟨by linarith [hb₂.1], ?_⟩).elim
    have hsm := congrArg ((2⁻¹ : ℝ) • ·) hb₂.2
    rw [h2, h0, h1] at hsm; simpa [smul_add, smul_smul] using hsm
  all_goals exact bot_le
private theorem commutator_reflConeSubgroup_le {i j : ι} {y₀ y₁ z₀ : N}
    (hy : IsDualPair P i j y₀ y₁) (k l : ℝ) {b₁ b₂ : ι}
    (hb₁z : 0 < P.root' b₁ z₀) (hb₂z : 0 < P.root' b₂ z₀) :
    ⁅φ.reflConeSubgroup i j y₀ y₁ k l b₁, φ.reflConeSubgroup i j y₀ y₁ k l b₂⁆ ≤
      ⨆ (n) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root n = p • P.root b₁ + q • P.root b₂),
        φ.reflConeSubgroup i j y₀ y₁ k l n := by
  by_cases hb₁ : reflCone P i j y₀ y₁ b₁
  · by_cases hb₂ : reflCone P i j y₀ y₁ b₂
    · have hnot_neg : ∀ c : ℝ, 0 < c → P.root b₂ ≠ -(c • P.root b₁) := fun c hc hneg ↦ by
        have : P.root' b₂ z₀ = -c * P.root' b₁ z₀ := by simp [RootPairing.root', hneg]
        nlinarith
      simp only [reflConeSubgroup, hb₁, hb₂, ↓reduceIte]
      refine (φ.commutator_filtration_le hnot_neg _ _).trans
        (iSup_le fun n ↦ iSup_le fun p ↦ iSup_le fun q ↦ iSup_le fun ⟨hp, hq, hn_eq⟩ ↦ ?_)
      have hn_lin : P.root n =
          ((p : ℝ) * P.root' b₁ y₀ + (q : ℝ) * P.root' b₂ y₀) • P.root j +
            ((p : ℝ) * P.root' b₁ y₁ + (q : ℝ) * P.root' b₂ y₁) • P.root i := by
        rw [hn_eq, hb₁.2, hb₂.2, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]; module
      have hLn : φ.reflConeSubgroup i j y₀ y₁ k l n = φ.filtration n
          (p * (P.root' b₁ y₀ * l + P.root' b₁ y₁ * k) +
            q * (P.root' b₂ y₀ * l + P.root' b₂ y₁ * k)) :=
        (φ.reflConeSubgroup_eq_of_root_eq hy k l
          (by have := hb₁.1; have := hb₂.1; positivity) hn_lin).trans (congrArg _ (by ring))
      exact hLn ▸ le_iSup₂ (f := fun (n : ι) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
        P.root n = p • P.root b₁ + q • P.root b₂) ↦ φ.reflConeSubgroup i j y₀ y₁ k l n)
        n ⟨p, q, hp, hq, hn_eq⟩
    · simp [reflConeSubgroup, hb₂]
  · simp [reflConeSubgroup, hb₁]
private theorem filtration_le_normalizer_iSup_reflConeSubgroup {i j : ι} {y₀ y₁ : N}
    (hy : IsDualPair P i j y₀ y₁) (k l : ℝ) (s : ι)
    (hs₀ : P.root' s y₀ = 0) (hs_eq : P.root s = P.root' s y₁ • P.root i) :
    φ.filtration s (P.root' s y₁ * k) ≤
      Subgroup.normalizer ((⨆ c, φ.reflConeSubgroup i j y₀ y₁ k l c : Subgroup G) : Set G) := by
  refine Subgroup.le_normalizer_iSup_of_commutator_le _ _ fun b ↦ ?_
  by_cases hb : reflCone P i j y₀ y₁ b
  · have hnot_neg : ∀ c : ℝ, 0 < c → P.root b ≠ -(c • P.root s) := fun c _ hneg ↦ by
      have : P.root' b y₀ = -c * P.root' s y₀ := by simp [RootPairing.root', hneg]
      rw [hs₀, mul_zero] at this; linarith [hb.1]
    simp only [reflConeSubgroup, hb, ↓reduceIte]
    refine (φ.commutator_filtration_le hnot_neg _ _).trans
      (iSup_le fun n ↦ iSup_le fun p ↦ iSup_le fun q ↦ iSup_le fun ⟨_hp, hq, hn_eq⟩ ↦ ?_)
    have hn_lin : P.root n = ((q : ℝ) * P.root' b y₀) • P.root j +
        ((p : ℝ) * P.root' s y₁ + (q : ℝ) * P.root' b y₁) • P.root i := by
      rw [hn_eq, hs_eq, hb.2, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]; module
    have hLn : φ.reflConeSubgroup i j y₀ y₁ k l n = φ.filtration n
        (p * (P.root' s y₁ * k) + q * (P.root' b y₀ * l + P.root' b y₁ * k)) :=
      (φ.reflConeSubgroup_eq_of_root_eq hy k l
        (mul_pos (Nat.cast_pos.mpr hq) hb.1) hn_lin).trans (congrArg _ (by ring))
    exact hLn ▸ le_iSup (φ.reflConeSubgroup i j y₀ y₁ k l) n
  · simp [reflConeSubgroup, hb]
private theorem inv_mem_normalizer_iSup_reflConeSubgroup {i j : ι} {y₀ y₁ : N}
    (hy : IsDualPair P i j y₀ y₁) {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G}
    (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k : ℝ}
    (hφu : φ i u = k) (l : ℝ) :
    m⁻¹ ∈ Subgroup.normalizer
      ((⨆ c, φ.reflConeSubgroup i j y₀ y₁ k l c : Subgroup G) : Set G) := by
  have ⟨hy₀i, _, _, hy₁i⟩ := hy; let L := φ.reflConeSubgroup i j y₀ y₁ k l
  have hm_prod : (u' : G) * u * u'' ∈ D.reflectionCoset i := hm_eq.symm ▸ hm
  have hu_norm : ((u⁻¹ : D.U i) : G) ∈ Subgroup.normalizer ((⨆ c, L c : Subgroup G) : Set G) :=
    φ.filtration_le_normalizer_iSup_reflConeSubgroup hy k l i hy₀i (by simp [hy₁i])
      (by rw [φ.coe_mem_filtration_iff u⁻¹, φ.apply_inv, hy₁i, one_mul, hφu])
  let ni := P.reflectionPerm i i; have hni₁ : P.root' ni y₁ = -1 := by simp [ni, hy₁i]
  have hni_norm {w : D.U ni} (hw : φ ni w = -φ i u) :
      ((w⁻¹ : D.U ni) : G) ∈ Subgroup.normalizer ((⨆ c, L c : Subgroup G) : Set G) :=
    φ.filtration_le_normalizer_iSup_reflConeSubgroup hy k l ni (by simp [ni, hy₀i])
      (by rw [hni₁, neg_one_smul]; simp [ni])
      (by rw [φ.coe_mem_filtration_iff, φ.apply_inv, hw, hφu, hni₁, neg_one_mul,
        WithTop.LinearOrderedAddCommGroup.coe_neg])
  have heq : m⁻¹ = ((u''⁻¹ : D.U ni) : G) * ((u⁻¹ : D.U i) : G) * ((u'⁻¹ : D.U ni) : G) := by
    simp only [Subgroup.coe_inv]; rw [← hm_eq]; group
  have hr := φ.apply_reflectionPerm_right_eq_neg_of_mul_mul_mem_reflectionCoset u u' u'' hm_prod
  have hl := φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' hm_prod
  exact heq ▸ mul_mem (mul_mem (hni_norm hr) hu_norm) (hni_norm hl)
private theorem linearIndependent_reflectionPerm_of_linearIndependent {i j : ι}
    (hli : LinearIndependent ℝ ![P.root i, P.root j]) :
    LinearIndependent ℝ ![P.root i, P.root (P.reflectionPerm i j)] := by
  rw [LinearIndependent.pair_iff] at hli ⊢; intro c d hcd
  have h1 : (c - d * P.pairing j i) • P.root i + d • P.root j = 0 := by
    rw [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing] at hcd
    exact (by module : (c - d * P.pairing j i) • P.root i + d • P.root j =
      c • P.root i + d • (P.root j - P.pairing j i • P.root i)).trans hcd
  obtain ⟨h2, hd0⟩ := hli _ _ h1; exact ⟨by linarith [hd0 ▸ h2], hd0⟩
private theorem coweightEquiv_symm_mem_corootSpan (e : P.Aut) {v : N}
    (hv : v ∈ P.corootSpan ℝ) : e.coweightEquiv.symm v ∈ P.corootSpan ℝ := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have hcor : e.coweightEquiv.symm (P.coroot j) = P.coroot (e.indexEquiv j) :=
      (LinearEquiv.symm_apply_eq e.coweightEquiv).mpr
        (by simp [RootPairing.Hom.coroot_coweightMap_apply])
    exact hcor ▸ (P.corootSpanMem ℝ _).2
  | zero => simp
  | add x y _ _ ihx ihy => exact map_add e.coweightEquiv.symm x y ▸ add_mem ihx ihy
  | smul c x _ ih => exact map_smul e.coweightEquiv.symm c x ▸ Submodule.smul_mem _ c ih
private theorem exists_mul_mul_mem_reflectionCoset_and_apply_eq (i : ι) :
    ∃ (k : ℝ) (u : D.U i) (u' u'' : D.U (P.reflectionPerm i i)) (m : G),
      m ∈ D.reflectionCoset i ∧ (u' : G) * u * u'' = m ∧ φ i u = k := by
  obtain ⟨k, u, hu⟩ := φ.exists_apply_eq_coe_of_index i
  have hu1 : (u : G) ≠ 1 := fun h ↦ by simp [(Subtype.ext h : u = 1)] at hu
  obtain ⟨_, ⟨x, hx, m, hm, rfl⟩, y, hy, hxy⟩ := D.bruhat (P.reflectionPerm i i)
    ⟨by rw [P.reflectionPerm_reflectionPerm_self]; exact u.2, hu1⟩
  dsimp only at hxy; rw [D.reflectionCoset_reflectionPerm_self] at hm
  exact ⟨k, u, ⟨x, hx⟩⁻¹, ⟨y, hy⟩⁻¹, m, hm, by simp only [Subgroup.coe_inv]; rw [← hxy]; group, hu⟩

section RealWeylAction
variable [Finite ι] [P.IsCrystallographic]
private abbrev reflN {i : ι} {m : G} (hm : m ∈ D.reflectionCoset i) : D.weylNormalizer :=
  ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩
private abbrev torusN {t : G} (ht : t ∈ D.T) : D.weylNormalizer := ⟨t, D.T_le_weylNormalizer ht⟩
theorem smul_shift (n : D.weylNormalizer) (v : N) :
    n • φ.shift v = (n • φ).shift ((D.weylGroupHom n : P.Aut).coweightEquiv.symm v) := by
  ext i u; rw [smul_apply, shift_apply, shift_apply, smul_apply]; congr 1
  have h := (D.weylGroupHom n : P.Aut).root'_coweightEquiv
    ((D.weylGroupHom n : P.Aut).indexEquiv.symm i) v
  rw [Equiv.apply_symm_apply] at h; exact congrArg WithTop.some h.symm
omit [P.IsCrystallographic] in
private theorem bijective_toDualRootSpan_corootSpan (P : RootPairing ι ℝ M N) :
    Function.Bijective (P.toDualRootSpan ∘ₗ (P.corootSpan ℝ).subtype) := by
  have := Fintype.ofFinite ι; have := Module.Finite.span_of_finite ℝ (Set.finite_range P.root)
  have := Module.Finite.span_of_finite ℝ (Set.finite_range P.coroot)
  have hinj : Function.Injective (P.toDualRootSpan ∘ₗ (P.corootSpan ℝ).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, ← Submodule.disjoint_iff_comap_eq_bot]
    exact P.disjoint_corootSpan_ker_toDualRootSpan
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [P.finrank_corootSpan_eq', Subspace.dual_finrank_eq])).mp hinj⟩
omit [P.IsCrystallographic] in
private theorem exists_regular_preserve_pos (D : RootDatum P G) (y₀ : N) :
    ∃ z₀ : N, (∀ b : ι, P.root' b z₀ ≠ 0) ∧ ∀ b : ι, 0 < P.root' b y₀ → 0 < P.root' b z₀ := by
  have := Fintype.ofFinite ι
  let C : ℝ := (∑ b : ι, |P.root' b D.positiveVector| / |P.root' b y₀|) + 1
  have hdom (b : ι) (hb : P.root' b y₀ ≠ 0) : |P.root' b D.positiveVector| < C * |P.root' b y₀| :=
    (div_lt_iff₀ (abs_pos.mpr hb)).mp <| lt_of_le_of_lt
      (Finset.single_le_sum (f := fun c : ι ↦ |P.root' c D.positiveVector| / |P.root' c y₀|)
        (fun _ _ ↦ div_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ b)) (lt_add_one _)
  let z₀ : N := C • y₀ + D.positiveVector
  have hpos (b : ι) (hb : 0 < P.root' b y₀) : 0 < P.root' b z₀ := by
    have h1 := hdom b hb.ne'; rw [abs_of_pos hb] at h1
    simp only [z₀, map_add, map_smul, smul_eq_mul]
    linarith [neg_abs_le (P.root' b D.positiveVector)]
  refine ⟨z₀, fun b ↦ ?_, hpos⟩
  rcases lt_trichotomy (P.root' b y₀) 0 with hn | h0 | hp
  · have h1 := hdom b hn.ne; rw [abs_of_neg hn] at h1
    exact (by simp only [z₀, map_add, map_smul, smul_eq_mul]
              linarith [le_abs_self (P.root' b D.positiveVector)] : P.root' b z₀ < 0).ne
  · simp [z₀, h0, D.positiveVector_regular b]
  · exact (hpos b hp).ne'
private theorem smul_reflection_apply_raw {i : ι} {m : G} (hm : m ∈ D.reflectionCoset i) (j : ι)
    (x : D.U j) : (reflN hm • φ) j x =
      φ (P.reflectionPerm i j) ⟨m⁻¹ * x * m, inv_mul_mul_mem_U_reflectionCoset hm x.2⟩ :=
  (smul_apply _ _ _ _).trans <| φ.apply_congr
    (by rw [D.weylGroupHom_reflection hm, RootPairing.weylGroup.ofIdx_inv_eq,
      P.weylGroupToPerm_ofIdx_apply]) rfl
private theorem smul_reflection_apply_self_aux {i : ι} {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) (x : D.U i) :
    (reflN hm • φ) i x = φ i x + ((-(2 * k) : ℝ) : WithTop ℝ) := by
  by_cases hx : x = 1; · simp [hx]
  have hni_i := P.reflectionPerm_reflectionPerm_self i
  have hm_prod : (u' : G) * u * u'' ∈ D.reflectionCoset i := hm_eq.symm ▸ hm
  have hφ_u' : φ (P.reflectionPerm i i) u' = -(k : WithTop ℝ) := by
    rw [φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset i u u' u'' hm_prod, hφ]
  have hφ_u'' : φ (P.reflectionPerm i i) u'' = -(k : WithTop ℝ) := by
    rw [φ.apply_reflectionPerm_right_eq_neg_of_mul_mul_mem_reflectionCoset u u' u'' hm_prod, hφ]
  have hw_mem : m * (u'' : G) * m⁻¹ ∈
      D.U (P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i)) :=
    hni_i.symm ▸ D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm u''.2
  have hw_prod : (m * (u'' : G) * m⁻¹) * (u' : G) * (u : G) ∈
      D.reflectionCoset (P.reflectionPerm i i) := by
    have hmeq : (m * (u'' : G) * m⁻¹) * (u' : G) * (u : G) = m := by rw [← hm_eq]; group
    rw [hmeq, D.reflectionCoset_reflectionPerm_self]; exact hm
  have hφ_conj : φ i ⟨m * u'' * m⁻¹, D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm u''.2⟩ = k := by
    rw [← φ.apply_congr hni_i (u := ⟨m * u'' * m⁻¹, hw_mem⟩) rfl,
      φ.apply_reflectionPerm_left_eq_neg_of_mul_mul_mem_reflectionCoset (P.reflectionPerm i i) u'
        ⟨_, hw_mem⟩ ⟨u, hni_i.symm ▸ u.2⟩ hw_prod, hφ_u', neg_neg]
  obtain ⟨c, hc⟩ := φ.exists_apply_eq_apply_conj_add i m hm
  have hc_eq : c = -(2 * k) := by
    have h1 := hc u'' (ne_one_right_of_mul_mul_mem_reflectionCoset hm_prod)
    rw [hφ_u'', hφ_conj] at h1; norm_cast at h1; linarith
  let y : D.U (P.reflectionPerm i i) := ⟨m⁻¹ * x * m, inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
  have hy_ne : y ≠ 1 := fun h ↦ hx <| Subtype.ext <|
    (conj_eq_one_iff (a := m⁻¹) (b := (x : G))).mp
      (by simpa only [y, inv_inv, Subgroup.coe_one] using congrArg Subtype.val h)
  rw [φ.smul_reflection_apply_raw hm i x, hc y hy_ne, hc_eq]
  exact congrArg (· + ((-(2 * k) : ℝ) : WithTop ℝ)) (φ.apply_congr rfl (by dsimp only [y]; group))
private theorem le_smul_reflection_of_linearIndependent {i j : ι}
    (hj : P.IsIndivisible j) (hli : LinearIndependent ℝ ![P.root i, P.root j])
    {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G}
    (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k l : ℝ}
    (hφu : φ i u = k) {x : D.U j} (hφx : (l : WithTop ℝ) ≤ φ j x) :
    ((l - P.pairing j i * k : ℝ) : WithTop ℝ) ≤ (reflN hm • φ) j x := by
  obtain ⟨y₀, hy₀i, hy₀j⟩ := exists_root'_eq_zero_and_eq_one hli
  obtain ⟨y₁, hy₁j, hy₁i⟩ :=
    exists_root'_eq_zero_and_eq_one (LinearIndependent.pair_symm_iff.mp hli)
  have hy : IsDualPair P i j y₀ y₁ := ⟨hy₀i, hy₀j, hy₁j, hy₁i⟩
  obtain ⟨z₀, hz₀, hz₀_pos⟩ := exists_regular_preserve_pos D y₀
  let L := φ.reflConeSubgroup i j y₀ y₁ k l
  have hLU : ∀ b, 0 < P.root' b z₀ → L b ≤ D.U b := fun b _ ↦ by
    dsimp [L, reflConeSubgroup]; split_ifs <;> simp [φ.filtration_le_U]
  have hiSup_eq : (⨆ (b) (_ : 0 < P.root' b z₀), L b) = ⨆ b, L b :=
    le_antisymm (iSup₂_le fun b _ ↦ le_iSup L b) <| iSup_le fun b ↦ by
      by_cases hb : reflCone P i j y₀ y₁ b
      exacts [le_iSup₂_of_le b (hz₀_pos b hb.1) le_rfl, by simp [L, reflConeSubgroup, hb]]
  have hminv_norm := φ.inv_mem_normalizer_iSup_reflConeSubgroup hy hm hm_eq hφu l
  have hLj : L j = φ.filtration j l := (φ.reflConeSubgroup_eq_of_root_eq hy k l
    (c := 1) (d := 0) one_pos (by simp)).trans (congrArg _ (by ring))
  have hx_mem : (x : G) ∈ ⨆ c, L c :=
    Subgroup.mem_iSup_of_mem j (hLj ▸ (φ.coe_mem_filtration_iff x).mpr hφx)
  set j' := P.reflectionPerm i j
  have hj'_lin : P.root j' = (1 : ℝ) • P.root j + (-P.pairing j i) • P.root i := by
    rw [P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing, one_smul, neg_smul,
      sub_eq_add_neg]
  have hj'₀ : P.root' j' y₀ = 1 := by simp [RootPairing.root', hj'_lin, hy₀i, hy₀j]
  have hLj' : L j' = φ.filtration j' (l - P.pairing j i * k) :=
    (φ.reflConeSubgroup_eq_of_root_eq hy k l one_pos hj'_lin).trans (congrArg _ (by ring))
  have hconj_mem : m⁻¹ * (x : G) * m ∈ (⨆ (b) (_ : 0 < P.root' b z₀), L b) ⊓ D.U j' :=
    ⟨hiSup_eq ▸ by simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hminv_norm x).mp hx_mem,
      inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
  rw [D.iSup_inf_U_eq_of_commutator_le hz₀ L hLU
    (fun b₁ b₂ _ ↦ φ.reflConeSubgroup_le_of_two_smul i j y₀ y₁ k l)
    (fun b₁ b₂ ↦ φ.commutator_reflConeSubgroup_le hy k l)
    (hj.reflectionPerm i) (hz₀_pos j' (hj'₀ ▸ one_pos)), hLj'] at hconj_mem
  rw [φ.smul_reflection_apply_raw hm j x]; exact (φ.coe_mem_filtration_iff ⟨_, _⟩).mp hconj_mem
private theorem smul_reflection_of_not_linearIndependent {i j : ι}
    (hi : P.IsIndivisible i) (hj : P.IsIndivisible j)
    (hli : ¬LinearIndependent ℝ ![P.root i, P.root j])
    {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) (x : D.U j) :
    (reflN hm • φ) j x = (φ.shift (-(k • P.coroot i))) j x := by
  rcases P.not_linearIndependent_root_iff.mp hli with rfl | hneg | h2 | h2 | hneg2 | hneg2
  · rw [φ.smul_reflection_apply_self_aux hm hm_eq hφ x, φ.shift_neg_smul_coroot, P.pairing_same]
  · have hj_eq : j = P.reflectionPerm i i := P.root.injective
      (by rw [P.root_reflectionPerm, P.reflection_apply_self, ← neg_eq_iff_eq_neg.mpr hneg])
    subst hj_eq
    have hm_inv : m⁻¹ ∈ D.reflectionCoset i := D.inv_mem_reflectionCoset hm
    have hm_inv_eq : ((u''⁻¹ : D.U _) : G) * (u⁻¹ : D.U i) * (u'⁻¹ : D.U _) = m⁻¹ := by
      simp only [Subgroup.coe_inv]; rw [← hm_eq]; group
    let y : D.U i := ⟨m⁻¹ * x * m, by simpa using inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
    have hself := φ.smul_reflection_apply_self_aux hm_inv hm_inv_eq ((φ.apply_inv u).trans hφ) y
    rw [φ.smul_reflection_apply_raw hm_inv i y,
      φ.apply_congr rfl (v := x) (by dsimp [y]; group)] at hself
    rw [φ.smul_reflection_apply_raw hm _ x, φ.apply_congr (P.reflectionPerm_self i i) (v := y) rfl,
      φ.shift_neg_smul_coroot, P.pairing_reflectionPerm_self_left, P.pairing_same, hself]
    cases φ i y with | top => simp | coe r => norm_cast; push_cast; ring
  · exact (P.isIndivisible_iff.mp hj i h2).elim
  · exact (P.isIndivisible_iff.mp hi j h2).elim
  · exact (P.isIndivisible_iff.mp hj (P.reflectionPerm i i) (by simpa [neg_smul] using hneg2)).elim
  · exact (P.isIndivisible_iff.mp hi (P.reflectionPerm j j) (by simpa [neg_smul] using hneg2)).elim
private theorem smul_reflection_of_isIndivisible {i : ι} (hi : P.IsIndivisible i) {u : D.U i}
    {u' u'' : D.U (P.reflectionPerm i i)} {m : G} (hm : m ∈ D.reflectionCoset i)
    (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) :
    reflN hm • φ = φ.shift (-(k • P.coroot i)) := by
  refine ext_of_isIndivisible fun j hj x ↦ ?_
  by_cases hli : LinearIndependent ℝ ![P.root i, P.root j]
  · by_cases hx : x = 1; · simp [hx]
    obtain ⟨l, hl⟩ := φ.exists_apply_eq_coe hx; set j' := P.reflectionPerm i j
    have hle₁ := φ.le_smul_reflection_of_linearIndependent hj hli hm hm_eq hφ hl.ge
    let x' : D.U j' := ⟨m⁻¹ * x * m, inv_mul_mul_mem_U_reflectionCoset hm x.2⟩
    have hx'_ne : x' ≠ 1 := fun h ↦ hx <| Subtype.ext <|
      (conj_eq_one_iff (a := m⁻¹) (b := (x : G))).mp
        (by simpa only [x', inv_inv, Subgroup.coe_one] using congrArg Subtype.val h)
    obtain ⟨l', hl'⟩ := φ.exists_apply_eq_coe hx'_ne
    have hsmul_eq := (φ.smul_reflection_apply_raw hm j x).trans hl'
    have hm_inv : m⁻¹ ∈ D.reflectionCoset i := D.inv_mem_reflectionCoset hm
    have hm_inv_eq : ((u''⁻¹ : D.U _) : G) * (u⁻¹ : D.U i) * (u'⁻¹ : D.U _) = m⁻¹ := by
      simp only [Subgroup.coe_inv]; rw [← hm_eq]; group
    have hle₂ := φ.le_smul_reflection_of_linearIndependent (hj.reflectionPerm i)
      (linearIndependent_reflectionPerm_of_linearIndependent hli)
      hm_inv hm_inv_eq ((φ.apply_inv u).trans hφ) hl'.ge
    have hpj' : P.pairing j' i = -P.pairing j i := by
      rw [← P.root_coroot'_eq_pairing, P.root_reflectionPerm, P.coroot'_reflection_self,
        P.root_coroot'_eq_pairing]
    rw [φ.smul_reflection_apply_raw hm_inv j' x',
      φ.apply_congr (P.reflectionPerm_self i j) (v := x) (by dsimp only [x']; group), hl,
      hpj'] at hle₂
    rw [hsmul_eq] at hle₁ ⊢; rw [φ.shift_neg_smul_coroot, hl]; norm_cast at hle₁ hle₂ ⊢; linarith
  · exact φ.smul_reflection_of_not_linearIndependent hi hj hli hm hm_eq hφ x
theorem smul_reflection {i : ι} {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)} {m : G}
    (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k : ℝ} (hφ : φ i u = k) :
    (⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ =
      φ.shift (-(k • P.coroot i)) := by
  rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨i₀, hi₀, hi_eq⟩
  · exact φ.smul_reflection_of_isIndivisible hi hm hm_eq hφ
  · have hm₀ : m ∈ D.reflectionCoset i₀ := D.reflectionCoset_eq_of_root_eq_two_smul hi_eq ▸ hm
    have hneg_eq : P.root (P.reflectionPerm i i) = (2 : ℝ) • P.root (P.reflectionPerm i₀ i₀) := by
      rw [P.root_reflectionPerm, P.reflection_apply_self, P.root_reflectionPerm,
        P.reflection_apply_self, hi_eq, smul_neg]
    let u₀ : D.U i₀ := ⟨u, D.le_of_root_eq_two_smul i₀ i hi_eq u.2⟩
    have hφ₀ : φ i₀ u₀ = ((k / 2 : ℝ) : WithTop ℝ) := by
      have h2 := φ.apply_eq_two_smul i₀ i hi_eq u; rw [hφ] at h2
      cases hval : φ i₀ u₀ with
      | top => rw [hval, two_nsmul, WithTop.top_add] at h2; exact absurd h2 WithTop.coe_ne_top
      | coe r => rw [hval, two_nsmul, ← WithTop.coe_add] at h2; norm_cast at h2 ⊢; linarith
    have hres := φ.smul_reflection_of_isIndivisible hi₀ (u := u₀)
      (u' := ⟨u', D.le_of_root_eq_two_smul _ _ hneg_eq u'.2⟩)
      (u'' := ⟨u'', D.le_of_root_eq_two_smul _ _ hneg_eq u''.2⟩) hm₀ hm_eq hφ₀
    have : HasUniqueDiv M := .of_isTorsionFree ℝ M; have : HasUniqueDiv N := .of_isTorsionFree ℝ N
    have hcor : (k / 2 : ℝ) • P.coroot i₀ = k • P.coroot i := by
      rw [P.coroot_eq_smul_coroot_iff.mpr hi_eq, smul_smul]; ring_nf
    rwa [hcor] at hres
theorem smul_reflection_apply_self {i : ι} {u : D.U i} {u' u'' : D.U (P.reflectionPerm i i)}
    {m : G} (hm : m ∈ D.reflectionCoset i) (hm_eq : (u' : G) * u * u'' = m) {k : ℝ}
    (hφ : φ i u = k) (x : D.U i) :
    ((⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) • φ) i x =
      φ i x - ((2 * k : ℝ) : WithTop ℝ) := by
  rw [φ.smul_reflection hm hm_eq hφ, φ.shift_neg_smul_coroot, P.pairing_same,
    WithTop.LinearOrderedAddCommGroup.coe_neg, sub_eq_add_neg]
omit [Finite ι] [P.IsCrystallographic] in
private theorem exists_apply_eq_conj_neg_add (i : ι) {m : G}
    (hm : m ∈ D.reflectionCoset (P.reflectionPerm i i)) :
    ∃ c : ℝ, ∀ x : D.U i, x ≠ 1 → φ i x =
      φ (P.reflectionPerm i i) ⟨m * x * m⁻¹, D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm
        ((P.reflectionPerm_reflectionPerm_self i).symm ▸ x.2)⟩ + c := by
  have hni := P.reflectionPerm_reflectionPerm_self i
  obtain ⟨c, hc⟩ := φ.exists_apply_eq_apply_conj_add (P.reflectionPerm i i) m hm
  refine ⟨c, fun x hx ↦ (φ.apply_congr hni.symm (v := ⟨x, hni.symm ▸ x.2⟩) rfl).trans ?_⟩
  refine (hc _ fun h ↦ hx (Subtype.ext (congrArg Subtype.val h : (x : G) = 1))).trans ?_
  exact congrArg (· + (c : WithTop ℝ)) (φ.apply_congr rfl rfl)
private theorem exists_torus_smul_add_const {t : G} (ht : t ∈ D.T) :
    ∃ d : ι → ℝ, ∀ (i : ι) (x : D.U i), (torusN ht • φ) i x = φ i x + (d i : WithTop ℝ) := by
  have hconst (i : ι) : ∃ c : ℝ, ∀ x : D.U i, (torusN ht • φ) i x = φ i x + (c : WithTop ℝ) := by
    obtain ⟨m, hm⟩ := D.reflectionCoset_nonempty (P.reflectionPerm i i)
    have hmt : m * t ∈ D.reflectionCoset (P.reflectionPerm i i) :=
      (by group : (m * t * m⁻¹) * m = m * t) ▸
        D.mul_mem_reflectionCoset (D.mul_mul_inv_mem_T hm ht) hm
    obtain ⟨c₁, hc₁⟩ := φ.exists_apply_eq_conj_neg_add i hm
    obtain ⟨c₂, hc₂⟩ := φ.exists_apply_eq_conj_neg_add i hmt
    refine ⟨c₂ - c₁, fun x ↦ ?_⟩
    by_cases hx : x = 1; · simp [hx]
    let x₁ : D.U i := ⟨t⁻¹ * x * t, D.inv_mul_mul_mem_U ht x.2⟩
    have hx₁ : x₁ ≠ 1 := fun h ↦ hx <| Subtype.ext <|
      (conj_eq_one_iff (a := t⁻¹) (b := (x : G))).mp
        (by simpa only [x₁, inv_inv, Subgroup.coe_one] using congrArg Subtype.val h)
    have hnt : (torusN ht • φ) i x = φ i x₁ := (smul_apply _ φ i x).trans
      (φ.apply_congr (by rw [D.weylGroupHom_torus ht]; simp) rfl)
    rw [hnt, hc₁ x hx, hc₂ x₁ hx₁, φ.apply_congr rfl
      (v := ⟨m * x * m⁻¹, D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm
        ((P.reflectionPerm_reflectionPerm_self i).symm ▸ x.2)⟩) (by dsimp [x₁]; group)]
    cases φ (P.reflectionPerm i i) ⟨m * x * m⁻¹, _⟩ with | top => simp | coe r => norm_cast; ring
  exact ⟨fun i ↦ (hconst i).choose, fun i ↦ (hconst i).choose_spec⟩
private theorem torus_add_const_reflectionPerm {t : G} (ht : t ∈ D.T) {d : ι → ℝ}
    (hd : ∀ (i : ι) (x : D.U i), (torusN ht • φ) i x = φ i x + (d i : WithTop ℝ))
    (i j : ι) : d (P.reflectionPerm i j) = d j - P.pairing j i * d i := by
  have hnt_apply (ψ : Valuation D) {b : ι} (w : D.U b) :
      (torusN ht • ψ) b w = ψ b ⟨t⁻¹ * w * t, D.inv_mul_mul_mem_U ht w.2⟩ :=
    (smul_apply _ ψ b w).trans (ψ.apply_congr (by rw [D.weylGroupHom_torus ht]; simp) rfl)
  obtain ⟨k, u, u', u'', m, hm, hm_eq, hu⟩ := φ.exists_mul_mul_mem_reflectionCoset_and_apply_eq i
  have hm' : t⁻¹ * m * t ∈ D.reflectionCoset i :=
    (by group : (t⁻¹ * (m * t * m⁻¹)) * m = t⁻¹ * m * t) ▸
      D.mul_mem_reflectionCoset (mul_mem (inv_mem ht) (D.mul_mul_inv_mem_T hm ht)) hm
  let v_u : D.U i := ⟨t⁻¹ * u * t, D.inv_mul_mul_mem_U ht u.2⟩
  have hm'_eq : ((⟨t⁻¹ * u' * t, D.inv_mul_mul_mem_U ht u'.2⟩ : D.U _) : G) * v_u *
      (⟨t⁻¹ * u'' * t, D.inv_mul_mul_mem_U ht u''.2⟩ : D.U _) = t⁻¹ * m * t := by
    dsimp only [v_u]; rw [← hm_eq]; group
  have hφ_vu : φ i v_u = ((k + d i : ℝ) : WithTop ℝ) := by
    have h1 := (hnt_apply φ u).symm.trans (hd i u); rw [hu] at h1; exact_mod_cast h1
  have hcomm_n : reflN hm * torusN ht = torusN ht * reflN hm' :=
    Subtype.ext (by simp only [Subgroup.coe_mul, reflN, torusN]; group)
  obtain ⟨l, z, hz⟩ := φ.exists_apply_eq_coe_of_index j
  have heval : (reflN hm • torusN ht • φ) j z = (torusN ht • reflN hm' • φ) j z := by
    rw [← mul_smul, ← mul_smul, hcomm_n]
  have hnt_z : φ j ⟨t⁻¹ * z * t, D.inv_mul_mul_mem_U ht z.2⟩ = ((l + d j : ℝ) : WithTop ℝ) := by
    have h1 := (hnt_apply φ z).symm.trans (hd j z); rw [hz] at h1; exact_mod_cast h1
  rw [(torusN ht • φ).smul_reflection_apply_raw hm j z, hd, ← φ.smul_reflection_apply_raw hm j z,
    φ.smul_reflection hm hm_eq hu, φ.shift_neg_smul_coroot, hz,
    hnt_apply (reflN hm' • φ) z, φ.smul_reflection hm' hm'_eq hφ_vu, φ.shift_neg_smul_coroot,
    hnt_z] at heval
  norm_cast at heval; linarith
private theorem exists_mem_corootSpan_of_forall_reflectionPerm (D : RootDatum P G) {d : ι → ℝ}
    (hrefl_d : ∀ i j : ι, d (P.reflectionPerm i j) = d j - P.pairing j i * d i) :
    ∃ v ∈ P.corootSpan ℝ, ∀ i : ι, P.IsIndivisible i → P.root' i v = d i := by
  let b₀ := P.indivisibleBaseOf D.positiveVector D.positiveVector_regular
  have hli_supp : LinearIndependent ℝ (fun a : b₀.support ↦ P.root a.1.1) := by
    simpa [LinearIndepOn, funext P.indivisiblePairing_root] using b₀.linearIndepOn_root
  let B := Module.Basis.span hli_supp
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.constr ℝ (fun a : b₀.support ↦ d a.1.1))
  obtain ⟨⟨v, hv⟩, hv_eq⟩ :=
    (bijective_toDualRootSpan_corootSpan P).2 (g ∘ₗ (P.rootSpan ℝ).subtype)
  have hv_supp (a : b₀.support) : P.root' a.1.1 v = d a.1.1 := by
    have h1 : P.toDualRootSpan v ⟨P.root a.1.1, (P.rootSpanMem ℝ a.1.1).2⟩ = g (P.root a.1.1) :=
      congr($hv_eq ⟨P.root a.1.1, (P.rootSpanMem ℝ a.1.1).2⟩)
    have hB : (B a : M) = P.root a.1.1 := congrArg Subtype.val (Module.Basis.span_apply hli_supp a)
    simpa [RootPairing.root'] using h1.trans (by simpa [hB, B.constr_basis] using congr($hg (B a)))
  refine ⟨v, hv, fun i hi ↦ b₀.induction_reflect ⟨i, hi⟩ (p := fun c ↦ P.root' c.1 v = d c.1)
    (fun a ih ↦ ?_) (fun a ha ↦ hv_supp ⟨a, ha⟩) fun a s ih hs ↦ ?_⟩
  · have h := hrefl_d a.1 a.1; rw [P.pairing_same] at h
    rw [P.coe_indivisiblePairing_reflectionPerm a a, P.root'_reflectionPerm_self,
      LinearMap.neg_apply, ih]; linarith
  · have hr : P.root' (P.reflectionPerm s.1 a.1) v =
        P.root' a.1 v - P.pairing a.1 s.1 * P.root' s.1 v := by
      simp [RootPairing.root', P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing]
    rw [P.coe_indivisiblePairing_reflectionPerm s a, hr, ih, hv_supp ⟨s, hs⟩, hrefl_d s.1 a.1]
private theorem exists_mem_corootSpan_torus_smul_eq_shift {t : G} (ht : t ∈ D.T) :
    ∃ v ∈ P.corootSpan ℝ, torusN ht • φ = φ.shift v := by
  obtain ⟨d, hd⟩ := φ.exists_torus_smul_add_const ht
  obtain ⟨v, hv, hv_ind⟩ :=
    exists_mem_corootSpan_of_forall_reflectionPerm D (φ.torus_add_const_reflectionPerm ht hd)
  exact ⟨v, hv, ext_of_isIndivisible fun i hi x ↦ by rw [hd i x, shift_apply, hv_ind i hi]⟩
theorem existsUnique_mem_corootSpan_smul_eq_shift (n : D.weylNormalizer) :
    ∃! v : N, v ∈ P.corootSpan ℝ ∧ n • φ = φ.shift v := by
  suffices ∃ v : N, v ∈ P.corootSpan ℝ ∧ n • φ = φ.shift v from let ⟨v, hv, hφv⟩ := this
    ⟨v, ⟨hv, hφv⟩, fun w ⟨hw, hφw⟩ ↦
      (φ.shift_eq_shift_iff_of_mem_corootSpan hw hv).mp (hφw.symm.trans hφv)⟩
  have hmul {n₁ n₂ : D.weylNormalizer}
      (h₁ : ∃ v₁ ∈ P.corootSpan ℝ, n₁ • φ = φ.shift v₁)
      (h₂ : ∃ v₂ ∈ P.corootSpan ℝ, n₂ • φ = φ.shift v₂) :
      ∃ v ∈ P.corootSpan ℝ, (n₁ * n₂) • φ = φ.shift v := by
    obtain ⟨⟨v₁, hv₁, e₁⟩, ⟨v₂, hv₂, e₂⟩⟩ := h₁, h₂
    exact ⟨v₁ + (D.weylGroupHom n₁ : P.Aut).coweightEquiv.symm v₂,
      add_mem hv₁ (coweightEquiv_symm_mem_corootSpan _ hv₂),
      by rw [mul_smul, e₂, φ.smul_shift, e₁, shift_shift]⟩
  induction n using D.weylNormalizer_induction with
  | torus t ht => exact φ.exists_mem_corootSpan_torus_smul_eq_shift ht
  | reflection i m hm =>
    obtain ⟨k, u₀, u', u'', m₀, hm₀, hm₀_eq, hu₀⟩ :=
      φ.exists_mul_mul_mem_reflectionCoset_and_apply_eq i
    have ht : m * m₀⁻¹ ∈ D.T := D.mul_inv_mem_T hm₀ hm
    have hnm_eq : (⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ : D.weylNormalizer) =
        torusN ht * reflN hm₀ := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    exact hnm_eq ▸ hmul (φ.exists_mem_corootSpan_torus_smul_eq_shift ht)
      ⟨-(k • P.coroot i), neg_mem (Submodule.smul_mem _ k (P.corootSpanMem ℝ i).2),
        φ.smul_reflection hm₀ hm₀_eq hu₀⟩
  | one => exact ⟨0, zero_mem _, by rw [one_smul, shift_zero]⟩
  | mul _ _ ih₁ ih₂ => exact hmul ih₁ ih₂
  | inv n₁ ih =>
    obtain ⟨v, hv, h₁⟩ := ih; let w_act := (D.weylGroupHom n₁⁻¹ : P.Aut).coweightEquiv.symm v
    have h2 : φ = (n₁⁻¹ • φ).shift w_act :=
      (inv_smul_smul n₁ φ).symm.trans ((congrArg (n₁⁻¹ • ·) h₁).trans (φ.smul_shift n₁⁻¹ v))
    exact ⟨-w_act, neg_mem (coweightEquiv_symm_mem_corootSpan _ hv),
      by simpa using congrArg (Valuation.shift · (-w_act)) h2.symm⟩
theorem equipollent_smul (n : D.weylNormalizer) : φ.Equipollent (n • φ) :=
  let ⟨v, ⟨_, hv⟩, _⟩ := φ.existsUnique_mem_corootSpan_smul_eq_shift n; hv ▸ φ.equipollent_shift v
end RealWeylAction
end Valuation
end TauCeti.BruhatTits
