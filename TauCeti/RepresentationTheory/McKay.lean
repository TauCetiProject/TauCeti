/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.McKay.Matrix
public import TauCeti.RepresentationTheory.SU2.SymmetricPower
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.IntegralNullVector
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Recognition
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.SpecialNodes
import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration

/-!
# The McKay correspondence

Let `G` be a nontrivial finite group and `V` a faithful two-dimensional complex representation of
`G` with `det (V.ρ g) = 1` for every `g : G`. John McKay observed in 1980 that the tensor-product
multiplicities `dim_ℂ Hom_G(X, V ⊗ Y)` on the isomorphism classes of simple complex representations
of `G` form `2I - C` for the generalized Cartan matrix `C` of a valid affine simply-laced Dynkin
diagram (`Aₙ` for `n ≥ 1`, `Dₙ` for `n ≥ 4`, or `E₆`, `E₇`, `E₈`), with the dimensions of the
simples as the marks and the trivial representation at an affine node.

Following Steinberg (*Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*,
1985), the classification is proved directly from representation theory
(`TauCeti.RepresentationTheory.McKay.Matrix`) and the recognition of affine simply-laced diagrams,
without using a prior classification of the finite subgroups of `SL₂(ℂ)`:

1. **Symmetry** (`TauCeti.isSymm_mckayMatrix`): the `Fin 2` determinant form on `V` is unimodular
   and `G`-invariant (`Representation.equivDualOfFinrankEqTwo`), so `V` is self-dual and Frobenius
   reciprocity makes `mckayMatrix V` symmetric.
2. **Null vector** (`TauCeti.sum_mckayMatrix_mul_finrank`): decomposing `V ⊗ Y` into simples shows
   that the vector `δ` of irreducible dimensions satisfies `M δ = (dim V) δ = 2 δ`, with `δ > 0`
   and `δ = 1` at the trivial class.
3. **Connectedness**: `(mckayMatrix V ^ n) c trivial` equals the multiplicity of `c` in `V^⊗n`
   (`TauCeti.mckayMatrix_pow_apply_trivial`), which is positive for some `n` by Burnside–Brauer
   faithful tensor generation (`FDRep.exists_pos_finrank_hom_tensorPower`).
4. **Loop-freeness** (`FDRep.finrank_hom_tensor_self_eq_zero`): when `G` is nontrivial, no simple
   `X` occurs in `V ⊗ X`.
5. **Affine ADE recognition** (`TauCeti.exists_isMcKayLabelling`): if some off-diagonal entry is at
   least `2`, additive balance forces the graph to have two vertices of mark `1` joined by a double
   edge, giving `Ã₁`. Otherwise all entries are `0` or `1`, so Kac's additive-function recognition
   theorem (`SimpleGraph.Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso`) and
   transitivity of diagram automorphisms on special nodes
   (`TauCeti.AffineDynkinType.exists_graph_iso_apply_eq_affineNode`) produce a valid affine diagram
   with the trivial representation at `affineNode`.

Both hypotheses `Nontrivial G` and `∀ g, det (V.ρ g) = 1` are sharp: for the trivial group the
`1 × 1` McKay matrix `(2)` has a self-loop and is no affine diagram, while the standard
`2`-dimensional reflection representation of `S₃` is faithful and self-dual with determinant `±1`
and has a self-loop at its `2`-dimensional simple constituent.

## Main definitions

* `TauCeti.IsMcKayLabelling`: an affine ADE labelling of `SimpleFDRepClasses ℂ G` relative to `V`.
* `TauCeti.SU2.stdFDRep`: the tautological `2`-dimensional complex representation of a subgroup of
  `SU(2)`.

## Main results

* `TauCeti.exists_isMcKayLabelling`: **the McKay correspondence**, and
  `TauCeti.IsMcKayLabelling.eq_of_valid`: uniqueness of the valid affine diagram `t`.
* `TauCeti.SU2.exists_isMcKayLabelling`: specialization to finite nontrivial subgroups of `SU(2)`.

## References

* J. McKay, *Graphs, singularities, and finite groups*, Proc. Symp. Pure Math. **37** (1980),
  183–186.
* R. Steinberg, *Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*, Pacific J.
  Math. **118** (1985), 587–598.
-/

public section

open CategoryTheory MonoidalCategory Finset

universe u

namespace TauCeti

/-! ### Off-diagonal walks and affine ADE recognition for natural matrices -/

section MatrixRecognition

/-- A positive `(i, j)`-entry in `M ^ n` yields a reflexive-transitive path in the off-diagonal
support `x ≠ y ∧ 0 < M x y`, removing any diagonal steps automatically. -/
private theorem reflTransGen_of_matrix_pow_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℕ) :
    ∀ {n : ℕ} {i j : ι}, 0 < (M ^ n) i j →
      Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < M x y) i j
  | 0, i, j, h => by
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hij
    · exact hij ▸ .refl
    · omega
  | n + 1, i, j, h => by
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    have hMik : 0 < M i k := Nat.pos_of_ne_zero (left_ne_zero_of_mul hk)
    have hMkj : 0 < (M ^ n) k j := Nat.pos_of_ne_zero (right_ne_zero_of_mul hk)
    have ih := reflTransGen_of_matrix_pow_pos M hMkj
    by_cases hik : i = k
    · exact hik ▸ ih
    · exact .head ⟨hik, hMik⟩ ih

/-- Any symmetric, loop-free, connected matrix `M : Matrix ι ι ℕ` admitting a positive vector `δ`
with `δ i₀ = 1` and `M *ᵥ δ = 2 • δ` is isomorphic to `2I - t.cartanMatrix` for a valid
`t : AffineDynkinType`, with `δ` matching `t.marks` and `i₀` mapped to `t.affineNode`. -/
private theorem exists_affineDynkinType_of_symm_loopFree_nullVector {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℕ) (hSymm : M.IsSymm) (hLoop : ∀ i, M i i = 0)
    (i₀ : ι) (hConn : ∀ i, Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < M x y) i i₀)
    (δ : ι → ℕ) (hδ_pos : ∀ i, 0 < δ i) (hδ_one : δ i₀ = 1)
    (hδ_sum : ∀ i, ∑ j, M i j * δ j = 2 * δ i) :
    ∃ (t : AffineDynkinType) (e : ι ≃ Fin t.nodes),
      t.Valid ∧
        (∀ x y : ι,
          (M x y : ℤ) = 2 * (if e x = e y then 1 else 0) - t.cartanMatrix (e x) (e y)) ∧
        (∀ x : ι, (δ x : ℤ) = t.marks (e x)) ∧
        e i₀ = t.affineNode := by
  classical
  let r : ι → ι → Prop := fun x y ↦ x ≠ y ∧ 0 < M x y
  have hsymm_rtg {x y : ι} (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.head ⟨hstep.1.symm, hSymm.apply _ _ ▸ hstep.2⟩
  have hReach (x y : ι) : Relation.ReflTransGen r x y :=
    (hConn x).trans (hsymm_rtg (hConn y))
  if hMult : ∃ a b : ι, 2 ≤ M a b then
    -- Double-edge branch: additive balance forces `ι` to consist of `{i₀, c}` with type `Ã₁`.
    obtain ⟨a, b, hab2⟩ := hMult
    have hab : a ≠ b := fun h ↦ by rw [h, hLoop b] at hab2; omega
    have hMba2 : 2 ≤ M b a := hSymm.apply a b ▸ hab2
    have hle_ab : M a b * δ b ≤ 2 * δ a := by
      rw [← hδ_sum a]
      exact single_le_sum (f := fun j ↦ M a j * δ j) (fun _ _ ↦ Nat.zero_le _) (mem_univ b)
    have hle_ba : M b a * δ a ≤ 2 * δ b := by
      rw [← hδ_sum b]
      exact single_le_sum (f := fun j ↦ M b j * δ j) (fun _ _ ↦ Nat.zero_le _) (mem_univ a)
    have hδ_le1 : 2 * δ b ≤ 2 * δ a :=
      (Nat.mul_le_mul_right (δ b) hab2).trans hle_ab
    have hδ_le2 : 2 * δ a ≤ 2 * δ b :=
      (Nat.mul_le_mul_right (δ a) hMba2).trans hle_ba
    have hδ_ab : δ a = δ b := by omega
    have hMab_eq : M a b = 2 := by
      have hpos := hδ_pos b
      have : 2 * δ b ≤ M a b * δ b ∧ M a b * δ b ≤ 2 * δ b :=
        ⟨Nat.mul_le_mul_right _ hab2, hδ_ab ▸ hle_ab⟩
      nlinarith
    have hMba_eq : M b a = 2 := (hSymm.apply a b).trans hMab_eq
    have hMa_other (j : ι) (hjb : j ≠ b) : M a j = 0 := by
      have hpair : M a b * δ b + M a j * δ j ≤ 2 * δ a := by
        rw [← hδ_sum a]
        exact add_le_sum (f := fun k ↦ M a k * δ k) (fun _ _ ↦ Nat.zero_le _)
          (mem_univ b) (mem_univ j) hjb.symm
      rw [hMab_eq, hδ_ab] at hpair
      have h0 : M a j * δ j = 0 := by omega
      exact (Nat.mul_eq_zero.mp h0).resolve_right (hδ_pos j).ne'
    have hMb_other (j : ι) (hja : j ≠ a) : M b j = 0 := by
      have hpair : M b a * δ a + M b j * δ j ≤ 2 * δ b := by
        rw [← hδ_sum b]
        exact add_le_sum (f := fun k ↦ M b k * δ k) (fun _ _ ↦ Nat.zero_le _)
          (mem_univ a) (mem_univ j) hja.symm
      rw [hMba_eq, hδ_ab] at hpair
      have h0 : M b j * δ j = 0 := by omega
      exact (Nat.mul_eq_zero.mp h0).resolve_right (hδ_pos j).ne'
    have hall_ab (k : ι) : k = a ∨ k = b := by
      suffices ∀ x y : ι, Relation.ReflTransGen r x y → (x = a ∨ x = b) → (y = a ∨ y = b) from
        this a k (hReach a k) (Or.inl rfl)
      intro x y hxy
      induction hxy with
      | refl => exact id
      | tail _ hstep ih =>
        intro hx
        rcases ih hx with rfl | rfl
        · exact Or.inr (by_contra fun hyb ↦ by have := hMa_other _ hyb; have := hstep.2; omega)
        · exact Or.inl (by_contra fun hya ↦ by have := hMb_other _ hya; have := hstep.2; omega)
    obtain ⟨c, hc_ne, hc_all, hMic, hMci, hδc⟩ :
        ∃ c : ι, i₀ ≠ c ∧ (∀ k : ι, k = i₀ ∨ k = c) ∧ M i₀ c = 2 ∧ M c i₀ = 2 ∧ δ c = 1 := by
      rcases hall_ab i₀ with rfl | rfl
      · exact ⟨b, hab, hall_ab, hMab_eq, hMba_eq, hδ_ab.symm.trans hδ_one⟩
      · exact ⟨a, hab.symm, fun k ↦ (hall_ab k).symm, hMba_eq, hMab_eq, hδ_ab.trans hδ_one⟩
    let e' : ι ≃ Fin 2 :=
      { toFun x := if x = i₀ then 0 else 1
        invFun j := if j = 0 then i₀ else c
        left_inv x := by
          rcases hc_all x with rfl | rfl
          · simp
          · simp [hc_ne.symm]
        right_inv := Fin.forall_fin_two.2 ⟨by simp, by simp [hc_ne.symm]⟩ }
    let e : ι ≃ Fin (AffineDynkinType.A 1).nodes := e'
    refine ⟨AffineDynkinType.A 1, e, AffineDynkinType.valid_A.mpr le_rfl, fun x y ↦ ?_,
      fun x ↦ ?_, ?_⟩
    · rw [AffineDynkinType.cartanMatrix_A_one_apply]
      simp only [e.injective.eq_iff]
      rcases hc_all x with rfl | rfl <;> rcases hc_all y with rfl | rfl
      · simp [hLoop]
      · simp [hc_ne, hMic]
      · simp [hc_ne.symm, hMci]
      · simp [hLoop]
    · rw [AffineDynkinType.marks_A_apply]
      rcases hc_all x with rfl | rfl <;> simp [hδ_one, hδc]
    · rw [AffineDynkinType.affineNode_A]
      change e' i₀ = 0
      simp [e']
  else
    -- Simple-graph branch: all entries of `M` are `0` or `1`.
    have hM_le1 (x y : ι) : M x y ≤ 1 :=
      Nat.le_of_not_lt fun h ↦ hMult ⟨x, y, h⟩
    let G : SimpleGraph ι :=
      { Adj x y := M x y ≠ 0
        symm := ⟨fun x y hxy ↦ by rwa [← hSymm.apply x y] at hxy⟩
        loopless := ⟨fun x hx ↦ hx (hLoop x)⟩ }
    let _ : DecidableRel G.Adj := fun x y ↦ inferInstanceAs (Decidable (M x y ≠ 0))
    have hM_ite (x y : ι) : M x y = if G.Adj x y then 1 else 0 := by
      have hle := hM_le1 x y
      change M x y = if M x y ≠ 0 then 1 else 0
      split_ifs <;> omega
    have _ : Nonempty ι := ⟨i₀⟩
    have hG_conn : G.Connected := by
      refine ⟨fun x y ↦ ?_⟩
      induction hReach x y with
      | refl => exact SimpleGraph.Reachable.refl (G := G) _
      | tail _ hstep ih => exact ih.trans (SimpleGraph.Adj.reachable hstep.2.ne')
    have hδ_ne : δ ≠ 0 := fun h ↦ by simp [h] at hδ_one
    have hG_sum (i : ι) : ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i := by
      rw [← hδ_sum i, SimpleGraph.neighborFinset_eq_filter]
      simp [hM_ite, Finset.sum_ite]
    obtain ⟨t, ⟨ht, hg, ⟨iso⟩⟩, -⟩ :=
      hG_conn.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso.mp ⟨δ, hδ_ne, hG_sum⟩
    have hgcd : univ.gcd δ = 1 := by
      apply Nat.dvd_one.mp
      simpa [hδ_one] using univ.gcd_dvd (f := δ) (mem_univ i₀)
    have hmarks_iso (x : ι) : (δ x : ℤ) = t.marks (iso x) := by
      have heq := congrFun (iso.eq_gcd_smul_marks_comp ht hg hG_sum) x
      simpa [hgcd] using heq
    have hmark_i₀ : t.marks (iso i₀) = 1 := by
      rw [← hmarks_iso i₀, hδ_one, Nat.cast_one]
    obtain ⟨σ, hσ⟩ := AffineDynkinType.exists_graph_iso_apply_eq_affineNode ht hmark_i₀
    let e_iso : G ≃g t.graph := iso.trans σ
    refine ⟨t, e_iso.toEquiv, ht, fun x y ↦ ?_, fun x ↦ ?_, hσ⟩
    · rw [AffineDynkinType.cartanMatrix_apply hg]
      simp only [RelIso.coe_fn_toEquiv, e_iso.injective.eq_iff, e_iso.map_adj_iff, hM_ite]
      by_cases hxy : x = y
      · subst hxy
        simp
      · simp only [hxy, ↓reduceIte]
        split_ifs <;> norm_num
    · change (δ x : ℤ) = t.marks (σ (iso x))
      rw [AffineDynkinType.marks_graph_iso_apply σ (iso x), hmarks_iso]

end MatrixRecognition

/-! ### McKay labellings and the McKay correspondence -/

/-- A **McKay labelling** of the simple complex representations of `G` by an affine simply-laced
diagram `t`, relative to `V`: a bijection `e` from `SimpleFDRepClasses ℂ G` to the nodes of `t`
such that

* the multiplicity `dim_ℂ Hom_G(X, V ⊗ Y)` of a simple `X` in `V ⊗ Y` equals `2 δ_{i,j} - C_{i,j}`
  at the nodes `i = e [X]` and `j = e [Y]`, for the generalized Cartan matrix `C` of `t`;
* the dimension of each simple equals the mark of its node;
* any one-dimensional trivial representation sits at `t.affineNode`. -/
def IsMcKayLabelling {G : Type u} [Group G] (V : FDRep ℂ G) (t : TauCeti.AffineDynkinType)
    (e : TauCeti.SimpleFDRepClasses ℂ G ≃ Fin t.nodes) : Prop :=
  (∀ (X Y : FDRep ℂ G) [Simple X] [Simple Y],
      (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
        2 * (if e (TauCeti.SimpleFDRepClasses.mk X) = e (TauCeti.SimpleFDRepClasses.mk Y)
          then 1 else 0) -
          t.cartanMatrix (e (TauCeti.SimpleFDRepClasses.mk X))
            (e (TauCeti.SimpleFDRepClasses.mk Y))) ∧
    (∀ (X : FDRep ℂ G) [Simple X],
      (Module.finrank ℂ X : ℤ) = t.marks (e (TauCeti.SimpleFDRepClasses.mk X))) ∧
    ∀ (X : FDRep ℂ G) [Simple X], (∀ g : G, X.ρ g = 1) →
      e (TauCeti.SimpleFDRepClasses.mk X) = t.affineNode

namespace IsMcKayLabelling

variable {G : Type u} [Group G] {V : FDRep ℂ G} {t : AffineDynkinType}
  {e : SimpleFDRepClasses ℂ G ≃ Fin t.nodes}

/-- Under a McKay labelling, `(mckayMatrix V c₁ c₂ : ℤ) = 2 δ_{e c₁, e c₂} - C_{e c₁, e c₂}`. -/
theorem mckayMatrix_apply (h : IsMcKayLabelling V t e) (c₁ c₂ : SimpleFDRepClasses ℂ G) :
    (mckayMatrix V c₁ c₂ : ℤ) =
      2 * (if e c₁ = e c₂ then 1 else 0) - t.cartanMatrix (e c₁) (e c₂) := by
  induction c₁ using SimpleFDRepClasses.ind with
  | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_mk_mk]
    exact h.1 X Y

/-- Under a McKay labelling, `(c.finrank : ℤ) = t.marks (e c)` for every simple class `c`. -/
theorem finrank_eq_marks (h : IsMcKayLabelling V t e) (c : SimpleFDRepClasses ℂ G) :
    (c.finrank : ℤ) = t.marks (e c) := by
  induction c using SimpleFDRepClasses.ind with
  | h X hX =>
    rw [SimpleFDRepClasses.finrank_mk]
    exact h.2.1 X

/-- Under a McKay labelling, `SimpleFDRepClasses.trivial ℂ G` maps to `t.affineNode`. -/
theorem apply_trivial (h : IsMcKayLabelling V t e) :
    e (SimpleFDRepClasses.trivial ℂ G) = t.affineNode := by
  let T : FDRep ℂ G := FDRep.of (_root_.Representation.trivial ℂ G ℂ)
  have htriv (g : G) : T.ρ g = 1 := LinearMap.ext fun v ↦ by
    rw [FDRep.of_ρ', _root_.Representation.trivial_apply, one_apply_eq_self]
  rw [← (SimpleFDRepClasses.mk_eq_trivial_iff T).mpr htriv]
  exact h.2.2 T htriv

/-- **Uniqueness of the affine Dynkin type in a McKay labelling.** Any two valid affine
simply-laced diagrams admitting McKay labellings for the same representation `V` are equal. -/
theorem eq_of_valid {t₁ t₂ : AffineDynkinType} {e₁ : SimpleFDRepClasses ℂ G ≃ Fin t₁.nodes}
    {e₂ : SimpleFDRepClasses ℂ G ≃ Fin t₂.nodes} (ht₁ : t₁.Valid) (ht₂ : t₂.Valid)
    (h₁ : IsMcKayLabelling V t₁ e₁) (h₂ : IsMcKayLabelling V t₂ e₂) :
    t₁ = t₂ := by
  let σ : Fin t₁.nodes ≃ Fin t₂.nodes := e₁.symm.trans e₂
  have hC (i j : Fin t₁.nodes) : t₂.cartanMatrix (σ i) (σ j) = t₁.cartanMatrix i j := by
    have eq1 := h₁.mckayMatrix_apply (e₁.symm i) (e₁.symm j)
    have eq2 := h₂.mckayMatrix_apply (e₁.symm i) (e₁.symm j)
    simp only [Equiv.apply_symm_apply] at eq1
    have hiff : (e₂ (e₁.symm i) = e₂ (e₁.symm j)) ↔ (i = j) := by
      rw [e₂.injective.eq_iff, e₁.symm.injective.eq_iff]
    simp only [σ, Equiv.trans_apply, hiff] at eq2 ⊢
    omega
  have hne01 : (0 : Fin (AffineDynkinType.A 1).nodes) ≠ 1 := by decide
  by_cases hg₁ : t₁.IsGraphical
  · by_cases hg₂ : t₂.IsGraphical
    · refine AffineDynkinType.eq_of_graph_iso ht₁ ht₂ ⟨σ, ?_⟩
      intro i j
      by_cases hij : i = j
      · subst hij
        simp [SimpleGraph.irrefl]
      · have hcij := hC i j
        rw [AffineDynkinType.cartanMatrix_apply hg₁,
          AffineDynkinType.cartanMatrix_apply hg₂] at hcij
        simp only [hij, σ.injective.eq_iff, ↓reduceIte] at hcij
        constructor <;> intro hadj <;> simp [hadj] at hcij <;>
          by_contra hnot <;> simp [hnot] at hcij
    · rw [AffineDynkinType.isGraphical_iff_ne_A_one, not_not] at hg₂
      subst hg₂
      have h01 := hC (σ.symm 0) (σ.symm 1)
      simp only [Equiv.apply_symm_apply, AffineDynkinType.cartanMatrix_A_one_apply,
        AffineDynkinType.cartanMatrix_apply hg₁, σ.symm.injective.eq_iff, hne01, ↓reduceIte] at h01
      split_ifs at h01; norm_num at h01
  · rw [AffineDynkinType.isGraphical_iff_ne_A_one, not_not] at hg₁
    subst hg₁
    by_cases hg₂ : t₂.IsGraphical
    · have h01 := hC 0 1
      simp only [AffineDynkinType.cartanMatrix_A_one_apply,
        AffineDynkinType.cartanMatrix_apply hg₂, σ.injective.eq_iff, hne01, ↓reduceIte] at h01
      split_ifs at h01; norm_num at h01
    · rw [AffineDynkinType.isGraphical_iff_ne_A_one, not_not] at hg₂
      exact hg₂.symm

end IsMcKayLabelling

/-- **The McKay correspondence** (McKay 1980; Steinberg 1985). For a nontrivial finite group `G`
and a faithful two-dimensional complex representation `V` of determinant `1`, the McKay matrix of
`V` is `2I - C` for the generalized Cartan matrix `C` of a valid affine simply-laced Dynkin
diagram, with the dimensions of the simples as its marks and the trivial representation at its
affine node. -/
theorem exists_isMcKayLabelling {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (V : FDRep ℂ G) (hdim : Module.finrank ℂ V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) :
    ∃ (t : TauCeti.AffineDynkinType) (e : TauCeti.SimpleFDRepClasses ℂ G ≃ Fin t.nodes),
      t.Valid ∧ IsMcKayLabelling V t e := by
  classical
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ : Fintype (SimpleFDRepClasses ℂ G) :=
    Fintype.ofEquiv _ (SimpleFDRepClasses.equivFinCardConjClasses ℂ G).symm
  have hSymm : (mckayMatrix V).IsSymm := isSymm_mckayMatrix hdim hdet
  have hLoop (c : SimpleFDRepClasses ℂ G) : mckayMatrix V c c = 0 :=
    mckayMatrix_apply_self_eq_zero hdim hfaithful hdet c
  have hConn (c : SimpleFDRepClasses ℂ G) :
      Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < mckayMatrix V x y)
        c (SimpleFDRepClasses.trivial ℂ G) := by
    obtain ⟨n, -, hn⟩ : ∃ n < V.characterValueCount, 0 < c.multiplicity (V.tensorPower n) := by
      induction c using SimpleFDRepClasses.ind with
      | h X hX =>
        simp_rw [SimpleFDRepClasses.multiplicity_mk]
        exact FDRep.exists_pos_finrank_hom_tensorPower V X hfaithful
          (FDRep.isIrreducible_of_simple X).finrank_pos
    rw [← mckayMatrix_pow_apply_trivial V n c] at hn
    exact reflTransGen_of_matrix_pow_pos (mckayMatrix V) hn
  have hSum (c : SimpleFDRepClasses ℂ G) :
      ∑ c₂, mckayMatrix V c c₂ * c₂.finrank = 2 * c.finrank := by
    simpa [hdim] using sum_mckayMatrix_mul_finrank hSymm c
  obtain ⟨t, e, ht, hCartan, hMarks, hAff⟩ :=
    exists_affineDynkinType_of_symm_loopFree_nullVector (mckayMatrix V) hSymm hLoop
      (SimpleFDRepClasses.trivial ℂ G) hConn SimpleFDRepClasses.finrank
      SimpleFDRepClasses.finrank_pos SimpleFDRepClasses.finrank_trivial hSum
  refine ⟨t, e, ht, ⟨fun X Y _ _ ↦ ?_, fun X _ ↦ ?_, fun X _ htriv ↦ ?_⟩⟩
  · simpa [mckayMatrix_mk_mk] using hCartan (SimpleFDRepClasses.mk X) (SimpleFDRepClasses.mk Y)
  · simpa [SimpleFDRepClasses.finrank_mk] using hMarks (SimpleFDRepClasses.mk X)
  · rw [(SimpleFDRepClasses.mk_eq_trivial_iff X).mpr htriv]
    exact hAff

/-! ### Specialization to finite subgroups of `SU(2)` -/

namespace SU2

/-- The tautological two-dimensional complex representation of a subgroup `H : Subgroup SU2`,
obtained by restricting `TauCeti.stdRep ℂ 2` along `H → SU(2) → GL₂(ℂ)`. -/
noncomputable def stdFDRep (H : Subgroup SU2) : FDRep ℂ H :=
  FDRep.of ((TauCeti.stdRep ℂ 2).comp (TauCeti.SU2.toGL.comp H.subtype))

/-- `SU2.stdFDRep H` is the bundling of `(stdRep ℂ 2).comp (SU2.toGL.comp H.subtype)`. Together
with `FDRep.of_ρ'`, this recovers the action without unfolding `stdFDRep`. -/
theorem stdFDRep_def (H : Subgroup SU2) :
    stdFDRep H = FDRep.of ((TauCeti.stdRep ℂ 2).comp (TauCeti.SU2.toGL.comp H.subtype)) :=
  (rfl)

@[simp]
theorem finrank_stdFDRep (H : Subgroup SU2) : Module.finrank ℂ (stdFDRep H) = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  simp

theorem injective_ρ_stdFDRep (H : Subgroup SU2) : Function.Injective (stdFDRep H).ρ := by
  rw [stdFDRep_def, FDRep.of_ρ']
  exact (TauCeti.stdRep_injective ℂ 2).comp (TauCeti.SU2.toGL_injective.comp H.subtype_injective)

@[simp]
theorem det_ρ_stdFDRep (H : Subgroup SU2) (h : H) : LinearMap.det ((stdFDRep H).ρ h) = 1 := by
  rw [stdFDRep_def, FDRep.of_ρ', MonoidHom.comp_apply, MonoidHom.comp_apply, TauCeti.stdRep_apply,
    ← Matrix.toLin'_apply', LinearMap.det_toLin', coe_toGL]
  exact (Matrix.mem_specialUnitaryGroup_iff.mp h.1.2).2

@[simp]
theorem character_stdFDRep (H : Subgroup SU2) (h : H) :
    (stdFDRep H).character h = Matrix.trace (h.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdFDRep_def, FDRep.character_of, _root_.Representation.character, MonoidHom.comp_apply,
    MonoidHom.comp_apply, TauCeti.stdRep_apply, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq,
    coe_toGL]
  rfl

/-- **The McKay correspondence for finite nontrivial subgroups of `SU(2)`.** -/
theorem exists_isMcKayLabelling (H : Subgroup SU2) [Finite H] [Nontrivial H] :
    ∃ (t : AffineDynkinType) (e : SimpleFDRepClasses ℂ H ≃ Fin t.nodes),
      t.Valid ∧ IsMcKayLabelling (stdFDRep H) t e :=
  TauCeti.exists_isMcKayLabelling (stdFDRep H) (finrank_stdFDRep H) (injective_ρ_stdFDRep H)
    (det_ρ_stdFDRep H)

end SU2

end TauCeti
