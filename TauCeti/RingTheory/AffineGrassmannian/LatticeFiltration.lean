/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Pi

/-!
# The filtration of the special fibre defined by a lattice

Let `B` be a commutative ring, `ξ ∈ B`, and `K` a `B`-algebra in which `ξ` becomes invertible;
the motivating case is `B = B⁺_dR`, `K = B_dR` and `ξ` a generator of the kernel of `θ`, so that
`B ⧸ ξ` is the residue field. For a `B`-submodule `Λ ⊆ Kⁿ` and `m ∈ ℤ` this file defines
`Fil^m Λ ⊆ (B ⧸ ξ)ⁿ` (`Submodule.latticeFiltration`) as the reduction modulo `ξ` of
`Bⁿ ∩ ξ^{-m} Λ`, that is, of the vectors `x ∈ Bⁿ` with `ξ^m x ∈ Λ`. When `B → K` is injective
this image is the quotient `(Bⁿ ∩ ξ^{-m} Λ) / (ξ Bⁿ ∩ ξ^{-m} Λ)` in which Caraiani–Scholze write
the filtration describing the Bialynicki-Birula map from the affine Grassmannian of `GLₙ` to a
flag variety. It increases with `m` and with `Λ`, and it is equivariant for `GLₙ(B)`.

For a cocharacter `μ = (k_i)` of the diagonal torus, `TauCeti.diagonalLattice k` is the lattice
`μ(ξ) Bⁿ = ⊕ ξ^{k_i} B`. If `B → K` is injective and `g ∈ GLₙ(B)`, the filtration of the
translated lattice `g μ(ξ) Bⁿ` is the image under the reduction of `g` modulo `ξ` of the
coordinate subspace spanned by the `e_i` with `k_i ≤ m`. Hence it is a direct summand of
`(B ⧸ ξ)ⁿ`, free of rank `#{i | k_i ≤ m}` when `ξ` is not a unit, and its formation commutes with
base change along any ring map `B → B'` for which `B'` also embeds in its coefficient algebra.

## Main definitions

* `Submodule.latticeFiltration Λ hξ m`: the filtration `Fil^m Λ ⊆ (B ⧸ ξ)ⁿ`.
* `TauCeti.diagonalLattice k hξ`: the lattice `μ(ξ) Bⁿ ⊆ Kⁿ` of the cocharacter `μ = (k_i)`.

## Main results

* `Submodule.monotone_latticeFiltration`: `Fil^m Λ ⊆ Fil^{m'} Λ` for `m ≤ m'`.
* `Submodule.latticeFiltration_map_mulVecLin`: `Fil^m (g Λ) = (g mod ξ) Fil^m Λ` for
  `g ∈ GLₙ(B)`.
* `Submodule.latticeFiltration_diagonalLattice`: `Fil^m (μ(ξ) Bⁿ)` consists of the vectors
  vanishing at every `i` with `m < k_i`.
* `Submodule.finrank_latticeFiltration_map_diagonalLattice`: `Fil^m (g μ(ξ) Bⁿ)` has rank
  `#{i | k_i ≤ m}`.
* `Submodule.exists_isCompl_latticeFiltration_map_diagonalLattice`: `Fil^m (g μ(ξ) Bⁿ)` is a
  direct summand of `(B ⧸ ξ)ⁿ`.
* `Submodule.latticeFiltration_map_diagonalLattice_eq_span_image`: for a ring map `φ : B → B'`,
  the filtration of `φ(g) μ(φ ξ) B'ⁿ` is spanned by the image of that of `g μ(ξ) Bⁿ`.

## References

* A. Caraiani, P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), Proposition 3.4.3 and its proof.
* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, §VI.2.
-/

public section

variable {B K : Type*} [CommRing B] [CommRing K] [Algebra B K] {n : Type*} {ξ : B}

namespace Submodule

/-- **The filtration of the special fibre defined by a lattice.** For a `B`-submodule
`Λ ⊆ Kⁿ`, an element `ξ ∈ B` that is invertible in `K`, and `m ∈ ℤ`, `Fil^m Λ` is the image in
`(B ⧸ ξ)ⁿ` of the vectors `x ∈ Bⁿ` with `ξ^m x ∈ Λ`, i.e. of `Bⁿ ∩ ξ^{-m} Λ`. -/
def latticeFiltration (Λ : Submodule B (n → K)) (hξ : IsUnit (algebraMap B K ξ)) (m : ℤ) :
    Submodule (B ⧸ Ideal.span {ξ}) (n → B ⧸ Ideal.span {ξ}) where
  carrier := {y | ∃ x : n → B, (hξ.unit ^ m) • (fun i ↦ algebraMap B K (x i)) ∈ Λ ∧
    (fun i ↦ Ideal.Quotient.mk _ (x i)) = y}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    refine ⟨x + x', ?_, by ext; simp⟩
    convert Λ.add_mem hx hx' using 1
    ext i
    simp [Units.smul_def]
  zero_mem' := ⟨0, by convert Λ.zero_mem; ext; simp, by ext; simp⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b • x, ?_, by ext; simp⟩
    convert Λ.smul_mem b hx using 1
    ext i
    simp [Units.smul_def, Algebra.smul_def]
    ring

@[simp]
theorem mem_latticeFiltration {Λ : Submodule B (n → K)} {hξ : IsUnit (algebraMap B K ξ)}
    {m : ℤ} {y : n → B ⧸ Ideal.span {ξ}} :
    y ∈ Λ.latticeFiltration hξ m ↔ ∃ x : n → B,
      (hξ.unit ^ m) • (fun i ↦ algebraMap B K (x i)) ∈ Λ ∧
        (fun i ↦ Ideal.Quotient.mk _ (x i)) = y :=
  Iff.rfl

/-- The filtration increases with the lattice. -/
theorem latticeFiltration_mono {Λ Λ' : Submodule B (n → K)} (h : Λ ≤ Λ')
    (hξ : IsUnit (algebraMap B K ξ)) (m : ℤ) :
    Λ.latticeFiltration hξ m ≤ Λ'.latticeFiltration hξ m := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- For `a ≤ b`, the power `ξ ^ b` in `K` is `ξ ^ a` times the image of `ξ ^ (b - a)`. -/
private theorem val_unit_zpow_of_le (hξ : IsUnit (algebraMap B K ξ)) {a b : ℤ} (h : a ≤ b) :
    ((hξ.unit ^ b : Kˣ) : K) = (hξ.unit ^ a : Kˣ) * algebraMap B K (ξ ^ (b - a).toNat) := by
  have hb : b = a + ((b - a).toNat : ℕ) := by omega
  conv_lhs => rw [hb, zpow_add, zpow_natCast]
  simp

/-- **The filtration is increasing**: `Fil^m Λ ⊆ Fil^{m'} Λ` for `m ≤ m'`. -/
theorem monotone_latticeFiltration (Λ : Submodule B (n → K)) (hξ : IsUnit (algebraMap B K ξ)) :
    Monotone (Λ.latticeFiltration hξ) := by
  rintro m m' h _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  convert Λ.smul_mem (ξ ^ (m' - m).toNat) hx using 1
  ext i
  simp [Units.smul_def, Algebra.smul_def, val_unit_zpow_of_le hξ h]
  ring

open Matrix

/-- Applying a ring map to the coordinates of `A *ᵥ x` gives `A.map f *ᵥ (f ∘ x)`. -/
private theorem map_mulVec_eq [Fintype n] {S : Type*} [CommRing S] (f : B →+* S)
    (A : Matrix n n B) (x : n → B) :
    (fun i ↦ f ((A *ᵥ x) i)) = A.map f *ᵥ fun i ↦ f (x i) :=
  funext fun i ↦ RingHom.map_mulVec f A x i

/-- **Equivariance of the filtration.** For `g ∈ GLₙ(B)`, the filtration of the translated
lattice `g Λ` is the image of the filtration of `Λ` under the reduction of `g` modulo `ξ`. -/
theorem latticeFiltration_map_mulVecLin [Fintype n] [DecidableEq n] (g : GL n B)
    (Λ : Submodule B (n → K)) (hξ : IsUnit (algebraMap B K ξ)) (m : ℤ) :
    (Λ.map (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B)
        ).latticeFiltration hξ m =
      (Λ.latticeFiltration hξ m).map
        ((g : Matrix n n B).map (Ideal.Quotient.mk (Ideal.span {ξ}))).mulVecLin := by
  ext y
  constructor
  · rintro ⟨x, ⟨l, hl, hxl⟩, rfl⟩
    simp only [LinearMap.restrictScalars_apply, mulVecLin_apply] at hxl
    refine ⟨_, ⟨(g : Matrix n n B)⁻¹ *ᵥ x, ?_, rfl⟩, ?_⟩
    · rw [map_mulVec_eq, Units.smul_def, ← mulVec_smul, ← Units.smul_def, ← hxl, mulVec_mulVec,
        GeneralLinearGroup.coe_map_inv_mul_map, one_mulVec]
      exact hl
    · rw [mulVecLin_apply, map_mulVec_eq, mulVec_mulVec, GeneralLinearGroup.coe_map_mul_map_inv,
        one_mulVec]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g *ᵥ x, ⟨_, hx, ?_⟩, ?_⟩
    · rw [LinearMap.restrictScalars_apply, mulVecLin_apply, map_mulVec_eq, Units.smul_def,
        Units.smul_def, mulVec_smul]
    · rw [mulVecLin_apply]
      exact map_mulVec_eq _ _ _

end Submodule

namespace TauCeti

/-- **The lattice of a diagonal cocharacter.** For `k : n → ℤ`, the `B`-lattice
`μ(ξ) Bⁿ = {v ∈ Kⁿ | v i ∈ ξ^{k i} B for all i}` of the cocharacter `μ = (k_i)` of the diagonal
torus, evaluated at `ξ`. -/
noncomputable def diagonalLattice (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    Submodule B (n → K) :=
  Submodule.pi Set.univ fun i ↦ Submodule.span B {((hξ.unit ^ k i : Kˣ) : K)}

@[simp]
theorem mem_diagonalLattice {k : n → ℤ} {hξ : IsUnit (algebraMap B K ξ)} {v : n → K} :
    v ∈ diagonalLattice k hξ ↔ ∀ i, ∃ b : B, v i = (hξ.unit ^ k i : Kˣ) * algebraMap B K b := by
  simp only [diagonalLattice, Submodule.mem_pi, Set.mem_univ, true_imp_iff,
    Submodule.mem_span_singleton, Algebra.smul_def]
  exact forall_congr' fun i ↦ exists_congr fun b ↦ by rw [mul_comm, eq_comm]

end TauCeti

namespace Submodule

open Matrix TauCeti

/-- **The filtration of a diagonal lattice.** If `B → K` is injective, `Fil^m (μ(ξ) Bⁿ)`
consists of the vectors of `(B ⧸ ξ)ⁿ` vanishing at every `i` with `m < k i`; it is the coordinate
subspace spanned by the `e_i` with `k i ≤ m`. -/
theorem latticeFiltration_diagonalLattice (hinj : Function.Injective (algebraMap B K))
    (hξ : IsUnit (algebraMap B K ξ)) (k : n → ℤ) (m : ℤ) :
    (diagonalLattice k hξ).latticeFiltration hξ m = pi {i | m < k i} fun _ ↦ ⊥ := by
  ext y
  simp only [mem_pi, mem_bot, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩ i hi
    -- `ξ^m x_i ∈ ξ^{k_i} B` with `m < k_i` forces `x_i ∈ ξ^{k_i - m} B ⊆ ξ B`.
    obtain ⟨b, hb⟩ := mem_diagonalLattice.1 hx i
    have hx' : x i = ξ ^ (k i - m).toNat * b := by
      apply hinj
      simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, val_unit_zpow_of_le hξ hi.le,
        mul_assoc] at hb
      simpa only [map_mul] using (Units.mul_right_inj _).1 hb
    dsimp only
    rw [hx', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact (dvd_pow_self ξ (by omega)).mul_right b
  · intro hy
    -- Lift `y`, choosing the lift `0` at the coordinates where `y` must vanish.
    choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
    classical
    refine ⟨fun i ↦ if m < k i then 0 else x i, mem_diagonalLattice.2 fun i ↦ ?_,
      funext fun i ↦ ?_⟩
    · simp only [Pi.smul_apply]
      split_ifs with h
      · exact ⟨0, by simp⟩
      · refine ⟨ξ ^ (m - k i).toNat * x i, ?_⟩
        simp [Units.smul_def, val_unit_zpow_of_le hξ (not_lt.1 h), mul_assoc]
    · dsimp only
      split_ifs with h
      · simp [hy i h]
      · exact hx i

variable [Fintype n] [DecidableEq n]

/-- The reduction of `g ∈ GLₙ(B)` modulo `ξ`, as a linear automorphism of `(B ⧸ ξ)ⁿ`. -/
private noncomputable def reductionEquiv (ξ : B) (g : GL n B) :
    (n → B ⧸ Ideal.span {ξ}) ≃ₗ[B ⧸ Ideal.span {ξ}] n → B ⧸ Ideal.span {ξ} :=
  LinearEquiv.ofLinearMap ((g : Matrix n n B).map (Ideal.Quotient.mk _)).mulVecLin
    ((g : Matrix n n B)⁻¹.map (Ideal.Quotient.mk _)).mulVecLin
    (by rw [← mulVecLin_mul, GeneralLinearGroup.coe_map_mul_map_inv, mulVecLin_one])
    (by rw [← mulVecLin_mul, GeneralLinearGroup.coe_map_inv_mul_map, mulVecLin_one])

private theorem latticeFiltration_map_diagonalLattice_eq
    (hinj : Function.Injective (algebraMap B K)) (hξ : IsUnit (algebraMap B K ξ)) (g : GL n B)
    (k : n → ℤ) (m : ℤ) :
    ((diagonalLattice k hξ).map
        (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B)).latticeFiltration
        hξ m = (pi {i | m < k i} fun _ ↦ ⊥).map (reductionEquiv ξ g).toLinearMap := by
  rw [latticeFiltration_map_mulVecLin, latticeFiltration_diagonalLattice hinj, reductionEquiv,
    LinearEquiv.toLinearMap_ofLinearMap]

/-- **Rank of the filtration of a translated diagonal lattice.** If `B → K` is injective and `ξ`
is not a unit of `B`, the filtration `Fil^m (g μ(ξ) Bⁿ)` has rank `#{i | k i ≤ m}` over `B ⧸ ξ`. -/
theorem finrank_latticeFiltration_map_diagonalLattice [Nontrivial (B ⧸ Ideal.span {ξ})]
    (hinj : Function.Injective (algebraMap B K)) (hξ : IsUnit (algebraMap B K ξ)) (g : GL n B)
    (k : n → ℤ) (m : ℤ) :
    Module.finrank (B ⧸ Ideal.span {ξ})
        (((diagonalLattice k hξ).map
          (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B)).latticeFiltration
          hξ m) = Fintype.card {i // k i ≤ m} := by
  classical
  have hd : Disjoint {i | k i ≤ m} {i | m < k i} :=
    Set.disjoint_left.2 fun i (hi : k i ≤ m) (hi' : m < k i) ↦ (not_lt.2 hi) hi'
  have hu : Set.univ ⊆ {i | k i ≤ m} ∪ {i | m < k i} := fun i _ ↦ le_or_gt (k i) m
  have h : (pi {i | m < k i} fun _ ↦ ⊥ : Submodule (B ⧸ Ideal.span {ξ}) (n → B ⧸ Ideal.span {ξ})) =
      ⨅ i ∈ {i | m < k i}, LinearMap.ker
        (LinearMap.proj i : (n → B ⧸ Ideal.span {ξ}) →ₗ[B ⧸ Ideal.span {ξ}] _) := by
    ext; simp
  rw [latticeFiltration_map_diagonalLattice_eq hinj, LinearEquiv.finrank_map_eq, h,
    (LinearMap.iInfKerProjEquiv (B ⧸ Ideal.span {ξ}) (fun _ ↦ B ⧸ Ideal.span {ξ}) hd
    hu).finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl)

/-- **The filtration of a translated diagonal lattice is a direct summand.** If `B → K` is
injective, `Fil^m (g μ(ξ) Bⁿ)` has a complement in `(B ⧸ ξ)ⁿ`, namely the image under the
reduction of `g` modulo `ξ` of the coordinate subspace spanned by the `e_i` with `m < k i`. -/
theorem exists_isCompl_latticeFiltration_map_diagonalLattice
    (hinj : Function.Injective (algebraMap B K)) (hξ : IsUnit (algebraMap B K ξ)) (g : GL n B)
    (k : n → ℤ) (m : ℤ) :
    ∃ C : Submodule (B ⧸ Ideal.span {ξ}) (n → B ⧸ Ideal.span {ξ}),
      IsCompl (((diagonalLattice k hξ).map
        (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B)).latticeFiltration
          hξ m) C := by
  classical
  rw [latticeFiltration_map_diagonalLattice_eq hinj]
  refine ⟨_, isCompl_map (reductionEquiv ξ g) (q := pi {i | m < k i}ᶜ fun _ ↦ ⊥) ?_⟩
  -- The vectors vanishing on `J` and those vanishing off `J` are complementary.
  refine ⟨?_, codisjoint_iff.2 (eq_top_iff.2 fun v _ ↦ ?_)⟩
  · simpa using disjoint_pi_compl_bot_of_disjoint (R := B ⧸ Ideal.span {ξ})
      (M := fun _ : n ↦ B ⧸ Ideal.span {ξ}) (disjoint_compl_left (a := {i | m < k i}))
  · refine mem_sup.2 ⟨fun i ↦ if m < k i then 0 else v i, mem_pi.2 fun i hi ↦ ?_,
      fun i ↦ if m < k i then v i else 0, mem_pi.2 fun i hi ↦ ?_, funext fun i ↦ ?_⟩
    · simp [show m < k i from hi]
    · simp [show ¬m < k i from hi]
    · by_cases hi : m < k i <;> simp [hi]

/-- **Base change of the filtration.** For a ring map `φ : B → B'` and `g ∈ GLₙ(B)`, the
filtration of the base-changed lattice `φ(g) μ(φ ξ) B'ⁿ` is the `B' ⧸ φ ξ`-span of the image of
the filtration of `g μ(ξ) Bⁿ` under reduction of `φ`, provided `B → K` and `B' → K'` are
injective. -/
theorem latticeFiltration_map_diagonalLattice_eq_span_image {B' K' : Type*} [CommRing B']
    [CommRing K'] [Algebra B' K'] (φ : B →+* B') (hinj : Function.Injective (algebraMap B K))
    (hinj' : Function.Injective (algebraMap B' K')) (hξ : IsUnit (algebraMap B K ξ))
    (hξ' : IsUnit (algebraMap B' K' (φ ξ))) (g : GL n B) (k : n → ℤ) (m : ℤ) :
    ((diagonalLattice k hξ').map
        (((GeneralLinearGroup.map φ g : Matrix n n B').map
          (algebraMap B' K')).mulVecLin.restrictScalars B')).latticeFiltration hξ' m =
      span (B' ⧸ Ideal.span {φ ξ})
        ((fun (y : n → B ⧸ Ideal.span {ξ}) i ↦ Ideal.quotientMap (Ideal.span {φ ξ}) φ
            (Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.mem_span_singleton_self _)) (y i)) ''
          ((diagonalLattice k hξ).map
            (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B)
              ).latticeFiltration hξ m) := by
  classical
  set φbar := Ideal.quotientMap (Ideal.span {φ ξ}) φ
    (Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.mem_span_singleton_self _))
  set F : (n → B ⧸ Ideal.span {ξ}) → n → B' ⧸ Ideal.span {φ ξ} := fun v i ↦ φbar (v i)
  -- Reduction of `φ` intertwines the two reductions of `g`.
  have hcomm : F ∘ reductionEquiv ξ g = reductionEquiv (φ ξ) (.map φ g) ∘ F := by
    ext v i
    simp only [F, Function.comp_apply, reductionEquiv, LinearEquiv.coe_ofLinearMap,
      mulVecLin_apply]
    rw [RingHom.map_mulVec]
    congr 2
  rw [latticeFiltration_map_diagonalLattice_eq hinj, latticeFiltration_map_diagonalLattice_eq hinj',
    map_coe, ← Set.image_comp, LinearEquiv.coe_coe, hcomm, Set.image_comp,
    ← LinearEquiv.coe_coe, span_image]
  congr 1
  -- It remains to see that the coordinate subspace over `B' ⧸ φ ξ` is spanned by the image of
  -- the one over `B ⧸ ξ`: both are spanned by the `e_i` with `k i ≤ m`.
  apply le_antisymm
  · intro w hw
    rw [pi_eq_sum_univ' w]
    refine sum_mem fun i _ ↦ ?_
    by_cases hi : m < k i
    · simp [(mem_bot _).1 ((mem_pi.1 hw) i hi)]
    · refine smul_mem _ _ (subset_span ⟨Pi.single i 1, mem_pi.2 fun j hj ↦ ?_, ?_⟩)
      · rw [mem_bot, Pi.single_apply, ite_eq_right (by rintro rfl; exact hi hj)]
      · ext j
        by_cases hj : j = i
        · subst hj; simp [F]
        · simp [F, hj]
  · rw [span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact mem_pi.2 fun i hi ↦ by simp [F, (mem_bot _).1 ((mem_pi.1 hv) i hi)]

end Submodule
