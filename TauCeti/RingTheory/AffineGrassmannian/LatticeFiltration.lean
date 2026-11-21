/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Pi
import TauCeti.Algebra.Algebra.IsUnit

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
* `Submodule.latticeFiltration_map_diagonalLattice_eq`: `Fil^m (g μ(ξ) Bⁿ)` is the image under
  `g mod ξ` of the coordinate subspace spanned by the `e_i` with `k_i ≤ m`.
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
    rw [smul_comm b]
    exact congrArg _ (funext fun i ↦ (map_mul (algebraMap B K) b (x i)).trans
      (Algebra.smul_def _ _).symm)

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

/-- **The filtration is increasing**: `Fil^m Λ ⊆ Fil^{m'} Λ` for `m ≤ m'`. -/
theorem monotone_latticeFiltration (Λ : Submodule B (n → K)) (hξ : IsUnit (algebraMap B K ξ)) :
    Monotone (Λ.latticeFiltration hξ) := by
  rintro m m' h _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  convert Λ.smul_mem (ξ ^ (m' - m).toNat) hx using 1
  rw [Units.smul_def, Units.smul_def, hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le h, mul_smul,
    algebraMap_smul, smul_comm]

open Matrix

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
    · -- `ξ^m g⁻¹ x = g⁻¹ (ξ^m x) = g⁻¹ g l = l`.
      have hinv : (fun i ↦ algebraMap B K (((g : Matrix n n B)⁻¹ *ᵥ x) i)) =
          (g : Matrix n n B)⁻¹.map (algebraMap B K) *ᵥ fun i ↦ algebraMap B K (x i) :=
        funext (RingHom.map_mulVec _ _ _)
      simpa [hinv, ← mulVec_smul, ← hxl, mulVec_mulVec,
        GeneralLinearGroup.coe_map_inv_mul_map] using hl
    · ext i
      simp [RingHom.map_mulVec, mulVec_mulVec, GeneralLinearGroup.coe_map_mul_map_inv]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g *ᵥ x, ⟨_, hx, ?_⟩, funext (RingHom.map_mulVec _ _ _)⟩
    rw [LinearMap.restrictScalars_apply, mulVecLin_apply, mulVec_smul]
    exact congrArg _ (funext (RingHom.map_mulVec _ _ _)).symm

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
      simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul,
        hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le hi.le, mul_assoc] at hb
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
        simp [Units.smul_def, hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le (not_lt.1 h),
          mul_assoc]
    · dsimp only
      split_ifs with h
      · simp [hy i h]
      · exact hx i

variable [Fintype n] [DecidableEq n]

/-- **The filtration of a translated diagonal lattice.** If `B → K` is injective, the filtration
of `g μ(ξ) Bⁿ` is the image of the coordinate subspace of the `e_i` with `k i ≤ m` under the
reduction of `g` modulo `ξ`, written as `mulVecLin` of the reduced matrix as in
`latticeFiltration_map_mulVecLin`. -/
theorem latticeFiltration_map_diagonalLattice_eq
    (hinj : Function.Injective (algebraMap B K)) (hξ : IsUnit (algebraMap B K ξ)) (g : GL n B)
    (k : n → ℤ) (m : ℤ) :
    ((diagonalLattice k hξ).map
        (((g : Matrix n n B).map (algebraMap B K)).mulVecLin.restrictScalars B)).latticeFiltration
        hξ m = (pi {i | m < k i} fun _ ↦ ⊥).map
          ((g : Matrix n n B).map (Ideal.Quotient.mk (Ideal.span {ξ}))).mulVecLin := by
  rw [latticeFiltration_map_mulVecLin, latticeFiltration_diagonalLattice hinj]

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
  -- The reduced matrix is invertible: `mulVecLin` of it is Mathlib's `toLin` of the reduction.
  rw [latticeFiltration_map_diagonalLattice_eq hinj,
    ← GeneralLinearGroup.val_map_apply, ← GeneralLinearGroup.coe_toLin,
    ← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap, LinearEquiv.finrank_map_eq, h,
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
  rw [latticeFiltration_map_diagonalLattice_eq hinj,
    ← GeneralLinearGroup.val_map_apply, ← GeneralLinearGroup.coe_toLin,
    ← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  exact ⟨_, isCompl_map _ (isCompl_pi_bot_compl _)⟩

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
  set φbar := Ideal.quotientMap (Ideal.span {φ ξ}) φ
    (Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.mem_span_singleton_self _))
  set F : (n → B ⧸ Ideal.span {ξ}) → n → B' ⧸ Ideal.span {φ ξ} := fun v i ↦ φbar (v i)
  -- Reduction of `φ` intertwines the two reductions of `g`.
  have hcomm (v : n → B ⧸ Ideal.span {ξ}) :
      F (((g : Matrix n n B).map (Ideal.Quotient.mk (Ideal.span {ξ}))).mulVecLin v) =
        (((GeneralLinearGroup.map φ g : Matrix n n B').map
          (Ideal.Quotient.mk (Ideal.span {φ ξ}))).mulVecLin) (F v) := by
    -- Entrywise, reducing `g` modulo `ξ` and then applying `φbar` is reducing `φ g` modulo `φ ξ`.
    have hmat : ((g : Matrix n n B).map (Ideal.Quotient.mk (Ideal.span {ξ}))).map φbar =
        (GeneralLinearGroup.map φ g : Matrix n n B').map
          (Ideal.Quotient.mk (Ideal.span {φ ξ})) := by
      ext a b
      simp only [map_apply, GeneralLinearGroup.map_apply, φbar, Ideal.quotientMap_mk]
    ext i
    simp only [F, mulVecLin_apply, RingHom.map_mulVec, hmat, Function.comp_def]
  rw [latticeFiltration_map_diagonalLattice_eq hinj, latticeFiltration_map_diagonalLattice_eq hinj',
    map_coe, Set.image_comm hcomm, span_image, span_image_map_pi_bot]

end Submodule
