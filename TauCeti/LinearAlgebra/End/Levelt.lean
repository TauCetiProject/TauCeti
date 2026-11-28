/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import TauCeti.LinearAlgebra.Charpoly.Quotient
import TauCeti.LinearAlgebra.LinearMap.Range
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.TensorProduct.Range

/-!
# Levelt's theorem for pairs of endomorphisms

Two endomorphisms with coprime characteristic polynomials whose difference has rank at most one
have no common proper nonzero invariant subspace. They can be put in companion form in the
same basis. These statements use only field operations and apply to hypergeometric monodromy
over finite fields as well as over the complex numbers. A simultaneous change of basis is
unique up to scalar, and the invariant-subspace statement holds after every field extension.

The companion matrices are `Polynomial.companion`. The proof uses the factorization of the
characteristic polynomial along an invariant subspace and its quotient.

## References

* F. Beukers and G. Heckman, *Monodromy for the hypergeometric function* ₙFₙ₋₁,
  Invent. Math. 95 (1989), 325–354, Proposition 3.3 and Theorem 3.5.
-/

public section

open Module Polynomial
open scoped TensorProduct

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A pair with coprime characteristic polynomials and difference of rank at most one has
no common proper nonzero invariant subspace. -/
theorem eq_bot_or_eq_top_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    (A B : Module.End K V) (hcop : IsCoprime A.charpoly B.charpoly)
    (hrank : finrank K (A - B).range ≤ 1) (W : Submodule K V)
    (hA : W ≤ W.comap A) (hB : W ≤ W.comap B) : W = ⊥ ∨ W = ⊤ := by
  have hdiff : W ≤ W.comap (A - B) := fun x hx ↦ W.sub_mem (hA hx) (hB hx)
  -- The difference vanishes on the subspace or its entire image lies in the subspace.
  by_cases hker : W ≤ (A - B).ker
  · left
    have heq : A.restrict hA = B.restrict hB := by
      ext ⟨x, hx⟩
      exact sub_eq_zero.mp (hker hx)
    have hu : IsUnit (A.restrict hA).charpoly := hcop.isUnit_of_dvd'
      ⟨_, A.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W hA⟩
      ⟨_, by
        rw [heq]
        exact B.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W hB⟩
    exact Submodule.finrank_eq_zero.mp (by
      simpa only [charpoly_natDegree] using natDegree_eq_zero_of_isUnit hu)
  · right
    have hm : W.map (A - B) ≠ ⊥ := by
      rw [Ne, ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot]
      exact hker
    have hr : (A - B).range ≤ W := by
      have hle : W.map (A - B) ≤ (A - B).range := LinearMap.map_le_range
      have hpos := (Module.finrank_pos_iff (R := K)).mpr (Submodule.nontrivial_iff_ne_bot.mpr hm)
      rw [← Submodule.eq_of_le_of_finrank_le hle (hrank.trans (Nat.succ_le_of_lt hpos))]
      exact Submodule.map_le_iff_le_comap.mpr hdiff
    have heq : W.mapQ W A hA = W.mapQ W B hB := by
      apply (LinearMap.cancel_right W.mkQ_surjective).mp
      rw [W.mapQ_mkQ, W.mapQ_mkQ]
      ext x
      exact sub_eq_zero.mp (by
        rw [comp_apply, comp_apply, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hr (LinearMap.mem_range_self (A - B) x))
    have hu : IsUnit (W.mapQ W A hA).charpoly := hcop.isUnit_of_dvd'
      ⟨_, (A.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W hA).trans (mul_comm _ _)⟩
      ⟨_, by
        rw [heq, mul_comm]
        exact B.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W hB⟩
    have hdim : finrank K (V ⧸ W) = 0 := by
      simpa only [charpoly_natDegree] using natDegree_eq_zero_of_isUnit hu
    have := W.finrank_quotient_add_finrank
    exact Submodule.eq_of_le_of_finrank_le le_top (by simpa [hdim] using this.ge)

/-- A vector subspace preserved by the scalar extensions of a pair as in Levelt's theorem
is either zero or the whole space. -/
theorem eq_bot_or_eq_top_baseChange_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    (A B : Module.End K V) (hcop : IsCoprime A.charpoly B.charpoly)
    (hrank : finrank K (A - B).range ≤ 1) (L : Type*) [Field L] [Algebra K L]
    (W : Submodule L (L ⊗[K] V))
    (hA : W ≤ W.comap (A.baseChange L)) (hB : W ≤ W.comap (B.baseChange L)) :
    W = ⊥ ∨ W = ⊤ := by
  apply (A.baseChange L).eq_bot_or_eq_top_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    (B.baseChange L) _ _ W hA hB
  · simpa only [LinearMap.charpoly_baseChange, Polynomial.coe_mapRingHom] using
      hcop.map (Polynomial.mapRingHom (algebraMap K L))
  · rw [← LinearMap.baseChange_sub,
      (A - B).finrank_range_baseChange_of_isComplemented (A - B).range.exists_isCompl L]
    exact hrank

private theorem exists_eq_on_initial_powers (A B : Module.End K V) {d : ℕ}
    (hd : finrank K V = d) (hpos : 0 < d) (hrank : finrank K (A - B).range ≤ 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ i : Fin (d - 1), A ((A ^ (i : ℕ)) v) = B ((A ^ (i : ℕ)) v) := by
  -- Each test has rank at most one, and there are fewer tests than the dimension of V.
  let tests : V →ₗ[K] Fin (d - 1) → (A - B).range :=
    LinearMap.pi fun i : Fin (d - 1) ↦ (A - B).rangeRestrict.comp (A ^ (i : ℕ))
  have hdim : finrank K (Fin (d - 1) → (A - B).range) < finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hd]
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ hrank) ?_
    simpa using Nat.sub_lt hpos (by decide : 0 < 1)
  obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := tests) hdim)
  refine ⟨v, hv₀, fun i ↦ sub_eq_zero.mp ?_⟩
  have hi := congrArg (fun f : Fin (d - 1) → (A - B).range ↦ (f i : V))
    (LinearMap.mem_ker.mp hv)
  simpa [tests] using hi

private theorem linearIndependent_powers_of_eq_on_initial_powers (A B : Module.End K V)
    (hcop : IsCoprime A.charpoly B.charpoly) (hrank : finrank K (A - B).range ≤ 1)
    {v : V} (hv : v ≠ 0) {d : ℕ} (hd : finrank K V = d)
    (hAB : ∀ i : Fin (d - 1), A ((A ^ (i : ℕ)) v) = B ((A ^ (i : ℕ)) v)) :
    LinearIndependent K (fun i : Fin d ↦ (A ^ (i : ℕ)) v) := by
  suffices ∀ m ≤ d, LinearIndependent K (fun i : Fin m ↦ (A ^ (i : ℕ)) v) from this d le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    exact linearIndependent_empty_type
  | succ m ih =>
    intro hm
    rw [linearIndependent_finSucc']
    refine ⟨ih (by omega), ?_⟩
    intro hmem
    -- A first dependence would make the span of the earlier iterates invariant under both maps.
    let W := Submodule.span K (Set.range fun i : Fin m ↦ (A ^ (i : ℕ)) v)
    have hlast : (A ^ m) v ∈ W := by
      simpa only [Fin.init_def, Fin.val_last, Fin.val_castSucc] using hmem
    have hA : W ≤ W.comap A := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [← mul_apply_eq_comp, ← pow_succ']
      by_cases hi : (i : ℕ) + 1 < m
      · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, hi⟩, rfl⟩
      · have hsucc : (i : ℕ) + 1 = m := by omega
        simpa only [hsucc] using hlast
    have hB : W ≤ W.comap B := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [← hAB ⟨i, by omega⟩]
      exact hA (Submodule.subset_span ⟨i, rfl⟩)
    have hvW : v ∈ W := by
      by_cases hm₀ : m = 0
      · simpa [hm₀] using hlast
      · simpa using (Submodule.subset_span
          (s := Set.range fun i : Fin m ↦ (A ^ (i : ℕ)) v)
          ⟨⟨0, Nat.pos_of_ne_zero hm₀⟩, rfl⟩ :
          (A ^ (0 : ℕ)) v ∈ W)
    rcases A.eq_bot_or_eq_top_of_isCoprime_charpoly_of_finrank_range_sub_le_one
      B hcop hrank W hA hB with hW | hW
    · exact hv (by simpa [hW] using hvW)
    · have := finrank_le_of_span_eq_top hW
      simp only [hd, Fintype.card_fin] at this
      omega

/-- Levelt's common cyclic basis for a pair with coprime characteristic polynomials whose
difference has rank at most one. Both endomorphisms shift each basis vector to its successor,
except the last. -/
private theorem exists_basis_shift_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    (A B : Module.End K V) (hcop : IsCoprime A.charpoly B.charpoly)
    (hrank : finrank K (A - B).range ≤ 1) {d : ℕ} (hd : finrank K V = d) :
    ∃ b : Basis (Fin d) K V, ∀ i : Fin d, ∀ hi : (i : ℕ) + 1 < d,
      A (b i) = b ⟨(i : ℕ) + 1, hi⟩ ∧ B (b i) = b ⟨(i : ℕ) + 1, hi⟩ := by
  obtain rfl | hpos := d.eq_zero_or_pos
  · exact ⟨basisOfFinrankZero hd, fun i ↦ i.elim0⟩
  obtain ⟨v, hv, hAB⟩ := exists_eq_on_initial_powers A B hd hpos hrank
  have hli := linearIndependent_powers_of_eq_on_initial_powers A B hcop hrank hv hd hAB
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simpa using hd.symm)
  refine ⟨b, fun i hi ↦ ?_⟩
  have hb : ⇑b = fun j : Fin d ↦ (A ^ (j : ℕ)) v :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  simp only [hb]
  have hshift : A ((A ^ (i : ℕ)) v) = (A ^ ((i : ℕ) + 1)) v := by
    rw [pow_succ', mul_apply_eq_comp]
  exact ⟨hshift, (hAB ⟨i, by omega⟩).symm.trans hshift⟩

/-- **Levelt's simultaneous companion form.** A pair of endomorphisms with coprime
characteristic polynomials and difference of rank at most one has a common basis in which
each is the companion matrix of its characteristic polynomial. -/
theorem levelt_rigidity_field (A B : Module.End K V) (p q : K[X])
    (hp : A.charpoly = p) (hq : B.charpoly = q)
    (hcop : IsCoprime p q) (hrank : finrank K (A - B).range ≤ 1)
    {d : ℕ} (hpd : p.natDegree = d) (hqd : q.natDegree = d) :
    ∃ b : Basis (Fin d) K V,
      A.toMatrix b b = Matrix.reindex (finCongr hpd) (finCongr hpd) p.companion ∧
      B.toMatrix b b = Matrix.reindex (finCongr hqd) (finCongr hqd) q.companion := by
  have hd : finrank K V = d := A.charpoly_natDegree.symm.trans (hp ▸ hpd)
  obtain ⟨b, hb⟩ := A.exists_basis_shift_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    B (by rwa [hp, hq]) hrank hd
  exact ⟨b, (A.toMatrix_eq_companion_of_basis_shift b (A.charpoly_natDegree.trans hd)
    (fun i hi ↦ (hb i hi).1)).trans
    (reindex_companion_eq _ hpd hp),
    (B.toMatrix_eq_companion_of_basis_shift b (B.charpoly_natDegree.trans hd)
      (fun i hi ↦ (hb i hi).2)).trans
      (reindex_companion_eq _ hqd hq)⟩

/-- Every endomorphism commuting with both members of a pair as in Levelt's theorem
is scalar. In particular an invertible intertwiner between two such pairs is unique up to
a nonzero scalar. -/
theorem exists_eq_smul_id_of_isCoprime_charpoly_of_finrank_range_sub_le_one_of_commute
    (A B T : Module.End K V) (hcop : IsCoprime A.charpoly B.charpoly)
    (hrank : finrank K (A - B).range ≤ 1) (hTA : Commute T A) (hTB : Commute T B) :
    ∃ a : K, T = a • LinearMap.id := by
  by_cases hzero : (A - B).range = ⊥
  · have hAB := sub_eq_zero.mp (LinearMap.range_eq_bot.mp hzero)
    have hu := hcop.isUnit_of_dvd' (dvd_refl A.charpoly) (by rw [← hAB])
    have hdim : finrank K V = 0 := by
      simpa only [charpoly_natDegree] using natDegree_eq_zero_of_isUnit hu
    have := Module.finrank_zero_iff.mp hdim
    exact ⟨0, Subsingleton.elim _ _⟩
  have hr : finrank K (A - B).range = 1 :=
    le_antisymm hrank (Nat.succ_le_of_lt
      (Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hzero)))
  have hTD : Commute T (A - B) := hTA.sub_right hTB
  have hstable : (A - B).range ≤ (A - B).range.comap T :=
    LinearMap.range_le_comap_range_of_comp_eq hTD.eq
  obtain ⟨a, ha, -⟩ := (T.restrict hstable).existsUnique_eq_smul_id_of_finrank_eq_one hr
  let W := Module.End.eigenspace T a
  have hle : (A - B).range ≤ W := by
    intro x hx
    apply Module.End.mem_eigenspace_iff.mpr
    simpa only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_smul_of_tower] using
      congrArg Subtype.val (DFunLike.congr_fun ha ⟨x, hx⟩)
  have hW (S : Module.End K V) (hTS : Commute T S) : W ≤ W.comap S :=
    fun _ hx ↦ Module.End.mapsTo_genEigenspace_of_comm hTS a 1 hx
  have htop := (A.eq_bot_or_eq_top_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    B hcop hrank W (hW A hTA) (hW B hTB)).resolve_left fun h ↦
      hzero (le_bot_iff.mp (h ▸ hle))
  refine ⟨a, LinearMap.ext fun x ↦ ?_⟩
  exact Module.End.mem_eigenspace_iff.mp (htop ▸ Submodule.mem_top : x ∈ W)

end LinearMap

namespace Polynomial

/-- **Levelt's irreducibility theorem.** Over any field extension, the companion matrices
of two coprime monic polynomials of the same degree have no common proper nonzero
invariant subspace. -/
theorem levelt_irreducible_field {K : Type*} [Field K] (p q : K[X])
    (hp : p.Monic) (hq : q.Monic) (hcop : IsCoprime p q) {d : ℕ}
    (hpdeg : p.natDegree = d) (hqdeg : q.natDegree = d)
    (L : Type*) [Field L] [Algebra K L] (W : Submodule L (Fin d → L))
    (hA : W ≤ W.comap
      ((Matrix.reindex (finCongr hpdeg) (finCongr hpdeg) p.companion).map
        (algebraMap K L)).toLin')
    (hB : W ≤ W.comap
      ((Matrix.reindex (finCongr hqdeg) (finCongr hqdeg) q.companion).map
        (algebraMap K L)).toLin') : W = ⊥ ∨ W = ⊤ := by
  let A := (Matrix.reindex (finCongr hpdeg) (finCongr hpdeg) p.companion).map (algebraMap K L)
  let B := (Matrix.reindex (finCongr hqdeg) (finCongr hqdeg) q.companion).map (algebraMap K L)
  apply A.toLin'.eq_bot_or_eq_top_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    B.toLin' _ _ W hA hB
  · simpa only [A, B, Matrix.charpoly_toLin', Matrix.charpoly_map, Matrix.charpoly_reindex,
      charpoly_companion hp, charpoly_companion hq, coe_mapRingHom] using
      hcop.map (mapRingHom (algebraMap K L))
  · rw [← map_sub, Matrix.toLin'_apply', Matrix.finrank_range_mulVecLin]
    -- The companion matrices differ only in the last column, if there is one.
    cases d with
    | zero => simp [Subsingleton.elim A B]
    | succ n =>
      apply Matrix.rank_sub_le_one_of_col_eq A B (Fin.last n)
      intro j hj
      have hj' : (j : ℕ) ≠ n := fun heq ↦
        hj (Fin.ext (by simpa only [Fin.val_last] using heq))
      funext i
      simp [A, B, Matrix.col_apply, Matrix.reindex_apply, hpdeg, hqdeg, hj']

end Polynomial

namespace Matrix

open scoped MatrixGroups

variable {K : Type*} [Field K] {d : ℕ}

/-- Two square matrices with coprime characteristic polynomials and difference of rank
at most one are simultaneously conjugate to their companion matrices. -/
theorem levelt_rigidity_field (A B : Matrix (Fin d) (Fin d) K) (p q : K[X])
    (hp : A.charpoly = p) (hq : B.charpoly = q)
    (hcop : IsCoprime p q) (hrank : Matrix.rank (A - B) ≤ 1)
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) :
    ∃ c : GL (Fin d) K,
      A = (↑c : Matrix (Fin d) (Fin d) K) *
        Matrix.reindex (finCongr hpd) (finCongr hpd) p.companion *
        (↑c⁻¹ : Matrix (Fin d) (Fin d) K) ∧
      B = (↑c : Matrix (Fin d) (Fin d) K) *
        Matrix.reindex (finCongr hqd) (finCongr hqd) q.companion *
        (↑c⁻¹ : Matrix (Fin d) (Fin d) K) := by
  let standard := Pi.basisFun K (Fin d)
  have hr : finrank K (A.toLin' - B.toLin').range ≤ 1 := by
    rwa [← map_sub, Matrix.toLin'_apply', Matrix.finrank_range_mulVecLin]
  obtain ⟨b, hA, hB⟩ := A.toLin'.levelt_rigidity_field B.toLin' p q
    ((Matrix.charpoly_toLin' A).trans hp) ((Matrix.charpoly_toLin' B).trans hq)
    hcop hr hpd hqd
  let := standard.invertibleToMatrix b
  let c : GL (Fin d) K := unitOfInvertible (standard.toMatrix b)
  have hc : (↑c : Matrix (Fin d) (Fin d) K) = standard.toMatrix b := rfl
  have hc' : (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = b.toMatrix standard := by
    apply left_inv_eq_right_inv (Units.inv_mul c)
    rw [hc, Basis.toMatrix_mul_toMatrix_flip]
  have conjugate (M C : Matrix (Fin d) (Fin d) K)
      (hM : M.toLin'.toMatrix b b = C) :
      M = (↑c : Matrix (Fin d) (Fin d) K) * C *
        (↑c⁻¹ : Matrix (Fin d) (Fin d) K) := by
    rw [hc, hc', ← hM]
    exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      standard b standard b M.toLin').trans (by simp [standard]) |>.symm
  exact ⟨c, conjugate A _ hA, conjugate B _ hB⟩

namespace GeneralLinearGroup

/-- **Levelt's companion form for a triple.** For a triple with product one in the order
`gInf * gOne * gZero`, coprime characteristic polynomials for `gInf` and `gZero⁻¹`, and
middle displacement of rank at most one, one change of basis conjugates `gInf` and
`gZero⁻¹` to the prescribed companion matrices `Cp` and `Cq`, respectively, and conjugates
`gOne` to `Cp⁻¹ * Cq`. -/
theorem levelt_rigidity_field (gInf gOne gZero : GL (Fin d) K) (p q : K[X])
    (hprod : gInf * gOne * gZero = 1)
    (hp : gInf.val.charpoly = p) (hq : gZero⁻¹.val.charpoly = q)
    (hcop : IsCoprime p q) (hrank : Matrix.rank (gOne.val - 1) ≤ 1)
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) :
    ∃ c : GL (Fin d) K,
      (c⁻¹ * gInf * c).val =
        Matrix.reindex (finCongr hpd) (finCongr hpd) p.companion ∧
      (c⁻¹ * gZero⁻¹ * c).val =
        Matrix.reindex (finCongr hqd) (finCongr hqd) q.companion ∧
      (c⁻¹ * gOne * c).val =
        (Matrix.reindex (finCongr hpd) (finCongr hpd) p.companion)⁻¹ *
          Matrix.reindex (finCongr hqd) (finCongr hqd) q.companion := by
  have hmul : gInf * gOne = gZero⁻¹ := by
    calc
      gInf * gOne = (gInf * gOne * gZero) * gZero⁻¹ := by group
      _ = gZero⁻¹ := by rw [hprod, one_mul]
  have hr : Matrix.rank (gZero⁻¹.val - gInf.val) ≤ 1 := by
    calc
      _ = Matrix.rank (gInf.val * (gOne.val - 1)) := by
        rw [mul_sub, Matrix.mul_one, ← coe_mul, hmul]
      _ ≤ 1 := (Matrix.rank_mul_le_right _ _).trans hrank
  obtain ⟨c, hq, hp⟩ := Matrix.levelt_rigidity_field gZero⁻¹.val gInf.val q p
    hq hp hcop.symm hr hqd hpd
  refine ⟨c, ?_⟩
  have conjugate (g : GL (Fin d) K) (C : Matrix (Fin d) (Fin d) K)
      (hg : g.val = c.val * C * c⁻¹.val) : (c⁻¹ * g * c).val = C := by
    rw [coe_mul, coe_mul, hg]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have hp' := conjugate _ _ hp
  have hq' := conjugate _ _ hq
  refine ⟨hp', hq', ?_⟩
  rw [← hp', ← hq', ← coe_inv, ← coe_mul]
  congr 1
  calc
    c⁻¹ * gOne * c = (c⁻¹ * gInf * c)⁻¹ * (c⁻¹ * (gInf * gOne) * c) := by group
    _ = _ := by rw [hmul]

end GeneralLinearGroup

/-- Two changes of basis that give the same simultaneous conjugates of a pair as in Levelt's
theorem differ by a nonzero scalar. -/
theorem exists_eq_smul_of_levelt_conj_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (c c' : GL n K) (hcop : IsCoprime A.charpoly B.charpoly)
    (hrank : Matrix.rank (A - B) ≤ 1)
    (hA : c⁻¹.val * A * c.val = c'⁻¹.val * A * c'.val)
    (hB : c⁻¹.val * B * c.val = c'⁻¹.val * B * c'.val) :
    ∃ a : Kˣ, c'.val = (a : K) • c.val := by
  let T := c' * c⁻¹
  have commute (M : Matrix n n K)
      (hM : c⁻¹.val * M * c.val = c'⁻¹.val * M * c'.val) :
      Commute T.val.toLin' M.toLin' := by
    have h : Commute T.val M := by
      calc
        T.val * M = c'.val * (c⁻¹.val * M * c.val) * c⁻¹.val := by
          simp [T, Matrix.mul_assoc]
        _ = c'.val * (c'⁻¹.val * M * c'.val) * c⁻¹.val := by rw [hM]
        _ = M * T.val := by
          simp [T, Matrix.mul_assoc]
    exact h.map Matrix.toLinAlgEquiv'
  have hr : finrank K (A.toLin' - B.toLin').range ≤ 1 := by
    rwa [← map_sub, Matrix.toLin'_apply', Matrix.finrank_range_mulVecLin]
  obtain ⟨a, ha⟩ :=
    A.toLin'.exists_eq_smul_id_of_isCoprime_charpoly_of_finrank_range_sub_le_one_of_commute
      B.toLin' T.val.toLin' (by simpa only [Matrix.charpoly_toLin'] using hcop)
      hr (commute A hA) (commute B hB)
  have hscalar : T.val = a • (1 : Matrix n n K) := by
    apply Matrix.toLin'.injective
    simpa only [map_smul, Matrix.toLin'_one] using ha
  by_cases hzero : a = 0
  · have hu : IsUnit (0 : Matrix n n K) := by
      simpa only [hscalar, hzero, zero_smul] using T.isUnit
    have := subsingleton_iff_zero_eq_one.mp (isUnit_zero_iff.mp hu)
    exact ⟨1, Subsingleton.elim _ _⟩
  refine ⟨Units.mk0 a hzero, ?_⟩
  calc
    c'.val = T.val * c.val := by rw [← GeneralLinearGroup.coe_mul]; simp [T, mul_assoc]
    _ = a • c.val := by rw [hscalar, smul_mul_assoc, Matrix.one_mul]

end Matrix
