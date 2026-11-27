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
    have hlast : (A ^ m) v ∈ W := hmem
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
theorem levelt_rigidity_field (A B : Module.End K V)
    (hcop : IsCoprime A.charpoly B.charpoly) (hrank : finrank K (A - B).range ≤ 1)
    {d : ℕ} (hd : finrank K V = d) :
    ∃ b : Basis (Fin d) K V,
      A.toMatrix b b = Matrix.reindex
        (finCongr (A.charpoly_natDegree.trans hd)) (finCongr (A.charpoly_natDegree.trans hd))
        A.charpoly.companion ∧
      B.toMatrix b b = Matrix.reindex
        (finCongr (B.charpoly_natDegree.trans hd)) (finCongr (B.charpoly_natDegree.trans hd))
        B.charpoly.companion := by
  obtain ⟨b, hb⟩ := A.exists_basis_shift_of_isCoprime_charpoly_of_finrank_range_sub_le_one
    B hcop hrank hd
  exact ⟨b, A.toMatrix_eq_companion_of_basis_shift b _ (fun i hi ↦ (hb i hi).1),
    B.toMatrix_eq_companion_of_basis_shift b _ (fun i hi ↦ (hb i hi).2)⟩

/-- Every endomorphism commuting with both members of a pair as in Levelt's theorem
is scalar. In particular an invertible intertwiner between two such pairs is unique up to
a nonzero scalar. -/
theorem exists_eq_smul_id_of_commute_of_isCoprime_charpoly_of_rank_sub_le_one
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
    have h := congrArg Subtype.val (DFunLike.congr_fun ha ⟨x, hx⟩)
    exact h
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
    (L : Type*) [Field L] [Algebra K L] (W : Submodule L (Fin d → L)) :
    let A := (Matrix.reindex (finCongr hpdeg) (finCongr hpdeg) p.companion).map (algebraMap K L)
    let B := (Matrix.reindex (finCongr hqdeg) (finCongr hqdeg) q.companion).map (algebraMap K L)
    W ≤ W.comap A.toLin' → W ≤ W.comap B.toLin' → W = ⊥ ∨ W = ⊤ := by
  intro A B hA hB
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
theorem levelt_rigidity_field (A B : Matrix (Fin d) (Fin d) K)
    (hcop : IsCoprime A.charpoly B.charpoly) (hrank : Matrix.rank (A - B) ≤ 1) :
    ∃ c : GL (Fin d) K,
      A = (↑c : Matrix (Fin d) (Fin d) K) *
        Matrix.reindex (finCongr (by simp : A.charpoly.natDegree = d))
          (finCongr (by simp : A.charpoly.natDegree = d)) A.charpoly.companion *
        (↑c⁻¹ : Matrix (Fin d) (Fin d) K) ∧
      B = (↑c : Matrix (Fin d) (Fin d) K) *
        Matrix.reindex (finCongr (by simp : B.charpoly.natDegree = d))
          (finCongr (by simp : B.charpoly.natDegree = d)) B.charpoly.companion *
        (↑c⁻¹ : Matrix (Fin d) (Fin d) K) := by
  let standard := Pi.basisFun K (Fin d)
  have hr : finrank K (A.toLin' - B.toLin').range ≤ 1 := by
    rwa [← map_sub, Matrix.toLin'_apply', Matrix.finrank_range_mulVecLin]
  obtain ⟨b, hA, hB⟩ := A.toLin'.levelt_rigidity_field B.toLin'
    (by simpa only [Matrix.charpoly_toLin'] using hcop) hr (d := d) (by simp)
  let := standard.invertibleToMatrix b
  let c : GL (Fin d) K := unitOfInvertible (standard.toMatrix b)
  -- The index types of the companions depend on their characteristic polynomials.
  have transport {p q : K[X]} (hp : p.natDegree = d) (hq : q.natDegree = d) (h : p = q) :
      reindex (finCongr hp) (finCongr hp) p.companion =
        reindex (finCongr hq) (finCongr hq) q.companion := by
    subst q
    rfl
  have conjugate (M : Matrix (Fin d) (Fin d) K) (hm : M.toLin'.charpoly.natDegree = d)
      (hM : M.toLin'.toMatrix b b = reindex (finCongr hm) (finCongr hm)
        M.toLin'.charpoly.companion) :
      M = (↑c : Matrix (Fin d) (Fin d) K) *
        reindex (finCongr (by simp : M.charpoly.natDegree = d))
          (finCongr (by simp : M.charpoly.natDegree = d)) M.charpoly.companion *
        (↑c⁻¹ : Matrix (Fin d) (Fin d) K) := by
    rw [← transport hm _ (Matrix.charpoly_toLin' M), ← hM]
    -- The inverse of the change-of-basis matrix is the reverse change of basis.
    exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      standard b standard b M.toLin').trans (by simp [standard]) |>.symm
  exact ⟨c, conjugate A _ hA, conjugate B _ hB⟩

namespace GeneralLinearGroup

/-- **Levelt's companion form for a triple.** For a triple with product one in the order
`gInf * gOne * gZero`, coprime characteristic polynomials for `gInf` and `gZero⁻¹`, and
middle displacement of rank at most one, one change of basis puts the two endpoint
operators in companion form and identifies the middle operator with their quotient. -/
theorem levelt_rigidity_field (gInf gOne gZero : GL (Fin d) K)
    (hprod : gInf * gOne * gZero = 1)
    (hcop : IsCoprime gInf.val.charpoly gZero⁻¹.val.charpoly)
    (hrank : Matrix.rank (gOne.val - 1) ≤ 1) :
    ∃ c : GL (Fin d) K,
      let p := gInf.val.charpoly
      let q := gZero⁻¹.val.charpoly
      let Cp := Matrix.reindex (finCongr (by simp [p] : p.natDegree = d))
        (finCongr (by simp [p] : p.natDegree = d)) p.companion
      let Cq := Matrix.reindex (finCongr (by simp [q] : q.natDegree = d))
        (finCongr (by simp [q] : q.natDegree = d)) q.companion
      (c⁻¹ * gInf * c).val = Cp ∧
      (c⁻¹ * gZero⁻¹ * c).val = Cq ∧
      (c⁻¹ * gOne * c).val = Cp⁻¹ * Cq := by
  have hmul : gInf * gOne = gZero⁻¹ := by
    calc
      gInf * gOne = (gInf * gOne * gZero) * gZero⁻¹ := by group
      _ = gZero⁻¹ := by rw [hprod, one_mul]
  have hr : Matrix.rank (gZero⁻¹.val - gInf.val) ≤ 1 := by
    calc
      _ = Matrix.rank (gInf.val * (gOne.val - 1)) := by
        rw [mul_sub, Matrix.mul_one, ← coe_mul, hmul]
      _ ≤ 1 := (Matrix.rank_mul_le_right _ _).trans hrank
  obtain ⟨c, hq, hp⟩ := Matrix.levelt_rigidity_field gZero⁻¹.val gInf.val hcop.symm hr
  refine ⟨c, ?_⟩
  dsimp only
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

/-- Two changes of basis that give the same simultaneous conjugates of a pair as in Levelt's
theorem differ by a nonzero scalar. -/
theorem exists_smul_eq_of_levelt_conj_eq (A B c c' : GL (Fin d) K)
    (hcop : IsCoprime A.val.charpoly B.val.charpoly) (hrank : Matrix.rank (A.val - B.val) ≤ 1)
    (hA : c⁻¹ * A * c = c'⁻¹ * A * c') (hB : c⁻¹ * B * c = c'⁻¹ * B * c') :
    ∃ a : Kˣ, c'.val = (a : K) • c.val := by
  let T := c' * c⁻¹
  have commute (M : GL (Fin d) K) (hM : c⁻¹ * M * c = c'⁻¹ * M * c') :
      Commute T.val.toLin' M.val.toLin' := by
    have h : Commute T M := calc
      T * M = c' * (c⁻¹ * M * c) * c⁻¹ := by dsimp [T]; group
      _ = c' * (c'⁻¹ * M * c') * c⁻¹ := by rw [hM]
      _ = M * T := by dsimp [T]; group
    exact (h.map (Units.coeHom _)).map Matrix.toLinAlgEquiv'
  have hr : finrank K (A.val.toLin' - B.val.toLin').range ≤ 1 := by
    rwa [← map_sub, Matrix.toLin'_apply', Matrix.finrank_range_mulVecLin]
  obtain ⟨a, ha⟩ :=
    A.val.toLin'.exists_eq_smul_id_of_commute_of_isCoprime_charpoly_of_rank_sub_le_one
      B.val.toLin' T.val.toLin' (by simpa only [Matrix.charpoly_toLin'] using hcop)
      hr (commute A hA) (commute B hB)
  have hscalar : T.val = a • (1 : Matrix (Fin d) (Fin d) K) := by
    apply Matrix.toLin'.injective
    simpa only [map_smul, Matrix.toLin'_one] using ha
  by_cases hzero : a = 0
  · have hu : IsUnit (0 : Matrix (Fin d) (Fin d) K) := by
      simpa only [hscalar, hzero, zero_smul] using T.isUnit
    have := subsingleton_iff_zero_eq_one.mp (isUnit_zero_iff.mp hu)
    exact ⟨1, Subsingleton.elim _ _⟩
  refine ⟨Units.mk0 a hzero, ?_⟩
  calc
    c'.val = T.val * c.val := by rw [← coe_mul]; simp [T, mul_assoc]
    _ = a • c.val := by rw [hscalar, smul_mul_assoc, Matrix.one_mul]

end GeneralLinearGroup

end Matrix
