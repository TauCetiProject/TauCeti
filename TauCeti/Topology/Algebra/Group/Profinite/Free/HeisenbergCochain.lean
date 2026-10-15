/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Graded

/-!
# Heisenberg cochains on a free pro-`p` group and the coordinates of `gr_1`

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with
canonical generators `x_i = freeProP.of i`, and let `a : F → M` and `b : F → A` be continuous
`1`-cocycles for trivial actions on `𝔽_p`-vector spaces, that is continuous homomorphisms to
elementary abelian `p`-groups, and let `h : F → P` be a Heisenberg cochain for `(a, b)`
(`TauCeti.ContCohomology.IsHeisenbergCochain`). For `𝔽_p`-coefficients `P = ZMod p` such a cochain
always exists, since `H²(F, 𝔽_p) = 0`
(`TauCeti.ContCohomology.exists_isHeisenbergCochain_of_subsingleton_H2` with
`TauCeti.freeProP.subsingleton_H2_zmod`); for a general `P` it exists whenever `H²(F, P)` vanishes,
and the results below take `h` as given. Its restriction to `λ_1(F)` is the graded restriction
`TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict`, an additive functional on
`gr_1(F) = λ_1(F) ⧸ λ_2(F)`, and this file evaluates it in the standard basis
`TauCeti.freeProP.degreeOneBasis` of `gr_1(F)`.

For `n ∈ λ_1(F)` with class `ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]` in `gr_1(F)`, where
`ξ_i ∈ gr_0(F)` is the class of `x_i`,

  `h n = Σ_i c_i • ((p choose 2) • μ (a x_i) (b x_i))
         + Σ_{i<k} a_{ik} • (μ (a x_i) (b x_k) - μ (a x_k) (b x_i))`.

When `a` and `b` are two coordinate characters `χ_i` and `χ_j` of `F` with values in `𝔽_p`, that
is `χ_i (x_k) = δ_{ik}`, the sums collapse to a single coordinate of `ρ`: `h n = a_{ij}` for
`i < j`, `h n = -a_{ji}` for `j < i`, and `h n = (p choose 2) c_i` for `i = j`. These coordinate
formulas are the `gr_1`-side input to Labute's Proposition 3: for a pro-`p` group `G = F ⧸ R`, the
transgression formula of `TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Transgression`
relates the cup product `χ_i ⌣ χ_j ∈ H²(G, 𝔽_p)` to the cocycle `-h|_R`, and combining it with
the formulas here would read that cup product off the classes of the relators in `gr_1(F)`. That
combination, for a minimal presentation, is not carried out in this file.

## Main results

* `TauCeti.ContCohomology.IsHeisenbergCochain.apply_eq_sum_repr_degreeOneBasis`: the value of a
  Heisenberg cochain on `n ∈ λ_1(F)`, expanded in the coordinates of the class of `n`.
* `TauCeti.ContCohomology.IsHeisenbergCochain.apply_eq_repr_degreeOneBasis_inr_of_lt`,
  `TauCeti.ContCohomology.IsHeisenbergCochain.apply_eq_neg_repr_degreeOneBasis_inr_of_gt`,
  `TauCeti.ContCohomology.IsHeisenbergCochain.apply_eq_choose_two_mul_repr_degreeOneBasis_inl`:
  for two coordinate characters, the value is a single coordinate of the class of `n`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Proposition 3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §9.
-/

public section

namespace TauCeti.ContCohomology.IsHeisenbergCochain

open TauCeti.freeProP

universe u uM uA uP

variable {p : ℕ} [Fact p.Prime] {X : Type u} [LinearOrder X]

section General

variable [Fintype X]

variable {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T1Space M]
    [DistribMulAction (freeProP p X) M] [Module (ZMod p) M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T1Space A]
    [DistribMulAction (freeProP p X) A] [Module (ZMod p) A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [T1Space P]
    [DistribMulAction (freeProP p X) P] [Module (ZMod p) P]
  {μ : M →+ A →+ P} {a : Z1 (freeProP p X) M} {b : Z1 (freeProP p X) A} {h : freeProP p X → P}
  (hh : IsHeisenbergCochain μ a b h)
  (htrivM : ∀ (g : freeProP p X) (m : M), g • m = m)
  (htrivA : ∀ (g : freeProP p X) (x : A), g • x = x)
  (htrivP : ∀ (g : freeProP p X) (x : P), g • x = x)
include hh htrivM htrivA htrivP

/-- **The value of a Heisenberg cochain on `λ_1(F)`, in the coordinates of `gr_1(F)`.** For
`n ∈ λ_1(F)` with class `Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]` in the standard basis of
`gr_1(F)`,

  `h n = Σ_i c_i • ((p choose 2) • μ (a x_i) (b x_i))
         + Σ_{i<k} a_{ik} • (μ (a x_i) (b x_k) - μ (a x_k) (b x_i))`. -/
theorem apply_eq_sum_repr_degreeOneBasis (n : pLowerCentralSeries p (freeProP p X) 1) :
    h n =
      ∑ i, (degreeOneBasis p X).repr (gradedMk p (freeProP p X) 1 n) (Sum.inl i) •
          (p.choose 2 • μ ((a : freeProP p X → M) (of i)) ((b : freeProP p X → A) (of i))) +
        ∑ ij : {ij : X × X // ij.1 < ij.2},
          (degreeOneBasis p X).repr (gradedMk p (freeProP p X) 1 n) (Sum.inr ij) •
            (μ ((a : freeProP p X → M) (of ij.1.1)) ((b : freeProP p X → A) (of ij.1.2)) -
              μ ((a : freeProP p X → M) (of ij.1.2)) ((b : freeProP p X → A) (of ij.1.1))) := by
  have haN : ∀ n : pLowerCentralSeries p (freeProP p X) 1, (a : freeProP p X → M) n = 0 :=
    fun n ↦ apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one htrivM
      (ZModModule.char_nsmul_eq_zero p) a.2 n.2
  have hbN : ∀ n : pLowerCentralSeries p (freeProP p X) 1, (b : freeProP p X → A) n = 0 :=
    fun n ↦ apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one htrivA
      (ZModModule.char_nsmul_eq_zero p) b.2 n.2
  rw [← hh.gradedRestrict_gradedMk htrivP haN hbN (ZModModule.char_nsmul_eq_zero p) n]
  conv_lhs => rw [← (degreeOneBasis p X).sum_repr (gradedMk p (freeProP p X) 1 n)]
  simp only [Fintype.sum_sum_type, map_add, map_sum, ZMod.map_smul, degreeOneBasis_apply,
    hh.gradedRestrict_degreeOneFamily_inl htrivP haN hbN
      (ZModModule.char_nsmul_eq_zero p) htrivM htrivA,
    hh.gradedRestrict_degreeOneFamily_inr htrivP haN hbN
      (ZModModule.char_nsmul_eq_zero p) htrivM htrivA]

end General

section Coordinate

variable [Finite X]

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action carried by the variables below is the one the cocycles are stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable [DistribMulAction (freeProP p X) (ZMod p)]
  {a b : Z1 (freeProP p X) (ZMod p)} {h : freeProP p X → ZMod p}
  (hh : IsHeisenbergCochain (AddMonoidHom.mul : ZMod p →+ ZMod p →+ ZMod p) a b h)
  (htriv : ∀ (g : freeProP p X) (x : ZMod p), g • x = x)

omit [Finite X] [DistribMulAction (freeProP p X) (ZMod p)] in
/-- The product of two Kronecker deltas. -/
private theorem single_mul_single (i j k l : X) :
    (Pi.single i 1 : X → ZMod p) k * (Pi.single j 1 : X → ZMod p) l =
      if k = i ∧ l = j then 1 else 0 := by
  rw [Pi.single_apply, Pi.single_apply, ite_zero_mul_ite_zero, one_mul]

include hh htriv

/-- A Heisenberg cochain with `𝔽_p`-values agrees on `λ_1(F)` with any linear functional on
`gr_1(F)` that takes the values of the cup pairing on the standard basis. -/
private theorem apply_eq_of_forall_degreeOneBasis
    (f : gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] ZMod p)
    (hinl : ∀ i, p.choose 2 •
        ((a : freeProP p X → ZMod p) (of i) * (b : freeProP p X → ZMod p) (of i)) =
      f (degreeOneBasis p X (Sum.inl i)))
    (hinr : ∀ ij : {ij : X × X // ij.1 < ij.2},
      (a : freeProP p X → ZMod p) (of ij.1.1) * (b : freeProP p X → ZMod p) (of ij.1.2) -
        (a : freeProP p X → ZMod p) (of ij.1.2) * (b : freeProP p X → ZMod p) (of ij.1.1) =
      f (degreeOneBasis p X (Sum.inr ij)))
    (n : pLowerCentralSeries p (freeProP p X) 1) :
    h n = f (gradedMk p (freeProP p X) 1 n) := by
  have haN : ∀ n : pLowerCentralSeries p (freeProP p X) 1, (a : freeProP p X → ZMod p) n = 0 :=
    fun n ↦ apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one htriv
      (ZModModule.char_nsmul_eq_zero p) a.2 n.2
  have hbN : ∀ n : pLowerCentralSeries p (freeProP p X) 1, (b : freeProP p X → ZMod p) n = 0 :=
    fun n ↦ apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one htriv
      (ZModModule.char_nsmul_eq_zero p) b.2 n.2
  have key : (hh.gradedRestrict htriv haN hbN
      (ZModModule.char_nsmul_eq_zero p)).toZModLinearMap p = f := by
    refine (degreeOneBasis p X).ext fun k ↦ ?_
    rw [AddMonoidHom.coe_toZModLinearMap]
    rcases k with i | ij
    · rw [← hinl i, degreeOneBasis_apply,
        hh.gradedRestrict_degreeOneFamily_inl htriv haN hbN
          (ZModModule.char_nsmul_eq_zero p) htriv htriv, AddMonoidHom.mul_apply]
    · rw [← hinr ij, degreeOneBasis_apply,
        hh.gradedRestrict_degreeOneFamily_inr htriv haN hbN
          (ZModModule.char_nsmul_eq_zero p) htriv htriv, AddMonoidHom.mul_apply,
        AddMonoidHom.mul_apply]
  rw [← key, AddMonoidHom.coe_toZModLinearMap, gradedRestrict_gradedMk]

variable {i j : X} (ha : ∀ k, (a : freeProP p X → ZMod p) (of k) = (Pi.single i 1 : X → ZMod p) k)
include ha

/-- **The value of a Heisenberg cochain of two coordinate characters `χ_i`, `χ_j` with `i < j` on
`λ_1(F)`** is the coefficient `a_{ij}` of the bracket `[ξ_i, ξ_j]` in the class of the argument. -/
theorem apply_eq_repr_degreeOneBasis_inr_of_lt (hij : i < j)
    (hb : ∀ k, (b : freeProP p X → ZMod p) (of k) = (Pi.single j 1 : X → ZMod p) k)
    (n : pLowerCentralSeries p (freeProP p X) 1) :
    h n = (degreeOneBasis p X).repr (gradedMk p (freeProP p X) 1 n) (Sum.inr ⟨(i, j), hij⟩) := by
  rw [← Module.Basis.coord_apply]
  refine hh.apply_eq_of_forall_degreeOneBasis htriv _ (fun k ↦ ?_) (fun ij ↦ ?_) n
  · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      ite_eq_right (Sum.inl_ne_inr), ha, hb, single_mul_single,
      ite_eq_right fun hk ↦ hij.ne (hk.1.symm.trans hk.2), smul_zero]
  · obtain ⟨⟨k, l⟩, hkl⟩ := ij
    -- The bracket `[ξ_k, ξ_l]` with `k < l` cannot be `[ξ_j, ξ_i]`, since `i < j`.
    have hne : ¬ (l = i ∧ k = j) := fun hlk ↦ by
      obtain ⟨rfl, rfl⟩ := hlk
      exact lt_asymm hij hkl
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ha, ha, hb, hb,
      single_mul_single, single_mul_single]
    simp only [hne, ite_false, sub_zero, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq]

/-- **The value of a Heisenberg cochain of two coordinate characters `χ_i`, `χ_j` with `j < i` on
`λ_1(F)`** is minus the coefficient `a_{ji}` of the bracket `[ξ_j, ξ_i]` in the class of the
argument. -/
theorem apply_eq_neg_repr_degreeOneBasis_inr_of_gt (hji : j < i)
    (hb : ∀ k, (b : freeProP p X → ZMod p) (of k) = (Pi.single j 1 : X → ZMod p) k)
    (n : pLowerCentralSeries p (freeProP p X) 1) :
    h n = -(degreeOneBasis p X).repr (gradedMk p (freeProP p X) 1 n) (Sum.inr ⟨(j, i), hji⟩) := by
  rw [← Module.Basis.coord_apply, ← LinearMap.neg_apply]
  refine hh.apply_eq_of_forall_degreeOneBasis htriv _ (fun k ↦ ?_) (fun ij ↦ ?_) n
  · rw [LinearMap.neg_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_right (Sum.inl_ne_inr), neg_zero, ha, hb, single_mul_single,
      ite_eq_right fun hk ↦ hji.ne (hk.2.symm.trans hk.1), smul_zero]
  · obtain ⟨⟨k, l⟩, hkl⟩ := ij
    -- The bracket `[ξ_k, ξ_l]` with `k < l` cannot be `[ξ_i, ξ_j]`, since `j < i`.
    have hne : ¬ (k = i ∧ l = j) := fun hkl' ↦ by
      obtain ⟨rfl, rfl⟩ := hkl'
      exact lt_asymm hji hkl
    rw [LinearMap.neg_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ha, ha, hb, hb, single_mul_single, single_mul_single]
    simp only [hne, ite_false, zero_sub, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq, and_comm]

/-- **The value of a Heisenberg cochain of a coordinate character `χ_i` with itself on `λ_1(F)`**
is `(p choose 2)` times the coefficient `c_i` of the `p`-th power `π ξ_i` in the class of the
argument; it vanishes for odd `p`, and it is `c_i` for `p = 2`. -/
theorem apply_eq_choose_two_mul_repr_degreeOneBasis_inl
    (hb : ∀ k, (b : freeProP p X → ZMod p) (of k) = (Pi.single i 1 : X → ZMod p) k)
    (n : pLowerCentralSeries p (freeProP p X) 1) :
    h n = (p.choose 2 : ZMod p) *
      (degreeOneBasis p X).repr (gradedMk p (freeProP p X) 1 n) (Sum.inl i) := by
  rw [← Module.Basis.coord_apply, ← smul_eq_mul, ← LinearMap.smul_apply]
  refine hh.apply_eq_of_forall_degreeOneBasis htriv _ (fun k ↦ ?_) (fun ij ↦ ?_) n
  · rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ha, hb, single_mul_single]
    simp only [and_self, Sum.inl.injEq, nsmul_eq_mul, smul_eq_mul]
  · obtain ⟨⟨k, l⟩, hkl⟩ := ij
    rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_right (Sum.inr_ne_inl), smul_zero, ha, ha, hb, hb,
      single_mul_single, single_mul_single]
    simp only [and_comm, sub_self]

end Coordinate

end TauCeti.ContCohomology.IsHeisenbergCochain
