/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.Periodic.Compression.Homology
public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Basic

/-!
# The homology of complex projective space compressed modulo `2(n + 1)`

The minimal Chern number of `CPⁿ` is `n + 1`, so Hamiltonian Floer complexes of `CPⁿ` built from
finite Laurent coefficients and specialized at `t = 1` are graded modulo `2(n + 1)`. In the PSS
comparison, a Morse generator of index `j` has the Floer degree `j - n`, which is the cochain
degree `2n - j` in the convention `n - μ` of `TauCeti.Floer.kernelProduct_mem_cochain_gradeBy`.
The cyclically graded module that the PSS comparison produces for `CPⁿ` is therefore the
homology of the `2(n + 1)`-periodic compression `TauCeti.PeriodicComplex.compression` of an
integer-graded complex `K` whose homology in degree `2n - j` is the singular homology
`Hⱼ(CPⁿ; R)`, for instance a Morse complex placed in these degrees. The PSS comparison itself is
not constructed here.

This file computes the homology of that compression. Since `Hⱼ(CPⁿ; R)` is `R` for even
`j ≤ 2n` and zero otherwise, the homology of `K` is `R` in the degrees `0, 2, …, 2n` and zero in the
other degrees. These degrees are distinct modulo `2(n + 1)`, so each residue class contains at
most one of them, and:

* the homology of the compression is `R` in each residue `2k`, `0 ≤ k ≤ n`
  (`TauCeti.ComplexProjectiveSpace.compressionHomologyIsoTwoMul`);
* it vanishes in the other residues
  (`TauCeti.ComplexProjectiveSpace.isZero_homology_compression_of_ne_two_mul`).

In the Floer degree `i = n - r` of a residue `r`, these are the degrees `i` for which `i + n` is
one of `0, 2, …, 2n` modulo `2(n + 1)`. Over a division ring `𝕜` the homology of the compression
is therefore one-dimensional in `n + 1` residues and zero in the others
(`TauCeti.ComplexProjectiveSpace.finrank_homology_compression`,
`TauCeti.ComplexProjectiveSpace.sum_finrank_homology_compression`). Consequently every complex of
finite-dimensional vector spaces graded modulo `2(n + 1)` with the same homology has total
dimension at least `n + 1` (`TauCeti.ComplexProjectiveSpace.add_one_le_sum_finrank_X`): a
cyclically graded Floer complex of `CPⁿ` with this homology has at least `n + 1` generators.

The cellular chain complex of `CPⁿ`, placed in the degrees `2n - j` by
`ComplexShape.embeddingUpIntLE (2 * n)`, is such a complex `K`: its homology in degree `2n - j` is
`Hⱼ(CPⁿ; R)` (`TauCeti.ComplexProjectiveSpace.extendCellularChainComplexHomologyIso`), and it is
supported in `[0, 2n]`, so it has no homology above `2n` (`CochainComplex.isZero_of_isLE`).

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progress in Mathematics **133** (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications **52** (2012), Chapter 11, the Floer homology of monotone symplectic
  manifolds such as `CPⁿ`.
-/

public section

noncomputable section

open CategoryTheory Limits Set Module TauCeti.PeriodicComplex

universe v u

namespace TauCeti.ComplexProjectiveSpace

/-- The residues of `0, 2, …, 2n` modulo `2(n + 1)` are distinct. -/
private lemma eq_of_two_mul_natCast_eq {n k l : ℕ} (hk : k ≤ n) (hl : l ≤ n)
    (h : (2 * k : ZMod (2 * (n + 1))) = 2 * l) : k = l := by
  have h' : ((2 * k : ℕ) : ZMod (2 * (n + 1))) = ((2 * l : ℕ) : ZMod (2 * (n + 1))) := by
    push_cast
    exact h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    at h'
  omega

section Homology

variable {n : ℕ} {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)
  (K : CochainComplex A ℤ)
  (e : ∀ j : ℕ, K.homology (2 * n - j) ≅
    ((AlgebraicTopology.singularHomologyFunctor A j).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n)))
  (hK : ∀ p : ℤ, 2 * n < p → IsZero (K.homology p))

include e hK in
/-- A complex with the homology of `CPⁿ` in the degrees `2n - j` has no homology outside the
degrees `0, 2, …, 2n`. -/
private lemma isZero_homology_of_forall_ne (q : ℤ) (hq : ∀ k : ℕ, k ≤ n → q ≠ 2 * k) :
    IsZero (K.homology q) := by
  rcases lt_or_ge (2 * (n : ℤ)) q with hq' | hq'
  · exact hK q hq'
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, q = 2 * n - j := ⟨(2 * n - q).toNat, by omega⟩
  refine (e j).isZero_iff.2 ?_
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hj
  · rcases lt_or_ge n m with hm | hm
    · exact isZero_singularHomology_of_lt R (by omega)
    · exact absurd (by omega) (hq (n - m) (by omega))
  · exact isZero_singularHomology_of_odd R hj

variable [HasCompression (2 * (n + 1)) K] (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- **The compressed homology of `CPⁿ` in the residue `2k`.** Let `K` be a complex supported in
`[a, b]` whose homology in degree `2n - j` is `Hⱼ(CPⁿ; R)`, with no homology above `2n`. For
`k ≤ n`, the homology of its compression modulo `2(n + 1)` in the residue `2k` is `R`. It is the
homology of `K` in degree `2k`, which is `H₂₍ₙ₋ₖ₎(CPⁿ; R) ≅ R`. -/
def compressionHomologyIsoTwoMul (k : ℕ) (hk : k ≤ n) :
    (compression (2 * (n + 1)) K).homology (2 * (k : ZMod (2 * (n + 1)))) ≅ R :=
  compressionHomologyIsoOfIsZero _ K a b _ (2 * k) (by simp) (fun q hq hqk ↦
      isZero_homology_of_forall_ne R K e hK q fun l hl hql ↦ hqk <| by
        subst hql
        rw [eq_of_two_mul_natCast_eq hl hk (by simpa using hq)]) ≪≫
    eqToIso (by rw [show (2 * k : ℤ) = 2 * n - ((2 * (n - k) : ℕ) : ℤ) by omega]) ≪≫
    e (2 * (n - k)) ≪≫
    singularHomologyIso R (Nat.sub_le n k)

/-- The isomorphism `compressionHomologyIsoTwoMul` is the projection `πCompressionHomology` onto
the summand of degree `2k`, followed by the given identification of that homology with
`H₂₍ₙ₋ₖ₎(CPⁿ; R)` and by `singularHomologyIso`. -/
@[reassoc]
lemma compressionHomologyIsoTwoMul_hom (k : ℕ) (hk : k ≤ n) :
    (compressionHomologyIsoTwoMul R K e hK a b k hk).hom =
      πCompressionHomology _ K _ (2 * k) ≫
        eqToHom (by rw [show (2 * k : ℤ) = 2 * n - ((2 * (n - k) : ℕ) : ℤ) by omega]) ≫
        (e (2 * (n - k))).hom ≫ (singularHomologyIso R (Nat.sub_le n k)).hom := by
  simp [compressionHomologyIsoTwoMul]

/-- The inverse of `compressionHomologyIsoTwoMul` ends with the inclusion `ιCompressionHomology` of
the summand of degree `2k`. -/
@[reassoc]
lemma compressionHomologyIsoTwoMul_inv (k : ℕ) (hk : k ≤ n) :
    (compressionHomologyIsoTwoMul R K e hK a b k hk).inv =
      (singularHomologyIso R (Nat.sub_le n k)).inv ≫ (e (2 * (n - k))).inv ≫
        eqToHom (by rw [show (2 * k : ℤ) = 2 * n - ((2 * (n - k) : ℕ) : ℤ) by omega]) ≫
        ιCompressionHomology _ K _ (2 * k) := by
  simp [compressionHomologyIsoTwoMul]

include e hK a b in
/-- **The compressed homology of `CPⁿ` vanishes in the residues other than `0, 2, …, 2n`.** Let
`K` be a complex supported in `[a, b]` whose homology in degree `2n - j` is `Hⱼ(CPⁿ; R)`, with no
homology above `2n`. The homology of its compression modulo `2(n + 1)` vanishes in every residue
`r` which is not `2k` for any `k ≤ n`. -/
theorem isZero_homology_compression_of_ne_two_mul (r : ZMod (2 * (n + 1)))
    (hr : ∀ k : ℕ, k ≤ n → 2 * (k : ZMod (2 * (n + 1))) ≠ r) :
    IsZero ((compression (2 * (n + 1)) K).homology r) :=
  PeriodicComplex.isZero_homology_compression _ K a b r fun q hq ↦
    isZero_homology_of_forall_ne R K e hK q fun k hk hqk ↦ hr k hk (by
      subst hqk
      simpa using hq)

end Homology

section DivisionRing

variable {n : ℕ} {𝕜 : Type u} [DivisionRing 𝕜] (K : CochainComplex (ModuleCat.{u} 𝕜) ℤ)
  (e : ∀ j : ℕ, K.homology (2 * n - j) ≅
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} 𝕜) j).obj (ModuleCat.of 𝕜 𝕜)).obj
      (TopCat.of (ComplexProjectiveSpace n)))
  (hK : ∀ p : ℤ, 2 * n < p → IsZero (K.homology p))
  [HasCompression (2 * (n + 1)) K] (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

include e hK a b in
/-- Over a division ring, the homology of the compression modulo `2(n + 1)` of a complex with
the homology of `CPⁿ` has dimension one in the residues `2k`, `k ≤ n`, and zero in the others:
its dimension in the residue `r` is the number of `k ≤ n` with `2k ≡ r`. -/
theorem finrank_homology_compression (r : ZMod (2 * (n + 1))) :
    finrank 𝕜 ((compression (2 * (n + 1)) K).homology r) =
      ((Finset.range (n + 1)).filter fun k : ℕ ↦ 2 * (k : ZMod (2 * (n + 1))) = r).card := by
  by_cases h : ∃ k : ℕ, k ≤ n ∧ 2 * (k : ZMod (2 * (n + 1))) = r
  · obtain ⟨k, hk, rfl⟩ := h
    rw [(compressionHomologyIsoTwoMul _ K e hK a b k hk).toLinearEquiv.finrank_eq]
    refine (finrank_self 𝕜).trans (Finset.card_eq_one.2 ⟨k, Finset.ext fun l ↦ ?_⟩).symm
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨fun hl ↦ eq_of_two_mul_natCast_eq (by omega) hk hl.2, fun hl ↦ hl ▸ ⟨by omega, rfl⟩⟩
  · simp only [not_exists, not_and] at h
    have := ModuleCat.isZero_iff_subsingleton.1
      (isZero_homology_compression_of_ne_two_mul _ K e hK a b r h)
    rw [finrank_zero_of_subsingleton, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun k hk ↦ h k (by simpa [Nat.lt_succ_iff] using hk)

include e hK a b in
/-- Over a division ring, the total dimension of the homology of the compression modulo
`2(n + 1)` of a complex with the homology of `CPⁿ` is `n + 1`, the total Betti number of `CPⁿ`. -/
theorem sum_finrank_homology_compression :
    ∑ r : ZMod (2 * (n + 1)), finrank 𝕜 ((compression (2 * (n + 1)) K).homology r) = n + 1 := by
  simp_rw [finrank_homology_compression K e hK a b]
  rw [← Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_univ _, Finset.card_range]

include e hK a b in
/-- **The rank bound for cyclically graded complexes with the homology of `CPⁿ`.** Over a division
ring, a complex `D` of finite-dimensional vector spaces graded modulo `2(n + 1)` whose homology is
isomorphic in each residue to that of the compression of a complex with the homology of `CPⁿ` has
total dimension at least `n + 1`. -/
theorem add_one_le_sum_finrank_X {c : ComplexShape (ZMod (2 * (n + 1)))}
    (D : HomologicalComplex (ModuleCat.{u} 𝕜) c) [∀ r, Module.Finite 𝕜 (D.X r)]
    (f : ∀ r, D.homology r ≅ (compression (2 * (n + 1)) K).homology r) :
    n + 1 ≤ ∑ r, finrank 𝕜 (D.X r) := by
  refine (sum_finrank_homology_compression K e hK a b).ge.trans <| Finset.sum_le_sum fun r _ ↦
    (f r).toLinearEquiv.finrank_eq.symm.le.trans (D.finrank_homology_le_finrank_X r)

end DivisionRing

section Cellular

attribute [local instance] cwComplex Abelian.hasFiniteBiproducts

variable {n : ℕ} {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- The cellular chain complex of `CPⁿ`, placed in the degrees `2n - j`, has the homology of
`CPⁿ`: its homology in degree `2n - j` is `Hⱼ(CPⁿ; R)`. -/
def extendCellularChainComplexHomologyIso (j : ℕ) :
    ((cellularChainComplex (univ : Set (ComplexProjectiveSpace n)) R).extend
        (ComplexShape.embeddingUpIntLE (2 * n))).homology (2 * n - j) ≅
      ((AlgebraicTopology.singularHomologyFunctor A j).obj R).obj
        (TopCat.of (ComplexProjectiveSpace n)) :=
  have := finite_cwComplex (n := n)
  HomologicalComplex.extendHomologyIso _ _ (ComplexShape.embeddingUpIntLE_f _ j) ≪≫
    cellularSingularHomologyIsoUniv R j

/-- The cellular chain complex of `CPⁿ`, placed in the degrees `2n - j`, vanishes below `0`. Like
every extension along `ComplexShape.embeddingUpIntLE (2 * n)`, it also vanishes above `2n`. -/
instance : CochainComplex.IsStrictlyGE ((cellularChainComplex
    (univ : Set (ComplexProjectiveSpace n)) R).extend (ComplexShape.embeddingUpIntLE (2 * n))) 0 :=
  (CochainComplex.isStrictlyGE_iff _ 0).2 fun p hp ↦ by
    by_cases h : ∃ j, (ComplexShape.embeddingUpIntLE (2 * n)).f j = p
    · obtain ⟨j, hj⟩ := h
      refine (HomologicalComplex.extendXIso _ _ hj).isZero_iff.2 ?_
      rw [ComplexShape.embeddingUpIntLE_f] at hj
      exact isZero_cellularChainComplex_X_of_lt R (by omega)
    · exact HomologicalComplex.isZero_extend_X _ _ p fun j hj ↦ h ⟨j, hj⟩

end Cellular

end TauCeti.ComplexProjectiveSpace
