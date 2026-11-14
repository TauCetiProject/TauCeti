/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.CartanSymmetry
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# Simple orbits of based automorphisms of irreducible root systems

Let `P` be a finite reduced crystallographic irreducible root system over a characteristic-zero
domain `R`, let `b` be a base of `P`, and let `σ : P.Aut` be an automorphism permuting the simple
roots of `b`. Transporting `σ` along the Cartan-Killing classification of `b` yields an element of
`t.diagramSymmetry` for the unique valid `TauCeti.DynkinType` `t` of `b`. Combining this transport
with the classification of `diagramSymmetry` in `TauCeti.LinearAlgebra.RootSystem.CartanSymmetry`
proves the irreducible dichotomy governing folding by diagram automorphisms:

* **Multiple-edge rigidity** (`RootPairing.eq_one_of_not_isSimplyLaced`,
  `RootPairing.indexEquiv_eq_self_of_multiple_edge`): if `b.cartanMatrix` is not simply laced, then
  `σ = 1` and `σ.indexEquiv` fixes every root index.
* **Simply-laced simple-orbit dichotomy** (`RootPairing.simpleOrbit_pairing_eq_zero_or_typeA_even`):
  if `b.cartanMatrix` is simply laced, then either distinct roots in every simple `σ`-orbit are
  orthogonal (`P.pairing i j = 0`), or `b` has Cartan type `A (2 * n)` (`1 ≤ n`) under a numbering
  `e : b.support ≃ Fin (2 * n)` in which `σ` reverses the chain (`e j = (e i).rev`).
* **Uniqueness of the non-orthogonal middle orbit in type `A₂ₙ`**
  (`RootPairing.pairing_eq_zero_iff_of_typeA_even_rev`,
  `RootPairing.pairing_typeA_even_mid`,
  `RootPairing.not_forall_simpleOrbit_pairing_eq_zero_of_typeA_even_rev`): in the even-`A`
  reversal case, the adjacent middle pair `{n - 1, n}` has pairing `-1` and is the unique
  non-orthogonal simple `σ`-orbit, so the two branches of the dichotomy are mutually exclusive.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4, Plates I--IX.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, p. 1, condition (1).
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-! ### Support invariance of based automorphisms and simple orbits -/

/-- An automorphism carrying `b.support` into itself maps a root index into `b.support` if and only
if the index already lies in `b.support`, because `b.support` is finite. -/
theorem Base.mem_support_indexEquiv_iff {P : RootPairing ι R M N} (b : P.Base) {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : ι) :
    σ.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  conv_lhs =>
    rw [← Base.map_eq_of_forall_mem_support hσ, b.mem_support_map_iff, Equiv.symm_apply_apply]

/-- For an automorphism permuting the simple roots of `b`, a `σ`-orbit either consists entirely of
simple roots or contains none. -/
theorem mem_support_iff_of_mem_orbitIndices {P : RootPairing ι R M N} [Finite ι] {b : P.Base}
    {σ : P.Aut} (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {i j : ι}
    (h : j ∈ P.orbitIndices σ i) : j ∈ b.support ↔ i ∈ b.support :=
  Iff.of_eq ((mem_orbitIndices.mp h).apply_eq_of_apply_eq (f := (· ∈ b.support)) fun z ↦
    propext (b.mem_support_indexEquiv_iff hσ z)).symm

/-! ### Transport to the standard diagram symmetry group -/

/-- Under a Cartan-type labelling `e : b.support ≃ Fin t.rank`, the permutation of `b.support`
induced by a based automorphism `σ` conjugates to a diagram symmetry of `t`. -/
private theorem permCongr_subtypePerm_mem_diagramSymmetry {P : RootPairing ι R M N} [CharZero R]
    [P.IsCrystallographic] {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {t : TauCeti.DynkinType}
    {e : b.support ≃ Fin t.rank}
    (he : ∀ i j : b.support, b.cartanMatrix i j = t.cartanMatrix (e i) (e j)) :
    e.permCongr (Equiv.Perm.subtypePerm σ.indexEquiv (b.mem_support_indexEquiv_iff hσ)) ∈
      t.diagramSymmetry := by
  refine TauCeti.DynkinType.mem_diagramSymmetry_iff.mpr fun u v ↦ ?_
  conv_rhs => rw [← e.apply_symm_apply u, ← e.apply_symm_apply v]
  simp only [_root_.Equiv.permCongr_apply, ← he, Base.cartanMatrix, Base.cartanMatrixIn_def,
    _root_.Equiv.Perm.subtypePerm_apply]
  exact σ.toHom.pairingIn_indexEquiv ℤ (e.symm u : ι) (e.symm v : ι)

/-! ### Multiple-edge rigidity -/

/-- **A based automorphism of an irreducible non-simply-laced root system is the identity.** -/
theorem eq_one_of_not_isSimplyLaced (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : σ = 1 := by
  obtain ⟨t, ⟨ht, hct⟩, -⟩ := TauCeti.existsUnique_dynkinType b
  have hsl : ¬ t.IsSimplyLaced := mt (hct.isSimplyLaced_iff_of_valid ht).mpr hmultiple
  obtain ⟨e, he⟩ := (TauCeti.hasCartanType_iff b t).mp hct
  let τ := _root_.Equiv.Perm.subtypePerm σ.indexEquiv (b.mem_support_indexEquiv_iff hσ)
  have hmem : e.permCongr τ ∈ t.diagramSymmetry := permCongr_subtypePerm_mem_diagramSymmetry hσ he
  rw [TauCeti.DynkinType.diagramSymmetry_eq_bot_of_not_isSimplyLaced hsl, Subgroup.mem_bot] at hmem
  refine b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ ?_
  have hi' := congrArg (fun ρ ↦ e.symm (ρ (e ⟨i, hi⟩))) hmem
  simpa [τ] using congrArg Subtype.val hi'

/-- **If the Cartan matrix of an irreducible root system has a multiple edge, every based
automorphism fixes every root index.** -/
theorem indexEquiv_eq_self_of_multiple_edge (P : RootPairing ι R M N) [Finite ι] [CharZero R]
    [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) (i : ι) : σ.indexEquiv i = i := by
  rw [P.eq_one_of_not_isSimplyLaced b σ hσ hmultiple]
  rfl

/-! ### The simply-laced dichotomy and the even-`A` middle orbit -/

/-- **Simple-orbit dichotomy for irreducible simply-laced root systems.** For a based automorphism
`σ` of an irreducible simply-laced finite reduced crystallographic root system, either distinct
roots in every simple `σ`-orbit have zero pairing, or the base has Cartan type `A (2 * n)` (`1 ≤ n`)
under a Bourbaki numbering `e : b.support ≃ Fin (2 * n)` in which `σ` reverses the chain. -/
theorem simpleOrbit_pairing_eq_zero_or_typeA_even (P : RootPairing ι R M N) [Finite ι] [CharZero R]
    [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced) :
    (∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∃ e : b.support ≃ Fin (2 * n),
        (∀ i j : b.support,
          b.cartanMatrix i j = (TauCeti.DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev := by
  obtain ⟨t, ⟨ht, hct⟩, -⟩ := TauCeti.existsUnique_dynkinType b
  have hsl : t.IsSimplyLaced := (hct.isSimplyLaced_iff_of_valid ht).mp hsimply
  obtain ⟨e, he⟩ := (TauCeti.hasCartanType_iff b t).mp hct
  let τ := _root_.Equiv.Perm.subtypePerm σ.indexEquiv (b.mem_support_indexEquiv_iff hσ)
  have hmem : e.permCongr τ ∈ t.diagramSymmetry := permCongr_subtypePerm_mem_diagramSymmetry hσ he
  rcases TauCeti.DynkinType.cartanMatrix_eq_zero_of_sameCycle_or_eq_A_even ht hsl hmem with
    horth | ⟨n, hn, rfl, hrev⟩
  · left
    intro i hi j hj hne
    have hj_supp : j ∈ b.support := (P.mem_support_iff_of_mem_orbitIndices hσ hj).mpr hi
    let i' : b.support := ⟨i, hi⟩
    let j' : b.support := ⟨j, hj_supp⟩
    have hcycle : (e.permCongr τ).SameCycle (e i') (e j') := by
      rw [_root_.Equiv.Perm.sameCycle_permCongr, _root_.Equiv.Perm.sameCycle_subtypePerm]
      exact mem_orbitIndices.mp hj
    have he_ne : e i' ≠ e j' := e.injective.ne (Subtype.coe_ne_coe.mp hne)
    have hzero : b.cartanMatrix i' j' = 0 := (he i' j').trans (horth (e i') (e j') hcycle he_ne)
    exact b.cartanMatrix_apply_eq_zero_iff_pairing.mp hzero
  · right
    have hrev' (i j : b.support) (hij : σ.indexEquiv i = j) : e j = (e i).rev := by
      have hτ_ij : τ i = j := Subtype.ext hij
      simpa only [_root_.Equiv.permCongr_apply, _root_.Equiv.symm_apply_apply, hτ_ij] using
        hrev (e i)
    exact ⟨n, hn, e, he, hrev'⟩

/-- Under chain reversal of a base of type `A₂ₙ`, two distinct simple roots in the same `σ`-orbit
are orthogonal if and only if neither is the middle node `n - 1` (equivalently, they do not form
the adjacent middle pair `{n - 1, n}`). -/
theorem pairing_eq_zero_iff_of_typeA_even_rev {P : RootPairing ι R M N} [Finite ι] [CharZero R]
    [P.IsCrystallographic] {b : P.Base} {σ : P.Aut}
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {n : ℕ} {e : b.support ≃ Fin (2 * n)}
    (he : ∀ i j : b.support,
      b.cartanMatrix i j = (TauCeti.DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) {i j : b.support}
    (hj : (j : ι) ∈ P.orbitIndices σ i) (hne : i ≠ j) :
    P.pairing (i : ι) (j : ι) = 0 ↔ (e i : ℕ) ≠ n - 1 ∧ (e j : ℕ) ≠ n - 1 := by
  let τ := _root_.Equiv.Perm.subtypePerm σ.indexEquiv (b.mem_support_indexEquiv_iff hσ)
  have hperm : e.permCongr τ = TauCeti.graphPermA (2 * n) := by
    refine _root_.Equiv.ext fun u ↦ ?_
    simp only [_root_.Equiv.permCongr_apply, TauCeti.graphPermA_apply]
    exact (hrev (e.symm u) (τ (e.symm u)) rfl).trans (congrArg Fin.rev (e.apply_symm_apply u))
  have hcycle : (TauCeti.graphPermA (2 * n)).SameCycle (e i) (e j) := by
    rw [← hperm, _root_.Equiv.Perm.sameCycle_permCongr, _root_.Equiv.Perm.sameCycle_subtypePerm]
    exact mem_orbitIndices.mp hj
  rw [← b.cartanMatrix_apply_eq_zero_iff_pairing, he]
  exact TauCeti.DynkinType.cartanMatrix_A_even_graphPermA_eq_zero_iff hcycle (e.injective.ne hne)

/-- Under chain reversal of `A₂ₙ` (`1 ≤ n`), `σ.indexEquiv` sends the middle node `n - 1` to `n`. -/
theorem indexEquiv_typeA_even_mid {P : RootPairing ι R M N} {b : P.Base} {σ : P.Aut}
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {n : ℕ} (hn : 1 ≤ n)
    {e : b.support ≃ Fin (2 * n)}
    (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) :
    σ.indexEquiv (e.symm ⟨n - 1, by omega⟩ : b.support) =
      (e.symm ⟨n, by omega⟩ : b.support) := by
  let u : b.support := e.symm ⟨n - 1, by omega⟩
  let w : b.support := ⟨σ.indexEquiv u, hσ u u.2⟩
  have hw : e w = ⟨n, by omega⟩ := by
    rw [hrev u w rfl]
    simp only [u, Equiv.apply_symm_apply]
    ext
    simp [Fin.val_rev]
    omega
  have hw_eq : w = e.symm ⟨n, by omega⟩ := e.injective (hw.trans (e.apply_symm_apply _).symm)
  exact congrArg Subtype.val hw_eq

/-- Under chain reversal of `A₂ₙ` (`1 ≤ n`), the middle simple root `n` lies in the `σ`-orbit of
`n - 1`. -/
theorem mem_orbitIndices_typeA_even_mid {P : RootPairing ι R M N} [Finite ι] {b : P.Base}
    {σ : P.Aut} (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {n : ℕ} (hn : 1 ≤ n)
    {e : b.support ≃ Fin (2 * n)}
    (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) :
    ((e.symm ⟨n, by omega⟩ : b.support) : ι) ∈
      P.orbitIndices σ (e.symm ⟨n - 1, by omega⟩ : b.support) :=
  mem_orbitIndices_iff_exists_pow.mpr ⟨1, by simpa using indexEquiv_typeA_even_mid hσ hn hrev⟩

/-- In a base of Cartan type `A₂ₙ` (`1 ≤ n`), the adjacent middle simple roots `n - 1` and `n` have
pairing `-1`. -/
theorem pairing_typeA_even_mid {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}
    {n : ℕ} (hn : 1 ≤ n) {e : b.support ≃ Fin (2 * n)}
    (he : ∀ i j : b.support,
      b.cartanMatrix i j = (TauCeti.DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.pairing (e.symm ⟨n - 1, by omega⟩ : b.support)
      (e.symm ⟨n, by omega⟩ : b.support) = -1 := by
  let u : b.support := e.symm ⟨n - 1, by omega⟩
  let v : b.support := e.symm ⟨n, by omega⟩
  have hmat : b.cartanMatrix u v = -1 := by
    rw [he u v]
    simp only [u, v, Equiv.apply_symm_apply]
    exact TauCeti.DynkinType.cartanMatrix_A_even_mid hn
  rw [Base.cartanMatrix, Base.cartanMatrixIn_def] at hmat
  rw [← P.algebraMap_pairingIn ℤ, hmat, map_neg, map_one]

/-- In the even-`A` reversal case (`1 ≤ n`), the simple `σ`-orbits are not pairwise orthogonal,
witnessed by the middle pair `{n - 1, n}` of pairing `-1`; hence the two branches of
`RootPairing.simpleOrbit_pairing_eq_zero_or_typeA_even` are mutually exclusive. -/
theorem not_forall_simpleOrbit_pairing_eq_zero_of_typeA_even_rev {P : RootPairing ι R M N}
    [Finite ι] [Nontrivial R] [P.IsCrystallographic] {b : P.Base} {σ : P.Aut}
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {n : ℕ} (hn : 1 ≤ n)
    {e : b.support ≃ Fin (2 * n)}
    (he : ∀ i j : b.support,
      b.cartanMatrix i j = (TauCeti.DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) :
    ¬ ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0 := by
  intro horth
  let u : b.support := e.symm ⟨n - 1, by omega⟩
  let v : b.support := e.symm ⟨n, by omega⟩
  have huv_ne : (u : ι) ≠ (v : ι) :=
    Subtype.coe_ne_coe.mpr (e.symm.injective.ne (Fin.ne_of_val_ne (by simp; omega)))
  have hzero := horth u u.2 v (mem_orbitIndices_typeA_even_mid hσ hn hrev) huv_ne
  rw [pairing_typeA_even_mid hn he] at hzero
  exact neg_ne_zero.mpr one_ne_zero hzero

end RootPairing
