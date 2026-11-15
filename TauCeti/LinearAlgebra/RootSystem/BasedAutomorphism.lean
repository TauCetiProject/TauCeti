/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Submatrix
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Symmetry
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# Based automorphisms and simple-root orbits of irreducible root systems

Let `P` be a root pairing with base `b`, and let `σ : P.Aut` be an automorphism carrying `b.support`
into itself (`∀ i ∈ b.support, σ.indexEquiv i ∈ b.support`, equivalently `σ ∈ b.basedAut` by
`RootPairing.Base.mem_basedAut_iff_forall_mem_support`). Restricting `σ.indexEquiv` to `b.support`
gives a permutation `RootPairing.Base.supportPerm b hσ : Equiv.Perm b.support`. Over a
characteristic-zero coefficient ring, this permutation preserves the Cartan matrix of `b`, and for a
finite reduced crystallographic root system over a characteristic-zero domain it identifies the
subgroup `b.basedAut` with `TauCeti.matrixSymmetryGroup b.cartanMatrix`
(`RootPairing.Base.basedAutMulEquivMatrixSymmetryGroup`).

When `P` is in addition irreducible, its Cartan matrix is connected and of finite type, so the
matrix-symmetry theorems of `TauCeti.LinearAlgebra.RootSystem.FiniteType.Symmetry` classify the
action of `σ` on the simple roots:

1. **Multiple-edge rigidity.** If `b.cartanMatrix` is not simply laced (`Bₙ` for `2 ≤ n`, `Cₙ` for
   `3 ≤ n`, `F₄`, or `G₂`), then `σ = 1` (`RootPairing.eq_one_of_not_isSimplyLaced` and
   `RootPairing.indexEquiv_eq_self_of_multiple_edge`), `b.basedAut = ⊥`, and every automorphism of
   `P` lies in its Weyl group (`RootPairing.Base.weylGroup_eq_top_of_not_isSimplyLaced`).
2. **Simply-laced simple-orbit dichotomy.** If `b.cartanMatrix` is simply laced, then either every
   simple `σ`-orbit is pairwise orthogonal (`P.pairing i j = 0` for `i ∈ b.support` and
   `j ∈ P.orbitIndices σ i` with `i ≠ j`), as required by the Stembridge folding hypotheses in
   `TauCeti.LinearAlgebra.RootSystem.Stembridge`, or `b` reindexes onto `DynkinType.A (2 * n)`
   (`1 ≤ n`) with `σ` reversing the chain of simple roots
   (`RootPairing.simpleOrbit_pairing_eq_zero_or_typeA_even`). In that exceptional even-`A` reversal
   case, the adjacent middle pair `{e.symm ⟨n - 1, _⟩, e.symm ⟨n, _⟩}` is the unique non-orthogonal
   simple orbit and has Cartan pairing `-1`
   (`RootPairing.Base.typeA_even_simpleOrbit_pairing_ne_zero_iff`,
   `RootPairing.Base.typeA_even_middle_pairingIn_eq_neg_one`, and
   `RootPairing.Base.typeA_even_middle_pairing_eq_neg_one`).

## Main definitions

* `RootPairing.Base.supportPerm`: the permutation of `b.support` induced by an automorphism carrying
  simple roots to simple roots.
* `RootPairing.Base.basedAutMulEquivMatrixSymmetryGroup`: the canonical group isomorphism
  `b.basedAut ≃* matrixSymmetryGroup b.cartanMatrix`.

## Main results

* `RootPairing.Base.supportPerm_mem_matrixSymmetryGroup`: `b.supportPerm hσ` preserves
  `b.cartanMatrix`.
* `RootPairing.Base.basedAut_eq_bot_of_not_isSimplyLaced` and
  `RootPairing.Base.weylGroup_eq_top_of_not_isSimplyLaced`: for an irreducible finite reduced
  crystallographic root system with a non-simply-laced base, `b.basedAut = ⊥` and `P.weylGroup = ⊤`.
* `RootPairing.eq_one_of_not_isSimplyLaced` and
  `RootPairing.indexEquiv_eq_self_of_multiple_edge`: any based automorphism of an irreducible
  non-simply-laced root system is trivial.
* `RootPairing.simpleOrbit_pairingIn_eq_zero_or_typeA_even` and
  `RootPairing.simpleOrbit_pairing_eq_zero_or_typeA_even`: the simply-laced simple-orbit dichotomy
  between pairwise orthogonal simple orbits and chain reversal of `A₂ₙ` (`1 ≤ n`).
* `RootPairing.Base.typeA_even_simpleOrbit_pairing_ne_zero_iff`,
  `RootPairing.Base.typeA_even_middle_pairingIn_eq_neg_one`, and
  `RootPairing.Base.typeA_even_middle_pairing_eq_neg_one`: in the `A₂ₙ` reversal case, the middle
  pair is the unique non-orthogonal simple orbit and pairs to `-1`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5, Proposition 16 and §4.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, §2.
-/

public section

open TauCeti

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- An irreducible root system (whose roots span the nontrivial weight module) has at least one root
index. Kept as a theorem rather than an instance to avoid cycling with Mathlib's
`[Nonempty ι] [NeZero (2 : R)] [P.IsIrreducible] → P.IsRootSystem` instance. -/
theorem nonempty_of_isIrreducible (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsIrreducible] :
    Nonempty ι := by
  by_contra h
  have := not_nonempty_iff.mp h
  have := IsIrreducible.nontrivial P
  have htop := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at htop
  exact bot_ne_top htop

namespace Base

/-! ## Permutation of simple roots induced by a based automorphism -/

/-- An automorphism carrying `b.support` into itself carries `b.support` onto itself, so membership
in `b.support` is preserved in both directions. -/
theorem indexEquiv_mem_support_iff (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i : ι) :
    σ.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  conv_lhs => rw [← b.map_eq_of_forall_mem_support hσ]
  rw [b.mem_support_map_iff, _root_.Equiv.symm_apply_apply]

/-- **The permutation of `b.support` induced by an automorphism carrying simple roots to simple
roots.** -/
def supportPerm (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) : _root_.Equiv.Perm b.support :=
  _root_.Equiv.Perm.subtypePerm σ.indexEquiv (b.indexEquiv_mem_support_iff hσ)

/-- Coercing `b.supportPerm hσ i` to `ι` evaluates `σ.indexEquiv i`. -/
@[simp]
theorem coe_supportPerm_apply (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i : b.support) :
    ((b.supportPerm hσ i : b.support) : ι) = σ.indexEquiv i :=
  (rfl)

/-- Coercing `(b.supportPerm hσ).symm i` to `ι` evaluates `σ.indexEquiv.symm i`. -/
@[simp]
theorem coe_supportPerm_symm_apply (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i : b.support) :
    (((b.supportPerm hσ).symm i : b.support) : ι) = σ.indexEquiv.symm i :=
  (rfl)

/-- Two simple roots lie in the same cycle of `b.supportPerm hσ` exactly when their ambient indices
lie in the same cycle of `σ.indexEquiv`. -/
theorem sameCycle_supportPerm_iff_sameCycle (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i j : b.support) :
    (b.supportPerm hσ).SameCycle i j ↔
      _root_.Equiv.Perm.SameCycle σ.indexEquiv (i : ι) (j : ι) :=
  _root_.Equiv.Perm.sameCycle_subtypePerm

/-- Two simple roots lie in the same cycle of `b.supportPerm hσ` exactly when one belongs to the
root orbit `P.orbitIndices σ` of the other. -/
theorem mem_orbitIndices_iff_sameCycle_supportPerm [Finite ι] (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i j : b.support) :
    (j : ι) ∈ P.orbitIndices σ i ↔ (b.supportPerm hσ).SameCycle i j := by
  rw [mem_orbitIndices, sameCycle_supportPerm_iff_sameCycle]

/-- **The permutation of simple roots induced by a based automorphism preserves the Cartan
matrix.** -/
theorem supportPerm_mem_matrixSymmetryGroup [CharZero R] [P.IsCrystallographic] (b : P.Base)
    {σ : P.Aut} (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) :
    b.supportPerm hσ ∈ matrixSymmetryGroup b.cartanMatrix := by
  refine mem_matrixSymmetryGroup_iff.mpr (Matrix.ext fun i j ↦ ?_)
  simp only [Matrix.submatrix_apply, cartanMatrix, cartanMatrixIn_def, coe_supportPerm_apply]
  exact σ.toHom.pairingIn_indexEquiv ℤ (i : ι) (j : ι)

/-- **For a finite reduced crystallographic root system over a characteristic-zero domain, the group
of based automorphisms is canonically isomorphic to the symmetry group of the Cartan matrix.** -/
noncomputable def basedAutMulEquivMatrixSymmetryGroup [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    b.basedAut ≃* matrixSymmetryGroup b.cartanMatrix := by
  let hom : b.basedAut →* matrixSymmetryGroup b.cartanMatrix :=
    { toFun := fun g ↦ ⟨b.supportPerm (mem_basedAut_iff_forall_mem_support.mp g.2),
        b.supportPerm_mem_matrixSymmetryGroup (mem_basedAut_iff_forall_mem_support.mp g.2)⟩
      map_one' := Subtype.ext <| _root_.Equiv.ext fun i ↦ Subtype.ext rfl
      map_mul' := fun g h ↦ Subtype.ext <| _root_.Equiv.ext fun i ↦ Subtype.ext <| by
        simp [coe_supportPerm_apply] }
  refine MulEquiv.ofBijective hom ⟨fun g h hgh ↦ ?_, fun ⟨τ, hτ⟩ ↦ ?_⟩
  · have hfix : (g : P.Aut)⁻¹ * h = 1 :=
      b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ by
        have hi' := congrArg
          (fun x : matrixSymmetryGroup b.cartanMatrix ↦ ((x.1 ⟨i, hi⟩ : b.support) : ι)) hgh
        simp only [hom, MonoidHom.coe_mk, OneHom.coe_mk, coe_supportPerm_apply] at hi'
        have hidx : ((g : P.Aut)⁻¹ * h).indexEquiv i =
            (g : P.Aut).indexEquiv.symm ((h : P.Aut).indexEquiv i) := by simp
        rw [hidx, ← hi', _root_.Equiv.symm_apply_apply]
    exact Subtype.ext (inv_mul_eq_one.mp hfix)
  · obtain ⟨g, hg, -⟩ := b.existsUnique_basedAut_of_cartanMatrix τ fun i j ↦
      congrFun₂ (mem_matrixSymmetryGroup_iff.mp hτ) i j
    refine ⟨g, Subtype.ext <| _root_.Equiv.ext fun i ↦ Subtype.ext ?_⟩
    simpa only [hom, MonoidHom.coe_mk, OneHom.coe_mk, coe_supportPerm_apply] using hg i

/-- `basedAutMulEquivMatrixSymmetryGroup` acts on `b.support` by restricting `g.indexEquiv`. -/
@[simp]
theorem coe_basedAutMulEquivMatrixSymmetryGroup_apply [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) (g : b.basedAut)
    (i : b.support) :
    (((b.basedAutMulEquivMatrixSymmetryGroup g : matrixSymmetryGroup b.cartanMatrix).1 i :
      b.support) : ι) = (g : P.Aut).indexEquiv i :=
  (rfl)

/-- If the Cartan matrix of `b` has no nontrivial symmetry, then `b.basedAut` is trivial. -/
theorem basedAut_eq_bot_of_matrixSymmetryGroup_eq_bot [CharZero R] [P.IsRootSystem]
    [P.IsCrystallographic] (b : P.Base) (hb : matrixSymmetryGroup b.cartanMatrix = ⊥) :
    b.basedAut = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
  have hσ' := mem_basedAut_iff_forall_mem_support.mp hσ
  have hperm : b.supportPerm hσ' = 1 :=
    Subgroup.mem_bot.mp (hb.le (b.supportPerm_mem_matrixSymmetryGroup hσ'))
  refine b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ ?_
  have hi' := _root_.Equiv.ext_iff.mp hperm ⟨i, hi⟩
  simpa only [coe_supportPerm_apply, _root_.Equiv.Perm.coe_one, id_eq, Subtype.ext_iff] using hi'

/-! ## Non-simply-laced rigidity -/

/-- **If an irreducible finite reduced crystallographic root system has a non-simply-laced Cartan
matrix, its based automorphism group is trivial.** -/
theorem basedAut_eq_bot_of_not_isSimplyLaced [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible] (b : P.Base)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : b.basedAut = ⊥ := by
  have : Nonempty ι := nonempty_of_isIrreducible P
  exact b.basedAut_eq_bot_of_matrixSymmetryGroup_eq_bot <|
    (isFiniteType_cartanMatrix b).matrixSymmetryGroup_eq_bot_of_not_isSimplyLaced
      (connected_diagramGraph_cartanMatrix b) hmultiple

/-- **If an irreducible finite reduced crystallographic root system has a non-simply-laced Cartan
matrix, every automorphism lies in its Weyl group.** -/
theorem weylGroup_eq_top_of_not_isSimplyLaced [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible] (b : P.Base)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : P.weylGroup = ⊤ := by
  have : Nonempty ι := nonempty_of_isIrreducible P
  exact b.weylGroup_eq_top_of_matrixSymmetryGroup_eq_bot <|
    (isFiniteType_cartanMatrix b).matrixSymmetryGroup_eq_bot_of_not_isSimplyLaced
      (connected_diagramGraph_cartanMatrix b) hmultiple

end Base

/-- **Every automorphism of a finite reduced crystallographic root system of a non-simply-laced
Dynkin type (`Bₙ`, `Cₙ`, `F₄`, `G₂`) lies in its Weyl group.** -/
theorem _root_.TauCeti.HasCartanType.weylGroup_eq_top_of_not_isSimplyLaced
    [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
    {b : P.Base} {t : DynkinType} (h : HasCartanType P b t) (ht : ¬ t.IsSimplyLaced) :
    P.weylGroup = ⊤ :=
  h.weylGroup_eq_top (DynkinType.diagramSymmetry_eq_bot_of_not_isSimplyLaced ht)

/-- **A based automorphism of an irreducible finite reduced crystallographic root system over a
characteristic-zero domain is the identity whenever the Cartan matrix is not simply laced.** -/
theorem eq_one_of_not_isSimplyLaced (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : σ = 1 :=
  Subgroup.mem_bot.mp <|
    (b.basedAut_eq_bot_of_not_isSimplyLaced hmultiple).le
      (b.mem_basedAut_iff_forall_mem_support.mpr hσ)

/-- **A based automorphism of an irreducible finite reduced crystallographic root system over a
characteristic-zero domain fixes every root index if the Cartan matrix is not simply laced.** -/
theorem indexEquiv_eq_self_of_multiple_edge (P : RootPairing ι R M N) [Finite ι] [CharZero R]
    [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hmultiple : ¬ b.cartanMatrix.IsSimplyLaced) : ∀ i : ι, σ.indexEquiv i = i := by
  rw [eq_one_of_not_isSimplyLaced P b σ hσ hmultiple]
  exact fun _ ↦ rfl

/-! ## Simply-laced simple-orbit dichotomy and the even-`A` middle pair -/

/-- **Integral simple-orbit dichotomy for irreducible simply-laced root systems.** Either every
simple `σ`-orbit has `P.pairingIn ℤ i j = 0` for distinct indices `i ≠ j`, or `b` reindexes onto
`DynkinType.A (2 * n)` (`1 ≤ n`) with `σ` reversing the numbered simple roots. -/
theorem simpleOrbit_pairingIn_eq_zero_or_typeA_even (P : RootPairing ι R M N) [Finite ι]
    [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
    [P.IsIrreducible] (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced) :
    (∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairingIn ℤ i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∃ e : b.support ≃ Fin (2 * n),
        (∀ i j : b.support, b.cartanMatrix i j =
          (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        (∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) := by
  have : Nonempty ι := nonempty_of_isIrreducible P
  rcases (isFiniteType_cartanMatrix b).orbit_apply_eq_zero_or_typeA_even
      (connected_diagramGraph_cartanMatrix b) hsimply
      (b.supportPerm_mem_matrixSymmetryGroup hσ) with horth | ⟨n, hn1, e, he, hrev⟩
  · left
    intro i hi j hjorb hne
    have hj : j ∈ b.support := by
      obtain ⟨k, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hjorb
      clear hjorb hne
      induction k with
      | zero => simpa using hi
      | succ k ih =>
        rw [pow_succ', _root_.Equiv.Perm.mul_apply]
        exact hσ _ ih
    have hcyc : (b.supportPerm hσ).SameCycle ⟨i, hi⟩ ⟨j, hj⟩ :=
      (b.mem_orbitIndices_iff_sameCycle_supportPerm hσ ⟨i, hi⟩ ⟨j, hj⟩).mp hjorb
    exact horth ⟨i, hi⟩ ⟨j, hj⟩ hcyc (fun heq ↦ hne (congrArg Subtype.val heq))
  · right
    refine ⟨n, hn1, e, he, fun i j hij ↦ ?_⟩
    have hj : j = b.supportPerm hσ i := Subtype.ext hij.symm
    rw [hj, hrev i]

/-- **Simple orbits in an irreducible simply-laced finite crystallographic root system are
pairwise orthogonal, except for the diagram reversal of even type `A₂ₙ` (`1 ≤ n`).** In the
exceptional case, `b.cartanMatrix` reindexes onto `(DynkinType.A (2 * n)).cartanMatrix` along an
equivalence `e : b.support ≃ Fin (2 * n)` under which `σ` reverses the node labels. -/
theorem simpleOrbit_pairing_eq_zero_or_typeA_even (P : RootPairing ι R M N) [Finite ι]
    [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
    [P.IsIrreducible] (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced) :
    (∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) ∨
      ∃ n : ℕ, 1 ≤ n ∧ ∃ e : b.support ≃ Fin (2 * n),
        (∀ i j : b.support, b.cartanMatrix i j =
          (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) ∧
        (∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev) := by
  refine (simpleOrbit_pairingIn_eq_zero_or_typeA_even P b σ hσ hsimply).imp (fun horth ↦ ?_) id
  intro i hi j hj hne
  rw [← P.algebraMap_pairingIn ℤ i j, horth i hi j hj hne, map_zero]

namespace Base

/-- **In the even-`A₂ₙ` reversal case (`1 ≤ n`), the adjacent middle pair
`{e.symm ⟨n - 1, _⟩, e.symm ⟨n, _⟩}` is the unique non-orthogonal simple `σ`-orbit.** -/
theorem typeA_even_simpleOrbit_pairing_ne_zero_iff [Finite ι] [CharZero R] [P.IsCrystallographic]
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {n : ℕ} (hn : 1 ≤ n) (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j : b.support, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)
    {i j : b.support} (hj : (j : ι) ∈ P.orbitIndices σ i) (hne : i ≠ j) :
    P.pairing (i : ι) (j : ι) ≠ 0 ↔
      (i = e.symm ⟨n - 1, by omega⟩ ∧ j = e.symm ⟨n, by omega⟩) ∨
        (i = e.symm ⟨n, by omega⟩ ∧ j = e.symm ⟨n - 1, by omega⟩) := by
  have hcyc_supp : (b.supportPerm hσ).SameCycle i j :=
    (b.mem_orbitIndices_iff_sameCycle_supportPerm hσ i j).mp hj
  have hcyc_A : (graphPermA (2 * n)).SameCycle (e i) (e j) :=
    hcyc_supp.map fun z ↦ by
      rw [graphPermA_apply]
      exact hrev z (b.supportPerm hσ z) rfl
  have hcartan : P.pairing (i : ι) (j : ι) ≠ 0 ↔ b.cartanMatrix i j ≠ 0 :=
    b.cartanMatrix_apply_eq_zero_iff_pairing.symm.not
  rw [hcartan, he i j,
    DynkinType.cartanMatrix_A_even_ne_zero_of_sameCycle_graphPermA_iff hn hcyc_A
      (e.injective.ne hne)]
  simp only [_root_.Equiv.eq_symm_apply]

/-- **The adjacent middle simple roots of `A₂ₙ` (`1 ≤ n`) have integral Cartan pairing `-1`.** -/
theorem typeA_even_middle_pairingIn_eq_neg_one [P.IsCrystallographic] (b : P.Base)
    {n : ℕ} (hn : 1 ≤ n) (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j : b.support, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.pairingIn ℤ (e.symm ⟨n - 1, by omega⟩ : ι) (e.symm ⟨n, by omega⟩ : ι) = -1 := by
  change b.cartanMatrix (e.symm ⟨n - 1, by omega⟩) (e.symm ⟨n, by omega⟩) = -1
  rw [he]
  simp only [_root_.Equiv.apply_symm_apply, DynkinType.cartanMatrix_A, CartanMatrix.A,
    Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The adjacent middle simple roots of `A₂ₙ` (`1 ≤ n`) have scalar pairing `-1`.** -/
theorem typeA_even_middle_pairing_eq_neg_one [P.IsCrystallographic] (b : P.Base)
    {n : ℕ} (hn : 1 ≤ n) (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j : b.support, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.pairing (e.symm ⟨n - 1, by omega⟩ : ι) (e.symm ⟨n, by omega⟩ : ι) = -1 := by
  rw [← P.algebraMap_pairingIn ℤ, b.typeA_even_middle_pairingIn_eq_neg_one hn e he, map_neg,
    map_one]

end Base

end RootPairing
