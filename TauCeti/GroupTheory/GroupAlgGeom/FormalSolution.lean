/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.EquationallyNoetherian
public import TauCeti.GroupTheory.GroupAlgGeom.FreeGGroup
public import TauCeti.GroupTheory.GroupAlgGeom.VarSubgroup
public import TauCeti.Logic.ForallExistsAlt
import TauCeti.GroupTheory.FreeGroup.Basis
import TauCeti.GroupTheory.FreeGroup.CSA
import TauCeti.GroupTheory.FreeGroup.Merzljakov.FormalSolution
import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic
import TauCeti.GroupTheory.FreeGroup.Vaught
import TauCeti.GroupTheory.GroupAlgGeom.Linear
import TauCeti.GroupTheory.GroupAlgGeom.SingleEquation

/-!
# Formal solutions of positive sentences and Merzljakov's theorem

Let `S(x, y) = 1` be a system of equations over a group `G` in the variables `x₀, …, x_{k-1}` and
`y₀, …, y_{k-1}`. A *formal solution* of the positive sentence
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` is a tuple of words `q₀, …, q_{k-1}` in the free
`G`-group `G[x₀, …, x_{k-1}]` such that `q i` involves only the coefficients and the variables
`x₀, …, x_i`, and such that `S(x, q) = 1` holds in `G[x₀, …, x_{k-1}]`. In other words, the
system has a solution in `G[x₀, …, x_{k-1}]` whose `x`-coordinates are the variables
`x₀, …, x_{k-1}` themselves and whose `y`-coordinates respect the order of the quantifiers.

A formal solution makes the sentence true in every group `H` receiving the coefficients through a
homomorphism `G →* H`: given values of the `x i` in `H`, the values of the words `q i` are
witnesses for the `y i`, and the value of `q i` depends only on `x₀, …, x_i`.

**Merzljakov's theorem** proves the converse when `G` is a nonabelian free group:
* for any finite system `S` over an arbitrary nonabelian free group `G` (of finite or infinite
  rank), if `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` holds in `G`, then `S` has a formal
  solution (`exists_isFormalSolution_of_finite`);
* when `G[x₀, …, x_{k-1}]` is equationally Noetherian over `G`—in particular whenever `G` is a
  countable nonabelian free group—the same equivalence holds for *every* (possibly infinite) system
  `S` (`exists_isFormalSolution_iff_forallExistsAlt`, Kharlampovich–Myasnikov §4.4, Theorem 4).

Consequently, any positive sentence of this form that holds in a nonabelian free group `G` transfers
along every homomorphism `G →* H` (`forallExistsAlt_of_forallExistsAlt_id_of_finite`,
`forallExistsAlt_of_forallExistsAlt_id`). Both rank `0` and rank `1` fail the converse
(`not_isFormalSolution_var`, `not_isFormalSolution_commutator_inl`), so `¬IsMulCommutative G` is
sharp.

## Main definitions

* `TauCeti.GroupAlgGeom.IsFormalSolution S q`: `q` is a formal solution of the sentence
  `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)`.

## Main results

* `TauCeti.GroupAlgGeom.IsFormalSolution.sumElim_eval_mem_V`: the values of the words of a
  formal solution solve the system, for any values of the universally quantified variables.
* `TauCeti.GroupAlgGeom.IsFormalSolution.forallExistsAlt`: a formal solution makes the sentence
  true in every group receiving the coefficients.
* `TauCeti.GroupAlgGeom.exists_isFormalSolution_singleton`,
  `TauCeti.GroupAlgGeom.exists_isFormalSolution_of_finite`,
  `TauCeti.GroupAlgGeom.exists_isFormalSolution_iff_forallExistsAlt_of_finite`: Merzljakov's
  theorem for single equations and finite systems over any nonabelian free group.
* `TauCeti.GroupAlgGeom.exists_isFormalSolution_of_isEquationallyNoetherian`,
  `TauCeti.GroupAlgGeom.exists_isFormalSolution`,
  `TauCeti.GroupAlgGeom.exists_isFormalSolution_iff_forallExistsAlt`: Merzljakov's theorem for
  arbitrary systems over countable (or equationally Noetherian) nonabelian free groups.
* `TauCeti.GroupAlgGeom.forallExistsAlt_of_forallExistsAlt_id_of_finite`,
  `TauCeti.GroupAlgGeom.forallExistsAlt_of_forallExistsAlt_id`: transfer of positive sentences from
  a nonabelian free group along any homomorphism.
* `TauCeti.GroupAlgGeom.not_isFormalSolution_var`,
  `TauCeti.GroupAlgGeom.not_isFormalSolution_commutator_inl`: failure of the converse in
  ranks `0` and `1`.
* `TauCeti.GroupAlgGeom.not_forallExistsAlt_sq_freeGroup`,
  `TauCeti.GroupAlgGeom.not_isFormalSolution_sq`: the sentence `∀ x ∃ y (y² = x)` fails in a free
  group on a nonempty alphabet, and has no formal solution.
* `TauCeti.GroupAlgGeom.not_isFormalSolution_eq_later`: `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₁)` has no
  formal solution, although `y₀ = x₁` is solvable in `G[x₀, x₁]`: the constraint on the variables
  of `q i` cannot be dropped.

## References

* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemma 5.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.4, Merzljakov's Theorem, Corollary 9, Definition 13, and Theorem 4.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod FreeGroup

variable {G H : Type*} [Group G] [Group H]

/-! ### Formal solutions -/

variable {k : ℕ}

/-- A *formal solution* of the positive sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)`,
for a system of equations `S` over `G` in the variables `x i = Sum.inl i` and `y i = Sum.inr i`:
words `q i` in the free `G`-group on `x₀, …, x_{k-1}` such that `q i` involves only the
coefficients and the variables `x j` with `j ≤ i`, and such that substituting `q i` for `y i`
makes every equation of `S` trivial. -/
@[mk_iff]
structure IsFormalSolution (S : Set (GX G (Fin k ⊕ Fin k))) (q : Fin k → GX G (Fin k)) : Prop where
  /-- The `i`-th word involves only the coefficients and the variables `x j` with `j ≤ i`. -/
  mem_varSubgroup (i : Fin k) : q i ∈ GX.varSubgroup G (Set.Iic i)
  /-- Substituting the words for the variables `y i` solves the system in the free `G`-group on
  the variables `x i`. -/
  sumElim_mem_V : Sum.elim (fun i => inr (of i)) q ∈ V (inl : G →* GX G (Fin k)) S

namespace IsFormalSolution

variable {S T : Set (GX G (Fin k ⊕ Fin k))} {q : Fin k → GX G (Fin k)}

/-- Substituting the words of a formal solution for the variables `y i` makes each equation of
the system trivial in the free `G`-group on the variables `x i`. -/
theorem eval_eq_one (h : IsFormalSolution S q) {s : GX G (Fin k ⊕ Fin k)} (hs : s ∈ S) :
    eval inl (Sum.elim (fun i => inr (of i)) q) s = 1 :=
  mem_V.1 h.sumElim_mem_V s hs

/-- A formal solution of a system is a formal solution of each of its subsystems. -/
theorem anti (h : IsFormalSolution T q) (hST : S ⊆ T) : IsFormalSolution S q :=
  ⟨h.mem_varSubgroup, V_antitone _ hST h.sumElim_mem_V⟩

/-- The value of the `i`-th word of a formal solution depends only on the values of
`x₀, …, x_i`. -/
theorem eval_eq_eval (h : IsFormalSolution S q) (ι : G →* H) {i : Fin k} {x x' : Fin k → H}
    (hx : ∀ j ≤ i, x j = x' j) : eval ι x (q i) = eval ι x' (q i) :=
  GX.eval_eq_eval_of_mem_varSubgroup (h.mem_varSubgroup i) ι hx

/-- Specialising a formal solution: in a group `H` receiving the coefficients, any values `x` of
the universally quantified variables together with the values at `x` of the words of a formal
solution solve the system. -/
theorem sumElim_eval_mem_V (h : IsFormalSolution S q) (ι : G →* H) (x : Fin k → H) :
    Sum.elim x (fun i => eval ι x (q i)) ∈ V ι S := by
  refine mem_V.2 fun s hs => ?_
  have hw : wordMap ι (Sum.elim (fun i => inr (of i)) q) x = Sum.elim x fun i => eval ι x (q i) :=
    funext fun j => by cases j <;> simp
  rw [← hw, ← eval_comp_eval, MonoidHom.comp_apply, h.eval_eq_one hs, _root_.map_one]

/-- A formal solution makes the sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` true in
every group `H` receiving the coefficients through a homomorphism `ι : G →* H`. -/
theorem forallExistsAlt (h : IsFormalSolution S q) (ι : G →* H) :
    ForallExistsAlt k fun x y : Fin k → H => Sum.elim x y ∈ V ι S :=
  forallExistsAlt_of_skolem (fun x i => eval ι x (q i)) (fun _ _ _ => h.eval_eq_eval ι)
    (h.sumElim_eval_mem_V ι)

end IsFormalSolution

variable {S T : Set (GX G (Fin k ⊕ Fin k))} {q : Fin k → GX G (Fin k)}

/-- A tuple of words is a formal solution of a union of two systems exactly when it is a formal
solution of both. -/
@[simp]
theorem isFormalSolution_union :
    IsFormalSolution (S ∪ T) q ↔ IsFormalSolution S q ∧ IsFormalSolution T q := by
  simp only [isFormalSolution_iff, V_union, Set.mem_inter_iff]
  tauto

/-- A formal solution of the empty system is a tuple of words whose `i`-th word involves only the
coefficients and the variables `x j` with `j ≤ i`. -/
@[simp]
theorem isFormalSolution_empty :
    IsFormalSolution (∅ : Set (GX G (Fin k ⊕ Fin k))) q ↔
      ∀ i, q i ∈ GX.varSubgroup G (Set.Iic i) := by
  simp [isFormalSolution_iff]

/-- A system and the normal subgroup it generates have the same formal solutions. -/
@[simp]
theorem isFormalSolution_normalClosure :
    IsFormalSolution (Subgroup.normalClosure S : Set (GX G (Fin k ⊕ Fin k))) q ↔
      IsFormalSolution S q := by
  simp [isFormalSolution_iff]

/-! ### Merzljakov's theorem -/

section Merzljakov

/-- For a free basis `b : FreeGroupBasis A G`, the free `G`-group `G[X]` is naturally isomorphic
to `FreeGroup (X ⊕ A)`. -/
private noncomputable def gxFreeGroupEquiv {A : Type*} (b : FreeGroupBasis A G) (X : Type*) :
    GX G X ≃* FreeGroup (X ⊕ A) :=
  MonoidHom.toMulEquiv
    (Monoid.Coprod.lift (b.lift (of ∘ Sum.inr)) (FreeGroup.map Sum.inl))
    (FreeGroup.lift (Sum.elim (inr ∘ of) (inl ∘ b)))
    (hom_ext (b.ext_hom _ _ fun _ => by simp) (FreeGroup.ext_hom _ _ fun _ => by simp))
    (FreeGroup.ext_hom _ _ fun z => by cases z <;> simp)

@[simp]
private theorem gxFreeGroupEquiv_inl_coe {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (c : A) : gxFreeGroupEquiv b X (inl (b c)) = of (Sum.inr c) := by
  simp [gxFreeGroupEquiv]

@[simp]
private theorem gxFreeGroupEquiv_inr_of {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (x : X) : gxFreeGroupEquiv b X (inr (of x)) = of (Sum.inl x) := by
  simp [gxFreeGroupEquiv]

@[simp]
private theorem gxFreeGroupEquiv_symm_of_inl {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (x : X) : (gxFreeGroupEquiv b X).symm (of (Sum.inl x)) = inr (of x) := by
  simp [gxFreeGroupEquiv]

@[simp]
private theorem gxFreeGroupEquiv_symm_of_inr {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (c : A) : (gxFreeGroupEquiv b X).symm (of (Sum.inr c)) = inl (b c) := by
  simp [gxFreeGroupEquiv]

/-- **Merzljakov's theorem** (single equation): over a nonabelian free group `G`, if the positive
sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (s(x, y) = 1)` holds in `G`, then `{s}` has a formal
solution in `G[x₀, …, x_{k-1}]`. -/
theorem exists_isFormalSolution_singleton [IsFreeGroup G] (hG : ¬IsMulCommutative G)
    {s : GX G (Fin k ⊕ Fin k)}
    (h : ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) {s}) :
    ∃ q, IsFormalSolution {s} q := by
  let b := IsFreeGroup.basis G
  obtain ⟨g₁, g₂, hg⟩ : ∃ g₁ g₂ : G, ¬Commute g₁ g₂ := by
    simpa [isMulCommutative_iff, ← commute_iff_eq] using hG
  have : Nontrivial (IsFreeGroup.Generators G) := b.nontrivial_of_not_commute hg
  obtain ⟨a₀, b₀, hab₀⟩ := exists_pair_ne (IsFreeGroup.Generators G)
  obtain ⟨f, hf, hs⟩ := h.exists_skolem
  let eX := gxFreeGroupEquiv b (Fin k)
  let eXY := gxFreeGroupEquiv b (Fin k ⊕ Fin k)
  let f' : (Fin k → FreeGroup (IsFreeGroup.Generators G)) →
      Fin k → FreeGroup (IsFreeGroup.Generators G) :=
    fun x' i => b.repr (f (b.repr.symm ∘ x') i)
  have hf' : ∀ i x₁ x₂, (∀ j ≤ i, x₁ j = x₂ j) → f' x₁ i = f' x₂ i := fun i x₁ x₂ hx =>
    congrArg b.repr (hf i _ _ fun j hj => congrArg b.repr.symm (hx j hj))
  have hs' : ∀ x',
      FreeGroup.lift (Sum.elim (Sum.elim x' (f' x')) of) (eXY s) = 1 := fun x' => by
    have hhom : (FreeGroup.lift (Sum.elim (Sum.elim x' (f' x')) of)).comp eXY.toMonoidHom =
        b.repr.toMonoidHom.comp (eval (.id G) (Sum.elim (b.repr.symm ∘ x')
          (f (b.repr.symm ∘ x')))) :=
      hom_ext (b.ext_hom _ _ fun c => by simp [eXY])
        (FreeGroup.ext_hom _ _ fun z => by cases z <;> simp [eXY, f'])
    have hval : eval (.id G) (Sum.elim (b.repr.symm ∘ x') (f (b.repr.symm ∘ x'))) s = 1 :=
      mem_V.1 (hs (b.repr.symm ∘ x')) s rfl
    simpa [hval] using DFunLike.congr_fun hhom s
  obtain ⟨y', hy', hw'⟩ := FreeGroup.exists_formalSolution_of_skolem hab₀ (eXY s) f' hf' hs'
  refine ⟨fun i => eX.symm (y' i), fun i => ?_, mem_V.2 ?_⟩
  · refine Subgroup.closure_induction (p := fun u _ => eX.symm u ∈ GX.varSubgroup G (Set.Iic i))
      ?_ (by simp) (fun _ _ _ _ h₁ h₂ => by simpa using mul_mem h₁ h₂)
      (fun _ _ h₁ => by simpa using inv_mem h₁) (hy' i)
    rintro _ (⟨c, rfl⟩ | ⟨j, hj, rfl⟩)
    · simp [eX]
    · simpa [eX] using GX.inr_of_mem_varSubgroup (G := G) hj
  · intro t ht
    rw [Set.mem_singleton_iff.1 ht]
    have hhom : eval (inl : G →* GX G (Fin k))
        (Sum.elim (fun i => inr (of i)) fun i => eX.symm (y' i)) =
        eX.symm.toMonoidHom.comp ((FreeGroup.lift
          (Sum.elim (Sum.elim (of ∘ Sum.inl) y') (of ∘ Sum.inr))).comp eXY.toMonoidHom) :=
      hom_ext (b.ext_hom _ _ fun c => by simp [eX, eXY])
        (FreeGroup.ext_hom _ _ fun z => by cases z <;> simp [eX, eXY])
    simpa [hw'] using DFunLike.congr_fun hhom s

/-- **Merzljakov's theorem** (finite systems): over any nonabelian free group `G` (of finite or
infinite rank), if the positive sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` holds in
`G` for a finite system `S`, then `S` has a formal solution in `G[x₀, …, x_{k-1}]`. -/
theorem exists_isFormalSolution_of_finite [IsFreeGroup G] (hG : ¬IsMulCommutative G)
    {S : Set (GX G (Fin k ⊕ Fin k))} (hS : S.Finite)
    (h : ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S) :
    ∃ q, IsFormalSolution S q := by
  have : IsFreeGroup (GX G (Fin k)) := (isFreeGGroup_inl (Fin k) (G := G)).isFreeGroup
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ¬Commute a b := by
    simpa [isMulCommutative_iff, ← commute_iff_eq] using hG
  obtain ⟨s, hs⟩ := exists_forall_V_singleton_eq_of_finite a b hS
  have hVG : V (.id G) {s} = V (.id G) S :=
    hs (.id G) IsFreeGroup.isVaught IsFreeGroup.isCSA hab
  have hVGX : V (inl : G →* GX G (Fin k)) {s} = V inl S :=
    hs (inl : G →* GX G (Fin k)) IsFreeGroup.isVaught IsFreeGroup.isCSA
      fun hc => hab (by simpa using hc.map (eval (.id G) (1 : Fin k → G)))
  obtain ⟨q, hq⟩ := exists_isFormalSolution_singleton (s := s) hG (by simpa only [← hVG] using h)
  exact ⟨q, hq.mem_varSubgroup, hVGX ▸ hq.sumElim_mem_V⟩

/-- **Merzljakov's theorem** for finite systems (equivalence): over any nonabelian free group `G`,
a finite system `S` has a formal solution if and only if the positive sentence
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` holds in `G`. -/
theorem exists_isFormalSolution_iff_forallExistsAlt_of_finite [IsFreeGroup G]
    (hG : ¬IsMulCommutative G) {S : Set (GX G (Fin k ⊕ Fin k))} (hS : S.Finite) :
    (∃ q, IsFormalSolution S q) ↔
      ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S :=
  ⟨fun ⟨_, hq⟩ => hq.forallExistsAlt (.id G), exists_isFormalSolution_of_finite hG hS⟩

/-- Over any nonabelian free group `G`, a positive sentence for a finite system `S` that holds in
`G` transfers along every homomorphism `ι : G →* H` (Kharlampovich–Myasnikov §4.4, Corollary 9). -/
theorem forallExistsAlt_of_forallExistsAlt_id_of_finite [IsFreeGroup G]
    (hG : ¬IsMulCommutative G) {S : Set (GX G (Fin k ⊕ Fin k))} (hS : S.Finite) (ι : G →* H)
    (h : ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S) :
    ForallExistsAlt k fun x y : Fin k → H => Sum.elim x y ∈ V ι S :=
  let ⟨_, hq⟩ := exists_isFormalSolution_of_finite hG hS h
  hq.forallExistsAlt ι

/-- **Merzljakov's theorem** for arbitrary systems under equational Noetherianity: if `G` is a
nonabelian free group and `G[x₀, …, x_{k-1}]` is equationally Noetherian over `G`, then any system
`S` (finite or infinite) whose positive sentence holds in `G` admits a formal solution. -/
theorem exists_isFormalSolution_of_isEquationallyNoetherian [IsFreeGroup G]
    (hG : ¬IsMulCommutative G) (hnoeth : IsEquationallyNoetherian (inl : G →* GX G (Fin k)))
    {S : Set (GX G (Fin k ⊕ Fin k))}
    (h : ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S) :
    ∃ q, IsFormalSolution S q := by
  obtain ⟨S₀, hS₀, hfin, hV⟩ := hnoeth.exists_finite S
  obtain ⟨q, hq⟩ := exists_isFormalSolution_of_finite hG hfin
    (h.mono fun _ _ hx => V_antitone _ hS₀ hx)
  exact ⟨q, hq.mem_varSubgroup, hV ▸ hq.sumElim_mem_V⟩

/-- **Merzljakov's theorem** for arbitrary systems over a countable nonabelian free group
(Kharlampovich–Myasnikov §4.4, Theorem 4): if `G` is a countable nonabelian free group, then any
system `S` (finite or infinite) whose positive sentence holds in `G` admits a formal solution in
`G[x₀, …, x_{k-1}]`. -/
theorem exists_isFormalSolution [IsFreeGroup G] [Countable G] (hG : ¬IsMulCommutative G)
    {S : Set (GX G (Fin k ⊕ Fin k))}
    (h : ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S) :
    ∃ q, IsFormalSolution S q := by
  let b := IsFreeGroup.basis G
  have : Countable (IsFreeGroup.Generators G) := b.injective.countable
  exact exists_isFormalSolution_of_isEquationallyNoetherian hG
    (isEquationallyNoetherian_of_freeGroupBasis inl (.ofRepr (gxFreeGroupEquiv b (Fin k)))) h

/-- **Merzljakov's theorem** for arbitrary systems over a countable nonabelian free group
(equivalence, Kharlampovich–Myasnikov §4.4, Theorem 4): over a countable nonabelian free group `G`,
a system `S` has a formal solution if and only if the positive sentence
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (S(x, y) = 1)` holds in `G`. -/
theorem exists_isFormalSolution_iff_forallExistsAlt [IsFreeGroup G] [Countable G]
    (hG : ¬IsMulCommutative G) (S : Set (GX G (Fin k ⊕ Fin k))) :
    (∃ q, IsFormalSolution S q) ↔
      ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S :=
  ⟨fun ⟨_, hq⟩ => hq.forallExistsAlt (.id G), exists_isFormalSolution hG⟩

/-- Over a countable nonabelian free group `G`, any positive sentence (for a possibly infinite
system `S`) that holds in `G` transfers along every homomorphism `ι : G →* H`. -/
theorem forallExistsAlt_of_forallExistsAlt_id [IsFreeGroup G] [Countable G]
    (hG : ¬IsMulCommutative G) {S : Set (GX G (Fin k ⊕ Fin k))} (ι : G →* H)
    (h : ForallExistsAlt k fun x y : Fin k → G => Sum.elim x y ∈ V (.id G) S) :
    ForallExistsAlt k fun x y : Fin k → H => Sum.elim x y ∈ V ι S :=
  let ⟨_, hq⟩ := exists_isFormalSolution hG h
  hq.forallExistsAlt ι

end Merzljakov

/-! ### Examples -/

section Examples

open scoped commutatorElement

/-- The sentence `∀ x ∃ y (y = x a)` has the formal solution `q(x) = x a`. -/
example (a : G) :
    IsFormalSolution (k := 1) {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 0)) * inl a)⁻¹}
      ![inr (of 0) * inl a] := by
  refine ⟨fun i => ?_, by simp⟩
  obtain rfl := Subsingleton.elim i 0
  exact mul_mem (GX.inr_of_mem_varSubgroup (by simp)) (GX.inl_mem_varSubgroup _ a)

/-- The sentence `∀ x ∃ y ([x, y] = 1)` has the formal solution `q(x) = x`. -/
example :
    IsFormalSolution (G := G) (k := 1)
      {⁅(inr (of (Sum.inl 0)) : GX G (Fin 1 ⊕ Fin 1)), inr (of (Sum.inr 0))⁆} ![inr (of 0)] := by
  refine ⟨fun i => ?_, by simp [map_commutatorElement]⟩
  obtain rfl := Subsingleton.elim i 0
  exact GX.inr_of_mem_varSubgroup (by simp)

/-- The sentence `∀ x ∃ y ([x, y] = 1)` also has the formal solution `q(x) = 1`. -/
example :
    IsFormalSolution (G := G) (k := 1)
      {⁅(inr (of (Sum.inl 0)) : GX G (Fin 1 ⊕ Fin 1)), inr (of (Sum.inr 0))⁆} ![1] := by
  refine ⟨fun i => ?_, by simp [map_commutatorElement]⟩
  obtain rfl := Subsingleton.elim i 0
  exact one_mem _

/-- With no quantifiers and the trivial equation, the empty tuple is a formal solution. -/
example (q : Fin 0 → GX G (Fin 0)) : IsFormalSolution {1} q :=
  ⟨fun i => i.elim0, by simp⟩

/-- With no quantifiers, a nontrivial coefficient equation `g = 1` has no formal solution. -/
example {g : G} (hg : g ≠ 1) (q : Fin 0 → GX G (Fin 0)) : ¬IsFormalSolution {inl g} q :=
  fun h => by simpa [hg] using h.forallExistsAlt (MonoidHom.id G)

/-- The sentence `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₀ ∧ y₁ = x₁ x₀)` has the formal solution `q₀ = x₀`,
`q₁ = x₁ x₀`. -/
example :
    IsFormalSolution (G := G) (k := 2)
      {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 0)))⁻¹,
        inr (of (Sum.inr 1)) * (inr (of (Sum.inl 1)) * inr (of (Sum.inl 0)))⁻¹}
      ![inr (of 0), inr (of 1) * inr (of 0)] := by
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, by simp⟩
  · exact GX.inr_of_mem_varSubgroup (by simp)
  · exact mul_mem (GX.inr_of_mem_varSubgroup (by simp)) (GX.inr_of_mem_varSubgroup (by simp))

/-- The sentence `∀ x ∃ y (y² = x)` is false in a free group on a nonempty alphabet, whatever
the homomorphism receiving the coefficients. -/
theorem not_forallExistsAlt_sq_freeGroup {A : Type*} [Nonempty A] (ι : G →* FreeGroup A) :
    ¬ForallExistsAlt 1 fun x y : Fin 1 → FreeGroup A =>
      Sum.elim x y ∈ V ι {inr (of (Sum.inr 0)) ^ 2 * (inr (of (Sum.inl 0)))⁻¹} := fun h => by
  obtain ⟨a⟩ := ‹Nonempty A›
  have hsq : ∀ x : FreeGroup A, ∃ y, y ^ 2 = x := by
    simpa [forallExistsAlt_one, mul_inv_eq_one] using h
  obtain ⟨y, hy⟩ := hsq (of a)
  exact not_isProperPower_of a (Group.isProperPower_iff.2 ⟨y, 2, le_rfl, hy.symm⟩)

/-- The sentence `∀ x ∃ y (y² = x)` has no formal solution over any group of coefficients. -/
theorem not_isFormalSolution_sq (q : Fin 1 → GX G (Fin 1)) :
    ¬IsFormalSolution {inr (of (Sum.inr 0)) ^ 2 * (inr (of (Sum.inl 0)))⁻¹} q := fun h =>
  not_forallExistsAlt_sq_freeGroup (1 : G →* FreeGroup Unit) (h.forallExistsAlt _)

/-- The equation `y₀ = x₁` is solved in the free `G`-group on `x₀`, `x₁` by `y₀ = x₁`, a word
involving a variable quantified after `y₀`. -/
example :
    Sum.elim (fun i => inr (of i)) ![inr (of 1), 1] ∈
      V (inl : G →* GX G (Fin 2)) {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 1)))⁻¹} := by
  simp

/-- The sentence `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ (y₀ = x₁)` has no formal solution, although the equation
`y₀ = x₁` is solvable in the free `G`-group on `x₀`, `x₁`: the words of a formal solution must
respect the order of the quantifiers. -/
theorem not_isFormalSolution_eq_later (q : Fin 2 → GX G (Fin 2)) :
    ¬IsFormalSolution {inr (of (Sum.inr 0)) * (inr (of (Sum.inl 1)))⁻¹} q := fun h => by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, ∀ b : ℤ, a = b := by
    simpa [forallExistsAlt_succ, mul_inv_eq_one] using
      h.forallExistsAlt (1 : G →* Multiplicative ℤ)
  have := ha (a + 1)
  omega

/-- The sentence `∀ x₀ ∃ y₀ (x₀ = 1)` has no formal solution over any group `G`. When `G` is
trivial (the free group of rank `0`), the sentence holds in `G`, so Merzljakov's theorem fails in
rank `0`. -/
theorem not_isFormalSolution_var (q : Fin 1 → GX G (Fin 1)) :
    ¬IsFormalSolution {inr (of (Sum.inl 0))} q := fun h => by
  have h1 : Multiplicative.ofAdd (1 : ℤ) = 1 := by
    simpa using congrArg (eval (1 : G →* Multiplicative ℤ) ![Multiplicative.ofAdd 1])
      (h.eval_eq_one rfl)
  exact one_ne_zero (Multiplicative.ofAdd.injective h1)

/-- In a trivial group (for instance `FreeGroup Empty`), `∀ x₀ ∃ y₀ (x₀ = 1)` holds even though it
has no formal solution (`not_isFormalSolution_var`). -/
example [Subsingleton G] :
    ForallExistsAlt 1 fun x y : Fin 1 → G =>
      Sum.elim x y ∈ V (.id G) {inr (of (Sum.inl 0))} :=
  forallExistsAlt_one.2 fun _ => ⟨1, mem_V.2 fun _ _ => Subsingleton.elim _ _⟩

/-- For a nontrivial coefficient `a ≠ 1`, the sentence `∀ x₀ ∃ y₀ (⁅x₀, a⁆ = 1)` has no formal
solution over `G`. When `G` is commutative and nontrivial (for instance the free group of rank
`1`), the sentence holds in `G`, so Merzljakov's theorem fails in rank `1`. -/
theorem not_isFormalSolution_commutator_inl {a : G} (ha : a ≠ 1) (q : Fin 1 → GX G (Fin 1)) :
    ¬IsFormalSolution {⁅(inr (of (Sum.inl 0)) : GX G (Fin 1 ⊕ Fin 1)),
      (inl a : GX G (Fin 1 ⊕ Fin 1))⁆} q := fun h => by
  have hcomm : ⁅(inr (of 0) : GX G (Fin 1)), (inl a : GX G (Fin 1))⁆ = 1 := by
    simpa [map_commutatorElement] using h.eval_eq_one rfl
  exact GX.not_commute_inl_inr_of ha 0 (commutatorElement_eq_one_iff_commute.1 hcomm).symm

/-- In a commutative group (for instance `FreeGroup Unit` of rank `1` with generator `a ≠ 1`),
`∀ x₀ ∃ y₀ (⁅x₀, a⁆ = 1)` holds even though it has no formal solution when `a ≠ 1`
(`not_isFormalSolution_commutator_inl`). -/
example [IsMulCommutative G] (a : G) :
    ForallExistsAlt 1 fun x y : Fin 1 → G =>
      Sum.elim x y ∈ V (.id G)
        {⁅(inr (of (Sum.inl 0)) : GX G (Fin 1 ⊕ Fin 1)), (inl a : GX G (Fin 1 ⊕ Fin 1))⁆} :=
  forallExistsAlt_one.2 fun _ => ⟨1, mem_V.2 (by
    rintro _ rfl
    simp [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      isMulCommutative_iff.1 ‹_›])⟩

end Examples

end TauCeti.GroupAlgGeom
