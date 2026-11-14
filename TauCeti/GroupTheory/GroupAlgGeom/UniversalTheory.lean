/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
public import TauCeti.GroupTheory.GroupAlgGeom.Linear
public import TauCeti.ModelTheory.Algebra.Group.Basic
public import TauCeti.ModelTheory.Algebra.Group.ExistentialUniversal
import Mathlib.Data.Int.Cast.Lemmas
import TauCeti.GroupTheory.FiniteAbelian.TorsionFree
import TauCeti.GroupTheory.FreeGroup.Basis

/-!
# Discrimination and universal sentences

Let `K` and `H` receive coefficients from `G`, and read the group language with coefficient names
`A` in both through a map `c : A → G`. If `K` is discriminated by `H` over `G`, then every
universal sentence that holds in `H` also holds in `K`.

A quantifier-free formula evaluated at a tuple of `K` keeps its truth value under every
coefficient-preserving homomorphism `K →* H` that keeps finitely many nontrivial elements of `K`,
determined by the tuple, nontrivial; discrimination provides such a homomorphism. A
counterexample in `K` to a universal sentence is therefore carried to a counterexample in `H`.

With trivial coefficients this says that a fully residually free group satisfies every universal
sentence true in the free group of rank two
(`TauCeti.LimitGroup.IsFullyResiduallyFree.realize_of_isUniversal`).

Conversely, let `H` be equationally Noetherian over `G`, let `K` be generated over `G` by
finitely many elements, and let the names `c` generate `G`. If every universal sentence true in
`H` holds in `K`, then `K` is discriminated by `H` over `G`. Given nontrivial elements
`k₁, …, k_m` of `K`, a finite part `S₀` of the relations of `K` has the same solutions in `H` as
all of them. The generators of `K` solve the equations `S₀` and the inequations `k_j ≠ 1`, so the
universal sentence saying that this system has no solution fails in `K`, hence in `H`. A
solution in `H` solves every relation of `K`, so it defines a coefficient-preserving
homomorphism `K →* H` that keeps every `k_j` nontrivial.

Taking `H = G`, a group discriminated by `G` over `G` contains `G`, so it satisfies the same
universal sentences with coefficient names as `G`. Conversely, a finitely generated group `K` over
an equationally Noetherian group `G` that satisfies the same universal sentences as `G` is
discriminated by `G` over `G`. This applies to free groups of finite or countable rank, with their
bases as names: a finitely generated group over such a free group `F` is discriminated by `F`
over `F` if and only if it is universally equivalent to `F` in the language with constants for a
basis.

Every nontrivial torsion-free abelian group has the universal theory of the infinite cyclic group
`ℤ`, in the group language without coefficients. It contains `ℤ`, and universal sentences pass to
subgroups. Conversely, each of its finitely generated subgroups is a free abelian group of finite
rank, hence discriminated by `ℤ`, and a universal sentence holds in a group as soon as it holds
in its finitely generated subgroups.

## Main results

* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.realize_coeff_of_isUniversal`: universal sentences with
  coefficients from `G` pass from `H` to `K`.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.realize_of_isUniversal`: universal sentences without
  coefficients pass from `H` to `K`.
* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.realize_coeff_iff_of_isUniversal`: a group
  discriminated by `G` over `G` satisfies the same universal sentences with coefficients from
  `G` as `G`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_of_forall_isUniversal`: conversely, over an
  equationally Noetherian `H`, a group finitely generated over `G` that satisfies every universal
  sentence true in `H` is discriminated by `H`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_iff_forall_isUniversal`: the two statements combined.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_id_iff_forall_realize_iff`: over an equationally
  Noetherian `G`, a group finitely generated over `G` is discriminated by `G` if and only if it
  satisfies the same universal sentences as `G`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_id_iff_forall_realize_iff_of_freeGroupBasis` and
  `TauCeti.GroupAlgGeom.isDiscriminatedBy_freeGroup_iff_forall_realize_iff`: the same for a group
  with a countable free basis, with constants for the basis, and for `FreeGroup α`.
* `realize_iff_multiplicative_int_of_isMulCommutative_of_isMulTorsionFree_of_isUniversal`, in
  `TauCeti.GroupAlgGeom`: a nontrivial torsion-free abelian group has the universal theory of
  `ℤ`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.3 and §2.6 (the theorem attributed to Remeslennikov).
* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), Theorem 5.1.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.3, Theorem C2.
* V. N. Remeslennikov, *∃-free groups*, Siberian Math. J. 30 (1989).
-/

public section

namespace TauCeti.GroupAlgGeom

open FirstOrder FirstOrder.Language

variable {G K H : Type*} [Group G] [Group K] [Group H] {ιK : G →* K} {ιH : G →* H}
  {A : Type*} {α : Type*} {n : ℕ}

/-- A coefficient-preserving homomorphism commutes with evaluation of group terms with
coefficient names `A`, read through `c : A → G`. -/
private theorem realize_term_comp (f : GHom ιK ιH) (c : A → G)
    {β : Type*} (t : Language.group[[A]].Term β) (w : β → K) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    t.realize (f ∘ w) = f (t.realize w) := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  let g := MonoidHom.coeffGroupLanguageHom (f : K →* H) (ιK ∘ c) (ιH ∘ c)
    fun a => f.map_coeff (c a)
  have hg : ⇑g = ⇑f := MonoidHom.coe_coeffGroupLanguageHom _ _ _ _
  rw [← hg]
  exact HomClass.realize_term g

/-- A quantifier-free formula keeps its truth value under every coefficient-preserving
homomorphism that keeps finitely many nontrivial elements, depending on the assignment,
nontrivial. -/
private theorem exists_finset_realize_comp_iff (c : A → G)
    {φ : Language.group[[A]].BoundedFormula α n} (hφ : φ.IsQF) (v : α → K) (xs : Fin n → K) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    ∃ s : Finset K, (∀ k ∈ s, k ≠ 1) ∧ ∀ f : GHom ιK ιH, (∀ k ∈ s, f k ≠ 1) →
      (φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs) := by
  classical
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  induction hφ with
  | falsum => exact ⟨∅, by simp, fun _ _ => Iff.rfl⟩
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ =>
      -- The only element to keep nontrivial is the quotient of the two sides.
      let x := t₁.realize (Sum.elim v xs) * (t₂.realize (Sum.elim v xs))⁻¹
      refine ⟨({x} : Finset K).filter (· ≠ 1), by simp, fun f hf => ?_⟩
      simp only [BoundedFormula.realize_bdEqual, ← Sum.comp_elim, realize_term_comp]
      refine ⟨fun hfx => ?_, fun hx => by rw [hx]⟩
      by_contra hx
      exact hf x (by simpa [x, mul_inv_eq_one] using hx) (by simp [x, hfx])
    | rel R _ => exact isEmptyElim R
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih₁
    obtain ⟨s₂, hs₂, h₂⟩ := ih₂
    refine ⟨s₁ ∪ s₂, fun k hk => (Finset.mem_union.1 hk).elim (hs₁ k) (hs₂ k), fun f hf => ?_⟩
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp,
      h₁ f fun k hk => hf k (Finset.mem_union_left _ hk),
      h₂ f fun k hk => hf k (Finset.mem_union_right _ hk)]

-- The reduction `FirstOrder.Language.group.universal_iff_no_solution` to word systems fixes one
-- universe for the groups it describes, while `K` and `H` may live in different universes, so
-- the transfer is proved by induction on the formula instead.
/-- If `K` is discriminated by `H` over `G`, a universal formula holds at an assignment in `K`
as soon as it holds at its image under every coefficient-preserving homomorphism to `H`. -/
private theorem realize_of_forall_realize_comp (h : IsDiscriminatedBy ιK ιH) (c : A → G)
    {φ : Language.group[[A]].BoundedFormula α n} (hφ : φ.IsUniversal) (v : α → K)
    (xs : Fin n → K) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    (∀ f : GHom ιK ιH, φ.Realize (f ∘ v) (f ∘ xs)) → φ.Realize v xs := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  induction hφ with
  | of_isQF hφ =>
    intro hf
    obtain ⟨s, hs, hsf⟩ := exists_finset_realize_comp_iff (ιK := ιK) (ιH := ιH) c hφ v xs
    obtain ⟨f, hf'⟩ := (isDiscriminatedBy_def ιK ιH).1 h s hs
    exact (hsf f hf').1 (hf f)
  | all _ ih =>
    intro hf
    rw [BoundedFormula.realize_all]
    intro x
    refine ih (Fin.snoc xs x) fun f => ?_
    rw [Fin.comp_snoc]
    exact (BoundedFormula.realize_all.1 (hf f)) (f x)

namespace IsDiscriminatedBy

/-- If `K` is discriminated by `H` over `G`, every universal sentence of the group language with
coefficient names `A`, read through `c : A → G`, that holds in `H` also holds in `K`. -/
theorem realize_coeff_of_isUniversal (h : IsDiscriminatedBy ιK ιH) (c : A → G)
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsUniversal) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
    H ⊨ σ → K ⊨ σ := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  let : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
  intro hH
  refine realize_of_forall_realize_comp h c hσ default default fun f => ?_
  -- A sentence has no free or bound variables, so every assignment is the default one.
  rwa [Subsingleton.elim (f ∘ default) default, Subsingleton.elim (f ∘ default) default]

/-- If `K` is discriminated by `H` over `G`, every universal sentence of the group language
without coefficients that holds in `H` also holds in `K`. -/
theorem realize_of_isUniversal (h : IsDiscriminatedBy ιK ιH)
    {σ : Language.group.Sentence} (hσ : σ.IsUniversal) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
    H ⊨ σ → K ⊨ σ := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : Language.group.Structure H := TauCeti.Group.structureOfGroup H
  -- Read `σ` in the group language with an empty set of coefficient names.
  let c : Empty → G := Empty.elim
  let : (constantsOn Empty).Structure K := constantsOn.structure (ιK ∘ c)
  let : (constantsOn Empty).Structure H := constantsOn.structure (ιH ∘ c)
  have := h.realize_coeff_of_isUniversal
    (σ := (Language.group.lhomWithConstants Empty).onSentence σ) c (hσ.onBoundedFormula _)
  rwa [LHom.realize_onSentence, LHom.realize_onSentence] at this

/-- If `K` is discriminated by `G` over `G`, then `K` and `G` satisfy the same universal sentences
of the group language with coefficient names `A`, read through `c : A → G`. -/
theorem realize_coeff_iff_of_isUniversal (h : IsDiscriminatedBy ιK (MonoidHom.id G)) (c : A → G)
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsUniversal) :
    letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
    letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
    letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    K ⊨ σ ↔ G ⊨ σ :=
  -- The coefficient map `ιK` is injective, so `G` is discriminated by `K` through `ιK` itself.
  ⟨((IsDiscriminatedBy.self ιK).of_injective (⟨ιK, fun _ => rfl⟩ : GHom (.id G) ιK)
    (h.injective_of_injective Function.injective_id)).realize_coeff_of_isUniversal c hσ,
    h.realize_coeff_of_isUniversal c hσ⟩

end IsDiscriminatedBy

/-! ### The converse for equationally Noetherian groups -/

open Monoid.Coprod

variable {X : Type*}

/-- **Discrimination from universal sentences.** Let `H` be equationally Noetherian over `G`,
let `K` be generated over `G` by the images of finitely many variables `X` through
`π : G[X] →* K`, and let the coefficient names `c : A → G` generate `G`. If every universal
sentence of the group language with coefficient names `A` that holds in `H` also holds in `K`,
then `K` is discriminated by `H` over `G`. -/
theorem isDiscriminatedBy_of_forall_isUniversal [Finite X] (hH : IsEquationallyNoetherian ιH)
    (π : GHom (inl : G →* GX G X) ιK) (hπ : Function.Surjective π) {c : A → G}
    (hc : Subgroup.closure (Set.range c) = ⊤)
    (h : letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
      letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
      letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
      ∀ σ : Language.group[[A]].Sentence, σ.IsUniversal → H ⊨ σ → K ⊨ σ) :
    IsDiscriminatedBy ιK ιH := by
  refine (isDiscriminatedBy_def ιK ιH).2 fun s hs => ?_
  -- A finite part `S₀` of the relations of `K` has the same solutions in `H` as all of them.
  obtain ⟨S₀, hS₀, hfin, hV⟩ := hH.exists_finite ((π : GX G X →* K).ker : Set (GX G X))
  let r := Function.surjInv (EqIneqSystem.toGX_surjective (X := X) hc)
  have hr : ∀ w, EqIneqSystem.toGX X c (r w) = w := Function.surjInv_eq _
  let p := Function.surjInv hπ
  -- The equations `S₀` and the inequations `k ≠ 1` for `k ∈ s`, as words in `X ⊕ A`.
  let S : EqIneqSystem X A := ⟨hfin.toFinset.toList.map r, (s.toList.map p).map r⟩
  -- The generators of `K` solve `S`; hence so does some tuple `u` of `H`.
  have h₀ (w : GX G X) : eval ιK (homEquiv ιK π) w = π w := by
    rw [← coe_evalGHom, ← homEquiv_symm_apply, Equiv.symm_apply_apply]
  have hK : S.IsSolution (homEquiv ιK π) (ιK ∘ c) := by
    simp only [S, EqIneqSystem.isSolution_iff, ← EqIneqSystem.eval_toGX, List.forall_mem_map,
      Finset.mem_toList, Set.Finite.mem_toFinset, hr, h₀]
    exact ⟨fun w hw => hS₀ hw, fun k hk => by simpa [p, Function.surjInv_eq hπ] using hs k hk⟩
  obtain ⟨u, hu⟩ := EqIneqSystem.exists_isSolution_of_forall_isUniversal h ⟨_, hK⟩
  simp only [S, EqIneqSystem.isSolution_iff, ← EqIneqSystem.eval_toGX, List.forall_mem_map,
    Finset.mem_toList, Set.Finite.mem_toFinset, hr] at hu
  -- The tuple `u` solves every relation of `K`, so evaluation at it factors through `π`.
  obtain ⟨φ, hφ⟩ := GX.exists_gHom_apply_eq_eval hπ (v := u) (by rw [← hV]; exact mem_V.2 hu.1)
  refine ⟨φ, fun k hk => ?_⟩
  rw [← Function.surjInv_eq hπ k, hφ]
  exact hu.2 k hk

/-- Over an equationally Noetherian group `H`, a group `K` generated over `G` by the images of
finitely many variables is discriminated by `H` if and only if every universal sentence of the
group language with coefficient names `A` that holds in `H` also holds in `K`; here the names
`c : A → G` generate `G`. -/
theorem isDiscriminatedBy_iff_forall_isUniversal [Finite X] (hH : IsEquationallyNoetherian ιH)
    (π : GHom (inl : G →* GX G X) ιK) (hπ : Function.Surjective π) {c : A → G}
    (hc : Subgroup.closure (Set.range c) = ⊤) : IsDiscriminatedBy ιK ιH ↔
      letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
      letI : Language.group.Structure H := TauCeti.Group.structureOfGroup H
      letI : (Language.constantsOn A).Structure H := Language.constantsOn.structure (ιH ∘ c)
      ∀ σ : Language.group[[A]].Sentence, σ.IsUniversal → H ⊨ σ → K ⊨ σ :=
  ⟨fun h _ hσ => h.realize_coeff_of_isUniversal c hσ,
    isDiscriminatedBy_of_forall_isUniversal hH π hπ hc⟩

/-- **Universal equivalence with the coefficient group.** Over a group `G` that is equationally
Noetherian over itself, a group `K` generated over `G` by the images of finitely many variables is
discriminated by `G` over `G` if and only if `K` and `G` satisfy the same universal sentences of
the group language with coefficient names `A`; here the names `c : A → G` generate `G`. -/
theorem isDiscriminatedBy_id_iff_forall_realize_iff [Finite X]
    (hG : IsEquationallyNoetherian (MonoidHom.id G)) (π : GHom (inl : G →* GX G X) ιK)
    (hπ : Function.Surjective π) {c : A → G} (hc : Subgroup.closure (Set.range c) = ⊤) :
    IsDiscriminatedBy ιK (MonoidHom.id G) ↔
      letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
      letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
      letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
      ∀ σ : Language.group[[A]].Sentence, σ.IsUniversal → (K ⊨ σ ↔ G ⊨ σ) :=
  ⟨fun h _ hσ => h.realize_coeff_iff_of_isUniversal c hσ,
    fun h => isDiscriminatedBy_of_forall_isUniversal hG π hπ hc fun σ hσ => (h σ hσ).2⟩

/-- **Remeslennikov's theorem.** Let `F` be a group with a countable free basis `b : α → F`, such
as a free group of finite rank, and let `K` be generated over `F` by the images of finitely many
variables. Then `K` is discriminated by `F` over `F` if and only if `K` and `F` satisfy the same
universal sentences of the group language with constants for the basis `b`. -/
theorem isDiscriminatedBy_id_iff_forall_realize_iff_of_freeGroupBasis {F : Type*} [Group F]
    [Countable α] (b : FreeGroupBasis α F) {ιK : F →* K} [Finite X]
    (π : GHom (inl : F →* GX F X) ιK) (hπ : Function.Surjective π) :
    IsDiscriminatedBy ιK (MonoidHom.id F) ↔
      letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn α).Structure K := Language.constantsOn.structure (ιK ∘ b)
      letI : Language.group.Structure F := TauCeti.Group.structureOfGroup F
      letI : (Language.constantsOn α).Structure F := Language.constantsOn.structure b
      ∀ σ : Language.group[[α]].Sentence, σ.IsUniversal → (K ⊨ σ ↔ F ⊨ σ) :=
  isDiscriminatedBy_id_iff_forall_realize_iff (isEquationallyNoetherian_of_freeGroupBasis _ b) π hπ
    b.closure_range_eq_top

/-- **Remeslennikov's theorem** for the free group on a countable set `α`, with constants for
its basis: a group `K` generated over `F(α)` by the images of finitely many variables is
discriminated by `F(α)` over `F(α)` if and only if `K` and `F(α)` satisfy the same universal
sentences of the group language with constants for `α`. -/
theorem isDiscriminatedBy_freeGroup_iff_forall_realize_iff [Countable α]
    {ιK : FreeGroup α →* K} [Finite X] (π : GHom (inl : FreeGroup α →* GX (FreeGroup α) X) ιK)
    (hπ : Function.Surjective π) : IsDiscriminatedBy ιK (MonoidHom.id (FreeGroup α)) ↔
      letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn α).Structure K :=
        Language.constantsOn.structure (ιK ∘ FreeGroup.of)
      letI : Language.group.Structure (FreeGroup α) := TauCeti.Group.structureOfGroup _
      letI : (Language.constantsOn α).Structure (FreeGroup α) :=
        Language.constantsOn.structure FreeGroup.of
      ∀ σ : Language.group[[α]].Sentence, σ.IsUniversal → (K ⊨ σ ↔ FreeGroup α ⊨ σ) :=
  isDiscriminatedBy_id_iff_forall_realize_iff_of_freeGroupBasis (.ofFreeGroup α) π hπ

section TorsionFree

attribute [local instance] TauCeti.Group.structureOfGroup

/-- A nontrivial torsion-free abelian group has the universal theory of the infinite cyclic group
`ℤ`. -/
theorem realize_iff_multiplicative_int_of_isMulCommutative_of_isMulTorsionFree_of_isUniversal
    [IsMulCommutative G] [IsMulTorsionFree G] [Nontrivial G] {σ : Language.group.Sentence}
    (hσ : σ.IsUniversal) : G ⊨ σ ↔ Multiplicative ℤ ⊨ σ := by
  classical
  refine ⟨fun hG => ?_, fun hZ => group.realize_of_isUniversal_of_forall_closure hσ fun S => ?_⟩
  · -- `ℤ` embeds into `G` through the powers of a nontrivial element.
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    exact (zpowersHom G g).realize_of_isUniversal_of_injective
      (fun a b h => by simpa [hg] using h) hσ hG
  · -- A finitely generated subgroup is isomorphic to some `ℤᵏ`, which is discriminated by `ℤ`.
    obtain ⟨k, -, ⟨e⟩⟩ := Subgroup.exists_mulEquiv_closure_of_pairwise_commute
      (s := S) fun a _ b _ _ => mul_comm' a b
    exact (e.realize_sentence_iff σ).2
      ((isDiscriminatedBy_multiplicative_pi_int (Fin k)).realize_of_isUniversal hσ hZ)

end TorsionFree

end TauCeti.GroupAlgGeom
