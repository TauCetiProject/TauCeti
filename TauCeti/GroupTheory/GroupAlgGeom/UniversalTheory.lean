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
public import Mathlib.ModelTheory.Complexity

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

Taking `H = G`, a finitely generated group `K` over an equationally Noetherian group `G` is
discriminated by `G` over `G` exactly when `K` and `G` satisfy the same universal sentences with
coefficient names. This applies to free groups of finite or countable rank, with their bases as
names: a finitely generated group over such a free group `F` is discriminated by `F` over `F` if
and only if it is universally equivalent to `F` in the language with constants for a basis.

## Main results

* `TauCeti.GroupAlgGeom.IsDiscriminatedBy.realize_of_isUniversal`: universal sentences with
  coefficients from `G` pass from `H` to `K`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_of_forall_isUniversal`: conversely, over an
  equationally Noetherian `H`, a group finitely generated over `G` that satisfies every universal
  sentence true in `H` is discriminated by `H`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_iff_forall_isUniversal`: the two statements combined.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_id_iff_forall_realize_iff`: over an equationally
  Noetherian `G`, a group finitely generated over `G` is discriminated by `G` if and only if it
  satisfies the same universal sentences as `G`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_freeGroup_iff_forall_realize_iff`: the same for a free
  group of finite or countable rank, with constants for its basis.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.3 and §2.6 (the theorem attributed to Remeslennikov).
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
  have hg : ⇑g = ⇑f := funext fun x => MonoidHom.coeffGroupLanguageHom_apply _ _ _ _ x
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
    | rel R _ =>
      -- The coefficient extension has two empty relation-symbol summands.
      change Empty ⊕ Empty at R
      rcases R with r | r <;> exact isEmptyElim r
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
theorem realize_of_isUniversal (h : IsDiscriminatedBy ιK ιH) (c : A → G)
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

end IsDiscriminatedBy

/-! ### The converse for equationally Noetherian groups -/

open Monoid.Coprod

variable {X Y : Type*}

/-- Words in the letters `Y ⊕ A`, read in `G[X]` through `e : Y → X` on the variables and through
`c : A → G` on the coefficient names. -/
-- For `G = F(A)`, `c = FreeGroup.of` and `e = id` this is `EqIneqSystem.toGX`.
private def wordHom (e : Y → X) (c : A → G) : FreeGroup (Y ⊕ A) →* GX G X :=
  FreeGroup.lift (Sum.elim (fun y => inr (FreeGroup.of (e y))) (fun a => inl (c a)))

/-- Evaluating the value of a word in `G[X]` evaluates the word at the variables and names. -/
private theorem eval_wordHom {M : Type*} [Group M] (e : Y → X) (c : A → G) (μ : G →* M) (v : X → M)
    (u : FreeGroup (Y ⊕ A)) : eval μ v (wordHom e c u) = EqIneqSystem.eval (v ∘ e) (μ ∘ c) u := by
  rw [← MonoidHom.comp_apply, EqIneqSystem.eval_eq_lift]
  congr 1
  ext (y | a) <;> simp [wordHom]

/-- If `e` is surjective and the names `c` generate `G`, every element of `G[X]` is the value of
a word in the letters `Y ⊕ A`. -/
private theorem wordHom_surjective {e : Y → X} (he : Function.Surjective e) {c : A → G}
    (hc : Subgroup.closure (Set.range c) = ⊤) : Function.Surjective (wordHom e c) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← range_inl_sup_range_inr]
  refine sup_le ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hc, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨FreeGroup.of (Sum.inr a), by simp [wordHom]⟩
  · rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := he x
    exact ⟨FreeGroup.of (Sum.inl y), by simp [wordHom]⟩

/-- Rewriting the equations `E` and the inequations `I` of `G[X]` as words in the letters `Y ⊕ A`
does not change their solutions. -/
private theorem isSolution_map_iff {M : Type*} [Group M] {e : Y → X} {c : A → G}
    {r : GX G X → FreeGroup (Y ⊕ A)} (hr : ∀ w, wordHom e c (r w) = w) (E I : List (GX G X))
    (μ : G →* M) (v : X → M) :
    (⟨E.map r, I.map r⟩ : EqIneqSystem Y A).IsSolution (v ∘ e) (μ ∘ c) ↔
      (∀ w ∈ E, eval μ v w = 1) ∧ ∀ w ∈ I, eval μ v w ≠ 1 := by
  simp [EqIneqSystem.isSolution_iff, ← eval_wordHom, hr]

/-- A point of `H` at which every relation of `K`, presented over `G` by `π`, vanishes defines a
coefficient-preserving homomorphism `K →* H` through which evaluation at the point factors. -/
private theorem exists_gHom_apply_eq_eval {π : GHom (inl : G →* GX G X) ιK}
    (hπ : Function.Surjective π) {v : X → H}
    (hv : v ∈ V ιH ((π : GX G X →* K).ker : Set (GX G X))) :
    ∃ φ : GHom ιK ιH, ∀ w, φ (π w) = eval ιH v w := by
  obtain ⟨ψ, hψ, hψπ⟩ := GX.exists_bijective_gHom_of_eq_ker π hπ rfl
  refine ⟨(GX.quotientEvalGHom v hv).comp (ψ.symmOfBijective hψ), fun w => ?_⟩
  rw [GHom.coe_comp, Function.comp_apply, ← hψπ, GHom.symmOfBijective_apply_apply,
    GX.quotientEvalGHom_mk]

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
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  -- A finite part `S₀` of the relations of `K` has the same solutions in `H` as all of them.
  obtain ⟨S₀, hS₀, hfin, hV⟩ := hH.exists_finite ((π : GX G X →* K).ker : Set (GX G X))
  let r := Function.surjInv (wordHom_surjective e.symm.surjective hc)
  have hr : ∀ w, wordHom e.symm c (r w) = w := Function.surjInv_eq _
  let p := Function.surjInv hπ
  -- The generators of `K` solve the equations `S₀` and the inequations `k ≠ 1` for `k ∈ s`,
  -- written as words in `Fin n ⊕ A`; hence so does some tuple of `H`.
  have hK : ∃ u : Fin n → K, (⟨hfin.toFinset.toList.map r, (s.toList.map p).map r⟩ :
      EqIneqSystem (Fin n) A).IsSolution u (ιK ∘ c) := by
    have h₀ (w : GX G X) : eval ιK (homEquiv ιK π) w = π w := by
      rw [← coe_evalGHom, ← homEquiv_symm_apply, Equiv.symm_apply_apply]
    refine ⟨homEquiv ιK π ∘ e.symm, (isSolution_map_iff hr _ _ ιK _).2 ⟨fun w hw => ?_, ?_⟩⟩
    · rw [h₀]
      exact hS₀ ((Set.Finite.mem_toFinset hfin).1 (Finset.mem_toList.1 hw))
    · simpa [h₀, p, Function.surjInv_eq hπ] using hs
  obtain ⟨u, hu⟩ := EqIneqSystem.exists_isSolution_of_forall_isUniversal h hK
  have hu' := (isSolution_map_iff hr _ _ ιH (u ∘ e)).1
    (by rwa [Function.comp_assoc, e.self_comp_symm, Function.comp_id])
  -- The tuple `u ∘ e` solves every relation of `K`, so evaluation at it factors through `π`.
  obtain ⟨φ, hφ⟩ := exists_gHom_apply_eq_eval hπ (v := u ∘ e) <| by
    rw [← hV]
    exact mem_V.2 fun w hw => hu'.1 w (Finset.mem_toList.2 ((Set.Finite.mem_toFinset hfin).2 hw))
  refine ⟨φ, fun k hk => ?_⟩
  rw [← Function.surjInv_eq hπ k, hφ]
  exact hu'.2 (p k) (by simpa using ⟨k, hk, rfl⟩)

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
  ⟨fun h _ hσ => h.realize_of_isUniversal c hσ,
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
      ∀ σ : Language.group[[A]].Sentence, σ.IsUniversal → (K ⊨ σ ↔ G ⊨ σ) := by
  let : Language.group.Structure K := TauCeti.Group.structureOfGroup K
  let : (Language.constantsOn A).Structure K := Language.constantsOn.structure (ιK ∘ c)
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  refine ⟨fun h σ hσ => ⟨fun hK => ?_, h.realize_of_isUniversal c hσ⟩,
    fun h => isDiscriminatedBy_of_forall_isUniversal hG π hπ hc fun σ hσ => (h σ hσ).2⟩
  -- A coefficient-preserving retraction `K → G` makes `ιK` injective, so `G` is discriminated
  -- by `K` through `ιK` itself.
  obtain ⟨φ, -⟩ := (isDiscriminatedBy_def _ _).1 h ∅ (by simp)
  have hι : Function.Injective ιK := Function.LeftInverse.injective (g := φ) φ.map_coeff
  exact ((IsDiscriminatedBy.self ιK).of_injective (⟨ιK, fun _ => rfl⟩ : GHom (.id G) ιK) hι
    ).realize_of_isUniversal c hσ hK

/-- **Remeslennikov's theorem.** Let `F` be the free group on a countable set `α`, for instance
of finite rank, and let `K` be generated over `F` by the images of finitely many variables. Then
`K` is discriminated by `F` over `F` if and only if `K` and `F` satisfy the same universal
sentences of the group language with constants for the basis `α`. -/
theorem isDiscriminatedBy_freeGroup_iff_forall_realize_iff {α : Type*} [Countable α]
    {ιK : FreeGroup α →* K} [Finite X] (π : GHom (inl : FreeGroup α →* GX (FreeGroup α) X) ιK)
    (hπ : Function.Surjective π) : IsDiscriminatedBy ιK (MonoidHom.id (FreeGroup α)) ↔
      letI : Language.group.Structure K := TauCeti.Group.structureOfGroup K
      letI : (Language.constantsOn α).Structure K :=
        Language.constantsOn.structure (ιK ∘ FreeGroup.of)
      letI : Language.group.Structure (FreeGroup α) := TauCeti.Group.structureOfGroup _
      letI : (Language.constantsOn α).Structure (FreeGroup α) :=
        Language.constantsOn.structure FreeGroup.of
      ∀ σ : Language.group[[α]].Sentence, σ.IsUniversal → (K ⊨ σ ↔ FreeGroup α ⊨ σ) :=
  isDiscriminatedBy_id_iff_forall_realize_iff (isEquationallyNoetherian_freeGroup _) π hπ
    (FreeGroup.closure_range_of α)

end TauCeti.GroupAlgGeom
