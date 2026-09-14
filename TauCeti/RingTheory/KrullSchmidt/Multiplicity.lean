/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Map
public import TauCeti.RingTheory.KrullSchmidt.Existence
public import TauCeti.RingTheory.KrullSchmidt.Uniqueness

/-!
# Krull-Schmidt multiplicities of an indecomposable module

A module of finite length is an internal direct sum of finitely many indecomposable submodules,
and the Krull-Schmidt theorem matches any two such decompositions summand by summand.  Counting
how often a fixed module `N` occurs among the summands is therefore an invariant of the module
alone: the **multiplicity** of `N` in `M`.  This file builds that count.

It is the direct-sum analogue of the Jordan-Hölder count
`TauCeti.jordanHolderMultiplicity`, and is well defined for the same reason: the existence theorem
`TauCeti.exists_isInternal_isIndecomposableModule` produces a decomposition, and the uniqueness
theorem `TauCeti.exists_equiv_linearEquiv_of_finset` matches any two of them by a bijection under
which corresponding summands are isomorphic, so the two counts agree.

The count is taken with `Nat.card`, over the subtype of members of the decomposition that are
copies of `N`, so no decidability of "is a copy of `N`" is needed in the definition.

Multiplicity is additive on direct sums, which is what makes it a coordinate on a Grothendieck
group of modules: the classes of the indecomposable modules are independent because their
multiplicities are the Kronecker delta.

## Main definitions

* `TauCeti.decompositionMultiplicity`: the number of members of a finite set of submodules that
  are copies of a given module.
* `TauCeti.indecomposableMultiplicity`: the multiplicity of a module `N` among the indecomposable
  summands of a module `M` of finite length.

## Main results

* `TauCeti.decompositionMultiplicity_eq_of_isInternal`: **the count is a Krull-Schmidt
  invariant** — two indecomposable decompositions contain the same number of copies of every
  module.  This is what makes `TauCeti.indecomposableMultiplicity` well defined, and
  `TauCeti.decompositionMultiplicity_eq_indecomposableMultiplicity` says that *every*
  indecomposable decomposition computes it.
* `TauCeti.indecomposableMultiplicity_eq_of_linearEquiv` and
  `TauCeti.indecomposableMultiplicity_congr`: the multiplicity depends on each of the two modules
  only through its isomorphism class.
* `TauCeti.isIndecomposableModule_of_indecomposableMultiplicity_ne_zero`: only an indecomposable
  module occurs, and `TauCeti.indecomposableMultiplicity_self` and
  `TauCeti.indecomposableMultiplicity_eq_zero_of_isEmpty_linearEquiv`: an indecomposable module
  occurs exactly once in itself and not at all in a nonisomorphic indecomposable module.
* `TauCeti.indecomposableMultiplicity_prod`: **multiplicity is additive on direct sums**, with
  `TauCeti.indecomposableMultiplicity_eq_add_of_isCompl` the internal form.

## References

* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory
  of Associative Algebras I*, Chapter I, Section 4.
-/

public section

namespace TauCeti

universe u v v' w w'

variable {A : Type u} [Ring A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {M' : Type v'} [AddCommGroup M'] [Module A M']
variable {N : Type w} [AddCommGroup N] [Module A N]
variable {N' : Type w'} [AddCommGroup N'] [Module A N']

/-! ### Counting the copies of a module in a finite set of submodules -/

/-- The number of members of the finite set of submodules `s` that are copies of `N`.  When `s` is
a decomposition of `M` into indecomposable submodules this is the multiplicity of `N` in `M`, by
`TauCeti.decompositionMultiplicity_eq_indecomposableMultiplicity`. -/
noncomputable def decompositionMultiplicity (s : Finset (Submodule A M)) (N : Type w)
    [AddCommGroup N] [Module A N] : ℕ :=
  Nat.card {P : Submodule A M // P ∈ s ∧ Nonempty (↥P ≃ₗ[A] N)}

/-- The defining equation of `TauCeti.decompositionMultiplicity`: it is the number of members of
`s` admitting a linear equivalence with `N`.  This is what introduces and eliminates the count,
whose body is not exposed to importing modules. -/
theorem decompositionMultiplicity_def (s : Finset (Submodule A M)) :
    decompositionMultiplicity s N =
      Nat.card {P : Submodule A M // P ∈ s ∧ Nonempty (↥P ≃ₗ[A] N)} :=
  (rfl)

/-- The count, as the cardinality of the corresponding `Finset.filter`.  The definition itself is
taken with `Nat.card` over a subtype, so that it needs no decidability hypothesis; this is the form
in which the counting arguments run. -/
theorem decompositionMultiplicity_eq_card_filter (s : Finset (Submodule A M))
    (N : Type w) [AddCommGroup N] [Module A N]
    [DecidablePred fun P : Submodule A M ↦ Nonempty (↥P ≃ₗ[A] N)] :
    decompositionMultiplicity s N =
      (s.filter fun P : Submodule A M ↦ Nonempty (↥P ≃ₗ[A] N)).card :=
  Nat.subtype_card _ fun _ ↦ Finset.mem_filter

/-- The count depends on `N` only through its isomorphism class. -/
theorem decompositionMultiplicity_congr (s : Finset (Submodule A M)) (e : N ≃ₗ[A] N') :
    decompositionMultiplicity s N = decompositionMultiplicity s N' :=
  Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦
    and_congr_right fun _ ↦ ⟨fun h ↦ h.map (·.trans e), fun h ↦ h.map (·.trans e.symm)⟩

/-- **The count is a Krull-Schmidt invariant**: two decompositions of a module of finite length
into indecomposable submodules contain the same number of copies of every module. -/
theorem decompositionMultiplicity_eq_of_isInternal (hM : IsFiniteLength A M)
    {s t : Finset (Submodule A M)} (hs : ∀ P ∈ s, IsIndecomposableModule A P)
    (hsi : DirectSum.IsInternal fun P : s ↦ (P : Submodule A M))
    (ht : ∀ P ∈ t, IsIndecomposableModule A P)
    (hti : DirectSum.IsInternal fun P : t ↦ (P : Submodule A M)) :
    decompositionMultiplicity s N = decompositionMultiplicity t N := by
  obtain ⟨e, he⟩ := exists_equiv_linearEquiv_of_finset hM hs hsi ht hti
  refine Nat.card_congr <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) _).symm.trans <|
      (Equiv.subtypeEquiv e fun P ↦ ?_).trans (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ t) _)
  exact ⟨fun h ↦ h.map ((he P).some.symm.trans ·), fun h ↦ h.map ((he P).some.trans ·)⟩

/-- The counts over two disjoint finite sets of submodules add. -/
theorem decompositionMultiplicity_union [DecidableEq (Submodule A M)]
    {s t : Finset (Submodule A M)} (hst : Disjoint s t) :
    decompositionMultiplicity (s ∪ t) N =
      decompositionMultiplicity s N + decompositionMultiplicity t N := by
  classical
  rw [decompositionMultiplicity_eq_card_filter, decompositionMultiplicity_eq_card_filter,
    decompositionMultiplicity_eq_card_filter, Finset.filter_union,
    Finset.card_union_of_disjoint ((Finset.disjoint_filter_filter hst))]

/-! ### Transport along an injective linear map -/

/-- Pushing a finite set of submodules forward along an injective linear map does not change how
many of its members are copies of `N`. -/
theorem decompositionMultiplicity_image [DecidableEq (Submodule A M')] {f : M →ₗ[A] M'}
    (hf : Function.Injective f) (s : Finset (Submodule A M)) :
    decompositionMultiplicity (s.image (Submodule.map f)) N = decompositionMultiplicity s N := by
  classical
  rw [decompositionMultiplicity_eq_card_filter, decompositionMultiplicity_eq_card_filter,
    Finset.filter_image,
    Finset.card_image_of_injective _ (Submodule.map_injective_of_injective hf)]
  refine congrArg _ (Finset.filter_congr fun P _ ↦ ?_)
  exact ⟨fun h ↦ h.map ((Submodule.equivMapOfInjective f hf P).trans ·),
    fun h ↦ h.map ((Submodule.equivMapOfInjective f hf P).symm.trans ·)⟩

/-! ### The multiplicity of an indecomposable module -/

variable (A M) in
/-- **The multiplicity of `N` in `M`**: the number of copies of `N` among the summands of a
decomposition of the finite-length module `M` into indecomposable submodules.  Every such
decomposition computes it, by
`TauCeti.decompositionMultiplicity_eq_indecomposableMultiplicity`. -/
noncomputable def indecomposableMultiplicity [IsArtinian A M]
    (N : Type w) [AddCommGroup N] [Module A N] : ℕ :=
  decompositionMultiplicity (exists_isInternal_isIndecomposableModule (A := A) (M := M)).choose N

variable [IsNoetherian A M] [IsArtinian A M]

/-- **Every indecomposable decomposition computes the multiplicity.** -/
theorem decompositionMultiplicity_eq_indecomposableMultiplicity {s : Finset (Submodule A M)}
    (hs : ∀ P ∈ s, IsIndecomposableModule A P)
    (hsi : DirectSum.IsInternal fun P : s ↦ (P : Submodule A M)) :
    decompositionMultiplicity s N = indecomposableMultiplicity A M N :=
  have h := (exists_isInternal_isIndecomposableModule (A := A) (M := M)).choose_spec
  decompositionMultiplicity_eq_of_isInternal
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩) hs hsi h.1 h.2

/-- An independent, spanning finite set of indecomposable submodules computes the multiplicity.
This is `TauCeti.decompositionMultiplicity_eq_indecomposableMultiplicity` in the packaging that
`TauCeti.exists_finset_isIndecomposableModule_supIndep_sup_eq` produces. -/
theorem decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep
    {s : Finset (Submodule A M)} (hs : ∀ P ∈ s, IsIndecomposableModule A P)
    (hsi : s.SupIndep id) (hsup : s.sup id = ⊤) :
    decompositionMultiplicity s N = indecomposableMultiplicity A M N :=
  decompositionMultiplicity_eq_indecomposableMultiplicity hs <|
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨hsi.independent, by simpa only [Finset.sup_eq_iSup, iSup_subtype, id_eq] using hsup⟩

omit [IsNoetherian A M] in
/-- The multiplicity depends on `N` only through its isomorphism class. -/
theorem indecomposableMultiplicity_congr (e : N ≃ₗ[A] N') :
    indecomposableMultiplicity A M N = indecomposableMultiplicity A M N' :=
  decompositionMultiplicity_congr _ e

/-- **The multiplicity depends on the ambient module only through its isomorphism class.** -/
theorem indecomposableMultiplicity_eq_of_linearEquiv (f : M ≃ₗ[A] M') :
    indecomposableMultiplicity A M N =
      @indecomposableMultiplicity A _ M' _ _ (isArtinian_of_linearEquiv f) N _ _ := by
  classical
  let _ : IsNoetherian A M' := isNoetherian_of_linearEquiv f
  let _ : IsArtinian A M' := isArtinian_of_linearEquiv f
  obtain ⟨s, hs, hsi, hsup⟩ :=
    exists_finset_isIndecomposableModule_supIndep_sup_eq (A := A) (⊤ : Submodule A M)
  rw [← decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep hs hsi hsup,
    ← decompositionMultiplicity_image (N := N) f.injective s,
    decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep ?_
      (Submodule.supIndep_image_map f.injective hsi) ?_]
  · rintro _ hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact (hs P hP).of_linearEquiv (Submodule.equivMapOfInjective _ f.injective P)
  · rw [Finset.sup_image]
    simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup,
      Submodule.map_top, LinearMap.range_eq_top.mpr f.surjective] using
      congrArg (Submodule.map f.toLinearMap) hsup

/-- A zero module has no indecomposable summands. -/
@[simp]
theorem indecomposableMultiplicity_eq_zero_of_subsingleton [Subsingleton M] :
    indecomposableMultiplicity A M N = 0 := by
  rw [← decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep (s := ∅)
      (by simp) (Finset.supIndep_empty _) (by simp [Subsingleton.elim (⊥ : Submodule A M) ⊤]),
    decompositionMultiplicity_def]
  simp

omit [IsNoetherian A M] in
/-- **Only an indecomposable module has a nonzero multiplicity**: the summands counted are
indecomposable by construction. -/
theorem isIndecomposableModule_of_indecomposableMultiplicity_ne_zero
    (h : indecomposableMultiplicity A M N ≠ 0) : IsIndecomposableModule A N := by
  have hne : Nonempty {P : Submodule A M //
      P ∈ (exists_isInternal_isIndecomposableModule (A := A) (M := M)).choose ∧
        Nonempty (↥P ≃ₗ[A] N)} := by
    rw [← not_isEmpty_iff]
    exact fun _ ↦ h (by rw [indecomposableMultiplicity, decompositionMultiplicity_def]; simp)
  obtain ⟨P, hP, ⟨e⟩⟩ := hne
  exact IsIndecomposableModule.of_linearEquiv
    ((exists_isInternal_isIndecomposableModule (A := A) (M := M)).choose_spec.1 P hP) e

section Indecomposable

variable (hM : IsIndecomposableModule A M)
include hM

/-- The one-member decomposition of an indecomposable module. -/
private theorem decompositionMultiplicity_top :
    decompositionMultiplicity {(⊤ : Submodule A M)} N = indecomposableMultiplicity A M N :=
  decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep
    (by simpa using hM.of_linearEquiv Submodule.topEquiv.symm)
    (Finset.supIndep_singleton _ _) (by simp)

/-- **An indecomposable module occurs exactly once in itself.** -/
theorem indecomposableMultiplicity_self (e : M ≃ₗ[A] N) :
    indecomposableMultiplicity A M N = 1 := by
  rw [← decompositionMultiplicity_top hM, decompositionMultiplicity_def]
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun P Q ↦ Subtype.ext ?_⟩,
    ⟨⟨⊤, by simp, ⟨Submodule.topEquiv.trans e⟩⟩⟩⟩
  rw [Finset.mem_singleton.mp P.2.1, Finset.mem_singleton.mp Q.2.1]

/-- **A nonisomorphic module does not occur in an indecomposable module.** -/
theorem indecomposableMultiplicity_eq_zero_of_isEmpty_linearEquiv (he : IsEmpty (M ≃ₗ[A] N)) :
    indecomposableMultiplicity A M N = 0 := by
  rw [← decompositionMultiplicity_top hM, decompositionMultiplicity_def]
  have : IsEmpty {P : Submodule A M // P ∈ ({⊤} : Finset (Submodule A M)) ∧
      Nonempty (↥P ≃ₗ[A] N)} :=
    ⟨fun P ↦ he.elim (Submodule.topEquiv.symm.trans
      (by rw [← Finset.mem_singleton.mp P.2.1]; exact P.2.2.some))⟩
  exact Nat.card_of_isEmpty

end Indecomposable

/-! ### Additivity -/

/-- **Multiplicity is additive on direct sums.** -/
theorem indecomposableMultiplicity_prod [IsNoetherian A M'] [IsArtinian A M'] :
    indecomposableMultiplicity A (M × M') N =
      indecomposableMultiplicity A M N + indecomposableMultiplicity A M' N := by
  classical
  obtain ⟨s, hs, hsi, hsup⟩ :=
    exists_finset_isIndecomposableModule_supIndep_sup_eq (A := A) (⊤ : Submodule A M)
  obtain ⟨t, ht, hti, htup⟩ :=
    exists_finset_isIndecomposableModule_supIndep_sup_eq (A := A) (⊤ : Submodule A M')
  set s' := s.image (Submodule.map (LinearMap.inl A M M')) with hs'
  set t' := t.image (Submodule.map (LinearMap.inr A M M')) with ht'
  have hsup' : s'.sup id = LinearMap.range (LinearMap.inl A M M') := by
    rw [hs', Finset.sup_image]
    simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup,
      Submodule.map_top] using congrArg (Submodule.map (LinearMap.inl A M M')) hsup
  have htup' : t'.sup id = LinearMap.range (LinearMap.inr A M M') := by
    rw [ht', Finset.sup_image]
    simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup,
      Submodule.map_top] using congrArg (Submodule.map (LinearMap.inr A M M')) htup
  have hind : ∀ P ∈ s' ∪ t', IsIndecomposableModule A P := by
    rintro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      exact (hs P hP).of_linearEquiv
        (Submodule.equivMapOfInjective _ LinearMap.inl_injective P)
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      exact (ht P hP).of_linearEquiv
        (Submodule.equivMapOfInjective _ LinearMap.inr_injective P)
  have hdisj : Disjoint (s'.sup id) (t'.sup id) := by
    rw [hsup', htup']
    exact LinearMap.isCompl_range_inl_inr.disjoint
  have hfdisj : Disjoint s' t' := by
    refine Finset.disjoint_left.mpr fun Q hQs hQt ↦ ?_
    have hQbot : Q = ⊥ := by
      refine le_bot_iff.mp (disjoint_iff.mp hdisj ▸ le_inf ?_ ?_)
      · exact Finset.le_sup (f := id) hQs
      · exact Finset.le_sup (f := id) hQt
    exact (Submodule.nontrivial_iff_ne_bot.mp (hind Q (Finset.mem_union_left _ hQs)).nontrivial)
      hQbot
  rw [← decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep hind
      ((Submodule.supIndep_image_map LinearMap.inl_injective hsi).union
        (Submodule.supIndep_image_map LinearMap.inr_injective hti) hdisj)
      (by rw [Finset.sup_union, hsup', htup']; exact LinearMap.sup_range_inl_inr),
    decompositionMultiplicity_union hfdisj, hs', ht',
    decompositionMultiplicity_image LinearMap.inl_injective,
    decompositionMultiplicity_image LinearMap.inr_injective,
    decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep hs hsi hsup,
    decompositionMultiplicity_eq_indecomposableMultiplicity_of_supIndep ht hti htup]

/-- **Multiplicity is additive on an internal direct sum decomposition into two summands.** -/
theorem indecomposableMultiplicity_eq_add_of_isCompl {T T' : Submodule A M} (h : IsCompl T T') :
    indecomposableMultiplicity A M N =
      indecomposableMultiplicity A T N + indecomposableMultiplicity A T' N := by
  rw [← indecomposableMultiplicity_prod (M := T) (M' := T') (N := N),
    indecomposableMultiplicity_eq_of_linearEquiv (M' := M) (N := N)
      (Submodule.prodEquivOfIsCompl T T' h)]

/-- **Multiplicity is additive on a split short exact sequence** `0 → M₁ → M → M₃ → 0`, the
splitting being given by a right inverse `σ` of the surjection. -/
theorem indecomposableMultiplicity_eq_add_of_exact_of_rightInverse
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁] [IsNoetherian A M₁] [IsArtinian A M₁]
    {M₃ : Type*} [AddCommGroup M₃] [Module A M₃] [IsNoetherian A M₃] [IsArtinian A M₃]
    {f : M₁ →ₗ[A] M} {g : M →ₗ[A] M₃} {σ : M₃ →ₗ[A] M} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hσ : Function.LeftInverse g σ) :
    indecomposableMultiplicity A M N =
      indecomposableMultiplicity A M₁ N + indecomposableMultiplicity A M₃ N := by
  have hσinj : Function.Injective σ := hσ.injective
  set pr : M →ₗ[A] LinearMap.range σ :=
    LinearMap.codRestrict (LinearMap.range σ) (σ ∘ₗ g) (fun x ↦ ⟨g x, rfl⟩) with hpr
  have hproj : ∀ x : LinearMap.range σ, pr x = x := by
    rintro ⟨_, z, rfl⟩
    exact Subtype.ext (congrArg σ (hσ z))
  have hker : LinearMap.ker pr = LinearMap.range f := by
    have hkr : LinearMap.ker pr = LinearMap.ker (σ ∘ₗ g) := by
      rw [hpr]; exact LinearMap.ker_codRestrict _ _ _
    rw [hkr, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hσinj, Submodule.comap_bot,
      hfg.linearMap_ker_eq]
  rw [indecomposableMultiplicity_eq_add_of_isCompl (N := N)
      (hker ▸ LinearMap.isCompl_of_proj hproj),
    indecomposableMultiplicity_eq_of_linearEquiv (M' := M₃) (N := N)
      (LinearEquiv.ofInjective σ hσinj).symm,
    indecomposableMultiplicity_eq_of_linearEquiv (M' := M₁) (N := N)
      (LinearEquiv.ofInjective f hf).symm, add_comm]

end TauCeti
