/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic
public import TauCeti.RingTheory.Idempotents.Semiperfect
public import TauCeti.RingTheory.Idempotents.Simple

/-!
# Projective covers of finitely generated modules over semiperfect rings

A finitely generated module `M` whose simple quotients all have projective covers has a projective
cover itself, whose source is a finite product of covers of simple quotients of `M`
(`TauCeti.exists_isProjectiveCover_pi_of_isCoatom`). Over a semiperfect ring every simple module
has a projective cover, so every finitely generated module does
(`TauCeti.exists_isProjectiveCover_of_isSemiperfectRing`); if the ring is moreover left Noetherian,
every finitely generated module has a minimal projective presentation by finitely generated
projectives (`TauCeti.exists_isMinimalProjectivePresentation_of_isSemiperfectRing`). Artin algebras
are semiperfect and Noetherian, so these apply to them.

Conversely, a cover of a simple module has a local endomorphism ring
(`TauCeti.IsProjectiveCover.isLocalRing_end`), and a projective cover of a projective module is an
isomorphism. So if every simple module has a projective cover, the cover of `R` from the first
result is an isomorphism, and `R` is a finite product of projectives with local endomorphism rings
(`TauCeti.exists_linearEquiv_pi_of_forall_isSimpleModule`), which makes `R` semiperfect
(`TauCeti.IsSemiperfectRing.of_linearEquiv_pi`). This gives the characterization of semiperfect
rings by projective covers (`TauCeti.isSemiperfectRing_tfae`).

## The construction

* **Covers of simple modules.** If `p : P → S` is a projective cover of a simple module, every
  proper submodule of `P` lies in `ker p` (`TauCeti.IsProjectiveCover.le_ker_of_ne_top`): its image
  is `0` or `S`, and in the second case it is all of `P` because `ker p` is superfluous.
* **Generation.** The images of maps `P → M` lifting covers `P → M ⧸ N` of simple quotients
  generate `M`: otherwise they lie in a maximal submodule `L`, and the lift of the cover of `M ⧸ L`
  would vanish. As `M` is finitely generated, finitely many of these images generate `M`; take a
  family of minimal size.
* **The kernel.** Let `e : P₁ × ⋯ × Pₙ → M` be the sum of the lifts `fᵢ`, and `Vᵢ` the sum of the
  images of the `fⱼ` with `j ≠ i`. By minimality `M ⧸ Vᵢ ≠ 0`, so the induced map `Pᵢ → M ⧸ Vᵢ`,
  which is onto, has a proper kernel, contained in the kernel of the cover `Pᵢ → M ⧸ Nᵢ`. The
  `i`-th component of an element of `ker e` lies in that kernel, so `ker e` lies in the product of
  the superfluous kernels of the covers, which is superfluous.

## Main results

* `TauCeti.exists_isProjectiveCover_pi_of_isCoatom`: a finitely generated module whose simple
  quotients have projective covers has a projective cover by a finite product of them.
* `TauCeti.exists_isProjectiveCover_of_isSemiperfectRing`: over a semiperfect ring, every finitely
  generated module has a projective cover.
* `TauCeti.exists_isMinimalProjectivePresentation_of_isSemiperfectRing`: over a left Noetherian
  semiperfect ring, every finitely generated module has a minimal projective presentation by
  finitely generated projectives.
* `TauCeti.IsProjectiveCover.isLocalRing_end`: a projective cover of a simple module has a local
  endomorphism ring.
* `TauCeti.isSemiperfectRing_tfae`: `R` is semiperfect exactly when it is a finite product of
  projectives with local endomorphism rings, exactly when every finitely generated module has a
  projective cover, exactly when every simple module has one.

## References

* R. Wisbauer, *Foundations of Module and Ring Theory*, Gordon and Breach (1991), 18.5 (the
  generation argument).
* R. Wisbauer, *Coalgebras and Bialgebras*, lecture notes, Cairo (2004), 3.12 (applied to covers
  of simple modules).
* F. L. Sandomierski, *On semiperfect and perfect rings*, Proc. Amer. Math. Soc. **21** (1969),
  205–207, Theorem 4 (semiperfect rings are those whose simple modules have projective covers).
* H. Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. **33** (2015), 535–549,
  Lemma 3.6 and Proposition 4.1.
* R. Wisbauer, *Foundations of Module and Ring Theory*, 19.7 (covers of simple modules are
  local).
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R]

section Superfluous

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite supremum of superfluous submodules is superfluous. -/
theorem isSuperfluous_iSup {ι : Type*} [Finite ι] {N : ι → Submodule R M}
    (hN : ∀ i, IsSuperfluous (N i)) : IsSuperfluous (⨆ i, N i) := by
  have := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup]
  exact Finset.sup_induction isSuperfluous_bot (fun _ ha _ hb ↦ ha.sup hb) fun i _ ↦ hN i

/-- A finite product of superfluous submodules is superfluous. -/
theorem IsSuperfluous.pi {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] {K : ∀ i, Submodule R (M i)} (hK : ∀ i, IsSuperfluous (K i)) :
    IsSuperfluous (Submodule.pi Set.univ K) := by
  classical
  rw [← Submodule.iSup_map_single]
  exact isSuperfluous_iSup fun i ↦ (hK i).map _

end Superfluous

section Simple

variable {P S : Type*} [AddCommGroup P] [Module R P] [AddCommGroup S] [Module R S]
  [IsSimpleModule R S]

/-- **A cover of a simple module is local**: every proper submodule of the source of a projective
cover of a simple module lies in the kernel. -/
theorem IsProjectiveCover.le_ker_of_ne_top {p : P →ₗ[R] S} (hp : IsProjectiveCover p)
    {U : Submodule R P} (hU : U ≠ ⊤) : U ≤ LinearMap.ker p := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (U.map p) with h | h
  · exact LinearMap.le_ker_iff_map.2 h
  · refine absurd (hp.isSuperfluous_ker.eq_top_of_sup_eq_top ?_) hU
    rw [sup_comm, ← Submodule.comap_map_eq, h, Submodule.comap_top]

end Simple

section Local

variable {P M S : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup S] [Module R S]

/-- **A projective cover of a projective module is an isomorphism**: it splits, and its kernel is a
superfluous direct summand. -/
theorem IsProjectiveCover.bijective_of_projective [Module.Projective R M] {f : P →ₗ[R] M}
    (hf : IsProjectiveCover f) : Function.Bijective f := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf.surjective
  have hfg (y : M) : f (g y) = y := LinearMap.congr_fun hg y
  -- `P` is the sum of `ker f` and the image of the section, which is therefore everything.
  have hsup : LinearMap.ker f ⊔ LinearMap.range g = ⊤ := eq_top_iff.2 fun x _ ↦
    Submodule.mem_sup.2 ⟨x - g (f x), by simp [hfg], g (f x), LinearMap.mem_range_self _ _,
      sub_add_cancel _ _⟩
  have hg_surj : Function.Surjective g :=
    LinearMap.range_eq_top.1 (hf.isSuperfluous_ker.eq_top_of_sup_eq_top hsup)
  refine ⟨fun x y hxy ↦ ?_, hf.surjective⟩
  obtain ⟨x, rfl⟩ := hg_surj x
  obtain ⟨y, rfl⟩ := hg_surj y
  rw [hfg, hfg] at hxy
  rw [hxy]

/-- **The cover of a simple module has a local endomorphism ring**: for an endomorphism `φ`, one of
`φ` and `1 - φ` is onto, since their images sum to everything and proper submodules lie in the
kernel of the cover; and an onto endomorphism is a projective cover of the projective source, hence
invertible. -/
theorem IsProjectiveCover.isLocalRing_end [IsSimpleModule R S] {p : P →ₗ[R] S}
    (hp : IsProjectiveCover p) : IsLocalRing (Module.End R P) := by
  have := hp.projective
  have := IsSimpleModule.nontrivial R S
  have : Nontrivial P := hp.surjective.nontrivial
  have hker : LinearMap.ker p ≠ ⊤ := fun h ↦ by
    obtain ⟨y, hy⟩ := exists_ne (0 : S)
    obtain ⟨x, rfl⟩ := hp.surjective y
    exact hy (LinearMap.mem_ker.1 (h ▸ Submodule.mem_top))
  -- An onto endomorphism has a proper, hence superfluous, kernel.
  have hunit (φ : Module.End R P) (hφ : Function.Surjective φ) : IsUnit φ := by
    have hφker : LinearMap.ker φ ≠ ⊤ := fun h ↦ by
      obtain ⟨y, hy⟩ := exists_ne (0 : P)
      obtain ⟨x, rfl⟩ := hφ y
      exact hy (LinearMap.mem_ker.1 (h ▸ Submodule.mem_top))
    have hcov : IsProjectiveCover φ :=
      ⟨inferInstance, hφ, hp.isSuperfluous_ker.mono (hp.le_ker_of_ne_top hφker)⟩
    exact (Module.End.isUnit_iff φ).2 hcov.bijective_of_projective
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun φ ↦ ?_
  by_contra! h
  have h₁ : LinearMap.range φ ≠ ⊤ := fun ht ↦ h.1 (hunit φ (LinearMap.range_eq_top.1 ht))
  have h₂ : LinearMap.range (1 - φ) ≠ ⊤ := fun ht ↦ h.2 (hunit _ (LinearMap.range_eq_top.1 ht))
  refine hker (top_le_iff.1 fun x _ ↦ ?_)
  have hx : x = φ x + (1 - φ) x := by simp
  rw [hx]
  exact add_mem (hp.le_ker_of_ne_top h₁ (LinearMap.mem_range_self _ _))
    (hp.le_ker_of_ne_top h₂ (LinearMap.mem_range_self _ _))

end Local

section Generation

variable {M : Type v} [AddCommGroup M] [Module R M]

variable (R M) in
/-- The images of maps into `M` lifting projective covers of simple quotients of `M`, with sources
in `Type w`. -/
private def coverImages : Set (Submodule R M) :=
  {U | ∃ (N : Submodule R M) (_ : IsCoatom N) (P : Type w) (_ : AddCommGroup P) (_ : Module R P)
    (p : P →ₗ[R] M ⧸ N) (_ : IsProjectiveCover p) (f : P →ₗ[R] M),
      N.mkQ ∘ₗ f = p ∧ LinearMap.range f = U}

/-- If the simple quotients of `M` have projective covers, the images of their lifts generate `M`.
-/
private theorem sSup_coverImages [Module.Finite R M]
    (h : ∀ N : Submodule R M, IsCoatom N → ∃ (P : Type w) (_ : AddCommGroup P) (_ : Module R P)
      (p : P →ₗ[R] M ⧸ N), IsProjectiveCover p) :
    sSup (coverImages.{u, v, w} R M) = ⊤ := by
  by_contra hne
  obtain ⟨L, hL, hle⟩ :=
    (eq_top_or_exists_le_coatom (sSup (coverImages.{u, v, w} R M))).resolve_left hne
  obtain ⟨P, _, _, p, hp⟩ := h L hL
  have := hp.projective
  obtain ⟨f, hf⟩ := Module.projective_lifting_property L.mkQ p L.mkQ_surjective
  have hmem : LinearMap.range f ∈ coverImages.{u, v, w} R M := by
    rw [coverImages, Set.mem_ofPred_eq]
    exact ⟨L, hL, P, _, _, p, hp, f, hf, rfl⟩
  have hfL : LinearMap.range f ≤ L := (le_sSup hmem).trans hle
  have : Nontrivial (M ⧸ L) := Submodule.Quotient.nontrivial_iff.2 hL.ne_top
  obtain ⟨y, hy⟩ := exists_ne (0 : M ⧸ L)
  obtain ⟨x, rfl⟩ := hp.surjective y
  refine hy ?_
  rw [← hf, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hfL (LinearMap.mem_range_self f x)

/-- A family of minimal size among the finite families in `coverImages` generating `M`. -/
private theorem exists_minimal_coverImages [Module.Finite R M]
    (h : ∀ N : Submodule R M, IsCoatom N → ∃ (P : Type w) (_ : AddCommGroup P) (_ : Module R P)
      (p : P →ₗ[R] M ⧸ N), IsProjectiveCover p) :
    ∃ (n : ℕ) (U : Fin n → Submodule R M), (∀ i, U i ∈ coverImages.{u, v, w} R M) ∧
      ⨆ i, U i = ⊤ ∧ ∀ i, ⨆ (j) (_ : j ≠ i), U j ≠ ⊤ := by
  classical
  have hex : ∃ n, ∃ U : Fin n → Submodule R M, (∀ i, U i ∈ coverImages.{u, v, w} R M) ∧
      ⨆ i, U i = ⊤ := by
    have hc : IsCompactElement (⊤ : Submodule R M) :=
      (Submodule.fg_iff_compact _).1 Module.Finite.fg_top
    obtain ⟨s, hs⟩ := hc.exists_finset_of_le_iSup (fun U : coverImages.{u, v, w} R M ↦ U.1)
      (by rw [← sSup_eq_iSup', sSup_coverImages h])
    refine ⟨s.card, fun i ↦ (s.equivFin.symm i).1.1, fun i ↦ (s.equivFin.symm i).1.2,
      top_le_iff.1 (hs.trans (iSup₂_le fun U hU ↦ ?_))⟩
    exact le_iSup_of_le (s.equivFin ⟨U, hU⟩) (by simp)
  obtain ⟨hU, hsup⟩ := (Nat.find_spec hex).choose_spec
  refine ⟨Nat.find hex, _, hU, hsup, fun i hi ↦ ?_⟩
  -- Dropping the `i`-th member would give a smaller generating family.
  let e := Fintype.equivFin {j // j ≠ i}
  refine Nat.find_min hex (show Fintype.card {j // j ≠ i} < Nat.find hex from ?_)
    ⟨fun k ↦ (Nat.find_spec hex).choose (e.symm k).1, fun k ↦ hU _, ?_⟩
  · rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    exact Nat.sub_one_lt_of_lt i.pos
  · refine Eq.trans ?_ hi
    rw [iSup_subtype']
    exact e.symm.iSup_comp (g := fun j : {j // j ≠ i} ↦ (Nat.find_spec hex).choose j.1)

/-- **Covers from covers of simple quotients.** If every simple quotient of a finitely generated
module `M` has a projective cover, then `M` has a projective cover whose source is a finite product
of projective covers of simple quotients of `M`. -/
theorem exists_isProjectiveCover_pi_of_isCoatom [Module.Finite R M]
    (h : ∀ N : Submodule R M, IsCoatom N → ∃ (P : Type w) (_ : AddCommGroup P) (_ : Module R P)
      (p : P →ₗ[R] M ⧸ N), IsProjectiveCover p) :
    ∃ (n : ℕ) (P : Fin n → Type w) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i))
      (N : Fin n → Submodule R M) (p : ∀ i, P i →ₗ[R] M ⧸ N i) (f : (∀ i, P i) →ₗ[R] M),
      (∀ i, IsCoatom (N i)) ∧ (∀ i, IsProjectiveCover (p i)) ∧ IsProjectiveCover f := by
  classical
  obtain ⟨n, U, hU, hsup, hirr⟩ := exists_minimal_coverImages h
  simp only [coverImages, Set.mem_ofPred_eq] at hU
  choose N hN P _ _ p hp f _ hrange using hU
  have : ∀ i, Module.Projective R (P i) := fun i ↦ (hp i).projective
  -- The sum of the lifts, and the sums `V i` of all but one of their images.
  let F : (∀ i, P i) →ₗ[R] M := ∑ i, f i ∘ₗ LinearMap.proj i
  have hF (x : ∀ i, P i) : F x = ∑ i, f i (x i) := by simp [F]
  let V : Fin n → Submodule R M := fun i ↦ ⨆ (j) (_ : j ≠ i), U j
  have hfV {i j : Fin n} (hj : j ≠ i) (y : P j) : f j y ∈ V i :=
    le_iSup₂ (f := fun j (_ : j ≠ i) ↦ U j) j hj (hrange j ▸ LinearMap.mem_range_self (f j) y)
  -- Each lift, followed by the quotient by `V i`, is onto with a proper kernel.
  have hker (i : Fin n) : LinearMap.ker ((V i).mkQ ∘ₗ f i) ≤ LinearMap.ker (p i) := by
    have : IsSimpleModule R (M ⧸ N i) := isSimpleModule_iff_isCoatom.2 (hN i)
    refine (hp i).le_ker_of_ne_top fun htop ↦ hirr i ?_
    -- `U i ⊔ V i = M`, and `U i` maps to zero modulo `V i`, so `V i = M`.
    have hUV : U i ⊔ V i = ⊤ := top_le_iff.1 (hsup ▸ iSup_le fun j ↦ by
      by_cases hj : j = i
      · exact hj ▸ le_sup_left
      · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) ↦ U j) j hj))
    refine eq_top_iff.2 fun m _ ↦ ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hUV ▸ Submodule.mem_top (x := m))
    rw [← hrange i] at hu
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hu
    have hy := LinearMap.mem_ker.1 (htop ▸ Submodule.mem_top (x := y))
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    exact add_mem hy hv
  refine ⟨n, P, inferInstance, inferInstance, N, p, F, hN, hp, ?_⟩
  refine ⟨Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R)), ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← hsup]
    refine iSup_le fun i ↦ ?_
    intro m hm
    rw [← hrange i] at hm
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hm
    refine LinearMap.mem_range.2 ⟨Pi.single i y, ?_⟩
    rw [hF, Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero])
      (by simp), Pi.single_eq_same]
  · refine (IsSuperfluous.pi fun i ↦ (hp i).isSuperfluous_ker).mono fun x hx ↦ ?_
    rw [Submodule.mem_pi]
    intro i _
    refine hker i ?_
    -- `f i (x i)` is minus the sum of the other components, which lies in `V i`.
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    have hx0 : ∑ j, f j (x j) = 0 := (hF x).symm.trans hx
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg] at hx0
    rw [hx0]
    exact neg_mem (Submodule.sum_mem _ fun j hj ↦ hfV (Finset.ne_of_mem_erase hj) _)

end Generation

section Semiperfect

/-- **A local idempotent gives a projective cover**: if the corner `eRe` is local, every surjection
from `Re` onto a nonzero module is a projective cover. -/
theorem _root_.IsIdempotentElem.isProjectiveCover_of_isLocalRing_corner {e : R}
    (he : IsIdempotentElem e) [IsLocalRing he.Corner] {S : Type*} [AddCommGroup S] [Module R S]
    [Nontrivial S] {f : (Ideal.span {e} : Ideal R) →ₗ[R] S} (hf : Function.Surjective f) :
    IsProjectiveCover f := by
  have := he.isLocalRing_end_of_isLocalRing_corner
  have := he.projective_span_singleton
  have : Module.Finite R (Ideal.span {e} : Ideal R) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span_singleton _)
  refine ⟨inferInstance, hf, isSuperfluous_of_le_jacobson
    (Module.Projective.le_jacobson_of_isLocalRing_end fun htop ↦ ?_)⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : S)
  obtain ⟨x, rfl⟩ := hf y
  exact hy (LinearMap.mem_ker.1 (htop ▸ Submodule.mem_top))

variable [IsSemiperfectRing R]

/-- Over a semiperfect ring every simple module has a projective cover. -/
theorem exists_isProjectiveCover_of_isSimpleModule_of_isSemiperfectRing (S : Type v)
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] S), IsProjectiveCover p := by
  obtain ⟨n, e, he, hloc⟩ :=
    IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner (A := R)
  have := IsSimpleModule.nontrivial R S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  -- Some `eᵢ` does not kill `s`, since the `eᵢ` sum to `1`.
  obtain ⟨i, hi⟩ : ∃ i, e i • s ≠ 0 := by
    by_contra! h
    exact hs (by
      rw [← one_smul R s, ← he.complete, Finset.sum_smul, Finset.sum_eq_zero fun i _ ↦ h i])
  have := hloc i
  let f : (Ideal.span {e i} : Ideal R) →ₗ[R] S :=
    LinearMap.toSpanSingleton R S s ∘ₗ (Ideal.span {e i}).subtype
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun hbot ↦ hi ?_
    have : f ⟨e i, Ideal.mem_span_singleton_self _⟩ ∈ LinearMap.range f :=
      LinearMap.mem_range_self _ _
    simpa [hbot, f] using this
  exact ⟨_, _, _, f, (he.idem i).isProjectiveCover_of_isLocalRing_corner hf⟩

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Projective covers over a semiperfect ring.** Every finitely generated module over a
semiperfect ring has a projective cover. -/
theorem exists_isProjectiveCover_of_isSemiperfectRing :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] M), IsProjectiveCover p := by
  obtain ⟨n, P, _, _, N, -, f, -, -, hf⟩ := exists_isProjectiveCover_pi_of_isCoatom.{u, v, u}
    fun (N : Submodule R M) hN ↦ have := isSimpleModule_iff_isCoatom.2 hN
      exists_isProjectiveCover_of_isSimpleModule_of_isSemiperfectRing (M ⧸ N)
  exact ⟨_, _, _, f, hf⟩

/-- **Minimal presentations over a Noetherian semiperfect ring.** Every finitely generated module
over a left Noetherian semiperfect ring, for instance an Artin algebra, has a minimal projective
presentation by finitely generated projectives. -/
theorem exists_isMinimalProjectivePresentation_of_isSemiperfectRing [IsNoetherianRing R] :
    ∃ (P₀ : Type u) (_ : AddCommGroup P₀) (_ : Module R P₀) (p₀ : P₀ →ₗ[R] M)
      (P₁ : Type u) (_ : AddCommGroup P₁) (_ : Module R P₁) (p₁ : P₁ →ₗ[R] P₀),
      IsMinimalProjectivePresentation p₁ p₀ ∧ Module.Finite R P₀ ∧ Module.Finite R P₁ := by
  obtain ⟨P₀, _, _, p₀, h₀⟩ := exists_isProjectiveCover_of_isSemiperfectRing (R := R) (M := M)
  have := h₀.finite
  obtain ⟨P₁, _, _, c, h₁⟩ :=
    exists_isProjectiveCover_of_isSemiperfectRing (R := R) (M := LinearMap.ker p₀)
  exact ⟨P₀, _, _, p₀, P₁, _, _, _, h₀.isMinimalProjectivePresentation h₁, this, h₁.finite⟩

end Semiperfect

section Decomposition

/-- **Covers of simple modules decompose the ring.** If every simple left `R`-module has a
projective cover, then `R` is, as a left module over itself, a finite product of projective modules
with local endomorphism rings: the projective cover of `R` given by
`TauCeti.exists_isProjectiveCover_pi_of_isCoatom` is an isomorphism, as `R` is projective. -/
theorem exists_linearEquiv_pi_of_forall_isSimpleModule
    (h : ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S], ∃ (P : Type u)
      (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] S), IsProjectiveCover p) :
    ∃ (n : ℕ) (P : Fin n → Type u) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i)),
      (∀ i, Module.Projective R (P i)) ∧ (∀ i, IsLocalRing (Module.End R (P i))) ∧
        Nonempty (R ≃ₗ[R] ∀ i, P i) := by
  obtain ⟨n, P, _, _, N, p, f, hN, hp, hf⟩ :=
    exists_isProjectiveCover_pi_of_isCoatom.{u, u, u} (R := R) (M := R)
      fun N hN ↦ have := isSimpleModule_iff_isCoatom.2 hN; h (R ⧸ N)
  have := fun i ↦ isSimpleModule_iff_isCoatom.2 (hN i)
  exact ⟨n, P, _, _, fun i ↦ (hp i).projective, fun i ↦ (hp i).isLocalRing_end,
    ⟨(LinearEquiv.ofBijective f hf.bijective_of_projective).symm⟩⟩

/-- **A decomposition of the ring into local projectives makes it semiperfect.** If `R` is, as a
left module over itself, a finite product of modules with local endomorphism rings, the
idempotents `eᵢ` of the factors are complete and orthogonal, with `Reᵢ` the `i`-th factor, so
their corners are local (`IsSemiperfectRing.of_isLocalRing_corner`). -/
theorem IsSemiperfectRing.of_linearEquiv_pi {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] [∀ i, IsLocalRing (Module.End R (P i))]
    (φ : R ≃ₗ[R] ∀ i, P i) : IsSemiperfectRing R := by
  classical
  let e : Fin n → R := fun i ↦ φ.symm (Pi.single i (φ 1 i))
  -- Right multiplication by `eᵢ` is the projection onto the `i`-th factor.
  have hφ (x : R) (i : Fin n) : φ x i = x • φ 1 i := by
    simpa using congrFun (φ.map_smul x 1) i
  have hmul (x : R) (i : Fin n) : x * e i = φ.symm (Pi.single i (φ x i)) := by
    rw [hφ x i, ← smul_eq_mul, ← map_smul, Pi.single_smul]
  have hφe (i : Fin n) : φ (e i) = Pi.single i (φ 1 i) := φ.apply_symm_apply _
  have he : CompleteOrthogonalIdempotents e := by
    refine ⟨⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩, ?_⟩
    · rw [IsIdempotentElem, hmul, hφe, Pi.single_eq_same]
    · beta_reduce
      rw [hmul, hφe, Pi.single_eq_of_ne' hij, Pi.single_zero, map_zero]
    · rw [← map_sum, Finset.univ_sum_single, φ.symm_apply_apply]
  refine IsSemiperfectRing.of_isLocalRing_corner he fun i ↦ ?_
  -- The left ideal `Reᵢ` is the `i`-th factor.
  let ψ : P i →ₗ[R] R := φ.symm.toLinearMap ∘ₗ LinearMap.single R P i
  have hψ : Function.Injective ψ := fun a b hab ↦ Pi.single_injective i (φ.symm.injective hab)
  have hrange : LinearMap.range ψ = (Ideal.span {e i} : Ideal R) := by
    ext x
    rw [LinearMap.mem_range, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨ψ y, ?_⟩
      simp only [hmul, ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, φ.apply_symm_apply,
        LinearMap.coe_single, Pi.single_eq_same]
    · rintro ⟨a, rfl⟩
      exact ⟨φ a i, by rw [hmul]; rfl⟩
  let iso : P i ≃ₗ[R] (Ideal.span {e i} : Ideal R) :=
    (LinearEquiv.ofInjective ψ hψ).trans (LinearEquiv.ofEq _ _ hrange)
  have : IsLocalRing (Module.End R (Ideal.span {e i} : Ideal R)) := iso.conjRingEquiv.isLocalRing
  exact (he.idem i).isLocalRing_corner_of_isLocalRing_end

/-- **Semiperfect rings by projective covers** (Sandomierski; Krause, Proposition 4.1). For a ring
`R`, the following are equivalent:
1. `R` is semiperfect;
2. `R` is, as a left module over itself, a finite product of projective modules with local
   endomorphism rings;
3. every finitely generated left `R`-module has a projective cover;
4. every simple left `R`-module has a projective cover. -/
theorem isSemiperfectRing_tfae : List.TFAE
    [IsSemiperfectRing R,
      ∃ (n : ℕ) (P : Fin n → Type u) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i)),
        (∀ i, Module.Projective R (P i)) ∧ (∀ i, IsLocalRing (Module.End R (P i))) ∧
          Nonempty (R ≃ₗ[R] ∀ i, P i),
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], ∃ (P : Type u)
        (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] M), IsProjectiveCover p,
      ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S], ∃ (P : Type u)
        (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] S), IsProjectiveCover p] := by
  tfae_have 1 → 3 := fun _ M _ _ _ ↦ exists_isProjectiveCover_of_isSemiperfectRing (M := M)
  tfae_have 3 → 4 := fun h S _ _ _ ↦ h S
  tfae_have 4 → 2 := exists_linearEquiv_pi_of_forall_isSimpleModule
  tfae_have 2 → 1 := fun ⟨_, _, _, _, _, hloc, ⟨φ⟩⟩ ↦
    have := hloc
    IsSemiperfectRing.of_linearEquiv_pi φ
  tfae_finish

end Decomposition

end TauCeti
