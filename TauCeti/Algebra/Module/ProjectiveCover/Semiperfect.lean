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

## References

* R. Wisbauer, *Foundations of Module and Ring Theory*, Gordon and Breach (1991), 18.5 (the
  generation argument).
* R. Wisbauer, *Coalgebras and Bialgebras*, lecture notes, Cairo (2004), 3.12 (applied to covers
  of simple modules).
* F. L. Sandomierski, *On semiperfect and perfect rings*, Proc. Amer. Math. Soc. **21** (1969),
  205–207, Theorem 4.
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

end TauCeti
