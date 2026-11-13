/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveCover.Simple
public import TauCeti.Order.CompactlyGenerated
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition
public import TauCeti.RingTheory.Idempotents.Semiperfect

/-!
# Projective covers of finitely generated modules over semiperfect rings

A finitely generated module `M` whose simple quotients all have projective covers has a projective
cover itself, whose source is a finite product of covers of simple quotients of `M`
(`TauCeti.exists_isProjectiveCover_pi_of_isCoatom`). Over a semiperfect ring every simple module
has a projective cover, by a left ideal `Reᵢ` for an idempotent with local corner
(`CompleteOrthogonalIdempotents.exists_isProjectiveCover_of_isLocalRing_corner`), so every finitely
generated module does (`TauCeti.exists_isProjectiveCover_of_isSemiperfectRing`). Semiprimary rings,
in particular Artinian rings and Artin algebras, are semiperfect. Minimal projective presentations
of finitely presented modules over a semiperfect ring are built from these covers in
`TauCeti/Algebra/Module/MinimalProjectivePresentation/Finite.lean`.

Conversely, a cover of a simple module has a local endomorphism ring
(`TauCeti.IsProjectiveCover.isLocalRing_end`), and a projective cover of a projective module is an
isomorphism. So if every simple module has a projective cover, the cover of `R` from the first
result is an isomorphism, and `R` is a finite product of projectives with local endomorphism rings
(`TauCeti.exists_linearEquiv_pi_of_forall_isSimpleModule`), which makes `R` semiperfect
(`TauCeti.IsSemiperfectRing.of_linearEquiv_pi`). This gives the characterization of semiperfect
rings by projective covers (`TauCeti.isSemiperfectRing_tfae`).

## The construction

* **Covers of simple modules.** If `p : P → S` is a projective cover of a simple module, every
  proper submodule of `P` lies in `ker p` (`TauCeti.IsProjectiveCover.le_ker_of_ne_top`).
* **Generation.** The images of maps `P → M` lifting covers `P → M ⧸ N` of simple quotients
  generate `M`: otherwise they lie in a maximal submodule `L`, and the lift of the cover of `M ⧸ L`
  would vanish. As `M` is finitely generated, `⊤` is compact, so an irredundant finite family of
  these images generates `M` (`IsCompactElement.exists_fin_iSup_eq_of_sSup_eq`).
* **The kernel.** Let `e : P₁ × ⋯ × Pₙ → M` be the sum of the lifts `fᵢ`, and `Vᵢ` the sum of the
  images of the `fⱼ` with `j ≠ i`. By minimality `M ⧸ Vᵢ ≠ 0`, so the induced map `Pᵢ → M ⧸ Vᵢ`,
  which is onto, has a proper kernel, contained in the kernel of the cover `Pᵢ → M ⧸ Nᵢ`. The
  `i`-th component of an element of `ker e` lies in that kernel, so `ker e` lies in the product of
  the superfluous kernels of the covers, which is superfluous.

## Main results

* `TauCeti.exists_isProjectiveCover_pi_of_isCoatom`: a finitely generated module whose simple
  quotients have projective covers has a projective cover by a finite product of them.
* `CompleteOrthogonalIdempotents.exists_isProjectiveCover_of_isLocalRing_corner`: for a complete
  family of orthogonal idempotents with local corners, every simple module is covered by some
  `Reᵢ`.
* `TauCeti.exists_isProjectiveCover_of_isSemiperfectRing`: over a semiperfect ring, every finitely
  generated module has a projective cover.
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
  have hfL : LinearMap.range f ≤ LinearMap.ker L.mkQ := by
    rw [Submodule.ker_mkQ]
    exact (le_sSup hmem).trans hle
  have : Nontrivial (M ⧸ L) := Submodule.Quotient.nontrivial_iff.2 hL.ne_top
  -- The cover of `M ⧸ L` would be the zero map.
  exact LinearMap.ne_zero_of_surjective hp.surjective
    (hf.symm.trans (LinearMap.range_le_ker_iff.1 hfL))

/-- **Covers from covers of simple quotients.** If every simple quotient of a finitely generated
module `M` has a projective cover, then `M` has a projective cover whose source is a finite product
of projective covers `pᵢ : Pᵢ → M ⧸ Nᵢ` of simple quotients of `M`, the `i`-th component of the
cover lifting `pᵢ`. -/
theorem exists_isProjectiveCover_pi_of_isCoatom [Module.Finite R M]
    (h : ∀ N : Submodule R M, IsCoatom N → ∃ (P : Type w) (_ : AddCommGroup P) (_ : Module R P)
      (p : P →ₗ[R] M ⧸ N), IsProjectiveCover p) :
    ∃ (n : ℕ) (P : Fin n → Type w) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i))
      (N : Fin n → Submodule R M) (p : ∀ i, P i →ₗ[R] M ⧸ N i) (f : (∀ i, P i) →ₗ[R] M),
      (∀ i, IsCoatom (N i)) ∧ (∀ i, IsProjectiveCover (p i)) ∧
        (∀ i, (N i).mkQ ∘ₗ f ∘ₗ LinearMap.single R P i = p i) ∧ IsProjectiveCover f := by
  classical
  have hc : IsCompactElement (⊤ : Submodule R M) :=
    (Submodule.fg_iff_compact _).1 Module.Finite.fg_top
  obtain ⟨n, U, hU, hsup, hirr⟩ := hc.exists_fin_iSup_eq_of_sSup_eq (sSup_coverImages h)
  simp only [coverImages, Set.mem_ofPred_eq] at hU
  choose N hN P _ _ p hp f hfp hrange using hU
  have : ∀ i, Module.Projective R (P i) := fun i ↦ (hp i).projective
  -- The sum of the lifts, and the sums `V i` of all but one of their images.
  let F : (∀ i, P i) →ₗ[R] M := LinearMap.lsum R P ℕ f
  have hFi (i : Fin n) : F ∘ₗ LinearMap.single R P i = f i :=
    LinearMap.ext fun y ↦ LinearMap.lsum_piSingle R P ℕ f i y
  let V : Fin n → Submodule R M := fun i ↦ ⨆ (j) (_ : j ≠ i), U j
  have hfV {i j : Fin n} (hj : j ≠ i) (y : P j) : f j y ∈ V i :=
    le_iSup₂ (f := fun j (_ : j ≠ i) ↦ U j) j hj (hrange j ▸ LinearMap.mem_range_self (f j) y)
  -- Each lift, followed by the quotient by `V i`, is onto with a proper kernel.
  have hker (i : Fin n) : LinearMap.ker ((V i).mkQ ∘ₗ f i) ≤ LinearMap.ker (p i) := by
    have : IsSimpleModule R (M ⧸ N i) := isSimpleModule_iff_isCoatom.2 (hN i)
    refine (hp i).le_ker_of_ne_top fun htop ↦ hirr i ?_
    -- `U i` maps to zero modulo `V i`, so `V i = U i ⊔ V i = M`.
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, ← LinearMap.range_le_iff_comap, hrange i] at htop
    exact (sup_eq_right.2 htop).symm.trans ((iSup_split_single U i).symm.trans hsup)
  refine ⟨n, P, inferInstance, inferInstance, N, p, F, hN, hp, fun i ↦ ?_, ?_⟩
  · rw [hFi i, hfp i]
  refine ⟨Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R)), ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← hsup]
    refine iSup_le fun i m hm ↦ ?_
    rw [← hrange i] at hm
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hm
    exact ⟨Pi.single i y, LinearMap.congr_fun (hFi i) y⟩
  · refine (isSuperfluous_pi_univ fun i ↦ (hp i).isSuperfluous_ker).mono fun x hx ↦ ?_
    rw [Submodule.mem_pi]
    intro i _
    refine hker i ?_
    -- `f i (x i)` is minus the sum of the other components, which lies in `V i`.
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    have hx0 : ∑ j, f j (x j) = 0 := by
      simpa [F, LinearMap.lsum_apply] using LinearMap.mem_ker.1 hx
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg] at hx0
    rw [hx0]
    exact neg_mem (Submodule.sum_mem _ fun j hj ↦ hfV (Finset.ne_of_mem_erase hj) _)

end Generation

section Semiperfect

/-- **A local idempotent gives a projective cover**: if the corner `eRe` is local, every surjection
from `Re` onto a nonzero module is a projective cover, as `Re` is projective with local
endomorphism ring. -/
theorem _root_.IsIdempotentElem.isProjectiveCover_of_isLocalRing_corner {e : R}
    (he : IsIdempotentElem e) [IsLocalRing he.Corner] {S : Type*} [AddCommMonoid S] [Module R S]
    [Nontrivial S] {f : (Ideal.span {e} : Ideal R) →ₗ[R] S} (hf : Function.Surjective f) :
    IsProjectiveCover f :=
  have := he.isLocalRing_end_of_isLocalRing_corner
  have := he.projective_span_singleton
  Module.Projective.isProjectiveCover_of_isLocalRing_end hf

/-- **Covers of simple modules from local idempotents.** For a complete family of orthogonal
idempotents `eᵢ` with local corners `eᵢReᵢ`, every simple module is covered by one of the left
ideals `Reᵢ`. -/
theorem _root_.CompleteOrthogonalIdempotents.exists_isProjectiveCover_of_isLocalRing_corner
    {ι : Type*} [Fintype ι] {e : ι → R} (he : CompleteOrthogonalIdempotents e)
    (hloc : ∀ i, IsLocalRing (he.idem i).Corner) (S : Type v) [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] :
    ∃ (i : ι) (f : (Ideal.span {e i} : Ideal R) →ₗ[R] S), IsProjectiveCover f := by
  obtain ⟨i, f, hf⟩ := he.exists_surjective_of_isSimpleModule S
  have := hloc i
  have := IsSimpleModule.nontrivial R S
  exact ⟨i, f, (he.idem i).isProjectiveCover_of_isLocalRing_corner hf⟩

variable [IsSemiperfectRing R]

/-- Over a semiperfect ring every simple module has a projective cover. -/
theorem exists_isProjectiveCover_of_isSimpleModule_of_isSemiperfectRing (S : Type v)
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] S), IsProjectiveCover p := by
  obtain ⟨n, e, he, hloc⟩ :=
    IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner (A := R)
  obtain ⟨i, f, hf⟩ := he.exists_isProjectiveCover_of_isLocalRing_corner hloc S
  exact ⟨_, _, _, f, hf⟩

/-- **Projective covers over a semiperfect ring.** Every finitely generated module over a
semiperfect ring has a projective cover. -/
theorem exists_isProjectiveCover_of_isSemiperfectRing (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] M), IsProjectiveCover p := by
  obtain ⟨n, P, _, _, N, -, f, -, -, -, hf⟩ := exists_isProjectiveCover_pi_of_isCoatom.{u, v, u}
    fun (N : Submodule R M) hN ↦ have := isSimpleModule_iff_isCoatom.2 hN
      exists_isProjectiveCover_of_isSimpleModule_of_isSemiperfectRing (M ⧸ N)
  exact ⟨_, _, _, f, hf⟩

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
  obtain ⟨n, P, _, _, N, p, f, hN, hp, -, hf⟩ :=
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
  tfae_have 1 → 3 := fun _ M _ _ _ ↦ exists_isProjectiveCover_of_isSemiperfectRing M
  tfae_have 3 → 4 := fun h S _ _ _ ↦ h S
  tfae_have 4 → 2 := exists_linearEquiv_pi_of_forall_isSimpleModule
  tfae_have 2 → 1 := fun ⟨_, _, _, _, _, hloc, ⟨φ⟩⟩ ↦
    have := hloc
    IsSemiperfectRing.of_linearEquiv_pi φ
  tfae_finish

end Decomposition

end TauCeti
