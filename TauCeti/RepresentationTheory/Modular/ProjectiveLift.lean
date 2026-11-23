/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.OrzechProperty
import TauCeti.Algebra.Module.LinearMap.EndQuotient
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.Module.Projective.Lift
import TauCeti.Algebra.Module.Projective.Reduction
import TauCeti.Algebra.Module.Projective.Top
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Ideal.Extended
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Jacobson.Basic
import TauCeti.RingTheory.Noetherian.LinearMap

/-!
# Projective modules over `O[G]` and their reductions

Let `O` be a Noetherian ring, complete with respect to a principal ideal `(ϖ)`, let `A` be an
`O`-algebra that is finite as an `O`-module, and let `π : A →+* B` be a surjective ring
homomorphism with kernel `ϖ A`. The main case is a complete discrete valuation ring `O` with
uniformizer `ϖ` and residue field `k`, a finite group `G`, `A = O[G]` and `B = k[G]`, with `π` the
reduction of coefficients. A **reduction** of an `A`-module `P` is a `B`-module `Y` with a
surjection `f : P → Y`, semilinear along `π`, whose kernel is `ϖ P`; in other words `Y ≅ P ⧸ ϖ P`
with its `B`-module structure.

This file proves that finitely generated projective `A`-modules and their reductions correspond:

* the reduction of a finitely generated projective `A`-module is a finitely generated projective
  `B`-module (`TauCeti.projective_of_reduction`; finiteness is Mathlib's
  `Module.Finite.of_surjective`);
* every finitely generated projective `B`-module is the reduction of a finitely generated
  projective `A`-module (`TauCeti.exists_projective_reduction_of_projective`);
* two finitely generated projective `A`-modules with the same reduction are isomorphic
  (`TauCeti.nonempty_linearEquiv_of_reduction`);
* a finitely generated projective `A`-module is indecomposable exactly when its reduction is
  (`TauCeti.isIndecomposableModule_iff_of_reduction`).

So the projective indecomposable `O[G]`-modules correspond to the projective indecomposable
`k[G]`-modules, and hence, as `k[G]` is a finite-dimensional algebra, to the simple
`k[G]`-modules: a finitely generated projective `A`-module is indecomposable exactly when the top
of its reduction is simple, when `B` is semiprimary
(`TauCeti.isIndecomposableModule_iff_isSimpleModule_top_of_reduction`).

The radical statement behind these is that `ϖ A` lies in the Jacobson radical of `A`
(`TauCeti.map_algebraMap_le_jacobson_of_finite`): left multiplication by `1 + y ϖ` on the finite
`O`-module `A` is onto by Nakayama's lemma, hence bijective. Indecomposability is transported by
idempotent endomorphisms: an idempotent endomorphism of `P` descends to the reduction, and with the
kernel of reduction in the radical it vanishes exactly when its reduction does; conversely an
idempotent endomorphism of the reduction `Y ≃ P ⧸ ϖ P` lifts to an idempotent endomorphism of `P`
because `End_A(P)` is `ϖ`-adically complete (`TauCeti.exists_isIdempotentElem_endMapQ_eq`).

For `O = ℤ₂` and `G = C₂`, the regular module `ℤ₂[C₂]` is projective indecomposable, with
reduction `𝔽₂[C₂]`, the projective cover of the trivial module.

## Main results

* `TauCeti.map_algebraMap_le_jacobson_of_finite`: for a finite algebra `A` over `R`, the extension
  of an ideal in the Jacobson radical of `R` lies in the Jacobson radical of `A`.
* `TauCeti.isIndecomposableModule_iff_of_reduction`: a finitely generated projective `A`-module is
  indecomposable exactly when its reduction is.
* `TauCeti.exists_projective_reduction_of_projective`: projective `B`-modules lift.
* `TauCeti.nonempty_linearEquiv_of_reduction`: lifts are unique up to isomorphism.
* `TauCeti.isIndecomposableModule_iff_of_reduction_residue`,
  `TauCeti.exists_projective_reduction_residue_of_projective` and
  `TauCeti.nonempty_linearEquiv_of_reduction_residue`: the three statements for `A = O[G]` and
  `B = k[G]`, where `O` is a complete discrete valuation ring with residue field `k`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 9.4.3 and 9.4.5.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
-/

public section

namespace TauCeti

/-- **The radical of a finite algebra contains the extended radical.** For an `R`-algebra `A`,
possibly noncommutative, that is finite as an `R`-module, the extension to `A` of an ideal in the
Jacobson radical of `R` lies in the Jacobson radical of `A`. -/
theorem map_algebraMap_le_jacobson_of_finite {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Module.Finite R A] {I : Ideal R} (hI : I ≤ Ring.jacobson R) :
    I.map (algebraMap R A) ≤ Ring.jacobson A := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ring.mem_jacobson_iff_isUnit_one_add_mul_left]
  intro y
  -- Left multiplication by `u = 1 + y x` is onto by Nakayama's lemma, hence bijective.
  set u := 1 + y * algebraMap R A x
  have hsurj : Function.Surjective (Algebra.lmul R A u) := by
    refine LinearMap.range_eq_top.mp (top_le_iff.mp <| Submodule.le_of_le_smul_of_le_jacobson
      Module.Finite.fg_top hI fun b _ ↦ ?_)
    refine Submodule.mem_sup.mpr ⟨u * b, ⟨b, rfl⟩, x • -(y * b),
      Submodule.smul_mem_smul hx Submodule.mem_top, ?_⟩
    rw [Algebra.smul_def, mul_neg, ← mul_assoc, Algebra.commutes]
    simp only [u, add_mul, one_mul, add_neg_cancel_right]
  exact Algebra.lmul_isUnit_iff.mp ((Module.End.isUnit_iff _).mpr
    ⟨OrzechProperty.injective_of_surjective_endomorphism _ hsurj, hsurj⟩)

section Reduction

variable {A B : Type*} [Ring A] [Ring B] {π : A →+* B}
  {P : Type*} [AddCommGroup P] [Module A P] {Y : Type*} [AddCommGroup Y] [Module B Y]

/-- A semilinear map into a `B`-module kills `ker π • P`. -/
private theorem map_eq_zero_of_mem_ker_smul_top {M : Type*} [AddCommGroup M] [Module B M]
    (h : P →ₛₗ[π] M) {x : P} (hx : x ∈ RingHom.ker π • (⊤ : Submodule A P)) : h x = 0 :=
  Submodule.smul_induction_on hx (fun r hr n _ ↦ by rw [h.map_smulₛₗ, hr, zero_smul])
    fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero]

variable (hπ : Function.Surjective π) {f : P →ₛₗ[π] Y} (hf : Function.Surjective f)
  (hfker : ∀ x, f x = 0 ↔ x ∈ RingHom.ker π • (⊤ : Submodule A P))

include hfker in
/-- A semilinear map out of `P` factors through a reduction `f : P → Y`. -/
private theorem map_eq_of_map_eq {M : Type*} [AddCommGroup M] [Module B M] (h : P →ₛₗ[π] M)
    {x x' : P} (hxx : f x = f x') : h x = h x' := by
  rw [← sub_eq_zero, ← map_sub]
  exact map_eq_zero_of_mem_ker_smul_top h ((hfker _).mp (by rw [map_sub, hxx, sub_self]))

/-- The descent of a semilinear map `h : P → M` to a `B`-linear map `Y → M` along a reduction
`f : P → Y`. -/
private noncomputable def descend {M : Type*} [AddCommGroup M] [Module B M] (h : P →ₛₗ[π] M) :
    Y →ₗ[B] M where
  toFun y := h (Function.surjInv hf y)
  map_add' y y' := by
    rw [← map_add]
    exact map_eq_of_map_eq hfker h (by simp [Function.surjInv_eq hf])
  map_smul' b y := by
    rw [RingHom.id_apply, ← Function.surjInv_eq hπ b, ← h.map_smulₛₗ]
    exact map_eq_of_map_eq hfker h (by simp [f.map_smulₛₗ, Function.surjInv_eq hf])

private theorem descend_apply {M : Type*} [AddCommGroup M] [Module B M] (h : P →ₛₗ[π] M) (x : P) :
    descend hπ hf hfker h (f x) = h x :=
  map_eq_of_map_eq hfker h (Function.surjInv_eq hf _)

include hπ hf hfker in
/-- **The reduction of a projective module is projective.** If `P` is a projective `A`-module and
`f : P → Y` is a reduction of `P`, then `Y` is a projective `B`-module. -/
theorem projective_of_reduction [Module.Projective A P] : Module.Projective B Y := by
  -- `Y` is a retract of the free module `Y →₀ B`: lift `f` along `Y →₀ B → Y` by projectivity.
  classical
  let s := Finsupp.linearCombination B (id : Y → Y)
  have hs : Function.Surjective s := fun y ↦ ⟨Finsupp.single y 1, by simp [s]⟩
  let _ : Module A Y := Module.compHom Y π
  let _ : Module A (Y →₀ B) := Module.compHom (Y →₀ B) π
  let sA : (Y →₀ B) →ₗ[A] Y :=
    { toFun := s, map_add' := s.map_add, map_smul' a v := s.map_smul (π a) v }
  let fA : P →ₗ[A] Y := { toFun := f, map_add' := f.map_add, map_smul' := f.map_smulₛₗ }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property sA fA hs
  let u' : P →ₛₗ[π] (Y →₀ B) := { toFun := u, map_add' := u.map_add, map_smul' := u.map_smul }
  refine Module.Projective.of_split (descend hπ hf hfker u') s (LinearMap.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := hf y
  simpa [descend_apply, u', sA, fA] using LinearMap.congr_fun hu x

include hfker in
/-- An idempotent endomorphism of `P` whose image lies in `ker π • P` is zero, when `ker π` lies in
the Jacobson radical and `P` is finitely generated. -/
private theorem eq_zero_of_isIdempotentElem_of_map_eq_zero [Module.Finite A P]
    (hJ : RingHom.ker π ≤ Ring.jacobson A) {e : Module.End A P} (he : IsIdempotentElem e)
    (h : ∀ x, f (e x) = 0) : e = 0 := by
  -- The range `N` of `e` satisfies `N ≤ ker π • N`, so it vanishes by Nakayama's lemma.
  have hN : LinearMap.range e ≤ Ring.jacobson A • LinearMap.range e := by
    rintro _ ⟨x, rfl⟩
    have hmem : e (e x) ∈ (RingHom.ker π • (⊤ : Submodule A P)).map e :=
      ⟨e x, (hfker _).mp (h x), rfl⟩
    rw [← mul_apply_eq_comp, he.eq, Submodule.map_smul'', ← LinearMap.range_eq_map] at hmem
    exact Submodule.smul_mono_left hJ hmem
  have hfg : (LinearMap.range e).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map e
  exact LinearMap.range_eq_bot.mp (Submodule.FG.eq_bot_of_le_jacobson_smul hfg hN)

variable {O : Type*} [CommRing O] [IsNoetherianRing O] (ϖ : O) [IsAdicComplete (Ideal.span {ϖ}) O]
  [Algebra O A] [Module.Finite O A]

omit [IsNoetherianRing O] in
/-- The kernel `ϖ A` of the reduction lies in the Jacobson radical of `A`. -/
private theorem span_le_jacobson :
    Ideal.span {algebraMap O A ϖ} ≤ Ring.jacobson A := by
  have h := map_algebraMap_le_jacobson_of_finite (A := A)
    (IsAdicComplete.le_jacobson (Ideal.span {ϖ}))
  rwa [Ideal.map_span, Set.image_singleton] at h

include hf hfker in
/-- An idempotent endomorphism of a reduction `Y` of a finitely generated projective `A`-module `P`
is the reduction of an idempotent endomorphism of `P`. -/
private theorem exists_isIdempotentElem_map_eq [Module.Finite A P] [Module.Projective A P]
    (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ}) {q : Module.End B Y}
    (hq : IsIdempotentElem q) :
    ∃ e : Module.End A P, IsIdempotentElem e ∧ ∀ x, f (e x) = q (f x) := by
  let _ : Module O P := Module.compHom P (algebraMap O A)
  have : IsScalarTower O A P := IsScalarTower.of_compHom O A P
  have : Module.Finite O P := .trans A P
  have : IsAdicComplete (Ideal.span {ϖ}) (Module.End A P) := .of_finite _ _
  let _ : Module A Y := Module.compHom Y π
  let fA : P →ₗ[A] Y := { toFun := f, map_add' := f.map_add, map_smul' := f.map_smulₛₗ }
  let qA : Y →ₗ[A] Y := { toFun := q, map_add' := q.map_add, map_smul' a y := q.map_smul (π a) y }
  have hqA : IsIdempotentElem qA := LinearMap.ext fun y ↦ LinearMap.congr_fun hq y
  -- Transport `q` along `P ⧸ ϖ P ≃ Y` and lift it to an idempotent of `P`.
  have hk : Ideal.span {algebraMap O A ϖ} • (⊤ : Submodule A P) = LinearMap.ker fA := by
    ext x
    rw [← hker]
    exact (hfker x).symm
  let E := (Submodule.quotEquivOfEq _ _ hk).trans (fA.quotKerEquivOfSurjective hf)
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_endMapQ_eq ϖ (hqA.map E.symm.conjRingEquiv)
  refine ⟨e, he, fun x ↦ ?_⟩
  simpa [E, fA, qA] using congrArg (fun g ↦ E (g (Submodule.Quotient.mk x))) hee

include hπ hf hfker in
/-- **Indecomposability is detected by reduction.** A finitely generated projective `A`-module `P`
is indecomposable exactly when its reduction `Y` is an indecomposable `B`-module. For
`A = O[G]` and `B = k[G]`, the reduction of a projective indecomposable `O[G]`-module is a
projective indecomposable `k[G]`-module. -/
theorem isIndecomposableModule_iff_of_reduction [Module.Finite A P] [Module.Projective A P]
    (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ}) :
    IsIndecomposableModule A P ↔ IsIndecomposableModule B Y := by
  have hJ : RingHom.ker π ≤ Ring.jacobson A := hker ▸ span_le_jacobson ϖ
  have hzero {e : Module.End A P} (he : IsIdempotentElem e) (h : ∀ x, f (e x) = 0) : e = 0 :=
    eq_zero_of_isIdempotentElem_of_map_eq_zero hfker hJ he h
  simp only [isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine and_congr ⟨fun hP ↦ ?_, fun _ ↦ hf.nontrivial⟩ ⟨fun hP q hq ↦ ?_, fun hY e he ↦ ?_⟩
  · -- If `Y = 0` then `P = ϖ P`, so `P = 0` by Nakayama's lemma.
    by_contra hY
    rw [not_nontrivial_iff_subsingleton] at hY
    have htop : (⊤ : Submodule A P) ≤ Ring.jacobson A • ⊤ := fun x _ ↦
      Submodule.smul_mono_left hJ ((hfker x).mp (Subsingleton.elim _ _))
    obtain ⟨x, x', hxx⟩ := hP
    have h := Submodule.FG.eq_bot_of_le_jacobson_smul Module.Finite.fg_top htop
    have hx : x ∈ (⊥ : Submodule A P) := h ▸ Submodule.mem_top
    have hx' : x' ∈ (⊥ : Submodule A P) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hx'
    exact hxx (hx.trans hx'.symm)
  · obtain ⟨e, he, hfe⟩ := exists_isIdempotentElem_map_eq hf hfker ϖ hker hq
    refine (hP e he).imp (fun h0 ↦ LinearMap.ext fun y ↦ ?_) fun h1 ↦ LinearMap.ext fun y ↦ ?_
    · obtain ⟨x, rfl⟩ := hf y
      rw [← hfe, h0, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
    · obtain ⟨x, rfl⟩ := hf y
      rw [← hfe, h1, one_apply_eq_self, one_apply_eq_self]
  · -- Descend `e` to `Y`; its reduction is `0` or `1`, and then so is `e`.
    let q := descend hπ hf hfker (f.comp e)
    have hq (x : P) : q (f x) = f (e x) := descend_apply hπ hf hfker _ x
    have hqi : IsIdempotentElem q := LinearMap.ext fun y ↦ by
      obtain ⟨x, rfl⟩ := hf y
      rw [mul_apply_eq_comp, hq, hq, ← mul_apply_eq_comp, he.eq]
    refine (hY q hqi).imp (fun h0 ↦ hzero he fun x ↦ ?_) fun h1 ↦ ?_
    · rw [← hq, h0, LinearMap.zero_apply]
    · refine (sub_eq_zero.mp (hzero he.one_sub fun x ↦ ?_)).symm
      rw [LinearMap.sub_apply, one_apply_eq_self, map_sub, ← hq, h1, one_apply_eq_self,
        sub_self]

include hπ hf hfker in
/-- **Projective indecomposable modules and simple modules.** When `B` is semiprimary, for
instance `B = k[G]` for a field `k` and a finite group `G`, a finitely generated projective
`A`-module is indecomposable exactly when the top `Y ⧸ J(B) Y` of its reduction `Y` is simple. -/
theorem isIndecomposableModule_iff_isSimpleModule_top_of_reduction [IsSemiprimaryRing B]
    [Module.Finite A P] [Module.Projective A P]
    (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ}) :
    IsIndecomposableModule A P ↔
      IsSimpleModule B (Y ⧸ Ring.jacobson B • (⊤ : Submodule B Y)) := by
  have := projective_of_reduction hπ hf hfker
  rw [isIndecomposableModule_iff_of_reduction hπ hf hfker ϖ hker,
    isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top]

omit [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O] [Module.Finite O A] in
/-- The kernel of a reduction is `ϖ P`, and the reduction is a linear equivalence
`P ⧸ ϖ P ≃ Y`, when `Y` is regarded as an `A`-module through `π`. -/
private theorem nonempty_linearEquiv_quotient [Module A Y] (hY : ∀ (a : A) (y : Y), a • y = π a • y)
    {f : P →ₛₗ[π] Y} (hf : Function.Surjective f)
    (hfker : ∀ x, f x = 0 ↔ x ∈ RingHom.ker π • (⊤ : Submodule A P)) :
    Nonempty ((P ⧸ RingHom.ker π • (⊤ : Submodule A P)) ≃ₗ[A] Y) := by
  let fA : P →ₗ[A] Y :=
    { toFun := f, map_add' := f.map_add, map_smul' a x := by rw [f.map_smulₛₗ, hY]; rfl }
  have hk : RingHom.ker π • (⊤ : Submodule A P) = LinearMap.ker fA := by
    ext x
    exact (hfker x).symm
  exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (fA.quotKerEquivOfSurjective hf)⟩

omit [IsNoetherianRing O] in
/-- **Projective lifts are unique.** Two finitely generated projective `A`-modules with the same
reduction `Y` are isomorphic. -/
theorem nonempty_linearEquiv_of_reduction (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ})
    [Module.Finite A P] [Module.Projective A P] {Q : Type*} [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Projective A Q] {f : P →ₛₗ[π] Y} (hf : Function.Surjective f)
    (hfker : ∀ x, f x = 0 ↔ x ∈ RingHom.ker π • (⊤ : Submodule A P))
    {g : Q →ₛₗ[π] Y} (hg : Function.Surjective g)
    (hgker : ∀ x, g x = 0 ↔ x ∈ RingHom.ker π • (⊤ : Submodule A Q)) :
    Nonempty (P ≃ₗ[A] Q) := by
  let _ : Module A Y := Module.compHom Y π
  obtain ⟨eP⟩ := nonempty_linearEquiv_quotient (fun _ _ ↦ rfl) hf hfker
  obtain ⟨eQ⟩ := nonempty_linearEquiv_quotient (fun _ _ ↦ rfl) hg hgker
  exact Ideal.nonempty_linearEquiv_of_quotient_smul_top _ P Q (hker ▸ span_le_jacobson ϖ)
    ⟨eP.trans eQ.symm⟩

omit [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O] [Module.Finite O A] in
/-- A vector over `A` is divisible by `ϖ` exactly when each of its coordinates reduces to `0`. -/
private theorem mem_span_smul_top_pi_iff (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ})
    {ι : Type*} {v : ι → A} :
    v ∈ Ideal.span {algebraMap O A ϖ} • (⊤ : Submodule A (ι → A)) ↔ ∀ i, π (v i) = 0 := by
  have hϖ : π (algebraMap O A ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  rw [Submodule.mem_span_algebraMap_smul_iff]
  simp only [Submodule.mem_top, true_and]
  constructor
  · rintro ⟨w, rfl⟩ i
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, hϖ, zero_mul]
  · intro hv
    have hv' (i : ι) : v i ∈ Ideal.span {algebraMap O A ϖ} := hker ▸ RingHom.mem_ker.mpr (hv i)
    choose w hw using fun i ↦ Ideal.mem_span_singleton'.mp (hv' i)
    exact ⟨w, funext fun i ↦ by rw [Pi.smul_apply, Algebra.smul_def, Algebra.commutes, hw]⟩

include hπ in
/-- **Projective `B`-modules lift.** For a surjection `π : A →+* B` with kernel `ϖ A`, every
finitely generated projective `B`-module `Y` is the reduction of a finitely generated projective
`A`-module `X`, realised as a submodule of some `Aⁿ`: there is a surjection `X → Y`, semilinear
along `π`, with kernel `ϖ X`. For `A = O[G]` and `B = k[G]`, every projective indecomposable
`k[G]`-module is the reduction of a projective indecomposable `O[G]`-module, by
`TauCeti.isIndecomposableModule_iff_of_reduction`, unique up to isomorphism by
`TauCeti.nonempty_linearEquiv_of_reduction`. -/
theorem exists_projective_reduction_of_projective
    (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ}) [Module.Finite B Y]
    [Module.Projective B Y] :
    ∃ (n : ℕ) (X : Submodule A (Fin n → A)), Module.Finite A X ∧ Module.Projective A X ∧
      ∃ f : X →ₛₗ[π] Y, Function.Surjective f ∧
        ∀ x, f x = 0 ↔ x ∈ RingHom.ker π • (⊤ : Submodule A X) := by
  -- Present `Y` as a direct summand of `Bⁿ`, the reduction of `Aⁿ`.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' B Y
  obtain ⟨t, hst⟩ := Module.projective_lifting_property s LinearMap.id hs
  let _ : Module A Y := Module.compHom Y π
  let _ : Module A (Fin n → B) := Module.compHom _ π
  let ρ : (Fin n → A) →ₗ[A] (Fin n → B) :=
    { toFun v i := π (v i)
      map_add' v w := funext fun i ↦ map_add π (v i) (w i)
      map_smul' a v := funext fun i ↦ map_mul π a (v i) }
  have hρ : Function.Surjective ρ := fun w ↦
    ⟨fun i ↦ Function.surjInv hπ (w i), funext fun i ↦ Function.surjInv_eq hπ (w i)⟩
  have hρker : Ideal.span {algebraMap O A ϖ} • (⊤ : Submodule A (Fin n → A)) = LinearMap.ker ρ := by
    ext v
    exact (mem_span_smul_top_pi_iff ϖ hker).trans funext_iff.symm
  let _ : Module O (Fin n → A) := inferInstance
  have : IsAdicComplete (Ideal.span {ϖ}) (Module.End A (Fin n → A)) := .of_finite _ _
  let E := (Submodule.quotEquivOfEq _ _ hρker).trans (ρ.quotKerEquivOfSurjective hρ)
  let s' : (Fin n → B) →ₗ[A] Y :=
    { toFun := s, map_add' := s.map_add, map_smul' a w := s.map_smul (π a) w }
  let t' : Y →ₗ[A] (Fin n → B) :=
    { toFun := t, map_add' := t.map_add, map_smul' a y := t.map_smul (π a) y }
  obtain ⟨X, hXp, ⟨g⟩⟩ := exists_projective_quotient_smul_top_linearEquiv ϖ
    (E.symm.toLinearMap ∘ₗ t') (s' ∘ₗ E.toLinearMap)
    (LinearMap.ext fun y ↦ by simpa [s', t'] using LinearMap.congr_fun hst y)
  have : IsNoetherian A (Fin n → A) := isNoetherian_of_tower O inferInstance
  refine ⟨n, X, inferInstance, hXp,
    { toFun x := g (Submodule.Quotient.mk x), map_add' x y := by simp,
      map_smul' a x := by simp; rfl },
    fun y ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (g.symm y)
    exact ⟨x, by simp [hx]⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero, hker]

end Reduction

section GroupAlgebra

variable {O G : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Monoid G] [Finite G]

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite G] in
/-- Reduction `O[G] → k[G]` is surjective. -/
private theorem mapRingHom_residue_surjective :
    Function.Surjective (MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)) := fun p ↦
  (MonoidAlgebra.mem_rangeS_mapRingHom_iff _ p).mpr fun _ ↦ IsLocalRing.residue_surjective _

omit [Finite G] in
/-- A uniformizer `ϖ` of `O`: `O` is `ϖ`-adically complete and the kernel of reduction
`O[G] → k[G]` is generated by `ϖ`. -/
private theorem exists_uniformizer : ∃ ϖ : O, IsAdicComplete (Ideal.span {ϖ}) O ∧
    RingHom.ker (MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)) =
      Ideal.span {algebraMap O (MonoidAlgebra O G) ϖ} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨ϖ, hϖ.maximalIdeal_eq ▸ inferInstance, MonoidAlgebra.ker_mapRingHom_eq_span_algebraMap ?_⟩
  rw [IsLocalRing.ker_residue, hϖ.maximalIdeal_eq]

variable {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra O G) P]
  [Module.Finite (MonoidAlgebra O G) P] [Module.Projective (MonoidAlgebra O G) P]
  {Y : Type*} [AddCommGroup Y] [Module (MonoidAlgebra (IsLocalRing.ResidueField O) G) Y]

/-- **Projective indecomposable `O[G]`-modules reduce to projective indecomposable
`k[G]`-modules.** For a complete discrete valuation ring `O` with residue field `k` and a finite
group `G`, a finitely generated projective `O[G]`-module `P` is indecomposable exactly when its
reduction `Y ≅ P ⧸ m P`, a projective `k[G]`-module, is indecomposable. -/
theorem isIndecomposableModule_iff_of_reduction_residue
    {f : P →ₛₗ[MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)] Y} (hf : Function.Surjective f)
    (hfker : ∀ x, f x = 0 ↔ x ∈ RingHom.ker (MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)) •
      (⊤ : Submodule (MonoidAlgebra O G) P)) :
    IsIndecomposableModule (MonoidAlgebra O G) P ↔
      IsIndecomposableModule (MonoidAlgebra (IsLocalRing.ResidueField O) G) Y := by
  obtain ⟨ϖ, _, hker⟩ := exists_uniformizer (O := O) (G := G)
  exact isIndecomposableModule_iff_of_reduction mapRingHom_residue_surjective hf hfker ϖ hker

/-- **Lifts to `O[G]` are unique.** For a complete discrete valuation ring `O` with residue field
`k` and a finite group `G`, two finitely generated projective `O[G]`-modules with the same
reduction `Y` are isomorphic. -/
theorem nonempty_linearEquiv_of_reduction_residue {Q : Type*} [AddCommGroup Q]
    [Module (MonoidAlgebra O G) Q] [Module.Finite (MonoidAlgebra O G) Q]
    [Module.Projective (MonoidAlgebra O G) Q]
    {f : P →ₛₗ[MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)] Y} (hf : Function.Surjective f)
    (hfker : ∀ x, f x = 0 ↔ x ∈ RingHom.ker (MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)) •
      (⊤ : Submodule (MonoidAlgebra O G) P))
    {g : Q →ₛₗ[MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)] Y} (hg : Function.Surjective g)
    (hgker : ∀ x, g x = 0 ↔ x ∈ RingHom.ker (MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)) •
      (⊤ : Submodule (MonoidAlgebra O G) Q)) :
    Nonempty (P ≃ₗ[MonoidAlgebra O G] Q) := by
  obtain ⟨ϖ, _, hker⟩ := exists_uniformizer (O := O) (G := G)
  exact nonempty_linearEquiv_of_reduction ϖ hker hf hfker hg hgker

omit [Module.Finite (MonoidAlgebra O G) P] [Module.Projective (MonoidAlgebra O G) P] in
/-- **Projective `k[G]`-modules lift to `O[G]`.** For a complete discrete valuation ring `O` with
residue field `k` and a finite group `G`, every finitely generated projective `k[G]`-module is the
reduction of a finitely generated projective `O[G]`-module, indecomposable when the `k[G]`-module
is (`TauCeti.isIndecomposableModule_iff_of_reduction_residue`). -/
theorem exists_projective_reduction_residue_of_projective
    [Module.Finite (MonoidAlgebra (IsLocalRing.ResidueField O) G) Y]
    [Module.Projective (MonoidAlgebra (IsLocalRing.ResidueField O) G) Y] :
    ∃ (n : ℕ) (X : Submodule (MonoidAlgebra O G) (Fin n → MonoidAlgebra O G)),
      Module.Finite (MonoidAlgebra O G) X ∧ Module.Projective (MonoidAlgebra O G) X ∧
      ∃ f : X →ₛₗ[MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)] Y,
        Function.Surjective f ∧ ∀ x, f x = 0 ↔
          x ∈ RingHom.ker (MonoidAlgebra.mapRingHom G (IsLocalRing.residue O)) •
            (⊤ : Submodule (MonoidAlgebra O G) X) := by
  obtain ⟨ϖ, _, hker⟩ := exists_uniformizer (O := O) (G := G)
  exact exists_projective_reduction_of_projective mapRingHom_residue_surjective ϖ hker

end GroupAlgebra

end TauCeti
