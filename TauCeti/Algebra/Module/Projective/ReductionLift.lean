/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable
import Mathlib.RingTheory.Nakayama
import TauCeti.Algebra.Module.LinearMap.EndQuotient
import TauCeti.Algebra.Module.Projective.Lift
import TauCeti.Algebra.Module.Projective.Reduction
import TauCeti.Algebra.Module.Projective.Semilinear
import TauCeti.Algebra.Module.Projective.Top
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Ideal.Extended
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Jacobson.Basic
import TauCeti.RingTheory.Jacobson.Finite
import TauCeti.RingTheory.Noetherian.LinearMap

/-!
# Lifting projective modules along a reduction

Let `π : A →+* B` be a surjective ring homomorphism. A **reduction** of an `A`-module `P` is a
`B`-module `Y` with a surjection `f : P → Y`, semilinear along `π`, whose kernel is `ker π • P`; in
other words `Y ≅ P ⧸ ker π • P` with its `B`-module structure. The main case is the reduction
`O[G] → k[G]` of a group algebra over a complete discrete valuation ring with residue field `k`
(`TauCeti/RepresentationTheory/Modular/ProjectiveLift.lean`).

This file proves that finitely generated projective `A`-modules and their reductions correspond:

* the reduction of a projective `A`-module is a projective `B`-module
  (`TauCeti.projective_of_reduction`; finiteness is Mathlib's `Module.Finite.of_surjective`);
* two finitely generated projective `A`-modules with the same reduction are isomorphic when
  `ker π` lies in the Jacobson radical of `A` (`TauCeti.nonempty_linearEquiv_of_reduction`).

When moreover `A` is an algebra over a Noetherian ring `O`, finite as an `O`-module, `O` is
complete with respect to a principal ideal `(ϖ)` and `ker π = ϖ A`, then `ϖ A` lies in the Jacobson
radical of `A` (`TauCeti.span_algebraMap_le_jacobson`, from `TauCeti.Ring.algebraMap_mem_jacobson`),
and:

* every finitely generated projective `B`-module is the reduction of a finitely generated
  projective `A`-module (`TauCeti.exists_projective_reduction_of_projective`);
* a finitely generated projective `A`-module is indecomposable exactly when its reduction is
  (`TauCeti.isIndecomposableModule_iff_of_reduction`), and, when `B` is semiprimary, exactly when
  the top of its reduction is simple
  (`TauCeti.isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top_of_reduction`).

Indecomposability is transported by idempotent endomorphisms: an idempotent endomorphism of `P`
descends to the reduction, and with the kernel of reduction in the radical it vanishes exactly when
its reduction does; conversely an idempotent endomorphism of the reduction `Y ≃ P ⧸ ϖ P` lifts to
an idempotent endomorphism of `P` because `End_A(P)` is `ϖ`-adically complete
(`TauCeti.exists_isIdempotentElem_endMapQ_eq`).

## Main results

* `TauCeti.projective_of_reduction`: the reduction of a projective module is projective.
* `TauCeti.nonempty_linearEquiv_of_reduction`: lifts are unique up to isomorphism.
* `TauCeti.span_algebraMap_le_jacobson`: `ϖ A` lies in the Jacobson radical of `A`.
* `TauCeti.isIndecomposableModule_iff_of_reduction`: a finitely generated projective `A`-module is
  indecomposable exactly when its reduction is.
* `TauCeti.exists_projective_reduction_of_projective`: projective `B`-modules lift.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 9.4.3 and 9.4.5.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
-/

public section

namespace TauCeti

section Reduction

variable {A B : Type*} [Ring A] [Ring B] {π : A →+* B}
  {P : Type*} [AddCommGroup P] [Module A P] {Y : Type*} [AddCommGroup Y] [Module B Y]

/-- A semilinear map into a `B`-module kills `ker π • P`. -/
private theorem map_eq_zero_of_mem_ker_smul_top {M : Type*} [AddCommGroup M] [Module B M]
    (h : P →ₛₗ[π] M) {x : P} (hx : x ∈ RingHom.ker π • (⊤ : Submodule A P)) : h x = 0 :=
  Submodule.smul_induction_on hx (fun r hr n _ ↦ by rw [h.map_smulₛₗ, hr, zero_smul])
    fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero]

/-- A map semilinear along `π` into a module on which `A` acts through `π`, as an `A`-linear
map. -/
private def toLinearMapOfCompHom {M : Type*} [AddCommGroup M] [Module B M] [Module A M]
    (hM : ∀ (a : A) (m : M), a • m = π a • m) (g : P →ₛₗ[π] M) : P →ₗ[A] M where
  toFun := g
  map_add' := g.map_add
  map_smul' a x := by rw [g.map_smulₛₗ, hM, RingHom.id_apply]

/-- A `B`-linear map between modules on which `A` acts through `π`, as an `A`-linear map. -/
private def restrictScalarsOfCompHom {M N : Type*} [AddCommGroup M] [Module B M] [Module A M]
    [AddCommGroup N] [Module B N] [Module A N] (hM : ∀ (a : A) (m : M), a • m = π a • m)
    (hN : ∀ (a : A) (n : N), a • n = π a • n) (g : M →ₗ[B] N) : M →ₗ[A] N where
  toFun := g
  map_add' := g.map_add
  map_smul' a m := by rw [hM, hN, g.map_smul, RingHom.id_apply]

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
  obtain ⟨u, hu⟩ := Module.projective_lifting_property_semilinear s hs f
  refine Module.Projective.of_split (descend hπ hf hfker u) s (LinearMap.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := hf y
  rw [LinearMap.comp_apply, descend_apply, ← LinearMap.comp_apply, hu, LinearMap.id_apply]

include hf hfker in
/-- A reduction `f : P → Y` induces a linear equivalence `P ⧸ ker π • P ≃ Y`, when `Y` is regarded
as an `A`-module through `π`. -/
private noncomputable def quotientEquiv [Module A Y] (hY : ∀ (a : A) (y : Y), a • y = π a • y) :
    (P ⧸ RingHom.ker π • (⊤ : Submodule A P)) ≃ₗ[A] Y :=
  (Submodule.quotEquivOfEq _ _ (Submodule.ext fun x ↦ (hfker x).symm :
      RingHom.ker π • ⊤ = LinearMap.ker (toLinearMapOfCompHom hY f))).trans
    ((toLinearMapOfCompHom hY f).quotKerEquivOfSurjective hf)

private theorem quotientEquiv_mk [Module A Y] (hY : ∀ (a : A) (y : Y), a • y = π a • y) (x : P) :
    quotientEquiv hf hfker hY (Submodule.Quotient.mk x) = f x :=
  rfl

include hf hfker in
/-- **Projective lifts are unique.** Two finitely generated projective `A`-modules with the same
reduction `Y` are isomorphic, when the kernel of `π` lies in the Jacobson radical of `A`, for
instance when it is `ϖ A` (`TauCeti.span_algebraMap_le_jacobson`). -/
theorem nonempty_linearEquiv_of_reduction (hJ : RingHom.ker π ≤ Ring.jacobson A)
    [Module.Finite A P] [Module.Projective A P] {Q : Type*} [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Projective A Q] {g : Q →ₛₗ[π] Y} (hg : Function.Surjective g)
    (hgker : ∀ x, g x = 0 ↔ x ∈ RingHom.ker π • (⊤ : Submodule A Q)) :
    Nonempty (P ≃ₗ[A] Q) := by
  let _ : Module A Y := Module.compHom Y π
  exact Ideal.nonempty_linearEquiv_of_quotient_smul_top _ P Q hJ
    ⟨(quotientEquiv hf hfker fun _ _ ↦ rfl).trans
      (quotientEquiv hg hgker fun _ _ ↦ rfl).symm⟩

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
theorem span_algebraMap_le_jacobson : Ideal.span {algebraMap O A ϖ} ≤ Ring.jacobson A :=
  Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <| Ring.algebraMap_mem_jacobson <|
    IsAdicComplete.le_jacobson _ (Ideal.mem_span_singleton_self ϖ)

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
  let qA := restrictScalarsOfCompHom (A := A) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) q
  have hqA : IsIdempotentElem qA := LinearMap.ext fun y ↦ LinearMap.congr_fun hq y
  -- Transport `q` along `P ⧸ ϖ P ≃ Y` and lift it to an idempotent of `P`.
  let E := (Submodule.quotEquivOfEq _ _ (by rw [hker])).trans
    (quotientEquiv hf hfker fun _ _ ↦ rfl)
  have hE (x : P) : E (Submodule.Quotient.mk x) = f x := by
    rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, quotientEquiv_mk]
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_endMapQ_eq ϖ (hqA.map E.symm.conjRingEquiv)
  refine ⟨e, he, fun x ↦ ?_⟩
  have h := congrArg (fun g ↦ E (g (Submodule.Quotient.mk x))) hee
  rw [Ideal.endMapQ_mk, hE] at h
  rw [h]
  simp [LinearEquiv.conjRingEquiv, LinearEquiv.arrowCongrAddEquiv, hE, qA,
    restrictScalarsOfCompHom]

include hπ hf hfker in
/-- **Indecomposability is detected by reduction.** A finitely generated projective `A`-module `P`
is indecomposable exactly when its reduction `Y` is an indecomposable `B`-module. For
`A = O[G]` and `B = k[G]`, the reduction of a projective indecomposable `O[G]`-module is a
projective indecomposable `k[G]`-module. -/
theorem isIndecomposableModule_iff_of_reduction [Module.Finite A P] [Module.Projective A P]
    (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ}) :
    IsIndecomposableModule A P ↔ IsIndecomposableModule B Y := by
  have hJ : RingHom.ker π ≤ Ring.jacobson A := hker ▸ span_algebraMap_le_jacobson ϖ
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
theorem isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top_of_reduction
    [IsSemiprimaryRing B]
    [Module.Finite A P] [Module.Projective A P]
    (hker : RingHom.ker π = Ideal.span {algebraMap O A ϖ}) :
    IsIndecomposableModule A P ↔
      IsSimpleModule B (Y ⧸ Ring.jacobson B • (⊤ : Submodule B Y)) := by
  have := projective_of_reduction hπ hf hfker
  rw [isIndecomposableModule_iff_of_reduction hπ hf hfker ϖ hker,
    isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top]

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
  have : IsAdicComplete (Ideal.span {ϖ}) (Module.End A (Fin n → A)) := .of_finite _ _
  let E := (Submodule.quotEquivOfEq _ _ hρker).trans (ρ.quotKerEquivOfSurjective hρ)
  have hY (a : A) (y : Y) : a • y = π a • y := rfl
  have hB (a : A) (w : Fin n → B) : a • w = π a • w := rfl
  let s' := restrictScalarsOfCompHom hB hY s
  let t' := restrictScalarsOfCompHom hY hB t
  obtain ⟨X, hXp, ⟨g⟩⟩ := exists_projective_quotient_smul_top_linearEquiv ϖ
    (E.symm.toLinearMap ∘ₗ t') (s' ∘ₗ E.toLinearMap)
    (LinearMap.ext fun y ↦ by
      simpa [s', t', restrictScalarsOfCompHom] using LinearMap.congr_fun hst y)
  have : IsNoetherian A (Fin n → A) := isNoetherian_of_tower O inferInstance
  refine ⟨n, X, inferInstance, hXp,
    { toFun x := g (Submodule.Quotient.mk x), map_add' x y := by simp,
      map_smul' a x := by
        rw [Submodule.Quotient.mk_smul, LinearEquiv.map_smul, hY] },
    fun y ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (g.symm y)
    exact ⟨x, by simp [hx]⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero, hker]

end Reduction

end TauCeti
